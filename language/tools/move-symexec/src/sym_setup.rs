// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{collections::HashMap, fmt};

use move_core_types::{
    account_address::AccountAddress,
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId,
};
use vm::{
    access::{ModuleAccess, ScriptAccess},
    file_format::{
        AddressIdentifierIndex, CodeUnit, CompiledModule, CompiledScript, FunctionDefinition,
        FunctionHandle, FunctionHandleIndex, FunctionInstantiation, FunctionInstantiationIndex,
        IdentifierIndex, ModuleHandle, ModuleHandleIndex, SignatureToken, StructFieldInformation,
        TypeSignature,
    },
};

/// uniquely identifies a function in the execution
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub(crate) enum CodeContext {
    Script,
    Module {
        module_id: ModuleId,
        function_id: Identifier,
    },
}

impl fmt::Display for CodeContext {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CodeContext::Script => write!(f, "<script>"),
            CodeContext::Module {
                module_id,
                function_id,
            } => write!(f, "{}::{}", module_id, function_id),
        }
    }
}

/// unify script and function accesses
pub(crate) enum ExecUnit<'a> {
    Script(&'a CompiledScript),
    Module(&'a CompiledModule, &'a FunctionDefinition),
}

impl ExecUnit<'_> {
    fn module_handle_at(&self, idx: ModuleHandleIndex) -> &ModuleHandle {
        match self {
            ExecUnit::Script(unit) => unit.module_handle_at(idx),
            ExecUnit::Module(unit, _) => unit.module_handle_at(idx),
        }
    }

    fn function_handle_at(&self, idx: FunctionHandleIndex) -> &FunctionHandle {
        match self {
            ExecUnit::Script(unit) => unit.function_handle_at(idx),
            ExecUnit::Module(unit, _) => unit.function_handle_at(idx),
        }
    }

    fn function_instantiation_at(&self, idx: FunctionInstantiationIndex) -> &FunctionInstantiation {
        match self {
            ExecUnit::Script(unit) => unit.function_instantiation_at(idx),
            ExecUnit::Module(unit, _) => unit.function_instantiation_at(idx),
        }
    }

    fn address_identifier_at(&self, idx: AddressIdentifierIndex) -> &AccountAddress {
        match self {
            ExecUnit::Script(unit) => unit.address_identifier_at(idx),
            ExecUnit::Module(unit, _) => unit.address_identifier_at(idx),
        }
    }

    fn identifier_at(&self, idx: IdentifierIndex) -> &IdentStr {
        match self {
            ExecUnit::Script(unit) => unit.identifier_at(idx),
            ExecUnit::Module(unit, _) => unit.identifier_at(idx),
        }
    }

    pub fn module_id_by_index(&self, idx: ModuleHandleIndex) -> ModuleId {
        let handle = self.module_handle_at(idx);
        ModuleId::new(
            *self.address_identifier_at(handle.address),
            self.identifier_at(handle.name).to_owned(),
        )
    }

    pub fn code_context_by_index(&self, idx: FunctionHandleIndex) -> CodeContext {
        let handle = self.function_handle_at(idx);
        CodeContext::Module {
            module_id: self.module_id_by_index(handle.module),
            function_id: self.identifier_at(handle.name).to_owned(),
        }
    }

    pub fn code_context_by_generic_index(&self, idx: FunctionInstantiationIndex) -> CodeContext {
        let instantiation = self.function_instantiation_at(idx);
        self.code_context_by_index(instantiation.handle)
    }

    pub fn code_unit(&self) -> &CodeUnit {
        match self {
            ExecUnit::Script(unit) => unit.code(),
            ExecUnit::Module(_, func) => (&func.code)
                .as_ref()
                .expect("A tracked function must have a code unit"),
        }
    }

    pub fn get_code_context(&self) -> CodeContext {
        match self {
            ExecUnit::Script(_) => CodeContext::Script,
            ExecUnit::Module(unit, func) => CodeContext::Module {
                module_id: unit.self_id(),
                function_id: unit
                    .identifier_at(unit.function_handle_at(func.function).name)
                    .to_owned(),
            },
        }
    }
}

/// Collect and hold all environmental information needed by various
/// components of the symbolic executor.
pub(crate) struct SymSetup<'a> {
    loaded_modules: HashMap<ModuleId, &'a CompiledModule>,
    defined_structs:
        HashMap<ModuleId, HashMap<Identifier, Option<HashMap<Identifier, TypeSignature>>>>,
    tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
}

impl<'a> SymSetup<'a> {
    pub fn new(
        modules: &[&'a CompiledModule],
        tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
    ) -> Self {
        // derive loaded modules
        let loaded_modules: HashMap<ModuleId, &'a CompiledModule> = modules
            .iter()
            .map(|module| (module.self_id(), *module))
            .collect();

        // collect struct definitions
        let defined_structs = SymSetup::collect_defined_structs(modules);

        // done
        let setup = Self {
            loaded_modules,
            defined_structs,
            tracked_functions,
        };

        // checks
        setup.check_defined_structs();

        // return
        setup
    }

    // getters
    pub fn num_defined_structs(&self) -> usize {
        self.defined_structs.iter().map(|(_, v)| v.len()).sum()
    }

    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.iter().map(|(_, v)| v.len()).sum()
    }

    pub fn get_exec_unit_by_context(&self, context: &CodeContext) -> Option<&ExecUnit> {
        match context {
            CodeContext::Script => None,
            CodeContext::Module {
                module_id,
                function_id,
            } => self
                .tracked_functions
                .get(module_id)
                .map(|func_map| func_map.get(function_id))
                .flatten(),
        }
    }

    // checkers
    fn check_defined_structs(&self) {
        // check that all indirect structs are also included
        for (module_id, module_structs) in self.defined_structs.iter() {
            let module = self.loaded_modules.get(module_id).unwrap();
            for struct_fields_opt in module_structs.values() {
                if let Some(struct_fields) = struct_fields_opt {
                    for field_type in struct_fields.values() {
                        self.check_defined_structs_field_sig(module, &field_type.0);
                    }
                }
            }
        }
    }

    fn check_defined_structs_field_sig(&self, module: &'a CompiledModule, sig: &SignatureToken) {
        match sig {
            SignatureToken::Bool
            | SignatureToken::U8
            | SignatureToken::U64
            | SignatureToken::U128
            | SignatureToken::Address
            | SignatureToken::Signer
            | SignatureToken::TypeParameter(_) => {}
            SignatureToken::Vector(element_sig) => {
                self.check_defined_structs_field_sig(module, element_sig.as_ref())
            }
            SignatureToken::Struct(handle_index)
            | SignatureToken::StructInstantiation(handle_index, ..) => {
                let struct_handle = module.struct_handle_at(*handle_index);
                let struct_name = module.identifier_at(struct_handle.name);
                let module_handle = module.module_handle_at(struct_handle.module);
                let module_id = module.module_id_for_handle(module_handle);
                debug_assert!(self
                    .defined_structs
                    .get(&module_id)
                    .unwrap()
                    .contains_key(struct_name));
            }
            SignatureToken::Reference(referred_sig)
            | SignatureToken::MutableReference(referred_sig) => {
                self.check_defined_structs_field_sig(module, referred_sig.as_ref())
            }
        }
    }

    // struct
    fn collect_defined_structs(
        modules: &[&'a CompiledModule],
    ) -> HashMap<ModuleId, HashMap<Identifier, Option<HashMap<Identifier, TypeSignature>>>> {
        let mut defined_structs = HashMap::new();

        for module in modules {
            let mut module_structs = HashMap::new();
            for struct_def in module.struct_defs() {
                let struct_handle = module.struct_handle_at(struct_def.struct_handle);
                let struct_name = module.identifier_at(struct_handle.name).to_owned();

                let struct_fields = match &struct_def.field_information {
                    StructFieldInformation::Native => None,
                    StructFieldInformation::Declared(field_defs) => {
                        let fields: HashMap<Identifier, TypeSignature> = field_defs
                            .iter()
                            .map(|field_def| {
                                (
                                    module.identifier_at(field_def.name).to_owned(),
                                    field_def.signature.clone(),
                                )
                            })
                            .collect();
                        Some(fields)
                    }
                };

                let exists = module_structs.insert(struct_name, struct_fields);
                debug_assert!(exists.is_none());
            }

            let exists = defined_structs.insert(module.self_id(), module_structs);
            debug_assert!(exists.is_none());
        }

        defined_structs
    }
}
