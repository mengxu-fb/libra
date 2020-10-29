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
        IdentifierIndex, ModuleHandle, ModuleHandleIndex, StructDefinition, StructFieldInformation,
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
    declared_structs:
        HashMap<ModuleId, HashMap<Identifier, Option<HashMap<Identifier, TypeSignature>>>>,
    tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
}

impl<'a> SymSetup<'a> {
    pub fn new(
        modules: &[&'a CompiledModule],
        tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
    ) -> Self {
        // derive loaded modules
        let loaded_modules = modules
            .iter()
            .map(|module| (module.self_id(), *module))
            .collect();

        // collect struct definitions
        let mut declared_structs: HashMap<
            ModuleId,
            HashMap<Identifier, Option<HashMap<Identifier, TypeSignature>>>,
        > = HashMap::new();
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

            let exists = declared_structs.insert(module.self_id(), module_structs);
            debug_assert!(exists.is_none());
        }

        // done
        Self {
            loaded_modules,
            declared_structs,
            tracked_functions,
        }
    }

    // getters
    pub fn num_declared_structs(&self) -> usize {
        self.declared_structs.iter().map(|(_, v)| v.len()).sum()
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

    // struct
    fn get_involved_structs_recursive(
        &self,
        module: &CompiledModule,
        structs: &mut HashMap<ModuleId, Vec<StructDefinition>>,
    ) {
        // add struct defs in this module
        let module_structs: Vec<StructDefinition> = module.struct_defs().iter().cloned().collect();
        let result = structs.insert(module.self_id(), module_structs);
        debug_assert!(result.is_none());

        // recursively explore dependencies
        for struct_handle in module.struct_handles() {
            let module_handle = module.module_handle_at(struct_handle.module);
            let module_id = ModuleId::new(
                *module.address_identifier_at(module_handle.address),
                module.identifier_at(module_handle.name).to_owned(),
            );
            if structs.contains_key(&module_id) {
                continue;
            }

            // only if we have not explored this module
            let dep = self.loaded_modules.get(&module_id).unwrap();
            self.get_involved_structs_recursive(dep, structs);
        }
    }

    pub fn get_involved_structs(
        &self,
        script: &CompiledScript,
    ) -> HashMap<ModuleId, Vec<StructDefinition>> {
        let mut structs = HashMap::new();

        for struct_handle in script.struct_handles() {
            let module_handle = script.module_handle_at(struct_handle.module);
            let module_id = ModuleId::new(
                *script.address_identifier_at(module_handle.address),
                script.identifier_at(module_handle.name).to_owned(),
            );
            if structs.contains_key(&module_id) {
                continue;
            }

            // only if we have not explored this module
            let dep = self.loaded_modules.get(&module_id).unwrap();
            self.get_involved_structs_recursive(dep, &mut structs);
        }

        structs
    }
}
