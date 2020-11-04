// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use move_core_types::{
    account_address::AccountAddress,
    identifier::{IdentStr, Identifier},
    language_storage::{ModuleId, TypeTag},
};
use vm::{
    access::{ModuleAccess, ScriptAccess},
    file_format::{
        AddressIdentifierIndex, Bytecode, CodeUnit, CompiledModule, CompiledScript, FieldHandle,
        FieldHandleIndex, FieldInstantiation, FieldInstantiationIndex, FunctionDefinition,
        FunctionHandle, FunctionHandleIndex, FunctionInstantiation, FunctionInstantiationIndex,
        IdentifierIndex, LocalIndex, ModuleHandle, ModuleHandleIndex, Signature, SignatureIndex,
        SignatureToken, StructDefInstantiation, StructDefInstantiationIndex, StructDefinition,
        StructDefinitionIndex, StructFieldInformation, StructHandle, StructHandleIndex,
        TypeParameterIndex, TypeSignature,
    },
};

/// uniquely identifies a function in the execution
/// (but may have different instantiations)
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub(crate) enum CodeContext {
    Script,
    Module {
        module_id: ModuleId,
        function_name: Identifier,
    },
}

impl fmt::Display for CodeContext {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CodeContext::Script => write!(f, "<script>"),
            CodeContext::Module {
                module_id,
                function_name,
            } => write!(
                f,
                "{}::{}::{}",
                module_id.address().short_str_lossless(),
                module_id.name(),
                function_name
            ),
        }
    }
}

/// uniquely identifiers a struct in the execution
/// (but may have different instantiations)
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
pub(crate) struct StructContext {
    module_id: ModuleId,
    struct_name: Identifier,
}

impl fmt::Display for StructContext {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}::{}::{}",
            self.module_id.address().short_str_lossless(),
            self.module_id.name(),
            self.struct_name
        )
    }
}

#[derive(Clone, Debug)]
pub(crate) enum StructInfo<'a> {
    Native,
    Declared {
        field_vec: Vec<Identifier>,
        field_map: HashMap<Identifier, &'a TypeSignature>,
    },
}

/// unify script and function accesses
#[derive(Clone, Debug)]
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

    fn struct_handle_at(&self, idx: StructHandleIndex) -> &StructHandle {
        match self {
            ExecUnit::Script(unit) => unit.struct_handle_at(idx),
            ExecUnit::Module(unit, _) => unit.struct_handle_at(idx),
        }
    }

    fn struct_def_at(&self, idx: StructDefinitionIndex) -> &StructDefinition {
        match self {
            ExecUnit::Script(_) => panic!("struct_def_at is only applicable to modules"),
            ExecUnit::Module(unit, _) => unit.struct_def_at(idx),
        }
    }

    fn struct_instantiation_at(&self, idx: StructDefInstantiationIndex) -> &StructDefInstantiation {
        match self {
            ExecUnit::Script(_) => panic!("struct_instantiation_at is only applicable to modules"),
            ExecUnit::Module(unit, _) => unit.struct_instantiation_at(idx),
        }
    }

    fn field_handle_at(&self, idx: FieldHandleIndex) -> &FieldHandle {
        match self {
            ExecUnit::Script(_) => panic!("field_handle_at is only applicable to modules"),
            ExecUnit::Module(unit, _) => unit.field_handle_at(idx),
        }
    }

    fn field_instantiation_at(&self, idx: FieldInstantiationIndex) -> &FieldInstantiation {
        match self {
            ExecUnit::Script(_) => panic!("field_instantiation_at is only applicable to modules"),
            ExecUnit::Module(unit, _) => unit.field_instantiation_at(idx),
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

    fn signature_at(&self, idx: SignatureIndex) -> &Signature {
        match self {
            ExecUnit::Script(unit) => unit.signature_at(idx),
            ExecUnit::Module(unit, _) => unit.signature_at(idx),
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
            function_name: self.identifier_at(handle.name).to_owned(),
        }
    }

    pub fn code_context_by_generic_index(&self, idx: FunctionInstantiationIndex) -> CodeContext {
        let instantiation = self.function_instantiation_at(idx);
        self.code_context_by_index(instantiation.handle)
    }

    pub fn struct_context_by_handle_index(&self, idx: StructHandleIndex) -> StructContext {
        let handle = self.struct_handle_at(idx);
        StructContext {
            module_id: self.module_id_by_index(handle.module),
            struct_name: self.identifier_at(handle.name).to_owned(),
        }
    }

    pub fn struct_context_by_def_index(&self, idx: StructDefinitionIndex) -> StructContext {
        let handle = self.struct_handle_at(self.struct_def_at(idx).struct_handle);
        StructContext {
            module_id: self.module_id_by_index(handle.module),
            struct_name: self.identifier_at(handle.name).to_owned(),
        }
    }

    pub fn struct_context_by_generic_index(
        &self,
        idx: StructDefInstantiationIndex,
    ) -> StructContext {
        let instantiation = self.struct_instantiation_at(idx);
        self.struct_context_by_def_index(instantiation.def)
    }

    pub fn struct_context_by_field_index(&self, idx: FieldHandleIndex) -> StructContext {
        let handle = self.field_handle_at(idx);
        self.struct_context_by_def_index(handle.owner)
    }

    pub fn struct_context_by_field_generic_index(
        &self,
        idx: FieldInstantiationIndex,
    ) -> StructContext {
        let instantiation = self.field_instantiation_at(idx);
        self.struct_context_by_field_index(instantiation.handle)
    }

    pub fn function_instantiation_signature_by_generic_index(
        &self,
        idx: FunctionInstantiationIndex,
    ) -> &Signature {
        let instantiation = self.function_instantiation_at(idx);
        self.signature_at(instantiation.type_parameters)
    }

    pub fn struct_instantiation_signature_by_generic_index(
        &self,
        idx: StructDefInstantiationIndex,
    ) -> &Signature {
        let instantiation = self.struct_instantiation_at(idx);
        self.signature_at(instantiation.type_parameters)
    }

    pub fn struct_instantiation_signature_by_field_generic_index(
        &self,
        idx: FieldInstantiationIndex,
    ) -> &Signature {
        let instantiation = self.field_instantiation_at(idx);
        self.signature_at(instantiation.type_parameters)
    }

    pub fn code_unit(&self) -> &CodeUnit {
        match self {
            ExecUnit::Script(unit) => unit.code(),
            ExecUnit::Module(_, func) => (&func.code)
                .as_ref()
                .expect("A tracked function must have a code unit"),
        }
    }

    fn params_signature(&self) -> &Signature {
        match self {
            ExecUnit::Script(unit) => self.signature_at(unit.as_inner().parameters),
            ExecUnit::Module(_, func) => {
                self.signature_at(self.function_handle_at(func.function).parameters)
            }
        }
    }

    fn locals_signature(&self) -> &Signature {
        self.signature_at(self.code_unit().locals)
    }

    // NOTE: locals in code unit is not the same as function locals
    pub fn local_signature_token(&self, idx: LocalIndex) -> &SignatureToken {
        let i = idx as usize;

        let params_sig = self.params_signature();
        if i < params_sig.len() {
            params_sig.0.get(i).unwrap()
        } else {
            let locals_sig = self.locals_signature();
            locals_sig.0.get(i - params_sig.len()).unwrap()
        }
    }

    pub fn get_code_context(&self) -> CodeContext {
        match self {
            ExecUnit::Script(_) => CodeContext::Script,
            ExecUnit::Module(unit, func) => CodeContext::Module {
                module_id: unit.self_id(),
                function_name: unit
                    .identifier_at(unit.function_handle_at(func.function).name)
                    .to_owned(),
            },
        }
    }
}

// Flattened type tracking
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExecTypeArg {
    Bool,
    U8,
    U64,
    U128,
    Address,
    Signer,
    Vector {
        element_type: Box<ExecTypeArg>,
    },
    Struct {
        context: StructContext,
        type_args: Vec<ExecTypeArg>,
    },
    Reference {
        referred_type: Box<ExecTypeArg>,
    },
    MutableReference {
        referred_type: Box<ExecTypeArg>,
    },
    TypeParameter {
        param_index: TypeParameterIndex,
        actual_type: Box<ExecTypeArg>,
    },
}

impl fmt::Display for ExecTypeArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExecTypeArg::Bool => write!(f, "bool"),
            ExecTypeArg::U8 => write!(f, "u8"),
            ExecTypeArg::U64 => write!(f, "u64"),
            ExecTypeArg::U128 => write!(f, "u128"),
            ExecTypeArg::Address => write!(f, "address"),
            ExecTypeArg::Signer => write!(f, "signer"),
            ExecTypeArg::Vector { element_type } => write!(f, "vector<{}>", element_type),
            ExecTypeArg::Struct { context, type_args } => {
                write!(f, "struct {}", context)?;
                if !type_args.is_empty() {
                    write!(f, "<")?;
                    write!(f, "{}", type_args.get(0).unwrap())?;
                    for i in 1..type_args.len() {
                        write!(f, ", {}", type_args.get(i).unwrap())?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            ExecTypeArg::Reference { referred_type } => write!(f, "&{}", referred_type),
            ExecTypeArg::MutableReference { referred_type } => write!(f, "&mut {}", referred_type),
            ExecTypeArg::TypeParameter {
                param_index,
                actual_type,
            } => write!(f, "#{}-{}", param_index, actual_type),
        }
    }
}

impl ExecTypeArg {
    pub fn convert_from_type_tag(tag: &TypeTag) -> ExecTypeArg {
        match tag {
            TypeTag::Bool => ExecTypeArg::Bool,
            TypeTag::U8 => ExecTypeArg::U8,
            TypeTag::U64 => ExecTypeArg::U64,
            TypeTag::U128 => ExecTypeArg::U128,
            TypeTag::Address => ExecTypeArg::Address,
            TypeTag::Signer => ExecTypeArg::Signer,
            TypeTag::Vector(element_tag) => ExecTypeArg::Vector {
                element_type: Box::new(ExecTypeArg::convert_from_type_tag(element_tag.as_ref())),
            },
            TypeTag::Struct(struct_tag) => ExecTypeArg::Struct {
                context: StructContext {
                    module_id: struct_tag.module_id(),
                    struct_name: struct_tag.name.clone(),
                },
                type_args: struct_tag
                    .type_params
                    .iter()
                    .map(ExecTypeArg::convert_from_type_tag)
                    .collect(),
            },
        }
    }

    pub fn convert_from_signature_token(
        token: &SignatureToken,
        exec_unit: &ExecUnit,
        type_args: &[ExecTypeArg],
    ) -> ExecTypeArg {
        match token {
            SignatureToken::Bool => ExecTypeArg::Bool,
            SignatureToken::U8 => ExecTypeArg::U8,
            SignatureToken::U64 => ExecTypeArg::U64,
            SignatureToken::U128 => ExecTypeArg::U128,
            SignatureToken::Address => ExecTypeArg::Address,
            SignatureToken::Signer => ExecTypeArg::Signer,
            SignatureToken::Vector(element_sig) => ExecTypeArg::Vector {
                element_type: Box::new(ExecTypeArg::convert_from_signature_token(
                    element_sig.as_ref(),
                    exec_unit,
                    type_args,
                )),
            },
            SignatureToken::Struct(handle_index) => ExecTypeArg::Struct {
                context: exec_unit.struct_context_by_handle_index(*handle_index),
                type_args: vec![],
            },
            SignatureToken::StructInstantiation(handle_index, inst_tokens) => ExecTypeArg::Struct {
                context: exec_unit.struct_context_by_handle_index(*handle_index),
                type_args: inst_tokens
                    .iter()
                    .map(|inst_token| {
                        ExecTypeArg::convert_from_signature_token(inst_token, exec_unit, type_args)
                    })
                    .collect(),
            },
            SignatureToken::Reference(referred_sig) => ExecTypeArg::Reference {
                referred_type: Box::new(ExecTypeArg::convert_from_signature_token(
                    referred_sig.as_ref(),
                    exec_unit,
                    type_args,
                )),
            },
            SignatureToken::MutableReference(referred_sig) => ExecTypeArg::MutableReference {
                referred_type: Box::new(ExecTypeArg::convert_from_signature_token(
                    referred_sig.as_ref(),
                    exec_unit,
                    type_args,
                )),
            },
            SignatureToken::TypeParameter(index) => {
                let indexed_type = type_args.get(*index as usize).unwrap();
                match indexed_type {
                    ExecTypeArg::TypeParameter { .. } => indexed_type.clone(),
                    _ => ExecTypeArg::TypeParameter {
                        param_index: *index,
                        actual_type: Box::new(indexed_type.clone()),
                    },
                }
            }
        }
    }
}

/// Collect and hold all environmental information needed by various
/// components of the symbolic executor.
#[derive(Clone, Debug)]
pub(crate) struct SymSetup<'a> {
    loaded_modules: HashMap<ModuleId, &'a CompiledModule>,
    defined_structs: HashMap<ModuleId, HashMap<Identifier, StructInfo<'a>>>,
    tracked_script: ExecUnit<'a>,
    tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
}

impl<'a> SymSetup<'a> {
    pub fn new(
        script: &'a CompiledScript,
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
            tracked_script: ExecUnit::Script(script),
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
            CodeContext::Script => Some(&self.tracked_script),
            CodeContext::Module {
                module_id,
                function_name,
            } => self
                .tracked_functions
                .get(module_id)
                .map(|func_map| func_map.get(function_name))
                .flatten(),
        }
    }

    pub fn get_struct_info_by_context(&self, context: &StructContext) -> Option<&StructInfo> {
        self.defined_structs
            .get(&context.module_id)
            .map(|struct_map| struct_map.get(&context.struct_name))
            .flatten()
    }

    // checkers
    fn check_defined_structs(&self) {
        // check that all indirect structs are also included
        for (module_id, module_structs) in self.defined_structs.iter() {
            let module = self.loaded_modules.get(module_id).unwrap();
            for struct_fields in module_structs.values() {
                if let StructInfo::Declared { field_map, .. } = struct_fields {
                    for field_type in field_map.values() {
                        self.check_defined_structs_field_signature_token(module, &field_type.0);
                    }
                }
            }
        }
    }

    fn check_defined_structs_field_signature_token(
        &self,
        module: &'a CompiledModule,
        token: &SignatureToken,
    ) {
        match token {
            SignatureToken::Bool
            | SignatureToken::U8
            | SignatureToken::U64
            | SignatureToken::U128
            | SignatureToken::Address
            | SignatureToken::Signer
            | SignatureToken::TypeParameter(_) => {}
            SignatureToken::Vector(element_sig) => {
                self.check_defined_structs_field_signature_token(module, element_sig.as_ref())
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
                self.check_defined_structs_field_signature_token(module, referred_sig.as_ref())
            }
        }
    }

    // struct
    fn collect_defined_structs(
        modules: &[&'a CompiledModule],
    ) -> HashMap<ModuleId, HashMap<Identifier, StructInfo<'a>>> {
        let mut defined_structs = HashMap::new();

        for module in modules {
            let mut module_structs = HashMap::new();
            for struct_def in module.struct_defs() {
                let struct_handle = module.struct_handle_at(struct_def.struct_handle);
                let struct_name = module.identifier_at(struct_handle.name).to_owned();

                let struct_fields = match &struct_def.field_information {
                    StructFieldInformation::Native => StructInfo::Native,
                    StructFieldInformation::Declared(field_defs) => StructInfo::Declared {
                        field_vec: field_defs
                            .iter()
                            .map(|field_def| module.identifier_at(field_def.name).to_owned())
                            .collect(),
                        field_map: field_defs
                            .iter()
                            .map(|field_def| {
                                (
                                    module.identifier_at(field_def.name).to_owned(),
                                    &field_def.signature,
                                )
                            })
                            .collect(),
                    },
                };

                let exists = module_structs.insert(struct_name, struct_fields);
                debug_assert!(exists.is_none());
            }

            let exists = defined_structs.insert(module.self_id(), module_structs);
            debug_assert!(exists.is_none());
        }

        defined_structs
    }

    fn collect_involved_structs_recursive(
        &self,
        context: &StructContext,
        inst_tokens: &[SignatureToken],
        exec_unit: &ExecUnit,
        type_args: &[ExecTypeArg],
        involved_structs: &mut HashMap<StructContext, HashSet<Vec<ExecTypeArg>>>,
    ) {
        let variants = involved_structs
            .entry(context.clone())
            .or_insert_with(HashSet::new);

        let inst_args: Vec<ExecTypeArg> = inst_tokens
            .iter()
            .map(|token| ExecTypeArg::convert_from_signature_token(token, exec_unit, type_args))
            .collect();

        if variants.insert(inst_args.clone()) {
            // recursively handle the fields in this struct
            let struct_info = self.get_struct_info_by_context(context).unwrap();
            match struct_info {
                StructInfo::Native => {}
                StructInfo::Declared { field_map, .. } => {
                    for field_type in field_map.values() {
                        self.collect_involved_structs_in_signature_token(
                            &field_type.0,
                            exec_unit,
                            // when analyzing struct fields, the
                            // type_args should be updated to the
                            // inst_args, as inst_args now defines
                            // the scope where type_parameters can be
                            // drawn from
                            &inst_args,
                            involved_structs,
                        );
                    }
                }
            }
        }
    }

    fn collect_involved_structs_in_signature_token(
        &self,
        token: &SignatureToken,
        exec_unit: &ExecUnit,
        type_args: &[ExecTypeArg],
        involved_structs: &mut HashMap<StructContext, HashSet<Vec<ExecTypeArg>>>,
    ) {
        match token {
            SignatureToken::Bool
            | SignatureToken::U8
            | SignatureToken::U64
            | SignatureToken::U128
            | SignatureToken::Address
            | SignatureToken::Signer
            | SignatureToken::TypeParameter(_) => {}
            SignatureToken::Vector(element_sig) => {
                self.collect_involved_structs_in_signature_token(
                    element_sig.as_ref(),
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            SignatureToken::Struct(handle_index) => {
                let context = exec_unit.struct_context_by_handle_index(*handle_index);
                self.collect_involved_structs_recursive(
                    &context,
                    &[],
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            SignatureToken::StructInstantiation(handle_index, inst_tokens) => {
                let context = exec_unit.struct_context_by_handle_index(*handle_index);
                self.collect_involved_structs_recursive(
                    &context,
                    inst_tokens,
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            SignatureToken::Reference(referred_sig)
            | SignatureToken::MutableReference(referred_sig) => {
                self.collect_involved_structs_in_signature_token(
                    referred_sig.as_ref(),
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
        }
    }

    pub fn collect_involved_structs_in_instruction(
        &self,
        instruction: &Bytecode,
        exec_unit: &ExecUnit,
        type_args: &[ExecTypeArg],
        involved_structs: &mut HashMap<StructContext, HashSet<Vec<ExecTypeArg>>>,
    ) {
        match instruction {
            Bytecode::CopyLoc(local_index)
            | Bytecode::MoveLoc(local_index)
            | Bytecode::StLoc(local_index)
            | Bytecode::MutBorrowLoc(local_index)
            | Bytecode::ImmBorrowLoc(local_index) => {
                let token = exec_unit.local_signature_token(*local_index);
                self.collect_involved_structs_in_signature_token(
                    token,
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            Bytecode::Pack(struct_def_index)
            | Bytecode::Unpack(struct_def_index)
            | Bytecode::MutBorrowGlobal(struct_def_index)
            | Bytecode::ImmBorrowGlobal(struct_def_index)
            | Bytecode::Exists(struct_def_index)
            | Bytecode::MoveFrom(struct_def_index)
            | Bytecode::MoveTo(struct_def_index) => {
                let context = exec_unit.struct_context_by_def_index(*struct_def_index);
                self.collect_involved_structs_recursive(
                    &context,
                    &[],
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            Bytecode::PackGeneric(struct_inst_index)
            | Bytecode::UnpackGeneric(struct_inst_index)
            | Bytecode::MutBorrowGlobalGeneric(struct_inst_index)
            | Bytecode::ImmBorrowGlobalGeneric(struct_inst_index)
            | Bytecode::ExistsGeneric(struct_inst_index)
            | Bytecode::MoveFromGeneric(struct_inst_index)
            | Bytecode::MoveToGeneric(struct_inst_index) => {
                let context = exec_unit.struct_context_by_generic_index(*struct_inst_index);
                let inst_sig =
                    exec_unit.struct_instantiation_signature_by_generic_index(*struct_inst_index);
                self.collect_involved_structs_recursive(
                    &context,
                    &inst_sig.0,
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            Bytecode::MutBorrowField(field_index) | Bytecode::ImmBorrowField(field_index) => {
                let context = exec_unit.struct_context_by_field_index(*field_index);
                self.collect_involved_structs_recursive(
                    &context,
                    &[],
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            Bytecode::MutBorrowFieldGeneric(field_inst_index)
            | Bytecode::ImmBorrowFieldGeneric(field_inst_index) => {
                let context = exec_unit.struct_context_by_field_generic_index(*field_inst_index);
                let inst_sig = exec_unit
                    .struct_instantiation_signature_by_field_generic_index(*field_inst_index);
                self.collect_involved_structs_recursive(
                    &context,
                    &inst_sig.0,
                    exec_unit,
                    type_args,
                    involved_structs,
                );
            }
            _ => {}
        }
    }
}
