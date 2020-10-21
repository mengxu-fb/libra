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
        IdentifierIndex, ModuleHandle, ModuleHandleIndex,
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

/// unify script and module accesses
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

    pub fn get_code_condext(&self) -> CodeContext {
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
    tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>,
}

impl<'a> SymSetup<'a> {
    pub fn new(tracked_functions: HashMap<ModuleId, HashMap<Identifier, ExecUnit<'a>>>) -> Self {
        Self { tracked_functions }
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
}
