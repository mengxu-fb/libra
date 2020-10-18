// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::collections::HashMap;

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

/// unify script and module accesses
pub(crate) enum ExecUnit<'a> {
    Script(&'a CompiledScript),
    Module(&'a CompiledModule, &'a FunctionDefinition),
}

impl ExecUnit<'_> {
    pub fn module_handle_at(&self, idx: ModuleHandleIndex) -> &ModuleHandle {
        match self {
            ExecUnit::Script(unit) => unit.module_handle_at(idx),
            ExecUnit::Module(unit, _) => unit.module_handle_at(idx),
        }
    }

    pub fn function_handle_at(&self, idx: FunctionHandleIndex) -> &FunctionHandle {
        match self {
            ExecUnit::Script(unit) => unit.function_handle_at(idx),
            ExecUnit::Module(unit, _) => unit.function_handle_at(idx),
        }
    }

    pub fn function_instantiation_at(
        &self,
        idx: FunctionInstantiationIndex,
    ) -> &FunctionInstantiation {
        match self {
            ExecUnit::Script(unit) => unit.function_instantiation_at(idx),
            ExecUnit::Module(unit, _) => unit.function_instantiation_at(idx),
        }
    }

    pub fn address_identifier_at(&self, idx: AddressIdentifierIndex) -> &AccountAddress {
        match self {
            ExecUnit::Script(unit) => unit.address_identifier_at(idx),
            ExecUnit::Module(unit, _) => unit.address_identifier_at(idx),
        }
    }

    pub fn identifier_at(&self, idx: IdentifierIndex) -> &IdentStr {
        match self {
            ExecUnit::Script(unit) => unit.identifier_at(idx),
            ExecUnit::Module(unit, _) => unit.identifier_at(idx),
        }
    }

    pub fn module_id_for_handle(&self, handle: &ModuleHandle) -> ModuleId {
        ModuleId::new(
            *self.address_identifier_at(handle.address),
            self.identifier_at(handle.name).to_owned(),
        )
    }

    pub fn code_unit(&self) -> &CodeUnit {
        match self {
            ExecUnit::Script(unit) => unit.code(),
            ExecUnit::Module(_, func) => (&func.code)
                .as_ref()
                .expect("A tracked function must have a code unit"),
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

    pub fn is_function_tracked(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        self.tracked_functions
            .get(module_id)
            .map_or(false, |func_set| func_set.get(func_id).is_some())
    }
}
