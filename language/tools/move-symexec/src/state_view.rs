// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use std::collections::HashMap;

use move_core_types::{
    account_address::AccountAddress,
    language_storage::{ModuleId, StructTag},
};
use move_vm_runtime::data_cache::RemoteCache;
use vm::{
    errors::{PartialVMResult, VMResult},
    file_format::CompiledModule,
};

pub(crate) struct InMemoryStateView {
    modules: HashMap<ModuleId, Vec<u8>>,
    resources: HashMap<(AccountAddress, StructTag), Vec<u8>>,
}

impl InMemoryStateView {
    pub fn new(compiled_modules: &[CompiledModule]) -> Result<Self> {
        let mut modules = HashMap::with_capacity(compiled_modules.len());
        for module in compiled_modules {
            let mut module_bytes = vec![];
            module.serialize(&mut module_bytes)?;
            modules.insert(module.self_id(), module_bytes);
        }
        Ok(Self {
            modules,
            resources: HashMap::new(),
        })
    }
}

impl RemoteCache for InMemoryStateView {
    fn get_module(&self, module_id: &ModuleId) -> VMResult<Option<Vec<u8>>> {
        Ok(self.modules.get(module_id).cloned())
    }

    fn get_resource(
        &self,
        address: &AccountAddress,
        tag: &StructTag,
    ) -> PartialVMResult<Option<Vec<u8>>> {
        Ok(self.resources.get(&(*address, tag.clone())).cloned())
    }
}
