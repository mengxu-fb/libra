// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::collections::BTreeMap;

use move_core_types::{
    account_address::AccountAddress,
    effects::{ChangeSet, Event},
    language_storage::{ModuleId, StructTag},
};
use move_vm_runtime::data_cache::RemoteCache;
use vm::{
    errors::{PartialVMResult, VMResult},
    file_format::CompiledModule,
};

/// An in-memory data store implementation
#[derive(Clone, Default)]
pub(crate) struct MoveDataStore {
    resources: BTreeMap<AccountAddress, BTreeMap<StructTag, Vec<u8>>>,
    modules: BTreeMap<ModuleId, Vec<u8>>,
    events: BTreeMap<Vec<u8>, Vec<Event>>,
}

impl MoveDataStore {
    /// Apply the change set generated from a script execution.
    pub fn apply_change_set(&mut self, change_set: ChangeSet) -> Result<()> {
        for (addr, account) in change_set.accounts {
            if !account.modules.is_empty() {
                bail!("Unexpected modules in change set");
            }
            for (struct_tag, blob_opt) in account.resources {
                match blob_opt {
                    Some(blob) => self.save_resource(addr, struct_tag, blob),
                    None => self.delete_resource(addr, struct_tag)?,
                }
            }
        }
        Ok(())
    }

    pub fn save_event(&mut self, event: Event) -> Result<()> {
        let key = event.0.clone();
        self.events.entry(key).or_insert_with(Vec::new).push(event);
        Ok(())
    }

    pub fn save_module(&mut self, module: &CompiledModule) -> Result<()> {
        let mut bytes = vec![];
        module.serialize(&mut bytes)?;
        self.modules.insert(module.self_id(), bytes);
        Ok(())
    }

    //
    // utilities to save resources to storage
    //

    fn save_resource(&mut self, addr: AccountAddress, tag: StructTag, bytes: Vec<u8>) {
        self.resources
            .entry(addr)
            .or_insert_with(BTreeMap::new)
            .insert(tag, bytes);
    }

    fn delete_resource(&mut self, addr: AccountAddress, tag: StructTag) -> Result<()> {
        if self
            .resources
            .get_mut(&addr)
            .map(|v| v.remove(&tag))
            .is_none()
        {
            bail!("Resource does not exist at {}::{}", addr, tag);
        }
        Ok(())
    }
}

impl RemoteCache for MoveDataStore {
    fn get_module(&self, module_id: &ModuleId) -> VMResult<Option<Vec<u8>>> {
        Ok(self.modules.get(module_id).cloned())
    }

    fn get_resource(
        &self,
        address: &AccountAddress,
        tag: &StructTag,
    ) -> PartialVMResult<Option<Vec<u8>>> {
        Ok(self
            .resources
            .get(address)
            .and_then(|v| v.get(tag))
            .cloned())
    }
}
