// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;

use move_core_types::{account_address::AccountAddress, value::MoveStruct};
use move_model::{
    model::{QualifiedInstId, StructId},
    ty::Type,
};

pub type ResourceKey = QualifiedInstId<StructId>;

pub(crate) fn struct_type_into_resource_key(ty: Type) -> Option<ResourceKey> {
    match ty {
        Type::Struct(module_id, struct_id, struct_insts) => {
            Some(module_id.qualified_inst(struct_id, struct_insts))
        }
        _ => None,
    }
}

pub(crate) fn resource_key_into_struct_type(key: ResourceKey) -> Type {
    let ResourceKey {
        module_id,
        id,
        inst,
    } = key;
    Type::Struct(module_id, id, inst)
}

#[derive(Clone, Default, Eq, PartialEq)]
struct AccountState {
    storage: BTreeMap<ResourceKey, MoveStruct>,
}

impl AccountState {
    fn get_resource(&self, key: &ResourceKey) -> Option<MoveStruct> {
        self.storage.get(key).cloned()
    }

    fn del_resource(&mut self, key: &ResourceKey) -> Option<MoveStruct> {
        self.storage.remove(key)
    }

    fn put_resource(&mut self, key: ResourceKey, val: MoveStruct) -> Option<MoveStruct> {
        self.storage.insert(key, val)
    }

    fn has_resource(&self, key: &ResourceKey) -> bool {
        self.storage.contains_key(key)
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct GlobalState {
    accounts: BTreeMap<AccountAddress, AccountState>,
}

impl GlobalState {
    pub fn get_resource(&self, account: &AccountAddress, key: &ResourceKey) -> Option<MoveStruct> {
        self.accounts
            .get(account)
            .and_then(|account| account.get_resource(key))
    }

    pub fn del_resource(
        &mut self,
        account: &AccountAddress,
        key: &ResourceKey,
    ) -> Option<MoveStruct> {
        self.accounts
            .get_mut(account)
            .and_then(|account| account.del_resource(key))
    }

    pub fn put_resource(
        &mut self,
        account: &AccountAddress,
        key: ResourceKey,
        val: MoveStruct,
    ) -> Option<MoveStruct> {
        self.accounts
            .entry(*account)
            .or_insert_with(AccountState::default)
            .put_resource(key, val)
    }

    pub fn has_resource(&self, account: &AccountAddress, key: &ResourceKey) -> bool {
        self.accounts
            .get(account)
            .map_or(false, |account| account.has_resource(key))
    }
}
