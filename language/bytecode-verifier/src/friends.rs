// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use diem_types::vm_status::StatusCode;
use move_core_types::language_storage::ModuleId;
use std::collections::BTreeSet;
use vm::{
    access::ModuleAccess,
    errors::{Location, PartialVMError, PartialVMResult, VMResult},
    file_format::CompiledModule,
};

pub struct FriendChecker {}

impl FriendChecker {
    pub fn verify_module<'a, F>(module: &CompiledModule, module_fetcher: F) -> VMResult<()>
    where
        F: 'a + Fn(&ModuleId) -> PartialVMResult<&'a CompiledModule>,
    {
        Self::verify_module_impl(module, module_fetcher)
            .map_err(|e| e.finish(Location::Module(module.self_id())))
    }

    fn verify_module_impl<'a, F>(module: &CompiledModule, module_fetcher: F) -> PartialVMResult<()>
    where
        F: 'a + Fn(&ModuleId) -> PartialVMResult<&'a CompiledModule>,
    {
        fn check_existence_in_dependency_recursive<'a, F>(
            target_module_ids: &BTreeSet<ModuleId>,
            cursor_module_id: &ModuleId,
            module_fetcher: &F,
            visited_modules: &mut BTreeSet<ModuleId>,
        ) -> PartialVMResult<bool>
        where
            F: 'a + Fn(&ModuleId) -> PartialVMResult<&'a CompiledModule>,
        {
            if target_module_ids.contains(cursor_module_id) {
                return Ok(true);
            }
            if visited_modules.insert(cursor_module_id.clone()) {
                for next in module_fetcher(cursor_module_id)?.immediate_dependency_module_ids() {
                    if check_existence_in_dependency_recursive(
                        target_module_ids,
                        &next,
                        module_fetcher,
                        visited_modules,
                    )? {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        let self_id = module.self_id();
        let friends: BTreeSet<_> = module.immediate_friend_module_ids().into_iter().collect();

        // check that self_id is not in the friend list
        if friends.contains(&self_id) {
            return Err(PartialVMError::new(
                StatusCode::INVALID_FRIEND_DECL_WITH_SELF,
            ));
        }
        // check that only modules in the same address as self_id are in the friend list
        if friends
            .iter()
            .any(|friend| friend.address() != self_id.address())
        {
            return Err(PartialVMError::new(
                StatusCode::INVALID_FRIEND_DECL_WITH_MODULES_OUTSIDE_ADDRESS,
            ));
        }
        // check that any direct/transitive dependenciesl do not show up in the friend list
        let mut visited_modules = BTreeSet::new();
        for dep in module.immediate_dependency_module_ids() {
            if check_existence_in_dependency_recursive(
                &friends,
                &dep,
                &module_fetcher,
                &mut visited_modules,
            )? {
                return Err(PartialVMError::new(
                    StatusCode::INVALID_FRIEND_DECL_WITH_MODULES_IN_DEPENDENCY,
                ));
            }
        }
        Ok(())
    }
}
