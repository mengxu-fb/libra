// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};

use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId,
};

/// Collect and hold all environmental information needed by various
/// components of the symbolic executor.
#[derive(Clone, Debug)]
pub(crate) struct SymSetup {
    tracked_functions: HashMap<ModuleId, HashSet<Identifier>>,
}

impl SymSetup {
    pub fn new(tracked_functions: HashMap<ModuleId, HashSet<Identifier>>) -> Self {
        Self { tracked_functions }
    }

    pub fn num_tracked_functions(&self) -> usize {
        self.tracked_functions.iter().map(|(_, v)| v.len()).sum()
    }

    pub fn is_function_tracked(&self, module_id: &ModuleId, func_id: &IdentStr) -> bool {
        self.tracked_functions
            .get(module_id)
            .map_or(false, |func_set| func_set.contains(func_id))
    }
}
