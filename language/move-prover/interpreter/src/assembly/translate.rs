// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use bytecode::function_target_pipeline::FunctionTargetsHolder;
use move_model::model::GlobalEnv;

use crate::assembly::ast::Assembly;

/// Translate function targets into assembly
pub fn translate(_env: &GlobalEnv, _targets: &FunctionTargetsHolder) -> Assembly {
    Assembly {}
}
