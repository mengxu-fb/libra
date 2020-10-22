// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use crate::sym_exec_graph::{ExecGraph, ExecWalker};

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {}

impl SymVM {
    pub fn new() -> Self {
        Self {}
    }

    pub fn interpret(&self, exec_graph: &ExecGraph) {
        // run the walker
        let mut walker = ExecWalker::new(exec_graph);
        while walker.next().is_some() {}
    }
}
