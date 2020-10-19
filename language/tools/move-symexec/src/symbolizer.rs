// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use log::debug;

use vm::file_format::CompiledScript;

use crate::{sym_exec_graph::ExecGraph, sym_setup::SymSetup};

/// The symbolizer
#[derive(Clone, Debug)]
pub(crate) struct MoveSymbolizer {
    exec_graph: ExecGraph,
}

impl MoveSymbolizer {
    pub fn new(setup: &SymSetup, script: &CompiledScript) -> Self {
        let exec_graph = ExecGraph::new(setup, script);

        // explore the paths
        let path_sets = exec_graph.scc_paths_from_entry();
        let path_nums = path_sets
            .values()
            .fold(0, |count, path_set| count + path_set.len());
        debug!(
            "{} nodes + {} edges + {} paths in exec graph",
            exec_graph.node_count(),
            exec_graph.edge_count(),
            path_nums
        );

        // done
        Self { exec_graph }
    }
}
