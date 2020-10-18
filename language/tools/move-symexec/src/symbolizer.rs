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
        debug!(
            "{} nodes + {} edges in exec graph",
            exec_graph.node_count(),
            exec_graph.edge_count()
        );

        Self { exec_graph }
    }
}
