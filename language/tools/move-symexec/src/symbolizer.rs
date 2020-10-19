// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use log::debug;
use std::{fs::File, io::Write};

use vm::file_format::CompiledScript;

use crate::{sym_exec_graph::ExecGraph, sym_setup::SymSetup, utils};

/// The default file name for the exec graph
const EXEC_GRAPH_NAME: &str = "exec_graph.dot";

/// The symbolizer
#[derive(Clone, Debug)]
pub(crate) struct MoveSymbolizer {
    workdir: String,
    exec_graph: ExecGraph,
}

impl MoveSymbolizer {
    pub fn new(workdir: String, setup: &SymSetup, script: &CompiledScript) -> Result<Self> {
        // prepare the directory
        utils::maybe_recreate_dir(&workdir)?;

        // build execution graph
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
        Ok(Self {
            workdir,
            exec_graph,
        })
    }

    pub fn save_exec_graph_as_dot(&self) -> Result<()> {
        let path = join_path_items!(&self.workdir, EXEC_GRAPH_NAME);
        let mut file = File::create(path)?;
        file.write_all(self.exec_graph.to_dot().as_bytes())?;
        Ok(())
    }
}
