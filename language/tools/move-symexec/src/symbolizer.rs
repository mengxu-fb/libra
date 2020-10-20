// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use log::info;
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

    pub fn show_exec_graph_stats(&self) {
        // show node and edge stats
        info!(
            "{} nodes + {} edges in exec graph",
            self.exec_graph.node_count(),
            self.exec_graph.edge_count()
        );

        // count paths manually
        let path_sets = self.exec_graph.scc_paths_from_entry();
        let path_nums = path_sets
            .values()
            .fold(0, |count, path_set| count + path_set.len());
        info!("{} paths in scc graph (handwritten algorithm)", path_nums);

        // build scc graph
        let scc_graph = self.exec_graph.scc_graph();
        info!(
            "{} paths in scc graph (by petgraph::all_simple_paths)",
            scc_graph.enumerate_paths().len()
        );
    }
}
