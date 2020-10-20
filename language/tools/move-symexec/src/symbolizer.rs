// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use std::{fs::File, io::Write};

use vm::file_format::CompiledScript;

use crate::{
    sym_exec_graph::{ExecGraph, ExecSccGraph},
    sym_setup::SymSetup,
    utils,
};

/// The default file name for the exec graph
const EXEC_GRAPH_NAME: &str = "exec_graph.dot";

/// Limit of path count
const EXEC_GRAPH_PATH_ENUMERATION_LIMIT: u128 = std::u16::MAX as u128;

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
        println!(
            "{} nodes + {} edges in exec graph",
            self.exec_graph.node_count(),
            self.exec_graph.edge_count()
        );

        // build the scc graph
        let scc_graph = ExecSccGraph::new(&self.exec_graph);

        // count paths with our handwritten algorithm
        let path_count = scc_graph.count_paths();
        println!("{} paths in scc graph", path_count);

        // cross-checking with the petgraph's algorithm
        if path_count > EXEC_GRAPH_PATH_ENUMERATION_LIMIT {
            println!("Warning: path count exceeds limit, will not enumerate paths");
        } else {
            assert_eq!(path_count, scc_graph.enumerate_paths().len() as u128);
        }
    }
}
