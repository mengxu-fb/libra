// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use log::{info, warn};
use std::{fs::File, io::Write};

use vm::file_format::CompiledScript;

use crate::{sym_exec_graph::ExecGraph, sym_setup::SymSetup, utils};

/// The default file name for the exec graph
const EXEC_GRAPH_NAME: &str = "exec_graph.dot";

/// Limit of path count
const EXEC_GRAPH_PATH_ENUMERATION_LIMIT: usize = std::u32::MAX as usize;

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

        // build the scc graph
        let scc_graph = self.exec_graph.scc_graph();

        // count paths with our handwritten algorithm
        let path_count = self.exec_graph.scc_path_count();
        if path_count > EXEC_GRAPH_PATH_ENUMERATION_LIMIT {
            warn!("Path count exceeding limit, will not try to enumerate paths");
        } else {
            assert_eq!(path_count, scc_graph.enumerate_paths().len());
        }
        info!("{} paths in scc graph", path_count);
    }
}
