// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use anyhow::Result;
use log::{debug, warn};
use serde_json::{self, json};
use std::{collections::HashMap, fs::File, io::Write};

use move_core_types::{account_address::AccountAddress, language_storage::TypeTag};
use vm::file_format::CompiledScript;

use crate::{
    sym_exec_graph::{ExecGraph, ExecRefGraph, ExecSccGraph, ExecWalker},
    sym_setup::{ExecTypeArg, SymSetup},
    sym_type_graph::TypeGraph,
    sym_vm::SymVM,
    sym_vm_types::SymTransactionArgument,
    utils,
};

/// The default file name for the exec graph
const EXEC_GRAPH_DOT_FILE: &str = "exec_graph.dot";
const EXEC_GRAPH_STATS_FILE: &str = "exec_graph_stats.json";

/// Limit of path count
const EXEC_GRAPH_PATH_ENUMERATION_LIMIT: u128 = std::u16::MAX as u128;

/// The symbolizer
#[derive(Clone, Debug)]
pub(crate) struct MoveSymbolizer<'a> {
    workdir: String,
    setup: &'a SymSetup<'a>,
    script: &'a CompiledScript,
    type_args: Vec<ExecTypeArg>,
    exec_graph: ExecGraph,
    type_graph: TypeGraph,
}

impl<'a> MoveSymbolizer<'a> {
    pub fn new(
        workdir: String,
        setup: &'a SymSetup<'a>,
        script: &'a CompiledScript,
        type_tags: &[TypeTag],
    ) -> Result<Self> {
        // prepare the directory
        utils::maybe_recreate_dir(&workdir)?;

        // convert type args
        let type_args: Vec<ExecTypeArg> = type_tags
            .iter()
            .map(ExecTypeArg::convert_from_type_tag)
            .collect();

        // build execution graph
        let exec_graph = ExecGraph::new(setup, script, &type_args);

        // build type graph
        let type_graph = MoveSymbolizer::discover_structs(setup, &exec_graph);

        // done
        Ok(Self {
            workdir,
            setup,
            script,
            type_args,
            exec_graph,
            type_graph,
        })
    }

    pub fn save_exec_graph_as_dot(&self) -> Result<()> {
        let path = join_path_items!(&self.workdir, EXEC_GRAPH_DOT_FILE);
        let mut file = File::create(path)?;
        file.write_all(self.exec_graph.to_dot().as_bytes())?;
        Ok(())
    }

    pub fn save_exec_graph_stats(&self) -> Result<()> {
        // show node and edge stats
        debug!(
            "{} nodes + {} edges in exec graph",
            self.exec_graph.node_count(),
            self.exec_graph.edge_count()
        );

        // build the ref graph
        let ref_graph = ExecRefGraph::from_graph(&self.exec_graph);

        // build the scc graph
        let scc_graph = ExecSccGraph::new(&ref_graph);

        // count paths with our handwritten algorithm
        let path_count = scc_graph.count_paths();
        debug!("{} paths in scc graph", path_count);

        // cross-checking with the petgraph's algorithm
        if path_count > EXEC_GRAPH_PATH_ENUMERATION_LIMIT {
            warn!("path count exceeds limit, will not enumerate paths");
        } else {
            assert_eq!(path_count, scc_graph.enumerate_paths().len() as u128);
        }

        // construct the stats json
        let stats = json!({
            "node_count": self.exec_graph.node_count(),
            "edge_count": self.exec_graph.edge_count(),
            "path_count": path_count.to_string(),  // u128 not supported
        });

        // save the stats to file
        let path = join_path_items!(&self.workdir, EXEC_GRAPH_STATS_FILE);
        serde_json::to_writer(&File::create(path)?, &stats)?;

        // done
        Ok(())
    }

    fn discover_structs(setup: &SymSetup, exec_graph: &ExecGraph) -> TypeGraph {
        // holds the struct types we have discovered so far
        let mut involved_structs = HashMap::new();
        let mut analyzed_structs = HashMap::new();

        // find all places that may use a struct type
        let mut walker = ExecWalker::new(exec_graph);
        while let Some((_, exec_block)) = walker.next() {
            let exec_unit = setup
                .get_exec_unit_by_context(&exec_block.code_context)
                .unwrap();
            for instruction in exec_block.instructions.iter() {
                setup.collect_involved_structs_in_instruction(
                    instruction,
                    exec_unit,
                    &exec_block.type_args,
                    &mut involved_structs,
                    &mut analyzed_structs,
                );
            }
        }

        // done
        TypeGraph::new(involved_structs, analyzed_structs)
    }

    pub fn execute(&self, signers: &[AccountAddress], sym_args: &[SymTransactionArgument]) {
        // prepare the vm
        let vm = SymVM::new(&self.type_graph);

        // do the interpretation
        vm.interpret(
            self.script,
            &self.type_args,
            &self.exec_graph,
            signers,
            sym_args,
        );
    }
}
