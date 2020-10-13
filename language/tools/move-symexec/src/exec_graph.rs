// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    algo::tarjan_scc,
    graph::{Graph, NodeIndex},
};
use std::collections::HashMap;

use bytecode_verifier::control_flow_graph::{BlockId, ControlFlowGraph, VMControlFlowGraph};
use vm::{
    access::{ModuleAccess, ScriptAccess},
    file_format::{CompiledModule, CompiledScript},
};

use crate::sym_config::SymConfig;

pub(crate) struct ExecGraph {}

impl ExecGraph {
    pub fn new(
        config: &SymConfig,
        script: &CompiledScript,
        src_modules: &[CompiledModule],
    ) -> Self {
        let script_code = script.code();
        let script_cfg = VMControlFlowGraph::new(&script_code.code);
        cfg_to_dag(&script_cfg);

        for module in src_modules {
            let module_id = module.self_id();
            for func_def in module.function_defs() {
                let handle = module.function_handle_at(func_def.function);
                let func_id = module.identifier_at(handle.name);
                if !config.is_function_tracked(&module_id, func_id) {
                    continue;
                }
                if let Some(code_unit) = &func_def.code {
                    let function_cfg = VMControlFlowGraph::new(&code_unit.code);
                    cfg_to_dag(&function_cfg);
                }
            }
        }

        // done
        Self {}
    }
}

fn cfg_to_generic_graph(cfg: &VMControlFlowGraph) -> Graph<BlockId, ()> {
    // convert a CFG into a generic graph provided by petgraph
    let mut graph = Graph::new();

    // add nodes
    let node_map: HashMap<BlockId, NodeIndex> = cfg
        .blocks()
        .into_iter()
        .map(|block_id| (block_id, graph.add_node(block_id)))
        .collect();

    // add edges
    cfg.blocks().iter().for_each(|block_id| {
        cfg.successors(*block_id).iter().for_each(|successor_id| {
            // all nodes added before, we can safely unwrap here
            graph.add_edge(
                *node_map.get(block_id).unwrap(),
                *node_map.get(successor_id).unwrap(),
                (),
            );
        })
    });

    // done
    graph
}

fn cfg_to_dag(cfg: &VMControlFlowGraph) {
    // convert a CFG into DAG by abstracting loops into a single node
    let graph = cfg_to_generic_graph(&cfg);
    tarjan_scc(&graph).reverse();
}
