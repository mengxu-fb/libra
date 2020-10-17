// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    algo::tarjan_scc,
    graph::{Graph, NodeIndex},
};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};

use bytecode_verifier::control_flow_graph::{BlockId, ControlFlowGraph, VMControlFlowGraph};
use move_core_types::{
    identifier::{IdentStr, Identifier},
    language_storage::ModuleId,
};
use vm::{
    access::{ModuleAccess, ScriptAccess},
    file_format::{Bytecode, CompiledModule, CompiledScript},
};

use crate::sym_setup::SymSetup;

/// The following classes aim for building an extended control-flow
/// graph that encloses both script and module CFGs, i.e., a super
/// graph that has CFGs connected by the call graph.

/// This is the basic block (i.e., the node) in the super-CFG.
struct ExecBlock {
    module_id: Option<ModuleId>,
    function_id: Identifier,
    instructions: Vec<Bytecode>,
}

impl ExecBlock {
    pub fn new(module_id: Option<ModuleId>, function_id: Identifier) -> Self {
        Self {
            module_id,
            function_id,
            instructions: vec![],
        }
    }

    pub fn add_instruction(&mut self, bytecode: Bytecode) {
        self.instructions.push(bytecode);
    }
}

/// This is the control transition (i.e., the edge) in the super-CFG.
enum ExecTransition {
    /// Fall through: the next instruction is PC + 1
    Fallthrough,

    /// Conditional or unconditional (if condition is None) branch
    Branch {
        bytecode: Bytecode,
        condition: Option<bool>,
    },

    /// Function call
    Call { bytecode: Bytecode },

    /// Function return
    Ret,
}

/// This is the super-CFG graph representation.
pub(crate) struct ExecGraph {}

impl ExecGraph {
    pub fn new(
        setup: &SymSetup,
        script: &CompiledScript,
        tracked_modules: &[CompiledModule],
    ) -> Self {
        // prepare
        // let mut call_stack = vec![];
        // let mut block_stack = vec![];

        // build CFG for the script
        let script_code = script.code();
        let script_cfg = VMControlFlowGraph::new(&script_code.code);

        // TODO: to be removed
        cfg_topological_sort(&script_cfg);
        for module in tracked_modules {
            let module_id = module.self_id();
            for func_def in module.function_defs() {
                let handle = module.function_handle_at(func_def.function);
                let func_id = module.identifier_at(handle.name);
                if !setup.is_function_tracked(&module_id, func_id) {
                    continue;
                }
                if let Some(code_unit) = &func_def.code {
                    let function_cfg = VMControlFlowGraph::new(&code_unit.code);
                    cfg_topological_sort(&function_cfg);
                }
            }
        }

        // done
        Self {}
    }
}

// CFG / graph utils

/// Convert a (partial) CFG into generic graphs so we can benefit
/// from the algorithms, in particular, the SCC calculation algorithm,
/// in the petgraph crate.
fn partial_cfg_to_generic_graph(
    cfg: &VMControlFlowGraph,
    blockset: &HashSet<BlockId>,
) -> Graph<BlockId, ()> {
    // convert a CFG into a generic graph provided by petgraph
    let mut graph = Graph::new();

    // add nodes
    let node_map: HashMap<BlockId, NodeIndex> = blockset
        .iter()
        .map(|block_id| (*block_id, graph.add_node(*block_id)))
        .collect();

    // add edges
    cfg.blocks()
        .iter()
        .filter(|block_id| blockset.contains(block_id))
        .for_each(|block_id| {
            cfg.successors(*block_id)
                .iter()
                .filter(|successor_id| blockset.contains(successor_id))
                .for_each(|successor_id| {
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

/// Iterate a (partial) CFG in DAG-topological order
/// The function first convert the (partial) CFG into a DAG by
/// abstracting each loop into a single component. And then iterate
/// over the DAG in topological order. For each component seen in
/// DAG-iteration, convert loop component into a sub DAG and further
/// iterate that sub-DAG.
fn partial_cfg_topological_sort(
    cfg: &VMControlFlowGraph,
    blockset: &HashSet<BlockId>,
) -> Vec<BlockId> {
    let mut sorted_blocks = vec![];

    // partial CFG convertion
    let graph = partial_cfg_to_generic_graph(&cfg, blockset);

    // iterate in topological order.
    // `petgraph::algo::tarjan_scc` guarantees reverse topological order
    for component in tarjan_scc(&graph).into_iter().rev() {
        if component.len() == 1 {
            // this is a single block
            sorted_blocks.push(*graph.node_weight(*component.last().unwrap()).unwrap());
        } else {
            // this is a loop, sort its blocks and concat the results
            let loop_blockset = HashSet::from_iter(
                component
                    .iter()
                    .map(|node_idx| *graph.node_weight(*node_idx).unwrap()),
            );
            sorted_blocks.extend(partial_cfg_topological_sort(cfg, &loop_blockset));
        }
    }

    // done
    sorted_blocks
}

fn cfg_topological_sort(cfg: &VMControlFlowGraph) -> Vec<BlockId> {
    let blockset = HashSet::from_iter(cfg.blocks());
    partial_cfg_topological_sort(cfg, &blockset)
}
