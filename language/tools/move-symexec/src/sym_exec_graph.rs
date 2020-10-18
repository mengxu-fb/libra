// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::DfsPostOrder,
    EdgeDirection,
};
use std::collections::HashMap;

use bytecode_verifier::control_flow_graph::{BlockId, ControlFlowGraph, VMControlFlowGraph};
use vm::file_format::{Bytecode, CodeOffset, CompiledScript};

use crate::sym_setup::{CodeContext, ExecUnit, SymSetup};

/// The following classes aim for building an extended control-flow
/// graph that encloses both script and module CFGs, i.e., a super
/// graph that has CFGs connected by the call graph.

/// This is the basic block (i.e., the node) in the super-CFG.
type ExecBlockId = usize;

#[derive(Clone, Debug)]
struct ExecBlock {
    block_id: ExecBlockId,
    code_context: CodeContext,
    instructions: Vec<Bytecode>,
}

impl ExecBlock {
    pub fn new(block_id: ExecBlockId, code_context: CodeContext) -> Self {
        Self {
            block_id,
            code_context,
            instructions: vec![],
        }
    }

    pub fn add_instruction(&mut self, bytecode: Bytecode) {
        self.instructions.push(bytecode);
    }

    pub fn clear_instructions(&mut self) {
        self.instructions.clear();
    }
}

/// This is the control flow (i.e., the edge) in the super-CFG.
type ExecFlowId = usize;

#[derive(Clone, Debug)]
enum ExecFlowType {
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

#[derive(Clone, Debug)]
struct ExecFlow {
    flow_id: ExecFlowId,
    flow_type: ExecFlowType,
}

/// This is the super-CFG graph representation.
#[derive(Clone, Debug)]
pub(crate) struct ExecGraph {
    graph: Graph<ExecBlock, ExecFlow>,
    node_map: HashMap<ExecBlockId, NodeIndex>,
    edge_map: HashMap<ExecFlowId, EdgeIndex>,
}

impl ExecGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
        }
    }

    fn incorporate(
        &mut self,
        exec_unit: &ExecUnit,
        call_stack: &mut Vec<(CodeContext, CodeOffset)>,
        setup: &SymSetup,
    ) {
        let code_context = exec_unit.get_code_condext();
        let instructions = &exec_unit.code_unit().code;
        let cfg = VMControlFlowGraph::new(instructions);

        // iterate CFG: build blocks only in this iteration
        for block_id in cfg_reverse_postorder_dfs(&cfg, instructions) {
            // create the block
            let exec_block_id = self.graph.node_count();
            let mut exec_block = ExecBlock::new(exec_block_id, code_context.clone());

            // scan instructions
            for offset in cfg.block_start(block_id)..=cfg.block_end(block_id) {
                let instruction = &instructions[offset as usize];
                exec_block.add_instruction(instruction.clone());

                #[cfg(debug_assertions)]
                // ensure that all branch instructions are terminations
                // in the block
                if instruction.is_branch() {
                    assert_eq!(offset, cfg.block_end(block_id));
                }

                // see if we are going to call into another exec unit
                let next_unit_opt = match instruction {
                    Bytecode::Call(func_handle_index) => setup.get_exec_unit_by_context(
                        &exec_unit.code_context_by_index(*func_handle_index),
                    ),
                    Bytecode::CallGeneric(func_instantiation_index) => setup
                        .get_exec_unit_by_context(
                            &exec_unit.code_context_by_generic_index(*func_instantiation_index),
                        ),
                    _ => None,
                };

                if let Some(next_unit) = next_unit_opt {
                    // check recursion
                    let next_context = next_unit.get_code_condext();
                    if !call_stack
                        .iter()
                        .any(|(call_context, _)| call_context == &next_context)
                    {
                        // done with exploration of this exec block
                        let node_index = self.graph.add_node(exec_block.clone());
                        self.node_map.insert(exec_block_id, node_index);

                        // clear this exec block so that it can be
                        // reused to host the rest of instructions in
                        // current basic block, after the call.
                        exec_block.clear_instructions();

                        // call into the next execution unit
                        call_stack.push((code_context.clone(), offset));
                        self.incorporate(next_unit, call_stack, setup);
                    }
                    // otherwise, it is recursion, we will not further
                    // expand the CFG of that function.
                }
            }

            // add block to graph
            let node_index = self.graph.add_node(exec_block);
            self.node_map.insert(exec_block_id, node_index);
        }
    }

    pub fn new(setup: &SymSetup, script: &CompiledScript) -> Self {
        // make the script an ExecUnit
        let init_unit = ExecUnit::Script(script);

        // start symbolization from here
        let mut call_stack = vec![];
        let mut exec_graph = ExecGraph::empty();
        exec_graph.incorporate(&init_unit, &mut call_stack, setup);

        // done
        exec_graph
    }

    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }
}

// CFG / graph utils

/// Convert a CFG into generic graphs so we can benefit from various
/// graph algorithms, in particular, the DfsPostOrder visit algorithm,
/// in the petgraph crate.
fn cfg_to_generic_graph(
    cfg: &VMControlFlowGraph,
    instructions: &[Bytecode],
) -> (Graph<BlockId, ()>, NodeIndex) {
    // convert a CFG into a generic graph provided by petgraph
    let mut graph = Graph::new();
    let blocks = cfg.blocks();

    // add nodes
    let node_map: HashMap<BlockId, NodeIndex> = blocks
        .iter()
        .map(|block_id| (*block_id, graph.add_node(*block_id)))
        .collect();

    // add edges
    blocks.iter().for_each(|block_id| {
        cfg.successors(*block_id).iter().for_each(|successor_id| {
            // all nodes added before, we can safely unwrap here
            graph.add_edge(
                *node_map.get(block_id).unwrap(),
                *node_map.get(successor_id).unwrap(),
                (),
            );
        })
    });

    // ensure there is only one unified exit
    let exit_blocks: Vec<BlockId> = blocks
        .into_iter()
        .filter(|block_id| cfg.successors(*block_id).is_empty())
        .collect();

    #[cfg(debug_assertions)]
    // if a basic block has no successors, it must be either
    //  1. a basic block ending with Ret
    //  2. a basic block ending with Abort
    for block_id in exit_blocks.iter() {
        match &instructions[cfg.block_end(*block_id) as usize] {
            Bytecode::Ret => true,
            Bytecode::Abort => false,
            _ => panic!("Invalid termination block in funciton CFG"),
        };
    }

    // If more than one exit blocks found, add an arbitrary unity block
    // and link all Ret blocks to the unity block.
    let exit_node = if exit_blocks.len() != 1 {
        // Note: given how BlockId are assigned, any number >= length of
        // instructions: &[Bytecode] will be safe to use as the BlockId
        // for artificial blocks
        let unity_node = graph.add_node(instructions.len() as BlockId);
        exit_blocks.iter().for_each(|block_id| {
            graph.add_edge(*node_map.get(block_id).unwrap(), unity_node, ());
        });
        unity_node
    } else {
        *node_map.get(exit_blocks.last().unwrap()).unwrap()
    };

    // done
    (graph, exit_node)
}

fn cfg_reverse_postorder_dfs(cfg: &VMControlFlowGraph, instructions: &[Bytecode]) -> Vec<BlockId> {
    let mut result = vec![];

    // build and reverse the CFG
    let (mut graph, exit_node) = cfg_to_generic_graph(cfg, instructions);
    graph.reverse();

    #[cfg(debug_assertions)]
    // check that the exit_node now is the entry node after reversal
    assert_eq!(
        graph
            .edges_directed(exit_node, EdgeDirection::Incoming)
            .count(),
        0
    );

    // Run post-order DFS visitation
    //
    // In reverse-postorder iteration, a node is visited before any of
    // its successor nodes has been visited, except when the successor
    // is reached by a back edge.
    // (Note that this is not the same as preorder.)
    let mut visitor = DfsPostOrder::new(&graph, exit_node);
    while let Some(node) = visitor.next(&graph) {
        let block_id = *graph.node_weight(node).unwrap();
        if block_id == instructions.len() as BlockId {
            // ignore the arbitrary unity block
            continue;
        }
        result.push(block_id);
    }

    // done
    result
}
