// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::DfsPostOrder,
    EdgeDirection,
};
use std::collections::{HashMap, HashSet};

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

    pub fn refresh(&mut self, block_id: ExecBlockId) {
        self.block_id = block_id;
        self.instructions.clear();
    }
}

/// This is the control flow (i.e., the edge) in the super-CFG.
#[derive(Clone, Debug)]
enum ExecFlowType {
    /// Fall through: the next instruction is PC + 1
    Fallthrough,
    /// Conditional or unconditional (if condition is None) branch
    Branch(Option<bool>),
    /// Function call
    Call,
    /// Function return
    Ret,
    /// Recursive call
    CallRecursive,
    /// Recursive return
    RetRecursive(ExecBlockId),
}

#[derive(Clone, Debug)]
struct ExecFlow {
    flow_src: ExecBlockId,
    flow_dst: ExecBlockId,
    flow_type: ExecFlowType,
}

impl ExecFlow {
    pub fn new(flow_src: ExecBlockId, flow_dst: ExecBlockId, flow_type: ExecFlowType) -> Self {
        Self {
            flow_src,
            flow_dst,
            flow_type,
        }
    }
}

/// This is the information stored on the call stack
struct CallSite {
    /// context where this call is initiated
    context: CodeContext,
    /// the exec block id for the entry block in this context
    init_block_id: ExecBlockId,
    /// the exec block id where the call is initiated
    call_block_id: ExecBlockId,
}

/// This is the super-CFG graph representation.
#[derive(Clone, Debug)]
pub(crate) struct ExecGraph {
    graph: Graph<ExecBlock, ExecFlow>,
    node_map: HashMap<ExecBlockId, NodeIndex>,
    edge_map: HashMap<(ExecBlockId, ExecBlockId), EdgeIndex>,
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
        call_stack: &mut Vec<CallSite>,
        exit_table: &mut HashMap<ExecBlockId, HashSet<ExecBlockId>>,
        id_counter: &mut ExecBlockId,
        recursions: &mut HashMap<(ExecBlockId, ExecBlockId), ExecBlockId>,
        setup: &SymSetup,
    ) -> HashSet<ExecBlockId> {
        // prepare
        let code_context = exec_unit.get_code_condext();
        let instructions = &exec_unit.code_unit().code;
        let cfg = VMControlFlowGraph::new(instructions);

        let mut inst_map: HashMap<CodeOffset, ExecBlockId> = HashMap::new();
        let mut call_inst_map: HashMap<CodeOffset, (ExecBlockId, HashSet<ExecBlockId>)> =
            HashMap::new();

        // iterate CFG
        for block_id in cfg_reverse_postorder_dfs(&cfg, instructions) {
            // create the block
            let mut exec_block_id = *id_counter;
            *id_counter += 1;
            let mut exec_block = ExecBlock::new(exec_block_id, code_context.clone());

            // scan instructions
            for offset in cfg.block_start(block_id)..=cfg.block_end(block_id) {
                let instruction = &instructions[offset as usize];
                exec_block.add_instruction(instruction.clone());

                // now update the local instruction map
                assert!(inst_map.insert(offset, exec_block.block_id).is_none());

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
                    // record block id
                    let call_site_block_id = exec_block.block_id;

                    // done with exploration of this exec block
                    let node_index = self.graph.add_node(exec_block.clone());
                    assert!(self.node_map.insert(exec_block_id, node_index).is_none());

                    // clear this exec block so that it can be reused
                    // to host the rest of instructions in current basic
                    // block, after the call.
                    exec_block_id = *id_counter;
                    *id_counter += 1;
                    exec_block.refresh(exec_block_id);

                    // record the block id that the call will return to
                    let call_site_ret_block_id = exec_block.block_id;

                    // check recursion and act accordingly
                    let next_context = next_unit.get_code_condext();
                    let rec_candidates: Vec<&CallSite> = call_stack
                        .iter()
                        .filter(|call_site| call_site.context == next_context)
                        .collect();

                    let ret_block_ids = if rec_candidates.is_empty() {
                        // non-recursive: call into the next unit
                        let call_site = CallSite {
                            context: code_context.clone(),
                            init_block_id: *inst_map
                                .get(&cfg.block_start(cfg.entry_block_id()))
                                .unwrap(),
                            call_block_id: call_site_block_id,
                        };
                        call_stack.push(call_site);
                        let ret_blocks = self.incorporate(
                            next_unit, call_stack, exit_table, id_counter, recursions, setup,
                        );
                        assert!(call_stack.pop().is_some());

                        // to build the return edges
                        ret_blocks
                    } else {
                        // recursive call: do not further expand the CFG
                        // of that function, just connect the blocks.

                        // ensure no duplicated context in call stack
                        assert_eq!(rec_candidates.len(), 1);

                        // mark that there should be a pending call edge
                        // from this block to the beginning of the call
                        // site context, and also that the context will
                        // return to the ret block.
                        let rec_call_site = rec_candidates.last().unwrap();
                        assert!(recursions
                            .insert(
                                (call_site_block_id, rec_call_site.init_block_id),
                                call_site_ret_block_id
                            )
                            .is_none());

                        // intentionally return an empty list as the
                        // recursive call site has not finished CFG
                        // exploration, and hence, we do not know all
                        // of their return blocks.
                        HashSet::new()
                    };

                    // add the new block id to the instruction map that
                    // tracks calls specifically
                    assert!(call_inst_map
                        .insert(offset, (call_site_ret_block_id, ret_block_ids))
                        .is_none());
                }
            }

            // add block to graph
            let node_index = self.graph.add_node(exec_block);
            assert!(self.node_map.insert(exec_block_id, node_index).is_none());
        }

        // find entry block id and node
        let cfg_entry_block_id = *inst_map
            .get(&cfg.block_start(cfg.entry_block_id()))
            .unwrap();
        let cfg_entry_node = *self.node_map.get(&cfg_entry_block_id).unwrap();

        // add incoming call edge
        if let Some(call_site) = call_stack.last() {
            // this exec unit is called into, add the call edge
            let call_from_block_id = call_site.call_block_id;
            let call_from_node = *self.node_map.get(&call_from_block_id).unwrap();

            let edge_index = self.graph.add_edge(
                call_from_node,
                cfg_entry_node,
                ExecFlow::new(call_from_block_id, cfg_entry_block_id, ExecFlowType::Call),
            );
            assert!(self
                .edge_map
                .insert((call_from_block_id, cfg_entry_block_id), edge_index)
                .is_none());
        }

        // add branching edges in CFG
        for block_id in cfg.blocks() {
            let term_offset = cfg.block_end(block_id);
            let term_instruction = &instructions[term_offset as usize];

            // derive origin node id
            let origin_block_id = *match term_instruction {
                Bytecode::Call(_) | Bytecode::CallGeneric(_) => call_inst_map
                    .get(&term_offset)
                    .map(|(ret_to_id, _)| ret_to_id)
                    .unwrap_or_else(|| inst_map.get(&term_offset).unwrap()),
                _ => inst_map.get(&term_offset).unwrap(),
            };
            let origin_node_id = *self.node_map.get(&origin_block_id).unwrap();

            for successor_offset in Bytecode::get_successors(term_offset, instructions) {
                // derive successor node id
                let successor_block_id = *inst_map.get(&successor_offset).unwrap();
                let successor_node_id = *self.node_map.get(&successor_block_id).unwrap();

                // derive flow type
                let exec_flow_type = match term_instruction {
                    Bytecode::Branch(_) => ExecFlowType::Branch(None),
                    Bytecode::BrTrue(target_offset) => {
                        ExecFlowType::Branch(Some(successor_offset == *target_offset))
                    }
                    Bytecode::BrFalse(target_offset) => {
                        ExecFlowType::Branch(Some(successor_offset != *target_offset))
                    }
                    _ => {
                        // ensure that these instruction never branch
                        assert!(!term_instruction.is_branch());

                        // fall through type
                        ExecFlowType::Fallthrough
                    }
                };

                // add edge to graph
                let edge_index = self.graph.add_edge(
                    origin_node_id,
                    successor_node_id,
                    ExecFlow::new(origin_block_id, successor_block_id, exec_flow_type),
                );
                assert!(self
                    .edge_map
                    .insert((origin_block_id, successor_block_id), edge_index)
                    .is_none());
            }
        }

        // add returning edges from internal calls
        for (ret_to_id, ret_from_ids) in call_inst_map.values() {
            // derive destination node id
            let ret_to_node_id = *self.node_map.get(ret_to_id).unwrap();

            for ret_from_id in ret_from_ids {
                // derive source node id
                let ret_from_node_id = *self.node_map.get(ret_from_id).unwrap();

                // add edge to graph
                let edge_index = self.graph.add_edge(
                    ret_from_node_id,
                    ret_to_node_id,
                    ExecFlow::new(*ret_from_id, *ret_to_id, ExecFlowType::Ret),
                );
                assert!(self
                    .edge_map
                    .insert((*ret_from_id, *ret_to_id), edge_index)
                    .is_none());
            }
        }

        // collect blocks that ends with Ret
        let exit_points: HashSet<ExecBlockId> = instructions
            .iter()
            .enumerate()
            .filter_map(|(offset, instruction)| match instruction {
                Bytecode::Ret => Some(*inst_map.get(&(offset as CodeOffset)).unwrap()),
                _ => None,
            })
            .collect();
        exit_table.insert(cfg_entry_block_id, exit_points.clone());

        // done
        exit_points
    }

    pub fn new(setup: &SymSetup, script: &CompiledScript) -> Self {
        // make the script an ExecUnit
        let init_unit = ExecUnit::Script(script);

        // start symbolization from here
        let mut call_stack = vec![];
        let mut exit_table = HashMap::new();
        let mut id_counter = 0;
        let mut recursions = HashMap::new();

        let mut exec_graph = ExecGraph::empty();
        exec_graph.incorporate(
            &init_unit,
            &mut call_stack,
            &mut exit_table,
            &mut id_counter,
            &mut recursions,
            setup,
        );

        // add all recursion edges
        for ((call_from_id, call_into_id), ret_into_id) in recursions.iter() {
            // add call edge to graph
            let call_from_node = *exec_graph.node_map.get(call_from_id).unwrap();
            let call_into_node = *exec_graph.node_map.get(call_into_id).unwrap();

            let edge_index = exec_graph.graph.add_edge(
                call_from_node,
                call_into_node,
                ExecFlow::new(*call_from_id, *call_into_id, ExecFlowType::CallRecursive),
            );
            assert!(exec_graph
                .edge_map
                .insert((*call_from_id, *call_into_id), edge_index)
                .is_none());

            // add return edges to graph
            let ret_into_node = *exec_graph.node_map.get(&ret_into_id).unwrap();
            for ret_from_id in exit_table.get(&call_into_id).unwrap() {
                let ret_from_node = *exec_graph.node_map.get(ret_from_id).unwrap();

                let edge_index = exec_graph.graph.add_edge(
                    ret_from_node,
                    ret_into_node,
                    ExecFlow::new(
                        *ret_from_id,
                        *ret_into_id,
                        ExecFlowType::RetRecursive(*call_from_id),
                    ),
                );
                assert!(exec_graph
                    .edge_map
                    .insert((*ret_from_id, *ret_into_id), edge_index)
                    .is_none());
            }
        }

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

    // there are no exit blocks, it means that the whole CFG is an
    // never-ending loop, which should have been filtered out by the
    // func_is_infinite_loop check
    assert!(!exit_blocks.is_empty());

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

pub fn function_is_infinite_loop(instructions: &[Bytecode]) -> bool {
    let cfg = VMControlFlowGraph::new(instructions);
    !cfg.blocks()
        .iter()
        .any(|block_id| cfg.successors(*block_id).is_empty())
}
