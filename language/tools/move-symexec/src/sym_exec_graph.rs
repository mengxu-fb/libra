// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use log::debug;
use petgraph::{
    algo::{all_simple_paths, tarjan_scc, toposort},
    dot::{self, Dot},
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::{Bfs, DfsPostOrder, EdgeRef},
    EdgeDirection,
};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};

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
    /// the starting offset of the instructions in code context
    /// A None code offset means that this must be an arbitrary block
    /// which will host no instructions.
    /// (However, not all arbitrary blocks have None as code_offset,
    /// those that do host instructions will have a valid code_offset)
    code_offset: Option<CodeOffset>,
    instructions: Vec<Bytecode>,
}

impl ExecBlock {
    pub fn new(
        block_id: ExecBlockId,
        code_context: CodeContext,
        code_offset: Option<CodeOffset>,
    ) -> Self {
        Self {
            block_id,
            code_context,
            code_offset,
            instructions: vec![],
        }
    }

    pub fn add_instruction(&mut self, bytecode: Bytecode) {
        self.instructions.push(bytecode);
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
    /// the graph structure
    graph: Graph<ExecBlock, ExecFlow>,
    /// a map mapping block id to node index
    node_map: HashMap<ExecBlockId, NodeIndex>,
    /// a map mapping a pair of connecting blocks to edge index
    edge_map: HashMap<(ExecBlockId, ExecBlockId), EdgeIndex>,
    /// the block id of the graph entry block
    entry_block_id: ExecBlockId,
    /// a list of blocks that are unreachable from the entry block
    dead_block_ids: HashSet<ExecBlockId>,
}

impl ExecGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            entry_block_id: 0,
            dead_block_ids: HashSet::new(),
        }
    }

    fn add_block(&mut self, block: ExecBlock) -> NodeIndex {
        let exec_block_id = block.block_id;
        let node_index = self.graph.add_node(block);
        assert!(self.node_map.insert(exec_block_id, node_index).is_none());
        node_index
    }

    fn get_node_by_block_id(&self, block_id: ExecBlockId) -> NodeIndex {
        *self.node_map.get(&block_id).unwrap()
    }

    fn get_block_id_by_node(&self, node: NodeIndex) -> ExecBlockId {
        self.graph.node_weight(node).unwrap().block_id
    }

    fn get_entry_node(&self) -> NodeIndex {
        self.get_node_by_block_id(self.entry_block_id)
    }

    fn add_flow(
        &mut self,
        src_block_id: ExecBlockId,
        dst_block_id: ExecBlockId,
        flow_type: ExecFlowType,
    ) -> EdgeIndex {
        let edge_index = self.graph.add_edge(
            self.get_node_by_block_id(src_block_id),
            self.get_node_by_block_id(dst_block_id),
            ExecFlow::new(src_block_id, dst_block_id, flow_type),
        );
        assert!(self
            .edge_map
            .insert((src_block_id, dst_block_id), edge_index)
            .is_none());
        edge_index
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

        // maps instruction offset within one context to exec block id
        let mut inst_map: HashMap<CodeOffset, ExecBlockId> = HashMap::new();

        // maps a call instruction to a tuple
        // (return_into exec block id, return_from exec block id set)
        let mut call_inst_map: HashMap<CodeOffset, (ExecBlockId, HashSet<ExecBlockId>)> =
            HashMap::new();

        // iterate CFG
        for block_id in cfg_reverse_postorder_dfs(&cfg, instructions) {
            // prepare
            let block_code_offset_begin = cfg.block_start(block_id);
            let block_code_offset_end = cfg.block_end(block_id);

            // create the block
            let mut exec_block_id = *id_counter;
            *id_counter += 1;
            let mut exec_block = ExecBlock::new(
                exec_block_id,
                code_context.clone(),
                Some(block_code_offset_begin),
            );

            // scan instructions
            for offset in block_code_offset_begin..=block_code_offset_end {
                let instruction = &instructions[offset as usize];
                exec_block.add_instruction(instruction.clone());

                // now update the local instruction map
                assert!(inst_map.insert(offset, exec_block.block_id).is_none());

                // ensure that all branch instructions are terminations
                // in the block
                if instruction.is_branch() {
                    assert_eq!(offset, block_code_offset_end);
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

                    // done with building of this exec block
                    self.add_block(exec_block.clone());

                    // clear this exec block so that it can be reused
                    // to host the rest of instructions in current basic
                    // block, after the call.
                    exec_block_id = *id_counter;
                    *id_counter += 1;
                    exec_block = ExecBlock::new(
                        exec_block_id,
                        code_context.clone(),
                        if offset == block_code_offset_end {
                            None
                        } else {
                            Some(offset + 1)
                        },
                    );

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
                        let rec_call_site = *rec_candidates.last().unwrap();
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
            self.add_block(exec_block);
        }

        // find entry block id and node
        let cfg_entry_block_id = *inst_map
            .get(&cfg.block_start(cfg.entry_block_id()))
            .unwrap();

        // add incoming call edge
        if let Some(call_site) = call_stack.last() {
            // this exec unit is called into, add the call edge
            self.add_flow(
                call_site.call_block_id,
                cfg_entry_block_id,
                ExecFlowType::Call,
            );
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

            for successor_offset in Bytecode::get_successors(term_offset, instructions) {
                // derive successor node id
                let successor_block_id = *inst_map.get(&successor_offset).unwrap();

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
                        ExecFlowType::Fallthrough
                    }
                };

                // add edge to graph
                self.add_flow(origin_block_id, successor_block_id, exec_flow_type);
            }
        }

        // add returning edges from internal calls
        for (ret_into_id, ret_from_ids) in call_inst_map.values() {
            for ret_from_id in ret_from_ids {
                self.add_flow(*ret_from_id, *ret_into_id, ExecFlowType::Ret);
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

        // at the end of the execution, we should have no calls in stack
        assert!(call_stack.is_empty());

        // add all recursion edges
        for ((call_from_id, call_into_id), ret_into_id) in recursions.iter() {
            // add call edge to graph
            exec_graph.add_flow(*call_from_id, *call_into_id, ExecFlowType::CallRecursive);

            // add return edges to graph
            for ret_from_id in exit_table.get(&call_into_id).unwrap() {
                exec_graph.add_flow(
                    *ret_from_id,
                    *ret_into_id,
                    ExecFlowType::RetRecursive(*call_from_id),
                );
            }
        }

        // additional sanity checks and information derivation
        exec_graph.check_and_finish();

        // done
        exec_graph
    }

    /// post-construction sanity check
    fn check_and_finish(&mut self) {
        // check all nodes and edges are mapped
        assert_eq!(self.graph.node_count(), self.node_map.len());
        assert_eq!(self.graph.edge_count(), self.edge_map.len());

        // check that each node has at least one incoming edge, except
        // for the entry node.
        let mut entry_node = None;
        let mut exit_nodes = vec![];
        let mut dead_nodes = vec![];
        for node in self.graph.node_indices() {
            if self
                .graph
                .first_edge(node, EdgeDirection::Incoming)
                .is_none()
            {
                match self.graph.node_weight(node).unwrap().code_offset {
                    None => {
                        debug!(
                            "Found a dead exec block {}: this is \
                            likely caused by calling a function \
                            that only aborts but never returns.",
                            self.get_block_id_by_node(node)
                        );
                        dead_nodes.push(node);
                    }
                    Some(offset) => {
                        if offset == 0 {
                            // this is the true entry node
                            assert!(entry_node.is_none());
                            entry_node = Some(node);
                        } else {
                            debug!(
                                "Found a dead exec block {}: this is \
                                likely caused by calling a function \
                                that only aborts but never returns.",
                                self.get_block_id_by_node(node)
                            );
                            dead_nodes.push(node);
                        }
                    }
                };
            }
            if self
                .graph
                .first_edge(node, EdgeDirection::Outgoing)
                .is_none()
            {
                let termination_instruction = self
                    .graph
                    .node_weight(node)
                    .unwrap()
                    .instructions
                    .last()
                    .unwrap();
                match termination_instruction {
                    Bytecode::Ret | Bytecode::Abort => (),
                    _ => panic!(
                        "Only Ret or Abort can be the termination \
                        instruction of an exit execution block"
                    ),
                };
                exit_nodes.push(node);
            }
        }

        // this statement checks that entry_note must exist
        let entry_node = entry_node.unwrap();

        // set the entry block id
        self.entry_block_id = self.get_block_id_by_node(entry_node);

        // find all dead blocks
        let mut reachable_nodes = HashSet::new();

        let mut bfs = Bfs::new(&self.graph, entry_node);
        while let Some(node) = bfs.next(&self.graph) {
            reachable_nodes.insert(node);
        }

        for (block_id, node) in self.node_map.iter() {
            if !reachable_nodes.contains(node) {
                self.dead_block_ids.insert(*block_id);
            }
        }
    }

    /// count number of nodes in the execution graph, including
    /// unreachable nodes from entry_block
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// count number of edges in the execution graph, including
    /// unreachable edges from entry_block
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// convert the graph into Dot representation
    pub fn to_dot(&self) -> String {
        format!(
            "{:?}",
            Dot::with_config(
                &self.graph,
                &[dot::Config::EdgeNoLabel, dot::Config::NodeIndexLabel],
            )
        )
    }
}

/// This is a self-contained set of blocks (can be either a single block
/// or a loop) (i.e., the SCC) in the super-CFG
type ExecSccId = usize;

#[derive(Clone, Debug)]
struct ExecScc {
    scc_id: ExecSccId,
    block_ids: HashSet<ExecBlockId>,
}

impl ExecScc {
    pub fn new(scc_id: ExecSccId, block_ids: HashSet<ExecBlockId>) -> Self {
        Self { scc_id, block_ids }
    }
}

pub(crate) struct ExecSccGraph {
    /// the graph structure
    graph: Graph<ExecScc, EdgeIndex>,
    /// a map mapping scc id to node index
    node_map: HashMap<ExecSccId, NodeIndex>,
    /// the scc id of the graph entry scc
    entry_scc_id: ExecSccId,
    /// a list of sccs that have no outgoing edges
    leaf_scc_ids: Vec<ExecSccId>,
    /// linkage between exec graph to exec scc graph
    linkage: HashMap<NodeIndex, ExecSccId>,
}

impl ExecSccGraph {
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            linkage: HashMap::new(),
            entry_scc_id: 0,
            leaf_scc_ids: vec![],
        }
    }

    fn add_scc(&mut self, scc: ExecScc) -> NodeIndex {
        let exec_scc_id = scc.scc_id;
        let node_index = self.graph.add_node(scc);
        assert!(self.node_map.insert(exec_scc_id, node_index).is_none());
        node_index
    }

    fn get_node_by_scc_id(&self, scc_id: ExecSccId) -> NodeIndex {
        *self.node_map.get(&scc_id).unwrap()
    }

    fn get_entry_node(&self) -> NodeIndex {
        self.get_node_by_scc_id(self.entry_scc_id)
    }

    /// build the scc graph out of the exec graph
    pub fn new(exec_graph: &ExecGraph) -> Self {
        let mut scc_graph = ExecSccGraph::empty();

        // build the nodes and edges in the scc graph
        for (scc_id, scc_nodes) in tarjan_scc(&exec_graph.graph).into_iter().enumerate() {
            // ignore dead scc
            let scc_is_unreachable = scc_nodes.iter().any(|node| {
                exec_graph
                    .dead_block_ids
                    .contains(&exec_graph.get_block_id_by_node(*node))
            });
            if scc_is_unreachable {
                continue;
            }

            // register scc to scc graph
            let exec_scc = ExecScc::new(
                scc_id,
                HashSet::from_iter(
                    scc_nodes
                        .iter()
                        .map(|node| exec_graph.get_block_id_by_node(*node)),
                ),
            );
            let exec_scc_node = scc_graph.add_scc(exec_scc);

            // map node to scc (must be done before edge collection)
            for node in scc_nodes.iter() {
                assert!(scc_graph.linkage.insert(*node, scc_id).is_none());
            }

            // collect edges branching out of this scc
            let mut outlet_map: HashMap<EdgeIndex, ExecSccId> = HashMap::new();
            for node in scc_nodes.iter() {
                for edge in exec_graph
                    .graph
                    .edges_directed(*node, EdgeDirection::Outgoing)
                {
                    let scc_dst_id = *scc_graph.linkage.get(&edge.target()).unwrap();
                    if scc_dst_id != scc_id {
                        assert!(outlet_map.insert(edge.id(), scc_dst_id).is_none());
                    }
                }
            }

            // detect leaf scc
            if outlet_map.is_empty() {
                scc_graph.leaf_scc_ids.push(scc_id);
            }

            // add edges between sccs
            for (exit_edge, exit_scc) in outlet_map {
                scc_graph.graph.add_edge(
                    exec_scc_node,
                    scc_graph.get_node_by_scc_id(exit_scc),
                    exit_edge,
                );
            }
        }

        // find the entry scc
        scc_graph.entry_scc_id = *scc_graph.linkage.get(&exec_graph.get_entry_node()).unwrap();

        // done
        scc_graph
    }

    /// count paths
    pub fn count_paths(&self) -> u128 {
        // per each path_end_scc (i.e., a leaf node in the SCC graph),
        // stores how many reachable paths from any_scc to path_end_scc
        let mut path_map: HashMap<NodeIndex, HashMap<NodeIndex, u128>> = HashMap::new();

        // go with reverse topological order
        for node in toposort(&self.graph, None).unwrap().into_iter().rev() {
            let mut out_edges_iter = self
                .graph
                .edges_directed(node, EdgeDirection::Outgoing)
                .peekable();
            if out_edges_iter.peek().is_none() {
                // this is a termination scc
                let mut term_path_map = HashMap::new();
                term_path_map.insert(node, 1);
                assert!(path_map.insert(node, term_path_map).is_none());
            } else {
                // update path count map
                let mut scc_reach_map: HashMap<NodeIndex, u128> = HashMap::new();
                for out_edge in out_edges_iter {
                    for (path_end_scc, path_end_reach_map) in path_map.iter() {
                        if let Some(path_count) = path_end_reach_map.get(&out_edge.target()) {
                            // there is a way from this exit_scc to
                            // path_end_scc, adding to existing count.
                            let existing_count = scc_reach_map.entry(*path_end_scc).or_insert(0);
                            *existing_count += path_count;
                        }
                    }
                }

                // merge into the path map
                for (path_end_scc, path_end_reach_count) in scc_reach_map {
                    assert!(path_map
                        .get_mut(&path_end_scc)
                        .unwrap()
                        .insert(node, path_end_reach_count)
                        .is_none());
                }
            }
        }

        // derive end-to-end path count
        let entry_scc_node = self.get_entry_node();

        let mut total_count = 0;
        for path_end_reach_map in path_map.values() {
            total_count += path_end_reach_map.get(&entry_scc_node).unwrap();
        }

        total_count
    }

    /// enumerate all paths from entry to the end
    pub fn enumerate_paths(&self) -> Vec<Vec<NodeIndex>> {
        let mut paths = vec![];
        for leaf_scc_id in self.leaf_scc_ids.iter() {
            if *leaf_scc_id == self.entry_scc_id {
                // the all_simple_paths does not count single node path
                // we add it manually to reconcile with the output from
                // the algorithm in scc_path_count
                paths.push(vec![]);
            } else {
                paths.extend(all_simple_paths::<Vec<NodeIndex>, _>(
                    &self.graph,
                    self.get_entry_node(),
                    self.get_node_by_scc_id(*leaf_scc_id),
                    0,
                    None,
                ));
            }
        }
        paths
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
