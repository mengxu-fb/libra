// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! This package aims for building an extended control-flow graph (eCFG) that encloses both script
//! and module per-function CFGs, i.e., a super graph that has CFGs connected by the call graph.

use itertools::Itertools;
use log::debug;
use petgraph::{
    algo::{all_simple_paths, tarjan_scc, toposort},
    dot::Dot,
    graph::{EdgeIndex, Graph, NodeIndex},
    visit::{Bfs, DfsPostOrder, EdgeRef},
    EdgeDirection,
};
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use bytecode::{
    stackless_bytecode::{Bytecode, Operation},
    stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph},
};
use vm::file_format::CodeOffset;

use crate::{
    sym_oracle::{SymFuncInfo, SymOracle},
    sym_typing::ExecTypeArg,
};

/// An id that uniquely identifies a basic block in the eCFG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct ExecBlockId(usize);

/// This is the basic block (i.e., the node) in the eCFG
pub(crate) struct ExecBlock<'env> {
    /// A unique identifier for the exec block
    block_id: ExecBlockId,
    /// The context (module, function) where this block lives
    exec_unit: &'env SymFuncInfo<'env>,
    /// The starting offset of the instructions in code context
    ///
    /// NOTE: A None value means that this is an arbitrary block which will host no instructions.
    /// However, not all arbitrary blocks have None as code_offset, those that do host instructions
    /// will have a valid code_offset.
    code_offset: Option<CodeOffset>,
    /// The type argument for the function in the code context
    type_args: Vec<ExecTypeArg<'env>>,
    /// The instructions within this basic block. It is OK to be empty.
    instructions: Vec<&'env Bytecode>,
}

impl<'env> ExecBlock<'env> {
    fn new(
        block_id: ExecBlockId,
        exec_unit: &'env SymFuncInfo<'env>,
        code_offset: Option<CodeOffset>,
        type_args: Vec<ExecTypeArg<'env>>,
    ) -> Self {
        Self {
            block_id,
            exec_unit,
            code_offset,
            type_args,
            instructions: vec![],
        }
    }

    fn add_instruction(&mut self, bytecode: &'env Bytecode) {
        self.instructions.push(bytecode);
    }
}

impl<'env> fmt::Display for ExecBlock<'env> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // block head
        writeln!(
            f,
            "[{} - {}<{}> - {}]",
            self.block_id.0,
            self.exec_unit.get_context_string(),
            self.type_args
                .iter()
                .map(|ty_arg| ty_arg.to_string())
                .join(", "),
            self.code_offset
                .map_or_else(|| String::from("X"), |offset| offset.to_string())
        )?;

        // block content
        for instruction in self.instructions.iter() {
            writeln!(f, "{}", instruction.display(&self.exec_unit.get_target()))?;
        }

        // done
        Ok(())
    }
}

/// Types of control-flow transitions
enum ExecFlowType {
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

impl fmt::Display for ExecFlowType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExecFlowType::Branch(cond) => write!(
                f,
                "Branch({})",
                cond.map_or_else(|| String::from("None"), |v| v.to_string())
            ),
            ExecFlowType::Call => write!(f, "Call"),
            ExecFlowType::Ret => write!(f, "Ret"),
            ExecFlowType::CallRecursive => write!(f, "CallRecursive"),
            ExecFlowType::RetRecursive(block_id) => write!(f, "RetRecursive({})", block_id.0),
        }
    }
}

/// This is the control-flow transition (i.e., the edge) in the eCFG
struct ExecFlow {
    /// The basic block where this flow goes from
    src_block_id: ExecBlockId,
    /// The basic block where this flow goes into
    dst_block_id: ExecBlockId,
    /// The type of this flow
    flow_type: ExecFlowType,
}

impl fmt::Display for ExecFlow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.flow_type.fmt(f)
    }
}

/// Used to track information stored on the call stack
struct CallSite<'env> {
    /// The context we are in right now
    exec_unit: &'env SymFuncInfo<'env>,
    /// Instantiation information (if any).
    /// NOTE: Calls to the same function with different instantiations are treated as if this is
    /// calling different functions. This is part of the effort of flattening the types
    type_args: Vec<ExecTypeArg<'env>>,
    /// The exec block id for the entry block in this context
    entry_block_id: ExecBlockId,
}

/// This is the super-CFG graph representation.
pub(crate) struct ExecGraph<'env> {
    /// The graph structure
    graph: Graph<ExecBlock<'env>, ExecFlow>,
    /// A map mapping block id to node index
    node_map: HashMap<ExecBlockId, NodeIndex>,
    /// A map mapping a pair of connecting blocks to edge index
    edge_map: HashMap<(ExecBlockId, ExecBlockId), EdgeIndex>,
    /// The block id of the graph entry block
    entry_block_id: ExecBlockId,
    /// A list of blocks that are unreachable from the entry block
    dead_block_ids: HashSet<ExecBlockId>,
}

impl<'env> ExecGraph<'env> {
    // graph construction
    fn empty() -> Self {
        Self {
            graph: Graph::new(),
            node_map: HashMap::new(),
            edge_map: HashMap::new(),
            entry_block_id: ExecBlockId(0),
            dead_block_ids: HashSet::new(),
        }
    }

    fn add_block(&mut self, block: ExecBlock<'env>) -> NodeIndex {
        let block_id = block.block_id;
        let node_index = self.graph.add_node(block);
        let exists = self.node_map.insert(block_id, node_index);
        debug_assert!(exists.is_none());
        node_index
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
            ExecFlow {
                src_block_id,
                dst_block_id,
                flow_type,
            },
        );
        let exists = self
            .edge_map
            .insert((src_block_id, dst_block_id), edge_index);
        debug_assert!(exists.is_none());
        edge_index
    }

    // information getters
    fn get_node_by_block_id(&self, block_id: ExecBlockId) -> NodeIndex {
        *self.node_map.get(&block_id).unwrap()
    }

    fn get_block_by_node(&self, node: NodeIndex) -> &ExecBlock<'env> {
        self.graph.node_weight(node).unwrap()
    }

    pub fn get_block_by_block_id(&self, block_id: ExecBlockId) -> &ExecBlock<'env> {
        self.get_block_by_node(self.get_node_by_block_id(block_id))
    }

    // core
    fn incorporate(
        &mut self,
        exec_unit: &'env SymFuncInfo<'env>,
        type_args: &[ExecTypeArg<'env>],
        call_from_block_id: Option<ExecBlockId>,
        call_stack: &mut Vec<CallSite<'env>>,
        exit_table: &mut HashMap<ExecBlockId, HashSet<ExecBlockId>>,
        id_counter: &mut ExecBlockId,
        recursions: &mut HashMap<(ExecBlockId, ExecBlockId), ExecBlockId>,
        oracle: &'env SymOracle<'env>,
    ) -> (ExecBlockId, HashSet<ExecBlockId>) {
        // prepare
        let instructions = exec_unit.get_instructions();
        let cfg = exec_unit.get_cfg();

        // maps instruction offset within one context to exec block id
        let mut inst_map: HashMap<CodeOffset, ExecBlockId> = HashMap::new();

        // maps a call instruction to a tuple
        // (return_into_exec_block_id, Set<return_from_exec_block_id>)
        let mut call_inst_map: HashMap<CodeOffset, (ExecBlockId, HashSet<ExecBlockId>)> =
            HashMap::new();

        // locate the entry block of this function CFG
        let mut entry_point = None;

        // iterate CFG with reverse postorder DFS
        for block_id in cfg_reverse_postorder_dfs(&cfg, instructions) {
            // prepare
            let block_code_offset_lower = cfg.block_start(block_id);
            let block_code_offset_upper = cfg.block_end(block_id);

            // create the block
            let mut exec_block = ExecBlock::new(
                *id_counter,
                exec_unit,
                Some(block_code_offset_lower),
                type_args.to_vec(),
            );
            id_counter.0 += 1;

            // prepare call stack if this is the entry block
            //
            // NOTE: cfg.entry_blocks() must return one and only one BlockId. We checked this when
            // the CFG is constructed in `SymFuncInfo::new()`
            //
            // NOTE: since we traverse the CFG in reverse postorder dfs, this is guaranteed to be
            // executed before any other blocks are visited
            if block_id == cfg.entry_blocks().pop().unwrap() {
                debug_assert!(entry_point.is_none());
                entry_point = Some(exec_block.block_id);

                let call_site = CallSite {
                    exec_unit,
                    type_args: type_args.to_vec(),
                    entry_block_id: exec_block.block_id,
                };
                call_stack.push(call_site);
            }

            // scan instructions
            for offset in block_code_offset_lower..=block_code_offset_upper {
                let instruction = &instructions[offset as usize];
                exec_block.add_instruction(instruction);

                // now update the local instruction map
                let exists = inst_map.insert(offset, exec_block.block_id);
                debug_assert!(exists.is_none());

                // ensure that all branch instructions are terminations in the block
                if instruction.is_branch() {
                    debug_assert_eq!(offset, block_code_offset_upper);
                }

                // see if we are going to call into another exec unit
                if let Bytecode::Call(
                    _,
                    _,
                    Operation::Function(module_id, func_id, type_actuals),
                    _,
                ) = instruction
                {
                    if let Some(next_exec_unit) =
                        oracle.get_tracked_function_by_spec(module_id, func_id)
                    {
                        let next_type_args: Vec<ExecTypeArg> = type_actuals
                            .iter()
                            .map(|type_actual| {
                                ExecTypeArg::convert_from_type_actual(
                                    type_actual,
                                    type_args,
                                    oracle,
                                )
                            })
                            .collect();

                        // record block id
                        let call_site_block_id = exec_block.block_id;

                        // done with building of this exec block
                        self.add_block(exec_block);

                        // clear this exec block so that it can be reused to host the rest of
                        // instructions in current basic block, after the call.
                        exec_block = ExecBlock::new(
                            *id_counter,
                            exec_unit,
                            if offset == block_code_offset_upper {
                                None
                            } else {
                                Some(offset + 1)
                            },
                            type_args.to_vec(),
                        );
                        id_counter.0 += 1;

                        // record the block id that the call will return to
                        let call_site_ret_block_id = exec_block.block_id;

                        // check recursion and act accordingly
                        let rec_candidates: Vec<&CallSite> = call_stack
                            .iter()
                            .filter(|call_site| {
                                call_site.exec_unit == next_exec_unit
                                    && call_site.type_args == next_type_args
                            })
                            .collect();

                        let ret_block_ids = if rec_candidates.is_empty() {
                            // non-recursive: call into the next unit
                            self.incorporate(
                                next_exec_unit,
                                &next_type_args,
                                Some(call_site_block_id),
                                call_stack,
                                exit_table,
                                id_counter,
                                recursions,
                                oracle,
                            )
                            .1
                        } else {
                            // recursive call: do not further expand the CFG of that function, just
                            // connect the blocks.

                            // ensure no duplicated context in call stack
                            debug_assert_eq!(rec_candidates.len(), 1);

                            // mark that there should be a pending call edge from this block to the
                            // beginning of the call site context, and also that the context will
                            // return to the ret block.
                            let rec_call_site = *rec_candidates.last().unwrap();
                            let exists = recursions.insert(
                                (call_site_block_id, rec_call_site.entry_block_id),
                                call_site_ret_block_id,
                            );
                            debug_assert!(exists.is_none());

                            // intentionally return an empty list as the recursive call site has not
                            // finished CFG exploration, and hence, we do not know all of their
                            // return blocks yet.
                            HashSet::new()
                        };

                        // add the new block id to the map that tracks calls specifically
                        let exists =
                            call_inst_map.insert(offset, (call_site_ret_block_id, ret_block_ids));
                        debug_assert!(exists.is_none());
                    }
                }
            }

            // add block to graph
            self.add_block(exec_block);
        }

        // pop the call stack after cfg exploration
        let call_site = call_stack.pop().unwrap();

        // add incoming call edge
        if let Some(exec_block_id) = call_from_block_id {
            // this exec unit is called into, add the call edge
            self.add_flow(exec_block_id, call_site.entry_block_id, ExecFlowType::Call);
        }

        // add branching edges in CFG
        let label_offsets = Bytecode::label_offsets(instructions);
        for block_id in cfg.blocks() {
            let term_offset = cfg.block_end(block_id);
            let term_instruction = &instructions[term_offset as usize];

            // derive origin node id
            let origin_block_id = call_inst_map.get(&term_offset).map_or_else(
                || inst_map.get(&term_offset).unwrap(),
                |(ret_to_id, _)| ret_to_id,
            );

            // it seems that in stackless CFG, every termination instruction is a branch
            debug_assert!(term_instruction.is_branch());

            for successor_offset in
                Bytecode::get_successors(term_offset, instructions, &label_offsets)
            {
                // exit instructions have no successors
                debug_assert!(!term_instruction.is_exit());

                // check which type of branch it is
                let exec_flow_type = if term_instruction.is_unconditional_branch() {
                    ExecFlowType::Branch(None)
                } else if let Bytecode::Branch(_, then_label, else_label, _) = term_instruction {
                    if successor_offset == *label_offsets.get(then_label).unwrap() {
                        ExecFlowType::Branch(Some(true))
                    } else {
                        debug_assert!(successor_offset == *label_offsets.get(else_label).unwrap());
                        ExecFlowType::Branch(Some(false))
                    }
                } else {
                    panic!("Invalid branch type for a termination instruction");
                };

                // add edge to graph
                self.add_flow(
                    *origin_block_id,
                    *inst_map.get(&successor_offset).unwrap(),
                    exec_flow_type,
                );
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
                Bytecode::Ret(..) => Some(*inst_map.get(&(offset as CodeOffset)).unwrap()),
                _ => None,
            })
            .collect();
        exit_table.insert(call_site.entry_block_id, exit_points.clone());

        // done
        (entry_point.unwrap(), exit_points)
    }

    pub fn new(type_args: &[ExecTypeArg<'env>], oracle: &'env SymOracle<'env>) -> Self {
        // find the init_unit
        let init_unit = oracle.get_script_exec_unit();

        // start symbolization from the init_unit
        let mut call_stack = vec![];
        let mut exit_table = HashMap::new();
        let mut id_counter = ExecBlockId(0);
        let mut recursions = HashMap::new();

        let mut exec_graph = ExecGraph::empty();
        let init_entry_point = exec_graph
            .incorporate(
                &init_unit,
                type_args,
                None,
                &mut call_stack,
                &mut exit_table,
                &mut id_counter,
                &mut recursions,
                oracle,
            )
            .0;

        // at the end of the execution, we should have no calls in stack
        debug_assert!(call_stack.is_empty());

        // add all recursion edges, this can only be done when incorporation is complete
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

        // check all nodes and edges are mapped
        debug_assert_eq!(exec_graph.graph.node_count(), exec_graph.node_map.len());
        debug_assert_eq!(exec_graph.graph.edge_count(), exec_graph.edge_map.len());

        // check that each node has at least one incoming edge, except for the entry node
        let mut entry_node = None;
        let mut exit_nodes = vec![];
        let mut dead_nodes = vec![];
        for node in exec_graph.graph.node_indices() {
            if exec_graph
                .graph
                .first_edge(node, EdgeDirection::Incoming)
                .is_none()
            {
                match exec_graph.get_block_by_node(node).code_offset {
                    None => {
                        dead_nodes.push(node);
                    }
                    Some(offset) => {
                        if offset == 0 {
                            // this is the true entry node
                            debug_assert!(entry_node.is_none());
                            entry_node = Some(node);
                        } else {
                            dead_nodes.push(node);
                        }
                    }
                };
            }
            if exec_graph
                .graph
                .first_edge(node, EdgeDirection::Outgoing)
                .is_none()
            {
                let term_instruction = exec_graph
                    .graph
                    .node_weight(node)
                    .unwrap()
                    .instructions
                    .last()
                    .unwrap();

                // check that only Ret or Abort can be the termination instruction of an exit block
                debug_assert!(term_instruction.is_exit());
                exit_nodes.push(node);
            }
        }

        // log on dead nodes
        if !dead_nodes.is_empty() {
            debug!(
                "Found {} dead exec block(s) [{}]: this is likely caused by calling into some \
                function that never returns (e.g., a function with aborts only or is essentially \
                an infinite loop)",
                dead_nodes.len(),
                dead_nodes
                    .into_iter()
                    .map(|node| exec_graph.get_block_by_node(node).block_id.0.to_string())
                    .join(", ")
            )
        }

        // construct the entry node to this eCFG if not exists
        //
        // NOTE: if an entry node does not exist, this eCFG is essentially an infinite loop. To
        // handle this case, we create a dummy header block (i.e., containing no instructions) and
        // link the header with the first block of the init unit.
        if entry_node.is_none() {
            let header_block = ExecBlock::new(id_counter, init_unit, None, type_args.to_vec());
            id_counter.0 += 1;

            let header_block_id = header_block.block_id;
            let header_block_node = exec_graph.add_block(header_block);
            exec_graph.add_flow(
                header_block_id,
                init_entry_point,
                ExecFlowType::Branch(None),
            );

            // now set the header block node as the entry node
            entry_node = Some(header_block_node);
        }

        // this statement checks that entry_note must exist
        let entry_node = entry_node.unwrap();

        // set the entry block id
        exec_graph.entry_block_id = exec_graph.get_block_by_node(entry_node).block_id;

        // find all dead blocks
        let mut reachable_nodes = HashSet::new();

        let mut bfs = Bfs::new(&exec_graph.graph, entry_node);
        while let Some(node) = bfs.next(&exec_graph.graph) {
            reachable_nodes.insert(node);
        }

        for (block_id, node) in exec_graph.node_map.iter() {
            if !reachable_nodes.contains(node) {
                exec_graph.dead_block_ids.insert(*block_id);
            }
        }

        // done
        exec_graph
    }

    /// count number of nodes in the execution graph, including unreachable nodes from entry_block
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    /// count number of edges in the execution graph, including unreachable edges from entry_block
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    /// convert the graph into Dot representation
    pub fn to_dot(&self) -> String {
        format!(
            "{}",
            Dot::with_attr_getters(&self.graph, &[], &|_, _| "".to_string(), &|_, _| {
                "shape=box".to_string()
            })
        )
    }
}

/// Convert a CFG into generic graphs so we can benefit from various graph algorithms in `petgraph`,
/// e.g., the `DfsPostOrder` visit algorithm
fn cfg_to_generic_graph(
    cfg: &StacklessControlFlowGraph,
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

    // collect exit blocks
    let exit_blocks: Vec<BlockId> = blocks
        .into_iter()
        .filter(|block_id| cfg.successors(*block_id).is_empty())
        .collect();

    // if a basic block has no successors, it must be either
    //  1. a basic block ending with Ret, or
    //  2. a basic block ending with Abort
    debug_assert!(exit_blocks.iter().all(|block_id| {
        match &instructions[cfg.block_end(*block_id) as usize] {
            Bytecode::Ret(..) => true,
            Bytecode::Abort(..) => true,
            _ => false,
        }
    }));

    // Find the exit block or create an arbitrary block as the unified exit block
    // It is important to have a unified exit block for reverse-postorder DFS, as the one and only
    // exit block serves as a good starting point for the visitation algorithm.
    //
    // NOTE: given how BlockId are assigned, any number >= length of instructions: &[Bytecode] will
    // be safe to use as the BlockId for artificial blocks
    let exit_node = if exit_blocks.is_empty() {
        // if there are no exit blocks, it means that the whole CFG is a loop. In this case, we
        // create an arbitrary exit node and link all existing blocks to this exit node
        let unity_node = graph.add_node(instructions.len() as BlockId);
        for node_id in node_map.values() {
            graph.add_edge(*node_id, unity_node, ());
        }
        unity_node
    } else if exit_blocks.len() != 1 {
        // if more than one exit blocks are found, add an arbitrary unity block and link all exit
        // blocks to the unity block
        let unity_node = graph.add_node(instructions.len() as BlockId);
        for block_id in &exit_blocks {
            graph.add_edge(*node_map.get(block_id).unwrap(), unity_node, ());
        }
        unity_node
    } else {
        *node_map.get(exit_blocks.last().unwrap()).unwrap()
    };

    // done
    (graph, exit_node)
}

fn cfg_reverse_postorder_dfs(
    cfg: &StacklessControlFlowGraph,
    instructions: &[Bytecode],
) -> Vec<BlockId> {
    let mut result = vec![];

    // build and reverse the CFG
    let (mut graph, exit_node) = cfg_to_generic_graph(cfg, instructions);
    graph.reverse();

    // check that the exit_node now is the entry node after reversal
    debug_assert_eq!(
        graph
            .edges_directed(exit_node, EdgeDirection::Incoming)
            .count(),
        0
    );

    // Run postorder DFS visitation
    //
    // In reverse-postorder iteration, a node is visited before any of its successor nodes has been
    // visited, except when the successor is reached by a back edge.
    //
    // NOTE: reverse-postorder DFS is not the same as preorder
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
