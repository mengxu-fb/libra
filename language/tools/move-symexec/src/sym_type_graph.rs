// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use itertools::Itertools;
use log::debug;
use petgraph::{
    algo::{is_cyclic_directed, toposort},
    graph::{Graph, NodeIndex},
};
use std::collections::HashMap;

use bytecode::stackless_bytecode::{Bytecode, Operation};
use spec_lang::env::{FieldEnv, FieldId};

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker, ExecWalkerStep},
    sym_oracle::{SymOracle, SymStructId, SymStructInfo},
    sym_typing::ExecTypeArg,
};

/// Fully instantiated struct information. This is generated only when the struct is actually
/// involved in the exec graph (a.k.a., the eCFG)
pub(crate) enum ExecStructInfo<'env> {
    Native,
    Declared {
        field_vec: Vec<FieldEnv<'env>>,
        field_map: HashMap<FieldId, ExecTypeArg<'env>>,
    },
}

/// Records the dependencies between the types, especially structs, involved in the execution.
pub(crate) struct TypeGraph<'env> {
    involved_structs: HashMap<SymStructId, HashMap<Vec<ExecTypeArg<'env>>, String>>,
    analyzed_structs: HashMap<String, ExecStructInfo<'env>>,
    graph: Graph<String, ()>,
}

impl<'env> TypeGraph<'env> {
    pub fn new(exec_graph: &ExecGraph<'env>, oracle: &'env SymOracle<'env>) -> Self {
        // holds the struct types we have discovered so far
        let mut involved_structs = HashMap::new();
        let mut analyzed_structs = HashMap::new();

        // holds the block access path
        let mut scc_stack = vec![None];

        // find all places that may use a struct type
        let mut walker = ExecWalker::new(exec_graph);
        while let Some(walker_step) = walker.next() {
            match walker_step {
                ExecWalkerStep::CycleEntry { scc, .. } => scc_stack.push(Some(scc.scc_id)),
                ExecWalkerStep::CycleExit { scc_id } => {
                    let cur_scc_id = scc_stack.pop().unwrap();
                    debug_assert_eq!(cur_scc_id.unwrap(), scc_id);
                }
                ExecWalkerStep::Block { block_id, .. } => {
                    // go over the instructions
                    let block = exec_graph.get_block_by_block_id(block_id);
                    for instruction in &block.instructions {
                        match instruction {
                            Bytecode::Call(_, _, op, _) => {
                                let (func_info_opt, struct_info_opt, type_actuals_opt) = match op {
                                    Operation::Function(mid, fid, type_actuals) => (
                                        oracle.get_tracked_function_by_spec(mid, fid),
                                        None,
                                        Some(type_actuals),
                                    ),
                                    Operation::Pack(mid, sid, type_actuals)
                                    | Operation::Unpack(mid, sid, type_actuals)
                                    | Operation::MoveTo(mid, sid, type_actuals)
                                    | Operation::MoveFrom(mid, sid, type_actuals)
                                    | Operation::Exists(mid, sid, type_actuals)
                                    | Operation::BorrowField(mid, sid, type_actuals, _)
                                    | Operation::BorrowGlobal(mid, sid, type_actuals)
                                    | Operation::GetField(mid, sid, type_actuals, _)
                                    | Operation::GetGlobal(mid, sid, type_actuals) => (
                                        None,
                                        Some(oracle.get_defined_struct_by_spec(mid, sid).unwrap()),
                                        Some(type_actuals),
                                    ),
                                    // other operation types do not have struct information
                                    _ => (None, None, None),
                                };

                                // collect types in type actuals
                                let mut sub_type_actuals = vec![];
                                if let Some(type_actuals) = type_actuals_opt {
                                    for type_arg in type_actuals {
                                        let exec_type_arg = ExecTypeArg::convert_from_type_actual(
                                            type_arg,
                                            &block.type_args,
                                            oracle,
                                        );
                                        collect_involved_structs_in_type_arg(
                                            &exec_type_arg,
                                            oracle,
                                            &mut involved_structs,
                                            &mut analyzed_structs,
                                        );
                                        sub_type_actuals.push(exec_type_arg);
                                    }
                                }

                                // collect types in function info
                                if let Some(func_info) = func_info_opt {
                                    for type_arg in &func_info.func_data.local_types {
                                        let exec_type_arg = ExecTypeArg::convert_from_type_actual(
                                            type_arg,
                                            &sub_type_actuals,
                                            oracle,
                                        );
                                        collect_involved_structs_in_type_arg(
                                            &exec_type_arg,
                                            oracle,
                                            &mut involved_structs,
                                            &mut analyzed_structs,
                                        );
                                    }

                                    for type_arg in &func_info.func_data.return_types {
                                        let exec_type_arg = ExecTypeArg::convert_from_type_actual(
                                            type_arg,
                                            &sub_type_actuals,
                                            oracle,
                                        );
                                        collect_involved_structs_in_type_arg(
                                            &exec_type_arg,
                                            oracle,
                                            &mut involved_structs,
                                            &mut analyzed_structs,
                                        );
                                    }
                                }

                                // collect types in struct info
                                if let Some(struct_info) = struct_info_opt {
                                    collect_involved_structs_recursive(
                                        struct_info,
                                        &sub_type_actuals,
                                        oracle,
                                        &mut involved_structs,
                                        &mut analyzed_structs,
                                    );
                                }
                            }
                            Bytecode::SpecBlock(_, _) => {
                                debug!("Specifications are not supported now");
                            }
                            // other instruction types do not have struct information
                            _ => {}
                        }
                    }
                }
            }
        }

        // stack integrity
        let base_scc = scc_stack.pop().unwrap();
        debug_assert!(base_scc.is_none());
        debug_assert!(scc_stack.is_empty());

        // start building the graph
        let mut graph = Graph::new();

        // create nodes
        let node_map = analyzed_structs
            .keys()
            .map(|variant_name| (variant_name.clone(), graph.add_node(variant_name.clone())))
            .collect();

        // create edges
        for (variant_name, variant_info) in analyzed_structs.iter() {
            match variant_info {
                ExecStructInfo::Native => {}
                ExecStructInfo::Declared { field_map, .. } => {
                    for field_type in field_map.values() {
                        TypeGraph::link(
                            variant_name,
                            field_type,
                            &involved_structs,
                            &node_map,
                            &mut graph,
                        );
                    }
                }
            }
        }

        // the type graph should not have cycles
        debug_assert!(!is_cyclic_directed(&graph));

        // done
        Self {
            involved_structs,
            analyzed_structs,
            graph,
        }
    }

    fn link(
        variant_name: &str,
        variant_type_arg: &ExecTypeArg<'env>,
        involved_structs: &HashMap<SymStructId, HashMap<Vec<ExecTypeArg<'env>>, String>>,
        graph_node_map: &HashMap<String, NodeIndex>,
        graph: &mut Graph<String, ()>,
    ) {
        match variant_type_arg {
            ExecTypeArg::Bool
            | ExecTypeArg::U8
            | ExecTypeArg::U64
            | ExecTypeArg::U128
            | ExecTypeArg::Address
            | ExecTypeArg::Signer => {}
            ExecTypeArg::Vector { element_type } => {
                TypeGraph::link(
                    variant_name,
                    element_type.as_ref(),
                    involved_structs,
                    graph_node_map,
                    graph,
                );
            }
            ExecTypeArg::Struct {
                struct_info,
                type_args,
            } => {
                let dep_name = involved_structs
                    .get(&struct_info.struct_id)
                    .unwrap()
                    .get(type_args)
                    .unwrap();
                let dep_node_id = graph_node_map.get(dep_name).unwrap();
                let src_node_id = graph_node_map.get(variant_name).unwrap();
                graph.add_edge(*src_node_id, *dep_node_id, ());
            }
            ExecTypeArg::Reference { referred_type, .. } => {
                TypeGraph::link(
                    variant_name,
                    referred_type.as_ref(),
                    involved_structs,
                    graph_node_map,
                    graph,
                );
            }
            ExecTypeArg::TypeParameter { actual_type, .. } => {
                TypeGraph::link(
                    variant_name,
                    actual_type.as_ref(),
                    involved_structs,
                    graph_node_map,
                    graph,
                );
            }
        }
    }

    pub fn type_count(&self) -> usize {
        self.analyzed_structs.len()
    }

    pub fn reverse_topological_sort(&self) -> Vec<(&str, &ExecStructInfo<'env>)> {
        // we can use toposort here because we know that the type graph must be acyclic
        let nodes = toposort(&self.graph, None).unwrap();
        nodes
            .into_iter()
            .rev()
            .map(|node| {
                let name = self.graph.node_weight(node).unwrap();
                (name.as_str(), self.analyzed_structs.get(name).unwrap())
            })
            .collect()
    }

    pub fn get_struct_name(
        &self,
        struct_id: &SymStructId,
        type_args: &[ExecTypeArg<'env>],
    ) -> Option<&str> {
        self.involved_structs
            .get(struct_id)
            .map(|struct_variants| {
                struct_variants
                    .get(type_args)
                    .map(|struct_name| struct_name.as_str())
            })
            .flatten()
    }
}

fn collect_involved_structs_recursive<'env>(
    struct_info: &'env SymStructInfo<'env>,
    type_args: &[ExecTypeArg<'env>],
    oracle: &'env SymOracle<'env>,
    involved_structs: &mut HashMap<SymStructId, HashMap<Vec<ExecTypeArg<'env>>, String>>,
    analyzed_structs: &mut HashMap<String, ExecStructInfo<'env>>,
) {
    let variants = involved_structs
        .entry(struct_info.struct_id)
        .or_insert_with(HashMap::new);

    if !variants.contains_key(type_args) {
        let inst_name = format!(
            "{}<{}>-{}",
            struct_info.get_context_string(),
            type_args
                .iter()
                .map(|type_arg| type_arg.to_string())
                .join(", "),
            variants.len()
        );
        variants.insert(type_args.to_vec(), inst_name.clone());

        // recursively handle the fields in this struct
        let exec_struct_info = if struct_info.struct_env.is_native() {
            ExecStructInfo::Native
        } else {
            let mut field_vec = vec![];
            let mut field_map = HashMap::new();
            for field_env in struct_info.struct_env.get_fields() {
                // handle field type recursively
                let field_type_actual =
                    ExecTypeArg::convert_from_type_actual(&field_env.get_type(), type_args, oracle);
                collect_involved_structs_in_type_arg(
                    &field_type_actual,
                    oracle,
                    involved_structs,
                    analyzed_structs,
                );

                field_map.insert(field_env.get_id(), field_type_actual);
                field_vec.push(field_env);
            }
            debug_assert_eq!(field_vec.len(), field_map.len());
            ExecStructInfo::Declared {
                field_vec,
                field_map,
            }
        };

        // mark that we have handled this struct
        let exists = analyzed_structs.insert(inst_name, exec_struct_info);
        debug_assert!(exists.is_none());
    }
}

fn collect_involved_structs_in_type_arg<'env>(
    arg: &ExecTypeArg<'env>,
    oracle: &'env SymOracle<'env>,
    involved_structs: &mut HashMap<SymStructId, HashMap<Vec<ExecTypeArg<'env>>, String>>,
    analyzed_structs: &mut HashMap<String, ExecStructInfo<'env>>,
) {
    match arg {
        ExecTypeArg::Bool
        | ExecTypeArg::U8
        | ExecTypeArg::U64
        | ExecTypeArg::U128
        | ExecTypeArg::Address
        | ExecTypeArg::Signer => {}
        ExecTypeArg::Vector { element_type } => {
            collect_involved_structs_in_type_arg(
                element_type.as_ref(),
                oracle,
                involved_structs,
                analyzed_structs,
            );
        }
        ExecTypeArg::Struct {
            struct_info,
            type_args,
        } => {
            collect_involved_structs_recursive(
                struct_info,
                type_args,
                oracle,
                involved_structs,
                analyzed_structs,
            );
        }
        ExecTypeArg::Reference { referred_type, .. } => {
            collect_involved_structs_in_type_arg(
                referred_type.as_ref(),
                oracle,
                involved_structs,
                analyzed_structs,
            );
        }
        ExecTypeArg::TypeParameter { actual_type, .. } => {
            collect_involved_structs_in_type_arg(
                actual_type.as_ref(),
                oracle,
                involved_structs,
                analyzed_structs,
            );
        }
    }
}
