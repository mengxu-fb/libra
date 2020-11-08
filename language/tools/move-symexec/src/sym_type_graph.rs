// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::{
    algo::{is_cyclic_directed, toposort},
    graph::{Graph, NodeIndex},
};
use std::collections::HashMap;

use crate::sym_setup::{ExecStructInfo, ExecTypeArg, StructContext};

/// Records the dependency relationship between the types, especially
/// structs, involved in the execution.
#[derive(Clone, Debug)]
pub(crate) struct TypeGraph {
    involved_structs: HashMap<StructContext, HashMap<Vec<ExecTypeArg>, String>>,
    analyzed_structs: HashMap<String, ExecStructInfo>,
    graph: Graph<String, ()>,
}

impl TypeGraph {
    fn link(
        variant_name: &str,
        variant_type_arg: &ExecTypeArg,
        involved_structs: &HashMap<StructContext, HashMap<Vec<ExecTypeArg>, String>>,
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
            ExecTypeArg::Struct { context, type_args } => {
                let dep_name = involved_structs
                    .get(context)
                    .unwrap()
                    .get(type_args)
                    .unwrap();
                let dep_node_id = graph_node_map.get(dep_name).unwrap();
                let src_node_id = graph_node_map.get(variant_name).unwrap();
                graph.add_edge(*src_node_id, *dep_node_id, ());
            }
            ExecTypeArg::Reference { referred_type }
            | ExecTypeArg::MutableReference { referred_type } => {
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

    pub fn new(
        involved_structs: HashMap<StructContext, HashMap<Vec<ExecTypeArg>, String>>,
        analyzed_structs: HashMap<String, ExecStructInfo>,
    ) -> Self {
        let mut graph = Graph::new();

        // create nodes
        let mut node_map: HashMap<String, NodeIndex> = HashMap::new();
        for variant_name in analyzed_structs.keys() {
            node_map.insert(variant_name.clone(), graph.add_node(variant_name.clone()));
        }

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

    pub fn reverse_topological_sort(&self) -> Vec<(&str, &ExecStructInfo)> {
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
        context: &StructContext,
        type_args: &[ExecTypeArg],
    ) -> Option<&str> {
        self.involved_structs
            .get(context)
            .map(|struct_variants| {
                struct_variants
                    .get(type_args)
                    .map(|struct_name| struct_name.as_str())
            })
            .flatten()
    }

    pub fn get_struct_info_by_name(&self, name: &str) -> &ExecStructInfo {
        self.analyzed_structs.get(name).unwrap()
    }
}
