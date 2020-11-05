// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use petgraph::graph::{Graph, NodeIndex};
use std::collections::HashMap;

use crate::sym_setup::{ExecStructInfo, ExecTypeArg, StructContext};

/// Records the dependency relationship between the types, especially
/// structs, involved in the execution.
#[derive(Clone, Debug)]
pub(crate) struct TypeGraph {
    graph: Graph<String, ()>,
}

impl TypeGraph {
    pub fn new(
        involved_structs: HashMap<StructContext, HashMap<Vec<ExecTypeArg>, String>>,
        analyzed_structs: HashMap<String, ExecStructInfo>,
    ) -> Self {
        let mut graph = Graph::new();

        // create nodes
        let mut node_map: HashMap<String, NodeIndex> = HashMap::new();
        for struct_variants in involved_structs.values() {
            for variant_name in struct_variants.values() {
                let exists =
                    node_map.insert(variant_name.clone(), graph.add_node(variant_name.clone()));
                debug_assert!(exists.is_none());
            }
        }

        // TODO: experimental
        println!("Number of structs: {}", analyzed_structs.len());

        // done
        Self { graph }
    }
}
