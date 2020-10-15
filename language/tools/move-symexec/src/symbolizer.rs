// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use vm::file_format::{CompiledModule, CompiledScript};

use crate::{sym_exec_graph::ExecGraph, sym_setup::SymSetup};

/// The symbolizer
#[derive(Clone, Debug)]
pub(crate) struct MoveSymbolizer {}

impl MoveSymbolizer {
    pub fn new(
        script: &CompiledScript,
        tracked_modules: &[CompiledModule],
        setup: &SymSetup,
    ) -> Self {
        ExecGraph::new(setup, script, tracked_modules);
        MoveSymbolizer {}
    }
}
