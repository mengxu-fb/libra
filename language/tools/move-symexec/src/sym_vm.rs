// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker},
    sym_smtlib::SmtCtxt,
    sym_vm_types::SymTransactionArgument,
};

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {
    smt_ctxt: SmtCtxt,
}

impl SymVM {
    pub fn new() -> Self {
        Self {
            smt_ctxt: SmtCtxt::new(),
        }
    }

    pub fn interpret(&self, exec_graph: &ExecGraph, sym_val_args: &[SymTransactionArgument]) {
        // run the walker
        let mut walker = ExecWalker::new(exec_graph);
        while walker.next().is_some() {}
    }
}
