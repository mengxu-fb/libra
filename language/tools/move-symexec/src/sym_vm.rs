// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use std::collections::HashSet;

use vm::file_format::Signature;

use crate::{
    sym_exec_graph::{ExecGraph, ExecWalker},
    sym_smtlib::SmtCtxt,
    sym_vm_types::{SymTransactionArgument, SymValue},
};

/// The symbolic interpreter that examines instructions one by one
pub(crate) struct SymVM {
    /// A wrapper over the smt solver context manager
    smt_ctxt: SmtCtxt,
    /// A map from variable names to exprs
    vars_set: HashSet<String>,
}

impl SymVM {
    pub fn new() -> Self {
        Self {
            smt_ctxt: SmtCtxt::new(),
            vars_set: HashSet::new(),
        }
    }

    pub fn interpret(
        &self,
        exec_graph: &ExecGraph,
        val_arg_sigs: &Signature,
        sym_val_args: &[SymTransactionArgument],
    ) {
        // run the walker
        let mut walker = ExecWalker::new(exec_graph);
        while walker.next().is_some() {}
    }
}
