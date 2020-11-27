// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! This package aims for building an extended control-flow graph (eCFG) that encloses both script
//! and module per-function CFGs, i.e., a super graph that has CFGs connected by the call graph.

use itertools::Itertools;
use std::fmt;

use bytecode::stackless_bytecode::Bytecode;
use vm::file_format::CodeOffset;

use crate::{sym_oracle::SymFuncInfo, sym_typing::ExecTypeArg};

/// This id uniquely identifies a basic block in the eCFG
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct ExecBlockId(usize);

/// This is the basic block (i.e., the node) in the eCFG
pub(crate) struct ExecBlock<'env> {
    /// A unique identifier for the exec block
    pub block_id: ExecBlockId,
    /// The context (module, function) where this block lives
    pub code_context: &'env SymFuncInfo<'env>,
    /// The starting offset of the instructions in code context
    ///
    /// NOTE: A None value means that this is an arbitrary block which will host no instructions.
    /// However, not all arbitrary blocks have None as code_offset, those that do host instructions
    /// will have a valid code_offset.
    pub code_offset: Option<CodeOffset>,
    /// The type argument for the function in the code context
    pub type_args: Vec<ExecTypeArg>,
    /// The instructions within this basic block. It is OK to be empty.
    pub instructions: Vec<&'env Bytecode>,
}

impl<'env> fmt::Display for ExecBlock<'env> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // block head
        write!(
            f,
            "[{} - {}::{} <{}>]",
            self.block_id.0,
            self.code_context.get_context_string(),
            self.code_offset
                .map_or_else(|| String::from("X"), |offset| offset.to_string()),
            self.type_args
                .iter()
                .map(|ty_arg| ty_arg.to_string())
                .join(", ")
        )?;

        // block content
        for instruction in self.instructions.iter() {
            writeln!(
                f,
                "{}",
                instruction.display(&self.code_context.get_function_target())
            )?;
        }

        // done
        Ok(())
    }
}
