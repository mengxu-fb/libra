// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};

use move_core_types::{
    parser::parse_transaction_argument, transaction_argument::TransactionArgument,
};

/// A holder for arguments that could be either symbolic or concrete
pub enum SymTransactionArgument {
    Concrete(TransactionArgument),
    Symbolic(String),
}

/// A utility parser that convert strings to symbolic argument
pub fn parse_sym_transaction_argument(s: &str) -> Result<SymTransactionArgument> {
    let tokens: Vec<&str> = s.split("::").collect();
    if tokens.len() != 2 {
        bail!("Invalid symbolic transaction argument");
    };

    if tokens[0] == "C" {
        Ok(SymTransactionArgument::Concrete(
            parse_transaction_argument(tokens[1])?,
        ))
    } else if tokens[0] == "S" {
        Ok(SymTransactionArgument::Symbolic(tokens[1].to_owned()))
    } else {
        bail!("Invalid symbolic transaction argument");
    }
}
