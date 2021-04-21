// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::assembly::display::{AstDebug, AstWriter};

pub struct Assembly {}

impl AstDebug for Assembly {
    fn ast_debug(&self, w: &mut AstWriter) {
        w.block(|w| w.write("<empty>"))
    }
}
