// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]

use once_cell::sync::Lazy;

/// Default path to directory containing libsymexec
pub static MOVE_LIBSYMEXEC: Lazy<String> =
    Lazy::new(|| join_path_items!(env!("CARGO_MANIFEST_DIR"), "libsymexec"));

/// Default path to directory containing nursery (source)
pub static MOVE_LIBNURSERY: Lazy<String> =
    Lazy::new(|| join_path_items!(env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "nursery"));

/// Default path to directory containing stdlib modules (pre-built)
pub static MOVE_STDLIB_BIN_MODULES: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "..",
        "..",
        "stdlib",
        "compiled",
        "stdlib"
    )
});

/// Default path to directory containing stdlib scripts (pre-built)
pub static MOVE_STDLIB_BIN_SCRIPTS: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "..",
        "..",
        "stdlib",
        "compiled",
        "transaction_scripts"
    )
});

/// Default path to directory containing stdlib modules (source)
pub static MOVE_STDLIB_SRC_MODULES: Lazy<String> =
    Lazy::new(|| join_path_items!(env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "modules"));

/// Default path to directory containing stdlib scripts (source)
pub static MOVE_STDLIB_SRC_SCRIPTS: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "..",
        "..",
        "stdlib",
        "transaction_scripts"
    )
});

/// Default file extension for Move source file
pub const MOVE_SRC_EXT: &str = "move";

/// Default file extension for Move compiled bytecode (module or script)
pub const MOVE_BIN_EXT: &str = "mv";
