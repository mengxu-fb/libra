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

/// Default path to directory containing stdlib (pre-built)
pub static MOVE_STDLIB_BIN: Lazy<String> = Lazy::new(|| {
    join_path_items!(
        env!("CARGO_MANIFEST_DIR"),
        "..",
        "..",
        "stdlib",
        "compiled",
        "stdlib"
    )
});

/// Default path to directory containing stdlib (source)
pub static MOVE_STDLIB_SRC: Lazy<String> =
    Lazy::new(|| join_path_items!(env!("CARGO_MANIFEST_DIR"), "..", "..", "stdlib", "modules"));
