// Copyright (c) The Libra Core Contributors
// SPDX-License-Identifier: Apache-2.0

#![macro_use]

use once_cell::sync::Lazy;
use std::path::PathBuf;

#[macro_export]
/// A macro utility to get compile-time paths relative to the crate
macro_rules! crate_path {
    ($name:ident, $($item:expr),*) => {
        pub static $name: Lazy<PathBuf> = Lazy::new(
            || [env!("CARGO_MANIFEST_DIR") $(,$item)*].iter().collect()
        );
    }
}

// Default path to directory containing libsymexec
crate_path!(MOVE_LIBSYMEXEC, "libsymexec");

// Default path to directory containing nursery (source)
crate_path!(MOVE_LIBNURSERY, "..", "..", "stdlib", "nursery");

// Default path to directory containing stdlib modules (source)
crate_path!(MOVE_STDLIB_SRC_MODULES, "..", "..", "stdlib", "modules");

// Default path to directory containing stdlib modules (pre-built)
crate_path!(
    MOVE_STDLIB_BIN_MODULES,
    "..",
    "..",
    "stdlib",
    "compiled",
    "stdlib"
);

// Default path to directory containing libra scripts (source)
crate_path!(
    MOVE_LIBRA_SRC_SCRIPTS,
    "..",
    "..",
    "stdlib",
    "transaction_scripts"
);

// Default path to directory containing libra scripts (pre-built)
crate_path!(
    MOVE_LIBRA_BIN_SCRIPTS,
    "..",
    "..",
    "stdlib",
    "compiled",
    "transaction_scripts"
);

/// A macro utility to get compile-time paths relative to the crate in String type
#[macro_export]
macro_rules! crate_path_string {
    ($name:ident, $($item:expr),*) => {
        static $name: Lazy<String> = Lazy::new(
            || [env!("CARGO_MANIFEST_DIR") $(,$item)*]
                .iter()
                .collect::<PathBuf>()
                .into_os_string()
                .into_string()
                .unwrap()
        );
    }
}
