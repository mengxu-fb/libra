// Copyright (c) The Diem Core Contributors
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

// Default path to directory containing nursery (source)
crate_path!(MOVE_LIBNURSERY, "..", "..", "stdlib", "nursery");

// Default path to directory containing stdlib modules (source)
crate_path!(MOVE_STDLIB_MODULES, "..", "..", "stdlib", "modules");

// Default path to directory containing diem scripts (source)
crate_path!(
    MOVE_DIEM_SCRIPTS,
    "..",
    "..",
    "stdlib",
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
