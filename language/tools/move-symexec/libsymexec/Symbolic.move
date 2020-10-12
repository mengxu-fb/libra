address 0x1 {

/// The Symbolic module defines a collection of functions that mark
/// values as symbolic. Any value marked as symbolic will be a variable
/// that can be solved for in order to satisfy a specific set of path
/// constraints, with the intention of exploring new code paths. A
/// symbolic value also has a concrete default (passed in as function
/// argument) to maintain compatibility of concrete execution.
module Symbolic {
    public fun mark_u8(val: u8): u8 {
        val
    }

    public fun mark_u64(val: u64): u64 {
        val
    }

    public fun mark_u128(val: u128): u128 {
        val
    }

    public fun mark_bool(val: bool): bool {
        val
    }

    public fun mark_address(val: address): address {
        val
    }
}

}
