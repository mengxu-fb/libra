address 0x42 {
module M {
    public fun baz<X: copyable, Y: copyable>(x: X, _y: Y, depth: u8) {
        if (depth != 0) {
            baz(0u128, copy x, depth - 1);
        }
    }
}
}

script {
    use 0x42::M;

    fun main(depth: u8) {
        M::baz(1u8, 2u64, depth);
    }
}
