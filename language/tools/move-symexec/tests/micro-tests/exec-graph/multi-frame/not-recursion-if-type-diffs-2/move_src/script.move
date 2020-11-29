address 0x42 {
module M {
    public fun bar<X: copyable, Y: copyable>(_x: X, _y: Y, depth: u8) {
        if (depth != 0) {
            bar(x"dead", x"beef", depth - 1);
        }
    }
}
}

script {
    use 0x42::M;

    fun main(depth: u8) {
        M::bar(1u8, 2u64, depth);
    }
}
