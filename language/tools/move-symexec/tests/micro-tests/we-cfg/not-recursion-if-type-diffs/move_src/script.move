address 0x42 {
module M {
    public fun foo<X: copyable, Y: copyable>(x: X, y: Y, depth: u8) {
        if (depth != 0) {
            foo(copy y, copy x, depth - 1);
            foo(x"dead", x"beef", depth - 1);
            foo(0u128, copy x, depth - 1);
        }
    }
}
}

script {
use 0x42::M;
fun main(depth: u8) {
    M::foo(1u8, 2u64, depth);
}
}
