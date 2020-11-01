address 0x42 {
module M {
    public fun foo(depth: u8) {
        if (depth != 0) {
            foo(depth - 1);
        }
    }
}
}

script {
use 0x42::M;
fun main(depth: u8) {
    M::foo(depth);
}
}
