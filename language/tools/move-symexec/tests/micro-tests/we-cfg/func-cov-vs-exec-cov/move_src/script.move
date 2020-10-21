address 0x42 {
module M {
    fun bar(v: u8): u8 {
        if (v == 42) { 0 } else { v }
    }

    public fun foo(x: u8): u8 {
        if (x == 0) { bar(42) } else { bar(x) }
    }

    public fun foobar(x: u8): u8 {
        if (x == 0) {
            if (x == 42) { 0 } else { x }
        } else {
            if (x == 42) { 0 } else { x }
        }
    }
}
}

script {
use 0x42::M;
fun main(x: u8) {
    assert(x == M::foobar(x), 1);
}
}

script {
use 0x42::M;
fun main(x: u8) {
    assert(x == M::foo(x), 1);
}
}
