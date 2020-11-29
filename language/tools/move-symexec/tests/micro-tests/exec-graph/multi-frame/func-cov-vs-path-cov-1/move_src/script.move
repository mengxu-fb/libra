address 0x42 {
module M {
    fun bar(v: u8): u8 {
        if (v == 42) { 0 } else { v }
    }

    public fun foo(x: u8): u8 {
        if (x == 0) { bar(42) } else { bar(x) }
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8) {
        assert(x == M::foo(x), 1);
    }
}
