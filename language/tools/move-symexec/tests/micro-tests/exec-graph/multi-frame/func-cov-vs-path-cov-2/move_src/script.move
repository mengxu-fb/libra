address 0x42 {
module M {
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
