address 0x42 {
module M {
    public fun foo(): u8 {
        42
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8) {
        assert(x == M::foo(), 1);
    }
}
