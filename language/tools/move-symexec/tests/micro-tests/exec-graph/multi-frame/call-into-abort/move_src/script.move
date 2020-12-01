address 0x42 {
module M {
    public fun foo() {
        abort 42
    }
}
}

script {
    use 0x42::M;

    fun main() {
        M::foo()
    }
}
