address 0x42 {
module M {
    public fun foo() {}
}
}

script {
    use 0x42::M;

    fun main() {
        M::foo();
    }
}
