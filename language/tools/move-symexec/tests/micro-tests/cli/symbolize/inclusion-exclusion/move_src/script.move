script {
    use 0x42::L;
    use 0x43::M;

    fun main() {
        L::foo();
        L::bar();
        M::foo();
        M::baz();
    }
}
