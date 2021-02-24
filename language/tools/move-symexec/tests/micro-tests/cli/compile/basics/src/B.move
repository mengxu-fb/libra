address 0x42 {
module B {
    use 0x42::A;

    public fun bar() {
        A::foo()
    }
}
}
