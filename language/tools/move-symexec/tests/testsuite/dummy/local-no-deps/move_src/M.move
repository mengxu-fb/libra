address 0x42 {
module M {
    use 0x42::L;
    public fun foo()  {
        L::foo()
    }
}
}
