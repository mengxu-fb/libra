address 0x42 {
module M {
    use 0x42::L;
    public fun foo(v: u8)  {
        if (v == 0) {
            L::foo()
        } else {
            L::bar()
        }
    }
}
}
