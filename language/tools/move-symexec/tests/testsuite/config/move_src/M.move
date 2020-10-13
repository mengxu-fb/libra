address 0x42 {
module M {
    use 0x1::Debug;
    public fun foo(v: u8)  {
        if (v == 0) {
            Debug::print(&0);
        } else {
            Debug::print(&42);
        }
    }
}
}
