address 0x42 {
module L {
    use 0x1::Debug;
    public fun foo()  {
        Debug::print(&1);
    }

    public fun bar() {
        Debug::print(&2);
    }
}
}
