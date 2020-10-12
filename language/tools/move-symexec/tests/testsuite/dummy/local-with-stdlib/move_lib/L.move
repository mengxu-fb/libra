address 0x42 {
module L {
    use 0x1::Debug;
    use 0x1::Vector;

    public fun foo()  {
        let v = Vector::empty();
        Vector::push_back(&mut v, 1);
        Vector::push_back(&mut v, 2);
        Vector::push_back(&mut v, 3);
        Debug::print(&v);
    }
}
}
