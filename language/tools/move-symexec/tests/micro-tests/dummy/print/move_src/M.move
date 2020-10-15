address 0x42 {
module M {
    use 0x1::Debug;
    use 0x1::Vector;
    use 0x42::L;

    public fun foo(a: u8)  {
        if (a == 0) {
            L::foo()
        } else {
            let v = Vector::empty();
            Vector::push_back(&mut v, 10);
            Vector::push_back(&mut v, 20);
            Vector::push_back(&mut v, 30);
            Debug::print(&v);
        }
    }
}
}
