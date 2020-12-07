address 0x42 {
module M {
    struct S {
        v: u8,
    }

    public fun foo(x: u8): S {
        S { v: x }
    }

    public fun bar(s: &S): u8 {
        s.v
    }

    public fun baz(s: &mut S, y: u8) {
        s.v = y;
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8, y: u8) {
        let s = M::foo(x);
        let _ = M::bar(&s);
        M::baz(&mut s, y);
        let _ = M::bar(&s);
    }
}
