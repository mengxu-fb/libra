address 0x42 {
module M {
    struct S {
        v: u8,
    }

    public fun foo1(x: u8): S {
        S { v: x }
    }

    public fun foo2(y: u8): S {
        S { v: y }
    }

    public fun bar(s: &S): u8 {
        s.v
    }

    public fun baz(s: &mut S, z: u8) {
        s.v = z;
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8, y: u8, z: u8) {
        let s1 = M::foo1(x);
        let s2 = M::foo2(y);
        let s = if (x == y) { &mut s1 } else { &mut s2 };
        let _ = M::bar(s);
        M::baz(s, z);
        let _ = M::bar(&s1);
        let _ = M::bar(&s2);
    }
}
