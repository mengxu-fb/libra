address 0x42 {
module M {
    resource struct R {
        v: u8,
    }

    public fun foo(x: u8): R {
        R { v: x }
    }

    public fun bar(r: R): u8 {
        let R {v} = r;
        v
    }

    public fun baz(r: &mut R, y: u8) {
        r.v = y;
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8, y: u8) {
        let r = M::foo(x);
        M::baz(&mut r, y);
        let _ = M::bar(r);
    }
}
