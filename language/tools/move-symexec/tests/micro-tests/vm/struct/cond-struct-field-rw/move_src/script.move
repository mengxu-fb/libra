address 0x42 {
module M {
    struct S {
        x: u8,
        y: u8,
    }

    public fun foo(x: u8, y: u8): S {
        S { x, y }
    }

    public fun bar(s: &mut S, x: u8, y: u8) {
        let f = if (x == y) { &mut s.x } else { &mut s.y };
        *f = 0;
    }
}
}

script {
    use 0x42::M;

    fun main(x: u8, y: u8) {
        let s = M::foo(x, y);
        M::bar(&mut s, x, y);
    }
}
