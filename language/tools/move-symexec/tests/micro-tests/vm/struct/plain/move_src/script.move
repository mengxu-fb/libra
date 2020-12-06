address 0x42 {
module M {
    struct S {
        v: u8,
    }

    public fun foo(i: u8): S {
        S { v: i }
    }

    public fun bar(s: S): u8 {
        s.v
    }
}
}

script {
    use 0x42::M;

    fun main(i: u8) {
        let s = M::foo(i);
        let _ = M::bar(s);
    }
}
