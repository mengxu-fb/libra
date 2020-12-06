address 0x42 {
module M {
    resource struct R {
        v: u8,
    }

    public fun foo(i: u8): R {
        R { v: i }
    }

    public fun bar(r: R): u8 {
        let R {v} = r;
        v
    }
}
}

script {
    use 0x42::M;

    fun main(i: u8) {
        let r = M::foo(i);
        let _ = M::bar(r);
    }
}
