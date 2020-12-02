address 0x42 {
module M {
    struct S<T> {
        v: T,
    }

    public fun foo<T>(i: T): S<T> {
        S { v: i }
    }

    public fun bar<T: copyable>(s: S<T>): T {
        *&s.v
    }
}
}

script {
    use 0x42::M;

    fun main() {
        let s1 = M::foo(0u8);
        assert(M::bar(s1) == 0u8, 1);

        let s2 = M::foo(0u64);
        assert(M::bar(s2) == 0u64, 1);
    }
}
