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
fun main(i: u8) {
    let s = M::foo(i);
    assert(M::bar(s) == i, 1);
}
}
