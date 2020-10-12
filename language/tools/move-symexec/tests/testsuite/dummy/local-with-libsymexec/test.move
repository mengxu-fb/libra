script {
use 0x1::Symbolic;
use 0x42::M;

fun main() {
    M::foo(Symbolic::mark_u8(0));
}
}
