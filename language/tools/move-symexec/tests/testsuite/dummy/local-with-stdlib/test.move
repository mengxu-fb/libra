script {
use 0x1::Debug;
use 0x1::Vector;
use 0x42::M;

fun main() {
    M::foo();

    let v = Vector::empty();
    Vector::push_back(&mut v, 100);
    Vector::push_back(&mut v, 200);
    Vector::push_back(&mut v, 300);
    Debug::print(&v);
}
}
