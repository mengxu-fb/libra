script {
use 0x1::Vector;
fun main(i: vector<u8>) {
    let x = x"42";
    assert(copy i == copy x, 1);

    let y = &mut i;
    *y = x"00";
    assert(&x != y, 2);

    let z = Vector::borrow(&x, 0);
    assert(*z == 66, 3);
}
}
