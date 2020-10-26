script {
fun main(x: u8) {
    let y = if (x == 42) { 0 } else { x };
    assert(y == x, 1);
}
}
