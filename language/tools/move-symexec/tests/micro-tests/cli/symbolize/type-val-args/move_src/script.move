script {
    use 0x1::Debug;

    fun main<T: copyable>(x: u8) {
        Debug::print(&x);
        assert(x == 0, 1);
    }
}
