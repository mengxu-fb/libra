script {
    use 0x1::Debug;

    fun main<T: copyable>(account1: &signer, account2: &signer, b: bool, u: u64) {
        Debug::print(&u);
        Debug::print(&b);
        Debug::print(account2);
        Debug::print(account1);
    }
}
