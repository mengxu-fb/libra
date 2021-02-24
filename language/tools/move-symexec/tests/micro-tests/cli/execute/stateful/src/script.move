script {
    use 0x42::M;

    fun main(account: &signer, x: u64) {
        M::deposit(account, x)
    }
}
