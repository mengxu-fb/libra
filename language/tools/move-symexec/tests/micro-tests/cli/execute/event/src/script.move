script {
    use 0x42::M;

    fun main(account: &signer, i: u64) {
        M::emit(account, i)
    }
}
