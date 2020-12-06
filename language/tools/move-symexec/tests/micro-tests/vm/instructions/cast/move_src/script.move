script {
    fun main(x: u8) {
        let v_u64 = (x as u64);
        let v_u128 = (v_u64 as u128);
        let v_u8 = (v_u128 as u8);
        let _ = move v_u8;
    }
}
