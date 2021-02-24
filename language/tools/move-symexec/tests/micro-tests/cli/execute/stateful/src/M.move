address 0x42 {
module M {
    resource struct R<T: copyable> { v: T }

    public fun deposit<T: copyable>(account: &signer, v: T) {
        let r = R { v };
        move_to(account, r)
    }
}
}
