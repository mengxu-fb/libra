# bare metal
cargo run -- args.txt -v --no-stdlib

# with stdlib
cargo run -- args.txt -v --no-libnursery

# default
cargo run -- args.txt -v

# with libra
cargo run -- args.txt -v --use-libra burn
