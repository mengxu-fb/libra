# bare metal
cargo run -- args.txt -v --no-stdlib

# with stdlib
cargo run -- args.txt -v --no-libnursery

# default
cargo run -- args.txt -v

# with diem
cargo run -- args.txt -v --use-diem burn
