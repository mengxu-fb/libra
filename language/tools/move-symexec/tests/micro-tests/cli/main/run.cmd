# bare metal
cargo run -- args.txt -v --no-stdlib --no-libsymexec

# with stdlib
cargo run -- args.txt -v --no-libnursery --no-libsymexec

# with nursery
cargo run -- args.txt -v --no-libsymexec

# default
cargo run -- args.txt -v

# with libra
cargo run -- args.txt -v --use-libra burn

# all fresh build
cargo run -- args.txt -v --track-stdlib --use-libra burn --track-libra
