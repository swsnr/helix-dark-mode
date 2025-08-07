default:
    just --list

vet *ARGS:
    cargo +stable vet {{ARGS}}

test-all:
    just vet --locked
    cargo +stable deny --all-features --locked check
    cargo +stable fmt -- --check
    cargo +stable build --all-targets --locked
    cargo +stable clippy --all-targets --locked
    cargo +stable test --locked
