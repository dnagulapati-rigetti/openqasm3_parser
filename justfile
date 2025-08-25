default:
    @just --list

# One-stop CI-ish local run
ci:
    cargo fmt --all -- --check
    cargo build --release --verbose
    cargo test --verbose --lib --tests
    cargo clippy --all-targets --all-features -- -D warnings -D clippy::dbg_macro

sourcegen:
    cargo clean
    cargo build -p oq3_syntax --features sourcegen
    cargo fmt -p oq3_syntax -p oq3_parser

assert_empty_git_status:
  # use git status --porcelain

check_sourcegen: assert_empty_git_status sourcegen assert_empty_git_status