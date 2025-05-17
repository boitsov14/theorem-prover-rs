# For windows compatibility
set windows-shell := ["C:\\Program Files\\Git\\bin\\sh.exe","-c"]

# Update everything: Rust toolchain, project dependencies, and global tools
# Note: -i means "allow incompatible upgrades"
# Requires cargo-edit and cargo-update
update:
    rustup update stable
    cargo upgrade -i allow
    cargo update
    cargo install-update -a

# Format code
fmt:
    cargo +nightly fmt

# Lint code
lint:
    cargo clippy --all-targets --all-features

# Run the project with arguments
# Use -- to separate cargo arguments from application arguments
run *ARGS:
    cargo run -- {{ARGS}}

# Run the project with arguments in release mode
run-release *ARGS:
    cargo run --release -- {{ARGS}}

# Run tests
test:
    cargo test -- --nocapture

# Run benchmarks
bench FILTER='':
    cargo bench --features bench -- {{FILTER}}

# Run flamegraph
# Requires admin
flame:
    cargo flamegraph --profile profiling

# Build in profiling mode
build-profiling:
    cargo build --profile profiling

# Run samply
samply:
    samply record --rate 1000000 ./target/profiling/theorem-prover-rs.exe

# Add dependency to Cargo.toml
add package:
    cargo add {{package}}

# Add dependency to Cargo.toml with specific features
add-features package +FEATURES:
    cargo add {{package}} --features {{FEATURES}}

# Install binary package globally
# Requires cargo-binstall
binstall package:
    cargo binstall {{package}}

# List globally installed packages
list-global:
    cargo install --list

# Clean the target directory
clean:
    cargo clean

# Update Rust toolchain including nightly
update-rust-all:
    rustup update

# Cross-compile for Linux
# Requires cross
cross-build:
    cross build --release --target x86_64-unknown-linux-gnu
