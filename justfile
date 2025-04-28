# Update everything: Rust toolchain, project dependencies, and global tools
# Note: -i means "allow incompatible upgrades"
# Requires cargo-edit and cargo-update
update:
    rustup update stable
    cargo upgrade -i allow
    cargo update
    cargo install-update -a

# Format code
format:
    cargo +nightly fmt

# Lint code
lint:
    cargo clippy --all-targets --all-features

# Run the project with arguments
# Use -- to separate cargo arguments from application arguments
run *ARGS:
    cargo run -- {{ARGS}}

# Run tests
test:
    cargo test -- --nocapture

# Run benchmarks
bench filter='':
    cargo bench --features bench {{ if filter != "" { "-- \"" + filter + "\"" } else { "" } }}

# Add dependency to Cargo.toml
add package:
    cargo add {{package}}

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
