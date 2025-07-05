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
# --no-fail-fast: Do not exit the test run until all tests complete.
# --cargo-quiet ×2: Suppress cargo output.
# cargo nextest run -p my-package
# cargo nextest run <test-name1> <test-name2>...
# cargo nextest run --no-capture
test:
    cargo nextest run --no-fail-fast --cargo-quiet --cargo-quiet

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

# Latex build
tex FILE:
    rm tex/*
    cp {{FILE}}.tex tex/out.tex
    pdflatex -halt-on-error -interaction=nonstopmode -output-directory tex tex/out.tex

# Detect unused dependencies
machete:
    cargo machete

# Generate code coverage report
cov:
    cargo +nightly llvm-cov nextest --branch --open

# Insta test
# cargo insta accept: Accept all snapshots
# cargo insta test --test-runner nextest: no review
insta:
    INSTA_UPDATE=unseen cargo insta test --test-runner nextest --review --unreferenced=reject -- test_latex_snapshot

# Build all snapshots to PNG images
tex-insta:
    #!/bin/bash
    # exit immediately on any error
    set -euo pipefail
    # delete old png
    rm examples/snapshots/*.png
    # process each snapshot file
    for snap in snapshots/*.snap; do
        name=$(basename "$snap" .snap)
        # extract tex content (skip first 4 lines)
        tail -n +5 "$snap" > examples/snapshots/"$name".tex
        # build pdf
        pdflatex -halt-on-error -interaction=nonstopmode -output-directory examples/snapshots examples/snapshots/"$name".tex
        # convert to png
        gswin64c -dBATCH -dNOPAUSE -r600 -sDEVICE=pngmono -o examples/snapshots/"$name".png examples/snapshots/"$name".pdf
        # cleanup temp files
        rm examples/snapshots/"$name".{tex,aux,log,pdf}
    done
