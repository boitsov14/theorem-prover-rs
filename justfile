###################################
# Basic configuration
###################################

# For windows compatibility
set windows-shell := ["C:\\Program Files\\Git\\bin\\sh.exe", "-c"]

# Ignore recipe lines beginning with #.
set ignore-comments := true

# Format justfile
j-fmt:
    j --fmt --unstable

###################################
# Update
###################################

# Update everything: Rust toolchain, project dependencies, and global tools
# Note: -i means "allow incompatible upgrades"
# Requires cargo-edit and cargo-update
update:
    cargo --version
    rustup update stable
    cargo upgrade -i allow
    cargo update
    cargo install-update -a

# Update Rust toolchain including nightly
update-rust-all:
    rustup update

###################################
# Formatter and Linter
###################################

# Format code
fmt:
    cargo +nightly fmt

# Lint code
lint:
    j fmt
    cargo clippy --all-targets --all-features

# Lint code allowing dead_code warnings
lint2:
    j fmt
    RUSTFLAGS="-A dead_code" cargo clippy --all-targets --all-features

###################################
# Run
###################################

# Run the project
run:
    -rm tmp/*.{log,tex,yaml,err}
    cargo run -- --out "tmp"

# Run the project in release mode
run-release:
    -rm tmp/*.{log,tex,yaml,err}
    cargo run --release -- --out "tmp"

# Latex build
tex FILE:
    -rm tex/*
    cp tmp/{{ FILE }}.tex tex/out.tex
    pdflatex -halt-on-error -interaction=nonstopmode -output-directory tex tex/out.tex

###################################
# Tests
###################################

# Run tests
# --no-fail-fast: Do not exit the test run until all tests complete.
# cargo nextest run -p my-package
# cargo nextest run <test-name1> <test-name2>...
# cargo nextest run --no-capture
test FILTER='':
    cargo nextest run --no-fail-fast {{ FILTER }}

# Generate code coverage report
cov:
    cargo +nightly llvm-cov nextest --release --branch --open

# Insta test
# cargo insta accept: Accept all snapshots
# cargo insta test --test-runner nextest: no review
# INSTA_UPDATE=unseen: if new, create .snap. if present, create .snap.new
# --unreferenced=warn: warn if there are unused snapshots left
# -- test_latex_snapshot::_props_expects: specify which snapshot to test
# --review: cargo insta test + cargo insta review
# find . -name "*.snap.new" -delete: delete .new files
insta:
    INSTA_UPDATE=unseen cargo insta test --test-runner nextest --unreferenced=warn

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

###################################
# Benchmark
###################################

# Run benchmarks
bench FILTER='':
    cargo bench --features bench -- {{ FILTER }}

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

###################################
# Dependencies
###################################

# Add dependency to Cargo.toml
add package:
    cargo add {{ package }}

# Add dependency to Cargo.toml with specific features
add-features package +FEATURES:
    cargo add {{ package }} --features {{ FEATURES }}

# Install binary package globally
# Requires cargo-binstall
binstall package:
    cargo binstall {{ package }}

# List globally installed packages
list-global:
    cargo install --list

# Detect unused dependencies
machete:
    cargo machete

###################################
# Build
###################################

# Build for Linux
build:
    cargo build --release
    cargo build --profile trace
    MSYS_NO_PATHCONV=1 docker run --rm -v "$(pwd):/app" -w /app rust:slim cargo build --release --target x86_64-unknown-linux-gnu
    MSYS_NO_PATHCONV=1 docker run --rm -v "$(pwd):/app" -w /app rust:slim cargo build --profile trace --target x86_64-unknown-linux-gnu

###################################
# Utils
###################################

# Clean the target directory
clean:
    cargo clean
