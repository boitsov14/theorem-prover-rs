mod formula;
mod naming;
mod parser;
mod prover;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    prover::example().unwrap();
    // prover::example_iltp_prop();
}
