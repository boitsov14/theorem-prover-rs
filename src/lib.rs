mod cli;
mod intern;
mod lang;
mod parser;
mod prover;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn main_prover() {
    cli::cli();
}
