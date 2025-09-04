mod app;
mod intern;
mod lang;
mod parser;
mod prover;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn run() {
    app::run();
}
