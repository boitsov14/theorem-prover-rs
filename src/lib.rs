mod app;
mod core {
    pub mod names;
    pub mod parser;
    pub mod syntax;
}
mod prover {
    mod bench;
    mod kernel;
    mod latex {
        mod ebproof;
        mod forest;
        #[cfg(test)]
        mod test;
        pub use ebproof::{Latex, SequentCalculusLatexError, sequent_calculus};
        pub use forest::{ForestLatexError, forest};
    }
    mod sequent;
    pub use kernel::prove_prop;
    pub use latex::{ForestLatexError, Latex, SequentCalculusLatexError, forest, sequent_calculus};
    pub use sequent::Sequent;
}
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn run() {
    app::run();
}
