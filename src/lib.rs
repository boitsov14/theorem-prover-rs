mod app;
mod core {
    pub mod names;
    pub mod parser;
    pub mod syntax;
}
mod prover {
    mod bench;
    mod countermodel;
    mod kernel;
    mod latex {
        mod sequent_calculus;
        mod tableau_method;
        #[cfg(test)]
        mod test;
        pub use sequent_calculus::{Latex, sequent_calculus};
        pub use tableau_method::tableau_method;
    }
    mod sequent;
    pub use countermodel::FormulaEvaluation;
    pub use kernel::{ProofResult, prove_prop};
    pub use latex::{Latex, sequent_calculus, tableau_method};
    pub use sequent::Sequent;
}
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn run() {
    app::run();
}
