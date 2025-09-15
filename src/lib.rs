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
        pub use ebproof::{Latex, sequent_calculus};
        pub use forest::forest;
    }
    mod sequent;
    pub use kernel::prove_prop;
    pub use latex::{Latex, forest, sequent_calculus};
    pub use sequent::Sequent;
}
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn run() {
    app::run();
}
