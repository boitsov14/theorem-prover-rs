mod formula;
mod naming;
mod parser;
mod prover;
mod unification;

pub use crate::parser::{modify_tptp, parse};
pub use crate::prover::{example, example_iltp_prop};
