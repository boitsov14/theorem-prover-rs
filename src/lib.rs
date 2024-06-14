mod lang;
mod name;
mod parser;
mod prover;
mod unification;

pub use crate::name::Names;
pub use crate::parser::parse_sequent;
pub use crate::prover::{example, example_iltp_prop};
