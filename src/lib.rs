mod lang;
pub mod name;
pub mod new_prover;
pub mod new_prover2;
pub mod parser;
pub mod prover;
mod unification;

use lang::Sequent;
use lang::SequentOwned;
use name::Names;
use typed_arena::Arena;

pub fn read_file_and_parse<'a>(
    path: &str,
    arena: &'a Arena<SequentOwned>,
) -> Vec<(Sequent<'a>, Names)> {
    use crate::parser::parse_sequent;
    use std::fs;

    fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter(|s| !s.is_empty() && !s.starts_with('#'))
        .map(|s| {
            let mut names = Names::default();
            let seq = arena.alloc(parse_sequent(s, &mut names, true, false).unwrap());
            let seq = seq.to_seq();
            (seq, names)
        })
        .collect()
}
