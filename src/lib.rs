mod intern;
mod lang;
mod parser;
mod prover;

use intern::Names;
use lang::OwnedSplitSequent;
use lang::SplitSequent;
use typed_arena::Arena;

pub use prover::prove_prop;

pub fn read_file_and_parse<'a>(
    path: &str,
    arena: &'a Arena<OwnedSplitSequent>,
) -> Vec<(SplitSequent<'a>, Names)> {
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
