use crate::new_prover::sequent_grid::SequentGrid;
use crate::Names;

mod lang;
mod prover;
mod sequent_grid;

pub fn example_new(s: &str) {
    use crate::parser::parse_sequent;
    use std::time::Instant;

    // parse
    let mut entities = Names::default();
    let seq = match parse_sequent(s, &mut entities, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            println!("{e}");
            return;
        }
    };
    println!("{}", seq.display(&entities));

    let mut grid = SequentGrid::init(&seq.ant, &seq.suc);

    // prove
    let start_time = Instant::now();
    let result = grid.prove_prop();
    let end_time = Instant::now();
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
}
