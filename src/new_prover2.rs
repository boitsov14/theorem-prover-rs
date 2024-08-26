use crate::new_prover2::prover::prove_prop;
use crate::Names;

mod lang;
mod prover;

pub fn example_new2(s: &str) {
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
    let seq = seq.to_sequent();
    println!("{}", seq.display(&entities));
    let seq = seq.to_sequent_extended();

    // prove
    let start_time = Instant::now();
    let result = prove_prop(&mut vec![seq], &entities);
    let end_time = Instant::now();
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
}
