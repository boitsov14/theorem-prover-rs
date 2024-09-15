mod lang;
mod prover;
mod sequent_grid;

pub fn example_new(s: &str) {
    use crate::name::Names;
    use crate::parser::parse_sequent;
    use prover::prove_prop;
    use std::time::Instant;

    // parse
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            println!("{e}");
            return;
        }
    };
    let seq = seq.to_sequent();
    println!("{}", seq.display(&names));

    // prove
    let start_time = Instant::now();
    let result = prove_prop(&seq, &names);
    let end_time = Instant::now();
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
}
