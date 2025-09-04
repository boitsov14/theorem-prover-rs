use crate::{
    app::CliOptions,
    intern::Names,
    parser::parse_sequent,
    prover::{
        core::prove_prop,
        latex::{ebproof, forest},
        sequent::Sequent,
    },
};
use log::info;
use std::{fs::File, io::Write, time::Instant};

pub fn prove(s: &str, options: &CliOptions, mut result: File) {
    // parse
    info!("Parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            info!("Failed: {e}");
            writeln!(result, "error: {e}").unwrap();
            return;
        }
    };
    let seq = Sequent::init(&seq);
    // log the parsed sequent
    info!("Parsed sequent: {}", seq.display(&names).to_unicode());
    writeln!(result, "sequent: {}", seq.display(&names)).unwrap();

    // prove
    info!("Proving...");
    let start_time = Instant::now();
    let provability = prove_prop(seq.clone(), &names);
    let end_time = Instant::now();
    info!("Result: {provability}");
    writeln!(result, "provability: {provability}").unwrap();
    #[allow(clippy::cast_precision_loss)]
    let proof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
    info!("Proof time: {proof_time} ms");
    writeln!(result, "proof_time: {proof_time} ms").unwrap();

    // ebproof
    if options.ebproof {
        info!("Generating ebproof...");
        let start_time = Instant::now();
        ebproof(seq.clone(), &names, &options.out);
        let end_time = Instant::now();
        #[allow(clippy::cast_precision_loss)]
        let ebproof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
        info!("Ebproof time: {ebproof_time} ms");
        writeln!(result, "ebproof_time: {ebproof_time} ms").unwrap();
    }

    // forest
    if provability && options.forest {
        info!("Generating forest...");
        let start_time = Instant::now();
        forest(seq, &names, &options.out);
        let end_time = Instant::now();
        #[allow(clippy::cast_precision_loss)]
        let forest_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
        info!("Forest time: {forest_time} ms");
        writeln!(result, "forest_time: {forest_time} ms").unwrap();
    }
}
