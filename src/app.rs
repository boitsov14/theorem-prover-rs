use crate::{
    core::{names::Names, parser::parse_sequent},
    prover::{Sequent, ebproof, forest, prove_prop},
};
use clap::Parser;
use itertools::Itertools;
use log::{info, trace};
use std::{
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Instant,
};

#[derive(Parser)]
pub struct CliOptions {
    /// Output LaTeX in ebproof format
    #[arg(long)]
    pub ebproof: bool,

    /// Output LaTeX in forest format  
    #[arg(long)]
    pub forest: bool,

    /// Enable trace level logging
    #[arg(long)]
    trace: bool,

    /// Output directory path
    #[arg(long, default_value = "")]
    pub out: String,
}

pub fn run() {
    // parse command line arguments
    let options = CliOptions::parse();

    // initialize logger
    let s = if options.trace {
        include_str!("../logger/trace.yaml")
    } else {
        include_str!("../logger/info.yaml")
    };
    let logger_config = serde_yml::from_str(s).unwrap();
    log4rs::init_raw_config(logger_config).unwrap();

    if options.ebproof {
        trace!("Using ebproof format");
    }
    if options.forest {
        trace!("Using forest format");
    }

    // read formula from file
    // but ignore lines starting with #
    let s = fs::read_to_string(PathBuf::from(&options.out).join("formula.txt"))
        .expect("Failed to read formula.txt")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .join(" ");
    info!("Input: {}", s.trim());

    // create result.log file for output
    let mut result = File::create(PathBuf::from(&options.out).join("result.log")).unwrap();

    // parse
    info!("Parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(&s, &mut names, true, false) {
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
