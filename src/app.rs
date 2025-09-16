use crate::{
    core::{names::Names, parser::parse_sequent},
    prover::{Latex, Sequent, prove_prop, sequent_calculus, tableau_method},
};
use clap::Parser;
use itertools::Itertools;
use log::{info, trace};
use serde::Deserialize;
use std::{
    fs::{self, File},
    io::Write,
    path::PathBuf,
    time::Instant,
};

/// Options from command line arguments
#[derive(Parser)]
struct CliOptions {
    /// Output directory path
    #[arg(long, default_value = "")]
    out: String,
}

/// Options from options.json
#[derive(Deserialize)]
#[expect(clippy::struct_excessive_bools)]
struct FileOptions {
    /// Output LaTeX in ebproof format
    #[serde(default)]
    ebproof: bool,
    /// Output LaTeX in bussproofs format
    #[serde(default)]
    bussproofs: bool,
    /// Output LaTeX in forest format
    #[serde(default)]
    forest: bool,
    /// Enable trace level logging
    #[serde(default)]
    trace: bool,
}

/// Maximum output size limit for LaTeX generation
pub const MAX_OUTPUT_SIZE: usize = 1_000_000; // 1MB

/// Error types for LaTeX generation
#[derive(Debug)]
pub enum LatexError {
    /// Output size exceeded the maximum limit
    OutputTooLarge,
    /// Too many branches for bussproofs package
    TooManyBranches,
}

pub fn run() {
    // parse command line arguments
    let options = CliOptions::parse();

    // output directory
    let out = options.out;

    // load file options from options.json
    let s = fs::read_to_string(PathBuf::from(&out).join("options.json"))
        .expect("options.json not found");
    let options = serde_json::from_str::<FileOptions>(&s).expect("invalid options.json format");

    // initialize logger
    let s = include_str!("../logger.yaml")
        .replace("LOG_DIR", &out)
        .replace("LOG_LEVEL", if options.trace { "trace" } else { "info" })
        .replace(
            "APPENDERS",
            if options.trace {
                "[log_file, trace_file]"
            } else {
                "[log_file]"
            },
        );
    let logger_config = serde_yaml_ng::from_str(&s).unwrap();
    log4rs::init_raw_config(logger_config).unwrap();

    if options.ebproof {
        trace!("Using ebproof format");
    }
    if options.forest {
        trace!("Using forest format");
    }

    // read formula from file
    // but ignore lines starting with #
    let s = fs::read_to_string(PathBuf::from(&out).join("formula.txt"))
        .expect("formula.txt not found")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .join(" ");
    info!("input: {}", s.trim());

    // create result.yaml file for output
    let mut result = File::create(PathBuf::from(&out).join("result.yaml")).unwrap();

    // parse
    info!("parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(&s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            info!("failed");
            // write error message to parse.err
            let mut f = File::create(PathBuf::from(&out).join("parse.err")).unwrap();
            writeln!(f, "{e}").unwrap();
            return;
        }
    };
    info!("done");
    let seq = Sequent::init(&seq);
    // log the parsed sequent
    writeln!(
        result,
        "sequent: {}",
        seq.display(&names)
            .to_string()
            .replace(r"&\vdash", r"\vdash")
            .trim()
    )
    .unwrap();

    // prove
    info!("proving...");
    let start_time = Instant::now();
    let provability = prove_prop(seq.clone(), &names);
    let end_time = Instant::now();
    info!("done");
    writeln!(result, "provability: {provability}").unwrap();
    let time = end_time.duration_since(start_time).as_secs_f32() * 1000.0;
    writeln!(result, "proofTime: {time:.3}").unwrap();

    // ebproof
    if provability && options.ebproof {
        info!("generating ebproof...");
        let start_time = Instant::now();
        match sequent_calculus(seq.clone(), &names, &out, Latex::Ebproof) {
            Ok(()) => {}
            Err(LatexError::OutputTooLarge) => {
                writeln!(result, "fileSizeError: true").unwrap();
            }
            Err(LatexError::TooManyBranches) => unreachable!(),
        }
        let end_time = Instant::now();
        info!("done");
        let time = end_time.duration_since(start_time).as_secs_f32() * 1000.0;
        writeln!(result, "ebproofTime: {time:.3}").unwrap();
    }

    // bussproofs
    if provability && options.bussproofs {
        info!("generating bussproofs...");
        let start_time = Instant::now();
        match sequent_calculus(seq.clone(), &names, &out, Latex::Bussproofs) {
            Ok(()) => {}
            Err(LatexError::OutputTooLarge) => {
                writeln!(result, "fileSizeError: true").unwrap();
            }
            Err(LatexError::TooManyBranches) => {
                writeln!(result, "tooManyBranches: true").unwrap();
            }
        }
        let end_time = Instant::now();
        info!("done");
        let time = end_time.duration_since(start_time).as_secs_f32() * 1000.0;
        writeln!(result, "bussproofsTime: {time:.3}").unwrap();
    }

    // forest
    if provability && options.forest {
        info!("generating forest...");
        let start_time = Instant::now();
        match tableau_method(seq, &names, &out) {
            Ok(()) => {}
            Err(LatexError::OutputTooLarge) => {
                writeln!(result, "fileSizeError: true").unwrap();
            }
            Err(LatexError::TooManyBranches) => unreachable!(),
        }
        let end_time = Instant::now();
        info!("done");
        let time = end_time.duration_since(start_time).as_secs_f32() * 1000.0;
        writeln!(result, "forestTime: {time:.3}").unwrap();
    }
}
