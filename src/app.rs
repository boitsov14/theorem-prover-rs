use crate::{
    core::{names::Names, parser::parse_sequent},
    prover::{
        Latex,
        ProofResult,
        Sequent,
        get_latex,
        prove_prop,
        sequent_calculus,
        tableau_method,
    },
};
use clap::Parser;
use itertools::Itertools;
use log::{info, warn};
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

    // load options from options.json
    let s = fs::read_to_string(PathBuf::from(&out).join("options.json"))
        .expect("options.json not found");
    let options = serde_json::from_str::<FileOptions>(&s).expect("invalid options.json format");

    // setup logger
    let logger = include_str!("../logger.yaml")
        .replace("LOG_DIR", &out)
        .replace(
            "LOG_LEVEL",
            if cfg!(debug_assertions) {
                "trace"
            } else {
                "info"
            },
        )
        .replace(
            "APPENDERS",
            if cfg!(debug_assertions) {
                "[log_file, trace_file]"
            } else {
                "[log_file]"
            },
        );
    let logger = serde_yaml_ng::from_str(&logger).unwrap();
    log4rs::init_raw_config(logger).unwrap();

    // read formula from file
    // but ignore lines starting with #
    let s = fs::read_to_string(PathBuf::from(&out).join("formula.txt"))
        .expect("formula.txt not found")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .join(" ");
    info!("input: {}", s.trim());

    // create result.yaml file
    let mut result = File::create(PathBuf::from(&out).join("result.yaml")).unwrap();

    // parse
    info!("parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(&s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            info!("failed");
            // write error to parse.err
            let mut f = File::create(PathBuf::from(&out).join("parse.err")).unwrap();
            writeln!(f, "{e}").unwrap();
            return;
        }
    };
    info!("done");
    let seq = Sequent::new(&seq);
    // log the parsed sequent
    writeln!(
        result,
        "sequent: {}",
        seq.display(&names).to_string().trim()
    )
    .unwrap();

    // prove
    info!("proving...");
    let start = Instant::now();
    let proof_result = prove_prop(seq.clone(), &names);
    let provability = matches!(proof_result, ProofResult::Proved);
    let end = Instant::now();
    info!("done");
    writeln!(result, "provability: {provability}").unwrap();

    // output countermodel if unprovable
    if let ProofResult::Unprovable(countermodel) = &proof_result {
        info!("generating countermodel LaTeX...");
        // create truth table for the countermodel
        let table = countermodel.evaluate(&seq);
        // generate LaTeX table
        let latex = get_latex(&seq, &names, &table);
        // save LaTeX file
        let mut file = File::create(PathBuf::from(&out).join("countermodel.tex")).unwrap();
        file.write_all(latex.as_bytes()).unwrap();
        info!("done");
        return;
    }
    let time = end.duration_since(start).as_secs_f32() * 1000.0;
    writeln!(result, "proofTime: {time:.3}").unwrap();

    // ebproof
    if provability && options.ebproof {
        info!("generating ebproof...");
        let start = Instant::now();
        match sequent_calculus(seq.clone(), &names, Latex::Ebproof) {
            Ok(proof) => {
                // save LaTeX file
                let mut file = File::create(PathBuf::from(&out).join("ebproof.tex")).unwrap();
                file.write_all(proof.as_bytes()).unwrap();
            }
            Err(LatexError::OutputTooLarge) => {
                warn!("ebproof output too large");
                writeln!(result, "outputTooLarge: true").unwrap();
                return;
            }
            Err(LatexError::TooManyBranches) => unreachable!(),
        }
        let end = Instant::now();
        info!("done");
        let time = end.duration_since(start).as_secs_f32() * 1000.0;
        writeln!(result, "ebproofTime: {time:.3}").unwrap();
    }

    // bussproofs
    if provability && options.bussproofs {
        info!("generating bussproofs...");
        let start = Instant::now();
        match sequent_calculus(seq.clone(), &names, Latex::Bussproofs) {
            Ok(proof) => {
                // save LaTeX file
                let mut file = File::create(PathBuf::from(&out).join("bussproofs.tex")).unwrap();
                file.write_all(proof.as_bytes()).unwrap();
            }
            Err(LatexError::OutputTooLarge) => {
                warn!("bussproofs output too large");
                writeln!(result, "outputTooLarge: true").unwrap();
                return;
            }
            Err(LatexError::TooManyBranches) => {
                writeln!(result, "tooManyBranches: true").unwrap();
            }
        }
        let end = Instant::now();
        info!("done");
        let time = end.duration_since(start).as_secs_f32() * 1000.0;
        writeln!(result, "bussproofsTime: {time:.3}").unwrap();
    }

    // forest
    if provability && options.forest {
        info!("generating forest...");
        let start = Instant::now();
        match tableau_method(seq, &names) {
            Ok(proof) => {
                // save LaTeX file
                let mut file = File::create(PathBuf::from(&out).join("forest.tex")).unwrap();
                file.write_all(proof.as_bytes()).unwrap();
            }
            Err(LatexError::OutputTooLarge) => {
                warn!("forest output too large");
                writeln!(result, "outputTooLarge: true").unwrap();
                return;
            }
            Err(LatexError::TooManyBranches) => unreachable!(),
        }
        let end = Instant::now();
        info!("done");
        let time = end.duration_since(start).as_secs_f32() * 1000.0;
        writeln!(result, "forestTime: {time:.3}").unwrap();
    }
}
