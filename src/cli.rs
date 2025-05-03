use crate::prover::prove;
use clap::Parser;
use itertools::Itertools;
use serde_yaml;
use std::{fs, path::PathBuf};

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

pub fn cli() {
    // parse command line arguments
    let options = CliOptions::parse();

    // initialize logger
    let s = if options.trace {
        include_str!("../logger/trace.yaml")
    } else {
        include_str!("../logger/info.yaml")
    };
    let logger_config = serde_yaml::from_str(s).unwrap();
    log4rs::init_raw_config(logger_config).unwrap();

    if options.ebproof {
        log::trace!("Using ebproof format");
    }
    if options.forest {
        log::trace!("Using forest format");
    }

    // read formula from file
    // but ignore lines starting with #
    let s = fs::read_to_string(PathBuf::from(&options.out).join("formula.txt"))
        .expect("Failed to read formula.txt")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .join("\n");

    prove(&s, &options).unwrap();
}
