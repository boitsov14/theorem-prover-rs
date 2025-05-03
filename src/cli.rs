use crate::prover::prove;
use clap::Parser;
use itertools::Itertools;
use serde_yaml;
use std::{fs, path::PathBuf};

#[derive(Parser)]
pub struct Config {
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

fn init_logger(trace: bool) {
    let config = if trace {
        include_str!("../logger/trace.yaml")
    } else {
        include_str!("../logger/info.yaml")
    };
    let config = serde_yaml::from_str(config).unwrap();
    log4rs::init_raw_config(config).unwrap();

    log::error!("Error message");
    log::warn!("Warning message");
    log::info!("Info message");
    log::debug!("Debug message");
    log::trace!("Trace message");

    for _ in 0..20 {
        log::trace!("Hi");
    }
}

pub fn cli() {
    let config = Config::parse();

    init_logger(config.trace);

    if config.ebproof {
        log::trace!("Using ebproof format");
    }
    if config.forest {
        log::trace!("Using forest format");
    }

    // read formula from file
    // but ignore lines starting with #
    let s = fs::read_to_string(PathBuf::from(&config.out).join("formula.txt"))
        .expect("Failed to read formula.txt")
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .join("\n");

    prove(&s, &config).unwrap();
}
