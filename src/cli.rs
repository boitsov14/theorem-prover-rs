use crate::prover::prove;
use clap::Parser;
use itertools::Itertools;
use std::{fs, path::PathBuf};

#[derive(Parser)]
struct Config {
    /// Memory usage limit in bytes
    #[arg(long)]
    memory: Option<u64>,

    /// Output LaTeX in ebproof format
    #[arg(long)]
    ebproof: bool,

    /// Output LaTeX in forest format  
    #[arg(long)]
    forest: bool,

    /// Enable trace level logging
    #[arg(long)]
    trace: bool,

    /// Output directory path
    #[arg(long, default_value = "")]
    out: String,
}

#[cfg(not(windows))]
fn set_memory_limit(limit: u64) {
    use rlimit::{Resource, getrlimit, setrlimit};
    if let Err(e) = setrlimit(Resource::AS, limit, 2 * limit) {
        eprintln!("Warning: Failed to set memory limit: {e}");
    } else {
        if let Ok((soft, hard)) = getrlimit(Resource::AS) {
            println!("Memory limit: ({soft}, {hard}) bytes");
        } else {
            eprintln!("Warning: Failed to get memory limit");
        }
    }
}

#[cfg(windows)]
fn set_memory_limit(_limit: u64) {
    println!("Warning: Memory limit is not supported on Windows");
}

fn init_logger(trace: bool) {
    let config = if trace {
        "config/log4rs-trace.yaml"
    } else {
        "config/log4rs.yaml"
    };
    log4rs::init_file(config, Default::default()).unwrap();

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

    if let Some(memory) = config.memory {
        set_memory_limit(memory);
    }
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

    prove(&s).unwrap();
}
