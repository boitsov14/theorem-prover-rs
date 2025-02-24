mod intern;
mod lang;
mod parser;
mod prover;

use clap::Parser;
use itertools::Itertools;
use mimalloc::MiMalloc;
use prover::prove;
#[cfg(not(windows))]
use rlimit::{Resource, setrlimit};
use std::{fs, path::PathBuf};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
struct Config {
    /// Memory usage limit in bytes
    #[arg(long)]
    memory: Option<usize>,

    /// Output LaTeX in ebproof format
    #[arg(long)]
    ebproof: bool,

    /// Output LaTeX in forest format  
    #[arg(long)]
    forest: bool,

    /// Output directory path
    #[arg(long, default_value = "")]
    out: String,
}

pub fn main_prover() {
    let config = Config::parse();

    if let Some(memory) = config.memory {
        println!("Memory limit: {memory} bytes");
        #[cfg(not(windows))]
        if let Err(e) = setrlimit(Resource::AS, memory, 2 * memory) {
            eprintln!("Warning: Failed to set memory limit: {e}");
        }
        #[cfg(windows)]
        println!("Warning: Memory limit is not supported on Windows");
    }
    if config.ebproof {
        println!("Using ebproof format");
    }
    if config.forest {
        println!("Using forest format");
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
