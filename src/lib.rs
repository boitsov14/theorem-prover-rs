mod intern;
mod lang;
mod parser;
mod prover;

use clap::Parser;
use itertools::Itertools;
use mimalloc::MiMalloc;
use prover::prove;
use std::{fs, path::PathBuf};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

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

pub fn main_prover() {
    let config = Config::parse();

    if let Some(memory) = config.memory {
        set_memory_limit(memory);
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
