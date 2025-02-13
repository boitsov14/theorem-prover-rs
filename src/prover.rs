// TODO: 2025/02/12 make it private? or flatten folder structure
pub mod lang;
pub mod latex_ebproof;
pub mod prover;

use crate::{name::Names, parser::parse_sequent};
use latex_ebproof::latex_sequent_calculus;
use prover::prove_prop;
use std::{
    fs::File,
    io::{self, BufWriter, Write},
    time::Instant,
};

pub fn example(s: &str) -> io::Result<()> {
    // parse
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            println!("{e}");
            return Ok(());
        }
    };
    let seq = seq.to_seq();
    // println!("{}", seq.display(&names));

    // prove
    let start_time = Instant::now();
    let result = prove_prop(&seq, &names);
    let end_time = Instant::now();
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    let mut file = BufWriter::new(File::create("proof0.tex")?);
    writeln!(
        file,
        r"\documentclass[preview,varwidth=\maxdimen,border=10pt]{{standalone}}
\usepackage{{ebproof}}
\begin{{document}}
\begin{{prooftree}}",
    )?;
    let start_time = Instant::now();
    const MAX_FILE_SIZE: usize = 1_000_000; // 1MB
    let mut buf: Vec<u8> = Vec::with_capacity(MAX_FILE_SIZE);
    let result = latex_sequent_calculus(&seq, &names, &mut buf)?;
    file.write_all(&buf)?;
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    writeln!(
        file,
        r"\end{{prooftree}}
\end{{document}}",
    )?;
    println!(">> {result:?}");
    Ok(())
}
