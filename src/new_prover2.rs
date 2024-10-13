mod lang;
mod latex;
mod prover;
mod prover2;

use crate::new_prover2::latex::latex_sequent_calculus;
pub use prover2::prove_prop;
use std::fs::File;
use std::io;
use std::io::{BufWriter, Write};

pub fn example_new2(s: &str) -> io::Result<()> {
    use crate::name::Names;
    use crate::parser::parse_sequent;
    use std::time::Instant;

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
    println!("{}", seq.display(&names));

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
    let result = latex_sequent_calculus(&seq, &names, &mut file)?;
    writeln!(
        file,
        r"\end{{prooftree}}
\end{{document}}",
    )?;
    println!(">> {result:?}");
    Ok(())
}
