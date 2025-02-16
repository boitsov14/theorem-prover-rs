mod core;
mod ebproof;
mod sequent;

use crate::{intern::Names, parser::parse_sequent};
pub use core::prove_prop;
use ebproof::ebproof;
use sequent::Sequent;
use std::{io, time::Instant};

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
    let seq = Sequent::init(&seq);
    println!("{}", seq.display(&names));

    // prove
    let start_time = Instant::now();
    let result = prove_prop(seq.clone(), &names);
    let end_time = Instant::now();
    println!(">> {result:?}");
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);

    // ebproof
    let start_time = Instant::now();
    ebproof(seq, &names)?;
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("{} ms", elapsed_time.as_secs_f32() * 1000.0);
    Ok(())
}
