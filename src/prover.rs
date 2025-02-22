mod core;
mod ebproof;
mod sequent;

use crate::{intern::Names, parser::parse_sequent};
use core::prove_prop;
use ebproof::ebproof;
use sequent::Sequent;
use std::{io, time::Instant};

pub fn prove(s: &str) -> io::Result<()> {
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

#[cfg(all(feature = "unstable", test))]
mod bench {
    extern crate test;

    use super::*;
    use crate::lang::SplitSequent;
    use std::fs;
    use typed_arena::Arena;

    fn parse<'a>(path: &str, arena: &'a Arena<SplitSequent>) -> Vec<(Sequent<'a>, Names)> {
        fs::read_to_string(path)
            .unwrap()
            .lines()
            .filter(|s| !s.is_empty() && !s.starts_with('#'))
            .map(|s| {
                let mut names = Names::default();
                let seq = arena.alloc(parse_sequent(s, &mut names, true, false).unwrap());
                (Sequent::init(seq), names)
            })
            .collect()
    }

    #[bench]
    fn bench_0(b: &mut test::Bencher) {
        let arena = Arena::new();
        let (seq, names) = &parse("examples/hard-props.txt", &arena)[0];
        println!("{}", &seq.display(&names).to_unicode()[..100]);
        b.iter(|| prove_prop(seq.clone(), &names));
    }
}
