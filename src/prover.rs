mod core;
mod ebproof;
mod forest;
mod sequent;

use crate::{app::CliOptions, intern::Names, parser::parse_sequent};
use core::prove_prop;
use ebproof::ebproof;
use forest::forest;
use log::info;
use sequent::Sequent;
use std::{fs::File, io::Write, time::Instant};

pub fn prove(s: &str, options: &CliOptions, mut result: File) {
    // parse
    info!("Parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            info!("Failed: {e}");
            writeln!(result, "error: {e}").unwrap();
            return;
        }
    };
    let seq = Sequent::init(&seq);
    // log the parsed sequent
    info!("Parsed sequent: {}", seq.display(&names).to_unicode());
    writeln!(result, "sequent: {}", seq.display(&names)).unwrap();

    // prove
    info!("Proving...");
    let start_time = Instant::now();
    let provability = prove_prop(seq.clone(), &names);
    let end_time = Instant::now();
    info!("Result: {provability}");
    writeln!(result, "provability: {provability}").unwrap();
    #[allow(clippy::cast_precision_loss)]
    let proof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
    info!("Proof time: {proof_time} ms");
    writeln!(result, "proof_time: {proof_time} ms").unwrap();

    // ebproof
    if options.ebproof {
        info!("Generating ebproof...");
        let start_time = Instant::now();
        ebproof(seq.clone(), &names, &options.out);
        let end_time = Instant::now();
        #[allow(clippy::cast_precision_loss)]
        let ebproof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
        info!("Ebproof time: {ebproof_time} ms");
        writeln!(result, "ebproof_time: {ebproof_time} ms").unwrap();
    }

    // forest
    if provability && options.forest {
        info!("Generating forest...");
        let start_time = Instant::now();
        forest(seq, &names, &options.out);
        let end_time = Instant::now();
        #[allow(clippy::cast_precision_loss)]
        let forest_time = end_time.duration_since(start_time).as_micros() as f32 / 1000.0;
        info!("Forest time: {forest_time} ms");
        writeln!(result, "forest_time: {forest_time} ms").unwrap();
    }
}

#[cfg(feature = "bench")]
#[divan::bench_group(max_time = 1)]
mod bench {
    #[allow(clippy::wildcard_imports)]
    use super::*;
    use crate::lang::SplitSequent;
    use divan::Bencher;
    use std::fs;
    use typed_arena::Arena;

    fn parse_nth<'a>(
        path: &str,
        arena: &'a Arena<SplitSequent>,
        n: usize,
    ) -> Option<(Sequent<'a>, Names)> {
        fs::read_to_string(path)
            .unwrap()
            .lines()
            .filter(|s| !s.is_empty() && !s.starts_with('#'))
            .nth(n)
            .map(|s| {
                let mut names = Names::default();
                let seq = arena.alloc(parse_sequent(s, &mut names, true, false).unwrap());
                (Sequent::init(seq), names)
            })
    }

    #[divan::bench(args = [0,1,2,3])]
    fn bench_props(bencher: Bencher, n: usize) {
        let arena = Arena::new();
        let (seq, names) = parse_nth("examples/hard-props.txt", &arena, n).unwrap();
        bencher.bench_local(|| prove_prop(seq.clone(), &names));
    }

    #[divan::bench(args = [0,1,2,3])]
    fn bench_ebproof(bencher: Bencher, n: usize) {
        let arena = Arena::new();
        let (seq, names) = parse_nth("examples/large-latex.txt", &arena, n).unwrap();
        bencher.bench_local(|| ebproof(seq.clone(), &names, ""));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use std::fs;
    use tempfile::TempDir;
    use test_case::case;

    #[case("props")]
    #[case("constants")]
    #[case("iltp-props")]
    fn test_latex_snapshot(file: &str) {
        // read snapshot file
        let content = fs::read_to_string(format!("examples/snapshots/{file}.txt")).unwrap();
        let mut name = String::new();
        let mut idx = 1;

        for line in content.lines() {
            if let Some(line) = line.strip_prefix('#') {
                // extract name from comment
                name = line.trim().replace('\'', "").replace([' ', '+', '.'], "-");
            } else if !line.is_empty() {
                println!("testing: {line}");
                // settings for snapshot tests
                let mut settings = insta::Settings::new();
                // short file names
                settings.set_prepend_module_to_snapshot(false);
                // snapshot path
                settings.set_snapshot_path(format!("../snapshots/{file}"));

                // create temporary directory for each test case
                let temp = TempDir::new().unwrap();
                let temp = temp.path();

                // parse sequent
                let mut names = Names::default();
                let seq = parse_sequent(line, &mut names, true, false).unwrap();
                let seq = Sequent::init(&seq);
                let seq_unicode = seq.display(&names).to_unicode();

                // check provability
                let provability = prove_prop(seq.clone(), &names);
                println!("{provability}");
                assert!(provability);

                // ebproof
                println!("ebproof...");
                // generate ebproof latex file
                ebproof(seq.clone(), &names, temp.to_str().unwrap());
                let ebproof_content = fs::read_to_string(temp.join("ebproof.tex")).unwrap();
                // snapshot test for ebproof
                settings.bind(|| {
                    assert_snapshot!(
                        format!("{idx}-ebproof-{name}"),
                        ebproof_content,
                        &seq_unicode
                    );
                });
                println!("done");

                // forest
                println!("forest...");
                // generate forest latex file
                forest(seq, &names, temp.to_str().unwrap());
                let forest_content = fs::read_to_string(temp.join("forest.tex")).unwrap();
                // snapshot test for forest
                settings.bind(|| {
                    assert_snapshot!(format!("{idx}-forest-{name}"), forest_content, &seq_unicode);
                });
                println!("done");

                idx += 1;
            }
        }
    }
}
