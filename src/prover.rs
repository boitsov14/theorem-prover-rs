mod core;
mod ebproof;
mod forest;
mod sequent;

use crate::{cli::CliOptions, intern::Names, parser::parse_sequent};
use core::prove_prop;
use ebproof::ebproof;
use forest::forest;
use log::info;
use sequent::Sequent;
use serde::{Deserialize, Serialize};
use serde_with::skip_serializing_none;
use std::{fs::File, path::PathBuf, time::Instant};

#[skip_serializing_none]
#[derive(Serialize, Deserialize, Default)]
struct Result {
    sequent: Option<String>,
    provability: Option<String>,
    proof_time: Option<String>,
    ebproof_time: Option<String>,
}

pub fn prove(s: &str, options: &CliOptions) {
    // set up result
    let mut result = Result::default();
    let write_json = |result: &Result| {
        let path = PathBuf::from(&options.out).join("result.json");
        let file = File::create(path).unwrap();
        serde_json::to_writer_pretty(file, result).unwrap();
    };
    write_json(&result);
    // parse
    info!("Parsing...");
    let mut names = Names::default();
    let seq = match parse_sequent(s, &mut names, true, false) {
        Ok(seq) => seq,
        Err(e) => {
            info!("Failed: {e}");
            return;
        }
    };
    let seq = Sequent::init(&seq);
    // log the parsed sequent
    info!("Parsed sequent: {}", seq.display(&names).to_unicode());
    result.sequent = Some(seq.display(&names).to_string());
    write_json(&result);

    // prove
    info!("Proving...");
    let start_time = Instant::now();
    let provability = prove_prop(seq.clone(), &names);
    let end_time = Instant::now();
    info!("Result: {provability}");
    result.provability = Some(provability.to_string());
    let proof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000 as f32;
    info!("Proof time: {proof_time} ms");
    result.proof_time = Some(format!("{proof_time} ms"));
    write_json(&result);

    // ebproof
    if options.ebproof {
        info!("Generating ebproof...");
        let start_time = Instant::now();
        ebproof(seq.clone(), &names, &options.out);
        let end_time = Instant::now();
        let ebproof_time = end_time.duration_since(start_time).as_micros() as f32 / 1000 as f32;
        info!("Ebproof time: {ebproof_time} ms");
        result.ebproof_time = Some(format!("{ebproof_time} ms"));
        write_json(&result);
    }

    // forest
    if provability && options.forest {
        info!("Generating forest...");
        let start_time = Instant::now();
        forest(seq, &names, &options.out);
        let end_time = Instant::now();
        let forest_time = end_time.duration_since(start_time).as_micros() as f32 / 1000 as f32;
        info!("Forest time: {forest_time} ms");
    }
}

#[cfg(feature = "bench")]
#[divan::bench_group(max_time = 1)]
mod bench {
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

    #[test]
    fn test_latex_snapshot() {
        // read snapshot file
        let content = fs::read_to_string("examples/snapshots.txt").unwrap();
        let mut name = String::new();

        for line in content.lines() {
            if line.starts_with('#') {
                // extract name from comment
                name = line[1..].trim().replace(" ", "-").replace("'", "");
            } else if !line.is_empty() {
                println!("testing: {}", line);
                // settings for snapshot tests
                let mut settings = insta::Settings::new();
                // short file names
                settings.set_prepend_module_to_snapshot(false);
                // snapshot path
                settings.set_snapshot_path("../snapshots");

                // create temporary directory for each test case
                let temp = TempDir::new().unwrap();
                let temp = temp.path();

                // parse sequent
                let mut names = Names::default();
                let seq = parse_sequent(line, &mut names, true, false).unwrap();
                let seq = Sequent::init(&seq);

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
                        format!("{name}-ebproof"),
                        ebproof_content,
                        &seq.display(&names).to_unicode()
                    );
                });
                println!("done");

                // forest
                println!("forest...");
                // generate forest latex file
                forest(seq.clone(), &names, temp.to_str().unwrap());
                let forest_content = fs::read_to_string(temp.join("forest.tex")).unwrap();
                // snapshot test for forest
                settings.bind(|| {
                    assert_snapshot!(
                        format!("{name}-forest"),
                        forest_content,
                        &seq.display(&names).to_unicode()
                    );
                });
                println!("done");
            }
        }
    }
}
