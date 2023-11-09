use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mimalloc::MiMalloc;
use std::fs;
use theorem_prover_rs::parser::*;
use theorem_prover_rs::prover::*;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn from_example_prop(c: &mut Criterion) {
    let fs = fs::read_to_string("benches/examples.txt").unwrap();
    let fmls = fs
        .lines()
        .filter(|s| !s.is_empty())
        .map(|s| parse(s).unwrap().0)
        .map(|fml| fml.universal_quantify());

    let mut group = c.benchmark_group("example_prop");
    group.sample_size(10);

    for ref fml in fmls {
        group.bench_with_input(BenchmarkId::from_parameter(fml), fml, |b, fml| {
            b.iter(|| example_for_bench(fml));
        });
    }
    group.finish();
}

fn from_iltp_prop(c: &mut Criterion) {
    let mut fmls = vec![];
    let list = vec!["SYJ202+1.004.p", "SYJ206+1.010.p"];

    let entries = fs::read_dir("benches/iltp_prop").unwrap();
    for entry in entries {
        let file = entry.unwrap().path();
        let file_name = file.file_name().unwrap().to_str().unwrap();
        if !list.contains(&file_name) {
            continue;
        }
        let s = fs::read_to_string(&file).unwrap();
        let (fml, _) = parse(&from_tptp(&s)).unwrap();
        fmls.push(fml);
    }

    let mut group = c.benchmark_group("iltp_prop");
    group.sample_size(10);

    for ref fml in fmls {
        group.bench_with_input(BenchmarkId::from_parameter(fml), fml, |b, fml| {
            b.iter(|| example_for_bench(fml));
        });
    }
    group.finish();
}

criterion_group!(benches, from_example_prop, from_iltp_prop);
criterion_main!(benches);
