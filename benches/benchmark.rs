use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mimalloc::MiMalloc;
use std::fs;
use theorem_prover_rs::parser::*;

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
            b.iter(|| fml.assert_provable());
        });
    }
    group.finish();
}

fn from_iltp_prop_0(c: &mut Criterion) {
    let mut fmls = vec![];

    let exclude_list = fs::read_to_string("benches/iltp_prop_exclude.txt").unwrap();
    let exclude_list = exclude_list.lines().collect::<Vec<_>>();

    let entries = fs::read_dir("benches/iltp_prop").unwrap();
    for entry in entries {
        let file = entry.unwrap().path();
        let file_name = file.file_name().unwrap().to_str().unwrap();
        if exclude_list.contains(&file_name) {
            continue;
        }
        let s = fs::read_to_string(&file).unwrap();
        let (fml, _) = parse(&from_tptp(&s)).unwrap();
        fmls.push(fml);
    }

    c.bench_function("iltp_prop_0", |b| {
        b.iter(|| {
            for fml in &fmls {
                fml.assert_provable();
            }
        });
    });
}

fn from_iltp_prop_1(c: &mut Criterion) {
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

    let mut group = c.benchmark_group("iltp_prop_1");
    group.sample_size(10);

    for ref fml in fmls {
        group.bench_with_input(BenchmarkId::from_parameter(fml), fml, |b, fml| {
            b.iter(|| fml.assert_provable());
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    from_iltp_prop_0,
    from_example_prop,
    from_iltp_prop_1
);
criterion_main!(benches);
