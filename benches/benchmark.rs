use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use itertools::Itertools;
use mimalloc::MiMalloc;
use std::fs;
use theorem_prover_rs::parser::*;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn from_example_prop(c: &mut Criterion) {
    let mut group = c.benchmark_group("example_prop");
    group.sample_size(10);

    let s = fs::read_to_string("benches/examples.txt").unwrap();
    let fmls = s.lines().filter(|s| !s.is_empty()).map(|s| {
        let (fml, entities) = parse(s).unwrap();
        (fml.universal_quantify(), entities)
    });

    for (ref fml, entities) in fmls {
        group.bench_with_input(
            BenchmarkId::from_parameter(fml.display(&entities)),
            fml,
            |b, fml| {
                b.iter(|| fml.assert_provable(entities.len()));
            },
        );
    }
    group.finish();
}

fn from_iltp_prop_0(c: &mut Criterion) {
    let s = fs::read_to_string("benches/iltp_prop/exclude.txt").unwrap();
    let exclude_list = s.lines().collect_vec();

    let fmls = fs::read_dir("benches/iltp_prop")
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|file| {
            let file_name = file.file_name().unwrap().to_str().unwrap();
            !exclude_list.contains(&file_name)
        })
        .map(|file| {
            let s = fs::read_to_string(&file).unwrap();
            parse(&from_tptp(&s)).unwrap()
        })
        .collect_vec();

    c.bench_function("iltp_prop_0", |b| {
        b.iter(|| {
            for (fml, entities) in &fmls {
                fml.assert_provable(entities.len());
            }
        });
    });
}

fn from_iltp_prop_1(c: &mut Criterion) {
    let mut group = c.benchmark_group("iltp_prop_1");
    group.sample_size(10);

    let list = vec!["SYJ202+1.004.p", "SYJ206+1.010.p"];

    let fmls = fs::read_dir("benches/iltp_prop")
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|file| {
            let file_name = file.file_name().unwrap().to_str().unwrap();
            list.contains(&file_name)
        })
        .map(|file| {
            let s = fs::read_to_string(&file).unwrap();
            parse(&from_tptp(&s)).unwrap()
        });

    for (ref fml, entities) in fmls {
        group.bench_with_input(
            BenchmarkId::from_parameter(fml.display(&entities)),
            fml,
            |b, fml| {
                b.iter(|| fml.assert_provable(entities.len()));
            },
        );
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
