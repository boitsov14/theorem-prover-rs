use std::fs;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use theorem_prover_rs::parser::*;
use theorem_prover_rs::prover::*;

fn from_elem(c: &mut Criterion) {
    let fs = fs::read_to_string("benches/examples.txt").unwrap();
    let fmls = fs
        .lines()
        .map(|s| parse(s).unwrap().0)
        .map(|fml| fml.universal_quantify());

    let mut group = c.benchmark_group("prop");

    for ref fml in fmls {
        group.bench_with_input(BenchmarkId::from_parameter(fml), fml, |b, fml| {
            b.iter(|| example_for_bench(fml));
        });
    }
    group.finish();
}

criterion_group!(benches, from_elem);
criterion_main!(benches);
