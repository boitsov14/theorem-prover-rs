use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mimalloc::MiMalloc;
use theorem_prover_rs::{prove_prop, read_file_and_parse};
use typed_arena::Arena;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn hard_props(c: &mut Criterion) {
    let mut group = c.benchmark_group("hard-props");
    let arena = Arena::new();
    let seqs = read_file_and_parse("examples/hard-props.txt", &arena);
    for (seq, names) in &seqs {
        group.bench_function(
            BenchmarkId::from_parameter(seq.extended().unwrap().display(names)),
            |b| {
                b.iter(|| assert!(prove_prop(seq, names)));
            },
        );
    }
    group.finish();
}

criterion_group!(benches, hard_props,);
criterion_main!(benches);
