use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use mimalloc::MiMalloc;
use theorem_prover_rs::new_prover2::prove_prop;
use theorem_prover_rs::read_file_and_parse;
use typed_arena::Arena;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn hard_propositional_examples(c: &mut Criterion) {
    let mut group = c.benchmark_group("hard_propositional_examples");
    let arena = Arena::new();
    let seqs = read_file_and_parse("benches/hard_propositional_examples.txt", &arena);
    for (seq, names) in &seqs {
        group.bench_function(BenchmarkId::from_parameter(seq.display(names)), |b| {
            b.iter(|| assert!(prove_prop(seq, names)));
        });
    }
    group.finish();
}

fn easy_propositional_examples(c: &mut Criterion) {
    let mut group = c.benchmark_group("easy_propositional_examples");
    let arena = Arena::new();
    let seqs = read_file_and_parse("benches/easy_propositional_examples.txt", &arena);
    for (seq, names) in &seqs {
        group.bench_function(BenchmarkId::from_parameter(seq.display(names)), |b| {
            b.iter(|| assert!(prove_prop(seq, names)));
        });
    }
    group.finish();
}

fn iltp_propositional_examples(c: &mut Criterion) {
    let arena = Arena::new();
    let seqs = read_file_and_parse("benches/iltp_propositional_examples.txt", &arena);
    c.bench_function("iltp_propositional_examples", |b| {
        b.iter(|| {
            for (seq, names) in &seqs {
                assert!(prove_prop(seq, names));
            }
        });
    });
}

criterion_group!(
    benches,
    hard_propositional_examples,
    // easy_propositional_examples,
    iltp_propositional_examples
);
criterion_main!(benches);
