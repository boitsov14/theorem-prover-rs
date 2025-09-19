#[cfg(feature = "bench")]
#[divan::bench_group(max_time = 1)]
mod benches {
    use crate::{
        core::{names::Names, parser::parse_sequent, syntax::SplitSequent},
        prover::{kernel::prove_prop, sequent::Sequent},
    };
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
                (Sequent::new(seq), names)
            })
    }

    #[divan::bench(args = [0,1,2,3])]
    fn bench_props(bencher: Bencher, n: usize) {
        let arena = Arena::new();
        let (seq, names) = parse_nth("examples/hard-props.txt", &arena, n).unwrap();
        bencher.bench_local(|| prove_prop(seq.clone(), &names));
    }
}
