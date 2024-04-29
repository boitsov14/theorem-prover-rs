use mimalloc::MiMalloc;
use theorem_prover_rs::{example, example_iltp_prop};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    // 112ms
    // let s = "((o11 ∨ o12 ∨ o13 ∨ o14) ∧ (o21 ∨ o22 ∨ o23 ∨ o24) ∧ (o31 ∨ o32 ∨ o33 ∨ o34) ∧ (o41 ∨ o42 ∨ o43 ∨ o44) ∧ (o51 ∨ o52 ∨ o53 ∨ o54)) → ((o11 ∧ o21) ∨ (o11 ∧ o31) ∨ (o11 ∧ o41) ∨ (o11 ∧ o51) ∨ (o21 ∧ o31) ∨ (o21 ∧ o41) ∨ (o21 ∧ o51) ∨ (o31 ∧ o41) ∨ (o31 ∧ o51) ∨ (o41 ∧ o51) ∨ (o12 ∧ o22) ∨ (o12 ∧ o32) ∨ (o12 ∧ o42) ∨ (o12 ∧ o52) ∨ (o22 ∧ o32) ∨ (o22 ∧ o42) ∨ (o22 ∧ o52) ∨ (o32 ∧ o42) ∨ (o32 ∧ o52) ∨ (o42 ∧ o52) ∨ (o13 ∧ o23) ∨ (o13 ∧ o33) ∨ (o13 ∧ o43) ∨ (o13 ∧ o53) ∨ (o23 ∧ o33) ∨ (o23 ∧ o43) ∨ (o23 ∧ o53) ∨ (o33 ∧ o43) ∨ (o33 ∧ o53) ∨ (o43 ∧ o53) ∨ (o14 ∧ o24) ∨ (o14 ∧ o34) ∨ (o14 ∧ o44) ∨ (o14 ∧ o54) ∨ (o24 ∧ o34) ∨ (o24 ∧ o44) ∨ (o24 ∧ o54) ∨ (o34 ∧ o44) ∨ (o34 ∧ o54) ∨ (o44 ∧ o54))";
    // 825ms
    // let s = "(((((((((((a⇔b)⇔c)⇔d)⇔e)⇔f)⇔g)⇔h)⇔i)⇔j)⇔k)⇔(a⇔(b⇔(c⇔(d⇔(e⇔(f⇔(g⇔(h⇔(i⇔(j⇔k)))))))))))";

    let s = "P and Q to Q and P";
    // let s = "P or Q to Q or P";
    // let s = "¬(P ∧ Q) ↔ (¬P ∨ ¬Q)";

    // let s = "all x P(x) to all y P(y)";
    // let s = "ex x P(x) to ex y P(y)";
    // let s = "all x P(x) to ex y P(y)";
    // let s = "ex x P(x) to all y P(y)";
    // let s = "P(a) to all x(P(x) → P(f(x))) to P(f(a))";
    // let s = "P(a) to all x(P(x) → P(f(x))) to P(f(f(a)))";
    // let s = "P(a) to all x(P(x) → P(f(x))) to P(f(f(f(f(f(f(f(f(f(f(a)))))))))))";
    // let s = "∃x∀yP(x,y) → ∀y∃xP(x,y)";

    // sort: 5274ms, un_sort: 1805ms -> 998ms
    // let s = "P(a) to all x(P(x) → P(f(x))) to P(f(f(f(f(f(f(f(f(f(a))))))))))";
    // u: {7: Func(3, [Func(3, [Func(4, [])])]), 9: Func(3, [Func(3, [Func(3, [Func(3, [Func(4, [])])])])]), 13: Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(4, [])])])])])])])])]), 10: Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(4, [])])])])])]), 8: Func(3, [Func(3, [Func(3, [Func(4, [])])])]), 12: Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(4, [])])])])])])])]), 6: Func(3, [Func(4, [])]), 5: Func(4, []), 11: Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(3, [Func(4, [])])])])])])])}

    example(s).unwrap();
    example_iltp_prop();
}
