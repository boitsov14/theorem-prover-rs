use mimalloc::MiMalloc;
use theorem_prover_rs::new_prover2::example_new2;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    // 95ms -> 79ms -> 42ms
    // let s = "((o11∨o12∨o13∨o14)∧(o21∨o22∨o23∨o24)∧(o31∨o32∨o33∨o34)∧(o41∨o42∨o43∨o44)∧(o51∨o52∨o53∨o54))→((o11∧o21)∨(o11∧o31)∨(o11∧o41)∨(o11∧o51)∨(o21∧o31)∨(o21∧o41)∨(o21∧o51)∨(o31∧o41)∨(o31∧o51)∨(o41∧o51)∨(o12∧o22)∨(o12∧o32)∨(o12∧o42)∨(o12∧o52)∨(o22∧o32)∨(o22∧o42)∨(o22∧o52)∨(o32∧o42)∨(o32∧o52)∨(o42∧o52)∨(o13∧o23)∨(o13∧o33)∨(o13∧o43)∨(o13∧o53)∨(o23∧o33)∨(o23∧o43)∨(o23∧o53)∨(o33∧o43)∨(o33∧o53)∨(o43∧o53)∨(o14∧o24)∨(o14∧o34)∨(o14∧o44)∨(o14∧o54)∨(o24∧o34)∨(o24∧o44)∨(o24∧o54)∨(o34∧o44)∨(o34∧o54)∨(o44∧o54))";
    // 39ms -> 30ms -> 16ms
    // let s = "(o11∨o12∨o13)∧(o21∨o22∨o23)∧(o31∨o32∨o33)∧(o41∨o42∨o43)→(o11∧o21∧o31∧o41)∨(o11∧o21∧o31∧o42)∨(o11∧o21∧o31∧o43)∨(o11∧o21∧o32∧o41)∨(o11∧o21∧o32∧o42)∨(o11∧o21∧o32∧o43)∨(o11∧o21∧o33∧o41)∨(o11∧o21∧o33∧o42)∨(o11∧o21∧o33∧o43)∨(o11∧o22∧o31∧o41)∨(o11∧o22∧o31∧o42)∨(o11∧o22∧o31∧o43)∨(o11∧o22∧o32∧o41)∨(o11∧o22∧o32∧o42)∨(o11∧o22∧o32∧o43)∨(o11∧o22∧o33∧o41)∨(o11∧o22∧o33∧o42)∨(o11∧o22∧o33∧o43)∨(o11∧o23∧o31∧o41)∨(o11∧o23∧o31∧o42)∨(o11∧o23∧o31∧o43)∨(o11∧o23∧o32∧o41)∨(o11∧o23∧o32∧o42)∨(o11∧o23∧o32∧o43)∨(o11∧o23∧o33∧o41)∨(o11∧o23∧o33∧o42)∨(o11∧o23∧o33∧o43)∨(o12∧o21∧o31∧o41)∨(o12∧o21∧o31∧o42)∨(o12∧o21∧o31∧o43)∨(o12∧o21∧o32∧o41)∨(o12∧o21∧o32∧o42)∨(o12∧o21∧o32∧o43)∨(o12∧o21∧o33∧o41)∨(o12∧o21∧o33∧o42)∨(o12∧o21∧o33∧o43)∨(o12∧o22∧o31∧o41)∨(o12∧o22∧o31∧o42)∨(o12∧o22∧o31∧o43)∨(o12∧o22∧o32∧o41)∨(o12∧o22∧o32∧o42)∨(o12∧o22∧o32∧o43)∨(o12∧o22∧o33∧o41)∨(o12∧o22∧o33∧o42)∨(o12∧o22∧o33∧o43)∨(o12∧o23∧o31∧o41)∨(o12∧o23∧o31∧o42)∨(o12∧o23∧o31∧o43)∨(o12∧o23∧o32∧o41)∨(o12∧o23∧o32∧o42)∨(o12∧o23∧o32∧o43)∨(o12∧o23∧o33∧o41)∨(o12∧o23∧o33∧o42)∨(o12∧o23∧o33∧o43)∨(o13∧o21∧o31∧o41)∨(o13∧o21∧o31∧o42)∨(o13∧o21∧o31∧o43)∨(o13∧o21∧o32∧o41)∨(o13∧o21∧o32∧o42)∨(o13∧o21∧o32∧o43)∨(o13∧o21∧o33∧o41)∨(o13∧o21∧o33∧o42)∨(o13∧o21∧o33∧o43)∨(o13∧o22∧o31∧o41)∨(o13∧o22∧o31∧o42)∨(o13∧o22∧o31∧o43)∨(o13∧o22∧o32∧o41)∨(o13∧o22∧o32∧o42)∨(o13∧o22∧o32∧o43)∨(o13∧o22∧o33∧o41)∨(o13∧o22∧o33∧o42)∨(o13∧o22∧o33∧o43)∨(o13∧o23∧o31∧o41)∨(o13∧o23∧o31∧o42)∨(o13∧o23∧o31∧o43)∨(o13∧o23∧o32∧o41)∨(o13∧o23∧o32∧o42)∨(o13∧o23∧o32∧o43)∨(o13∧o23∧o33∧o41)∨(o13∧o23∧o33∧o42)∨(o13∧o23∧o33∧o43)";
    // 44ms -> 65ms
    // let s = "((((((((((((((p1↔p2)↔p3)↔p4)↔p5)↔p6)↔p7)↔p8)↔p9)↔p10)↔p11)↔p12)↔p13)↔p14)↔(p14↔(p13↔(p12↔(p11↔(p10↔(p9↔(p8↔(p7↔(p6↔(p5↔(p4↔(p3↔(p2↔p1))))))))))))))";
    // 67ms
    // let s = "p1↔(p2↔(p3↔(p4↔(p5↔(p6↔(p7↔(p8↔(p9↔(p10↔(p11↔(p12↔(p13↔(p14↔(p1↔(p2↔(p3↔(p4↔(p5↔(p6↔(p7↔(p8↔(p9↔(p10↔(p11↔(p12↔(p13↔p14))))))))))))))))))))))))))";

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

    // example(s).unwrap();
    // example_new(s);
    example_new2(s);
}
