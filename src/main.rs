use mimalloc::MiMalloc;
use theorem_prover_rs::new_prover2::example_new2;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
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

    example_new2(s).unwrap();
}
