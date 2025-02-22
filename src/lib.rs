mod intern;
mod lang;
mod parser;
mod prover;

use mimalloc::MiMalloc;
use prover::prove;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn main_prover() {
    // let s = "P and Q to Q and P";
    // 0.80520004 ms to prove
    // 547.71094 ms to print to file -> 10ms
    // 1.6MB
    let s = "(((((((((p6↔p7)↔p8)↔p9)↔p10)↔p11)↔p12)↔p13)↔p14)↔(p14↔(p13↔(p12↔(p11↔(p10↔(p9↔(p8↔(p7↔p6)))))))))";
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

    prove(s).unwrap();
}
