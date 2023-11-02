mod formula;
mod naming;
mod parser;
mod prover;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    prover::example();
    // prover::example_iltp_prop();
    return;

    println!("Hello, world!");
    let s = "P and Q and R or S";
    let Some((fml, inf)) = parser::parse(s) else {
        return;
    };
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&inf));
}
