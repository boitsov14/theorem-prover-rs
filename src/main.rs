mod formula;
mod naming;
mod parser;
mod prover;

use crate::parser::parse;

fn main() {
    prover::example();
    return;

    println!("Hello, world!");
    let s = "P and Q and R or S";
    let Some((fml, inf)) = parse(s) else {
        return;
    };
    let fml = fml.universal_quantify();
    println!("{}", fml.display(&inf));
}
