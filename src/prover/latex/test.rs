use crate::{
    app::LatexError,
    core::{names::Names, parser::parse_sequent},
    prover::{
        ProofResult,
        get_latex,
        kernel::prove_prop,
        latex::{Latex, sequent_calculus, tableau_method},
        sequent::Sequent,
    },
};
use insta::assert_snapshot;
use std::fs;
use test_case::case;

#[case("props")]
#[case("constants")]
#[case("iltp-props")]
fn test_latex_snapshot(file: &str) {
    // read snapshot file
    let content = fs::read_to_string(format!("examples/snapshots/{file}.txt")).unwrap();
    let mut name = String::new();
    let mut idx = 1;

    for line in content.lines() {
        if line.is_empty() {
            continue;
        }
        if let Some(line) = line.strip_prefix('#') {
            // extract name from comment
            name = line.trim().replace('\'', "").replace([' ', '+', '.'], "-");
            continue;
        }
        println!("testing: {line}");
        // settings for snapshot tests
        let mut settings = insta::Settings::new();
        // short file names
        settings.set_prepend_module_to_snapshot(false);
        // snapshot path
        settings.set_snapshot_path(format!("../../../snapshots/{file}"));

        // parse sequent
        let mut names = Names::default();
        let seq = parse_sequent(line, &mut names, true, false).unwrap();
        let seq = Sequent::new(&seq);
        let seq_unicode = seq.display(&names).to_unicode();

        // check provability
        let result = prove_prop(seq.clone(), &names);
        println!("{result:?}");

        // ebproof
        println!("ebproof...");
        // generate ebproof latex file
        let proof = sequent_calculus(seq.clone(), &names, Latex::Ebproof).unwrap();
        // snapshot test for ebproof
        settings.bind(|| {
            assert_snapshot!(format!("{idx}-ebproof-{name}"), proof, &seq_unicode);
        });
        println!("done");

        // bussproofs
        println!("bussproofs...");
        // generate bussproofs latex file
        let result = sequent_calculus(seq.clone(), &names, Latex::Bussproofs);
        if matches!(&result, Err(LatexError::TooManyBranches)) {
            // skip when too many branches
            println!("skipped (too many branches)");
        }
        if let Ok(proof) = result {
            settings.bind(|| {
                assert_snapshot!(format!("{idx}-bussproofs-{name}"), proof, &seq_unicode);
            });
            println!("done");
        }

        // forest
        println!("forest...");
        // generate forest latex file
        let proof = tableau_method(seq, &names).unwrap();
        // snapshot test for forest
        settings.bind(|| {
            assert_snapshot!(format!("{idx}-forest-{name}"), proof, &seq_unicode);
        });
        println!("done");

        idx += 1;
    }
}

#[test]
fn test_latex_countermodel_snapshot() {
    // read snapshot file
    let content = fs::read_to_string("examples/snapshots/countermodel.txt").unwrap();
    let mut name = String::new();
    let mut idx = 1;

    for line in content.lines() {
        if line.is_empty() {
            continue;
        }
        if let Some(line) = line.strip_prefix('#') {
            // extract name from comment
            name = line.trim().replace('\'', "").replace([' ', '+', '.'], "-");
            continue;
        }
        println!("testing: {line}");
        // settings for snapshot tests
        let mut settings = insta::Settings::new();
        // short file names
        settings.set_prepend_module_to_snapshot(false);
        // snapshot path
        settings.set_snapshot_path("../../../snapshots/countermodel");

        // parse sequent
        let mut names = Names::default();
        let seq = parse_sequent(line, &mut names, true, false).unwrap();
        let seq = Sequent::new(&seq);
        let seq_unicode = seq.display(&names).to_unicode();

        // check provability
        let result = prove_prop(seq.clone(), &names);
        println!("{result:?}");

        // get countermodel
        let ProofResult::Unprovable(countermodel) = &result else {
            unreachable!()
        };
        // create truth table for the countermodel
        let table = countermodel.evaluate(&seq);
        // generate LaTeX table
        let latex = get_latex(&seq, &names, &table);

        // snapshot test
        settings.bind(|| {
            assert_snapshot!(format!("{idx}-{name}"), latex, &seq_unicode);
        });
        println!("done");

        idx += 1;
    }
}
