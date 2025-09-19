use crate::{
    app::LatexError,
    core::{names::Names, parser::parse_sequent},
    prover::{
        kernel::{ProofResult, prove_prop},
        latex::{Latex, sequent_calculus, tableau_method},
        sequent::Sequent,
    },
};
use insta::assert_snapshot;
use std::fs;
use tempfile::TempDir;
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
        if let Some(line) = line.strip_prefix('#') {
            // extract name from comment
            name = line.trim().replace('\'', "").replace([' ', '+', '.'], "-");
        } else if !line.is_empty() {
            println!("testing: {line}");
            // settings for snapshot tests
            let mut settings = insta::Settings::new();
            // short file names
            settings.set_prepend_module_to_snapshot(false);
            // snapshot path
            settings.set_snapshot_path(format!("../../../snapshots/{file}"));

            // create temporary directory for each test case
            let temp = TempDir::new().unwrap();
            let temp = temp.path();

            // parse sequent
            let mut names = Names::default();
            let seq = parse_sequent(line, &mut names, true, false).unwrap();
            let seq = Sequent::new(&seq);
            let seq_unicode = seq.display(&names).to_unicode();

            // check provability
            let proof_result = prove_prop(seq.clone(), &names);
            let provability = matches!(proof_result, ProofResult::Proved);
            println!("{provability}");
            assert!(provability);

            // ebproof
            println!("ebproof...");
            // generate ebproof latex file
            sequent_calculus(seq.clone(), &names, temp.to_str().unwrap(), Latex::Ebproof).unwrap();
            let ebproof_content = fs::read_to_string(temp.join("ebproof.tex")).unwrap();
            // snapshot test for ebproof
            settings.bind(|| {
                assert_snapshot!(
                    format!("{idx}-ebproof-{name}"),
                    ebproof_content,
                    &seq_unicode
                );
            });
            println!("done");

            // bussproofs
            println!("bussproofs...");
            // generate bussproofs latex file
            match sequent_calculus(
                seq.clone(),
                &names,
                temp.to_str().unwrap(),
                Latex::Bussproofs,
            ) {
                Ok(()) => {
                    let bussproofs_content =
                        fs::read_to_string(temp.join("bussproofs.tex")).unwrap();
                    // snapshot test for bussproofs
                    settings.bind(|| {
                        assert_snapshot!(
                            format!("{idx}-bussproofs-{name}"),
                            bussproofs_content,
                            &seq_unicode
                        );
                    });
                    println!("done");
                }
                Err(LatexError::TooManyBranches) => {
                    println!("skipped (too many branches)");
                }
                Err(_) => unreachable!(),
            }

            // forest
            println!("forest...");
            // generate forest latex file
            tableau_method(seq, &names, temp.to_str().unwrap()).unwrap();
            let forest_content = fs::read_to_string(temp.join("forest.tex")).unwrap();
            // snapshot test for forest
            settings.bind(|| {
                assert_snapshot!(format!("{idx}-forest-{name}"), forest_content, &seq_unicode);
            });
            println!("done");

            idx += 1;
        }
    }
}
