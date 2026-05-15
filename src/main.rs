//! birkhoff-asa: symbolic estimator for the fully-expanded ZFC proof size of
//! the Angle-Side-Angle theorem in a Birkhoff (ruler/protractor) formalism.
//!
//! Run:  cargo run --release

mod dag;
#[allow(dead_code)]
mod kernel;
mod model;
mod number;

use model::{build, Foundation, Kernel};

fn ratio_log10(num: &number::ProofSize, den: &number::ProofSize) -> f64 {
    num.log10() - den.log10()
}

fn row(found: Foundation, kernel: Kernel) -> (number::ProofSize, number::ProofSize, f64) {
    let b = build(found, kernel);
    let exp = b.dag.expand();
    let asa = exp[b.asa].clone();
    // Fraction of ASA's expanded nodes attributable to the ℝ substrate.
    let sub = exp[b.real_substrate].nodes.log10();
    let frac = sub - asa.nodes.log10(); // log10 of the share
    (asa.nodes, asa.bits, frac)
}

fn main() {
    use Foundation::*;
    use Kernel::*;

    let founds = [
        ("F0  ordered field (added, ASA-minimal)", F0OrderedField),
        ("F1  Euclidean field (added)", F1EuclideanField),
        ("F2  constructive Cauchy reals in ZFC", F2ConstructiveReals),
        ("F3  Dedekind reals + LUB (all of analysis)", F3DedekindReals),
    ];

    println!("\n=== Fully-expanded ZFC proof of ASA (Birkhoff formalism) ===");
    println!("PRE-CALIBRATION estimates — structure is real, magnitudes are placeholders.\n");

    for (kname, k) in [("Metamath-CD kernel", MetamathCD), ("raw-Hilbert kernel", RawHilbert)] {
        println!("── {kname} ──────────────────────────────────────────");
        println!(
            "{:<44} {:>26} {:>30}",
            "foundation", "proof-tree nodes", "written bitlength"
        );
        for (label, f) in &founds {
            let (nodes, bits, _) = row(*f, k);
            println!("{:<44} {:>26} {:>30}", label, nodes.pretty(), bits.pretty());
        }
        println!();
    }

    println!("── headline gaps (Metamath-CD kernel, node metric) ──────");
    let f0 = row(F0OrderedField, MetamathCD).0;
    let f2 = row(F2ConstructiveReals, MetamathCD).0;
    let f3 = row(F3DedekindReals, MetamathCD).0;
    println!(
        "  F3/F0  (cost of constructed completeness you don't need) : 10^{:.2}",
        ratio_log10(&f3, &f0)
    );
    println!(
        "  F3/F2  (classical Dedekind  vs  constructive Cauchy)     : 10^{:.2}",
        ratio_log10(&f3, &f2)
    );
    let (_, _, frac_f3) = row(F3DedekindReals, MetamathCD);
    println!(
        "  ℝ-substrate share of F3 ASA nodes                        : 10^{:.2} of total",
        frac_f3
    );
    let kern_mult = ratio_log10(&row(F3DedekindReals, RawHilbert).0, &f3);
    println!(
        "  raw-Hilbert / Metamath-CD kernel multiplier (F3)         : 10^{:.2}",
        kern_mult
    );

    println!(
        "\nNext: calibrate per-lemma constants against real set.mm stats \
         (peano5 ≈ 7.5e10 anchor).\n"
    );
}
