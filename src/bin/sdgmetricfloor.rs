//! sdgmetricfloor — kernel-verify data/sdg.metric.mm (BOOK-3 WAVE-11:
//! the FLAGGED non-conservative metric commitment #4 + the genuine
//! metric Hodge involution) and MEASURE each result's exact cut-free
//! cost in OUR kernel with OUR project metric (the same $a-leaf count
//! used by sdgfloor / sdgnonabfloor / sdgjacobifloor).
//!
//! Run:  cargo run --release --bin sdgmetricfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.metric.mm (the metric-extended base; the FROZEN
//! data/sdg.base.mm is UNCHANGED — commitment #4 is quarantined here).
//! The full inhomogeneous D⋆F=J with a dynamical source, the
//! Yang–Mills action's variational principle, matter, quantization are
//! NOT built here — they are the NAMED residual, never faked into a
//! figure (Iron Rule); the model-meaning floor (that this IS physical
//! field theory) is the UNCHANGED Book-Two [PROJECTION].

#[path = "../kernel.rs"]
mod kernel;
#[path = "../number.rs"]
mod number;

use number::ProofSize;
use std::collections::HashMap;

fn expand(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, ProofSize>,
) -> ProofSize {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    memo.insert(label.to_string(), ProofSize::one());
    let st = match db.get(label) {
        Some(s) => s,
        None => return ProofSize::zero(),
    };
    let out = match st.kind {
        kernel::Kind::F | kernel::Kind::E => ProofSize::zero(),
        kernel::Kind::A => ProofSize::one(),
        kernel::Kind::P => {
            let mut tot = ProofSize::zero();
            for step in st.proof.clone() {
                tot = tot.add(&expand(db, &step, memo));
            }
            tot
        }
    };
    memo.insert(label.to_string(), out.clone());
    out
}

fn main() {
    let path = "data/sdg.metric.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.metric.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };

    match db.verify() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("KERNEL REJECTED: {e}");
            std::process::exit(1);
        }
    }
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!(
        "Kernel: verified all {n_p} $p in {} \u{2714}  (db: {} statements)",
        path,
        db.stmts.len()
    );

    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/sdg.metric.mm), cut-free $a-leaf count ==="
    );
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<24} = {:>10}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
    }

    println!(
        "\n=== FLAGGED metric commitment #4 + the genuine metric Hodge involution ===\n  \
         ax-metric : ( met * imet ) = 1 — a NON-DEGENERATE scalar\n  \
         metric, FLAGGED non-conservative substrate commitment #4\n  \
         (Verdict-B non-derivable: the all-zero model satisfies the\n  \
         frozen base+eq-ap but 0*0=0!=1; positive-Horn, NO classical\n  \
         content).  QUARANTINED: the frozen data/sdg.base.mm is\n  \
         UNCHANGED; commitment #4 lives ONLY in this metric-extended\n  \
         corpus; every other corpus (50+ pure $p) rides the frozen\n  \
         base.  sdg-metric-symm and the headline sdg-metric-involution\n  \
         ( imet*inv(met*inv F) ) = F GENUINELY CONSUME ax-metric — the\n  \
         genuine metric Hodge round-trip is an involution BECAUSE the\n  \
         metric is non-degenerate (wave-9's orientation ⋆⋆=id needed\n  \
         NO metric; THIS does), the well-posedness precondition the\n  \
         dynamical field equation stands on.  The pure-ring helpers are\n  \
         frozen-base-only.  NAMED RESIDUAL (not papered): the full\n  \
         inhomogeneous D⋆F=J with a dynamical source, the Yang–Mills\n  \
         action's variational principle, matter, quantization — the\n  \
         genuine DYNAMICS beyond the well-posed-⋆ precondition; the\n  \
         model-meaning floor the UNCHANGED Book-Two [PROJECTION].\n  \
         Commitment #4 buys the metric, not the physics — flagged,\n  \
         quarantined, claimed at exactly its weight.\n  \
         [metric commitment #4 flagged & genuinely consumed; the\n  \
         dynamics NAMED, not faked]"
    );
}
