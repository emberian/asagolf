//! sdgcalcfloor — kernel-verify data/sdg.calc.mm (the POINTWISE synthetic
//! differentiation rules) and MEASURE each rule's exact cut-free cost in
//! OUR kernel with OUR project metric (the same $a-leaf count used by
//! sdgfloor / euclidfloor / qzffloor / grounded).
//!
//! Run:  cargo run --release --bin sdgcalcfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.calc.mm.  The pointwise->global linking seam is the separate
//! keystone SDG-K and is explicitly NOT in scope here (these rules are
//! pointwise by construction); it is named as a deferred milestone, never
//! summed into a measured figure (Iron Rule).

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
    let path = "data/sdg.calc.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.calc.mm");
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
        "Kernel: verified all {n_p} $p in {} OK  (db: {} statements)",
        path,
        db.stmts.len()
    );

    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/sdg.calc.mm), cut-free $a-leaf count ==="
    );
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<18} = {:>16}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
    }

    println!("\n=== POINTWISE differentiation rules — headline MEASURED costs ===");
    for r in ["sdg-calc-sum", "sdg-calc-prod", "sdg-calc-chain"] {
        if let Some(s) = db.get(r) {
            if s.kind == kernel::Kind::P {
                let sz = expand(&db, r, &mut memo);
                println!(
                    "  >>> {:<14} = {}  (10^{:.3})  [MEASURED]",
                    r,
                    sz.pretty(),
                    sz.log10()
                );
            }
        }
    }

    println!(
        "\n=== Pointwise->global linking seam — explicitly DEFERRED (NOT here) ===\n  \
         These rules are POINTWISE by construction (the affine slope reps\n  \
         are $e hypotheses; no ax-microcancel, no ax-gen over a linking\n  \
         universal).  Globalising them — discharging the pointwise\n  \
         identity into a universally-quantified derivative equation via\n  \
         the pointwise->global seam — is the SEPARATE keystone SDG-K and\n  \
         is deliberately NOT attempted or summed here.  [DEFERRED]\n  \
         CHAIN additionally carries ONE explicit ap-Leibniz $e\n  \
         (chain.sub): the substrate instantiates congruence only for + and\n  \
         * , not for the application symbol `ap`.  This is a substrate-\n  \
         instantiation gap (NOT classical, NOT the global seam), surfaced\n  \
         honestly as a labelled hypothesis."
    );
}
