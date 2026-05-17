//! sdggaugefloor — kernel-verify data/sdg.gauge.mm (the SYNTHETIC
//! GAUGE-CONNECTION layer, the Book-3 target foundation) and MEASURE
//! each result's exact cut-free cost in OUR kernel with OUR project
//! metric (the same $a-leaf count used by sdgfloor / sdgconnfloor /
//! sdgtanfloor / euclidfloor / qzffloor).
//!
//! Run:  cargo run --release --bin sdggaugefloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.gauge.mm.  The field-strength / Bianchi / FULL gauge-
//! covariance seam (B3-curv = the full curvature generator) is
//! explicitly NOT in scope here; it is named as the precise deferred
//! Book-3 dependency, never summed into a measured figure (Iron Rule).

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
    let path = "data/sdg.gauge.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.gauge.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.gauge.mm), cut-free $a-leaf count ==="
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
        "\n=== Field-strength / Bianchi / FULL gauge-covariance seam — DEFERRED ===\n  \
         The cleanly-reachable structural layer (transport0, kl-affine,\n  \
         conj-welldef, law-affine, F-cross) is PURE RING — no\n  \
         microcancellation, no globalization, nothing classical.  A is\n  \
         KL-affine; the gauge-transformation law of A is well-defined;\n  \
         the symmetric zeroth-order part of F vanishes by RING.\n  \
         GAUGE-COVARIANCE carries EXACTLY ONE labelled boundary $e\n  \
         (gauge.fstr): F's genuine curvature value + its Bianchi + its\n  \
         FULL gauge-covariance is BOTH (a) ap-congruence AND (b) the\n  \
         full curvature generator B3-curv (the globalized bracket).\n  \
         This is the PRECISE Book-3 dependency map: F's genuine value /\n  \
         Bianchi / full covariance genuinely need B3-curv.  It is named\n  \
         as the deferred Book-3 keystone, never summed here.  [DEFERRED]"
    );
}
