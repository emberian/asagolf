//! qzffloor — kernel-verify data/qzf.mm (Milestone A: ℚ built natively
//! from ZF — ω→ℕ→ℤ→ℚ as ZF sets, the ordered-field laws as $p) and
//! MEASURE its exact cut-free cost in OUR kernel with OUR cut-free metric
//! (the same `$a`-leaf-count metric as euclidfloor / grounded — the
//! project metric used everywhere).
//!
//! Run:  cargo run --release --bin qzffloor
//!
//! Every MEASURED line is produced here from OUR kernel over data/qzf.mm.
//! Any PROJECTION line is a labelled derivation, never recomputed or
//! merged into a measured figure (Iron Rule).

#[path = "../kernel.rs"]
mod kernel;
#[path = "../number.rs"]
mod number;

use number::ProofSize;
use std::collections::HashMap;

/// Cut-free, fully-inlined $a-leaf count of `label` (the project metric):
///   $f / $e -> 0 (substitution glue)
///   $a      -> 1 (a primitive axiom/definition leaf)
///   $p      -> Σ over its proof steps (no DAG sharing — the genuine
///              expanded tree).  Identical to euclidfloor's `expand`.
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
    let path = "data/qzf.mm";
    let src = std::fs::read_to_string(path).expect("read data/qzf.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };

    // ---- 1. kernel verdict (the trust root re-checks every $p) -----------
    match db.verify() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("KERNEL REJECTED: {e}");
            std::process::exit(1);
        }
    }
    let n_p = db
        .stmts
        .iter()
        .filter(|s| s.kind == kernel::Kind::P)
        .count();
    println!(
        "Kernel: verified all {n_p} $p in {} ✔  (db: {} statements)",
        path,
        db.stmts.len()
    );

    // ---- 2. MEASURE every $p's exact cut-free cost -----------------------
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/qzf.mm), cut-free $a-leaf count ==="
    );
    let mut grand = ProofSize::zero();
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<14} = {:>16}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
        grand = grand.add(&sz);
    }
    println!(
        "  ----\n  Milestone-A ℚ-from-ZF total (Σ $p) = {}   (10^{:.3})   [MEASURED]",
        grand.pretty(),
        grand.log10()
    );

    // ---- 3. honest comparison to the set.mm substrate floor --------------
    // EXTRACTED constants quoted verbatim from EUCLID_FLOOR.md (the exact
    // set.mm extractor over data/set.mm) — NOT recomputed or measured here.
    println!(
        "\n=== set.mm-EXTRACTED substrate floor (from EUCLID_FLOOR.md; NOT measured here) ==="
    );
    println!("  full analytic-ℝ model (resqrtth)        : 10^45.74");
    println!("  set.mm √-primitive residual (msqge0)    : 10^37.19");
    println!("  from-ZF twin achievable (axmulass)      : 10^30.75");
    println!("  strict extractable lower bound(axresscn): 10^25.95");
    println!(
        "\n  Native ℚ-from-ZF construction (MEASURED above) vs set.mm's"
    );
    println!(
        "  ℚ-through-CCfld (qsubdrg, 10^46.10 EXTRACTED): see STAGE2_A.md §6."
    );
}
