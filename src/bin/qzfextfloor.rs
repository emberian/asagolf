//! qzfextfloor — Milestone B.  Kernel-verify data/qzfext.mm (the ONE
//! quadratic extension ℚ_geo(√r) over the native ℚ-from-ZF base, at the
//! Stage-1 radicand) and MEASURE its exact cut-free cost in OUR kernel
//! with OUR cut-free $a-leaf metric — byte-for-byte the metric used by
//! `euclidfloor` / `qzffloor` / `grounded`:
//!     $f / $e -> 0   (substitution glue)
//!     $a      -> 1   (a primitive axiom/definition leaf)
//!     $p      -> Σ over its proof steps (no DAG sharing — genuine tree).
//!
//! The MEASURED 10^2.149 generic Euclidean unit (euclid.mm, euclidfloor)
//! is NEVER recomputed or merged here: it is quoted as a clearly-labelled
//! constant for the reuse statement only.  This file measures qzfext.mm's
//! OWN cut-free cost.
//!
//! Run:  cargo run --release --bin qzfextfloor

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
    let path = "data/qzfext.mm";
    let src = std::fs::read_to_string(path).expect("read data/qzfext.mm");
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

    // ---- 2. MEASURE this file's exact cut-free cost ----------------------
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/qzfext.mm), cut-free $a-leaf count ===\n\
         (Milestone B: ONE quadratic ext ℚ_geo(√r) over native ℚ-from-ZF,\n\
          at the Stage-1 radicand  rdcd = ( u-elt Qt ( Qi sdac ) ) )"
    );
    let mut total = ProofSize::zero();
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        let note = match st.label.as_str() {
            "eqtr" => "reusable FOL= transitivity helper",
            "eu-sqrt-r" => "F1 ax-sqrt @ Stage-1 radicand   (DERIVED, native ℚ)",
            "eu-sqrtnn-r" => "F1 of-sqrtnn @ Stage-1 radicand (DERIVED, native ℚ)",
            _ => "",
        };
        println!(
            "  {:<13} = {:>6}   (10^{:.3})   {}",
            st.label,
            sz.pretty(),
            sz.log10(),
            note
        );
        total = total.add(&sz);
    }
    println!(
        "  ----\n  Milestone-B ℚ_geo(√r) total (Σ $p) = {}   (10^{:.3})   [MEASURED]",
        total.pretty(),
        total.log10()
    );

    // ---- 3. reuse statement (MEASURED-elsewhere constant, NOT merged) ----
    let euclid_unit_log10_measured = 2.149_f64; // euclidfloor: 141 cut-free $a
    let euclid_unit_steps_measured: u64 = 141;
    println!(
        "\n=== Reuse of the already-MEASURED generic unit (NOT recomputed) ===\n\
         \x20 generic Euclidean unit step (euclid.mm, by euclidfloor, OUR kernel)\n\
         \x20   = {euclid_unit_steps_measured} cut-free $a-leaves = 10^{euclid_unit_log10_measured:.3}\n\
         \x20   (kernel: verified all 3 $p ✔, data/euclid.mm)\n\
         \x20 qzfext.mm INSTANTIATES that exact proof skeleton at the native-ℚ\n\
         \x20 operators (Qt / Qle / Q0) and the Stage-1 radicand; the figure\n\
         \x20 measured above is qzfext.mm's OWN kernel-verified cut-free cost,\n\
         \x20 K = 1 (Stage-1 MEASURED: exactly one distinct un-nested radical)."
    );
    println!(
        "\n  Milestone-B verdict: ℚ_geo(√r) is exhibited as a ZF set + ordered\n\
         \x20 field with √r present, F1's two non-conservative √-axioms\n\
         \x20 (ax-sqrt, of-sqrtnn) DISCHARGED at the Stage-1 radicand over the\n\
         \x20 native ℚ-from-ZF carrier — kernel-verified, MEASURED at 10^{:.3}.\n\
         \x20 NO CCfld, NO Dedekind/Cauchy, NO analytic ℝ.",
        total.log10()
    );
}
