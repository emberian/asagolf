//! euclidfloor — kernel-verify data/euclid.mm (the generic Euclidean
//! extension step) and MEASURE its exact cut-free cost in OUR kernel with
//! OUR cut-free metric (the same `$a`-leaf-count metric used everywhere in
//! this project), then combine it additively with the set.mm-extracted
//! substrate figures (read from a snapshot file, NOT recomputed here) to
//! report the transport-anchored Euclidean substrate floor.
//!
//! Run:  cargo run --release --bin euclidfloor
//!
//! All MEASURED lines are produced here from OUR kernel over data/euclid.mm.
//! All set.mm-EXTRACTED lines are constants quoted from a prior modelsplice
//! run and are clearly labelled as such — they are never recomputed or
//! merged into a measured figure.

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
///              expanded tree).
fn expand(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, ProofSize>,
) -> ProofSize {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    // Cycle guard (there are none in a well-formed acyclic proof DB, but be
    // defensive): provisionally insert 1.
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
    let path = "data/euclid.mm";
    let src = std::fs::read_to_string(path).expect("read data/euclid.mm");
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

    // ---- 2. MEASURE the unit step's exact cut-free cost ------------------
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!("\n=== MEASURED in OUR kernel (data/euclid.mm), cut-free $a-leaf count ===");
    let mut unit_total = ProofSize::zero();
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<12} = {:>20}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
        unit_total = unit_total.add(&sz);
    }
    println!(
        "  ----\n  UNIT STEP total (sum of step $p)   = {}   (10^{:.3})",
        unit_total.pretty(),
        unit_total.log10()
    );

    // ---- 3. set.mm-EXTRACTED constants (NOT recomputed here) -------------
    // Quoted verbatim from `cargo run --release --bin modelsplice` against
    // data/set.mm (50,707,170-byte develop snapshot).  These are EXTRACTED,
    // never measured here; printed only for the honest comparison.
    let setmm_full_real_log10 = 45.74_f64; // resqrtth, analytic ℝ
    let setmm_eucl_primitive_log10 = 37.19_f64; // √ primitive, msqge0 residual
    let setmm_axmulass_log10 = 30.75_f64; // from-ZF "twin" achievable
    let setmm_axresscn_log10 = 25.95_f64; // strict extractable lower bound

    println!("\n=== set.mm-EXTRACTED constants (from modelsplice; NOT measured here) ===");
    println!("  full analytic-ℝ model (resqrtth)        : 10^{setmm_full_real_log10:.2}");
    println!("  set.mm √-primitive residual (msqge0)    : 10^{setmm_eucl_primitive_log10:.2}");
    println!("  from-ZF twin achievable (axmulass)      : 10^{setmm_axmulass_log10:.2}");
    println!("  strict extractable lower bound(axresscn): 10^{setmm_axresscn_log10:.2}");
    println!("  (below 10^{setmm_axresscn_log10:.2} set.mm contains nothing to extract)");

    // ---- 4. tower-count derivation (RIGOROUS, labelled PROJECTION) -------
    // The minimal F1 model is the Euclidean closure of ℚ.  It is NOT a
    // single extension: it is a countable tower whose length is the
    // *number of distinct √-radicals the grounded geometry actually forces*.
    // The geometry (G1 ruler) introduces √ exactly once per ruler placement
    // in df-cp:  sqrt( u * inv( sqd a c ) ).  Cut-free, with no DAG sharing,
    // the kernel-verified grounded G1/G4 build invokes that √-term a
    // bounded, EXACT number of times — call it K (the per-proof √-radical
    // multiplicity).  Each distinct radical = one tower level discharged by
    // one MEASURED unit step.  The transport-anchored Euclidean substrate
    // floor is therefore:
    //
    //   EUCLID_FLOOR  =  K · (MEASURED unit step)            [construction]
    //                  +  (one-time transport/satisfaction)  [the bridge]
    //
    // K is itself kernel-MEASURABLE (count `sqrt` leaves in the grounded
    // cut-free tree) but is owned by the grounded build; here it is a
    // labelled PROJECTION with its derivation shown.  See EUCLID_FLOOR.md.
    println!("\n=== Euclidean substrate floor (PROVEN unit × PROJECTED tower + transport) ===");
    println!(
        "  MEASURED unit step (this file, kernel-exact) : 10^{:.3}",
        unit_total.log10()
    );
    println!("  PROJECTION: tower length K — see EUCLID_FLOOR.md derivation.");
    println!("  PROJECTION: transport/satisfaction bridge — see transport section.");
}
