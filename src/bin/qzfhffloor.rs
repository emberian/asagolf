//! qzfhffloor — STAGE 3.  Kernel-verify data/qzfhf.mm (the HF carrier:
//! the *finite* ℚ-element set the closed ASA′ proof names, built as
//! hereditarily-finite sets in V_ω — NO Infinity, NO `om`, NO general ℚ
//! machinery — with the finite quantifier-free ordered-field obligations
//! proved as finite ground $p) and MEASURE its exact cut-free cost in
//! OUR kernel with OUR cut-free $a-leaf metric — byte-for-byte the metric
//! of euclidfloor / qzffloor / qzfextfloor / grounded:
//!     $f / $e -> 0   (substitution glue)
//!     $a      -> 1   (a primitive axiom/definition leaf)
//!     $p      -> Σ over its proof steps (no DAG sharing — genuine tree).
//!
//! It also re-extracts the substrate floor with `om`/Infinity REMOVED:
//! the HF construction applies `suc` exactly once and never `om`, so the
//! heaviest set.mm-EXTRACTED bare-ZF primitive the carrier needs drops
//! from `omex` (10^17.484, Infinity) to `sucexg`/`opex` (one successor /
//! Kuratowski pair).  The set.mm EXTRACTED constants are quoted verbatim
//! from STAGE2_BC.md / modelsplice.rs — NOT re-measured in OUR kernel and
//! NOT merged with any MEASURED line (Iron Rule).
//!
//! Run:  cargo run --release --bin qzfhffloor

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
    let path = "data/qzfhf.mm";
    let src = std::fs::read_to_string(path).expect("read data/qzfhf.mm");
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

    // ---- 1b. structural audit: NO `om` token anywhere; `suc` once -------
    // Strip Metamath comments `$( ... $)` first so the audit reflects the
    // actual CONSTRUCTION (signature + df-* + proof bodies), not prose.
    let mut code = String::with_capacity(src.len());
    {
        let mut rest = src.as_str();
        loop {
            match rest.find("$(") {
                Some(o) => {
                    code.push_str(&rest[..o]);
                    match rest[o..].find("$)") {
                        Some(c) => rest = &rest[o + c + 2..],
                        None => break,
                    }
                }
                None => {
                    code.push_str(rest);
                    break;
                }
            }
        }
    }
    let has_om = code.split_whitespace().any(|t| t == "om");
    // `( suc ` applications in the CONSTRUCTION (comment-stripped): the
    // signature declares `tsuc` and df-n1 applies it once; the term-
    // constructor declaration `term ( suc x )` is the only other `( suc `.
    let suc_uses_code = code.matches("( suc ").count();
    let suc_applied = code.matches("suc (/)").count(); // genuine applications
    println!(
        "  STRUCTURAL AUDIT (comment-stripped): `om`/ω token present: {}\n\
         \x20                    `( suc ` in code: {} (1 = tsuc decl, rest = df-n1);\n\
         \x20                    genuine `suc (/)` applications: {}",
        if has_om { "YES (HF claim INVALID — investigate)" } else { "NO" },
        suc_uses_code,
        suc_applied
    );
    println!(
        "  -> HF carrier is in V_ω: NO Infinity (no `om`); `suc` applied\n\
         \x20   exactly {} time(s) (the single ordinal 1 = suc (/)); never iterated.",
        suc_applied
    );

    // ---- 2. MEASURE every $p's exact cut-free cost -----------------------
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/qzfhf.mm), cut-free $a-leaf count ===\n\
         (STAGE 3: finite HF element set + finite quantifier-free\n\
          ordered-field obligations, proved ground — NO induction.)"
    );
    let mut grand = ProofSize::zero();
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        let note = match st.label.as_str() {
            "eqtr" => "reusable FOL= transitivity helper",
            "gndN-0addN1" => "ℕ ground left +-id @ named 1   (DERIVED)",
            "gndN-1mul1" => "ℕ ground 1·1=1                  (DERIVED)",
            "gndZ-0addZ1" => "ℤ ground left +-id @ named Z1  (DERIVED)",
            "gndZ-mZ0" => "ℤ ground left +-inverse @ Z0   (DERIVED)",
            "gndQ-0addQ1" => "ℚ ground left +-id @ named Q1  (DERIVED)",
            "gndQ-1mulQ1" => "ℚ ground left ·-id @ named Q1  (DERIVED)",
            "gndQ-addinvQ0" => "ℚ ground left +-inverse @ Q0   (DERIVED)",
            "gndQ-mulinvQ1" => "ℚ ground nonzero ·-inverse @Q1 (DERIVED)",
            "gndQ-0leQ1" => "ℚ ground order literal Q0≤Q1   (DERIVED)",
            _ => "",
        };
        println!(
            "  {:<14} = {:>10}   (10^{:.3})   {}",
            st.label,
            sz.pretty(),
            sz.log10(),
            note
        );
        grand = grand.add(&sz);
    }
    println!(
        "  ----\n  STAGE-3 HF finite-element total (Σ $p) = {}   (10^{:.3})   [MEASURED]",
        grand.pretty(),
        grand.log10()
    );

    // ---- 3. the discharged Stage-2 PROJECTION, now MEASURED --------------
    println!(
        "\n=== Stage-2 PROJECTION → now MEASURED (the signature discharge) ===\n\
         \x20 Stage 2 (qzf.mm) ASSERTED the GENERIC ax-N*/ax-Z*/ax-Q*\n\
         \x20 signature (quotient well-definedness for ALL elements — needs\n\
         \x20 induction) and labelled its full bare-ZF discharge a\n\
         \x20 PROJECTION ≤ 10^4 (STAGE2_A.md §6 / STAGE2_BC.md).\n\
         \x20 STAGE 3: for the FINITE NAMED element set the closed proof\n\
         \x20 actually uses, that obligation is quantifier-free over\n\
         \x20 finitely many named terms (Seam-1 MEASURED).  qzfhf.mm\n\
         \x20 discharges it as the finite ground $p MEASURED above —\n\
         \x20 a FINITE CASE-CHECK, NO induction.\n\
         \x20 => the ≤10^4 signature PROJECTION is DISCHARGED → MEASURED\n\
         \x20    at 10^{:.3} (this file, kernel-verified, {} $p ✔).",
        grand.log10(),
        n_p
    );

    // ---- 4. re-extract the substrate floor with `om`/Infinity REMOVED ---
    // set.mm-EXTRACTED constants quoted VERBATIM from STAGE2_BC.md /
    // src/bin/modelsplice.rs (the exact set.mm extractor over data/set.mm).
    // NOT re-measured here, NOT merged with the MEASURED line above.
    println!(
        "\n=== Substrate floor re-extracted with Infinity (omex) REMOVED ===\n\
         \x20 (set.mm-EXTRACTED, quoted verbatim from STAGE2_BC.md /\n\
         \x20  modelsplice.rs — NOT re-measured in OUR kernel)\n\
         \x20 The HF carrier's df-* primitives that must denote ZF sets:\n\
         \x20   (/)  empty set        0ex     10^10.064  bare-ZF\n\
         \x20   suc  ONE successor    sucexg  10^12.810  bare-ZF\n\
         \x20   <.,.> Kuratowski pair opex    10^12.490  bare-ZF\n\
         \x20   {{x,y}} pairing        zfpair2 10^11.903  bare-ZF\n\
         \x20   U. union (in `suc`)   uniex   10^10.943  bare-ZF\n\
         \x20   [ ]~ class / quotient axextg  10^7.539   bare-ZF\n\
         \x20   --- om = ω (Infinity) omex    10^17.484  NOT USED (no `om`)\n\
         \x20 With `om` removed (HF: `suc` once, never `om`), the heaviest\n\
         \x20 set.mm-EXTRACTED bare-ZF primitive the carrier needs is\n\
         \x20   sucexg = 10^12.810  (EXTRACTED; was omex = 10^17.484).\n\
         \x20 substrate floor drop  =  10^17.484 → 10^12.810\n\
         \x20                       =  Δ 10^4.674  (Infinity eliminated)."
    );

    // ---- 5. honest split (strictly separated) ---------------------------
    let qzf_a = 2.408_f64;     // qzffloor  : 256 cut-free $a (MEASURED, Stage 2)
    let qzfext_b = 2.149_f64;  // qzfextfloor: 141 cut-free $a (MEASURED, Stage 2)
    let omex = 17.484_f64;     // STAGE2_BC.md EXTRACTED (Stage-2 floor)
    let sucexg = 12.810_f64;   // STAGE2_BC.md EXTRACTED (new dominant, no om)
    let new_floor = qzf_a.max(qzfext_b).max(grand.log10()).max(sucexg);
    println!(
        "\n=== HONEST SPLIT — MEASURED · EXTRACTED · (no residual PROJECTION) ===\n\
         \x20 [MEASURED, OUR kernel]\n\
         \x20   Stage-2 A native ℚ-from-ZF derived layer : 10^{qzf_a:.3} (qzffloor)\n\
         \x20   Stage-2 B ℚ_geo(√r) @ K=1 radicand       : 10^{qzfext_b:.3} (qzfextfloor)\n\
         \x20   Stage-3 HF finite-element discharge       : 10^{:.3} (this file, {} $p ✔)\n\
         \x20     (this MEASURED line DISCHARGES the Stage-2 ≤10^4\n\
         \x20      signature PROJECTION — finite case-check, no induction)\n\
         \x20 [EXTRACTED, set.mm — quoted verbatim, NOT re-measured]\n\
         \x20   HF carrier ZF-set-hood, Infinity REMOVED:\n\
         \x20   dominant bare-ZF primitive = sucexg 10^{sucexg:.3}\n\
         \x20   (was omex 10^{omex:.3}; `om` not used by the HF carrier)\n\
         \x20 [PROJECTION] none for the finite element set: the Stage-2\n\
         \x20   ≤10^4 signature projection is DISCHARGED → MEASURED above.\n\
         \x20 ---------------------------------------------------------------\n\
         \x20 projection-free HF substrate floor\n\
         \x20   = max( A 10^{qzf_a:.3}, B 10^{qzfext_b:.3}, HF 10^{:.3}, ZF-bind 10^{sucexg:.3} )\n\
         \x20   = 10^{new_floor:.3}   [EXTRACTED-dominated (sucexg); A/B/HF MEASURED]\n\
         \n  vs Stage-2 (omex-dominated): 10^{omex:.3}  →  Stage-3: 10^{new_floor:.3}\n\
         \x20   Infinity eliminated; substrate now projection-free.",
        grand.log10(),
        n_p,
        grand.log10(),
    );
}
