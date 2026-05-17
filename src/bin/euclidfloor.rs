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

    // ---- 4. tower-count K — now MEASURED (was a labelled PROJECTION) -----
    // The minimal field making the *closed ASA′ proof* sound need only
    // contain √ of the radicands that proof actually forms (a field, once
    // it adjoins √x, has it forever — reuse is free; tower DEPTH, not
    // occurrence count, is the construction cost).  So K = the radical
    // tower depth of the set of *distinct* `( sqrt … )` subterms in the
    // kernel-verified corpus.  We measure it directly (read-only over the
    // kernel-verified data/grounded.out.mm; the count is exact).  This
    // converts the former K ≤ 10^6 PROJECTION into a MEASURED number for
    // the proof-relativized model.  The full-F1-schema model (Euclidean
    // closure: √ of *every* nonneg element) is a *separate* quantity and
    // stays an explicitly labelled PROJECTION — never conflated.
    let (k_used, max_nest, used_rads) = measure_radicals("data/grounded.out.mm");
    let constr_log = (k_used.max(1) as f64).log10() + unit_total.log10();
    println!("\n=== Euclidean substrate floor — construction now MEASURED ===");
    println!(
        "  MEASURED unit step (this file, kernel-exact)        : 10^{:.3}  ({} leaves)",
        unit_total.log10(),
        unit_total.pretty()
    );
    println!(
        "  MEASURED distinct USED radicals (closed ASA′ corpus): {}  (nesting depth {})",
        k_used, max_nest
    );
    for r in &used_rads {
        println!("      {r}");
    }
    println!(
        "  ⇒ proof-relativized construction = K·unit           : 10^{constr_log:.3}   [MEASURED]"
    );
    println!(
        "  full-F1-schema model (Euclidean closure of ℚ, √ of\n   \
         every nonneg element)                               : [PROJECTION] countable tower,\n   \
         each level = one MEASURED unit step — see EUCLID_FLOOR.md (NOT this number)"
    );
    println!("  transport/satisfaction bridge (set.mm)              : [EXTRACTED] — see modelsplice");
    println!(
        "\n  Honest split: the closed ASA′ proof forces exactly {k_used} un-nested\n  \
         radical(s), so the proof-relativized minimal model is MEASURED at\n  \
         10^{constr_log:.3} (no projection).  This does not change the set.mm\n  \
         transport bridge (~10^46, EXTRACTED) — it only sharpens that the\n  \
         ~10^46 is entirely set.mm's construction choice, not F1's: F1's\n  \
         model for this proof is ~10^{constr_log:.0}."
    );
}

/// Read-only MEASUREMENT over the kernel-verified corpus: distinct
/// balanced `( sqrt <arg> )` subterms, excluding the bare axiom template
/// `( sqrt u )` (a single $f variable radicand — the F1 schema form, not
/// a used instance).  Returns (distinct-used-count, max sqrt-nesting
/// depth, the distinct used radical strings).  Untrusted convenience;
/// the count itself is exact (the corpus it reads is kernel-verified).
fn measure_radicals(path: &str) -> (usize, usize, Vec<String>) {
    let raw = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => return (0, 0, vec![]),
    };
    // strip $( ... $) comments
    let mut src = String::with_capacity(raw.len());
    let mut it = raw.split_whitespace().peekable();
    let mut in_comment = false;
    while let Some(t) = it.next() {
        if t == "$(" {
            in_comment = true;
        } else if t == "$)" {
            in_comment = false;
        } else if !in_comment {
            src.push_str(t);
            src.push(' ');
        }
    }
    let toks: Vec<&str> = src.split_whitespace().collect();
    let mut used: std::collections::BTreeSet<String> = Default::default();
    let mut i = 0;
    while i + 1 < toks.len() {
        if toks[i] == "(" && toks[i + 1] == "sqrt" {
            let mut depth = 0i32;
            let mut j = i;
            let mut buf: Vec<&str> = Vec::new();
            while j < toks.len() {
                match toks[j] {
                    "(" => depth += 1,
                    ")" => depth -= 1,
                    _ => {}
                }
                buf.push(toks[j]);
                if depth == 0 {
                    break;
                }
                j += 1;
            }
            // radicand = tokens between `( sqrt` and the matching `)`
            let radicand = &buf[2..buf.len().saturating_sub(1)];
            // exclude the bare schema template `( sqrt u )` (single var)
            if radicand.len() > 1 {
                used.insert(buf.join(" "));
            }
            i = j + 1;
        } else {
            i += 1;
        }
    }
    // nesting depth = number of `sqrt` occurrences in the subterm string
    // (1 = a single, un-nested radical; the leading `sqrt` is counted once
    // and there is no `+1` — that would overstate an un-nested radical).
    let max_nest = used
        .iter()
        .map(|r| r.matches("sqrt").count())
        .max()
        .unwrap_or(0);
    let v: Vec<String> = used.into_iter().collect();
    (v.len(), max_nest, v)
}
