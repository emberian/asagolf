//! sdgfloor — kernel-verify data/sdg.mm (the certified-intuitionistic SDG
//! substrate + the first synthetic-derivative theorem) and MEASURE its
//! exact cut-free cost in OUR kernel with OUR project metric (the same
//! `$a`-leaf count used by euclidfloor / qzffloor / grounded).
//!
//! Run:  cargo run --release --bin sdgfloor
//!
//! Every MEASURED line is produced here from OUR kernel over data/sdg.mm.
//! The substrate-grounding question (a model of SDG — a well-adapted
//! topos) is named as an explicitly-labelled PROJECTION and is NEVER
//! computed or merged into a measured figure (Iron Rule).

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
    let path = "data/sdg.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };

    // ---- 1. kernel verdict (the trust root re-checks every $p) ----------
    match db.verify() {
        Ok(()) => {}
        Err(e) => {
            eprintln!("KERNEL REJECTED: {e}");
            std::process::exit(1);
        }
    }
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!(
        "Kernel: verified all {n_p} $p in {} ✔  (db: {} statements)",
        path,
        db.stmts.len()
    );

    // ---- 2. MEASURE every $p's exact cut-free cost ----------------------
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!("\n=== MEASURED in OUR kernel (data/sdg.mm), cut-free $a-leaf count ===");
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
    }

    // The headline: the first synthetic-differential theorem.
    if let Some(s) = db.get("sdg-deriv") {
        if s.kind == kernel::Kind::P {
            let sz = expand(&db, "sdg-deriv", &mut memo);
            println!(
                "\n  >>> FIRST SYNTHETIC DERIVATIVE  sdg-deriv  =  {}  (10^{:.3})  [MEASURED]",
                sz.pretty(),
                sz.log10()
            );
        }
    }

    // §5k: the Lie-bracket globalization half (b), CLOSED seam-free.
    if let Some(s) = db.get("sdg-bracket-global") {
        if s.kind == kernel::Kind::P {
            let sz = expand(&db, "sdg-bracket-global", &mut memo);
            println!(
                "\n  >>> LIE BRACKET (globalization half b, SEAM-FREE)  \
                 sdg-bracket-global  =  {}  (10^{:.3})  [MEASURED]\n  \
                 (the bracket principal part [X,Y]=X(q)-Y(p) is uniquely\n  \
                 determined; X(q)/Y(p) carried as universal ax-kl-EXISTENCE\n  \
                 $e; linking universal threaded via §5b seam + ax-gen +\n  \
                 ax-microcancel — NO tanbr.flow $e, NO globalization $e)",
                sz.pretty(),
                sz.log10()
            );
        }
    }

    // ---- 3. the model-grounding question — labelled PROJECTION ----------
    println!(
        "\n=== Substrate grounding — explicitly-labelled PROJECTION (NOT measured) ===\n  \
         The dual of the prequel's \"ground ℝ in ZFC\": SDG is consistent /\n  \
         non-vacuous iff it has a model — a well-adapted topos (the Cahiers\n  \
         topos, or 𝓢𝓮𝓽^(𝔻^op) over the dual of finitely-presented C∞-rings),\n  \
         in which D is genuinely non-degenerate and KL holds.  Its\n  \
         construction cost is a SEPARATE quantity, never summed into the\n  \
         proof cost above.  Named here as the next milestone; deliberately\n  \
         NOT attempted in this file.  [PROJECTION]"
    );
}
