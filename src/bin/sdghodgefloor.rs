//! sdghodgefloor — kernel-verify data/sdg.hodge.mm (BOOK-3 WAVE-8:
//! the ORIENTATION-DUAL HODGE-⋆ / codifferential pairing's ALGEBRAIC
//! SKELETON in the 2D microsquare SCALAR reduction, pure-ring over the
//! FROZEN base, NO new substrate commitment) and MEASURE each result's
//! exact cut-free cost in OUR kernel with OUR project metric (the same
//! $a-leaf count used by sdgfloor / sdgnonabfloor / sdgspinefloor).
//!
//! Run:  cargo run --release --bin sdghodgefloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.hodge.mm.  This is ONLY the algebraic skeleton of the
//! orientation-dual ⋆ in the scalar model.  The GENUINE metric Hodge
//! ⋆ (which needs an inner product / metric tensor — ABSENT from the
//! frozen base), the INHOMOGENEOUS D⋆F=J with a source current J, the
//! action ∫tr F∧⋆F, matter, quantization are NOT built here — they
//! are the NAMED residuals, the dynamics of field theory, each
//! forcing a NEW FLAGGED metric/bilinear commitment, never faked into
//! a figure (Iron Rule).  The model-meaning floor is the UNCHANGED
//! Book-Two [PROJECTION], never re-summed.

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
    let path = "data/sdg.hodge.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.hodge.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.hodge.mm), cut-free $a-leaf count ==="
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
        "\n=== The ORIENTATION-DUAL HODGE-* SKELETON — CLOSED pure-ring (2D scalar model) ===\n  \
         eqneg (the inv-congruence supporting lemma; base has no\n  \
         eq-neg), area-antisym (the oriented 2D area 2-form is\n  \
         ANTISYMMETRIC — * reverses orientation WITH a sign),\n  \
         starstar (**=+id, the 2D Euclidean (-1)^k(n-k)=+1\n  \
         involution), star-lin (* is scalar-linear: the field\n  \
         coefficient pulls through the orientation sign), codiff-dual\n  \
         (grad*F=0, the coclosed ORIENTATION-DUAL of the source-free\n  \
         differential Bianchi grad F=0 — the EXACT bianchi2-cyclic\n  \
         construction with the area element dualised).  PURE RING,\n  \
         nothing classical, NO new substrate commitment, over the\n  \
         UNCHANGED frozen base.  THIS IS ONLY THE ALGEBRAIC SKELETON\n  \
         of the orientation-dual * in the scalar model — NOT a GENUINE\n  \
         metric Hodge *: a real * needs an INNER PRODUCT / metric\n  \
         tensor g; the frozen base has NO inner product, NO metric, NO\n  \
         <.,.>.  THE NAMED RESIDUALS (not papered): the genuine metric\n  \
         * in dim>2, the INHOMOGENEOUS (dynamical) D*F=J with a SOURCE\n  \
         current J, the action int tr F^*F, matter, quantization —\n  \
         each forcing a NEW FLAGGED metric/bilinear commitment NOT in\n  \
         the frozen ring (the dynamics of field theory, not its\n  \
         kinematic skeleton).  The model-meaning floor is the\n  \
         UNCHANGED Book-Two [PROJECTION], never re-summed.\n  \
         [orientation-dual * skeleton CLOSED pure-ring; the genuine\n  \
         metric/dynamical content NAMED, not faked]"
    );
}
