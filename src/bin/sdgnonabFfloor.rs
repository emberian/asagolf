//! sdgnonabFfloor — kernel-verify data/sdg.nonabF.mm (BOOK-3 WAVE-7:
//! the NON-ABELIAN bracket algebra underlying the homogeneous
//! Yang–Mills field equation DF = ∇F + [A,F] = 0, pure-ring over the
//! FROZEN base, NO new substrate commitment) and MEASURE each result's
//! exact cut-free cost in OUR kernel with OUR project metric (the same
//! $a-leaf count used by sdgfloor / sdgnonabfloor / sdgspinefloor).
//!
//! Run:  cargo run --release --bin sdgnonabFfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.nonabF.mm.  The dynamics of field theory (the full DF=0
//! assembly, the matrix-Jacobi at a non-vanishing witness, the
//! inhomogeneous D⋆F=J, action/Hodge/matter/quantization) are NOT
//! built here — they are the NAMED residuals, never faked into a
//! figure (Iron Rule); the genuine non-abelian non-vacuity is the
//! already-grounded spine 1≠0 (data/sdg.spine.mm).

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
    let path = "data/sdg.nonabF.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.nonabF.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.nonabF.mm), cut-free $a-leaf count ==="
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
        "\n=== The NON-ABELIAN bracket algebra — CLOSED pure-ring (the toolkit of DF=gradF+[A,F]=0) ===\n  \
         neguniq (additive-inverse uniqueness, deduction form), eqneg\n  \
         (the inv-congruence, base has no eq-neg), invinv (involution),\n  \
         invadd, mulneg / mulnegr (scalar through the additive inverse),\n  \
         brktantisym (the bracket is ANTISYMMETRIC: [a,b]=inv[b,a]).\n  \
         GENUINE & NON-VACUOUS: inv/distribution identities true in ANY\n  \
         ring, NOT commutator-collapse — over the commutative base every\n  \
         symbolic [x,y] is 0, so a symbolic Jacobi would be VACUOUS and\n  \
         is deliberately NOT shipped.  The genuine non-abelian non-\n  \
         vacuity is the structural 2x2 route (waves 4-5), grounded as\n  \
         the spine 1!=0 (wave 6, data/sdg.spine.mm).  NO new substrate\n  \
         commitment, nothing classical, pure-ring over the UNCHANGED\n  \
         frozen base.  THE NAMED RESIDUALS (not papered): the full DF=0\n  \
         assembly, the matrix-level Jacobi at a non-vanishing witness,\n  \
         the inhomogeneous (dynamical) D*F=J, and action / Hodge /\n  \
         matter / quantization — the dynamics of field theory, not its\n  \
         kinematic skeleton.  The model-meaning floor is the UNCHANGED\n  \
         Book-Two [PROJECTION], never re-summed.  [bracket algebra\n  \
         CLOSED pure-ring; the dynamics NAMED, not faked]"
    );
}
