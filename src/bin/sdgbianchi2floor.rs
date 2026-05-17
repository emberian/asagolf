//! sdgbianchi2floor — kernel-verify data/sdg.bianchi2.mm (the BOOK-3
//! WAVE-2 keystone: the SECOND/DIFFERENTIAL Bianchi identity ∇R = 0)
//! and MEASURE each result's exact cut-free cost in OUR kernel with OUR
//! project metric (the same $a-leaf count used by sdgfloor /
//! sdgconnfloor / sdggaugefloor / euclidfloor / qzffloor).
//!
//! Run:  cargo run --release --bin sdgbianchi2floor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.bianchi2.mm.  The model-meaning floor (that this synthetic
//! ∇R = 0 IS the physical homogeneous field equation) is the UNCHANGED
//! Book-Two well-adapted-topos [PROJECTION] — named, never summed into
//! a measured figure (Iron Rule).

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
    let path = "data/sdg.bianchi2.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.bianchi2.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.bianchi2.mm), cut-free $a-leaf count ==="
    );
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<26} = {:>10}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
    }

    println!(
        "\n=== Differential Bianchi ∇R = 0 — the §5m residual, DISCHARGED ===\n  \
         sdg-bianchi2-covd is wave-1's seam-free sdg-curvature ONE LEVEL\n  \
         UP: the curvature symbol R ( ap c · ) (a wave-1 derivative\n  \
         output) is the symbol flowed; ∇R is UNIQUELY determined,\n  \
         GENUINELY CONSUMING ax-microcancel + ax-gen one level up (the\n  \
         §5j/§5k recursion) — verified by sdgbianchi2pure's hard-fail\n  \
         adversarial assertion, NOT an inert $e.  sdg-bianchi2-cyclic is\n  \
         the PURE-RING cyclic / antisymmetric vanishing of ∇R over the\n  \
         D×D×D cube, built ON that seam-consumed uniqueness.  The non-\n  \
         abelian [A,R] term is zero by BOOK3_SCOPE §2's commutative\n  \
         scalar-line model reduction (a CITED model choice, NOT a new\n  \
         axiom).  That this synthetic ∇R = 0 IS the physical homogeneous\n  \
         field equation rests on the UNCHANGED Book-Two well-adapted-\n  \
         topos model floor — a labelled [PROJECTION], never re-summed,\n  \
         not dissolved by any better construction (the recurring theorem,\n  \
         third turn's tail).  [PROJECTION named, not measured]"
    );
}
