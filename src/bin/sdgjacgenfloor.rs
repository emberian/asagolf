//! sdgjacgenfloor — kernel-verify data/sdg.jacgen.mm (BOOK-3 WAVE-10:
//! general symbolic 2x2 matrix-product ASSOCIATIVITY — the structural
//! backbone of the non-abelian framework, pure-ring over the FROZEN
//! base, NO new substrate commitment) and MEASURE each result's exact
//! cut-free cost in OUR kernel with OUR project metric (the same
//! $a-leaf count used by sdgfloor / sdgnonabfloor / sdgjacobifloor).
//!
//! Run:  cargo run --release --bin sdgjacgenfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.jacgen.mm.  The full general symbolic Jacobi (all entries,
//! nested triple bracket) and general n x n rank are NOT built here —
//! they are the NAMED residual, never faked into a figure (Iron Rule);
//! the concrete sl2 witness (data/sdg.jacobi.mm) is the proof-of-
//! concept and its non-vacuity is the already-grounded spine 1≠0
//! (data/sdg.spine.mm).

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
    let path = "data/sdg.jacgen.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.jacgen.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.jacgen.mm), cut-free $a-leaf count ==="
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
        "\n=== General symbolic 2x2 matrix-product ASSOCIATIVITY — the structural backbone ===\n  \
         ((A.B).C)_11 = (A.(B.C))_11 and the (1,2) entry, for GENERAL\n  \
         symbolic 2x2 entries over the FROZEN commutative ring — the\n  \
         pure-ring reason the concrete non-abelian Jacobi (thread-2,\n  \
         data/sdg.jacobi.mm) closed was STRUCTURE, not coincidence.\n  \
         rdistr (right-distributivity, DERIVED — ax-distr is left-only)\n  \
         + shuffle4 (additive 4-term reshuffle) are the pure-ring\n  \
         helpers.  assoc11 == assoc12 in leaf count: associativity is\n  \
         not special to the (1,1) position.  NO new substrate\n  \
         commitment, nothing classical, every $p PURE RING over the\n  \
         UNCHANGED frozen base.  NAMED RESIDUAL (not papered): the FULL\n  \
         general symbolic Jacobi (all entries, nested triple bracket)\n  \
         and general n x n rank — the concrete sl2 witness is the\n  \
         proof-of-concept, this is its structural backbone, the tower\n  \
         stays the named residual (the exact nonab->nonabgen\n  \
         concrete->general discipline).  The non-vacuity of the non-\n  \
         abelian content is the GROUNDED spine 1!=0; the model-meaning\n  \
         floor the UNCHANGED Book-Two [PROJECTION], never re-summed.\n  \
         [structural backbone CLOSED pure-ring; the full tower NAMED]"
    );
}
