//! sdgspinefloor — kernel-verify data/sdg.spine.mm (GROUNDING THE
//! CROSS-BOOK SPINE: the Book-Three segment of the wave-4 finding,
//! made a kernel-verified transport, pure-ring over the FROZEN base,
//! NO new substrate commitment) and MEASURE each result's exact
//! cut-free cost in OUR kernel with OUR project metric (the same
//! $a-leaf count used by sdgfloor / sdgnonabfloor / sdgbianchi2floor).
//!
//! Run:  cargo run --release --bin sdgspinefloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.spine.mm.  The BOOK-ONE segment (suc0!=0 ~= 1!=0) is NOT
//! re-measured here: it is already transport-anchored & set.mm-bound
//! in Book One (COST_STRUCTURE bottom), CITED and counted once at the
//! shared literal 1!=0, never re-summed / re-faked (Iron Rule;
//! transport-anchored-floor discipline).

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
    let path = "data/sdg.spine.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.spine.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.spine.mm), cut-free $a-leaf count ==="
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
        "\n=== The CROSS-BOOK SPINE — Book-Three segment GROUNDED (kernel-verified transport) ===\n  \
         Wave 4 NAMED that the non-abelian commutator witness's non-\n  \
         vacuity is EXACTLY 1!=0 = Book One's measured irreducible\n  \
         residue (suc0!=0 / orientation, COST_STRUCTURE bottom).  Here\n  \
         the BOOK-THREE SEGMENT is GROUNDED into a kernel-verified\n  \
         transport: sdg-spine-comm11 rebuilds the witness (1,1) entry\n  \
         = 1 pure-ring over the FROZEN base (sdg-spine-eqneg = the\n  \
         derived inv-congruence, base has no eq-neg); sdg-spine-b3 is\n  \
         the transport ( <[A,B]11-expr> = 0 -> 1 = 0 ) — the non-\n  \
         abelian non-vacuity reduces EXACTLY to 1!=0, MEASURED here.\n  \
         The BOOK-ONE SEGMENT (suc0!=0 ~= 1!=0, standard numeral\n  \
         interpretation) is ALREADY transport-anchored & set.mm-bound\n  \
         in Book One (COST_STRUCTURE) — CITED, joined at the identical\n  \
         literal 1!=0, counted once, NEVER re-derived / re-summed /\n  \
         re-faked here.  NET: the spine is upgraded from a narrative\n  \
         [PROJECTION] to a two-segment transport, BOTH segments\n  \
         anchored.  Claimed at exactly that weight: a structural\n  \
         identity between two MEASURED residues, never a grand\n  \
         unification.  PURE RING, nothing classical, NO new substrate\n  \
         commitment.  The model-meaning floor is the UNCHANGED Book-Two\n  \
         [PROJECTION], never re-summed.  [Book-3 segment GROUNDED;\n  \
         Book-1 segment CITED transport-anchored; bridge counted once]"
    );
}
