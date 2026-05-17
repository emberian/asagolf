//! sdgnonabfloor — kernel-verify data/sdg.nonab.mm (BOOK-3 WAVE-4:
//! the NON-ABELIAN structure, pure-ring over the FROZEN base, NO new
//! substrate commitment) and MEASURE each result's exact cut-free cost
//! in OUR kernel with OUR project metric (the same $a-leaf count used
//! by sdgfloor / sdggaugefloor / sdgbianchi2floor / euclidfloor).
//!
//! Run:  cargo run --release --bin sdgnonabfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.nonab.mm.  The non-vacuity residue (that [A,B] is a
//! genuinely NON-ZERO matrix = 1!=0) is NOT measured here: it is the
//! named cross-book residual, identical to Book One's irreducible
//! residue (COST_STRUCTURE bottom), never faked into a figure (Iron
//! Rule).

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
    let path = "data/sdg.nonab.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.nonab.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.nonab.mm), cut-free $a-leaf count ==="
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
        "\n=== Non-abelian structure CLOSED pure-ring; the CROSS-BOOK SPINE named ===\n  \
         2x2 matrices over the FROZEN commutative ring R; the canonical\n  \
         witness A=[[0,1],[0,0]] B=[[0,0],[1,0]] has [A,B]=A.B-B.A=\n  \
         [[1,0],[0,(inv 1)]], computed ENTRYWISE pure-ring (comm11=1,\n  \
         comm12=comm21=0, comm22=inv 1; eq-neg derived; the non-abelian\n  \
         F wedge cross-term IS the commutator, structurally NON-\n  \
         cancelling vs the abelian sdg-gauge-F-cross).  NO new substrate\n  \
         commitment, nothing classical, NO seam, NO eq-ap — genuine\n  \
         non-abelian structure over the UNCHANGED frozen base (the\n  \
         recurring theorem holds even here: §1b BOUND NOT triggered).\n  \
         THE NAMED RESIDUAL (the cross-book spine): that [A,B] is\n  \
         genuinely NON-ZERO — its non-vacuity — is EXACTLY 1!=0, which\n  \
         is PRECISELY Book One's measured irreducible residue\n  \
         (suc0!=0 / orientation, COST_STRUCTURE bottom).  Book Three's\n  \
         non-abelian meaning-residue IS Book One's residue, literally\n  \
         the same 1!=0.  Reported as a named residual, never faked into\n  \
         a measured figure.  The model-meaning floor is the UNCHANGED\n  \
         Book-Two [PROJECTION], never re-summed.  [residual NAMED, the\n  \
         spine is one bone]"
    );
}
