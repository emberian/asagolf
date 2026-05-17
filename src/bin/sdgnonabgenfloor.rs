//! sdgnonabgenfloor — kernel-verify data/sdg.nonabgen.mm (BOOK-3
//! WAVE-5: the GENERAL STRUCTURAL non-commutation theorem, pure-ring
//! over the FROZEN base, NO new substrate commitment) and MEASURE each
//! result's exact cut-free cost in OUR kernel with OUR project metric
//! (the same $a-leaf count used by sdgfloor / sdgnonabfloor /
//! sdggaugefloor / sdgbianchi2floor / euclidfloor).
//!
//! Run:  cargo run --release --bin sdgnonabgenfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.nonabgen.mm.  The GENERAL theorem is a pure-ring identity
//! and needs NO 1!=0; wave-4's concrete-witness non-vacuity residue
//! (= Book One's irreducible residue, COST_STRUCTURE bottom) is
//! UNCHANGED, NOT a hypothesis here, never faked into a figure (Iron
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
    let path = "data/sdg.nonabgen.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.nonabgen.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.nonabgen.mm), cut-free $a-leaf count ==="
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
        "\n=== GENERAL structural non-commutation CLOSED pure-ring ===\n  \
         General 2x2 matrices over the FROZEN commutative ring R with\n  \
         symbolic entries A=[[a,b],[c,_]] B=[[p,q],[r,_]] (p:=x, q:=y,\n  \
         r:=z).  (A.B)_11=((a*x)+(b*z)), (B.A)_11=((x*a)+(y*c)); the\n  \
         GENERAL non-commutation theorem sdg-nonabgen-mixcancel:\n  \
         ( (A.B)_11 + inv (B.A)_11 ) reduces PURE-RING to\n  \
         ( (b*z) + inv (y*c) ) — the a*x/x*a symmetric (commuting)\n  \
         parts cancel EXACTLY by ax-mulcom+ax-addneg\n  \
         (sdg-nonabgen-symvanish).  This is the GENERAL statement of\n  \
         which wave-4's concrete witness was the instance.  NO new\n  \
         substrate commitment, nothing classical, NO seam, NO eq-ap —\n  \
         a pure-ring identity over the UNCHANGED frozen base (the\n  \
         recurring theorem holds even here: §1b BOUND NOT triggered).\n  \
         1!=0 IS NOT NEEDED to state or prove the general theorem (it\n  \
         is true in EVERY commutative ring, even the trivial one);\n  \
         1!=0 was ONLY wave-4's CONCRETE-witness non-vacuity — that\n  \
         named cross-book residual (= Book One's measured irreducible\n  \
         residue, suc0!=0 / orientation, COST_STRUCTURE bottom) is\n  \
         UNCHANGED, NOT a hypothesis here, kept distinct, never faked\n  \
         into a measured figure.  THE NAMED RESIDUAL of this wave: the\n  \
         full general-rank / n x n Yang-Mills tower (general matrix\n  \
         size, full F=dA+A^A assembly, differential Bianchi / gauge\n  \
         covariance) — this wave closes the (1,1) entry at general 2x2\n  \
         symbolic, NOT the whole tower.  The model-meaning floor is the\n  \
         UNCHANGED Book-Two [PROJECTION], never re-summed.  [residual\n  \
         NAMED; the general identity MEASURED]"
    );
}
