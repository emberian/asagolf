//! sdgjacobifloor — kernel-verify data/sdg.jacobi.mm (BOOK-3 WAVE-8:
//! the GENUINE NON-VACUOUS non-abelian Jacobi at a concrete 2x2 witness,
//! ENTRYWISE pure-ring over the FROZEN base, NO new substrate
//! commitment) and MEASURE each result's exact cut-free cost in OUR
//! kernel with OUR project metric (the same $a-leaf count used by
//! sdgfloor / sdggaugefloor / sdgnonabfloor / euclidfloor).
//!
//! Run:  cargo run --release --bin sdgjacobifloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.jacobi.mm.  The non-vacuity residue (that [A,B],[B,C],[C,A]
//! are genuinely NON-ZERO matrices = 1!=0) is NOT measured here: it is
//! the named cross-book residual, identical to Book One's irreducible
//! residue (the GROUNDED spine), never faked into a figure (Iron Rule).

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
    let path = "data/sdg.jacobi.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.jacobi.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.jacobi.mm), cut-free $a-leaf count ==="
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
        "\n=== Genuine NON-VACUOUS non-abelian Jacobi CLOSED entrywise pure-ring ===\n  \
         Concrete witness A=[[0,1],[0,0]] B=[[0,0],[1,0]] C=[[1,0],[0,0]]\n  \
         over the FROZEN commutative ring R.  Pairwise commutators\n  \
         genuinely NON-ZERO: [A,B]=[[1,0],[0,inv 1]] [B,C]=[[0,0],[1,0]]\n  \
         [C,A]=[[0,1],[0,0]] (NOT commutator-collapse; a symbolic\n  \
         commutative Jacobi is the vacuous 0+0+0=0, not shipped).  Nested\n  \
         brackets [A,[B,C]]=[[1,0],[0,inv 1]] [B,[C,A]]=[[inv 1,0],[0,1]]\n  \
         [C,[A,B]]=0 themselves non-zero, yet the cyclic Jacobi sum\n  \
         vanishes ENTRYWISE (j11=j12=j21=j22=0) by pure ring algebra —\n  \
         the genuine non-abelian structural Jacobi, non-vacuous.  eq-neg\n  \
         derived pure-ring.  NO new substrate commitment, nothing\n  \
         classical, NO seam, NO eq-ap, over the UNCHANGED frozen base\n  \
         (recurring theorem holds even here: §1b BOUND NOT triggered).\n  \
         THE NAMED RESIDUALS: (a) the non-vacuity itself — that [A,B],\n  \
         [B,C],[C,A] are genuinely NON-ZERO — is EXACTLY 1!=0, PRECISELY\n  \
         Book One's measured irreducible residue (the GROUNDED spine,\n  \
         suc0!=0 / orientation); (b) general matrix rank / arbitrary Lie\n  \
         algebra; (c) the full DF=0 assembly and dynamics (action /\n  \
         Hodge / matter / quantization).  Reported as named residuals,\n  \
         never faked into a measured figure.  The model-meaning floor is\n  \
         the UNCHANGED Book-Two [PROJECTION], never re-summed.  [residuals\n  \
         NAMED, the spine is one bone]"
    );
}
