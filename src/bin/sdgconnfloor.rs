//! sdgconnfloor — kernel-verify data/sdg.conn.mm (the SYNTHETIC
//! CONNECTION layer, the Book-3 bridge) and MEASURE each result's exact
//! cut-free cost in OUR kernel with OUR project metric (the same $a-leaf
//! count used by sdgfloor / sdgtanfloor / euclidfloor / qzffloor).
//!
//! Run:  cargo run --release --bin sdgconnfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.conn.mm.  The curvature/Bianchi globalization seam (W3-glob2
//! = Book-3's globalized bracket) is explicitly NOT in scope here; it is
//! named as the precise deferred Book-3 dependency, never summed into a
//! measured figure (Iron Rule).

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
    let path = "data/sdg.conn.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.conn.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.conn.mm), cut-free $a-leaf count ==="
    );
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<22} = {:>10}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
    }

    println!(
        "\n=== Curvature/Bianchi globalization seam — explicitly DEFERRED ===\n  \
         The cleanly-reachable structural layer (transport0, kl-affine,\n  \
         diff-tensor, torsion-sym, curv-cross) is PURE RING — no\n  \
         microcancellation, no globalization, nothing classical.\n  \
         CURVATURE carries EXACTLY ONE labelled boundary $e (conn.hol):\n  \
         composing one direction's transport into the other's argument is\n  \
         BOTH (a) ap-congruence AND (b) a globalized/generator-side\n  \
         derivative of the Christoffel symbol = W3-glob2, Book-3's\n  \
         globalized bracket.  This is the PRECISE Book-3 dependency map:\n  \
         curvature/Bianchi genuinely needs W3-glob2.  It is named as the\n  \
         deferred Book-3 keystone, never summed here.  [DEFERRED]"
    );
}
