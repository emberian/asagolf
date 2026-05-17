//! sdggaugecovfloor — kernel-verify data/sdg.gaugecov.mm (BOOK-3
//! WAVE-3: the `gauge.fstr` boundary DISCHARGED) and MEASURE each
//! result's exact cut-free cost in OUR kernel with OUR project metric
//! (the same $a-leaf count used by sdgfloor / sdggaugefloor /
//! sdgbianchi2floor / euclidfloor / qzffloor).
//!
//! Run:  cargo run --release --bin sdggaugecovfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.gaugecov.mm.  The model-meaning floor (that this synthetic
//! gauge-covariance IS physical gauge theory) is the UNCHANGED
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
    let path = "data/sdg.gaugecov.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.gaugecov.mm");
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
        "\n=== MEASURED in OUR kernel (data/sdg.gaugecov.mm), cut-free $a-leaf count ==="
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
        "\n=== gauge.fstr boundary — DISCHARGED (the conn.hol->seam-free upgrade, one domain over) ===\n  \
         data/sdg.gauge.mm folded F's genuine value + FULL gauge-\n  \
         covariance into ONE opaque composite boundary $e (gauge.fstr) =\n  \
         the inseparable (a) ap-Leibniz + (b) full curvature generator\n  \
         (SEQUEL_SCOPE §5n).  Here BOTH halves are GENUINELY CONSUMED,\n  \
         NOT carried inert: sdg-gaugecov-fstr is the seam-free curvature\n  \
         construction on the gauge potential A (consumes ax-microcancel\n  \
         + ax-gen — the (b)-half, the wave-1 conn.hol retirement one\n  \
         domain over); sdg-gaugecov-aprot consumes the flagged eq-ap\n  \
         (the (a)-half, the §5j sdg-calc2-apflow pattern); sdg-gaugecov-\n  \
         covariant is the PURE-RING conjugation swap F'=g.F.g^-1 for the\n  \
         genuine field strength.  NO inert composite gauge.fstr $e\n  \
         survives — sdggaugecovpure asserts this hard-fail.  The full\n  \
         non-abelian holonomy beyond BOOK3_SCOPE §2's commutative\n  \
         scalar-line reduction stays the named residual (CITED, not\n  \
         new).  That this synthetic gauge-covariance IS physical gauge\n  \
         theory rests on the UNCHANGED Book-Two well-adapted-topos model\n  \
         floor — a labelled [PROJECTION], never re-summed.  [PROJECTION\n  \
         named, not measured]"
    );
}
