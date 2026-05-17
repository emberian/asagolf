//! sdgtayfloor — kernel-verify data/sdg.taylor.mm (the SYNTHETIC ORDER-2
//! TAYLOR corpus) and MEASURE each theorem's exact cut-free cost in OUR
//! kernel with OUR project metric (the same $a-leaf count used by
//! sdgfloor / sdgcalcfloor / euclidfloor).
//!
//! Run:  cargo run --release --bin sdgtayfloor
//!
//! Every MEASURED line is produced here from OUR kernel over
//! data/sdg.taylor.mm.  EXISTENCE of the order-2 Taylor expansion is
//! exactly ax-kl2 (an axiom, CITED — never measured as content; restating
//! it as a one-line $p would be vacuous).  Model-grounding (a well-adapted
//! topos in which D_2 is non-degenerate and KL2 holds) is the separate
//! PROJECTION, never summed into a measured figure (Iron Rule).

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
    let path = "data/sdg.taylor.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.taylor.mm");
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
        "Kernel: verified all {n_p} $p in {} OK  (db: {} statements)",
        path,
        db.stmts.len()
    );

    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    println!(
        "\n=== MEASURED in OUR kernel (data/sdg.taylor.mm), cut-free $a-leaf count ==="
    );
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let sz = expand(&db, &st.label, &mut memo);
        println!(
            "  {:<24} = {:>16}   (10^{:.3})",
            st.label,
            sz.pretty(),
            sz.log10()
        );
    }

    println!("\n=== ORDER-2 TAYLOR — headline MEASURED costs ===");
    for r in ["sdg-tay-quad-slope", "sdg-tay-deriv2"] {
        if let Some(s) = db.get(r) {
            if s.kind == kernel::Kind::P {
                let sz = expand(&db, r, &mut memo);
                println!(
                    "  >>> {:<22} = {}  (10^{:.3})  [MEASURED]",
                    r,
                    sz.pretty(),
                    sz.log10()
                );
            }
        }
    }

    println!(
        "\n=== EXISTENCE + the general meta-k Taylor scheme — CITED / SCHEME ===\n  \
         EXISTENCE of the order-2 expansion f(x+d)=f(x)+d*f'(x)+(d*d)*s(x)\n  \
         on D_2 is *exactly* ax-kl2 (a substrate axiom).  Restating it as\n  \
         a one-line $p would be vacuous, so it is CITED, not re-derived\n  \
         and never measured as content (same discipline as ax-kl for the\n  \
         order-1 derivative).  The forall-k Taylor formula is an axiom\n  \
         SCHEME (the substrate has no internal natural-number object): one\n  \
         axiom per meta-level k, k=1 = the existing order-1 derivative\n  \
         (sdg-tay-k1-reduce records this), k=2 = ax-kl2 + ax-microcancel2,\n  \
         delivered here.  Model-grounding (a well-adapted topos with D_2\n  \
         non-degenerate and KL2) is the separate [PROJECTION], never\n  \
         summed.  sdg-tay-deriv2 GENUINELY consumes ax-microcancel2 (see\n  \
         sdgtaypure's per-theorem consumed-axiom closure)."
    );
}
