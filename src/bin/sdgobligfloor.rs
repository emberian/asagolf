//! sdgobligfloor — MEASURE the cut-free $a-leaf cost of the proofs of
//! Obligation O's target literal `( x * x ) = 0 -> x = 0` (the order /
//! "no nonzero nilpotents" residue, COST_STRUCTURE Closure 2 / Frontier
//! C Open Obligation O).
//!
//! Run:  cargo run --release --bin sdgobligfloor
//!
//! This binary measures TWO things with OUR kernel and OUR project
//! metric (the exact $a-leaf count used by sdgfloor / euclidfloor /
//! grounded.rs::expand : $f/$e = 0, $a = 1, $p = sum-of-steps with the
//! proof DAG fully tree-inlined — NO sharing in the count):
//!
//!   (1) The EXISTING canonical figure: the kernel-verified $p `sqz`
//!       (and its sub-lemmas `sqzhalf`, `subeq0`) in data/grounded.out.mm
//!       — `sqz` proves exactly `(u*u)=0 |- u=0`, i.e. Obligation O's
//!       target literal, over the project's standard ordered-field +
//!       order signature.  Read-only; this binary does not modify or
//!       re-emit grounded.out.mm.
//!
//!   (2) A fresh, self-contained minimal corpus data/sdg.oblig.mm over
//!       the FROZEN data/sdg.base.mm signature, in which the literal is
//!       proved cut-free from the standard order axioms (it is NOT
//!       provable from the ring base alone — that ABSENCE is exactly
//!       Frontier C's theorem and the whole point of the residue).
//!
//! NEITHER number is a lower bound.  The exact-constant lower bound is
//! the OPEN part of Obligation O (smallest-grammar / minimal-DAG is
//! NP-hard; SEAM2).  The measured numbers below are UPPER bounds only.

#[path = "../kernel.rs"]
mod kernel;
#[path = "../number.rs"]
mod number;

use number::ProofSize;
use std::collections::HashMap;

/// The project cut-free $a-leaf metric, identical to grounded.rs::expand
/// and sdgnonabfloor.rs::expand : $f/$e contribute 0, $a contributes 1,
/// $p is the SUM of its proof steps with the DAG fully tree-inlined
/// (memo holds the per-label inlined total, NOT a shared-count).
fn expand(db: &kernel::Db, label: &str, memo: &mut HashMap<String, ProofSize>) -> ProofSize {
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

fn measure(path: &str, targets: &[&str]) {
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("  [skip] cannot read {path}: {e}");
            return;
        }
    };
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("PARSE ERROR ({path}): {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("KERNEL REJECTED ({path}): {e}");
        std::process::exit(1);
    }
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!(
        "Kernel: verified all {n_p} $p in {path} \u{2714}  ({} statements)",
        db.stmts.len()
    );
    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    for t in targets {
        match db.get(t) {
            Some(st) => {
                let sz = expand(&db, t, &mut memo);
                println!(
                    "  {:<10} {:<34} = {:>9}   (10^{:.3})",
                    t,
                    st.expr.join(" "),
                    sz.pretty(),
                    sz.log10()
                );
            }
            None => println!("  {t:<10} (not present in {path})"),
        }
    }
}

fn main() {
    println!("=== Obligation O target literal :  ( x * x ) = 0  ->  x = 0 ===");
    println!("=== MEASURED upper bounds in OUR kernel, cut-free $a-leaf metric ===\n");

    println!("(1) EXISTING canonical figure — data/grounded.out.mm (read-only):");
    println!("    `sqz` proves exactly  (u*u)=0 |- u=0  (Obligation O's literal),");
    println!("    over the project's standard ordered-field + order signature.\n");
    measure("data/grounded.out.mm", &["subeq0", "sqzhalf", "sqz"]);

    println!("\n(2) Fresh self-contained corpus — data/sdg.oblig.mm");
    println!("    (over the FROZEN data/sdg.base.mm signature; the literal is");
    println!("     proved cut-free from the standard order axioms — it is NOT");
    println!("     ring-derivable, which is Frontier C's theorem):\n");
    measure(
        "data/sdg.oblig.mm",
        &[
            "sdg-oblig-subeq0",
            "sdg-oblig-sqzhalf",
            "sdg-oblig-sqz",
        ],
    );

    println!(
        "\n=== RIGOROUSLY-PROVABLE WEAK LOWER BOUND (clearly labelled WEAK) ===\n\
         Unconditional, but trivial.  Frontier C is a THEOREM: `(x*x)=0 ->\n\
         x=0` is false in the commutative ring Z/4 (2^2=0, 2!=0), so it is\n\
         NOT a consequence of the ring axioms alone — EVERY cut-free proof\n\
         must apply >= 1 order-essential ($a) axiom (one not sound over\n\
         every commutative ring; concretely an `of-letot`/`of-lein`\n\
         instance).  Hence:\n\
            cut-free $a-leaf count  >=  1     [PROVED, unconditional]\n\
         A second, also-trivial structural bound: the proof must at minimum\n\
         introduce the hypothesis term and the goal `x = 0`, so it contains\n\
         the `weq`/`t0`/`tmu` syntax leaves of the endsequent; but those\n\
         are SYNTAX (COST_STRUCTURE's separate 94.76% bucket) and are NOT\n\
         folded into a proof-difficulty LB here (honest bucketing).  No\n\
         technique in this codebase yields any LB beyond the constant `1`;\n\
         claiming more would be the exact violation the iron rule forbids.\n\n\
         === HONEST FRAMING (COST_STRUCTURE adversarial voice) ===\n\
         These are MEASURED UPPER bounds only.  The exact-constant cut-free\n\
         LOWER bound for `( x*x )=0 -> x=0` is Frontier C's Open Obligation\n\
         O and remains OPEN: a Frege-style unconditional cut-free proof-size\n\
         lower bound for a fixed order-theoretic implication, against ALL\n\
         proofs not the one we wrote.  Minimal-DAG / smallest-grammar\n\
         compression of these very proofs is NP-hard (SEAM2), so no\n\
         efficient method in this codebase delivers the matching lower\n\
         bound.  The only RIGOROUSLY-PROVABLE lower bound is the trivial\n\
         unconditional structural one (below), explicitly labelled WEAK.\n\
         The exact constant is NOT closed; this is a sharpened restatement\n\
         + a measured upper bound.  Reported, not faked."
    );
}
