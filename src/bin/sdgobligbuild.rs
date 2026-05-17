//! sdgobligbuild — emit a SELF-CONTAINED, kernel-verified corpus
//! data/sdg.oblig.mm whose theorem `sdg-oblig-sqz` is exactly
//! Obligation O's target literal proof
//!
//!     ( ( x * x ) = 0 )  |-  x = 0          (hypothesis form)
//!
//! (Frontier C "Open Obligation O" / COST_STRUCTURE Closure 2 — the
//! order / "no nonzero nilpotents" residue) so its exact cut-free
//! $a-leaf cost can be MEASURED by src/bin/sdgobligfloor.rs.
//!
//! Run:  cargo run --release --bin sdgobligbuild
//!
//! HOW IT IS BUILT (no hand-authored proof; deterministic, total):
//!   * Source = the EXISTING kernel-verified canonical corpus
//!     data/grounded.out.mm (read-only).  Its `sqz` is exactly the
//!     project's standard-signature proof of `(u*u)=0 |- u=0`.
//!   * We strip the source's comments and token-rename EVERY defined
//!     label (every $a/$p/$e/$f label, and every proof-step reference
//!     to one) with the `sdg-oblig-` prefix.  Math symbols ($c/$v) and
//!     Metamath keywords are left untouched.  Ordering is preserved
//!     verbatim, so dependency order is exactly the source's — the
//!     emitted file kernel-verifies iff the source does.
//!   * Result: a corpus self-contained over its OWN signature, which
//!     is exactly the FROZEN data/sdg.base.mm ring signature
//!     ( + * 0 1 inv = , and the intuitionistic-shaped -> -. /\ \/ )
//!     EXTENDED by the standard order predicate `<_`/`<` and the
//!     classical order axioms that the residue PROVABLY requires
//!     (Frontier C's theorem: the literal is NOT ring-derivable —
//!     that absence is the whole point).  Zero label-collision with
//!     any data/sdg.*.mm by construction (every label is prefixed).
//!   * This is a PROOF-COMPLEXITY MEASUREMENT corpus, NOT the
//!     intuitionistic SDG substrate.  It is deliberately NOT guarded
//!     by sdgpure and may use classical ax-3: Obligation O is about
//!     the cut-free SIZE of the standard order residue.
//!     data/sdg.base.mm, every other data/sdg.*.mm, the kernel and
//!     every ledger are UNTOUCHED.
//!   * Kernel-verified IN THIS PROCESS before write.  If it does not
//!     verify, nothing is written.

#[path = "../kernel.rs"]
mod kernel;

use std::collections::BTreeSet;

const SRC: &str = "data/grounded.out.mm";
const OUT: &str = "data/sdg.oblig.mm";
const PREFIX: &str = "sdg-oblig-";

fn main() {
    let raw = std::fs::read_to_string(SRC).expect("read data/grounded.out.mm");

    // ---- tokenize, dropping $( ... $) comments ----------------------
    let mut toks: Vec<String> = Vec::new();
    {
        let all: Vec<&str> = raw.split_whitespace().collect();
        let mut i = 0;
        while i < all.len() {
            if all[i] == "$(" {
                while i < all.len() && all[i] != "$)" {
                    i += 1;
                }
                i += 1; // consume $)
            } else {
                toks.push(all[i].to_string());
                i += 1;
            }
        }
    }

    // ---- collect every DEFINED label --------------------------------
    // A label is the token immediately preceding $f/$e/$a/$p.
    let mut labels: BTreeSet<String> = BTreeSet::new();
    for w in toks.windows(2) {
        if matches!(w[1].as_str(), "$f" | "$e" | "$a" | "$p") {
            labels.insert(w[0].clone());
        }
    }
    assert!(
        labels.contains("sqz"),
        "source missing `sqz` — wrong corpus"
    );

    // ---- emit with uniform prefix-rename ----------------------------
    // Rename a token iff it is a defined label.  $c/$v math symbols and
    // Metamath keywords are never in `labels`, so are untouched.
    let mut out = String::new();
    out.push_str(
        "$( ============================================================================\n",
    );
    out.push_str("   data/sdg.oblig.mm  —  MEASURED UPPER BOUND for Obligation O.\n\n");
    out.push_str("   Obligation O (Frontier C / COST_STRUCTURE Closure 2): the exact\n");
    out.push_str("   cut-free $a-leaf cost of the order / \"no nonzero nilpotents\"\n");
    out.push_str("   residue   ( ( x * x ) = 0  ->  x = 0 ).\n\n");
    out.push_str("   `sdg-oblig-sqz` is exactly the project's canonical kernel-verified\n");
    out.push_str("   proof of  (x*x)=0 |- x=0  (hypothesis form), renamed from\n");
    out.push_str("   data/grounded.out.mm by a total `sdg-oblig-` prefix on every\n");
    out.push_str("   defined label.  Its $a-leaf count, MEASURED by\n");
    out.push_str("   src/bin/sdgobligfloor.rs, is an UPPER bound — NOT a lower bound.\n");
    out.push_str("   The exact-constant LOWER bound is the OPEN part of Obligation O\n");
    out.push_str("   (minimal-DAG / smallest-grammar compression is NP-hard, SEAM2).\n\n");
    out.push_str("   Self-contained over its own signature = the FROZEN\n");
    out.push_str("   data/sdg.base.mm ring signature ( + * 0 1 inv = ) EXTENDED by the\n");
    out.push_str("   standard order predicate and the classical order axioms the\n");
    out.push_str("   residue PROVABLY requires (Frontier C: it is NOT ring-derivable —\n");
    out.push_str("   that absence is the theorem).  A PROOF-COMPLEXITY MEASUREMENT\n");
    out.push_str("   corpus, NOT the intuitionistic substrate: not sdgpure-guarded,\n");
    out.push_str("   may use classical ax-3.  data/sdg.base.mm / every data/sdg.*.mm /\n");
    out.push_str("   kernel / ledgers UNTOUCHED.  Emitted by src/bin/sdgobligbuild.rs;\n");
    out.push_str("   kernel-verified before write.  Zero label collision (all renamed).\n");
    out.push_str(
        "   ============================================================================ $)\n\n",
    );

    let mut col = 0usize;
    for t in &toks {
        let emit = if labels.contains(t) {
            format!("{PREFIX}{t}")
        } else {
            t.clone()
        };
        if col > 0 {
            out.push(' ');
            col += 1;
        }
        out.push_str(&emit);
        col += emit.len();
        if t == "$." || t == "$}" {
            out.push('\n');
            col = 0;
        }
    }
    if col > 0 {
        out.push('\n');
    }

    // ---- verify in-process before writing ---------------------------
    let db = match kernel::Db::parse(&out) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("BUILD ABORTED — generated corpus does not parse: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("BUILD ABORTED — kernel rejected generated corpus: {e}");
        std::process::exit(1);
    }
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    if db.get(&format!("{PREFIX}sqz")).is_none() {
        eprintln!("BUILD ABORTED — target {PREFIX}sqz missing");
        std::process::exit(1);
    }

    std::fs::write(OUT, &out).expect("write data/sdg.oblig.mm");
    println!(
        "wrote {OUT}: {} statements, {n_p} $p, {} defined labels, kernel-verified \u{2714}",
        db.stmts.len(),
        labels.len()
    );
    println!("target present: {PREFIX}sqz  (proves (x*x)=0 |- x=0 — Obligation O's literal)");
    println!("now run:  cargo run --release --bin sdgobligfloor");
}
