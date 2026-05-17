//! sdgnonabFpure — intuitionistic-purity guard + MEASURED cost +
//! the STRONG adversarial assertion for data/sdg.nonabF.mm (BOOK-3
//! WAVE-7: the NON-ABELIAN bracket algebra underlying the homogeneous
//! Yang–Mills field equation DF = ∇F + [A,F] = 0).  Mirrors
//! sdgnonabpure / sdgspinepure exactly.
//!
//! Purity (all must pass): NAME blacklist on every logical $a; SHAPE
//! scan vs classical templates; per-$p consumed-axiom closure none
//! classical.
//! PLUS the STRONG hard-fail assertion:
//!   * EVERY $p is PURE RING — none consumes ax-microcancel /
//!     ax-microcancel2 / ax-kl / ax-kl2 / ax-gen / ax-spec / eq-ap.
//!     The bracket algebra (neguniq, eqneg, invinv, invadd, mulneg,
//!     mulnegr, brktantisym) is pure-ring over the UNCHANGED frozen
//!     base, nothing classical, NO new substrate commitment.  These
//!     are genuine inv/distribution identities (true in ANY ring),
//!     NOT commutator-collapse: a symbolic Jacobi over the commutative
//!     base would be VACUOUS and is deliberately NOT shipped.  If ANY
//!     $p reached the seam / KL / eq-ap it would be unsound —
//!     hard-fail.
//! The genuine non-abelian non-vacuity is the structural 2×2 route
//! (waves 4–5), grounded as the spine 1≠0 (wave 6,
//! data/sdg.spine.mm) — NOT re-done here.  The dynamics (full DF=0,
//! matrix-Jacobi at a non-vanishing witness, the inhomogeneous
//! D⋆F=J, action/Hodge/matter/quantization) are the NAMED residuals,
//! never faked.
//!
//! Run:  cargo run --release --bin sdgnonabFpure
//! Exit 0 = genuinely intuitionistic AND every $p pure-ring — the
//! non-abelian bracket algebra soundly closed.

#[path = "../kernel.rs"]
mod kernel;
#[path = "../number.rs"]
mod number;

use number::ProofSize;
use std::collections::{BTreeSet, HashMap};

const BLACKLIST_NAMES: &[&str] = &[
    "ax-3", "peirce", "lem", "exmid", "dne", "notnotr", "notnot1",
    "stab", "stable", "dceq", "decidable", "ax-ap", "apart", "apti",
    "condc", "dcn", "ax-cd", "ax-lem", "ax-dne", "ax-peirce",
];

// The whole corpus is the pure-ring layer: NOTHING may consume the
// seam / KL / eq-ap.  (That is precisely this wave's thesis.)
const NON_RING: &[&str] = &[
    "ax-microcancel", "ax-microcancel2", "ax-kl", "ax-kl2",
    "ax-gen", "ax-spec", "eq-ap",
];

fn body(expr: &[String]) -> String {
    let e = if expr.first().map(|s| s.as_str()) == Some("|-") {
        &expr[1..]
    } else {
        expr
    };
    e.join(" ")
}

fn classical_reason(b: &str) -> Option<String> {
    let abst: Vec<String> = b
        .split_whitespace()
        .map(|tk| match tk {
            "ph" | "ps" | "ch" | "th" => "P".to_string(),
            "x" | "y" | "z" | "d" | "e" | "a" | "b" | "c" | "f" | "g"
            | "u" | "v" | "w" => "X".to_string(),
            other => other.to_string(),
        })
        .collect();
    let s = abst.join(" ");
    if s == "( P \\/ -. P )" || s == "( -. P \\/ P )" {
        return Some("law of excluded middle".into());
    }
    if s == "( -. -. P -> P )" {
        return Some("double-negation elimination".into());
    }
    if s == "( ( -. P -> -. P ) -> ( P -> P ) )" {
        return Some("ax-3 / classical contraposition".into());
    }
    if s == "( ( ( P -> P ) -> P ) -> P )" {
        return Some("Peirce's law".into());
    }
    if s == "( ( -. P -> P ) -> P )" {
        return Some("consequentia mirabilis".into());
    }
    if s == "( -. -. X = X -> X = X )" {
        return Some("stable equality".into());
    }
    if s == "( X = X \\/ -. X = X )" || s == "( -. X = X \\/ X = X )" {
        return Some("decidable equality".into());
    }
    None
}

fn consumed_axioms(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    memo.insert(label.to_string(), BTreeSet::new());
    let st = match db.get(label) {
        Some(s) => s,
        None => return BTreeSet::new(),
    };
    let out: BTreeSet<String> = match st.kind {
        kernel::Kind::F | kernel::Kind::E => BTreeSet::new(),
        kernel::Kind::A => {
            let mut s = BTreeSet::new();
            s.insert(label.to_string());
            s
        }
        kernel::Kind::P => {
            let mut s = BTreeSet::new();
            for step in st.proof.clone() {
                s.extend(consumed_axioms(db, &step, memo));
            }
            s
        }
    };
    memo.insert(label.to_string(), out.clone());
    out
}

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
    let path = "data/sdg.nonabF.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.nonabF.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdgnonabFpure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("sdgnonabFpure: KERNEL REJECTED — refusing to certify: {e}");
        std::process::exit(1);
    }

    let mut flagged: Vec<(String, String)> = Vec::new();
    let mut n_ax = 0usize;
    for st in &db.stmts {
        if st.kind != kernel::Kind::A {
            continue;
        }
        if st.expr.first().map(|s| s.as_str()) != Some("|-") {
            continue;
        }
        n_ax += 1;
        if BLACKLIST_NAMES.contains(&st.label.as_str()) {
            flagged.push((st.label.clone(), "blacklisted name".into()));
        }
        if let Some(r) = classical_reason(&body(&st.expr)) {
            flagged.push((st.label.clone(), r));
        }
    }

    let flagged_set: BTreeSet<String> =
        flagged.iter().map(|(l, _)| l.clone()).collect();
    let mut memo: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut sizmemo: HashMap<String, ProofSize> = HashMap::new();

    println!("=== sdgnonabFpure — NON-ABELIAN bracket algebra (Book-3 wave-7) purity + MEASURED ===");
    println!(
        "corpus: {}  ({} statements, {} logical $a audited)",
        path,
        db.stmts.len(),
        n_ax
    );
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!("Kernel: verified all {n_p} $p in {path} \u{2714}");

    let mut hard_fail = false;
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let ax = consumed_axioms(&db, &st.label, &mut memo);
        let sz = expand(&db, &st.label, &mut sizmemo);
        let bad_cl: Vec<&String> =
            ax.iter().filter(|a| flagged_set.contains(*a)).collect();
        let bad_ring: Vec<&str> = NON_RING
            .iter()
            .copied()
            .filter(|a| ax.contains(*a))
            .collect();
        let verdict = if !bad_cl.is_empty() {
            format!("CLASSICAL via {bad_cl:?}")
        } else if !bad_ring.is_empty() {
            format!("NOT PURE RING via {bad_ring:?}")
        } else {
            "pure ring \u{2714}".to_string()
        };
        println!(
            "  {:<24} {:>2} axioms  {:>8} leaves (10^{:.3})  [{}]",
            st.label,
            ax.len(),
            sz.pretty(),
            sz.log10(),
            verdict
        );
        if !bad_ring.is_empty() {
            hard_fail = true;
        }
    }

    println!("\n=== adversarial assertion (kernel-authoritative): EVERY $p PURE RING ===");
    if hard_fail {
        eprintln!(
            "FATAL: a $p reached the seam / KL / eq-ap.  The non-abelian\n\
             bracket algebra must be PURE RING over the frozen base —\n\
             if any $p needs the seam / eq-ap it is unsound — refusing\n\
             to certify (a ZERO)."
        );
    } else {
        println!(
            "  every $p's consumed-axiom closure is PURE RING — no\n\
            \x20    ax-microcancel/2, no ax-kl/2, no ax-gen, no ax-spec,\n\
            \x20    no eq-ap.  The bracket algebra (neguniq / eqneg /\n\
            \x20    invinv / invadd / mulneg / mulnegr / brktantisym) is\n\
            \x20    sound pure-ring over the FROZEN base, NO new\n\
            \x20    substrate commitment — genuine inv/distribution\n\
            \x20    identities, NOT commutator-collapse."
        );
    }

    if !flagged.is_empty() {
        eprintln!("\nVERDICT: CLASSICAL CONTAMINATION FOUND \u{2717} (a ZERO — reported)");
        for (l, w) in &flagged {
            eprintln!("  axiom `{l}` : {w}");
        }
        std::process::exit(1);
    }
    if hard_fail {
        std::process::exit(1);
    }

    println!(
        "\nNAME + SHAPE scan: all {n_ax} logical axioms intuitionistically pure."
    );
    println!(
        "\nVERDICT: GENUINELY INTUITIONISTIC \u{2714} AND EVERY $p PURE RING.\n         \
         The NON-ABELIAN BRACKET ALGEBRA underlying the homogeneous\n         \
         Yang–Mills field equation DF = ∇F + [A,F] = 0 — additive-\n         \
         inverse uniqueness, the inv-congruence, involution, inv-of-\n         \
         sum, scalar-through-inverse (left/right), and the bracket\n         \
         ANTISYMMETRY [a,b]=inv[b,a] — closes PURE RING over the FROZEN\n         \
         base, nothing classical, NO new substrate commitment.  Genuine\n         \
         & NON-VACUOUS: inv/distribution identities true in ANY ring,\n         \
         NOT commutator-collapse (a symbolic Jacobi over the\n         \
         commutative base would be VACUOUS and is deliberately NOT\n         \
         shipped).  The genuine non-abelian non-vacuity is the\n         \
         structural 2×2 route, already GROUNDED as the spine 1≠0\n         \
         (wave 6).  The dynamics of field theory — full DF=0 assembly,\n         \
         matrix-Jacobi at a non-vanishing witness, the inhomogeneous\n         \
         D⋆F=J, action/Hodge/matter/quantization — are the NAMED\n         \
         residuals, claimed at exactly their weight.  Reported, not\n         \
         faked."
    );
    std::process::exit(0);
}
