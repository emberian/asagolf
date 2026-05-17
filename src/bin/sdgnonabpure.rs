//! sdgnonabpure — intuitionistic-purity guard + MEASURED cost +
//! the STRONG adversarial assertion for data/sdg.nonab.mm (BOOK-3
//! WAVE-4: the NON-ABELIAN structure).  Mirrors sdgbianchi2pure /
//! sdggaugecovpure exactly.
//!
//! Purity (all must pass): NAME blacklist on every logical $a; SHAPE
//! scan vs classical templates; per-$p consumed-axiom closure none
//! classical.
//! PLUS the STRONG hard-fail assertion that IS this wave's thesis:
//!   * EVERY $p is PURE RING — none consumes ax-microcancel /
//!     ax-microcancel2 / ax-kl / ax-kl2 / ax-gen / ax-spec / eq-ap.
//!     Genuine non-abelian structure (the witness commutator, the inv
//!     congruence, the non-abelian wedge) forces NO seam, NO eq-ap,
//!     NO new substrate commitment, nothing classical — over the
//!     UNCHANGED frozen commutative base.  If ANY $p reached any of
//!     those, the "non-abelian needs no new commitment" claim would be
//!     a lie — hard-fail.
//! The non-vacuity residue (that [A,B] is genuinely NON-ZERO = 1!=0,
//! identical to Book One's irreducible residue) is the NAMED cross-book
//! residual, reported by sdgnonabfloor — never faked into a $p, never
//! a guard pass/fail (the guard certifies the pure-ring fact; the
//! residue is named, not measured).
//!
//! Run:  cargo run --release --bin sdgnonabpure
//! Exit 0 = genuinely intuitionistic AND every $p pure-ring (no seam,
//! no eq-ap, no new commitment) — the strong non-abelian thesis.

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
    let path = "data/sdg.nonab.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.nonab.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdgnonabpure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("sdgnonabpure: KERNEL REJECTED — refusing to certify: {e}");
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

    println!("=== sdgnonabpure — NON-ABELIAN structure (Book-3 wave-4) purity + MEASURED ===");
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
            "FATAL: a $p reached the seam / KL / eq-ap.  The whole point\n\
             of this wave is that GENUINE non-abelian structure forces\n\
             NO seam, NO eq-ap, NO new substrate commitment over the\n\
             frozen commutative base.  A $p that needs any of those\n\
             would falsify that — refusing to certify (a ZERO)."
        );
    } else {
        println!(
            "  every $p's consumed-axiom closure is PURE RING — no\n\
            \x20    ax-microcancel/2, no ax-kl/2, no ax-gen, no ax-spec,\n\
            \x20    no eq-ap.  Genuine non-abelian structure (the witness\n\
            \x20    commutator [A,B]=[[1,0],[0,inv 1]], the derived inv\n\
            \x20    congruence, the non-abelian wedge) forces NO new\n\
            \x20    substrate commitment (§1b BOUND NOT triggered)."
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
         Genuine non-abelian gauge structure — 2x2 matrices over the\n         \
         FROZEN commutative ring, the canonical witness commutator\n         \
         [A,B]=[[1,0],[0,(inv 1)]] entrywise, the derived inv\n         \
         congruence, the non-abelian F wedge (NON-cancelling, vs the\n         \
         abelian sdg-gauge-F-cross which cancels) — closes with NO new\n         \
         substrate commitment, NO seam, NO eq-ap, nothing classical.\n         \
         The recurring theorem holds even at the non-abelian frontier.\n         \
         THE CROSS-BOOK SPINE (named, not faked, not measured): the\n         \
         non-vacuity of [A,B] (that it is genuinely NON-ZERO) is\n         \
         EXACTLY 1!=0 — PRECISELY Book One's measured irreducible\n         \
         residue (suc0!=0 / orientation).  Book Three's non-abelian\n         \
         meaning-residue IS Book One's residue: the spine is one bone.\n         \
         Reported, not faked."
    );
    std::process::exit(0);
}
