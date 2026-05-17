//! sdgcalc2pure — purity guard + MEASURED cost for data/sdg.calc2.mm
//! (the SEAM-FREE chain rule).  Mirrors sdgcalcpure/sdgcalcfloor.
//!
//! Three checks, all must pass:
//!   1. NAME blacklist on every logical $a (incl. the new eq-ap).
//!   2. SHAPE scan: every $a statement vs classical templates.
//!   3. Per-$p consumed-axiom closure: none classical.
//! PLUS an adversarial assertion specific to this keystone:
//!   * sdg-calc2-chain GENUINELY consumes `eq-ap` (the flagged ap-cong
//!     axiom) — if it did not, the seam-free claim would be a lie.
//!   * sdg-calc2-chain does NOT consume `ax-microcancel` (still pointwise)
//!     and there is NO `chain.sub`-style ap-Leibniz $e in the corpus.
//! And the MEASURED cut-free $a-leaf cost (OUR project metric).
//!
//! Run:  cargo run --release --bin sdgcalc2pure
//! Exit 0 = genuinely intuitionistic AND eq-ap genuinely consumed.

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
    let path = "data/sdg.calc2.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.calc2.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdgcalc2pure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("sdgcalc2pure: KERNEL REJECTED — refusing to certify: {e}");
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

    println!("=== sdgcalc2pure — SEAM-FREE chain rule purity + MEASURED ===");
    println!(
        "corpus: {}  ({} statements, {} logical $a audited)",
        path,
        db.stmts.len(),
        n_ax
    );
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!("Kernel: verified all {n_p} $p in {path} \u{2714}");

    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let ax = consumed_axioms(&db, &st.label, &mut memo);
        let sz = expand(&db, &st.label, &mut sizmemo);
        let bad: Vec<&String> =
            ax.iter().filter(|a| flagged_set.contains(*a)).collect();
        let verdict = if bad.is_empty() {
            "intuitionistic".to_string()
        } else {
            format!("CLASSICAL via {bad:?}")
        };
        println!(
            "  {:<16} {:>2} axioms  {:>12} leaves (10^{:.3})  [{}]",
            st.label,
            ax.len(),
            sz.pretty(),
            sz.log10(),
            verdict
        );
    }

    // ---- adversarial keystone assertions --------------------------------
    let chain_ax = consumed_axioms(&db, "sdg-calc2-chain", &mut memo);
    let consumes_eqap = chain_ax.contains("eq-ap");
    let consumes_mc = chain_ax.contains("ax-microcancel");
    let has_chainsub = db
        .stmts
        .iter()
        .any(|s| s.kind == kernel::Kind::E && s.label == "chain.sub");

    println!("\n=== adversarial keystone assertions (kernel-authoritative) ===");
    println!(
        "  sdg-calc2-chain consumes eq-ap (flagged ap-cong)  : {}",
        if consumes_eqap { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    println!(
        "  sdg-calc2-chain consumes ax-microcancel           : {}  (must be NO — pointwise)",
        if consumes_mc { "YES \u{2717}" } else { "NO \u{2714}" }
    );
    println!(
        "  corpus contains a `chain.sub` ap-Leibniz $e       : {}  (must be NO — discharged)",
        if has_chainsub { "YES \u{2717}" } else { "NO \u{2714}" }
    );

    let mut hard_fail = false;
    if !consumes_eqap {
        eprintln!(
            "\nFATAL: sdg-calc2-chain does NOT consume eq-ap — the seam-free\n\
             claim would be vacuous/false.  Refusing to certify."
        );
        hard_fail = true;
    }
    if consumes_mc {
        eprintln!("\nFATAL: sdg-calc2-chain consumed ax-microcancel — not pointwise.");
        hard_fail = true;
    }
    if has_chainsub {
        eprintln!("\nFATAL: a chain.sub ap-Leibniz $e is still present — not seam-free.");
        hard_fail = true;
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
        "  eq-ap is a POSITIVE Horn congruence schema (no -. , no \\/): it\n  \
         matches NO classical template (LEM/Peirce/DNE/stable/decidable/\n  \
         apartness) — the structural twin of eq-pl1/2 / eq-mu1/2."
    );
    println!(
        "\nVERDICT: GENUINELY INTUITIONISTIC \u{2714}  AND seam-free chain rule\n         \
         genuinely consumes the flagged eq-ap (no chain.sub $e, no\n         \
         microcancellation).  The substrate GAINED ONE NAMED AXIOM\n         \
         (eq-ap); ap-congruence is a NEW intuitionistic substrate axiom\n         \
         (verdict B), NOT a derived rule — stated plainly."
    );
    std::process::exit(0);
}
