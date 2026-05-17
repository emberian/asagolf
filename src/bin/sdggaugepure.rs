//! sdggaugepure — intuitionistic-purity guard + MEASURED cost for
//! data/sdg.gauge.mm (the SYNTHETIC GAUGE-CONNECTION layer — the Book-3
//! target foundation).  Mirrors sdgconnpure / sdgcalc2pure / sdgtanpure
//! exactly.
//!
//! Three checks, all must pass:
//!   1. NAME blacklist on every logical $a (incl. eq-ap).
//!   2. SHAPE scan: every $a statement vs classical templates.
//!   3. Per-$p consumed-axiom closure: none classical.
//! PLUS adversarial assertions specific to this Book-3 foundation:
//!   * The cleanly-reachable structural layer (sdg-gauge-transport0,
//!     -kl-affine, -conj-welldef, -law-affine, -F-cross) is PURE RING:
//!     it does NOT consume ax-microcancel, ax-kl, ax-gen — if it did,
//!     the "does not need the full curvature generator" claim would be a
//!     lie (gauge-covariance ASSERTED, not KL/conjugation-derived, is a
//!     FAKE — this hard-fails it mechanically).
//!   * The gauge-covariance result carries EXACTLY ONE boundary $e
//!     (`gauge.fstr`); the gauge-layer ($e label prefix `gauge.`) has
//!     EXACTLY THREE $e total: the ONE boundary `gauge.fstr` + the TWO
//!     pure-ring definition hypotheses `gauge.conj` / `gauge.law`
//!     (which carry no ap-congruence and no globalization — just the
//!     gauge action's value definitions).  If gauge.fstr were absent the
//!     covariance claim would be unsound; if there were any OTHER
//!     boundary the Book-3 dependency would not be precisely
//!     characterised.
//! And the MEASURED cut-free $a-leaf cost (OUR project metric).
//!
//! Run:  cargo run --release --bin sdggaugepure
//! Exit 0 = genuinely intuitionistic AND the Book-3 boundary is exactly
//! one labelled $e (gauge.fstr), the structural layer pure-ring.

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

const STRUCTURAL: &[&str] = &[
    "sdg-gauge-transport0",
    "sdg-gauge-kl-affine",
    "sdg-gauge-conj-welldef",
    "sdg-gauge-law-affine",
    "sdg-gauge-F-cross",
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
    let path = "data/sdg.gauge.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.gauge.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdggaugepure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("sdggaugepure: KERNEL REJECTED — refusing to certify: {e}");
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

    println!("=== sdggaugepure — SYNTHETIC GAUGE CONNECTION (Book-3 foundation) purity + MEASURED ===");
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
            "  {:<24} {:>2} axioms  {:>8} leaves (10^{:.3})  [{}]",
            st.label,
            ax.len(),
            sz.pretty(),
            sz.log10(),
            verdict
        );
    }

    // ---- adversarial Book-3-foundation assertions -----------------------
    let mut hard_fail = false;

    println!("\n=== adversarial assertions (kernel-authoritative) ===");
    println!(
        "  structural layer is PURE RING (no ax-microcancel / ax-kl / ax-gen):"
    );
    for lab in STRUCTURAL {
        let ax = consumed_axioms(&db, lab, &mut memo);
        let bad: Vec<&str> = ["ax-microcancel", "ax-microcancel2", "ax-kl",
            "ax-kl2", "ax-gen", "ax-spec"]
            .iter()
            .copied()
            .filter(|a| ax.contains(*a))
            .collect();
        let ok = bad.is_empty();
        println!(
            "    {:<24} : {}{}",
            lab,
            if ok { "PURE RING \u{2714}" } else { "NOT PURE \u{2717}" },
            if ok { String::new() } else { format!(" (reaches {bad:?})") }
        );
        if !ok {
            eprintln!(
                "FATAL: {lab} is supposed to be the cleanly-reachable\n\
                 structural layer but reaches {bad:?} — the \"does not need\n\
                 the full curvature generator\" claim would be a lie\n\
                 (gauge-covariance ASSERTED, not derived = a FAKE)."
            );
            hard_fail = true;
        }
    }

    // The gauge-covariance carries exactly one boundary $e: gauge.fstr;
    // the gauge layer ($e prefix `gauge.`) has exactly 3 $e total: the
    // ONE boundary gauge.fstr + the TWO pure-ring definition hypotheses
    // gauge.conj / gauge.law.  The 5 framework $e from data/sdg.base.mm
    // (mp.min/mp.maj/gen.1/q2.1/ee.1 — Hilbert-system rule premises) are
    // NOT layer hypotheses and are excluded.
    let es: Vec<&kernel::Stmt> = db
        .stmts
        .iter()
        .filter(|s| s.kind == kernel::Kind::E && s.label.starts_with("gauge."))
        .collect();
    let n_e = es.len();
    let has_fstr = es.iter().any(|s| s.label == "gauge.fstr");
    let has_conj = es.iter().any(|s| s.label == "gauge.conj");
    let has_law = es.iter().any(|s| s.label == "gauge.law");
    println!(
        "\n  gauge-layer $e (label `gauge.*`) in corpus        : {n_e}"
    );
    println!(
        "  covariance boundary $e `gauge.fstr` present       : {}",
        if has_fstr { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    println!(
        "  gauge-action pure-ring def $e `gauge.conj`        : {}  (adjoint g·A·g⁻¹ value def; NOT a boundary)",
        if has_conj { "YES" } else { "NO" }
    );
    println!(
        "  gauge-law pure-ring def $e `gauge.law`            : {}  (full A'=g·A·g⁻¹+g·dg value def; NOT a boundary)",
        if has_law { "YES" } else { "NO" }
    );
    println!(
        "  => EXACTLY ONE boundary $e (gauge.fstr) = the PRECISE Book-3\n\
        \x20    dependency: F's genuine value / Bianchi / FULL gauge-\n\
        \x20    covariance genuinely needs B3-curv (the full curvature\n\
        \x20    generator).  gauge.conj / gauge.law are pure-ring gauge-\n\
        \x20    action value definitions, NOT boundaries."
    );
    if !has_fstr {
        eprintln!(
            "FATAL: covariance boundary $e `gauge.fstr` missing — the\n\
             gauge-covariance result would be unsound / its boundary\n\
             unstated (ASSERTED, not derived = a FAKE)."
        );
        hard_fail = true;
    }
    if n_e != 3 {
        eprintln!(
            "FATAL: expected exactly 3 gauge-layer $e (gauge.fstr boundary\n\
             + gauge.conj + gauge.law pure-ring value defs); found {n_e}.\n\
             The Book-3 boundary must be precisely ONE labelled boundary\n\
             $e — refusing to certify."
        );
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
         matches NO classical template — the structural twin of\n  \
         eq-pl1/2 / eq-mu1/2.  No level / no result needs a classical\n  \
         principle: the gauge layer is uniformly intuitionistically\n  \
         pure (every $p's consumed-axiom closure is classical-free)."
    );
    println!(
        "\nVERDICT: GENUINELY INTUITIONISTIC \u{2714}  The cleanly-reachable\n         \
         synthetic gauge-connection structural layer (the gauge potential\n         \
         A is KL-affine; the gauge-transformation law of A —\n         \
         A'=g·A·g⁻¹+g·dg — is well-defined; the symmetric zeroth-order\n         \
         part of the field strength F vanishes) is PURE RING and needs\n         \
         NO full curvature generator.  F's genuine value / Bianchi / FULL\n         \
         gauge-covariance genuinely needs B3-curv (the full curvature) —\n         \
         surfaced as EXACTLY ONE labelled $e (gauge.fstr), the precise\n         \
         Book-3 dependency map.  A precisely-characterised boundary is a\n         \
         FULL SUCCESS per the Iron Rule — reported, not faked."
    );
    std::process::exit(0);
}
