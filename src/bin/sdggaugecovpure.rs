//! sdggaugecovpure — intuitionistic-purity guard + MEASURED cost +
//! BOUNDARY-DISCHARGE adversarial assertions for data/sdg.gaugecov.mm
//! (BOOK-3 WAVE-3: the `gauge.fstr` boundary DISCHARGED).  Mirrors
//! sdgbianchi2pure / sdggaugepure / sdgpure exactly.
//!
//! Purity (all must pass): NAME blacklist on every logical $a; SHAPE
//! scan vs classical templates; per-$p consumed-axiom closure none
//! classical.
//! PLUS hard-fail adversarial assertions specific to retiring the
//! gauge.fstr composite boundary (the conn.hol->seam-free lesson, one
//! domain over — a faked / inert-$e "discharge" is a ZERO):
//!   * sdg-gaugecov-fstr GENUINELY CONSUMES ax-microcancel AND ax-gen —
//!     the (b)-half: F = curvature-of-A's seam, exactly the wave-1
//!     sdg-curvature construction.  Missing either ⇒ the (b)-half is
//!     faked ⇒ hard-fail.
//!   * sdg-gaugecov-aprot GENUINELY CONSUMES eq-ap — the (a)-half: the
//!     gauge rotation under the inner `ap` evaluation, the §5j
//!     ap-Leibniz step DERIVED by the flagged axiom.  Missing ⇒ the
//!     (a)-half is faked ⇒ hard-fail.
//!   * NO inert composite `gauge.fstr` $e survives anywhere.  The
//!     corpus carries EXACTLY the principled boundary $e: gc.hr1/gc.hr2
//!     (ax-kl-existence reps, same discipline as cv.hr*/b2.hr*) +
//!     gc.rot (the rotation's structural rep) — prefix `gc.`, count 3,
//!     and no $e literally named `gauge.fstr`.
//!   * sdg-gaugecov-addcan-imp and sdg-gaugecov-covariant are PURE RING
//!     (no ax-microcancel / ax-kl / ax-gen / ax-spec / eq-ap): the §5b
//!     closer and the conjugation-swap covariance are ring-only; only
//!     -fstr consumes the seam, only -aprot consumes eq-ap.
//! And the MEASURED cut-free $a-leaf cost (OUR project metric).
//!
//! Run:  cargo run --release --bin sdggaugecovpure
//! Exit 0 = genuinely intuitionistic AND both inseparable halves of the
//! gauge.fstr boundary genuinely consumed AND no inert composite $e.

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

// Pure-ring layer: the §5b closer + the conjugation-swap covariance.
// Only -fstr may consume the seam; only -aprot may consume eq-ap.
const PURE_RING: &[&str] = &[
    "sdg-gaugecov-addcan-imp",
    "sdg-gaugecov-covariant",
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
    let path = "data/sdg.gaugecov.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.gaugecov.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdggaugecovpure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("sdggaugecovpure: KERNEL REJECTED — refusing to certify: {e}");
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

    println!("=== sdggaugecovpure — gauge.fstr boundary DISCHARGED (Book-3 wave-3) purity + MEASURED ===");
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
            "  {:<26} {:>2} axioms  {:>8} leaves (10^{:.3})  [{}]",
            st.label,
            ax.len(),
            sz.pretty(),
            sz.log10(),
            verdict
        );
    }

    let mut hard_fail = false;
    println!("\n=== adversarial assertions (kernel-authoritative) ===");

    // (b)-half: sdg-gaugecov-fstr genuinely consumes the curvature seam.
    let fstr_ax = consumed_axioms(&db, "sdg-gaugecov-fstr", &mut memo);
    let f_mc = fstr_ax.contains("ax-microcancel");
    let f_gen = fstr_ax.contains("ax-gen");
    println!(
        "  (b) sdg-gaugecov-fstr consumes ax-microcancel : {}",
        if f_mc { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    println!(
        "  (b) sdg-gaugecov-fstr consumes ax-gen         : {}",
        if f_gen { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    if !(f_mc && f_gen) {
        eprintln!(
            "FATAL: sdg-gaugecov-fstr must GENUINELY CONSUME ax-microcancel\n\
             AND ax-gen (the (b)-half — F=curvature-of-A's seam, the\n\
             wave-1 sdg-curvature construction).  Missing one ⇒ the\n\
             gauge.fstr boundary's (b)-half is FAKED = a ZERO."
        );
        hard_fail = true;
    }

    // (a)-half: sdg-gaugecov-aprot genuinely consumes the flagged eq-ap.
    let aprot_ax = consumed_axioms(&db, "sdg-gaugecov-aprot", &mut memo);
    let a_eqap = aprot_ax.contains("eq-ap");
    println!(
        "  (a) sdg-gaugecov-aprot consumes eq-ap         : {}",
        if a_eqap { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    if !a_eqap {
        eprintln!(
            "FATAL: sdg-gaugecov-aprot must GENUINELY CONSUME eq-ap (the\n\
             (a)-half — the gauge rotation under the inner ap evaluation,\n\
             the §5j ap-Leibniz step DERIVED by the flagged axiom).\n\
             Missing ⇒ the gauge.fstr boundary's (a)-half is FAKED = ZERO."
        );
        hard_fail = true;
    }

    // No inert composite gauge.fstr $e; exactly the principled gc.* $e.
    let es: Vec<&kernel::Stmt> = db
        .stmts
        .iter()
        .filter(|s| s.kind == kernel::Kind::E && s.label.starts_with("gc."))
        .collect();
    let n_e = es.len();
    let has_hr1 = es.iter().any(|s| s.label == "gc.hr1");
    let has_hr2 = es.iter().any(|s| s.label == "gc.hr2");
    let has_rot = es.iter().any(|s| s.label == "gc.rot");
    let any_fstr_e = db
        .stmts
        .iter()
        .any(|s| s.kind == kernel::Kind::E && s.label == "gauge.fstr");
    println!(
        "\n  principled boundary $e (label `gc.*`) in corpus   : {n_e}"
    );
    println!(
        "  ax-kl-existence reps gc.hr2 / gc.hr1 (fstr)       : {} / {}",
        if has_hr2 { "YES \u{2714}" } else { "NO \u{2717}" },
        if has_hr1 { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    println!(
        "  rotation structural rep gc.rot (aprot)            : {}",
        if has_rot { "YES \u{2714}" } else { "NO \u{2717}" }
    );
    println!(
        "  inert composite `gauge.fstr` $e anywhere          : {}",
        if any_fstr_e { "PRESENT \u{2717}" } else { "ABSENT \u{2714}" }
    );
    println!(
        "  => the opaque composite boundary is RETIRED to the principled\n\
        \x20    seam + eq-ap + KL-existence structure (the conn.hol→seam-\n\
        \x20    free upgrade, one domain over).  Both inseparable halves\n\
        \x20    GENUINELY consumed; no inert $e."
    );
    if !(has_hr1 && has_hr2 && has_rot) || n_e != 3 || any_fstr_e {
        eprintln!(
            "FATAL: expected EXACTLY the three principled boundary $e\n\
             (gc.hr1 + gc.hr2 + gc.rot) and NO inert composite\n\
             `gauge.fstr` $e; found {n_e} gc.* and gauge.fstr {}.\n\
             An inert-$e \"discharge\" is rejected, not shipped.",
            if any_fstr_e { "PRESENT" } else { "absent" }
        );
        hard_fail = true;
    }

    // Pure-ring layer must not consume the seam or eq-ap.
    println!(
        "\n  pure-ring layer (no ax-microcancel / ax-kl / ax-gen / ax-spec / eq-ap):"
    );
    for lab in PURE_RING {
        let ax = consumed_axioms(&db, lab, &mut memo);
        let bad: Vec<&str> = ["ax-microcancel", "ax-microcancel2", "ax-kl",
            "ax-kl2", "ax-gen", "ax-spec", "eq-ap"]
            .iter()
            .copied()
            .filter(|a| ax.contains(*a))
            .collect();
        let ok = bad.is_empty();
        println!(
            "    {:<26} : {}{}",
            lab,
            if ok { "PURE RING \u{2714}" } else { "NOT PURE \u{2717}" },
            if ok { String::new() } else { format!(" (reaches {bad:?})") }
        );
        if !ok {
            eprintln!(
                "FATAL: {lab} is supposed to be the pure-ring layer but\n\
                 reaches {bad:?} — only -fstr may consume the seam, only\n\
                 -aprot may consume eq-ap."
            );
            hard_fail = true;
        }
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
         matches NO classical template.  No level / no result needs a\n  \
         classical principle: every $p's consumed-axiom closure is\n  \
         classical-free."
    );
    println!(
        "\nVERDICT: GENUINELY INTUITIONISTIC \u{2714}  The gauge.fstr boundary\n         \
         is DISCHARGED — F = curvature-of-the-gauge-potential genuinely\n         \
         consumes the curvature seam (ax-microcancel+ax-gen, the (b)-half,\n         \
         the wave-1 conn.hol retirement one domain over); the gauge\n         \
         rotation under the inner ap evaluation genuinely consumes the\n         \
         flagged eq-ap (the (a)-half); the covariance F'=g·F·g⁻¹ is\n         \
         PURE RING on top.  Both inseparable halves SEQUEL_SCOPE §5n\n         \
         declared are now GENUINELY CONSUMED; NO inert composite\n         \
         gauge.fstr $e survives.  The full non-abelian holonomy beyond\n         \
         BOOK3_SCOPE §2's scalar-line reduction is the named residual\n         \
         (CITED, not new).  That this IS physical gauge theory rests on\n         \
         the UNCHANGED Book-Two model [PROJECTION], never re-summed —\n         \
         the recurring theorem, held once more.  Reported, not faked."
    );
    std::process::exit(0);
}
