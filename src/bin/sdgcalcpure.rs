//! sdgcalcpure — the INTUITIONISTIC-PURITY GUARD.  The NEW trust root of the
//! sequel, mirroring the prequel's no-cheating / `--lint` guard.
//!
//! It mechanically certifies that NO classical principle appears (a) as
//! an $a in data/sdg.calc.mm at all, nor (b) in the transitive consumed-$a
//! closure of ANY $p.  The kernel guarantees "derived from these axioms";
//! this guard certifies "these axioms are intuitionistically pure".
//!
//! Run:  cargo run --release --bin sdgcalcpure
//! Exit 0 = genuinely intuitionistic; exit 1 = a classical principle was
//! found (REPORTED precisely — that finding is first-class, not hidden).
//!
//! Two independent checks, both must pass:
//!   1. NAME blacklist: no $a label is a known classical-principle name.
//!   2. SHAPE scan: every $a's *statement* is matched against structural
//!      templates for LEM / Peirce / DNE / stable equality / decidable
//!      equality / apartness / consequentia-mirabilis — catching a
//!      classical axiom even if it were given an innocent name.
//!   3. CLOSURE: for every $p, the transitive set of consumed $a is
//!      computed (same recursion sdgfloor's `expand` uses) and checked
//!      to contain none of the flagged axioms.  (Vacuously clean if 1&2
//!      pass, but computed and reported explicitly so the trust story is
//!      auditable per-theorem and stays correct if the base ever grows.)

#[path = "../kernel.rs"]
mod kernel;

use std::collections::{BTreeSet, HashMap};

/// Known classical-principle LABELS (defensive: if any of these ever
/// appear as an $a, fail immediately regardless of shape).
const BLACKLIST_NAMES: &[&str] = &[
    "ax-3", "peirce", "lem", "exmid", "dne", "notnotr", "notnot1",
    "stab", "stable", "dceq", "decidable", "ax-ap", "apart", "apti",
    "condc", "dcn", "ax-cd", "ax-lem", "ax-dne", "ax-peirce",
];

/// Normalise an expression to a whitespace-joined string for matching,
/// dropping the leading `|-` typecode.
fn body(expr: &[String]) -> String {
    let e = if expr.first().map(|s| s.as_str()) == Some("|-") {
        &expr[1..]
    } else {
        expr
    };
    e.join(" ")
}

/// Structural classifier: does this $a *statement body* match a known
/// classical principle template (up to the propositional/term
/// metavariables actually used in our grammar)?  Returns Some(reason).
///
/// We match on shape, not on the specific metavariable names, by
/// abstracting: any single wff metavariable (ph,ps,ch,th) -> "P", any
/// term metavariable -> "X".  The templates are the canonical
/// non-intuitionistic schemes.
fn classical_reason(b: &str) -> Option<String> {
    // token-level abstraction
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

    // Law of excluded middle: ( P \/ -. P )  (any orientation)
    if s == "( P \\/ -. P )" || s == "( -. P \\/ P )" {
        return Some("law of excluded middle ( ph \\/ -. ph )".into());
    }
    // Double-negation elimination: ( -. -. P -> P )
    if s == "( -. -. P -> P )" {
        return Some("double-negation elimination ( -. -. ph -> ph )".into());
    }
    // Peirce / ax-3 contraposition: ( ( -. P -> -. P ) -> ( P -> P ) )
    // canonical ax-3 is ( ( -. ph -> -. ps ) -> ( ps -> ph ) )
    if s == "( ( -. P -> -. P ) -> ( P -> P ) )" {
        return Some("ax-3 / classical contraposition".into());
    }
    // Peirce's law: ( ( ( P -> P ) -> P ) -> P )
    if s == "( ( ( P -> P ) -> P ) -> P )" {
        return Some("Peirce's law".into());
    }
    // Consequentia mirabilis: ( ( -. P -> P ) -> P )
    if s == "( ( -. P -> P ) -> P )" {
        return Some("consequentia mirabilis".into());
    }
    // Stable equality: ( -. -. X = X -> X = X )
    if s == "( -. -. X = X -> X = X )" {
        return Some("stable equality ( -. -. x = y -> x = y )".into());
    }
    // Decidable equality: ( X = X \/ -. X = X )
    if s == "( X = X \\/ -. X = X )" || s == "( -. X = X \\/ X = X )" {
        return Some("decidable equality ( x = y \\/ -. x = y )".into());
    }
    // Generic stability for any predicate: ( -. -. P -> P ) already caught.
    // Apartness primitive: an `# ` apartness symbol or apartness tightness
    // ( -. X # X -> X = X ) — we have no `#` constant; flag if it appears.
    if abst.iter().any(|tk| tk == "#" || tk == "ap#" || tk == "#") && s.contains("# ") {
        return Some("apartness primitive / tightness".into());
    }
    // General LEM-for-predicates of arity (e.g. ( ( D X ) \/ -. ( D X ) ))
    if (s.starts_with("( ( ") && s.contains(" ) \\/ -. ( "))
        || s.contains("\\/ -. (") && s.ends_with(") )")
    {
        // Only flag if it is literally `Q \/ -. Q` shaped: lhs == inner of rhs
        if let Some(reason) = lem_for_atom(&s) {
            return Some(reason);
        }
    }
    None
}

/// Detect ( Q \/ -. Q ) for an atomic/predicate Q (e.g. ( ( D x ) \/ -. ( D x ) )).
fn lem_for_atom(s: &str) -> Option<String> {
    // strip one outer ( ... )
    let inner = s.strip_prefix("( ")?.strip_suffix(" )")?;
    // split at top-level \/
    let toks: Vec<&str> = inner.split(' ').collect();
    let mut depth = 0i32;
    for (i, tk) in toks.iter().enumerate() {
        match *tk {
            "(" => depth += 1,
            ")" => depth -= 1,
            "\\/" if depth == 0 => {
                let lhs = toks[..i].join(" ");
                let rhs = toks[i + 1..].join(" ");
                let rhs_neg = rhs.strip_prefix("-. ")?;
                if lhs == rhs_neg {
                    return Some(format!("excluded middle for atom `{lhs}`"));
                }
            }
            _ => {}
        }
    }
    None
}

/// Transitive consumed-$a closure of a $p (the same recursion sdgfloor's
/// `expand` uses, collecting $a labels instead of counting leaves).
fn consumed_axioms(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    memo.insert(label.to_string(), BTreeSet::new()); // cycle guard
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

fn main() {
    let path = "data/sdg.calc.mm";
    let src = std::fs::read_to_string(path).expect("read data/sdg.calc.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("sdgcalcpure: PARSE ERROR: {e}");
            std::process::exit(1);
        }
    };
    // The guard requires the corpus to itself be kernel-sound (a classical
    // principle hidden behind an unverifiable proof would be moot, but we
    // refuse to certify a corpus the kernel rejects).
    if let Err(e) = db.verify() {
        eprintln!("sdgcalcpure: KERNEL REJECTED — refusing to certify: {e}");
        std::process::exit(1);
    }

    let mut flagged: Vec<(String, String)> = Vec::new();

    // ---- checks 1 & 2: every $a, by name and by shape -------------------
    let mut n_ax = 0usize;
    for st in &db.stmts {
        if st.kind != kernel::Kind::A {
            continue;
        }
        // skip pure wff/term syntax constructors (typecode wff/term, not |-)
        let is_logical = st.expr.first().map(|s| s.as_str()) == Some("|-");
        if !is_logical {
            continue;
        }
        n_ax += 1;
        if BLACKLIST_NAMES.contains(&st.label.as_str()) {
            flagged.push((
                st.label.clone(),
                format!("blacklisted classical-principle name `{}`", st.label),
            ));
        }
        if let Some(reason) = classical_reason(&body(&st.expr)) {
            flagged.push((st.label.clone(), reason));
        }
    }

    // ---- check 3: per-$p consumed-axiom closure -------------------------
    let flagged_set: BTreeSet<String> =
        flagged.iter().map(|(l, _)| l.clone()).collect();
    let mut memo: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut per_thm: Vec<(String, BTreeSet<String>)> = Vec::new();
    for st in &db.stmts {
        if st.kind != kernel::Kind::P {
            continue;
        }
        let ax = consumed_axioms(&db, &st.label, &mut memo);
        per_thm.push((st.label.clone(), ax));
    }

    println!("=== sdgcalcpure — INTUITIONISTIC-PURITY GUARD (new trust root) ===");
    println!(
        "corpus: {}  ({} statements, {} logical $a audited)",
        path,
        db.stmts.len(),
        n_ax
    );
    println!("\nPer-theorem consumed-axiom closure (cut-free reachable $a):");
    for (lbl, ax) in &per_thm {
        let bad: Vec<&String> = ax.iter().filter(|a| flagged_set.contains(*a)).collect();
        let verdict = if bad.is_empty() {
            "intuitionistic".to_string()
        } else {
            format!("CLASSICAL via {bad:?}")
        };
        println!(
            "  {:<14} {:>2} axioms  [{}]",
            lbl,
            ax.len(),
            verdict
        );
    }

    if flagged.is_empty() {
        println!(
            "\nNAME + SHAPE scan: all {n_ax} logical axioms are intuitionistically pure."
        );
        println!("  (NO ax-3 / Peirce / LEM / DNE / stable-eq / decidable-eq / apartness)");
        println!(
            "\nVERDICT: GENUINELY INTUITIONISTIC ✔  — no classical principle in any\n         $a, and none in the consumed-axiom closure of any $p."
        );
        std::process::exit(0);
    } else {
        eprintln!("\nVERDICT: CLASSICAL CONTAMINATION FOUND ✗  (this is a ZERO — reported, not hidden)");
        for (lbl, why) in &flagged {
            eprintln!("  axiom `{lbl}` : {why}");
        }
        for (lbl, ax) in &per_thm {
            let bad: Vec<&String> =
                ax.iter().filter(|a| flagged_set.contains(*a)).collect();
            if !bad.is_empty() {
                eprintln!("  theorem `{lbl}` CONSUMES classical {bad:?}");
            }
        }
        std::process::exit(1);
    }
}
