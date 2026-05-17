//! dagsep — the tree-like vs DAG-like proof-size separation for the
//! Birkhoff postulates, as a concrete *measured* instance.
//!
//! READ-ONLY consumer of the kernel-verified corpus. It does NOT touch
//! grounded.rs/kernel.rs/cse.rs/grounded.mm. It:
//!
//!   1. parses `data/grounded.out.mm` (the assembled corpus that the
//!      authoritative `grounded` run wrote — byte-identical to the db it
//!      verified with `verified all 96 ✔`),
//!   2. *independently re-verifies it with a fresh `kernel::Db`* — the same
//!      sole trust root; if this fails, every number below is discarded,
//!   3. for each Birkhoff postulate `$p` reports three kernel-grounded
//!      sizes:
//!        - TREE  : `expand()` — the fully-inlined cut-free $a-leaf count
//!                  (set.mm convention: $f/$e = 0, $a = 1, $p = expand).
//!                  This is the project's headline metric.
//!        - DAG   : the distinct-node size of that postulate's proof when
//!                  every named sub-lemma is stored once and shared — i.e.
//!                  Σ stored RPN proof length over the reachable closure of
//!                  `$p` lemmas, plus the distinct $a/$f leaves it reaches
//!                  (each size 1). This is the honest per-postulate analogue
//!                  of the project-wide `shared_total`.
//!        - CSE   : the same DAG measure recomputed on the corpus AFTER the
//!                  sound common-subproof minimizer (`cse::crunch`), adopted
//!                  ONLY if a fresh `kernel::Db::verify()` accepts the
//!                  crunched corpus AND every original `$p` keeps a
//!                  byte-identical conclusion (the exact same gate as
//!                  grounded.rs's emit_json). Else: CSE = DAG, reported
//!                  un-crunched, with an honest discard line.
//!
//! Every figure printed is computed from a corpus a fresh kernel accepted
//! in THIS process. Nothing here is trusted that the kernel did not just
//! re-derive.

#[path = "../kernel.rs"]
mod kernel;
#[path = "../number.rs"]
mod number;
#[path = "../cse.rs"]
mod cse;

use number::ProofSize;
use std::collections::{HashMap, HashSet};

/// Fully-inlined ($a-invocation) count — identical semantics to
/// grounded.rs::expand (set.mm convention).
fn expand(db: &kernel::Db, label: &str, memo: &mut HashMap<String, ProofSize>) -> ProofSize {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    let st = match db.get(label) {
        Some(s) => s,
        None => {
            let z = ProofSize::zero();
            memo.insert(label.to_string(), z.clone());
            return z;
        }
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

/// DAG size of `root`'s proof under maximal named-lemma sharing.
///
/// Walk the reachable set of labels from `root` (a `$p`). Every distinct
/// label is counted once. A `$p`/`$a` contributes its stored RPN proof
/// length if it is a `$p` (the bytes the kernel actually stores and
/// re-checks for that node), and 1 if it is an `$a` (a primitive leaf,
/// the same unit `expand` charges it). `$f`/`$e` glue is 0, exactly as in
/// the cut-free metric, so TREE and DAG are measured on the same scale and
/// the only difference is sharing.
fn dag_size(db: &kernel::Db, root: &str) -> (u64, usize, usize, usize) {
    let mut seen: HashSet<String> = HashSet::new();
    let mut stack = vec![root.to_string()];
    let mut total: u64 = 0;
    let mut n_p = 0usize;
    let mut n_a = 0usize;
    let mut rpn_sum = 0usize;
    while let Some(lbl) = stack.pop() {
        if !seen.insert(lbl.clone()) {
            continue;
        }
        let st = match db.get(&lbl) {
            Some(s) => s,
            None => continue,
        };
        match st.kind {
            kernel::Kind::F | kernel::Kind::E => {}
            kernel::Kind::A => {
                total += 1;
                n_a += 1;
            }
            kernel::Kind::P => {
                total += st.proof.len() as u64;
                rpn_sum += st.proof.len();
                n_p += 1;
                for s in &st.proof {
                    if !seen.contains(s) {
                        stack.push(s.clone());
                    }
                }
            }
        }
    }
    (total, n_p, n_a, rpn_sum)
}

fn p_proof_total(db: &kernel::Db) -> usize {
    db.stmts
        .iter()
        .filter(|s| matches!(s.kind, kernel::Kind::P))
        .map(|s| s.proof.len())
        .sum()
}

const POSTULATES: &[(&str, &str)] = &[
    ("G0-congsub", "G0  congruence-substitution"),
    ("G1a-rulerr", "G1  ruler (ray exists)"),
    ("G1b-rulerd", "G1  ruler (distance)"),
    ("G2-incid", "G2  incidence"),
    ("G3a-rayangle", "G3a ray-angle"),
    ("G3bp-protuniq-oriented", "G3b protractor-uniqueness (oriented)"),
    ("G3c-rayline", "G3c ray-line"),
    ("G4-sas", "G4  SAS (hardest postulate)"),
    ("g3a-dotprop", "g3a-dotprop (ASA' vertex-a transitivity)"),
    ("g4a-sss", "g4a-sss (SSS->ACong, closes ASA' GAP#2)"),
    ("sqd-sym", "sqd-sym (distance symmetry)"),
];

fn fmt_log(x: f64) -> String {
    if x.is_finite() {
        format!("10^{:.3}", x)
    } else {
        "0".into()
    }
}

fn run_table(db: &kernel::Db, label: &str, crunched_db: Option<&kernel::Db>) {
    println!("\n=== {label} ===");
    println!(
        "{:<40} {:>16} {:>9} {:>14} {:>9} {:>11} {:>9}",
        "postulate", "TREE (cut-free)", "log10", "DAG (shared)", "log10", "CSE", "log10"
    );
    let mut memo = HashMap::new();
    for (name, desc) in POSTULATES {
        if db.get(name).is_none() {
            println!("{desc:<40} {:>16}", "(absent)");
            continue;
        }
        let tree = expand(db, name, &mut memo);
        let tl = tree.log10();
        let (dag, np, _na, _rpn) = dag_size(db, name);
        let dl = (dag as f64).log10();
        let (cse_v, cl) = match crunched_db {
            Some(cdb) if cdb.get(name).is_some() => {
                let (c, _, _, _) = dag_size(cdb, name);
                (c.to_string(), (c as f64).log10())
            }
            _ => ("—".to_string(), f64::NAN),
        };
        let tree_dag = if dag > 0 {
            10f64.powf(tl - dl)
        } else {
            f64::NAN
        };
        println!(
            "{:<40} {:>16} {:>9} {:>14} {:>9} {:>11} {:>9}   [{} $p in closure; TREE/DAG = {:.3e}x]",
            desc,
            tree.pretty().replace("≈", ""),
            fmt_log(tl),
            dag,
            fmt_log(dl),
            cse_v,
            if cl.is_finite() { fmt_log(cl) } else { "—".into() },
            np,
            tree_dag
        );
    }
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "data/grounded.out.mm".to_string());
    eprintln!("[dagsep] reading {path}");
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("FATAL: cannot read {path}: {e}");
        std::process::exit(1);
    });

    // ---- GATE: independent fresh-kernel re-verification ----------------
    let db = kernel::Db::parse(&src).unwrap_or_else(|e| {
        eprintln!("FATAL: corpus parse failed: {e}");
        std::process::exit(1);
    });
    match db.verify() {
        Ok(()) => {
            let np = db
                .stmts
                .iter()
                .filter(|s| matches!(s.kind, kernel::Kind::P))
                .count();
            println!(
                "[dagsep] fresh-kernel re-verification: VERIFIED ALL ✔  \
                 ({} statements, {} $p) — figures below are kernel-grounded",
                db.stmts.len(),
                np
            );
        }
        Err(e) => {
            eprintln!("FATAL: fresh-kernel re-verification REJECTED: {e}");
            eprintln!("All figures discarded (the corpus does not verify).");
            std::process::exit(1);
        }
    }

    let dag_total = p_proof_total(&db);
    println!(
        "[dagsep] corpus-wide shared_total (Σ stored RPN over all $p) = {} ({})",
        dag_total,
        fmt_log((dag_total as f64).log10())
    );

    // ---- sound CSE pass, kernel-gated exactly like grounded.rs ---------
    let mut concl_before: HashMap<String, Vec<String>> = HashMap::new();
    for s in &db.stmts {
        if matches!(s.kind, kernel::Kind::P) {
            concl_before.insert(s.label.clone(), s.expr.clone());
        }
    }
    let crunched_src = cse::crunch(&src);
    let crunched_db: Option<kernel::Db> = match kernel::Db::parse(&crunched_src) {
        Ok(cdb) => {
            let concl_ok = concl_before.iter().all(|(lbl, expr)| {
                matches!(cdb.get(lbl), Some(c) if matches!(c.kind, kernel::Kind::P) && &c.expr == expr)
            });
            let verify_ok = cdb.verify().is_ok();
            let after = p_proof_total(&cdb);
            if verify_ok && concl_ok && after < dag_total {
                println!(
                    "[dagsep] [cse] kernel-verified DAG: shared_total {dag_total} -> {after} \
                     (−{}, {:.2}% smaller); CSE column is kernel-gated ✔",
                    dag_total - after,
                    100.0 * (dag_total - after) as f64 / dag_total as f64
                );
                Some(cdb)
            } else {
                println!(
                    "[dagsep] [cse] DISCARDED (verify={verify_ok}, concl_ok={concl_ok}, \
                     {dag_total}->{after}); reporting un-crunched (CSE = DAG)"
                );
                None
            }
        }
        Err(e) => {
            println!("[dagsep] [cse] crunched parse failed ({e}); reporting un-crunched");
            None
        }
    };

    run_table(&db, "Per-postulate tree/DAG/CSE (kernel-verified)", crunched_db.as_ref());

    // ---- ASA' proof-relativized composition ---------------------------
    // ASA' (src/bin/asaprime.rs) is a SEPARATE binary; the corpus contains
    // no single ASA' `$p`. Its no-cheating closure of ( sqd a c )=( sqd e g )
    // invokes the real verified postulate `$p`s. The DAG cost of the ASA'
    // *instance* is therefore the shared closure over exactly the postulates
    // it relies on (no double counting — shared lemmas counted once); the
    // TREE cost is their inlined sum (asaprime adds only tiny O(10^2-10^3)
    // bridges, dominated by these). This is a COMPOSITION, explicitly
    // labelled, not a corpus `$p` — reported, not faked.
    let asap_deps = ["G0-congsub", "g4a-sss", "G1a-rulerr", "G1b-rulerd", "sqd-sym"];
    let mut memo = HashMap::new();
    let mut tree_sum = ProofSize::zero();
    for d in &asap_deps {
        tree_sum = tree_sum.add(&expand(&db, d, &mut memo));
    }
    // DAG: union closure (shared once) — model as a synthetic root over the
    // deps via the same reachable-set walk seeded with all dep labels.
    let mut seen: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = asap_deps.iter().map(|s| s.to_string()).collect();
    let mut dag_union: u64 = 0;
    while let Some(lbl) = stack.pop() {
        if !seen.insert(lbl.clone()) {
            continue;
        }
        if let Some(st) = db.get(&lbl) {
            match st.kind {
                kernel::Kind::A => dag_union += 1,
                kernel::Kind::P => {
                    dag_union += st.proof.len() as u64;
                    for s in &st.proof {
                        if !seen.contains(s) {
                            stack.push(s.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }
    println!(
        "\n=== ASA' instance (COMPOSITION over verified postulate $p — not a single corpus $p) ===\n\
         deps: {:?}\n\
         TREE (sum of inlined deps, + asaprime's tiny ~10^2-3 bridges): {} ({})\n\
         DAG  (shared closure, each lemma once)                       : {} ({})\n\
         TREE/DAG separation factor                                   : {:.3e}x",
        asap_deps,
        tree_sum.pretty().replace("≈", ""),
        fmt_log(tree_sum.log10()),
        dag_union,
        fmt_log((dag_union as f64).log10()),
        10f64.powf(tree_sum.log10() - (dag_union as f64).log10())
    );

    println!(
        "\n[dagsep] DONE. TREE = cut-free fully-inlined $a-leaf count (headline metric); \
         DAG = maximal named-lemma sharing (Σ stored RPN over reachable $p closure + $a leaves); \
         CSE = DAG after sound kernel-gated common-subproof factoring."
    );
}
