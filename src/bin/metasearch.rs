//! metasearch — a kernel-gated proof superoptimizer (separate tool).
//!
//! It NEVER edits the production proof construction or normalizer. It reads
//! the emitted corpus `data/grounded.out.mm` (produced by `grounded`) and
//! calls the sound kernel `kernel::Db::verify()` as the sole fitness oracle.
//!
//! Usage:
//!   cargo run --release --bin metasearch -- s1
//!   cargo run --release --bin metasearch -- s2 [path/to/grounded.out.mm]
//!   cargo run --release --bin metasearch          (runs both)

#[path = "../kernel.rs"]
mod kernel;
#[path = "../elaborate.rs"]
mod elaborate;
#[path = "../number.rs"]
mod number;
#[path = "../search.rs"]
mod search;

use search::*;

fn s1() {
    println!("=== S1 — normalizer-strategy search (kernel-gated) ===\n");
    let d = law_of_cosines_demo();
    println!(
        "Demo identity `{}` (degree-4: quadratic monomials a²,b²,c²,d²):",
        d.name
    );
    println!("  LHS tree shape: ((a*a)+(b*b)) + ((c*c)+(d*d))");
    println!("  RHS tree shape: (d*d) + ((c*c) + ((b*b) + (a*a)))");
    println!(
        "  Content: pure additive AC over 4 quadratic monomials — exactly\n  \
         the reassociation/reordering the production `loclink` exploits.\n"
    );
    let results = run_s1(&d);
    println!(
        "{:<22} {:>8} {:>14}  {}",
        "strategy", "rpn", "cut-free($a)", "kernel"
    );
    println!("{}", "-".repeat(72));
    let mut default_nodes = None;
    let mut best_nodes = None;
    for r in &results {
        let tag = format!("{:?}/{:?}", r.strat.order, r.strat.assoc);
        let cf = if r.verified {
            r.cut_free.pretty()
        } else {
            "-".to_string()
        };
        println!(
            "{:<22} {:>8} {:>14}  {}",
            tag, r.nodes, cf, r.note
        );
        // "default" = the NAIVE unsearched normalizer: a left fold of the
        // atoms (Lex order + LeftSpine) — what you get without optimizing the
        // association. The search must beat this.
        if r.strat.order == MonoOrder::Lex
            && r.strat.assoc == Assoc::LeftSpine
            && r.verified
        {
            default_nodes = Some((tag.clone(), r.nodes, r.cut_free.clone()));
        }
        if r.verified && best_nodes.as_ref().map(|(_, n, _)| r.nodes < *n).unwrap_or(true) {
            best_nodes = Some((tag, r.nodes, r.cut_free.clone()));
        }
    }
    println!();
    if let (Some((dt, dn, dc)), Some((bt, bn, bc))) = (&default_nodes, &best_nodes) {
        println!(
            "DEFAULT (Lex/LeftSpine, naive left-fold): {dt}  rpn={dn}  cut-free={}",
            dc.pretty()
        );
        println!(
            "SEARCHED BEST                           : {bt}  rpn={bn}  cut-free={}",
            bc.pretty()
        );
        if bn < dn {
            println!(
                "  -> search improved rpn node count {} -> {} ({:.1}% smaller)",
                dn,
                bn,
                100.0 * (1.0 - *bn as f64 / *dn as f64)
            );
        } else if bn == dn {
            println!("  -> default already optimal among searched strategies for this identity");
        }
        println!(
            "  cut-free: {} -> {}  (every reported number is from a corpus\n  \
             the kernel ACCEPTED in this process; rejected strategies print\n  \
             `KERNEL REJECTED` and are never reported as wins)",
            dc.pretty(),
            bc.pretty()
        );
    } else {
        println!("(no Lex/RightSpine baseline verified — see notes above)");
    }
    // --- Honest task-2 question: does S1 beat the PRODUCTION normalizer? ---
    // The production AC normalizer `ra`/`canon_sum` in src/bin/grounded.rs
    // builds a RIGHT-SPINE sum:  ra(xs) = tpl(xs[0], ra(xs[1..])).  That is
    // *exactly* the Assoc::RightSpine association S1 searches.  So the honest
    // production baseline is NOT the naive Lex/LeftSpine left-fold above —
    // it is the RightSpine result.  We pull the kernel-verified RightSpine
    // number out of `results` and compare S1-best against IT.
    let prod = results
        .iter()
        .filter(|r| r.verified && r.strat.assoc == Assoc::RightSpine)
        .min_by(|a, b| a.cut_free.log10().partial_cmp(&b.cut_free.log10()).unwrap());
    println!();
    println!("---- S1 vs PRODUCTION normalizer (the real task-2 question) ----");
    match (prod, &best_nodes) {
        (Some(p), Some((bt, bn, bc))) => {
            println!(
                "PRODUCTION shape (ra = right-spine; what grounded.rs ACTUALLY\n  \
                 emits)            : {:?}/{:?}  rpn={}  cut-free={}",
                p.strat.order,
                p.strat.assoc,
                p.nodes,
                p.cut_free.pretty()
            );
            println!(
                "S1 SEARCHED BEST                       : {bt}  rpn={bn}  cut-free={}",
                bc.pretty()
            );
            let pl = p.cut_free.log10();
            let bl = bc.log10();
            if bl < pl - 1e-9 {
                println!(
                    "  -> S1 BEATS production: cut-free {} -> {} (10^{:.3} -> 10^{:.3})",
                    p.cut_free.pretty(),
                    bc.pretty(),
                    pl,
                    bl
                );
            } else if (bl - pl).abs() <= 1e-9 && *bn == p.nodes {
                println!(
                    "  -> HONEST FINDING: S1 does NOT beat production. S1's optimum\n  \
                     ({} cut-free, rpn={}) is byte-identical to the RightSpine\n  \
                     association the production `ra` normalizer ALREADY builds.\n  \
                     The 30%% \"win\" above is only over a STRAWMAN naive left-fold\n  \
                     (Lex/LeftSpine) that production never used. Production is\n  \
                     already on the optimal association spine for this family;\n  \
                     S1 confirms optimality, it does not improve it.",
                    bc.pretty(),
                    bn
                );
            } else {
                println!(
                    "  -> S1 best (10^{:.3}) vs production (10^{:.3}): no strict win.",
                    bl, pl
                );
            }
        }
        _ => println!("(no kernel-verified RightSpine/production result to compare)"),
    }
    let n_ok = results.iter().filter(|r| r.verified).count();
    println!(
        "\n{}/{} strategies kernel-verified the exact target conclusion.",
        n_ok,
        results.len()
    );
}

fn s2(path: &str) {
    println!("\n=== S2 — auto-generic-factoring over emitted corpus ===\n");
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            println!("cannot read corpus {path}: {e}");
            println!("(run `cargo run --release --bin grounded` first to emit it)");
            return;
        }
    };
    println!("corpus: {path} ({} bytes)", src.len());
    let out = run_s2(&src);
    println!("candidate lemma   : {}", out.lemma);
    println!("occurrences       : {}", out.occurrences);
    println!(
        "KERNEL-SOUND      : {}  (rewritten corpus re-verified by the kernel\n  \
         AND every original $p conclusion byte-identical — GATE 1 ∧ GATE 2)",
        out.kernel_sound
    );
    if out.kernel_sound {
        println!(
            "  -> verified factored corpus written to data/grounded.factored.mm\n  \
             (independently re-checkable; lemma `{}` shared at {} sites)",
            out.lemma, out.occurrences
        );
    }
    println!("cut-free before   : {}", out.before.pretty());
    println!("cut-free after    : {}", out.after.pretty());
    println!(
        "stored-tokens bef : {}   (Σ |$p proof| — the share-respecting size)",
        out.tokens_before
    );
    println!("stored-tokens aft : {}", out.tokens_after);
    if out.tokens_before > 0 {
        let d = out.tokens_before as i64 - out.tokens_after as i64;
        println!(
            "  -> stored-proof delta: {} tokens ({:+.3}%)  [{}]",
            -d,
            -100.0 * d as f64 / out.tokens_before as f64,
            if out.tokens_after < out.tokens_before {
                "factoring shrinks the stored corpus"
            } else {
                "no stored-size win"
            }
        );
    }
    println!(
        "ACCEPTED (GATE3)  : {}  ({})",
        out.accepted, out.reason
    );
    if out.accepted {
        let db = out.before.log10();
        let da = out.after.log10();
        println!(
            "  kernel-verified delta: 10^{:.3} -> 10^{:.3}  ({:.3} dex)",
            db,
            da,
            db - da
        );
    }
    println!(
        "\nS2 scope (honest): this finds the *ground* maximal-repeated-subtree\n\
         specialization of the generic-lemma move — it shares an identical\n\
         repeated proof chunk via one $p. The full loclink-style move\n\
         (anti-unify differing subterms, abstract them to fresh $f, instantiate\n\
         by substitution) needs anti-unification of the variant positions; the\n\
         CSE engine here only fires when the repeated chunk is *syntactically\n\
         identical*. See METASEARCH.md for the precise gap and what closes it."
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("all");
    let corpus = args
        .get(2)
        .cloned()
        .unwrap_or_else(|| "data/grounded.out.mm".to_string());
    match mode {
        "s1" => s1(),
        "verify" => {
            // Independent kernel re-check of an on-disk corpus (adversarial
            // gate: prove the written factored corpus really verifies, with
            // no in-process state).
            let src = std::fs::read_to_string(&corpus)
                .unwrap_or_else(|e| panic!("read {corpus}: {e}"));
            let db = kernel::Db::parse(&src)
                .unwrap_or_else(|e| panic!("parse {corpus}: {e}"));
            let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
            match db.verify() {
                Ok(()) => println!(
                    "INDEPENDENT KERNEL VERIFY: {corpus}\n  Ok — all {n_p} $p re-verified by a fresh kernel"
                ),
                Err(e) => println!("INDEPENDENT KERNEL VERIFY: {corpus}\n  REJECTED: {e}"),
            }
        }
        "s2" => s2(&corpus),
        _ => {
            s1();
            s2(&corpus);
        }
    }
}
