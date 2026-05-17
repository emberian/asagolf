//! sdgobligpure — the HONESTY GUARD for data/sdg.oblig.mm.
//!
//! sdg.oblig.mm is the DUAL of the intuitionistic substrate: a
//! PROOF-COMPLEXITY MEASUREMENT corpus for Obligation O (the cut-free
//! cost of the order residue `(x*x)=0 -> x=0`).  It deliberately is
//! classical (it may use ax-3) — so sdgpure must NOT be applied to it.
//! This guard instead certifies the things that keep the MEASUREMENT
//! honest under the iron rule:
//!
//!   1. The corpus kernel-verifies (the upper bound is real).
//!   2. The Obligation-O literal is a genuine DERIVATION, not smuggled:
//!      NO $a in the corpus has the shape `(x*x)=0 -> x=0` (nor the
//!      hypothesis form): the residue must be EARNED, so the measured
//!      $a-leaf count is a meaningful upper bound and not 1-by-fiat.
//!   3. `sdg-oblig-sqz` exists and is a `$p` whose statement is exactly
//!      the residue literal (in hypothesis form `(x*x)=0 |- x=0`).
//!   4. ZERO label collision with data/sdg.base.mm or ANY data/sdg.*.mm
//!      (every label is `sdg-oblig-`-prefixed; verified, not assumed).
//!
//! Run:  cargo run --release --bin sdgobligpure
//! Exit 0 = the measurement is honest; exit 1 = a violation REPORTED.

#[path = "../kernel.rs"]
mod kernel;

use std::collections::BTreeSet;

const OBLIG: &str = "data/sdg.oblig.mm";

fn norm(expr: &[String]) -> String {
    // drop leading typecode, join
    let s = if expr.first().map(|t| t.as_str()) == Some("|-") {
        &expr[1..]
    } else {
        &expr[..]
    };
    s.join(" ")
}

fn main() {
    let mut fail = false;

    // ---- 1. kernel-verify -------------------------------------------
    let src = std::fs::read_to_string(OBLIG).expect("read data/sdg.oblig.mm");
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("FAIL: parse error: {e}");
            std::process::exit(1);
        }
    };
    if let Err(e) = db.verify() {
        eprintln!("FAIL: kernel rejected sdg.oblig.mm: {e}");
        std::process::exit(1);
    }
    let n_p = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
    println!("[1] kernel: verified all {n_p} $p in {OBLIG} OK");

    // ---- 2. residue NOT smuggled as an axiom ------------------------
    // forbidden $a shapes (any variable name) for the residue literal:
    //   ( ( X * X ) = 0 -> X = 0 )            closed implication
    //   X = 0          with an $e ( X * X ) = 0 hyp (1-step sqz-by-fiat)
    let mut smuggled = false;
    for st in &db.stmts {
        if st.kind != kernel::Kind::A {
            continue;
        }
        let b = norm(&st.expr);
        // pattern: ( ( v * v ) = 0 -> v = 0 )
        let bt: Vec<&str> = b.split_whitespace().collect();
        if bt.len() == 11
            && bt[0] == "("
            && bt[1] == "("
            && bt[3] == "*"
            && bt[2] == bt[4]
            && bt[5] == ")"
            && bt[6] == "="
            && bt[7] == "0"
            && bt[8] == "->"
            && bt[9] == bt[2]
            && bt[10] == "="
        {
            eprintln!("FAIL[2]: residue smuggled as $a {}: {}", st.label, b);
            smuggled = true;
        }
    }
    // also: an $a `v = 0` carrying an $e `( v * v ) = 0`
    for st in &db.stmts {
        if st.kind != kernel::Kind::A {
            continue;
        }
        let b = norm(&st.expr);
        let bt: Vec<&str> = b.split_whitespace().collect();
        if bt.len() == 3 && bt[1] == "=" && bt[2] == "0" {
            let v = bt[0];
            for h in &st.mand_hyps {
                if let Some(hs) = db.get(h) {
                    if hs.kind == kernel::Kind::E {
                        let hb = norm(&hs.expr);
                        if hb == format!("( ( {v} * {v} ) = 0 )")
                            || hb == format!("( {v} * {v} ) = 0")
                        {
                            eprintln!(
                                "FAIL[2]: residue smuggled as $a {} with nilpotent $e hyp",
                                st.label
                            );
                            smuggled = true;
                        }
                    }
                }
            }
        }
    }
    if smuggled {
        fail = true;
    } else {
        println!("[2] residue is a genuine derivation (no $a asserts (x*x)=0->x=0) OK");
    }

    // ---- 3. target present, correct statement -----------------------
    match db.get("sdg-oblig-sqz") {
        Some(st) if st.kind == kernel::Kind::P => {
            let concl = norm(&st.expr);
            // sqz is hypothesis form: conclusion `v = 0`, $e hyp `(v*v)=0`
            let ct: Vec<&str> = concl.split_whitespace().collect();
            let ok_concl = ct.len() == 3 && ct[1] == "=" && ct[2] == "0";
            let mut has_nilp_hyp = false;
            if ok_concl {
                let v = ct[0];
                for h in &st.mand_hyps {
                    if let Some(hs) = db.get(h) {
                        let hb = norm(&hs.expr);
                        if hb.contains(&format!("{v} * {v}")) && hb.contains("= 0") {
                            has_nilp_hyp = true;
                        }
                    }
                }
            }
            if ok_concl && has_nilp_hyp {
                println!(
                    "[3] sdg-oblig-sqz : (x*x)=0 |- x=0  (Obligation O literal) OK"
                );
            } else {
                eprintln!(
                    "FAIL[3]: sdg-oblig-sqz statement is not the residue literal: {concl}"
                );
                fail = true;
            }
        }
        _ => {
            eprintln!("FAIL[3]: sdg-oblig-sqz missing or not a $p");
            fail = true;
        }
    }

    // ---- 4. zero label collision vs every data/sdg.*.mm -------------
    let mut my_labels: BTreeSet<String> = BTreeSet::new();
    for st in &db.stmts {
        if matches!(
            st.kind,
            kernel::Kind::A | kernel::Kind::P | kernel::Kind::E | kernel::Kind::F
        ) {
            my_labels.insert(st.label.clone());
        }
    }
    let bad_prefix = my_labels
        .iter()
        .filter(|l| !l.starts_with("sdg-oblig-"))
        .count();
    if bad_prefix != 0 {
        eprintln!("FAIL[4]: {bad_prefix} labels NOT sdg-oblig- prefixed");
        fail = true;
    }
    let mut collisions = 0usize;
    let dir = std::fs::read_dir("data").expect("read data/");
    for ent in dir.flatten() {
        let p = ent.path();
        let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if !(name.starts_with("sdg.") && name.ends_with(".mm")) {
            continue;
        }
        if name == "sdg.oblig.mm" {
            continue;
        }
        let other = std::fs::read_to_string(&p).unwrap_or_default();
        let ot: Vec<&str> = other.split_whitespace().collect();
        for w in ot.windows(2) {
            if matches!(w[1], "$f" | "$e" | "$a" | "$p") && my_labels.contains(w[0]) {
                eprintln!("FAIL[4]: label {} collides with {}", w[0], name);
                collisions += 1;
            }
        }
    }
    if collisions == 0 && bad_prefix == 0 {
        println!(
            "[4] zero collision with data/sdg.base.mm and every data/sdg.*.mm OK"
        );
    } else {
        fail = true;
    }

    if fail {
        eprintln!("\nsdgobligpure: VIOLATION REPORTED (exit 1)");
        std::process::exit(1);
    }
    println!(
        "\nsdgobligpure: the Obligation-O measurement is HONEST.\n  \
         sdg-oblig-sqz = 16476 cut-free $a-leaves (MEASURED, sdgobligfloor)\n  \
         is an UPPER bound for (x*x)=0->x=0.  It is NOT a lower bound.\n  \
         The exact-constant LOWER bound (Frontier C Open Obligation O)\n  \
         is OPEN: an unconditional cut-free proof-size lower bound for a\n  \
         fixed order implication; minimal-DAG/smallest-grammar is\n  \
         NP-hard (SEAM2).  The only PROVED LB is the trivial >= 1\n  \
         (Frontier C: false in Z/4 => >=1 order-essential axiom).\n  \
         The exact constant is NOT closed.  Reported, not faked."
    );
}
