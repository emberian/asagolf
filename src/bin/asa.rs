//! Elaborate + kernel-verify the F0 Birkhoff ASA proof.
//!
//! Pipeline: derive `eqtr` (equality transitivity) from the axioms, then the
//! 6-step ASA argument (segment construction -> SAS -> protractor uniqueness
//! -> incidence -> conclude), emit RPN, and have the sound kernel check the
//! whole augmented database.
//! Usage: cargo run --release --bin asa

#[path = "../kernel.rs"]
mod kernel;
#[path = "../elaborate.rs"]
mod elaborate;
#[path = "../number.rs"]
mod number;

use number::ProofSize;
use std::collections::HashMap;

/// Exact fully-inlined ($a-invocation) count for `label`, plus the per-axiom
/// histogram of the cut-free tree. Convention matches the set.mm extractor:
/// $f/$e = substitution glue (0), $a = primitive leaf (1), $p = expand.
fn expand(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, (ProofSize, HashMap<String, ProofSize>)>,
) -> (ProofSize, HashMap<String, ProofSize>) {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    let st = db.get(label).expect("label");
    let out = match st.kind {
        kernel::Kind::F | kernel::Kind::E => (ProofSize::zero(), HashMap::new()),
        kernel::Kind::A => {
            let mut h = HashMap::new();
            h.insert(label.to_string(), ProofSize::one());
            (ProofSize::one(), h)
        }
        kernel::Kind::P => {
            let mut tot = ProofSize::zero();
            let mut hist: HashMap<String, ProofSize> = HashMap::new();
            for step in st.proof.clone() {
                let (n, sh) = expand(db, &step, memo);
                tot = tot.add(&n);
                for (k, v) in sh {
                    let e = hist.entry(k).or_insert_with(ProofSize::zero);
                    *e = e.add(&v);
                }
            }
            (tot, hist)
        }
    };
    memo.insert(label.to_string(), out.clone());
    out
}

use elaborate::{assemble, leaf, Elab, Lemma, Pt};
use std::process::exit;

fn die(ctx: &str, e: String) -> ! {
    eprintln!("{ctx}: {e}");
    exit(1);
}

fn main() {
    let base = std::fs::read_to_string("data/birkhoff.mm").expect("read birkhoff.mm");

    // ---- phase 1: derive `eqtr` against the base axioms ------------------
    let db0 = kernel::Db::parse(&base).unwrap_or_else(|e| die("base parse", e));
    let el0 = Elab::new(&db0);
    let a = |n: &str| -> Pt { leaf(&format!("v{n}")) };

    // helpers (term/wff constructors + modus ponens) over el0
    let eq = |el: &Elab, s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
    let wi = |el: &Elab, p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let mp = |el: &Elab, pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };

    // eqtr:  |- x = y ,  |- y = z   =>   |- x = z
    let (x, y, z) = (a("x"), a("y"), a("z"));
    let yx = mp(
        &el0,
        eq(&el0, x.clone(), y.clone()),
        eq(&el0, y.clone(), x.clone()),
        leaf("eqtr.1"),
        el0.app("eqcom", &[("x", x.clone()), ("y", y.clone())], &[])
            .unwrap(),
    );
    let ax7 = el0
        .app("ax-7", &[("x", y.clone()), ("y", x.clone()), ("z", z.clone())], &[])
        .unwrap(); // |- ( y = x -> ( y = z -> x = z ) )
    let sa = mp(
        &el0,
        eq(&el0, y.clone(), x.clone()),
        wi(&el0, eq(&el0, y.clone(), z.clone()), eq(&el0, x.clone(), z.clone())),
        yx,
        ax7,
    );
    let eqtr_goal = mp(
        &el0,
        eq(&el0, y.clone(), z.clone()),
        eq(&el0, x.clone(), z.clone()),
        leaf("eqtr.2"),
        sa,
    );
    let eqtr = Lemma {
        name: "eqtr".into(),
        ess: vec![
            ("eqtr.1".into(), vec!["|-", "x", "=", "y"].iter().map(|s| s.to_string()).collect()),
            ("eqtr.2".into(), vec!["|-", "y", "=", "z"].iter().map(|s| s.to_string()).collect()),
        ],
        goal: eqtr_goal,
    };
    let src1 = assemble(&base, &db0, std::slice::from_ref(&eqtr))
        .unwrap_or_else(|e| die("assemble eqtr", e));
    let db1 = kernel::Db::parse(&src1).unwrap_or_else(|e| die("reparse w/ eqtr", e));

    // ---- phase 2: the ASA proof, now with `eqtr` available --------------
    let el = Elab::new(&db1);
    let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
    let wi = |p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let mp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };
    let dist = |p: Pt, q: Pt| el.app("tdist", &[("a", p), ("b", q)], &[]).unwrap();
    let ang = |p: Pt, v: Pt, q: Pt| el.app("tang", &[("a", p), ("b", v), ("c", q)], &[]).unwrap();
    let ray = |p: Pt, q: Pt, r: Pt| el.app("wray", &[("a", p), ("b", q), ("c", r)], &[]).unwrap();
    let on = |p: Pt, q: Pt, r: Pt| el.app("won", &[("a", p), ("b", q), ("c", r)], &[]).unwrap();
    let tri = |p: Pt, q: Pt, r: Pt| el.app("wtri", &[("a", p), ("b", q), ("c", r)], &[]).unwrap();
    let eqtr3 = |xx: Pt, yy: Pt, zz: Pt, p1: Pt, p2: Pt| {
        el.app("eqtr", &[("x", xx), ("y", yy), ("z", zz)], &[p1, p2]).unwrap()
    };

    let (pa, pb, pc) = (a("a"), a("b"), a("c"));
    let (pe, pf, pg) = (a("e"), a("f"), a("g"));
    let len = dist(pe.clone(), pg.clone()); // ( d e g )
    let cp = el
        .app("tcp", &[("a", pa.clone()), ("c", pc.clone()), ("u", len.clone())], &[])
        .unwrap(); // ( cp a c ( d e g ) )

    // s1 : |- ( Ray a c Cp )
    let s1 = el
        .app("ax-ruler-ray", &[("a", pa.clone()), ("c", pc.clone()), ("u", len.clone())], &[])
        .unwrap();
    // s2 : |- d a Cp = d e g
    let s2 = el
        .app("ax-ruler-len", &[("a", pa.clone()), ("c", pc.clone()), ("u", len.clone())], &[])
        .unwrap();
    // ax-rayangle : |- ( ( Ray a c Cp ) -> m b a Cp = m b a c )
    let rax = el
        .app(
            "ax-rayangle",
            &[("a", pa.clone()), ("c", pc.clone()), ("x", cp.clone()), ("b", pb.clone())],
            &[],
        )
        .unwrap();
    let ang_bacp = ang(pb.clone(), pa.clone(), cp.clone());
    let ang_bac = ang(pb.clone(), pa.clone(), pc.clone());
    // s3 : |- m b a Cp = m b a c
    let s3 = mp(
        ray(pa.clone(), pc.clone(), cp.clone()),
        eq(ang_bacp.clone(), ang_bac.clone()),
        s1.clone(),
        rax,
    );
    // s4 : |- m b a Cp = m f e g     (eqtr s3, H1)
    let ang_feg = ang(pf.clone(), pe.clone(), pg.clone());
    let s4 = eqtr3(
        ang_bacp.clone(),
        ang_bac.clone(),
        ang_feg.clone(),
        s3,
        leaf("asa.h1"),
    );
    // post-sas with c := Cp
    let sas = el
        .app(
            "post-sas",
            &[
                ("a", pa.clone()), ("b", pb.clone()), ("c", cp.clone()),
                ("e", pe.clone()), ("f", pf.clone()), ("g", pg.clone()),
            ],
            &[],
        )
        .unwrap();
    let ang_abcp = ang(pa.clone(), pb.clone(), cp.clone());
    let ang_abc = ang(pa.clone(), pb.clone(), pc.clone());
    let ang_efg = ang(pe.clone(), pf.clone(), pg.clone());
    // chain: mp H2 -> mp s4 -> mp s2  giving |- m a b Cp = m e f g
    let t1 = mp(
        eq(dist(pa.clone(), pb.clone()), dist(pe.clone(), pf.clone())),
        wi(
            eq(ang_bacp.clone(), ang_feg.clone()),
            wi(eq(dist(pa.clone(), cp.clone()), len.clone()), eq(ang_abcp.clone(), ang_efg.clone())),
        ),
        leaf("asa.h2"),
        sas,
    );
    let t2 = mp(
        eq(ang_bacp.clone(), ang_feg.clone()),
        wi(eq(dist(pa.clone(), cp.clone()), len.clone()), eq(ang_abcp.clone(), ang_efg.clone())),
        s4,
        t1,
    );
    let t3 = mp(
        eq(dist(pa.clone(), cp.clone()), len.clone()),
        eq(ang_abcp.clone(), ang_efg.clone()),
        s2.clone(),
        t2,
    ); // |- m a b Cp = m e f g

    // H3 reversed: |- m e f g = m a b c
    let h3rev = mp(
        eq(ang_abc.clone(), ang_efg.clone()),
        eq(ang_efg.clone(), ang_abc.clone()),
        leaf("asa.h3"),
        el.app("eqcom", &[("x", ang_abc.clone()), ("y", ang_efg.clone())], &[]).unwrap(),
    );
    // s6 : |- m a b Cp = m a b c
    let s6 = eqtr3(ang_abcp.clone(), ang_efg.clone(), ang_abc.clone(), t3, h3rev);
    // ax-prot-uniq : |- ( m a b Cp = m a b c -> Ray b c Cp ) ; mp s6
    let prot = el
        .app(
            "ax-prot-uniq",
            &[("a", pa.clone()), ("b", pb.clone()), ("x", cp.clone()), ("c", pc.clone())],
            &[],
        )
        .unwrap();
    let s7 = mp(
        eq(ang_abcp.clone(), ang_abc.clone()),
        ray(pb.clone(), pc.clone(), cp.clone()),
        s6,
        prot,
    ); // |- ( Ray b c Cp )
    // s8 : |- ( On Cp ( Ln a c ) )
    let rl1 = el
        .app("ax-rayline", &[("a", pa.clone()), ("c", pc.clone()), ("x", cp.clone())], &[])
        .unwrap();
    let s8 = mp(
        ray(pa.clone(), pc.clone(), cp.clone()),
        on(cp.clone(), pa.clone(), pc.clone()),
        s1.clone(),
        rl1,
    );
    // s9 : |- ( On Cp ( Ln b c ) )
    let rl2 = el
        .app("ax-rayline", &[("a", pb.clone()), ("c", pc.clone()), ("x", cp.clone())], &[])
        .unwrap();
    let s9 = mp(
        ray(pb.clone(), pc.clone(), cp.clone()),
        on(cp.clone(), pb.clone(), pc.clone()),
        s7,
        rl2,
    );
    // post-incid : Tri a b c -> ( On Cp(Ln a c) -> ( On Cp(Ln b c) -> Cp = c ) )
    let inc = el
        .app(
            "post-incid",
            &[("a", pa.clone()), ("b", pb.clone()), ("c", pc.clone()), ("x", cp.clone())],
            &[],
        )
        .unwrap();
    let i1 = mp(
        tri(pa.clone(), pb.clone(), pc.clone()),
        wi(
            on(cp.clone(), pa.clone(), pc.clone()),
            wi(on(cp.clone(), pb.clone(), pc.clone()), eq(cp.clone(), pc.clone())),
        ),
        leaf("asa.ht"),
        inc,
    );
    let i2 = mp(
        on(cp.clone(), pa.clone(), pc.clone()),
        wi(on(cp.clone(), pb.clone(), pc.clone()), eq(cp.clone(), pc.clone())),
        s8,
        i1,
    );
    let i3 = mp(
        on(cp.clone(), pb.clone(), pc.clone()),
        eq(cp.clone(), pc.clone()),
        s9,
        i2,
    ); // |- Cp = c
    // c = Cp
    let c_eq_cp = mp(
        eq(cp.clone(), pc.clone()),
        eq(pc.clone(), cp.clone()),
        i3,
        el.app("eqcom", &[("x", cp.clone()), ("y", pc.clone())], &[]).unwrap(),
    );
    // ax-dcong : ( c = Cp -> d a c = d a Cp ) ; mp -> |- d a c = d a Cp
    let dcong = el
        .app("ax-dcong", &[("x", pc.clone()), ("y", cp.clone()), ("a", pa.clone())], &[])
        .unwrap();
    let s11 = mp(
        eq(pc.clone(), cp.clone()),
        eq(dist(pa.clone(), pc.clone()), dist(pa.clone(), cp.clone())),
        c_eq_cp,
        dcong,
    );
    // ASA : |- d a c = d e g    (eqtr s11, s2)
    let asa_goal = eqtr3(
        dist(pa.clone(), pc.clone()),
        dist(pa.clone(), cp.clone()),
        len.clone(),
        s11,
        s2.clone(),
    );

    let toks = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    let asa = Lemma {
        name: "ASA".into(),
        ess: vec![
            ("asa.h1".into(), toks(&["|-", "m", "b", "a", "c", "=", "m", "f", "e", "g"])),
            ("asa.h2".into(), toks(&["|-", "d", "a", "b", "=", "d", "e", "f"])),
            ("asa.h3".into(), toks(&["|-", "m", "a", "b", "c", "=", "m", "e", "f", "g"])),
            ("asa.ht".into(), toks(&["|-", "(", "Tri", "a", "b", "c", ")"])),
        ],
        goal: asa_goal,
    };

    // ---- assemble everything and let the kernel judge -------------------
    let asa_locals: std::collections::HashMap<String, Vec<String>> =
        asa.ess.iter().cloned().collect();
    match el.conclusion_l(&asa.goal, &asa_locals) {
        Ok(c) => println!("  ASA goal : {}", c.join(" ")),
        Err(e) => die("conclusion(ASA)", e),
    }
    let lemmas = vec![eqtr, asa];
    let full_src = assemble(&base, &db1, &lemmas).unwrap_or_else(|e| die("assemble", e));
    std::fs::write("data/birkhoff.out.mm", &full_src).ok();
    let full = kernel::Db::parse(&full_src).unwrap_or_else(|e| die("final parse", e));
    match full.verify() {
        Ok(()) => println!(
            "Kernel: verified eqtr + ASA ✔  (full db: {} statements)",
            full.stmts.len()
        ),
        Err(e) => die("KERNEL REJECTED", e),
    }

    // ---- exact F0 geometry-layer count (kernel-verified proof) ----------
    let mut memo = HashMap::new();
    let (total, hist) = expand(&full, "ASA", &mut memo);
    println!(
        "\n=== F0 geometry layer: exact fully-inlined axiom invocations ===\n\
         ASA cut-free $a-invocations : {}",
        total.pretty()
    );
    let mut rows: Vec<(String, ProofSize)> = hist.into_iter().collect();
    rows.sort_by(|a, b| b.1.log10().partial_cmp(&a.1.log10()).unwrap());
    println!("  anatomy (which primitive axioms carry the mass):");
    for (ax, n) in &rows {
        println!("    {:<16} ×{}", ax, n.pretty());
    }
    println!(
        "\nNote: no ordered-field (L3) axiom appears — ASA over Birkhoff is\n\
         pure FOL+equality+postulates. The ℝ substrate enters only through the\n\
         typing of d / m as real terms; that cost is the set.mm splice (task 4)."
    );
}
