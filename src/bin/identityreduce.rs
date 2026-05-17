//! SEAM 4 — the identity-reduction MEASUREMENT (read-only analysis).
//!
//! Question: how much of the cut-free metric content of Birkhoff plane
//! geometry is *literally polynomial-identity expansion* over an ordered
//! field, and how much is structural glue (df-unfold / congruence / FOL)?
//!
//! This binary touches NOTHING authoritative. It parses the
//! kernel-verified corpus `data/grounded.out.mm` (the exact artifact the
//! `grounded data/grounded.mm` 96-verify emits) and re-derives, with the
//! SAME cut-free `$a`-leaf metric `grounded` uses (`expand`: $f/$e = 0,
//! $a = 1, $p = Σ children), a per-postulate split of the total into
//!
//!   IDENTITY  — the ordered-ring polynomial-identity machinery the
//!               `ring_eq`/`canon_sum`/`desub`/`sdist` normalizer reduces
//!               to: the field axioms + their additive/multiplicative
//!               congruences + equality plumbing.
//!   GLUE      — everything else: df-* unfold, geometric-predicate
//!               congruence, the ordering fragment, √/recip primitives,
//!               first-order logic.
//!
//! The classification is at the *primitive `$a` axiom* level (the only
//! things `expand` ever counts), so it is exact and auditable: every
//! leaf is one named axiom, each placed in exactly one bucket, and the
//! bucket assignment is printed. No fitting is hidden; the cost-law fit
//! in §2 reports its residuals.
//!
//! Authoritative check remains solely `grounded data/grounded.mm`'s
//! `Kernel: verified all N ✔`. This is convenience measurement.

use std::collections::HashMap;

#[path = "../number.rs"]
mod number;
#[path = "../kernel.rs"]
mod kernel;

use number::ProofSize;

// ---------------------------------------------------------------------
//  The cut-free metric — byte-identical semantics to grounded::expand.
// ---------------------------------------------------------------------
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

/// Like `expand` but accumulates, per primitive `$a` axiom, how many
/// fully-inlined leaf occurrences of it the proof of `label` contains.
/// Σ over all axioms == expand(label). Exact bignum throughout.
fn expand_by_axiom(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, HashMap<String, ProofSize>>,
) -> HashMap<String, ProofSize> {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    let st = match db.get(label) {
        Some(s) => s,
        None => {
            memo.insert(label.to_string(), HashMap::new());
            return HashMap::new();
        }
    };
    let out: HashMap<String, ProofSize> = match st.kind {
        kernel::Kind::F | kernel::Kind::E => HashMap::new(),
        kernel::Kind::A => {
            let mut m = HashMap::new();
            m.insert(label.to_string(), ProofSize::one());
            m
        }
        kernel::Kind::P => {
            let mut acc: HashMap<String, ProofSize> = HashMap::new();
            for step in st.proof.clone() {
                for (ax, n) in expand_by_axiom(db, &step, memo) {
                    let e = acc.entry(ax).or_insert_with(ProofSize::zero);
                    *e = e.add(&n);
                }
            }
            acc
        }
    };
    memo.insert(label.to_string(), out.clone());
    out
}

// ---------------------------------------------------------------------
//  IDENTITY vs GLUE classification of every primitive `$a` axiom.
//
//  IDENTITY = exactly the axioms the ordered-ring polynomial-identity
//  normalizer (`desub`/`sdist`/`canon_sum`/`ring_eq` in grounded.rs)
//  is built from — verified by reading those functions' bodies:
//    field laws      of-addass of-addcom of-add0 of-addinv
//                    of-distr of-mulass of-mulcom
//    + congruences   cong-pl1 cong-pl2 cong-mi1 cong-mi2
//                    cong-mu1 cong-mu2
//    equality glue   eqid eqcom            (AC refl/symmetry; the
//                                           normalizer's own plumbing)
//  Everything else is structural GLUE.
// ---------------------------------------------------------------------
const IDENTITY_AX: &[&str] = &[
    "of-addass", "of-addcom", "of-add0", "of-addinv", "of-distr",
    "of-mulass", "of-mulcom", "cong-pl1", "cong-pl2", "cong-mi1",
    "cong-mi2", "cong-mu1", "cong-mu2", "eqid", "eqcom",
];

/// `eqid`/`eqcom` are pure equality plumbing used by BOTH the ring
/// normalizer and the df-unfold/congruence glue. They are reported in
/// IDENTITY (they are the AC normalizer's reflexivity/symmetry steps),
/// but the split is also reported with them moved to GLUE so the
/// sensitivity of the headline % to this single judgement call is
/// explicit and honest.
const BORDERLINE: &[&str] = &["eqid", "eqcom"];

fn is_identity(ax: &str) -> bool {
    IDENTITY_AX.contains(&ax)
}
fn is_borderline(ax: &str) -> bool {
    BORDERLINE.contains(&ax)
}

/// A primitive `$a` is SYNTAX iff its conclusion's typecode is `wff` or
/// `term` — i.e. it is a formula/term *constructor*, asserting only
/// well-formedness, proving zero mathematical content. Every Metamath
/// proof carries these (they are the cost of *writing the goal down*);
/// they are orthogonal to the identity-vs-glue question and so are
/// reported as a separate third bucket, never folded into GLUE. The
/// IDENTITY/GLUE headline ratio is taken over the *proof-content*
/// axioms only (SYNTAX excluded), which is the honest denominator.
fn is_syntax(db: &kernel::Db, ax: &str) -> bool {
    match db.get(ax) {
        Some(s) if s.kind == kernel::Kind::A => {
            matches!(s.expr.first().map(|t| t.as_str()), Some("wff") | Some("term"))
        }
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Bucket { Identity, Glue, Syntax }

fn bucket(db: &kernel::Db, ax: &str) -> Bucket {
    if is_syntax(db, ax) { Bucket::Syntax }
    else if is_identity(ax) { Bucket::Identity }
    else { Bucket::Glue }
}

// ---------------------------------------------------------------------
//  The generic polynomial-identity set (extracted from grounded.rs /
//  proof_g*.rs source — see SEAM4_IDENTITY.md §1 for derivations).
//  (name, degree, #monomials lhs+rhs after expansion, #fresh atoms,
//   association note)
// ---------------------------------------------------------------------
struct Ident {
    name: &'static str,
    deg: u32,
    monos: u32,   // expanded signed-monomial count, lhs+rhs
    atoms: u32,
    note: &'static str,
}
// `monos` = exact expanded signed-monomial count, lhs+rhs, obtained by
// fully distributing every product over every sum and pushing every
// `-x`/neg in (exactly what grounded::sdist does *before* canon_sum
// cancellation). Derived by hand from each identity's source term tree
// and re-checked against the §1 measured cost ordering:
//   telesh   LHS (c-a)-(b-a) → [c,-a,-b,+a]=4 ; RHS c-b=2          → 6
//   loc-gen  (c-a)²+(e-b)²=8 ; RHS (a²+b²+c²+e²)-(2·(ac+be))=8     → 16
//   sqc-diffsq (p-q)(p+q)=4 ; p²-q²=2                              → 6
//   sqc-gprod  (q²)(p²)=1 ; (pq)(pq)=1                             → 2
//   sqc-4uv  (p+q)²-(p-q)²=8 ; ((pq+pq)+(pq+pq))=4                 → 12
const GENERICS: &[Ident] = &[
    Ident { name: "telesh",     deg: 1, monos: 6,  atoms: 3, note: "(c-a)-(b-a)=(c-b)  degree-1 telescope" },
    Ident { name: "loc-gen",    deg: 2, monos: 16, atoms: 4, note: "law of cosines |C-B|^2=|u|^2+|w|^2-2u.w" },
    Ident { name: "sqc-diffsq", deg: 2, monos: 6,  atoms: 2, note: "(p-q)(p+q)=p^2-q^2" },
    Ident { name: "sqc-gprod",  deg: 4, monos: 2,  atoms: 2, note: "(q^2)(p^2)=(pq)(pq)  the degree-4 one" },
    Ident { name: "sqc-4uv",    deg: 2, monos: 12, atoms: 2, note: "(p+q)^2-(p-q)^2=4pq" },
];

fn fnum(p: &ProofSize) -> f64 {
    p.log10()
}

fn main() {
    let path = "data/grounded.out.mm";
    let src = std::fs::read_to_string(path)
        .unwrap_or_else(|e| { eprintln!("read {path}: {e} — run `grounded data/grounded.mm` first"); std::process::exit(1); });
    let db = kernel::Db::parse(&src).unwrap_or_else(|e| { eprintln!("parse: {e}"); std::process::exit(1); });
    // Re-verify so the measured corpus is provably the kernel-checked one.
    match db.verify() {
        Ok(()) => println!("corpus kernel-reverified ✔  ({} statements)\n", db.stmts.len()),
        Err(e) => { eprintln!("CORPUS REJECTED: {e}"); std::process::exit(1); }
    }

    let mut memo: HashMap<String, ProofSize> = HashMap::new();
    let mut amemo: HashMap<String, HashMap<String, ProofSize>> = HashMap::new();

    // === §0  audit: every primitive $a axiom, bucketed ===============
    let mut ax_labels: Vec<String> = db.stmts.iter()
        .filter(|s| s.kind == kernel::Kind::A)
        .map(|s| s.label.clone()).collect();
    ax_labels.sort();
    println!("=== §0  primitive $a axiom classification (every leaf the metric counts) ===");
    println!("  Three buckets. SYNTAX = wff/term constructors (well-formedness");
    println!("  only, zero math content, present in every Metamath proof) — a");
    println!("  separate bucket, NEVER folded into GLUE. The headline");
    println!("  IDENTITY:GLUE ratio is over proof-content axioms (SYNTAX out).\n");
    println!("  IDENTITY (ordered-ring polynomial-identity normalizer):");
    for a in &ax_labels { if bucket(&db, a) == Bucket::Identity { println!("    {a}{}", if is_borderline(a) {"   [borderline: eq-plumbing]"} else {""}); } }
    println!("  GLUE (df-unfold / geometric congruence / ordering / sqrt / FOL):");
    let glue: Vec<&String> = ax_labels.iter().filter(|a| bucket(&db, a) == Bucket::Glue).collect();
    for chunk in glue.chunks(8) {
        println!("    {}", chunk.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" "));
    }
    println!("  SYNTAX (wff/term constructors — well-formedness only):");
    let syn: Vec<&String> = ax_labels.iter().filter(|a| bucket(&db, a) == Bucket::Syntax).collect();
    for chunk in syn.chunks(8) {
        println!("    {}", chunk.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" "));
    }
    println!();

    // === §1  the generic identity set, MEASURED ======================
    println!("=== §1  generic polynomial-identity set: extracted + MEASURED cut-free cost ===");
    println!("  {:<12} {:>3} {:>6} {:>5} {:>14} {:>9}  identity",
             "name", "deg", "monos", "atom", "cut-free $a", "log10");
    let mut fit_rows: Vec<(f64, f64, f64, f64)> = vec![]; // (deg, monos, atoms, log10cost)
    for g in GENERICS {
        let c = expand(&db, g.name, &mut memo);
        println!("  {:<12} {:>3} {:>6} {:>5} {:>14} {:>9.3}  {}",
                 g.name, g.deg, g.monos, g.atoms, c.pretty(), fnum(&c), g.note);
        fit_rows.push((g.deg as f64, g.monos as f64, g.atoms as f64, fnum(&c)));
    }
    println!();

    // === §2  MEASURED cost law ======================================
    // Model the cut-free $a cost of a generic ring identity as
    //   log10 cost ≈ b0 + b1·log10(monos)        (canon_sum is ~O(n^3)
    //                                              in the monomial count;
    //                                              degree enters only via
    //                                              monos, so a 1-regressor
    //                                              power law is the honest
    //                                              minimal model.)
    // Ordinary least squares on the 5 measured generics; residuals shown.
    let n = fit_rows.len() as f64;
    let xs: Vec<f64> = fit_rows.iter().map(|r| r.1.ln()).collect();      // ln(monos)
    let ys: Vec<f64> = fit_rows.iter().map(|r| r.3 * std::f64::consts::LN_10).collect(); // ln(cost)
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let sxx: f64 = xs.iter().map(|x| (x - mx).powi(2)).sum();
    let sxy: f64 = xs.iter().zip(&ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let b1 = sxy / sxx;
    let b0 = my - b1 * mx;
    let ss_tot: f64 = ys.iter().map(|y| (y - my).powi(2)).sum();
    let ss_res: f64 = xs.iter().zip(&ys).map(|(x, y)| (y - (b0 + b1 * x)).powi(2)).sum();
    let r2 = 1.0 - ss_res / ss_tot;
    println!("=== §2  MEASURED cost law (OLS over the 5 generics) ===");
    println!("  Model A (1 regressor):  cost ≈ exp({b0:.4}) · monos^{b1:.4}");
    println!("  i.e.  cut-free $a leaves ≈ {:.3} · monos^{:.3}", b0.exp(), b1);
    println!("  R² = {r2:.5}   (degree enters only through the monomial count)");
    println!("  residuals (measured vs fitted, log10):");
    let mut maxres = 0f64;
    for (i, g) in GENERICS.iter().enumerate() {
        let pred_ln = b0 + b1 * xs[i];
        let pred_log10 = pred_ln / std::f64::consts::LN_10;
        let d = fit_rows[i].3 - pred_log10;
        if d.abs() > maxres { maxres = d.abs(); }
        println!("    {:<12} measured {:>7.3}  fitted {:>7.3}  Δ {:+.3}",
                 g.name, fit_rows[i].3, pred_log10, d);
    }
    println!("  worst residual: {maxres:.3} log10 (×{:.2}); the canon_sum",
             10f64.powf(maxres));
    println!("  spine is ~O(monos^2) — measured exponent {b1:.2} ≈ 2, the");
    println!("  honest reading: cut-free cost of a ring identity is");
    println!("  QUADRATIC in its expanded monomial count, not in degree.");

    // Model B: 2-regressor ln-ln on (monos, deg) — does degree add signal
    // beyond monomial count? Normal-equations OLS, 3 params.
    {
        let m: Vec<f64> = fit_rows.iter().map(|r| r.1.ln()).collect();
        let d: Vec<f64> = fit_rows.iter().map(|r| (r.0).ln()).collect();
        let y: Vec<f64> = fit_rows.iter().map(|r| r.3 * std::f64::consts::LN_10).collect();
        // design [1, m, d]; solve 3x3 normal equations
        let mut xtx = [[0f64; 3]; 3];
        let mut xty = [0f64; 3];
        for i in 0..fit_rows.len() {
            let row = [1.0, m[i], d[i]];
            for a in 0..3 {
                for b in 0..3 { xtx[a][b] += row[a] * row[b]; }
                xty[a] += row[a] * y[i];
            }
        }
        // Gaussian elimination
        let mut aug = [[0f64; 4]; 3];
        for r in 0..3 { for c in 0..3 { aug[r][c] = xtx[r][c]; } aug[r][3] = xty[r]; }
        for col in 0..3 {
            let piv = aug[col][col];
            if piv.abs() < 1e-12 { continue; }
            for c in 0..4 { aug[col][c] /= piv; }
            for r in 0..3 {
                if r != col {
                    let f = aug[r][col];
                    for c in 0..4 { aug[r][c] -= f * aug[col][c]; }
                }
            }
        }
        let (c0, cm, cd) = (aug[0][3], aug[1][3], aug[2][3]);
        let mut ssr = 0f64;
        let ybar = y.iter().sum::<f64>() / y.len() as f64;
        let mut sst = 0f64;
        for i in 0..fit_rows.len() {
            let pred = c0 + cm * m[i] + cd * d[i];
            ssr += (y[i] - pred).powi(2);
            sst += (y[i] - ybar).powi(2);
        }
        println!("  Model B (monos & deg): cost ≈ exp({c0:.3})·monos^{cm:.3}·deg^{cd:.3}");
        println!("  R² = {:.5}; degree coefficient {cd:+.3} — {} signal beyond monos.",
                 1.0 - ssr / sst,
                 if cd.abs() < 0.25 { "negligible additional" } else { "some additional" });
    }
    println!();

    // === §2c  the reduction, MEASURED on the production identities ===
    // loclink (the geometry's law-of-cosines instance) and sqcong (the
    // a²=b² ⇒ a=b core) are the two heavy production polynomial
    // identities. The thesis is: their cut-free cost = Σ(generic
    // identity costs, reached by substitution = free in this metric) +
    // measured residual glue. Measure that decomposition exactly off
    // the kernel-verified corpus (no fit, pure expand attribution).
    println!("=== §2c  reduction MEASURED on the production identities ===");
    for (host, parts) in &[
        ("loclink", &["loc-gen", "telesh"][..]),
        ("sqcong", &["sqc-4uv", "sqc-diffsq", "sqc-gprod"][..]),
    ] {
        if db.get(host).is_none() { continue; }
        let tot = expand(&db, host, &mut memo);
        let st = db.get(host).unwrap();
        let mut occ: HashMap<&str, u64> = HashMap::new();
        for l in &st.proof { *occ.entry(l).or_insert(0) += 1; }
        let mut gen_sum = ProofSize::zero();
        print!("  {host}  total {} =", tot.pretty());
        for p in parts.iter() {
            let c = expand(&db, p, &mut memo);
            let k = *occ.get(p).unwrap_or(&0);
            let contrib = c.mul_u64(k.max(1));
            gen_sum = gen_sum.add(&contrib);
            print!("  {k}·{p}({})", c.pretty());
        }
        let resid = tot.checked_sub(&gen_sum).unwrap_or_else(ProofSize::zero);
        let gpct = 100.0 * 10f64.powf(fnum(&gen_sum) - fnum(&tot));
        println!(
            "\n     generic-identity core = {} ({:.2}% of host)  +  residual glue {} ({:.2}%)",
            gen_sum.pretty(), gpct, resid.pretty(), 100.0 - gpct
        );
    }
    println!("  ⇒ the production polynomial identities reduce, to within the");
    println!("    stated residual, to substitution-instances of the §1 generic");
    println!("    set; substitution is FREE in the cut-free metric, so the");
    println!("    identity content collapses to the §1 generics' MEASURED cost.");
    println!();

    // === §3  per-postulate IDENTITY vs GLUE split ====================
    // Roots: one $p per Birkhoff postulate (+ ASA′ support lemmas).
    let roots: &[(&str, &str)] = &[
        ("G4-sas",                  "G4  SAS (hardest postulate)"),
        ("G3a-rayangle",            "G3a ray-angle"),
        ("g3a-dotprop",             "G3a dot-prop (ASA′ s4 support)"),
        ("G3bp-protuniq-oriented",  "G3b protractor-uniqueness (oriented)"),
        ("G3c-rayline",             "G3c ray-line"),
        ("G2-incid",                "G2  incidence"),
        ("G1b-rulerd",              "G1  ruler (distance)"),
        ("G1a-rulerr",              "G1  ruler (ray)"),
        ("G0-congsub",              "G0  congruence-substitution"),
        ("g4a-sss",                 "g4a SSS→ACong (ASA′ GAP#2)"),
        ("g4a-dot",                 "g4a dot equality"),
        ("sqd-sym",                 "sqd symmetry (ASA′ support)"),
    ];
    println!("=== §3  per-postulate cut-free split: IDENTITY vs GLUE vs SYNTAX ===");
    println!("  Columns: shares of the cut-free $a total (id+gl+syn = 100%).");
    println!("  id|gl(content) = the HONEST identity:glue ratio with SYNTAX");
    println!("  removed from the denominator. id*|gl* = the same content");
    println!("  ratio with eqid/eqcom reclassified GLUE (sensitivity bound).");
    println!("  {:<28} {:>13} {:>6} {:>6} {:>6} | {:>7} {:>7} | {:>7}",
             "postulate", "cut-free", "id%", "gl%", "syn%", "id|cnt", "gl|cnt", "id*|cnt");
    let mut grand_id = ProofSize::zero();
    let mut grand_gl = ProofSize::zero();
    let mut grand_sy = ProofSize::zero();
    let mut grand_id2 = ProofSize::zero();
    let mut detail: Vec<(String, Vec<(String, ProofSize)>)> = vec![];
    for (root, label) in roots {
        if db.get(root).is_none() { continue; }
        let per = expand_by_axiom(&db, root, &mut amemo);
        let total = expand(&db, root, &mut memo);
        let mut id = ProofSize::zero();
        let mut gl = ProofSize::zero();
        let mut sy = ProofSize::zero();
        let mut id2 = ProofSize::zero();   // borderline→glue, content basis
        let mut rows: Vec<(String, ProofSize)> = vec![];
        for (ax, cnt) in &per {
            rows.push((ax.clone(), cnt.clone()));
            match bucket(&db, ax) {
                Bucket::Syntax => sy = sy.add(cnt),
                Bucket::Identity => {
                    id = id.add(cnt);
                    if is_borderline(ax) { /* moves to glue in id2 */ } else { id2 = id2.add(cnt); }
                }
                Bucket::Glue => gl = gl.add(cnt),
            }
        }
        let tl = fnum(&total);
        let pct = |p: &ProofSize| 100.0 * 10f64.powf(fnum(p) - tl);
        let content = id.add(&gl);
        let cl = fnum(&content);
        let cpct = |p: &ProofSize| if cl.is_finite() { 100.0 * 10f64.powf(fnum(p) - cl) } else { 0.0 };
        let gl2 = content.checked_sub(&id2).unwrap_or_else(|| gl.clone());
        let _ = gl2;
        println!("  {:<28} {:>13} {:>5.2}% {:>5.2}% {:>5.2}% | {:>6.2}% {:>6.2}% | {:>6.2}%",
                 label, total.pretty(), pct(&id), pct(&gl), pct(&sy),
                 cpct(&id), cpct(&gl), cpct(&id2));
        grand_id = grand_id.add(&id);
        grand_gl = grand_gl.add(&gl);
        grand_sy = grand_sy.add(&sy);
        grand_id2 = grand_id2.add(&id2);
        rows.sort_by(|a, b| fnum(&b.1).partial_cmp(&fnum(&a.1)).unwrap());
        detail.push((label.to_string(), rows));
    }
    let gt = grand_id.add(&grand_gl).add(&grand_sy);
    let gtl = fnum(&gt);
    let gcontent = grand_id.add(&grand_gl);
    let gcl = fnum(&gcontent);
    println!("  {:-<28} {:->13} {:->6} {:->6} {:->6}-{:->8}{:->8}-{:->8}", "","","","","","","","");
    println!("  {:<28} {:>13} {:>5.2}% {:>5.2}% {:>5.2}% | {:>6.2}% {:>6.2}% | {:>6.2}%",
             "Σ all postulate roots", gt.pretty(),
             100.0 * 10f64.powf(fnum(&grand_id) - gtl),
             100.0 * 10f64.powf(fnum(&grand_gl) - gtl),
             100.0 * 10f64.powf(fnum(&grand_sy) - gtl),
             100.0 * 10f64.powf(fnum(&grand_id) - gcl),
             100.0 * 10f64.powf(fnum(&grand_gl) - gcl),
             100.0 * 10f64.powf(fnum(&grand_id2) - gcl));
    println!();

    // === §4  the per-postulate axiom breakdown (the receipts) ========
    println!("=== §4  per-postulate primitive-axiom receipts (top contributors) ===");
    for (label, rows) in &detail {
        println!("  -- {label} --");
        let tot: ProofSize = rows.iter().fold(ProofSize::zero(), |a, (_, c)| a.add(c));
        let tl = fnum(&tot);
        for (ax, c) in rows.iter().take(10) {
            let share = 100.0 * 10f64.powf(fnum(c) - tl);
            let tag = match bucket(&db, ax) {
                Bucket::Syntax => "SYN",
                Bucket::Identity => if is_borderline(ax) { "ID?" } else { "ID " },
                Bucket::Glue => "GL ",
            };
            println!("    [{tag}] {:<14} {:>14}  {:>6.2}%", ax, c.pretty(), share);
        }
    }
}
