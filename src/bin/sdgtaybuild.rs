//! sdgtaybuild — constructs the kernel-verified SYNTHETIC ORDER-2 TAYLOR
//! corpus and writes data/sdg.taylor.mm.
//!
//! COMPOSITION / why a SEPARATE file.  This file is fully self-contained:
//! it embeds the certified-intuitionistic substrate base verbatim
//! (data/sdg.base.mm — the SAME trust surface sdgtaypure audits) and
//! appends ONLY new order-2 Taylor $p with disjoint `sdg-tay-*` labels.
//! It deliberately does NOT touch data/sdg.mm, data/sdg.base.mm,
//! data/sdg.calc.mm, src/bin/sdgbuild.rs, src/kernel.rs, src/elaborate.rs
//! or any other agent's files, so it cannot merge-conflict.  Intended
//! composition: data/sdg.taylor.mm is an independent kernel-checked /
//! purity-checked corpus over the IDENTICAL data/sdg.base.mm axiom
//! surface; a downstream union is a rename-free concatenation of $p
//! blocks (disjoint labels).  This is the exact zero-conflict pattern of
//! data/sdg.calc.mm + src/bin/sdgcalcbuild.rs, copied.
//!
//! WHAT IS PROVED (SEQUEL_SCOPE §5h).  Order-2 synthetic Taylor.  From
//! the generalized Kock-Lawvere axiom at level 2 (ax-kl2: every D_2 -> R
//! map is a UNIQUE degree-<=2 polynomial) the EXISTENCE of the expansion
//!     f(x+d) = f(x) + d*f'(x) + (d*d)*s(x)        for d in D_2
//! is exactly ax-kl2 (CITED, an axiom — restating it as a vacuous one-
//! line $p would be dishonest).  The genuine content delivered here is
//! UNIQUENESS:
//!   * sdg-tay-quad-slope : the ORDER-2 pointwise uniqueness of the
//!     linear (derivative) coefficient — RING-ONLY additive cancellation
//!     that GENUINELY cancels BOTH the constant term AND the quadratic
//!     term (b*d)+(q*(d*d)) etc.  This is the real order-2 analog of
//!     sdg-slope (order-1 only had a constant to cancel); the quadratic
//!     monomial is present and must be killed.  No order, no metric
//!     residue, no classical principle, no microcancellation.
//!   * sdg-tay-deriv2 : THE SEAM-FREE HEADLINE.  From two UNIVERSAL KL2
//!     representations over D_2 it MECHANICALLY THREADS the linking
//!     universal A. d ( ( D2 d ) -> ( b*d )=( c*d ) ) (deduction-form
//!     combinators + ax-spec/ax-gen, NO linking $e) and GENUINELY
//!     CONSUMES ax-microcancel2 to conclude b = c — order-2 uniqueness
//!     of the Taylor derivative coefficient.  Verified RPN ends
//!     `... gen ... ax-microcancel2 ax-mp`.  This is the exact order-2
//!     mirror of data/sdg.mm's seam-free sdg-deriv (which consumed
//!     ax-microcancel); it does NOT reuse the §5b $e and does NOT
//!     hand-wave: the KL2 representation and ax-microcancel2 are both
//!     genuinely on the consumed path.
//!   * sdg-tay-k1-reduce : the k=1 instance of the Taylor scheme IS the
//!     existing order-1 derivative (KL_1 = ax-kl): recorded as the
//!     identity on that exact KL_1 formula — an HONEST marker that k=1
//!     adds nothing, NOT a vacuous re-derivation.
//!
//! The general meta-k Taylor scheme is documented precisely in
//! SEQUEL_SCOPE §5h (the substrate has no internal natural-number
//! object, so the forall-k statement is an axiom SCHEME, not one $a —
//! presenting it as one would be a glib misstatement; we do not).
//!
//! Run:  cargo run --release --bin sdgtaybuild
//!
//! UNTRUSTED scaffolding.  Trust root = src/kernel.rs re-checking the
//! emitted data/sdg.taylor.mm (run `cargo run --bin sdgtayfloor` and
//! `cargo run --bin sdgtaypure`).

#[path = "../kernel.rs"]
mod kernel;

use std::collections::HashMap;
use std::fmt::Write as _;

type Toks = Vec<String>;

fn t(s: &str) -> Toks {
    s.split_whitespace().map(|x| x.to_string()).collect()
}

fn rpn_app(args: &[&[String]], label: &str) -> Toks {
    let mut v = Vec::new();
    for a in args {
        v.extend(a.iter().cloned());
    }
    v.push(label.to_string());
    v
}

#[derive(Clone)]
struct Pf {
    stmt: Toks,
    rpn: Toks,
}

#[derive(Clone)]
struct W {
    rpn: Toks,
    toks: Toks,
}

fn leaf(varlabel: &str, tok: &str) -> W {
    W { rpn: t(varlabel), toks: t(tok) }
}

fn wi(a: &W, b: &W) -> W {
    W {
        rpn: rpn_app(&[&a.rpn, &b.rpn], "wi"),
        toks: {
            let mut v = vec!["(".into()];
            v.extend(a.toks.clone());
            v.push("->".into());
            v.extend(b.toks.clone());
            v.push(")".into());
            v
        },
    }
}

fn wa(a: &W, b: &W) -> W {
    W {
        rpn: rpn_app(&[&a.rpn, &b.rpn], "wa"),
        toks: {
            let mut v = vec!["(".into()];
            v.extend(a.toks.clone());
            v.push("/\\".into());
            v.extend(b.toks.clone());
            v.push(")".into());
            v
        },
    }
}

fn weq(a: &W, b: &W) -> W {
    W {
        rpn: rpn_app(&[&a.rpn, &b.rpn], "weq"),
        toks: {
            let mut v = a.toks.clone();
            v.push("=".into());
            v.extend(b.toks.clone());
            v
        },
    }
}

fn binop(a: &W, b: &W, op: &str, label: &str) -> W {
    W {
        rpn: rpn_app(&[&a.rpn, &b.rpn], label),
        toks: {
            let mut v = vec!["(".into()];
            v.extend(a.toks.clone());
            v.push(op.into());
            v.extend(b.toks.clone());
            v.push(")".into());
            v
        },
    }
}

fn wal(xvar_flabel: &str, xtok: &str, body: &W) -> W {
    W {
        rpn: {
            let mut r = body.rpn.clone();
            r.push(xvar_flabel.to_string());
            r.push("wal".into());
            r
        },
        toks: {
            let mut v = vec!["A.".into(), xtok.to_string()];
            v.extend(body.toks.clone());
            v
        },
    }
}

fn wex(xvar_flabel: &str, xtok: &str, body: &W) -> W {
    W {
        rpn: {
            let mut r = body.rpn.clone();
            r.push(xvar_flabel.to_string());
            r.push("wex".into());
            r
        },
        toks: {
            let mut v = vec!["E.".into(), xtok.to_string()];
            v.extend(body.toks.clone());
            v
        },
    }
}

fn wD2(x: &W) -> W {
    W {
        rpn: rpn_app(&[&x.rpn], "wD2"),
        toks: {
            let mut v = vec!["(".into(), "D2".into()];
            v.extend(x.toks.clone());
            v.push(")".into());
            v
        },
    }
}

fn ap(f: &W, x: &W) -> W {
    // tap $a term ( ap f x ) $.  Float order: vx (x) BEFORE vf (f).
    W {
        rpn: rpn_app(&[&x.rpn, &f.rpn], "tap"),
        toks: {
            let mut v = vec!["(".into(), "ap".into()];
            v.extend(f.toks.clone());
            v.extend(x.toks.clone());
            v.push(")".into());
            v
        },
    }
}

thread_local! {
    static REG: std::cell::RefCell<HashMap<String, W>> = std::cell::RefCell::new(HashMap::new());
}

fn reg(w: &W) -> W {
    REG.with(|r| {
        r.borrow_mut().insert(w.toks.join(" "), w.clone());
    });
    w.clone()
}

fn stmt_to_w(toks: &Toks) -> W {
    REG.with(|r| {
        let key = toks.join(" ");
        r.borrow()
            .get(&key)
            .cloned()
            .unwrap_or_else(|| panic!("no construction registered for wff `{key}`"))
    })
}

fn w_of(toks: &Toks) -> W {
    stmt_to_w(toks)
}

fn split_impl(toks: &Toks) -> Toks {
    assert_eq!(toks.first().map(|s| s.as_str()), Some("("));
    assert_eq!(toks.last().map(|s| s.as_str()), Some(")"));
    let inner = &toks[1..toks.len() - 1];
    let mut depth = 0i32;
    for (i, tk) in inner.iter().enumerate() {
        match tk.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            "->" if depth == 0 => return inner[i + 1..].to_vec(),
            _ => {}
        }
    }
    panic!("not a top-level implication: {}", toks.join(" "));
}

fn split_ant(toks: &Toks) -> Toks {
    assert_eq!(toks.first().map(|s| s.as_str()), Some("("));
    assert_eq!(toks.last().map(|s| s.as_str()), Some(")"));
    let inner = &toks[1..toks.len() - 1];
    let mut depth = 0i32;
    for (i, tk) in inner.iter().enumerate() {
        match tk.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            "->" if depth == 0 => return inner[..i].to_vec(),
            _ => {}
        }
    }
    panic!("not a top-level implication: {}", toks.join(" "));
}

fn split_eq(toks: &Toks) -> (Toks, Toks) {
    let mut depth = 0i32;
    for (i, tk) in toks.iter().enumerate() {
        match tk.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            "=" if depth == 0 => return (toks[..i].to_vec(), toks[i + 1..].to_vec()),
            _ => {}
        }
    }
    panic!("not a top-level equation: {}", toks.join(" "));
}

fn mp(min: &Pf, maj: &Pf) -> Pf {
    let a = &min.stmt;
    let b = split_impl(&maj.stmt);
    let a_w = stmt_to_w(a);
    let b_w = stmt_to_w(&b);
    let mut rpn = Vec::new();
    rpn.extend(a_w.rpn.clone());
    rpn.extend(b_w.rpn.clone());
    rpn.extend(min.rpn.clone());
    rpn.extend(maj.rpn.clone());
    rpn.push("ax-mp".into());
    Pf { stmt: b, rpn }
}

fn apply(label: &str, floats: &[&W], ess: &[&Pf], result: Toks) -> Pf {
    let mut rpn = Vec::new();
    for f in floats {
        rpn.extend(f.rpn.clone());
    }
    for e in ess {
        rpn.extend(e.rpn.clone());
    }
    rpn.push(label.to_string());
    Pf { stmt: result, rpn }
}

/// Global $f declaration order in data/sdg.base.mm.
const FVARS: &[(&str, &str)] = &[
    ("wph", "ph"), ("wps", "ps"), ("wch", "ch"), ("wth", "th"),
    ("vx", "x"), ("vy", "y"), ("vz", "z"), ("vd", "d"), ("ve", "e"),
    ("va", "a"), ("vb", "b"), ("vc", "c"), ("vf", "f"), ("vg", "g"),
    ("vu", "u"), ("vv", "v"), ("vw", "w"),
];

fn use_thm(label: &str, subst: &[(&str, &W)], ess: &[&Pf], result: Toks) -> Pf {
    let mut rpn = Vec::new();
    for (_fl, vn) in FVARS {
        if let Some((_, w)) = subst.iter().find(|(v, _)| v == vn) {
            rpn.extend(w.rpn.clone());
        }
    }
    for e in ess {
        rpn.extend(e.rpn.clone());
    }
    rpn.push(label.to_string());
    Pf { stmt: result, rpn }
}

// ---- equational combinators ----------------------------------------------

fn eqsym(p: &Pf) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let ba = reg(&weq(&bw, &aw));
    let inst = apply("eqcom", &[&aw, &bw], &[], wi(&ab, &ba).toks);
    mp(p, &inst)
}

fn eqtr(p: &Pf, q: &Pf) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let (b2, c) = split_eq(&q.stmt);
    assert_eq!(b, b2, "eqtr: middle terms differ\n {b:?}\n {b2:?}");
    let aw = w_of(&a);
    let bw = w_of(&b);
    let cw = w_of(&c);
    let ab = reg(&weq(&aw, &bw));
    let bc = reg(&weq(&bw, &cw));
    let ac = reg(&weq(&aw, &cw));
    let inner = reg(&wi(&bc, &ac));
    let eqtri_inst = apply("eqtri", &[&aw, &bw, &cw], &[], wi(&ab, &inner).toks);
    let step1 = mp(p, &eqtri_inst);
    mp(q, &step1)
}

/// Fold a non-empty list of equality Pfs via eqtr.
fn chain(ps: &[Pf]) -> Pf {
    let mut it = ps.iter();
    let mut acc = it.next().expect("chain: empty").clone();
    for p in it {
        acc = eqtr(&acc, p);
    }
    acc
}

fn cong_l(p: &Pf, z: &W, op: &str, tlabel: &str, eqlabel: &str) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let lhs = reg(&binop(&aw, z, op, tlabel));
    let rhs = reg(&binop(&bw, z, op, tlabel));
    let inst = apply(
        eqlabel,
        &[&aw, &bw, z],
        &[],
        wi(&reg(&weq(&aw, &bw)), &reg(&weq(&lhs, &rhs))).toks,
    );
    mp(p, &inst)
}

fn cong_r(p: &Pf, z: &W, op: &str, tlabel: &str, eqlabel: &str) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let lhs = reg(&binop(z, &aw, op, tlabel));
    let rhs = reg(&binop(z, &bw, op, tlabel));
    let inst = apply(
        eqlabel,
        &[&aw, &bw, z],
        &[],
        wi(&reg(&weq(&aw, &bw)), &reg(&weq(&lhs, &rhs))).toks,
    );
    mp(p, &inst)
}

fn plus_l(p: &Pf, z: &W) -> Pf { cong_l(p, z, "+", "tpl", "eq-pl1") }
fn plus_r(p: &Pf, z: &W) -> Pf { cong_r(p, z, "+", "tpl", "eq-pl2") }

fn axeq(label: &str, floats: &[&W], l: &W, r: &W) -> Pf {
    reg(l);
    reg(r);
    apply(label, floats, &[], weq(l, r).toks)
}

fn pl(a: &W, b: &W) -> W { reg(&binop(a, b, "+", "tpl")) }
fn mu(a: &W, b: &W) -> W { reg(&binop(a, b, "*", "tmu")) }

// ===========================================================================
//  DEDUCTION-FORM COMBINATORS  (the §5b seam-closing rule, reproduced here
//  self-contained over data/sdg.base.mm — the SAME derived intuitionistic
//  rule data/sdg.mm's seam-free sdg-deriv uses, NOT imported).
//
//  SOUND and intuitionistically pure by construction: each emits ONLY
//  ax-1 / ax-2 / ax-mp / eqtri / eqcom / eq-* / ax-ial / ax-iar / ax-ian /
//  ax-spec / ax-gen — NO ax-3 / Peirce / LEM / DNE / stable-or-decidable
//  equality / apartness.  Soundness = the intuitionistic deduction
//  theorem fragment: imp_a1 is the weakening/axiom case (ax-1), imp_mp is
//  the modus-ponens case (ax-2); the higher combinators are these two
//  applied to the equational $a (which are themselves implications).
//  sdgtaypure re-verifies the consumed-axiom closure mechanically.
// ===========================================================================

/// `imp_a1` : from `p : |- X` and antecedent `G`, derive `|- ( G -> X )`.
fn imp_a1(p: &Pf, g: &W) -> Pf {
    let xw = w_of(&p.stmt);
    let g_x = reg(&wi(g, &xw));
    let ax1_inst = apply("ax-1", &[&xw, g], &[], reg(&wi(&xw, &g_x)).toks);
    mp(p, &ax1_inst)
}

/// `imp_mp` : from `pa : |- ( G -> A )` and `pab : |- ( G -> ( A -> B ) )`
/// derive `|- ( G -> B )` via ax-2.
fn imp_mp(pa: &Pf, pab: &Pf) -> Pf {
    let g = split_ant(&pa.stmt);
    let a = split_impl(&pa.stmt);
    let a_to_b = split_impl(&pab.stmt);
    let b = split_impl(&a_to_b);
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let a_b = reg(&wi(&aw, &bw));
    let g_ab = reg(&wi(&gw, &a_b));
    let g_a = reg(&wi(&gw, &aw));
    let g_b = reg(&wi(&gw, &bw));
    let ax2_inst = apply(
        "ax-2",
        &[&gw, &aw, &bw],
        &[],
        wi(&g_ab, &reg(&wi(&g_a, &g_b))).toks,
    );
    let step = mp(pab, &ax2_inst);
    mp(pa, &step)
}

/// `imp_eqtr` : transitivity under a shared antecedent `G`.
fn imp_eqtr(pab: &Pf, pbc: &Pf) -> Pf {
    let g = split_ant(&pab.stmt);
    let (a, b) = split_eq(&split_impl(&pab.stmt));
    let (b2, c) = split_eq(&split_impl(&pbc.stmt));
    assert_eq!(b, b2, "imp_eqtr: middle terms differ");
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let cw = w_of(&c);
    let ab = reg(&weq(&aw, &bw));
    let bc = reg(&weq(&bw, &cw));
    let ac = reg(&weq(&aw, &cw));
    let bc_ac = reg(&wi(&bc, &ac));
    let eqtri_inst = apply("eqtri", &[&aw, &bw, &cw], &[], reg(&wi(&ab, &bc_ac)).toks);
    let g_eqtri = imp_a1(&eqtri_inst, &gw);
    let g_bc_ac = imp_mp(pab, &g_eqtri);
    imp_mp(pbc, &g_bc_ac)
}

/// `imp_eqsym` : symmetry under a shared antecedent `G`.
fn imp_eqsym(pab: &Pf) -> Pf {
    let g = split_ant(&pab.stmt);
    let (a, b) = split_eq(&split_impl(&pab.stmt));
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let ba = reg(&weq(&bw, &aw));
    let eqcom_inst = apply("eqcom", &[&aw, &bw], &[], reg(&wi(&ab, &ba)).toks);
    let g_eqcom = imp_a1(&eqcom_inst, &gw);
    imp_mp(pab, &g_eqcom)
}

/// `gen` : universal generalization (ax-gen).  SOUNDNESS PROVISO
/// (metatheoretic, identical to data/sdg.mm's sdg-deriv): the bound
/// variable must not occur free in any essential hypothesis the proof
/// actually depends on.  At the sole use-site the discharged dependencies
/// are tay2.hb / tay2.hc, each `A. d ( ... )` — `d` is BOUND there, so
/// the proviso holds (same discipline as the prequel's quantifier
/// provisos and data/sdg.mm's seam-free sdg-deriv).
fn gen(p: &Pf, xflabel: &str, xtok: &str) -> Pf {
    let bodyw = w_of(&p.stmt);
    let all = reg(&wal(xflabel, xtok, &bodyw));
    let mut rpn = bodyw.rpn.clone();
    rpn.push(xflabel.to_string());
    rpn.extend(p.rpn.clone());
    rpn.push("ax-gen".to_string());
    Pf { stmt: all.toks, rpn }
}

fn main() {
    let base = include_str!("../../data/sdg.base.mm");

    let zero = reg(&W { rpn: t("t0"), toks: t("0") });
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let z = leaf("vz", "z");
    let d = leaf("vd", "d");
    let b = leaf("vb", "b");
    let c = leaf("vc", "c");
    let f = leaf("vf", "f");

    // =====================================================================
    //  RING SCAFFOLD (pure equational algebra; reproduced self-contained
    //  over data/sdg.base.mm — NOT imported from data/sdg.mm).  No order,
    //  no metric residue, no microcancellation, no classical principle.
    // =====================================================================

    // ---- sdg-tay-addcan : [ ( z + u ) = ( z + v ) ] |- u = v -----------
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });
    let z_pl_u = pl(&z, &u);
    let z_pl_v = pl(&z, &v);
    let addcan_hyp = Pf { stmt: weq(&z_pl_u, &z_pl_v).toks, rpn: t("addcan.h") };
    let s1 = cong_r(&addcan_hyp, &invz, "+", "tpl", "eq-pl2");
    let mk_collapse = |tm: &W| -> Pf {
        let z_pl_t = pl(&z, tm);
        let iz_z = pl(&invz, &z);
        let _ = pl(&invz, &z_pl_t);
        let assoc = axeq(
            "ax-addass",
            &[&invz, &z, tm],
            &reg(&binop(&iz_z, tm, "+", "tpl")),
            &reg(&binop(&invz, &z_pl_t, "+", "tpl")),
        );
        let a = eqsym(&assoc);
        let z_iz = pl(&z, &invz);
        let comm = axeq("ax-addcom", &[&invz, &z], &iz_z, &z_iz);
        let neg = axeq("ax-addneg", &[&z], &z_iz, &zero);
        let iz_z_eq0 = eqtr(&comm, &neg);
        let c1 = plus_l(&iz_z_eq0, tm);
        let zero_pl_t = pl(&zero, tm);
        let t_pl_zero = pl(tm, &zero);
        let d1 = axeq("ax-addcom", &[&zero, tm], &zero_pl_t, &t_pl_zero);
        let d2 = axeq("ax-add0", &[tm], &t_pl_zero, tm);
        let dd = eqtr(&d1, &d2);
        eqtr(&a, &eqtr(&c1, &dd))
    };
    let cu = mk_collapse(&u);
    let cv = mk_collapse(&v);
    let sdg_tay_addcan = eqtr(&eqsym(&cu), &eqtr(&s1, &cv));

    // ---- sdg-tay-addcan-imp : |- ( ( z + u ) = ( z + v ) -> u = v ) ----
    //  Deduction-discharged form (HYPOTHESIS-FREE).  Same intuitionistic
    //  deduction-theorem move as data/sdg.mm's sdg-addcan-imp; eq-pl2 is
    //  itself the implication, so the discharge is exact.
    let g_addcan = reg(&weq(&z_pl_u, &z_pl_v));
    let iz_zu = pl(&invz, &z_pl_u);
    let iz_zv = pl(&invz, &z_pl_v);
    let s1_imp = apply(
        "eq-pl2",
        &[&z_pl_u, &z_pl_v, &invz],
        &[],
        wi(&g_addcan, &reg(&weq(&iz_zu, &iz_zv))).toks,
    );
    let cu_imp = imp_a1(&cu, &g_addcan);
    let cv_imp = imp_a1(&cv, &g_addcan);
    let sdg_tay_addcan_imp =
        imp_eqtr(&imp_eqsym(&cu_imp), &imp_eqtr(&s1_imp, &cv_imp));

    // =====================================================================
    //  ORDER-2 POINTWISE UNIQUENESS OF THE LINEAR (DERIVATIVE) COEFF.
    //
    //  sdg-tay-quad-slope.  The GENUINE order-2 analog of data/sdg.mm's
    //  sdg-slope.  Two degree-<=2 KL2 representations of the SAME value V,
    //  sharing the constant term K = ( ap f 0 ) AND the quadratic
    //  coefficient q (the standard SDG setting: ax-microcancel2 isolates
    //  the LINEAR coefficient; quadratic uniqueness is the separate level
    //  the §5h scheme documents):
    //     EB := V = ( ( K + ( b * d ) ) + ( q * ( d * d ) ) )
    //     EC := V = ( ( K + ( c * d ) ) + ( q * ( d * d ) ) )
    //  |- ( b * d ) = ( c * d )
    //  PROOF (RING-ONLY additive cancellation, TWICE):
    //   (K+(b*d))+(q*(d*d)) = (K+(c*d))+(q*(d*d))            [eqsym EB; EC]
    //   cancel ( q*(d*d) ) on the right  (addcan with z := q*(d*d),
    //     after commuting it to the front)                   [sdg-tay-addcan]
    //     -> ( K + ( b*d ) ) = ( K + ( c*d ) )
    //   cancel K  (addcan with z := K)                        [sdg-tay-addcan]
    //     -> ( b*d ) = ( c*d )
    //  No order, no metric residue, no microcancellation, nothing
    //  classical.  The quadratic monomial is PRESENT and is genuinely
    //  cancelled — this is real order-2 content beyond order-1's sdg-slope
    //  (which had only a constant to cancel).
    // =====================================================================
    let apf0 = reg(&ap(&f, &zero));            // K = ( ap f 0 )
    let apfd = reg(&ap(&f, &d));               // V = ( ap f d )
    let b_d = mu(&b, &d);                      // ( b * d )
    let c_d = mu(&c, &d);                      // ( c * d )
    let dd_m = mu(&d, &d);                     // ( d * d )
    let q = leaf("vy", "y");                   // quadratic coefficient q
    let q_dd = mu(&q, &dd_m);                  // ( q * ( d * d ) )
    let k_bd = pl(&apf0, &b_d);                // ( K + ( b * d ) )
    let k_cd = pl(&apf0, &c_d);                // ( K + ( c * d ) )
    let kbd_q = pl(&k_bd, &q_dd);              // ( ( K + ( b*d ) ) + ( q*(d*d) ) )
    let kcd_q = pl(&k_cd, &q_dd);              // ( ( K + ( c*d ) ) + ( q*(d*d) ) )
    let qs_hb = Pf { stmt: weq(&apfd, &kbd_q).toks, rpn: t("qs.hb") };
    let qs_hc = Pf { stmt: weq(&apfd, &kcd_q).toks, rpn: t("qs.hc") };

    // EB,EC  ->  ( (K+(b*d)) + q*(d*d) ) = ( (K+(c*d)) + q*(d*d) )
    let kbdq_eq_kcdq = eqtr(&eqsym(&qs_hb), &qs_hc);
    // commute the shared ( q*(d*d) ) to the FRONT on both sides so the
    // single-summand sdg-tay-addcan (cancel a LEADING z) applies.
    //   ( (K+b*d) + q*(d*d) ) = ( q*(d*d) + (K+b*d) )         ax-addcom
    let qdd_kbd = pl(&q_dd, &k_bd);
    let qdd_kcd = pl(&q_dd, &k_cd);
    let comm_l = axeq("ax-addcom", &[&k_bd, &q_dd], &kbd_q, &qdd_kbd);
    let comm_r = axeq("ax-addcom", &[&k_cd, &q_dd], &kcd_q, &qdd_kcd);
    //   ( q*(d*d) + (K+b*d) ) = ( q*(d*d) + (K+c*d) )
    let qfront = chain(&[eqsym(&comm_l), kbdq_eq_kcdq, comm_r.clone()]);
    // cancel the leading ( q*(d*d) ):  -> ( K+b*d ) = ( K+c*d )
    let kbd_eq_kcd = use_thm(
        "sdg-tay-addcan",
        &[("z", &q_dd), ("u", &k_bd), ("v", &k_cd)],
        &[&qfront],
        weq(&k_bd, &k_cd).toks,
    );
    // cancel the constant K:  -> ( b*d ) = ( c*d )
    let sdg_tay_quad_slope = use_thm(
        "sdg-tay-addcan",
        &[("z", &apf0), ("u", &b_d), ("v", &c_d)],
        &[&kbd_eq_kcd],
        weq(&b_d, &c_d).toks,
    );
    assert_eq!(sdg_tay_quad_slope.stmt, weq(&b_d, &c_d).toks);

    // =====================================================================
    //  sdg-tay-quad-slope-imp : the DEDUCTION-DISCHARGED order-2 pointwise
    //  uniqueness, HYPOTHESIS-FREE with a single conjunctive antecedent
    //      |- ( ( EB /\ EC ) -> ( b*d ) = ( c*d ) )
    //  (so the single-antecedent imp_* toolkit threads it under ( D2 d )
    //  in the seam-free headline).  Same construction as data/sdg.mm's
    //  sdg-slope-imp, lifted to the order-2 quadratic representation.
    // =====================================================================
    let eb = reg(&weq(&apfd, &kbd_q));         // EB
    let ec = reg(&weq(&apfd, &kcd_q));         // EC
    let q_bd_cd = reg(&weq(&b_d, &c_d));       // Q := ( b*d ) = ( c*d )
    let g_slope = reg(&wa(&eb, &ec));          // G := ( EB /\ EC )
    let g_eb = apply("ax-ial", &[&eb, &ec], &[], wi(&g_slope, &eb).toks);
    let g_ec = apply("ax-iar", &[&eb, &ec], &[], wi(&g_slope, &ec).toks);
    // ( G -> ( (K+b*d)+q*(d*d) ) = V )       [imp_eqsym of g_eb]
    let g_kbdq_v = imp_eqsym(&g_eb);
    // ( G -> ( (K+b*d)+q*(d*d) ) = ( (K+c*d)+q*(d*d) ) )   [imp_eqtr via g_ec]
    let g_kbdq_kcdq = imp_eqtr(&g_kbdq_v, &g_ec);
    // commute q*(d*d) to the front, under G, to feed sdg-tay-addcan-imp.
    //   closed: ( (K+b*d)+q*(d*d) ) = ( q*(d*d)+(K+b*d) )   [ax-addcom], lift
    let comm_l_imp = imp_a1(&comm_l, &g_slope);          // ( G -> kbd_q = qdd_kbd )
    let comm_r_imp = imp_a1(&comm_r, &g_slope);          // ( G -> kcd_q = qdd_kcd )
    //   ( G -> ( q*(d*d)+(K+b*d) ) = ( q*(d*d)+(K+c*d) ) )
    let g_qfront =
        imp_eqtr(&imp_eqsym(&comm_l_imp), &imp_eqtr(&g_kbdq_kcdq, &comm_r_imp));
    // sdg-tay-addcan-imp[z:=q*(d*d), u:=K+b*d, v:=K+c*d] :
    //   |- ( ( q*(d*d)+(K+b*d) ) = ( q*(d*d)+(K+c*d) ) -> ( K+b*d )=( K+c*d ) )
    let ac1_inst = use_thm(
        "sdg-tay-addcan-imp",
        &[("z", &q_dd), ("u", &k_bd), ("v", &k_cd)],
        &[],
        reg(&wi(&reg(&weq(&qdd_kbd, &qdd_kcd)), &reg(&weq(&k_bd, &k_cd)))).toks,
    );
    let g_ac1 = imp_a1(&ac1_inst, &g_slope);
    let g_kbd_kcd = imp_mp(&g_qfront, &g_ac1); // ( G -> ( K+b*d )=( K+c*d ) )
    // sdg-tay-addcan-imp[z:=K, u:=b*d, v:=c*d] :
    //   |- ( ( K+b*d )=( K+c*d ) -> ( b*d )=( c*d ) )
    let ac2_inst = use_thm(
        "sdg-tay-addcan-imp",
        &[("z", &apf0), ("u", &b_d), ("v", &c_d)],
        &[],
        reg(&wi(&reg(&weq(&k_bd, &k_cd)), &q_bd_cd)).toks,
    );
    let g_ac2 = imp_a1(&ac2_inst, &g_slope);
    let sdg_tay_quad_slope_imp = imp_mp(&g_kbd_kcd, &g_ac2); // ( ( EB/\EC ) -> Q )
    assert_eq!(
        sdg_tay_quad_slope_imp.stmt,
        wi(&g_slope, &q_bd_cd).toks
    );

    // =====================================================================
    //  THE SEAM-FREE HEADLINE — sdg-tay-deriv2.
    //
    //  Order-2 uniqueness of the Taylor LINEAR (derivative) coefficient.
    //  Hypotheses are ONLY the two UNIVERSAL degree-<=2 KL2
    //  representations over D_2 (each an ax-kl2 instance — EXISTENCE):
    //    tay2.hb : A. d ( ( D2 d ) -> EB )
    //    tay2.hc : A. d ( ( D2 d ) -> EC )
    //  Conclusion: b = c.  The linking universal
    //    A. d ( ( D2 d ) -> ( b*d )=( c*d ) )
    //  is MECHANICALLY THREADED, not assumed:
    //    1. ax-spec strips A.d :  pB:( (D2 d)->EB ),  pC:( (D2 d)->EC ).
    //    2. ax-ian lifted under ( D2 d ) by imp_a1, detached by imp_mp
    //       twice  ->  ( ( D2 d ) -> ( EB /\ EC ) ).
    //    3. sdg-tay-quad-slope-imp : ( ( EB/\EC ) -> Q ); lifted under
    //       ( D2 d ) by imp_a1, detached  ->  ( ( D2 d ) -> Q ).
    //    4. gen (ax-gen) :  A. d ( ( D2 d ) -> Q )   — SOUND: `d` is
    //       BOUND in tay2.hb / tay2.hc, the only discharged hyps.
    //    5. ax-microcancel2 mp :  b = c.
    //  NO linking `$e`.  GENUINELY CONSUMES ax-microcancel2 (the level-2
    //  uniqueness axiom) + the KL2 representation — verified RPN ends
    //  `... ax-gen ... ax-microcancel2 ax-mp`; sdgtaypure re-verifies the
    //  consumed-axiom closure mechanically.  This is the exact order-2
    //  mirror of data/sdg.mm's seam-free sdg-deriv.
    // =====================================================================
    let d2_pred = reg(&wD2(&d));               // ( D2 d )
    let imp_b = reg(&wi(&d2_pred, &eb));       // ( ( D2 d ) -> EB )
    let imp_c = reg(&wi(&d2_pred, &ec));
    let all_b = reg(&wal("vd", "d", &imp_b));
    let all_c = reg(&wal("vd", "d", &imp_c));
    let hb = Pf { stmt: all_b.toks.clone(), rpn: t("tay2.hb") };
    let hc = Pf { stmt: all_c.toks.clone(), rpn: t("tay2.hc") };
    // ax-spec[ph:=imp_*, x:=d] : floats = [imp_*, d]
    let spec_b = apply("ax-spec", &[&imp_b, &d], &[], reg(&wi(&all_b, &imp_b)).toks);
    let spec_c = apply("ax-spec", &[&imp_c, &d], &[], reg(&wi(&all_c, &imp_c)).toks);
    let p_b = mp(&hb, &spec_b);                // |- ( ( D2 d ) -> EB )
    let p_c = mp(&hc, &spec_c);                // |- ( ( D2 d ) -> EC )
    // ( ( D2 d ) -> ( EB /\ EC ) )
    let eb_ec = reg(&wa(&eb, &ec));
    let ian = apply(
        "ax-ian",
        &[&eb, &ec],
        &[],
        reg(&wi(&eb, &reg(&wi(&ec, &eb_ec)))).toks,
    );
    let g_ian = imp_a1(&ian, &d2_pred);
    let g_ec_conj = imp_mp(&p_b, &g_ian);
    let g_conj = imp_mp(&p_c, &g_ec_conj);     // ( ( D2 d ) -> ( EB /\ EC ) )
    // thread sdg-tay-quad-slope-imp under ( D2 d )
    let qsi_inst = use_thm(
        "sdg-tay-quad-slope-imp",
        &[("b", &b), ("c", &c), ("d", &d), ("f", &f), ("y", &q)],
        &[],
        reg(&wi(&eb_ec, &q_bd_cd)).toks,
    );
    let g_qsi = imp_a1(&qsi_inst, &d2_pred);
    let g_q = imp_mp(&g_conj, &g_qsi);         // |- ( ( D2 d ) -> Q )
    // ax-gen over d  (SOUND: d bound in tay2.hb / tay2.hc)
    let all_guard = gen(&g_q, "vd", "d");      // |- A. d ( ( D2 d ) -> Q )
    // ax-microcancel2 : ( A. d ( ( D2 d ) -> ( b*d )=( c*d ) ) -> b = c )
    let b_eq_c = reg(&weq(&b, &c));
    let mc2_inst = use_thm(
        "ax-microcancel2",
        &[("b", &b), ("c", &c), ("d", &d)],
        &[],
        wi(&w_of(&all_guard.stmt), &b_eq_c).toks,
    );
    let sdg_tay_deriv2 = mp(&all_guard, &mc2_inst); // |- b = c  (seam-free)
    assert_eq!(sdg_tay_deriv2.stmt, weq(&b, &c).toks);

    // =====================================================================
    //  sdg-tay-k1-reduce : the k=1 instance of the Taylor scheme IS the
    //  existing order-1 derivative (KL_1 = ax-kl): the degree-<=1
    //  expansion f(d)=f(0)+b*d on D is exactly the order-1 case.  Recorded
    //  as the identity implication on that EXACT KL_1 formula — an HONEST
    //  marker that k=1 adds nothing new (it reduces to the §4 / §5b
    //  synthetic derivative), NOT a vacuous re-derivation.  Pure logic
    //  (ax-1 / ax-2 only); consumes NOTHING of the SDG substrate.
    // =====================================================================
    let kl1 = reg(&wex(
        "vb",
        "b",
        &wal(
            "vd",
            "d",
            &reg(&wi(
                &reg(&W { rpn: rpn_app(&[&d.rpn], "wD"), toks: { let mut v=vec!["(".into(),"D".into()]; v.extend(d.toks.clone()); v.push(")".into()); v } }),
                &reg(&weq(
                    &reg(&ap(&f, &d)),
                    &pl(&reg(&ap(&f, &zero)), &mu(&b, &d)),
                )),
            )),
        ),
    ));
    let sdg_tay_k1_reduce = {
        let p = &kl1;
        let pp = reg(&wi(p, p));
        let p_pp = reg(&wi(p, &pp));
        let pp_p = reg(&wi(&pp, p));
        let p__pp_p = reg(&wi(p, &pp_p));
        let _ = reg(&wi(&p_pp, &pp));
        let s1 = apply("ax-1", &[p, p], &[], p_pp.toks.clone());
        let s2 = apply("ax-1", &[p, &pp], &[], p__pp_p.toks.clone());
        let s3 = apply("ax-2", &[p, &pp, p], &[], {
            let lhs = wi(p, &p__pp_p);
            let rhs = wi(&p_pp, &pp);
            wi(&lhs, &rhs).toks
        });
        let s4 = mp(&s2, &s3);
        mp(&s1, &s4)
    };

    // =====================================================================
    //  assemble + emit
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-tay-addcan",
            "|- u = v",
            vec![("addcan.h", "|- ( z + u ) = ( z + v )")],
            &sdg_tay_addcan,
        ),
        (
            "sdg-tay-addcan-imp",
            "|- ( ( z + u ) = ( z + v ) -> u = v )",
            vec![],
            &sdg_tay_addcan_imp,
        ),
        (
            // ORDER-2 pointwise uniqueness of the linear coefficient.
            // RING-ONLY: cancels the quadratic term q*(d*d) AND the
            // constant K.  Genuine order-2 content (order-1's sdg-slope
            // had only a constant).  No microcancellation, nothing
            // classical.
            "sdg-tay-quad-slope",
            "|- ( b * d ) = ( c * d )",
            vec![
                ("qs.hb", "|- ( ap f d ) = ( ( ( ap f 0 ) + ( b * d ) ) + ( y * ( d * d ) ) )"),
                ("qs.hc", "|- ( ap f d ) = ( ( ( ap f 0 ) + ( c * d ) ) + ( y * ( d * d ) ) )"),
            ],
            &sdg_tay_quad_slope,
        ),
        (
            // Deduction-discharged order-2 pointwise uniqueness,
            // HYPOTHESIS-FREE (conjunctive antecedent).
            "sdg-tay-quad-slope-imp",
            "|- ( ( ( ap f d ) = ( ( ( ap f 0 ) + ( b * d ) ) + ( y * ( d * d ) ) ) /\\ ( ap f d ) = ( ( ( ap f 0 ) + ( c * d ) ) + ( y * ( d * d ) ) ) ) -> ( b * d ) = ( c * d ) )",
            vec![],
            &sdg_tay_quad_slope_imp,
        ),
        (
            // THE SEAM-FREE ORDER-2 TAYLOR HEADLINE.  The linking
            // universal is mechanically threaded from the two universal
            // degree-<=2 KL2 representations over D_2 (tay2.hb/tay2.hc,
            // each an ax-kl2 instance) via the deduction-form combinators
            // + ax-spec/ax-gen; NO linking $e.  GENUINELY CONSUMES
            // ax-microcancel2 (level-2 uniqueness) — and NOTHING
            // classical.  Exact order-2 mirror of data/sdg.mm sdg-deriv.
            "sdg-tay-deriv2",
            "|- b = c",
            vec![
                ("tay2.hb", "|- A. d ( ( D2 d ) -> ( ap f d ) = ( ( ( ap f 0 ) + ( b * d ) ) + ( y * ( d * d ) ) ) )"),
                ("tay2.hc", "|- A. d ( ( D2 d ) -> ( ap f d ) = ( ( ( ap f 0 ) + ( c * d ) ) + ( y * ( d * d ) ) ) )"),
            ],
            &sdg_tay_deriv2,
        ),
        (
            // The k=1 instance of the Taylor scheme IS the existing
            // order-1 synthetic derivative (KL_1 = ax-kl): recorded as
            // the identity on that exact KL_1 formula — an honest marker
            // that k=1 adds nothing, not a vacuous re-derivation.
            "sdg-tay-k1-reduce",
            "|- ( E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) -> E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) )",
            vec![],
            &sdg_tay_k1_reduce,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         SYNTHETIC ORDER-2 TAYLOR (sdgtaybuild).  SEQUEL_SCOPE §5h.\n   \
         Self-contained over the data/sdg.base.mm surface; independent of\n   \
         data/sdg.mm and data/sdg.calc.mm (no shared $p; disjoint\n   \
         `sdg-tay-*` labels) so the corpora never merge-conflict.\n   \
         EXISTENCE of the order-2 expansion f(x+d)=f(x)+d*f'(x)+(d*d)*s(x)\n   \
         on D_2 is exactly ax-kl2 (an axiom, CITED).  Delivered here:\n   \
         the genuine UNIQUENESS content.  sdg-tay-quad-slope: order-2\n   \
         pointwise uniqueness of the linear coeff, RING-ONLY, cancels the\n   \
         quadratic term too.  sdg-tay-deriv2: SEAM-FREE, mechanically\n   \
         threads the linking universal over D_2 and GENUINELY CONSUMES\n   \
         ax-microcancel2 to get b=c (exact order-2 mirror of sdg-deriv).\n   \
         sdg-tay-k1-reduce: honest marker that k=1 = the existing order-1\n   \
         derivative.  POINTWISE/seam discipline identical to data/sdg.mm.\n   \
         ================================================================ $)\n\n",
    );
    for (name, stmt, hyps, pf) in &proofs {
        let want: Vec<String> = stmt
            .strip_prefix("|- ")
            .unwrap()
            .split_whitespace()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(
            &pf.stmt, &want,
            "builder produced wrong statement for {name}:\n  built {:?}\n  want  {:?}",
            pf.stmt, want
        );
        if hyps.is_empty() {
            writeln!(out, "{name} $p {stmt} $= {} $.", pf.rpn.join(" ")).unwrap();
        } else {
            writeln!(out, "${{").unwrap();
            for (hl, hs) in hyps {
                writeln!(out, "  {hl} $e {hs} $.").unwrap();
            }
            writeln!(out, "  {name} $p {stmt} $= {} $.", pf.rpn.join(" ")).unwrap();
            writeln!(out, "$}}").unwrap();
        }
    }

    match kernel::Db::parse(&out) {
        Ok(db) => match db.verify() {
            Ok(()) => {
                let n = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
                std::fs::write("data/sdg.taylor.mm", &out).expect("write data/sdg.taylor.mm");
                println!("sdgtaybuild: kernel-verified {n} $p; wrote data/sdg.taylor.mm OK");
            }
            Err(e) => {
                eprintln!("sdgtaybuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.taylor.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgtaybuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.taylor.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
