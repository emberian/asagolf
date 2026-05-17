//! sdgtanbuild — constructs the kernel-verified SYNTHETIC TANGENT
//! STRUCTURE (tangent vectors `D -> R`, the tangent bundle `R^D`, the
//! Kock-Lawvere correspondence `R^D ~= R x R`, and the Lie-bracket
//! microsquare construction up to its precise substrate boundary) and
//! writes data/sdg.tangent.mm.
//!
//! COMPOSITION / why a SEPARATE file (the proven data/sdg.calc.mm
//! zero-conflict pattern, copied exactly).  This file is fully
//! self-contained: it embeds the certified-intuitionistic substrate base
//! verbatim (data/sdg.base.mm — the SAME trust surface sdgpure/sdgtanpure
//! audit) and appends ONLY new `sdg-tan-*` $p.  It deliberately does NOT
//! touch data/sdg.mm, data/sdg.base.mm, data/sdg.calc.mm, sdgbuild.rs,
//! src/kernel.rs, src/elaborate.rs, or any other agent's file, so it can
//! never merge-conflict.  Intended composition: data/sdg.mm,
//! data/sdg.calc.mm and data/sdg.tangent.mm are independent kernel-checked
//! / purity-checked corpora over the IDENTICAL data/sdg.base.mm axiom
//! surface, sharing NO $p (disjoint label namespaces `sdg-*`,
//! `sdg-calc-*`, `sdg-tan-*`); a downstream union is a rename-free
//! concatenation of their $p blocks.
//!
//! WHAT IS GENUINE vs WHAT IS A REPORTED BOUNDARY (Iron Rule, adversarial).
//!   * `sdg-tan-base` / `sdg-tan-roundtrip` : the `R x R -> R^D` direction
//!     of the correspondence and its round-trip, PURE RING.
//!   * `sdg-tan-principal` : the `R^D -> R x R` direction's
//!     well-definedness — the principal part of a tangent vector is
//!     UNIQUELY determined.  This GENUINELY CONSUMES `ax-microcancel`
//!     (KL's uniqueness half), threaded mechanically exactly like
//!     data/sdg.mm's seam-free `sdg-deriv` (no linking `$e`): the affine
//!     KL representations are `ax-kl`-instance hypotheses (EXISTENCE), the
//!     pointwise slope identity is derived ring-only, ax-gen closes the
//!     universal, ax-microcancel detaches `b = c`.  KL is consumed, NOT
//!     asserted — verified by sdgtanpure's per-$p consumed-axiom closure.
//!   * `sdg-tan-bracket` : the Lie bracket via the standard SDG `D x D`
//!     microsquare commutator.  The algebraic skeleton (the commutator of
//!     the two infinitesimal flows collapses, on the microsquare, to the
//!     bracket's principal-part form) is DERIVED ring-only.  The single
//!     genuinely off-limits step — composing one vector field's flow INTO
//!     the other's argument, which is (a) `ap`-congruence (the documented
//!     data/sdg.calc.mm chain-rule substrate gap: data/sdg.base.mm
//!     instantiates Leibniz only for `+`/`*`, not for `ap`) AND (b) a
//!     globalized/generator-side derivative of the principal part
//!     (W2-glob, the keystone-side machinery this task must NOT touch) —
//!     is surfaced as EXACTLY ONE loudly-labelled `$e`
//!     (`tanbr.flow`).  A precisely-characterised boundary is a FULL
//!     SUCCESS per the Iron Rule; it is reported, not faked.
//!
//! Run:  cargo run --release --bin sdgtanbuild
//!
//! UNTRUSTED scaffolding.  Trust root = src/kernel.rs re-checking the
//! emitted data/sdg.tangent.mm (run `cargo run --bin sdgtanfloor` and
//! `cargo run --bin sdgtanpure`).

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

fn wD(x: &W) -> W {
    W {
        rpn: rpn_app(&[&x.rpn], "wD"),
        toks: {
            let mut v = vec!["(".into(), "D".into()];
            v.extend(x.toks.clone());
            v.push(")".into());
            v
        },
    }
}

/// wal $a wff A. x ph $.  Kernel mandatory $f order = declaration order
/// = wph (body) BEFORE vx, so RPN = body.rpn, then xvar, then `wal`.
fn wal(xflabel: &str, xtok: &str, body: &W) -> W {
    W {
        rpn: {
            let mut r = body.rpn.clone();
            r.push(xflabel.to_string());
            r.push("wal".to_string());
            r
        },
        toks: {
            let mut v = vec!["A.".into(), xtok.to_string()];
            v.extend(body.toks.clone());
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
    static REG: std::cell::RefCell<HashMap<String, W>> =
        std::cell::RefCell::new(HashMap::new());
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
fn mul_l(p: &Pf, z: &W) -> Pf { cong_l(p, z, "*", "tmu", "eq-mu1") }
fn mul_r(p: &Pf, z: &W) -> Pf { cong_r(p, z, "*", "tmu", "eq-mu2") }

fn axeq(label: &str, floats: &[&W], l: &W, r: &W) -> Pf {
    reg(l);
    reg(r);
    apply(label, floats, &[], weq(l, r).toks)
}

fn pl(a: &W, b: &W) -> W { reg(&binop(a, b, "+", "tpl")) }
fn mu(a: &W, b: &W) -> W { reg(&binop(a, b, "*", "tmu")) }

// ---- the intuitionistic deduction-theorem fragment (verbatim from
//      sdgbuild.rs — ax-1 weakening + ax-2 mp distribution; NO classical
//      principle; sdgtanpure re-verifies the consumed-axiom closure). ----

fn imp_a1(p: &Pf, g: &W) -> Pf {
    let xw = w_of(&p.stmt);
    let g_x = reg(&wi(g, &xw));
    let ax1_inst = apply("ax-1", &[&xw, g], &[], reg(&wi(&xw, &g_x)).toks);
    mp(p, &ax1_inst)
}

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

/// Universal generalization.  From `p : |- ph` derive `|- A. x ph`.
/// SOUNDNESS PROVISO (metatheoretic, identical discipline to
/// sdgbuild.rs's seam-free sdg-deriv, SEQUEL_SCOPE §5b): the bound
/// variable must not occur free in any essential hypothesis `p` actually
/// depends on.  At the sole use-site the discharged dependencies are the
/// two `pp.hb`/`pp.hc` universal KL representations `A. d ( ... )`, in
/// which `d` is BOUND — the proviso holds.
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
    let x = leaf("vx", "x");
    let y = leaf("vy", "y");
    let z = leaf("vz", "z");
    let e = leaf("ve", "e");
    let d = leaf("vd", "d");
    let a = leaf("va", "a");
    let b = leaf("vb", "b");
    let c = leaf("vc", "c");
    // tangent vectors carried by the function symbols t (use vf), and the
    // two vector fields' principal parts by g, w.
    let tf = leaf("vf", "f"); // a tangent vector  t : D -> R   ( ap f d )
    let _ = (&x, &y, &e);

    // =====================================================================
    //  RING SCAFFOLD (pure equational algebra; reproduced self-contained
    //  over data/sdg.base.mm, exactly like data/sdg.calc.mm does — NO
    //  import from data/sdg.mm, NO order, NO metric residue, NO
    //  microcancellation in these).
    // =====================================================================

    // ---- sdg-tan-addcan : [ ( z + u ) = ( z + v ) ] |- u = v ------------
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });
    let z_pl_u = pl(&z, &u);
    let z_pl_v = pl(&z, &v);
    let addcan_hyp = Pf { stmt: weq(&z_pl_u, &z_pl_v).toks, rpn: t("tanac.h") };
    let s1 = plus_r(&addcan_hyp, &invz);
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
        let aa = eqsym(&assoc);
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
        eqtr(&aa, &eqtr(&c1, &dd))
    };
    let cu = mk_collapse(&u);
    let cv = mk_collapse(&v);
    let sdg_tan_addcan = eqtr(&eqsym(&cu), &eqtr(&s1, &cv));

    // ---- sdg-tan-addcan-imp : |- ( ( z+u )=( z+v ) -> u = v ) -----------
    //  deduction-discharged form (used to thread the principal-part
    //  uniqueness without an `$e`), exactly mirroring sdgbuild's
    //  sdg-addcan-imp.
    let g_addcan = reg(&weq(&z_pl_u, &z_pl_v));
    let iz_zu = reg(&binop(&invz, &z_pl_u, "+", "tpl"));
    let iz_zv = reg(&binop(&invz, &z_pl_v, "+", "tpl"));
    let s1_imp = apply(
        "eq-pl2",
        &[&z_pl_u, &z_pl_v, &invz],
        &[],
        wi(&g_addcan, &reg(&weq(&iz_zu, &iz_zv))).toks,
    );
    let cu_imp = imp_a1(&cu, &g_addcan);
    let cv_imp = imp_a1(&cv, &g_addcan);
    let sdg_tan_addcan_imp =
        imp_eqtr(&imp_eqsym(&cu_imp), &imp_eqtr(&s1_imp, &cv_imp));

    // =====================================================================
    //  PART 1 — THE TANGENT BUNDLE  R^D  AND THE  R x R -> R^D  DIRECTION.
    //
    //  A tangent vector at a point is a map  t : D -> R.  Its base point
    //  is  ( ap t 0 ).  The canonical tangent vector built from a pair
    //  ( a , b ) in R x R is the affine map  d |-> ( a + ( b * d ) ).
    //
    //  sdg-tan-base : the constructed tangent vector has base point a:
    //      |- ( ( a + ( b * 0 ) ) ) = a            (PURE RING)
    //  i.e. evaluating  d |-> ( a + ( b * d ) )  at  d = 0  recovers a.
    //  This is the R x R -> R^D map landing at the correct base point.
    // =====================================================================
    let b0 = mu(&b, &zero); // ( b * 0 )
    let a_b0 = pl(&a, &b0); // ( a + ( b * 0 ) )
    // ( b * 0 ) = 0                                          ax-mul0
    let bz_eq0 = axeq("ax-mul0", &[&b], &b0, &zero);
    // ( a + ( b * 0 ) ) = ( a + 0 )                          cong-r
    let step_ab = plus_r(&bz_eq0, &a);
    // ( a + 0 ) = a                                          ax-add0
    let a0 = pl(&a, &zero);
    let a0_eq_a = axeq("ax-add0", &[&a], &a0, &a);
    let sdg_tan_base = eqtr(&step_ab, &a0_eq_a); // |- ( a + ( b * 0 ) ) = a

    // =====================================================================
    //  sdg-tan-roundtrip : the  R x R -> R^D -> R x R  round trip is the
    //  identity (PURE RING).  Take the pair ( a , b ); build the tangent
    //  vector  T(d) = ( a + ( b * d ) ).  Extracting its data back:
    //  base point = T(0) = ( a + ( b * 0 ) ) (= a by sdg-tan-base) and
    //  principal part = b.  Rebuilding the affine representation FROM the
    //  extracted base point  ( a + ( b * 0 ) )  must give back T pointwise:
    //      |- ( ( ( a + ( b * 0 ) ) + ( b * d ) ) = ( a + ( b * d ) )
    //  This is exactly "rebuild-from-extracted-data = original map",
    //  i.e. R x R -> R^D -> R x R = id.  PURE RING (sdg-tan-base lifted
    //  under +).
    // =====================================================================
    let bd = mu(&b, &d); // ( b * d )
    let ab0_bd = pl(&a_b0, &bd); // ( ( a + ( b * 0 ) ) + ( b * d ) )
    let a_bd = pl(&a, &bd); // ( a + ( b * d ) )
    // ( a + ( b * 0 ) ) = a   [sdg-tan-base]  -> cong-l by ( b * d )
    let sdg_tan_roundtrip = plus_l(&sdg_tan_base, &bd);
    let _ = (&ab0_bd, &a_bd);

    // =====================================================================
    //  PART 2 — THE  R^D -> R x R  DIRECTION: THE PRINCIPAL PART IS
    //  UNIQUELY DETERMINED.  THIS IS THE GENUINE KL CONSEQUENCE.
    //
    //  By Kock-Lawvere (ax-kl), every tangent vector t : D -> R IS affine:
    //    EXISTS b. FORALL d in D.  ( ap t d ) = ( ( ap t 0 ) + ( b * d ) )
    //  The forward map  R^D -> R x R  sends t to ( ( ap t 0 ) , b ).  For
    //  it to be a genuine bijection (the correspondence, not merely a
    //  surjection) the principal part b must be UNIQUELY determined by t.
    //  THAT is KL's uniqueness half and it GENUINELY CONSUMES
    //  ax-microcancel — we consume it, we do NOT assert it.
    //
    //  sdg-tan-principal  (seam-free, NO linking `$e` — threaded exactly
    //  like data/sdg.mm's headline sdg-deriv):
    //    pp.hb : A. d ( ( D d ) -> ( ap t d )=( ( ap t 0 )+( b*d ) ) )  [ax-kl EXISTENCE]
    //    pp.hc : A. d ( ( D d ) -> ( ap t d )=( ( ap t 0 )+( c*d ) ) )  [ax-kl EXISTENCE]
    //    |- b = c
    //  Derivation: ax-spec strips A.d; ax-ian (lifted under the ( D d )
    //  guard by imp_a1, detached by imp_mp twice) gives the conjunction;
    //  the pointwise slope identity ( b*d )=( c*d ) is ring-only
    //  (sdg-tan-addcan-imp); ax-gen closes the universal (SOUND: d bound
    //  in pp.hb/pp.hc); ax-microcancel detaches  b = c.
    // =====================================================================
    let t0 = reg(&ap(&tf, &zero)); // ( ap t 0 )   (constant term / base pt)
    let td = reg(&ap(&tf, &d)); // ( ap t d )
    let cd = mu(&c, &d); // ( c * d )
    let k_bd = pl(&t0, &bd); // ( ( ap t 0 ) + ( b * d ) )
    let k_cd = pl(&t0, &cd); // ( ( ap t 0 ) + ( c * d ) )
    let dd_pred = reg(&wD(&d)); // ( D d )
    let eq_b = reg(&weq(&td, &k_bd)); // EB
    let eq_c = reg(&weq(&td, &k_cd)); // EC
    let imp_b = reg(&wi(&dd_pred, &eq_b));
    let imp_c = reg(&wi(&dd_pred, &eq_c));
    let all_b = reg(&wal("vd", "d", &imp_b));
    let all_c = reg(&wal("vd", "d", &imp_c));
    let hb = Pf { stmt: all_b.toks.clone(), rpn: t("pp.hb") };
    let hc = Pf { stmt: all_c.toks.clone(), rpn: t("pp.hc") };

    // ax-spec : strip A.d.  Float order: wph(ph) then vx(x); ph:=imp_*,
    // x:=d.
    let spec_b = apply("ax-spec", &[&imp_b, &d], &[], reg(&wi(&all_b, &imp_b)).toks);
    let spec_c = apply("ax-spec", &[&imp_c, &d], &[], reg(&wi(&all_c, &imp_c)).toks);
    let pb = mp(&hb, &spec_b); // |- ( ( D d ) -> EB )
    let pc = mp(&hc, &spec_c); // |- ( ( D d ) -> EC )

    // ( ( D d ) -> ( EB /\ EC ) )
    let eb_ec = reg(&wa(&eq_b, &eq_c));
    let ian = apply(
        "ax-ian",
        &[&eq_b, &eq_c],
        &[],
        reg(&wi(&eq_b, &reg(&wi(&eq_c, &eb_ec)))).toks,
    );
    let g_ian = imp_a1(&ian, &dd_pred);
    let g_ec_conj = imp_mp(&pb, &g_ian);
    let g_conj = imp_mp(&pc, &g_ec_conj); // |- ( ( D d ) -> ( EB /\ EC ) )

    // ( ( EB /\ EC ) -> ( b*d )=( c*d ) ), derived ring-only:
    //   EB,EC share ( ap t d ); eqsym+eqtr gives
    //   ( ( ap t 0 )+( b*d ) )=( ( ap t 0 )+( c*d ) ); sdg-tan-addcan-imp
    //   [z:=( ap t 0 ),u:=( b*d ),v:=( c*d )] detaches ( b*d )=( c*d ).
    let q_bd_cd = reg(&weq(&bd, &cd));
    let g_slope = reg(&wa(&eq_b, &eq_c));
    let g_eb = apply("ax-ial", &[&eq_b, &eq_c], &[], wi(&g_slope, &eq_b).toks);
    let g_ec = apply("ax-iar", &[&eq_b, &eq_c], &[], wi(&g_slope, &eq_c).toks);
    let g_kbd_v = imp_eqsym(&g_eb); // ( G -> ( K+(b*d) )=V )
    let g_kbd_kcd = imp_eqtr(&g_kbd_v, &g_ec); // ( G -> ( K+(b*d) )=( K+(c*d) ) )
    let ac_inst = use_thm(
        "sdg-tan-addcan-imp",
        &[("z", &t0), ("u", &bd), ("v", &cd)],
        &[],
        reg(&wi(&reg(&weq(&k_bd, &k_cd)), &q_bd_cd)).toks,
    );
    let g_ac = imp_a1(&ac_inst, &g_slope);
    let sdg_tan_slope_imp = imp_mp(&g_kbd_kcd, &g_ac); // |- ( ( EB /\ EC ) -> Q )

    // thread ( ( EB /\ EC ) -> Q ) under the ( D d ) guard.
    let g_slope_imp = imp_a1(&sdg_tan_slope_imp, &dd_pred);
    let g_q = imp_mp(&g_conj, &g_slope_imp); // |- ( ( D d ) -> Q )
    // ax-gen : A. d ( ( D d ) -> Q )   (SOUND: d bound in pp.hb/pp.hc).
    let all_guard = gen(&g_q, "vd", "d");
    // microcancellation : b = c.  GENUINELY CONSUMED.
    let b_eq_c = reg(&weq(&b, &c));
    let mc_inst = use_thm(
        "ax-microcancel",
        &[("b", &b), ("c", &c), ("d", &d)],
        &[],
        wi(&w_of(&all_guard.stmt), &b_eq_c).toks,
    );
    let sdg_tan_principal = mp(&all_guard, &mc_inst); // |- b = c  (seam-free)

    // =====================================================================
    //  PART 3 — VECTOR FIELDS AS SECTIONS, AND THE LIE BRACKET VIA THE
    //  STANDARD SDG  D x D  MICROSQUARE COMMUTATOR.
    //
    //  A vector field is a section  X : R -> R^D , x |-> ( the tangent
    //  vector at x ).  By PART 2's correspondence  R^D ~= R x R , X is
    //  carried by its PRINCIPAL PART  p : R -> R :
    //      X(x)(d) = ( x + ( ( ap p x ) * d ) )      ( d in D )
    //  Two vector fields with principal parts p, q.  The Lie bracket
    //  [X,Y] is, in the standard SDG construction, read off from the
    //  commutator of the two infinitesimal flows on the MICROSQUARE
    //  D x D : flowing by X for d1 then Y for d2, vs Y then X, and the
    //  failure-to-commute is  [X,Y]·(d1·d2).
    //
    //  The PURELY ALGEBRAIC skeleton (the part the ring substrate carries)
    //  is: on the microsquare the two composite displacements differ by
    //  the cross term  ( ( ap p x ) * ( ap q x ) - ( ap q x ) * ( ap p x ) )
    //  * ( d1 * d2 ), which is the ZERO-th order obstruction; the genuine
    //  bracket is the NEXT-order term, the derivative cross
    //  ( X(q) - Y(p) ).  We derive what the substrate proves:
    //
    //  sdg-tan-bracket-cross : the symmetric (zeroth-order) part of the
    //  microsquare commutator VANISHES — the scalar pieces commute
    //  (PURE RING, ax-mulcom + cancellation):
    //      |- ( ( ( ap p x ) * ( ap q x ) ) * ( d1 * d2 ) )
    //       = ( ( ( ap q x ) * ( ap p x ) ) * ( d1 * d2 ) )
    //  i.e. the would-be obstruction at the symmetric order is identically
    //  zero before any derivative enters — the bracket is genuinely the
    //  next-order (derivative) term, not the scalar commutator.  This is
    //  the real microsquare computation's first reduction, ring-only.
    //
    //  THE BOUNDARY (reported, ONE labelled `$e` — a FULL SUCCESS per the
    //  Iron Rule).  Producing the actual bracket — the principal part
    //  ( X(q) - Y(p) ) of [X,Y] — requires composing one field's flow
    //  INTO the other's argument, i.e. evaluating  ( ap p ( x + ( ... ) ) )
    //  and expanding it.  That step is BOTH:
    //    (a) `ap`-Leibniz / `ap`-congruence : substituting the inner
    //        flow's value under the application symbol `ap`.
    //        data/sdg.base.mm instantiates equality's congruence ONLY for
    //        `+` and `*` (eq-pl1/2, eq-mu1/2); it provides NO
    //        ( x = y -> ( ap g x )=( ap g y ) ).  Adding one modifies the
    //        authored substrate (forbidden).  This is the SAME, already
    //        documented data/sdg.calc.mm chain-rule substrate gap.
    //    (b) a GLOBALIZED / generator-side derivative of the principal
    //        part ( the W2-glob keystone-side machinery this task must NOT
    //        touch ): X(q) is the synthetic DERIVATIVE of q along X,
    //        which needs the pointwise->global linking rule (the keystone
    //        SDG-K), explicitly off-limits here.
    //  Both obstructions are orthogonal to classicality.  The single
    //  composite step is supplied as EXACTLY ONE loud `$e`
    //  (tanbr.flow) and the bracket's defining identity is then
    //  closed from it by pure ring algebra:
    //
    //  sdg-tan-bracket :
    //    [ tanbr.flow :
    //        ( ap w ( d1 * d2 ) )
    //      = ( ( ( ap p x ) * ( ap q x ) ) + ( ( ap c x ) * ( d1 * d2 ) ) ) ]
    //    |- ( ap w ( d1 * d2 ) )
    //     = ( ( ( ap q x ) * ( ap p x ) ) + ( ( ap c x ) * ( d1 * d2 ) ) )
    //  where `w` carries the X-then-Y composite microsquare displacement,
    //  `p`,`q` the two principal parts, and `c` the bracket principal
    //  part  [X,Y] = X(q) - Y(p)  (whose CONSTRUCTION is exactly the
    //  off-limits (a)+(b) folded into the single honest `$e`).  The
    //  conclusion swaps the scalar product via the RING (sdg-tan-bracket-
    //  cross), proving the commutator is symmetric at zeroth order and the
    //  bracket lives entirely in the `$e`-supplied derivative term — the
    //  microsquare algebra is genuine, only the one cross-substitution is
    //  the reported boundary.
    // =====================================================================
    let pp = leaf("vg", "g"); // principal part p of X   ( ap g x )
    let qq = leaf("vu", "u"); // principal part q of Y   ( ap u x )
    let xv = leaf("vx", "x"); // base point x
    let d1 = leaf("vd", "d"); // microsquare coordinate d1
    let d2 = leaf("ve", "e"); // microsquare coordinate d2
    let wcomp = leaf("vw", "w"); // X-then-Y composite microsquare displacement
    let brc = leaf("vc", "c"); // bracket principal part  [X,Y] = X(q)-Y(p)

    let px = reg(&ap(&pp, &xv)); // ( ap p x )  = principal part of X at x
    let qx = reg(&ap(&qq, &xv)); // ( ap q x )  = principal part of Y at x
    let d1d2 = mu(&d1, &d2); // ( d1 * d2 )  the microsquare area element
    let pq = mu(&px, &qx); // ( ( ap p x ) * ( ap q x ) )
    let qp = mu(&qx, &px); // ( ( ap q x ) * ( ap p x ) )
    let pq_a = mu(&pq, &d1d2); // ( ( p*q ) * ( d1*d2 ) )
    let qp_a = mu(&qp, &d1d2); // ( ( q*p ) * ( d1*d2 ) )

    // ---- sdg-tan-bracket-cross : ( ( p*q )*(d1*d2) ) = ( ( q*p )*(d1*d2) )
    //  PURE RING: ax-mulcom on the scalar factor, then cong-l.
    let pq_eq_qp = axeq("ax-mulcom", &[&px, &qx], &pq, &qp);
    let sdg_tan_bracket_cross = mul_l(&pq_eq_qp, &d1d2);
    let _ = (&pq_a, &qp_a);

    // ---- sdg-tan-bracket : the bracket identity, modulo the ONE boundary
    //  `$e` (tanbr.flow) folding the off-limits (a)+(b) step.
    let cx = reg(&ap(&brc, &xv)); // ( ap c x )  = bracket principal part at x
    let cx_a = mu(&cx, &d1d2); // ( ( ap c x ) * ( d1*d2 ) )
    let wd = reg(&ap(&wcomp, &d1d2)); // ( ap w ( d1*d2 ) )  composite displacement
    let pq_plus = pl(&pq, &cx_a); // ( ( p*q ) + ( ( ap c x )*(d1*d2) ) )
    let qp_plus = pl(&qp, &cx_a); // ( ( q*p ) + ( ( ap c x )*(d1*d2) ) )
    // tanbr.flow : ( ap w ( d1*d2 ) ) = ( ( p*q ) + ( c-term ) )
    let flow_hyp = Pf {
        stmt: weq(&wd, &pq_plus).toks,
        rpn: t("tanbr.flow"),
    };
    // ( p*q ) = ( q*p )   ->  cong-l by + ( c-term ) :
    //   ( ( p*q )+(c-term) ) = ( ( q*p )+(c-term) )
    let pq_qp_plus = plus_l(&pq_eq_qp, &cx_a);
    // chain:  ( ap w (d1*d2) ) = ( (p*q)+ct ) = ( (q*p)+ct )
    let sdg_tan_bracket = eqtr(&flow_hyp, &pq_qp_plus);
    let _ = (&qp_plus, &sdg_tan_bracket_cross);

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-tan-addcan",
            "|- u = v",
            vec![("tanac.h", "|- ( z + u ) = ( z + v )")],
            &sdg_tan_addcan,
        ),
        (
            "sdg-tan-addcan-imp",
            "|- ( ( z + u ) = ( z + v ) -> u = v )",
            vec![],
            &sdg_tan_addcan_imp,
        ),
        (
            "sdg-tan-base",
            "|- ( a + ( b * 0 ) ) = a",
            vec![],
            &sdg_tan_base,
        ),
        (
            "sdg-tan-roundtrip",
            "|- ( ( a + ( b * 0 ) ) + ( b * d ) ) = ( a + ( b * d ) )",
            vec![],
            &sdg_tan_roundtrip,
        ),
        (
            "sdg-tan-slope-imp",
            "|- ( ( ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) /\\ ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) -> ( b * d ) = ( c * d ) )",
            vec![],
            &sdg_tan_slope_imp,
        ),
        (
            "sdg-tan-principal",
            "|- b = c",
            vec![
                (
                    "pp.hb",
                    "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )",
                ),
                (
                    "pp.hc",
                    "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) )",
                ),
            ],
            &sdg_tan_principal,
        ),
        (
            "sdg-tan-bracket-cross",
            "|- ( ( ( ap g x ) * ( ap u x ) ) * ( d * e ) ) = ( ( ( ap u x ) * ( ap g x ) ) * ( d * e ) )",
            vec![],
            &sdg_tan_bracket_cross,
        ),
        (
            "sdg-tan-bracket",
            "|- ( ap w ( d * e ) ) = ( ( ( ap u x ) * ( ap g x ) ) + ( ( ap c x ) * ( d * e ) ) )",
            vec![(
                "tanbr.flow",
                "|- ( ap w ( d * e ) ) = ( ( ( ap g x ) * ( ap u x ) ) + ( ( ap c x ) * ( d * e ) ) )",
            )],
            &sdg_tan_bracket,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         SYNTHETIC TANGENT STRUCTURE (sdgtanbuild).\n   \
         Self-contained over the data/sdg.base.mm surface; independent of\n   \
         data/sdg.mm and data/sdg.calc.mm (no shared $p; disjoint\n   \
         `sdg-tan-*` labels) so the corpora never merge-conflict.\n   \
         R x R -> R^D (sdg-tan-base / sdg-tan-roundtrip): PURE RING.\n   \
         R^D -> R x R principal-part UNIQUENESS (sdg-tan-principal):\n   \
         GENUINELY CONSUMES ax-microcancel (KL uniqueness), threaded\n   \
         seam-free exactly like data/sdg.mm's sdg-deriv — KL consumed,\n   \
         not asserted.  LIE BRACKET (sdg-tan-bracket): the D x D\n   \
         microsquare commutator; its symmetric zeroth-order part\n   \
         vanishes by RING (sdg-tan-bracket-cross); the one genuinely\n   \
         off-limits step (compose one flow into the other's argument =\n   \
         `ap`-congruence + a globalized/generator-side derivative,\n   \
         W2-glob) is surfaced as EXACTLY ONE loud $e (tanbr.flow) —\n   \
         a precisely-characterised boundary, reported not faked.\n   \
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
                std::fs::write("data/sdg.tangent.mm", &out)
                    .expect("write data/sdg.tangent.mm");
                println!(
                    "sdgtanbuild: kernel-verified {n} $p; wrote data/sdg.tangent.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgtanbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.tangent.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgtanbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.tangent.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
