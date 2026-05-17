//! sdgcalcbuild — constructs the kernel-verified POINTWISE synthetic
//! differentiation rules (SUM / PRODUCT-Leibniz / CHAIN) and writes
//! data/sdg.calc.mm.
//!
//! COMPOSITION / why a SEPARATE file.  This file is fully self-contained:
//! it embeds the certified-intuitionistic substrate base verbatim
//! (data/sdg.base.mm — the SAME trust surface sdgpure audits) and appends
//! ONLY new pointwise-calculus $p.  It deliberately does NOT touch
//! data/sdg.mm so it cannot merge-conflict with the other in-flight SDG
//! agents that own data/sdg.mm.  Intended composition: data/sdg.mm and
//! data/sdg.calc.mm are two independent kernel-checked corpora over the
//! IDENTICAL data/sdg.base.mm axiom surface; a downstream union is a
//! no-op rename-free concatenation of their $p blocks (disjoint labels,
//! `sdg-calc-*`).  Both are independently re-checked by the kernel and by
//! sdgpure.
//!
//! POINTWISE ONLY (SEQUEL_SCOPE §5b).  Every rule is stated as the
//! existence (from KL — the affine slope reps are the $e hypotheses,
//! exactly mirroring data/sdg.mm's `sdg-slope` shape) PLUS the pointwise
//! identifying equation.  NOTHING here invokes ax-microcancel, ax-gen
//! over a linking universal, or the pointwise->global seam.  Staying
//! pointwise is the point; globalisation is the separate keystone SDG-K.
//!
//! Run:  cargo run --release --bin sdgcalcbuild
//!
//! UNTRUSTED scaffolding.  Trust root = src/kernel.rs re-checking the
//! emitted data/sdg.calc.mm (run `cargo run --bin sdgcalcfloor` and
//! `cargo run --bin sdgcalcpure`).

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

fn wb(a: &W, b: &W) -> W {
    W {
        rpn: rpn_app(&[&a.rpn, &b.rpn], "wb"),
        toks: {
            let mut v = vec!["(".into()];
            v.extend(a.toks.clone());
            v.push("<->".into());
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

fn refl(w: &W) -> Pf {
    reg(w);
    apply("eqid", &[w], &[], weq(w, w).toks)
}

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

// addition congruence (both sides)
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

fn main() {
    let base = include_str!("../../data/sdg.base.mm");

    let zero = reg(&W { rpn: t("t0"), toks: t("0") });
    let x = leaf("vx", "x");
    let y = leaf("vy", "y");
    let z = leaf("vz", "z");
    let e = leaf("ve", "e");
    let d = leaf("vd", "d");
    let b = leaf("vb", "b");
    let c = leaf("vc", "c");
    let f = leaf("vf", "f");
    let g = leaf("vg", "g");

    // =====================================================================
    //  RING SCAFFOLD LEMMAS (pure equational algebra, no order, no metric
    //  residue, no classical principle, no microcancellation).
    // =====================================================================

    // ---- sdg-calc-addcan : [ ( z + u ) = ( z + v ) ] |- u = v ----------
    //  reproduced (NOT imported from data/sdg.mm — this file is
    //  self-contained over data/sdg.base.mm).  Same derivation as
    //  data/sdg.mm's sdg-addcan.
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });
    let z_pl_u = pl(&z, &u);
    let z_pl_v = pl(&z, &v);
    let addcan_hyp = Pf { stmt: weq(&z_pl_u, &z_pl_v).toks, rpn: t("addcan.h") };
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
    let sdg_addcan = eqtr(&eqsym(&cu), &eqtr(&s1, &cv));

    // ---- sdg-calc-add4 : |- ( ( x + y ) + ( z + e ) )
    //                          = ( ( x + z ) + ( y + e ) )  (assoc/comm) -
    let xy = pl(&x, &y);
    let ze = pl(&z, &e);
    let yz = pl(&y, &z);
    let zy = pl(&z, &y);
    let ye = pl(&y, &e);
    let xz = pl(&x, &z);
    let yze = pl(&yz, &e);
    let zye = pl(&zy, &e);
    let y_ze = pl(&y, &ze);
    let z_ye = pl(&z, &ye);
    let xy_ze = pl(&xy, &ze);                 // ( ( x + y ) + ( z + e ) )
    let x_yze = pl(&x, &yze);
    let x_zye = pl(&x, &zye);
    let x_zye2 = pl(&x, &z_ye);
    let xz_ye = pl(&xz, &ye);                  // ( ( x + z ) + ( y + e ) )
    // step1: ((x+y)+(z+e)) = (x+(y+(z+e)))                 ax-addass
    let st1 = axeq("ax-addass", &[&x, &y, &ze], &xy_ze, &pl(&x, &y_ze));
    // step2: (y+(z+e)) = ((y+z)+e)                          sym ax-addass
    let st2 = eqsym(&axeq("ax-addass", &[&y, &z, &e], &yze, &y_ze));
    // step2': (x+(y+(z+e))) = (x+((y+z)+e))                 cong-r by st2
    let st2c = plus_r(&st2, &x);
    // step3: (y+z) = (z+y)                                  ax-addcom
    let st3 = axeq("ax-addcom", &[&y, &z], &yz, &zy);
    // step3': ((y+z)+e) = ((z+y)+e)                         cong-l
    let st3e = plus_l(&st3, &e);
    // step3'': (x+((y+z)+e)) = (x+((z+y)+e))                cong-r
    let st3c = plus_r(&st3e, &x);
    // step4: ((z+y)+e) = (z+(y+e))                          ax-addass
    let st4 = axeq("ax-addass", &[&z, &y, &e], &zye, &z_ye);
    let st4c = plus_r(&st4, &x);              // (x+((z+y)+e)) = (x+(z+(y+e)))
    // step5: (x+(z+(y+e))) = ((x+z)+(y+e))                  sym ax-addass
    let st5 = eqsym(&axeq("ax-addass", &[&x, &z, &ye], &xz_ye, &x_zye2));
    let _ = (x_yze, x_zye);
    let sdg_add4 = chain(&[st1, st2c, st3c, st4c, st5]);

    // ---- sdg-calc-rdistr : |- ( ( x + y ) * z )
    //                            = ( ( x * z ) + ( y * z ) )  -----------
    let xpy = pl(&x, &y);
    let xpy_z = mu(&xpy, &z);                  // ( ( x + y ) * z )
    let z_xpy = mu(&z, &xpy);                  // ( z * ( x + y ) )
    let zx = mu(&z, &x);
    let zy_m = mu(&z, &y);
    let zx_zy = pl(&zx, &zy_m);                // ( ( z * x ) + ( z * y ) )
    let xz_m = mu(&x, &z);
    let yz_m = mu(&y, &z);
    let xz_yz = pl(&xz_m, &yz_m);              // ( ( x * z ) + ( y * z ) )
    // ((x+y)*z) = (z*(x+y))                                 ax-mulcom
    let r1 = axeq("ax-mulcom", &[&xpy, &z], &xpy_z, &z_xpy);
    // (z*(x+y)) = ((z*x)+(z*y))                             ax-distr
    let r2 = axeq("ax-distr", &[&z, &x, &y], &z_xpy, &zx_zy);
    // (z*x) = (x*z)  ; (z*y) = (y*z)                        ax-mulcom
    let r3a = axeq("ax-mulcom", &[&z, &x], &zx, &xz_m);
    let r3b = axeq("ax-mulcom", &[&z, &y], &zy_m, &yz_m);
    // ((z*x)+(z*y)) = ((x*z)+(z*y))                         cong-l
    let r3 = plus_l(&r3a, &zy_m);
    // ((x*z)+(z*y)) = ((x*z)+(y*z))                         cong-r
    let r4 = plus_r(&r3b, &xz_m);
    let sdg_rdistr = chain(&[r1, r2, r3, r4]);
    let _ = xz_yz;

    // helper: prove ( ( s + t ) * z ) = ( ( s * z ) + ( t * z ) ) for
    // concrete s,t,z using sdg-calc-rdistr.
    let rdistr = |s: &W, tt: &W, zz: &W| -> Pf {
        let lhs = mu(&pl(s, tt), zz);
        let rhs = pl(&mu(s, zz), &mu(tt, zz));
        use_thm(
            "sdg-calc-rdistr",
            &[("x", s), ("y", tt), ("z", zz)],
            &[],
            weq(&lhs, &rhs).toks,
        )
    };

    // =====================================================================
    //  POINTWISE SUM RULE.
    //  Functions f,g and their pointwise sum carried by h.
    //  HF: ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )      [KL slope of f]
    //  HG: ( ap g d ) = ( ( ap g 0 ) + ( c * d ) )      [KL slope of g]
    //  HH: ( ap h d ) = ( ( ap f d ) + ( ap g d ) )     [h is f+g pointwise]
    //  HH0:( ap h 0 ) = ( ( ap f 0 ) + ( ap g 0 ) )     [ditto at 0]
    //  |-  ( ap h d ) = ( ( ap h 0 ) + ( ( b + c ) * d ) )
    //  Pure ring algebra; does NOT use d*d=0; nothing classical.
    // =====================================================================
    let h = leaf("vw", "w"); // use w as the composite-function symbol
    let f0 = reg(&ap(&f, &zero));
    let fd = reg(&ap(&f, &d));
    let g0 = reg(&ap(&g, &zero));
    let gd = reg(&ap(&g, &d));
    let h0 = reg(&ap(&h, &zero));
    let hd = reg(&ap(&h, &d));
    let bd = mu(&b, &d);
    let cd = mu(&c, &d);
    let f0_bd = pl(&f0, &bd);
    let g0_cd = pl(&g0, &cd);
    let f0_g0 = pl(&f0, &g0);
    let fd_gd = pl(&fd, &gd);
    let bpc = pl(&b, &c);
    let bpc_d = mu(&bpc, &d);
    let h0_bpcd = pl(&h0, &bpc_d);

    let hf = Pf { stmt: weq(&fd, &f0_bd).toks, rpn: t("sum.hf") };
    let hg = Pf { stmt: weq(&gd, &g0_cd).toks, rpn: t("sum.hg") };
    let hh = Pf { stmt: weq(&hd, &fd_gd).toks, rpn: t("sum.hh") };
    let hh0 = Pf { stmt: weq(&h0, &f0_g0).toks, rpn: t("sum.hh0") };

    // ( ap h d ) = ( ( ap f d ) + ( ap g d ) )                 HH
    // = ( ( f0 + b*d ) + ( g0 + c*d ) )                        cong by HF,HG
    let sa = plus_l(&hf, &gd);                 // (fd+gd)=((f0+bd)+gd)
    let sb = plus_r(&hg, &f0_bd);              // ((f0+bd)+gd)=((f0+bd)+(g0+cd))
    let s_expand = eqtr(&hh, &eqtr(&sa, &sb));
    // ( (f0+bd)+(g0+cd) ) = ( (f0+g0)+(bd+cd) )                sdg-calc-add4
    let bd_cd = pl(&bd, &cd);
    let f0g0_bdcd = pl(&f0_g0, &bd_cd);
    let s_shuffle = use_thm(
        "sdg-calc-add4",
        &[("x", &f0), ("y", &bd), ("z", &g0), ("e", &cd)],
        &[],
        weq(
            &pl(&f0_bd, &g0_cd),
            &f0g0_bdcd,
        )
        .toks,
    );
    // ( bd + cd ) = ( ( b + c ) * d )                          sym rdistr
    let s_dist = eqsym(&rdistr(&b, &c, &d));   // ((b+c)*d)=((b*d)+(c*d)) -> sym
    // ( (f0+g0)+(bd+cd) ) = ( (f0+g0)+((b+c)*d) )              cong-r
    let s_dc = plus_r(&s_dist, &f0_g0);
    // ( (f0+g0)+((b+c)*d) ) = ( h0 + ((b+c)*d) )               cong-l sym HH0
    let s_h0 = plus_l(&eqsym(&hh0), &bpc_d);
    let sdg_sum = chain(&[s_expand, s_shuffle, s_dc, s_h0]);
    assert_eq!(sdg_sum.stmt, weq(&hd, &h0_bpcd).toks);

    // =====================================================================
    //  POINTWISE PRODUCT (LEIBNIZ) RULE — the canonical SDG proof.
    //  HF: ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )
    //  HG: ( ap g d ) = ( ( ap g 0 ) + ( c * d ) )
    //  HH: ( ap h d ) = ( ( ap f d ) * ( ap g d ) )    [h is f*g pointwise]
    //  HH0:( ap h 0 ) = ( ( ap f 0 ) * ( ap g 0 ) )
    //  HD: ( D d )                                      [d infinitesimal]
    //  |-  ( ap h d )
    //      = ( ( ap h 0 ) + ( ( ( ( ap f 0 ) * c ) + ( b * ( ap g 0 ) ) ) * d ) )
    //  GENUINELY consumes d*d=0 (via df-D applied to HD): the second-order
    //  term ( b*d ) * ( c*d ) collapses to 0 because d*d=0.  Without
    //  d*d=0 the Leibniz coefficient would carry a (b*c)*(d*d) remainder.
    // =====================================================================
    let dd_pred = reg(&wD(&d));
    let hd2 = Pf { stmt: weq(&hd, &reg(&mu(&fd, &gd))).toks, rpn: t("prod.hh") };
    let hh0p = Pf { stmt: weq(&h0, &reg(&mu(&f0, &g0))).toks, rpn: t("prod.hh0") };
    let hDp = Pf { stmt: wD(&d).toks, rpn: t("prod.hD") };

    // ( ap h d ) = ( ( f0+bd ) * ( g0+cd ) )
    let p_lhs = mu(&fd, &gd);
    let pa = mul_l(&hf, &gd);                  // (fd*gd) = ((f0+bd)*gd)
    let pb = mul_r(&hg, &f0_bd);               // ((f0+bd)*gd)=((f0+bd)*(g0+cd))
    let p_expand0 = eqtr(&hd2, &eqtr(&pa, &pb));
    let _ = p_lhs;

    // ((f0+bd)*(g0+cd)) = ((f0+bd)*g0)+((f0+bd)*cd)            ax-distr
    let fbd = f0_bd.clone();
    let fbd_g0 = mu(&fbd, &g0);
    let fbd_cd = mu(&fbd, &cd);
    let p1 = axeq("ax-distr", &[&fbd, &g0, &cd], &reg(&mu(&fbd, &g0_cd)), &reg(&pl(&fbd_g0, &fbd_cd)));
    // ((f0+bd)*g0) = (f0*g0)+(bd*g0)                           rdistr
    let f0g0 = mu(&f0, &g0);
    let bd_g0 = mu(&bd, &g0);
    let p2 = rdistr(&f0, &bd, &g0);            // ((f0+bd)*g0)=((f0*g0)+(bd*g0))
    // ((f0+bd)*cd) = (f0*cd)+(bd*cd)                           rdistr
    let f0_cd = mu(&f0, &cd);
    let bd_cd_m = mu(&bd, &cd);
    let p3 = rdistr(&f0, &bd, &cd);            // ((f0+bd)*cd)=((f0*cd)+(bd*cd))
    // assemble:  P*(...) = ( (f0g0+bd*g0) + (f0*cd+bd*cd) )
    let p_step = eqtr(
        &p1,
        &eqtr(
            &plus_l(&p2, &fbd_cd),
            &plus_r(&p3, &reg(&pl(&f0g0, &bd_g0))),
        ),
    );
    // now expr = ( ( f0*g0 + bd*g0 ) + ( f0*cd + bd*cd ) )

    // -- the SDG heart: ( bd * cd ) = 0  because d*d = 0. -----------------
    // ( b*d )*( c*d ) = ( b*c )*( d*d )  by assoc/comm; then d*d=0 (df-D
    // on HD) ; then ( b*c )*0 = 0 (ax-mul0).
    let bc = mu(&b, &c);
    let dd_m = mu(&d, &d);
    let bc_dd = mu(&bc, &dd_m);
    // step: ( (b*d)*(c*d) ) = ( (b*c)*(d*d) )
    //   (b*d)*(c*d) = b*(d*(c*d))            ax-mulass [b,d,(c*d)]
    let d_cd = mu(&d, &cd);
    let q1 = axeq("ax-mulass", &[&b, &d, &cd], &reg(&mu(&bd, &cd)), &reg(&mu(&b, &d_cd)));
    //   d*(c*d) = (d*c)*d                    sym ax-mulass [d,c,d]
    let dc = mu(&d, &c);
    let q2 = eqsym(&axeq("ax-mulass", &[&d, &c, &d], &reg(&mu(&dc, &d)), &reg(&mu(&d, &cd))));
    //   (d*c) = (c*d)                        ax-mulcom
    let q3 = axeq("ax-mulcom", &[&d, &c], &dc, &cd);
    //   (d*c)*d = (c*d)*d                    cong-l
    let q3e = mul_l(&q3, &d);
    //   (c*d)*d = c*(d*d)                    ax-mulass [c,d,d]
    let q4 = axeq("ax-mulass", &[&c, &d, &d], &reg(&mu(&cd, &d)), &reg(&mu(&c, &dd_m)));
    //   d*(c*d) = c*(d*d)
    let d_cd_eq = chain(&[q2, q3e, q4]);
    //   b*(d*(c*d)) = b*(c*(d*d))            cong-r
    let q5 = mul_r(&d_cd_eq, &b);
    //   b*(c*(d*d)) = (b*c)*(d*d)            sym ax-mulass [b,c,(d*d)]
    let q6 = eqsym(&axeq("ax-mulass", &[&b, &c, &dd_m], &bc_dd, &reg(&mu(&b, &reg(&mu(&c, &dd_m))))));
    let bd_cd_to_bcdd = chain(&[q1, q5, q6]); // (b*d)*(c*d) = (b*c)*(d*d)
    // d*d = 0  via df-D applied to HD
    //   df-D[x:=d] : ( ( D d ) <-> ( d*d ) = 0 )
    let dd_eq0_w = reg(&weq(&dd_m, &zero));
    let bicond = reg(&wb(&dd_pred, &dd_eq0_w));
    let dfd = apply("df-D", &[&d], &[], bicond.toks.clone());
    let bi1 = apply("ax-bi1", &[&dd_pred, &dd_eq0_w], &[], wi(&bicond, &reg(&wi(&dd_pred, &dd_eq0_w))).toks);
    let dd_imp = mp(&dfd, &bi1);               // ( ( D d ) -> ( d*d )=0 )
    let dd_eq0 = mp(&hDp, &dd_imp);            // |- ( d*d ) = 0
    //   (b*c)*(d*d) = (b*c)*0                cong-r
    let q7 = mul_r(&dd_eq0, &bc);
    //   (b*c)*0 = 0                          ax-mul0
    let q8 = axeq("ax-mul0", &[&bc], &reg(&mu(&bc, &zero)), &zero);
    let bdcd_eq0 = chain(&[bd_cd_to_bcdd, q7, q8]); // (b*d)*(c*d) = 0

    // collapse ( f0*cd + bd*cd ) using bd*cd = 0:
    //   ( f0*cd + bd*cd ) = ( f0*cd + 0 ) = f0*cd
    let p_drop = {
        let s = plus_r(&bdcd_eq0, &f0_cd);     // (f0*cd + bd*cd) = (f0*cd + 0)
        let z0 = axeq("ax-add0", &[&f0_cd], &reg(&pl(&f0_cd, &zero)), &f0_cd);
        eqtr(&s, &z0)
    };
    // so ( (f0g0+bd*g0) + (f0*cd+bd*cd) ) = ( (f0g0+bd*g0) + f0*cd )
    let p_after_drop = plus_r(&p_drop, &reg(&pl(&f0g0, &bd_g0)));

    // Rearrange ( (f0g0 + bd*g0) + f0*cd )
    //   = ( f0g0 + ( bd*g0 + f0*cd ) )                        ax-addass
    let bdg0_f0cd = pl(&bd_g0, &f0_cd);
    let p_assoc = axeq(
        "ax-addass",
        &[&f0g0, &bd_g0, &f0_cd],
        &reg(&pl(&reg(&pl(&f0g0, &bd_g0)), &f0_cd)),
        &reg(&pl(&f0g0, &bdg0_f0cd)),
    );

    // ( bd*g0 + f0*cd ) = ( ( f0*c + b*g0 ) * d )
    //   bd*g0 = (b*g0)*d : (b*d)*g0 = b*(d*g0)=b*(g0*d)=(b*g0)*d
    let dg0 = mu(&d, &g0);
    let g0d = mu(&g0, &d);
    let bg0 = mu(&b, &g0);
    let r_bdg0 = chain(&[
        axeq("ax-mulass", &[&b, &d, &g0], &reg(&mu(&bd, &g0)), &reg(&mu(&b, &dg0))), // (b*d)*g0=b*(d*g0)
        mul_r(&axeq("ax-mulcom", &[&d, &g0], &dg0, &g0d), &b),                       // b*(d*g0)=b*(g0*d)
        eqsym(&axeq("ax-mulass", &[&b, &g0, &d], &reg(&mu(&bg0, &d)), &reg(&mu(&b, &g0d)))), // b*(g0*d)=(b*g0)*d
    ]); // ( bd*g0 ) = ( (b*g0)*d )
    //   f0*cd = (f0*c)*d : f0*(c*d)=(f0*c)*d (sym ax-mulass)
    let f0c = mu(&f0, &c);
    let r_f0cd = eqsym(&axeq("ax-mulass", &[&f0, &c, &d], &reg(&mu(&f0c, &d)), &reg(&mu(&f0, &cd))));
    // ( bd*g0 + f0*cd ) = ( (b*g0)*d + (f0*c)*d )
    let r_pair = eqtr(&plus_l(&r_bdg0, &f0_cd), &plus_r(&r_f0cd, &reg(&mu(&bg0, &d))));
    // ( (b*g0)*d + (f0*c)*d ) = ( ( b*g0 + f0*c ) * d )       sym rdistr
    let r_fold = eqsym(&rdistr(&bg0, &f0c, &d)); // ((b*g0)+(f0*c))*d -> sym
    // ( (b*g0)+(f0*c) ) = ( (f0*c)+(b*g0) )                   ax-addcom -> cong-l
    let r_comm = axeq("ax-addcom", &[&bg0, &f0c], &reg(&pl(&bg0, &f0c)), &reg(&pl(&f0c, &bg0)));
    let r_comm_d = cong_l(&r_comm, &d, "*", "tmu", "eq-mu1"); // ((b*g0+f0*c)*d)=((f0*c+b*g0)*d)
    let coeff = pl(&f0c, &bg0);                 // ( ( f0*c ) + ( b*g0 ) )
    let coeff_d = mu(&coeff, &d);
    let r_coef = chain(&[r_pair, r_fold, r_comm_d]); // (bd*g0+f0*cd) = (coeff*d)
    //   ( f0g0 + ( bd*g0 + f0*cd ) ) = ( f0g0 + ( coeff * d ) )   cong-r
    let p_coef = plus_r(&r_coef, &f0g0);
    //   ( f0g0 + (coeff*d) ) = ( h0 + (coeff*d) )                 cong-l sym HH0
    let p_h0 = plus_l(&eqsym(&hh0p), &coeff_d);

    let sdg_prod = chain(&[
        p_expand0, p_step, p_after_drop, p_assoc, p_coef, p_h0,
    ]);
    let prod_goal = weq(&hd, &reg(&pl(&h0, &coeff_d)));
    assert_eq!(sdg_prod.stmt, prod_goal.toks, "product rule statement mismatch");

    // =====================================================================
    //  sdg-calc-Dscale : [ ( D d ) ] |- ( D ( b * d ) )
    //  The genuine SDG content underpinning the chain rule: an R-scaling
    //  of an infinitesimal is infinitesimal.  Consumes d*d=0.
    //  ( b*d )*( b*d ) = ( b*b )*( d*d ) = ( b*b )*0 = 0  ==>  ( D (b*d) ).
    // =====================================================================
    let bd_w = mu(&b, &d);
    let bd_bd = mu(&bd_w, &bd_w);
    let bb = mu(&b, &b);
    let bb_dd = mu(&bb, &dd_m);
    // ( b*d )*( b*d ) = ( b*b )*( d*d )
    //   (b*d)*(b*d) = b*(d*(b*d))          ax-mulass [b,d,(b*d)]
    let d_bd = mu(&d, &bd_w);
    let c1 = axeq("ax-mulass", &[&b, &d, &bd_w], &bd_bd, &reg(&mu(&b, &d_bd)));
    //   d*(b*d) = (d*b)*d                  sym ax-mulass [d,b,d]
    let db = mu(&d, &b);
    let c2 = eqsym(&axeq("ax-mulass", &[&d, &b, &d], &reg(&mu(&db, &d)), &reg(&mu(&d, &bd_w))));
    //   (d*b) = (b*d)                      ax-mulcom
    let c3 = mul_l(&axeq("ax-mulcom", &[&d, &b], &db, &bd_w), &d); // (d*b)*d=(b*d)*d
    //   (b*d)*d = b*(d*d)                  ax-mulass [b,d,d]
    let c4 = axeq("ax-mulass", &[&b, &d, &d], &reg(&mu(&bd_w, &d)), &reg(&mu(&b, &dd_m)));
    //   d*(b*d) = b*(d*d)
    let d_bd_eq = chain(&[c2, c3, c4]);
    //   b*(d*(b*d)) = b*(b*(d*d))          cong-r
    let c5 = mul_r(&d_bd_eq, &b);
    //   b*(b*(d*d)) = (b*b)*(d*d)          sym ax-mulass
    let c6 = eqsym(&axeq("ax-mulass", &[&b, &b, &dd_m], &bb_dd, &reg(&mu(&b, &reg(&mu(&b, &dd_m))))));
    let bdbd_to_bbdd = chain(&[c1, c5, c6]);
    //   (b*b)*(d*d) = (b*b)*0              cong-r by dd_eq0 (df-D on HD)
    let dd_eq0_2 = {
        let dfd2 = apply("df-D", &[&d], &[], reg(&wb(&dd_pred, &dd_eq0_w)).toks.clone());
        let bi1_2 = apply("ax-bi1", &[&dd_pred, &dd_eq0_w], &[], wi(&reg(&wb(&dd_pred, &dd_eq0_w)), &reg(&wi(&dd_pred, &dd_eq0_w))).toks);
        let imp = mp(&dfd2, &bi1_2);
        let hDp2 = Pf { stmt: wD(&d).toks, rpn: t("dsc.hD") };
        mp(&hDp2, &imp)
    };
    let c7 = mul_r(&dd_eq0_2, &bb);
    let c8 = axeq("ax-mul0", &[&bb], &reg(&mu(&bb, &zero)), &zero);
    let bdbd_eq0 = chain(&[bdbd_to_bbdd, c7, c8]); // ( (b*d)*(b*d) ) = 0
    // ( D (b*d) )  via df-D <- direction (ax-bi2)
    let dbd = reg(&wD(&bd_w));
    let bdbd_eq0_w = reg(&weq(&bd_bd, &zero));
    let bicond2 = reg(&wb(&dbd, &bdbd_eq0_w));
    let dfd3 = apply("df-D", &[&bd_w], &[], bicond2.toks.clone());
    let bi2 = apply("ax-bi2", &[&dbd, &bdbd_eq0_w], &[], wi(&bicond2, &reg(&wi(&bdbd_eq0_w, &dbd))).toks);
    let eq0_imp_D = mp(&dfd3, &bi2);           // ( ( (b*d)*(b*d) )=0 -> ( D (b*d) ) )
    let sdg_dscale = mp(&bdbd_eq0, &eq0_imp_D);
    assert_eq!(sdg_dscale.stmt, wD(&bd_w).toks);

    // =====================================================================
    //  POINTWISE CHAIN RULE  (with the substrate-gap surfaced honestly).
    //
    //  HONEST OBSTRUCTION (reported, not faked).  Composing f's affine
    //  expansion INTO g's argument is Leibniz-substitution under the
    //  function-application symbol `ap`.  data/sdg.base.mm instantiates
    //  Leibniz (eqid/eqcom/eqtri + congruence) ONLY for the ring
    //  operations + / * (eq-pl1/2, eq-mu1/2).  It provides NO
    //  congruence `x = y -> ( ap g x ) = ( ap g y )`.  Adding one would
    //  be modifying the authored substrate (forbidden) — and it is a
    //  substrate-instantiation gap, NOT a classical principle and NOT
    //  the pointwise->global keystone.  So the SINGLE ap-Leibniz instance
    //  is supplied as an explicit, loudly-labelled $e hypothesis
    //  `chain.sub`; everything else (the increment is infinitesimal:
    //  sdg-calc-Dscale, consuming d*d=0; and the scalar collapse
    //  c*(b*d) = (c*b)*d) is genuinely derived.
    //
    //  HF:  ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )          [KL slope of f]
    //  SUB: ( ap g ( ap f d ) )
    //         = ( ap g ( ( ap f 0 ) + ( b * d ) ) )           [ap-Leibniz; the gap]
    //  HG:  ( ap g ( ( ap f 0 ) + ( b * d ) ) )
    //         = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) )   [KL slope of g
    //                                                           at ( ap f 0 ),
    //                                                           valid since
    //                                                           ( b*d ) in D —
    //                                                           sdg-calc-Dscale]
    //  HH:  ( ap h d ) = ( ap g ( ap f d ) )                  [h = g o f]
    //  HH0: ( ap h 0 ) = ( ap g ( ap f 0 ) )
    //  |-   ( ap h d ) = ( ( ap h 0 ) + ( ( c * b ) * d ) )
    //  Pointwise; no microcancellation, nothing classical.
    // =====================================================================
    let f0_bd_w = pl(&f0, &bd_w);
    let g_apfd = reg(&ap(&g, &fd));
    let g_f0bd = reg(&ap(&g, &f0_bd_w));
    let g_f0 = reg(&ap(&g, &f0));
    let cbd = mu(&c, &bd_w);                    // ( c * ( b * d ) )
    let g_f0_cbd = pl(&g_f0, &cbd);
    let cb = mu(&c, &b);
    let cb_d = mu(&cb, &d);                     // ( ( c * b ) * d )
    let hd_ch = reg(&ap(&h, &d));
    let h0_ch = reg(&ap(&h, &zero));

    let ch_hh = Pf { stmt: weq(&hd_ch, &g_apfd).toks, rpn: t("chain.hh") };
    let ch_sub = Pf { stmt: weq(&g_apfd, &g_f0bd).toks, rpn: t("chain.sub") };
    let ch_hg = Pf { stmt: weq(&g_f0bd, &g_f0_cbd).toks, rpn: t("chain.hg") };
    let ch_hh0 = Pf { stmt: weq(&h0_ch, &g_f0).toks, rpn: t("chain.hh0") };

    // ( ap h d ) = ( ap g ( ap f d ) ) = ( ap g (f0+b*d) )
    //            = ( ap g (ap f 0) + c*(b*d) )
    let ch1 = chain(&[ch_hh.clone(), ch_sub.clone(), ch_hg.clone()]);
    // c*(b*d) = (c*b)*d                                       sym ax-mulass
    let ch_scal = eqsym(&axeq("ax-mulass", &[&c, &b, &d], &cb_d, &cbd));
    // ( g_f0 + c*(b*d) ) = ( g_f0 + (c*b)*d )                 cong-r
    let ch2 = plus_r(&ch_scal, &g_f0);
    // ( g_f0 + (c*b)*d ) = ( h0 + (c*b)*d )                   cong-l sym HH0
    let ch3 = plus_l(&eqsym(&ch_hh0), &cb_d);
    let sdg_chain = chain(&[ch1, ch2, ch3]);
    let chain_goal = weq(&hd_ch, &reg(&pl(&h0_ch, &cb_d)));
    assert_eq!(sdg_chain.stmt, chain_goal.toks, "chain rule statement mismatch");

    // =====================================================================
    //  assemble + emit
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-calc-addcan",
            "|- u = v",
            vec![("addcan.h", "|- ( z + u ) = ( z + v )")],
            &sdg_addcan,
        ),
        (
            "sdg-calc-add4",
            "|- ( ( x + y ) + ( z + e ) ) = ( ( x + z ) + ( y + e ) )",
            vec![],
            &sdg_add4,
        ),
        (
            "sdg-calc-rdistr",
            "|- ( ( x + y ) * z ) = ( ( x * z ) + ( y * z ) )",
            vec![],
            &sdg_rdistr,
        ),
        (
            "sdg-calc-sum",
            "|- ( ap w d ) = ( ( ap w 0 ) + ( ( b + c ) * d ) )",
            vec![
                ("sum.hf", "|- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )"),
                ("sum.hg", "|- ( ap g d ) = ( ( ap g 0 ) + ( c * d ) )"),
                ("sum.hh", "|- ( ap w d ) = ( ( ap f d ) + ( ap g d ) )"),
                ("sum.hh0", "|- ( ap w 0 ) = ( ( ap f 0 ) + ( ap g 0 ) )"),
            ],
            &sdg_sum,
        ),
        (
            "sdg-calc-prod",
            "|- ( ap w d ) = ( ( ap w 0 ) + ( ( ( ( ap f 0 ) * c ) + ( b * ( ap g 0 ) ) ) * d ) )",
            vec![
                ("prod.hf", "|- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )"),
                ("prod.hg", "|- ( ap g d ) = ( ( ap g 0 ) + ( c * d ) )"),
                ("prod.hh", "|- ( ap w d ) = ( ( ap f d ) * ( ap g d ) )"),
                ("prod.hh0", "|- ( ap w 0 ) = ( ( ap f 0 ) * ( ap g 0 ) )"),
                ("prod.hD", "|- ( D d )"),
            ],
            &sdg_prod,
        ),
        (
            "sdg-calc-Dscale",
            "|- ( D ( b * d ) )",
            vec![("dsc.hD", "|- ( D d )")],
            &sdg_dscale,
        ),
        (
            "sdg-calc-chain",
            "|- ( ap w d ) = ( ( ap w 0 ) + ( ( c * b ) * d ) )",
            vec![
                ("chain.hh", "|- ( ap w d ) = ( ap g ( ap f d ) )"),
                (
                    "chain.sub",
                    "|- ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b * d ) ) )",
                ),
                (
                    "chain.hg",
                    "|- ( ap g ( ( ap f 0 ) + ( b * d ) ) ) = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) )",
                ),
                ("chain.hh0", "|- ( ap w 0 ) = ( ap g ( ap f 0 ) )"),
            ],
            &sdg_chain,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         POINTWISE SYNTHETIC DIFFERENTIATION RULES (sdgcalcbuild).\n   \
         Self-contained over the data/sdg.base.mm surface; independent of\n   \
         data/sdg.mm (no shared $p; disjoint `sdg-calc-*` labels) so the\n   \
         two corpora never merge-conflict.  POINTWISE ONLY: no\n   \
         ax-microcancel, no ax-gen over a linking universal, no\n   \
         pointwise->global seam (that is the separate keystone SDG-K).\n   \
         SUM: pure ring.  PRODUCT (Leibniz): genuinely consumes d*d=0.\n   \
         Dscale: R-scaling of an infinitesimal is infinitesimal (d*d=0).\n   \
         CHAIN: derived modulo ONE explicit ap-Leibniz $e (chain.sub) —\n   \
         the substrate instantiates congruence only for + and * , not\n   \
         for the application symbol `ap`; surfaced, not faked.\n   \
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
                std::fs::write("data/sdg.calc.mm", &out).expect("write data/sdg.calc.mm");
                println!("sdgcalcbuild: kernel-verified {n} $p; wrote data/sdg.calc.mm OK");
            }
            Err(e) => {
                eprintln!("sdgcalcbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.calc.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgcalcbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.calc.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
