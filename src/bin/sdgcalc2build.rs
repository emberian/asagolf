//! sdgcalc2build — the SEAM-FREE chain rule, discharging the `chain.sub`
//! ap-Leibniz `$e` of `data/sdg.calc.mm` using the FLAGGED substrate
//! axiom `eq-ap` (the function-application congruence schema).  Writes
//! `data/sdg.calc2.mm`.
//!
//! THE ap-CONGRUENCE VERDICT (B, PROVEN — see data/sdg.base.mm header and
//! SEQUEL_SCOPE §5j).  `x = y -> ( ap g x ) = ( ap g y )` is GENUINELY
//! NOT DERIVABLE from the substrate's equality discipline (reflexivity +
//! symmetry + transitivity + per-operation congruence for + and * ONLY).
//! It is therefore added as ONE named, loudly-flagged, intuitionistically
//! pure (positive Horn) substrate axiom `eq-ap` — NOT smuggled as a
//! derived lemma.  This builder USES eq-ap to re-prove the chain rule
//! with NO `chain.sub` $e: the substitution step
//!   ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b * d ) ) )
//! is now a one-line eq-ap instance off the KL slope hypothesis of f.
//! It ALSO ships `sdg-calc2-apflow`: the Lie-bracket flow-composition
//! ap-Leibniz half (the (a) half of data/sdg.tangent.mm's `tanbr.flow`
//! $e) discharged as a pure eq-pl2+eq-ap derivation — the (b) W2-glob
//! generator-side half is the precisely-characterised residual, NOT
//! closed here (claiming the full bracket would be faking it).
//!
//! COMPOSITION.  Self-contained over the (now eq-ap-extended)
//! data/sdg.base.mm surface; disjoint `sdg-calc2-*` labels; shares no $p
//! with sdg.mm / sdg.calc.mm / sdg.tangent.mm / sdg.taylor.mm; a
//! downstream union is a rename-free concatenation.
//!
//! Run:  cargo run --release --bin sdgcalc2build
//! Trust root = src/kernel.rs re-checking the emitted data/sdg.calc2.mm
//! (and sdgcalc2pure for the purity verdict / MEASURED leaf cost).

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

/// The FLAGGED ap-congruence axiom, applied as a derived inference:
/// from a proof of  `s = u`  produce  `( ap g s ) = ( ap g u )`.
/// eq-ap $a |- ( x = y -> ( ap g x ) = ( ap g y ) ) $.
/// Float order among declared $f: vx (x), vy (y), vg (g).
fn eq_ap(p: &Pf, g: &W) -> Pf {
    let (s, u) = split_eq(&p.stmt);
    let sw = w_of(&s);
    let uw = w_of(&u);
    let lhs = reg(&ap(g, &sw));
    let rhs = reg(&ap(g, &uw));
    let inst = apply(
        "eq-ap",
        &[&sw, &uw, g],
        &[],
        wi(&reg(&weq(&sw, &uw)), &reg(&weq(&lhs, &rhs))).toks,
    );
    mp(p, &inst)
}

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
    let d = leaf("vd", "d");
    let b = leaf("vb", "b");
    let c = leaf("vc", "c");
    let f = leaf("vf", "f");
    let g = leaf("vg", "g");
    let w = leaf("vw", "w");

    // =====================================================================
    //  SEAM-FREE POINTWISE CHAIN RULE — `chain.sub` DISCHARGED via eq-ap.
    //
    //  Hypotheses are now ONLY genuine KL-existence reps + the composite
    //  identity (NO ap-Leibniz $e):
    //    chain.hf : ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )      [KL slope f]
    //    chain.hg : ( ap g ( ( ap f 0 ) + ( b * d ) ) )
    //               = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) ) [KL slope g
    //                                                  at ( ap f 0 ); the
    //                                                  ( b*d ) in D content
    //                                                  is sdg-calc-Dscale,
    //                                                  carried as before]
    //    chain.hh : ( ap w d ) = ( ap g ( ap f d ) )             [ w = g o f ]
    //    chain.hh0: ( ap w 0 ) = ( ap g ( ap f 0 ) )
    //  GOAL :  ( ap w d ) = ( ( ap w 0 ) + ( ( c * b ) * d ) )
    //
    //  The previously-surfaced chain.sub
    //    ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b * d ) ) )
    //  is now DERIVED in one step: eq-ap applied to chain.hf with g := g.
    //  Pointwise; no microcancellation, nothing classical.  Genuinely SDG
    //  content unchanged; only the ap-Leibniz seam is now discharged by
    //  the FLAGGED substrate axiom rather than an $e hypothesis.
    // =====================================================================
    let fd = reg(&ap(&f, &d));
    let f0 = reg(&ap(&f, &zero));
    let bd_w = mu(&b, &d);
    let f0_bd_w = pl(&f0, &bd_w);
    let g_apfd = reg(&ap(&g, &fd));
    let g_f0bd = reg(&ap(&g, &f0_bd_w));
    let g_f0 = reg(&ap(&g, &f0));
    let cbd = mu(&c, &bd_w); // ( c * ( b * d ) )
    let g_f0_cbd = pl(&g_f0, &cbd);
    let cb = mu(&c, &b);
    let cb_d = mu(&cb, &d); // ( ( c * b ) * d )
    let wd_ch = reg(&ap(&w, &d));
    let w0_ch = reg(&ap(&w, &zero));

    // hypotheses as $e leaves
    let ch_hf = Pf { stmt: weq(&fd, &f0_bd_w).toks, rpn: t("chain.hf") };
    let ch_hg = Pf { stmt: weq(&g_f0bd, &g_f0_cbd).toks, rpn: t("chain.hg") };
    let ch_hh = Pf { stmt: weq(&wd_ch, &g_apfd).toks, rpn: t("chain.hh") };
    let ch_hh0 = Pf { stmt: weq(&w0_ch, &g_f0).toks, rpn: t("chain.hh0") };

    // DERIVED ap-Leibniz: ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b*d ) ) )
    let ch_sub = eq_ap(&ch_hf, &g);
    assert_eq!(
        ch_sub.stmt,
        weq(&g_apfd, &g_f0bd).toks,
        "derived ap-Leibniz step has wrong statement"
    );

    // ( ap w d ) = ( ap g ( ap f d ) ) = ( ap g (f0+b*d) )
    //            = ( ap g (ap f 0) + c*(b*d) )
    let ch1 = chain(&[ch_hh.clone(), ch_sub.clone(), ch_hg.clone()]);
    // c*(b*d) = (c*b)*d                                       sym ax-mulass
    let ch_scal = eqsym(&axeq("ax-mulass", &[&c, &b, &d], &cb_d, &cbd));
    // ( g_f0 + c*(b*d) ) = ( g_f0 + (c*b)*d )                 cong-r
    let ch2 = plus_r(&ch_scal, &g_f0);
    // ( g_f0 + (c*b)*d ) = ( w0 + (c*b)*d )                   cong-l sym HH0
    let ch3 = plus_l(&eqsym(&ch_hh0), &cb_d);
    let sdg_chain = chain(&[ch1, ch2, ch3]);
    let chain_goal = weq(&wd_ch, &reg(&pl(&w0_ch, &cb_d)));
    assert_eq!(
        sdg_chain.stmt, chain_goal.toks,
        "seam-free chain rule statement mismatch"
    );

    // =====================================================================
    //  LIE-BRACKET `ap`-HALF DEMONSTRATION  (sdg-calc2-apflow).
    //
    //  data/sdg.tangent.mm closes the Lie bracket modulo ONE labelled $e
    //  `tanbr.flow`, which §5i documents as BOTH (a) ap-congruence AND
    //  (b) W2-glob generator-side globalization, folded together.  This
    //  lemma mechanically discharges HALF (a) — the ap-Leibniz / flow-
    //  composition substitution — showing it is now a PURE derivation
    //  off eq-ap.  Half (b) (X(q) is the synthetic DERIVATIVE of q along
    //  X, needing the pointwise->global linking rule SDG-K) remains the
    //  precisely-characterised residual and is NOT closed here (claiming
    //  the full bracket would be faking it).
    //
    //  The off-limits flow-composition step of tanbr.flow is, abstractly:
    //  from the inner flow value  ( ap f d ) = z  conclude
    //    ( ap g ( x + ( ap f d ) ) ) = ( ap g ( x + z ) )
    //  i.e. substitute the inner flow under the OUTER field's `ap`.  This
    //  is exactly an eq-pl2 (congruence of + on the right) followed by
    //  eq-ap (the now-flagged ap-congruence) — NO $e, NO globalization,
    //  NO classical principle.  The hypothesis flow.inner abstracts the
    //  inner flow's value `z`; identifying `z` with the expanded affine
    //  flow and reading the derivative coefficient off it is precisely
    //  residual half (b), deliberately left as the abstract `z`.
    // =====================================================================
    let zt = reg(&leaf("vz", "z"));
    let x = reg(&leaf("vx", "x"));
    let x_fd = pl(&x, &fd); // ( x + ( ap f d ) )
    let x_z = pl(&x, &zt); // ( x + z )
    let g_x_fd = reg(&ap(&g, &x_fd));
    let g_x_z = reg(&ap(&g, &x_z));

    let flow_inner = Pf { stmt: weq(&fd, &zt).toks, rpn: t("flow.inner") };
    // ( x + ( ap f d ) ) = ( x + z )            eq-pl2 (right-congruence of +)
    let step_pl = plus_r(&flow_inner, &x);
    // ( ap g ( x + ( ap f d ) ) ) = ( ap g ( x + z ) )   eq-ap (ap-cong)
    let sdg_apflow = eq_ap(&step_pl, &g);
    let apflow_goal = weq(&g_x_fd, &g_x_z);
    assert_eq!(
        sdg_apflow.stmt, apflow_goal.toks,
        "ap-flow half statement mismatch"
    );

    // =====================================================================
    //  emit
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
        "sdg-calc2-chain",
        "|- ( ap w d ) = ( ( ap w 0 ) + ( ( c * b ) * d ) )",
        vec![
            ("chain.hf", "|- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )"),
            (
                "chain.hg",
                "|- ( ap g ( ( ap f 0 ) + ( b * d ) ) ) = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) )",
            ),
            ("chain.hh", "|- ( ap w d ) = ( ap g ( ap f d ) )"),
            ("chain.hh0", "|- ( ap w 0 ) = ( ap g ( ap f 0 ) )"),
        ],
        &sdg_chain,
        ),
        (
            "sdg-calc2-apflow",
            "|- ( ap g ( x + ( ap f d ) ) ) = ( ap g ( x + z ) )",
            vec![("flow.inner", "|- ( ap f d ) = z")],
            &sdg_apflow,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         SEAM-FREE CHAIN RULE (sdgcalc2build) — the ap-congruence keystone.\n   \
         The `chain.sub` ap-Leibniz $e of data/sdg.calc.mm is DISCHARGED:\n   \
         ap-congruence is verdict B (NOT derivable — see data/sdg.base.mm\n   \
         header + SEQUEL_SCOPE §5j), so it is the FLAGGED positive-Horn\n   \
         substrate axiom eq-ap; this $p USES eq-ap (one inference) to\n   \
         derive the substitution step.  No microcancellation, no\n   \
         classical principle, no $e for the substitution.  Self-contained\n   \
         over the eq-ap-extended data/sdg.base.mm; disjoint sdg-calc2-*\n   \
         labels; composes by concatenation with the other corpora.\n   \
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
        writeln!(out, "${{").unwrap();
        for (hl, hs) in hyps {
            writeln!(out, "  {hl} $e {hs} $.").unwrap();
        }
        writeln!(out, "  {name} $p {stmt} $= {} $.", pf.rpn.join(" ")).unwrap();
        writeln!(out, "$}}").unwrap();
    }

    match kernel::Db::parse(&out) {
        Ok(db) => match db.verify() {
            Ok(()) => {
                let n = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
                std::fs::write("data/sdg.calc2.mm", &out).expect("write data/sdg.calc2.mm");
                println!("sdgcalc2build: kernel-verified {n} $p; wrote data/sdg.calc2.mm OK");
            }
            Err(e) => {
                eprintln!("sdgcalc2build: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.calc2.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgcalc2build: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.calc2.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
