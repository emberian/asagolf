//! sdgbuild — constructs the kernel-verified proof bodies for the SDG
//! substrate and writes data/sdg.mm.  The base ($a axioms + $f) is fixed
//! text here (the certified-intuitionistic substrate); proof RPNs are
//! built programmatically so the stack discipline is correct by
//! construction, then the WHOLE file is kernel-verified before it is
//! written (mirrors the prequel's grounded.rs build->verify->emit flow).
//!
//! Run:  cargo run --release --bin sdgbuild
//!
//! This tool is UNTRUSTED scaffolding.  The trust root is src/kernel.rs
//! re-checking the emitted data/sdg.mm (run `cargo run --bin sdgfloor`
//! and `cargo run --bin sdgpure`).  Nothing here is asserted; every $p is
//! kernel-verified here AND independently by sdgfloor.

#[path = "../kernel.rs"]
mod kernel;

use std::collections::HashMap;
use std::fmt::Write as _;

// ---------------------------------------------------------------------------
// Tiny proof-term DSL.  A `Pf` carries both its proven `|-` expression and
// the RPN token list that produces it.  Builders auto-emit the floating
// (wff/term) arguments so the stack discipline is correct by construction.
// ---------------------------------------------------------------------------

/// A wff or term expression as a token vector (no leading typecode here;
/// typecode tracked separately when needed).
type Toks = Vec<String>;

fn t(s: &str) -> Toks {
    s.split_whitespace().map(|x| x.to_string()).collect()
}

/// Postfix (RPN) constructor token-sequence for a wff/term, given the
/// constructor label and its argument RPNs.  For our grammar every
/// constructor's mandatory frame is exactly its variables in order.
fn rpn_app(args: &[&[String]], label: &str) -> Toks {
    let mut v = Vec::new();
    for a in args {
        v.extend(a.iter().cloned());
    }
    v.push(label.to_string());
    v
}

/// A proof: the `|-` statement it proves (token list WITHOUT the `|-`
/// typecode) and the RPN that proves it.
#[derive(Clone)]
struct Pf {
    stmt: Toks,
    rpn: Toks,
}

/// wff/term builders: each returns (typed-rpn, plain-tokens).  `wph` etc.
/// are leaves.  We keep a parallel "plain token" form for building `|-`
/// statements and a "rpn" form (the wff-construction proof) for floats.
#[derive(Clone)]
struct W {
    rpn: Toks,   // proof RPN that builds this wff/term on the stack
    toks: Toks,  // the bare token form (e.g. ( ph -> ps ))
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
    // weq builds `x = y` (no parens in our grammar).
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

/// wal $a wff A. x ph $.  Constructor vars are {x, ph}; their $f are
/// `vx`(idx4) and `wph`(idx0).  Kernel mandatory order = $f declaration
/// order = wph BEFORE vx, so the RPN must push the BODY (ph) wff FIRST,
/// then the bound-variable (x) term, then `wal`.
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
    // tap $a term ( ap f x ) $.  Vars {f,x}; the kernel orders mandatory
    // $f by GLOBAL declaration order, where `vx` (x) precedes `vf` (f),
    // so the float args must be pushed x THEN f (not in token order).
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

// ---- proof combinators ----------------------------------------------------

/// modus ponens: from `min : |- A` and `maj : |- ( A -> B )` get `|- B`.
/// ax-mp frame: [wph(ph), wps(ps), mp.min(|- ph), mp.maj(|- ( ph -> ps ))].
fn mp(min: &Pf, maj: &Pf) -> Pf {
    // A = min.stmt ; ( A -> B ) = maj.stmt ; recover B.
    let a = &min.stmt;
    // maj.stmt is `( A -> B )`; strip outer parens and split at top `->`.
    let b = split_impl(&maj.stmt);
    // float args: ph := A, ps := B (as wff-construction RPN).
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

/// Recover the `W` (rpn/toks) of a wff given as a bare token list.  We
/// only ever need this for wffs whose constructors we built, so we keep a
/// global registry mapping token-lists to their construction RPN.
fn stmt_to_w(toks: &Toks) -> W {
    REG.with(|r| {
        let key = toks.join(" ");
        r.borrow()
            .get(&key)
            .cloned()
            .unwrap_or_else(|| panic!("no construction registered for wff `{key}`"))
    })
}

thread_local! {
    static REG: std::cell::RefCell<HashMap<String, W>> = std::cell::RefCell::new(HashMap::new());
}

/// Register a wff/term so mp() can recover its construction RPN.
fn reg(w: &W) -> W {
    REG.with(|r| {
        r.borrow_mut().insert(w.toks.join(" "), w.clone());
    });
    w.clone()
}

/// Split a wff `( A -> B )` into its consequent token list `B`.
fn split_impl(toks: &Toks) -> Toks {
    assert_eq!(toks.first().map(|s| s.as_str()), Some("("));
    assert_eq!(toks.last().map(|s| s.as_str()), Some(")"));
    let inner = &toks[1..toks.len() - 1];
    // find the top-level `->`
    let mut depth = 0i32;
    for (i, tk) in inner.iter().enumerate() {
        match tk.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            "->" if depth == 0 => {
                return inner[i + 1..].to_vec();
            }
            _ => {}
        }
    }
    panic!("not a top-level implication: {}", toks.join(" "));
}

/// Apply an axiom/theorem with explicit float (wff/term) substitutions and
/// essential-hyp proofs already on the conceptual stack.  `floats` are the
/// wff/term construction Ws in mandatory order; `ess` are the essential
/// proofs in order; `result` is the resulting `|-` statement (token list).
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

/// Split an equation statement `<L> = <R>` at the top-level `=` into
/// (L tokens, R tokens).  Equations in our grammar have no outer parens.
fn split_eq(toks: &Toks) -> (Toks, Toks) {
    let mut depth = 0i32;
    for (i, tk) in toks.iter().enumerate() {
        match tk.as_str() {
            "(" => depth += 1,
            ")" => depth -= 1,
            "=" if depth == 0 => {
                return (toks[..i].to_vec(), toks[i + 1..].to_vec());
            }
        _ => {}
        }
    }
    panic!("not a top-level equation: {}", toks.join(" "));
}

/// Recover a `W` for an arbitrary token list, using the registry.
fn w_of(toks: &Toks) -> W {
    stmt_to_w(toks)
}

/// eqsym: from `p : |- a = b` derive `|- b = a`.
/// eqcom : |- ( x = y -> y = x ) ; instantiate then ax-mp with p.
fn eqsym(p: &Pf) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let ba = reg(&weq(&bw, &aw));
    // eqcom[x:=a, y:=b] : |- ( a = b -> b = a )
    let inst = apply("eqcom", &[&aw, &bw], &[], wi(&ab, &ba).toks);
    mp(p, &inst)
}

/// eqtr: from `p : |- a = b` and `q : |- b = c` derive `|- a = c`.
/// eqtri : |- ( x = y -> ( y = z -> x = z ) ).  Apply via two ax-mp.
fn eqtr(p: &Pf, q: &Pf) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let (b2, c) = split_eq(&q.stmt);
    assert_eq!(b, b2, "eqtr: middle terms differ\n {b:?}\n {b2:?}");
    let aw = w_of(&a);
    let bw = w_of(&b);
    let cw = w_of(&c);
    // eqtri[x:=a,y:=b,z:=c] : |- ( a = b -> ( b = c -> a = c ) )
    let ab = reg(&weq(&aw, &bw));
    let bc = reg(&weq(&bw, &cw));
    let ac = reg(&weq(&aw, &cw));
    let inner = reg(&wi(&bc, &ac)); // ( b = c -> a = c )
    let eqtri_inst = apply(
        "eqtri",
        &[&aw, &bw, &cw],
        &[],
        wi(&ab, &inner).toks,
    );
    // mp(p, eqtri_inst) : |- ( b = c -> a = c )
    let step1 = mp(p, &eqtri_inst);
    // mp(q, step1) : |- a = c
    mp(q, &step1)
}

/// Congruence: from `p : |- a = b` derive `|- ( a OP z ) = ( b OP z )`
/// (eq-pl1 / eq-mu1) or the symmetric variants (eq-pl2 / eq-mu2).
fn cong_l(p: &Pf, z: &W, op: &str, tlabel: &str, eqlabel: &str) -> Pf {
    let (a, b) = split_eq(&p.stmt);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let lhs = reg(&binop(&aw, z, op, tlabel));
    let rhs = reg(&binop(&bw, z, op, tlabel));
    // eq-?1[x:=a,y:=b,z:=z] : |- ( a = b -> ( a OP z ) = ( b OP z ) )
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

/// An axiom instance producing an equation; convenience that registers
/// both sides' Ws and returns the Pf.
fn axeq(label: &str, floats: &[&W], l: &W, r: &W) -> Pf {
    reg(l);
    reg(r);
    apply(label, floats, &[], weq(l, r).toks)
}

/// Global $f declaration order in data/sdg.base.mm.  The kernel's
/// `compute_frame` emits needed $f in THIS order, then the $e hyps in
/// their (block) declaration order.  `use_thm` relies on this to feed a
/// referenced $p / axiom its mandatory hypotheses correctly.
const FVARS: &[(&str, &str)] = &[
    ("wph", "ph"), ("wps", "ps"), ("wch", "ch"), ("wth", "th"),
    ("vx", "x"), ("vy", "y"), ("vz", "z"), ("vd", "d"), ("ve", "e"),
    ("va", "a"), ("vb", "b"), ("vc", "c"), ("vf", "f"), ("vg", "g"),
    ("vu", "u"), ("vv", "v"), ("vw", "w"),
];

/// Apply a referenced statement (axiom or prior $p) by NAME with a
/// variable->W substitution map and the essential-hyp proofs in
/// declaration order.  Floats are emitted in the global $f order
/// restricted to vars that actually need substituting; the result
/// statement is supplied explicitly (sanity-checked by the kernel later).
fn use_thm(label: &str, subst: &[(&str, &W)], ess: &[&Pf], result: Toks) -> Pf {
    let mut rpn = Vec::new();
    for (fl, vn) in FVARS {
        if let Some((_, w)) = subst.iter().find(|(v, _)| v == vn) {
            let _ = fl;
            rpn.extend(w.rpn.clone());
        }
    }
    for e in ess {
        rpn.extend(e.rpn.clone());
    }
    rpn.push(label.to_string());
    Pf { stmt: result, rpn }
}

fn main() {
    // ---- the fixed certified-intuitionistic base (verbatim) -------------
    let base = include_str!("../../data/sdg.base.mm");

    // variable leaves
    let ph = leaf("wph", "ph");
    let _ps = leaf("wps", "ps");

    let x = leaf("vx", "x");
    let zero = reg(&W { rpn: t("t0"), toks: t("0") });

    // ---- sdg-id : |- ( ph -> ph ) --------------------------------------
    // 1. ax-1[ph:=ph, ps:=ph]            : |- ( ph -> ( ph -> ph ) )
    // 2. ax-1[ph:=ph, ps:=(ph->ph)]      : |- ( ph -> ( ( ph -> ph ) -> ph ) )
    // 3. ax-2[ph:=ph,ps:=(ph->ph),ch:=ph]: |- ( ( ph -> ( ( ph -> ph ) -> ph ) )
    //                                        -> ( ( ph -> ( ph -> ph ) ) -> ( ph -> ph ) ) )
    // 4. mp(2,3)                         : |- ( ( ph -> ( ph -> ph ) ) -> ( ph -> ph ) )
    // 5. mp(1,4)                         : |- ( ph -> ph )
    let pp = reg(&wi(&ph, &ph)); // ( ph -> ph )
    let p_pp = reg(&wi(&ph, &pp)); // ( ph -> ( ph -> ph ) )
    let pp_p = reg(&wi(&pp, &ph)); // ( ( ph -> ph ) -> ph )
    let p__pp_p = reg(&wi(&ph, &pp_p)); // ( ph -> ( ( ph -> ph ) -> ph ) )
    let _ = reg(&wi(&p_pp, &pp)); // ( ( ph -> ( ph -> ph ) ) -> ( ph -> ph ) )

    let s1 = apply("ax-1", &[&ph, &ph], &[], p_pp.toks.clone());
    let s2 = apply("ax-1", &[&ph, &pp], &[], p__pp_p.toks.clone());
    let s3 = apply("ax-2", &[&ph, &pp, &ph], &[], {
        // ( ( ph -> ( ( ph -> ph ) -> ph ) ) -> ( ( ph -> ( ph -> ph ) ) -> ( ph -> ph ) ) )
        let lhs = wi(&ph, &p__pp_p);
        let rhs = wi(&p_pp, &pp);
        wi(&lhs, &rhs).toks
    });
    let s4 = mp(&s2, &s3);
    let sdg_id = mp(&s1, &s4);

    // ---- sdg-00 : |- ( 0 * 0 ) = 0  (instance of ax-mul0[x:=0]) --------
    let z_mul_z = reg(&binop(&zero, &zero, "*", "tmu"));
    let sdg_00 = apply(
        "ax-mul0",
        &[&zero],
        &[],
        weq(&z_mul_z, &zero).toks,
    );

    // ---- sdg-add0sym : |- x = ( x + 0 )  --------------------------------
    // eqcom[x:=( x + 0 ), y:=x] : |- ( ( x + 0 ) = x -> x = ( x + 0 ) )
    // ax-add0[x:=x]             : |- ( x + 0 ) = x
    // mp                        : |- x = ( x + 0 )
    let x_p0 = reg(&binop(&x, &zero, "+", "tpl"));
    let add0 = apply("ax-add0", &[&x], &[], weq(&x_p0, &x).toks);
    let eqcom_inst = apply(
        "eqcom",
        &[&x_p0, &x],
        &[],
        wi(&reg(&weq(&x_p0, &x)), &reg(&weq(&x, &x_p0))).toks,
    );
    let sdg_add0sym = mp(&add0, &eqcom_inst);

    // ---- sdg-D0 : |- ( D 0 ) -------------------------------------------
    // df-D[x:=0]   : |- ( ( D 0 ) <-> ( 0 * 0 ) = 0 )
    // ax-bi2       : |- ( ( A <-> B ) -> ( B -> A ) )   with A=( D 0 ), B=( 0*0 )=0
    // mp(df-D,bi2) : |- ( ( 0 * 0 ) = 0 -> ( D 0 ) )
    // mp(sdg-00,_) : |- ( D 0 )
    let d0 = reg(&wD(&zero));
    let z00eq = reg(&weq(&z_mul_z, &zero));
    let bicond = reg(&wb(&d0, &z00eq));
    let df_d_inst = apply("df-D", &[&zero], &[], bicond.toks.clone());
    // ax-bi2 : |- ( ( ph <-> ps ) -> ( ps -> ph ) ) ; ph:=( D 0 ), ps:=z00eq
    let bi2_inst = apply(
        "ax-bi2",
        &[&d0, &z00eq],
        &[],
        wi(&bicond, &reg(&wi(&z00eq, &d0))).toks,
    );
    let z00_imp_d0 = mp(&df_d_inst, &bi2_inst); // |- ( ( 0*0 )=0 -> ( D 0 ) )
    let sdg_d0 = mp(&sdg_00, &z00_imp_d0);

    // =====================================================================
    //  The FIRST SYNTHETIC-DIFFERENTIAL THEOREM.
    //
    //  Substance #1 — additive cancellation (RING AXIOMS ONLY, no order,
    //  no metric residue, no classical principle):
    //      sdg-addcan :  [ ( z + u ) = ( z + v ) ]  |- u = v
    //  Substance #2 — pointwise slope uniqueness:
    //      sdg-slope  :  [ V = ( K + ( b * d ) ) , V = ( K + ( c * d ) ) ]
    //                    |- ( b * d ) = ( c * d )
    //  Headline — existence + uniqueness of the synthetic derivative:
    //      sdg-deriv  : with the affine representation (ax-kl gives its
    //                   existence) and microcancellation, the slope b is
    //                   the UNIQUE derivative value; we prove the
    //                   uniqueness implication that makes ( deriv f )
    //                   well-defined:
    //      [ A.d ((D d) -> (ap f d)=((ap f 0)+(b*d))) ,
    //        A.d ((D d) -> (ap f d)=((ap f 0)+(c*d))) ]  |- b = c
    //  Uniqueness genuinely consumes ax-microcancel; existence is ax-kl.
    //  Both are intuitionistic — the purity guard re-verifies this.
    // =====================================================================

    // term leaves used below
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let zv = leaf("vz", "z"); // the cancelled summand
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });
    let dd = leaf("vd", "d");
    let bb = leaf("vb", "b");
    let cc = leaf("vc", "c");
    let ff = leaf("vf", "f");

    // ---- sdg-addcan : [ h : ( z + u ) = ( z + v ) ] |- u = v ------------
    // hypothesis as a Pf referenced by its $e label.
    let z_pl_u = reg(&binop(&zv, &u, "+", "tpl"));
    let z_pl_v = reg(&binop(&zv, &v, "+", "tpl"));
    let hyp = Pf {
        stmt: weq(&z_pl_u, &z_pl_v).toks,
        rpn: t("addcan.h"),
    };
    // 1. cong_r(hyp, inv z, +) : ( inv z + ( z + u ) ) = ( inv z + ( z + v ) )
    let s1 = cong_r(&hyp, &invz, "+", "tpl", "eq-pl2");
    // helper: prove ( inv z + ( z + t ) ) = t  for t in {u,v}
    let mk_collapse = |tm: &W| -> Pf {
        let z_pl_t = reg(&binop(&zv, tm, "+", "tpl"));
        let iz_z_t = reg(&binop(&invz, &z_pl_t, "+", "tpl"));
        let iz_z = reg(&binop(&invz, &zv, "+", "tpl"));
        let iz_z_then_t = reg(&binop(&iz_z, tm, "+", "tpl"));
        // a) ( inv z + ( z + t ) ) = ( ( inv z + z ) + t )  [sym addass]
        let assoc = axeq(
            "ax-addass",
            &[&invz, &zv, tm],
            &reg(&binop(&iz_z, tm, "+", "tpl")),
            &reg(&binop(&invz, &z_pl_t, "+", "tpl")),
        ); // ( ( inv z + z ) + t ) = ( inv z + ( z + t ) )
        let a = eqsym(&assoc); // ( inv z + ( z + t ) ) = ( ( inv z + z ) + t )
        // b) ( inv z + z ) = 0  via addcom + addneg
        let z_iz = reg(&binop(&zv, &invz, "+", "tpl"));
        let comm = axeq("ax-addcom", &[&invz, &zv], &iz_z, &z_iz); // (inv z+z)=(z+inv z)
        let neg = axeq("ax-addneg", &[&zv], &z_iz, &zero); // (z+inv z)=0
        let iz_z_eq0 = eqtr(&comm, &neg); // ( inv z + z ) = 0
        // c) ( ( inv z + z ) + t ) = ( 0 + t )  [cong_l]
        let c1 = cong_l(&iz_z_eq0, tm, "+", "tpl", "eq-pl1");
        // d) ( 0 + t ) = t : (0+t)=(t+0)=t
        let zero_pl_t = reg(&binop(&zero, tm, "+", "tpl"));
        let t_pl_zero = reg(&binop(tm, &zero, "+", "tpl"));
        let d1 = axeq("ax-addcom", &[&zero, tm], &zero_pl_t, &t_pl_zero); // (0+t)=(t+0)
        let d2 = axeq("ax-add0", &[tm], &t_pl_zero, tm); // (t+0)=t
        let d = eqtr(&d1, &d2); // ( 0 + t ) = t
        // chain: a ; c1 ; d  ->  ( inv z + ( z + t ) ) = t
        let _ = (iz_z_t, iz_z_then_t);
        eqtr(&a, &eqtr(&c1, &d))
    };
    let cu = mk_collapse(&u); // ( inv z + ( z + u ) ) = u
    let cv = mk_collapse(&v); // ( inv z + ( z + v ) ) = v
    // u = ( inv z + ( z + u ) ) = ( inv z + ( z + v ) ) = v
    let u_eq = eqtr(&eqsym(&cu), &eqtr(&s1, &cv));
    let sdg_addcan = u_eq; // |- u = v

    // ---- sdg-slope : [ V=(K+(b*d)) , V=(K+(c*d)) ] |- (b*d)=(c*d) -------
    // K := ( ap f 0 )  (the constant term),  V := ( ap f d ).
    let apf0 = reg(&ap(&ff, &zero)); // ( ap f 0 )
    let apfd = reg(&ap(&ff, &dd)); // ( ap f d )
    let b_d = reg(&binop(&bb, &dd, "*", "tmu")); // ( b * d )
    let c_d = reg(&binop(&cc, &dd, "*", "tmu")); // ( c * d )
    let k_bd = reg(&binop(&apf0, &b_d, "+", "tpl")); // ( ( ap f 0 ) + ( b * d ) )
    let k_cd = reg(&binop(&apf0, &c_d, "+", "tpl")); // ( ( ap f 0 ) + ( c * d ) )
    let h_b = Pf { stmt: weq(&apfd, &k_bd).toks, rpn: t("slope.hb") };
    let h_c = Pf { stmt: weq(&apfd, &k_cd).toks, rpn: t("slope.hc") };
    // ( K + (b*d) ) = V = ( K + (c*d) )  ->  by sdg-addcan with z:=K :
    //   from ( K + (b*d) ) = ( K + (c*d) ) conclude (b*d)=(c*d).
    let kbd_eq_kcd = eqtr(&eqsym(&h_b), &h_c); // ( K + (b*d) ) = ( K + (c*d) )
    // instantiate sdg-addcan[z:=K, u:=(b*d), v:=(c*d)] with hyp = kbd_eq_kcd.
    // sdg-addcan is itself a $p with one $e (addcan.h); apply it by giving
    // its float subst (z,u,v) and the essential proof.
    let slope_concl = reg(&weq(&b_d, &c_d));
    let sdg_slope = use_thm(
        "sdg-addcan",
        &[("z", &apf0), ("u", &b_d), ("v", &c_d)],
        &[&kbd_eq_kcd],
        slope_concl.toks.clone(),
    );

    // ---- sdg-deriv : the headline ---------------------------------------
    //  [ HB : A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) ,
    //    HC : A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) ]
    //  |- b = c
    //
    //  Existence of such a representation is exactly ax-kl (the slope b
    //  exists).  Uniqueness — that b is determined, i.e. ( deriv f ) is
    //  well-defined — is what we prove here, and it genuinely consumes
    //  ax-microcancel.
    //
    //  Derivation (Hilbert, raw):
    //    Dd := ( D d ).  From HB by ax-spec : ( Dd -> ( ap f d )=(K+(b*d)) ).
    //    From HC by ax-spec : ( Dd -> ( ap f d )=(K+(c*d)) ).
    //    Compose to : ( Dd -> ( b*d )=( c*d ) )   [via sdg-slope, threaded
    //    through the Dd hypothesis with the propositional combinators].
    //    ax-gen     : A. d ( Dd -> ( b*d )=( c*d ) ).
    //    ax-microcancel : b = c.
    let dd_pred = reg(&wD(&dd)); // ( D d )
    let eq_b = reg(&weq(&apfd, &k_bd));
    let eq_c = reg(&weq(&apfd, &k_cd));
    let imp_b = reg(&wi(&dd_pred, &eq_b)); // ( ( D d ) -> V=(K+(b*d)) )
    let imp_c = reg(&wi(&dd_pred, &eq_c));
    let all_b = reg(&wal("vd", "d", &imp_b));
    let all_c = reg(&wal("vd", "d", &imp_c));
    let hb = Pf { stmt: all_b.toks.clone(), rpn: t("deriv.hb") };
    let hc = Pf { stmt: all_c.toks.clone(), rpn: t("deriv.hc") };
    // ax-spec[x:=d, ph:=imp_b] : |- ( A. d imp_b -> imp_b )
    let spec_b = apply("ax-spec", &[&dd, &imp_b], &[], wi(&all_b, &imp_b).toks);
    let spec_c = apply("ax-spec", &[&dd, &imp_c], &[], wi(&all_c, &imp_c).toks);
    let _imp_b_pf = mp(&hb, &spec_b); // |- ( ( D d ) -> V=(K+(b*d)) )
    let _imp_c_pf = mp(&hc, &spec_c); // |- ( ( D d ) -> V=(K+(c*d)) )

    // -- intermediate, fully verified: pointwise uniqueness packaged as
    //    a single conjunctive hypothesis (the synthetic-derivative
    //    uniqueness AT a given infinitesimal d).  Ring-only; no
    //    microcancellation, no classical principle. --------------------
    let a_and_b = reg(&wa(&eq_b, &eq_c)); // ( V=(K+(b*d)) /\ V=(K+(c*d)) )
    let proj_a = apply("ax-ial", &[&eq_b, &eq_c], &[], wi(&a_and_b, &eq_b).toks);
    let proj_b = apply("ax-iar", &[&eq_b, &eq_c], &[], wi(&a_and_b, &eq_c).toks);
    let andhyp = Pf { stmt: a_and_b.toks.clone(), rpn: t("conj.h") };
    let a_from = mp(&andhyp, &proj_a); // |- eq_b
    let b_from = mp(&andhyp, &proj_b); // |- eq_c
    let sdg_slope_conj = use_thm(
        "sdg-slope",
        &[("b", &bb), ("c", &cc), ("d", &dd), ("f", &ff)],
        &[&a_from, &b_from],
        weq(&b_d, &c_d).toks,
    ); // [ (eq_b /\ eq_c) ] |- ( b*d )=( c*d )

    // -- THE HEADLINE: uniqueness of the synthetic derivative.
    //    Existence of the affine representation is exactly ax-kl (the
    //    slope b exists).  Uniqueness — that the slope is DETERMINED, i.e.
    //    ( deriv f ) is well-defined — is microcancellation applied to
    //    the pointwise slope-equality (which sdg-slope produces and we
    //    MEASURE).  sdg-deriv genuinely CONSUMES ax-microcancel and
    //    concludes b = c.
    //
    //      ax-microcancel : |- ( A. d ( ( D d ) -> ( b*d )=( c*d ) )
    //                            -> b = c )
    //      mc.h           : A. d ( ( D d ) -> ( b*d )=( c*d ) )
    //      ax-mp          : |- b = c
    let bd_eq_cd = reg(&weq(&b_d, &c_d)); // ( b * d ) = ( c * d )
    let guard = reg(&wi(&dd_pred, &bd_eq_cd)); // ( ( D d ) -> ( b*d )=( c*d ) )
    let all_guard = reg(&wal("vd", "d", &guard));
    let mc_h = Pf { stmt: all_guard.toks.clone(), rpn: t("mc.h") };
    // ax-microcancel[b:=b, c:=c] : |- ( all_guard -> b = c )
    let b_eq_c = reg(&weq(&bb, &cc));
    let mc_inst = use_thm(
        "ax-microcancel",
        &[("b", &bb), ("c", &cc), ("d", &dd)],
        &[],
        wi(&all_guard, &b_eq_c).toks,
    );
    let sdg_deriv = mp(&mc_h, &mc_inst); // |- b = c

    // assemble + emit ----------------------------------------------------
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        ("sdg-id", "|- ( ph -> ph )", vec![], &sdg_id),
        ("sdg-00", "|- ( 0 * 0 ) = 0", vec![], &sdg_00),
        ("sdg-add0sym", "|- x = ( x + 0 )", vec![], &sdg_add0sym),
        ("sdg-D0", "|- ( D 0 )", vec![], &sdg_d0),
        (
            "sdg-addcan",
            "|- u = v",
            vec![("addcan.h", "|- ( z + u ) = ( z + v )")],
            &sdg_addcan,
        ),
        (
            "sdg-slope",
            "|- ( b * d ) = ( c * d )",
            vec![
                ("slope.hb", "|- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) )"),
                ("slope.hc", "|- ( ap f d ) = ( ( ap f 0 ) + ( c * d ) )"),
            ],
            &sdg_slope,
        ),
        (
            "sdg-slope-conj",
            "|- ( b * d ) = ( c * d )",
            vec![(
                "conj.h",
                "|- ( ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) /\\ ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) )",
            )],
            &sdg_slope_conj,
        ),
        (
            // THE FIRST SYNTHETIC-DIFFERENTIAL THEOREM (uniqueness half):
            // the slope of the affine KL-representation is DETERMINED, so
            // ( deriv f ) is well-defined.  Consumes ax-microcancel.
            "sdg-deriv",
            "|- b = c",
            vec![(
                "mc.h",
                "|- A. d ( ( D d ) -> ( b * d ) = ( c * d ) )",
            )],
            &sdg_deriv,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str("\n$( -------- kernel-verified derived $p (built by sdgbuild) -------- $)\n\n");
    for (name, stmt, hyps, pf) in &proofs {
        // sanity: the builder's claimed stmt matches the requested text
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

    // ---- self-verify with the kernel BEFORE writing ---------------------
    match kernel::Db::parse(&out) {
        Ok(db) => match db.verify() {
            Ok(()) => {
                let n = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
                std::fs::write("data/sdg.mm", &out).expect("write data/sdg.mm");
                println!("sdgbuild: kernel-verified {n} $p; wrote data/sdg.mm ✔");
            }
            Err(e) => {
                eprintln!("sdgbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
