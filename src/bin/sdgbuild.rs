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

/// wex $a wff E. x ph $.  Same $f order as wal (wph before vx): push the
/// body wff first, then the bound-variable term, then `wex`.
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

// ===========================================================================
//  DEDUCTION-FORM COMBINATORS  (the §5b seam-closing rule).
//
//  These are the SOUND, intuitionistically-pure derived rules that thread
//  a guard/antecedent `G` through an equational derivation WITHOUT taking
//  the conclusion as an `$e` hypothesis.  Each is a derived rule of the
//  intuitionistic substrate: it emits ONLY `ax-1`, `ax-2`, `ax-mp`,
//  `eqtri`, `eqcom`, `eq-*`, `ax-spec`, `ax-gen` — NO classical principle
//  (the purity guard re-verifies this mechanically).
//
//  Soundness argument (the intuitionistic deduction theorem, the fragment
//  we actually use): in minimal implicational logic with `ax-1`
//  `( ph -> ( ps -> ph ) )` and `ax-2`
//  `( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )`,
//  modus ponens admits the deduction theorem.  `imp_a1` is the
//  axiom/`weakening` case (lift a closed theorem under any antecedent via
//  `ax-1`); `imp_mp` is the modus-ponens case (distribute the shared
//  antecedent `G` over an implication via `ax-2`).  All higher combinators
//  (`imp_eqtr`, `imp_eqsym`, `imp_cong_*`) are just these two applied to
//  the equational `$a` (`eqtri`/`eqcom`/`eq-*`), which are THEMSELVES
//  already implications, so no extra principle is introduced.  None of
//  `ax-1`/`ax-2`/`ax-mp` is classical (no `ax-3`/Peirce/LEM/DNE), so the
//  whole toolkit is intuitionistically pure by construction.
// ===========================================================================

/// `imp_a1` : from `p : |- X` and an antecedent wff `G`, derive
/// `|- ( G -> X )`.  This is the WEAKENING / axiom case of the deduction
/// theorem: `ax-1[ph:=X, ps:=G] : |- ( X -> ( G -> X ) )`, then mp.
fn imp_a1(p: &Pf, g: &W) -> Pf {
    let xw = w_of(&p.stmt);
    let g_x = reg(&wi(g, &xw));
    // ax-1 : |- ( ph -> ( ps -> ph ) )  with ph:=X, ps:=G
    let ax1_inst = apply("ax-1", &[&xw, g], &[], reg(&wi(&xw, &g_x)).toks);
    mp(p, &ax1_inst)
}

/// `imp_mp` : the MODUS-PONENS case of the deduction theorem.  From
/// `pa : |- ( G -> A )` and `pab : |- ( G -> ( A -> B ) )` derive
/// `|- ( G -> B )` via `ax-2[ph:=G, ps:=A, ch:=B]`.
fn imp_mp(pa: &Pf, pab: &Pf) -> Pf {
    // pa.stmt = ( G -> A ) ; pab.stmt = ( G -> ( A -> B ) )
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
    // ax-2 : |- ( ( G -> ( A -> B ) ) -> ( ( G -> A ) -> ( G -> B ) ) )
    let ax2_inst = apply(
        "ax-2",
        &[&gw, &aw, &bw],
        &[],
        wi(&g_ab, &reg(&wi(&g_a, &g_b))).toks,
    );
    // mp(pab, ax2) : |- ( ( G -> A ) -> ( G -> B ) )
    let step = mp(pab, &ax2_inst);
    mp(pa, &step)
}

/// Split a wff `( A -> B )` into its ANTECEDENT token list `A`.
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

/// `imp_eqtr` : transitivity UNDER a shared antecedent `G`.  From
/// `pab : |- ( G -> a = b )` and `pbc : |- ( G -> b = c )` derive
/// `|- ( G -> a = c )`, using `eqtri` lifted by `imp_a1`/`imp_mp`.
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
    // eqtri : |- ( a = b -> ( b = c -> a = c ) )   (a closed implication)
    let eqtri_inst = apply("eqtri", &[&aw, &bw, &cw], &[], reg(&wi(&ab, &bc_ac)).toks);
    // lift it under G:  |- ( G -> ( a=b -> ( b=c -> a=c ) ) )
    let g_eqtri = imp_a1(&eqtri_inst, &gw);
    // imp_mp with pab : |- ( G -> ( b=c -> a=c ) )
    let g_bc_ac = imp_mp(pab, &g_eqtri);
    // imp_mp with pbc : |- ( G -> a=c )
    imp_mp(pbc, &g_bc_ac)
}

/// `imp_eqsym` : symmetry under a shared antecedent `G`.  From
/// `pab : |- ( G -> a = b )` derive `|- ( G -> b = a )` via `eqcom`.
fn imp_eqsym(pab: &Pf) -> Pf {
    let g = split_ant(&pab.stmt);
    let (a, b) = split_eq(&split_impl(&pab.stmt));
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let ba = reg(&weq(&bw, &aw));
    // eqcom : |- ( a = b -> b = a )
    let eqcom_inst = apply("eqcom", &[&aw, &bw], &[], reg(&wi(&ab, &ba)).toks);
    let g_eqcom = imp_a1(&eqcom_inst, &gw); // |- ( G -> ( a=b -> b=a ) )
    imp_mp(pab, &g_eqcom)
}

/// `imp_cong_l` : congruence under a shared antecedent `G`.  From
/// `pab : |- ( G -> a = b )` derive `|- ( G -> ( a OP z ) = ( b OP z ) )`.
fn imp_cong_l(pab: &Pf, z: &W, op: &str, tlabel: &str, eqlabel: &str) -> Pf {
    let g = split_ant(&pab.stmt);
    let (a, b) = split_eq(&split_impl(&pab.stmt));
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let lhs = reg(&binop(&aw, z, op, tlabel));
    let rhs = reg(&binop(&bw, z, op, tlabel));
    let cong = reg(&weq(&lhs, &rhs));
    // eq-?1 : |- ( a = b -> ( a OP z ) = ( b OP z ) )
    let eq_inst = apply(eqlabel, &[&aw, &bw, z], &[], reg(&wi(&ab, &cong)).toks);
    let g_eq = imp_a1(&eq_inst, &gw); // |- ( G -> ( a=b -> (aOPz)=(bOPz) ) )
    imp_mp(pab, &g_eq)
}

/// `imp_cong_r` : symmetric congruence ( z OP a ) = ( z OP b ) under `G`.
/// `gen` : universal generalization.  From `p : |- ph` derive
/// `|- A. x ph` via `ax-gen` ( gen.1 $e |- ph  ->  ax-gen |- A. x ph ).
/// SOUNDNESS PROVISO (metatheoretic, argued in SEQUEL_SCOPE §5b): the
/// bound variable `x` must not occur free in any ESSENTIAL hypothesis on
/// which `p` actually depends.  At the sole use-site the discharged
/// dependencies are `deriv.hb`/`deriv.hc`, each of the form
/// `A. d ( ... )` — `d` is BOUND there, so the proviso holds.
fn gen(p: &Pf, xflabel: &str, xtok: &str) -> Pf {
    let bodyw = w_of(&p.stmt);
    // ax-gen mandatory frame: wph (body), then vx (the bound var), then
    // gen.1 (the essential proof).  Result: A. x <body>.
    let all = reg(&wal(xflabel, xtok, &bodyw));
    let mut rpn = bodyw.rpn.clone();
    rpn.push(xflabel.to_string());
    rpn.extend(p.rpn.clone());
    rpn.push("ax-gen".to_string());
    Pf { stmt: all.toks, rpn }
}

fn imp_cong_r(pab: &Pf, z: &W, op: &str, tlabel: &str, eqlabel: &str) -> Pf {
    let g = split_ant(&pab.stmt);
    let (a, b) = split_eq(&split_impl(&pab.stmt));
    let gw = w_of(&g);
    let aw = w_of(&a);
    let bw = w_of(&b);
    let ab = reg(&weq(&aw, &bw));
    let lhs = reg(&binop(z, &aw, op, tlabel));
    let rhs = reg(&binop(z, &bw, op, tlabel));
    let cong = reg(&weq(&lhs, &rhs));
    let eq_inst = apply(eqlabel, &[&aw, &bw, z], &[], reg(&wi(&ab, &cong)).toks);
    let g_eq = imp_a1(&eq_inst, &gw);
    imp_mp(pab, &g_eq)
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

    // =====================================================================
    //  §5b SEAM-CLOSING ARTIFACT #1 — sdg-addcan-imp.
    //
    //  The DEDUCTION-DISCHARGED form of sdg-addcan: the SAME ring
    //  derivation, but with its single `$e` (addcan.h) discharged into the
    //  antecedent of a closed implication.  HYPOTHESIS-FREE:
    //      |- ( ( z + u ) = ( z + v ) -> u = v )
    //  This is the intuitionistic deduction theorem applied by hand to the
    //  one place addcan.h was used (the cong_r step) — and `eq-pl2` is
    //  ITSELF already an implication `( x=y -> (z+x)=(z+y) )`, so the
    //  discharge is exact: the G-antecedented `s1` is literally the
    //  `eq-pl2` instance.  Everything else (mk_collapse) is hypothesis-free
    //  and lifted under G by `imp_a1`; transitivity by `imp_eqtr`.  Only
    //  ax-1/ax-2/ax-mp/eqtri/eqcom/eq-* — NO classical principle.
    // =====================================================================
    let g_addcan = reg(&weq(&z_pl_u, &z_pl_v)); // G := ( z + u ) = ( z + v )
    // s1 under G: eq-pl2[x:=(z+u),y:=(z+v),z:=inv z] is *exactly*
    //   |- ( ( z+u )=( z+v ) -> ( inv z + ( z+u ) ) = ( inv z + ( z+v ) ) )
    let iz_zu = reg(&binop(&invz, &z_pl_u, "+", "tpl"));
    let iz_zv = reg(&binop(&invz, &z_pl_v, "+", "tpl"));
    let s1_imp = apply(
        "eq-pl2",
        &[&z_pl_u, &z_pl_v, &invz],
        &[],
        wi(&g_addcan, &reg(&weq(&iz_zu, &iz_zv))).toks,
    ); // |- ( G -> ( inv z+(z+u) ) = ( inv z+(z+v) ) )
    // cu, cv are hypothesis-free (the closure helper) — lift them under G.
    let cu_imp = imp_a1(&cu, &g_addcan); // |- ( G -> ( inv z+(z+u) ) = u )
    let cv_imp = imp_a1(&cv, &g_addcan); // |- ( G -> ( inv z+(z+v) ) = v )
    // u = ( inv z+(z+u) ) = ( inv z+(z+v) ) = v, all under G.
    let sdg_addcan_imp = imp_eqtr(
        &imp_eqsym(&cu_imp),
        &imp_eqtr(&s1_imp, &cv_imp),
    ); // |- ( G -> u = v )

    // =====================================================================
    //  §5b SEAM-CLOSING ARTIFACT #2 — sdg-slope-imp.
    //
    //  The DEDUCTION-DISCHARGED pointwise slope lemma, HYPOTHESIS-FREE,
    //  with the two slope hypotheses packaged as a single conjunctive
    //  antecedent (so the single-antecedent imp_* toolkit suffices):
    //      |- ( ( EB /\ EC ) -> Q )
    //  where EB := V = ( K + ( b*d ) ), EC := V = ( K + ( c*d ) ),
    //        Q  := ( b*d ) = ( c*d ),  V := ( ap f d ), K := ( ap f 0 ).
    //  Under G := ( EB /\ EC ):  ax-ial/ax-iar give ( G -> EB ), ( G -> EC );
    //  imp_eqsym+imp_eqtr give ( G -> ( K+(b*d) )=( K+(c*d) ) ); then
    //  sdg-addcan-imp[z:=K,u:=(b*d),v:=(c*d)], lifted under G by imp_a1 and
    //  detached by imp_mp, yields ( G -> Q ).  Only ax-1/ax-2/ax-mp/
    //  eqtri/eqcom/ax-ial/ax-iar + ring eq-axioms — NO classical principle.
    // =====================================================================
    let eb = reg(&weq(&apfd, &k_bd)); // EB := V = ( K + ( b*d ) )
    let ec = reg(&weq(&apfd, &k_cd)); // EC := V = ( K + ( c*d ) )
    let q_bd_cd = reg(&weq(&b_d, &c_d)); // Q := ( b*d ) = ( c*d )
    let g_slope = reg(&wa(&eb, &ec)); // G := ( EB /\ EC )
    // ( G -> EB )  and  ( G -> EC )  via ax-ial / ax-iar.
    let g_eb = apply("ax-ial", &[&eb, &ec], &[], wi(&g_slope, &eb).toks);
    let g_ec = apply("ax-iar", &[&eb, &ec], &[], wi(&g_slope, &ec).toks);
    // ( G -> ( K+(b*d) ) = V )    [eqsym of g_eb]
    let g_kbd_v = imp_eqsym(&g_eb);
    // ( G -> ( K+(b*d) ) = ( K+(c*d) ) )   [eqtr through V via g_ec]
    let g_kbd_kcd = imp_eqtr(&g_kbd_v, &g_ec);
    // sdg-addcan-imp[z:=K, u:=(b*d), v:=(c*d)] :
    //   |- ( ( K+(b*d) ) = ( K+(c*d) ) -> ( b*d ) = ( c*d ) )
    let ac_inst = use_thm(
        "sdg-addcan-imp",
        &[("z", &apf0), ("u", &b_d), ("v", &c_d)],
        &[],
        reg(&wi(&reg(&weq(&k_bd, &k_cd)), &q_bd_cd)).toks,
    );
    // lift under G, detach with g_kbd_kcd -> ( G -> Q )
    let g_ac = imp_a1(&ac_inst, &g_slope); // ( G -> ( (K+bd)=(K+cd) -> Q ) )
    let sdg_slope_imp = imp_mp(&g_kbd_kcd, &g_ac); // |- ( ( EB /\ EC ) -> Q )

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
    // ax-spec $a |- ( A. x ph -> ph ) : mandatory $f are wph(ph) then
    // vx(x); here x:=d, ph:=imp_b/imp_c, so floats = [imp_*, dd].
    let spec_b = apply("ax-spec", &[&imp_b, &dd], &[], reg(&wi(&all_b, &imp_b)).toks);
    let spec_c = apply("ax-spec", &[&imp_c, &dd], &[], reg(&wi(&all_c, &imp_c)).toks);
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

    // =====================================================================
    //  §5b SEAM-CLOSING ARTIFACT #3 — THE SEAM-FREE HEADLINE.
    //
    //  sdg-deriv, NO linking `$e`.  Hypotheses are ONLY the two universal
    //  affine KL-representations (each an `ax-kl` instance — EXISTENCE):
    //    deriv.hb : A. d ( ( D d ) -> EB )
    //    deriv.hc : A. d ( ( D d ) -> EC )
    //  Conclusion: b = c.  The linking universal
    //    A. d ( ( D d ) -> ( b*d )=( c*d ) )
    //  is now MECHANICALLY THREADED, not assumed:
    //    1. ax-spec strips A.d :  pB : ( ( D d ) -> EB ),  pC : ( ( D d ) -> EC ).
    //    2. ax-ian, lifted under the shared guard ( D d ) by imp_a1 and
    //       detached by imp_mp twice, gives  ( ( D d ) -> ( EB /\ EC ) ).
    //    3. sdg-slope-imp : ( ( EB /\ EC ) -> Q ); lifted under ( D d ) by
    //       imp_a1, detached by imp_mp, gives  ( ( D d ) -> Q ).
    //    4. gen (ax-gen) :  A. d ( ( D d ) -> Q )   — SOUND: `d` is bound
    //       in deriv.hb/deriv.hc, the only discharged hypotheses.
    //    5. ax-microcancel mp :  b = c.
    //  The `$e` mc.h is GONE.  Only ax-1/ax-2/ax-mp/ax-ial/ax-iar/ax-ian/
    //  ax-spec/ax-gen/eq-* + ax-microcancel — NO classical principle (the
    //  purity guard re-verifies the consumed-axiom closure).
    // =====================================================================
    let bd_eq_cd = reg(&weq(&b_d, &c_d)); // Q := ( b * d ) = ( c * d )
    // step 1: strip A.d off the two universal KL-representations.
    let pB = mp(&hb, &spec_b); // |- ( ( D d ) -> EB )
    let pC = mp(&hc, &spec_c); // |- ( ( D d ) -> EC )
    // step 2: ( ( D d ) -> ( EB /\ EC ) ).
    //   ax-ian : |- ( EB -> ( EC -> ( EB /\ EC ) ) )
    let eb_ec = reg(&wa(&eq_b, &eq_c)); // ( EB /\ EC )
    let ian = apply(
        "ax-ian",
        &[&eq_b, &eq_c],
        &[],
        reg(&wi(&eq_b, &reg(&wi(&eq_c, &eb_ec)))).toks,
    );
    let g_ian = imp_a1(&ian, &dd_pred); // ( (D d) -> ( EB -> ( EC -> (EB/\EC) ) ) )
    let g_ec_conj = imp_mp(&pB, &g_ian); // ( (D d) -> ( EC -> ( EB /\ EC ) ) )
    let g_conj = imp_mp(&pC, &g_ec_conj); // ( (D d) -> ( EB /\ EC ) )
    // step 3: thread sdg-slope-imp : ( ( EB /\ EC ) -> Q ) under ( D d ).
    let slope_imp_inst = use_thm(
        "sdg-slope-imp",
        &[("b", &bb), ("c", &cc), ("d", &dd), ("f", &ff)],
        &[],
        reg(&wi(&eb_ec, &bd_eq_cd)).toks,
    );
    let g_slope_imp = imp_a1(&slope_imp_inst, &dd_pred); // ( (D d) -> ( (EB/\EC) -> Q ) )
    let g_q = imp_mp(&g_conj, &g_slope_imp); // |- ( ( D d ) -> Q )
    // step 4: ax-gen over d  (SOUND: d bound in deriv.hb/deriv.hc).
    let all_guard = gen(&g_q, "vd", "d"); // |- A. d ( ( D d ) -> Q )
    // step 5: microcancellation.
    let b_eq_c = reg(&weq(&bb, &cc));
    let mc_inst = use_thm(
        "ax-microcancel",
        &[("b", &bb), ("c", &cc), ("d", &dd)],
        &[],
        wi(&w_of(&all_guard.stmt), &b_eq_c).toks,
    );
    let sdg_deriv = mp(&all_guard, &mc_inst); // |- b = c  (seam-free)

    // =====================================================================
    //  THE HIGHER-INFINITESIMAL HIERARCHY  D_k = { x | x^(k+1) = 0 }.
    //  D_1 = D (df-D), D_2 = D2 (df-D2 : ( D2 x ) <-> ( ( x * x ) * x )=0).
    //  Pure-substrate-algebra consequences (NO classical principle, NO
    //  metric residue, NO order — RING + df only).  These are the
    //  Taylor-base sanity $p; Taylor's formula ITSELF is deferred to the
    //  post-keystone agent and is NOT proved here (scope discipline).
    // =====================================================================

    // ---- sdg-D2-0 : |- ( D2 0 )  (0 is a level-2 infinitesimal too) -----
    //  ( 0 * 0 ) = 0                              [ax-mul0]
    //  ( ( 0 * 0 ) * 0 ) = 0                      [ax-mul0[x:=(0*0)]]
    //  df-D2[x:=0] + ax-bi2 + mp                  -> ( D2 0 )
    let z0z0 = reg(&binop(&zero, &zero, "*", "tmu")); // ( 0 * 0 )
    let z0z0_0 = reg(&binop(&z0z0, &zero, "*", "tmu")); // ( ( 0 * 0 ) * 0 )
    let cube0_eq0 = axeq("ax-mul0", &[&z0z0], &z0z0_0, &zero); // ((0*0)*0)=0
    let d2_0 = reg(&wD2(&zero));
    let cube0eq = reg(&weq(&z0z0_0, &zero));
    let bicond2_0 = reg(&wb(&d2_0, &cube0eq));
    let df_d2_0 = apply("df-D2", &[&zero], &[], bicond2_0.toks.clone());
    let bi2_2_0 = apply(
        "ax-bi2",
        &[&d2_0, &cube0eq],
        &[],
        wi(&bicond2_0, &reg(&wi(&cube0eq, &d2_0))).toks,
    );
    let cube0_imp_d2_0 = mp(&df_d2_0, &bi2_2_0); // ( ((0*0)*0)=0 -> ( D2 0 ) )
    let sdg_d2_0 = mp(&cube0_eq0, &cube0_imp_d2_0); // |- ( D2 0 )

    // ---- sdg-D1subD2 : [ ( D x ) ] |- ( D2 x )  — D_1 SUBSET D_2 --------
    //  This is the level-inclusion of the hierarchy, PURE RING ALGEBRA:
    //   ( D x )                                   [hyp dsub.h]
    //   ( x * x ) = 0                             [df-D + ax-bi1, mp]
    //   ( ( x * x ) * x ) = ( 0 * x )             [eq-mu1, mp]
    //   ( 0 * x ) = ( x * 0 ) = 0                 [ax-mulcom ; ax-mul0]
    //   ( ( x * x ) * x ) = 0                     [eqtr]
    //   ( D2 x )                                  [df-D2 + ax-bi2, mp]
    let dx = reg(&wD(&x));
    let xx = reg(&binop(&x, &x, "*", "tmu")); // ( x * x )
    let xxeq0 = reg(&weq(&xx, &zero)); // ( x * x ) = 0
    let dsub_h = Pf { stmt: dx.toks.clone(), rpn: t("dsub.h") };
    // df-D[x:=x] : ( ( D x ) <-> ( x * x )=0 )
    let dfd_x = apply("df-D", &[&x], &[], reg(&wb(&dx, &xxeq0)).toks.clone());
    // ax-bi1 : ( ( ph <-> ps ) -> ( ph -> ps ) )
    let bi1_x = apply(
        "ax-bi1",
        &[&dx, &xxeq0],
        &[],
        wi(&reg(&wb(&dx, &xxeq0)), &reg(&wi(&dx, &xxeq0))).toks,
    );
    let dx_imp_xxeq0 = mp(&dfd_x, &bi1_x); // ( ( D x ) -> ( x*x )=0 )
    let xx_eq0 = mp(&dsub_h, &dx_imp_xxeq0); // |- ( x * x ) = 0
    // eq-mu1[x:=(x*x), y:=0, z:=x] : ( (x*x)=0 -> ( (x*x)*x )=( 0*x ) )
    let cube = reg(&binop(&xx, &x, "*", "tmu")); // ( ( x * x ) * x )
    let zero_x = reg(&binop(&zero, &x, "*", "tmu")); // ( 0 * x )
    let cube_eq_0x = cong_l(&xx_eq0, &x, "*", "tmu", "eq-mu1"); // ((x*x)*x)=(0*x)
    // ( 0 * x ) = ( x * 0 ) = 0
    let x_zero = reg(&binop(&x, &zero, "*", "tmu")); // ( x * 0 )
    let mulcom_0x = axeq("ax-mulcom", &[&zero, &x], &zero_x, &x_zero); // (0*x)=(x*0)
    let mul0_x = axeq("ax-mul0", &[&x], &x_zero, &zero); // (x*0)=0
    let zerox_eq0 = eqtr(&mulcom_0x, &mul0_x); // ( 0 * x ) = 0
    let _ = (&cube, &zero_x);
    let cube_eq0 = eqtr(&cube_eq_0x, &zerox_eq0); // ( ( x*x )*x ) = 0
    // df-D2[x:=x] + ax-bi2 : ( ( (x*x)*x )=0 -> ( D2 x ) )
    let d2x = reg(&wD2(&x));
    let cubeeq = reg(&weq(&cube, &zero));
    let bicond2_x = reg(&wb(&d2x, &cubeeq));
    let df_d2_x = apply("df-D2", &[&x], &[], bicond2_x.toks.clone());
    let bi2_2_x = apply(
        "ax-bi2",
        &[&d2x, &cubeeq],
        &[],
        wi(&bicond2_x, &reg(&wi(&cubeeq, &d2x))).toks,
    );
    let cube_imp_d2x = mp(&df_d2_x, &bi2_2_x); // ( ((x*x)*x)=0 -> ( D2 x ) )
    let sdg_d1subd2 = mp(&cube_eq0, &cube_imp_d2x); // [ ( D x ) ] |- ( D2 x )

    // ---- sdg-kl1-is-kl : the k=1 instance of the generalized KL scheme
    //  IS the existing ax-kl (nothing new asserted at k=1).  Recorded as
    //  the identity implication on that exact KL_1 formula — a HONEST
    //  marker that KL_1 = ax-kl, not a re-derivation (which would be
    //  vacuous).  Pure logic (sdg-id specialised); consumes only ax-1/2.
    let kl1 = reg(&wex(
        "vb",
        "b",
        &wal(
            "vd",
            "d",
            &reg(&wi(
                &reg(&wD(&dd)),
                &reg(&weq(
                    &reg(&ap(&ff, &dd)),
                    &reg(&binop(
                        &reg(&ap(&ff, &zero)),
                        &reg(&binop(&bb, &dd, "*", "tmu")),
                        "+",
                        "tpl",
                    )),
                )),
            )),
        ),
    ));
    let sdg_kl1_is_kl = {
        // ( KL_1 -> KL_1 ) by the same construction as sdg-id (ax-1/ax-2).
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
            // §5b seam-closer #1: deduction-discharged additive
            // cancellation — HYPOTHESIS-FREE.  The intuitionistic
            // deduction theorem applied to sdg-addcan's single $e.
            "sdg-addcan-imp",
            "|- ( ( z + u ) = ( z + v ) -> u = v )",
            vec![],
            &sdg_addcan_imp,
        ),
        (
            // §5b seam-closer #2: deduction-discharged pointwise slope
            // lemma — HYPOTHESIS-FREE (conjunctive antecedent).
            "sdg-slope-imp",
            "|- ( ( ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) /\\ ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) -> ( b * d ) = ( c * d ) )",
            vec![],
            &sdg_slope_imp,
        ),
        (
            // THE FIRST SYNTHETIC-DIFFERENTIAL THEOREM — SEAM-FREE.
            // The linking universal is now mechanically threaded from the
            // two universal affine KL-representations (deriv.hb/deriv.hc,
            // each an ax-kl instance) via the deduction-form combinators +
            // ax-spec/ax-gen; NO linking `$e`.  Consumes ax-microcancel
            // (uniqueness) — and NOTHING classical.
            "sdg-deriv",
            "|- b = c",
            vec![
                ("deriv.hb", "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )"),
                ("deriv.hc", "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) )"),
            ],
            &sdg_deriv,
        ),
        // ---- THE HIGHER-INFINITESIMAL HIERARCHY (Taylor-base) ----------
        // Pure-substrate-algebra consequences of D_k = { x | x^(k+1)=0 }.
        // Taylor's formula itself is DEFERRED (post-keystone agent).
        ("sdg-D2-0", "|- ( D2 0 )", vec![], &sdg_d2_0),
        (
            // D_1 SUBSET D_2 : x^2=0 implies x^3=0.  Ring + df only; no
            // metric residue, no order, no classical principle.
            "sdg-D1subD2",
            "|- ( D2 x )",
            vec![("dsub.h", "|- ( D x )")],
            &sdg_d1subd2,
        ),
        (
            // The k=1 instance of the generalized KL scheme IS ax-kl
            // (KL_1 = the existing Kock-Lawvere axiom): recorded as the
            // identity on that exact KL_1 formula — an honest marker that
            // nothing new is asserted at k=1, not a vacuous re-derivation.
            "sdg-kl1-is-kl",
            "|- ( E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) -> E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) )",
            vec![],
            &sdg_kl1_is_kl,
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
