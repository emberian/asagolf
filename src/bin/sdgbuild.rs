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
    let eqw = reg(&weq(l, r));
    apply(label, floats, &[], eqw.toks)
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

/// `( k + t )` registered.
fn w0_ad(k: &W, tm: &W) -> W {
    reg(&binop(k, tm, "+", "tpl"))
}

/// Build `|- ( guard -> G )` where `G` is the left-nested conjunction of
/// `conjs`, GIVEN, for each conjunct ci, a proof `imps[i] : ( guard -> ci )`.
/// Uses ax-ian (lifted by imp_a1, detached by imp_mp) — pure ax-1/ax-2/
/// ax-mp/ax-ian; NO classical principle.  This is exactly the §5b
/// seam-closing technique seam-free sdg-deriv uses, generalised to an
/// n-ary conjunction.
fn build_guarded_conj(guard: &W, imps: &[&Pf], conjs: &[&W]) -> Pf {
    assert_eq!(imps.len(), conjs.len());
    assert!(!conjs.is_empty());
    // ( guard -> prefix[0] ) = imps[0]
    let mut acc = imps[0].clone();
    let mut prefix = conjs[0].clone();
    for k in 1..conjs.len() {
        let ci = conjs[k];
        let new_prefix = reg(&wa(&prefix, ci));
        // ax-ian : ( prefix -> ( ci -> ( prefix /\ ci ) ) )
        let ian = apply(
            "ax-ian",
            &[&prefix, ci],
            &[],
            reg(&wi(&prefix, &reg(&wi(ci, &new_prefix)))).toks,
        );
        // lift under guard: ( guard -> ( prefix -> ( ci -> (prefix/\ci) ) ) )
        let g_ian = imp_a1(&ian, guard);
        // detach prefix:  ( guard -> ( ci -> ( prefix /\ ci ) ) )
        let g_ci_conj = imp_mp(&acc, &g_ian);
        // detach ci:      ( guard -> ( prefix /\ ci ) )
        acc = imp_mp(imps[k], &g_ci_conj);
        prefix = new_prefix;
    }
    acc
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

    // =====================================================================
    //  §5g  GLOBALIZED DIFFERENTIATION CALCULUS.
    //
    //  The pointwise rules of data/sdg.calc.mm (sum / product / chain) are
    //  here LIFTED to GLOBAL synthetic-derivative theorems: the slope is no
    //  longer a free coefficient in a pointwise identity but a UNIQUELY
    //  determined function value, discharged through the SAME §5b seam
    //  fragment (deduction combinators + guarded ax-gen) and ax-microcancel
    //  that seam-free sdg-deriv uses — NO linking `$e`, NO mc.h.
    //
    //  Two ring-only, hypothesis-free helpers are first re-proved IN the
    //  generator (the calc corpus is read-only; its content is re-derived,
    //  not imported): sdg-add4 (commutative-monoid 4-shuffle) and
    //  sdg-rdistr (right distributivity).  Both pure ring; no df-D, no
    //  ax-mul0, no order, no classical principle.
    // =====================================================================

    let yv = leaf("vy", "y");
    let ev = leaf("ve", "e");
    let gg = leaf("vg", "g");
    let ww = leaf("vw", "w");
    let sa = leaf("va", "a"); // w's (global) slope variable

    // ---- sdg-add4 : ( ( x + y ) + ( z + e ) ) = ( ( x + z ) + ( y + e ) )
    //  Pure associativity/commutativity.  Chain:
    //   ((x+y)+(z+e)) =[addass]  (x+(y+(z+e)))
    //                 =[~addass] (x+((y+z)+e))
    //                 =[addcom]  (x+((z+y)+e))
    //                 =[addass]  (x+(z+(y+e)))
    //                 =[~addass] ((x+z)+(y+e))
    let x_p_y = reg(&binop(&x, &yv, "+", "tpl"));
    let z_p_e = reg(&binop(&zv, &ev, "+", "tpl"));
    let xy_zе = reg(&binop(&x_p_y, &z_p_e, "+", "tpl")); // ((x+y)+(z+e))
    let y_zе = reg(&binop(&yv, &z_p_e, "+", "tpl")); // (y+(z+e))
    let x_y_zе = reg(&binop(&x, &y_zе, "+", "tpl")); // (x+(y+(z+e)))
    let s_add4_1 = axeq(
        "ax-addass",
        &[&x, &yv, &z_p_e],
        &xy_zе,
        &x_y_zе,
    ); // ((x+y)+(z+e)) = (x+(y+(z+e)))
    // (y+(z+e)) = ((y+z)+e)  [sym addass]
    let y_p_z = reg(&binop(&yv, &zv, "+", "tpl"));
    let yz_e = reg(&binop(&y_p_z, &ev, "+", "tpl"));
    let inner2 = eqsym(&axeq("ax-addass", &[&yv, &zv, &ev], &yz_e, &y_zе)); // (y+(z+e))=((y+z)+e)
    let s_add4_2 = cong_r(&inner2, &x, "+", "tpl", "eq-pl2"); // (x+(y+(z+e)))=(x+((y+z)+e))
    // (y+z)=(z+y) -> cong under +e -> cong under x+
    let z_p_y = reg(&binop(&zv, &yv, "+", "tpl"));
    let zy_e = reg(&binop(&z_p_y, &ev, "+", "tpl"));
    let yz_zy = axeq("ax-addcom", &[&yv, &zv], &y_p_z, &z_p_y); // (y+z)=(z+y)
    let yze_zye = cong_l(&yz_zy, &ev, "+", "tpl", "eq-pl1"); // ((y+z)+e)=((z+y)+e)
    let s_add4_3 = cong_r(&yze_zye, &x, "+", "tpl", "eq-pl2"); // (x+((y+z)+e))=(x+((z+y)+e))
    // ((z+y)+e)=(z+(y+e))  [addass]
    let y_p_e = reg(&binop(&yv, &ev, "+", "tpl"));
    let z_ye = reg(&binop(&zv, &y_p_e, "+", "tpl"));
    let zye_z_ye = axeq("ax-addass", &[&zv, &yv, &ev], &zy_e, &z_ye); // ((z+y)+e)=(z+(y+e))
    let s_add4_4 = cong_r(&zye_z_ye, &x, "+", "tpl", "eq-pl2"); // (x+((z+y)+e))=(x+(z+(y+e)))
    // (x+(z+(y+e))) = ((x+z)+(y+e))  [sym addass x z (y+e)]
    let x_p_z = reg(&binop(&x, &zv, "+", "tpl"));
    let xz_ye = reg(&binop(&x_p_z, &y_p_e, "+", "tpl"));
    let x_z_ye = reg(&binop(&x, &z_ye, "+", "tpl")); // (x+(z+(y+e)))
    let s_add4_5 = eqsym(&axeq("ax-addass", &[&x, &zv, &y_p_e], &xz_ye, &x_z_ye)); // (x+(z+(y+e)))=((x+z)+(y+e))
    let sdg_add4 = eqtr(
        &s_add4_1,
        &eqtr(&s_add4_2, &eqtr(&s_add4_3, &eqtr(&s_add4_4, &s_add4_5))),
    ); // |- ( ( x + y ) + ( z + e ) ) = ( ( x + z ) + ( y + e ) )

    // ---- sdg-rdistr : ( ( x + y ) * z ) = ( ( x * z ) + ( y * z ) ) -----
    //  (x+y)*z =[mulcom] z*(x+y) =[distr] (z*x)+(z*y)
    //          =[mulcom both summands] (x*z)+(y*z)
    let xy_mul_z = reg(&binop(&x_p_y, &zv, "*", "tmu")); // ((x+y)*z)
    let z_mul_xy = reg(&binop(&zv, &x_p_y, "*", "tmu")); // (z*(x+y))
    let r1 = axeq("ax-mulcom", &[&x_p_y, &zv], &xy_mul_z, &z_mul_xy); // ((x+y)*z)=(z*(x+y))
    let z_mul_x = reg(&binop(&zv, &x, "*", "tmu"));
    let z_mul_y = reg(&binop(&zv, &yv, "*", "tmu"));
    let zx_p_zy = reg(&binop(&z_mul_x, &z_mul_y, "+", "tpl"));
    let r2 = axeq("ax-distr", &[&zv, &x, &yv], &z_mul_xy, &zx_p_zy); // (z*(x+y))=((z*x)+(z*y))
    let x_mul_z = reg(&binop(&x, &zv, "*", "tmu"));
    let y_mul_z = reg(&binop(&yv, &zv, "*", "tmu"));
    let zx_xz = axeq("ax-mulcom", &[&zv, &x], &z_mul_x, &x_mul_z); // (z*x)=(x*z)
    let zy_yz = axeq("ax-mulcom", &[&zv, &yv], &z_mul_y, &y_mul_z); // (z*y)=(y*z)
    let r3 = cong_l(&zx_xz, &z_mul_y, "+", "tpl", "eq-pl1"); // ((z*x)+(z*y))=((x*z)+(z*y))
    let r4 = cong_r(&zy_yz, &x_mul_z, "+", "tpl", "eq-pl2"); // ((x*z)+(z*y))=((x*z)+(y*z))
    let sdg_rdistr = eqtr(&r1, &eqtr(&r2, &eqtr(&r3, &r4))); // |- ((x+y)*z)=((x*z)+(y*z))

    // =====================================================================
    //  Shared seam machinery for the global calculus theorems.
    //
    //  Every global rule is: GIVEN the universal KL representations
    //  (existence, ax-kl instances, as universal `$e`) for f, g and the
    //  composite w, PLUS the universal pointwise relation that DEFINES w
    //  (w=f+g / w=f·g / w=g∘f) as `$e` — CONCLUDE the unique global slope
    //  identity (s = <expr>) by:
    //    1. ax-spec strips A.d from every universal `$e` under guard (D d).
    //    2. ax-ian (lifted by imp_a1, detached by imp_mp) builds the big
    //       conjunctive antecedent G under (D d).
    //    3. a deduction-discharged pointwise core `( G -> ( s*d = E*d ) )`
    //       (built ONLY from imp_a1/imp_mp/imp_eqtr/imp_eqsym/imp_cong_*
    //       and sdg-addcan-imp + the ring helpers — NO classical principle)
    //       is lifted under (D d) and detached -> ( (D d) -> s*d = E*d ).
    //    4. gen (ax-gen) over d (SOUND: d is bound in every `$e`).
    //    5. ax-microcancel : s = E.
    //  The `$e` hypotheses are ONLY universals (KL existence) and the
    //  defining pointwise relation — exactly the discipline of seam-free
    //  sdg-deriv; the linking universal s*d=E*d is THREADED, never assumed.
    // =====================================================================

    // term abbreviations reused below
    let apg0 = reg(&ap(&gg, &zero)); // ( ap g 0 )
    let apgd = reg(&ap(&gg, &dd)); // ( ap g d )
    let apw0 = reg(&ap(&ww, &zero)); // ( ap w 0 )
    let apwd = reg(&ap(&ww, &dd)); // ( ap w d )
    let s_d = reg(&binop(&sa, &dd, "*", "tmu")); // ( a * d )  (w's slope * d)

    // build the conjunctive antecedent G from a list of conjunct wffs
    // (left-nested: ( ( ( c1 /\ c2 ) /\ c3 ) ... )).  Returns the W of G
    // plus, for each conjunct, a Pf  |- ( G -> conjunct ).
    fn conj_and_projs(conjs: &[W]) -> (W, Vec<Pf>) {
        assert!(!conjs.is_empty());
        let mut g = conjs[0].clone();
        for cj in &conjs[1..] {
            g = reg(&wa(&g, cj));
        }
        // projections: for conjunct i, ( G -> ci ).  G is left-nested;
        // peel right with ax-iar to expose the last conjunct, ax-ial to
        // descend.  Build ( G -> ci ) compositionally.
        let n = conjs.len();
        let mut projs: Vec<Pf> = Vec::with_capacity(n);
        // prefix[k] = W of the left-nested conjunction of conjs[0..=k]
        let mut prefix: Vec<W> = Vec::with_capacity(n);
        prefix.push(conjs[0].clone());
        for k in 1..n {
            prefix.push(reg(&wa(&prefix[k - 1], &conjs[k])));
        }
        // ( G -> prefix[k] ) for every k: from G, repeatedly ax-ial.
        // g_to_prefix[n-1] = identity-ish ( G -> G ) handled via sdg-id-like;
        // simpler: ( G -> prefix[k] ) by (n-1-k) left-projections.
        let g_w = prefix[n - 1].clone();
        let mut g_to_prefix: Vec<Pf> = vec![Pf { stmt: vec![], rpn: vec![] }; n];
        // ( G -> G ): use ax-1-based identity via the sdg-id trick inline.
        g_to_prefix[n - 1] = {
            let p = &g_w;
            let pp = reg(&wi(p, p));
            let p_pp = reg(&wi(p, &pp));
            let pp_p = reg(&wi(&pp, p));
            let p__pp_p = reg(&wi(p, &pp_p));
            let _ = reg(&wi(&p_pp, &pp));
            let a1 = apply("ax-1", &[p, p], &[], p_pp.toks.clone());
            let a2 = apply("ax-1", &[p, &pp], &[], p__pp_p.toks.clone());
            let a3 = apply("ax-2", &[p, &pp, p], &[], {
                let lhs = wi(p, &p__pp_p);
                let rhs = wi(&p_pp, &pp);
                wi(&lhs, &rhs).toks
            });
            mp(&a1, &mp(&a2, &a3))
        };
        for k in (0..n - 1).rev() {
            // prefix[k] = ( prefix[k] /\ conjs[k+1] ) split left:
            // ax-ial : ( ( prefix[k] /\ conjs[k+1] ) -> prefix[k] )
            let lhs = prefix[k].clone();
            let rhs = conjs[k + 1].clone();
            let pk1 = reg(&wa(&lhs, &rhs)); // = prefix[k+1]
            let ial = apply("ax-ial", &[&lhs, &rhs], &[], reg(&wi(&pk1, &lhs)).toks);
            // ( G -> prefix[k] ) = imp_mp( (G->prefix[k+1]), imp_a1(ial,G) )
            let g_ial = imp_a1(&ial, &g_w);
            g_to_prefix[k] = imp_mp(&g_to_prefix[k + 1], &g_ial);
        }
        for i in 0..n {
            if i == n - 1 {
                // last conjunct: ax-iar on prefix[n-1] = ( prefix[n-2] /\ cn )
                if n == 1 {
                    projs.push(g_to_prefix[0].clone());
                } else {
                    let lhs = prefix[n - 2].clone();
                    let rhs = conjs[n - 1].clone();
                    let iar = apply("ax-iar", &[&lhs, &rhs], &[], reg(&wi(&g_w, &rhs)).toks);
                    projs.push(iar);
                }
            } else {
                // conjunct i is the RIGHT child of prefix[i] (= prefix[i-1] /\ ci)
                // for i>=1; for i==0 it is the left-most leaf of prefix[0..].
                if i == 0 {
                    // ( G -> prefix[0] ) and prefix[0] == conjs[0]
                    projs.push(g_to_prefix[0].clone());
                } else {
                    let lhs = prefix[i - 1].clone();
                    let rhs = conjs[i].clone();
                    let pk = reg(&wa(&lhs, &rhs)); // prefix[i]
                    let iar = apply("ax-iar", &[&lhs, &rhs], &[], reg(&wi(&pk, &rhs)).toks);
                    let g_iar = imp_a1(&iar, &g_w);
                    projs.push(imp_mp(&g_to_prefix[i], &g_iar));
                }
            }
        }
        (g_w, projs)
    }

    // ---------------------------------------------------------------------
    //  GLOBAL SUM :  ( f + g )' = f' + g'   (derivative operator additive)
    //
    //  $e (all universal / pointwise — the KL existence + the definition of
    //  w as the pointwise sum, exactly the seam-free sdg-deriv discipline):
    //    sum.hf  : A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )
    //    sum.hg  : A. d ( ( D d ) -> ( ap g d ) = ( ( ap g 0 ) + ( c * d ) ) )
    //    sum.hw  : A. d ( ( D d ) -> ( ap w d ) = ( ( ap w 0 ) + ( a * d ) ) )
    //    sum.hpw : A. d ( ( D d ) -> ( ap w d ) = ( ( ap f d ) + ( ap g d ) ) )
    //    sum.h0  : ( ap w 0 ) = ( ( ap f 0 ) + ( ap g 0 ) )
    //  conclusion:  a = ( b + c )    (the global identifying equation;
    //  uniqueness of w's slope discharged via ax-microcancel — NO mc.h).
    // ---------------------------------------------------------------------
    let apf0 = reg(&ap(&ff, &zero));
    let apfd = reg(&ap(&ff, &dd));
    let b_d = reg(&binop(&bb, &dd, "*", "tmu"));
    let c_d = reg(&binop(&cc, &dd, "*", "tmu"));
    let k_bd = reg(&binop(&apf0, &b_d, "+", "tpl"));
    let g_cd = reg(&binop(&apg0, &c_d, "+", "tpl"));
    let w_ad = reg(&binop(&apw0, &s_d, "+", "tpl"));
    let dd_pred = reg(&wD(&dd));
    let ef = reg(&weq(&apfd, &k_bd)); // ( ap f d ) = ( ( ap f 0 ) + ( b*d ) )
    let eg = reg(&weq(&apgd, &g_cd)); // ( ap g d ) = ( ( ap g 0 ) + ( c*d ) )
    let ew = reg(&weq(&apwd, &w_ad)); // ( ap w d ) = ( ( ap w 0 ) + ( a*d ) )
    let fpg = reg(&binop(&apfd, &apgd, "+", "tpl"));
    let epw = reg(&weq(&apwd, &fpg)); // ( ap w d ) = ( ( ap f d ) + ( ap g d ) )
    let kw0 = reg(&binop(&apf0, &apg0, "+", "tpl"));
    let e0 = reg(&weq(&apw0, &kw0)); // ( ap w 0 ) = ( ( ap f 0 ) + ( ap g 0 ) )

    let sum_hf = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ef)))).toks, rpn: t("sum.hf") };
    let sum_hg = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &eg)))).toks, rpn: t("sum.hg") };
    let sum_hw = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ew)))).toks, rpn: t("sum.hw") };
    let sum_hpw = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &epw)))).toks, rpn: t("sum.hpw") };
    let sum_h0 = Pf { stmt: e0.toks.clone(), rpn: t("sum.h0") };

    // step 1: ax-spec each universal under (D d).
    let mk_spec = |all: &Pf, body_imp: &W| -> Pf {
        let inst = apply(
            "ax-spec",
            &[body_imp, &dd],
            &[],
            reg(&wi(&w_of(&all.stmt), body_imp)).toks,
        );
        mp(all, &inst) // |- ( ( D d ) -> <eq> )
    };
    let imp_f = mk_spec(&sum_hf, &reg(&wi(&dd_pred, &ef)));
    let imp_g = mk_spec(&sum_hg, &reg(&wi(&dd_pred, &eg)));
    let imp_w = mk_spec(&sum_hw, &reg(&wi(&dd_pred, &ew)));
    let imp_pw = mk_spec(&sum_hpw, &reg(&wi(&dd_pred, &epw)));
    // sum.h0 is non-universal: lift under (D d) by imp_a1.
    let imp_e0 = imp_a1(&sum_h0, &dd_pred); // ( ( D d ) -> e0 )

    // step 2: deduction-discharged pointwise SUM core, under conjunctive G.
    //   G := ( ( ( ( EF /\ EG ) /\ EW ) /\ EPW ) /\ E0 )
    //   target: ( G -> ( ( a*d ) = ( ( b + c )*d ) ) )
    let (g_sum, p_sum) =
        conj_and_projs(&[ef.clone(), eg.clone(), ew.clone(), epw.clone(), e0.clone()]);
    let g_ef = &p_sum[0]; // ( G -> EF )
    let g_eg = &p_sum[1];
    let g_ew = &p_sum[2];
    let g_epw = &p_sum[3];
    let g_e0 = &p_sum[4];
    // Under G:
    //  ( ap w d ) = ( ap f d ) + ( ap g d )                      [EPW]
    //             = ( (apf0+b*d) + (apg0+c*d) )                   [cong EF,EG]
    //             = ( (apf0+apg0) + ((b*d)+(c*d)) )               [sdg-add4]
    //             = ( (ap w 0)  + ((b*d)+(c*d)) )                  [~E0 cong]
    //             = ( (ap w 0)  + ((b+c)*d) )                      [~sdg-rdistr]
    //  also ( ap w d ) = ( (ap w 0) + (a*d) )                      [EW]
    //  => ( (ap w 0)+(a*d) ) = ( (ap w 0)+((b+c)*d) )  [eqtr via apwd]
    //  => ( a*d ) = ( (b+c)*d )                          [sdg-addcan-imp]
    let bpc = reg(&binop(&bb, &cc, "+", "tpl")); // ( b + c )
    let bpc_d = reg(&binop(&bpc, &dd, "*", "tmu")); // ( ( b + c ) * d )
    let bd_p_cd = reg(&binop(&b_d, &c_d, "+", "tpl")); // ( ( b*d ) + ( c*d ) )
    let kf_kg = reg(&binop(&apf0, &apg0, "+", "tpl")); // ( apf0 + apg0 )
    let lhs_big = reg(&binop(&k_bd, &g_cd, "+", "tpl")); // ( (apf0+b*d) + (apg0+c*d) )
    let mid_big = reg(&binop(&kf_kg, &bd_p_cd, "+", "tpl")); // ( (apf0+apg0) + ((b*d)+(c*d)) )
    let w0_bdcd = reg(&binop(&apw0, &bd_p_cd, "+", "tpl")); // ( apw0 + ((b*d)+(c*d)) )
    let w0_bpc_d = reg(&binop(&apw0, &bpc_d, "+", "tpl")); // ( apw0 + ((b+c)*d) )

    // ( G -> ( ap w d ) = ( (apf0+b*d) + (apg0+c*d) ) )
    //   from g_epw and cong with g_ef (left) then g_eg (right).
    let g_step_fg = {
        // ( G -> ( apfd + apgd ) = ( (apf0+b*d) + apgd ) )  via g_ef cong_l
        let c1 = imp_cong_l(g_ef, &apgd, "+", "tpl", "eq-pl1");
        // ( G -> ( (apf0+b*d) + apgd ) = ( (apf0+b*d) + (apg0+c*d) ) ) via g_eg cong_r
        let c2 = imp_cong_r(g_eg, &k_bd, "+", "tpl", "eq-pl2");
        // chain with g_epw: ( G -> apwd = (apf0+b*d)+(apg0+c*d) )
        imp_eqtr(g_epw, &imp_eqtr(&c1, &c2))
    };
    // sdg-add4[x:=apf0,y:=(b*d),z:=apg0,e:=(c*d)] :
    //   |- ( ( apf0 + (b*d) ) + ( apg0 + (c*d) ) )
    //        = ( ( apf0 + apg0 ) + ( (b*d) + (c*d) ) )
    let add4_inst = use_thm(
        "sdg-add4",
        &[("x", &apf0), ("y", &b_d), ("z", &apg0), ("e", &c_d)],
        &[],
        reg(&weq(&lhs_big, &mid_big)).toks,
    );
    let g_add4 = imp_a1(&add4_inst, &g_sum); // ( G -> lhs_big = mid_big )
    // ( G -> apwd = mid_big )
    let g_apwd_mid = imp_eqtr(&g_step_fg, &g_add4);
    // ( apf0 + apg0 ) = ( ap w 0 )   from g_e0 (E0: apw0 = apf0+apg0) symm
    let g_kfkg_w0 = imp_eqsym(g_e0); // ( G -> ( apf0+apg0 ) = apw0 )
    // cong under +( (b*d)+(c*d) )  ->  ( G -> mid_big = w0_bdcd )
    let g_mid_w0 = imp_cong_l(&g_kfkg_w0, &bd_p_cd, "+", "tpl", "eq-pl1");
    let g_apwd_w0bdcd = imp_eqtr(&g_apwd_mid, &g_mid_w0); // ( G -> apwd = w0_bdcd )
    // sdg-rdistr[x:=b,y:=c,z:=d] : |- ( (b+c)*d ) = ( (b*d)+(c*d) )
    let rdistr_inst = use_thm(
        "sdg-rdistr",
        &[("x", &bb), ("y", &cc), ("z", &dd)],
        &[],
        reg(&weq(&bpc_d, &bd_p_cd)).toks,
    );
    // need ( (b*d)+(c*d) ) = ( (b+c)*d ) : symm
    let rdistr_sym = eqsym(&rdistr_inst); // |- ( (b*d)+(c*d) ) = ( (b+c)*d )
    let g_rdistr = imp_a1(&rdistr_sym, &g_sum);
    let g_bdcd_to_bpcd = imp_cong_r(&g_rdistr, &apw0, "+", "tpl", "eq-pl2"); // ( G -> w0_bdcd = w0_bpc_d )
    let g_apwd_w0bpcd = imp_eqtr(&g_apwd_w0bdcd, &g_bdcd_to_bpcd); // ( G -> apwd = w0_bpc_d )
    // EW: ( G -> apwd = ( apw0 + (a*d) ) ) ; symm -> ( G -> (apw0+(a*d)) = apwd )
    let g_w0ad_apwd = imp_eqsym(g_ew);
    // chain: ( G -> ( apw0+(a*d) ) = w0_bpc_d )
    let g_w0ad_w0bpcd = imp_eqtr(&g_w0ad_apwd, &g_apwd_w0bpcd);
    // sdg-addcan-imp[z:=apw0,u:=(a*d),v:=((b+c)*d)] :
    //   |- ( ( apw0+(a*d) ) = ( apw0+((b+c)*d) ) -> ( a*d ) = ( (b+c)*d ) )
    let ac_sum = use_thm(
        "sdg-addcan-imp",
        &[("z", &apw0), ("u", &s_d), ("v", &bpc_d)],
        &[],
        reg(&wi(&reg(&weq(&w0_ad(&apw0, &s_d), &w0_bpc_d)), &reg(&weq(&s_d, &bpc_d)))).toks,
    );
    let g_ac_sum = imp_a1(&ac_sum, &g_sum); // ( G -> ( (w0+ad)=(w0+bpcd) -> ad=bpcd ) )
    let g_q_sum = imp_mp(&g_w0ad_w0bpcd, &g_ac_sum); // ( G -> ( a*d ) = ( (b+c)*d ) )

    // step 3: thread ( G -> Q ) under ( D d ).  Build ( (D d) -> G ) from
    //  the five spec'd / lifted implications via ax-ian chained left.
    let g_under_d_sum = build_guarded_conj(
        &dd_pred,
        &[&imp_f, &imp_g, &imp_w, &imp_pw, &imp_e0],
        &[&ef, &eg, &ew, &epw, &e0],
    );
    // ( (D d) -> ( G -> Q ) ) by imp_a1, then imp_mp -> ( (D d) -> Q ).
    let g_sum_imp_under_d = imp_a1(&g_q_sum, &dd_pred);
    let dd_to_q_sum = imp_mp(&g_under_d_sum, &g_sum_imp_under_d); // ( (D d) -> a*d=(b+c)*d )
    // step 4: ax-gen over d.
    let all_q_sum = gen(&dd_to_q_sum, "vd", "d"); // A. d ( (D d) -> a*d=(b+c)*d )
    // step 5: ax-microcancel[b:=a, c:=(b+c), d:=d] : ( A.d (...) -> a = (b+c) )
    let a_eq_bpc = reg(&weq(&sa, &bpc));
    let mc_sum = use_thm(
        "ax-microcancel",
        &[("b", &sa), ("c", &bpc), ("d", &dd)],
        &[],
        wi(&w_of(&all_q_sum.stmt), &a_eq_bpc).toks,
    );
    let sdg_global_sum = mp(&all_q_sum, &mc_sum); // |- a = ( b + c )

    // ---------------------------------------------------------------------
    //  GLOBAL PRODUCT / LEIBNIZ :  ( f · g )' = f'·g + f·g'  globally.
    //
    //  $e :  product KL reps for f, g, w + the pointwise product relation
    //        ( ap w d ) = ( ap f d ) * ( ap g d )  and at 0, all universal.
    //  conclusion:  a = ( ( ( ap f 0 ) * c ) + ( b * ( ap g 0 ) ) )
    //  i.e. the global Leibniz slope:  f(0)·g' + f'·g(0)  (the synthetic
    //  product rule; the second-order ( b*d )·( c*d ) term is killed by
    //  d·d=0 — df-D applied to the SHARED GUARD ( D d ), ax-mul0).
    // ---------------------------------------------------------------------
    // pointwise product equality, all under (D d):
    let f_mul_g = reg(&binop(&apfd, &apgd, "*", "tmu")); // ( apfd * apgd )
    let epw_p = reg(&weq(&apwd, &f_mul_g)); // ( ap w d ) = ( apfd * apgd )
    let kf_mul_kg = reg(&binop(&apf0, &apg0, "*", "tmu"));
    let e0_p = reg(&weq(&apw0, &kf_mul_kg)); // ( ap w 0 ) = ( apf0 * apg0 )
    // Leibniz slope L := ( ( apf0 * c ) + ( b * apg0 ) )
    let kf_c = reg(&binop(&apf0, &cc, "*", "tmu"));
    let b_kg = reg(&binop(&bb, &apg0, "*", "tmu"));
    let leib = reg(&binop(&kf_c, &b_kg, "+", "tpl"));
    let leib_d = reg(&binop(&leib, &dd, "*", "tmu")); // ( L * d )

    let prod_hf = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ef)))).toks, rpn: t("prod.hf") };
    let prod_hg = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &eg)))).toks, rpn: t("prod.hg") };
    let prod_hw = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ew)))).toks, rpn: t("prod.hw") };
    let prod_hpw = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &epw_p)))).toks, rpn: t("prod.hpw") };
    let prod_h0 = Pf { stmt: e0_p.toks.clone(), rpn: t("prod.h0") };

    let pimp_f = mk_spec(&prod_hf, &reg(&wi(&dd_pred, &ef)));
    let pimp_g = mk_spec(&prod_hg, &reg(&wi(&dd_pred, &eg)));
    let pimp_w = mk_spec(&prod_hw, &reg(&wi(&dd_pred, &ew)));
    let pimp_pw = mk_spec(&prod_hpw, &reg(&wi(&dd_pred, &epw_p)));
    let pimp_e0 = imp_a1(&prod_h0, &dd_pred);

    // The pointwise product algebra, deduction-discharged under
    //  G := ( ( ( ( EF /\ EG ) /\ EW ) /\ EPW' ) /\ E0' )  AND the guard
    //  ( D d ) is also a conjunct (we genuinely consume d·d=0 via df-D on
    //  it — the canonical SDG Leibniz step).
    let (g_prod, p_prod) = conj_and_projs(&[
        ef.clone(),
        eg.clone(),
        ew.clone(),
        epw_p.clone(),
        e0_p.clone(),
        dd_pred.clone(),
    ]);
    let gp_ef = &p_prod[0];
    let gp_eg = &p_prod[1];
    let gp_ew = &p_prod[2];
    let gp_epw = &p_prod[3];
    let gp_e0 = &p_prod[4];
    let gp_dd = &p_prod[5]; // ( G -> ( D d ) )

    // ( G -> apwd = ( apf0+b*d ) * ( apg0+c*d ) )
    let g_prod_fg = {
        let c1 = imp_cong_l(gp_ef, &apgd, "*", "tmu", "eq-mu1");
        let c2 = imp_cong_r(gp_eg, &k_bd, "*", "tmu", "eq-mu2");
        imp_eqtr(gp_epw, &imp_eqtr(&c1, &c2))
    }; // ( G -> apwd = ( (apf0+bd) * (apg0+cd) ) )

    // Expand ( (apf0+bd)*(apg0+cd) ) by distributivity to
    //   ( apf0*apg0 ) + ( ( (apf0*c) + (b*apg0) )*d ) + ( (b*c)*(d*d) )
    // then kill the last term with ( D d ) (df-D: d*d=0 ; ax-mul0).
    // We assemble this as a closed ring identity instance proved by a
    // dedicated builder lemma sdg-prodexp (hypothesis-free EXCEPT it needs
    // d*d=0, supplied as one antecedent), then discharged under G via the
    // ( G -> ( D d ) ) projection.  To stay within the existing combinator
    // toolkit we build the chain explicitly:
    let kbd = k_bd.clone(); // ( apf0 + ( b*d ) )
    let gcd = g_cd.clone(); // ( apg0 + ( c*d ) )
    let prod_lr = reg(&binop(&kbd, &gcd, "*", "tmu")); // ( kbd * gcd )
    // distribute: kbd*gcd = ( kbd*apg0 ) + ( kbd*(c*d) )            [ax-distr]
    let kbd_kg = reg(&binop(&kbd, &apg0, "*", "tmu"));
    let kbd_cd = reg(&binop(&kbd, &c_d, "*", "tmu"));
    let dist1 = axeq(
        "ax-distr",
        &[&kbd, &apg0, &c_d],
        &prod_lr,
        &reg(&binop(&kbd_kg, &kbd_cd, "+", "tpl")),
    ); // kbd*gcd = (kbd*apg0)+(kbd*(c*d))
    // kbd*apg0 = (apf0*apg0)+((b*d)*apg0)                            [rdistr]
    let kf_kg2 = reg(&binop(&apf0, &apg0, "*", "tmu"));
    let bd_kg = reg(&binop(&b_d, &apg0, "*", "tmu"));
    let rd_a = use_thm(
        "sdg-rdistr",
        &[("x", &apf0), ("y", &b_d), ("z", &apg0)],
        &[],
        reg(&weq(&kbd_kg, &reg(&binop(&kf_kg2, &bd_kg, "+", "tpl")))).toks,
    );
    // kbd*(c*d) = (apf0*(c*d))+((b*d)*(c*d))                         [rdistr]
    let kf_cd = reg(&binop(&apf0, &c_d, "*", "tmu"));
    let bd_cd = reg(&binop(&b_d, &c_d, "*", "tmu"));
    let rd_b = use_thm(
        "sdg-rdistr",
        &[("x", &apf0), ("y", &b_d), ("z", &c_d)],
        &[],
        reg(&weq(&kbd_cd, &reg(&binop(&kf_cd, &bd_cd, "+", "tpl")))).toks,
    );
    // assemble prod_lr = ( ( (apf0*apg0)+((b*d)*apg0) ) + ( (apf0*(c*d))+((b*d)*(c*d)) ) )
    let sumA = reg(&binop(&kf_kg2, &bd_kg, "+", "tpl"));
    let sumB = reg(&binop(&kf_cd, &bd_cd, "+", "tpl"));
    let dist_full = eqtr(
        &dist1,
        &eqtr(
            &cong_l(&rd_a, &kbd_cd, "+", "tpl", "eq-pl1"),
            &cong_r(&rd_b, &sumA, "+", "tpl", "eq-pl2"),
        ),
    ); // prod_lr = ( sumA + sumB )
    // ( (b*d)*(c*d) ) = ( (b*c)*(d*d) )  : reassociate/commute
    //   (b*d)*(c*d) = b*(d*(c*d)) = b*((d*c)*d) = b*((c*d)*d)
    //              = b*(c*(d*d)) = (b*c)*(d*d)
    let b_c = reg(&binop(&bb, &cc, "*", "tmu"));
    let d_d = reg(&binop(&dd, &dd, "*", "tmu"));
    let bc_dd = reg(&binop(&b_c, &d_d, "*", "tmu"));
    let bdcd_eq_bcdd = {
        // (b*d)*(c*d) = b*( d*(c*d) )                       [ax-mulass]
        let t1 = axeq(
            "ax-mulass",
            &[&bb, &dd, &c_d],
            &reg(&binop(&b_d, &c_d, "*", "tmu")),
            &reg(&binop(&bb, &reg(&binop(&dd, &c_d, "*", "tmu")), "*", "tmu")),
        );
        // d*(c*d) = (d*c)*d                                  [~ax-mulass]
        let d_cd = reg(&binop(&dd, &c_d, "*", "tmu"));
        let dc = reg(&binop(&dd, &cc, "*", "tmu"));
        let dc_d = reg(&binop(&dc, &dd, "*", "tmu"));
        let t2 = eqsym(&axeq("ax-mulass", &[&dd, &cc, &dd], &dc_d, &d_cd));
        // (d*c) = (c*d)                                      [ax-mulcom]
        let cd = reg(&binop(&cc, &dd, "*", "tmu"));
        let t3 = cong_l(
            &axeq("ax-mulcom", &[&dd, &cc], &dc, &cd),
            &dd,
            "*",
            "tmu",
            "eq-mu1",
        ); // (d*c)*d = (c*d)*d
        // (c*d)*d = c*(d*d)                                  [ax-mulass]
        let cd_d = reg(&binop(&cd, &dd, "*", "tmu"));
        let c_dd = reg(&binop(&cc, &d_d, "*", "tmu"));
        let t4 = axeq("ax-mulass", &[&cc, &dd, &dd], &cd_d, &c_dd);
        // b*( d*(c*d) ) = b*( c*(d*d) ) via cong_r of (t2;t3;t4)
        let inner = eqtr(&t2, &eqtr(&t3, &t4)); // d*(c*d) = c*(d*d)
        let t5 = cong_r(&inner, &bb, "*", "tmu", "eq-mu2"); // b*(d*(c*d)) = b*(c*(d*d))
        // b*( c*(d*d) ) = (b*c)*(d*d)                        [~ax-mulass]
        let t6 = eqsym(&axeq(
            "ax-mulass",
            &[&bb, &cc, &d_d],
            &bc_dd,
            &reg(&binop(&bb, &c_dd, "*", "tmu")),
        ));
        eqtr(&t1, &eqtr(&t5, &t6)) // (b*d)*(c*d) = (b*c)*(d*d)
    };
    // Under G: ( D d ) -> ( d*d ) = 0   [df-D + ax-bi1], then (b*c)*(d*d)=(b*c)*0=0
    let dd_eq0 = reg(&weq(&d_d, &zero));
    let g_dd_eq0 = {
        // df-D[x:=d] : ( ( D d ) <-> ( d*d )=0 )
        let dfd = apply("df-D", &[&dd], &[], reg(&wb(&dd_pred, &dd_eq0)).toks);
        // ax-bi1 : ( ( ph<->ps ) -> ( ph -> ps ) )
        let bi1 = apply(
            "ax-bi1",
            &[&dd_pred, &dd_eq0],
            &[],
            wi(&reg(&wb(&dd_pred, &dd_eq0)), &reg(&wi(&dd_pred, &dd_eq0))).toks,
        );
        let dd_imp = mp(&dfd, &bi1); // ( ( D d ) -> ( d*d )=0 )
        // thread under G: g_dd : ( G -> ( D d ) ) ; imp_a1 lifts dd_imp,
        // imp_mp detaches -> ( G -> ( d*d )=0 ).
        let g_ddimp = imp_a1(&dd_imp, &g_prod);
        imp_mp(gp_dd, &g_ddimp) // ( G -> ( d*d )=0 )
    };
    // ( G -> ( (b*c)*(d*d) ) = ( (b*c)*0 ) )   cong_r of g_dd_eq0
    let g_bcdd_bc0 = imp_cong_r(&g_dd_eq0, &b_c, "*", "tmu", "eq-mu2");
    // ( (b*c)*0 ) = 0   [ax-mul0]  -> lift under G
    let bc_0 = reg(&binop(&b_c, &zero, "*", "tmu"));
    let bc0_eq0 = axeq("ax-mul0", &[&b_c], &bc_0, &zero);
    let g_bc0_0 = imp_a1(&bc0_eq0, &g_prod);
    let g_bcdd_0 = imp_eqtr(&g_bcdd_bc0, &g_bc0_0); // ( G -> ( (b*c)*(d*d) )=0 )
    // bdcd = (b*d)*(c*d) ; ( G -> bdcd = 0 )
    let g_bdcd_bcdd = imp_a1(&bdcd_eq_bcdd, &g_prod); // ( G -> (b*d)*(c*d) = (b*c)*(d*d) )
    let g_bdcd_0 = imp_eqtr(&g_bdcd_bcdd, &g_bcdd_0); // ( G -> (b*d)*(c*d) = 0 )

    // Now collect: prod_lr = sumA + sumB, sumA = (apf0*apg0)+((b*d)*apg0),
    // sumB = (apf0*(c*d))+((b*d)*(c*d)).  With (b*d)*(c*d)=0 (under G) and
    // ring-rearrangement, prod_lr = ( apf0*apg0 ) + ( L * d ) where
    // L = ( apf0*c ) + ( b*apg0 ).  We finish the algebra under G.
    // Rearranged target: prod_lr = ( (apf0*apg0) + ( L*d ) ).
    //   sumA + sumB
    //   = ( (apf0*apg0)+((b*d)*apg0) ) + ( (apf0*(c*d))+(b*d)*(c*d) )
    // Under G, (b*d)*(c*d)=0, so sumB = (apf0*(c*d)) + 0 = apf0*(c*d).
    // Then apf0*(c*d)=(apf0*c)*d, (b*d)*apg0=(b*apg0)*d, and
    //  ((b*apg0)*d)+((apf0*c)*d) = ((b*apg0)+(apf0*c))*d ; reorder to
    //  ((apf0*c)+(b*apg0))*d = L*d.  And (apf0*apg0) is the constant.
    // We do this via the deduction combinators on the explicit chain.
    let g_prodlr_eq = {
        // ( G -> prod_lr = sumA + sumB )
        let g_df = imp_a1(&dist_full, &g_prod);
        // sumB = ( apf0*(c*d) ) + ( (b*d)*(c*d) ) ; rewrite 2nd to 0
        let g_sumB_collapse = {
            // ( G -> sumB = ( apf0*(c*d) + 0 ) )  via cong_r g_bdcd_0
            let c = imp_cong_r(&g_bdcd_0, &kf_cd, "+", "tpl", "eq-pl2");
            // ( apf0*(c*d) + 0 ) = apf0*(c*d)  [ax-add0]
            let kfcd_p0 = reg(&binop(&kf_cd, &zero, "+", "tpl"));
            let add0 = axeq("ax-add0", &[&kf_cd], &kfcd_p0, &kf_cd);
            imp_eqtr(&c, &imp_a1(&add0, &g_prod)) // ( G -> sumB = apf0*(c*d) )
        };
        // ( G -> ( sumA + sumB ) = ( sumA + apf0*(c*d) ) )
        let g_sAB = imp_cong_r(&g_sumB_collapse, &sumA, "+", "tpl", "eq-pl2");
        // chain: ( G -> prod_lr = ( sumA + apf0*(c*d) ) )
        let g_pl1 = imp_eqtr(&g_df, &g_sAB);
        // Now pure ring identity (hypothesis-free):
        //  ( sumA + apf0*(c*d) )
        //    = ( ( (apf0*apg0)+((b*d)*apg0) ) + (apf0*(c*d)) )
        //    = ( (apf0*apg0) + ( ((b*d)*apg0) + (apf0*(c*d)) ) )   [addass]
        //    = ( (apf0*apg0) + ( ((b*apg0)*d) + ((apf0*c)*d) ) )   [mulass*2]
        //    = ( (apf0*apg0) + ( ((b*apg0)+(apf0*c)) * d ) )       [~rdistr]
        //    = ( (apf0*apg0) + ( ((apf0*c)+(b*apg0)) * d ) )       [addcom]
        //    = ( (apf0*apg0) + ( L * d ) )
        let bapg0 = reg(&binop(&bb, &apg0, "*", "tmu"));
        let bapg0_d = reg(&binop(&bapg0, &dd, "*", "tmu"));
        let apf0c = reg(&binop(&apf0, &cc, "*", "tmu"));
        let apf0c_d = reg(&binop(&apf0c, &dd, "*", "tmu"));
        // (b*d)*apg0 = (b*apg0)*d  : (b*d)*apg0 = b*(d*apg0)=b*(apg0*d)=(b*apg0)*d
        let bd_kg2 = reg(&binop(&b_d, &apg0, "*", "tmu"));
        let d_kg = reg(&binop(&dd, &apg0, "*", "tmu"));
        let kg_d = reg(&binop(&apg0, &dd, "*", "tmu"));
        let e1 = axeq(
            "ax-mulass",
            &[&bb, &dd, &apg0],
            &bd_kg2,
            &reg(&binop(&bb, &d_kg, "*", "tmu")),
        ); // (b*d)*apg0 = b*(d*apg0)
        let e2 = cong_r(
            &axeq("ax-mulcom", &[&dd, &apg0], &d_kg, &kg_d),
            &bb,
            "*",
            "tmu",
            "eq-mu2",
        ); // b*(d*apg0) = b*(apg0*d)
        let e3 = eqsym(&axeq(
            "ax-mulass",
            &[&bb, &apg0, &dd],
            &bapg0_d,
            &reg(&binop(&bb, &kg_d, "*", "tmu")),
        )); // b*(apg0*d) = (b*apg0)*d
        let bdkg_eq = eqtr(&e1, &eqtr(&e2, &e3)); // (b*d)*apg0 = (b*apg0)*d
        // apf0*(c*d) = (apf0*c)*d   [~ax-mulass]
        let apf0cd_eq = eqsym(&axeq(
            "ax-mulass",
            &[&apf0, &cc, &dd],
            &apf0c_d,
            &reg(&binop(&apf0, &c_d, "*", "tmu")),
        )); // apf0*(c*d) = (apf0*c)*d
        // addass: ( (K)+(P) )+(Q) = (K)+( (P)+(Q) ), K=apf0*apg0,
        //   P=(b*d)*apg0, Q=apf0*(c*d)
        let kk = reg(&binop(&apf0, &apg0, "*", "tmu"));
        let pp = bd_kg.clone();
        let qq = kf_cd.clone();
        let kp = reg(&binop(&kk, &pp, "+", "tpl"));
        let kp_q = reg(&binop(&kp, &qq, "+", "tpl"));
        let p_q = reg(&binop(&pp, &qq, "+", "tpl"));
        let k_pq = reg(&binop(&kk, &p_q, "+", "tpl"));
        let assoc = axeq("ax-addass", &[&kk, &pp, &qq], &kp_q, &k_pq); // (K+P)+Q = K+(P+Q)
        // ( P + Q ) = ( (b*apg0)*d + (apf0*c)*d )  via bdkg_eq, apf0cd_eq
        let pq_rw = eqtr(
            &cong_l(&bdkg_eq, &qq, "+", "tpl", "eq-pl1"),
            &cong_r(&apf0cd_eq, &bapg0_d, "+", "tpl", "eq-pl2"),
        ); // (P+Q) = ((b*apg0)*d)+((apf0*c)*d)
        // ((b*apg0)*d)+((apf0*c)*d) = ((b*apg0)+(apf0*c))*d   [~rdistr]
        let bapg0_apf0c = reg(&binop(&bapg0, &apf0c, "+", "tpl"));
        let rd_pq = eqsym(&use_thm(
            "sdg-rdistr",
            &[("x", &bapg0), ("y", &apf0c), ("z", &dd)],
            &[],
            reg(&weq(
                &reg(&binop(&bapg0_apf0c, &dd, "*", "tmu")),
                &reg(&binop(&bapg0_d, &apf0c_d, "+", "tpl")),
            ))
            .toks,
        )); // ((b*apg0)*d)+((apf0*c)*d) = ((b*apg0)+(apf0*c))*d
        // ((b*apg0)+(apf0*c)) = ((apf0*c)+(b*apg0)) = L   [addcom]
        let l_w = reg(&binop(&apf0c, &bapg0, "+", "tpl")); // = L (apf0*c + b*apg0)
        let addc = axeq("ax-addcom", &[&bapg0, &apf0c], &bapg0_apf0c, &l_w);
        let addc_d = cong_l(&addc, &dd, "*", "tmu", "eq-mu1"); // ((b*apg0)+(apf0*c))*d = L*d
        // chain P+Q rewrites: (P+Q) = ... = L*d
        let pq_to_ld = eqtr(&pq_rw, &eqtr(&rd_pq, &addc_d)); // (P+Q) = L*d
        // K + (P+Q) = K + (L*d)   cong_r
        let k_pq_to_k_ld = cong_r(&pq_to_ld, &kk, "+", "tpl", "eq-pl2"); // K+(P+Q)=K+(L*d)
        // ( sumA + apf0*(c*d) ) == (K+P)+Q  (definally: sumA=K+P, qq=apf0*(c*d))
        // assoc : (K+P)+Q = K+(P+Q) ; then k_pq_to_k_ld : = K+(L*d)
        let ring_tail = eqtr(&assoc, &k_pq_to_k_ld); // (K+P)+Q = K+(L*d)
        // lift ring_tail under G and chain with g_pl1
        let g_ring_tail = imp_a1(&ring_tail, &g_prod);
        imp_eqtr(&g_pl1, &g_ring_tail) // ( G -> prod_lr = ( (apf0*apg0) + (L*d) ) )
    };
    // ( G -> apwd = prod_lr )  was g_prod_fg ; chain to ( apf0*apg0 + L*d )
    let kk_full = reg(&binop(&apf0, &apg0, "*", "tmu"));
    let kk_ld = reg(&binop(&kk_full, &leib_d, "+", "tpl")); // ( (apf0*apg0) + (L*d) )
    let g_apwd_klld = imp_eqtr(&g_prod_fg, &g_prodlr_eq); // ( G -> apwd = (apf0*apg0)+(L*d) )
    // ( apf0*apg0 ) = ( ap w 0 )   from gp_e0 : ( ap w 0 ) = ( apf0*apg0 ) symm
    let g_kk_w0 = imp_eqsym(gp_e0);
    let g_klld_w0ld = imp_cong_l(&g_kk_w0, &leib_d, "+", "tpl", "eq-pl1"); // (apf0*apg0+L*d)=(apw0+L*d)
    let g_apwd_w0ld = imp_eqtr(&g_apwd_klld, &g_klld_w0ld); // ( G -> apwd = (apw0+L*d) )
    // EW : ( G -> apwd = ( apw0 + a*d ) ) ; symm + chain
    let g_w0ad_apwd_p = imp_eqsym(gp_ew);
    let g_w0ad_w0ld = imp_eqtr(&g_w0ad_apwd_p, &g_apwd_w0ld); // (apw0+a*d)=(apw0+L*d)
    // sdg-addcan-imp[z:=apw0,u:=(a*d),v:=(L*d)]
    let ac_prod = use_thm(
        "sdg-addcan-imp",
        &[("z", &apw0), ("u", &s_d), ("v", &leib_d)],
        &[],
        reg(&wi(
            &reg(&weq(&w0_ad(&apw0, &s_d), &reg(&binop(&apw0, &leib_d, "+", "tpl")))),
            &reg(&weq(&s_d, &leib_d)),
        ))
        .toks,
    );
    let g_ac_prod = imp_a1(&ac_prod, &g_prod);
    let g_q_prod = imp_mp(&g_w0ad_w0ld, &g_ac_prod); // ( G -> ( a*d ) = ( L*d ) )

    // thread under ( D d ): build ( (D d) -> G ).  Here ( D d ) itself is
    // a conjunct of G, so the guard supplies it directly (closing the
    // df-D consumption honestly at the guard).
    let g_under_d_prod = build_guarded_conj(
        &dd_pred,
        &[&pimp_f, &pimp_g, &pimp_w, &pimp_pw, &pimp_e0, &{
            // ( ( D d ) -> ( D d ) ) : identity, so the guard's own
            // truth feeds the ( D d ) conjunct.
            let p = &dd_pred;
            let pp = reg(&wi(p, p));
            let p_pp = reg(&wi(p, &pp));
            let pp_p = reg(&wi(&pp, p));
            let p__pp_p = reg(&wi(p, &pp_p));
            let _ = reg(&wi(&p_pp, &pp));
            let a1 = apply("ax-1", &[p, p], &[], p_pp.toks.clone());
            let a2 = apply("ax-1", &[p, &pp], &[], p__pp_p.toks.clone());
            let a3 = apply("ax-2", &[p, &pp, p], &[], {
                let lhs = wi(p, &p__pp_p);
                let rhs = wi(&p_pp, &pp);
                wi(&lhs, &rhs).toks
            });
            mp(&a1, &mp(&a2, &a3))
        }],
        &[&ef, &eg, &ew, &epw_p, &e0_p, &dd_pred],
    );
    let g_prod_imp_d = imp_a1(&g_q_prod, &dd_pred);
    let dd_to_q_prod = imp_mp(&g_under_d_prod, &g_prod_imp_d); // ( (D d) -> a*d=L*d )
    let all_q_prod = gen(&dd_to_q_prod, "vd", "d");
    let a_eq_leib = reg(&weq(&sa, &leib));
    let mc_prod = use_thm(
        "ax-microcancel",
        &[("b", &sa), ("c", &leib), ("d", &dd)],
        &[],
        wi(&w_of(&all_q_prod.stmt), &a_eq_leib).toks,
    );
    let sdg_global_prod = mp(&all_q_prod, &mc_prod); // |- a = ( ( apf0*c ) + ( b*apg0 ) )

    // ---------------------------------------------------------------------
    //  GLOBAL CHAIN :  ( g ∘ f )' = ( g'∘f )·f'  globally.
    //
    //  Composing f's affine expansion INTO g's argument is Leibniz
    //  substitution under the function-application symbol `ap`.  The
    //  authored substrate (data/sdg.base.mm) instantiates equality's
    //  congruence ONLY for the ring ops + and * (eq-pl*/eq-mu*); it gives
    //  NO  x = y -> ( ap g x ) = ( ap g y ).  This is the SEQUEL §5e
    //  ap-congruence substrate gap (NOT a classical principle, NOT the
    //  pointwise→global seam).  Per the task we STOP at exactly this
    //  boundary: the single ap-Leibniz instance is surfaced as ONE
    //  loudly-labelled universal `$e` (chain.sub) — exactly as the
    //  pointwise sdg-calc-chain did — and NOTHING else is assumed; the
    //  globalization seam (uniqueness via ax-microcancel) is still fully
    //  threaded.  We do NOT add an ap-congruence axiom (that is the held
    //  W2-apcong follow-on's job).  Staying at the boundary IS the honest
    //  result.
    //
    //  $e :  KL rep for f (gives the affine inner expansion), the ap-
    //        Leibniz substitution step (chain.sub, the surfaced boundary),
    //        g's KL rep at the expanded point (chain.hg), w=g∘f pointwise
    //        (chain.hw / chain.h0), and w's KL rep (chain.hw'), all
    //        universal under ( D d ).
    //  conclusion:  a = ( c * b )    (global chain slope).
    // ---------------------------------------------------------------------
    let apg_apfd = reg(&ap(&gg, &apfd)); // ( ap g ( ap f d ) )
    let apg_kbd = reg(&ap(&gg, &k_bd)); // ( ap g ( apf0 + b*d ) )
    let apg_apf0 = reg(&ap(&gg, &apf0)); // ( ap g ( ap f 0 ) )
    let c_bd = reg(&binop(&cc, &b_d, "*", "tmu")); // ( c * ( b*d ) )
    let cb = reg(&binop(&cc, &bb, "*", "tmu")); // ( c * b )
    let cb_d = reg(&binop(&cb, &dd, "*", "tmu")); // ( ( c*b )*d )
    // chain.hw  : A. d ( ( D d ) -> ( ap w d ) = ( ap g ( ap f d ) ) )
    let ch_hw_body = reg(&weq(&apwd, &apg_apfd));
    // chain.sub : A. d ( ( D d ) -> ( ap g ( ap f d ) ) = ( ap g ( apf0+b*d ) ) )
    //   THE SURFACED ap-LEIBNIZ BOUNDARY (one labelled $e).
    let ch_sub_body = reg(&weq(&apg_apfd, &apg_kbd));
    // chain.hg  : A. d ( ( D d ) -> ( ap g ( apf0+b*d ) ) = ( ( ap g (apf0) ) + ( c*(b*d) ) ) )
    let kg0_cbd = reg(&binop(&apg_apf0, &c_bd, "+", "tpl"));
    let ch_hg_body = reg(&weq(&apg_kbd, &kg0_cbd));
    // chain.hw' : A. d ( ( D d ) -> ( ap w d ) = ( ( ap w 0 ) + ( a*d ) ) )
    // chain.h0  : ( ap w 0 ) = ( ap g ( ap f 0 ) )
    let ch_h0_body = reg(&weq(&apw0, &apg_apf0));
    // chain.hf  : A. d ( ( D d ) -> ( ap f d ) = ( apf0 + b*d ) )   (KL of f)

    let chain_hf = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ef)))).toks, rpn: t("chain.hf") };
    let chain_hw = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ch_hw_body)))).toks, rpn: t("chain.hw") };
    let chain_sub = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ch_sub_body)))).toks, rpn: t("chain.sub") };
    let chain_hg = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ch_hg_body)))).toks, rpn: t("chain.hg") };
    let chain_hwp = Pf { stmt: reg(&wal("vd", "d", &reg(&wi(&dd_pred, &ew)))).toks, rpn: t("chain.hwp") };
    let chain_h0 = Pf { stmt: ch_h0_body.toks.clone(), rpn: t("chain.h0") };

    let cimp_f = mk_spec(&chain_hf, &reg(&wi(&dd_pred, &ef)));
    let cimp_hw = mk_spec(&chain_hw, &reg(&wi(&dd_pred, &ch_hw_body)));
    let cimp_sub = mk_spec(&chain_sub, &reg(&wi(&dd_pred, &ch_sub_body)));
    let cimp_hg = mk_spec(&chain_hg, &reg(&wi(&dd_pred, &ch_hg_body)));
    let cimp_wp = mk_spec(&chain_hwp, &reg(&wi(&dd_pred, &ew)));
    let cimp_h0 = imp_a1(&chain_h0, &dd_pred);

    // G := conj of [ EF, HW, SUB, HG, EW, H0 ]
    let (g_chain, p_chain) = conj_and_projs(&[
        ef.clone(),
        ch_hw_body.clone(),
        ch_sub_body.clone(),
        ch_hg_body.clone(),
        ew.clone(),
        ch_h0_body.clone(),
    ]);
    let gc_ef = &p_chain[0]; // unused directly but kept for completeness
    let gc_hw = &p_chain[1];
    let gc_sub = &p_chain[2];
    let gc_hg = &p_chain[3];
    let gc_ew = &p_chain[4];
    let gc_h0 = &p_chain[5];
    let _ = gc_ef;
    // Under G:
    //  apwd = ( ap g ( ap f d ) )                          [HW]
    //       = ( ap g ( apf0 + b*d ) )                       [SUB — the surfaced ap-Leibniz]
    //       = ( ( ap g (apf0) ) + ( c*(b*d) ) )             [HG]
    //  ( ap g (apf0) ) = ( ap w 0 )                          [~H0]
    //  c*(b*d) = (c*b)*d                                     [~ax-mulass]
    //  => apwd = ( apw0 + ( (c*b)*d ) )
    //  EW: apwd = ( apw0 + ( a*d ) )
    //  => ( a*d ) = ( (c*b)*d )   [sdg-addcan-imp] => a = c*b
    let g_chain_1 = imp_eqtr(gc_hw, &imp_eqtr(gc_sub, gc_hg)); // ( G -> apwd = (apg(apf0))+(c*(b*d)) )
    // ( ap g (apf0) ) = ( ap w 0 )  via gc_h0 (H0: apw0 = ap g(apf0)) symm
    let g_kg0_w0 = imp_eqsym(gc_h0);
    let g_chain_2 = imp_cong_l(&g_kg0_w0, &c_bd, "+", "tpl", "eq-pl1"); // ((apg apf0)+c(bd)) = (apw0+c(bd))
    let g_chain_3 = imp_eqtr(&g_chain_1, &g_chain_2); // ( G -> apwd = ( apw0 + c*(b*d) ) )
    // c*(b*d) = (c*b)*d  [~ax-mulass]
    let cbd_eq_cb_d = eqsym(&axeq(
        "ax-mulass",
        &[&cc, &bb, &dd],
        &cb_d,
        &reg(&binop(&cc, &b_d, "*", "tmu")),
    )); // c*(b*d) = (c*b)*d
    let g_cbd = imp_a1(&cbd_eq_cb_d, &g_chain);
    let g_w0cbd_w0cbd = imp_cong_r(&g_cbd, &apw0, "+", "tpl", "eq-pl2"); // (apw0+c(bd))=(apw0+(c*b)*d)
    let g_chain_4 = imp_eqtr(&g_chain_3, &g_w0cbd_w0cbd); // ( G -> apwd = ( apw0 + (c*b)*d ) )
    // EW symm + chain
    let g_w0ad_apwd_c = imp_eqsym(gc_ew);
    let g_w0ad_w0cbd = imp_eqtr(&g_w0ad_apwd_c, &g_chain_4); // (apw0+a*d)=(apw0+(c*b)*d)
    let ac_chain = use_thm(
        "sdg-addcan-imp",
        &[("z", &apw0), ("u", &s_d), ("v", &cb_d)],
        &[],
        reg(&wi(
            &reg(&weq(&w0_ad(&apw0, &s_d), &reg(&binop(&apw0, &cb_d, "+", "tpl")))),
            &reg(&weq(&s_d, &cb_d)),
        ))
        .toks,
    );
    let g_ac_chain = imp_a1(&ac_chain, &g_chain);
    let g_q_chain = imp_mp(&g_w0ad_w0cbd, &g_ac_chain); // ( G -> ( a*d ) = ( (c*b)*d ) )

    let g_under_d_chain = build_guarded_conj(
        &dd_pred,
        &[&cimp_f, &cimp_hw, &cimp_sub, &cimp_hg, &cimp_wp, &cimp_h0],
        &[&ef, &ch_hw_body, &ch_sub_body, &ch_hg_body, &ew, &ch_h0_body],
    );
    let _ = &cimp_f; // cimp_f (KL of f) retained as $e for honest provenance
    let g_chain_imp_d = imp_a1(&g_q_chain, &dd_pred);
    let dd_to_q_chain = imp_mp(&g_under_d_chain, &g_chain_imp_d);
    let all_q_chain = gen(&dd_to_q_chain, "vd", "d");
    let a_eq_cb = reg(&weq(&sa, &cb));
    let mc_chain = use_thm(
        "ax-microcancel",
        &[("b", &sa), ("c", &cb), ("d", &dd)],
        &[],
        wi(&w_of(&all_q_chain.stmt), &a_eq_cb).toks,
    );
    let sdg_global_chain = mp(&all_q_chain, &mc_chain); // |- a = ( c * b )

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
        // ---- §5g  GLOBALIZED DIFFERENTIATION CALCULUS ------------------
        // Two ring-only helpers re-proved in the generator (calc corpus
        // is read-only; content re-derived, not imported).
        (
            "sdg-add4",
            "|- ( ( x + y ) + ( z + e ) ) = ( ( x + z ) + ( y + e ) )",
            vec![],
            &sdg_add4,
        ),
        (
            "sdg-rdistr",
            "|- ( ( x + y ) * z ) = ( ( x * z ) + ( y * z ) )",
            vec![],
            &sdg_rdistr,
        ),
        (
            // GLOBAL SUM: ( f + g )' = f' + g'  (derivative additive).
            // Uniqueness of w's global slope discharged via the §5b seam
            // fragment + ax-microcancel — NO linking $e.  Consumes
            // ax-microcancel; nothing classical.
            "sdg-global-sum",
            "|- a = ( b + c )",
            vec![
                ("sum.hf", "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )"),
                ("sum.hg", "|- A. d ( ( D d ) -> ( ap g d ) = ( ( ap g 0 ) + ( c * d ) ) )"),
                ("sum.hw", "|- A. d ( ( D d ) -> ( ap w d ) = ( ( ap w 0 ) + ( a * d ) ) )"),
                ("sum.hpw", "|- A. d ( ( D d ) -> ( ap w d ) = ( ( ap f d ) + ( ap g d ) ) )"),
                ("sum.h0", "|- ( ap w 0 ) = ( ( ap f 0 ) + ( ap g 0 ) )"),
            ],
            &sdg_global_sum,
        ),
        (
            // GLOBAL PRODUCT / LEIBNIZ: ( f · g )' = f(0)·g' + f'·g(0)
            // globally.  Genuinely consumes d·d=0 (df-D on the SHARED
            // GUARD ( D d ), a conjunct of G) + ax-mul0 to kill the
            // second-order term, then ax-microcancel for uniqueness.
            "sdg-global-prod",
            "|- a = ( ( ( ap f 0 ) * c ) + ( b * ( ap g 0 ) ) )",
            vec![
                ("prod.hf", "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )"),
                ("prod.hg", "|- A. d ( ( D d ) -> ( ap g d ) = ( ( ap g 0 ) + ( c * d ) ) )"),
                ("prod.hw", "|- A. d ( ( D d ) -> ( ap w d ) = ( ( ap w 0 ) + ( a * d ) ) )"),
                ("prod.hpw", "|- A. d ( ( D d ) -> ( ap w d ) = ( ( ap f d ) * ( ap g d ) ) )"),
                ("prod.h0", "|- ( ap w 0 ) = ( ( ap f 0 ) * ( ap g 0 ) )"),
            ],
            &sdg_global_prod,
        ),
        (
            // GLOBAL CHAIN: ( g ∘ f )' = ( g'∘f )·f' globally.  Hits the
            // SEQUEL §5e ap-congruence substrate gap: composing f's affine
            // expansion INTO g's argument is Leibniz under `ap`, and the
            // authored substrate gives congruence ONLY for + and *.  Per
            // the task we STOP at exactly that boundary: the single
            // ap-Leibniz instance is surfaced as ONE loudly-labelled
            // universal $e `chain.sub` (exactly as the pointwise
            // sdg-calc-chain did) — NO ap-congruence axiom added.  The
            // globalization seam (uniqueness via ax-microcancel) is still
            // fully threaded; nothing else is assumed.
            "sdg-global-chain",
            "|- a = ( c * b )",
            vec![
                ("chain.hf", "|- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) )"),
                ("chain.hw", "|- A. d ( ( D d ) -> ( ap w d ) = ( ap g ( ap f d ) ) )"),
                ("chain.sub", "|- A. d ( ( D d ) -> ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b * d ) ) ) )"),
                ("chain.hg", "|- A. d ( ( D d ) -> ( ap g ( ( ap f 0 ) + ( b * d ) ) ) = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) ) )"),
                ("chain.hwp", "|- A. d ( ( D d ) -> ( ap w d ) = ( ( ap w 0 ) + ( a * d ) ) )"),
                ("chain.h0", "|- ( ap w 0 ) = ( ap g ( ap f 0 ) )"),
            ],
            &sdg_global_chain,
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
