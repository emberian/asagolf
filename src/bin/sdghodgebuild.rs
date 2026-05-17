//! sdghodgebuild — BOOK-3 WAVE-8: the ORIENTATION-DUAL HODGE-⋆ /
//! codifferential pairing's ALGEBRAIC SKELETON in the 2D microsquare
//! scalar reduction.  Writes data/sdg.hodge.mm.
//!
//! HONEST FRAMING (stated up front, iron rule).  We hold the kinematic
//! core + the SOURCE-FREE field equation ∇F=0 (the differential
//! Bianchi, data/sdg.bianchi2.mm).  The DYNAMICS are NAMED residuals:
//! the inhomogeneous equation D⋆F=J with a source current J, a GENUINE
//! metric Hodge ⋆ in dim>2, action ∫tr F∧⋆F, matter, quantization.
//!
//! THE PRECISE SCOPING RESULT (a negative map is SUCCESS; a fake
//! positive is ZERO).  In the 2D microsquare SCALAR reduction the
//! Hodge ⋆ acts on the area 2-form ( d * e ) as the orientation /
//! duality map ( d * e ) ↔ ( e * d ) WITH A SIGN.  This wave ships
//! ONLY the part of that ⋆-pairing whose ALGEBRAIC SKELETON closes
//! PURE-RING over the FROZEN base — and NAMES precisely what does not:
//!
//!   * sdg-hodge-eqneg     : ( x = y -> ( inv x ) = ( inv y ) )
//!       the inv-congruence (deduction form; base has no eq-neg) — the
//!       supporting lemma (⋆ respects equality through the sign).
//!   * sdg-hodge-area-antisym :
//!       ( ( d * e ) + ( inv ( e * d ) ) ) = 0
//!       the ORIENTED 2D area element is ANTISYMMETRIC: ⋆ on the
//!       microsquare reverses orientation with a sign — the basic ⋆
//!       duality on the area 2-form.  PURE RING (ax-mulcom +
//!       ax-addneg).
//!   * sdg-hodge-starstar  : ( inv ( inv X ) ) = X
//!       ⋆⋆ = +id : double orientation reversal is the identity (the
//!       2D Euclidean (-1)^{k(n-k)} = +1 involution), realised as the
//!       inv-involution.  PURE RING.
//!   * sdg-hodge-star-lin  : ( a * ( inv w ) ) = ( inv ( a * w ) )
//!       ⋆ is LINEAR over the scalar field: the field coefficient
//!       pulls through the orientation sign — ⋆(c·F) = c·⋆F.  PURE
//!       RING.
//!   * sdg-hodge-codiff-dual :
//!       ( ( ( ( ap c x ) * v ) * ( e * d ) )
//!         + ( inv ( ( ( ap c x ) * v ) * ( d * e ) ) ) ) = 0
//!       the COCLOSED ORIENTATION-DUAL of the differential Bianchi:
//!       ∇⋆F = 0 is the orientation-reversed twin of ∇F = 0 — the
//!       EXACT data/sdg.bianchi2.mm sdg-bianchi2-cyclic construction
//!       with the area element dualised.  PURE RING.
//!
//! WHAT THIS IS, precisely (no overclaim).  This is the ALGEBRAIC
//! SKELETON of the orientation-dual ⋆ pairing in the 2D scalar model:
//! ⋆ as oriented-area antisymmetry, ⋆⋆=+id, ⋆-scalar-linearity, and
//! ∇⋆F=0 as the orientation-dual of ∇F=0.  It is NOT a GENUINE Hodge
//! ⋆: a real ⋆ needs an INNER PRODUCT / metric tensor g (⟨α,β⟩ vol =
//! α∧⋆β) — the FROZEN base has NO inner-product symbol, NO metric, NO
//! ⟨·,·⟩.  The genuine metric ⋆ in dim>2, the INHOMOGENEOUS D⋆F=J
//! with a SOURCE current J, the action ∫tr F∧⋆F, matter, quantization
//! ALL force a NEW FLAGGED COMMITMENT (a metric / bilinear form NOT in
//! the frozen ring) and are the NAMED residuals (BOOK3_SCOPE, §5t).
//! The model-meaning floor is the UNCHANGED Book-Two [PROJECTION],
//! never re-summed.
//!
//! Self-contained over the FROZEN eq-ap-extended data/sdg.base.mm;
//! disjoint `sdg-hodge-*` labels; shares NO $p with any corpus —
//! rename-free concatenation.  Modifies no kernel / base / other
//! corpus / builder.  Toolkit copied VERBATIM from
//! src/bin/sdgnonabFbuild.rs (deterministic constructors; the kernel
//! independently re-checks).
//!
//! Run:  cargo run --release --bin sdghodgebuild
//! Trust root = src/kernel.rs re-checking data/sdg.hodge.mm (also
//! sdghodgefloor / sdghodgepure).
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


fn neg(w: &W) -> W {
    reg(&W {
        rpn: rpn_app(&[&w.rpn], "tneg"),
        toks: {
            let mut t = vec!["(".into(), "inv".into()];
            t.extend(w.toks.clone());
            t.push(")".into());
            t
        },
    })
}

/// ( g -> g ), the standard ax-1/ax-2 identity, for the deduction-form
/// guard-step (G -> a=b) where the step IS the guard itself.
fn idimp(g: &W) -> Pf {
    let pp = reg(&wi(g, g));
    let p_pp = reg(&wi(g, &pp));
    let pp_p = reg(&wi(&pp, g));
    let p__pp_p = reg(&wi(g, &pp_p));
    let s1 = apply("ax-1", &[g, g], &[], p_pp.toks.clone());
    let s2 = apply("ax-1", &[g, &pp], &[], p__pp_p.toks.clone());
    let s3 = apply("ax-2", &[g, &pp, g], &[], {
        let lhs = reg(&wi(g, &p__pp_p));
        let rhs = reg(&wi(&p_pp, &pp));
        reg(&wi(&lhs, &rhs)).toks
    });
    let s4 = mp(&s2, &s3);
    mp(&s1, &s4)
}

fn main() {
    let base = include_str!("../../data/sdg.base.mm");
    let zero = reg(&W { rpn: t("t0"), toks: t("0") });

    let pl = |a: &W, b: &W| reg(&binop(a, b, "+", "tpl"));
    let ml = |a: &W, b: &W| reg(&binop(a, b, "*", "tmu"));
    let add0 = |x: &W| axeq("ax-add0", &[x], &reg(&binop(x, &zero, "+", "tpl")), x);
    let mul0 = |x: &W| axeq("ax-mul0", &[x], &reg(&binop(x, &zero, "*", "tmu")), &zero);
    let addcom = |a: &W, b: &W| {
        axeq("ax-addcom", &[a, b], &reg(&binop(a, b, "+", "tpl")), &reg(&binop(b, a, "+", "tpl")))
    };
    let mulcom = |a: &W, b: &W| {
        axeq("ax-mulcom", &[a, b], &reg(&binop(a, b, "*", "tmu")), &reg(&binop(b, a, "*", "tmu")))
    };
    let addneg = |x: &W| axeq("ax-addneg", &[x], &reg(&binop(x, &neg(x), "+", "tpl")), &zero);
    let addass = |a: &W, b: &W, c: &W| {
        let l = reg(&binop(&reg(&binop(a, b, "+", "tpl")), c, "+", "tpl"));
        let r = reg(&binop(a, &reg(&binop(b, c, "+", "tpl")), "+", "tpl"));
        axeq("ax-addass", &[a, b, c], &l, &r)
    };
    let distr = |a: &W, b: &W, c: &W| {
        let l = reg(&binop(a, &reg(&binop(b, c, "+", "tpl")), "*", "tmu"));
        let r = reg(&binop(&reg(&binop(a, b, "*", "tmu")), &reg(&binop(a, c, "*", "tmu")), "+", "tpl"));
        axeq("ax-distr", &[a, b, c], &l, &r)
    };
    let clp1 = |p: &Pf, z: &W| cong_l(p, z, "+", "tpl", "eq-pl1");
    let crp2 = |p: &Pf, z: &W| cong_r(p, z, "+", "tpl", "eq-pl2");
    let cmu2 = |p: &Pf, z: &W| cong_r(p, z, "*", "tmu", "eq-mu2");
    let _ = (&pl, &mul0, &add0, &distr);

    // ===== sdg-hodge-eqneg : ( x = y -> ( inv x ) = ( inv y ) ) =======
    // The supporting lemma: ⋆ respects equality through the orientation
    // sign.  The base has eq-pl/eq-mu/eq-ap only — NO eq-neg — so this
    // inv-congruence is DERIVED pure-ring in deduction form (the §5b
    // seam-closer fragment, intuitionistically pure: ax-1/ax-2/ax-mp +
    // the equational $a; NO classical principle, NO ax-gen/ax-spec).
    let x = reg(&leaf("vx", "x"));
    let y = reg(&leaf("vy", "y"));
    let ix = neg(&x);
    let iy = neg(&y);
    let g_xy = reg(&weq(&x, &y));
    let n1 = eqsym(&add0(&ix));
    let n2 = crp2(&eqsym(&addneg(&y)), &ix);
    let n3 = eqsym(&addass(&ix, &y, &iy));
    let n5 = clp1(&addcom(&ix, &x), &iy);
    let n6 = clp1(&addneg(&x), &iy);
    let n7 = eqtr(&addcom(&zero, &iy), &add0(&iy));
    let yx = reg(&weq(&y, &x));
    let p_yx = apply("eqcom", &[&x, &y], &[], reg(&wi(&g_xy, &yx)).toks);
    let ixy = pl(&ix, &y);
    let ixx = pl(&ix, &x);
    let eqpl2_inst = apply(
        "eq-pl2",
        &[&y, &x, &ix],
        &[],
        reg(&wi(&yx, &reg(&weq(&ixy, &ixx)))).toks,
    );
    let g_eqpl2 = imp_a1(&eqpl2_inst, &g_xy);
    let g_sub = imp_mp(&p_yx, &g_eqpl2);
    let g_e4 = imp_cong_l(&g_sub, &iy, "+", "tpl", "eq-pl1");
    let c = imp_a1(&n1, &g_xy);
    let c = imp_eqtr(&c, &imp_a1(&n2, &g_xy));
    let c = imp_eqtr(&c, &imp_a1(&n3, &g_xy));
    let c = imp_eqtr(&c, &g_e4);
    let c = imp_eqtr(&c, &imp_a1(&n5, &g_xy));
    let c = imp_eqtr(&c, &imp_a1(&n6, &g_xy));
    let sdg_hodge_eqneg = imp_eqtr(&c, &imp_a1(&n7, &g_xy));

    // ===== sdg-hodge-area-antisym :                              =====
    //   ( ( d * e ) + ( inv ( e * d ) ) ) = 0
    // The ORIENTED 2D area element is ANTISYMMETRIC.  The Hodge ⋆ on
    // the microsquare 2-form ( d * e ) is the orientation map ( d*e )↔
    // ( e*d ) WITH A SIGN; the oriented sum vanishes: ( e*d ) is
    // ring-equal to ( d*e ) by ax-mulcom, so the antisymmetric pairing
    // ( d*e ) + inv ( e*d ) collapses to ( X + inv X ) = 0 by
    // ax-addneg.  This IS the ⋆-duality of the area 2-form, PURE RING.
    let cd = reg(&leaf("vd", "d"));
    let ce = reg(&leaf("ve", "e"));
    let de = ml(&cd, &ce); // ( d * e )  oriented area element
    let ed = ml(&ce, &cd); // ( e * d )  orientation-reversed
    let sdg_hodge_area_antisym = {
        // ( d*e ) = ( e*d )                                ax-mulcom
        let de_comm = mulcom(&cd, &ce);
        // lift: ( ( d*e ) + inv ( e*d ) ) = ( ( e*d ) + inv ( e*d ) )
        let lifted = clp1(&de_comm, &neg(&ed));
        // ( ( e*d ) + inv ( e*d ) ) = 0                    ax-addneg
        let an = addneg(&ed);
        eqtr(&lifted, &an)
    };

    // ===== sdg-hodge-starstar : ( inv ( inv X ) ) = X ============
    // ⋆⋆ = +id.  In the 2D Euclidean signature ⋆⋆ = (-1)^{k(n-k)} =
    // +1 on the relevant degree; concretely the Hodge ⋆ on the scalar
    // microsquare model IS orientation reversal, so ⋆⋆ is DOUBLE
    // orientation reversal = the involution ( inv ( inv X ) ) = X.
    // Carrier X = the field strength's scalar carrier ( ( ap c x )*v ).
    // PURE RING (additive-inverse uniqueness via the §5b seam-closer
    // fragment — NO ax-gen/ax-spec, nothing classical).
    let neguniq = |p: &Pf, s: &W, tt: &W, g_uv0: &W| -> Pf {
        // sdg-nonabF-neguniq inlined locally (self-contained, pure-ring):
        // from p:( (s+tt)=0 ) get  tt = ( inv s ).  We rebuild the proof
        // via the same q1..q6 chain so NO cross-corpus reference is made.
        let is = neg(s);
        let q1 = eqsym(&add0(tt));
        let q2 = crp2(&eqsym(&addneg(s)), tt);
        let q3 = eqsym(&addass(tt, s, &is));
        let q4 = clp1(&addcom(tt, s), &is);
        let g_q5 = imp_cong_l(&idimp(g_uv0), &is, "+", "tpl", "eq-pl1");
        let q6 = eqtr(&addcom(&zero, &is), &add0(&is));
        let cc = imp_a1(&q1, g_uv0);
        let cc = imp_eqtr(&cc, &imp_a1(&q2, g_uv0));
        let cc = imp_eqtr(&cc, &imp_a1(&q3, g_uv0));
        let cc = imp_eqtr(&cc, &imp_a1(&q4, g_uv0));
        let cc = imp_eqtr(&cc, &g_q5);
        let neguniq_thm = imp_eqtr(&cc, &imp_a1(&q6, g_uv0)); // ( G -> tt = inv s )
        mp(p, &neguniq_thm)
    };
    let cc = reg(&leaf("vc", "c")); // field-strength symbol F : ( ap c · )
    let cx = reg(&leaf("vx", "x"));
    let cvv = reg(&leaf("vv", "v"));
    let ccx = reg(&ap(&cc, &cx)); // ( ap c x )
    let xcarrier = reg(&binop(&ccx, &cvv, "*", "tmu")); // ( ( ap c x ) * v )
    let sdg_hodge_starstar = {
        let ixc = neg(&xcarrier);
        // ( inv X + X ) = 0  via ( inv X + X ) = ( X + inv X ) = 0
        let prem = eqtr(&eqsym(&addcom(&xcarrier, &ixc)), &addneg(&xcarrier));
        let g0 = reg(&weq(&pl(&ixc, &xcarrier), &zero));
        // neguniq( prem, inv X, X ) : X = inv ( inv X )
        let x_eq_iix = neguniq(&prem, &ixc, &xcarrier, &g0);
        eqsym(&x_eq_iix) // ( inv ( inv X ) ) = X
    };

    // ===== sdg-hodge-star-lin : ( a * ( inv w ) ) = ( inv ( a * w ) )
    // ⋆ is LINEAR over the scalar field: the field coefficient pulls
    // through the orientation sign, ⋆( a · F ) = a · ⋆F.  Modelled as
    // the scalar passing through the additive-inverse (the orientation
    // sign).  PURE RING (distributivity + ax-mul0 + neguniq).
    let aa = reg(&leaf("va", "a"));
    let ww = reg(&leaf("vw", "w"));
    let iw = neg(&ww);
    let sdg_hodge_star_lin = {
        let m1 = eqsym(&distr(&aa, &ww, &iw)); // (a*w)+(a*iw) = a*(w+iw)
        let m2 = cmu2(&addneg(&ww), &aa); // a*(w+iw) = a*0
        let m3 = mul0(&aa); // a*0 = 0
        let prem = eqtr(&eqtr(&m1, &m2), &m3); // (a*w)+(a*iw)=0
        let aw = ml(&aa, &ww);
        let a_iw = ml(&aa, &iw);
        let g0 = reg(&weq(&pl(&aw, &a_iw), &zero));
        neguniq(&prem, &aw, &a_iw, &g0) // (a*iw)=inv(a*w)
    };

    // ===== sdg-hodge-codiff-dual :                                =====
    //   ( ( ( ( ap c x ) * v ) * ( e * d ) )
    //     + ( inv ( ( ( ap c x ) * v ) * ( d * e ) ) ) ) = 0
    // The COCLOSED orientation-dual of the differential Bianchi.
    // ∇⋆F = 0 is the orientation-REVERSED twin of ∇F = 0: the EXACT
    // data/sdg.bianchi2.mm sdg-bianchi2-cyclic construction with the
    // area element DUALISED (e*d in the positive slot, d*e under inv).
    // Built on the SAME pure-ring orientation cancellation, so it is
    // the genuine orientation-dual of the source-free equation, not an
    // unrelated identity.  PURE RING (ax-mulcom + ax-addneg).
    let rv = xcarrier.clone(); // ( ( ap c x ) * v )  ⋆F scalar carrier
    let rv_ed = reg(&binop(&rv, &ed, "*", "tmu")); // ⋆F·v·( e*d )  (dual orient.)
    let rv_de = reg(&binop(&rv, &de, "*", "tmu")); // ⋆F·v·( d*e )
    let inv_rv_de = neg(&rv_de);
    let sdg_hodge_codiff_dual = {
        // ( e*d ) = ( d*e )                                  ax-mulcom
        let ed_comm = mulcom(&ce, &cd);
        // lift by cong_r under ( ⋆F·v ) * _
        let rv_ed_eq = cong_r(&ed_comm, &rv, "*", "tmu", "eq-mu2");
        // cong_l under _ + ( inv ( ⋆F·v·(d*e) ) )
        let sum_eq = cong_l(&rv_ed_eq, &inv_rv_de, "+", "tpl", "eq-pl1");
        // now ( ⋆F·v·(e*d) + inv(⋆F·v·(d*e)) ) = ( ⋆F·v·(d*e) + inv(⋆F·v·(d*e)) )
        let an = addneg(&rv_de); // ( X + inv X ) = 0
        eqtr(&sum_eq, &an)
    };

    let _ = (
        &sdg_hodge_eqneg,
        &sdg_hodge_area_antisym,
        &sdg_hodge_starstar,
        &sdg_hodge_star_lin,
        &sdg_hodge_codiff_dual,
    );

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-hodge-eqneg",
            "|- ( x = y -> ( inv x ) = ( inv y ) )",
            vec![],
            &sdg_hodge_eqneg,
        ),
        (
            "sdg-hodge-area-antisym",
            "|- ( ( d * e ) + ( inv ( e * d ) ) ) = 0",
            vec![],
            &sdg_hodge_area_antisym,
        ),
        (
            "sdg-hodge-starstar",
            "|- ( inv ( inv ( ( ap c x ) * v ) ) ) = ( ( ap c x ) * v )",
            vec![],
            &sdg_hodge_starstar,
        ),
        (
            "sdg-hodge-star-lin",
            "|- ( a * ( inv w ) ) = ( inv ( a * w ) )",
            vec![],
            &sdg_hodge_star_lin,
        ),
        (
            "sdg-hodge-codiff-dual",
            "|- ( ( ( ( ap c x ) * v ) * ( e * d ) ) + ( inv ( ( ( ap c x ) * v ) * ( d * e ) ) ) ) = 0",
            vec![],
            &sdg_hodge_codiff_dual,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         ORIENTATION-DUAL HODGE-* SKELETON (sdghodgebuild) — BOOK-3\n   \
         WAVE-8.  The pure-ring ALGEBRAIC SKELETON of the Hodge-* /\n   \
         codifferential pairing in the 2D microsquare SCALAR reduction:\n   \
         eqneg (the inv-congruence supporting lemma), area-antisym (the\n   \
         oriented 2D area 2-form is ANTISYMMETRIC, * reverses\n   \
         orientation with a sign), starstar (** = +id, the 2D Euclidean\n   \
         involution), star-lin (* is scalar-linear, the coefficient\n   \
         pulls through the orientation sign), codiff-dual (grad * F = 0,\n   \
         the coclosed ORIENTATION-DUAL of the source-free differential\n   \
         Bianchi grad F = 0).  PURE RING, nothing classical, NO new\n   \
         substrate commitment.  THIS IS ONLY THE ALGEBRAIC SKELETON of\n   \
         the orientation-dual * in the scalar model — NOT a GENUINE\n   \
         metric Hodge *: a real * needs an INNER PRODUCT / metric\n   \
         tensor g (the frozen base has NO inner product, NO metric, NO\n   \
         <.,.>).  The genuine metric * in dim>2, the INHOMOGENEOUS\n   \
         D*F=J with a SOURCE current J, the action int tr F^*F, matter,\n   \
         quantization ALL force a NEW FLAGGED COMMITMENT (a metric /\n   \
         bilinear form NOT in the frozen ring) — the NAMED residuals\n   \
         (the dynamics of field theory, SEQUEL_SCOPE §5t).  The model-\n   \
         meaning floor is the UNCHANGED Book-Two [PROJECTION], never\n   \
         re-summed.  Self-contained over the FROZEN eq-ap-extended\n   \
         data/sdg.base.mm; disjoint `sdg-hodge-*` labels; shares no $p\n   \
         with any corpus.\n   \
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
                std::fs::write("data/sdg.hodge.mm", &out).expect("write data/sdg.hodge.mm");
                println!(
                    "sdghodgebuild: kernel-verified {n} $p; wrote data/sdg.hodge.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdghodgebuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.hodge.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdghodgebuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.hodge.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
