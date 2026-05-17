//! sdgnonabgenbuild — BOOK-3 WAVE-5: the GENERAL STRUCTURAL non-
//! commutation theorem, pure-ring over the FROZEN base, NO new
//! substrate commitment.  Writes data/sdg.nonabgen.mm.
//!
//! Wave 4 (data/sdg.nonab.mm) proved the CONCRETE canonical witness
//! A=[[0,1],[0,0]] B=[[0,0],[1,0]] commutator entrywise pure-ring.
//! This wave GENERALISES that to the structural statement of which the
//! witness was the instance: for two GENERAL 2x2 matrices over the
//! FROZEN commutative ring R, with symbolic ring entries
//!     A = [[ a , b ],[ c , _ ]]    B = [[ p , q ],[ r , _ ]]
//! (base $v entry vars: a b c for A's used entries; p:=x q:=y r:=z for
//! B's, all distinct, all from the base's declared $v), the matrix
//! products' (1,1) entries are
//!     ( A . B )_11 = ( ( a * x ) + ( b * z ) )
//!     ( B . A )_11 = ( ( x * a ) + ( y * c ) )
//! and the GENERAL non-commutation theorem is that the commutator (1,1)
//! entry equals the off-diagonal MIXING term:
//!     ( (A.B)_11 + inv (B.A)_11 )
//!         reduces PURE-RING to  ( ( b * z ) + ( inv ( y * c ) ) )
//! the a*x / x*a symmetric (commuting) parts cancelling EXACTLY by
//! ax-mulcom + ax-addneg.  This is the GENERAL statement; wave-4's
//! concrete [A,B]=[[1,0],[0,inv 1]] is its a=0,b=1,c=0,p=0,q=0,r=1
//! (with the 2,2 dual) instance.
//!
//! THE 1!=0 DISTINCTION (kept EXPLICIT, never blurred).  The GENERAL
//! theorem here needs NO 1!=0 to STATE or PROVE: it is a pure-ring
//! IDENTITY, true in EVERY (even trivial) commutative ring.  1!=0 was
//! ONLY the wave-4 concrete witness's NON-VACUITY (that its particular
//! [A,B] is genuinely non-zero) — that named cross-book residual
//! (= Book One's irreducible residue) is UNCHANGED and UNTOUCHED here;
//! it is NOT a hypothesis of the general theorem.  The general
//! structural source of non-commutativity is the off-diagonal mixing
//! term, intrinsic, requiring nothing beyond the frozen commutative
//! ring.  We do NOT claim the general theorem needs 1!=0.
//!
//!   * sdg-nonabgen-eqneg : additive-inverse congruence
//!       ( x = y -> ( inv x ) = ( inv y ) ), DERIVED pure-ring
//!       (deduction form) — a clean general lemma (base has no eq-neg).
//!   * sdg-nonabgen-invadd : ( inv ( u + v ) ) = ( ( inv u ) + ( inv v ) )
//!       — the general inverse-of-sum identity, pure-ring (true in any
//!       commutative ring; no 1!=0).
//!   * sdg-nonabgen-symvanish : ( ( a * x ) + ( inv ( x * a ) ) ) = 0
//!       — the PRECISE pure-ring core: the symmetric / commuting part
//!       of the commutator (1,1) entry vanishes (ax-mulcom + ax-addneg).
//!   * sdg-nonabgen-addcancel : ( ( u + v ) + ( inv u ) ) = v
//!       — a clean general additive-cancellation lemma.
//!   * sdg-nonabgen-mixcancel : the HEADLINE general theorem,
//!       ( ( ( a * x ) + ( b * z ) ) + ( inv ( ( x * a ) + ( y * c ) ) ) )
//!         = ( ( b * z ) + ( inv ( y * c ) ) )
//!       — the commutator (1,1) entry reduces pure-ring to the off-
//!       diagonal mixing term; the general structural non-commutation.
//!
//! HONEST SCOPE.  What CLOSES pure-ring, kernel-verified, over the
//! FROZEN base, NO new substrate commitment, nothing classical: the
//! GENERAL 2x2 (1,1)-entry non-commutation identity and its supporting
//! general algebra (inverse-of-sum, symmetric-part vanishing, additive
//! cancellation, inv congruence).  What STAYS the NAMED residual: the
//! full general-rank / n x n Yang-Mills tower (general matrix size,
//! full F=dA+A^A assembly, differential Bianchi / gauge covariance) —
//! this wave closes the (1,1) entry at general 2x2 symbolic, NOT the
//! whole tower; and the model-meaning floor is the UNCHANGED Book-Two
//! [PROJECTION], never re-summed.  Wave-4's 1!=0 cross-book spine is
//! the residual of the CONCRETE witness's non-vacuity, unchanged and
//! NOT a hypothesis here — kept distinct, not papered.
//!
//! Composition / zero-conflict.  Self-contained over the IDENTICAL
//! FROZEN eq-ap-extended data/sdg.base.mm; disjoint `sdg-nonabgen-*`
//! labels; shares NO $p with any corpus — rename-free concatenation.
//! Modifies no kernel / base / other corpus / builder / ledger.
//!
//! Run:  cargo run --release --bin sdgnonabgenbuild
//! Trust root = src/kernel.rs re-checking the emitted file (also
//! sdgnonabgenfloor / sdgnonabgenpure).  Toolkit copied VERBATIM from
//! src/bin/sdgnonabbuild.rs lines 68-710 (deterministic constructors;
//! the kernel re-checks every step).
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

fn main() {
    let base = include_str!("../../data/sdg.base.mm");
    let zero = reg(&W { rpn: t("t0"), toks: t("0") });

    // ring-axiom instance helpers (all PURE RING over the frozen base)
    let pl = |a: &W, b: &W| reg(&binop(a, b, "+", "tpl"));
    let ml = |a: &W, b: &W| reg(&binop(a, b, "*", "tmu"));
    let add0 = |x: &W| axeq("ax-add0", &[x], &reg(&binop(x, &zero, "+", "tpl")), x);
    let addcom = |a: &W, b: &W| {
        axeq("ax-addcom", &[a, b], &reg(&binop(a, b, "+", "tpl")), &reg(&binop(b, a, "+", "tpl")))
    };
    let addneg = |x: &W| axeq("ax-addneg", &[x], &reg(&binop(x, &neg(x), "+", "tpl")), &zero);
    let addass = |a: &W, b: &W, c: &W| {
        let l = reg(&binop(&reg(&binop(a, b, "+", "tpl")), c, "+", "tpl"));
        let r = reg(&binop(a, &reg(&binop(b, c, "+", "tpl")), "+", "tpl"));
        axeq("ax-addass", &[a, b, c], &l, &r)
    };
    let mulcom = |a: &W, b: &W| {
        axeq("ax-mulcom", &[a, b], &reg(&binop(a, b, "*", "tmu")), &reg(&binop(b, a, "*", "tmu")))
    };
    let clp1 = |p: &Pf, z: &W| cong_l(p, z, "+", "tpl", "eq-pl1"); // (a+z)=(b+z)
    let crp2 = |p: &Pf, z: &W| cong_r(p, z, "+", "tpl", "eq-pl2"); // (z+a)=(z+b)

    // entry variables (all from the FROZEN base $v).  A = [[a,b],[c,_]] ;
    // B = [[p,q],[r,_]] with p:=x, q:=y, r:=z (distinct, base-declared).
    let a = leaf("va", "a");
    let b = leaf("vb", "b");
    let c = leaf("vc", "c");
    let x = leaf("vx", "x"); // = p (B_11)
    let y = leaf("vy", "y"); // = q (B_12)
    let z = leaf("vz", "z"); // = r (B_21)

    // ( inv 0 ) = 0   (pure ring; needed by negcong path / kept available)
    let inv0 = neg(&zero);
    let an0 = addneg(&zero); // ( 0 + ( inv 0 ) ) = 0
    let t1 = addcom(&zero, &inv0); // ( 0 + inv 0 ) = ( inv 0 + 0 )
    let t2 = add0(&inv0); // ( inv 0 + 0 ) = ( inv 0 )
    let z_i0_eq_i0 = eqtr(&t1, &t2); // ( 0 + inv 0 ) = ( inv 0 )
    let _pf_inv0 = eqtr(&eqsym(&z_i0_eq_i0), &an0); // ( inv 0 ) = 0

    // =====================================================================
    //  sdg-nonabgen-eqneg : ( x = y -> ( inv x ) = ( inv y ) ) — the inv
    //  congruence, DERIVED pure-ring in deduction form (clean general
    //  lemma; base has eq-pl/eq-mu/eq-ap only, NO eq-neg).  Statement is
    //  a standalone schema over x,y (independent of the entry naming).
    // ---------------------------------------------------------------------
    let ex = leaf("vx", "x");
    let ey = leaf("vy", "y");
    let eix = neg(&ex);
    let eiy = neg(&ey);
    let g_xy = reg(&weq(&ex, &ey)); // G := x = y

    let e1 = eqsym(&add0(&eix)); // inv x = ( inv x + 0 )
    let e2 = crp2(&eqsym(&addneg(&ey)), &eix); // ( inv x + 0 ) = ( inv x + ( y + inv y ) )
    let e3 = eqsym(&addass(&eix, &ey, &eiy)); // = ( ( inv x + y ) + inv y )
    let e5 = clp1(&addcom(&eix, &ex), &eiy); // ((inv x+x)+iy) = ((x+inv x)+iy)
    let e6 = clp1(&addneg(&ex), &eiy); // ((x+inv x)+iy) = (0+iy)
    let e7 = eqtr(&addcom(&zero, &eiy), &add0(&eiy)); // (0+iy) = inv y

    let yx = reg(&weq(&ey, &ex));
    let p_yx = apply("eqcom", &[&ex, &ey], &[], reg(&wi(&g_xy, &yx)).toks); // (G -> y=x)
    let ixy = pl(&eix, &ey);
    let ixx = pl(&eix, &ex);
    let eqpl2_inst = apply(
        "eq-pl2",
        &[&ey, &ex, &eix],
        &[],
        reg(&wi(&yx, &reg(&weq(&ixy, &ixx)))).toks,
    ); // ( y=x -> ( inv x + y )=( inv x + x ) )
    let g_eqpl2 = imp_a1(&eqpl2_inst, &g_xy);
    let g_sub = imp_mp(&p_yx, &g_eqpl2); // (G -> (inv x+y)=(inv x+x))
    let g_e4 = imp_cong_l(&g_sub, &eiy, "+", "tpl", "eq-pl1");

    let ch = imp_a1(&e1, &g_xy);
    let ch = imp_eqtr(&ch, &imp_a1(&e2, &g_xy));
    let ch = imp_eqtr(&ch, &imp_a1(&e3, &g_xy));
    let ch = imp_eqtr(&ch, &g_e4);
    let ch = imp_eqtr(&ch, &imp_a1(&e5, &g_xy));
    let ch = imp_eqtr(&ch, &imp_a1(&e6, &g_xy));
    let sdg_nonabgen_eqneg = imp_eqtr(&ch, &imp_a1(&e7, &g_xy)); // |- ( x=y -> inv x = inv y )

    // =====================================================================
    //  sdg-nonabgen-invadd : ( inv ( u + v ) ) = ( ( inv u ) + ( inv v ) )
    //  — the general inverse-of-sum identity, PURE RING (abelian-group
    //  algebra; true in EVERY commutative ring; NO 1!=0).
    // ---------------------------------------------------------------------
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let iu = neg(&u);
    let iv = neg(&v);
    let s_uv = pl(&u, &v); // S = ( u + v )
    let is_uv = neg(&s_uv); // inv S
    let iuiv = pl(&iu, &iv); // ( inv u + inv v )

    // First: ( ( inv u + inv v ) + ( u + v ) ) = 0
    // ((iu+iv)+(u+v)) = (((iu+iv)+u)+v)   [eqsym addass(iu+iv,u,v)]
    let k0 = eqsym(&addass(&iuiv, &u, &v));
    // (((iu+iv)+u)+v) = ((iu+(iv+u))+v)   [clp1 addass(iu,iv,u)]
    let k1 = clp1(&addass(&iu, &iv, &u), &v);
    // ((iu+(iv+u))+v) = ((iu+(u+iv))+v)   [clp1 (crp2 addcom(iv,u) iu)]
    let k2 = clp1(&crp2(&addcom(&iv, &u), &iu), &v);
    // ((iu+(u+iv))+v) = (((iu+u)+iv)+v)   [clp1 (eqsym addass(iu,u,iv))]
    let k3 = clp1(&eqsym(&addass(&iu, &u, &iv)), &v);
    // (iu+u)=0  : addcom(iu,u) ; addneg(u)
    let iu_u_0 = eqtr(&addcom(&iu, &u), &addneg(&u));
    // (((iu+u)+iv)+v) = (((0)+iv)+v)      [clp1 (clp1 iu_u_0 iv)]
    let k4 = clp1(&clp1(&iu_u_0, &iv), &v);
    // ((0+iv)+v) = (iv+v)                 [clp1 ( (0+iv)=iv )]
    let z_iv = eqtr(&addcom(&zero, &iv), &add0(&iv)); // (0+iv)=iv
    let k5 = clp1(&z_iv, &v);
    // (iv+v)=0
    let iv_v_0 = eqtr(&addcom(&iv, &v), &addneg(&v));
    // chain: ((iu+iv)+(u+v)) = 0
    let sum_zero = eqtr(
        &eqtr(&eqtr(&eqtr(&eqtr(&eqtr(&k0, &k1), &k2), &k3), &k4), &k5),
        &iv_v_0,
    );

    // Now: (iu+iv) = (iu+iv)+0 = (iu+iv)+(S+iS) = ((iu+iv)+S)+iS
    //              = ((iu+iv)+(u+v))+iS = (0+iS) = iS
    let m0 = eqsym(&add0(&iuiv)); // (iu+iv) = ((iu+iv)+0)
    let s_is = pl(&s_uv, &is_uv); // ( S + inv S )
    let m1 = crp2(&eqsym(&addneg(&s_uv)), &iuiv); // ((iu+iv)+0)=((iu+iv)+(S+iS))
    let m2 = eqsym(&addass(&iuiv, &s_uv, &is_uv)); // =(((iu+iv)+S)+iS)
    let _ = &s_is;
    let m3 = clp1(&sum_zero, &is_uv); // (((iu+iv)+(u+v))+iS)=(0+iS)
    let z_is = eqtr(&addcom(&zero, &is_uv), &add0(&is_uv)); // (0+iS)=iS
    let iuiv_eq_is = eqtr(&eqtr(&eqtr(&eqtr(&m0, &m1), &m2), &m3), &z_is); // (iu+iv)=iS
    let sdg_nonabgen_invadd = eqsym(&iuiv_eq_is); // ( inv (u+v) ) = ( inv u + inv v )

    // =====================================================================
    //  sdg-nonabgen-symvanish : ( ( a * x ) + ( inv ( x * a ) ) ) = 0
    //  — the symmetric / commuting part of the commutator (1,1) entry
    //  vanishes (ax-mulcom + ax-addneg).  The PRECISE pure-ring core.
    // ---------------------------------------------------------------------
    let ax_ = ml(&a, &x); // ( a * x )
    let xa_ = ml(&x, &a); // ( x * a )
    let inv_xa = neg(&xa_);
    // (a*x)+inv(x*a) = (x*a)+inv(x*a)   [clp1 mulcom(a,x)]
    let sv1 = clp1(&mulcom(&a, &x), &inv_xa);
    // (x*a)+inv(x*a) = 0                [addneg(x*a)]
    let sv2 = addneg(&xa_);
    let sdg_nonabgen_symvanish = eqtr(&sv1, &sv2);

    // =====================================================================
    //  sdg-nonabgen-addcancel : ( ( u + v ) + ( inv u ) ) = v  — a clean
    //  general additive-cancellation lemma (pure ring).
    // ---------------------------------------------------------------------
    let vu = pl(&v, &u);
    // (u+v)+iu = (v+u)+iu     [clp1 addcom(u,v)]
    let ac1 = clp1(&addcom(&u, &v), &iu);
    // (v+u)+iu = v+(u+iu)     [addass(v,u,iu)]
    let ac2 = addass(&v, &u, &iu);
    // v+(u+iu) = v+0          [crp2 addneg(u) v]
    let ac3 = crp2(&addneg(&u), &v);
    // v+0 = v
    let ac4 = add0(&v);
    let _ = &vu;
    let sdg_nonabgen_addcancel =
        eqtr(&eqtr(&eqtr(&ac1, &ac2), &ac3), &ac4);

    // =====================================================================
    //  sdg-nonabgen-mixcancel : THE HEADLINE general theorem.
    //   ( ( ( a*x ) + ( b*z ) ) + ( inv ( ( x*a ) + ( y*c ) ) ) )
    //       = ( ( b*z ) + ( inv ( y*c ) ) )
    //  ( A.B )_11 + inv ( B.A )_11  reduces pure-ring to the off-diagonal
    //  MIXING term; the a*x / x*a symmetric parts cancel by symvanish.
    // ---------------------------------------------------------------------
    let p_ = ml(&a, &x); // P  = (A.B)_11 first summand = ( a * x )
    let q_ = ml(&b, &z); // Q  = (A.B)_11 second summand = ( b * z )
    let pp = ml(&x, &a); // P' = (B.A)_11 first summand = ( x * a )
    let rr = ml(&y, &c); // R  = (B.A)_11 second summand = ( y * c )
    let ip = neg(&pp); // inv P'
    let ir = neg(&rr); // inv R
    let pq = pl(&p_, &q_); // ( P + Q ) = (A.B)_11
    let ppr = pl(&pp, &rr); // ( P' + R ) = (B.A)_11
    let inv_ppr = neg(&ppr); // inv (B.A)_11
    let lhs = pl(&pq, &inv_ppr); // the commutator (1,1) entry
    let _ = &lhs;

    // step1: inv(P'+R) = inv P' + inv R   [invadd at u:=P', v:=R]
    let invadd_inst = use_thm(
        "sdg-nonabgen-invadd",
        &[("u", &pp), ("v", &rr)],
        &[],
        reg(&weq(&inv_ppr, &reg(&pl(&ip, &ir)))).toks,
    );
    let ipir = pl(&ip, &ir); // ( inv P' + inv R )
    // ((P+Q)+inv(P'+R)) = ((P+Q)+(iP'+iR))   [crp2 invadd_inst (P+Q)]
    let s1 = crp2(&invadd_inst, &pq);
    // ((P+Q)+(iP'+iR)) = (P+(Q+(iP'+iR)))    [addass(P,Q,(iP'+iR))]
    let s2 = addass(&p_, &q_, &ipir);
    // (Q+(iP'+iR)) = ((Q+iP')+iR)            [eqsym addass(Q,iP',iR)]; under +P (crp2)
    let s3 = crp2(&eqsym(&addass(&q_, &ip, &ir)), &p_);
    // ((Q+iP')+iR) = ((iP'+Q)+iR)            [clp1 addcom(Q,iP') iR]; under +P
    let s4 = crp2(&clp1(&addcom(&q_, &ip), &ir), &p_);
    // ((iP'+Q)+iR) = (iP'+(Q+iR))            [addass(iP',Q,iR)]; under +P
    let s5 = crp2(&addass(&ip, &q_, &ir), &p_);
    // (P+(iP'+(Q+iR))) = ((P+iP')+(Q+iR))    [eqsym addass(P,iP',(Q+iR))]
    let q_ir = pl(&q_, &ir);
    let s6 = eqsym(&addass(&p_, &ip, &q_ir));
    // (P+iP') = 0                            [symvanish at a:=a, x:=x] -> ((a*x)+inv(x*a))=0
    let symv_inst = use_thm(
        "sdg-nonabgen-symvanish",
        &[("a", &a), ("x", &x)],
        &[],
        reg(&weq(&reg(&pl(&p_, &ip)), &zero)).toks,
    );
    // ((P+iP')+(Q+iR)) = (0+(Q+iR))          [clp1 symv_inst (Q+iR)]
    let s7 = clp1(&symv_inst, &q_ir);
    // (0+(Q+iR)) = (Q+iR)
    let s8 = eqtr(&addcom(&zero, &q_ir), &add0(&q_ir));

    // chain s1..s8 by transitivity: lands exactly on ( Q + iR ) =
    // ( ( b * z ) + ( inv ( y * c ) ) ).
    let sdg_nonabgen_mixcancel = eqtr(
        &eqtr(
            &eqtr(&eqtr(&eqtr(&eqtr(&eqtr(&s1, &s2), &s3), &s4), &s5), &s6),
            &s7,
        ),
        &s8,
    );

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-nonabgen-eqneg",
            "|- ( x = y -> ( inv x ) = ( inv y ) )",
            vec![],
            &sdg_nonabgen_eqneg,
        ),
        (
            "sdg-nonabgen-invadd",
            "|- ( inv ( u + v ) ) = ( ( inv u ) + ( inv v ) )",
            vec![],
            &sdg_nonabgen_invadd,
        ),
        (
            "sdg-nonabgen-symvanish",
            "|- ( ( a * x ) + ( inv ( x * a ) ) ) = 0",
            vec![],
            &sdg_nonabgen_symvanish,
        ),
        (
            "sdg-nonabgen-addcancel",
            "|- ( ( u + v ) + ( inv u ) ) = v",
            vec![],
            &sdg_nonabgen_addcancel,
        ),
        (
            "sdg-nonabgen-mixcancel",
            "|- ( ( ( a * x ) + ( b * z ) ) + ( inv ( ( x * a ) + ( y * c ) ) ) ) = ( ( b * z ) + ( inv ( y * c ) ) )",
            vec![],
            &sdg_nonabgen_mixcancel,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         GENERAL STRUCTURAL NON-COMMUTATION over the FROZEN base\n   \
         (sdgnonabgenbuild) — BOOK-3 WAVE-5, NO new substrate\n   \
         commitment.  General 2x2 matrices over the commutative ring R\n   \
         with symbolic entries A=[[a,b],[c,_]] B=[[p,q],[r,_]] (p:=x,\n   \
         q:=y, r:=z, all base $v).  (A.B)_11=((a*x)+(b*z)),\n   \
         (B.A)_11=((x*a)+(y*c)); the GENERAL non-commutation theorem\n   \
         sdg-nonabgen-mixcancel: ( (A.B)_11 + inv (B.A)_11 ) reduces\n   \
         PURE-RING to ( (b*z) + inv (y*c) ) — the a*x/x*a symmetric\n   \
         (commuting) parts cancel EXACTLY by ax-mulcom+ax-addneg\n   \
         (sdg-nonabgen-symvanish).  This is the GENERAL statement of\n   \
         which wave-4's concrete witness was the instance.  1!=0 is\n   \
         NOT needed to STATE or PROVE the general theorem (a pure-ring\n   \
         identity, true in EVERY commutative ring); 1!=0 was ONLY the\n   \
         wave-4 CONCRETE witness's non-vacuity (the cross-book residual,\n   \
         unchanged, NOT a hypothesis here).  Supporting general lemmas:\n   \
         sdg-nonabgen-eqneg (inv congruence, derived deduction-form),\n   \
         sdg-nonabgen-invadd (inverse-of-sum), sdg-nonabgen-addcancel\n   \
         (additive cancellation).  NO new axiom; NO seam; NO eq-ap;\n   \
         nothing classical; model floor the UNCHANGED Book-Two\n   \
         [PROJECTION], never re-summed.  NAMED residual: the full\n   \
         general-rank / n x n Yang-Mills tower.  Self-contained over\n   \
         the FROZEN eq-ap-extended data/sdg.base.mm; disjoint\n   \
         `sdg-nonabgen-*` labels; shares no $p with any corpus.\n   \
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
                std::fs::write("data/sdg.nonabgen.mm", &out)
                    .expect("write data/sdg.nonabgen.mm");
                println!(
                    "sdgnonabgenbuild: kernel-verified {n} $p; wrote data/sdg.nonabgen.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgnonabgenbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.nonabgen.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgnonabgenbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.nonabgen.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
