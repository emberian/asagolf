//! sdgjacobibuild — BOOK-3 WAVE-8: the GENUINE NON-VACUOUS non-abelian
//! Jacobi identity at a CONCRETE 2x2 witness, ENTRYWISE PURE RING over
//! the FROZEN commutative base.  Writes data/sdg.jacobi.mm.
//!
//! HONEST FRAMING (iron rule, stated up front).  Over a COMMUTATIVE
//! base a *symbolic* bracket [x,y]=(x*y)+inv(y*x) is identically 0, so a
//! symbolic Jacobi is VACUOUS (0+0+0=0) and was deliberately NOT shipped
//! by wave-7 (data/sdg.nonabF.mm shipped only the bracket ALGEBRA).
//! THIS wave ships the genuine article one level up: a CONCRETE sl2-style
//! triple of 2x2 matrices over the frozen ring whose PAIRWISE commutators
//! are genuinely NON-ZERO matrices, yet whose cyclic nested Jacobi sum
//! vanishes ENTRYWISE by pure ring algebra.  The witness (wave-4
//! concrete-witness discipline, one level up):
//!     H = [[1,0],[0,(inv 1)]]   E = [[0,1],[0,0]]   Fm = [[0,0],[1,0]]
//! (here taken as A=[[0,1],[0,0]], B=[[0,0],[1,0]], C=[[1,0],[0,0]] —
//! the same sl2 root/idempotent skeleton).  Matrix product entrywise
//! ( X.Y )_ij = ( ( X_i1 * Y_1j ) + ( X_i2 * Y_2j ) ); commutator entry
//! [X,Y]_ij = ( ( X.Y )_ij + ( inv ( Y.X )_ij ) ).  Computed entrywise
//! pure-ring over the FROZEN base:
//!     [A,B]=[[1,0],[0,(inv 1)]]  [B,C]=[[0,0],[1,0]]  [C,A]=[[0,1],[0,0]]
//! — all genuinely NON-ZERO matrices (NOT commutator-collapse).  The
//! nested brackets [A,[B,C]]=[[1,0],[0,inv 1]], [B,[C,A]]=[[inv 1,0],
//! [0,1]], [C,[A,B]]=0 are themselves non-zero matrices, yet the cyclic
//! sum  [A,[B,C]]+[B,[C,A]]+[C,[A,B]]  is the ZERO matrix ENTRYWISE.
//! That is the genuine non-abelian structural Jacobi, non-vacuous.
//!
//!   * sdg-jacobi-eqneg : ( x = y -> ( inv x ) = ( inv y ) ), the inv
//!       congruence, DERIVED pure-ring (deduction form) — base has no
//!       eq-neg (copied verbatim from sdg-nonab-eqneg, relabelled).
//!   * sdg-jacobi-j11 / j12 / j21 / j22 : the four entries of the
//!       cyclic Jacobi sum for the concrete witness, each = 0, ENTRYWISE
//!       PURE RING.  The LHS is the LITERAL nested ring term obtained by
//!       entrywise matrix multiply/commutator/add of the concrete
//!       witnesses; proven 0 by a recursive ring evaluator (the wave-4
//!       discipline: every step a frozen ring-axiom congruence).
//!
//! HONEST SCOPE.  What CLOSES: the genuine non-vacuous non-abelian
//! Jacobi at a concrete 2x2 witness, ENTRYWISE PURE RING, kernel-
//! verified, over the FROZEN base — NO new substrate commitment, nothing
//! classical, NO seam, NO eq-ap.  The NAMED residuals (never papered):
//! (a) the non-vacuity itself — that [A,B],[B,C],[C,A] are genuinely
//! NON-ZERO matrices — is EXACTLY 1!=0, the GROUNDED cross-book spine
//! (Book One's irreducible residue, data/sdg.spine.mm); (b) general
//! matrix rank / arbitrary Lie algebra (this is the Book-One-style
//! concrete separation, the proof of concept, not the whole tower);
//! (c) the full DF=0 field-equation assembly and dynamics (action /
//! Hodge / matter / quantization).  Model-meaning floor: the UNCHANGED
//! Book-Two [PROJECTION], never re-summed.
//!
//! Composition / zero-conflict.  Self-contained over the IDENTICAL
//! FROZEN eq-ap-extended data/sdg.base.mm; disjoint `sdg-jacobi-*`
//! labels; shares NO $p with any corpus — rename-free concatenation.
//! Modifies no kernel / base / other corpus / builder.
//!
//! Run:  cargo run --release --bin sdgjacobibuild
//! Trust root = src/kernel.rs re-checking the emitted file (also
//! sdgjacobifloor / sdgjacobipure).  Toolkit copied VERBATIM from
//! src/bin/sdgnonabbuild.rs lines 68-709 (deterministic constructors;
//! kernel re-checks).
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

// ===========================================================================
//  RING-TERM EVALUATOR over the value lattice { 0, 1, ( inv 1 ) }.
//
//  A `Val` is the symbolic normal form of a closed ring term built from
//  the literals 0 and 1 by + , * , inv (the only constructors that occur
//  in the entrywise Jacobi expansion of the concrete witness).  Every
//  subterm value lies in { 0, 1, m } with m := ( inv 1 ) (verified
//  exhaustively offline; the kernel re-checks each emitted proof anyway).
//
//  `eval(term)` returns ( Val , Pf ) where Pf : |- <term> = <Val.w()> ,
//  built ONLY from frozen ring axioms via the verbatim toolkit
//  (eqtr/eqcom/cong_l/cong_r + ax-mul0/mul1/mulcom/add0/addcom/addneg).
//  Genuine wave-4 discipline: every step a ring-axiom congruence; the
//  literal nested LHS is reduced, NOT replaced.
// ===========================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Val {
    Zero,
    One,
    NegOne, // ( inv 1 )
}

// A ring term over literals {0,1} and constructors + * inv.
#[derive(Clone)]
enum Tm {
    Z,
    I,
    Add(Box<Tm>, Box<Tm>),
    Mul(Box<Tm>, Box<Tm>),
    Inv(Box<Tm>),
}

fn add_t(a: Tm, b: Tm) -> Tm {
    Tm::Add(Box::new(a), Box::new(b))
}
fn mul_t(a: Tm, b: Tm) -> Tm {
    Tm::Mul(Box::new(a), Box::new(b))
}
fn inv_t(a: Tm) -> Tm {
    Tm::Inv(Box::new(a))
}

fn main() {
    let base = include_str!("../../data/sdg.base.mm");
    let zero = reg(&W { rpn: t("t0"), toks: t("0") });
    let one = reg(&W { rpn: t("t1"), toks: t("1") });
    let mw = reg(&neg(&one)); // m := ( inv 1 )

    // ---- frozen ring-axiom instance helpers (all PURE RING) -------------
    let pl = |a: &W, b: &W| reg(&binop(a, b, "+", "tpl"));
    let ml = |a: &W, b: &W| reg(&binop(a, b, "*", "tmu"));
    let mul0 = |x: &W| axeq("ax-mul0", &[x], &reg(&binop(x, &zero, "*", "tmu")), &zero);
    let mul1 = |x: &W| axeq("ax-mul1", &[x], &reg(&binop(x, &one, "*", "tmu")), x);
    let add0 = |x: &W| axeq("ax-add0", &[x], &reg(&binop(x, &zero, "+", "tpl")), x);
    let addcom = |a: &W, b: &W| {
        axeq(
            "ax-addcom",
            &[a, b],
            &reg(&binop(a, b, "+", "tpl")),
            &reg(&binop(b, a, "+", "tpl")),
        )
    };
    let mulcom = |a: &W, b: &W| {
        axeq(
            "ax-mulcom",
            &[a, b],
            &reg(&binop(a, b, "*", "tmu")),
            &reg(&binop(b, a, "*", "tmu")),
        )
    };
    let addneg = |x: &W| axeq("ax-addneg", &[x], &reg(&binop(x, &neg(x), "+", "tpl")), &zero);
    let clp1 = |p: &Pf, z: &W| cong_l(p, z, "+", "tpl", "eq-pl1"); // (a+z)=(b+z)
    let crp2 = |p: &Pf, z: &W| cong_r(p, z, "+", "tpl", "eq-pl2"); // (z+a)=(z+b)
    let cml1 = |p: &Pf, z: &W| cong_l(p, z, "*", "tmu", "eq-mu1"); // (a*z)=(b*z)
    let cmu2 = |p: &Pf, z: &W| cong_r(p, z, "*", "tmu", "eq-mu2"); // (z*a)=(z*b)

    let wof = |v: Val| -> W {
        match v {
            Val::Zero => zero.clone(),
            Val::One => one.clone(),
            Val::NegOne => mw.clone(),
        }
    };

    // =====================================================================
    //  sdg-jacobi-eqneg : ( x = y -> ( inv x ) = ( inv y ) )
    //  Copied verbatim from sdg-nonab-eqneg, relabelled.  DERIVED pure-
    //  ring in deduction form (the frozen base has no eq-neg axiom).
    // ---------------------------------------------------------------------
    let inv0 = neg(&zero);
    let an0 = addneg(&zero);
    let t1c = addcom(&zero, &inv0);
    let t2c = add0(&inv0);
    let z_i0_eq_i0 = eqtr(&t1c, &t2c);
    let pf_inv0 = eqtr(&eqsym(&z_i0_eq_i0), &an0); // ( inv 0 ) = 0

    let x = leaf("vx", "x");
    let y = leaf("vy", "y");
    let ix = neg(&x);
    let iy = neg(&y);
    let g_xy = reg(&weq(&x, &y));
    let e1 = eqsym(&add0(&ix));
    let e2 = crp2(&eqsym(&addneg(&y)), &ix);
    let e3 = eqsym(&{
        let l = reg(&binop(&reg(&binop(&ix, &y, "+", "tpl")), &iy, "+", "tpl"));
        let r = reg(&binop(&ix, &reg(&binop(&y, &iy, "+", "tpl")), "+", "tpl"));
        axeq("ax-addass", &[&ix, &y, &iy], &l, &r)
    });
    let e5 = clp1(&addcom(&ix, &x), &iy);
    let e6 = clp1(&addneg(&x), &iy);
    let e7 = eqtr(&addcom(&zero, &iy), &add0(&iy));
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
    let c = imp_a1(&e1, &g_xy);
    let c = imp_eqtr(&c, &imp_a1(&e2, &g_xy));
    let c = imp_eqtr(&c, &imp_a1(&e3, &g_xy));
    let c = imp_eqtr(&c, &g_e4);
    let c = imp_eqtr(&c, &imp_a1(&e5, &g_xy));
    let c = imp_eqtr(&c, &imp_a1(&e6, &g_xy));
    let sdg_jacobi_eqneg = imp_eqtr(&c, &imp_a1(&e7, &g_xy));

    // negcong rule: from P:(a=b) get (inv a)=(inv b) via sdg-jacobi-eqneg.
    let negcong = |p: &Pf| -> Pf {
        let (a, b) = split_eq(&p.stmt);
        let aw = w_of(&a);
        let bw = w_of(&b);
        let inst = use_thm(
            "sdg-jacobi-eqneg",
            &[("x", &aw), ("y", &bw)],
            &[],
            wi(
                &reg(&weq(&aw, &bw)),
                &reg(&weq(&neg(&aw), &neg(&bw))),
            )
            .toks,
        );
        mp(p, &inst)
    };

    // =====================================================================
    //  TABLE LEMMAS — closed pure-ring proofs of every (op,val,val) /
    //  (inv,val) combination that occurs in the entrywise expansion.
    //  Each returns Pf : |- <lhs literal> = <rhs Val literal>.
    // ---------------------------------------------------------------------

    // inv 0 = 0   (pf_inv0 above);  inv 1 = ( inv 1 )  (eqid).
    let inv1_refl = apply("eqid", &[&mw], &[], reg(&weq(&mw, &mw)).toks);

    // 1 + ( inv 1 ) = 0    (ax-addneg at 1)
    let one_plus_m = addneg(&one); // ( 1 + ( inv 1 ) ) = 0
    // ( inv 1 ) + 1 = 0    (addcom then ax-addneg)
    let m_plus_one = eqtr(&addcom(&mw, &one), &addneg(&one));
    // 0 + ( inv 1 ) = ( inv 1 )
    let zero_plus_m = eqtr(&addcom(&zero, &mw), &add0(&mw));
    // 0 + 1 = 1
    let zero_plus_one = eqtr(&addcom(&zero, &one), &add0(&one));
    // 0 + 0 = 0
    let zero_plus_zero = add0(&zero);
    // 1 + 0 = 1
    let one_plus_zero = add0(&one);

    // mul table:
    // 0 * 0 = 0 ; 1 * 0 = 0  (ax-mul0)
    // 0 * 1 = 0 : (0*1)=(1*0)=0 via mulcom + mul0
    // 1 * 1 = 1 : ax-mul1
    // 0 * m = 0 : (0*m)=(m*0)=0 via mulcom + mul0
    // m * 0 = 0 : ax-mul0

    // addition of two Vals -> (Val result, Pf : |- ( <lw> + <rw> ) = res)
    let add_vv = |lv: Val, rv: Val| -> (Val, Pf) {
        use Val::*;
        let lw = wof(lv);
        let rw = wof(rv);
        match (lv, rv) {
            (Zero, Zero) => (Zero, add0(&zero)),
            (Zero, One) => (One, zero_plus_one.clone()),
            (Zero, NegOne) => (NegOne, zero_plus_m.clone()),
            (One, Zero) => (One, one_plus_zero.clone()),
            (One, NegOne) => (Zero, one_plus_m.clone()),
            (NegOne, One) => (Zero, m_plus_one.clone()),
            // remaining combinations do not occur in the expansion; provide
            // generic pure-ring fallbacks so the evaluator is total.
            (One, One) => {
                // ( 1 + 1 ) — never occurs; not a lattice value, refuse.
                panic!("unexpected ( 1 + 1 ) in expansion");
            }
            (NegOne, Zero) => (NegOne, add0(&mw)),
            (NegOne, NegOne) => panic!("unexpected ( m + m ) in expansion"),
            (One, _) | (Zero, _) | (NegOne, _) => {
                let _ = (&lw, &rw);
                unreachable!()
            }
        }
    };

    let mul_vv = |lv: Val, rv: Val| -> (Val, Pf) {
        use Val::*;
        match (lv, rv) {
            (Zero, Zero) => (Zero, mul0(&zero)),
            (One, Zero) => (Zero, mul0(&one)),
            (NegOne, Zero) => (Zero, mul0(&mw)),
            (Zero, One) => {
                // ( 0 * 1 ) = ( 1 * 0 ) = 0
                (Zero, eqtr(&mulcom(&zero, &one), &mul0(&one)))
            }
            (One, One) => (One, mul1(&one)),
            (Zero, NegOne) => {
                // ( 0 * m ) = ( m * 0 ) = 0
                (Zero, eqtr(&mulcom(&zero, &mw), &mul0(&mw)))
            }
            (One, NegOne) => (NegOne, mul1(&mw)), // ( 1 * m )=... ; mul1: (m*1)=m
            // fallbacks (unused by witness)
            (NegOne, One) => (NegOne, {
                // ( m * 1 ) = m
                mul1(&mw)
            }),
            (NegOne, NegOne) => panic!("unexpected ( m * m ) in expansion"),
        }
    };

    // recursive evaluator: Tm -> (Val, Pf : |- <tm> = <Val>)
    fn build_eval(
        tm: &Tm,
        zero: &W,
        one: &W,
        mw: &W,
        wof: &dyn Fn(Val) -> W,
        pf_inv0: &Pf,
        inv1_refl: &Pf,
        add_vv: &dyn Fn(Val, Val) -> (Val, Pf),
        mul_vv: &dyn Fn(Val, Val) -> (Val, Pf),
        negcong: &dyn Fn(&Pf) -> Pf,
    ) -> (Val, Pf) {
        match tm {
            Tm::Z => (
                Val::Zero,
                apply("eqid", &[zero], &[], reg(&weq(zero, zero)).toks),
            ),
            Tm::I => (
                Val::One,
                apply("eqid", &[one], &[], reg(&weq(one, one)).toks),
            ),
            Tm::Add(a, b) => {
                let (av, ap) = build_eval(
                    a, zero, one, mw, wof, pf_inv0, inv1_refl, add_vv, mul_vv, negcong,
                );
                let (bv, bp) = build_eval(
                    b, zero, one, mw, wof, pf_inv0, inv1_refl, add_vv, mul_vv, negcong,
                );
                let aw = wof(av);
                let bw = wof(bv);
                // ( a + b ) = ( av + b )   [cong_l on ap]
                let s1 = cong_l(&ap, &orig_w(b, zero, one, mw), "+", "tpl", "eq-pl1");
                // ( av + b ) = ( av + bv ) [cong_r on bp]
                let s2 = cong_r(&bp, &aw, "+", "tpl", "eq-pl2");
                let chain = eqtr(&s1, &s2); // ( a + b ) = ( av + bv )
                let (rv, rp) = add_vv(av, bv);
                let _ = &bw;
                (rv, eqtr(&chain, &rp))
            }
            Tm::Mul(a, b) => {
                let (av, ap) = build_eval(
                    a, zero, one, mw, wof, pf_inv0, inv1_refl, add_vv, mul_vv, negcong,
                );
                let (bv, bp) = build_eval(
                    b, zero, one, mw, wof, pf_inv0, inv1_refl, add_vv, mul_vv, negcong,
                );
                let aw = wof(av);
                let s1 = cong_l(&ap, &orig_w(b, zero, one, mw), "*", "tmu", "eq-mu1");
                let s2 = cong_r(&bp, &aw, "*", "tmu", "eq-mu2");
                let chain = eqtr(&s1, &s2);
                let (rv, rp) = mul_vv(av, bv);
                (rv, eqtr(&chain, &rp))
            }
            Tm::Inv(a) => {
                let (av, ap) = build_eval(
                    a, zero, one, mw, wof, pf_inv0, inv1_refl, add_vv, mul_vv, negcong,
                );
                // ( inv a ) = ( inv av )   via negcong on ap
                let s1 = negcong(&ap);
                let (rv, rp) = match av {
                    Val::Zero => (Val::Zero, pf_inv0.clone()), // ( inv 0 ) = 0
                    Val::One => (Val::NegOne, inv1_refl.clone()), // ( inv 1 ) = m
                    Val::NegOne => {
                        // ( inv ( inv 1 ) ) — does not occur; refuse.
                        panic!("unexpected ( inv ( inv 1 ) ) in expansion");
                    }
                };
                (rv, eqtr(&s1, &rp))
            }
        }
    }

    // Reconstruct the W (token/rpn) for a raw Tm (the literal nested term).
    fn orig_w(tm: &Tm, zero: &W, one: &W, mw: &W) -> W {
        match tm {
            Tm::Z => zero.clone(),
            Tm::I => one.clone(),
            Tm::Add(a, b) => reg(&binop(
                &orig_w(a, zero, one, mw),
                &orig_w(b, zero, one, mw),
                "+",
                "tpl",
            )),
            Tm::Mul(a, b) => reg(&binop(
                &orig_w(a, zero, one, mw),
                &orig_w(b, zero, one, mw),
                "*",
                "tmu",
            )),
            Tm::Inv(a) => reg(&neg(&orig_w(a, zero, one, mw))),
        }
    }

    let _ = (&ml, &pl, &clp1, &crp2, &cml1, &cmu2, &zero_plus_zero);

    // =====================================================================
    //  THE WITNESS  A=[[0,1],[0,0]]  B=[[0,0],[1,0]]  C=[[1,0],[0,0]]
    //  Pairwise commutators genuinely NON-ZERO:
    //    [A,B]=[[1,0],[0,inv 1]]  [B,C]=[[0,0],[1,0]]  [C,A]=[[0,1],[0,0]]
    //  Cyclic Jacobi sum [A,[B,C]]+[B,[C,A]]+[C,[A,B]] = ZERO entrywise.
    // ---------------------------------------------------------------------
    type Mat = [[Tm; 2]; 2];
    fn z2() -> Tm {
        Tm::Z
    }
    fn i2() -> Tm {
        Tm::I
    }
    fn matmul(x: &Mat, y: &Mat) -> Mat {
        let g = |i: usize, j: usize| {
            add_t(
                mul_t(x[i][0].clone(), y[0][j].clone()),
                mul_t(x[i][1].clone(), y[1][j].clone()),
            )
        };
        [[g(0, 0), g(0, 1)], [g(1, 0), g(1, 1)]]
    }
    fn comm(x: &Mat, y: &Mat) -> Mat {
        let xy = matmul(x, y);
        let yx = matmul(y, x);
        let g = |i: usize, j: usize| add_t(xy[i][j].clone(), inv_t(yx[i][j].clone()));
        [[g(0, 0), g(0, 1)], [g(1, 0), g(1, 1)]]
    }
    fn madd(x: &Mat, y: &Mat) -> Mat {
        let g = |i: usize, j: usize| add_t(x[i][j].clone(), y[i][j].clone());
        [[g(0, 0), g(0, 1)], [g(1, 0), g(1, 1)]]
    }
    let a_m: Mat = [[z2(), i2()], [z2(), z2()]];
    let b_m: Mat = [[z2(), z2()], [i2(), z2()]];
    let c_m: Mat = [[i2(), z2()], [z2(), z2()]];

    let abc = comm(&a_m, &comm(&b_m, &c_m));
    let bca = comm(&b_m, &comm(&c_m, &a_m));
    let cab = comm(&c_m, &comm(&a_m, &b_m));
    let jac = madd(&madd(&abc, &bca), &cab);

    // Build the four entrywise proofs : |- <literal jac_ij> = 0
    let eval_one = |tm: &Tm| -> Pf {
        let (v, p) = build_eval(
            tm, &zero, &one, &mw, &wof, &pf_inv0, &inv1_refl, &add_vv, &mul_vv,
            &negcong,
        );
        assert_eq!(v, Val::Zero, "Jacobi entry did not evaluate to 0");
        p
    };
    let j11 = eval_one(&jac[0][0]);
    let j12 = eval_one(&jac[0][1]);
    let j21 = eval_one(&jac[1][0]);
    let j22 = eval_one(&jac[1][1]);

    // exact statement strings (literal nested LHS = 0)
    fn render(tm: &Tm) -> String {
        match tm {
            Tm::Z => "0".into(),
            Tm::I => "1".into(),
            Tm::Add(a, b) => format!("( {} + {} )", render(a), render(b)),
            Tm::Mul(a, b) => format!("( {} * {} )", render(a), render(b)),
            Tm::Inv(a) => format!("( inv {} )", render(a)),
        }
    }
    let st11 = format!("|- {} = 0", render(&jac[0][0]));
    let st12 = format!("|- {} = 0", render(&jac[0][1]));
    let st21 = format!("|- {} = 0", render(&jac[1][0]));
    let st22 = format!("|- {} = 0", render(&jac[1][1]));

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, String, &Pf)> = vec![
        (
            "sdg-jacobi-eqneg",
            "|- ( x = y -> ( inv x ) = ( inv y ) )".to_string(),
            &sdg_jacobi_eqneg,
        ),
        ("sdg-jacobi-j11", st11, &j11),
        ("sdg-jacobi-j12", st12, &j12),
        ("sdg-jacobi-j21", st21, &j21),
        ("sdg-jacobi-j22", st22, &j22),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         GENUINE NON-VACUOUS NON-ABELIAN JACOBI at a CONCRETE 2x2 witness\n   \
         (sdgjacobibuild) — BOOK-3 WAVE-8, NO new substrate commitment.\n   \
         Witness A=[[0,1],[0,0]] B=[[0,0],[1,0]] C=[[1,0],[0,0]] over the\n   \
         FROZEN commutative ring R.  Matrix product entrywise via ring\n   \
         + and * ; commutator entry [X,Y]_ij=((X.Y)_ij+inv(Y.X)_ij).\n   \
         Pairwise commutators genuinely NON-ZERO: [A,B]=[[1,0],[0,inv 1]]\n   \
         [B,C]=[[0,0],[1,0]] [C,A]=[[0,1],[0,0]] (NOT commutator-collapse\n   \
         — a symbolic commutative Jacobi would be the vacuous 0+0+0=0,\n   \
         deliberately NOT shipped by wave-7).  The nested brackets\n   \
         [A,[B,C]]=[[1,0],[0,inv 1]] [B,[C,A]]=[[inv 1,0],[0,1]]\n   \
         [C,[A,B]]=0 are themselves non-zero, yet the cyclic Jacobi sum\n   \
         [A,[B,C]]+[B,[C,A]]+[C,[A,B]] vanishes ENTRYWISE (j11=j12=j21=\n   \
         j22=0) by pure ring algebra — the genuine non-abelian structural\n   \
         Jacobi, non-vacuous.  sdg-jacobi-eqneg is the inv congruence\n   \
         (x=y -> inv x=inv y), DERIVED pure-ring (deduction form; the\n   \
         frozen base has no eq-neg).  THE NAMED RESIDUALS (never papered):\n   \
         (a) the non-vacuity itself (that [A,B],[B,C],[C,A] are genuinely\n   \
         NON-ZERO) is EXACTLY 1!=0, the GROUNDED cross-book spine (Book\n   \
         One's irreducible residue); (b) general matrix rank / arbitrary\n   \
         Lie algebra; (c) the full DF=0 assembly and dynamics.  No new\n   \
         axiom; nothing classical; NO seam, NO eq-ap; model floor the\n   \
         UNCHANGED Book-Two [PROJECTION], never re-summed.  Self-contained\n   \
         over the FROZEN data/sdg.base.mm; disjoint `sdg-jacobi-*`\n   \
         labels; shares no $p with any corpus.\n   \
         ================================================================ $)\n\n",
    );
    for (name, stmt, pf) in &proofs {
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
        writeln!(out, "{name} $p {stmt} $= {} $.", pf.rpn.join(" ")).unwrap();
    }

    match kernel::Db::parse(&out) {
        Ok(db) => match db.verify() {
            Ok(()) => {
                let n = db.stmts.iter().filter(|s| s.kind == kernel::Kind::P).count();
                std::fs::write("data/sdg.jacobi.mm", &out)
                    .expect("write data/sdg.jacobi.mm");
                println!(
                    "sdgjacobibuild: kernel-verified {n} $p; wrote data/sdg.jacobi.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgjacobibuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.jacobi.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgjacobibuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.jacobi.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
