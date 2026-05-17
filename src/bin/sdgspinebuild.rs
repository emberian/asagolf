//! sdgspinebuild — GROUNDING THE CROSS-BOOK SPINE.  Writes
//! data/sdg.spine.mm.
//!
//! Wave 4 (data/sdg.nonab.mm) NAMED a finding: the non-vacuity of the
//! non-abelian commutator witness [A,B]=[[1,0],[0,(inv 1)]] — that it
//! is genuinely NON-ZERO — is EXACTLY 1≠0, which is PRECISELY Book
//! One's measured irreducible residue (suc∅≠∅ / orientation,
//! COST_STRUCTURE bottom).  That was a NARRATIVE claim, honestly
//! labelled.  This corpus GROUNDS the Book-Three segment of that spine
//! into a kernel-verified transport, per the transport-anchored-floor
//! discipline (the binding is machine-checked; the bridge is cited
//! once, never re-summed, never faked).
//!
//! The spine is a TWO-SEGMENT transport joined at the shared literal
//! 1≠0:
//!   * BOOK-THREE SEGMENT — grounded HERE, kernel-verified, MEASURED:
//!       sdg-spine-comm11 rebuilds the witness (1,1) commutator entry
//!       = 1 pure-ring over the FROZEN base (with the derived inv
//!       congruence sdg-spine-eqneg, since the base has no eq-neg);
//!       sdg-spine-b3 is the transport
//!         |- ( <[A,B]11-expr> = 0 -> 1 = 0 )
//!       i.e. "if the witness commutator's (1,1) entry vanishes then
//!       1 = 0" — equivalently, the non-abelian non-vacuity reduces
//!       EXACTLY to 1≠0.  Tiny, pure-ring (eqtri on the witness
//!       identity).  Its intuitionistic contrapositive — 1≠0 ⇒ the
//!       commutator is genuinely non-zero (non-vacuity) — is the
//!       restatement; the positive implication IS the grounded fact
//!       (a base-level ¬-repackaging would need hypothetical
//!       syllogism and adds proof-engineering risk for zero semantic
//!       gain — NOT done; the implication is the honest deliverable).
//!   * BOOK-ONE SEGMENT — already transport-anchored, CITED not
//!       re-derived: Book One's measured irreducible residue
//!       suc∅≠∅ ≅ 1≠0 under the standard numeral interpretation
//!       (∅↦0, suc∅↦1), machine-checked & set.mm-anchored in Book
//!       One (COST_STRUCTURE.md / the transport-anchored-floor
//!       binding).  It is JOINED to the Book-Three segment at the
//!       identical literal 1≠0 — cited, counted once, NEVER re-summed
//!       into these MEASURED figures and NEVER re-faked here.
//!
//! NET: the spine is upgraded from a narrative [PROJECTION] to a
//! two-segment transport, BOTH segments anchored — Book-Three
//! kernel-verified here (MEASURED), Book-One cited transport-anchored
//! (its prior set.mm binding, not re-derived).  This is GROUNDING in
//! the only honest sense: a machine-checked binding, the bridge
//! counted once.  What is NOT claimed: that the two residues are the
//! "same" by anything beyond this explicit transport at the literal
//! 1≠0 — it is a structural identity between two MEASURED residues,
//! claimed at exactly that weight, never a grand unification.
//!
//! Self-contained over the FROZEN eq-ap-extended data/sdg.base.mm;
//! disjoint `sdg-spine-*` labels; shares NO $p with any corpus —
//! rename-free concatenation.  Modifies no kernel / base / other
//! corpus / builder.  Toolkit copied VERBATIM from src/bin/sdgbuild.rs
//! (deterministic constructors; the kernel independently re-checks
//! every emitted $p).
//!
//! Run:  cargo run --release --bin sdgspinebuild
//! Trust root = src/kernel.rs re-checking data/sdg.spine.mm (also
//! sdgspinefloor / sdgspinepure).
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
    let one = reg(&W { rpn: t("t1"), toks: t("1") });

    let pl = |a: &W, b: &W| reg(&binop(a, b, "+", "tpl"));
    let ml = |a: &W, b: &W| reg(&binop(a, b, "*", "tmu"));
    let mul0 = |x: &W| axeq("ax-mul0", &[x], &reg(&binop(x, &zero, "*", "tmu")), &zero);
    let mul1 = |x: &W| axeq("ax-mul1", &[x], &reg(&binop(x, &one, "*", "tmu")), x);
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
    let clp1 = |p: &Pf, z: &W| cong_l(p, z, "+", "tpl", "eq-pl1");
    let crp2 = |p: &Pf, z: &W| cong_r(p, z, "+", "tpl", "eq-pl2");

    // ( inv 0 ) = 0
    let inv0 = neg(&zero);
    let an0 = addneg(&zero);
    let _z_i0 = pl(&zero, &inv0);
    let t1 = addcom(&zero, &inv0);
    let t2 = add0(&inv0);
    let z_i0_eq_i0 = eqtr(&t1, &t2);
    let pf_inv0 = eqtr(&eqsym(&z_i0_eq_i0), &an0); // ( inv 0 ) = 0

    // ---- sdg-spine-eqneg : ( x = y -> ( inv x ) = ( inv y ) ) ----------
    //  the inv-congruence, DERIVED pure-ring deduction form (base has no
    //  eq-neg).  Needed to rewrite inside ( inv ... ) when rebuilding the
    //  witness commutator (1,1) entry locally.
    let x = leaf("vx", "x");
    let y = leaf("vy", "y");
    let ix = neg(&x);
    let iy = neg(&y);
    let g_xy = reg(&weq(&x, &y));
    let e1 = eqsym(&add0(&ix));
    let e2 = crp2(&eqsym(&addneg(&y)), &ix);
    let e3 = eqsym(&addass(&ix, &y, &iy));
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
    let sdg_spine_eqneg = imp_eqtr(&c, &imp_a1(&e7, &g_xy));

    let negcong = |p: &Pf| -> Pf {
        let (a, b) = split_eq(&p.stmt);
        let aw = w_of(&a);
        let bw = w_of(&b);
        let inst = use_thm(
            "sdg-spine-eqneg",
            &[("x", &aw), ("y", &bw)],
            &[],
            wi(&reg(&weq(&aw, &bw)), &reg(&weq(&neg(&aw), &neg(&bw)))).toks,
        );
        mp(p, &inst)
    };

    // ---- sdg-spine-comm11 : the witness [A,B](1,1) entry = 1 -----------
    //  A=[[0,1],[0,0]] B=[[0,0],[1,0]] :
    //    ( ( 0*0 ) + ( 1*1 ) ) + ( inv ( ( 0*0 ) + ( 0*0 ) ) ) = 1
    let m00 = ml(&zero, &zero);
    let m11 = ml(&one, &one);
    let r00 = mul0(&zero); // 0*0 = 0
    let r11 = mul1(&one); // 1*1 = 1
    let r0p0 = add0(&zero); // 0+0 = 0
    let r0p1 = eqtr(&addcom(&zero, &one), &add0(&one)); // 0+1 = 1

    let i_dd = {
        let b1 = clp1(&r00, &m00);
        let b2 = crp2(&r00, &zero);
        eqtr(&eqtr(&b1, &b2), &r0p0) // ((0*0)+(0*0)) = 0
    };
    let inv_s00_00 = neg(&pl(&m00, &m00));
    let inv_dd_eq0 = eqtr(&negcong(&i_dd), &pf_inv0); // ( inv ((0*0)+(0*0)) ) = 0
    let l11 = {
        let a1 = clp1(&r00, &m11);
        let a2 = crp2(&r11, &zero);
        eqtr(&eqtr(&a1, &a2), &r0p1) // ((0*0)+(1*1)) = 1
    };
    let sdg_spine_comm11 = {
        let c1 = clp1(&l11, &inv_s00_00); // (sum+invDD)=(1+invDD)
        let c2 = crp2(&inv_dd_eq0, &one); // (1+invDD)=(1+0)
        let c3 = add0(&one); // (1+0)=1
        eqtr(&eqtr(&c1, &c2), &c3)
    };

    // E := the witness (1,1) commutator expression (= comm11's LHS).
    let e_expr = reg(&binop(&pl(&m00, &m11), &neg(&pl(&m00, &m00)), "+", "tpl"));

    // ---- sdg-spine-b3 : ( E = 0 -> 1 = 0 ) ----------------------------
    //  THE GROUNDING.  The Book-Three non-abelian non-vacuity reduces
    //  EXACTLY to 1≠0: if the witness commutator's (1,1) entry vanishes
    //  then 1 = 0.  eqtri on the witness identity E = 1.  Pure-ring.
    //  Joined at the literal 1≠0 to Book One's already-transport-
    //  anchored suc∅≠∅≅1≠0 (cited from COST_STRUCTURE — NOT re-derived
    //  here, NOT re-summed; the bridge counted once).
    let one_eq_e = reg(&weq(&one, &e_expr));
    let e_eq_0 = reg(&weq(&e_expr, &zero));
    let one_eq_0 = reg(&weq(&one, &zero));
    let inner = reg(&wi(&e_eq_0, &one_eq_0)); // ( E=0 -> 1=0 )
    let one_to_e = eqsym(&sdg_spine_comm11); // 1 = E
    let _ = &one_eq_e;
    let eqtri_inst = apply(
        "eqtri",
        &[&one, &e_expr, &zero],
        &[],
        reg(&wi(&reg(&weq(&one, &e_expr)), &inner)).toks,
    ); // ( 1=E -> ( E=0 -> 1=0 ) )
    let sdg_spine_b3 = mp(&one_to_e, &eqtri_inst); // ( E=0 -> 1=0 )

    let _ = (&sdg_spine_eqneg, &sdg_spine_comm11, &sdg_spine_b3);

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-spine-eqneg",
            "|- ( x = y -> ( inv x ) = ( inv y ) )",
            vec![],
            &sdg_spine_eqneg,
        ),
        (
            "sdg-spine-comm11",
            "|- ( ( ( 0 * 0 ) + ( 1 * 1 ) ) + ( inv ( ( 0 * 0 ) + ( 0 * 0 ) ) ) ) = 1",
            vec![],
            &sdg_spine_comm11,
        ),
        (
            "sdg-spine-b3",
            "|- ( ( ( ( 0 * 0 ) + ( 1 * 1 ) ) + ( inv ( ( 0 * 0 ) + ( 0 * 0 ) ) ) ) = 0 -> 1 = 0 )",
            vec![],
            &sdg_spine_b3,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         GROUNDING THE CROSS-BOOK SPINE (sdgspinebuild).  Wave 4 NAMED\n   \
         the finding that the non-abelian commutator witness's non-\n   \
         vacuity is EXACTLY 1!=0 = Book One's measured irreducible\n   \
         residue (suc0!=0 / orientation, COST_STRUCTURE bottom).  This\n   \
         corpus GROUNDS the BOOK-THREE SEGMENT into a kernel-verified\n   \
         transport: sdg-spine-comm11 rebuilds the witness (1,1) entry\n   \
         = 1 pure-ring over the FROZEN base (with the derived inv-\n   \
         congruence sdg-spine-eqneg); sdg-spine-b3 is the transport\n   \
         ( <[A,B]11-expr> = 0 -> 1 = 0 ) — the non-abelian non-vacuity\n   \
         reduces EXACTLY to 1!=0, pure-ring (eqtri on the witness\n   \
         identity).  The BOOK-ONE SEGMENT (suc0!=0 ~= 1!=0, the\n   \
         standard numeral interpretation) is ALREADY transport-anchored\n   \
         & set.mm-bound in Book One (COST_STRUCTURE) — CITED, joined at\n   \
         the identical literal 1!=0, counted once, NEVER re-derived /\n   \
         re-summed / re-faked here.  NET: the spine is upgraded from a\n   \
         narrative [PROJECTION] to a two-segment transport, BOTH\n   \
         segments anchored.  Claimed at exactly that weight: a\n   \
         structural identity between two MEASURED residues, never a\n   \
         grand unification.  PURE RING, nothing classical, NO new\n   \
         substrate commitment.  Self-contained over the FROZEN\n   \
         eq-ap-extended data/sdg.base.mm; disjoint `sdg-spine-*`\n   \
         labels; shares no $p with any corpus.\n   \
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
                std::fs::write("data/sdg.spine.mm", &out).expect("write data/sdg.spine.mm");
                println!(
                    "sdgspinebuild: kernel-verified {n} $p; wrote data/sdg.spine.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgspinebuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.spine.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgspinebuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.spine.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
