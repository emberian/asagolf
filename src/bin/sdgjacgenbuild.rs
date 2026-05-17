//! sdgjacgenbuild — BOOK-3 WAVE-10: the STRUCTURAL BACKBONE of the
//! non-abelian framework — general symbolic 2x2 matrix-product
//! ASSOCIATIVITY, entrywise, pure-ring over the FROZEN base.  Writes
//! data/sdg.jacgen.mm.
//!
//! Why this is the right "general-rank tower" rung (not just "bigger
//! matrices").  Wave 4 gave the concrete 2x2 commutator; wave 5
//! generalized ONE commutator entry symbolically (sdg-nonabgen-*);
//! thread-2 gave the concrete sl2 Jacobi (all 4 entries, witness).
//! The genuine question those leave open: was the concrete Jacobi a
//! COINCIDENCE of the witness, or STRUCTURAL?  It is structural, and
//! the structural reason is exactly one fact: **2x2 matrix
//! multiplication is associative**, entrywise, for GENERAL symbolic
//! entries over the commutative ring — which is itself pure-ring
//! (ring associativity + distributivity + additive commutativity, NO
//! new commitment).  Associativity is precisely what makes [A,[B,C]]
//! expand consistently and the cyclic sum cancel; proving it general
//! shows the concrete Jacobi (thread-2) was not luck.  This is the
//! honest concrete->general lift, the exact nonab->nonabgen
//! discipline, one structural level deeper.
//!
//!   * sdg-jacgen-rdistr  : ( ( u + v ) * w ) = ( ( u*w ) + ( v*w ) )
//!       right-distributivity, DERIVED pure-ring (ax-distr is the LEFT
//!       form only; + ax-mulcom).
//!   * sdg-jacgen-shuffle4: ( (a+b)+(c+d) ) = ( (a+c)+(b+d) )
//!       the additive 4-term reshuffle, pure-ring (ax-addass/addcom).
//!   * sdg-jacgen-assoc11 : general symbolic ((A·B)·C)_11 = (A·(B·C))_11
//!       — A=[[a,c],[.,.]], B=[[b,f],[d,g]], C=[[e,.],[u,.]] :
//!       ( ( ((a*b)+(c*d)) * e ) + ( ((a*f)+(c*g)) * u ) )
//!         = ( ( a*((b*e)+(f*u)) ) + ( c*((d*e)+(g*u)) ) ).
//!       THE structural backbone: matrix-product associativity, (1,1).
//!   * sdg-jacgen-assoc12 : the same at the (1,2) entry (C col2 = v,w)
//!       — associativity is not special to (1,1); a second entry, to
//!       show generality across positions.
//!
//! HONEST SCOPE.  What CLOSES, pure-ring, general symbolic, kernel-
//! verified, NO new substrate commitment, nothing classical: 2x2
//! matrix-product associativity at two entries (the structural reason
//! the concrete non-abelian Jacobi closed) + its two pure-ring
//! helpers.  NAMED RESIDUAL (not papered): the FULL general symbolic
//! Jacobi (all 4 entries, nested triple bracket) and general n x n
//! rank.  The concrete sl2 witness (thread-2, data/sdg.jacobi.mm) is
//! the proof-of-concept; this wave supplies the structural backbone
//! that makes it not-a-coincidence; the full general symbolic Jacobi
//! tower remains the named residual, exactly as nonabgen was one
//! entry of the bare commutator, not the whole tower.  The non-
//! vacuity of the non-abelian content remains the GROUNDED spine
//! 1!=0; the model-meaning floor the UNCHANGED Book-Two [PROJECTION],
//! never re-summed.
//!
//! Self-contained over the FROZEN eq-ap-extended data/sdg.base.mm;
//! disjoint `sdg-jacgen-*` labels; shares NO $p with any corpus.
//! Modifies no kernel / base / other corpus / builder.  Toolkit
//! copied VERBATIM from src/bin/sdgbuild.rs (deterministic
//! constructors; the kernel independently re-checks every emitted $p).
//!
//! Run:  cargo run --release --bin sdgjacgenbuild
//! Trust root = src/kernel.rs re-checking data/sdg.jacgen.mm (also
//! sdgjacgenfloor / sdgjacgenpure).
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
    let base = include_str!("../../data/sdg.base.mm");

    let a = reg(&leaf("va", "a"));
    let b = reg(&leaf("vb", "b"));
    let c = reg(&leaf("vc", "c"));
    let d = reg(&leaf("vd", "d"));
    let e = reg(&leaf("ve", "e"));
    let f = reg(&leaf("vf", "f"));
    let g = reg(&leaf("vg", "g"));
    let uu = reg(&leaf("vu", "u"));
    let vv = reg(&leaf("vv", "v"));
    let ww = reg(&leaf("vw", "w"));

    let pl = |x: &W, y: &W| reg(&binop(x, y, "+", "tpl"));
    let ml = |x: &W, y: &W| reg(&binop(x, y, "*", "tmu"));
    let mulcom = |x: &W, y: &W| {
        axeq("ax-mulcom", &[x, y], &reg(&binop(x, y, "*", "tmu")), &reg(&binop(y, x, "*", "tmu")))
    };
    let addcom = |x: &W, y: &W| {
        axeq("ax-addcom", &[x, y], &reg(&binop(x, y, "+", "tpl")), &reg(&binop(y, x, "+", "tpl")))
    };
    let mulass = |x: &W, y: &W, z: &W| {
        let l = reg(&binop(&reg(&binop(x, y, "*", "tmu")), z, "*", "tmu"));
        let r = reg(&binop(x, &reg(&binop(y, z, "*", "tmu")), "*", "tmu"));
        axeq("ax-mulass", &[x, y, z], &l, &r)
    };
    let addass = |x: &W, y: &W, z: &W| {
        let l = reg(&binop(&reg(&binop(x, y, "+", "tpl")), z, "+", "tpl"));
        let r = reg(&binop(x, &reg(&binop(y, z, "+", "tpl")), "+", "tpl"));
        axeq("ax-addass", &[x, y, z], &l, &r)
    };
    let distr = |x: &W, y: &W, z: &W| {
        let l = reg(&binop(x, &reg(&binop(y, z, "+", "tpl")), "*", "tmu"));
        let r = reg(&binop(&reg(&binop(x, y, "*", "tmu")), &reg(&binop(x, z, "*", "tmu")), "+", "tpl"));
        axeq("ax-distr", &[x, y, z], &l, &r)
    };
    let clp1 = |p: &Pf, z: &W| cong_l(p, z, "+", "tpl", "eq-pl1");
    let crp2 = |p: &Pf, z: &W| cong_r(p, z, "+", "tpl", "eq-pl2");

    // ===== sdg-jacgen-rdistr : ( ( u + v ) * w ) = ( ( u*w ) + ( v*w ) )
    let upv = pl(&uu, &vv);
    let r_s1 = mulcom(&upv, &ww); // ((u+v)*w) = (w*(u+v))
    let r_s2 = distr(&ww, &uu, &vv); // (w*(u+v)) = ((w*u)+(w*v))
    let r_s3 = clp1(&mulcom(&ww, &uu), &reg(&binop(&ww, &vv, "*", "tmu"))); // ((w*u)+(w*v))=((u*w)+(w*v))
    let r_s4 = crp2(&mulcom(&ww, &vv), &reg(&binop(&uu, &ww, "*", "tmu"))); // ((u*w)+(w*v))=((u*w)+(v*w))
    let sdg_jacgen_rdistr = eqtr(&eqtr(&eqtr(&r_s1, &r_s2), &r_s3), &r_s4);

    let rdistr_use = |x: &W, y: &W, z: &W| -> Pf {
        use_thm(
            "sdg-jacgen-rdistr",
            &[("u", x), ("v", y), ("w", z)],
            &[],
            reg(&weq(
                &reg(&binop(&reg(&binop(x, y, "+", "tpl")), z, "*", "tmu")),
                &reg(&binop(&reg(&binop(x, z, "*", "tmu")), &reg(&binop(y, z, "*", "tmu")), "+", "tpl")),
            ))
            .toks,
        )
    };

    // ===== sdg-jacgen-shuffle4 : ((a+b)+(c+d)) = ((a+c)+(b+d))
    let s_t1 = addass(&a, &b, &pl(&c, &d)); // ((a+b)+(c+d)) = (a+(b+(c+d)))
    let s_mid = {
        let m1 = eqsym(&addass(&b, &c, &d)); // (b+(c+d)) = ((b+c)+d)
        let m2 = clp1(&addcom(&b, &c), &d); // ((b+c)+d) = ((c+b)+d)
        let m3 = addass(&c, &b, &d); // ((c+b)+d) = (c+(b+d))
        eqtr(&eqtr(&m1, &m2), &m3) // (b+(c+d)) = (c+(b+d))
    };
    let s_t2 = crp2(&s_mid, &a); // (a+(b+(c+d))) = (a+(c+(b+d)))
    let s_t3 = eqsym(&addass(&a, &c, &pl(&b, &d))); // (a+(c+(b+d))) = ((a+c)+(b+d))
    let sdg_jacgen_shuffle4 = eqtr(&eqtr(&s_t1, &s_t2), &s_t3);

    let shuffle4_use = |p: &W, q: &W, r: &W, s: &W| -> Pf {
        use_thm(
            "sdg-jacgen-shuffle4",
            &[("a", p), ("b", q), ("c", r), ("d", s)],
            &[],
            reg(&weq(
                &reg(&binop(&reg(&binop(p, q, "+", "tpl")), &reg(&binop(r, s, "+", "tpl")), "+", "tpl")),
                &reg(&binop(&reg(&binop(p, r, "+", "tpl")), &reg(&binop(q, s, "+", "tpl")), "+", "tpl")),
            ))
            .toks,
        )
    };

    // ===== general symbolic 2x2 matrix-product associativity, one entry.
    //  C-column = (m, n).  A=[[a,c],[.,.]] B=[[b,f],[d,g]] C col=[m;n].
    //  ( ( ((a*b)+(c*d)) * m ) + ( ((a*f)+(c*g)) * n ) )
    //    = ( ( a*((b*m)+(f*n)) ) + ( c*((d*m)+(g*n)) ) )
    let assoc_entry = |m: &W, n: &W| -> Pf {
        let ab = ml(&a, &b);
        let cd = ml(&c, &d);
        let af = ml(&a, &f);
        let cg = ml(&c, &g);
        let abcd = pl(&ab, &cd); // (A·B)_11
        let afcg = pl(&af, &cg); // (A·B)_12
        // P = a*(b*m)  Q = c*(d*m)  T = a*(f*n)  W = c*(g*n)
        let bm = ml(&b, m);
        let dm = ml(&d, m);
        let fn_ = ml(&f, n);
        let gn = ml(&g, n);
        let cap_p = ml(&a, &bm);
        let cap_q = ml(&c, &dm);
        let cap_t = ml(&a, &fn_);
        let cap_w = ml(&c, &gn);

        // term1 : ( ( (a*b)+(c*d) ) * m ) = ( P + Q )
        let t1a = rdistr_use(&ab, &cd, m); // = ((a*b)*m)+((c*d)*m)
        let t1b = clp1(&mulass(&a, &b, m), &ml(&cd, m)); // ((a*b)*m)->P  under +((c*d)*m)
        let t1c = crp2(&mulass(&c, &d, m), &cap_p); // ((c*d)*m)->Q  under P+_
        let term1 = eqtr(&eqtr(&t1a, &t1b), &t1c); // ((abcd)*m) = (P+Q)
        // term2 : ( ( (a*f)+(c*g) ) * n ) = ( T + W )
        let t2a = rdistr_use(&af, &cg, n);
        let t2b = clp1(&mulass(&a, &f, n), &ml(&cg, n));
        let t2c = crp2(&mulass(&c, &g, n), &cap_t);
        let term2 = eqtr(&eqtr(&t2a, &t2b), &t2c); // ((afcg)*n) = (T+W)
        // LHS_orig = ((abcd)*m) + ((afcg)*n)  ->  (P+Q)+(T+W)
        let lhs_e1 = clp1(&term1, &ml(&afcg, n)); // ((abcd)*m + (afcg)*n) = ((P+Q) + (afcg)*n)
        let lhs_e2 = crp2(&term2, &pl(&cap_p, &cap_q)); // = ((P+Q)+(T+W))
        let lhs_eq = eqtr(&lhs_e1, &lhs_e2);
        // RHS_orig = a*((b*m)+(f*n)) + c*((d*m)+(g*n))  ->  (P+T)+(Q+W)
        let r_t1 = distr(&a, &bm, &fn_); // a*((b*m)+(f*n)) = (P+T)
        let r_t2 = distr(&c, &dm, &gn); // c*((d*m)+(g*n)) = (Q+W)
        let rhs_e1 = clp1(&r_t1, &ml(&c, &pl(&dm, &gn)));
        let rhs_e2 = crp2(&r_t2, &pl(&cap_p, &cap_t));
        let rhs_eq = eqtr(&rhs_e1, &rhs_e2); // RHS_orig = ((P+T)+(Q+W))
        // bridge: (P+Q)+(T+W) = (P+T)+(Q+W)
        let sh = shuffle4_use(&cap_p, &cap_q, &cap_t, &cap_w);
        eqtr(&lhs_eq, &eqtr(&sh, &eqsym(&rhs_eq))) // LHS_orig = RHS_orig
    };

    let sdg_jacgen_assoc11 = assoc_entry(&e, &uu);
    let sdg_jacgen_assoc12 = assoc_entry(&vv, &ww);

    let _ = (
        &sdg_jacgen_rdistr,
        &sdg_jacgen_shuffle4,
        &sdg_jacgen_assoc11,
        &sdg_jacgen_assoc12,
    );

    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-jacgen-rdistr",
            "|- ( ( u + v ) * w ) = ( ( u * w ) + ( v * w ) )",
            vec![],
            &sdg_jacgen_rdistr,
        ),
        (
            "sdg-jacgen-shuffle4",
            "|- ( ( a + b ) + ( c + d ) ) = ( ( a + c ) + ( b + d ) )",
            vec![],
            &sdg_jacgen_shuffle4,
        ),
        (
            "sdg-jacgen-assoc11",
            "|- ( ( ( ( a * b ) + ( c * d ) ) * e ) + ( ( ( a * f ) + ( c * g ) ) * u ) ) = ( ( a * ( ( b * e ) + ( f * u ) ) ) + ( c * ( ( d * e ) + ( g * u ) ) ) )",
            vec![],
            &sdg_jacgen_assoc11,
        ),
        (
            "sdg-jacgen-assoc12",
            "|- ( ( ( ( a * b ) + ( c * d ) ) * v ) + ( ( ( a * f ) + ( c * g ) ) * w ) ) = ( ( a * ( ( b * v ) + ( f * w ) ) ) + ( c * ( ( d * v ) + ( g * w ) ) ) )",
            vec![],
            &sdg_jacgen_assoc12,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         GENERAL SYMBOLIC 2x2 MATRIX-PRODUCT ASSOCIATIVITY\n   \
         (sdgjacgenbuild) — BOOK-3 WAVE-10, the STRUCTURAL BACKBONE.\n   \
         ((A.B).C)_11 = (A.(B.C))_11 and the (1,2) entry, for GENERAL\n   \
         symbolic 2x2 entries over the FROZEN commutative ring — the\n   \
         pure-ring reason the concrete non-abelian Jacobi (thread-2)\n   \
         closed was STRUCTURE, not coincidence.  rdistr (right-\n   \
         distributivity, derived; ax-distr is left-only) + shuffle4\n   \
         (additive 4-term reshuffle) are the pure-ring helpers.  NO new\n   \
         substrate commitment, nothing classical, every $p PURE RING.\n   \
         NAMED RESIDUAL: the full general symbolic Jacobi (all entries,\n   \
         nested triple bracket) and general n x n rank — the concrete\n   \
         sl2 witness is the proof-of-concept, this is its structural\n   \
         backbone, the tower stays the named residual (the exact\n   \
         nonab->nonabgen concrete->general discipline).  Self-contained\n   \
         over the FROZEN data/sdg.base.mm; disjoint `sdg-jacgen-*`\n   \
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
                std::fs::write("data/sdg.jacgen.mm", &out).expect("write data/sdg.jacgen.mm");
                println!(
                    "sdgjacgenbuild: kernel-verified {n} $p; wrote data/sdg.jacgen.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgjacgenbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.jacgen.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgjacgenbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.jacgen.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
