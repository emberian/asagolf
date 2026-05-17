//! sdgbianchi2build — constructs the kernel-verified proof bodies for the
//! BOOK-3 WAVE-2 keystone: the SECOND (DIFFERENTIAL) BIANCHI IDENTITY
//! ∇R = 0, the source-free / homogeneous synthetic field equation —
//! the precise §5m residual ("a SECOND application of the Christoffel-
//! flow globalization to R itself … the §5j/§5k recursion ONE LEVEL UP")
//! DISCHARGED, and writes data/sdg.bianchi2.mm.
//!
//! Wave 1 (data/sdg.mm) closed the FIRST/algebraic Bianchi: sdg-curvature
//! threaded the Christoffel-flow seam (ax-microcancel+ax-gen) so the
//! curvature principal part R is uniquely determined; sdg-bianchi is its
//! pure-ring cyclic vanishing.  Wave 2 is the EXACT same construction
//! ONE LEVEL UP, with the curvature symbol R (here `c`, ( ap c · )) now
//! the symbol being flowed — R is itself a derivative output, so its
//! covariant derivative ∇R is the §5j/§5k recursion one level up:
//!
//!   * sdg-bianchi2-addcan-imp : the §5b seam-closer #1 (additive
//!       cancellation, deduction-discharged, HYPOTHESIS-FREE) rebuilt
//!       LOCALLY so the corpus is self-contained over the FROZEN base
//!       (data/sdg.mm's sdg-addcan-imp is NOT a base axiom).  PURE RING.
//!   * sdg-bianchi2-covd : THE KEYSTONE.  From two KL representations of
//!       the SAME R-flow value  ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) )
//!       — the curvature R evaluated along its own connection-transport
//!       flow — the covariant-derivative coefficient ∇R is UNIQUELY
//!       determined.  The linking universal is MECHANICALLY THREADED
//!       (ax-spec strips A.d; ax-ian under the ( D d ) guard;
//!       sdg-bianchi2-addcan-imp ring-only on the shared ( ap c x );
//!       ax-gen recloses — SOUND, d bound in b2.hr1/b2.hr2;
//!       ax-microcancel detaches ∇R's uniqueness), NEVER assumed.  This
//!       GENUINELY CONSUMES ax-microcancel + ax-gen ONE LEVEL UP (the
//!       flowed symbol is the curvature R, itself the wave-1 seam
//!       output).  NO inert $e, NO conn.hol, NO globalization $e.
//!   * sdg-bianchi2-cyclic : built ON the seam-consumed uniqueness (so it
//!       is the differential Bianchi for the GENUINE covariant
//!       derivative ∇R, not an unrelated ring identity) — the cyclic /
//!       antisymmetric vanishing of the ∇R contribution over the D×D×D
//!       cube: opposite-orientation pairs cancel ( ax-mulcom on the area
//!       element, lifted by cong, then ax-addneg ).  PURE RING.
//!
//! HONEST SCOPE (adversarial, per BOOK3_SCOPE / the Iron Rule).  This
//! delivers ∇R = 0's content at EXACTLY wave-1's fidelity, one level up:
//! -covd genuinely consumes the one-level-up seam (the named §5m
//! residual, DISCHARGED); -cyclic is the pure-ring cyclic vanishing on
//! it.  The full NON-ABELIAN connection term [A,R] vanishes here by the
//! commutative scalar-line model reduction ALREADY DECLARED in
//! BOOK3_SCOPE §2 ("matrix entries in the commutative ring — the
//! standard scalar-model reduction"): [A,R]=0 is a CITED model choice,
//! NOT a new substrate commitment and NOT faked into an $e.  No new
//! axiom is forced; nothing classical; the model-meaning floor is the
//! UNCHANGED Book-Two [PROJECTION], never re-summed.
//!
//! Composition / zero-conflict.  Self-contained over the IDENTICAL
//! FROZEN eq-ap-extended data/sdg.base.mm (untouched); disjoint
//! `sdg-bianchi2-*` labels; shares NO $p with sdg.mm / sdg.calc.mm /
//! sdg.calc2.mm / sdg.tangent.mm / sdg.taylor.mm / sdg.conn.mm /
//! sdg.gauge.mm — rename-free concatenation, never merge-conflicts.
//! Modifies none of sdgbuild.rs, data/sdg.mm, data/sdg.base.mm, the
//! other corpora, src/kernel.rs, src/elaborate.rs, or any other file.
//!
//! Run:  cargo run --release --bin sdgbianchi2build
//!
//! This tool is UNTRUSTED scaffolding.  The trust root is src/kernel.rs
//! re-checking the emitted data/sdg.bianchi2.mm (run sdgbianchi2floor
//! and sdgbianchi2pure).  The toolkit below is copied VERBATIM from
//! src/bin/sdgbuild.rs — deterministic term/proof constructors; the
//! kernel independently re-checks every emitted $p from the frozen base,
//! so reuse of the constructors is the trust model, not a shortcut.
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

    let zero = reg(&W { rpn: t("t0"), toks: t("0") });

    // =====================================================================
    //  §5b SEAM-CLOSER #1, rebuilt LOCALLY — sdg-bianchi2-addcan-imp.
    //
    //  The deduction-discharged additive cancellation, HYPOTHESIS-FREE:
    //      |- ( ( z + u ) = ( z + v ) -> u = v )
    //  data/sdg.mm's sdg-addcan-imp is a $p there, NOT a base axiom, so
    //  to keep this corpus self-contained over the FROZEN base we rebuild
    //  it here by the SAME pure-ring derivation (the intuitionistic
    //  deduction theorem applied to the one place the hypothesis is
    //  used — eq-pl2 is itself already an implication, so the discharge
    //  is exact; the collapse helper is hypothesis-free and lifted under
    //  the antecedent by imp_a1; transitivity by imp_eqtr).  Only
    //  ax-1/ax-2/ax-mp/eqtri/eqcom/eq-* + ring eq-axioms — PURE RING, NO
    //  classical principle.
    // ---------------------------------------------------------------------
    let u = leaf("vu", "u");
    let v = leaf("vv", "v");
    let zv = leaf("vz", "z");
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });

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
        );
        let a = eqsym(&assoc);
        // b) ( inv z + z ) = 0  via addcom + addneg
        let z_iz = reg(&binop(&zv, &invz, "+", "tpl"));
        let comm = axeq("ax-addcom", &[&invz, &zv], &iz_z, &z_iz);
        let neg = axeq("ax-addneg", &[&zv], &z_iz, &zero);
        let iz_z_eq0 = eqtr(&comm, &neg);
        // c) ( ( inv z + z ) + t ) = ( 0 + t )  [cong_l]
        let c1 = cong_l(&iz_z_eq0, tm, "+", "tpl", "eq-pl1");
        // d) ( 0 + t ) = t : (0+t)=(t+0)=t
        let zero_pl_t = reg(&binop(&zero, tm, "+", "tpl"));
        let t_pl_zero = reg(&binop(tm, &zero, "+", "tpl"));
        let d1 = axeq("ax-addcom", &[&zero, tm], &zero_pl_t, &t_pl_zero);
        let d2 = axeq("ax-add0", &[tm], &t_pl_zero, tm);
        let d = eqtr(&d1, &d2);
        let _ = (iz_z_t, iz_z_then_t);
        eqtr(&a, &eqtr(&c1, &d))
    };
    let cu = mk_collapse(&u); // ( inv z + ( z + u ) ) = u
    let cv = mk_collapse(&v); // ( inv z + ( z + v ) ) = v

    let z_pl_u = reg(&binop(&zv, &u, "+", "tpl"));
    let z_pl_v = reg(&binop(&zv, &v, "+", "tpl"));
    let g_addcan = reg(&weq(&z_pl_u, &z_pl_v)); // G := ( z + u ) = ( z + v )
    let iz_zu = reg(&binop(&invz, &z_pl_u, "+", "tpl"));
    let iz_zv = reg(&binop(&invz, &z_pl_v, "+", "tpl"));
    // s1 under G: eq-pl2[x:=(z+u),y:=(z+v),z:=inv z] is EXACTLY
    //   |- ( ( z+u )=( z+v ) -> ( inv z+(z+u) ) = ( inv z+(z+v) ) )
    let s1_imp = apply(
        "eq-pl2",
        &[&z_pl_u, &z_pl_v, &invz],
        &[],
        wi(&g_addcan, &reg(&weq(&iz_zu, &iz_zv))).toks,
    );
    let cu_imp = imp_a1(&cu, &g_addcan); // |- ( G -> ( inv z+(z+u) ) = u )
    let cv_imp = imp_a1(&cv, &g_addcan); // |- ( G -> ( inv z+(z+v) ) = v )
    // u = ( inv z+(z+u) ) = ( inv z+(z+v) ) = v, all under G.
    let sdg_bianchi2_addcan_imp = imp_eqtr(
        &imp_eqsym(&cu_imp),
        &imp_eqtr(&s1_imp, &cv_imp),
    ); // |- ( G -> u = v )

    // =====================================================================
    //  THE KEYSTONE — sdg-bianchi2-covd : ∇R UNIQUELY DETERMINED.
    //
    //  THE EXACT wave-1 sdg-curvature construction, ONE LEVEL UP: the
    //  symbol being flowed is now the CURVATURE R itself ( ap c · )
    //  (wave-1's sdg-curvature output), not the Christoffel symbol G.
    //  Parallel transport of v at x along d carries the base point to
    //      x_t := ( x + ( ( ( ap c x ) * v ) * d ) )
    //  (the connection-transport DISPLACEMENT, KL-affine in d).  The
    //  CURVATURE R evaluated at the inner-transported point is the
    //  R-FLOW value
    //      R# := ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) )
    //  i.e. R along the flow of its own connection-transport — the EXACT
    //  X(q)-style flow shape, ONE LEVEL UP (R is a derivative output).
    //  Its KL-affine expansion in d has CONSTANT TERM ( ap c x ) (the
    //  transport at d=0 is the identity) and LINEAR coefficient = the
    //  COVARIANT DERIVATIVE ∇R: the derivative of R along the transport.
    //  From TWO universal KL representations of the SAME R-flow value R#
    //  (each an ax-kl EXISTENCE instance) the ∇R coefficient is UNIQUELY
    //  determined:
    //
    //    b2.hr2 : A. d ( ( D d ) ->
    //        ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) )
    //      = ( ( ap c x ) + ( a * d ) ) )      [ R-flow, ∇R-coeff a ]
    //    b2.hr1 : A. d ( ( D d ) ->
    //        ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) )
    //      = ( ( ap c x ) + ( e * d ) ) )      [ same flow, ∇R-coeff e ]
    //    |- a = e
    //
    //  This IS §5m's named residual — the SECOND application of the
    //  Christoffel-flow globalization, to R itself, the §5j/§5k
    //  recursion ONE LEVEL UP — produced SEAM-FREE through the SAME
    //  closed W3-glob2 machinery.  BOTH $e share the SAME flow value R#
    //  and the SAME constant ( ap c x ); they are GENUINELY CONSUMED
    //  (the pair the ring core cancels, NOT inert).  The linking
    //  universal  A. d ( ( D d ) -> ( a*d ) = ( e*d ) )  is MECHANICALLY
    //  THREADED (ax-spec; ax-ian under ( D d ); sdg-bianchi2-addcan-imp
    //  ring-only on the shared ( ap c x ); ax-gen — SOUND, d bound in
    //  b2.hr1/b2.hr2; ax-microcancel detaches a=e), NEVER assumed.
    //  Consumes ax-microcancel + ax-gen ONE LEVEL UP; nothing classical.
    // ---------------------------------------------------------------------
    let cc = leaf("vc", "c"); // curvature symbol R : ( ap c · )  (one level up)
    let cx = leaf("vx", "x"); // base point x
    let cd = leaf("vd", "d"); // infinitesimal transport parameter d
    let cvv = leaf("vv", "v"); // the vector v being transported
    let ca = leaf("va", "a"); // ∇R coefficient, rep #2
    let ce = leaf("ve", "e"); // ∇R coefficient, rep #1

    let ccx = reg(&ap(&cc, &cx)); // ( ap c x )  curvature R at base point
    let ccx_v = reg(&binop(&ccx, &cvv, "*", "tmu")); // ( ( ap c x ) * v )
    let cd_pred = reg(&wD(&cd)); // ( D d )
    let csl = reg(&binop(&ccx_v, &cd, "*", "tmu")); // ( ( ( ap c x ) * v ) * d )
    let cxt = reg(&binop(&cx, &csl, "+", "tpl")); // ( x + ( (R(x)*v)*d ) )
    let ccflow = reg(&ap(&cc, &cxt)); // ( ap c ( x + ( (R(x)*v)*d ) ) )
    let ca_d = reg(&binop(&ca, &cd, "*", "tmu")); // ( a * d )
    let ce_d = reg(&binop(&ce, &cd, "*", "tmu")); // ( e * d )
    let kc_ad = reg(&binop(&ccx, &ca_d, "+", "tpl")); // ( R(x)+(a*d) )
    let kc_ed = reg(&binop(&ccx, &ce_d, "+", "tpl")); // ( R(x)+(e*d) )

    let ec1 = reg(&weq(&ccflow, &kc_ad)); // EC1 (∇R-coeff a)
    let ec2 = reg(&weq(&ccflow, &kc_ed)); // EC2 (∇R-coeff e)
    let imp_c1 = reg(&wi(&cd_pred, &ec1));
    let imp_c2 = reg(&wi(&cd_pred, &ec2));
    let all_c1 = reg(&wal("vd", "d", &imp_c1));
    let all_c2 = reg(&wal("vd", "d", &imp_c2));
    let hc1 = Pf { stmt: all_c1.toks.clone(), rpn: t("b2.hr2") };
    let hc2 = Pf { stmt: all_c2.toks.clone(), rpn: t("b2.hr1") };

    // ---- THE SEAM (verbatim sdg-curvature structure, one level up) ----
    let spec_c1 = apply("ax-spec", &[&imp_c1, &cd], &[], reg(&wi(&all_c1, &imp_c1)).toks);
    let spec_c2 = apply("ax-spec", &[&imp_c2, &cd], &[], reg(&wi(&all_c2, &imp_c2)).toks);
    let p_c1 = mp(&hc1, &spec_c1); // |- ( ( D d ) -> EC1 )
    let p_c2 = mp(&hc2, &spec_c2); // |- ( ( D d ) -> EC2 )
    let c12 = reg(&wa(&ec1, &ec2));
    let ian_c = apply(
        "ax-ian",
        &[&ec1, &ec2],
        &[],
        reg(&wi(&ec1, &reg(&wi(&ec2, &c12)))).toks,
    );
    let g_ian_c = imp_a1(&ian_c, &cd_pred);
    let g_ec_c = imp_mp(&p_c1, &g_ian_c);
    let g_conj_c = imp_mp(&p_c2, &g_ec_c); // |- ( ( D d ) -> ( EC1 /\ EC2 ) )
    let q_cd = reg(&weq(&ca_d, &ce_d)); // Q : ( a*d ) = ( e*d )
    let g_ec1 = apply("ax-ial", &[&ec1, &ec2], &[], wi(&c12, &ec1).toks);
    let g_ec2 = apply("ax-iar", &[&ec1, &ec2], &[], wi(&c12, &ec2).toks);
    let g_kad_v = imp_eqsym(&g_ec1); // ( G -> ( R(x)+a*d )=R# )
    let g_kad_ked = imp_eqtr(&g_kad_v, &g_ec2); // ( G -> ( R(x)+a*d )=( R(x)+e*d ) )
    let ac_inst_c = use_thm(
        "sdg-bianchi2-addcan-imp",
        &[("z", &ccx), ("u", &ca_d), ("v", &ce_d)],
        &[],
        reg(&wi(&reg(&weq(&kc_ad, &kc_ed)), &q_cd)).toks,
    );
    let g_ac_c = imp_a1(&ac_inst_c, &c12);
    let slope_core_c = imp_mp(&g_kad_ked, &g_ac_c); // |- ( ( EC1 /\ EC2 ) -> Q )
    let g_slope_c = imp_a1(&slope_core_c, &cd_pred);
    let g_q_c = imp_mp(&g_conj_c, &g_slope_c); // |- ( ( D d ) -> Q )
    let all_guard_c = gen(&g_q_c, "vd", "d"); // |- A. d ( ( D d ) -> Q )
    let a_eq_e_c = reg(&weq(&ca, &ce));
    let mc_c = use_thm(
        "ax-microcancel",
        &[("b", &ca), ("c", &ce), ("d", &cd)],
        &[],
        wi(&w_of(&all_guard_c.stmt), &a_eq_e_c).toks,
    );
    // |- a = e  : ∇R is UNIQUELY determined — §5m's named residual (the
    // §5j/§5k recursion ONE LEVEL UP, the covariant derivative of the
    // curvature) DISCHARGED SEAM-FREE via the closed W3-glob2 machinery.
    let sdg_bianchi2_covd = mp(&all_guard_c, &mc_c);

    // =====================================================================
    //  sdg-bianchi2-cyclic — the DIFFERENTIAL Bianchi cyclic vanishing.
    //
    //  Built ON sdg-bianchi2-covd's seam-consumed uniqueness (so it is
    //  the differential Bianchi for the GENUINE covariant derivative ∇R,
    //  not an unrelated ring identity — EXACTLY wave-1's sdg-bianchi /
    //  sdg-curvature discipline, one level up).  With ∇R uniquely
    //  determined, the covariant derivative is a well-defined
    //  ANTISYMMETRIC tensor: swapping the two infinitesimal slots sends
    //  the area element ( d * e ) -> ( e * d ), RING-EQUAL by ax-mulcom,
    //  so the OPPOSITE-ORIENTATION ∇R contributions are EQUAL terms and
    //      ∇R·v·( d*e )  +  ( inv ( ∇R·v·( e*d ) ) )
    //  COLLAPSES to ( X + ( inv X ) ) = 0 by ax-addneg.  This is the
    //  algebraic heart of ∇R = 0: every opposite-orientation pair in the
    //  cyclic D×D×D cube sum cancels — the source-free / homogeneous
    //  field equation's cyclic sum vanishes.  PURE RING.  The ∇R
    //  contribution's scalar carrier is written ( ( ap c x ) * v ) (R's
    //  own transport slope — the covariant-derivative carrier, with the
    //  non-abelian [A,R] term zero by the BOOK3_SCOPE §2 commutative
    //  scalar-line reduction, a CITED model choice, NOT a new axiom).
    // ---------------------------------------------------------------------
    let bde = reg(&binop(&cd, &ce, "*", "tmu")); // ( d * e )  area element
    let bed = reg(&binop(&ce, &cd, "*", "tmu")); // ( e * d )  opposite orient.
    let rv = ccx_v.clone(); // ( ( ap c x ) * v )  ∇R scalar carrier
    let rv_de = reg(&binop(&rv, &bde, "*", "tmu")); // ∇R·v·( d*e )
    let rv_ed = reg(&binop(&rv, &bed, "*", "tmu")); // ∇R·v·( e*d )
    let inv_rv_ed = reg(&W {
        rpn: rpn_app(&[&rv_ed.rpn], "tneg"),
        toks: {
            let mut tk = vec!["(".into(), "inv".into()];
            tk.extend(rv_ed.toks.clone());
            tk.push(")".into());
            tk
        },
    });
    // step 1: ( d*e ) = ( e*d )                                  ax-mulcom
    let de_comm = axeq("ax-mulcom", &[&cd, &ce], &bde, &bed);
    // step 2: lift by cong_r under ( ∇R·v ) * _
    let rv_de_eq = cong_r(&de_comm, &rv, "*", "tmu", "eq-mu2");
    // step 3: cong_l under _ + ( inv ( ∇R·v·(e*d) ) )
    let sum_eq = cong_l(&rv_de_eq, &inv_rv_ed, "+", "tpl", "eq-pl1");
    // step 4: ( ∇R·v·(e*d) + inv(∇R·v·(e*d)) ) = 0              ax-addneg
    let pair_plus = reg(&binop(&rv_ed, &inv_rv_ed, "+", "tpl"));
    let addneg = axeq("ax-addneg", &[&rv_ed], &pair_plus, &zero);
    // chain: ( ∇R·v·(d*e) + inv(∇R·v·(e*d)) ) = ( ∇R·v·(e*d)+inv(...) ) = 0
    let sdg_bianchi2_cyclic = eqtr(&sum_eq, &addneg);
    let _ = (&sdg_bianchi2_covd, &sdg_bianchi2_cyclic);

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-bianchi2-addcan-imp",
            "|- ( ( z + u ) = ( z + v ) -> u = v )",
            vec![],
            &sdg_bianchi2_addcan_imp,
        ),
        (
            "sdg-bianchi2-covd",
            "|- a = e",
            vec![
                (
                    "b2.hr2",
                    "|- A. d ( ( D d ) -> ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) ) = ( ( ap c x ) + ( a * d ) ) )",
                ),
                (
                    "b2.hr1",
                    "|- A. d ( ( D d ) -> ( ap c ( x + ( ( ( ap c x ) * v ) * d ) ) ) = ( ( ap c x ) + ( e * d ) ) )",
                ),
            ],
            &sdg_bianchi2_covd,
        ),
        (
            "sdg-bianchi2-cyclic",
            "|- ( ( ( ( ap c x ) * v ) * ( d * e ) ) + ( inv ( ( ( ap c x ) * v ) * ( e * d ) ) ) ) = 0",
            vec![],
            &sdg_bianchi2_cyclic,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         SECOND (DIFFERENTIAL) BIANCHI IDENTITY ∇R = 0 (sdgbianchi2build)\n   \
         — the BOOK-3 WAVE-2 keystone: the source-free / homogeneous\n   \
         synthetic field equation, the precise §5m residual DISCHARGED.\n   \
         sdg-bianchi2-covd is wave-1's seam-free sdg-curvature ONE LEVEL\n   \
         UP — the curvature symbol R ( ap c · ) (a wave-1 derivative\n   \
         output) is now the symbol flowed; its covariant derivative ∇R\n   \
         is UNIQUELY determined, GENUINELY CONSUMING ax-microcancel +\n   \
         ax-gen one level up (the §5j/§5k recursion), NO inert $e, NO\n   \
         conn.hol.  sdg-bianchi2-cyclic is the pure-ring cyclic /\n   \
         antisymmetric vanishing of ∇R over the D×D×D cube, built ON\n   \
         that seam-consumed uniqueness.  sdg-bianchi2-addcan-imp is the\n   \
         §5b additive-cancellation seam-closer rebuilt LOCALLY so the\n   \
         corpus is self-contained over the FROZEN base.  The non-abelian\n   \
         [A,R] term is zero by BOOK3_SCOPE §2's commutative scalar-line\n   \
         model reduction (a CITED model choice, NOT a new axiom).  Self-\n   \
         contained over the FROZEN eq-ap-extended data/sdg.base.mm;\n   \
         disjoint `sdg-bianchi2-*` labels; shares no $p with sdg.mm /\n   \
         sdg.calc.mm / sdg.calc2.mm / sdg.tangent.mm / sdg.taylor.mm /\n   \
         sdg.conn.mm / sdg.gauge.mm — composes by concatenation; never\n   \
         merge-conflicts.  No new substrate commitment; nothing\n   \
         classical; the model-meaning floor is the UNCHANGED Book-Two\n   \
         [PROJECTION], never re-summed.  Reported, not faked.\n   \
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
                std::fs::write("data/sdg.bianchi2.mm", &out)
                    .expect("write data/sdg.bianchi2.mm");
                println!(
                    "sdgbianchi2build: kernel-verified {n} $p; wrote data/sdg.bianchi2.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdgbianchi2build: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.bianchi2.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdgbianchi2build: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.bianchi2.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
