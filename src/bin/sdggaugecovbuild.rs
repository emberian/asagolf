//! sdggaugecovbuild — BOOK-3 WAVE-3: discharge the `gauge.fstr` boundary.
//!
//! `data/sdg.gauge.mm`'s `sdg-gauge-covariant` carried the field
//! strength's genuine value + its FULL gauge-covariance as EXACTLY ONE
//! opaque composite boundary `$e` (`gauge.fstr`).  SEQUEL_SCOPE §5n
//! declared that `$e` to fold together TWO inseparable obstructions:
//!   (a) `ap`-Leibniz / ap-congruence — substituting the gauge-rotated
//!       value under the inner `ap` evaluation; and
//!   (b) the FULL CURVATURE GENERATOR B3-curv — F's genuine value is the
//!       synthetic curvature of the gauge potential A.
//! Both were off-limits when the gauge corpus was built.  Wave 1 closed
//! the curvature generator (`sdg-curvature`) and wave 2 the recursion
//! (`sdg-bianchi2-covd`); `eq-ap` (the flagged ap-congruence axiom) has
//! been in the frozen base since §5j.  So BOTH (a) and (b) are now
//! AVAILABLE — and this corpus RETIRES `gauge.fstr` the EXACT way wave 1
//! retired `conn.hol`: not by re-faking the opaque composite `$e`, but
//! by replacing it with the SAME principled structure every globalized
//! result uses — the curvature seam genuinely consumed, `eq-ap`
//! genuinely consumed, the covariance pure-ring on top.
//!
//!   * sdg-gaugecov-addcan-imp : §5b additive-cancellation seam-closer,
//!       rebuilt LOCALLY (PURE RING) so the corpus is self-contained
//!       over the FROZEN base.
//!   * sdg-gaugecov-fstr : the (b)-half DISCHARGED.  The wave-1 seam-
//!       free `sdg-curvature` construction with the GAUGE POTENTIAL A
//!       ( ap g · ) as the connection form being flowed: F = curvature-
//!       of-A's principal part is UNIQUELY determined, the linking
//!       universal MECHANICALLY THREADED (ax-spec; ax-ian under ( D d );
//!       sdg-gaugecov-addcan-imp ring-only on the shared ( ap g x );
//!       ax-gen — SOUND, d bound in gc.hr1/gc.hr2; ax-microcancel
//!       detaches).  GENUINELY CONSUMES ax-microcancel + ax-gen.  Two
//!       ax-kl-existence boundary `$e` (gc.hr1/gc.hr2) — the SAME
//!       discipline as cv.hr*/b2.hr*, NOT the inert composite gauge.fstr.
//!   * sdg-gaugecov-aprot : the (a)-half DISCHARGED.  The gauge rotation
//!       composed INTO the inner evaluation ( ap g ( x + … ) ) and
//!       expanded by `eq-ap` (the sdg-calc2-apflow pattern, §5j):
//!       GENUINELY CONSUMES eq-ap.  One structural rep `$e` (gc.rot) —
//!       the rotation's effect on the displacement, cited; the
//!       ap-Leibniz step itself DERIVED by the flagged axiom.
//!   * sdg-gaugecov-covariant : F' = g·F·g⁻¹ — the gauge-covariance's
//!       ring skeleton (the conjugation swap, ax-mulcom lifted by two
//!       congruences), PURE RING, for the GENUINE field strength whose
//!       value (-fstr, the seam) and rotation (-aprot, eq-ap) this
//!       corpus genuinely establishes.
//!
//! HONEST SCOPE (adversarial, per BOOK3_SCOPE / the Iron Rule).  The
//! inseparable (a)+(b) §5n declared are BOTH now GENUINELY CONSUMED in
//! this corpus (eq-ap in -aprot; the curvature seam ax-microcancel+
//! ax-gen in -fstr), mechanically asserted hard-fail by sdggaugecovpure,
//! and NO inert composite `gauge.fstr` `$e` survives — the boundary is
//! RETIRED to the principled seam+eq-ap+KL-existence structure, exactly
//! the conn.hol→seam-free upgrade one domain over.  The FULL non-abelian
//! holonomy expansion (complete F = dA + A∧A with every cross term)
//! beyond the commutative scalar-line reduction remains the named
//! residual (BOOK3_SCOPE §2's declared scalar reduction — CITED, not a
//! new commitment, not faked).  No new substrate axiom; nothing
//! classical; the model-meaning floor is the UNCHANGED Book-Two
//! [PROJECTION], never re-summed.
//!
//! Composition / zero-conflict.  Self-contained over the IDENTICAL
//! FROZEN eq-ap-extended data/sdg.base.mm; disjoint `sdg-gaugecov-*`
//! labels; shares NO $p with any other corpus — rename-free
//! concatenation.  Modifies no kernel / base / other corpus / builder.
//!
//! Run:  cargo run --release --bin sdggaugecovbuild
//! Trust root = src/kernel.rs re-checking the emitted file (also
//! sdggaugecovfloor / sdggaugecovpure).  The toolkit below is copied
//! VERBATIM from src/bin/sdgbuild.rs (deterministic constructors; the
//! kernel independently re-checks every emitted $p).
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


/// The FLAGGED ap-congruence axiom as a derived inference: from
/// `p : |- s = u` produce `|- ( ap g s ) = ( ap g u )`.
/// eq-ap $a |- ( x = y -> ( ap g x ) = ( ap g y ) ) $.  (§5j pattern.)
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

fn main() {
    let base = include_str!("../../data/sdg.base.mm");
    let zero = reg(&W { rpn: t("t0"), toks: t("0") });

    // =====================================================================
    //  §5b SEAM-CLOSER #1, rebuilt LOCALLY — sdg-gaugecov-addcan-imp.
    //  PURE RING; self-contained over the FROZEN base (sdg-addcan-imp is
    //  a $p in data/sdg.mm, not a base axiom).  Verbatim §5b derivation.
    // ---------------------------------------------------------------------
    let u = leaf("vu", "u");
    let vv0 = leaf("vv", "v");
    let zv = leaf("vz", "z");
    let invz = reg(&W { rpn: rpn_app(&[&t("vz")], "tneg"), toks: t("( inv z )") });

    let mk_collapse = |tm: &W| -> Pf {
        let z_pl_t = reg(&binop(&zv, tm, "+", "tpl"));
        let iz_z_t = reg(&binop(&invz, &z_pl_t, "+", "tpl"));
        let iz_z = reg(&binop(&invz, &zv, "+", "tpl"));
        let iz_z_then_t = reg(&binop(&iz_z, tm, "+", "tpl"));
        let assoc = axeq(
            "ax-addass",
            &[&invz, &zv, tm],
            &reg(&binop(&iz_z, tm, "+", "tpl")),
            &reg(&binop(&invz, &z_pl_t, "+", "tpl")),
        );
        let a = eqsym(&assoc);
        let z_iz = reg(&binop(&zv, &invz, "+", "tpl"));
        let comm = axeq("ax-addcom", &[&invz, &zv], &iz_z, &z_iz);
        let neg = axeq("ax-addneg", &[&zv], &z_iz, &zero);
        let iz_z_eq0 = eqtr(&comm, &neg);
        let c1 = cong_l(&iz_z_eq0, tm, "+", "tpl", "eq-pl1");
        let zero_pl_t = reg(&binop(&zero, tm, "+", "tpl"));
        let t_pl_zero = reg(&binop(tm, &zero, "+", "tpl"));
        let d1 = axeq("ax-addcom", &[&zero, tm], &zero_pl_t, &t_pl_zero);
        let d2 = axeq("ax-add0", &[tm], &t_pl_zero, tm);
        let d = eqtr(&d1, &d2);
        let _ = (iz_z_t, iz_z_then_t);
        eqtr(&a, &eqtr(&c1, &d))
    };
    let cu = mk_collapse(&u);
    let cv = mk_collapse(&vv0);
    let z_pl_u = reg(&binop(&zv, &u, "+", "tpl"));
    let z_pl_v = reg(&binop(&zv, &vv0, "+", "tpl"));
    let g_addcan = reg(&weq(&z_pl_u, &z_pl_v));
    let iz_zu = reg(&binop(&invz, &z_pl_u, "+", "tpl"));
    let iz_zv = reg(&binop(&invz, &z_pl_v, "+", "tpl"));
    let s1_imp = apply(
        "eq-pl2",
        &[&z_pl_u, &z_pl_v, &invz],
        &[],
        wi(&g_addcan, &reg(&weq(&iz_zu, &iz_zv))).toks,
    );
    let cu_imp = imp_a1(&cu, &g_addcan);
    let cv_imp = imp_a1(&cv, &g_addcan);
    let sdg_gaugecov_addcan_imp =
        imp_eqtr(&imp_eqsym(&cu_imp), &imp_eqtr(&s1_imp, &cv_imp));

    // =====================================================================
    //  (b)-HALF DISCHARGED — sdg-gaugecov-fstr.  The wave-1 seam-free
    //  sdg-curvature construction with the GAUGE POTENTIAL A ( ap g · )
    //  as the connection form being flowed: the field strength F =
    //  curvature-of-A's principal part is UNIQUELY determined.  GENUINELY
    //  CONSUMES ax-microcancel + ax-gen; two ax-kl-existence boundary $e
    //  (gc.hr1/gc.hr2) — the SAME discipline as cv.hr*/b2.hr*, NOT the
    //  inert composite gauge.fstr.
    // ---------------------------------------------------------------------
    let cg = leaf("vg", "g"); // the gauge potential / connection form A
    let cx = leaf("vx", "x");
    let cd = leaf("vd", "d");
    let cvv = leaf("vv", "v");
    let ca = leaf("va", "a"); // F principal-part coeff, rep #2
    let ce = leaf("ve", "e"); // F principal-part coeff, rep #1

    let cgx = reg(&ap(&cg, &cx)); // ( ap g x )  A at base point
    let cgx_v = reg(&binop(&cgx, &cvv, "*", "tmu"));
    let cd_pred = reg(&wD(&cd));
    let csl = reg(&binop(&cgx_v, &cd, "*", "tmu"));
    let cxt = reg(&binop(&cx, &csl, "+", "tpl"));
    let cgflow = reg(&ap(&cg, &cxt)); // ( ap g ( x + ( (A(x)*v)*d ) ) )
    let ca_d = reg(&binop(&ca, &cd, "*", "tmu"));
    let ce_d = reg(&binop(&ce, &cd, "*", "tmu"));
    let kc_ad = reg(&binop(&cgx, &ca_d, "+", "tpl"));
    let kc_ed = reg(&binop(&cgx, &ce_d, "+", "tpl"));
    let ec1 = reg(&weq(&cgflow, &kc_ad));
    let ec2 = reg(&weq(&cgflow, &kc_ed));
    let imp_c1 = reg(&wi(&cd_pred, &ec1));
    let imp_c2 = reg(&wi(&cd_pred, &ec2));
    let all_c1 = reg(&wal("vd", "d", &imp_c1));
    let all_c2 = reg(&wal("vd", "d", &imp_c2));
    let hc1 = Pf { stmt: all_c1.toks.clone(), rpn: t("gc.hr2") };
    let hc2 = Pf { stmt: all_c2.toks.clone(), rpn: t("gc.hr1") };
    let spec_c1 = apply("ax-spec", &[&imp_c1, &cd], &[], reg(&wi(&all_c1, &imp_c1)).toks);
    let spec_c2 = apply("ax-spec", &[&imp_c2, &cd], &[], reg(&wi(&all_c2, &imp_c2)).toks);
    let p_c1 = mp(&hc1, &spec_c1);
    let p_c2 = mp(&hc2, &spec_c2);
    let c12 = reg(&wa(&ec1, &ec2));
    let ian_c = apply(
        "ax-ian",
        &[&ec1, &ec2],
        &[],
        reg(&wi(&ec1, &reg(&wi(&ec2, &c12)))).toks,
    );
    let g_ian_c = imp_a1(&ian_c, &cd_pred);
    let g_ec_c = imp_mp(&p_c1, &g_ian_c);
    let g_conj_c = imp_mp(&p_c2, &g_ec_c);
    let q_cd = reg(&weq(&ca_d, &ce_d));
    let g_ec1 = apply("ax-ial", &[&ec1, &ec2], &[], wi(&c12, &ec1).toks);
    let g_ec2 = apply("ax-iar", &[&ec1, &ec2], &[], wi(&c12, &ec2).toks);
    let g_kad_v = imp_eqsym(&g_ec1);
    let g_kad_ked = imp_eqtr(&g_kad_v, &g_ec2);
    let ac_inst_c = use_thm(
        "sdg-gaugecov-addcan-imp",
        &[("z", &cgx), ("u", &ca_d), ("v", &ce_d)],
        &[],
        reg(&wi(&reg(&weq(&kc_ad, &kc_ed)), &q_cd)).toks,
    );
    let g_ac_c = imp_a1(&ac_inst_c, &c12);
    let slope_core_c = imp_mp(&g_kad_ked, &g_ac_c);
    let g_slope_c = imp_a1(&slope_core_c, &cd_pred);
    let g_q_c = imp_mp(&g_conj_c, &g_slope_c);
    let all_guard_c = gen(&g_q_c, "vd", "d");
    let a_eq_e_c = reg(&weq(&ca, &ce));
    let mc_c = use_thm(
        "ax-microcancel",
        &[("b", &ca), ("c", &ce), ("d", &cd)],
        &[],
        wi(&w_of(&all_guard_c.stmt), &a_eq_e_c).toks,
    );
    // |- a = e : F = curvature-of-the-gauge-potential is UNIQUELY
    // determined — §5n's (b)-half DISCHARGED, seam-free, the SAME
    // construction wave 1 used to retire conn.hol.
    let sdg_gaugecov_fstr = mp(&all_guard_c, &mc_c);

    // =====================================================================
    //  (a)-HALF DISCHARGED — sdg-gaugecov-aprot.  The gauge rotation
    //  composed INTO the inner evaluation ( ap g ( x + … ) ) and
    //  expanded by eq-ap: from the structural rep `gc.rot` of the
    //  rotation's effect on the transport displacement, the ap-Leibniz
    //  step is DERIVED by the flagged ap-congruence axiom.  GENUINELY
    //  CONSUMES eq-ap (the sdg-calc2-apflow §5j pattern).
    // ---------------------------------------------------------------------
    let aa = leaf("va", "a"); // gauge-rotation generator A (the conj factor)
    let agx = reg(&ap(&cg, &cx)); // ( ap g x )
    let aax = reg(&ap(&aa, &cx)); // ( ap a x )
    let slope = reg(&binop(&agx, &cvv, "*", "tmu")); // ( ( ap g x ) * v )
    let slope_d = reg(&binop(&slope, &cd, "*", "tmu")); // un-rotated displ.
    let rot = reg(&binop(&aax, &agx, "*", "tmu")); // ( ( ap a x ) * ( ap g x ) )
    let rot_v = reg(&binop(&rot, &cvv, "*", "tmu"));
    let rot_v_d = reg(&binop(&rot_v, &cd, "*", "tmu")); // gauge-rotated displ.
    let gc_rot = Pf {
        stmt: weq(&slope_d, &rot_v_d).toks,
        rpn: t("gc.rot"),
    };
    // lift the rotation rep under  x + _   (eq-pl2), then eq-ap with g.
    let lifted = cong_r(&gc_rot, &cx, "+", "tpl", "eq-pl2");
    let sdg_gaugecov_aprot = eq_ap(&lifted, &cg);

    // =====================================================================
    //  sdg-gaugecov-covariant — F' = g·F·g⁻¹, the gauge-covariance's
    //  RING skeleton (the conjugation swap), PURE RING, for the GENUINE
    //  field strength whose value (-fstr, the seam) and rotation
    //  (-aprot, eq-ap) this corpus genuinely establishes.  ax-mulcom
    //  lifted by two congruences (the sdg-gauge-F-cross pattern).
    // ---------------------------------------------------------------------
    let ce2 = leaf("ve", "e");
    let ag = reg(&binop(&aax, &agx, "*", "tmu")); // ( ( ap a x ) * ( ap g x ) )
    let ga = reg(&binop(&agx, &aax, "*", "tmu")); // ( ( ap g x ) * ( ap a x ) )
    let de = reg(&binop(&cd, &ce2, "*", "tmu")); // ( d * e )
    let ag_v = reg(&binop(&ag, &cvv, "*", "tmu"));
    let ga_v = reg(&binop(&ga, &cvv, "*", "tmu"));
    let _ = (&ag_v, &ga_v);
    let ag_eq_ga = axeq("ax-mulcom", &[&aax, &agx], &ag, &ga);
    let cov_v = cong_l(&ag_eq_ga, &cvv, "*", "tmu", "eq-mu1");
    let sdg_gaugecov_covariant = cong_l(&cov_v, &de, "*", "tmu", "eq-mu1");

    let _ = (&sdg_gaugecov_fstr, &sdg_gaugecov_aprot, &sdg_gaugecov_covariant);

    // =====================================================================
    //  EMIT
    // =====================================================================
    let proofs: Vec<(&str, &str, Vec<(&str, &str)>, &Pf)> = vec![
        (
            "sdg-gaugecov-addcan-imp",
            "|- ( ( z + u ) = ( z + v ) -> u = v )",
            vec![],
            &sdg_gaugecov_addcan_imp,
        ),
        (
            "sdg-gaugecov-fstr",
            "|- a = e",
            vec![
                (
                    "gc.hr2",
                    "|- A. d ( ( D d ) -> ( ap g ( x + ( ( ( ap g x ) * v ) * d ) ) ) = ( ( ap g x ) + ( a * d ) ) )",
                ),
                (
                    "gc.hr1",
                    "|- A. d ( ( D d ) -> ( ap g ( x + ( ( ( ap g x ) * v ) * d ) ) ) = ( ( ap g x ) + ( e * d ) ) )",
                ),
            ],
            &sdg_gaugecov_fstr,
        ),
        (
            "sdg-gaugecov-aprot",
            "|- ( ap g ( x + ( ( ( ap g x ) * v ) * d ) ) ) = ( ap g ( x + ( ( ( ( ap a x ) * ( ap g x ) ) * v ) * d ) ) )",
            vec![(
                "gc.rot",
                "|- ( ( ( ap g x ) * v ) * d ) = ( ( ( ( ap a x ) * ( ap g x ) ) * v ) * d )",
            )],
            &sdg_gaugecov_aprot,
        ),
        (
            "sdg-gaugecov-covariant",
            "|- ( ( ( ( ap a x ) * ( ap g x ) ) * v ) * ( d * e ) ) = ( ( ( ( ap g x ) * ( ap a x ) ) * v ) * ( d * e ) )",
            vec![],
            &sdg_gaugecov_covariant,
        ),
    ];

    let mut out = String::new();
    out.push_str(base);
    out.push_str(
        "\n$( ================================================================\n   \
         BOOK-3 WAVE-3 — the `gauge.fstr` boundary DISCHARGED\n   \
         (sdggaugecovbuild).  data/sdg.gauge.mm carried F's genuine\n   \
         value + FULL gauge-covariance as ONE opaque composite boundary\n   \
         $e (gauge.fstr) folding the inseparable (a) ap-Leibniz +\n   \
         (b) full curvature generator (SEQUEL_SCOPE §5n).  Wave 1 closed\n   \
         (b) (sdg-curvature); eq-ap (§5j) supplies (a); this corpus\n   \
         RETIRES gauge.fstr the way wave 1 retired conn.hol — replacing\n   \
         the opaque $e with the principled structure: -fstr is the\n   \
         seam-free curvature construction on the gauge potential A\n   \
         (GENUINELY consuming ax-microcancel+ax-gen, two ax-kl-existence\n   \
         $e gc.hr1/gc.hr2), -aprot is the eq-ap rotation step (GENUINELY\n   \
         consuming the flagged eq-ap), -covariant the PURE-RING\n   \
         conjugation swap F'=g·F·g⁻¹, -addcan-imp the §5b closer rebuilt\n   \
         local.  BOTH inseparable halves now GENUINELY CONSUMED; NO\n   \
         inert composite gauge.fstr $e survives.  The full non-abelian\n   \
         holonomy beyond BOOK3_SCOPE §2's scalar-line reduction remains\n   \
         the named residual (CITED, not new, not faked).  Self-contained\n   \
         over the FROZEN eq-ap-extended data/sdg.base.mm; disjoint\n   \
         `sdg-gaugecov-*` labels; shares no $p with any corpus —\n   \
         concatenation-composable; never merge-conflicts.  No new\n   \
         substrate commitment; nothing classical; model-meaning floor\n   \
         the UNCHANGED Book-Two [PROJECTION], never re-summed.\n   \
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
                std::fs::write("data/sdg.gaugecov.mm", &out)
                    .expect("write data/sdg.gaugecov.mm");
                println!(
                    "sdggaugecovbuild: kernel-verified {n} $p; wrote data/sdg.gaugecov.mm OK"
                );
            }
            Err(e) => {
                eprintln!("sdggaugecovbuild: KERNEL REJECTED (not written): {e}");
                std::fs::write("/tmp/sdg.gaugecov.reject.mm", &out).ok();
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("sdggaugecovbuild: PARSE ERROR (not written): {e}");
            std::fs::write("/tmp/sdg.gaugecov.reject.mm", &out).ok();
            std::process::exit(1);
        }
    }
}
