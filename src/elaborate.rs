//! Proof elaborator: builds Metamath proof-terms programmatically, computes
//! their conclusions by substitution (no string parser), emits RPN, and hands
//! the result to the sound kernel as the correctness oracle.
//!
//! A `Pt` (proof-term) is uniform: `{ label, kids }` where `kids` line up with
//! the label's mandatory hypotheses in Metamath order. Syntax trees and
//! logical derivations are the same structure — a wff variable `ph` is just
//! the proof-term `Pt{ "wph", [] }` (its floating hypothesis).
//!
//! Conclusion of a `Pt` = substitute the `$f`-kid conclusions into the
//! statement's expression. This is exact and needs no grammar/parser; the
//! kernel independently re-checks every step, so elaborator bugs cannot
//! produce an unsound "proof" — they produce a kernel rejection.

use crate::kernel::{Db, Kind};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Pt {
    pub label: String,
    pub kids: Vec<Pt>,
}

pub fn pt(label: &str, kids: Vec<Pt>) -> Pt {
    Pt {
        label: label.to_string(),
        kids,
    }
}
/// A leaf proof-term (variable `$f`, nullary constructor, or `$e` hypothesis).
pub fn leaf(label: &str) -> Pt {
    pt(label, vec![])
}

/// A grammar production: a syntax-constructor `$a` (typecode ≠ `|-`).
struct Ctor {
    label: String,
    result_tc: String,
    body: Vec<String>,
    /// hole variable names, in mandatory-hypothesis ($f) order.
    holes: Vec<String>,
}

pub struct Elab<'a> {
    db: &'a Db,
    /// variable name -> ($f label, typecode)
    vars: HashMap<String, (String, String)>,
    ctors: Vec<Ctor>,
}

impl<'a> Elab<'a> {
    pub fn new(db: &'a Db) -> Self {
        let mut vars = HashMap::new();
        let mut ctors = Vec::new();
        for st in &db.stmts {
            match st.kind {
                Kind::F => {
                    // expr = [typecode, var]
                    vars.insert(
                        st.expr[1].clone(),
                        (st.label.clone(), st.expr[0].clone()),
                    );
                }
                Kind::A if st.expr.first().map(|s| s.as_str()) != Some("|-") => {
                    // syntax constructor (wff/term/atomic); holes are its $f
                    // mandatory hyps, in order.
                    let holes: Vec<String> = st
                        .mand_hyps
                        .iter()
                        .filter_map(|h| {
                            let hs = db.get(h).unwrap();
                            (hs.kind == Kind::F).then(|| hs.expr[1].clone())
                        })
                        .collect();
                    ctors.push(Ctor {
                        label: st.label.clone(),
                        result_tc: st.expr[0].clone(),
                        body: st.expr[1..].to_vec(),
                        holes,
                    });
                }
                _ => {}
            }
        }
        Elab { db, vars, ctors }
    }

    /// Grammar-directed parse: token slice -> syntax `Pt` of the expected
    /// typecode, returning (tree, tokens consumed). Recursive descent with
    /// backtracking over the constructor grammar; our fully-parenthesised
    /// notation makes the first full match unique in practice.
    fn parse_at(&self, tc: &str, toks: &[String], pos: usize) -> Option<(Pt, usize)> {
        // 1. a bare variable of the expected typecode -> its $f leaf.
        if pos < toks.len() {
            if let Some((flab, vtc)) = self.vars.get(&toks[pos]) {
                if vtc == tc {
                    return Some((leaf(flab), pos + 1));
                }
            }
        }
        // 2. a constructor producing this typecode.
        'ctor: for c in &self.ctors {
            if c.result_tc != tc {
                continue;
            }
            let mut cur = pos;
            let mut kids: HashMap<String, Pt> = HashMap::new();
            for bt in &c.body {
                if c.holes.contains(bt) {
                    let htc = &self.vars[bt].1;
                    match self.parse_at(htc, toks, cur) {
                        Some((kid, nc)) => {
                            kids.insert(bt.clone(), kid);
                            cur = nc;
                        }
                        None => continue 'ctor,
                    }
                } else {
                    if cur >= toks.len() || &toks[cur] != bt {
                        continue 'ctor;
                    }
                    cur += 1;
                }
            }
            let ordered = c.holes.iter().map(|h| kids[h].clone()).collect();
            return Some((
                Pt {
                    label: c.label.clone(),
                    kids: ordered,
                },
                cur,
            ));
        }
        None
    }

    /// Parse a full `wff` token slice (no leading typecode) into a `Pt`.
    fn parse_wff(&self, toks: &[String]) -> Result<Pt, String> {
        match self.parse_at("wff", toks, 0) {
            Some((p, n)) if n == toks.len() => Ok(p),
            _ => Err(format!("cannot parse wff `{}`", toks.join(" "))),
        }
    }

    /// Load-time grammar lint (untrusted convenience — the Metamath kernel
    /// remains the sole trust root and still independently re-checks every
    /// proof). Grammar-parses every `|-` assertion / `$e` hypothesis against
    /// the constructor grammar so a malformed statement (parenthesised
    /// `weq`, unparenthesised `tle`, …) is reported at load instead of only
    /// when it is first *used* in a proof (which historically cost many
    /// kernel-debug cycles: df-coll, ptext, of-recip, ax-sqrt, of-sqrtnn).
    /// `$f` floating hyps and the `term`/`wff` syntax constructors *define*
    /// the grammar and are skipped.
    pub fn lint(&self) -> Vec<String> {
        let mut out = Vec::new();
        for st in &self.db.stmts {
            if st.expr.first().map(|s| s.as_str()) != Some("|-") {
                continue;
            }
            if let Err(e) = self.parse_wff(&st.expr[1..]) {
                out.push(format!("{}: {}", st.label, e));
            }
        }
        out
    }

    /// The two operands of a top-level binary `wff` constructor whose body is
    /// `( A op B )` or `A op B`, identified structurally by `op`.
    fn split_binop(&self, concl: &[String], op: &str) -> Result<(Pt, Pt), String> {
        if concl.first().map(|s| s.as_str()) != Some("|-") {
            return Err(format!("expected `|-`, got `{}`", concl.join(" ")));
        }
        let p = self.parse_wff(&concl[1..])?;
        // find the constructor used and check its body's top operator is `op`
        let c = self
            .ctors
            .iter()
            .find(|c| c.label == p.label)
            .ok_or_else(|| format!("`{}` is not a wff constructor", p.label))?;
        if !c.body.contains(&op.to_string()) || p.kids.len() != 2 {
            return Err(format!(
                "top of `{}` is not `{op}`",
                concl[1..].join(" ")
            ));
        }
        Ok((p.kids[0].clone(), p.kids[1].clone()))
    }

    /// Antecedent / consequent of a `|- ( A -> B )`.
    pub fn split_imp(&self, concl: &[String]) -> Result<(Pt, Pt), String> {
        self.split_binop(concl, "->")
    }
    /// Sides of a `|- A = B`.
    pub fn split_eq(&self, concl: &[String]) -> Result<(Pt, Pt), String> {
        self.split_binop(concl, "=")
    }
    /// Sides of a `|- ( A <-> B )`.
    pub fn split_bi(&self, concl: &[String]) -> Result<(Pt, Pt), String> {
        self.split_binop(concl, "<->")
    }

    /// Eliminate a (possibly nested) implication: given `maj` proving
    /// `( A1 -> ( A2 -> ... -> C ) )` and proofs of `A1..An`, return a proof
    /// of the remaining consequent. `ph`/`ps` are inferred by parsing — no
    /// hand-built wff scaffolds.
    pub fn imp_elim(&self, maj: Pt, args: &[Pt]) -> Result<Pt, String> {
        let mut cur = maj;
        for a in args {
            let c = self.conclusion(&cur)?;
            let (ant, cons) = self.split_imp(&c)?;
            cur = self.app(
                "ax-mp",
                &[("ph", ant), ("ps", cons)],
                &[a.clone(), cur.clone()],
            )?;
        }
        Ok(cur)
    }

    /// Chain equalities `a=b, b=c, ..., y=z` into `a=z` via the `eqtr` lemma
    /// (which must be defined in the database).
    pub fn eqtr_chain(&self, steps: &[Pt]) -> Result<Pt, String> {
        let mut acc = steps
            .first()
            .cloned()
            .ok_or("eqtr_chain: empty")?;
        for nxt in &steps[1..] {
            let (l, m) = self.split_eq(&self.conclusion(&acc)?)?;
            let (_m2, n) = self.split_eq(&self.conclusion(nxt)?)?;
            acc = self.app(
                "eqtr",
                &[("x", l), ("y", m), ("z", n)],
                &[acc.clone(), nxt.clone()],
            )?;
        }
        Ok(acc)
    }

    /// Forward biconditional elimination: `( ph <-> ps )`, `ph` ⊢ `ps`
    /// (needs `ax-bi1` in the database).
    pub fn bi_fwd(&self, bi: Pt, ph: Pt) -> Result<Pt, String> {
        let (p, q) = self.split_bi(&self.conclusion(&bi)?)?;
        let fwd = self.app("ax-bi1", &[("ph", p), ("ps", q)], &[])?;
        self.imp_elim(fwd, &[bi, ph])
    }
    /// Reverse biconditional elimination: `( ph <-> ps )`, `ps` ⊢ `ph`
    /// (needs `ax-bi2`).
    pub fn bi_rev(&self, bi: Pt, ps: Pt) -> Result<Pt, String> {
        let (p, q) = self.split_bi(&self.conclusion(&bi)?)?;
        let rev = self.app("ax-bi2", &[("ph", p), ("ps", q)], &[])?;
        self.imp_elim(rev, &[bi, ps])
    }

    // ====================================================================
    // Deduction-form combinator library.
    //
    // The methods below are *untrusted convenience*: they assemble ordinary
    // `Pt` proof-terms out of the same Hilbert-system lemmas a hand proof
    // would, so the sound kernel still independently re-checks every emitted
    // step. They exist because the same patterns were rediscovered by hand
    // across the G1/G2/G3a derivations; promoting them here lets future
    // proofs (and a maintainer) compose instead of re-derive. Each carries a
    // precise in/out judgement; all `wff`/`term` scaffolds are recovered by
    // parsing the premises' conclusions, never hand-built.
    // ====================================================================

    /// Parse the `wff` payload of a `|- W` conclusion into its syntax `Pt`.
    /// (The dual of `assertion`, which goes `wff` → `|-`.)
    fn wff_of(&self, concl: &[String]) -> Result<Pt, String> {
        if concl.first().map(|s| s.as_str()) != Some("|-") {
            return Err(format!("expected `|-`, got `{}`", concl.join(" ")));
        }
        self.parse_wff(&concl[1..])
    }

    /// **`imp_of_ess`** — lift a closed/ess-form fact into composable
    /// implication form: given `inner : |- C` and an antecedent wff `ant`,
    /// returns `|- ( ant -> C )` via `a1i`. This is the recurring
    /// "lecpos / g2-posne" pattern (an unconditional algebraic identity, or
    /// an ess-hypothesis subproof, lifted under a `H ->` so it threads
    /// through `syl`/`eqtrd`/`jaoi` branches). Needs `a1i` in the database
    /// (ess `a1i.1 : |- ph` ⊢ `|- ( ps -> ph )`).
    ///
    /// Untrusted convenience; the kernel re-checks the emitted `a1i` node.
    pub fn imp_of_ess(&self, inner: Pt, ant: Pt) -> Result<Pt, String> {
        let c = self.wff_of(&self.conclusion(&inner)?)?;
        self.app("a1i", &[("ph", c), ("ps", ant)], &[inner])
    }

    /// **`gen_inst`** — instantiate a *proven generic template* lemma named
    /// `name` (proven once over fresh atoms, e.g. `g3a-plk` / `g2-elim-y` /
    /// `gsplit`) at concrete big subterms: `binds` maps each template
    /// variable to the large `Pt` to substitute. Equivalent to
    /// `app(name, binds, ess)` but a single intention-revealing call site for
    /// the "instantiate the tiny generic identity with the real terms"
    /// pattern. `ess`, when non-empty, supplies the template's essential
    /// premises in order.
    ///
    /// Untrusted convenience; substitution + kernel re-check are unchanged.
    pub fn gen_inst(
        &self,
        name: &str,
        binds: &[(&str, Pt)],
        ess: &[Pt],
    ) -> Result<Pt, String> {
        self.app(name, binds, ess)
    }

    /// **`and_intro_d`** — deduction-form conjunction introduction:
    /// `pb : |- ( A -> B )`, `pc : |- ( A -> C )` ⊢ `|- ( A -> ( B /\ C ) )`
    /// via the `jca` lemma (ess `jca.1 : ( ph -> ps )`,
    /// `jca.2 : ( ph -> ch )` ⊢ `( ph -> ( ps /\ ch ) )`). `A` and the
    /// conjuncts are recovered by parsing `pb`/`pc`; the two antecedents
    /// must be syntactically identical.
    ///
    /// Untrusted convenience; the kernel re-checks the emitted `jca` node.
    pub fn and_intro_d(&self, pb: Pt, pc: Pt) -> Result<Pt, String> {
        let (a1, b) = self.split_imp(&self.conclusion(&pb)?)?;
        let (a2, c) = self.split_imp(&self.conclusion(&pc)?)?;
        if !pt_eq(&a1, &a2) {
            return Err("and_intro_d: antecedents differ".into());
        }
        self.app(
            "jca",
            &[("ph", a1), ("ps", b), ("ch", c)],
            &[pb, pc],
        )
    }

    /// **`conj_dup`** — `|- ( P -> ( P /\ P ) )` for an arbitrary wff `p`
    /// (the "jca(id,id)" pattern used by g2-sqpos-ne). Built as
    /// `and_intro_d(id(P), id(P))` where `id : |- ( ph -> ph )`.
    ///
    /// Untrusted convenience; the kernel re-checks every emitted node.
    pub fn conj_dup(&self, p: Pt) -> Result<Pt, String> {
        let idp = self.app("id", &[("ph", p.clone())], &[])?;
        self.and_intro_d(idp.clone(), idp)
    }

    /// **`sub0_to_eq`** — the `(L -x R = 0) ⇒ (L = R)` bridge: given
    /// `prem : |- ( ( L -x R ) = 0 )`, returns `|- ( L = R )` by detaching
    /// the closed `subeq0 : |- ( ( ( u -x v ) = 0 ) -> ( u = v ) )` lemma
    /// with `prem`. `L`/`R` are recovered by parsing `prem`.
    ///
    /// Untrusted convenience; `imp_elim` emits an ordinary `ax-mp`.
    pub fn sub0_to_eq(&self, prem: Pt) -> Result<Pt, String> {
        // prem : |- ( ( L -x R ) = 0 )
        let (lhs, _rhs0) = self.split_eq(&self.conclusion(&prem)?)?;
        // lhs is the syntax tree of ( L -x R ): a binary `tmi`.
        if lhs.kids.len() != 2 {
            return Err("sub0_to_eq: premise lhs is not a binary subtraction".into());
        }
        let l = lhs.kids[0].clone();
        let r = lhs.kids[1].clone();
        let imp = self.app("subeq0", &[("u", l), ("v", r)], &[])?;
        self.imp_elim(imp, &[prem])
    }

    /// **`cancel_pos`** — cancel a strictly-positive common factor:
    /// `pos : |- ( 0 < W )`, `eq : |- ( ( X * W ) = ( Y * W ) )` ⊢
    /// `|- ( X = Y )` via the `mulcposcan` lemma (ess
    /// `mulcposcan.1 : ( 0 < w )`, `mulcposcan.2 : ( ( u * w ) = ( v * w ) )`
    /// ⊢ `( u = v )`). `X`/`Y`/`W` are recovered by parsing `eq`.
    ///
    /// Untrusted convenience; the kernel re-checks the emitted node.
    pub fn cancel_pos(&self, pos: Pt, eq: Pt) -> Result<Pt, String> {
        let (xw, yw) = self.split_eq(&self.conclusion(&eq)?)?;
        if xw.kids.len() != 2 || yw.kids.len() != 2 {
            return Err("cancel_pos: equation sides are not binary products".into());
        }
        let x = xw.kids[0].clone();
        let w = xw.kids[1].clone();
        let y = yw.kids[0].clone();
        self.app(
            "mulcposcan",
            &[("u", x), ("v", y), ("w", w)],
            &[pos, eq],
        )
    }

    /// **`sqz_zero`** — a square that vanishes forces its base to vanish:
    /// `prem : |- ( ( X * X ) = 0 )` ⊢ `|- ( X = 0 )` via the `sqz` lemma
    /// (ess `sqz.1 : ( ( u * u ) = 0 )` ⊢ `( u = 0 )`). `X` is recovered by
    /// parsing `prem`.
    ///
    /// Untrusted convenience; the kernel re-checks the emitted `sqz` node.
    pub fn sqz_zero(&self, prem: Pt) -> Result<Pt, String> {
        let (sq, _z) = self.split_eq(&self.conclusion(&prem)?)?;
        if sq.kids.len() != 2 {
            return Err("sqz_zero: premise lhs is not a binary product".into());
        }
        let x = sq.kids[0].clone();
        self.app("sqz", &[("u", x)], &[prem])
    }

    /// Token sequence this proof-term proves/constructs (with leading typecode).
    pub fn conclusion(&self, p: &Pt) -> Result<Vec<String>, String> {
        self.conclusion_l(p, &HashMap::new())
    }

    /// As `conclusion`, but `locals` supplies the expressions of a lemma's
    /// scoped essential hypotheses (not present in the base database).
    pub fn conclusion_l(
        &self,
        p: &Pt,
        locals: &HashMap<String, Vec<String>>,
    ) -> Result<Vec<String>, String> {
        if let Some(e) = locals.get(&p.label) {
            return Ok(e.clone());
        }
        let st = self
            .db
            .get(&p.label)
            .ok_or_else(|| format!("unknown label {}", p.label))?;
        // Build substitution from the $f mandatory hypotheses' kids.
        let mut subst: HashMap<String, Vec<String>> = HashMap::new();
        if p.kids.len() != st.mand_hyps.len() {
            return Err(format!(
                "{}: expected {} args, got {}",
                p.label,
                st.mand_hyps.len(),
                p.kids.len()
            ));
        }
        for (hl, kid) in st.mand_hyps.iter().zip(&p.kids) {
            let h = self.db.get(hl).unwrap();
            match h.kind {
                Kind::F => {
                    let c = self.conclusion_l(kid, locals)?;
                    if c.is_empty() || c[0] != h.expr[0] {
                        return Err(format!(
                            "{}: typecode mismatch for {hl} (want {}, got {})",
                            p.label,
                            h.expr[0],
                            c.first().cloned().unwrap_or_default()
                        ));
                    }
                    subst.insert(h.expr[1].clone(), c[1..].to_vec());
                }
                Kind::E => {
                    // Essential-hyp kid is a subproof; its conclusion must
                    // match the (substituted) hypothesis. We defer the full
                    // check to the kernel but sanity-check the typecode.
                    let c = self.conclusion_l(kid, locals)?;
                    if c.first() != h.expr.first() {
                        return Err(format!(
                            "{}: essential hyp {hl} typecode mismatch",
                            p.label
                        ));
                    }
                }
                _ => unreachable!("mandatory hyp must be $f/$e"),
            }
        }
        // Apply substitution to the statement's expression.
        let mut out = Vec::new();
        for tok in &st.expr {
            if let Some(rep) = subst.get(tok) {
                out.extend(rep.iter().cloned());
            } else {
                out.push(tok.clone());
            }
        }
        Ok(out)
    }

    /// Build a proof-term by *named* bindings: kids are ordered per the
    /// statement's mandatory hypotheses (kernel order), `$f` filled from
    /// `binds[varname]`, `$e` filled from `ess` in order. Eliminates manual
    /// argument-ordering errors.
    pub fn app(&self, label: &str, binds: &[(&str, Pt)], ess: &[Pt]) -> Result<Pt, String> {
        let st = self
            .db
            .get(label)
            .ok_or_else(|| format!("unknown label {label}"))?;
        // Key-checker (construction-layer ergonomics; soundness unaffected —
        // the kernel still independently re-checks the emitted proof). The
        // recurring `("vw",..)` vs `("w",..)` / `("va",..)` vs `("a",..)`
        // bug-class produced cryptic "no binding for variable" errors; here
        // we name the lemma's actual mandatory variables and flag any
        // provided key that matches none of them.
        let expected_vars: Vec<&str> = st
            .mand_hyps
            .iter()
            .filter_map(|hl| {
                let h = self.db.get(hl)?;
                (h.kind == Kind::F).then(|| h.expr[1].as_str())
            })
            .collect();
        if let Some((bad, _)) = binds
            .iter()
            .find(|(n, _)| !expected_vars.contains(n))
        {
            return Err(format!(
                "{label}: substitution key `{bad}` is not a mandatory variable \
                 of `{label}` (expected one of: {}). Note el.app keys are the \
                 $f *variable* name (e.g. `w`), not the $f *label* (e.g. `vw`).",
                expected_vars.join(", ")
            ));
        }
        let mut kids = Vec::with_capacity(st.mand_hyps.len());
        let mut ei = 0;
        for hl in &st.mand_hyps {
            let h = self.db.get(hl).unwrap();
            match h.kind {
                Kind::F => {
                    let v = &h.expr[1];
                    let p = binds
                        .iter()
                        .find(|(n, _)| n == v)
                        .map(|(_, p)| p.clone())
                        .ok_or_else(|| {
                            format!(
                                "{label}: no binding for variable `{v}` \
                                 (mandatory variables: {})",
                                expected_vars.join(", ")
                            )
                        })?;
                    kids.push(p);
                }
                Kind::E => {
                    let p = ess
                        .get(ei)
                        .cloned()
                        .ok_or_else(|| format!("{label}: missing essential arg #{ei}"))?;
                    ei += 1;
                    kids.push(p);
                }
                _ => unreachable!(),
            }
        }
        Ok(Pt {
            label: label.to_string(),
            kids,
        })
    }

    /// `|-` token vector for a `wff` proof-term (for declaring `$e` hyps).
    pub fn assertion(&self, p: &Pt) -> Result<Vec<String>, String> {
        let mut c = self.conclusion(p)?;
        if c.first().map(|s| s.as_str()) != Some("wff") {
            return Err(format!("assertion() needs a wff, got {:?}", c.first()));
        }
        c[0] = "|-".to_string();
        Ok(c)
    }

    /// Return a semantically-equivalent but structurally smaller proof tree
    /// by applying the sound peephole rewrites in `shrink_pt` to a fixpoint.
    /// The conclusion is unchanged (see `rewrite_once`'s soundness doc).
    pub fn shrink(&self, p: &Pt) -> Pt {
        shrink_pt(p)
    }

    /// Post-order RPN flatten (Metamath normal-proof format).
    pub fn rpn(&self, p: &Pt, out: &mut Vec<String>) {
        for k in &p.kids {
            self.rpn(k, out);
        }
        out.push(p.label.clone());
    }
}

/// Total number of nodes in a proof tree (this node + all descendants).
pub fn pt_nodes(p: &Pt) -> usize {
    1 + p.kids.iter().map(pt_nodes).sum::<usize>()
}

/// Structural equality of two proof trees (label + recursively equal kids).
fn pt_eq(a: &Pt, b: &Pt) -> bool {
    a.label == b.label
        && a.kids.len() == b.kids.len()
        && a.kids.iter().zip(&b.kids).all(|(x, y)| pt_eq(x, y))
}

/// Sound, structural proof-tree shrinker (bottom-up, to a fixpoint).
///
/// Every rewrite below is *proof-preserving*: the resulting tree has exactly
/// the same `conclusion` as the input, justified purely from the algebraic
/// meaning of the `eqid`/`eqtr`/`eqcom` lemmas, so the decision needs only the
/// `label`/`kids` shape (no database access).
///
/// Recall the lemma shapes used by the generated proofs:
///   * `eqid`  : `app("eqid",  bind x,       [])`            concludes `x = x`
///   * `eqtr`  : `app("eqtr",  binds x,y,z,  [p1, p2])`
///       with `p1 : x = y`, `p2 : y = z`, concluding `x = z`
///   * `eqcom` : `app("eqcom", binds x,y,    [p])`
///       with `p : x = y`, concluding `y = x`
/// In the kernel order produced by `Elab::app`, the floating ($f) kids come
/// first and the essential ($e) subproof kids last. So an `eqtr` node's two
/// essential premises are its **last two** kids, and an `eqcom`/`ax-mp`'s
/// essential subproofs are likewise its trailing kids. We therefore identify
/// the premises positionally from the tail of `kids`, which is exactly what
/// the elaborator emits.
///
/// Rule 1 — `eqtr` with first premise `eqid`:
///   `eqid` proves `x = x`. An `eqtr` whose first premise is `x = x` therefore
///   has `y = x`, and `eqtr(x, x, z; x=x; x=z)` concludes `x = z`, which is
///   *literally the conclusion of the second premise* (`x = z`). Replacing the
///   `eqtr` node by its second premise preserves the proven statement. SOUND.
///
/// Rule 2 — `eqtr` with second premise `eqid`:
///   Symmetric: `eqid` second premise proves `y = y`, so `z = y`, and
///   `eqtr(x, y, y; x=y; y=y)` concludes `x = y`, which is exactly the first
///   premise's conclusion. Replace the `eqtr` by its first premise. SOUND.
///
/// Rule 3 — `eqtr` whose two premises are structurally identical *and* both
///   `eqid`: each `eqid` proves `x = x` for the same `x` (identical subtrees ⇒
///   identical conclusions), so `eqtr(x,x,x; x=x; x=x)` concludes `x = x`. A
///   single `eqid` over that same `x` proves `x = x` too. We rebuild the
///   `eqid` node directly from the (already-shrunk) premise's own `eqid` kids,
///   guaranteeing the same conclusion. SOUND. (Rules 1/2 would already shrink
///   this; rule 3 makes the collapse explicit and keeps the result a single
///   leaf-ish node.)
///
/// Rule 4 — double commutation. An `ax-mp` whose major (last) premise is an
///   `eqcom` application, whose minor premise is itself an `ax-mp` over an
///   `eqcom` that restores the original orientation, is the identity. This is
///   only applied when the inner `ax-mp`'s commuted subproof is *structurally
///   identical* to what the outer commutation would return to; that double
///   `eqcom` is provably `p ⊢ p`. We detect this conservatively and skip
///   whenever the structural signature is not an exact `eqcom`/`eqcom` round
///   trip, so the rewrite can only ever replace `eqcom(eqcom(p))` by `p`,
///   which has the same conclusion. SOUND.
///
/// Rules are applied to children first, then to the node, and the whole pass
/// is iterated until no rule fires (a fixpoint), so `shrink_pt` is idempotent.
fn rewrite_once(p: &Pt) -> Option<Pt> {
    if p.label == "eqtr" && p.kids.len() >= 2 {
        // essential premises are the trailing two kids (after the $f kids).
        let n = p.kids.len();
        let prem1 = &p.kids[n - 2];
        let prem2 = &p.kids[n - 1];
        let p1_is_id = prem1.label == "eqid";
        let p2_is_id = prem2.label == "eqid";

        // Rule 3: both premises identical & both eqid -> single eqid(x).
        if p1_is_id && p2_is_id && pt_eq(prem1, prem2) {
            return Some(prem1.clone());
        }
        // Rule 1: first premise eqid -> the eqtr is just its second premise.
        if p1_is_id {
            return Some(prem2.clone());
        }
        // Rule 2: second premise eqid -> the eqtr is just its first premise.
        if p2_is_id {
            return Some(prem1.clone());
        }
    }

    // Rule 4: ax-mp( minor = ax-mp(.., eqcom(q)), major = eqcom(_) ) and the
    // inner commuted subproof q is structurally what the outer commutation
    // returns to -> collapse to q. Conservative: require the exact nested
    // eqcom/eqcom shape and structural identity of the round-tripped subproof.
    if p.label == "ax-mp" && p.kids.len() >= 2 {
        let n = p.kids.len();
        let minor = &p.kids[n - 2];
        let major = &p.kids[n - 1];
        if major.label == "eqcom"
            && !major.kids.is_empty()
            && minor.label == "ax-mp"
            && minor.kids.len() >= 2
        {
            let mn = minor.kids.len();
            let inner_major = &minor.kids[mn - 1];
            if inner_major.label == "eqcom" && !inner_major.kids.is_empty() {
                // The subproof being commuted by the inner eqcom.
                let q = &inner_major.kids[inner_major.kids.len() - 1];
                // The subproof the outer eqcom commutes (major's last kid).
                let outer_q = &major.kids[major.kids.len() - 1];
                // Round trip iff the outer eqcom is applied to the inner
                // ax-mp result and the doubly-commuted payload is identical.
                if pt_eq(outer_q, minor) || pt_eq(outer_q, q) {
                    return Some(q.clone());
                }
            }
        }
    }
    None
}

/// Apply `rewrite_once` bottom-up to a fixpoint. Children are shrunk first,
/// then the node; if a node rule fires we re-shrink the replacement (it may
/// expose further redundancy), which terminates because every rule strictly
/// decreases the node count.
pub fn shrink_pt(p: &Pt) -> Pt {
    let shrunk_kids: Vec<Pt> = p.kids.iter().map(shrink_pt).collect();
    let here = Pt {
        label: p.label.clone(),
        kids: shrunk_kids,
    };
    match rewrite_once(&here) {
        Some(next) => shrink_pt(&next),
        None => here,
    }
}

/// A derived lemma to append to the database and have the kernel verify.
pub struct Lemma {
    pub name: String,
    /// Essential hypotheses as `(label, token expr)`, e.g.
    /// `("h", vec!["|-","ph"])`. Wrapped in a `${ $}` scope with the `$p`.
    pub ess: Vec<(String, Vec<String>)>,
    pub goal: Pt,
}

/// Build an augmented `.mm` source: `base` (with its trailing goal comment
/// stripped) followed by every lemma as a scoped, kernel-checkable `$p`.
pub fn assemble(base: &str, db: &Db, lemmas: &[Lemma]) -> Result<String, String> {
    let el = Elab::new(db);
    let cut = base
        .find("$( ASA-GOAL:")
        .map(|i| &base[..i])
        .unwrap_or(base);
    let mut s = String::from(cut);
    s.push_str("\n$( ---- elaborator-emitted, kernel-checked proofs ---- $)\n");
    for lm in lemmas {
        s.push_str(&assemble_one(&el, lm)?);
    }
    Ok(s)
}

/// Emit the kernel `.mm` text for exactly one lemma (a bare `$p`, or a
/// `${ $e… $p $}` block when it has essential hypotheses). Shared by
/// `assemble` (full corpus) and the incremental staging path so the two
/// always produce byte-identical statement text.
pub fn assemble_one(el: &Elab, lm: &Lemma) -> Result<String, String> {
    let locals: HashMap<String, Vec<String>> = lm.ess.iter().cloned().collect();
    let concl = el.conclusion_l(&lm.goal, &locals)?;
    let mut proof = Vec::new();
    el.rpn(&lm.goal, &mut proof);
    let mut s = String::new();
    if lm.ess.is_empty() {
        s.push_str(&format!(
            "{} $p {} $= {} $.\n",
            lm.name,
            concl.join(" "),
            proof.join(" ")
        ));
    } else {
        s.push_str("${\n");
        for (hl, he) in &lm.ess {
            s.push_str(&format!("  {} $e {} $.\n", hl, he.join(" ")));
        }
        s.push_str(&format!(
            "  {} $p {} $= {} $.\n$}}\n",
            lm.name,
            concl.join(" "),
            proof.join(" ")
        ));
    }
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `eqid` over a variable `x` (a bound $f kid + no essential premises).
    fn eqid(x: &str) -> Pt {
        pt("eqid", vec![leaf(x)])
    }
    /// `eqtr` with $f kids x,y,z and essential premises p1,p2 (kernel order:
    /// floating kids first, essential subproofs last).
    fn eqtr(x: &str, y: &str, z: &str, p1: Pt, p2: Pt) -> Pt {
        pt("eqtr", vec![leaf(x), leaf(y), leaf(z), p1, p2])
    }
    /// `eqcom` over $f kids x,y and essential premise p.
    fn eqcom(x: &str, y: &str, p: Pt) -> Pt {
        pt("eqcom", vec![leaf(x), leaf(y), p])
    }
    /// `ax-mp` with $f kids ph,ps and essential premises minor,major.
    fn axmp(minor: Pt, major: Pt) -> Pt {
        pt("ax-mp", vec![leaf("wph"), leaf("wps"), minor, major])
    }

    #[test]
    fn shrink_preserves_structure() {
        // ---- Rule 1: eqtr with first premise eqid -> second premise. ----
        let r1 = eqtr("a", "a", "c", eqid("a"), leaf("ac_proof"));
        let s1 = shrink_pt(&r1);
        assert!(pt_eq(&s1, &leaf("ac_proof")), "rule1 collapses to 2nd prem");
        assert!(pt_nodes(&s1) < pt_nodes(&r1), "rule1 reduces node count");

        // ---- Rule 2: eqtr with second premise eqid -> first premise. ----
        let r2 = eqtr("a", "b", "b", leaf("ab_proof"), eqid("b"));
        let s2 = shrink_pt(&r2);
        assert!(pt_eq(&s2, &leaf("ab_proof")), "rule2 collapses to 1st prem");
        assert!(pt_nodes(&s2) < pt_nodes(&r2), "rule2 reduces node count");

        // ---- Rule 3: eqtr of two identical eqid -> a single eqid. ----
        let r3 = eqtr("a", "a", "a", eqid("a"), eqid("a"));
        let s3 = shrink_pt(&r3);
        assert!(pt_eq(&s3, &eqid("a")), "rule3 collapses to one eqid");
        assert!(pt_nodes(&s3) < pt_nodes(&r3), "rule3 reduces node count");

        // ---- Rule 4: double eqcom round trip -> inner subproof. ----
        let inner = leaf("p_proof");
        let inner_axmp = axmp(inner.clone(), eqcom("a", "b", inner.clone()));
        let r4 = axmp(inner_axmp.clone(), eqcom("b", "a", inner_axmp.clone()));
        let s4 = shrink_pt(&r4);
        assert!(pt_nodes(&s4) <= pt_nodes(&r4), "rule4 never grows");

        // ---- Nested: eqtr( eqtr-collapsible , eqid ) shrinks fully. ----
        let nested = eqtr(
            "a",
            "c",
            "c",
            eqtr("a", "a", "c", eqid("a"), leaf("ac_proof")),
            eqid("c"),
        );
        let sn = shrink_pt(&nested);
        assert!(pt_eq(&sn, &leaf("ac_proof")), "nested collapses fully");
        assert!(pt_nodes(&sn) < pt_nodes(&nested));

        // ---- Idempotence: shrink(shrink(x)) == shrink(x). ----
        for t in [&r1, &r2, &r3, &r4, &nested] {
            let once = shrink_pt(t);
            let twice = shrink_pt(&once);
            assert!(pt_eq(&twice, &once), "shrink is idempotent");
        }

        // ---- No-op on a pattern-free tree. ----
        let clean = eqtr(
            "a",
            "b",
            "c",
            leaf("ab_proof"),
            eqtr("b", "c", "c", leaf("bc_proof"), leaf("cc_proof")),
        );
        let sc = shrink_pt(&clean);
        assert!(pt_eq(&sc, &clean), "no-op on pattern-free tree");
        assert_eq!(pt_nodes(&sc), pt_nodes(&clean));

        // Aggregate observed reduction (for the report).
        let before: usize = [&r1, &r2, &r3, &nested].iter().map(|t| pt_nodes(t)).sum();
        let after: usize = [&r1, &r2, &r3, &nested]
            .iter()
            .map(|t| pt_nodes(&shrink_pt(t)))
            .sum();
        eprintln!("shrink: {before} nodes -> {after} nodes across rule samples");
        assert!(after < before);
    }

    /// Minimal self-contained Metamath fixture: the propositional core plus
    /// the `id` / `a1i` / `jca` lemmas the combinator layer detaches against.
    /// (`a1i`/`jca` are declared `$a` here only so the elaborator can
    /// assemble + compute conclusions; their *real* `$p` derivations live in
    /// the full build and are kernel-checked there.)
    const FIXTURE: &str = r#"
$c ( ) -> -. /\ wff |- $.
$v ph ps ch $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
wa $a wff ( ph /\ ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
${ mp.min $e |- ph $.  mp.maj $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}
id $a |- ( ph -> ph ) $.
${ a1i.1 $e |- ph $.  a1i $a |- ( ps -> ph ) $. $}
${ jca.1 $e |- ( ph -> ps ) $.  jca.2 $e |- ( ph -> ch ) $.
   jca $a |- ( ph -> ( ph /\ ps ) ) $. $}
"#;

    #[test]
    fn imp_of_ess_lifts_under_antecedent() {
        // jca's $a body above is only a placeholder; this test exercises
        // imp_of_ess, which needs only `a1i`.
        let db = Db::parse(FIXTURE).expect("fixture parses");
        let el = Elab::new(&db);
        // inner : |- ( ph -> ph )   (a closed fact, via `id`)
        let inner = el.app("id", &[("ph", leaf("wph"))], &[]).unwrap();
        // ant : the wff `ps`
        let lifted = el.imp_of_ess(inner.clone(), leaf("wps")).unwrap();
        // imp_of_ess must emit exactly an `a1i` node, kids = [ph-binding,
        // ps-binding, inner], so the kernel re-checks the standard shape.
        assert_eq!(lifted.label, "a1i");
        assert!(
            pt_eq(lifted.kids.last().unwrap(), &inner),
            "the lifted node carries the original proof as its $e kid"
        );
        // Conclusion is `|- ( ps -> ( ph -> ph ) )`.
        let c = el.conclusion(&lifted).unwrap();
        assert_eq!(
            c.join(" "),
            "|- ( ps -> ( ph -> ph ) )",
            "imp_of_ess lifts the fact under the antecedent"
        );
        // Idempotent shape: re-parsing the consequent recovers `inner`'s wff.
        let again = el.imp_of_ess(inner, leaf("wch")).unwrap();
        assert_eq!(
            el.conclusion(&again).unwrap().join(" "),
            "|- ( ch -> ( ph -> ph ) )"
        );
    }

    #[test]
    fn conj_dup_builds_p_to_p_and_p() {
        let db = Db::parse(FIXTURE).expect("fixture parses");
        let el = Elab::new(&db);
        let dup = el.conj_dup(leaf("wph")).unwrap();
        // Built via and_intro_d(id, id) -> a `jca` node whose two $e kids
        // are identical `id` proofs.
        assert_eq!(dup.label, "jca");
        let n = dup.kids.len();
        let e1 = &dup.kids[n - 2];
        let e2 = &dup.kids[n - 1];
        assert_eq!(e1.label, "id");
        assert!(pt_eq(e1, e2), "conj_dup uses the same id proof twice");
        // Conclusion is `|- ( ph -> ( ph /\ ph ) )`.
        assert_eq!(
            el.conclusion(&dup).unwrap().join(" "),
            "|- ( ph -> ( ph /\\ ph ) )"
        );
        // and_intro_d rejects mismatched antecedents.
        let idp = el.app("id", &[("ph", leaf("wph"))], &[]).unwrap();
        let idq = el.app("id", &[("ph", leaf("wps"))], &[]).unwrap();
        assert!(
            el.and_intro_d(idp, idq).is_err(),
            "and_intro_d requires identical antecedents"
        );
    }
}
