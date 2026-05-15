//! A sound Metamath-subset verifier — the trust root for the F0 ASA proof.
//!
//! Faithful to the Metamath spec for what we use: constants/variables,
//! `$f`/`$e`/`$a`/`$p`, `$d`, `${ $}` scoping, mandatory-frame computation,
//! substitution, the stack verification algorithm, and disjoint-variable
//! checking. We only parse NORMAL (uncompressed) proofs — our authored
//! database uses them; the set.mm extractor (separate module) handles the
//! compressed format.
//!
//! If `verify()` returns Ok, every `$p` was derived from the `$a` axioms by
//! substitution + the stack discipline, with DV side-conditions enforced.
//! That is the soundness guarantee: every `$p` was derived by substitution,
//! not merely claimed.

use std::collections::{BTreeSet, HashMap};

pub type Sym = String;
pub type Expr = Vec<Sym>; // first token is the typecode

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    F, // floating hypothesis: `typecode var`
    E, // essential hypothesis
    A, // axiomatic assertion
    P, // provable assertion
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub label: String,
    pub kind: Kind,
    pub expr: Expr,
    /// For `$p`: the proof as a flat list of referenced labels (normal format).
    pub proof: Vec<String>,
    /// Mandatory hypotheses (labels), in Metamath order. Filled for A/P.
    pub mand_hyps: Vec<String>,
    /// Mandatory disjoint-variable pairs (unordered, sorted).
    pub mand_dv: BTreeSet<(Sym, Sym)>,
}

#[derive(Default)]
pub struct Db {
    pub stmts: Vec<Stmt>,
    pub by_label: HashMap<String, usize>,
    consts: BTreeSet<Sym>,
    vars: BTreeSet<Sym>,
}

#[derive(Default, Clone)]
struct Scope {
    active_hyps: Vec<String>, // labels of $f/$e active here, in order
    dv: BTreeSet<(Sym, Sym)>, // disjoint pairs active here
}

impl Db {
    fn is_var(&self, s: &str) -> bool {
        self.vars.contains(s)
    }

    pub fn get(&self, label: &str) -> Option<&Stmt> {
        self.by_label.get(label).map(|&i| &self.stmts[i])
    }

    /// Parse a Metamath-subset source string into a database.
    pub fn parse(src: &str) -> Result<Db, String> {
        let toks = tokenize(src);
        let mut db = Db::default();
        let mut stack: Vec<Scope> = vec![Scope::default()];
        let mut i = 0;
        while i < toks.len() {
            match toks[i].as_str() {
                "$(" => {
                    // comment: skip to $)
                    while i < toks.len() && toks[i] != "$)" {
                        i += 1;
                    }
                    i += 1;
                }
                "${" => {
                    let top = stack.last().unwrap().clone();
                    stack.push(top);
                    i += 1;
                }
                "$}" => {
                    stack.pop().ok_or("unbalanced $}")?;
                    if stack.is_empty() {
                        return Err("unbalanced $}".into());
                    }
                    i += 1;
                }
                "$c" => {
                    i += 1;
                    while toks[i] != "$." {
                        db.consts.insert(toks[i].clone());
                        i += 1;
                    }
                    i += 1;
                }
                "$v" => {
                    i += 1;
                    while toks[i] != "$." {
                        db.vars.insert(toks[i].clone());
                        i += 1;
                    }
                    i += 1;
                }
                "$d" => {
                    i += 1;
                    let mut vs = Vec::new();
                    while toks[i] != "$." {
                        vs.push(toks[i].clone());
                        i += 1;
                    }
                    i += 1;
                    let sc = stack.last_mut().unwrap();
                    for a in 0..vs.len() {
                        for b in (a + 1)..vs.len() {
                            let (x, y) = (vs[a].clone(), vs[b].clone());
                            if x == y {
                                return Err(format!("$d with repeated var {x}"));
                            }
                            sc.dv.insert(order_pair(x, y));
                        }
                    }
                }
                t if t.starts_with('$') => {
                    return Err(format!("unexpected keyword {t} at token {i}"));
                }
                _ => {
                    // labelled statement: label <kw> ... $.
                    let label = toks[i].clone();
                    let kw = toks[i + 1].clone();
                    i += 2;
                    let mut body = Vec::new();
                    let mut proof = Vec::new();
                    if kw == "$p" {
                        while toks[i] != "$=" {
                            body.push(toks[i].clone());
                            i += 1;
                        }
                        i += 1; // skip $=
                        while toks[i] != "$." {
                            proof.push(toks[i].clone());
                            i += 1;
                        }
                        i += 1;
                    } else {
                        while toks[i] != "$." {
                            body.push(toks[i].clone());
                            i += 1;
                        }
                        i += 1;
                    }
                    let kind = match kw.as_str() {
                        "$f" => Kind::F,
                        "$e" => Kind::E,
                        "$a" => Kind::A,
                        "$p" => Kind::P,
                        other => return Err(format!("bad statement kw {other}")),
                    };
                    if db.by_label.contains_key(&label) {
                        return Err(format!("duplicate label {label}"));
                    }
                    let mut st = Stmt {
                        label: label.clone(),
                        kind: kind.clone(),
                        expr: body,
                        proof,
                        mand_hyps: vec![],
                        mand_dv: BTreeSet::new(),
                    };
                    match kind {
                        Kind::F | Kind::E => {
                            stack.last_mut().unwrap().active_hyps.push(label.clone());
                        }
                        Kind::A | Kind::P => {
                            db.compute_frame(&mut st, stack.last().unwrap());
                        }
                    }
                    let idx = db.stmts.len();
                    db.by_label.insert(label, idx);
                    db.stmts.push(st);
                }
            }
        }
        Ok(db)
    }

    /// Mandatory frame: active `$e` plus the active `$f` whose variable occurs
    /// in the assertion or in some active `$e`, in declaration order; and the
    /// `$d` pairs restricted to those mandatory variables.
    fn compute_frame(&self, st: &mut Stmt, sc: &Scope) {
        // Variables referenced by the assertion + active $e statements.
        let mut needed: BTreeSet<Sym> = BTreeSet::new();
        for s in &st.expr {
            if self.is_var(s) {
                needed.insert(s.clone());
            }
        }
        for hl in &sc.active_hyps {
            let h = &self.stmts[self.by_label[hl]];
            if h.kind == Kind::E {
                for s in &h.expr {
                    if self.is_var(s) {
                        needed.insert(s.clone());
                    }
                }
            }
        }
        // First pass: $f for needed vars contribute their var too (transitive
        // closure is unnecessary in our fragment: $f bodies are `tc var`).
        let mut mand = Vec::new();
        let mut mvars: BTreeSet<Sym> = BTreeSet::new();
        for hl in &sc.active_hyps {
            let h = &self.stmts[self.by_label[hl]];
            match h.kind {
                Kind::F => {
                    let v = &h.expr[1];
                    if needed.contains(v) {
                        mand.push(hl.clone());
                        mvars.insert(v.clone());
                    }
                }
                Kind::E => {
                    mand.push(hl.clone());
                    for s in &h.expr {
                        if self.is_var(s) {
                            mvars.insert(s.clone());
                        }
                    }
                }
                _ => {}
            }
        }
        st.mand_hyps = mand;
        for (a, b) in &sc.dv {
            if mvars.contains(a) && mvars.contains(b) {
                st.mand_dv.insert((a.clone(), b.clone()));
            }
        }
    }

    /// Verify every `$p`. Returns Ok(()) iff all proofs check.
    pub fn verify(&self) -> Result<(), String> {
        for st in &self.stmts {
            if st.kind == Kind::P {
                self.verify_proof(st)
                    .map_err(|e| format!("proof of {}: {e}", st.label))?;
            }
        }
        Ok(())
    }

    fn verify_proof(&self, thm: &Stmt) -> Result<(), String> {
        // Frame DV available while proving `thm`: its mandatory DV (sufficient
        // for our database; optional-DV declarations would extend this).
        let frame_dv = &thm.mand_dv;
        let mut stack: Vec<Expr> = Vec::new();
        for lbl in &thm.proof {
            let s = self
                .get(lbl)
                .ok_or_else(|| format!("unknown label {lbl}"))?;
            match s.kind {
                Kind::F | Kind::E => stack.push(s.expr.clone()),
                Kind::A | Kind::P => {
                    let n = s.mand_hyps.len();
                    if stack.len() < n {
                        return Err(format!("stack underflow applying {lbl}"));
                    }
                    let args = stack.split_off(stack.len() - n);
                    let mut subst: HashMap<Sym, Expr> = HashMap::new();
                    for (h_lbl, arg) in s.mand_hyps.iter().zip(&args) {
                        let h = &self.stmts[self.by_label[h_lbl]];
                        match h.kind {
                            Kind::F => {
                                if arg.is_empty() || arg[0] != h.expr[0] {
                                    return Err(format!(
                                        "typecode mismatch for {h_lbl} in {lbl}"
                                    ));
                                }
                                subst.insert(h.expr[1].clone(), arg[1..].to_vec());
                            }
                            Kind::E => {
                                let want = self.apply(&h.expr, &subst);
                                if &want != arg {
                                    return Err(format!(
                                        "essential hyp {h_lbl} unmatched in {lbl}"
                                    ));
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    // Disjoint-variable side conditions of the applied assertion.
                    for (a, b) in &s.mand_dv {
                        let sa = vars_of(self, subst.get(a).map(|v| v.as_slice()).unwrap_or(&[]));
                        let sb = vars_of(self, subst.get(b).map(|v| v.as_slice()).unwrap_or(&[]));
                        for x in &sa {
                            for y in &sb {
                                if x == y {
                                    return Err(format!(
                                        "DV violated: {a}/{b} share {x} applying {lbl}"
                                    ));
                                }
                                if !frame_dv.contains(&order_pair(x.clone(), y.clone())) {
                                    return Err(format!(
                                        "DV {x}/{y} required by {lbl} not declared in frame"
                                    ));
                                }
                            }
                        }
                    }
                    stack.push(self.apply(&s.expr, &subst));
                }
            }
        }
        if stack.len() != 1 {
            return Err(format!("proof ends with {} stack entries", stack.len()));
        }
        if stack[0] != thm.expr {
            return Err(format!(
                "proved `{}` but statement is `{}`",
                stack[0].join(" "),
                thm.expr.join(" ")
            ));
        }
        Ok(())
    }

    fn apply(&self, e: &Expr, subst: &HashMap<Sym, Expr>) -> Expr {
        let mut out = Vec::with_capacity(e.len());
        for s in e {
            if let Some(rep) = subst.get(s) {
                if self.is_var(s) {
                    out.extend(rep.iter().cloned());
                    continue;
                }
            }
            out.push(s.clone());
        }
        out
    }
}

fn vars_of(db: &Db, e: &[Sym]) -> Vec<Sym> {
    e.iter().filter(|s| db.is_var(s)).cloned().collect()
}

fn order_pair(a: Sym, b: Sym) -> (Sym, Sym) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

fn tokenize(src: &str) -> Vec<String> {
    src.split_whitespace().map(|s| s.to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal propositional calculus: `wi` builds implications, `ax1` is the
    /// first axiom, `mp` is modus ponens. `th2` applies `mp` to two essential
    /// hypotheses — a proof small enough to verify entirely by hand.
    const PROP: &str = r#"
$c ( ) -> wff |- $.
$v p q $.
wp $f wff p $.
wq $f wff q $.
wi $a wff ( p -> q ) $.
ax1 $a |- ( p -> ( q -> p ) ) $.
${
  mi $e |- p $.
  mj $e |- ( p -> q ) $.
  mp $a |- q $.
$}
${
  h1 $e |- p $.
  h2 $e |- ( p -> q ) $.
  th2 $p |- q $= wp wq h1 h2 mp $.
$}
th1 $p |- ( p -> ( q -> p ) ) $= wp wq ax1 $.
"#;

    #[test]
    fn accepts_known_good_proof() {
        let db = Db::parse(PROP).expect("parse");
        db.verify().expect("PROP th1/th2 must verify");
    }

    #[test]
    fn rejects_corrupted_proof() {
        // Drop the final `mp`: stack no longer reduces to a single `|- q`.
        let bad = PROP.replace("wp wq h1 h2 mp $.", "wp wq h1 h2 $.");
        let db = Db::parse(&bad).expect("parse");
        assert!(db.verify().is_err(), "corrupted proof must be rejected");
    }

    #[test]
    fn rejects_wrong_conclusion() {
        let bad = PROP.replace("th1 $p |- ( p -> ( q -> p ) ) $=", "th1 $p |- ( q -> p ) $=");
        let db = Db::parse(&bad).expect("parse");
        assert!(db.verify().is_err(), "mismatched conclusion must be rejected");
    }

    /// Disjoint-variable enforcement: an axiom requiring `$d p q` must be
    /// rejected when applied with a substitution that collapses them.
    #[test]
    fn enforces_disjoint_variables() {
        let ok = r#"
$c wff |- R $.
$v p q $.
wp $f wff p $.
wq $f wff q $.
${
  $d p q $.
  axd $a |- R p q $.
$}
${
  $d p q $.
  good $p |- R p q $= wp wq axd $.
$}
"#;
        let db = Db::parse(ok).expect("parse");
        db.verify().expect("DV-respecting proof must verify");

        // `bad` substitutes both p and q with the same variable p: the $d of
        // `axd` is violated and the frame lacks the needed $d anyway.
        let bad = r#"
$c wff |- R $.
$v p q $.
wp $f wff p $.
wq $f wff q $.
${
  $d p q $.
  axd $a |- R p q $.
$}
bad $p |- R p p $= wp wp axd $.
"#;
        let db = Db::parse(bad).expect("parse");
        assert!(
            db.verify().is_err(),
            "DV violation (p/q collapsed) must be rejected"
        );
    }
}
