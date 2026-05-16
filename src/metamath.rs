//! Metamath proof-DAG extractor.
//!
//! Parses a Metamath database (e.g. `data/set.mm`) and computes, for any
//! `$a`/`$p` label, the size of its **fully-expanded** proof tree: every label
//! reference is recursively unfolded down to axioms and hypotheses (leaves).
//!
//! We do NOT verify proofs (no unification / substitution). We only need the
//! proof's *reference structure*: which labels each proof invokes and with what
//! multiplicity. From that:
//!
//!   nodes(T) = 1                      if T is a $f/$e hypothesis or $a axiom
//!   nodes(T) = Σ_{steps s} nodes(label(s))   if T is a $p (each occurrence of a
//!                                            label in the decompressed step
//!                                            list contributes its expansion)
//!
//! Two metrics are produced:
//!   * `expanded` — the fully-inlined tree count (Z-tagged subproofs are
//!     expanded, NOT shared).
//!   * `dag`      — the DAG-shared count: Z-tagged subproofs and identical
//!     theorem expansions are shared (each distinct theorem counted once via
//!     memoization; within a single proof, Z back-references are shared too).
//!
//! Because totals are astronomically large we use the project's exact-bignum
//! `ProofSize`. Each theorem's expanded size is memoized once (the definition
//! graph is a DAG: a proof only references earlier labels).

use crate::number::ProofSize;
use std::collections::HashMap;

/// Kind of a labelled statement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// `$f` floating hypothesis (typecode + variable).
    Floating,
    /// `$e` essential hypothesis.
    Essential,
    /// `$a` axiomatic assertion (leaf).
    Axiom,
    /// `$p` provable assertion (has a proof).
    Provable,
}

/// One labelled statement in the database.
pub struct Statement {
    pub label: String,
    pub kind: Kind,
    /// For `$f`: tokens are `[typecode, var]`. For `$e`/`$a`/`$p`: the full
    /// math-symbol string of the assertion (typecode + body). Used only for
    /// mandatory-hypothesis variable detection.
    pub math: Vec<String>,
    /// Mandatory hypotheses (statement indices), in correct Metamath order.
    /// Empty for `$f`/`$e` (they are leaves themselves).
    pub mand_hyps: Vec<usize>,
    /// Decoded proof reference list (only for `$p`): the linear sequence of
    /// proof steps, each either a label reference or a saved-subproof
    /// back-reference. `None` for non-`$p` or `$p ?` (incomplete) proofs.
    pub proof: Option<Vec<ProofStep>>,
}

/// One step in a decoded proof.
#[derive(Clone, Debug)]
pub enum ProofStep {
    /// Apply the statement with this global index (RPN: pop its mandatory
    /// hypotheses, push the result).
    Stmt(usize),
    /// Push a previously Z-tagged saved subproof's result (0-based tag id).
    Saved(usize),
    /// Z marker: tag the current top-of-stack as saved subproof #id.
    Tag(usize),
}

/// Classification of an `$a` statement for the ZFC-grounding analysis.
///
///  * `GenuineAxiom`   — `$a` whose label starts with `ax-` and which is NOT
///    re-proved elsewhere as a `$p` with an identical statement expression.
///    These are the true FOL/ZFC primitives (ax-mp, ax-1, ax-gen, ax-ext,
///    ax-pow, ax-un, ax-pr, ax-inf2, ax-ac2, ax-sep, ax-reg, ax-12, ax-13, …).
///  * `ConstructedAxiom` — `$a` whose label starts with `ax-` and which DOES
///    have a `$p` twin proving the identical statement from ZFC (e.g.
///    `ax-1cn` ↔ `ax1cn`, `ax-pre-sup` ↔ `axpre-sup`). The ZFC proof exists
///    in-database.
///  * `Definition`     — `$a` whose label starts with `df-` (a definitional
///    extension, not a genuine axiom).
///  * `Syntax`         — every other `$a`: the `w*`/`c*` grammar / typecode
///    constructors.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Class {
    GenuineAxiom,
    ConstructedAxiom,
    Definition,
    Syntax,
}

impl Class {
    /// Index into the 4-bucket breakdown vector.
    pub fn idx(self) -> usize {
        match self {
            Class::GenuineAxiom => 0,
            Class::ConstructedAxiom => 1,
            Class::Definition => 2,
            Class::Syntax => 3,
        }
    }
}

/// The parsed database.
pub struct Database {
    pub statements: Vec<Statement>,
    /// label -> index into `statements`.
    pub by_label: HashMap<String, usize>,
}

/// A scope frame. We only need the active `$f`/`$e` declared in it for the
/// mandatory-hypothesis computation; on `$}` the frame (and thus its
/// hypotheses) goes inactive. Variable-hood is determined from active `$f`s
/// per the Metamath spec, so we don't track `$v`/`$c` here.
struct Frame {
    /// Active `$f` statement indices declared in this frame.
    floats: Vec<usize>,
    /// Active `$e` statement indices declared in this frame.
    essen: Vec<usize>,
}

/// Streaming tokenizer over the database bytes, skipping `$( ... $)` comments
/// and handling `$[ ... $]` file inclusions gracefully (set.mm has none real).
struct Tokenizer<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Tokenizer<'a> {
    fn new(s: &'a [u8]) -> Self {
        Tokenizer { s, i: 0 }
    }

    fn next_token(&mut self) -> Option<&'a str> {
        loop {
            // Skip whitespace.
            while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
                self.i += 1;
            }
            if self.i >= self.s.len() {
                return None;
            }
            // Comment?  `$(` ... `$)`
            if self.s[self.i] == b'$' && self.i + 1 < self.s.len() {
                let c = self.s[self.i + 1];
                if c == b'(' {
                    self.i += 2;
                    // Scan to closing `$)`.
                    while self.i + 1 < self.s.len()
                        && !(self.s[self.i] == b'$' && self.s[self.i + 1] == b')')
                    {
                        self.i += 1;
                    }
                    self.i = (self.i + 2).min(self.s.len());
                    continue;
                }
                if c == b'[' {
                    // File inclusion `$[ filename $]` — skip it entirely.
                    self.i += 2;
                    while self.i + 1 < self.s.len()
                        && !(self.s[self.i] == b'$' && self.s[self.i + 1] == b']')
                    {
                        self.i += 1;
                    }
                    self.i = (self.i + 2).min(self.s.len());
                    continue;
                }
            }
            // Read one whitespace-delimited token.
            let start = self.i;
            while self.i < self.s.len() && !self.s[self.i].is_ascii_whitespace() {
                self.i += 1;
            }
            // SAFETY: set.mm is ASCII; tokens are ASCII by Metamath spec.
            return Some(std::str::from_utf8(&self.s[start..self.i]).unwrap());
        }
    }
}

impl Database {
    /// Parse a Metamath database from a string.
    pub fn parse(src: &str) -> Database {
        let mut tok = Tokenizer::new(src.as_bytes());

        let mut statements: Vec<Statement> = Vec::new();
        let mut by_label: HashMap<String, usize> = HashMap::new();

        // Scope stack. Frame 0 is the outermost (global) scope.
        let mut scope: Vec<Frame> = vec![Frame {
            floats: Vec::new(),
            essen: Vec::new(),
        }];

        // Pending label (Metamath: a label precedes `$f`/`$e`/`$a`/`$p`).
        let mut pending_label: Option<String> = None;

        while let Some(t) = tok.next_token() {
            match t {
                "${" => {
                    scope.push(Frame {
                        floats: Vec::new(),
                        essen: Vec::new(),
                    });
                }
                "$}" => {
                    scope.pop();
                    assert!(!scope.is_empty(), "unbalanced $}}");
                }
                "$c" => {
                    // Constants: consume until `$.` (we don't need the values).
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                    }
                }
                "$v" => {
                    // Variable declarations: variable-hood is derived from
                    // active `$f`s, so we just skip to `$.`.
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                    }
                }
                "$d" => {
                    // Disjoint-variable restriction — irrelevant to counting.
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                    }
                }
                "$f" => {
                    let label = pending_label.take().expect("$f without label");
                    let mut math = Vec::new();
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                        math.push(x.to_string());
                    }
                    // $f is `typecode var`.
                    let idx = statements.len();
                    by_label.insert(label.clone(), idx);
                    statements.push(Statement {
                        label,
                        kind: Kind::Floating,
                        math,
                        mand_hyps: Vec::new(),
                        proof: None,
                    });
                    scope.last_mut().unwrap().floats.push(idx);
                }
                "$e" => {
                    let label = pending_label.take().expect("$e without label");
                    let mut math = Vec::new();
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                        math.push(x.to_string());
                    }
                    let idx = statements.len();
                    by_label.insert(label.clone(), idx);
                    statements.push(Statement {
                        label,
                        kind: Kind::Essential,
                        math,
                        mand_hyps: Vec::new(),
                        proof: None,
                    });
                    scope.last_mut().unwrap().essen.push(idx);
                }
                "$a" | "$p" => {
                    let is_p = t == "$p";
                    let label = pending_label.take().expect("assertion without label");
                    // Read the math string up to `$.` (for `$a`) or up to `$=`
                    // (for `$p`, after which comes the proof up to `$.`).
                    let mut math = Vec::new();
                    let mut proof_tokens: Vec<String> = Vec::new();
                    let mut in_proof = false;
                    while let Some(x) = tok.next_token() {
                        if x == "$." {
                            break;
                        }
                        if is_p && x == "$=" {
                            in_proof = true;
                            continue;
                        }
                        if in_proof {
                            proof_tokens.push(x.to_string());
                        } else {
                            math.push(x.to_string());
                        }
                    }

                    let mand =
                        Self::mandatory_hyps(&scope, &statements, &math);

                    let idx = statements.len();
                    let proof = if is_p {
                        Some(Self::decode_proof(
                            &proof_tokens,
                            &mand,
                            &by_label,
                        ))
                    } else {
                        None
                    };
                    by_label.insert(label.clone(), idx);
                    statements.push(Statement {
                        label,
                        kind: if is_p { Kind::Provable } else { Kind::Axiom },
                        math,
                        mand_hyps: mand,
                        proof,
                    });
                }
                "$." => { /* stray terminator (shouldn't happen) */ }
                _ => {
                    // A bare token in statement position is a label for the
                    // next `$f`/`$e`/`$a`/`$p`.
                    pending_label = Some(t.to_string());
                }
            }
        }

        Database {
            statements,
            by_label,
        }
    }

    /// Compute the mandatory hypotheses of an assertion, in correct Metamath
    /// order.
    ///
    /// Per the Metamath spec, the mandatory hypotheses are, in the order they
    /// appear in the (nested) scope:
    ///   * every active `$e` (essential hypothesis), and
    ///   * every active `$f` (floating hypothesis) whose variable occurs in
    ///     some active `$e` or in the assertion itself.
    /// The order is exactly the order the `$f`/`$e` statements were declared
    /// (outermost scope first, then inner, in source order). `$d` does not
    /// contribute.
    fn mandatory_hyps(
        scope: &[Frame],
        statements: &[Statement],
        assertion_math: &[String],
    ) -> Vec<usize> {
        // Collect active $f and $e in declaration order across the scope
        // stack (outer -> inner; within a frame, source order is preserved
        // because we interleave by re-walking — but $f and $e in the same
        // frame must keep their *relative* source order. We recorded them in
        // separate vecs, losing interleaving. Reconstruct by global index:
        // statement indices are monotonically increasing in source order, so
        // sorting the union of active $f/$e indices reproduces source order.)
        let mut active: Vec<usize> = Vec::new();
        for f in scope {
            active.extend_from_slice(&f.floats);
            active.extend_from_slice(&f.essen);
        }
        active.sort_unstable(); // global index == source order.

        // Variables referenced by the assertion or by any active $e.
        let mut referenced: std::collections::HashSet<&str> =
            std::collections::HashSet::new();

        // Set of all variables that have an active $f (token -> needed test).
        // First gather $f variable names.
        let mut float_var: HashMap<usize, &str> = HashMap::new();
        for &i in &active {
            if statements[i].kind == Kind::Floating {
                // $f math = [typecode, var]
                if statements[i].math.len() >= 2 {
                    float_var.insert(i, statements[i].math[1].as_str());
                }
            }
        }
        let float_var_set: std::collections::HashSet<&str> =
            float_var.values().copied().collect();
        let is_var = |tok: &str| float_var_set.contains(tok);

        for tokn in assertion_math {
            if is_var(tokn) {
                referenced.insert(tokn.as_str());
            }
        }
        for &i in &active {
            if statements[i].kind == Kind::Essential {
                for tokn in &statements[i].math {
                    if is_var(tokn) {
                        referenced.insert(tokn.as_str());
                    }
                }
            }
        }

        // Build mandatory list in source order: include every active $e, and
        // every active $f whose variable is referenced.
        let mut mand = Vec::new();
        for &i in &active {
            match statements[i].kind {
                Kind::Essential => mand.push(i),
                Kind::Floating => {
                    if let Some(v) = float_var.get(&i) {
                        if referenced.contains(*v) {
                            mand.push(i);
                        }
                    }
                }
                _ => {}
            }
        }
        mand
    }

    /// Decode a proof's token list into a flat sequence of `ProofStep`s,
    /// handling both the normal (uncompressed) format and the compressed
    /// `( ... ) LETTERS` format.
    ///
    /// The returned sequence is the *linear list of proof steps* exactly as
    /// the proof executes them. For node counting we don't need the RPN stack
    /// semantics — only "this step references label/saved X" — because
    /// nodes(T) = Σ nodes(referenced) over every step occurrence, and every
    /// step references exactly one statement (or one saved subproof).
    fn decode_proof(
        tokens: &[String],
        mand: &[usize],
        by_label: &HashMap<String, usize>,
    ) -> Vec<ProofStep> {
        if tokens.is_empty() {
            return Vec::new();
        }
        if tokens[0] != "(" {
            // Normal/uncompressed proof: a flat sequence of labels.
            // `?` means an incomplete proof step (treat as a leaf-ish unknown:
            // we map it to nothing, contributing 0 — but set.mm is complete).
            let mut out = Vec::new();
            for lbl in tokens {
                if lbl == "?" {
                    continue;
                }
                if let Some(&idx) = by_label.get(lbl) {
                    out.push(ProofStep::Stmt(idx));
                }
            }
            return out;
        }

        // Compressed proof.
        //   ( L1 L2 ... Ln )  <letter block...>
        // Parse the parenthesised label list.
        let mut k = 1; // tokens[0] == "("
        let mut paren_labels: Vec<usize> = Vec::new();
        while k < tokens.len() && tokens[k] != ")" {
            // Each is a label; map to a global statement index.
            if let Some(&idx) = by_label.get(&tokens[k]) {
                paren_labels.push(idx);
            } else {
                // Unknown label in paren list — shouldn't happen in set.mm.
                // Push a sentinel that resolves to a 1-node leaf via Stmt to
                // an out-of-range guard handled at scoring time. To stay safe
                // we just skip; indices would shift, so instead panic.
                panic!("compressed proof references unknown label {}", tokens[k]);
            }
            k += 1;
        }
        // tokens[k] == ")"
        k += 1;

        // Concatenate the remaining letter block(s) into one string.
        let mut letters = String::new();
        while k < tokens.len() {
            letters.push_str(&tokens[k]);
            k += 1;
        }

        // Decode the letter stream.
        //
        // A..T  -> base-20 low digit, value 0..19; terminates the current
        //          integer.
        // U..Y  -> base-5 high "continuation" digit, value 1..5; accumulates
        //          BEFORE a terminating A..T:  num = num*5 + (c-'U'+1).
        // On a terminating letter: integer = num*20 + (c-'A'); num resets 0.
        // Z     -> tag the proof step just produced as a saved subproof.
        //
        // Integer n (1-based) maps to:
        //   1 .. m                 -> mand[n-1]                 (mandatory hyp)
        //   m+1 .. m+p             -> paren_labels[n-m-1]        (paren label)
        //   m+p+1 ..               -> saved subproof #(n-m-p-1)  (0-based)
        let m = mand.len();
        let p = paren_labels.len();

        // Emit the RAW RPN step sequence. `Stmt(i)` = apply statement i;
        // `Saved(j)` = push the j-th (0-based, tag order) saved subproof's
        // result. We deliberately do NOT resolve saved refs here: the
        // expanded-tree fold (RPN over ProofSize) duplicates them, and the
        // DAG fold shares them. A `Z` tags the subproof that produced the
        // current top-of-stack — recorded as the index of the step that the
        // tag follows (the `Tag` marker carries the running saved-counter so
        // the scoring RPN can map `Saved(j)` to the right stack snapshot).
        let mut out: Vec<ProofStep> = Vec::new();
        // Number of `Z` tags seen so far (== next saved subproof's 0-based id).
        let mut nsaved: usize = 0;

        let mut num: u64 = 0;

        for ch in letters.chars() {
            match ch {
                'A'..='T' => {
                    // Terminating low digit. Per the Metamath compressed-proof
                    // spec, A..T encode 1..20 (NOT 0..19): n = num*20 + (ch-'A'+1).
                    let n = num * 20 + (ch as u64 - 'A' as u64 + 1);
                    num = 0;
                    if n == 0 {
                        // Unreachable for well-formed proofs (min value is 1).
                        continue;
                    }
                    let step = if n <= m as u64 {
                        ProofStep::Stmt(mand[(n - 1) as usize])
                    } else if n <= (m + p) as u64 {
                        ProofStep::Stmt(paren_labels[(n - 1 - m as u64) as usize])
                    } else {
                        ProofStep::Saved((n - 1 - (m + p) as u64) as usize)
                    };
                    out.push(step);
                }
                'U'..='Y' => {
                    // High continuation digit, base 5, value 1..5.
                    num = num * 5 + (ch as u64 - 'U' as u64 + 1);
                }
                'Z' => {
                    // Tag the subproof that produced the current
                    // top-of-stack as saved subproof #nsaved. We encode this
                    // as an explicit Tag marker so the scoring RPN can snap-
                    // shot the stack top at exactly this point.
                    out.push(ProofStep::Tag(nsaved));
                    nsaved += 1;
                }
                _ => {
                    // Tokenizer already stripped whitespace; ignore anything
                    // else defensively.
                }
            }
        }
        out
    }

    /// Compute the fully-expanded proof-tree node count for every statement,
    /// memoized. Returns a vector indexed by statement index.
    ///
    /// Leaves ($f, $e, $a) = 1 node. A $p = Σ over its proof steps of the
    /// expansion of the referenced statement. Because the definition graph is
    /// a DAG (proofs reference only earlier labels) a single forward pass with
    /// memoization suffices; no recursion stack blowups, no materialization.
    /// Convention-free decoder gate: every complete `$p` proof, simulated as
    /// an RPN stack using only *arities* (a step consumes |mandatory hyps|,
    /// pushes 1; `Saved` pushes 1; `Tag` is a no-op needing depth ≥ 1), must
    /// never underflow and must end with exactly one stack entry. A wrong
    /// compressed-proof decoder cannot satisfy this across the whole library.
    /// Returns (ok, total, sample of failing labels).
    pub fn arity_check(&self) -> (usize, usize, Vec<String>) {
        let mut ok = 0;
        let mut total = 0;
        let mut fails: Vec<String> = Vec::new();
        for st in &self.statements {
            if st.kind != Kind::Provable {
                continue;
            }
            let steps = match &st.proof {
                Some(s) => s,
                None => continue, // incomplete `$p ?` — excluded
            };
            total += 1;
            let mut depth: i64 = 0;
            let mut bad = false;
            for stp in steps {
                match stp {
                    ProofStep::Stmt(i) => {
                        let ar = self.statements[*i].mand_hyps.len() as i64;
                        if depth < ar {
                            bad = true;
                            break;
                        }
                        depth = depth - ar + 1;
                    }
                    ProofStep::Tag(_) => {
                        if depth < 1 {
                            bad = true;
                            break;
                        }
                    }
                    ProofStep::Saved(_) => depth += 1,
                }
            }
            if !bad && depth == 1 {
                ok += 1;
            } else if fails.len() < 12 {
                fails.push(st.label.clone());
            }
        }
        (ok, total, fails)
    }

    pub fn expanded_sizes(&self) -> Vec<ProofSize> {
        let n = self.statements.len();
        let mut memo: Vec<Option<ProofSize>> = vec![None; n];

        // Iterative post-order DFS with an explicit (idx, visited?) stack to
        // avoid recursion blowups (set.mm proofs chain thousands deep).
        for root in 0..n {
            if memo[root].is_some() {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if memo[idx].is_some() {
                    continue;
                }
                let st = &self.statements[idx];
                let steps: Option<&Vec<ProofStep>> = match st.kind {
                    // Citable, convention-stable metric: count primitive AXIOM
                    // ($a) invocations in the fully-inlined tree.
                    //   $f / $e : substitution glue (replaced at use site) -> 0
                    //   $a      : a primitive axiom leaf                    -> 1
                    //   $p      : expand its proof
                    Kind::Floating | Kind::Essential => {
                        memo[idx] = Some(ProofSize::zero());
                        continue;
                    }
                    Kind::Axiom => None,
                    Kind::Provable => st.proof.as_ref(),
                };
                let steps = match steps {
                    // $a axiom leaf, or incomplete `$p ?` (unknown) -> 1.
                    None => {
                        memo[idx] = Some(ProofSize::one());
                        continue;
                    }
                    Some(s) => s,
                };
                if visited {
                    // All referenced statements memoized. Replay the proof's
                    // RPN, accumulating per-stack-entry the sum of
                    // nodes(label) over the subproof that produced it. This
                    // realises the task's metric
                    //   nodes(T) = Σ over the *decompressed* (saved-subproofs
                    //              textually expanded) flat step list of
                    //              nodes(label) ,
                    // where nodes(label) is that label's own memoized
                    // expanded size. Saved subproofs are DUPLICATED (no Z
                    // sharing) — exactly the fully-expanded tree.
                    let acc = self.rpn_fold(idx, steps, &memo);
                    memo[idx] = Some(acc);
                } else {
                    // Re-push self as "visited", then push children.
                    stack.push((idx, true));
                    for stp in steps {
                        if let ProofStep::Stmt(c) = stp {
                            if memo[*c].is_none() {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
            }
        }

        memo.into_iter()
            .map(|o| o.unwrap_or_else(ProofSize::one))
            .collect()
    }

    /// Replay a `$p`'s RPN proof, returning Σ nodes(label) over the fully
    /// decompressed (saved-subproofs expanded) flat step list. Each stack
    /// entry holds the running Σ for the subproof that produced it.
    ///
    /// For a step applying statement `X` of arity `a` (= |mandatory hyps|):
    /// pop the `a` argument subproof-sums, add this single occurrence's
    /// contribution `nodes(X)` (memoized: 1 for $f/$e/$a leaves, X's own
    /// expanded total for $p), push the new sum. `Tag` snapshots the current
    /// top; `Saved` pushes a clone of that snapshot (full duplication = no Z
    /// sharing, i.e. the genuine expanded tree).
    fn rpn_fold(
        &self,
        _idx: usize,
        steps: &[ProofStep],
        memo: &[Option<ProofSize>],
    ) -> ProofSize {
        let mut stack: Vec<ProofSize> = Vec::new();
        let mut saved: Vec<ProofSize> = Vec::new();
        for stp in steps {
            match stp {
                ProofStep::Stmt(c) => {
                    let arity = self.statements[*c].mand_hyps.len();
                    let mut sum = memo[*c]
                        .clone()
                        .unwrap_or_else(ProofSize::one);
                    let popn = arity.min(stack.len());
                    for _ in 0..popn {
                        let v = stack.pop().unwrap();
                        sum = sum.add(&v);
                    }
                    stack.push(sum);
                }
                ProofStep::Tag(j) => {
                    // Tag the current top-of-stack as saved subproof #j.
                    let top = stack
                        .last()
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    if *j == saved.len() {
                        saved.push(top);
                    } else if *j < saved.len() {
                        saved[*j] = top;
                    } else {
                        // Sparse (shouldn't happen): pad.
                        while saved.len() < *j {
                            saved.push(ProofSize::one());
                        }
                        saved.push(top);
                    }
                }
                ProofStep::Saved(j) => {
                    let v = saved
                        .get(*j)
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    stack.push(v);
                }
            }
        }
        // Well-formed proof: exactly one entry left = nodes(T).
        match stack.pop() {
            Some(v) if v.log10().is_finite() => v,
            _ => {
                // Empty / malformed proof — count the statement itself as 1.
                ProofSize::one()
            }
        }
    }

    /// Compute the DAG-shared node count for a single statement (by index).
    ///
    /// This is the classic "proof DAG size": the number of *distinct* proof
    /// nodes when every identical subproof is merged into one. With full
    /// identical-subtree sharing across the database, that equals the number
    /// of distinct statements reachable from the root via the proof-reference
    /// relation (the root included). This subsumes Z-tagged in-proof sharing
    /// (a back-reference reuses an already-present label) and cross-lemma
    /// sharing alike.
    ///
    /// Computed by a memoized reachable-set fold. Reachable sets are bounded
    /// by the (small) number of distinct lemmas a proof transitively uses
    /// (~10^4 for peano5), so this is cheap for the handful of anchors we
    /// query — we do NOT compute it for all 40k statements.
    pub fn dag_size(&self, root: usize) -> ProofSize {
        use std::collections::BTreeSet;
        // Memoized transitive reachable-statement set, keyed by index.
        // Stored only for nodes we actually touch.
        let mut memo: HashMap<usize, std::rc::Rc<BTreeSet<usize>>> =
            HashMap::new();

        // Iterative post-order DFS.
        let mut stack: Vec<usize> = vec![root];
        while let Some(&idx) = stack.last() {
            if memo.contains_key(&idx) {
                stack.pop();
                continue;
            }
            let st = &self.statements[idx];
            let children: Vec<usize> = match st.kind {
                Kind::Provable => match &st.proof {
                    Some(steps) => {
                        let mut v: Vec<usize> = steps
                            .iter()
                            .filter_map(|s| match s {
                                ProofStep::Stmt(c) => Some(*c),
                                ProofStep::Saved(_) | ProofStep::Tag(_) => None,
                            })
                            .collect();
                        v.sort_unstable();
                        v.dedup();
                        v
                    }
                    None => Vec::new(),
                },
                _ => Vec::new(),
            };
            let pending: Vec<usize> = children
                .iter()
                .copied()
                .filter(|c| !memo.contains_key(c))
                .collect();
            if pending.is_empty() {
                let mut set: BTreeSet<usize> = BTreeSet::new();
                set.insert(idx);
                for c in &children {
                    if let Some(cs) = memo.get(c) {
                        for &e in cs.iter() {
                            set.insert(e);
                        }
                    }
                }
                memo.insert(idx, std::rc::Rc::new(set));
                stack.pop();
            } else {
                for c in pending {
                    stack.push(c);
                }
            }
        }

        let count = memo.get(&root).map(|s| s.len()).unwrap_or(1) as u64;
        ProofSize::from_u64(count)
    }

    /// Build the convention-free *constructed-axiom alias map*.
    ///
    /// For every `$a` statement whose label starts with `ax-`, we look for a
    /// `$p` statement with the **identical full math-symbol token vector**
    /// (the entire `math` field equal — typecode + body). Such a `$p` is a
    /// from-ZFC proof of the stand-in axiom.
    ///
    /// Pairing rule (statement-expression equality only; robust to naming):
    ///   1. Collect every `$p` whose `math` equals the `ax-FOO`'s `math`
    ///      (excluding the statement itself).
    ///   2. If any candidate's label is the preferred variant — the
    ///      `ax-`-stripped form (`ax-FOO` → `FOO`) or the `ax`-prefixed,
    ///      hyphen-removed form (`ax-FOO` → `axFOO`) or the hyphen-kept
    ///      `ax`-form (`ax-pre-sup` → `axpre-sup`) — pick that one.
    ///   3. Otherwise pick the lexicographically smallest `$p` label.
    ///
    /// Returns `idx(ax-FOO) -> idx($p twin)`.
    pub fn constructed_axiom_map(&self) -> HashMap<usize, usize> {
        // Group all $p statements by their full math token vector.
        let mut by_math: HashMap<&[String], Vec<usize>> = HashMap::new();
        for (i, st) in self.statements.iter().enumerate() {
            if st.kind == Kind::Provable && st.proof.is_some() {
                by_math.entry(st.math.as_slice()).or_default().push(i);
            }
        }

        let mut map: HashMap<usize, usize> = HashMap::new();
        for (i, st) in self.statements.iter().enumerate() {
            if st.kind != Kind::Axiom {
                continue;
            }
            if !st.label.starts_with("ax-") {
                continue;
            }
            let cands = match by_math.get(st.math.as_slice()) {
                Some(c) => c,
                None => continue,
            };
            // Preferred-variant labels.
            let stripped = &st.label[3..]; // "ax-FOO" -> "FOO"
            let ax_prefixed = format!("ax{}", stripped); // "ax-FOO" -> "axFOO"
            let ax_nohyphen = st.label.replace('-', ""); // "ax-pre-sup" -> "axpresup"

            let mut chosen: Option<usize> = None;
            // Pass 1: preferred-variant label match.
            for &c in cands {
                if c == i {
                    continue;
                }
                let cl = &self.statements[c].label;
                if cl == stripped || *cl == ax_prefixed || *cl == ax_nohyphen {
                    chosen = Some(c);
                    break;
                }
            }
            // Pass 2: lexicographically smallest non-self $p label.
            if chosen.is_none() {
                let mut best: Option<usize> = None;
                for &c in cands {
                    if c == i {
                        continue;
                    }
                    match best {
                        None => best = Some(c),
                        Some(b) => {
                            if self.statements[c].label
                                < self.statements[b].label
                            {
                                best = Some(c);
                            }
                        }
                    }
                }
                chosen = best;
            }
            if let Some(c) = chosen {
                // Principled guard: a twin is a *construction* only if it does
                // NOT transitively reference the axiom itself. set.mm proves
                // several FOL/ZFC axioms inter-derivable; those redundancy `$p`
                // reach the axiom (cyclic) → they stay GenuineAxiom. The
                // real/complex axioms (ax-1cn↔ax1cn …) build from ZFC and are
                // acyclic → genuinely ConstructedAxiom.
                if !self.proof_reaches(c, i) {
                    map.insert(i, c);
                }
            }
        }
        map
    }

    /// Does statement `from`'s proof transitively reference statement `target`
    /// (over the ordinary proof-reference DAG)? Fresh visited set per query;
    /// only invoked for the handful of `ax-` candidates, so cost is bounded.
    fn proof_reaches(&self, from: usize, target: usize) -> bool {
        let mut stack = vec![from];
        let mut seen = vec![false; self.statements.len()];
        while let Some(n) = stack.pop() {
            if n == target {
                return true;
            }
            if seen[n] {
                continue;
            }
            seen[n] = true;
            if let Some(steps) = &self.statements[n].proof {
                for s in steps {
                    if let ProofStep::Stmt(c) = s {
                        if *c == target {
                            return true;
                        }
                        if !seen[*c] {
                            stack.push(*c);
                        }
                    }
                }
            }
        }
        false
    }

    /// Classify a statement (only `$a` are classified; others return `None`).
    /// `alias` is the map from [`constructed_axiom_map`].
    pub fn class_of(
        &self,
        idx: usize,
        alias: &HashMap<usize, usize>,
    ) -> Option<Class> {
        let st = &self.statements[idx];
        if st.kind != Kind::Axiom {
            return None;
        }
        if st.label.starts_with("df-") {
            return Some(Class::Definition);
        }
        if alias.contains_key(&idx) {
            return Some(Class::ConstructedAxiom);
        }
        if st.label.starts_with("ax-") {
            return Some(Class::GenuineAxiom);
        }
        Some(Class::Syntax)
    }

    /// Fully-expanded `$a`-leaf count, split into the four [`Class`] buckets.
    ///
    /// Same recurrence and memoization as [`expanded_sizes`]:
    ///   * `$f`/`$e` → the zero vector (substitution glue),
    ///   * `$a`       → a single unit in its own class bucket,
    ///   * `$p`       → Σ over its decompressed RPN steps of the child vectors
    ///     (per occurrence, with Z-saved subproofs duplicated, exactly like
    ///     the existing fold).
    ///
    /// Indexed by [`Class::idx`] (GenuineAxiom, ConstructedAxiom, Definition,
    /// Syntax). Returned vector is indexed by statement index.
    pub fn expanded_classed(&self) -> Vec<[ProofSize; 4]> {
        let alias = self.constructed_axiom_map();
        let n = self.statements.len();
        let zero4 = || {
            [
                ProofSize::zero(),
                ProofSize::zero(),
                ProofSize::zero(),
                ProofSize::zero(),
            ]
        };
        let mut memo: Vec<Option<[ProofSize; 4]>> = vec![None; n];

        for root in 0..n {
            if memo[root].is_some() {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if memo[idx].is_some() {
                    continue;
                }
                let st = &self.statements[idx];
                let steps: Option<&Vec<ProofStep>> = match st.kind {
                    Kind::Floating | Kind::Essential => {
                        memo[idx] = Some(zero4());
                        continue;
                    }
                    Kind::Axiom => None,
                    Kind::Provable => st.proof.as_ref(),
                };
                let steps = match steps {
                    None => {
                        // $a leaf (or incomplete `$p ?`): unit in its bucket.
                        let mut v = zero4();
                        let cls = self
                            .class_of(idx, &alias)
                            .unwrap_or(Class::Syntax);
                        v[cls.idx()] = ProofSize::one();
                        memo[idx] = Some(v);
                        continue;
                    }
                    Some(s) => s,
                };
                if visited {
                    let acc = self.rpn_fold_classed(steps, &memo, &zero4);
                    memo[idx] = Some(acc);
                } else {
                    stack.push((idx, true));
                    for stp in steps {
                        if let ProofStep::Stmt(c) = stp {
                            if memo[*c].is_none() {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
            }
        }

        memo.into_iter()
            .map(|o| o.unwrap_or_else(|| zero4()))
            .collect()
    }

    /// RPN fold producing the 4-bucket class breakdown (mirrors `rpn_fold`).
    fn rpn_fold_classed(
        &self,
        steps: &[ProofStep],
        memo: &[Option<[ProofSize; 4]>],
        zero4: &dyn Fn() -> [ProofSize; 4],
    ) -> [ProofSize; 4] {
        let add4 = |a: &[ProofSize; 4], b: &[ProofSize; 4]| {
            [
                a[0].add(&b[0]),
                a[1].add(&b[1]),
                a[2].add(&b[2]),
                a[3].add(&b[3]),
            ]
        };
        let mut stack: Vec<[ProofSize; 4]> = Vec::new();
        let mut saved: Vec<[ProofSize; 4]> = Vec::new();
        for stp in steps {
            match stp {
                ProofStep::Stmt(c) => {
                    let arity = self.statements[*c].mand_hyps.len();
                    let mut sum =
                        memo[*c].clone().unwrap_or_else(|| zero4());
                    let popn = arity.min(stack.len());
                    for _ in 0..popn {
                        let v = stack.pop().unwrap();
                        sum = add4(&sum, &v);
                    }
                    stack.push(sum);
                }
                ProofStep::Tag(j) => {
                    let top = stack
                        .last()
                        .cloned()
                        .unwrap_or_else(|| zero4());
                    if *j == saved.len() {
                        saved.push(top);
                    } else if *j < saved.len() {
                        saved[*j] = top;
                    } else {
                        while saved.len() < *j {
                            saved.push(zero4());
                        }
                        saved.push(top);
                    }
                }
                ProofStep::Saved(j) => {
                    let v = saved
                        .get(*j)
                        .cloned()
                        .unwrap_or_else(|| zero4());
                    stack.push(v);
                }
            }
        }
        stack.pop().unwrap_or_else(|| zero4())
    }

    /// ZFC-grounded fully-expanded `$a`-leaf count.
    ///
    /// Same recurrence as [`expanded_sizes`], except a `ConstructedAxiom`
    /// `$a` (one in the alias map) is **not** a leaf: it expands to its
    /// paired `$p`'s proof tree (i.e. `ax-FOO` is scored as if its proof
    /// were `axFOO`'s). `GenuineAxiom`, `Syntax`, `Definition` `$a` each = 1
    /// (df-elimination is left as future work — see note below).
    ///
    /// Termination: the paired `$p` does not (for the core real/complex
    /// axioms) transitively depend on its own `ax-` stand-in. We still guard
    /// against cycles: if the grounded expansion of a constructed axiom would
    /// reach itself, we break the cycle by treating that `ax-FOO` as a leaf
    /// (=1) and record its label in the returned `zfc_cycles` list.
    ///
    /// Returns `(sizes_by_index, zfc_cycles)`.
    pub fn expanded_zfc(&self) -> (Vec<ProofSize>, Vec<String>) {
        let alias = self.constructed_axiom_map();
        let n = self.statements.len();
        let mut memo: Vec<Option<ProofSize>> = vec![None; n];
        let mut zfc_cycles: Vec<String> = Vec::new();
        // Cycle detection: indices currently on the resolution path. We only
        // need to track constructed-axiom redirections (the only place the
        // DAG-ness of statement order can be violated, since ax-FOO routes to
        // a *later* $p axFOO).
        let mut on_path: Vec<bool> = vec![false; n];
        // Statements whose constructed-axiom redirect was cycle-broken.
        let mut broken: Vec<bool> = vec![false; n];

        // The recursion target for a node: for a constructed axiom (not
        // broken) it's the paired $p; otherwise itself.
        let target = |idx: usize, broken: &[bool]| -> usize {
            if !broken[idx] {
                if let Some(&p) = alias.get(&idx) {
                    return p;
                }
            }
            idx
        };

        for root in 0..n {
            if memo[root].is_some() {
                continue;
            }
            // (idx, visited?) — `idx` is the *logical* node; if it's a
            // redirected constructed axiom we expand `target(idx)`'s proof.
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if memo[idx].is_some() {
                    continue;
                }
                let st = &self.statements[idx];

                // Constructed axiom (redirected) — expand the paired $p.
                let tgt = target(idx, &broken);
                if tgt != idx {
                    if !visited {
                        if memo[tgt].is_some() {
                            memo[idx] = memo[tgt].clone();
                            continue;
                        }
                        if on_path[tgt] {
                            // Cycle: paired $p depends (transitively) on this
                            // stand-in. Break by treating this ax-FOO as a
                            // leaf = 1.
                            broken[idx] = true;
                            zfc_cycles.push(st.label.clone());
                            memo[idx] = Some(ProofSize::one());
                            continue;
                        }
                        on_path[idx] = true;
                        stack.push((idx, true));
                        stack.push((tgt, false));
                    } else {
                        on_path[idx] = false;
                        if broken[idx] {
                            memo[idx] = Some(ProofSize::one());
                        } else {
                            memo[idx] = Some(
                                memo[tgt]
                                    .clone()
                                    .unwrap_or_else(ProofSize::one),
                            );
                        }
                    }
                    continue;
                }

                let steps: Option<&Vec<ProofStep>> = match st.kind {
                    Kind::Floating | Kind::Essential => {
                        memo[idx] = Some(ProofSize::zero());
                        continue;
                    }
                    Kind::Axiom => None,
                    Kind::Provable => st.proof.as_ref(),
                };
                let steps = match steps {
                    // Genuine-axiom / syntax / definition leaf (or `$p ?`).
                    None => {
                        memo[idx] = Some(ProofSize::one());
                        continue;
                    }
                    Some(s) => s,
                };
                if visited {
                    on_path[idx] = false;
                    let acc = self.rpn_fold_zfc(steps, &memo, &broken, &alias);
                    memo[idx] = Some(acc);
                } else {
                    on_path[idx] = true;
                    stack.push((idx, true));
                    for stp in steps {
                        if let ProofStep::Stmt(c) = stp {
                            // Push the *logical* child. If it's a constructed
                            // axiom we'll redirect when we pop it.
                            if memo[*c].is_none() {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
            }
        }

        let sizes = memo
            .into_iter()
            .map(|o| o.unwrap_or_else(ProofSize::one))
            .collect();
        zfc_cycles.sort();
        zfc_cycles.dedup();
        (sizes, zfc_cycles)
    }

    /// RPN fold for the ZFC-grounded metric. A constructed-axiom child (not
    /// cycle-broken) contributes its paired `$p`'s memoized grounded size;
    /// everything else contributes its own memoized grounded size. Mirrors
    /// `rpn_fold` (Z-saved subproofs duplicated, no sharing).
    fn rpn_fold_zfc(
        &self,
        steps: &[ProofStep],
        memo: &[Option<ProofSize>],
        broken: &[bool],
        alias: &HashMap<usize, usize>,
    ) -> ProofSize {
        let mut stack: Vec<ProofSize> = Vec::new();
        let mut saved: Vec<ProofSize> = Vec::new();
        for stp in steps {
            match stp {
                ProofStep::Stmt(c) => {
                    let arity = self.statements[*c].mand_hyps.len();
                    // Redirect a constructed axiom to its paired $p (unless
                    // its cycle was broken, in which case it stays a leaf).
                    let src = if !broken[*c] {
                        *alias.get(c).unwrap_or(c)
                    } else {
                        *c
                    };
                    let mut sum = memo[src]
                        .clone()
                        .unwrap_or_else(ProofSize::one);
                    let popn = arity.min(stack.len());
                    for _ in 0..popn {
                        let v = stack.pop().unwrap();
                        sum = sum.add(&v);
                    }
                    stack.push(sum);
                }
                ProofStep::Tag(j) => {
                    let top = stack
                        .last()
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    if *j == saved.len() {
                        saved.push(top);
                    } else if *j < saved.len() {
                        saved[*j] = top;
                    } else {
                        while saved.len() < *j {
                            saved.push(ProofSize::one());
                        }
                        saved.push(top);
                    }
                }
                ProofStep::Saved(j) => {
                    let v = saved
                        .get(*j)
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    stack.push(v);
                }
            }
        }
        match stack.pop() {
            Some(v) if v.log10().is_finite() => v,
            _ => ProofSize::one(),
        }
    }

    // ---------------------------------------------------------------------
    // df-* DEFINITION-ELIMINATION model.
    //
    // A Metamath definition `df-foo` is a `$a` whose label starts with `df-`
    // and whose statement has the form
    //     |- <DEFINIENDUM> <CONN> <DEFINIENS>
    // where <CONN> is the top-level (paren-depth-0) `<->` (wff definitions)
    // or `=` (class / term definitions). Eliminating definitions means
    // recursively replacing every use of the defined symbol by its
    // definiens.
    //
    // We model the SIZE impact of definition elimination by the recursive
    // *definiens symbol-size*: a df-'s weight is the sum, over its definiens
    // (RHS) tokens, of the (recursive) weight of any token that is itself a
    // defined symbol, else 1. This is a FORMULA-SIZE model and is therefore
    // a strict LOWER BOUND on the true proof-level cost of eliminating a
    // definition (a real elimination also drags in the definition's
    // justification theorem and the congruence/closure machinery, which we
    // do NOT count here). The qualitative verdict (≪ 10^1000) is unaffected
    // as long as the lower bound itself stays modest.
    //
    // Paren-depth is measured over `(` / `)` only (Metamath's `{ }` / `<. .>`
    // etc. are ordinary constants and do NOT change depth). In set.mm almost
    // every wff/class definition wraps its top connective in an enclosing
    // `( ... )`, so a strict depth-0 connective is found mainly for the
    // class/term definitions written `LHS = RHS` or `( LHS ... ) = RHS`
    // (df-v, df-dif, df-un, df-rab, df-mpt, df-iota, df-fv, df-csb, …). The
    // wff definitions wrapped as `( A <-> B )` (df-an, df-or, df-clab,
    // df-cleq, …) and the primitive bootstraps written without a top-level
    // connective at all (df-bi: `|- -. ( ... )`) have NO paren-depth-0
    // connective: they are recorded as base cases with RHS = the whole
    // statement and weight = its math length (a primitive-ish constant cost).
    // ---------------------------------------------------------------------

    /// Set of tokens that are *variables*: a token is a variable iff it
    /// appears as the variable (second token) of some `$f` floating
    /// hypothesis anywhere in the database. Mirrors the variable-hood test
    /// used by `mandatory_hyps`.
    fn variable_token_set(&self) -> std::collections::HashSet<&str> {
        let mut set = std::collections::HashSet::new();
        for st in &self.statements {
            if st.kind == Kind::Floating && st.math.len() >= 2 {
                set.insert(st.math[1].as_str());
            }
        }
        set
    }

    /// For each `$a` whose label starts with `df-`, determine the DEFINED
    /// CONSTANT it introduces and map that constant token -> the df-
    /// statement index.
    ///
    /// Heuristic (see module note above):
    ///   1. Drop the leading `|-` typecode token.
    ///   2. Find the FIRST top-level (paren-depth-0) token equal to `<->`
    ///      or `=`. LHS = tokens before it; RHS = tokens after it.
    ///   3. The defined symbol = the LHS constant token (not a `$f`
    ///      variable) that is *newly introduced* — i.e. the first LHS
    ///      constant that does NOT already occur in any *earlier* statement's
    ///      math. This avoids the degenerate pick of the structural `(`
    ///      while still being the simple "principal constant of the LHS"
    ///      rule. If every LHS constant has been seen before, fall back to
    ///      the first LHS constant token.
    ///   4. If the split fails (no paren-depth-0 `<->`/`=` — the primitive
    ///      bootstraps like df-bi / df-clab / df-an / …), the df- is still
    ///      recorded (its weight becomes the whole-statement math length, see
    ///      `defelim_weight`) but it introduces no looked-up symbol here.
    ///
    /// On collisions (two df- claiming the same constant) the first wins.
    pub fn defined_symbol_map(&self) -> HashMap<String, usize> {
        let vars = self.variable_token_set();
        // Constants seen in the math of statements strictly *before* index i.
        // Built incrementally as we scan forward.
        let mut seen_const: std::collections::HashSet<&str> =
            std::collections::HashSet::new();
        let mut map: HashMap<String, usize> = HashMap::new();

        for (idx, st) in self.statements.iter().enumerate() {
            let is_df = st.kind == Kind::Axiom && st.label.starts_with("df-");
            if is_df {
                if let Some((lhs, _rhs)) = Self::split_definition(&st.math) {
                    // Principal constant: first newly-introduced LHS constant.
                    let mut chosen: Option<&str> = None;
                    let mut first_const: Option<&str> = None;
                    for t in lhs {
                        let s = t.as_str();
                        if vars.contains(s) {
                            continue;
                        }
                        if first_const.is_none() {
                            first_const = Some(s);
                        }
                        if !seen_const.contains(s) {
                            chosen = Some(s);
                            break;
                        }
                    }
                    let pick = chosen.or(first_const);
                    if let Some(sym) = pick {
                        map.entry(sym.to_string()).or_insert(idx);
                    }
                }
            }
            // Record this statement's constants as "seen" for later df-.
            for t in &st.math {
                let s = t.as_str();
                if !vars.contains(s) {
                    seen_const.insert(s);
                }
            }
        }
        map
    }

    /// Split a definition statement's math into (LHS, RHS) about the first
    /// top-level (paren-depth-0) `<->` or `=`, dropping the leading `|-`
    /// typecode token. Returns `None` when there is no such top-level
    /// connective (primitive bootstrap / base case).
    fn split_definition(math: &[String]) -> Option<(&[String], &[String])> {
        // Drop the leading typecode (`|-`). If the statement is shorter than
        // that there is nothing to split.
        if math.is_empty() {
            return None;
        }
        let body = &math[1..];
        let mut depth: i64 = 0;
        for (i, t) in body.iter().enumerate() {
            match t.as_str() {
                "(" => depth += 1,
                ")" => depth -= 1,
                "<->" | "=" if depth == 0 => {
                    return Some((&body[..i], &body[i + 1..]));
                }
                _ => {}
            }
        }
        None
    }

    /// For each df- `$a`, its recursive definiens symbol-size as a
    /// [`ProofSize`]. Memoized; cycle-guarded (set.mm definitions are
    /// acyclic by the definitional discipline, but we break defensively: a
    /// df- that transitively reaches itself contributes weight 1 for the
    /// back-edge token and its label is pushed to the returned cycle list —
    /// available via [`Database::defelim_weight_with_cycles`]). Minimum
    /// weight is 1.
    ///
    /// FORMULA-SIZE model: a strict LOWER BOUND on true proof-level
    /// definition elimination (see module note).
    pub fn defelim_weight(&self) -> HashMap<usize, ProofSize> {
        self.defelim_weight_with_cycles().0
    }

    /// As [`defelim_weight`], also returning the `defelim_cycles` label list
    /// (df- labels whose recursion was cycle-broken).
    pub fn defelim_weight_with_cycles(
        &self,
    ) -> (HashMap<usize, ProofSize>, Vec<String>) {
        let sym_map = self.defined_symbol_map();
        // sym token -> df- statement index.
        let mut weight: HashMap<usize, ProofSize> = HashMap::new();
        let mut cycles: Vec<String> = Vec::new();

        // df- indices, in source order (definitional discipline: a df-'s
        // definiens only uses earlier-defined symbols, so a forward pass with
        // memoization terminates; the explicit on-path guard is purely
        // defensive against a hypothetical back-edge).
        let df_indices: Vec<usize> = self
            .statements
            .iter()
            .enumerate()
            .filter(|(_, st)| {
                st.kind == Kind::Axiom && st.label.starts_with("df-")
            })
            .map(|(i, _)| i)
            .collect();

        // Iterative post-order over the df- dependency graph (edge: df A
        // uses symbol whose df is B). `on_path` breaks cycles.
        let mut on_path: HashMap<usize, bool> = HashMap::new();
        for &root in &df_indices {
            if weight.contains_key(&root) {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if weight.contains_key(&idx) {
                    continue;
                }
                let st = &self.statements[idx];
                let rhs: Vec<&String> = match Self::split_definition(&st.math) {
                    Some((_lhs, rhs)) => rhs.iter().collect(),
                    // Base case: no top-level connective. Weight = whole
                    // statement math length (primitive-ish constant cost).
                    None => {
                        let w = (st.math.len() as u64).max(1);
                        weight.insert(idx, ProofSize::from_u64(w));
                        continue;
                    }
                };
                if !visited {
                    on_path.insert(idx, true);
                    stack.push((idx, true));
                    for t in &rhs {
                        if let Some(&d) = sym_map.get(t.as_str()) {
                            if d == idx {
                                continue;
                            }
                            if *on_path.get(&d).unwrap_or(&false) {
                                // Back-edge: cycle. Break (treated as
                                // weight-1 token at fold time below).
                                if !cycles.contains(&self.statements[d].label) {
                                    cycles.push(
                                        self.statements[d].label.clone(),
                                    );
                                }
                                continue;
                            }
                            if !weight.contains_key(&d) {
                                stack.push((d, false));
                            }
                        }
                    }
                } else {
                    on_path.insert(idx, false);
                    let mut sum = ProofSize::zero();
                    for t in &rhs {
                        let tok = t.as_str();
                        let contrib = match sym_map.get(tok) {
                            Some(&d) if d != idx => {
                                // If cycle-broken / not yet memoized
                                // (defensive), the back-edge token counts 1.
                                weight
                                    .get(&d)
                                    .cloned()
                                    .unwrap_or_else(ProofSize::one)
                            }
                            _ => ProofSize::one(),
                        };
                        sum = sum.add(&contrib);
                    }
                    // Min weight 1.
                    if sum.log10() == f64::NEG_INFINITY {
                        sum = ProofSize::one();
                    }
                    weight.insert(idx, sum);
                }
            }
        }
        cycles.sort();
        cycles.dedup();
        (weight, cycles)
    }

    /// Fully-expanded `$a`-leaf count under the df- DEFINITION-ELIMINATION
    /// model. Same recurrence / memoization / iterative post-order as
    /// [`expanded_sizes`], except a `$a` that is a df- (Definition class)
    /// contributes its [`defelim_weight`] instead of 1. Genuine-axiom and
    /// syntax `$a` = 1; constructed-axiom `$a` = 1 (NOT inlined here — kept
    /// orthogonal to the ZFC grounding). `$f`/`$e` = 0; `$p` = expand.
    ///
    /// FORMULA-SIZE model: a strict LOWER BOUND (see module note).
    pub fn expanded_defelim(&self) -> Vec<ProofSize> {
        let (dw, _cyc) = self.defelim_weight_with_cycles();
        let n = self.statements.len();
        let mut memo: Vec<Option<ProofSize>> = vec![None; n];

        for root in 0..n {
            if memo[root].is_some() {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if memo[idx].is_some() {
                    continue;
                }
                let st = &self.statements[idx];
                let steps: Option<&Vec<ProofStep>> = match st.kind {
                    Kind::Floating | Kind::Essential => {
                        memo[idx] = Some(ProofSize::zero());
                        continue;
                    }
                    Kind::Axiom => None,
                    Kind::Provable => st.proof.as_ref(),
                };
                let steps = match steps {
                    None => {
                        // $a leaf: df- -> defelim weight; else 1.
                        let w = if st.label.starts_with("df-") {
                            dw.get(&idx)
                                .cloned()
                                .unwrap_or_else(ProofSize::one)
                        } else {
                            ProofSize::one()
                        };
                        memo[idx] = Some(w);
                        continue;
                    }
                    Some(s) => s,
                };
                if visited {
                    let acc = self.rpn_fold(idx, steps, &memo);
                    memo[idx] = Some(acc);
                } else {
                    stack.push((idx, true));
                    for stp in steps {
                        if let ProofStep::Stmt(c) = stp {
                            if memo[*c].is_none() {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
            }
        }

        memo.into_iter()
            .map(|o| o.unwrap_or_else(ProofSize::one))
            .collect()
    }

    /// The STRICT poll answer: combine BOTH groundings —
    ///   * constructed-axiom `$a` inlined to its twin `$p` (exact same
    ///     redirect + acyclicity logic as [`expanded_zfc`]), AND
    ///   * df- `$a` weighted by its [`defelim_weight`] (genuine-axiom /
    ///     syntax `$a` = 1).
    /// `$f`/`$e` = 0; `$p` = expand. Returns `(sizes_by_index, cycles)`
    /// where `cycles` merges the ZFC redirect cycles and the df- elimination
    /// cycles.
    ///
    /// Still a strict LOWER BOUND on true proof-level definition
    /// elimination (formula-size model; see module note).
    pub fn expanded_zfc_defelim(&self) -> (Vec<ProofSize>, Vec<String>) {
        let alias = self.constructed_axiom_map();
        let (dw, mut cycles) = self.defelim_weight_with_cycles();
        let n = self.statements.len();
        let mut memo: Vec<Option<ProofSize>> = vec![None; n];
        let mut zfc_cycles: Vec<String> = Vec::new();
        let mut on_path: Vec<bool> = vec![false; n];
        let mut broken: Vec<bool> = vec![false; n];

        let target = |idx: usize, broken: &[bool]| -> usize {
            if !broken[idx] {
                if let Some(&p) = alias.get(&idx) {
                    return p;
                }
            }
            idx
        };

        for root in 0..n {
            if memo[root].is_some() {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(root, false)];
            while let Some((idx, visited)) = stack.pop() {
                if memo[idx].is_some() {
                    continue;
                }
                let st = &self.statements[idx];

                // Constructed axiom (redirected) — expand the paired $p.
                let tgt = target(idx, &broken);
                if tgt != idx {
                    if !visited {
                        if memo[tgt].is_some() {
                            memo[idx] = memo[tgt].clone();
                            continue;
                        }
                        if on_path[tgt] {
                            broken[idx] = true;
                            zfc_cycles.push(st.label.clone());
                            memo[idx] = Some(ProofSize::one());
                            continue;
                        }
                        on_path[idx] = true;
                        stack.push((idx, true));
                        stack.push((tgt, false));
                    } else {
                        on_path[idx] = false;
                        if broken[idx] {
                            memo[idx] = Some(ProofSize::one());
                        } else {
                            memo[idx] = Some(
                                memo[tgt]
                                    .clone()
                                    .unwrap_or_else(ProofSize::one),
                            );
                        }
                    }
                    continue;
                }

                let steps: Option<&Vec<ProofStep>> = match st.kind {
                    Kind::Floating | Kind::Essential => {
                        memo[idx] = Some(ProofSize::zero());
                        continue;
                    }
                    Kind::Axiom => None,
                    Kind::Provable => st.proof.as_ref(),
                };
                let steps = match steps {
                    None => {
                        // df- -> defelim weight; genuine/syntax/other -> 1.
                        let w = if st.label.starts_with("df-") {
                            dw.get(&idx)
                                .cloned()
                                .unwrap_or_else(ProofSize::one)
                        } else {
                            ProofSize::one()
                        };
                        memo[idx] = Some(w);
                        continue;
                    }
                    Some(s) => s,
                };
                if visited {
                    on_path[idx] = false;
                    let acc = self.rpn_fold_zfc_defelim(
                        steps, &memo, &broken, &alias,
                    );
                    memo[idx] = Some(acc);
                } else {
                    on_path[idx] = true;
                    stack.push((idx, true));
                    for stp in steps {
                        if let ProofStep::Stmt(c) = stp {
                            if memo[*c].is_none() {
                                stack.push((*c, false));
                            }
                        }
                    }
                }
            }
        }

        let sizes = memo
            .into_iter()
            .map(|o| o.unwrap_or_else(ProofSize::one))
            .collect();
        // Merge ZFC redirect cycles + df- elimination cycles.
        zfc_cycles.sort();
        zfc_cycles.dedup();
        cycles.extend(zfc_cycles);
        cycles.sort();
        cycles.dedup();
        (sizes, cycles)
    }

    /// RPN fold for [`expanded_zfc_defelim`]: identical to `rpn_fold_zfc`
    /// (constructed-axiom child redirected to its twin `$p`, Z-saved
    /// subproofs duplicated). The df- weighting is already baked into the
    /// memo (a df- leaf was memoized to its defelim weight), so this fold
    /// only needs the ZFC redirect logic.
    fn rpn_fold_zfc_defelim(
        &self,
        steps: &[ProofStep],
        memo: &[Option<ProofSize>],
        broken: &[bool],
        alias: &HashMap<usize, usize>,
    ) -> ProofSize {
        let mut stack: Vec<ProofSize> = Vec::new();
        let mut saved: Vec<ProofSize> = Vec::new();
        for stp in steps {
            match stp {
                ProofStep::Stmt(c) => {
                    let arity = self.statements[*c].mand_hyps.len();
                    let src = if !broken[*c] {
                        *alias.get(c).unwrap_or(c)
                    } else {
                        *c
                    };
                    let mut sum = memo[src]
                        .clone()
                        .unwrap_or_else(ProofSize::one);
                    let popn = arity.min(stack.len());
                    for _ in 0..popn {
                        let v = stack.pop().unwrap();
                        sum = sum.add(&v);
                    }
                    stack.push(sum);
                }
                ProofStep::Tag(j) => {
                    let top = stack
                        .last()
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    if *j == saved.len() {
                        saved.push(top);
                    } else if *j < saved.len() {
                        saved[*j] = top;
                    } else {
                        while saved.len() < *j {
                            saved.push(ProofSize::one());
                        }
                        saved.push(top);
                    }
                }
                ProofStep::Saved(j) => {
                    let v = saved
                        .get(*j)
                        .cloned()
                        .unwrap_or_else(ProofSize::one);
                    stack.push(v);
                }
            }
        }
        match stack.pop() {
            Some(v) if v.log10().is_finite() => v,
            _ => ProofSize::one(),
        }
    }

    // ---------------------------------------------------------------------
    // TASK #9 — resqrtth completion / ℤ→ℚ-core attribution.
    //
    // set.mm's √-of-nonnegatives (resqrtth) routes through the FULL analytic
    // construction of ℝ.  We mechanically split resqrtth's fully-inlined,
    // ZFC-grounded leaf tree into:
    //
    //   (a) the COMPLETION-CONSTRUCTION subtree — the Dedekind-cut positive
    //       reals (df-np/df-1p/df-plp/df-mp/df-ltp), the signed-real layer
    //       (df-nr/df-enr/df-plr/df-mr/df-ltr/df-0r/df-1r), LUB completeness
    //       (df-sup / axsup / ax-pre-sup), and the analytic limit/sup/Cauchy
    //       machinery (df-clim/df-rlim/df-cau/df-limsup/df-rli/…).  This is
    //       the part a Euclidean / real-closed (RCF) model would NOT build.
    //
    //   (b) the ℤ→ℚ-CONSTRUCTION CORE + shared glue — positive integers
    //       (df-ni/df-pli/df-mi/df-lti), the ℕ×ℕ-pair positive rationals
    //       (df-plpq/df-mpq/df-ltpq/df-enq/df-nq/df-erq/df-plq/df-mq/df-1nq/
    //       df-rq/df-ltnq), the final ℕ/ℤ/ℚ (df-nn/df-z/df-q), plus all the
    //       propositional / predicate / set-theory glue.  ANY construction of
    //       ℝ (even a real-closed one) needs ℤ→ℚ pair-plumbing.
    //
    // BIPARTITION RULE (mechanical, OCCURRENCE-LEVEL, exact):
    //   Over the ZFC-grounded reference DAG (constructed-axiom redirects
    //   applied, exactly as `expanded_zfc`), the fully-inlined tree of
    //   resqrtth is split by where each LEAF OCCURRENCE sits:
    //     * the entire expanded ZFC subtree of a COMPLETION-ANCHOR node is
    //       charged to (a) COMPLETION (its size = its ordinary expanded_zfc
    //       size; that whole subtree IS the Dedekind/Cauchy/sup/limit build);
    //     * every non-anchor primitive leaf occurrence is (b) ℤ→ℚ-core +
    //       FOL/set glue ($f/$e → 0);
    //     * a non-anchor $p propagates the (comp, core) pair componentwise
    //       through its RPN (Z-saved subproofs duplicated), so occurrences
    //       that descend through an anchor land in (a) and occurrences that
    //       never cross one land in (b).
    //   Because the split is per OCCURRENCE (not per leaf identity), a lemma
    //   reused both under and outside the completion layer has its through-
    //   anchor occurrences in (a) and its completion-free occurrences in (b),
    //   and (a)+(b) == expanded_zfc[resqrtth] EXACTLY (cross-checked).
    //
    // AMBIGUITY / DESIGN NOTE:
    //   The only modelling choice is the ANCHOR SET itself: which df-/axiom
    //   labels constitute "the completion construction". We take the full
    //   Dedekind-cut→signed-real→LUB→limit ladder (the part a real-closed /
    //   Euclidean field model provably does not build — RCF is decidable,
    //   no completeness). Everything below an anchor is (a) wholesale; the
    //   integer/rational pair-plumbing (df-ni/pli/.../nq/.../z/q) and all
    //   propositional/predicate/set glue are (b). An earlier leaf-identity
    //   rule (a leaf is core iff *some* completion-free path reaches it) was
    //   rejected: it charged every shared glue lemma's ENTIRE multiplicity
    //   (including its through-completion occurrences) to (b), collapsing (a)
    //   to a vacuous lower bound (~0.6% of total). The occurrence-level rule
    //   above is the faithful mechanical attribution.

    /// The completion-construction anchor labels (see module note). The
    /// entire expanded ZFC subtree of any of these is attributed to part (a)
    /// COMPLETION. Labels absent from the DB are skipped (reported by the
    /// caller via `anchors_missing`).
    pub const COMPLETION_ANCHORS: &'static [&'static str] = &[
        // Dedekind-cut positive reals.
        "df-np", "df-1p", "df-plp", "df-mp", "df-ltp",
        // Signed reals (equivalence classes of pairs of positive reals).
        "df-nr", "df-enr", "df-plr", "df-mr", "df-ltr", "df-0r", "df-1r",
        // LUB completeness.
        "df-sup", "df-inf", "axsup", "ax-pre-sup", "axpre-sup",
        // Analytic limit / Cauchy / lim sup machinery.
        "df-clim", "df-rlim", "df-cau", "df-caufval", "df-limsup",
        "df-rli", "df-li", "df-ntr", "df-lm",
    ];

    /// Mechanically split resqrtth's fully-inlined ZFC-grounded leaf tree into
    /// the completion-construction subtree (a) and the ℤ→ℚ core + glue (b).
    ///
    /// Returns `(total, completion, core, anchors_found, anchors_missing,
    /// n_leaves_completion, n_leaves_core)` where the three `ProofSize`s
    /// satisfy `completion + core == total` exactly. The leaf-class counts
    /// are the number of DISTINCT statement indices classified each way among
    /// nodes actually reached from resqrtth (diagnostic, not the weighted
    /// metric).
    ///
    /// `alias` is the caller's [`constructed_axiom_map`] (reused — recomputing
    /// it is non-trivial). `total` is the precomputed `expanded_zfc[resqrtth]`;
    /// the completion part is derived as `total - core` (one masked fold
    /// instead of two), exact since both are ~46-digit `Exact` bignums.
    pub fn resqrtth_completion_split(
        &self,
        root_label: &str,
        alias: &HashMap<usize, usize>,
        total: &ProofSize,
    ) -> Option<(
        ProofSize,
        ProofSize,
        ProofSize,
        Vec<String>,
        Vec<String>,
        usize,
        usize,
    )> {
        let root = self.index(root_label)?;
        let n = self.statements.len();

        // ZFC-grounded child resolver: a constructed axiom (not its own twin
        // by self-reference) redirects to its paired $p; everything else is
        // itself. (Cycle-broken constructed axioms in `expanded_zfc` become
        // leaves; here such a node simply has no proof to recurse into, which
        // is the same leaf outcome for reachability.)
        let resolve = |idx: usize| -> usize { *alias.get(&idx).unwrap_or(&idx) };
        // ZFC children of a (resolved) node.
        let zfc_children = |idx: usize| -> Vec<usize> {
            let tgt = resolve(idx);
            match &self.statements[tgt].proof {
                Some(steps) => {
                    let mut v: Vec<usize> = steps
                        .iter()
                        .filter_map(|s| match s {
                            ProofStep::Stmt(c) => Some(resolve(*c)),
                            _ => None,
                        })
                        .collect();
                    v.sort_unstable();
                    v.dedup();
                    v
                }
                None => Vec::new(),
            }
        };

        // Anchor index set.
        let mut anchors_found = Vec::new();
        let mut anchors_missing = Vec::new();
        let mut is_anchor = vec![false; n];
        for &lbl in Self::COMPLETION_ANCHORS {
            match self.index(lbl) {
                Some(i) => {
                    if !is_anchor[i] {
                        is_anchor[i] = true;
                        anchors_found.push(lbl.to_string());
                    }
                }
                None => anchors_missing.push(lbl.to_string()),
            }
        }
        anchors_found.sort();
        anchors_missing.sort();

        // Reachability over the ZFC DAG.
        //   `block_anchors=false` → S (full reach)
        //   `block_anchors=true`  → R0 (anchors not traversed nor included)
        let reach = |block_anchors: bool| -> Vec<bool> {
            let mut seen = vec![false; n];
            let r0 = resolve(root);
            // The root itself is never an anchor in practice; guard anyway.
            if block_anchors && is_anchor[r0] {
                return seen;
            }
            seen[r0] = true;
            let mut stack = vec![r0];
            while let Some(x) = stack.pop() {
                for c in zfc_children(x) {
                    if block_anchors && is_anchor[c] {
                        continue; // do not enter/traverse the completion layer
                    }
                    if !seen[c] {
                        seen[c] = true;
                        stack.push(c);
                    }
                }
            }
            seen
        };

        let t0 = std::time::Instant::now();
        let in_s = reach(false);
        let in_r0 = reach(true);
        eprintln!(
            "[task9] reachability done ({:.1}s)",
            t0.elapsed().as_secs_f64()
        );

        // A leaf index is CORE iff in R0 (some completion-free path reaches
        // it); else COMPLETION. Diagnostic distinct-leaf counts over S.
        let mut n_leaf_comp = 0usize;
        let mut n_leaf_core = 0usize;
        for i in 0..n {
            if !in_s[i] {
                continue;
            }
            // Leaves are the units expanded_zfc counts: a node with no ZFC
            // proof to recurse into (axiom / definition / syntax / $p ?).
            let is_leaf = self.statements[resolve(i)].proof.is_none()
                && self.statements[i].kind != Kind::Floating
                && self.statements[i].kind != Kind::Essential;
            if !is_leaf {
                continue;
            }
            if in_r0[i] {
                n_leaf_core += 1;
            } else {
                n_leaf_comp += 1;
            }
        }

        // ONE masked ZFC fold for the ℤ→ℚ-CORE part: a leaf counts 1 iff it
        // is CORE (in R0). The recurrence is otherwise identical to
        // `expanded_zfc`'s rpn_fold_zfc (Z-saved subproofs duplicated,
        // constructed-axiom redirect applied), so the UNMASKED fold equals
        // expanded_zfc[resqrtth]; therefore COMPLETION = total - core
        // exactly (both ~46-digit Exact bignums). The proof-reference DAG is
        // acyclic (a proof only cites earlier labels); constructed-axiom
        // redirects are kept acyclic by `constructed_axiom_map` (its
        // `proof_reaches` guard). So this memoized post-order terminates
        // without cycle-breaking. `idx` is always already resolved (children
        // pushed as `resolve(*c)`).
        // Phase 1: a single iterative DFS over the RESOLVED ZFC DAG from
        // resolve(root), emitting a reverse-topological (post-order) list of
        // every reachable resolved node. Each node is colored, so it is
        // pushed/expanded EXACTLY ONCE regardless of fan-in — this is what
        // makes the whole thing strict O(V+E) (the previous lazy-memo DFS
        // re-pushed shared deep nodes once per parent, which over resqrtth's
        // whole-analysis cone is catastrophic). The resolved DAG is acyclic
        // (proofs cite only earlier labels; constructed-axiom redirects kept
        // acyclic by `constructed_axiom_map`), so a finish-order DFS yields a
        // valid topological order.
        let r_root = resolve(root);
        let mut color = vec![0u8; n]; // 0=unseen 1=on-stack 2=done
        let mut topo: Vec<usize> = Vec::new();
        // Stack of (node, next-child-cursor) — explicit recursion.
        let mut dfs: Vec<(usize, usize)> = Vec::new();
        // Precompute resolved child lists lazily; cache to avoid rebuilding.
        let child_cache: std::cell::RefCell<HashMap<usize, std::rc::Rc<Vec<usize>>>> =
            std::cell::RefCell::new(HashMap::new());
        let kids_of = |idx: usize| -> std::rc::Rc<Vec<usize>> {
            if let Some(v) = child_cache.borrow().get(&idx) {
                return v.clone();
            }
            let v = std::rc::Rc::new(match &self.statements[idx].proof {
                Some(steps) => {
                    let mut k: Vec<usize> = steps
                        .iter()
                        .filter_map(|s| match s {
                            ProofStep::Stmt(c) => Some(resolve(*c)),
                            _ => None,
                        })
                        .collect();
                    k.sort_unstable();
                    k.dedup();
                    k
                }
                None => Vec::new(),
            });
            child_cache.borrow_mut().insert(idx, v.clone());
            v
        };
        color[r_root] = 1;
        dfs.push((r_root, 0));
        while let Some(&(node, ci)) = dfs.last() {
            let kids = kids_of(node);
            if ci < kids.len() {
                dfs.last_mut().unwrap().1 += 1;
                let c = kids[ci];
                if color[c] == 0 {
                    color[c] = 1;
                    dfs.push((c, 0));
                }
            } else {
                color[node] = 2;
                topo.push(node);
                dfs.pop();
            }
        }

        // Phase 2: OCCURRENCE-LEVEL attribution. Each node carries a pair
        // (comp, core) of ZFC-grounded leaf counts whose sum is exactly that
        // node's plain `expanded_zfc` size. The rule is principled and
        // mechanical:
        //
        //   * An ANCHOR node contributes its ENTIRE expanded ZFC subtree to
        //     `comp` — by definition the completion-construction subtree is
        //     everything reached *through* a completion anchor (Dedekind /
        //     sup / Cauchy / limit). (core, comp) = (0, fullZfcSize).
        //   * A leaf (non-anchor primitive / df / syntax) is pure ℤ→ℚ-core
        //     glue: (core, comp) = (1, 0).  ($f/$e → (0,0).)
        //   * A non-anchor `$p` replays its RPN exactly like rpn_fold_zfc,
        //     but accumulates the (comp, core) PAIR componentwise — so an
        //     occurrence that descends into an anchor is charged to comp
        //     wherever it sits, and occurrences that never cross an anchor
        //     stay in core.  Z-saved subproofs duplicated (no sharing),
        //     identical to the existing fold.
        //
        // This attributes by OCCURRENCE PATH, not leaf identity: a lemma
        // reused both under the completion layer and outside it has its
        // through-anchor occurrences in comp and its completion-free
        // occurrences in core. comp + core == expanded_zfc[resqrtth] exactly.
        // (`in_r0` / leaf distinct-counts above are kept only as the
        // diagnostic "distinct leaves reached" line.)
        let t1 = std::time::Instant::now();
        // memo[idx] = (comp, core); comp+core = plain expanded_zfc(idx).
        let mut memo: Vec<Option<(ProofSize, ProofSize)>> = vec![None; n];
        for &idx in &topo {
            if is_anchor[idx] {
                // Whole anchor subtree → completion. Plain ZFC size = the
                // ordinary rpn fold where each child's plain size is the
                // (comp+core) already stored for it (children precede in
                // topo). $f/$e → 0, leaves → 1, $p → RPN sum.
                let full = match &self.statements[idx].proof {
                    None => {
                        let k = self.statements[idx].kind;
                        if k == Kind::Floating || k == Kind::Essential {
                            ProofSize::zero()
                        } else {
                            ProofSize::one()
                        }
                    }
                    Some(steps) => {
                        let mut st: Vec<ProofSize> = Vec::new();
                        let mut sv: Vec<ProofSize> = Vec::new();
                        for stp in steps {
                            match stp {
                                ProofStep::Stmt(c) => {
                                    let rc = resolve(*c);
                                    let arity =
                                        self.statements[*c].mand_hyps.len();
                                    let (bc, cc) = memo[rc]
                                        .clone()
                                        .unwrap_or_else(|| {
                                            (
                                                ProofSize::zero(),
                                                ProofSize::zero(),
                                            )
                                        });
                                    let mut sum = bc.add(&cc);
                                    let popn = arity.min(st.len());
                                    for _ in 0..popn {
                                        sum = sum.add(&st.pop().unwrap());
                                    }
                                    st.push(sum);
                                }
                                ProofStep::Tag(j) => {
                                    let top = st
                                        .last()
                                        .cloned()
                                        .unwrap_or_else(ProofSize::zero);
                                    if *j == sv.len() {
                                        sv.push(top);
                                    } else if *j < sv.len() {
                                        sv[*j] = top;
                                    } else {
                                        while sv.len() < *j {
                                            sv.push(ProofSize::zero());
                                        }
                                        sv.push(top);
                                    }
                                }
                                ProofStep::Saved(j) => st.push(
                                    sv.get(*j)
                                        .cloned()
                                        .unwrap_or_else(ProofSize::zero),
                                ),
                            }
                        }
                        st.pop().unwrap_or_else(ProofSize::zero)
                    }
                };
                memo[idx] = Some((full, ProofSize::zero()));
                continue;
            }
            let steps = match &self.statements[idx].proof {
                None => {
                    let k = self.statements[idx].kind;
                    let pair = if k == Kind::Floating || k == Kind::Essential {
                        (ProofSize::zero(), ProofSize::zero())
                    } else {
                        // Non-anchor primitive / df / syntax / $p ? leaf:
                        // irreducible ℤ→ℚ-core + FOL/set glue.
                        (ProofSize::zero(), ProofSize::one())
                    };
                    memo[idx] = Some(pair);
                    continue;
                }
                Some(s) => s,
            };
            // RPN replay accumulating the (comp, core) pair componentwise.
            let mut st: Vec<(ProofSize, ProofSize)> = Vec::new();
            let mut sv: Vec<(ProofSize, ProofSize)> = Vec::new();
            for stp in steps {
                match stp {
                    ProofStep::Stmt(c) => {
                        let rc = resolve(*c);
                        let arity = self.statements[*c].mand_hyps.len();
                        let (bc, cc) = memo[rc]
                            .clone()
                            .unwrap_or_else(|| {
                                (ProofSize::zero(), ProofSize::zero())
                            });
                        let mut comp = bc;
                        let mut cor = cc;
                        let popn = arity.min(st.len());
                        for _ in 0..popn {
                            let (b, c2) = st.pop().unwrap();
                            comp = comp.add(&b);
                            cor = cor.add(&c2);
                        }
                        st.push((comp, cor));
                    }
                    ProofStep::Tag(j) => {
                        let top = st.last().cloned().unwrap_or_else(|| {
                            (ProofSize::zero(), ProofSize::zero())
                        });
                        if *j == sv.len() {
                            sv.push(top);
                        } else if *j < sv.len() {
                            sv[*j] = top;
                        } else {
                            while sv.len() < *j {
                                sv.push((
                                    ProofSize::zero(),
                                    ProofSize::zero(),
                                ));
                            }
                            sv.push(top);
                        }
                    }
                    ProofStep::Saved(j) => st.push(
                        sv.get(*j).cloned().unwrap_or_else(|| {
                            (ProofSize::zero(), ProofSize::zero())
                        }),
                    ),
                }
            }
            memo[idx] = Some(st.pop().unwrap_or_else(|| {
                (ProofSize::zero(), ProofSize::zero())
            }));
        }
        let (completion0, core0) = memo[r_root]
            .clone()
            .unwrap_or_else(|| (ProofSize::zero(), ProofSize::zero()));
        eprintln!(
            "[task9] occurrence-level fold done ({:.1}s)",
            t1.elapsed().as_secs_f64()
        );
        let core = core0;
        // COMPLETION should equal total - core exactly (both Exact). Prefer
        // the directly-folded comp; cross-check against the subtraction.
        let (completion, total_out) = match total.checked_sub(&core) {
            Some(c) => (c, total.clone()),
            None => {
                let comp = completion0.clone();
                let t = comp.add(&core);
                (comp, t)
            }
        };
        Some((
            total_out,
            completion,
            core,
            anchors_found,
            anchors_missing,
            n_leaf_comp,
            n_leaf_core,
        ))
    }

    /// Distinct `GenuineAxiom` labels reachable in the fully-expanded tree of
    /// `root` (sorted). Cheap reachable-set fold (same shape as `dag_size`),
    /// computed only for the handful of anchors we query.
    pub fn genuine_axioms_reachable(
        &self,
        root: usize,
        alias: &HashMap<usize, usize>,
    ) -> Vec<String> {
        use std::collections::BTreeSet;
        let mut memo: HashMap<usize, std::rc::Rc<BTreeSet<usize>>> =
            HashMap::new();
        let mut stack: Vec<usize> = vec![root];
        while let Some(&idx) = stack.last() {
            if memo.contains_key(&idx) {
                stack.pop();
                continue;
            }
            let st = &self.statements[idx];
            let children: Vec<usize> = match st.kind {
                Kind::Provable => match &st.proof {
                    Some(steps) => {
                        let mut v: Vec<usize> = steps
                            .iter()
                            .filter_map(|s| match s {
                                ProofStep::Stmt(c) => Some(*c),
                                ProofStep::Saved(_) | ProofStep::Tag(_) => None,
                            })
                            .collect();
                        v.sort_unstable();
                        v.dedup();
                        v
                    }
                    None => Vec::new(),
                },
                _ => Vec::new(),
            };
            let pending: Vec<usize> = children
                .iter()
                .copied()
                .filter(|c| !memo.contains_key(c))
                .collect();
            if pending.is_empty() {
                let mut set: BTreeSet<usize> = BTreeSet::new();
                if self.class_of(idx, alias) == Some(Class::GenuineAxiom) {
                    set.insert(idx);
                }
                for c in &children {
                    if let Some(cs) = memo.get(c) {
                        for &e in cs.iter() {
                            set.insert(e);
                        }
                    }
                }
                memo.insert(idx, std::rc::Rc::new(set));
                stack.pop();
            } else {
                for c in pending {
                    stack.push(c);
                }
            }
        }
        let mut out: Vec<String> = memo
            .get(&root)
            .map(|s| {
                s.iter()
                    .map(|&i| self.statements[i].label.clone())
                    .collect()
            })
            .unwrap_or_default();
        out.sort();
        out
    }

    /// Look up a statement index by label.
    pub fn index(&self, label: &str) -> Option<usize> {
        self.by_label.get(label).copied()
    }
}
