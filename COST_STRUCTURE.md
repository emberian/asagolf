# The cost structure of grounding Euclidean geometry

A synthesis of what this project's instrument actually found, once it
stopped being a Twitter rebuttal and became a measurement of where the
cost of grounding a piece of mathematics in ZFC really lives. Every
figure here is `[MEASURED]` (our kernel, cut-free `$a`-leaf metric),
`[EXTRACTED]` (set.mm proof-DAG, verbatim), or a labelled `[PROJECTION]`
with its derivation — never merged.

## The three quantities (never summed)

1. **Geometry proof size over F1** — G4 SAS = 383,606 cut-free
   (10^5.58), ASA′ closed no-cheating end-to-end. `[MEASURED]`
2. **Grounding cost** (expand F1 → ZFC via set.mm's library) — 10^45.74
   analytic-ℝ; 10^30.75 RCF route; 10^25.95 strict extractable floor.
   `[EXTRACTED]`
3. **Satisfiability** — exhibit a model of F1. This is where the real
   structure was hiding.

## The through-line: every "floor" was a construction choice

The headline finding. Each time we removed a *construction scaffold*,
the apparent floor receded — it was never the mathematics:

| model / route | substrate floor | what was removed |
|---|---|---|
| set.mm's ℝ (`CCfld`/analytic √) | **10^46.10** `[EXTRACTED]` | — |
| native ZF model, √ a kernel theorem | **10^17.484** `[EXTRACTED]` | set.mm's analytic-√ *routing* |
| HF carrier (Vω), proof-relativized | **10^12.810** `[EXTRACTED]` | the **ω-tower** (Axiom of Infinity) |

- The 10^46 was set.mm building √ through the reals. A native ℚ-from-ZF
  with √-satisfaction a *kernel-proved theorem* (Stage 2) dropped it to
  10^17.484, residual = `omex` (Axiom of Infinity).
- Seam #1 then MEASURED that `omex` is **incidental**: the closed
  obligation is quantifier-free over finitely many named terms; ℚ-
  constants unfold to pair-classes over only `∅` and `suc ∅` (`suc`
  applied **once**, never iterated) — Stage-1's K=1 is the structural
  reason. Floor → `sucexg` 10^12.810.
- Stage 3 realized that as a kernel construction: the finite ℚ-elements
  the proof *names*, built as hereditarily-finite sets, with quotient
  well-definedness a finite induction-free kernel check (10 `$p`,
  `[MEASURED]` 10^2.344). This **discharged** Stage-2's inductive
  ≤10^4 `[PROJECTION]` into a measured finite computation.

Then Frontier B discharged the residual itself: all 19 `gnd-*` ground
arithmetic facts derived as kernel-verified `$p` from bare ZF. The
substrate is now **projection-free and fully-MEASURED for all
arithmetic**. After every arithmetic fact is mechanically discharged,
the entire residual is **exactly two order literals** — `Q0 ≤ Q1` and
`Q1 ≠ Q0` on concrete ℚ-constants: decidable, non-inductive,
Infinity-free.

## The convergence — the result

This is the finding the instrument was built to reach. **Three
independent threads, from three different directions, land on the same
residue:**

- **Frontier C (proof content):** the order predicate is *proven* not
  expressible as any ring identity — `sqcong` fails in ℤ/8; logically
  essential, localized to `of-letot`. A THEOREM.
- **Frontier A (proof strength):** the closed proof is *exactly* an
  open quantifier-free theory **below EFA** — no induction, no
  quantifiers, ≠ RCF — whose only irreducible content is the order/√
  core. MEASURED + bounded.
- **Frontier B (substrate construction):** strip ℝ, Infinity, ω, ℚ,
  and every arithmetic computation, and what is left, irreducibly, is
  **two order inequalities on rational constants**. MEASURED.

Proof-content, proof-strength, and set-construction — entirely
independent attacks — all triangulate on **order / orientation, and
nothing else**. Frontier D explains *why* the stripping was possible at
all: `rank = K + c·D` is additively separable, so the geometric and
arithmetic costs are orthogonal coordinates that never entangle —
scaffolding genuinely separable from content. Frontier E shows the
stripping itself was a near-optimal solve of an NP-hard compression
(the substitution-closed smallest-grammar problem), done by hand and
kernel-checked, optimum honestly left open.

**Reading.** The cost of a ZFC model of plane geometry is not ℝ, not
completeness, not Infinity, not ω, not even ℚ or arithmetic — chased
all the way down, *every one of those was removable scaffolding*. The
single irreducible residue of Euclidean metric geometry is **the
ordering** — the principal square root being a function, orientation
being a choice — pinned to two concrete inequalities, proven not to be
algebra, and bounded inside an open theory weaker than EFA. The poll
asked how big the proof is. The honest answer the instrument found is
deeper: *almost all of it was scaffolding we chose; what remains is
orientation, and orientation alone.*

## What the proof content actually is (Seam #4)

Partitioning every cut-free leaf (kernel-reverified, 9,017,010 `$a`):

- **SYNTAX 94.76%** — writing the coordinate formulas down. Orthogonal
  to "proof difficulty"; a separate bucket, never folded.
- Of *proof content*: **IDENTITY ≈ 31%** (bounded-degree polynomial
  identities over an ordered field; localised to 5 generic lemmas, all
  ≤ degree 4) **+ GLUE ≈ 69%**. Cost law (the one labelled
  `[PROJECTION]` fit, R²=0.99, cross-validated): ring-identity cut-free
  cost ≈ quadratic in monomials, sub-linear in degree.

The qualified, honest reduction — and the first floor that looks
**intrinsic, not chosen**: `loclink` (law of cosines) reduces **96.82%**
to generic substitution-instances — near-perfect. But `sqcong`
(a²=b² ⇒ a=b) reduces only **38.48%**; the other **61.52%** is
irreducible ordered-field **sign reasoning** (`sqz`/`sqzhalf`/`subeq0` +
a case-split) that is provably *not* a polynomial identity. So:

> Birkhoff plane geometry = bounded-degree polynomial identities over an
> ordered field **+ an essential, irreducible order/sign-reasoning
> core** + syntax.

The reduction is tight exactly where the content is equational and
honestly incomplete exactly where it is order-theoretic. Of every floor
chased, the order-core is the only one that did **not** dissolve under a
better construction — and Frontier C **proved** why.

**Frontier C (`FRONTIER_C_ORDERCORE.md`, machine-checked separating
arithmetic):** the qualitative irreducibility is now a **THEOREM**, not
an appearance. Ring identities are sound over *every* commutative ring;
`sqcong`'s conclusion `u²=v²→u=v` is false in ℤ/8 (3²≡1²≡1, 3≠1) and
its load-bearing internal step `x²=0→x=0` is false in ℤ/4 (2²≡0, 2≠0).
By contraposition, **no set of ring identities of any degree can
express the order-core** — it is logically essential, localized to one
named axiom (`of-letot`, "no nonzero nilpotents"). This is the **first
and only intrinsic floor** in the entire project: every other floor was
a removable construction choice; this one provably is not. What remains
`[CONJECTURED]` is only the *exact 61.52% constant* being minimal,
isolated to a single named open proof-complexity lemma (Obligation O: an
unconditional cut-free lower bound for `x²=0→x=0`) — the factor-through
clause provable, the size clause open. The intuition was right; it is
now a precise, correct separation at the exact signature and obligation.

## The proof-complexity datum (Seam #2)

Tree-like vs DAG-like proof size for the Birkhoff postulates is a
**small constant in [0.59×, 3.35×]** — *not* exponential — and it
**inverts** for the generic-lemma-factored proofs (5/11 have cut-free
*smaller* than the named DAG, because substitution is free cut-free).
A long-budget kernel-gated probe shows the production CSE figure (−81%)
is budget-limited; real verified slack reaches **−91.83%**. Minimal-DAG
lower bound honestly **OPEN** (smallest-grammar is NP-hard). Framed
correctly: a fixed-instance CSE datum with measured constants —
*explicitly not* a Frege/extended-Frege or tree/dag separation theorem.

## Frontier status (the live frontier — being unfolded)

- **Order-core lower bound — RESOLVED (Frontier C, THEOREM).** Proven:
  no ring identity of any degree expresses the order-core; logically
  essential, localized to `of-letot`; machine-checked separating
  arithmetic. The first and only intrinsic floor. Open residual: the
  *exact constant* (Obligation O, a named cut-free LB problem).
- **Rank ↔ radical-depth — RESOLVED (Frontier D, MEASURED law).**
  `rank(constant) = K + c·D` exactly on all 6 named constants (K =
  suc-*depth* = radical-tower depth; D = pair-class tower-depth; c=2
  REP / 3 CLASS). Rank is linear and **additively separable** —
  geometric content enters *only* via K, the number-tower *only* via
  c·D, no interaction; K=1 is why the carrier sits at the minimal
  rank-1 Infinity-free corner of Vω. Honest hedge: class-rank is a
  lower bound (the `gnd-*` residual); the *shape* `rank=K+Θ(D)` is
  convention-independent, the constant `c` is not; measured for the
  finite named set only, not generic ℚ. Naive `K=suc-count` honestly
  reported as breaking at Q1 (forced the corrected depth form).
- **Exact reverse-math base — RESOLVED (Frontier A, MEASURED + bounded).**
  The closed proof is carried *exactly* by an **OPEN (quantifier-free)
  two-sorted theory**: propositional calculus + equality-congruence +
  the ordered-field axioms + the one √-adjunction — the universal
  fragment of ordered Euclidean (Pythagorean) fields restricted to the
  single √ the proof forces. MEASURED: 2 sorts (no set/class), **0**
  quantifier/binder occurrences in any used body, **0** `$d`, **0**
  ℕ/ω/induction, 81/82 `$a` consumed (`cong-lt1` redundant, reported).
  Interpretable in/**below EFA (IΔ₀+exp)**, far below RCA₀, ≠ RCF (no
  real-closure scheme, no completeness).
  **CLOSED (Closure 1) — bound UPPER → EXACT.** The `df-*`
  conservativity is now machine-certified: 9/11 geometry df-* strict
  Suppes-eliminable; `df-xc`/`df-yc` are free-pairing projections (not
  single-symbol defs) proven conservative via the surjective-pairing
  interpretation, *every metatheorem hypothesis machine-checked*;
  composition ⇒ the whole geometry layer conservative over F1. So the
  closed proof **is exactly** `OPEN(prop + equality-congruence +
  ordered-field + one √)` — modulo the cited classical metatheorems
  (Suppes/Shoenfield; surjective-pairing), correctly stated with
  hypotheses checked but not re-derived in-kernel, labelled as such
  (the honest foundation, not a gap). **A↔C interlock, both now
  exact/proven:** an open quantifier-free theory *exactly*
  characterized below EFA (A), the order predicate *proven* logically
  essential (C). Remaining: the exact-constant Obligation O, and the
  two order literals (Closure 2, in flight).
- **The `gnd-*` residual — RESOLVED (Frontier B, MEASURED).** All 19
  ground arithmetic facts discharged to kernel-verified `$p` from bare
  ZF (`verified all 55 $p ✔`, no induction, no `om`, `suc` once). The
  substrate is now **projection-free and fully-MEASURED for all
  arithmetic**; floor still `sucexg` 10^12.810 EXTRACTED. The entire
  residual, after every arithmetic fact is mechanically discharged, is
  **exactly two order literals**: `gnd-Q0leQ1` (Q0 ≤ Q1) and
  `gnd-Q1neQ0` (Q1 ≠ Q0) — decidable, non-inductive, Infinity-free,
  pure order decisions on concrete ℚ-constants.
- **Minimum generic-lemma cover — RESOLVED (Frontier E, object +
  NP-hardness + near-optimal instance).** Formalized: the
  substitution-closed generalization of a straight-line program /
  shared DAG (empty σ = grammar nonterminal, non-empty σ = parametric
  macro). **MIN-GENERIC-LEMMA-COVER is NP-hard** (cost-preserving
  reduction from SMALLEST GRAMMAR; no constant-factor poly-approx) —
  the substitution-closed *superproblem* of Seam #2's minimal-DAG.
  Measured (kernel-grounded, 267 reverified): the hand cover = **81,062
  cut-free leaves, paid once**, certified an **irredundant 0-edge
  substitution antichain of minimal arity** (no lemma deletable). The
  exact minimum is an `[OPEN]` lower bound (needs an info-theoretic
  bound or super-exponential search; NP-hardness rules out an efficient
  approximate LB) — 81,062 is an exact kernel-grounded *upper* bound.
  Discipline note: a speculative `loc-gen` refinement was *discarded*
  (kernel-gating it would require write-protected code; an unverifiable
  refactor is refused, not claimed).

Reported, not faked — including the projections, the open lower bounds,
the one floor that is *proven* not to move, and the honest negatives
(D's broken naive variant) that forced the correct laws.
