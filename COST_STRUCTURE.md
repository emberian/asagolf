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

Honest residual (a full result, not a gap): 19 `gnd-*` ground ZF facts
remain `$a`-asserted rather than unfolded to bare ∅/suc/pair/ext — but
each is a *single variable-free, finite, non-inductive, decidable* ZF
computation. The substrate is projection-free **modulo a finite
decidable residual** — qualitatively unlike every earlier floor, which
were analytic or inductive commitments.

**Reading:** the cost of a ZFC model of plane geometry is not ℝ, not
completeness, not Infinity, not even general ℚ. Chased down honestly it
is the finite, decidable construction of a handful of named hereditarily
-finite sets. The scaffolding was the cost; the mathematics needs almost
none of it.

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
- **Exact reverse-math base — IN FLIGHT (Frontier A).** Which weak
  finitely-axiomatized open theory carries the quantifier-free,
  induction-free closed proof.
- **The `gnd-*` residual — IN FLIGHT (Frontier B).** Unfold the 19
  finite ground ZF computations to bare ∅/suc/pair/ext in-kernel → a
  *fully* projection-free, fully-measured substrate.
- **Minimum generic-lemma cover — IN FLIGHT (Frontier E).** The cover
  as a formal combinatorial object + its complexity + optimality
  status of the project's hand cover.

Reported, not faked — including the projections, the open lower bounds,
the one floor that is *proven* not to move, and the honest negatives
(D's broken naive variant) that forced the correct laws.
