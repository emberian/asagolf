# FRONTIER A — the EXACT proof-theoretic base of the closed ASA′ proof

Adversarially honest. Every number here is **MEASURED** by
`src/bin/revmath.rs` over the kernel-reverified corpus
`data/grounded.out.mm` (the 96 `$p` the staged build emits), trust root
`src/kernel.rs`. No projection is merged into a measured line; the one
characterization that goes beyond measurement (the named place in the
reverse-math hierarchy) is an **UPPER BOUND** with the honest lower-bound
residual stated explicitly. Read-only over the verified corpus.

Reproduce:

```
cargo run --release --bin grounded     # emits data/grounded.out.mm (96 $p)
cargo run --release --bin revmath      # the audit; re-verifies in OUR kernel first
```

---

## 0. The MEASURED audit numbers (kernel-exact)

`revmath` re-verifies the whole corpus in the sound kernel before
reporting anything:

```
KERNEL ✔  96 $p  82 $a  69 $e  20 $f  (267 statements)
```

| Quantity | MEASURED value | Meaning |
|---|---|---|
| variable typecodes (sorts) | `{ term , wff }` — **2** | only a propositional sort + an *element* sort; **no `set`/`class`/`setvar` sort** |
| mandatory `$d` side conditions in whole DB | **0** | the Metamath device for soundly schematising bound/free variables is **never used** |
| ∀/∃/binder occurrences in *every used body* | **0** (`A. E. E! E* setvar [ ] / S.` each 0) | the obligation has **quantifier rank 0** |
| max parenthesis nesting of any used body | **7** | bounded term/formula depth; no schematic blowup |
| ℕ/ω/recursion/Peano carrier symbols in any used body | **0** (`om suc rec NN ZZ QQ RR CC …` all 0) | **zero arithmetic induction; no completed-infinite carrier** |
| declared `$a` | **82** | the full axiom surface |
| consumed `$a` (proof-DAG closure of all 96 `$p`) | **81** | the *consumed* base |
| unused `$a` | **1** — `cong-lt1` | one redundant Leibniz `<`-congruence; honestly reported |
| `ax-sqrt` (the one non-field primitive) consumed | **true** | the √-adjunction is genuinely used (not vacuous) |

The `A.` (∀) constant *is declared* in the `$c` line but appears in
**zero statement bodies** — `revmath` counts parsed bodies only (the
kernel strips the `$c` declaration and comments), so this is genuine
*non-use*, not a parsing artifact.

### Axiom classification (MEASURED, all 82 `$a`)

| class | count | schematic over wff? |
|---|---|---|
| `L`  propositional Hilbert (`ax-1/2/3`, `ax-mp`, `ax-bi1/2`) | 6 | **yes, all 6** (this *is* propositional calculus) |
| `EQ` equality logic (`ax-7`, `eqid`, `eqcom`, `cong-*`, `ptext`) | 16 | none |
| `OF` ordered-field algebra (`of-*`) | 16 | none |
| `SQ` square-root adjunction (`ax-sqrt`, `of-sqrtnn`) | 2 | none |
| `DEF` conservative definitions (`df-*`) | 15 | 2 (`df-an`, `df-or` — definitional, eliminable) |
| `SYNTAX` grammar builders (`w*`, `t*`) | 27 | 5 (`wn wi wb wa wo` — pure grammar) |

**Decisive fact:** the *only* axioms that are proper schemas (range over
a metavariable) are the propositional Hilbert/⟷ axioms over **wff**
metavariables `ph/ps/ch/th`. **No axiom is a schema over an *element*
(`term`) metavariable under an induction or comprehension shape.** There
is no induction scheme, no separation/comprehension, no `∈`. Every
algebraic axiom (`of-*`, `ax-sqrt`, `cong-*`) is a single
*quantifier-free* sentence with implicitly-universal free term
variables — i.e. an **open (universal) axiom**.

---

## 1. The exact base-theory characterization

Combining the measured facts, the closed ASA′ proof is carried, exactly,
by:

> **T = OPEN( classical propositional calculus
> + equality-with-operator-congruence
> + the ordered-field axioms
> + one √-adjunction `0 ≤ u → (√u)·(√u) = u` )**,
> over a **two-sorted, quantifier-free** signature
> (`wff` propositional, `term` field element),
> with the geometry layer (points/lines/`sqd`/`dot`/`Coll`/`Ray`/`ACong`,
> the ruler `cp`) entirely **conservative definitions** (`df-*`).

Equivalently in standard terms: **T is (an open, finitely-axiomatised
fragment of) the universal/quantifier-free theory of *ordered Euclidean
fields*** — ordered fields in which every non-negative element has a
square root (Pythagorean closure) — *restricted to the single √ the
proof forces*. It is **strictly weaker than RCF**: there is no
real-closure scheme (no "every odd-degree polynomial has a root"), no
completeness/Dedekind axiom, no limit/sup principle, no first-order
quantifier alternation at all. The equality layer is **Robinson-Q-style
Leibniz congruence** (operator-by-operator `cong-*` + point
extensionality `ptext`), *not* a set theory.

Three structural properties pin it precisely, all MEASURED:

1. **Quantifier rank 0.** No `∀`/`∃` over field elements anywhere
   (corroborates `SEAM1_INFINITY.md` §3's read-only claim with a
   mechanical full-corpus count: 0).
2. **Induction-free.** No ℕ/ω/recursion carrier symbol; no element-sorted
   axiom schema. The provably-total functions of T are *exactly the
   closed open terms*: field polynomials plus one un-nested √
   (Stage-1's `K = 1`). No function is proved total by recursion.
3. **Conservative geometry.** Every geometric primitive enters only
   through an eliminable `df-*` (rewrite rule); the 15 `DEF` axioms add
   no first-order strength over the algebraic core (this is *asserted by
   construction* in `grounded.mm` and consistent with the audit — see
   the residual, it is not separately machine-certified here).

---

## 2. UPPER BOUND on proof-theoretic strength

T's logical strength is bounded from **above** as follows
(characterization beyond raw measurement — labelled as a bound, not a
measured equality):

- T has **no induction**, **no exponentiation/totality object**, and
  **only quantifier-free axioms over a fixed finite operator set**. Its
  theorems are derived by propositional logic + equational rewriting +
  finitely many open ordered-field/√ instances and case splits.
- Therefore **T is interpretable in EFA (= IΔ₀ + exp)** and, a fortiori,
  far below **RCA₀** (whose Σ⁰₁-induction T entirely lacks) and below
  **PRA**. It does not prove the totality of any function not given by an
  explicit open term.
- Within the arithmetised/ordered-field hierarchy, T sits **at or below
  the quantifier-free fragment of the theory of ordered Euclidean
  fields** — well inside the elementary (EFA / `I∆₀+exp`) region, with
  no quantifier-elimination *cost* incurred because the obligation is
  already quantifier-free (no Tarski/RCF decision procedure is invoked
  in the proof; cf. `COST_STRUCTURE.md`'s RCF-route vs. analytic-ℝ-route
  distinction — the *proof* never enters either).
- Set-theoretically (cross-checked against `SEAM1_INFINITY.md`,
  EXTRACTED there, not recomputed here): a model of T is realisable in
  the hereditarily-finite sets — the closed obligation needs ∅ and `suc`
  applied **once**, never ω; consistent with this audit's measured
  "zero ω/recursion symbols."

So the **upper bound is sharp in form**: an open (universal),
finitely-axiomatised, two-sorted theory — propositional + equational +
ordered-field + one Skolem √ — provably below EFA in consistency
strength.

---

## 3. The HONEST OPEN RESIDUAL (no tight LOWER bound is claimed)

This instrument bounds strength **from above only**. A *matching lower
bound* — "the closed ASA′ obligation cannot be carried by anything
strictly weaker" — is **OPEN**. Specifically, to pin T's exact location
one would need:

1. **Machine-certified conservativity of the `df-*` layer.** The
   geometric definitions are *designed* to be eliminable rewrites and the
   audit finds no schema/quantifier that would break this, but a formal
   conservativity proof (every `df-*` use is provably eliminable, the
   geometry adds no `term`-sorted theorem unprovable in the bare
   algebraic core) is **not produced here**. Until it is, "geometry is
   purely definitional" is a strongly-evidenced but uncertified premise
   of the upper bound.

2. **A model-theoretic independence/separation for the lower bound.**
   To show T is *not* reducible to pure equational logic (i.e. that the
   ordered-field **+ √** content is essential, not eliminable), one needs
   an algebraic-independence / two-model argument: exhibit a structure
   satisfying the equational+propositional fragment but refuting a
   quantifier-free ordered-field+√ consequence that `G4-sas` actually
   uses. `SEAM4_IDENTITY.md`'s MEASURED ~61.52% irreducible
   *sign/order-reasoning core* in `sqcong` (`a²=b² → a=b`) is **evidence**
   that an essential non-equational residue exists — it is **not a
   proof** of a lower bound, and is explicitly not merged into one here.

3. **An exact reverse-math placement.** Whether T is *equivalent* to (not
   merely *below*) the open ordered-Euclidean-field fragment, or strictly
   weaker (e.g. only the equational diagram plus one √ instance, since
   `K = 1` and quantifier rank 0), is **OPEN**. The measured facts
   constrain it tightly from above; the precise least theory is not
   determined by a syntactic audit alone and would require the
   separation in (2).

**Net honest claim.** The closed ASA′ proof's base is **MEASURED** to be
an open, quantifier-free, induction-free, two-sorted theory =
propositional + equality-congruence + ordered-field + one √-adjunction,
with all geometry conservative-by-construction. Its strength is
**bounded above** by the elementary region (≤ EFA, ≪ RCA₀, ≠ RCF — no
real-closure, no completeness). A **tight lower bound is the residual**:
it needs certified `df-*` conservativity and a model-theoretic separation
isolating the irreducible order/√ core (the SEAM4 ~61% is the live
evidence, not the proof). Reported, not faked — including the one unused
axiom (`cong-lt1`), the single non-certified premise (df-* eliminability),
and the open lower bound.

---

## 4. Ledger

| Item | Status | Value | Source |
|---|---|---|---|
| corpus kernel re-verify | **MEASURED** | 96 `$p` ✔ (267 stmts) | `revmath`, `src/kernel.rs` |
| sorts | **MEASURED** | `{term, wff}` (2; no set/class) | `revmath` (3) |
| `$d` side conditions | **MEASURED** | 0 | `revmath` (3) |
| ∀/∃/binder occurrences | **MEASURED** | 0 | `revmath` (1) |
| induction/ω/recursion symbols | **MEASURED** | 0 | `revmath` (2) |
| element-sorted axiom schemas | **MEASURED** | 0 | `revmath` (4) |
| consumed `$a` / declared `$a` | **MEASURED** | 81 / 82 (`cong-lt1` unused) | `revmath` (5) |
| `ax-sqrt` consumed | **MEASURED** | true | `revmath` (5) |
| base theory T | **CHARACTERIZED (measured surface)** | open prop.+eq.-cong.+ord.field+1·√ | §1 |
| strength upper bound | **UPPER BOUND** | ≤ EFA; ≪ RCA₀; ≠ RCF | §2 |
| df-* conservativity | **OPEN (uncertified premise)** | — | §3.1 |
| tight lower bound / exact placement | **OPEN** | — | §3.2–3.3 |

## 5. Files

* `src/bin/revmath.rs` — the FRONTIER-A instrument (new, additive,
  read-only over the corpus). OUR kernel re-verifies all 96 `$p` before
  any number is reported; then audits sorts, quantifiers, induction,
  axiom classes, and the consumed-theory proof-DAG closure.
* `FRONTIER_A_REVMATH.md` — this report.
* Read-only consumed: `data/grounded.out.mm` (generated by
  `cargo run --release --bin grounded`).
* Untouched: `src/kernel.rs`, `src/elaborate.rs`, `src/bin/grounded.rs`,
  `src/proof_g*.rs`, `data/*.mm`, `src/cse.rs`, other agents' files.
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
