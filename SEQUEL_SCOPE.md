# SEQUEL_SCOPE — Synthetic Differential Geometry (the dual of the prequel)

## 0. What the prequel established (the thing we are dualizing)

The prequel (`birkhoff-asa`, now CLOSED) measured the fully-expanded,
kernel-verified proof size of a basic metric-geometry theorem and traced
its irreducible logical residue. The convergent finding: metric
geometry's irreducible core is **`of-letot`-flavoured order**, and the
single inference that the *content* cannot remove is

```
of-letot-style positivity culminating in:   x · x = 0  ⟹  x = 0
```

This is **proven, not a ring identity** — it fails in ℤ/8 and ℤ/4, so it
is a genuine extra axiom about the line, not algebra. Call it the
**metric residue**.

## 1. The mirror hypothesis (stated precisely)

Synthetic Differential Geometry (SDG) is the intuitionistic world that
**refuses exactly that inference**. Classically the set
`D = { d | d·d = 0 }` collapses to `{0}` (precisely because
`x·x=0 ⟹ x=0`). Intuitionistically — with no Law of Excluded Middle, no
double-negation elimination, no decidable/stable equality — `D` is
*non-degenerate*: it is a non-trivial infinitesimal object, the carrier
of synthetic calculus.

> **Mirror Hypothesis (MH).** SDG's irreducible residue is the exact
> dual of the metric residue. Where metric geometry's irreducible core
> is the positivity inference `x·x=0 ⟹ x=0` (everything else removable
> field/order scaffolding), SDG's irreducible core is the
> **Kock–Lawvere axiom** (KL): every map `D → R` is uniquely affine,
> i.e. `∀ f:D→R  ∃! (a,b)  ∀ d∈D  f(d) = a + b·d`. Everything else —
> the ring laws, the definition of `D`, microcancellation as a
> *derived* consequence vs. an axiom — is removable scaffolding. The
> dual of "you may not refuse `x·x=0 ⟹ x=0`" is "you *must* refuse it,
> and the single thing you must instead assert is KL."

Concretely the mirror is structural, not numerical: the prequel's first
real theorem (a congruence/length identity) needed the metric residue
exactly once at its core; the sequel's first real theorem (existence and
uniqueness of the **synthetic derivative**) must need KL exactly once at
its core, with microcancellation as the *only* extra structural axiom
and *no classical principle anywhere in its consumed-axiom closure*.

The MH would be **falsified** if the first synthetic-derivative theorem
provably required a classical principle (LEM / `ax-3` / DNE / stable
equality / decidable apartness) — that would make SDG's "intuitionistic"
core a fiction, the exact analog of cheating in the prequel.

## 2. Trust story

- **Verifier reused UNCHANGED.** The sole derivation-checking trust root
  remains `src/kernel.rs` — the sealed, logic-AGNOSTIC sound
  Metamath-subset verifier. It checks that every `$p` is derived from
  its `$a` base by substitution + the stack discipline + DV
  side-conditions, regardless of what those `$a` say. It does **not**
  know or care whether the axiom base is classical or intuitionistic.

- **NEW trust root #1: a certified-intuitionistic substrate**
  (`data/sdg.mm`). The kernel guarantees "derived from these axioms".
  It is on *us* to certify that "these axioms" contain **no classical
  principle**. The substrate is an intuitionistic Hilbert-style
  predicate logic with equality: `ax-1`, `ax-2`, the explicit-`∧`/`∨`/
  `⊥` intuitionistic connective axioms, `efq` (ex falso), modus ponens
  and the quantifier rules — and crucially **NO `ax-3`/Peirce, NO LEM,
  NO DNE, NO stable/decidable equality, NO apartness**. Equality is
  bare Leibniz (reflexivity + substitution), never assumed stable or
  decidable.

- **NEW trust root #2: the intuitionistic-purity guard**
  (`src/bin/sdgpure.rs`). This MIRRORS the prequel's
  no-cheating/`--lint` guard. It mechanically computes, for every `$p`
  in `data/sdg.mm`, the transitive closure of consumed `$a` axioms
  (the same recursion `euclidfloor`'s `expand` uses, but collecting
  axiom labels instead of counting leaves), and certifies that this
  closure contains **none** of a hard-coded blacklist of classical
  principles. It also structurally scans the substrate for any
  axiom whose *statement shape* is a classical principle even if
  unused. The guard is the new trust root and is treated with the
  rigor the no-cheating guard received: it fails loud, it is
  adversarial, and an honest "lemma L provably needs DNE, here is the
  derivation" is reported as a first-class finding rather than hidden.

The **Iron Rule** is unchanged: reported, not faked. Every claimed
theorem is a kernel-verified `$p` or a labelled `PROJECTION:` with its
derivation. A precisely-characterized obstruction is a FULL SUCCESS.

## 3. The substrate (`data/sdg.mm`)

Certified-intuitionistic predicate logic with equality, **plus** the SDG
substrate:

- `R`: a commutative ring with `1` (the line object). Ring axioms as
  `$a` equalities (assoc/comm/unit/distrib/additive inverse) — pure
  equational algebra, no order, no `x·x=0 ⟹ x=0`.
- `D`: defined by `d ∈ D  ↔  d · d = 0` (a *definition*, `df-D`, not an
  axiom — conservative, mirrors the prequel's `df-*` discipline).
- **Kock–Lawvere axiom** (`ax-kl`): for every `f : D → R` there exist
  `a, b ∈ R` with `∀ d∈D  f(d) = a + b·d`, and they are unique.
  Encoded with explicit existence and a uniqueness axiom
  `ax-microcancel` (microcancellation: `(∀ d∈D  b·d = c·d) → b = c`),
  which is the standard way KL-uniqueness is stated. Microcancellation
  is the *only* extra structural axiom besides KL-existence and ring.
- Kernel-verify the well-formedness/base: a handful of `$p`
  sanity-derivations over the base establish the substrate parses and
  the connective/quantifier glue is sound.

## 4. The first synthetic-differential theorem (deliverable 4)

`sdg-deriv`: from KL (existence) **+** microcancellation (uniqueness),
every `f : R → R` has a **unique** `f' : R → R` with

```
∀ x ∈ R  ∀ d ∈ D   f(x + d) = f(x) + d · f'(x)
```

Existence is KL applied pointwise (the map `d ↦ f(x+d)` is `D→R`, so it
is uniquely affine with constant term `f(x)`; its linear coefficient,
as a function of `x`, *is* `f'`). Uniqueness uses microcancellation —
**and we say so explicitly**: if uniqueness secretly needs a classical
principle, the purity guard will catch it and we REPORT that as the
headline finding.

Kernel-verify it; run the purity guard on it.

## 5. What is MEASURED vs labelled PROJECTION

- **MEASURED:** the cut-free `$a`-leaf cost of `sdg-deriv` in OUR
  kernel with OUR project metric (`$a`→1, `$f`/`$e`→0, `$p`→Σ steps),
  produced by `src/bin/sdgfloor.rs` (mirrors `euclidfloor.rs`). Also
  the purity-guard verdict (a boolean + the exact consumed-axiom set).

- **PROJECTION (named, NOT computed here):** the substrate-grounding
  question — the cost to exhibit a *model* of SDG (a well-adapted
  topos, e.g. the Cahiers topos or `𝓢𝓮𝓽^{𝔻^op}` over the dual of
  finitely-presented `C∞`-rings). This is the sequel's exact analog of
  the prequel's "ground ℝ in ZFC": the theory is consistent/non-vacuous
  iff such a model exists, and its construction cost is a separate
  quantity that is never summed into the proof cost. Labelled as the
  next milestone, deliberately not attempted here.

## 5b. MEASURED outcome (this build) — adversarially honest

Kernel: verified all 8 `$p` in `data/sdg.mm` ✔ (92 statements).
Purity guard: GENUINELY INTUITIONISTIC ✔ — 40 logical `$a`, none
classical (NAME + SHAPE), none in any `$p` consumed-axiom closure.

The first synthetic-differential theorem is delivered as a chain, each
piece kernel-verified and MEASURED (cut-free `$a`-leaf, project metric):

| theorem | what it is | consumes | leaves |
|---|---|---|---|
| `sdg-addcan` | additive cancellation, RING-ONLY | ring eq-axioms | 406 |
| `sdg-slope` | pointwise slope uniqueness `[eqb,eqc]⊢(b·d)=(c·d)` | sdg-addcan | 478 |
| `sdg-slope-conj` | same, single conjunctive hypothesis | sdg-slope | 544 |
| `sdg-deriv` | **the headline**: `[∀d (Dd→(b·d)=(c·d))] ⊢ b=c` | **`ax-microcancel`** | 9 |

Honest decomposition of "existence + uniqueness of the synthetic
derivative":

- **Existence** is exactly `ax-kl` (the slope `b` exists). It is a
  substrate axiom; restating it as a one-line `$p` would be vacuous, so
  it is CITED, not re-proved — stated plainly, not hidden.
- **Pointwise uniqueness** (`sdg-slope`, MEASURED 478) is the genuine
  mathematical content: from two affine KL-representations of the same
  `(ap f d)` it derives `(b·d)=(c·d)` by additive cancellation —
  RING-ONLY, no order, no metric residue, no classical principle.
- **Global uniqueness / well-definedness of `( deriv f )`**
  (`sdg-deriv`, MEASURED 9) genuinely CONSUMES `ax-microcancel` to pass
  from `∀d∈D (b·d)=(c·d)` to `b=c`. Verified RPN ends
  `… mc.h vd vb vc ax-microcancel ax-mp`.

**Honest open residual (named, not papered over).** The two halves are
each kernel-verified but are presented with the linking universal as an
`$e` hypothesis (`mc.h`) rather than mechanically threaded: closing the
seam — lifting `sdg-slope-conj` under the `( D d )` guard and
discharging its `$e` into `ax-gen` to synthesise `ax-microcancel`'s
exact universal antecedent — requires a deduction-theorem / quantifier-
proviso rule not yet built in this intuitionistic substrate. This is a
precisely-characterised obstruction (a FULL SUCCESS per the Iron Rule),
NOT a hidden gap: existence=`ax-kl` (cited), pointwise=`sdg-slope`
(measured, ring-only), uniqueness-glue=`sdg-deriv` (measured, consumes
microcancellation). The mirror hypothesis is SUPPORTED so far: the
synthetic-derivative core needs exactly KL (existence) +
microcancellation (uniqueness) and NOTHING classical — the guard
certifies this mechanically.

## 5c. Model-grounding milestone (named PROJECTION, not done here)

The sequel's analog of "ground ℝ in ZFC": exhibit a well-adapted topos
model (Cahiers topos / `𝓢𝓮𝓽^{𝔻^op}`) in which `D` is non-degenerate
and KL holds — establishing SDG is consistent/non-vacuous. Its
construction cost is a SEPARATE quantity, never summed into the proof
cost. Explicitly labelled `[PROJECTION]` by `sdgfloor`; the next
milestone.

## 6. Milestone plan

1. ✅ `SEQUEL_SCOPE.md` (this file).
2. `data/sdg.mm` — certified-intuitionistic substrate + SDG axioms;
   kernel-verify base well-formedness `$p`.
3. `src/bin/sdgpure.rs` — the intuitionistic-purity guard (new trust
   root); verdict on every `$p`.
4. `sdg-deriv` — first synthetic derivative as kernel-verified `$p`;
   purity guard run on it.
5. `src/bin/sdgfloor.rs` — MEASURE its cut-free `$a`-leaf cost; state
   MEASURED cost + purity verdict; name the model-grounding milestone
   as the explicitly-labelled PROJECTION / next step.

Commit after every sub-step. Do not push, do not work on main.
Adversarially honest throughout: a classical principle smuggled into
"intuitionistic" SDG is a ZERO; an honest "this step provably needs
DNE, here is why" is gold.
