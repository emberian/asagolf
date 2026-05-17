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

**§5b SEAM: RESOLVED — verified in the integrated tree.** The
pointwise→global seam is closed: `mc.h` `$e` removed; seam-free
`sdg-deriv` (RPN ends `… ax-gen vd vb vc ax-microcancel ax-mp`) is
kernel-verified in the *integrated* union, not merely on a branch.
The closing rule is a *derived* deduction-theorem fragment
(`imp_a1`=ax-1, `imp_mp`=ax-2) + a guarded `ax-gen` (proviso
discharged by hypothesis-shape, same discipline as the prequel's
quantifier provisos) — **no new substrate axiom**. Honest measured
delta: `sdg-deriv` 9 → **2243** leaves — a cost *revealed, not added*
(the threading was previously hidden in the zero-cost `$e`).

Integrated union: **`Kernel: verified all 13 $p in data/sdg.mm ✔
(db 103)`** (base 8 ∪ keystone 2 ∪ D_k 3); `data/sdg.calc.mm` still
`verified all 7 $p ✔` over the D_k-extended base (the layers compose).
Purity guard on the union: **GENUINELY INTUITIONISTIC ✔** — 43
logical `$a`, none classical (NAME + SHAPE), none in any `$p`
consumed-axiom closure. (Prior single-layer S1 figure was 8 `$p` /
92 statements; superseded by the verified union above.)

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

## 5d. The higher-infinitesimal hierarchy D_k — Taylor-base milestone

**This is the Taylor-base milestone. Taylor's formula ITSELF is DEFERRED
to the post-keystone agent and is NOT proved here** (it depends on the
keystone SDG-K pointwise→global linking rule; staying scoped is part of
the task). This milestone extends ONLY the substrate/definitions.

The substrate is extended with the higher-infinitesimal hierarchy
`D_k = { x | x^(k+1) = 0 }`:

- `D_1 = D` — the existing `df-D` (`( D x ) <-> ( x * x ) = 0`,
  i.e. x^2 = x^(1+1) = 0). Unchanged.
- `D_2` — NEW definition `df-D2` (`( D2 x ) <-> ( ( x * x ) * x ) = 0`,
  i.e. x^3 = x^(2+1) = 0). A `df-` (conservative), not an axiom —
  mirrors `df-D`'s discipline.

**The generalized Kock–Lawvere axiom is stated HONESTLY as an axiom
scheme**, not glibly as one sentence. The substrate has no internal
natural-number object, so the ∀k-quantified statement is NOT a single
first-order `$a`; presenting it as if it were would be a misstatement.
The scheme is, for each meta-level natural k:

```
(KL_k)  ∀ f:D_k→R  ∃! (a_0,…,a_k)  ∀ x∈D_k  f(x) = a_0 + a_1 x + … + a_k x^k
```

instantiated at the required levels:

- **k=1** is *literally* the existing `ax-kl` (KL_1 = the original
  Kock–Lawvere axiom — nothing new asserted at k=1). The `$p`
  `sdg-kl1-is-kl` records this reduction as the identity on the exact
  KL_1 formula — an HONEST marker that k=1 adds nothing, NOT a vacuous
  re-derivation dressed up as content.
- **k=2** is NEW: `ax-kl2` (existence: every `D_2→R` map is a unique
  degree-≤2 polynomial `( ap f 0 ) + ( b·d ) + ( e·(d·d) )`) plus
  level-2 microcancellation `ax-microcancel2` (same positive,
  quantifier-only SHAPE as `ax-microcancel`; no `¬`, no `∨`, no
  decidability).

**Pure-substrate-algebra consequences, kernel-verified `$p`:**

| theorem | what it is | consumes | leaves |
|---|---|---|---|
| `sdg-D2-0` | `0` is a level-2 infinitesimal: `( D2 0 )` | ring + df-D2 | 47 |
| `sdg-D1subD2` | **D_1 ⊆ D_2**: `[ ( D x ) ] ⊢ ( D2 x )` (x²=0 ⟹ x³=0) | ring + df-D/df-D2 | 123 |
| `sdg-kl1-is-kl` | KL_1 = `ax-kl` marker: `( KL_1 → KL_1 )` | ax-1/ax-2 (pure logic) | 247 |

`sdg-D1subD2` is the genuine level-inclusion of the hierarchy and is
RING-ONLY: x²=0 ⟹ x³ = (x·x)·x = 0·x = x·0 = 0. No order, no metric
residue, no classical principle.

**MEASURED (this build), adversarially honest:**

```
Kernel: verified all 11 $p in data/sdg.mm ✔  (db: 100 statements)
Purity guard: GENUINELY INTUITIONISTIC ✔ — 43 logical $a audited,
  NONE classical by NAME or SHAPE (df-D2 / ax-kl2 / ax-microcancel2
  included), NONE in any $p consumed-axiom closure.
  sdg-D2-0 = 47   sdg-D1subD2 = 123   sdg-kl1-is-kl = 247   [MEASURED]
```

**Honest open residual at level k≥2 (named, not papered over).**
`ax-microcancel2` is in the base and SHAPE-verified pure, but it is NOT
yet consumed by any `$p`: a level-2 analog of `sdg-deriv` (uniqueness of
the degree-≤2 KL coefficients) would consume it, but that is exactly the
same deduction-theorem / quantifier-proviso seam already documented as
the open residual at level 1 (§5b) — closing it for k=2 would not be new
mathematics here, and threading it toward the global derivative drifts
into the keystone-dependent linking rule this task must NOT touch. So
`ax-kl2`/`ax-microcancel2` are stated and SHAPE-certified pure but, like
`ax-kl` itself, CITED as substrate axioms rather than re-derived. This
is a precisely-characterised scope boundary (a FULL SUCCESS per the Iron
Rule), NOT a hidden gap.

**Honest finding on classicality per level.** No level needs a
classical principle: the hierarchy is *uniformly* intuitionistically
pure. `df-D2`, `ax-kl2`, `ax-microcancel2` all pass the NAME and SHAPE
guard, and every new `$p`'s consumed-axiom closure is classical-free.
Classically each `D_k` collapses to `{0}` (via the metric residue the
substrate REFUSES) and KL_k is vacuous — the whole content is the
intuitionistic setting, and the guard certifies it mechanically.

## 5e. Pointwise-calculus layer (MEASURED; globalization deferred to SDG-K)

The pointwise synthetic differentiation rules from KL, each
kernel-verified and intuitionistic-purity-clean, delivered as the
standalone corpus `data/sdg.calc.mm` (built by `src/bin/sdgcalcbuild.rs`,
measured by `sdgcalcfloor`, guarded by `sdgcalcpure`).

**Intended composition.** `data/sdg.calc.mm` is fully self-contained over
the *identical* `data/sdg.base.mm` axiom surface that `data/sdg.mm` uses,
and shares **no `$p`** with it (disjoint `sdg-calc-*` labels). The two
corpora are independent kernel-checked / purity-checked artifacts;
a downstream union is a rename-free concatenation of their `$p` blocks.
Kept separate deliberately so it never merge-conflicts with the other
in-flight SDG agents that own `data/sdg.mm`.

**POINTWISE ONLY.** Every rule is stated as KL-existence (the affine
slope reps are `$e` hypotheses, mirroring `data/sdg.mm`'s `sdg-slope`
shape) **plus** the pointwise identifying equation. NONE consumes
`ax-microcancel` or `ax-gen` over a linking universal — verified
mechanically (per-theorem consumed-axiom closure). Globalization
(discharging the pointwise identity into a quantified derivative
equation via the pointwise→global seam) is the **separate keystone
SDG-K** and is deliberately NOT attempted or duplicated here.

| rule | what it is | consumes `d·d=0`? | leaves (MEASURED) |
|---|---|---|---|
| `sdg-calc-addcan` | additive cancellation, RING-ONLY | no | 406 |
| `sdg-calc-add4` | commutative-monoid 4-shuffle, RING-ONLY | no | 303 |
| `sdg-calc-rdistr` | right distributivity, RING-ONLY | no | 163 |
| `sdg-calc-sum` | **SUM rule**: slope of `f+g` is `b+c` | **no** (pure ring) | 1055 |
| `sdg-calc-prod` | **PRODUCT/Leibniz**: slope of `f·g` is `f·g'+f'·g` | **YES** (`df-D`+`ax-mul0`) | 3521 |
| `sdg-calc-Dscale` | `(D d) ⊢ (D (b·d))`: R-scaling of an infinitesimal | **YES** (`df-D`+`ax-mul0`) | 401 |
| `sdg-calc-chain` | **CHAIN rule**: slope of `g∘f` is `(g'∘f)·f'` | via `Dscale` | 328 |

Adversarially-honest closure check (mechanical, `sdgcalcpure` +
independent recomputation): `sdg-calc-sum` does **not** reach `df-D`
or `ax-mul0` (it is genuinely pure ring — no `d·d=0`); `sdg-calc-prod`
and `sdg-calc-Dscale` **do** reach both `df-D` and `ax-mul0` — the
Leibniz proof genuinely kills the second-order term `(b·d)·(c·d)` by
rewriting it to `(b·c)·(d·d)`, applying `df-D` to the `(D d)` hypothesis
to get `d·d=0`, then `ax-mul0` to get `(b·c)·0=0`. This is the canonical
SDG product proof; it is **not** hand-waved.

**CHAIN — a precisely-characterised substrate-instantiation
obstruction (reported, not faked; a FULL SUCCESS per the Iron Rule).**
Composing `f`'s affine expansion *into* `g`'s argument is Leibniz
substitution under the function-application symbol `ap`. The authored
`data/sdg.base.mm` instantiates equality's congruence **only** for the
ring operations `+` and `*` (`eq-pl1/2`, `eq-mu1/2`); it provides **no**
`x = y → ( ap g x ) = ( ap g y )`. Adding one would modify the authored
substrate (forbidden) — and note this gap is **not** a classical
principle and **not** the pointwise→global keystone; it is purely that
the substrate's Leibniz is congruence-closed for the ring ops but not
for `ap`. Therefore the single `ap`-Leibniz instance is supplied as one
explicit, loudly-labelled `$e` (`chain.sub`); everything genuinely SDG
is derived — the increment `b·d` is proved infinitesimal by
`sdg-calc-Dscale` (genuinely consuming `d·d=0`) and the scalar collapse
`c·(b·d) = (c·b)·d` is derived. The precise finding: *the chain rule's
"substitute the inner expansion into the outer function" step is
intrinsically function-argument Leibniz; it is not derivable in a
substrate whose congruence is instantiated only for the ring operations.
This is orthogonal to both classicality and globalization.*

`sdgcalcpure` verdict: **GENUINELY INTUITIONISTIC ✔** — all 7 `$p`
intuitionistic; 40 logical `$a` audited (NAME+SHAPE), none classical,
none in any `$p`'s consumed-axiom closure. Kernel: verified all 7 `$p`
in `data/sdg.calc.mm` (101 statements).

## 5f. Keystone integration status (honest, current)

**INTEGRATED.** SDG-K (commit `4f13bac`) and the D_k milestone
(§5d, `46e08c8`) both extended the generator from the same base, so a
kernel-gated merge subagent produced the union builder (commit
`9ea6fe7`) — and it was honest enough to catch and flag an error in
its own brief (its base was the common ancestor, not the Taylorbase
HEAD, so it did a clean 3-way merge of both deltas). The union is now
integrated and **re-verified in-tree** (see §5b): 13 `$p ✔`, seam-free
`sdg-deriv` = 2243, D_k figures (47/123/247) reproduce, `sdg.calc.mm`
still 7 `$p ✔` over the extended base, `sdgpure` GENUINELY
INTUITIONISTIC on the union. The two feature sets are cleanly
composable — the conflict was purely structural, no mathematical
interaction. §5b is RESOLVED *because* the union re-verified here, not
before — the iron rule held for the documentation as it did for the
proofs.


## 5g. Globalized differentiation calculus (MEASURED; the chain `ap` boundary explicit)

The pointwise calculus of §5e (`data/sdg.calc.mm`) is **lifted to GLOBAL
synthetic-derivative theorems** in the integrated union `data/sdg.mm`.
"Global" means the slope is no longer a free coefficient in a *pointwise*
identity (the §5e `$e`-rep discipline) but the **uniquely determined
function value**, discharged through the **same §5b seam fragment** (the
derived deduction-theorem combinators `imp_a1`/`imp_mp`/`imp_eqtr`/
`imp_eqsym`/`imp_cong_*` + guarded `ax-gen` + `ax-spec`) and
`ax-microcancel` that seam-free `sdg-deriv` uses — **NO linking `$e`, NO
`mc.h`-style hypothesis**. The `data/sdg.calc.mm` corpus is read-only; its
two ring helpers were **re-derived in the generator** (`sdg-add4`,
`sdg-rdistr`), not imported.

Each global rule's hypotheses are ONLY universals: the KL existence
representations (`ax-kl` instances, `A. d ( ( D d ) -> … )`) for `f`, `g`
and the composite `w`, **plus** the universal pointwise relation that
*defines* `w` (`w=f+g` / `w=f·g` / `w=g∘f`). The linking universal
`A. d ( ( D d ) -> ( a·d = E·d ) )` is **mechanically threaded** (build the
conjunctive guard under `( D d )` via `ax-ian` lifted by `imp_a1`/detached
by `imp_mp`; deduction-discharged pointwise core via `sdg-addcan-imp` +
the ring helpers; `ax-gen`; `ax-microcancel`), never assumed.

| global rule | statement | consumes | leaves (MEASURED) |
|---|---|---|---|
| `sdg-add4` | comm-monoid 4-shuffle, RING-ONLY | ring eq-ax | **303** |
| `sdg-rdistr` | right distributivity, RING-ONLY | ring eq-ax | **167** |
| `sdg-global-sum` | `( f + g )' = f' + g'` : `⊢ a = ( b + c )` | `ax-microcancel`,`ax-gen`,`ax-spec` (pure ring) | **23508** |
| `sdg-global-prod` | Leibniz globally: `⊢ a = ( ( f(0)·c ) + ( b·g(0) ) )` | + **`df-D`** + **`ax-mul0`** | **39571** |
| `sdg-global-chain` | `( g∘f )' = ( g'∘f )·f'` : `⊢ a = ( c · b )` | `ax-microcancel`,`ax-gen`,`ax-spec` | **28314** |

Integrated union: **`Kernel: verified all 18 $p in data/sdg.mm ✔
(db 124)`**. `sdgpure`: **GENUINELY INTUITIONISTIC ✔** — 43 logical `$a`
audited (NAME+SHAPE), none classical, **none in any `$p`'s
consumed-axiom closure** (all three globals included).

**Adversarially-honest closure audit (kernel-authoritative, recomputed
via `src/kernel.rs` over the emitted union):**

- **Global uniqueness genuinely consumes the seam.** All three globals
  reach `ax-microcancel` **and** `ax-gen` **and** `ax-spec` — the global
  identifying equation is *threaded* from the universal KL reps, not
  taken as a hidden hypothesis. Verified true for
  `sdg-global-sum`/`-prod`/`-chain` (and `sdg-deriv` for reference).
- **`sdg-global-prod` genuinely consumes `df-D` AND `ax-mul0`** (both
  `true` in its closure). The canonical SDG Leibniz proof really kills
  the second-order `( b·d )·( c·d )` term: it is reassociated to
  `( b·c )·( d·d )`, then `df-D` applied to the **shared guard `( D d )`**
  (a genuine conjunct of the deduction antecedent — `d·d=0` is consumed
  exactly there, the honest place) gives `d·d=0`, then `ax-mul0` gives
  `( b·c )·0 = 0`. Not hand-waved.
- **`sdg-global-sum` is pure ring** — does **not** reach `df-D` or
  `ax-mul0` (no `d·d=0`); `sdg-global-chain` likewise does not reach
  them (its infinitesimal content is entirely inside the surfaced `$e`).

**CHAIN — the `ap`-congruence boundary, HELD (reported, not faked; a
FULL SUCCESS per the Iron Rule).** Composing `f`'s affine expansion
*into* `g`'s argument is Leibniz substitution under the
function-application symbol `ap`. The authored `data/sdg.base.mm`
instantiates equality's congruence **only** for the ring operations `+`
and `*` (`eq-pl1/2`, `eq-mu1/2`); it provides **no**
`x = y → ( ap g x ) = ( ap g y )`. This gap is **not** a classical
principle and **not** the pointwise→global seam — it is precisely the
SEQUEL §5e `ap`-congruence substrate-instantiation gap. Per the task we
**STOP at exactly this boundary**: the single `ap`-Leibniz instance is
surfaced as **one loudly-labelled universal `$e`** (`chain.sub`,
`A. d ( ( D d ) -> ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b·d ) ) ) )`)
— **exactly as the pointwise `sdg-calc-chain` did** — and **nothing
else** is assumed: the globalization seam (uniqueness via
`ax-microcancel`, the universal threading) is still fully discharged.
We did **NOT** add an `ap`-congruence axiom (that is the held
**W2-apcong follow-on**'s job). The kernel-authoritative audit confirms
the boundary held: **no `ap`-congruence axiom appears in any closure**
(`apcong:[]`; only the pre-existing `tap` *term* constructor, which is
not a congruence rule). Staying at the boundary IS the honest result.

The mirror hypothesis remains SUPPORTED and is now *strengthened*: the
entire globalized synthetic-differentiation calculus (sum, product,
chain) needs exactly KL (existence, cited) + microcancellation
(uniqueness, consumed) + the `df-D`/`ax-mul0` ring residue for Leibniz —
and **NOTHING classical**, at every rule, mechanically certified. The
only honest residual is the orthogonal `ap`-congruence substrate gap,
isolated to one labelled `$e` in the chain rule.

## 5h. Synthetic Taylor — ORDER-2, MEASURED (BOOK TWO / SDG, wave 2)

The order-2 synthetic Taylor formula, kernel-verified and
intuitionistic-purity-clean, delivered as the standalone corpus
`data/sdg.taylor.mm` (built by `src/bin/sdgtaybuild.rs`, measured by
`sdgtayfloor`, guarded by `sdgtaypure` — the `sdgcalc*` trio pattern,
copied exactly).

**Composition / zero-conflict.** `data/sdg.taylor.mm` is fully
self-contained over the *identical* FROZEN `data/sdg.base.mm` axiom
surface, shares **no `$p`** with `data/sdg.mm` or `data/sdg.calc.mm`
(disjoint `sdg-tay-*` labels), and touches none of `src/bin/sdgbuild.rs`,
`src/kernel.rs`, `src/elaborate.rs`, the prequel, or any other agent's
files. It conflicts with nothing; a downstream union is a rename-free
concatenation of `$p` blocks.

**The general meta-k Taylor scheme (stated HONESTLY as a scheme, like
§5d).** For each meta-level natural `k`, order-`k` synthetic Taylor on
`D_k = { x | x^(k+1)=0 }` is

```
(TAY_k)  forall f:R->R, forall x, forall δ∈D_k :
         f(x+δ) = Σ_{i=0..k} a_i(x)·δ^i      with the a_i UNIQUE,
         a_0 = f(x), a_1 = f'(x), ... (the i-th synthetic Taylor coeff)
```

an axiom **scheme** indexed by the meta-level `k` (the substrate has no
internal natural-number object, so the ∀k statement is NOT one first-
order `$a`; presenting it as one would be a glib misstatement, so we do
not). Existence at level `k` is exactly `KL_k`; uniqueness is `MC_k`
(level-k microcancellation). Instantiated:

- **k=1** is *literally* the existing order-1 synthetic derivative
  (§4/§5b): `f(x+δ)=f(x)+δ·f'(x)` on `D_1`, existence = `ax-kl`,
  uniqueness = `ax-microcancel`. The `$p` `sdg-tay-k1-reduce` records
  this reduction as the identity on the exact `KL_1` formula — an
  HONEST marker that k=1 adds nothing, NOT a vacuous re-derivation.
- **k=2** is delivered here: `f(x+δ)=f(x)+δ·f'(x)+(δ·δ)·s(x)` on `D_2`,
  existence = `ax-kl2` (CITED — a substrate axiom; restating it as a
  one-line `$p` would be vacuous, same discipline as `ax-kl`),
  uniqueness of the linear (derivative) coefficient genuinely consuming
  `ax-microcancel2`.

**Kernel-verified `$p`, MEASURED (cut-free `$a`-leaf, project metric):**

| theorem | what it is | consumes | leaves |
|---|---|---|---|
| `sdg-tay-addcan` | additive cancellation, RING-ONLY | ring eq-axioms | 406 |
| `sdg-tay-addcan-imp` | deduction-discharged form of the above | sdg-tay-addcan | 851 |
| `sdg-tay-quad-slope` | **order-2 pointwise uniqueness of the linear coeff** | sdg-tay-addcan (×2) | 1190 |
| `sdg-tay-quad-slope-imp` | hyp-free conjunctive form (seam combinators) | sdg-tay-addcan-imp | 5378 |
| `sdg-tay-deriv2` | **THE HEADLINE: seam-free order-2 uniqueness** | **`ax-microcancel2`** | 6080 |
| `sdg-tay-k1-reduce` | honest k=1 marker (`KL_1` = `ax-kl`) | ax-1/ax-2 (pure logic) | 247 |

`sdgtayfloor`: **`Kernel: verified all 6 $p in data/sdg.taylor.mm ✔`**
(db 94 statements). `sdgtaypure`: **GENUINELY INTUITIONISTIC ✔** — 43
logical `$a` audited (NAME+SHAPE, incl. `df-D2`/`ax-kl2`/
`ax-microcancel2`), none classical, none in any `$p`'s consumed-axiom
closure.

**Adversarially-honest decomposition of "order-2 Taylor existence +
uniqueness".**

- **Existence** of the degree-≤2 expansion on `D_2` is *exactly*
  `ax-kl2`. It is a substrate axiom; CITED, stated plainly, NOT hidden,
  NOT measured as content (same discipline `sdg-deriv` used for `ax-kl`).
- **Order-2 pointwise uniqueness** (`sdg-tay-quad-slope`, MEASURED 1190)
  is the genuine new mathematical content beyond order-1: from two
  degree-≤2 KL2 representations of the same `(ap f d)` sharing the
  constant `K=(ap f 0)` and the quadratic coefficient `q`, it derives
  `(b·d)=(c·d)` by additive cancellation applied **twice** — it cancels
  the quadratic monomial `q·(d·d)` (commuted to the front) **and** the
  constant `K`. Order-1's `sdg-slope` only had a constant to cancel; the
  quadratic term is genuinely present here and genuinely killed. RING-
  ONLY: no order, no metric residue, no classical principle, no
  microcancellation.
- **Seam-free global uniqueness** (`sdg-tay-deriv2`, MEASURED 6080)
  GENUINELY CONSUMES `ax-microcancel2`. Its only hypotheses are the two
  *universal* degree-≤2 KL2 representations over `D_2`
  (`tay2.hb`/`tay2.hc`, each an `ax-kl2` instance — EXISTENCE). The
  linking universal `A. d ( ( D2 d ) -> ( b·d )=( c·d ) )` is
  MECHANICALLY THREADED (ax-spec strips `A.d`; `ax-ian` lifted under
  `( D2 d )`; `sdg-tay-quad-slope-imp` threaded under `( D2 d )`;
  `ax-gen` over `d`), then `ax-microcancel2` detaches `b = c`. Verified
  RPN ends `… ax-gen vd vb vc ax-microcancel2 ax-mp`. **NO linking
  `$e`** — this is the exact order-2 mirror of `data/sdg.mm`'s seam-free
  `sdg-deriv` (which consumed `ax-microcancel`), and `sdgtaypure` has a
  hard-coded adversarial assertion that `sdg-tay-deriv2`'s consumed-
  axiom closure contains `ax-microcancel2` (it does: 27 axioms,
  `YES ✔`) — if it did not, the guard exits non-zero and refuses to
  certify. Uniqueness is **not** hand-waved.

**No explicit `$e` boundary was needed.** Unlike `sdg.calc.mm`'s chain
rule (the `ap`-Leibniz `chain.sub` `$e`), the order-2 Taylor uniqueness
required NO extra labelled `$e`: the §5b seam-closing deduction-form
combinators (reproduced self-contained here, emitting only
`ax-1/ax-2/ax-mp/ax-ial/ax-iar/ax-ian/ax-spec/ax-gen/eq-*` — all
intuitionistically pure) discharge the pointwise→`D_2`-universal seam
mechanically, exactly as the integrated `sdg-deriv` does at level 1. The
linking universal is a threaded `ax-gen`, not an assumed `$e`. (The
`ax-gen` soundness proviso — `d` not free in any discharged essential
hypothesis — holds: the only discharged hyps `tay2.hb`/`tay2.hc` bind
`d` under `A. d`. Same metatheoretic discipline as the prequel's
quantifier provisos and `data/sdg.mm`'s seam-free `sdg-deriv`.)

**Honest finding on classicality.** Order-2 Taylor is uniformly
intuitionistically pure: `ax-kl2`, `ax-microcancel2`, `df-D2` all pass
NAME+SHAPE; every `$p`'s consumed-axiom closure is classical-free.
Classically `D_2` collapses to `{0}` (via the metric residue the
substrate REFUSES) and the expansion is vacuous — the whole content is
the intuitionistic setting, and `sdgtaypure` certifies it mechanically.
Uniqueness of the **quadratic** coefficient (the level-2 analog at the
`e`-slot) would consume the `e`-form of `ax-microcancel2`; that is a
clean further level the scheme documents, not attempted here, and is a
precisely-characterised scope boundary, not a hidden gap.

## 5i. Synthetic tangent structure (MEASURED; one labelled boundary)

The synthetic tangent layer, kernel-verified and intuitionistic-purity-
clean, delivered as the standalone corpus `data/sdg.tangent.mm` (built by
`src/bin/sdgtanbuild.rs`, measured by `sdgtanfloor`, guarded by
`sdgtanpure`) — the proven `data/sdg.calc.mm` zero-conflict pattern:
fully self-contained over the *identical frozen* `data/sdg.base.mm` axiom
surface, sharing **no `$p`** with `data/sdg.mm` or `data/sdg.calc.mm`
(disjoint `sdg-tan-*` labels). A downstream union is a rename-free
concatenation. Nothing else was modified (not `sdgbuild.rs`,
`data/sdg.mm`, `data/sdg.base.mm`, `data/sdg.calc.mm`, `src/kernel.rs`,
`src/elaborate.rs`, or other agents' files).

**The objects.** A *tangent vector at a point* is a map `t : D → R`
over the line object `R` as model space; its base point is `( ap t 0 )`.
The *tangent bundle* is `R^D`. A *vector field* is a section
`X : R → R^D`; by the correspondence below it is carried by its
*principal part* `p : R → R`, `X(x)(d) = ( x + ( ( ap p x ) · d ) )`.

| theorem | what it is | consumes | leaves (MEASURED) |
|---|---|---|---|
| `sdg-tan-addcan` | additive cancellation, RING-ONLY | ring eq-axioms | 406 |
| `sdg-tan-addcan-imp` | deduction-discharged cancellation, RING-ONLY | ax-1/ax-2/eqtri/eq-* | 851 |
| `sdg-tan-base` | `R×R→R^D` lands at the base pt: `( a + ( b·0 ) ) = a` | ring (`ax-mul0`,`ax-add0`) | 46 |
| `sdg-tan-roundtrip` | `R×R→R^D→R×R = id`: `( ( a+(b·0) )+(b·d) ) = ( a+(b·d) )` | sdg-tan-base | 64 |
| `sdg-tan-slope-imp` | pointwise principal-part identity, RING-ONLY | sdg-tan-addcan-imp | 1727 |
| `sdg-tan-principal` | **`R^D ≅ R×R`**: the principal part is UNIQUE | **`ax-microcancel`** (+`ax-gen`) | 2243 |
| `sdg-tan-bracket-cross` | microsquare commutator is symmetric at 0th order, RING | `ax-mulcom` | 30 |
| `sdg-tan-bracket` | the Lie bracket identity, modulo ONE boundary `$e` | sdg-tan-bracket-cross | 116 |

**`R^D ≅ R×R` genuinely CONSUMES KL — adversarially honest.** The
forward map `R^D → R×R` sends `t` to `( ( ap t 0 ) , b )` where `b` is
its KL principal part. For the correspondence to be a bijection (not a
mere surjection) `b` must be *uniquely determined* — that is KL's
uniqueness half. `sdg-tan-principal` is the seam-free statement: from two
universal affine KL representations (each an `ax-kl` EXISTENCE instance,
the `$e` hypotheses `pp.hb`/`pp.hc`) it derives `b = c`. It is threaded
*exactly* like `data/sdg.mm`'s headline seam-free `sdg-deriv`
(ax-spec → ax-ian conjunction under the `( D d )` guard → ring-only
pointwise slope `sdg-tan-slope-imp` → `ax-gen` closing the universal →
`ax-microcancel` detaching `b=c`). Mechanically verified: the
`sdg-tan-principal` RPN literally contains `ax-microcancel` (×1) and
`ax-gen` (×1); its consumed-axiom closure (sdgtanpure, 27 axioms)
includes `ax-microcancel`. KL's uniqueness is **consumed, not asserted**.
The `R×R → R^D` direction (`sdg-tan-base`, `sdg-tan-roundtrip`) is
PURE RING. MEASURED `sdg-tan-principal` = **2243** leaves (identical to
the seam-free `sdg-deriv` figure — same construction, independently
re-derived self-contained, not imported).

**The Lie bracket — the genuine `D×D` microsquare, with ONE precisely-
characterised boundary `$e` (a FULL SUCCESS per the Iron Rule).** The
bracket `[X,Y]` is read off the commutator of the two infinitesimal
flows on the microsquare `D×D`. The substrate genuinely proves the first
real reduction: the *symmetric zeroth-order* part of the commutator
vanishes — `( ( ( ap p x )·( ap q x ) )·( d₁·d₂ ) ) =
( ( ( ap q x )·( ap p x ) )·( d₁·d₂ ) )` (`sdg-tan-bracket-cross`,
RING-ONLY via `ax-mulcom`), so the scalar commutator is *not* the
bracket and the bracket lives entirely in the next-order derivative
term. The single genuinely off-limits step — composing one field's flow
*into* the other's argument to produce the bracket principal part
`[X,Y] = X(q) − Y(p)` — is **BOTH** (a) `ap`-Leibniz / `ap`-congruence
(the *same* documented `data/sdg.calc.mm` chain-rule substrate gap:
`data/sdg.base.mm` instantiates Leibniz only for `+`/`*`
(`eq-pl1/2`,`eq-mu1/2`), there is **no** `x=y → ( ap g x )=( ap g y )`;
`grep` confirms none in the base — adding one would modify the frozen
substrate, forbidden) **and** (b) a globalized / generator-side
derivative of the principal part (W2-glob, the keystone-side machinery
this task must NOT touch — `X(q)` is the synthetic derivative of `q`
along `X`, needing the deferred pointwise→global linking rule). Both
obstructions are *orthogonal to classicality*. The composite step is
surfaced as **EXACTLY ONE loudly-labelled `$e`** (`tanbr.flow`);
`sdg-tan-bracket` then closes the bracket's defining identity from it by
pure ring algebra (swapping the scalar via `sdg-tan-bracket-cross`). The
microsquare algebra is genuine; only the one cross-substitution is the
reported boundary — it is reported, not faked.

**MEASURED outcome (this build), adversarially honest:**

```
Kernel: verified all 8 $p in data/sdg.tangent.mm ✔  (db: 95 statements)
sdgtanpure: GENUINELY INTUITIONISTIC ✔ — 43 logical $a audited
  (NAME+SHAPE), NONE classical, NONE in any $p consumed-axiom closure.
  sdg-tan-base=46  sdg-tan-roundtrip=64  sdg-tan-addcan=406
  sdg-tan-addcan-imp=851  sdg-tan-slope-imp=1727
  sdg-tan-principal=2243 (CONSUMES ax-microcancel — KL uniqueness)
  sdg-tan-bracket-cross=30  sdg-tan-bracket=116 (ONE $e: tanbr.flow)
                                                          [MEASURED]
```

**Self-contained composition statement.** `data/sdg.tangent.mm` is a
rename-free extension of the frozen `data/sdg.base.mm` by eight
`sdg-tan-*` `$p`; it is independently kernel-checked and
purity-checked, shares no `$p` with `data/sdg.mm`/`data/sdg.calc.mm`,
and composes with them by concatenation. The honest residual is exactly
ONE `$e` (`tanbr.flow`) carrying the `ap`-congruence + W2-glob bracket
step — a precisely-characterised boundary identical in kind to the
already-documented chain-rule gap, NOT a hidden assumption and NOT a
classical smuggle (sdgtanpure certifies the latter mechanically).

## 5j. The `ap`-congruence resolution — KEYSTONE (verdict B, PROVEN)

This is the Book Two keystone: the rigorous A-vs-B classification of
function-application congruence, the discharged `chain.sub` `$e`, the
Lie-bracket `ap`-half, MEASURED, and the honest trust-story statement.

### The QUESTION, answered: VERDICT B (NOT A) — with proof

`x = y → ( ap g x ) = ( ap g y )` is **GENUINELY NOT DERIVABLE** from
the substrate's equality discipline. It is **B**, not A.

**Why it is not A.** Despite the `data/sdg.base.mm` header prose
"Leibniz substitution", the substrate's *actual* equality theory is, in
full: `eqid` (reflexivity), `eqcom` (symmetry), `eqtri` (transitivity),
and the **four per-operation congruence axioms** `eq-pl1/2`, `eq-mu1/2`
for `+` and `*` **only**. There is **no** general Leibniz schema
`( x = y → ( ph → ph[y/x] ) )` and **no** congruence rule for any other
term constructor (`ap`, `inv`, `deriv`). Equality here is an
equivalence relation equipped with *hand-picked* congruence rules for
the ring operations and nothing else. Congruence under an arbitrary
constructor is therefore *not* "normally a consequence of Leibniz
substitution" **in this substrate**, because this substrate has no
Leibniz substitution — only the listed instances.

**Proof of non-derivability (syntactic, kernel-faithful — the exact
discipline `src/kernel.rs` enforces).** Define the *ap-skeleton* of a
term as the multiset of its maximal `( ap _ _ )` subterms. Claim: every
closed equation `s = u` derivable from `{ eqid, eqcom, eqtri,
eq-pl1/2, eq-mu1/2, df-D }` + pure logic with **no equality `$e`**
satisfies `skeleton(s) = skeleton(u)`. Induction on the derivation:
`eqid` gives `s = s` (trivial); `eqcom`/`eqtri` are the
equivalence-closure of a relation already having the invariant;
`eq-pl1/2`, `eq-mu1/2` rewrite a subterm sitting in a `+`/`*` position
and **never** inside the argument slot of an `( ap _ _ )`; `df-D`
introduces only ring/`0` equations. **No axiom's conclusion can rewrite
the argument position of an `ap`.** Hence for distinct variables `x`,
`y` (`x = y` itself underivable, distinct skeletons), the equation
`( ap g x ) = ( ap g y )` has unequal skeletons and is outside the
derivable set. **QED — B is proven, not assumed.** (Model gloss:
quotient the term algebra by the ring-axiom congruence and let `ap` act
non-extensionally on distinct-but-ring-equal arguments — every `$a`
above holds, `ap`-congruence fails.)

### The resolution: ONE flagged, intuitionistically-pure substrate axiom

Per the B branch of the task: added `eq-ap` to `data/sdg.base.mm`,
**FLAGGED exactly as `ax-kl` / `ax-microcancel`** (a long named-block
header: "FLAGGED NON-CONSERVATIVE SUBSTRATE COMMITMENT #3"):

```
eq-ap $a |- ( x = y -> ( ap g x ) = ( ap g y ) ) $.
```

**Intuitionistic acceptability (rigorous, mechanically certified).**
`eq-ap` is a **positive Horn congruence schema**: one atomic-equality
antecedent, one atomic-equality consequent, **no `¬`, no `∨`**, no
`→`-nesting, no quantifier alternation, no decidability/stability/
apartness. It is the literal structural twin of the already-present
`eq-pl1/2`, `eq-mu1/2` (same shape, different constructor) and is the
eq-elimination/transport rule of every intuitionistic type theory,
valid in every Heyting-valued/topos model. All five purity guards
(`sdgpure`, `sdgcalcpure`, `sdgtanpure`, `sdgtaypure`, `sdgcalc2pure`)
re-certify **GENUINELY INTUITIONISTIC ✔** — now **44** logical `$a`
(was 43; +1 = `eq-ap`), `eq-ap` passing NAME and SHAPE, none classical,
none classical in any `$p`'s consumed-axiom closure.

### Deliverable 1 — seam-free chain rule (DISCHARGED, MEASURED)

New self-contained corpus `data/sdg.calc2.mm` (builder
`src/bin/sdgcalc2build.rs`, guard+floor `src/bin/sdgcalc2pure.rs`):
disjoint `sdg-calc2-*` labels, rename-free-concatenation composition,
shares no `$p` with any other corpus. `sdg-calc2-chain` re-proves the
pointwise chain rule **with NO `chain.sub` `$e`** — the substitution
step `( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b·d ) ) )` is now
one `eq-ap` inference off the KL slope hypothesis of `f`.

| theorem | what it is | consumes | leaves (MEASURED) |
|---|---|---|---|
| `sdg-calc-chain` (old, `data/sdg.calc.mm`) | chain rule WITH `chain.sub` `$e` | (ap-Leibniz `$e`) | **328** |
| `sdg-calc2-chain` (new, seam-free) | chain rule, NO `$e`, USES `eq-ap` | **`eq-ap`** (no `ax-microcancel`) | **349** |
| `sdg-calc2-apflow` | Lie-bracket `ap`-half: `[ ( ap f d )=z ] ⊢ ( ap g ( x+( ap f d ) ) )=( ap g ( x+z ) )` | `eq-pl2`+**`eq-ap`** | **24** |

**MEASURED cut-free cost of the discharged chain rule: 349 leaves**
(project metric, OUR kernel over `data/sdg.calc2.mm`). The honest delta
is **+21 leaves** vs the `$e`-bearing `sdg-calc-chain` (328): a cost
*revealed, not added* — it is exactly the `eq-ap` instantiation
(`vd vf tap | t0 vf tap vb vd tmu tpl | vg eq-ap ax-mp` + its `wi`
construction) that was previously **hidden inside the zero-cost
`chain.sub` `$e`**. Kernel-authoritative adversarial assertions in
`sdgcalc2pure` (hard-fail if false): `sdg-calc2-chain` **genuinely
consumes `eq-ap`** (YES ✔), does **NOT** consume `ax-microcancel`
(NO ✔ — still pointwise), and **NO `chain.sub` `$e` exists** in the
corpus (NO ✔ — discharged).

### Deliverable 2 — Lie-bracket `ap`-half: UNBLOCKED; W2-glob residual precise

`data/sdg.tangent.mm`'s `tanbr.flow` `$e` was documented (§5i) as
folding together **(a)** `ap`-congruence **and (b)** W2-glob
generator-side globalization. With `eq-ap`, **half (a) is now
unblocked**: `sdg-calc2-apflow` mechanically discharges the
flow-composition `ap`-Leibniz step as a pure `eq-pl2`+`eq-ap`
derivation (6 axioms, 24 leaves, intuitionistic, **no
microcancellation, no globalization**). **Half (b) remains the
precisely-characterised residual** and is **NOT** closed: `X(q)` is the
synthetic *derivative* of `q` along `X`, which needs the
pointwise→global SDG-K linking rule (off-limits this round). **The full
Lie bracket does NOT close here — claiming it would be faking it.** The
honest status: the `ap` half is closed (eq-ap, kernel-verified,
demonstrated); the globalization half is exactly the SDG-K linking
residual already documented at §5b/§5g, now isolated as the *sole*
remaining obstruction in the bracket (the `ap` half no longer
contributes).

### Deliverable 3 — purity across everything touched

All five guards GENUINELY INTUITIONISTIC ✔ on the eq-ap-extended base:
`sdgpure` (`data/sdg.mm`, 18 `$p`, 125 stmts), `sdgcalcpure`
(`data/sdg.calc.mm`, 7 `$p`), `sdgtanpure` (`data/sdg.tangent.mm`,
8 `$p`), `sdgtaypure` (`data/sdg.taylor.mm`, 6 `$p`), `sdgcalc2pure`
(`data/sdg.calc2.mm`, 2 `$p`). Adding an axiom is monotone: every
pre-existing `$p` in every corpus still kernel-verifies unchanged.
`eq-ap` passes NAME+SHAPE in all of them (positive Horn — no `¬`,
no `∨`).

### THE HONEST TRUST-STORY STATEMENT (did the substrate gain an axiom?)

**YES. The substrate GAINED ONE NAMED AXIOM, `eq-ap`.** Book Two's
trust story is therefore stated plainly: **`ap`-congruence is a NEW
NAMED intuitionistic substrate axiom (verdict B), NOT a derived rule.**
It is *not* a consequence of the pre-existing equality discipline (the
ap-skeleton proof shows this rigorously); it is a flagged,
non-conservative, but *intuitionistically pure* (positive Horn
congruence — mechanically certified, zero classical content) commitment
of the same status as `ax-kl` and `ax-microcancel`. The honest
classification is the deliverable and it is: **B, with `eq-ap` added
and flagged, not smuggled.** The mirror hypothesis is unaffected — no
classical principle entered; the new axiom is the constructive
transport rule for the `ap` term former, which every intuitionistic
type theory already has. The cut-free chain rule is genuinely
seam-free at MEASURED 349 leaves; the Lie bracket's `ap` half is
closed and its sole residual is the orthogonal, pre-documented SDG-K
globalization, not the `ap` gap.

## 5l. Synthetic-connections layer — the BOOK-3 BRIDGE (MEASURED; the explicit W3-glob2 boundary)

The definitional + cleanly-provable synthetic-connection layer,
kernel-verified and intuitionistic-purity-clean, delivered as the
standalone corpus `data/sdg.conn.mm` (built by `src/bin/sdgconnbuild.rs`,
measured by `sdgconnfloor`, guarded by `sdgconnpure` — the proven
`sdgcalc*`/`sdgtan*`/`sdgcalc2*` trio pattern, copied exactly).

**This is the Book-3 bridge.** It lays Book 3's foundation early in the
Taylorbase scaffolding pattern. Book 3's thesis — gauge theory's
differential-geometric content needs no classical-analysis apparatus and
encodes in small intuitionistic kernel proofs — is here *partially
TESTED, not assumed*: the connection's structural layer is proven
pure-ring intuitionistic; the exact point where curvature/Bianchi
genuinely needs off-limits machinery is precisely named.

**Composition / zero-conflict.** `data/sdg.conn.mm` is fully
self-contained over the *identical* FROZEN eq-ap-extended
`data/sdg.base.mm` axiom surface (untouched — `git diff` empty), shares
**no `$p`** with `data/sdg.mm`/`data/sdg.calc.mm`/`data/sdg.calc2.mm`/
`data/sdg.tangent.mm`/`data/sdg.taylor.mm` (disjoint `sdg-conn-*`
labels), and modifies none of `sdgbuild.rs`, `data/sdg.mm`,
`data/sdg.base.mm`, the other corpora, `src/kernel.rs`,
`src/elaborate.rs`, or any other agent's file. A downstream union is a
rename-free concatenation.

**The objects (Kock/Nishimura synthetic-connection setting, in the line
model `R`).** A (Koszul/affine) connection is carried by its
Christoffel-like symbol `G : R → R` (`( ap g x )`), a `D→` linear
KL-affine map. Infinitesimal **parallel transport** of a vector `v` at
base point `x` along `d ∈ D` is
`P_d(v) = ( v + ( ( ( ap g x ) · v ) · d ) )` — affine in the
infinitesimal `d` (the KL shape) with constant term `v` (transport at
`d=0` = identity). The **connection difference / torsion** is the
(1,2)-tensor `S = G − H`. **Curvature** = the `D×D`
infinitesimal-square holonomy.

**Kernel-verified `$p`, MEASURED (cut-free `$a`-leaf, OUR project
metric):**

| theorem | what it is | consumes | leaves |
|---|---|---|---|
| `sdg-conn-transport0` | `P_0(v) = v`: transport at the zero infinitesimal is the identity | ring (`ax-mul0`,`ax-add0`) | 62 |
| `sdg-conn-kl-affine` | transport is KL-affine: rebuild-from-extracted-constant = the transport map | sdg-conn-transport0 (RING) | 92 |
| `sdg-conn-diff-tensor` | connection difference `S=G−H` is a well-defined (1,2)-tensor displacement | RING + `conn.diff` (pure-ring $e) | 48 |
| `sdg-conn-torsion-sym` | torsion-free scalar symmetry of the transport coefficient | ring (`ax-mulcom`) | 20 |
| `sdg-conn-curv-cross` | **symmetric zeroth-order part of the `D×D` holonomy commutator VANISHES** | ring (`ax-mulcom`) | 60 |
| `sdg-conn-curvature` | the curvature identity, modulo ONE boundary `$e` (`conn.hol`) | sdg-conn-curv-cross + `conn.hol` | 230 |

`sdgconnfloor`/`sdgconnpure`: **`Kernel: verified all 6 $p in
data/sdg.conn.mm ✔`** (db 92 statements). `sdgconnpure`: **GENUINELY
INTUITIONISTIC ✔** — 44 logical `$a` audited (NAME+SHAPE, incl.
`eq-ap`), none classical, **none in any `$p`'s consumed-axiom closure**.

**Adversarially-honest decomposition (kernel-authoritative,
`sdgconnpure` hard-fails if false).**

- **The cleanly-reachable structural layer is PURE RING.**
  `sdg-conn-transport0`, `-kl-affine`, `-diff-tensor`, `-torsion-sym`,
  `-curv-cross` each have a consumed-axiom closure that reaches **none**
  of `ax-microcancel`/`ax-microcancel2`/`ax-kl`/`ax-kl2`/`ax-gen`/
  `ax-spec` (mechanically asserted, hard-fail). Transport KL-affinity,
  connection difference/torsion well-definedness, and the symmetric
  zeroth-order vanishing of curvature need **no globalization, no
  microcancellation, nothing classical** — exactly the cleanly-provable
  facts that do not need the W3-glob2 keystone.
- **`conn.diff` is a pure-ring tensor-definition `$e`, NOT a boundary.**
  It supplies the *definition* `S := G − H` as a value identity
  (`( ap w x ) = ( ( ap g x ) + ( inv ( ap u x ) ) )`); the
  well-definedness is then RING-ONLY congruence. It carries no
  `ap`-congruence and no globalization.
- **Curvature genuinely needs the globalized bracket — ONE precisely-
  characterised boundary `$e` (`conn.hol`).** The `D×D` holonomy's
  *symmetric zeroth-order* scalar part vanishes RING-ONLY
  (`sdg-conn-curv-cross`, `ax-mulcom`), so the curvature is genuinely the
  *next-order* term, not the scalar commutator. Producing the actual
  curvature principal part `R(d₁,d₂)` — composing one direction's
  transport *into* the other's argument, evaluating the outer Christoffel
  symbol at the inner-transported point `( ap g ( x + … ) )` and
  expanding it — is **BOTH** (a) `ap`-Leibniz substitution **and** (b) a
  **globalized / generator-side derivative of the Christoffel symbol**:
  the curvature is the synthetic *derivative* of `G` along the transport,
  needing the pointwise→global linking rule. Here (a) and (b) are
  **inseparable** — there is no value to substitute under `ap` until the
  generator-side derivative of `G` is taken — so even though `eq-ap`
  (§5j) exists in the base, it cannot discharge this alone. **This is the
  PRECISE Book-3 dependency map: curvature/Bianchi genuinely needs
  W3-glob2 (the globalized bracket).** It is surfaced as **EXACTLY ONE
  loudly-labelled `$e`** (`conn.hol`); `sdgconnpure` asserts (hard-fail)
  exactly two `conn.*` `$e` exist — the `conn.hol` boundary + the
  pure-ring `conn.diff` tensor definition. Both obstructions are
  **orthogonal to classicality** (`sdgconnpure` certifies the closure
  classical-free mechanically).

**Self-contained composition statement.** `data/sdg.conn.mm` is a
rename-free extension of the frozen eq-ap-extended `data/sdg.base.mm` by
six `sdg-conn-*` `$p`; independently kernel-checked and purity-checked;
shares no `$p` with any other corpus; composes by concatenation. The
honest residual is **exactly ONE boundary `$e`** (`conn.hol`) carrying
the inseparable `ap`-congruence + W3-glob2 globalized-bracket curvature
step — a precisely-characterised boundary (a FULL SUCCESS per the Iron
Rule), the Book-3 dependency map, NOT a hidden assumption and NOT a
classical smuggle. The mirror hypothesis is unaffected: no classical
principle entered; the structural connection layer is uniformly
intuitionistically pure, and the single thing curvature/Bianchi depends
on is named exactly — the globalized bracket W3-glob2, Book 3's keystone.

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
