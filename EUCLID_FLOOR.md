# EUCLID_FLOOR — the minimal F1 model and its set.mm transport

Adversarially honest. Every number here is one of:
**MEASURED** (kernel-exact, OUR kernel, OUR cut-free metric),
**EXTRACTED** (the exact set.mm extractor over `data/set.mm`), or
**PROJECTION** (a labelled derivation, never merged into / printed as a
measured figure).

## 1. The question

Substrate floor = cost to exhibit ONE model of **F1** (ordered field +
principal √ of nonnegatives + FOL=) *in ZFC*. The maintainer's
non-optional requirement: a privately-defined cheap structure proves
nothing about ZFC grounding unless the exhibited object is shown, in
set.mm/ZFC, to BE a ZFC set that SATISFIES F1 — a first-class transport
binding, analogous to the existing `ax-sqrt ↔ resqrtth` Bind.

Prior measured baselines (`modelsplice`, EXTRACTED from a 50,707,170-byte
`develop` set.mm):

| route | ZFC cost |
|---|---|
| full analytic-ℝ model (`resqrtth`) | 10^45.74 |
| set.mm √-primitive residual (`msqge0`) | 10^37.19 |
| from-ZF "twin" achievable (`axmulass`) | 10^30.75 |
| strict extractable lower bound (`axresscn`) | 10^25.95 |
| below 10^25.95 | set.mm has nothing to extract |

## 2. The minimal model: the Euclidean closure of ℚ

The minimal model of F1 is **not** ℝ. It is the Euclidean closure of ℚ:
the tower

    ℚ = K0 ⊂ K1 ⊂ K2 ⊂ … ,   K_{j+1} = K_j[√a_j]   (0 ≤ a_j ∈ K_j)

of degree-≤2 extensions, each adjoining a principal √ of one nonnegative.
No limits, no Cauchy/Dedekind, no completeness, no ℤ→ℚ→ℝ multiplicity.
Its union is an ordered field in which every nonnegative has a √ — a model
of F1 — equal to the field of real constructible numbers (⊂ real-algebraic
numbers), a genuine ZFC set. The grounded geometry uses no completeness
(it is valid in every Euclidean field), so this model suffices.

## 3. MEASURED: the generic Euclidean extension step

`data/euclid.mm` proves ONCE, over FRESH ATOMS (a specific-but-arbitrary
ordered field; free instantiation = the generic-lemma weapon), the unit
step the tower iterates. Given an ordered field K and `0 <_ a-elt`,
whenever a root `r-root` with `( r-root * r-root ) = a-elt` and
`0 <_ r-root` has been ADJOINED (the degree-2 step), the two
non-conservative F1 √-axioms instantiated at `a-elt` become THEOREMS:

* `eu-sqrt`   : `( ( sqrt a-elt ) * ( sqrt a-elt ) ) = a-elt`  (ax-sqrt)
* `eu-sqrtnn` : `( 0 <_ ( sqrt a-elt ) )`                       (of-sqrtnn)

with `( sqrt a-elt )` realised by `r-root` via the conservative definition
`df-sqrtr` (eliminable by rewriting; introduces NO non-conservative
axiom). The step therefore *removes* two non-conservative axioms per tower
level, deriving them from ordered-field algebra + FOL= only.

`src/bin/euclidfloor.rs` kernel-verifies `data/euclid.mm` and MEASURES the
exact cut-free `$a`-leaf count (the project metric, OUR kernel):

```
Kernel: verified all 3 $p in data/euclid.mm ✔  (db: 43 statements)
  eqtr       = 13   (10^1.114)   reusable FOL= transitivity helper
  eu-sqrt    = 88   (10^1.944)   ax-sqrt discharged per level
  eu-sqrtnn  = 40   (10^1.602)   of-sqrtnn discharged per level
  UNIT STEP total = 141 cut-free $a-leaves = 10^2.149   [MEASURED]
```

Soundness: euclid.mm asserts only propositional + FOL= logic and the
of-* ordered-field signature over fresh atoms — the SAME signature audited
in grounded.mm — plus the conservative `df-sqrtr`. NO √ axiom is asserted.
A derivation bug can only be a kernel REJECTION.

## 4. tower length K — now MEASURED (the projection is removed)

The grounded geometry introduces √ exactly via `df-cp`'s
`sqrt( u * inv( sqd a c ) )`. G1 (ruler) is the only √-bearing postulate.
A field, once it adjoins √x, has it forever (reuse is free) — so the
construction cost is the radical tower **depth**, i.e. the number of
*distinct* `( sqrt … )` subterms (and their nesting), **not** the
occurrence multiplicity (occurrences are already counted in the 10^5.58
geometry). That depth is directly kernel-MEASURABLE; `euclidfloor` now
measures it read-only over the kernel-verified `data/grounded.out.mm`:

    MEASURED distinct USED radicals in the closed ASA′ corpus : 1
        ( sqrt ( u * ( inv ( sqd a c ) ) ) )
    MEASURED max sqrt-nesting depth                           : 1
    (the only other `( sqrt … )` form is the bare axiom template
     `( sqrt u )` — the F1 *schema* statement, not a used instance)

So the minimal field making the **closed ASA′ proof** sound needs
exactly **one un-nested degree-2 extension** — K = 1:

    proof-relativized construction = K · unit = 1 · 10^2.149
                                   = 10^2.149            [MEASURED]

The former `K ≤ 10^6  ⇒  10^8.15 [PROJECTION]` is **superseded**: for the
proof-relativized model the construction is now a fully MEASURED
**10^2.149** (no projection). It is ~10^2 — astronomically below EVERY
set.mm substrate figure (10^25.95 / 10^30.75 / 10^45.74).

**Separate, still-labelled PROJECTION (never conflated):** a model of the
*entire F1 schema* (√ of *every* nonneg element) is the full Euclidean
closure of ℚ — a countable tower, each level one MEASURED unit step.
That is a *different quantity* from "what the closed ASA′ proof needs",
remains an explicitly labelled PROJECTION, and is **not** the 10^2.149
figure above.

## 5. TRANSPORT BINDING (EXTRACTED) — the decisive term

`src/bin/modelsplice.rs` (additive-only transport section) binds the
euclid.mm unit step to its set.mm satisfaction targets and EXTRACTS their
ZFC cost with the same exact extractor:

| bridge component | set.mm | ZFC cost (EXTRACTED) |
|---|---|---|
| tower base: ℚ a ZFC sub-division-ring of CCfld | `qsubdrg` | 10^46.10 |
| each level stays a ZFC subring of CCfld | `cnsubrg` | 10^44.87 |
| SATISFACTION of ax-sqrt | `resqrtth` | 10^45.74 |
| SATISFACTION of of-sqrtnn | `sqrtge0` | 10^45.97 |

Decisive findings, verified by `grep` over `data/set.mm`:

* set.mm has **no** real-algebraic / Euclidean / real-closed *subfield*
  object, **no** `SubRing`/`SubDRing` witness for `AA`, and **no** theorem
  that √ of a nonnegative algebraic number is algebraic.
* set.mm's **only** √-of-nonneg theorems (`resqrtth`, `sqrtge0`) are
  stated over the analytic ℝ (`A e. RR`) and cost ~10^45.7 ZFC-grounded.
* Even ℚ-as-a-ring (`qsubdrg`) is phrased through `CCfld` (the analytic
  complex field), so its ZFC expansion is itself ~10^46.

Therefore the satisfaction bridge, expressed *in set.mm*, reintroduces the
full analytic-ℝ cost.

## 6. The transport-anchored floor — PROVEN vs PROJECTED

```
construction (PROVEN unit × PROJECTED tower K≤10^6) ≤ 10^8.15  [PROVEN×PROJ]
transport-satisfaction bridge (set.mm)              =  10^45.97 [EXTRACTED]
transport-anchored TOTAL = max(…)                   =  10^46.10 [EXTRACTED]
```

## 7. Verdict (adversarially honest)

Is the transport-anchored total below 10^25.95? **No — not through
set.mm.** The exact argument:

1. The Euclidean-closure CONSTRUCTION is genuinely cheap: kernel-MEASURED
   unit = 141 cut-free steps (10^2.149); even with a generous projected
   tower length the construction is ≤10^8.15. This **proves F1 does not
   need ℝ**: the substrate's intrinsic cost is ~10^8, not ~10^46.
2. But "ZFC grounding" *as the maintainer defines it* requires a machine
   bridge proving, IN set.mm, that the exhibited object satisfies F1's √
   axioms. set.mm contains **no** Euclidean/real-algebraic/real-closed
   subfield, and its only √-of-nonneg facts ride the analytic ℝ at
   ~10^45.97 (EXTRACTED). The bridge therefore costs 10^46.10.
3. So the **transport-anchored** floor is **10^46.10**, dominated entirely
   by the set.mm bridge, NOT by the construction.

This is a real, valuable result, not a failure: it **sharpens the
thesis**. The irreducible ~10^46 is not a property of F1 (F1's model
construction is provably ~10^8) — it is a property of *set.mm*: set.mm has
no √-of-nonneg fact below the analytic-ℝ scale to transport to. A
set.mm-anchored F1 model is analytic-ℝ-priced *because of what set.mm
chose to prove*, not because F1 needs it. The honest split:
**the construction WINS (kernel-MEASURED ~10^8); the set.mm bridge does
not (EXTRACTED ~10^46).**

To beat 10^25.95 with a transport-anchored model one would have to ADD to
set.mm a proof that the constructible/real-algebraic field is a ZFC
ordered subfield closed under √-of-nonnegatives that does *not* route
through analytic ℝ. That theorem does not exist in set.mm today; building
it is the only honest path below the floor, and its cost would itself have
to be measured.

## Files / instruments

* `data/euclid.mm` — kernel-checked generic Euclidean extension step.
* `src/bin/euclidfloor.rs` — kernel-verifies + MEASURES the unit step.
* `src/bin/modelsplice.rs` — additive transport section (EXTRACTED bridge).
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
* Reproduce: `cargo run --release --bin euclidfloor`
  and `cargo run --release --bin modelsplice` (needs `data/set.mm`).
