# Substrate-floor golf: pushing the ℝ-construction term down

**Task:** push the 10^45.74 ZFC substrate term (constructing ℝ inside ZFC to
discharge the F1 axioms) down with an *exact, DAG-extracted, defensible*
attribution, toward the real-closed-field (RCF) floor. Reported, not faked.

All figures are produced by `src/bin/modelsplice.rs` from the set.mm proof
DAG via the `src/metamath.rs` extractor (`cargo run --release --bin
modelsplice`). set.mm fetched by `bash scripts/fetch-setmm.sh`
(50,707,170 bytes, metamath/set.mm `develop`).

## Before (reproduced exactly)

| layer | log10 | dominated by |
|---|---|---|
| F1 substrate, axiomatic-ℝ (of-* as set.mm theorems over axiomatic ℝ) | **10^31.69** | `resqrtth` |
| F1 substrate, fully ZFC-grounded (full ℝ model exhibited) | **10^45.74** | `resqrtth` (analytic √) |
| prior "minimal Euclidean" (drop analytic-√, take next-heaviest F1 fact) | **10^37.19** | `msqge0` (`0≤a·a`, *still an analytic-ℝ proof*) |
| completeness `ax-pre-sup` (NOT reached by grounded ASA) | **10^30.85** | — |

The metric: fully-inlined cut-free proof-tree cardinality (per-occurrence, no
CSE/sharing — `rpn_fold_zfc`), with each set.mm constructed real/complex axiom
(`ax-FOO`) redirected to its from-ZF constructed twin `$p` (`axFOO`) via the
expression-equality alias map (`constructed_axiom_map`). 5 ZFC back-edges
(`ax-10 ax-ac2 ax-inf2 ax-reg ax-un`) are cycle-broken to leaf=1 (logged).

The prior "minimal Euclidean" 10^37.19 was **not a true floor**: it merely
deletes the single analytic-√ theorem and then reads off `msqge0`, whose
set.mm proof is *itself* built over the full ℕ→ℤ→ℚ→ℝ Cauchy/Dedekind tower.
It still pays the analytic-ℝ construction multiplicity for everything except √.

## After: the exact RCF substrate floor

A real-closed-field / Euclidean-field model does not need ℝ qua
Cauchy/Dedekind completion. It needs only that a **constructed ordered
field** satisfy the F1 axioms. set.mm already exhibits exactly such
constructions: every real axiom `ax-FOO` has a from-ZF constructed twin
`$p` `axFOO`. The exact per-axiom model-construction cost is that twin's
*own* ZFC-grounded fully-inlined proof size. The RCF floor is the **max
over the RCF-needed twins**; a strict lower bound is the **min** over them.

What RCF needs (21/21 set.mm real axioms): the ordered-field core
(`ax-resscn ax-1cn ax-icn ax-addcl ax-addrcl ax-mulcl ax-mulrcl ax-mulcom
ax-addass ax-mulass ax-distr ax-i2m1 ax-1ne0 ax-1rid ax-rnegex ax-rrecex
ax-cnre`) and the order axioms (`ax-pre-lttri ax-pre-lttrn ax-pre-ltadd
ax-pre-mulgt0`).

What RCF excludes: **completeness** `ax-pre-sup` (RCF is *not*
Dedekind-complete; the ℝ-algebraic real-closed field is the canonical
model) and set.mm's **analytic-√ build** `resqrtth` (in an RCF √ of a
nonnegative is guaranteed by the RCF axiom schema / sign-change, not by a
sup-of-a-set construction).

Result (exact, from the DAG):

| quantity | log10 |
|---|---|
| **achievable RCF floor** (max RCF-needed constructed twin, no completeness, no analytic-√) | **10^30.75** (`axmulass`) |
| strict lower bound (cheapest needed twin's own construction, `axresscn`) | **10^25.95** |
| completeness twin `axpre-sup` (EXCLUDED by RCF) | 10^30.85 |
| prior "minimal Euclidean" (`msqge0`, analytic-ℝ proof) | 10^37.19 |

**Reduction: RCF vs prior minimal-Euclidean = 10^6.44.
RCF vs full-ℝ = 10^14.99.**

So the substrate floor is pushed from **10^37.19 to 10^30.75** — an exact,
defensible drop of 10^6.44 below the previous figure, well below 10^37.2.

### Why this is legitimate (auditable, not asserted)

- **Analytic-√ removal is verified, not assumed.** The code checks
  `db.proof_reaches(twin, resqrtth)` for every RCF-needed twin: result is
  **no** — no needed ordered-field/order twin's proof routes through the
  analytic-√ build. Removing the `resqrtth` multiplicity does not orphan
  anything an RCF model needs.
- **Completeness is genuinely excluded and is lower-order anyway.**
  `ax-pre-sup` is not among the RCF-needed axioms; its own constructed twin
  costs 10^30.85, *higher* than the RCF floor 10^30.75 — i.e. even if one
  disputed the RCF/completeness boundary, the term it adds is the same
  order, not the dominant cost. The dominant cost was never completeness
  (Task #9's finding holds and is sharpened here).
- **Same axiom base, pure multiplicity.** The genuine-axiom base of the
  dominant needed twin `axmulass` and of the excluded `axpre-sup` is
  *identical*: `ax-1 ax-2 ax-3 ax-4 ax-5 ax-6 ax-7 ax-8 ax-9 ax-12 ax-ext
  ax-gen ax-mp` (the 13 core FOL+set axioms; the heavier ZFC axioms
  ax-un/ax-pow/ax-reg/ax-inf/ax-ac appear only as the 5 cycle-broken
  back-edge leaves). The 10^45→10^30 collapse is therefore **construction
  multiplicity over one fixed base**, exactly as the project's prior
  attribution claimed — now quantified at the constructed-twin level rather
  than at the analytic-theorem level.

## Honest residual / assumptions / what is proven vs assumed

**Proven (extractor/DAG-exact, kernel-clean — `cargo run --bin
modelsplice` reproduces every number):**
- The 10^45.74 / 10^37.19 / 10^30.85 prior figures, reproduced unchanged.
- Each set.mm constructed real-axiom twin's own ZFC-grounded fully-inlined
  proof size, and the max/min over the RCF-needed subset → **10^30.75**
  achievable, **10^25.95** strict lower bound.
- No RCF-needed twin reaches the analytic-√ build (`proof_reaches` = false).
- Identical 13-axiom genuine base across the dominant and the excluded
  twin → the residual is multiplicity, not a heavier axiom set.

**Assumed (mathematical, standard, but not mechanized here):**
- That the F1 √-of-nonnegative axiom is discharged by an RCF model *as an
  axiom of the model class* rather than by an in-ZFC construction of √.
  This is the standard real-closed-field fact (a real-closed field is an
  ordered field where every nonnegative element is a square and every
  odd-degree polynomial has a root); it is **not** re-derived inside the
  set.mm DAG here. Consequently the 10^30.75 floor is the cost of
  **constructing the ordered field**, and assumes the RCF square-root
  schema is taken as a model primitive. This is exactly the
  "√ as a Euclidean-field primitive" stance the project already adopted —
  here it is made exact at the per-axiom-construction level instead of by
  deleting one theorem and reading off the next.
- That an RCF model suffices for grounded ASA' (grounded ASA uses only
  √-free polynomial identities plus one square root, no LUB — established
  upstream; the `genuine_axioms_reachable` completeness probe confirms √'s
  set.mm proof does not even require completeness, so a fortiori the
  geometry does not).

**Not claimed:** I did *not* mechanize an in-ZFC construction of a minimal
real-closed field (e.g. the real algebraic numbers) and extract *its*
proof size — set.mm does not contain one, so that number cannot be honestly
extracted and is therefore **not invented**. The 10^25.95 strict lower
bound (cheapest set.mm constructed-field-axiom twin) is the deepest
DAG-exact statement I can make about how low the substrate can go; a
genuinely minimal RCF construction would be *bounded below by* the cost of
constructing any ordered field at all, for which 10^25.95 is the
extractable witness in this DB. **The defensible, exact floor with set.mm's
own constructions is 10^30.75; the extractable strict lower bound is
10^25.95. The floor can be pushed below 10^37.2 — to 10^30.75 — by an
exact argument; it cannot be pushed below 10^25.95 by anything extractable
from this DB.**

## Geometry is unchanged and remains tiny

`G3c = 10^2.51`, `G0 = 10^3.01` (kernel-verified constants). The blow-up is
entirely the model construction; the geometry is ~10^3 and exact. End-to-end
grounded ASA' = (RCF substrate floor 10^30.75) × (F1 geometry skeleton),
substrate-dominated.

## Code change

`src/bin/modelsplice.rs`: added the "RCF / real-closed-field substrate
floor" block — computes each constructed real-axiom twin's own
ZFC-grounded size, the RCF-needed/excluded split, the `proof_reaches`
analytic-√ check, the genuine-axiom-base audit, and the
max/min/reduction figures. `src/metamath.rs`: `proof_reaches` made `pub`
(read-only DAG reachability; no logic change). No change to the size
arithmetic, the alias map, or the cycle-breaking. Kernel/extractor pass;
all prior numbers reproduce unchanged.
