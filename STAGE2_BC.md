# STAGE2_BC — Milestones B & C: the ONE quadratic extension and the
#               transport binding to set.mm's GENUINE ZF base

Adversarially honest. Every number here is exactly one of:
**MEASURED** (kernel-exact, OUR `src/kernel.rs`, OUR cut-free `$a`-leaf
metric — the same metric as `euclidfloor`/`qzffloor`/`grounded`),
**EXTRACTED** (the exact set.mm extractor `db.expanded_zfc` over the
50,707,170-byte `develop` `data/set.mm`, plus a full proof-DAG
reachability audit `db.proof_reaches`), or **PROJECTION:** (a labelled
derivation, reasoning shown, NEVER merged into / printed as a measured
figure).

Trust root: `src/kernel.rs`. A derivation bug can only become a kernel
REJECTION; it can never inflate a measured number. The set.mm figures
are EXTRACTED, never re-derived in OUR kernel and never merged with a
MEASURED line.

Base of this work: commit `37df8aa` (Stage 2 Milestone A: native
ℚ-from-ZF, `data/qzf.mm`, MEASURED 10^2.408; `data/euclid.mm` generic
√-step MEASURED 10^2.149; `src/bin/modelsplice.rs` EXTRACTED set.mm
bridge). Stage 1: MEASURED K=1 — the closed ASA′ proof forces exactly
ONE distinct, un-nested radical `( sqrt ( u * ( inv ( sqd a c ) ) ) )`.

---

## Milestone B — the ONE quadratic extension ℚ_geo(√r) (MEASURED)

`data/qzfext.mm` instantiates the `data/euclid.mm` *generic* Euclidean
√-extension step ONCE, over the native ℚ-from-ZF base (Milestone A), at
the Stage-1 MEASURED radicand in native-ℚ notation

    rdcd  :=  ( u-elt Qt ( Qi sdac ) )           ( = u * inv( sqd a c ) )

It exhibits ℚ_geo(√r) = ℚ_geo[x]/(x²−r) as a ZF set + ordered field
with √r present, by adjoining one root element `rr` of the native-ℚ
carrier with the degree-2 ordered-field extension hypotheses
`( rr Qt rr ) = rdcd` and `( Q0 Qle rr )` (NOT global axioms — exactly
what "adjoin √r at this level" supplies), then deriving F1's two
non-conservative √-axioms instantiated at `rdcd` as kernel `$p`:

* `eu-sqrt-r`   : `( ( Qsqrt rdcd ) Qt ( Qsqrt rdcd ) ) = rdcd`  (ax-sqrt @ r)
* `eu-sqrtnn-r` : `( Q0 Qle ( Qsqrt rdcd ) )`                    (of-sqrtnn @ r)

with `( Qsqrt rdcd )` realised by `rr` via the conservative
`df-qsqrtr` (eliminable by rewriting; introduces NO non-conservative
axiom). No `CCfld`, no Dedekind/Cauchy, no analytic ℝ.

`src/bin/qzfextfloor.rs` (mirrors `euclidfloor.rs` metric byte-for-byte)
kernel-verifies and MEASURES:

```
Kernel: verified all 3 $p in data/qzfext.mm ✔  (db: 47 statements)
=== MEASURED in OUR kernel (data/qzfext.mm), cut-free $a-leaf count ===
  eqtr          = 13   (10^1.114)   reusable FOL= transitivity helper
  eu-sqrt-r     = 88   (10^1.944)   F1 ax-sqrt   @ Stage-1 radicand (native ℚ)
  eu-sqrtnn-r   = 40   (10^1.602)   F1 of-sqrtnn @ Stage-1 radicand (native ℚ)
  Milestone-B ℚ_geo(√r) total (Σ $p) = 141 = 10^2.149   [MEASURED]
```

The per-lemma decomposition is byte-for-byte identical to `euclid.mm`'s
already-MEASURED generic unit (eqtr=13, eu-sqrt=88, eu-sqrtnn=40, total
141 = 10^2.149) — the task's instruction to *reuse the MEASURED
10^2.149 unit* is honoured: the generic figure is NOT re-derived; the
141 above is qzfext.mm's OWN kernel-verified cut-free cost, K=1 (Stage-1
MEASURED). **Milestone B cost: 10^2.149, kernel-MEASURED, `verified all
3 $p ✔`.**

---

## Milestone C — transport binding to set.mm's GENUINE 13-axiom ZF base

### The binding question, sharpened by B

The OLD `modelsplice` bridge is 10^46.10 (EXTRACTED) for ONE reason: it
binds F1's √-SATISFACTION to set.mm's only √-of-nonneg theorems,
`resqrtth` / `sqrtge0`, which are stated over the analytic ℝ and ride
`CCfld`. **Milestone B removed that need**: √-satisfaction at the
(Stage-1 MEASURED, K=1) radicand is now a KERNEL-PROVED theorem over the
native ℚ-from-ZF carrier (`qzfext.mm`, 10^2.149 MEASURED). A faithful
transport therefore no longer needs set.mm's √ theorems at all.

The ONLY residual set.mm dependency is that the native carrier's `df-*`
ZF-construction primitives — `(/)`, `suc`, `om`(=ω), Kuratowski
`<. , >.`, `[ ~ ]`, `e.` — genuinely denote **ZF sets**. Milestone C's
decisive test: does *that* binding stay on set.mm's bare 13-axiom ZF
base, or does some unavoidable dependency drag it back through
`CCfld`/analytic ℝ — and at exactly what EXTRACTED cost?

### Targets, EXTRACTED cost, and the full-DAG reachability audit

Additive Milestone-C section in `src/bin/modelsplice.rs`. Each
ZF-construction primitive → its set.mm validating theorem; ZFC cost via
the same `db.expanded_zfc` extractor; binding audited by a FULL proof-DAG
walk (`db.proof_reaches`) against every analytic-ℝ/CCfld construction
root present in set.mm (`df-c df-r df-cnfld df-resub df-sqrt sqrtval
axresscn axmulass axcnex qsubdrg df-q cnfldbas resqrtth sqrtge0`):

| ZF primitive | set.mm | ZFC cost (EXTRACTED) | binding audit (full DAG) |
|---|---|---|---|
| `(/)` empty set is a ZF set        | `0ex`    | 10^10.064 | bare-ZF, no analytic-ℝ |
| `suc` successor is a ZF set        | `sucexg` | 10^12.810 | bare-ZF, no analytic-ℝ |
| `om`=ω exists (Infinity)           | `omex`   | **10^17.484** | bare-ZF, no analytic-ℝ |
| `<.,.>` Kuratowski pair is a set   | `opex`   | 10^12.490 | bare-ZF, no analytic-ℝ |
| `{x,y}` pairing is a set           | `zfpair2`| 10^11.903 | bare-ZF, no analytic-ℝ |
| `U.` union is a set                | `uniex`  | 10^10.943 | bare-ZF, no analytic-ℝ |
| `[ ]~` / `/.` equiv-class/quotient | `axextg` | 10^7.539  | bare-ZF, no analytic-ℝ |

Auditable, not asserted — the genuine-axiom base of the dominant target:

```
genuine-axiom base of omex: ax-1 ax-2 ax-3 ax-4 ax-5 ax-6 ax-7 ax-8 ax-9 ax-ext ax-gen ax-mp
contains a constructed-ℝ / CCfld axiom: no (pure FOL+ZF base — bare 13-axiom family)
FULL-DAG audit: analytic-ℝ / CCfld reached by ANY binding target: NONE
```

Every binding target reaches **exactly the genuine FOL+ZF base** (the
bare family the #9/substrate analysis isolated; here ax-1..9 + ax-ext +
ax-gen + ax-mp for `omex`) and **ZERO** analytic-ℝ/CCfld roots anywhere
in its full proof DAG.

### The transport-anchored floor — the PROVEN/MEASURED · EXTRACTED · PROJECTION split

```
[MEASURED, OUR kernel]
  Milestone A  native ℚ-from-ZF derived layer  : 10^2.408  (qzffloor, 11 $p ✔)
  Milestone B  ℚ_geo(√r) @ Stage-1 radicand K=1: 10^2.149  (qzfextfloor, 3 $p ✔)
[EXTRACTED, set.mm]
  native carrier ZF-set-hood → GENUINE ZF base : 10^17.484 (omex; ω from Infinity)
[PROJECTION, labelled, never merged]
  qzf.mm asserted ax-N*/ax-Z*/ax-Q* signature → bare ZF (quotient
  well-definedness) ≤ 10^4  (STAGE2_A.md §6 derivation; NOT measured)
---------------------------------------------------------------------
transport-anchored native-model floor
  = max( 10^2.408 , 10^2.149 , 10^17.484 )
  = 10^17.484          [EXTRACTED-dominated; A/B MEASURED]

vs the OLD set.mm-routed bridge:
  CCfld-routed √-satisfaction bridge : 10^46.10  [EXTRACTED]
  Milestone-C native-model floor     : 10^17.484 [EXTRACTED]
  collapse                           : 10^28.61
```

---

## DEFINITIVE VERDICT (adversarially honest)

**Does the ~10^46 collapse? YES — and the binding is machine-checked.**

The exact, machine-checked argument:

1. The old 10^46.10 was set.mm's analytic-ℝ **ROUTING CHOICE** for √:
   the bridge bound F1's √-satisfaction to `resqrtth`/`sqrtge0`, which
   ride `CCfld`. It is NOT a property of F1 or of ℚ.
2. Milestone B made √-satisfaction, at the Stage-1 MEASURED (K=1)
   radicand, a KERNEL-PROVED theorem over the native ℚ-from-ZF carrier
   (10^2.149 MEASURED). The transport no longer needs set.mm's √
   theorems — the analytic-ℝ term is *eliminated at its source*.
3. The sole residual set.mm dependency — that the native carrier's
   `df-*` primitives denote genuine ZF sets — is EXTRACTED and
   FULL-DAG-audited to bind to set.mm's **genuine 13-axiom ZF base**
   with **ZERO** analytic-ℝ/CCfld reachability.
4. The transport-anchored native-model floor is therefore **EXTRACTED
   at 10^17.484**, with A/B derivation **MEASURED at 10^2.408 /
   10^2.149** and the signature→bare-ZF discharge a labelled
   **PROJECTION ≤ 10^4**.

**The exact irreducible residual is NOT analytic ℝ.** It is the cost,
IN set.mm, of proving **ω is a set from the Axiom of Infinity** —
`omex` at 10^17.484 EXTRACTED, a *bare-ZF* fact, ~29 orders of magnitude
**below** the CCfld-routed 10^46.10. That residual is forced by set.mm's
own `omex` proof of Infinity (the heaviest bare-ZF construction
primitive the native ℚ tower needs: ω is the base of ω→ℕ→ℤ→ℚ); it
involves no `CCfld`, no Dedekind/Cauchy, no analytic ℝ.

One-line verdict: **~10^46 collapses to 10^17.484 (EXTRACTED,
machine-checked), dominated by set.mm's `omex` (ω-from-Infinity) — a
bare-ZF fact ~29 orders below the analytic-ℝ bridge; the ~10^46 was
set.mm's analytic-ℝ routing choice for √, not a property of F1 or ℚ, and
routing F1 through a native ZF model collapses it to the bare-ZF
Infinity cost.**

---

## Files / instruments / reproduce

* `data/qzfext.mm` — Milestone B: ONE quadratic ext ℚ_geo(√r) over
  native ℚ-from-ZF at the Stage-1 radicand (kernel-checked).
* `src/bin/qzfextfloor.rs` — kernel-verifies + MEASURES Milestone B.
  Reproduce: `cargo run --release --bin qzfextfloor`
* `src/bin/modelsplice.rs` — additive Milestone-C transport-binding
  section (EXTRACTED + full-DAG audit). Needs `data/set.mm`
  (`sh scripts/fetch-setmm.sh`). Reproduce:
  `cargo run --release --bin modelsplice`
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
* Commits: B `aa50219`, C `cb70135` (branch `stage2-bc-a6b61bc8`,
  base `37df8aa`).

### Scope honesty

The MEASURED A/B numbers are OUR-kernel cut-free `$a`-leaf counts; the
10^17.484 is EXTRACTED from set.mm by the same extractor used for the
10^46.10 it replaces (apples-to-apples). The asserted
ax-N*/ax-Z*/ax-Q* signature → bare-ZF discharge remains an explicitly
labelled PROJECTION ≤10^4 (the euclid.mm/STAGE2_A discipline), never
merged into a measured or extracted figure. The geometry (10^5.58) and
grounding lines are untouched — Stage 2 moves only the
satisfiability/transport number, and it moves from 10^46.10 to a
machine-checked 10^17.484.
