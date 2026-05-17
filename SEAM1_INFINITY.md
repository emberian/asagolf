# SEAM 1 — Is `omex`/Infinity ESSENTIAL to grounding the closed ASA′
#          proof, or an ARTIFACT of constructing ℚ via von-Neumann ω?

Adversarially honest. Every number here is exactly one of:
**MEASURED** (kernel-exact, OUR `src/kernel.rs`, OUR cut-free `$a`-leaf
metric — the metric of `euclidfloor`/`qzffloor`/`qzfextfloor`/`grounded`),
**EXTRACTED** (the exact set.mm extractor `db.expanded_zfc` + full
proof-DAG reachability `db.proof_reaches`, quoted **verbatim** from
Milestone C / `STAGE2_BC.md` — *not* recomputed here), or
**PROJECTION:** (a labelled derivation, reasoning shown, NEVER merged
into a measured/extracted figure).

Trust root: `src/kernel.rs`. The new instrument `src/bin/seam1floor.rs`
re-verifies `data/qzf.mm` (11 `$p` ✔) and `data/qzfext.mm` (3 `$p` ✔) in
OUR sound kernel before measuring anything. A derivation bug can only
DROP a symbol from a reachability set (making a primitive *look*
incidental); the report is therefore built to be falsifiable — it prints
the full reached-symbol set, runs positive controls, and an adversarial
deep check (below). Read-only consumed: `data/grounded.mm`,
`data/qzf.mm`, `data/qzfext.mm`.

---

## 1. The question, made precise

Milestone C (machine-checked) bound the native ℚ-from-ZF carrier's
ZF-set-hood to set.mm's **genuine 13-axiom ZF base** and found the floor
**10^17.484**, dominated by `omex` — set.mm's cost of proving *ω is a set
from the Axiom of Infinity*. Milestone C bound **all seven**
ZF-construction primitives because `qzf.mm` constructs ℚ via the full
von-Neumann tower `ω → ℕ → ℤ → ℚ`.

But Stage 1 MEASURED **K = 1**: the closed ASA′ proof forces exactly
**one** distinct, un-nested radical `( sqrt ( u * ( inv ( sqd a c ) ) ) )`
— no induction, no ℕ visible in the geometry content. So the sharp
question is:

> Of the seven Milestone-C ZF primitives
> (`0ex/sucexg/omex/opex/zfpair2/uniex/axextg`), which are **essential to
> the *closed proof's* model**, and which are merely **incidental to the
> *general* ℚ construction**? In particular: is `omex`/Infinity essential,
> or an artifact of building ℚ through von-Neumann ω?

---

## 2. Method (the same extractor/DAG-reachability discipline as
##    `modelsplice`, applied to the closed model's own files)

`modelsplice` decides set.mm bindings by proof-DAG reachability
(`db.proof_reaches`) against named roots. `seam1floor` applies the exact
same idea **inside the closed model**, in OUR kernel:

* **Roots the closed proof actually consumes.**
  - Milestone B: `eu-sqrt-r`, `eu-sqrtnn-r` — F1's two non-conservative
    √-axioms discharged at the Stage-1 (K=1) radicand. The *only* √ the
    closed proof forces.
  - Milestone A: `Q0addlid Q1mullid Qaddlinv Qmullinv Qleaddl` — the ℚ
    ordered-field consequences the F1 geometry consumes.
* **Closure.** Transitive closure of those roots over the kernel
  statement DAG: proof-step references **and** definitional unfolding —
  every `df-*` whose defined head symbol enters any reached expression is
  itself unfolded (so a primitive hidden one `df-` deeper is still
  caught).
* **Verdict.** A ZF primitive is **ESSENTIAL to the closed proof's
  model** iff one of its carrier symbols occurs in that closure;
  **INCIDENTAL to the general ℚ construction** iff it occurs only in
  `qzf.mm`'s general signature/scaffolding and never in the closure.
* **Falsifiability.** Positive controls (`suc`, `(/)` must be reached —
  `df-n1 = ( suc (/) )`, `df-n0 = (/)`); the full reached ZF/ctor symbol
  set is printed; an adversarial deep check enumerates which arithmetic
  operators enter the closure.

Reproduce: `cargo run --release --bin seam1floor`.

---

## 3. Per-primitive essential / incidental split (MEASURED in OUR kernel;
##    set.mm ZFC costs EXTRACTED, quoted verbatim from Milestone C)

`seam1floor` (kernel-verified `qzf.mm` 11 `$p` ✔, `qzfext.mm` 3 `$p` ✔):

closed-model reached ZF/ctor symbols (df-* unfolded):
`(/) <. >. N0 N1 Q0 Q1 Z0 Z1 [ ] suc ~`  — **`om` absent**.

| ZF primitive | set.mm | ZFC cost (EXTRACTED, M-C) | verdict for the CLOSED ASA′ proof |
|---|---|---|---|
| `(/)` empty set        | `0ex`    | 10^10.064 | **ESSENTIAL** (`(/)` reached: `df-n0`) |
| `suc` successor        | `sucexg` | 10^12.810 | **ESSENTIAL** (`suc` reached: `df-n1`) |
| `om`=ω (**Infinity**)  | `omex`   | **10^17.484** | **INCIDENTAL** — `om` NOT in closed-model closure |
| `<.,.>` Kuratowski pair| `opex`   | 10^12.490 | **ESSENTIAL** (`<. >.` reached: `df-z*/df-q*`) |
| `{x,y}` pairing        | `zfpair2`| 10^11.903 | **ESSENTIAL** (`<. >.` reached) |
| `U.` union             | `uniex`  | 10^10.943 | **ESSENTIAL** (`[ ~` reached: classes) |
| `[ ]~` equiv-class     | `axextg` | 10^7.539  | **ESSENTIAL** (`[ ~ ]` reached: `df-z*/df-q*`) |

**Adversarial cross-check** (machine output): `qzf.mm` statements
mentioning `om` = **1** (the bare signature declaration `tom $a term om
$.`); reached from the closed-proof roots = **NONE**. Positive controls:
`suc` reached = true, `(/)` reached = true (method is not vacuously
dropping symbols).

**Adversarial DEEP check** (the heart of the honest residual). `om`
unreached *syntactically* is necessary but not sufficient — if the
closed roots used the ℕ/ℤ recursion `( x Np y )`, `( x Zt y )` over
*variables*, discharging that to bare ZF would still need ω as the
completed recursion domain. Machine output — operators in the closed
closure:

```
Np  false   Nt  false   Nle false   Zp  false   Zt  false
Zle false   Zm  false   Qp  true    Qt  true    Qle true
Qi  true    Qm  true
```

**The closed proof reaches ZERO ℕ-layer and ZERO ℤ-layer recursion
operators.** It reaches only ℚ-layer operators — and those enter solely
as the abstract `ax-Q*` **signature axioms over term variables**, whose
discharge to bare ZF is the *already-separated* labelled
**PROJECTION ≤ 10^4** (`STAGE2_A.md` §6), never an EXTRACTED ZF-set-hood
line.

### Why (the exact mechanism — auditable, not asserted)

The closed proof's ℚ constants unfold, through `df-q*/df-z*/df-n*`
(all kernel `$a` definitions, eliminable by rewriting), to:

```
Q0 = [ <. Z0 , Z1 >. ~ Z0 ]      Q1 = [ <. Z1 , Z1 >. ~ Z0 ]
Z0 = [ <. N0 , N0 >. ~ N0 ]      Z1 = [ <. N1 , N0 >. ~ N0 ]
N0 = (/)                          N1 = ( suc (/) )
```

`suc` is applied **exactly once** to `(/)`; it is never iterated, and
`om`/ω never appears. Every ℚ element the closed proof names reduces to
a pair-class **over the two finite ordinals ∅ and {∅}**. K = 1 (Stage-1
MEASURED: one radical, no induction, no ℕ in the geometry) is *precisely*
why the von-Neumann recursion is never invoked at a variable, hence why ω
is never forced.

A further structural fact (read-only audit of the closed chain): there
are **no `A.`/`E.` quantifiers** over field elements anywhere in
`grounded.mm` (the `A.` constant is declared but used in **0**
statements), `qzf.mm`, or `qzfext.mm`. The entire closed ASA′ model
obligation is a **quantifier-free Horn/equational theory over finitely
many named ℚ terms** plus one degree-2 √-adjunction — it never needs ℚ,
ℤ, or ℕ as a *completed* (infinite) set.

---

## 4. The SEAM-1 floor (PROVEN/MEASURED · EXTRACTED · PROJECTION split)

```
[MEASURED, OUR kernel — NOT recomputed here]
  Milestone A  native ℚ-from-ZF derived layer : 10^2.408  (qzffloor,  11 $p ✔)
  Milestone B  ℚ_geo(√r) @ Stage-1 radicand   : 10^2.149  (qzfextfloor, 3 $p ✔)
[EXTRACTED, set.mm — quoted verbatim from Milestone C, NOT recomputed]
  closed-model ZF-set-hood, ESSENTIAL primitives only
    dominant = sucexg (successor is a set)     : 10^12.810
  ruled INCIDENTAL to the closed proof's model:
    omex (ω from Infinity)  10^17.484  — `om` not in closed closure
[PROJECTION, labelled, never merged]
  qzf.mm asserted ax-N*/ax-Z*/ax-Q* signature → bare ZF (quotient /
  recursion well-definedness) ≤ 10^4  (STAGE2_A.md §6 derivation)
---------------------------------------------------------------------
SEAM-1 closed-model floor
  = max( A 10^2.408 , B 10^2.149 , essential-ZF 10^12.810 )
  = 10^12.810          [EXTRACTED-dominated; A/B MEASURED]

vs Milestone C (ALL 7 primitives — the *general* ℚ construction):
  Milestone-C floor (omex, all-7)  : 10^17.484  [EXTRACTED]
  SEAM-1 closed-model floor        : 10^12.810  [EXTRACTED]
  drop vs Infinity-bound floor     : 10^4.674
  OLD CCfld-routed √ bridge        : 10^46.10   [EXTRACTED]
```

---

## 5. VERDICT (adversarially honest — the precise, non-overreaching claim)

**`omex`/Infinity is INCIDENTAL to the closed ASA′ proof's model — it is
an ARTIFACT of constructing ℚ via the von-Neumann-ω tower, not a property
the closed proof forces.**

This is the **MEASURED, machine-checked** core, and it is exact:

1. The closed proof's two model roots (B's √-at-K=1, A's ℚ
   ordered-field consequences) have, in OUR kernel, a model closure that
   reaches `(/) suc <. >. [ ~ ]` and the finite ordinal constants
   `N0/N1/Z0/Z1/Q0/Q1` — and **provably never reaches `om`**.
2. The closure reaches **zero** ℕ-/ℤ-recursion operators; the only `om`
   occurrence in `qzf.mm` is the unused signature declaration.
3. The closed obligation is quantifier-free over finitely many named
   terms; the ℚ constants reduce to pair-classes over `∅` and `{∅}`
   with `suc` applied once. Stage-1 K = 1 is the structural reason.
4. Therefore the ZF-set-hood floor of the *closed proof's* model is
   **EXTRACTED at 10^12.810** (`sucexg` — "the successor of a set is a
   set"), **10^4.674 below** the Milestone-C `omex` floor 10^17.484, and
   **~10^33 below** the old CCfld-routed √ bridge 10^46.10. The Axiom of
   Infinity is **not** the irreducible residual for this proof.

### The HONEST OPEN RESIDUAL (explicitly not claimed as closed)

The result above is a statement about the **current** native model
(`qzf.mm`/`qzfext.mm` as written): its ZF-set-hood closure does not reach
`om`. That makes `omex` incidental and lowers the *extracted ZF-set-hood
line* to `sucexg` 10^12.810. What is **NOT** yet done — and is the honest
open sub-question — is a *standalone* exhibited carrier:

* **Sub-question 2, partially answered, not fully discharged.** The
  evidence that a carrier avoiding `omex` *can* model the closed proof is
  strong and machine-checked at the symbol/DAG level (finite-ordinal
  pair-classes; quantifier-free; zero recursion ops; K = 1). The natural
  witness is the **hereditarily-finite sets `V_ω`** (or even a bounded
  `V_n`): ∅ and `suc ∅` and finitely many Kuratowski-pair classes of
  them are all hereditarily finite, and HF-set existence routes through
  `0ex/sucexg/opex/zfpair2/uniex/axextg` (the six ESSENTIAL primitives,
  dominant `sucexg` 10^12.810) — **not** through `omex` (`ax-inf`/`omex`
  asserts the *single* infinite set; HF never needs it).
* **What remains for a fully-discharged drop.** The asserted
  `ax-N*/ax-Z*/ax-Q*` signature is currently a labelled PROJECTION
  (≤ 10^4). For the *general* ℚ that discharge needs ω (ℕ as a completed
  semiring). For the *closed proof's finite, quantifier-free element
  set*, the deep check shows it is invoked **only at finite constants**,
  so the discharge should also avoid ω — but exhibiting that as a
  *kernel-checked* HF-carrier construction (replacing the ≤10^4
  PROJECTION with a MEASURED `$p`) is **not done in this seam** and is
  the precise next step. Until then the honest claim is bounded:
  `omex` is **incidental by machine-checked DAG-reachability**, the
  EXTRACTED ZF-set-hood floor **drops to 10^12.810**, and the
  signature-discharge avoiding ω for the finite set is **strongly
  evidenced but remains a labelled PROJECTION**, never merged into the
  EXTRACTED line.

No fabrication: the drop 10^17.484 → 10^12.810 is an EXTRACTED-line
result (set.mm cost of `sucexg` vs `omex`, both quoted verbatim from the
machine-checked Milestone C). The "Infinity is not essential to *this*
proof" conclusion is a precisely-characterized, machine-checked structural
fact about the closed model's DAG — an honest positive result with its
residual (the standalone HF carrier + PROJECTION discharge) explicitly
left open.

---

## 6. PROVEN/MEASURED · EXTRACTED · PROJECTION ledger

| Quantity | Status | Value | Source |
|---|---|---|---|
| `qzf.mm` / `qzfext.mm` kernel-verify | **MEASURED** | 11 + 3 `$p` ✔ | `seam1floor` (OUR kernel) |
| closed-model reached symbols; `om` absent | **MEASURED** | DAG fact | `seam1floor` |
| closed roots reach 0 ℕ/ℤ recursion ops | **MEASURED** | DAG fact | `seam1floor` deep check |
| Milestone A derived layer | **MEASURED** | 10^2.408 | `qzffloor` (quoted) |
| Milestone B ℚ_geo(√r) @ K=1 | **MEASURED** | 10^2.149 | `qzfextfloor` (quoted) |
| `sucexg` ZFC cost (essential dominant) | **EXTRACTED** | 10^12.810 | Milestone C / `STAGE2_BC.md` (verbatim) |
| `omex` ZFC cost (ruled incidental) | **EXTRACTED** | 10^17.484 | Milestone C / `STAGE2_BC.md` (verbatim) |
| SEAM-1 closed-model floor | **EXTRACTED-dominated** | 10^12.810 | `max(A,B,essential-ZF)` |
| ax-N*/ax-Z*/ax-Q* → bare ZF discharge | **PROJECTION** | ≤ 10^4 | `STAGE2_A.md` §6 (labelled; not merged) |
| standalone ω-free HF carrier, kernel-checked | **OPEN** | — | residual, §5 |

## 7. Files / reproduce

* `src/bin/seam1floor.rs` — the SEAM-1 instrument (new; additive). OUR
  kernel re-verifies both model files, then measures essentiality by
  DAG-reachability. `cargo run --release --bin seam1floor`.
* Read-only consumed: `data/qzf.mm`, `data/qzfext.mm`,
  `data/grounded.mm`. `modelsplice.rs`/`kernel.rs`/`grounded.mm` etc.
  untouched.
* set.mm figures: EXTRACTED-elsewhere (Milestone C, `STAGE2_BC.md`),
  quoted verbatim, never recomputed or merged here.
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
