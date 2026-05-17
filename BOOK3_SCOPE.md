# BOOK3_SCOPE — Gauge theory's differential-geometric content (the third turn of the recurring theorem)

**This is BOOK THREE — the thesis anchor.** It is the rigorous,
adversarially-honest scope document the eventual Book-3 claims are
checked against by a hostile reader. It mirrors `SEQUEL_SCOPE.md`'s
structure and `SDG_MODEL.md`'s dual-immovable-floor discipline, and it
states the predicted honest ceiling **now**, in advance of the
measurement, so the measurement is held to it.

Adversarially honest. Every statement here is, and every eventual
Book-3 claim must be, exactly one of:

- **MEASURED** — `src/kernel.rs` (the sole, unchanged, logic-agnostic
  trust root) over a frozen `.mm` corpus; OUR cut-free `$a`-leaf metric
  (`$a`→1, `$f`/`$e`→0, `$p`→Σ steps), reproduced by a `*floor`
  instrument; plus the intuitionistic-purity verdict (`sdgpure`-family).
- **EXTRACTED** — a set.mm/ZFC proof-DAG figure, verbatim. (Book 3 is
  not expected to produce one; see §3/§4.)
- **[PROJECTION]** — a labelled structural / citation-level derivation.
  It is **never** a measured or extracted proof-size number, is
  **never** summed into or merged with the MEASURED Book-3 cost, and is
  presented with its full derivation. A precisely-characterized
  projection IS a deliverable; a fabricated number dressed as measured
  is a ZERO (Iron Rule).
- **OPEN** — a precisely-characterized obstruction, named up front. Per
  the Iron Rule a precisely-characterized obstruction is a FULL
  SUCCESS, not a hidden gap.

The slogan is never substituted for the measured truth. Where Book 3's
honest ceiling is "proofs small & pure, meaning irreducibly heavy", that
is **stated as the prediction now** (§1, §4), not discovered later.

---

## 0. What Books One and Two established (the recurring theorem, proven 3×)

The project has measured the same structural theorem on three different
mathematical objects. The theorem, stated once:

> **The irreducible *content* of a piece of mathematics is small,
> exact, and removable-from-derivation; the irreducible *cost* is the
> *meaning* — the model / grounding that makes the content
> non-vacuous — and that cost is immovable, lives in a different
> column, and is never summed into the content.**

The three turns (each MEASURED, none a slogan):

1. **Book One — metric geometry (`birkhoff-asa`, CLOSED, on
   `origin/main`).** The fully-expanded kernel-verified ASA′
   metric-geometry proof is small (geometry ≈ 10^2.51–10^5.58
   `[MEASURED]`). Its entire classical scaffolding (field, completeness,
   most of order) is *removable*; the single irreducible content residue
   is **two order literals** — `x·x=0 ⟹ x=0`-flavoured positivity,
   *proven not a ring identity* (it fails in ℤ/8, ℤ/4). The cost of
   *grounding* the line (ℝ in ZFC) is huge and lives in a separate
   column: set.mm's analytic ℝ **10^46.10 `[EXTRACTED]`**, collapsing
   under a native ZF model to **10^17.484** and a proof-relativized HF
   carrier to **10^12.810 `[EXTRACTED]`**, the irreducible residual
   being `omex` (Axiom of Infinity), *not* analytic ℝ. Three quantities
   (content · grounding · satisfiability) **never summed**.

2. **Book Two — synthetic differential geometry (`SEQUEL_SCOPE.md`,
   `SDG_MODEL.md`).** The exact dual: SDG is the intuitionistic world
   that *refuses* Book One's irreducible inference. The synthetic
   proofs — first synthetic derivative `sdg-deriv` 2243; seam-free
   chain `sdg-calc2-chain` 349; order-2 Taylor 6080; tangent
   `R^D≅R×R` 2243; the W3-glob2 keystone `sdg-bracket-global` 2525 —
   are **small (10^2–10^4.6), MEASURED, and mechanically certified
   GENUINELY INTUITIONISTIC** (`sdgpure`: 44 logical `$a`, none
   classical in NAME or SHAPE, none in any `$p`'s consumed-axiom
   closure). The classical apparatus is **removable from the
   derivation**. The cost that is irreducible is the **model** that
   makes them non-vacuous: a well-adapted topos (Dubuc/Cahiers/
   Moerdijk–Reyes), an 11-rung citation ladder rooted in full classical
   ZFC, *containing Book One's entire ℝ-in-ZFC term as rung 2*. It is
   **[PROJECTION]**, strictly heavier than Book One's grounding, **never
   summed** into the MEASURED proof figures. A genuinely leaner
   *syntactic / classifying-topos* model exists but only for the *weak*
   (formal-consistency) reading, with the exact caveat that it does not
   certify the system *is* differential geometry.

The recurring theorem held both times, and twice it held *as a duality*:
Book One's content was tiny and its grounding huge-and-classical; Book
Two's content was tiny-**and-constructive** and its grounding
huge-**and-classical** (heavier still). In neither book did a better
construction dissolve the meaning-cost; in both, almost everything else
was removable scaffolding. **Book Three asks whether this holds a third
time, on a genuine physical theory: gauge theory.**

---

## 1. The Book-3 thesis (stated PRECISELY, NON-SLOGAN)

> **THESIS (Book Three).** The differential-geometric content of gauge
> theory — connection, curvature / field-strength `F`, the Bianchi
> identity, and gauge-covariance of `F` — encodes in **small
> intuitionistic kernel proofs** over the **Book-Two substrate**
> (`data/sdg.base.mm`: a commutative ring `R` + Kock–Lawvere `ax-kl` +
> microcancellation `ax-microcancel` + the `D_k` tower + the
> positive-Horn application congruence `eq-ap`), with the
> **classical-analysis apparatus removable from the DERIVATION** and
> **irreducible only in the INTERPRETATION** — the well-adapted model,
> per `SDG_MODEL.md`'s dual immovable floor. **Book Three MEASURES
> exactly where that line falls**: which gauge-theoretic identities are
> kernel-verified pure-intuitionistic `$p` over the frozen substrate,
> versus where (if anywhere) a *new* substrate commitment is forced
> (flagged exactly as `eq-ap` was — named, not smuggled), versus what
> remains a labelled model-grounding [PROJECTION] (the Book-Two
> model-floor, *not re-summed*).**

This is the third turn of the §0 recurring theorem, on gauge theory.
It is **not** the slogan "gauge theory is free / needs no analysis." It
is the precise, falsifiable claim that the *derivation* of the
gauge-geometric core is intuitionistically pure and small while the
*meaning* (that this synthetic gauge theory **is** the physical one)
remains the Book-Two model-floor [PROJECTION].

### 1a. What would FALSIFY the thesis (a hard, mechanical falsifier)

The thesis is **FALSIFIED** if a genuine gauge-theoretic core `$p`
— curvature/field-strength `F`, the Bianchi identity `dF`-style, or
gauge-covariance of `F` — **provably requires a classical principle**
(LEM / `ax-3`/Peirce / DNE / stable equality / decidable apartness) in
its consumed-axiom closure. This is caught **mechanically** by the
`sdgpure`-family guard (reused unchanged): it computes the transitive
consumed-`$a` closure of every `$p` and hard-fails if any blacklisted
classical principle appears by NAME or by statement SHAPE. A
gauge-theoretic theorem that cannot be proven without a classical
smuggle would make "the gauge-geometric content is intuitionistic" a
fiction — the exact Book-3 analog of Book One's "asserting what should
be proven" and Book Two's "assuming what should be refused." If this
occurs it is **REPORTED as the headline finding**, with the derivation
showing the classical dependence, not hidden.

### 1b. What would merely BOUND the thesis (not falsify it)

The thesis is **BOUNDED, not falsified**, by the following — each of
which is *predicted up front* in §4:

- **The model-grounding remains a labelled [PROJECTION].** That the
  synthetic gauge theory **is** physical gauge theory requires a
  well-adapted model in which `R` is the smooth line and the synthetic
  curvature coincides with the classical field strength. This is
  **exactly the Book-Two model-floor** (`SDG_MODEL.md` §1–§4):
  irreducibly heavy, irreducibly classical, strictly above Book One's
  ℝ-grounding. It is **already a labelled [PROJECTION]**; Book 3 does
  **not** re-sum it and does **not** newly fabricate a number for it.
  Its persistence is the *predicted* outcome, not a falsification.

- **A gauge identity may force a NEW positive substrate commitment.**
  If curvature/Bianchi/gauge-covariance cannot close over the frozen
  `eq-ap`-extended `data/sdg.base.mm` without one further axiom, that
  axiom — **provided it is intuitionistically pure** (positive Horn /
  geometric, no `¬`/`∨`, no decidability/stability/apartness, passing
  `sdgpure` NAME+SHAPE) — is a *bound*, not a falsification, and it
  is **FLAGGED exactly as `eq-ap` was**: a loudly-named
  "FLAGGED NON-CONSERVATIVE SUBSTRATE COMMITMENT #N" block, classified
  B-not-A with a syntactic non-derivability argument, never smuggled.
  The thesis survives a *named, pure* new commitment; it does **not**
  survive a *classical* one (that is §1a falsification) or a *hidden*
  one (that is an Iron-Rule ZERO).

The asymmetry between §1a (classical ⇒ falsified) and §1b (named pure
axiom, or model-[PROJECTION] ⇒ merely bounded) is the whole content of
the honesty discipline and is the deliverable.

---

## 2. The dependency map (curvature keystone → Bianchi → a genuine gauge statement)

Book Two already laid the Book-3 bridge and **named Book 3's keystone
exactly** (`SEQUEL_SCOPE.md` §5l, the synthetic-connections layer
`data/sdg.conn.mm`, kernel-verified, `sdgconnpure` GENUINELY
INTUITIONISTIC). The dependency map is therefore not speculative; it is
the precise continuation of an existing, measured boundary.

```
  Book-2 substrate (FROZEN, eq-ap-extended data/sdg.base.mm)
        + Book-2 keystone  sdg-bracket-global  (W3-glob2, CLOSED, MEASURED 2525)
                                   │
                                   ▼
  [B3-conn]  synthetic-connections layer            STATUS: ALREADY DONE (§5l)
   sdg-conn-{transport0,kl-affine,diff-tensor,        — kernel-verified, MEASURED
   torsion-sym,curv-cross}  PURE RING, intuitionistic   (62/92/48/20/60 leaves),
                                   │                     sdgconnpure clean.
                                   ▼
  ┌─────────────────────────────────────────────────────────────────────┐
  │ [B3-curv]  KEYSTONE — the curvature / field-strength F principal     │
  │  part R(d₁,d₂).  Book 2 surfaced this as EXACTLY ONE loudly-labelled  │
  │  boundary $e (conn.hol): the inseparable (a) ap-Leibniz + (b)         │
  │  W3-glob2 globalized generator-side derivative of the Christoffel     │
  │  symbol.  Book 3's keystone task: CLOSE conn.hol by consuming the     │
  │  already-CLOSED seam-free sdg-bracket-global machinery at curvature   │
  │  level — exactly as Book 2 closed the bracket via the seam-free       │
  │  sdg-deriv construction.  KEYSTONE-GATED.                             │
  └─────────────────────────────────────────────────────────────────────┘
                                   │ (consumes the closed sdg-bracket-global)
                                   ▼
  [B3-bianchi]  the Bianchi identity (dF-style): the D×D×D                KEYSTONE-GATED
   infinitesimal-cube cyclic-sum of curvature vanishes.  Expected:        (downstream of
   pure-ring + the keystone bracket globalization; NO new classical.       B3-curv)
                                   │
                                   ▼
  [B3-gauge]  a GENUINE gauge-theory statement — the deliverable that     KEYSTONE-GATED
   makes Book 3 about gauge theory and not just connections:               + the honest
   F gauge-covariant under G ↦ G + (gauge change), AND the source-free     candidate for a
   Yang–Mills/Maxwell-type identity (dF = 0 / Bianchi as the homogeneous   NEW flagged
   field equation).  Expected pure-ring + keystone; this is where a new    commitment if
   positive substrate commitment, if any, would surface (§1b) — flagged.   one is forced.
```

**Keystone-gated vs separate-corpus (the honest split):**

- **KEYSTONE-GATED:** `B3-curv`, `B3-bianchi`, `B3-gauge`. Each
  genuinely **consumes the closed `sdg-bracket-global`** (the W3-glob2
  Lie-bracket globalization, MEASURED 2525, `ax-microcancel`+`ax-gen`
  in its closure). They cannot be honestly claimed without it; Book 2
  proved (§5l) that curvature *is* the generator-side synthetic
  derivative of the Christoffel symbol, so the gate is real, not
  decorative.
- **SEPARATE-CORPUS (not keystone-gated):** the structural connection
  layer `B3-conn` is **already done** — pure-ring, intuitionistic,
  kernel-verified, `sdgconnpure`-clean, self-contained over the frozen
  base, sharing no `$p` with any other corpus (rename-free
  concatenation). Any further purely-structural gauge bookkeeping
  (e.g. the (1,2)-tensor character of the connection difference, the
  zeroth-order vanishing of the holonomy commutator) is in this
  separate, ungated column.

**The honest expectation from `SDG_MODEL.md`.** The dual immovable
floor pre-sharpens Book 3: even with every gauge `$p` closed
intuitionistically and small, the statement "this **is** physical
gauge theory" rests on a well-adapted model where `R` is the smooth
line — the *same* 11-rung, ZFC-rooted, real-analysis-leaf [PROJECTION]
floor as Book Two, **strictly heavier than Book One's**, and
**containing Book One's ℝ-in-ZFC as a sub-rung**. There is **no
well-adapted analog of Book One's RCF descent**: an ordered field
cannot replace the smooth line because KL is *false* in any C^∞-free
algebraic model. Book 3's honest expectation, stated now, is that the
gauge content is small and pure and the gauge *meaning* is exactly this
pre-existing immovable model-floor — **not re-summed, not re-derived,
not newly numbered.**

---

## 3. MEASURED vs [PROJECTION] discipline, restated for Book 3 (the trust story)

- **Verifier reused, UNCHANGED.** The sole derivation-checking trust
  root is `src/kernel.rs` — the sealed, logic-agnostic Metamath-subset
  verifier. It checks every `$p` is derived from its `$a` base by
  substitution + stack discipline + DV side-conditions, agnostic to
  whether the base is classical or intuitionistic. Book 3 adds **no new
  verifier and no kernel change**.

- **`sdgpure` is the dual no-cheating guard, reused.** The
  intuitionistic-purity guard (the Book-2 dual of Book One's
  no-cheating `--lint`) is the trust root for the *intuitionistic*
  claim. For every gauge `$p` it computes the transitive consumed-`$a`
  closure and hard-fails on any classical principle by NAME or SHAPE,
  and structurally scans the substrate for any classical-shaped axiom
  even if unused. A Book-3 gauge corpus is only certifiable if its
  guard returns **GENUINELY INTUITIONISTIC ✔**. An honest "this gauge
  `$p` provably needs DNE, here is the derivation" is a **first-class
  reported finding** (the §1a falsifier), never hidden.

- **The gauge model-grounding is the Book-Two model-floor, NOT
  re-summed.** Book 3 does **not** produce a new model-cost number.
  `SDG_MODEL.md` already classified the well-adapted-topos grounding as
  an irreducibly-heavy classical [PROJECTION] (16 nodes, 11-rung
  ladder, ZFC leaf, *contains Book One's ℝ-in-ZFC as rung 2*). Gauge
  theory in the line model `R` lives **inside that same model**; its
  grounding is the *identical* [PROJECTION], cited not re-derived,
  **never added** to the MEASURED gauge `$p` figures. Fabricating a
  fresh "gauge model cost" dressed as measured would be an Iron-Rule
  ZERO. There is, by design, **no EXTRACTED number** for Book 3's
  grounding — no Metamath/ZFC formalization of a well-adapted topos
  exists to run an extractor over (same principled absence as
  `SDG_MODEL.md`).

- **Three columns, never summed.** Gauge proof size `[MEASURED]` ·
  model-grounding `[PROJECTION]` (= the Book-2 floor, cited) ·
  satisfiability (the real structure). The discipline — not the
  magnitude of any column — is the deliverable, exactly as in Books
  One and Two.

---

## 4. Honest open — the predicted residuals, named UP FRONT

Per the Iron Rule, a precisely-characterized obstruction is a FULL
SUCCESS. These are named **now**, in advance of the measurement, so the
eventual Book-3 result is held to them and cannot drift into the slogan:

1. **Model-grounding [PROJECTION] (PREDICTED, will persist).** That the
   synthetic gauge theory **is** physical gauge theory is the Book-Two
   well-adapted-topos model-floor: irreducibly heavy, irreducibly
   classical, 11-rung ZFC-rooted, containing Book One's ℝ-in-ZFC as a
   sub-rung. **Book 3 will NOT dissolve this.** Its persistence is the
   predicted, honest ceiling — *not* a Book-3 failure. No leaner
   *well-adapted* route exists (no RCF analog; KL false without
   smoothness). A leaner *syntactic* route exists only for the weak
   formal-consistency reading, with `SDG_MODEL.md` §4's exact caveat
   (it does not certify the system *is* gauge theory). Reported as a
   labelled [PROJECTION], **never summed**.

2. **A gauge identity may force a NEW substrate commitment — flagged
   like `eq-ap` if so (OPEN, watched).** Curvature/Bianchi/
   gauge-covariance may not close over the frozen `eq-ap`-extended base
   without one further axiom. If so, and **only if it is
   intuitionistically pure** (positive Horn/geometric, `sdgpure`
   NAME+SHAPE clean), it is a **bound, not a falsification** (§1b),
   surfaced as a loudly-flagged "NON-CONSERVATIVE SUBSTRATE COMMITMENT
   #N" with a syntactic B-not-A non-derivability argument — the exact
   `eq-ap` discipline. A *classical* forced commitment is instead the
   §1a **falsification** and is reported as the headline. A *hidden*
   one is an Iron-Rule ZERO.

3. **The keystone gate is real (OPEN until B3-curv closes).** `B3-curv`
   is gated on consuming the closed `sdg-bracket-global` at curvature
   level (Book 2's `conn.hol` boundary `$e`, §5l). Until that `$e` is
   genuinely discharged — kernel-authoritatively, with
   `sdg-bracket-global`'s seam (`ax-microcancel`+`ax-gen`) actually in
   the closure, not an inert decorative hypothesis — curvature/Bianchi/
   gauge are **OPEN**, named, not claimed. An inert-`$e` "closure" is
   rejected, not shipped (the Book-2 §5k precedent).

### The predicted honest ceiling (stated NOW, adversarially)

> **Predicted Book-3 result, in advance:** the gauge-geometric content
> — connection, curvature `F`, Bianchi, gauge-covariance — will be
> **small, intuitionistically pure, kernel-verified `$p`** over the
> Book-Two substrate (10^2–10^4-ish leaves, the Book-2 regime),
> possibly at the cost of **one further FLAGGED positive-Horn substrate
> commitment** in the `eq-ap` mould (a bound, not a falsification),
> with the classical-analysis apparatus **removable from the
> derivation**; and the statement that this **is** physical gauge
> theory will rest on the **same irreducibly-heavy, irreducibly-
> classical well-adapted-topos model-floor as Book Two** — a labelled
> [PROJECTION], never summed, not dissolved by any better construction.
> **The honest ceiling is the §0 recurring theorem's third turn:
> proofs small & pure, meaning irreducibly heavy — the same finding as
> Book Two.** If the measurement comes back better than this, that is a
> genuine surprise to be reported with its proof; if it comes back at
> exactly this ceiling, that is the *expected* success and must be
> stated as such, never inflated past it. The thesis is FALSIFIED only
> by §1a (a gauge core provably needing a classical principle, caught
> by `sdgpure`); everything else (model-[PROJECTION], a named pure new
> axiom) merely BOUNDS it, exactly as predicted here.

This document is the anchor. Any eventual Book-3 claim that is not a
kernel-verified MEASURED `$p`, a labelled [PROJECTION] with its
derivation, or a precisely-characterized OPEN obstruction — or that
sums the model-floor into the proof figures, or substitutes the slogan
for the measured truth — is, by this document's standard, a ZERO.

---

## 5. WAVE-2 RESULT — graded against this contract (post-registration, MEASURED)

This section is appended *after* the prediction above; the prediction
text is **unchanged** so the result is checkable against the contract,
not graded on a curve drawn after seeing it.

**Wave 1 (registered/CONFIRMED earlier):** `B3-conn` (done), `B3-curv`
(curvature `R` seam-free, `conn.hol` discharged), `B3-bianchi` (first /
algebraic Bianchi), `B3-gauge` (gauge layer, one labelled boundary `$e`)
— all kernel-verified pure intuitionistic, landed at the predicted
ceiling. (`SEQUEL_SCOPE` §5m/§5n.)

**Wave 2 — the differential Bianchi `∇R = 0` (the `B3-bianchi` tail,
§4 residual #3's named keystone gate):** `data/sdg.bianchi2.mm`, 3
kernel-verified pure `$p` over the FROZEN base. `sdg-bianchi2-covd`
**genuinely threads the one-level-up seam** (the §5j/§5k recursion
applied to `R` itself — the §5m named residual), consuming
`ax-microcancel`+`ax-gen`, **MEASURED 2685 cut-free `$a`-leaves —
identical to wave-1 `sdg-curvature`** (the recursion proven *exact*, not
approximated); `sdg-bianchi2-cyclic` the pure-ring cyclic vanishing
(163, identical to wave-1 `sdg-bianchi`); `sdg-bianchi2-addcan-imp` the
§5b seam-closer rebuilt local for self-containment (851). `sdgbianchi2pure`:
**GENUINELY INTUITIONISTIC ✔**, hard-fail adversarial assertions all
pass. (`SEQUEL_SCOPE` §5o.)

**Verdict against §1a / §1b / §4:**

- **§1a (FALSIFIER) — NOT triggered.** No gauge/Bianchi core `$p`
  required any classical principle; `sdgbianchi2pure` certifies the
  whole consumed-axiom closure classical-free by NAME+SHAPE.
- **§1b (BOUND) — NOT newly triggered.** No new substrate commitment
  was forced: the differential Bianchi closed over the frozen
  `eq-ap`-extended base with **zero** new axioms. The non-abelian
  `[A,R]` term vanishes by the **§2 commutative scalar-line reduction
  already declared in this contract** — a CITED model choice, not a new
  commitment, not a hidden one.
- **§4 residual #1 (model-grounding [PROJECTION]) — persists EXACTLY as
  predicted.** Unchanged Book-Two well-adapted-topos floor, never
  re-summed, not dissolved.
- **§4 residual #3 (the keystone gate) — DISCHARGED for the
  differential Bianchi**, kernel-authoritatively (seam genuinely
  consumed, asserted hard-fail, not an inert `$e`).

**Wave 3 — the `gauge.fstr` boundary discharged (`B3-gauge`'s lone
boundary `$e`, §4 residual #3 for the gauge layer):**
`data/sdg.gaugecov.mm`, 4 kernel-verified pure `$p`. SEQUEL_SCOPE §5n
had surfaced F's genuine value + FULL gauge-covariance as **exactly one
opaque composite `$e`** (`gauge.fstr`) folding the inseparable (a)
`ap`-Leibniz + (b) full curvature generator. Wave 3 **retires it the
way wave 1 retired `conn.hol`**: `sdg-gaugecov-fstr` is the seam-free
curvature construction on the gauge potential A — **genuinely consumes
`ax-microcancel`+`ax-gen`** (the (b)-half), MEASURED 2685 (identical to
wave-1 `sdg-curvature`); `sdg-gaugecov-aprot` **genuinely consumes
`eq-ap`** (the (a)-half, the §5j pattern); `sdg-gaugecov-covariant` the
PURE-RING conjugation swap. `sdggaugecovpure`: **GENUINELY
INTUITIONISTIC ✔**, hard-fail adversarial assertions all pass — both
halves genuinely consumed, **NO inert composite `gauge.fstr` `$e`
survives**. (`SEQUEL_SCOPE` §5p.)

**Verdict against §1a / §1b / §4 (wave 3):**

- **§1a (FALSIFIER) — NOT triggered.** No gauge-covariance core `$p`
  required a classical principle; `sdggaugecovpure` certifies the
  closure classical-free.
- **§1b (BOUND) — NOT newly triggered.** No new substrate commitment:
  closed over the frozen `eq-ap`-extended base with zero new axioms.
  The full non-abelian `[A,R]`/`A∧A` beyond the **§2 declared scalar
  reduction** is the named residual — a CITED model choice, not new,
  not hidden.
- **§4 residual #1 (model [PROJECTION]) — persists exactly as
  predicted.** Unchanged Book-Two floor, never re-summed.
- **§4 residual #3 (the keystone gate) — DISCHARGED for the gauge
  layer too**, kernel-authoritatively (both inseparable halves
  genuinely consumed, asserted hard-fail, no inert `$e`).

**Wave 4 — the NON-ABELIAN structure (the §2 scalar-reduction
residual, attacked head-on):** `data/sdg.nonab.mm`, 6 kernel-verified
`$p`. NOT a new non-commutative axiom — **2×2 matrices over the FROZEN
commutative ring**, non-commutativity purely structural. The canonical
witness `[A,B] = [[1,0],[0,(inv 1)]]` computed entrywise PURE RING,
plus the derived `inv`-congruence and the non-abelian wedge.
`sdgnonabpure`: **GENUINELY INTUITIONISTIC ✔ AND EVERY `$p` PURE RING ✔**
(hard-fail if any `$p` reaches the seam / KL / `eq-ap` — none does).
(`SEQUEL_SCOPE` §5q.)

**Verdict against §1a / §1b / §4 (wave 4):**

- **§1a (FALSIFIER) — NOT triggered.** No `$p` consumed any classical
  principle (NAME+SHAPE, full closure).
- **§1b (BOUND) — NOT triggered.** **No new substrate commitment**:
  genuine non-abelian structure closed over the frozen base with zero
  new axioms and zero seam/`eq-ap` — the recurring theorem holds *even
  at the non-abelian frontier*. The general-rank Yang–Mills tower
  beyond the canonical 2×2 concrete witness is the named residual (the
  Book-One-style concrete-separation discipline), not a forced
  commitment.
- **§4 residual #1 (model [PROJECTION]) — persists, never re-summed.**
- **CROSS-BOOK FINDING (new, named, not faked).** The non-vacuity of
  `[A,B]` (that it is genuinely non-zero) **is exactly `1≠0`**, which
  is **identical to Book One's measured irreducible residue**
  (`COST_STRUCTURE` bottom, `suc∅≠∅`/orientation). Book Three's
  non-abelian meaning-residue **reduces to** Book One's — the spine is
  one bone. Reported as a named residual.

**Wave 5 — the GENERAL structural non-commutation theorem
(`SEQUEL_SCOPE` §5s):** `data/sdg.nonabgen.mm`, 5 kernel-verified
pure-ring `$p`. The general statement of which wave-4's concrete
witness was the instance: for general symbolic `2×2` entries the
commutator `(1,1)` entry reduces pure-ring to the off-diagonal mixing
term (`sdg-nonabgen-mixcancel`, MEASURED 2647), the symmetric parts
cancelling via `sdg-nonabgen-symvanish`. Independently re-verified
(kernel + purity + statement-content). **§1a NOT triggered, §1b NOT
triggered** — pure-ring identity, true in every commutative ring
including the trivial one, needs **no `1≠0`** (kept rigorously distinct
from the wave-4 non-vacuity residue, not conflated). Named residual:
the full general-rank/`n×n` Yang–Mills tower (the `(1,1)` entry at
general `2×2` is closed; the tower is not — the Book-One concrete→general
discipline).

**Wave 6 — GROUNDING the cross-book spine + characterizing the
model-grounding (`SEQUEL_SCOPE` §5r, `SDG_MODEL` §4c):** the wave-4
spine claim, narrative in §5q, is **grounded**: `data/sdg.spine.mm`
(3 pure-ring `$p`) kernel-verifies the transport
`( <[A,B]₁₁-expr> = 0 -> 1 = 0 )` (`sdg-spine-b3`, MEASURED 3008) —
the Book-Three segment; joined at the literal `1≠0` to Book One's
already-set.mm-anchored residue (cited, counted once). The spine is
upgraded narrative-`[PROJECTION]` → two-segment transport, both
anchored, claimed at exactly that weight (a structural identity between
two MEASURED residues, never a grand unification). The model-grounding
`[PROJECTION]` is honestly characterized: the **strong** well-adapted
model stays principled-`[PROJECTION]` (un-groundable by principle, the
immovable dual floor); the **weak** non-vacuity segment's irreducible
residue **is** this now-grounded spine `1≠0` — grounded exactly as far
as it honestly can be, the rest named not faked.

**The §0 recurring theorem's third turn — its tail, the gauge
boundary's discharge, the non-abelian frontier, its general statement,
and the grounded cross-book spine — all held at exactly the predicted
ceiling: content small, pure, kernel-verified, no new commitment;
meaning irreducibly the Book-Two model `[PROJECTION]`, its non-abelian
meaning-residue *identical to Book One's* and now *transport-grounded*
to it. Stated as the expected success — and the genuine new structural
findings, claimed at exactly their weight — NOT inflated past the
contract.**

**Wave 7 — the non-abelian bracket algebra; the field-theory question
answered precisely (`SEQUEL_SCOPE` §5t):** `data/sdg.nonabF.mm`, 7
kernel-verified pure-ring `$p` — the `inv`/distribution toolkit of the
homogeneous Yang–Mills equation `DF=∇F+[A,F]=0`, headlined by bracket
**antisymmetry** `[a,b]=inv[b,a]` (proven as an `inv`-distribution
identity, genuine & non-vacuous in any ring). Stated up front and
honestly: a *symbolic* Jacobi over the commutative base is **vacuous**
and is deliberately **not** shipped; the genuine non-abelian non-vacuity
is the already-grounded spine `1≠0`. **§1a NOT triggered, §1b NOT
triggered** (pure-ring, no new commitment, nothing classical). This
delimits the project's scope precisely: we hold the **kinematic core +
the source-free field equation's algebra** of a classical gauge field
theory; the **dynamics** (full `DF=0` assembly, matrix-Jacobi at a
non-vanishing witness, the inhomogeneous `D⋆F=J`, action / Hodge /
matter / quantization) are the **named residuals** — and the *meaning*
remains the immovable Book-Two model `[PROJECTION]`. The recurring
theorem, held once more — reported, not faked, not inflated past the
contract.**

**Wave 8 — the genuine non-vacuous non-abelian Jacobi at a concrete
witness (`SEQUEL_SCOPE` §5u):** `data/sdg.jacobi.mm`, 5 kernel-verified
pure-ring `$p`; the §5t residual discharged at the sl₂-style witness
`A=[[0,1],[0,0]],B=[[0,0],[1,0]],C=[[1,0],[0,0]]` — all **4 entries**
of `[A,[B,C]]+[B,[C,A]]+[C,[A,B]]=0` close entrywise (j11..j22, MEASURED
~64k leaves each), pairwise commutators genuinely non-zero (NOT
collapse). Integrator-reverified: kernel + purity + independent matrix
recomputation + structural pattern-match of the literal term. **§1a/§1b
NOT triggered.** Non-vacuity = the already-grounded spine `1≠0`, named
not faked. Residual: general rank / arbitrary Lie algebra (the
Book-One concrete-separation discipline).

**Wave 9 — the orientation-dual Hodge-⋆ skeleton; a precise NEGATIVE
map (`SEQUEL_SCOPE` §5v):** `data/sdg.hodge.mm`, 5 kernel-verified
pure-ring `$p`. The 2D-scalar orientation-dual `⋆` algebra closes
pure-ring (`area-antisym`, `starstar`=⋆⋆=id, `star-lin`, and
`codiff-dual` = `∇⋆F=0` verified to be **exactly the orientation-dual
of the source-free `∇F=0`**, 163 leaves identical to
`sdg-bianchi2-cyclic`). **§1a NOT triggered; §1b honestly engaged and
REPORTED, not crossed:** a genuine *metric* Hodge `⋆` (dim>2,
`D⋆F=J`, action, matter, quantization) **forces a new flagged
metric/bilinear commitment absent from the frozen bare ring** — the
precisely-named dynamical residual, claimed at its weight, not faked
into a `$p`. This is the iron-rule-correct deliverable: the cheap
orientation skeleton shipped; the genuine dynamics named as the
boundary they are. The recurring theorem, held twice more — reported,
not inflated past the contract.**
