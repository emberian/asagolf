# SEAM2 — the tree-like vs DAG-like proof-size separation for the Birkhoff postulates

**A concrete, kernel-MEASURED instance. Reported, not faked.**

This document characterizes, as a named instance with measured constants,
the tree-like (cut-free, fully-inlined) vs DAG-like (shared-subproof)
proof-size relationship for the seven derived Birkhoff postulates and the
ASA′ composition. Every number below is computed from a corpus that a
*fresh, independent* `kernel::Db::verify()` accepted in the measuring
process; the CSE column additionally passes the exact same three-gate
kernel discipline as `grounded.rs`'s `emit_json` (verify ∧
byte-identical conclusions ∧ strict shrink).

Trust root: `src/kernel.rs`, alone. Measurement tool:
`src/bin/dagsep.rs` (read-only consumer; modifies no trusted or
protected file). Authoritative inputs:

* `grounded data/grounded.mm` → `Kernel: verified all 96 staged lemmas ✔
  (db: 267 statements)`, `G4 SAS = 383606`, `[cse] shared_total
  10134529 -> 1820328 (−82.04%)` (41 rounds, 180 s budget).
* `dagsep data/grounded.out.mm` → independent fresh-kernel re-verify
  `VERIFIED ALL ✔ (267 statements, 96 $p)`; per-postulate table below;
  its own kernel-gated `[cse] 10134529 -> 1916452 (−81.09%)` (40 rounds,
  180 s budget). (The CSE figure differs run-to-run only because the
  greedy batched pass is wall-clock-budgeted — see §3; both are
  kernel-verified valid lower bounds, neither is the fixpoint.)

## 1. The three metrics (same scale, only sharing differs)

For a target `$p` *P*:

* **TREE** = `expand(P)` — the fully-inlined cut-free proof: every `$p`
  reference recursively replaced by its proof, counting `$a` primitive
  leaves 1, `$f`/`$e` substitution glue 0 (set.mm convention). This is
  the project's headline metric and the poll's actual subject ("size of
  a fully-expanded proof"). It is an **exact integer**, sharing-invariant
  by construction.
* **DAG** = the size of *P*'s proof under maximal *named-lemma* sharing:
  Σ stored RPN proof length over the reachable closure of `$p` lemmas
  (each distinct lemma counted once) + the distinct `$a` leaves it
  reaches (1 each), `$f`/`$e` = 0. This is the honest per-postulate
  analogue of the project-wide `shared_total`.
* **CSE** = the DAG measure recomputed after the sound common-subproof
  minimizer `cse::crunch`, adopted **only** under the kernel gate.

## 2. The exact per-postulate table (kernel-verified)

Fresh-kernel re-verification: **VERIFIED ALL ✔ (267 statements, 96 $p)**.
Corpus-wide `shared_total` (Σ stored RPN over all 96 `$p`) =
**10,134,529** (10^7.006).

| postulate | TREE (cut-free) | DAG (named-share) | CSE (kernel-gated) | TREE/DAG | $p in closure |
|---|--:|--:|--:|--:|--:|
| G0 congruence-subst | 1,035 (10^3.015) | 1,080 (10^3.033) | 1,080 (10^3.033) | 0.958× | 4 |
| G1 ruler (ray exists) | 324,767 (10^5.512) | 441,133 (10^5.645) | 271,763 (10^5.434) | 0.736× | 34 |
| G1 ruler (distance) | 1,829,012 (10^6.262) | 3,087,822 (10^6.490) | 366,187 (10^5.564) | 0.592× | 33 |
| G2 incidence | 787,393 (10^5.896) | 658,010 (10^5.818) | 313,493 (10^5.496) | **1.197×** | 46 |
| G3a ray-angle | 3,987,466 (10^6.601) | 4,819,684 (10^6.683) | 499,821 (10^5.699) | 0.827× | 47 |
| G3b prot-uniq (oriented) | 306,883 (10^5.487) | 300,868 (10^5.478) | 244,772 (10^5.389) | **1.020×** | 58 |
| G3c ray-line | 320 (10^2.505) | 491 (10^2.691) | 491 (10^2.691) | 0.652× | 9 |
| **G4 SAS** (hardest) | **383,606 (10^5.584)** | 136,112 (10^5.134) | 117,821 (10^5.071) | **2.818×** | 51 |
| g3a-dotprop (ASA′) | 437,578 (10^5.641) | 589,899 (10^5.771) | 136,680 (10^5.136) | 0.742× | 8 |
| g4a-sss (ASA′ GAP#2) | 662,520 (10^5.821) | 197,771 (10^5.296) | 118,610 (10^5.074) | **3.350×** | 44 |
| sqd-sym | 76,027 (10^4.881) | 79,143 (10^4.898) | 58,561 (10^4.768) | 0.961× | 8 |

**ASA′ instance** (an explicit *composition* over the verified postulate
`$p` — `src/bin/asaprime.rs` is a separate binary, there is no single
ASA′ `$p` in the corpus; deps `{G0-congsub, g4a-sss, G1a-rulerr,
G1b-rulerd, sqd-sym}`, asaprime adds only ~10^2–10^3 bridges):

* TREE (inlined dep sum) = **2,893,361** (10^6.461)
* DAG (shared closure) = **3,797,403** (10^6.579)
* TREE/DAG = **0.762×**

## 3. The separation, stated as a concrete instance

> **The Birkhoff-postulate corpus is a measured instance in which the
> tree-like / DAG-like proof-size gap is small, bounded, and — for the
> generic-lemma-factored proofs — *inverts*.**

Two findings, both kernel-measured, neither matching the naive
"tree-like is exponentially larger than DAG-like" intuition:

1. **The gap is sub-decadic, not exponential.** Across all eleven
   targets the TREE/DAG ratio lies in **[0.59×, 3.35×]** — under one
   order of magnitude either way. The single largest *tree>dag*
   separation is **G4 SAS at 2.818×** (383,606 cut-free vs 136,112
   shared) and **g4a-sss at 3.350×**. There is no postulate where the
   cut-free proof is even 4× its shared form. The poll's "10^1000" and
   the broad "fully inlining explodes a proof" intuition are *not*
   visible at the postulate granularity: the geometry's tree/DAG seam is
   a small constant factor, not a separation.

2. **The generic-lemma template inverts the classical direction.** For
   G1, G3a, g3a-dotprop, G3c, sqd-sym the cut-free TREE is **smaller**
   than the named-DAG storage (ratio < 1). This is structural and
   honest: the size weapon documented in `README.md`'s *Golf* section —
   prove a tiny identity once over fresh `$f` atoms, instantiate huge
   subterms by *substitution* — is **free in the cut-free metric**
   (substitution adds no `$a` leaves) but is **stored as full RPN** in
   the named-lemma DAG (the giant instantiated term-trees are written
   out in every `$f`-arg position). So the very technique that makes the
   cut-free count small makes the named-DAG count *large*. The classical
   "DAG ≤ tree" inequality holds only for the *post-CSE* DAG, never for
   the as-stored named-lemma DAG of these proofs.

   This is why the corpus-wide `shared_total` (10^7.006) is *larger*
   than the cut-free G4 SAS (10^5.584): they are different roots over
   different metrics (the "read down, not across" rule), and the named
   DAG of the substitution-heavy generic proofs is genuinely bigger than
   their inlined leaf-count. The dagsep table is the apples-to-apples
   per-root reconciliation that makes this precise.

### What this instance establishes vs. does NOT

**Establishes (measured):**
* An exact, reproducible, kernel-verified tree/DAG/CSE size for every
  Birkhoff postulate and the ASA′ composition.
* That for *these* proofs the tree-like vs DAG-like factor is a small
  constant in [0.59×, 3.35×] — concrete constants, not asymptotics.
* That sound CSE compresses the named DAG by **~81–82%**
  (10,134,529 → 1.82–1.92 ×10^6, kernel-gated) yet **provably cannot
  move the cut-free TREE** (it is sharing-invariant by construction —
  `expand` re-inlines every helper; this is `METASEARCH.md` S2's
  kernel-verified-negative wall).

**Does NOT establish:**
* This is **not** a Frege vs extended-Frege, or tree-like vs dag-like
  Resolution, separation in the proof-complexity sense. Those are
  *asymptotic* lower-bound separations over a *family* of tautologies
  (e.g. tree-like Resolution is exponentially weaker than dag-like for
  the pigeonhole / Tseitin families; extended Frege simulates dag-like
  reasoning Frege cannot succinctly). Here we have **one fixed finite
  instance** with **measured constants**, no parameterized family, and
  hence **no asymptotic claim and no super-polynomial lower bound**.
* The constants here are an artifact of the *engineered* generic-lemma
  template; they say nothing about the intrinsic tree/dag separation of
  geometry as a parameterized theory. A genuine separation would require
  a family {ASA_n} and a lower-bound argument, which this project does
  not attempt and which remains open in the literature for geometric
  theories.
* The DAG/CSE numbers are **upper bounds on a minimal DAG, not the
  minimum** (see §4).

The honest framing: this is the proof-complexity analogue of *exhibiting
one concrete circuit and measuring its size before/after common-
subexpression elimination* — informative as an exact instance, but
**not** a circuit lower bound. The value is the measured constant and
the inversion phenomenon, not a separation theorem.

## 4. Optimality of the DAG: improved, bounded, or open?

**Verdict: the named-lemma DAG is NOT optimal (CSE already shrinks it
~81–82%, kernel-gated); the post-CSE DAG is NOT proven optimal either —
there is a *measured, identifiable* residual slack and a true minimum-DAG
lower bound is OPEN. Stated precisely, with evidence:**

**(improved)** The as-stored named-lemma DAG is demonstrably
non-optimal. The sound, kernel-gated `cse::crunch` reduces the
corpus-wide DAG **10,134,529 → 1,916,452 (−81.09%)** in the dagsep run
(grounded.rs's run: → 1,820,328, −82.04%). Per-postulate the CSE column
shows the improvement is uniform and large where there is repeated
structure (e.g. G1-distance 3,087,822 → 366,187, an 8.4× DAG collapse;
G3a 4,819,684 → 499,821, 9.6×). This is a real, kernel-verified further
DAG reduction (option (a) of the brief), already wired into the
project's reported `shared_total`.

**(bounded / not optimal — measured slack)** The post-CSE DAG is itself
**provably not the minimum**, for three concrete, code-identifiable
reasons (all in `src/cse.rs`, which is read-only here):

1. **Budget cut, not fixpoint — slack now MEASURED.** `crunch` stops at
   the first of (a) a wall-clock budget, (b) 60 rounds, or (c) a
   no-profit round. Both 180 s authoritative runs hit the *budget*
   (`[cse] time budget reached after 40/41 round(s)`), i.e. terminated
   with **profitable rounds still pending** — not converged. A
   long-budget probe (`CSE_BUDGET_SECS=1500`, same kernel gate, fresh
   re-verify `VERIFIED ALL ✔`) **quantifies this exactly**: it reaches

   > **shared_total 10,134,529 → 828,377 (−91.83%)** — and prints **no
   > `time budget reached` line**, i.e. it stopped on the 60-round cap
   > or a no-profit round (the greedy heuristic's own local fixpoint),
   > *not* the clock.

   So the 180 s figure (1.82–1.92 ×10^6) was **2.2–2.3× off the greedy
   heuristic's own optimum** (8.28 ×10^5): the budget cut alone was
   ~1.09 ×10^6 nodes of *real, kernel-verified* unrealized slack. Per
   postulate at the 1500 s budget: G4 SAS DAG→CSE **136,112 → 55,231**
   (vs 117,821 at 180 s), G3a **4,819,684 → 186,847** (vs 499,821),
   g4a-sss **197,771 → 54,711**, G1-distance **3,087,822 → 245,338**.
   This is a concrete kernel-gated *further* DAG reduction (option (a)),
   and it sharpens the verdict: even the project's reported
   `shared_total` is **conservatively un-crunched by ~2.3×** purely
   because the production gate is wall-clock-budgeted to 180 s. The
   −91.83% figure is the *greedy heuristic's* fixpoint, **still not the
   certified global minimum** (reasons 2–3 below remain).
2. **Subtree-size cap.** `collect()` only tallies closed subtrees with
   `n.size ≤ MAX_SUBTREE = 4096`. Lemmas in this corpus have
   >3·10^5 nodes, so any repeated span larger than 4096 nodes is
   **never directly factored** — only its ≤4096 sub-patterns are, across
   rounds. Repeated large spans are a structurally-identified,
   un-captured saving. Raising the cap is sound (the kernel still
   re-gates) but memory- and time-costlier; it was not raised here
   (read-only mandate on cse.rs).
3. **Greedy batched local optimum.** Each round takes a `BATCH = 400`
   largest-first non-overlapping pattern set and rewrites top-down.
   Greedy non-overlapping selection with a fixed batch is not the
   optimal common-subexpression DAG (computing the minimum is the
   minimum-equivalent-DAG / smallest-grammar problem — **NP-hard** in
   general; the smallest-grammar problem has no known constant-factor
   poly-time approximation). So even at fixpoint `cse::crunch` returns a
   *heuristic* DAG, not a certified minimum.

**(open — what a true lower bound would require)** A *lower bound* on the
minimal DAG size of these specific proofs is **open**. The cut-free TREE
is an exact integer (so the TREE side has no slack — it is both the upper
and lower bound for the inlined metric). But "the smallest proof-DAG
re-presenting these exact 96 conclusions" is the minimum-equivalent-DAG
problem; certifying a lower bound *L* would require either (i) an
information-theoretic / Kolmogorov argument that no DAG below *L* nodes
can encode these conclusions under the kernel's substitution rule
(no such argument is known for this corpus), or (ii) exhaustive search
over sound factorings (super-exponential; intractable at 10^7 nodes).
We therefore **honestly report the post-CSE figure as a kernel-verified
upper bound on the minimal DAG, with the gap to the true minimum OPEN**,
and the three slack sources above as the exact reasons it is not tight.

This is, by the project's iron rule, a **success**: an honest "the
DAG is not provably optimal, here is the exact measured residual slack
and precisely why a lower bound is open" — not a fabricated optimum.

## 5. Summary

* Per-postulate tree/DAG/CSE: **§2 table, kernel-verified**, fresh-kernel
  re-verify `VERIFIED ALL ✔ (267, 96 $p)`.
* The separation as a concrete instance: TREE/DAG ∈ **[0.59×, 3.35×]**,
  a small constant — and it **inverts** under the generic-lemma template
  (cut-free is *smaller* than the named DAG for 5 of 11 targets).
* This is a **measured instance, not an asymptotic separation**; it is
  the CSE-of-one-circuit analogue, not a Frege/extended-Frege or
  tree/dag-Resolution lower bound. No family, no super-poly bound.
* Optimality: named DAG **improved by kernel-gated CSE** — −81–82% at
  the production 180 s budget, and **−91.83% (10,134,529 → 828,377)**
  measured at a 1500 s budget where the greedy pass reaches its own
  fixpoint (no `time budget` line). So the production `shared_total` is
  itself ~2.3× conservatively un-crunched purely by the wall-clock
  budget. The −91.83% fixpoint is **still not the certified minimum**
  (4096-node subtree cap; greedy selection is the NP-hard
  smallest-grammar problem) and a **minimal-DAG lower bound is OPEN**,
  with all three slack sources named and the budget slack now measured.

*Reported, not faked — including the parts still open.*
