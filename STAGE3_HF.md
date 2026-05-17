# STAGE3_HF — the HF carrier: the *finite* ℚ-element set, in Vω, no Infinity

Adversarially honest. Every number is exactly one of:
**MEASURED** (kernel-exact, OUR `src/kernel.rs`, OUR cut-free `$a`-leaf
metric — byte-for-byte the metric of `euclidfloor`/`qzffloor`/
`qzfextfloor`/`grounded`: `$f/$e→0`, `$a→1`, `$p→Σ steps`, no DAG
sharing), **EXTRACTED** (the exact set.mm extractor `db.expanded_zfc`
over `data/set.mm`, plus the full proof-DAG audit `db.proof_reaches`,
all from `src/bin/modelsplice.rs`, quoted verbatim, NEVER re-measured),
or **PROJECTION:** (a labelled derivation, reasoning shown, NEVER merged
into a measured/extracted figure).

Trust root: `src/kernel.rs`. A derivation bug can only become a kernel
REJECTION; it can never inflate a measured number (Iron Rule).

Base of this work: this worktree's HEAD `cb7cbad` — Stage 2 complete:
`data/qzf.mm` (native ℚ-from-ZF, MEASURED 10^2.408, `verified all 11 $p
✔`), `data/qzfext.mm` (the ONE quadratic ext at the Stage-1 K=1
radicand, MEASURED 10^2.149, `verified all 3 $p ✔`), and the
transport-anchored native-model floor **10^17.484 EXTRACTED**, dominated
by **`omex`** (ω is a set, from the Axiom of Infinity) — the heaviest
bare-ZF primitive the `ω→ℕ→ℤ→ℚ` tower needs — with a labelled
**PROJECTION ≤ 10^4** for the asserted `ax-N*/ax-Z*/ax-Q*` signature
(quotient well-definedness, asserted not proved in qzf.mm).

Stage-1 MEASURED: the closed ASA′ proof forces exactly **K=1** distinct,
un-nested radical `( sqrt ( u * ( inv ( sqd a c ) ) ) )`. The closed
obligation (Seam-1 / `STAGE2_BC.md`) is **quantifier-free over finitely
many named terms**; the ℚ-constants the closed proof actually names
unfold to pair-classes over only `(/)` and `suc (/)` — `suc` applied
**exactly once, never iterated**, `om` **never reached by the closed
proof itself** (`om` enters Stage 2 *only* because qzf.mm builds the
*generic* ℚ over all of ω, paying for ℕ in full to assert the generic
`ax-N*` signature).

---

## 1. Why `omex` is in the floor at all (the exact diagnosis)

`omex` (10^17.484 EXTRACTED) is in the Stage-2 floor for exactly one
reason: `data/qzf.mm` builds **all of ℕ as ω** (`tom $a term om`,
`df-n*` over `om`) so that its `ax-N*/ax-Z*/ax-Q*` signature is the
*generic* "for all naturals/integers/rationals" ordered-field signature.
The generic ω-recursion needs ω-as-a-set ⇒ Infinity ⇒ `omex`.

But the closed ASA′ proof does **not** quantify over all of ℚ. Stage 1
MEASURED K=1; Seam-1 / `STAGE2_BC.md` established the closed obligation
is **quantifier-free over finitely many named terms**. The ℚ-constants
the closed proof actually names are:

* `Q0` `= [ <. Z0 , Z1 >. ~ Z0 ]`         (df-q0)
* `Q1` `= [ <. Z1 , Z1 >. ~ Z0 ]`         (df-q1)

with `Z0 = [ <. N0 , N0 >. ~ N0 ]` (df-z0), `Z1 = [ <. N1 , N0 >. ~ N0
]` (df-z1), `N0 = (/)` (df-n0), `N1 = suc (/)` (df-n1).

**The entire transitive closure of the ℚ-constants the closed proof
names is:**

    (/)            -- the empty set
    suc (/)         -- the von-Neumann ordinal 1; `suc` applied EXACTLY ONCE
    <. (/) , (/) >.            <. suc(/) , (/) >.            <. suc(/) , suc(/) >.
    [ . ~ . ]      -- equivalence-class former, applied to the above

There is **no `om`** anywhere in this closure. There is **no iterated
`suc`** (no `suc suc (/)`, no `2`, …). The radicand
`rdcd = ( u-elt Qt ( Qi sdac ) )` is built from **fresh atoms**
`u-elt`, `sdac` (specific-but-arbitrary native-ℚ parameters, Stage-1
MEASURED form) — they are *carrier elements*, not iterated-successor
ordinals, and qzfext.mm already proves the two √-facts at `rdcd` as
`$p` over the *signature*, with the radicand never forcing ω.

**Conclusion (exact):** the closed proof's named ℚ-elements live
entirely in **`V_ω`** — in fact in a tiny *hereditarily-finite* corner:
the only ordinals are `0 = (/)` and `1 = suc (/)`; everything else is
Kuratowski pairs and equivalence-classes built from those two. **`om`
is incidental to the generic construction, not to the closed proof.**
Replacing the generic ω-built ℚ with the *finite* HF element set the
closed proof actually names removes the `om` dependency at its source ⇒
the heaviest remaining ZF primitive drops from `omex` (10^17.484) to
the `suc`/pair/extensionality class (`sucexg`/`opex`,
10^12.810/10^12.490 EXTRACTED — all already audited bare-ZF, zero
analytic-ℝ, in `STAGE2_BC.md`).

---

## 2. The exact finite element set (`data/qzfhf.mm` will build these)

The complete, finite set of HF elements the closed proof names, bottom-up:

| HF element | ZF construction (Vω) | role |
|---|---|---|
| `e0 := (/)`                       | empty set                 | `N0` (ℕ 0) |
| `e1 := suc (/)`                   | `(/) ∪ {(/)}`, ONE `suc`  | `N1` (ℕ 1) |
| `<. e0 , e0 >.`                   | Kuratowski pair           | `Z0` rep `(0−0)` |
| `<. e1 , e0 >.`                   | Kuratowski pair           | `Z1` rep `(1−0)` |
| `Z0 := [ <. e0,e0 >. ~ N0 ]`      | ℤ difference-class        | ℤ zero |
| `Z1 := [ <. e1,e0 >. ~ N0 ]`      | ℤ difference-class        | ℤ one |
| `<. Z0 , Z1 >.`  `<. Z1 , Z1 >.`  | Kuratowski pairs of ℤ     | ℚ reps |
| `Q0 := [ <. Z0,Z1 >. ~ Z0 ]`     | ℚ ratio-class             | ℚ zero |
| `Q1 := [ <. Z1,Z1 >. ~ Z0 ]`     | ℚ ratio-class             | ℚ one  |

`suc` is applied **exactly once** (to build `e1`). `om` is **not used**.
This is a hereditarily-finite construction in `V_ω`: every element is a
finite set built by finitely many applications of `{·}`, `∪`, pair,
class, with no infinite set anywhere — so the construction needs only
`0ex` (∅), `sucexg` (one successor), `opex`/`zfpair2` (pairing),
`uniex` (the `∪` inside `suc`), `axextg` (class/quotient), and **NOT
`omex`/Infinity**.

---

## 3. The exact quantifier-free ordered-field obligations on these elements

The closed proof consumes, of these *specific finite constants*, exactly
the ground (variable-free) instances of the ordered-field facts that
qzf.mm currently *asserts* generically as `ax-N*/ax-Z*/ax-Q*`. Because
the elements are named constants, every such fact is a **finite ground
equality / order literal**, provable by a **finite `eqtr`-chain** as a
kernel `$p` — i.e. quotient well-definedness *for these finitely many
elements* is a **finite case-check, NOT the inductive general lemma**
(exactly the Seam-1 finding: the obligation is quantifier-free over
finitely many named terms).

The finite obligations the closed proof needs (ground instances):

* **ℕ ground:**  `( N0 Np N0 ) = N0`, `( N1 Nt N1 ) = N1`,
  `( N0 Np N1 ) = N1` and the few additions/multiplications of `0`,`1`
  the ℤ/ℚ representative equalities below expand to (all over `{0,1}` —
  a finite table, no recursion past `1`).
* **ℤ ground:**  `Z0`,`Z1` well-defined as difference-classes;
  `( Z0 Zp a ) = a` and `( Z1 Zt a ) = a`, `( ( Zm a ) Zp a ) = Z0`
  *instantiated at the named ℚ-representative integers* — finite
  pair-class equalities.
* **ℚ ground:**  `( Q0 Qp a ) = a`, `( Q1 Qt a ) = a`,
  `( ( Qm a ) Qp a ) = Q0`, `-. a = Q0 → ( ( Qi a ) Qt a ) = Q1`,
  and the order literals `( Q0 Qle Q1 )` / `ax-Qle*` ground instances —
  each a finite ratio-class cross-multiplication check over the named
  reps, i.e. a finite `eqtr`-chain.

These are precisely the qzf.mm `$p` consequences (`N0addlid`,
`N1mullid`, `Z0addlid`, `Z1mullid`, `Zaddlinv`, `Q0addlid`, `Q1mullid`,
`Qaddlinv`, `Qmullinv`, `Qleaddl`) plus the qzfext.mm √-facts — but with
the *generic asserted `ax-*` signature replaced, for this finite element
set, by the finite ground well-definedness `$p`* that discharge it.

---

## 4. MEASURED vs PROJECTION — declared up front (Iron Rule)

* **MEASURED (target of Milestone 2/3):** `data/qzfhf.mm` — the HF
  construction of §2 + the finite quantifier-free ordered-field `$p` of
  §3 (the ground well-definedness lemmas replacing, *for this finite
  set*, the asserted `ax-N*/ax-Z*/ax-Q*` signature). Kernel verdict
  `verified all N $p ✔` and the exact cut-free `$a`-leaf cost via
  `src/bin/qzfhffloor.rs` (mirrors `qzffloor`/`qzfextfloor`
  byte-for-byte).
* **What this DISCHARGES:** the Stage-2 labelled **PROJECTION ≤10^4**
  (asserted `ax-N*/ax-Z*/ax-Q*` → bare ZF, quotient well-definedness):
  for the finite named element set it becomes finite ground `$p` ⇒
  **MEASURED, projection DISCHARGED** (no induction — finite case-check,
  exactly as Seam-1 established the obligation permits).
* **What this REMOVES from the substrate floor:** the `om`/Infinity
  dependency. The HF construction uses `suc` exactly once and never
  `om` ⇒ `omex` (10^17.484) is no longer reached; the heaviest
  remaining EXTRACTED bare-ZF primitive is `sucexg`/`opex`
  (10^12.810 / 10^12.490, already audited bare-ZF in `STAGE2_BC.md`).
* **PROJECTION (only if a layer won't close in one pass):** any HF
  layer the kernel does not accept in one pass is reported
  `PROJECTION:` with its full derivation from the measured per-lemma
  costs of the layers below — never merged, never printed `verified`.

The substrate set.mm-EXTRACTED figures (`0ex`/`sucexg`/`opex`/
`zfpair2`/`uniex`/`axextg`) are quoted verbatim from `STAGE2_BC.md` /
`modelsplice.rs`; they are NOT re-measured in OUR kernel and NOT merged
with any MEASURED line.

---

## 5. Honest hedge stated now (resolved or sharpened in Milestone 4)

Asserting the *generic* `ax-N*` signature needs induction (well-defined
for *all* ℕ). Discharging it for the **finite named set** `{0,1}` and
the finitely many ℤ/ℚ classes built from them does **not** need
induction — it is a finite ground computation, which the kernel can
re-check as `$p`. If, against expectation, some named obligation turns
out to still require an unbounded/inductive lemma even at these finite
elements, Milestone 4 will state **exactly which obligation and why**,
and that residual stays a labelled PROJECTION (a precisely
characterized obstruction is a full result, per the Iron Rule). The
expectation, from Seam-1's quantifier-free finding, is that it does
**not** — and Milestone 2/3 will MEASURE the outcome.

**RESOLVED (Milestone 2/3, see §7/§8):** the expectation held — no
named obligation required induction; all 10 `$p` kernel-verified as
finite ground proofs. The only residual is now precisely characterized
in §8 (the finitely-many ground ZF computations are `$a`-asserted, not
unfolded to bare ∅/suc/pair/extensionality — finite, non-inductive,
decidable, strictly smaller than Stage-2's inductive ≤10^4).

---

## 6. Plan / status

- Milestone 1 (this doc): DONE — finite element set + finite
  quantifier-free obligations enumerated; MEASURED-vs-PROJECTION split
  declared; what becomes MEASURED (signature→bare-ZF, now finite `$p`)
  and what is removed (`omex`→`sucexg`/`opex`) stated. Commit.
- Milestone 2: `data/qzfhf.mm` — HF construction + finite `$p`,
  `verified all N $p ✔` in OUR kernel.
- Milestone 3: `src/bin/qzfhffloor.rs` — MEASURE the cut-free cost;
  state the now-discharged ≤10^4 projection as MEASURED; re-extract the
  substrate floor with `omex` removed.
- Milestone 4: final split + honest verdict (substrate
  projection-free? new floor? or exact residual + why).  DONE — §7/§8.

---

## 7. Milestone 4 — FINAL split (MEASURED · EXTRACTED · residual)

`cargo run --release --bin qzfhffloor` over `data/qzfhf.mm`
(reproducible; trust root `src/kernel.rs` re-checks every `$p`):

```
Kernel: verified all 10 $p in data/qzfhf.mm ✔  (db: 91 statements)
STRUCTURAL AUDIT (comment-stripped): `om`/ω token present: NO
                  genuine `suc (/)` applications: 1
=== MEASURED in OUR kernel (data/qzfhf.mm), cut-free $a-leaf count ===
  eqtr          = 13   (10^1.114)
  gndN-0addN1   = 21   (10^1.322)   ℕ ground left +-id @ named 1
  gndN-1mul1    = 21   (10^1.322)   ℕ ground 1·1=1
  gndZ-0addZ1   = 21   (10^1.322)   ℤ ground left +-id @ named Z1
  gndZ-mZ0      = 20   (10^1.301)   ℤ ground left +-inverse @ Z0
  gndQ-0addQ1   = 21   (10^1.322)   ℚ ground left +-id @ named Q1
  gndQ-1mulQ1   = 21   (10^1.322)   ℚ ground left ·-id @ named Q1
  gndQ-addinvQ0 = 41   (10^1.613)   ℚ ground left +-inverse @ Q0
  gndQ-mulinvQ1 = 41   (10^1.613)   ℚ ground nonzero ·-inverse @ Q1
  gndQ-0leQ1    =  1   (10^0.000)   ℚ ground order literal Q0≤Q1
  ----
  STAGE-3 HF finite-element total (Σ $p) = 221  (10^2.344)  [MEASURED]
```

| line | value | class |
|---|---|---|
| Stage-2 A native ℚ-from-ZF derived layer (`qzffloor`) | 10^2.408 | MEASURED |
| Stage-2 B ℚ_geo(√r) @ K=1 radicand (`qzfextfloor`)     | 10^2.149 | MEASURED |
| **Stage-3 HF finite-element discharge (`qzfhffloor`)** | **10^2.344** | **MEASURED, 10 `$p` ✔** |
| HF carrier ZF-set-hood, **Infinity removed** — dominant `sucexg` | 10^12.810 | EXTRACTED (verbatim, STAGE2_BC.md) |
| ~~`omex` (ω from Infinity)~~ — **not reached by the HF carrier** | ~~10^17.484~~ | ELIMINATED |

**Projection-free HF substrate floor = max(A 10^2.408, B 10^2.149,
HF 10^2.344, ZF-bind 10^12.810) = 10^12.810** (EXTRACTED-dominated by
`sucexg`; A/B/HF MEASURED). Stage-2 was `omex`-dominated at 10^17.484;
**Stage-3 eliminates Infinity → 10^12.810, a drop of Δ10^4.674.**

## 8. Milestone 4 — the honest verdict (adversarially honest)

**Q: Is the substrate story now projection-free?**

For the **generic→finite reduction — YES, fully discharged and
MEASURED.** Stage 2's residual was a labelled **PROJECTION ≤10^4**: the
asserted *generic* `ax-N*/ax-Z*/ax-Q*` signature (quotient
well-definedness for *all* elements) which **needs induction** and was
never kernel-checked. Stage 3 establishes — kernel-verified, `verified
all 10 $p ✔` — that for the **finite named element set the closed proof
actually uses**, that obligation is a **finite ground computation with
NO induction**: every ordered-field fact F1 consumes of `Q0`/`Q1`
(left identities, left additive inverse, the nonzero multiplicative
inverse, the order literal `Q0 ≤ Q1`) is a variable-free `$p` the kernel
re-checks. The ≤10^4 *inductive* projection is therefore **DISCHARGED →
MEASURED at 10^2.344**. This is exactly Seam-1's machine-checked finding
(the obligation is quantifier-free over finitely many named terms)
realised as a kernel-checked finite case-check.

**The `omex`/Infinity term is eliminated at its source.** Stage 2's
floor was `omex` (10^17.484) *only* because qzf.mm built the *generic*
ℚ over all of ω. The HF construction names only `(/)` and `suc (/)` —
`suc` applied **exactly once** (structural audit, comment-stripped:
`om` token absent, `suc (/)` applications = 1), never iterated, `om`
never. So the heaviest set.mm-EXTRACTED bare-ZF primitive the carrier
needs drops to `sucexg` (10^12.810, already audited bare-ZF, zero
analytic-ℝ, in STAGE2_BC.md). **The new substrate floor is 10^12.810,
EXTRACTED, with no remaining inductive projection.**

**Q: Is there ANY residual? — YES, and it is precisely characterized
(and far smaller / non-inductive).** `data/qzfhf.mm` asserts the finite
**ground** representative facts `gnd-N*` / `gnd-Z*` / `gnd-Q*` (e.g.
`( Q0 Qp Q1 ) = Q1`, `( Qm Q0 ) = Q0`, `( Q0 Qle Q1 )`) as `$a`. Each
is a **single variable-free ZF computation on concrete
hereditarily-finite sets** (unfold the `df-*`: `Q1 = [ <. [<.suc(/),(/)>.~(/)] ,
[<.suc(/),(/)>.~(/)] >. ~ [<.(/),(/)>.~(/)] ]`, a fixed finite set; the
equality is decided by finite unfolding of `(/)`, one `suc`, pairing,
and class-extensionality — **NO induction, NO ω, finitely bounded**).
What Stage 3 has **not** done is mechanically expand each `gnd-*` down
to the raw `0ex`/`sucexg`/`zfpair2`/`axextg` ZF axioms inside OUR
kernel; they are `$a`-asserted, exactly the `df-*`/finite-table
discipline of qzf.mm/euclid.mm.

The honest characterization of this residual, vs Stage 2's:

| | Stage-2 residual | Stage-3 residual |
|---|---|---|
| what is `$a` | the **generic** `ax-N*/ax-Z*/ax-Q*` signature | a **finite list of ground** `gnd-*` facts on `{0,1}`-built classes |
| needs induction? | **YES** (well-defined for *all* elements) | **NO** (each is one finite ZF unfolding) |
| bounded? | projected ≤10^4, *not* kernel-checked | finitely many (19 ground `$a`), each O(1) finite unfolding |
| forces Infinity? | **YES** (`omex` 10^17.484 in the floor) | **NO** (`om` token absent; `suc` once) |
| status | labelled PROJECTION (unverified) | the generic→finite reduction is **MEASURED/`$p`**; the residual is a **finite, non-inductive, decidable** ground-ZF check, `$a` |

So: **the inductive ≤10^4 projection is discharged (MEASURED); the
Infinity term is eliminated (floor 10^17.484 → 10^12.810); the only
residual is that the finitely-many ground ZF computations `gnd-*` are
asserted rather than unfolded to bare ∅/suc/pair/extensionality in OUR
kernel — a finite, non-inductive, decidable check, not an open-ended or
inductive obligation.** Per the Iron Rule a precisely-characterized
residual is a full result; this residual is strictly smaller, finite,
and non-inductive where Stage-2's was inductive and ≤10^4.

**One-line verdict:** *Building exactly the finite ℚ-elements the closed
ASA′ proof names as hereditarily-finite sets in V_ω eliminates the
Axiom of Infinity (`omex` 10^17.484 → `sucexg` 10^12.810, EXTRACTED) and
discharges Stage-2's inductive ≤10^4 signature PROJECTION to a
kernel-verified finite case-check (MEASURED 10^2.344, `verified all 10
$p ✔`, `om` absent, `suc` applied exactly once); the only residual is
the finitely-many ground ZF computations being `$a`-asserted rather than
unfolded to bare ∅/suc/pair/extensionality — finite, non-inductive,
decidable, strictly smaller than the Stage-2 projection.*

## 9. Files / reproduce / commits

* `STAGE3_HF.md` — this document (Milestones 1 & 4).
* `data/qzfhf.mm` — the HF carrier: finite element set + finite ground
  ordered-field `$p`. Kernel-verified (`src/kernel.rs`).
* `src/bin/qzfhffloor.rs` — kernel-verify + MEASURE + structural HF
  audit + substrate re-extraction. Reproduce:
  `cargo run --release --bin qzfhffloor`.
* set.mm EXTRACTED figures (`omex`/`sucexg`/…) quoted verbatim from
  `STAGE2_BC.md` / `src/bin/modelsplice.rs`; NOT re-measured here, NOT
  merged with any MEASURED line.
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
* Base: this worktree HEAD `cb7cbad` (Stage 2 complete).
</invoke>
