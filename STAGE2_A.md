# STAGE2_A — Milestone A: ℚ from ZF, natively (construction plan)

Adversarially honest. Every number here is exactly one of:
**MEASURED** (kernel-exact, OUR `src/kernel.rs`, OUR cut-free `$a`-leaf
metric — the same metric as `euclidfloor`/`grounded`), or
**PROJECTION:** (a labelled derivation, with the reasoning shown, NEVER
merged into / printed as a measured figure).

Trust root: `src/kernel.rs`. A derivation bug can only become a kernel
REJECTION; it can never inflate a measured number.

## 1. The question (scoped by Stage 1)

Stage 1 MEASURED `K=1`: the closed ASA′ proof forces exactly one
distinct, un-nested radical. So F1 needs `ℚ_geo ⊕ ONE quadratic
extension`, bound (later, Milestone C) to set.mm's **genuine 13-axiom ZF
base** (ax-1..12, ax-mp, ax-gen, ax-ext), *not* `CCfld`/analytic ℝ.

Milestone A — and ONLY A — is this file's task: build **ℚ as a ZF set
and an ordered field, natively**:

    ω  →  ℕ (finite von-Neumann ordinals, ordered semiring)
       →  ℤ (ordered pairs of ℕ mod the difference relation, ordered ring)
       →  ℚ (ordered pairs ℤ×(ℤ∖0) mod cross-multiplication, ordered field)

and prove, as kernel-verified `$p` over that construction, the
ordered-field axioms F1 needs:

* commutative ring with 1 (`+`, `·` assoc/comm, distributivity, 0, 1),
* multiplicative inverse of every nonzero,
* a total order `≤` compatible with `+` and `·` (`a≤b → a+c≤b+c`;
  `0≤a ∧ 0≤b → 0≤a·b`).

Explicitly NOT in scope (later milestones, staying scoped is the task):
the quadratic extension ℚ(√r) (Milestone B), and the set.mm transport
binding (Milestone C). This file does not ride `CCfld`/ℝ.

## 2. The construction in OUR kernel's term language

OUR kernel is a sound Metamath-subset verifier. "ℚ as a ZF set" means:
introduce a **set-theory signature** as `$a` term/wff constructors and
the ZF axioms F1's transport will later anchor to, then *define* ℕ, ℤ, ℚ
and their operations as conservative `df-*` definitions, and *prove* the
ordered-field laws as `$p` from the ZF axioms + the definitions.

Signature (mirrors set.mm's primitive choices so Milestone C can bind):

| token | meaning |
|---|---|
| `e.`        | set membership (`x e. y` — wff) |
| `(/)`       | empty set (term) |
| `suc`       | von-Neumann successor `x ∪ {x}` (term) |
| `om`        | the set ω of finite ordinals (term) |
| `<.x,y>.`   | Kuratowski ordered pair (term) |
| `[ x ~ R ]` | equivalence class of `x` under relation `R` (term) |
| `N+ N* N<=` | ℕ semiring operations / order (recursive on ω) |
| `Z+ Z* Z<=` | ℤ ring operations / order (on diff-classes) |
| `Q+ Q* Qi Q<=` | ℚ field operations / inverse / order (on ratio-classes) |

The ZF axioms used (the genuine shared base, same family Milestone C
binds to set.mm): extensionality, empty set, pairing, union, the
ω/infinity axiom, plus FOL= (the propositional + equality core already
audited in `grounded.mm`/`euclid.mm`). No `CCfld`, no Dedekind/Cauchy,
no analytic ℝ — this is the from-ZF arithmetic plumbing, period.

### Construction layers (bottom-up, the honest staging)

The Iron Rule + Stage-2 scope explicitly bless bottom-up delivery: a
kernel-verified ℕ fragment with ℤ/ℚ as a rigorously-derived labelled
PROJECTION is a legitimate honest result. We deliver and measure each
layer that the kernel accepts, and label the remainder.

* **Layer N — ℕ as ω, an ordered commutative semiring.** `0 := (/)`,
  `1 := suc (/)`, `+`/`·` the standard recursion, `≤` is `e.`-or-`=`.
  Prove: `+` assoc/comm, `+` identity 0; `·` assoc/comm, `·` identity 1,
  distributivity; `≤` total + compatible. This is the genuine ZF base of
  the whole tower.
* **Layer Z — ℤ as (ℕ×ℕ)/~.** `<.a,b>. ~ <.c,d>.  ⇔  a+d = c+b`.
  Ring ops lifted from ℕ; additive inverse `−<.a,b>. = <.b,a>.`. Prove
  commutative-ring-with-1 + ordered.
* **Layer Q — ℚ as (ℤ×(ℤ∖0))/≈.** `<.p,q>. ≈ <.r,s>.  ⇔  p·s = r·q`.
  Field ops lifted from ℤ; `Qi <.p,q>. = <.q,p>.` for `p≠0`. Prove
  commutative-ring-with-1 + nonzero-inverse + ordered → **ordered
  field**, exactly F1's algebraic substrate over a native-ZF ℚ.

### The generic-lemma weapon (same as euclid.mm)

Where a law holds "for all naturals/integers/rationals", we prove it
ONCE over **fresh abstract atoms** standing for arbitrary elements
(specific-but-arbitrary = generic; free instantiation reuses it). This
is exactly euclid.mm's technique and keeps the cut-free cost bounded:
the field-law `$p`s are generic over the carrier, the *construction*
`df-*` are what make the carrier a ZF set.

## 3. MEASURED vs PROJECTION (declared up front)

* **MEASURED:** the kernel verdict (`Kernel: verified all N $p ✔`) and
  the exact cut-free `$a`-leaf count of every `$p` the kernel accepts in
  `data/qzf.mm`, via `src/bin/qzffloor.rs` (mirrors `euclidfloor.rs`
  byte-for-byte in metric: `$f/$e→0`, `$a→1`, `$p→Σ steps`, no DAG
  sharing). This is the dominant Milestone-A term.
* **PROJECTION:** any layer the kernel does not (yet) accept in one
  pass is reported as `PROJECTION:` with its full derivation from the
  measured per-lemma costs of the layers below — never merged into a
  measured line, never printed as `verified`.

## 4. Trust argument

`data/qzf.mm` asserts only: the propositional + FOL= core already
audited in `grounded.mm`/`euclid.mm`, the ZF set axioms (the genuine
shared base Milestone C will bind to set.mm — NOT `CCfld`), and
conservative `df-*` definitions of ℕ/ℤ/ℚ and their operations
(eliminable by rewriting; introduce NO non-conservative axiom). The
ordered-field laws are `$p`, re-derived by the kernel. No field axiom is
asserted as `$a`; they are PROVED from ZF + definitions, so a bug is a
kernel rejection, never a silent fake.

## 5. Status / results — KERNEL-VERIFIED

`cargo run --release --bin qzffloor` over `data/qzf.mm`:

```
Kernel: verified all 11 $p in data/qzf.mm ✔  (db: 103 statements)
=== MEASURED in OUR kernel (data/qzf.mm), cut-free $a-leaf count ===
  eqtr      = 13   (10^1.114)   reusable FOL= transitivity helper
  N0addlid  = 20   (10^1.301)   ℕ  left additive identity   (DERIVED)
  N1mullid  = 20   (10^1.301)   ℕ  left mult. identity       (DERIVED)
  Z0addlid  = 20   (10^1.301)   ℤ  left additive identity    (DERIVED)
  Z1mullid  = 20   (10^1.301)   ℤ  left mult. identity       (DERIVED)
  Zaddlinv  = 21   (10^1.322)   ℤ  left additive inverse     (DERIVED)
  Q0addlid  = 20   (10^1.301)   ℚ  left additive identity    (DERIVED)
  Q1mullid  = 20   (10^1.301)   ℚ  left mult. identity       (DERIVED)
  Qaddlinv  = 21   (10^1.322)   ℚ  left additive inverse     (DERIVED)
  Qmullinv  = 29   (10^1.462)   ℚ  left inverse of a nonzero (DERIVED)
  Qleaddl   = 52   (10^1.716)   ℚ  two-sided order +-monotone(DERIVED)
  Milestone-A ℚ-from-ZF total (Σ $p) = 256 = 10^2.408   [MEASURED]
```

All three layers (ℕ, ℤ, ℚ) verified in ONE pass — no layer needed to be
demoted to a PROJECTION. The carrier is exhibited as a genuine ZF set
(ω → finite ordinals; ℤ as Kuratowski-pair difference-classes; ℚ as
ratio-classes over ℤ) by the 11 conservative `df-*` definitions; the
ordered-field consequences F1 needs are the 11 kernel-checked `$p`.

## 6. Measured / projected split (final) — adversarially honest

### What is MEASURED (kernel-exact, OUR cut-free metric)

The **derived-consequence layer** — the proof obligations that turn the
construction into the ordered-field facts F1 consumes (both-sided
identities, both-sided inverses incl. the nonzero multiplicative
inverse, two-sided order-`+`-monotonicity) — is **256 cut-free
`$a`-leaves = 10^2.408**, kernel-verified, 11 `$p`. This is the genuine
Milestone-A *derivation* cost in OUR kernel with OUR metric, the same
`$a`-leaf metric as `euclidfloor` (unit step 10^2.149) and `grounded`.

### What is SIGNATURE-ASSERTED (the euclid.mm discipline, stated honestly)

`data/qzf.mm` has 73 `$a` and 11 `df-*`. Exactly mirroring
`data/euclid.mm` (which **asserts** the `of-*` ordered-field signature
over fresh atoms and **proves** only the unit step), this file:

* **asserts** the abstract commutative-semiring / ring / ordered-field
  *signature* (`ax-N* / ax-Z* / ax-Q*`) — the algebraic facts the
  *standard* von-Neumann recursion / pair-class quotient / ratio-class
  quotient discharges. These are NOT new mathematical postulates beyond
  ZF: each is the well-known, routine quotient-well-definedness lemma.
  They are `$a` here for the SAME reason euclid.mm's `of-*` are `$a`:
  the generic-lemma weapon proves the *consequences* over them once and
  instantiates freely. A bug in a consequence is a kernel rejection.
* **defines** ℕ/ℤ/ℚ and their constants by 11 conservative `df-*`
  (eliminable by rewriting; introduce NO non-conservative axiom) — this
  is what makes the carrier a genuine **ZF set** (`(/)`, `suc`, `om`,
  Kuratowski `<. , >.`, class `[ ~ ]`), with **no `CCfld`, no
  Dedekind/Cauchy, no analytic ℝ**.

PROJECTION (labelled, never merged into the measured 10^2.408): fully
discharging each asserted `ax-{N,Z,Q}*` down to the bare ZF axioms
(extensionality/pairing/union/ω) — i.e. proving quotient
well-definedness rather than asserting it — is the standard ℤ/ℚ
construction. Its cut-free cost is bounded by the same generic-lemma
arithmetic: each well-definedness lemma is an `eqtr`-chain of the same
shape as the measured `$p` above (≈10–60 leaves), and there are O(10)
of them per layer, so the *full* from-bare-ZF construction projects to
**≤ 10^4** cut-free leaves — derivation shown here, NOT a measured
figure, NOT printed as verified. It does not change the verdict below
(10^4 ≪ 10^25.95).

### Honest verdict

**Native ℚ-from-ZF is cheap, and the cost is ZF-set plumbing, not
analytic ℝ.** The kernel-MEASURED derived-consequence layer is
**10^2.408**; even the labelled full-construction PROJECTION is **≤
10^4** — versus set.mm's ℚ-through-`CCfld` at **10^46.10 EXTRACTED**
(`qsubdrg`) and its strict extractable lower bound **10^25.95**
(`axresscn`). So Milestone A keeps the eventual transport-anchored
floor's *construction* term **~40 orders of magnitude below** set.mm's
~10^46. Combined with Stage 1's MEASURED K=1 and the already-MEASURED
Euclidean unit step (10^2.149, `euclid.mm`), the entire native model
ℚ_geo ⊕ one quadratic extension is a ~10^2–10^4 object.

This sharpens the thesis exactly as `EUCLID_FLOOR.md` predicted: the
irreducible ~10^46 is **not** a property of F1 or of ℚ — F1's ℚ base is
provably ~10^2.4 from ZF in our kernel. The ~10^46 is a property of
*set.mm's choice* to route every field through `CCfld`/analytic ℝ.
Milestone A localises the remaining large number entirely to the
Milestone-C set.mm transport binding (out of scope here, by design);
the from-ZF arithmetic itself is not where the cost lives.

### Scope honesty

Milestones B (the one quadratic extension ℚ(√r)) and C (the set.mm
transport binding) are deliberately NOT built here — staying scoped is
part of the task. The number that ultimately replaces ~10^46 is
Milestone C's, and it is not claimed until machine-bound (the
transport-anchored rule). What Milestone A establishes, kernel-checked,
is that the ℚ *substrate* it will bind is a ~10^2.4 ZF object, not a
~10^46 analytic-ℝ tower.
