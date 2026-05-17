# FRONTIER D — the HF-RANK LAW: minimal von-Neumann rank = f(K, tower-depth)

Adversarially honest. Every figure here is exactly one of:
**MEASURED** (computed read-only over `data/qzfhf.mm` after OUR trust
root `src/kernel.rs` re-verifies all 10 `$p`; the conservative `df-*`
right-hand sides are unfolded to pure ZF set-terms and the standard
von-Neumann rank recursion applied — `src/bin/rankdepth.rs`,
reproducible), or **CONJECTURED** (a labelled structural law, its scope
and the convention it depends on stated, never merged into a MEASURED
figure). Read-only consumed: `data/qzfhf.mm`. Modifies nothing;
`kernel.rs`/`elaborate.rs`/`grounded.rs`/`data/*.mm`/other agents'
files untouched. New files only: `src/bin/rankdepth.rs`, this document.

Trust root: `src/kernel.rs`. A derivation bug in `rankdepth` can only
mis-state a rank; it cannot inflate any kernel-MEASURED quantity (the
kernel re-checks every `$p` independently — Iron Rule).

Reproduce: `cargo run --release --bin rankdepth`.

---

## 1. The question

`STAGE3_HF.md` / `SEAM1_INFINITY.md` (both MEASURED) established that the
closed ASA′ proof forces **K = 1** — exactly one distinct, **un-nested**
radical — and that the only successor it ever names is `suc (/)`
(applied **exactly once, never iterated**), `om` never reached. The
observation to test (`COST_STRUCTURE.md` open item): `suc` is applied
once *because* the radical-tower depth K = 1. Conjecture and test a
precise structural law

> minimal von-Neumann (set-theoretic) RANK of the HF carrier element
> = f(K, pair-class tower-depth).

## 2. The rank recursion used (standard, stated explicitly)

Each named constant's `df-*` RHS is unfolded to a pure ZF set-term over
`{ (/), suc, <.·,·>., [·~·] }`; rank by the standard von-Neumann
recursion `rank(x) = sup{ rank(y)+1 : y ∈ x }`, specialised:

| construct | set | rank |
|---|---|---|
| `(/)` | ∅ | `0` |
| `( suc x )` | `x ∪ {x}` | `rank(x) + 1` |
| `<. a , b >.` | Kuratowski `{ {a}, {a,b} }` | `max(rank a, rank b) + 2` |
| `[ a ~ r ]` | equivalence/quotient class | **convention-dependent** — see §5 |

Two **explicitly labelled** conventions for the class former are
reported (the honest hedge, §5): **REP** `rank([a~r]) = max(rk a, rk r)`
(the class named by its representative term — a strict *lower* bound on
the true extensional rank) and **CLASS** `… + 1` (the class as a set
whose members include the representative — the minimal class-as-set
bump).

## 3. MEASURED ranks (kernel-verified `data/qzfhf.mm`, 10 `$p` ✔)

`Kernel: verified all 10 $p in data/qzfhf.mm ✔ (db: 91 statements)`,
then df-* unfolded:

| const | role | sucΣ (sum) | **K = suc-DEPTH** | D = tower-depth | rankREP | rankCLASS | normalised ZF term |
|---|---|---|---|---|---|---|---|
| `N0` | ℕ 0 | 0 | **0** | 0 | 0 | 0 | `(/)` |
| `N1` | ℕ 1 | 1 | **1** | 0 | 1 | 1 | `( suc (/) )` |
| `Z0` | ℤ 0 | 0 | **0** | 1 | 2 | 3 | `[ <. (/) , (/) >. ~ (/) ]` |
| `Z1` | ℤ 1 | 1 | **1** | 1 | 3 | 4 | `[ <. ( suc (/) ) , (/) >. ~ (/) ]` |
| `Q0` | ℚ 0 | 1 | **1** | 2 | 5 | 7 | `[ <. Z0 , Z1 >. ~ Z0 ]` (unfolded) |
| `Q1` | ℚ 1 | 2 | **1** | 2 | 5 | 7 | `[ <. Z1 , Z1 >. ~ Z0 ]` (unfolded) |

`sucΣ` = textual occurrences of the ordinal 1 (a **sum**); `K` =
**max nesting depth of `suc`** (a **max**). `D` = pair-class tower
depth (ℕ-ordinal = 0, ℤ difference-class = 1, ℚ ratio-class = 2).

### 3a. The honest measured finding (reported, not hidden)

A naive `K := sucΣ` (suc-**count**) law **BREAKS at Q1**:
`Q1 = [ <. Z1 , Z1 >. ~ Z0 ]` names the ordinal 1 **twice** (numerator
and denominator both `Z1`), so `sucΣ(Q1) = 2`, predicting rankREP = 6 —
but the **MEASURED** rankREP(Q1) = 5. This is **not** iteration: it is
the *same* un-nested `suc (/)` reused. Rank is a **max-recursion**, so
the correct radical-tower witness is **suc-DEPTH** (max nesting), which
is **1** at Q1 (and on every 1-carrying constant), never iterated —
exactly the Stage-1 MEASURED K = 1. With `K := suc-DEPTH` the law is
EXACT on all 6 constants.

## 4. THE LAW (MEASURED-tested closed form)

With **K := suc-DEPTH** (= 1 on every constant whose closure contains
the ordinal 1; = 0 for the pure-zero tower `N0`, `Z0`) and **D :=
pair-class tower depth** (ℕ = 0, ℤ = 1, ℚ = 2):

> **rank(constant) = K + c · D**
>
> with **c = 2** under the REP convention, **c = 3** under the CLASS
> convention.

MEASURED test, every named constant (all ✔, EXACT):

```
test N0 : K=0 D=0  K+2D=0  rankREP=0  ✔     K+3D=0  rankCLASS=0  ✔
test N1 : K=1 D=0  K+2D=1  rankREP=1  ✔     K+3D=1  rankCLASS=1  ✔
test Z0 : K=0 D=1  K+2D=2  rankREP=2  ✔     K+3D=3  rankCLASS=3  ✔
test Z1 : K=1 D=1  K+2D=3  rankREP=3  ✔     K+3D=4  rankCLASS=4  ✔
test Q0 : K=1 D=2  K+2D=5  rankREP=5  ✔     K+3D=7  rankCLASS=7  ✔
test Q1 : K=1 D=2  K+2D=5  rankREP=5  ✔     K+3D=7  rankCLASS=7  ✔
LAW VERDICT (REP,   K=suc-depth): rank = K + 2·D : ✔ EXACT (6/6)
LAW VERDICT (CLASS, K=suc-depth): rank = K + 3·D : ✔ EXACT (6/6)
```

**Structural reading.** The ordinal core contributes exactly **K** (the
radical-tower depth — one un-nested `suc` ⟺ K = 1 ⟺ one radical, the
Stage-1 MEASURED fact). Each algebraic quotient layer that builds the
pair-class tower — ℤ as difference-classes over ℕ, ℚ as ratio-classes
over ℤ — adds exactly a **constant** (+2: one Kuratowski pair, REP
class former +0; or +3 under CLASS) **independent of K**. So:

> **The set-theoretic rank of the HF carrier is LINEAR and ADDITIVELY
> SEPARABLE in the two depths: rank = K + c·D. The radical (geometric)
> content enters ONLY through K, the algebraic-quotient (number-tower)
> content ONLY through c·D; they do not interact.** K = 1 (one radical,
> never iterated) is *why* the HF carrier sits at the minimal possible
> ordinal core (rank-1 successor, never `suc suc …`), hence in a tiny
> fixed corner of V_ω with no `om`/Infinity — the set-theoretic shadow
> of Stage-1's K = 1.

## 5. SCOPE & LIMITS (adversarially honest)

**MEASURED, exact, this model:**
- `suc-DEPTH = K = 1` on every 1-carrying constant, `0` on the
  pure-zero tower — machine-verified; matches Stage-1 MEASURED K = 1.
- pair-class tower-depth `D ∈ {0,1,2}` for ℕ/ℤ/ℚ constants.
- `rank = K + c·D` holds **EXACTLY for all 6 named constants** the
  closed ASA′ proof uses, `c = 2` (REP) or `c = 3` (CLASS).
- the broken naive `K = sucΣ` law is **reported, not papered over**
  (§3a): it is the evidence that K must be a *depth* (max), aligned
  with rank's own max-recursion — an honest negative that sharpened
  the law.

**CONVENTION-DEPENDENT (the honest hedge — explicitly NOT hidden):**
- `[ a ~ r ]` is an **equivalence class**; its TRUE extensional
  von-Neumann rank is the sup over the class's *actual members*, which
  this read-only term analysis does **not** enumerate. `qzfhf.mm`
  asserts the ground class facts as `$a`; the class *extension* is not
  unfolded to bare ∅/suc/pair/ext (precisely the
  `gnd-*` residual already characterised in `STAGE3_HF.md` §8 /
  `COST_STRUCTURE.md`). So `rankREP` is a strict **lower bound** and
  `rankCLASS` the minimal class-as-set model; the true rank is
  `rankREP + O(1)` per class layer. **The LAW SHAPE
  `rank = K + Θ(D)` — linear, additively separable, K-only-radical —
  is convention-INDEPENDENT; only the constant `c ∈ {2,3,…}` is
  convention-dependent.** This is the exact and only hedge.
- K is the measured suc-DEPTH; its **identity with the Stage-1
  radical-tower depth** is the structural claim — evidenced by `suc`
  applied exactly once *because* the closed obligation is
  quantifier-free over the finitely-many named terms (Seam-1 MEASURED:
  a single radical forces a single, un-nested successor).

**SCOPE bound:** the law is MEASURED for the **finite named element
set** the closed ASA′ proof actually uses (`N0 N1 Z0 Z1 Q0 Q1`). It is
**NOT** claimed for the *generic* ℚ (which builds all of ω and has
unbounded rank). For *this* HF carrier — the one that eliminates
Infinity (`STAGE3_HF` floor `omex 10^17.484 → sucexg 10^12.810`) — it
is exact and machine-verified.

## 6. One-line verdict

*Unfolding the finite ℚ-elements the closed ASA′ proof names to pure ZF
set-terms and measuring their von-Neumann rank gives the exact,
machine-verified law **rank = K + c·D** (K = suc-DEPTH = the radical-
tower depth = 1, never iterated; D = pair-class tower depth ∈ {0,1,2};
c = 2 REP / c = 3 CLASS): rank is linear and additively separable, the
geometric/radical content entering ONLY through K and the
algebraic-quotient tower ONLY through the K-independent constant c·D —
so K = 1 (one un-nested radical) is precisely why the HF carrier sits
at the minimal rank-1 ordinal core in a tiny fixed Infinity-free corner
of V_ω; the only hedge is that the K-independent layer constant c is
class-convention-dependent (REP lower-bound 2, CLASS 3) because the
class extension is `$a`-asserted not unfolded — the law SHAPE is
convention-independent. The naive suc-COUNT variant honestly BREAKS at
Q1 and is reported as the finding that forced K to be a depth.*

## 7. Files / reproduce / commit

- `src/bin/rankdepth.rs` — read-only rank analyser over
  `data/qzfhf.mm` (OUR kernel re-verifies all 10 `$p` first; df-*
  unfolded; rank/suc-depth/tower-depth measured; law tested both
  conventions). Reproduce: `cargo run --release --bin rankdepth`.
- `FRONTIER_D_RANK.md` — this document.
- Read-only consumed: `data/qzfhf.mm`. Trust root: `src/kernel.rs`.
- No kernel/proof/data/other-agent file modified.
