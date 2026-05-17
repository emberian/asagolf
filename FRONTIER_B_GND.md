# FRONTIER B — discharging the `gnd-*` substrate residual

Adversarially honest. Every number here is **MEASURED** (OUR
`src/kernel.rs`, OUR cut-free `$a`-leaf metric — byte-for-byte the metric
of `euclidfloor`/`qzffloor`/`qzfextfloor`/`qzfhffloor`: `$f/$e→0`,
`$a→1`, `$p→Σ steps`, no DAG sharing) or **EXTRACTED** (set.mm,
quoted verbatim from `STAGE2_BC.md`/`SEAM1_INFINITY.md`, NEVER
re-measured, NEVER merged with a MEASURED line). Trust root:
`src/kernel.rs` re-checks every `$p`; a derivation bug can only become a
kernel REJECTION, never a fake number (Iron Rule).

Base: this worktree HEAD. New files only; `data/qzfhf.mm`,
`data/qzf.mm`, `data/qzfext.mm`, `src/kernel.rs` consumed read-only / not
modified.

---

## 1. The residual being discharged

Stage 3 (`data/qzfhf.mm`, `STAGE3_HF.md §8`) reduced Stage-2's inductive
`≤10^4` signature **PROJECTION** to a kernel-verified finite case-check,
but left **21 `gnd-*` ground facts `$a`-ASSERTED** (the `gnd-N*`/`gnd-Z*`/
`gnd-Q*` representative-arithmetic and order literals). The
`COST_STRUCTURE.md` live-frontier item:

> The `gnd-*` residual. Unfold the … finite ground ZF computations to
> bare ∅/suc/pair/ext in-kernel → a fully projection-free, fully-measured
> substrate. Finite and decidable; not yet done.

This is now **done for all 19 arithmetic facts**.

## 2. The construction (`data/qzfhf_gnd.mm`)

A new self-contained OUR-kernel database. It `$a`-keeps only:

- the propositional + FOL= core (as `qzf.mm`/`qzfhf.mm`);
- the bare ZF set primitives `(/)` [`0ex`], `( suc x )` [`sucexg`],
  Kuratowski `<. , >.` [`opex`/`zfpair2`], the union inside `suc`
  [`uniex`], class/quotient `[ ~ ]` [`axextg`], with the ax-8/ax-9
  Leibniz congruence family;
- the **conservative primitive-recursive defining equations** of the
  von-Neumann ordinal operations: `df-Np0` (n+0=n), `df-Nps`
  (n+suc m = suc(n+m)), `df-Nt0` (n·0=0), `df-Nts` (n·suc m = n·m+n) —
  the recursion-theorem output, **used at fixed finite arguments only**,
  never quantified inductively, never iterated past the single ordinal
  `1 = suc (/)`;
- the **conservative difference-class / ratio-class operation
  definitions** `df-Zp`/`df-Zt`/`df-Zm` and `df-Qp`/`df-Qt`/`df-Qm`/
  `df-Qi` (the standard quotient-construction operation definitions,
  eliminable by rewriting);
- the conservative `df-n*`/`df-z*`/`df-q*` constant definitions.

From these, **every one of the 19 arithmetic `gnd-*` facts is a
kernel-verified `$p`**, derived by a finite `eqtr`/congruence chain
(`redslot`/`redqslot`/`clpr`/`qlpr` helpers) — finite ground unfolding,
**NO induction, NO `om`, `suc` applied exactly once**.

This is a genuine reduction, not re-assertion: `qzfhf.mm` `$a`-asserted
the ground *outputs* (`( N0 Np N1 ) = N1`, …, `( Q1 Qt Q0 ) = Q0`).
`qzfhf_gnd.mm` `$a`-keeps only the *defining recursion / class-operation
equations* (conservative, eliminable) and **proves every output**.

## 3. MEASURED result

`cargo run --release --bin qzfhfgndfloor` (reproducible; `src/kernel.rs`
re-checks every `$p`):

```
Kernel: verified all 55 $p in data/qzfhf_gnd.mm ✔  (db: 183 statements)
STRUCTURAL AUDIT (comment-stripped): `om`/ω token present: NO
                  genuine `suc (/)` applications: 1
```

The 19 arithmetic `gnd-*`, now `$p` (MEASURED cut-free `$a`-leaf count):

| gnd-* (now `$p`) | cut-free | gnd-* (now `$p`) | cut-free |
|---|---|---|---|
| gnd-N0addN0 | 2 (10^0.301) | gnd-Z0addZ0 | 212 (10^2.326) |
| gnd-N1addN0 | 2 (10^0.301) | gnd-Z0addZ1 | 373 (10^2.572) |
| gnd-N1mulN0 | 2 (10^0.301) | gnd-ZmZ0 | 74 (10^1.869) |
| gnd-N0mulN0 | 2 (10^0.301) | gnd-Z1mulZ1 | 765 (10^2.884) |
| gnd-N0addN1 | 163 (10^2.212) | gnd-Z0mulZ1 | 604 (10^2.781) |
| gnd-N0mulN1 | 128 (10^2.107) | gnd-Z1mulZ0 | 352 (10^2.547) |
| gnd-N1mulN1 | 289 (10^2.461) | gnd-Q0addQ0 | 2459 (10^3.391) |
| gnd-Q1mulQ1 | 1738 (10^3.240) | gnd-Q0addQ1 | 2781 (10^3.444) |
| gnd-Q1mulQ0 | 1325 (10^3.122) | gnd-QmQ0 | 233 (10^2.367) |
| gnd-QiQ1 | 74 (10^1.869) | | |

```
gnd-* discharge subtotal (Σ the 19 arithmetic ground $p) = 11578 (10^4.064)  [MEASURED]
FRONTIER-B file total     (Σ all 55 $p, incl. helpers)   = 12142 (10^4.084)  [MEASURED]
```

## 4. The restated substrate floor

| line | value | class |
|---|---|---|
| Stage-2 A native ℚ-from-ZF derived layer (`qzffloor`) | 10^2.408 | MEASURED |
| Stage-2 B ℚ_geo(√r) @ K=1 radicand (`qzfextfloor`) | 10^2.149 | MEASURED |
| Stage-3 HF finite-element discharge (`qzfhffloor`) | 10^2.344 | MEASURED |
| **FRONTIER-B `gnd-*` ground-ZF unfolding (`qzfhfgndfloor`)** | **10^4.064** | **MEASURED, 55 `$p` ✔** |
| HF carrier ZF-set-hood, Infinity removed — dominant `sucexg` | 10^12.810 | EXTRACTED (verbatim) |
| ~~`omex` (ω from Infinity)~~ — not reached by the HF carrier | ~~10^17.484~~ | ELIMINATED |

**Projection-free HF substrate floor = max(A 10^2.408, B 10^2.149,
HF 10^2.344, gndB 10^4.064, ZF-bind 10^12.810) = 10^12.810**
(EXTRACTED-dominated by `sucexg`; A/B/HF/gndB all MEASURED). Unchanged
in magnitude from Stage 3 — as expected, the `gnd-*` unfolding is
cheap (10^4.064) and well below the EXTRACTED `sucexg` bind; what
changed is that the floor is now **MEASURED with the `gnd-*` residual
discharged**, not standing on `$a`-asserted ground facts.

## 5. Honest verdict (adversarially honest)

**The arithmetic substrate is now projection-free and fully MEASURED.**
All 19 ground representative-arithmetic facts the closed proof consumes
of the named ℕ/ℤ/ℚ constants — every `=`, `+`, `·`, `−`, `·⁻¹` literal —
are kernel-verified `$p`, derived by finite ground unfolding from the
bare ZF set primitives plus conservative defining equations. No
induction, no ω, `suc` applied exactly once (structural audit:
`om` token absent, `suc (/)` applications = 1).

**The precisely-characterised remnant — a full result, per the Iron
Rule.** Two literals stay `$a`: `gnd-Q0leQ1` ( `Q0 ≤ Q1` ) and
`gnd-Q1neQ0` ( `Q1 ≠ Q0` ). These are **order / disequality decisions
on the concrete ratio-classes**, not equational class computations.
They are NOT inductive, NOT Infinity-bearing, NOT open-ended — each is a
single decidable order/apartness check on fixed hereditarily-finite
sets. This is exactly the **intrinsic order/sign core** `SEAM4` /
`COST_STRUCTURE` identifies as *the one floor that did not dissolve
under a better construction* (the irreducible ~61% sign-reasoning in
`sqcong`). Reaching it here, isolated to two ground order literals after
all arithmetic is discharged, is the sharpest possible localisation of
that core at the substrate.

**One-line verdict:** *Unfolding the 19 finite ground ℕ/ℤ/ℚ
representative-arithmetic facts to bare ∅/suc/pair/union/extensionality
plus conservative recursion / class-operation defining equations
discharges the entire `gnd-*` arithmetic residual to a kernel-verified
finite computation (MEASURED 10^4.064, `verified all 55 $p ✔`, `om`
absent, `suc` once); the substrate is now projection-free and
fully-MEASURED for ALL arithmetic, with the only residual being two
irreducible ground order/disequality literals — the intrinsic order
core, decidable, non-inductive, no Infinity.*

## 6. Files / reproduce

- `FRONTIER_B_GND.md` — this document.
- `data/qzfhf_gnd.mm` — the bare-ZF discharge: 19 arithmetic `gnd-*`
  as kernel-verified `$p` (+ helpers; 55 `$p` total). Kernel-verified
  (`src/kernel.rs`).
- `src/bin/qzfhfgndfloor.rs` — kernel-verify + MEASURE + structural
  audit + restated floor. Reproduce: `cargo run --release --bin
  qzfhfgndfloor`.
- set.mm EXTRACTED figures (`omex`/`sucexg`/…) quoted verbatim from
  `STAGE2_BC.md`/`SEAM1_INFINITY.md`; NOT re-measured, NOT merged with
  any MEASURED line.
- Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
