# CLOSURE — the two order literals (the FINAL substrate residual)

Adversarially honest. Every number is **MEASURED** (OUR `src/kernel.rs`,
OUR cut-free `$a`-leaf metric — byte-for-byte the metric of
`euclidfloor`/`qzffloor`/`qzfextfloor`/`qzfhffloor`/`qzfhfgndfloor`:
`$f/$e→0`, `$a→1`, `$p→Σ steps`, no DAG sharing) or **EXTRACTED**
(set.mm, quoted verbatim, NEVER re-measured, NEVER merged with a MEASURED
line). Trust root: `src/kernel.rs` re-checks every `$p`; a derivation
bug can only become a kernel REJECTION, never a fake number (Iron Rule).

Base: this worktree HEAD. New files only
(`data/qzfhf_ord.mm`, `src/bin/qzfhfordfloor.rs`, this doc).
`data/qzfhf*.mm`, `data/grounded.mm`, `src/kernel.rs` consumed
read-only / not modified.

---

## 1. The residual being closed

Frontier B (`FRONTIER_B_GND.md`, `data/qzfhf_gnd.mm`) discharged ALL 19
ground **arithmetic** `gnd-*` facts to kernel-verified `$p` from bare ZF.
After that, the **entire** remaining substrate residual was **exactly two
literals**, still `$a`:

> `gnd-Q0leQ1 : ( Q0 Qle Q1 )`  ( 0/1 ≤ 1/1 )
> `gnd-Q1neQ0 : -. Q1 = Q0`     ( 1/1 ≠ 0/1 )

on the concrete hereditarily-finite ratio-classes
`Q0=[<.Z0,Z1>.~Z0]`, `Q1=[<.Z1,Z1>.~Z0]`,
`Z0=[<.N0,N0>.~N0]`, `Z1=[<.N1,N0>.~N0]`,
`N0=(/)`, `N1=( suc (/) )`.

Frontier C (`FRONTIER_C_ORDERCORE.md`) had independently **PROVEN** that
the order predicate is *logically essential* — no set of ring identities
of any degree can express the order-core (`sqcong`'s `u²=v²→u=v` is false
in ℤ/8; its kernel `x²=0→x=0` false in ℤ/4), localised to the single
named axiom `of-letot`.

This document **closes the loop**: it discharges *both* order literals as
kernel-verified `$p` — and shows the discharge **consumes precisely
`of-letot`'s bare-ZF reflection**, i.e. exactly the C-proven-intrinsic
ingredient. Outcome (a): DISCHARGED.

## 2. The construction (`data/qzfhf_ord.mm`)

A new self-contained OUR-kernel database. The ratio-class order `Qle` is
introduced as a **conservative, eliminable definition**, relayed down
through the difference-class and von-Neumann ordinal layers:

- `df-Qle1` : `( [<.a,Z1>.~Z0] Qle [<.c,Z1>.~Z0] ) <-> ( a Zle c )`
  (canonical denominator `Z1`; Frontier-D K=1 says every named constant
  has denominator `Z1` / offset `N0`).
- `df-Zle1` : `( [<.a,N0>.~N0] Zle [<.c,N0>.~N0] ) <-> ( a Nle c )`.
- `df-Nle`  : `( x Nle y ) <-> ( ( x e. y ) \/ x = y )`
  (von-Neumann ordinal ≤ = membership-or-equality).
- `df-Qne1`/`df-Zne1` : the **contrapositive constructor-injectivity**
  criteria `( -. a = c -> -. C(a) = C(c) )` — pure equational/extensional
  content (the constructor is injective in its first coordinate), NO
  order content.

Each `df-*` is conservative and eliminable by rewriting; none asserts an
order *fact*. From these, **both order literals are kernel-verified
`$p`**, by a finite ground unfolding (Leibniz equality-logic congruence
chains — the ax-8/ax-9 family, exactly `data/grounded.mm`'s `cong-le*`
discipline) down to **two — and only two — primitive bare-ZF
von-Neumann order/foundation facts kept `$a`**:

| primitive `$a` | statement | what it is |
|---|---|---|
| `el-0-suc` | `( (/) e. ( suc (/) ) )` | the von-Neumann reflection of the **ORDER** axiom `of-letot` (totality/positivity: `0 < 1`) |
| `ne-suc-0` | `-. ( suc (/) ) = (/)` | ordinal **irreflexivity / Foundation** (the successor of a set is never that set: `1 ≠ 0`) |

`gnd-Q0leQ1` relays `Qle → Zle → Nle → ( ∈ ∨ = )` and bottoms at
`el-0-suc`. `gnd-Q1neQ0` relays the contrapositive injectivities
`df-Qne1 → df-Zne1` and bottoms at `ne-suc-0`. NO induction, NO `om`;
the single ordinal `suc (/)` appears (3 textual occurrences: `df-n1`'s
RHS + its two `eqsym` rewrites) and is **never iterated** (machine-checked:
no `suc ( suc`).

This is a genuine reduction, not re-assertion: `qzfhf*.mm` `$a`-asserted
the *outputs* `( Q0 Qle Q1 )` and `-. Q1 = Q0` directly. `qzfhf_ord.mm`
`$a`-keeps only the *conservative order/injectivity definitions* plus the
two bare von-Neumann order/foundation primitives, and **proves both
outputs**.

## 3. MEASURED result

`cargo run --release --bin qzfhfordfloor` (reproducible; `src/kernel.rs`
re-checks every `$p`):

```
Kernel: verified all 23 $p in data/qzfhf_ord.mm ✔  (db: 113 statements)
STRUCTURAL AUDIT: `om`/ω present: NO ; `suc` all the single ordinal
                  `suc (/)` (3 occ.), NEVER iterated: confirmed
ORDER-AXIOM DEPENDENCY: el-0-suc present-as-$a: YES
                        ne-suc-0 present-as-$a: YES
gnd-Q0leQ1 : now `$p` (was `$a`) ✔
gnd-Q1neQ0 : now `$p` (was `$a`) ✔
```

| now `$p` | cut-free `$a`-leaf |
|---|---|
| `gnd-N0leN1` | 68 (10^1.833) |
| `gnd-N1neN0` | 49 (10^1.690) |
| `gnd-Z0leZ1` | 148 (10^2.170) |
| `gnd-Z1neZ0` | 135 (10^2.130) |
| **`gnd-Q0leQ1`** | **228 (10^2.358)**  [ORDER LITERAL DISCHARGED] |
| **`gnd-Q1neQ0`** | **221 (10^2.344)**  [ORDER LITERAL DISCHARGED] |

```
order-literal discharge subtotal (gnd-Q0leQ1 + gnd-Q1neQ0) = 449  (10^2.652)  [MEASURED]
qzfhf_ord file total (Σ all 23 $p, incl. helpers)          = 1034 (10^3.015)  [MEASURED]
```

## 4. The now-fully-closed substrate floor

| line | value | class |
|---|---|---|
| Stage-2 A native ℚ-from-ZF derived layer (`qzffloor`) | 10^2.408 | MEASURED |
| Stage-2 B ℚ_geo(√r) @ K=1 radicand (`qzfextfloor`) | 10^2.149 | MEASURED |
| Stage-3 HF finite-element discharge (`qzfhffloor`) | 10^2.344 | MEASURED |
| FRONTIER-B `gnd-*` arithmetic discharge (`qzfhfgndfloor`) | 10^4.064 | MEASURED |
| **CLOSURE order-literal discharge (`qzfhfordfloor`)** | **10^2.652** | **MEASURED, 23 `$p` ✔** |
| HF carrier ZF-set-hood, Infinity removed — dominant `sucexg` | 10^12.810 | EXTRACTED (verbatim) |

**Projection-free HF substrate floor (NOW INCLUDING ORDER) =
max(A 10^2.408, B 10^2.149, HF 10^2.344, gndB 10^4.064, ord 10^2.652,
ZF-bind 10^12.810) = 10^12.810** (EXTRACTED-dominated by `sucexg`;
A/B/HF/gndB/ord all MEASURED). Unchanged in magnitude — the order
discharge is cheap (10^2.652, well below the EXTRACTED `sucexg` bind);
what changed is that **nothing remains `$a` but the C-essential order
primitive itself**.

## 5. The loop-closure statement (adversarially honest)

**The substrate is now FULLY projection-free, INCLUDING ORDER.** Both
order literals — every `≤` and every `≠` the closed proof consumes of the
named ℚ constants — are kernel-verified `$p`, derived by finite ground
unfolding from conservative order/injectivity definitions plus the bare
von-Neumann order/foundation primitives. After every arithmetic fact
(Frontier B) *and* both order facts are mechanically discharged, the only
non-arithmetic ingredient that remains is:

> **`el-0-suc` : `( (/) e. ( suc (/) ) )`** — the bare-ZF von-Neumann
> reflection of `of-letot` — together with its irreflexivity companion
> **`ne-suc-0` : `-. ( suc (/) ) = (/)`** (Foundation: `1 ≠ 0`).

**This discharge consumes the order predicate — STATED, NOT HIDDEN, NOT
MERGED.** `el-0-suc` *is* the von-Neumann form of "the order is total /
positive" — i.e. `of-letot`. By Frontier C that is the **PROVEN-
intrinsic** ingredient: no set of ring identities of any degree expresses
it (it is exactly the content false in ℤ/8 and ℤ/4 while every ring
identity is true there). So **removing order as a projection still costs
precisely the one thing proven irreducible** — the loop is closed:

- **Frontier C (proof content):** order is *proven* not expressible as
  any ring identity; essential, localised to `of-letot`.
- **Frontier B (substrate, arithmetic):** strip ℝ/Infinity/ω/ℚ and all
  arithmetic — what is left is **two order literals**.
- **CLOSURE (this file, substrate, order):** discharge those two — and
  the residue is **exactly `of-letot`'s bare-ZF reflection** (`el-0-suc`)
  plus its Foundation companion. Nothing else remains `$a`.

Three independent attacks land on the *same* irreducible point, and
removing it as a projection re-incurs *precisely it*. The single
irreducible residue of a ZFC model of plane geometry is **the ordering**
— the von-Neumann order primitive `0 ∈ 1` / `1 ≠ 0` — pinned to two
concrete inequalities, proven (Frontier C) not to be algebra.

**One-line verdict.** *Both order literals are discharged to
kernel-verified `$p` (MEASURED 10^2.652, `verified all 23 $p ✔`, `om`
absent, single ordinal `suc (/)` never iterated); the substrate is now
fully projection-free **including order**; and the discharge **consumes
exactly `of-letot`'s bare-ZF von-Neumann reflection** (`el-0-suc`, +
Foundation `ne-suc-0`) — the Frontier-C-proven-intrinsic ingredient,
flagged and never smuggled. The loop is closed: the residue is order,
and removing it still costs precisely the one thing proven essential.*

## 6. Adversarial self-audit (why this is a discharge, not a smuggle)

- The pre-existing `$a` outputs were `( Q0 Qle Q1 )` / `-. Q1 = Q0`
  *directly*. Here they are **derived**; what is `$a` is only the
  *conservative definitions* + the two bare von-Neumann primitives.
- `df-Zne1`/`df-Qne1` are *parametric* injectivity (`-. a=c -> -. C(a)=C(c)`),
  NOT the constants' disequality. The actual `1≠0` content enters **only**
  via `ne-suc-0` at the very bottom. No smuggle.
- `el-0-suc`/`ne-suc-0` are about the bare ordinals `(/)` and `suc (/)`
  (0 and 1), **not** the ratio-class literals — the sharpest honest
  localisation: the order/foundation core of the von-Neumann naturals.
- The order-axiom dependency is reported by `qzfhfordfloor` as a separate
  EXPLICIT section, never folded into the MEASURED cost line.
- Trust root `src/kernel.rs` re-verifies all 23 `$p`; a faked `$p` would
  be REJECTED.

## 7. Files / reproduce

- `CLOSURE_ORDLIT.md` — this document.
- `data/qzfhf_ord.mm` — the discharge: both order literals as
  kernel-verified `$p` (+ helpers; 23 `$p` total; 113 statements).
  Kernel-verified (`src/kernel.rs`).
- `src/bin/qzfhfordfloor.rs` — kernel-verify + MEASURE + structural
  audit + EXPLICIT order-axiom-dependency flag + restated now-closed
  floor + loop-closure verdict. Reproduce:
  `cargo run --release --bin qzfhfordfloor`.
- set.mm EXTRACTED figures (`sucexg`/…) quoted verbatim from
  `STAGE2_BC.md`/`FRONTIER_B_GND.md`; NOT re-measured, NOT merged.
- Trust root: `src/kernel.rs` (sound; re-checks every `$p`).
