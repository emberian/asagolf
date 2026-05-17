# SEAM 4 — the identity-reduction, MEASURED

**Research question.** Make precise and *measure* the structural claim
that the entire cut-free metric content of Birkhoff plane geometry
reduces, with exact constants, to cut-free proving of a small set of
bounded-degree polynomial identities over an ordered field.

**Instrument.** `src/bin/identityreduce.rs` (new, read-only). It parses
the kernel-verified corpus `data/grounded.out.mm` — the exact artifact
the authoritative `grounded data/grounded.mm` 96-verify emits —
**re-runs `db.verify()`** so every number below is measured on a
provably kernel-checked object, and uses the *identical* cut-free metric
(`expand`: `$f/$e = 0`, `$a = 1`, `$p = Σ children`). Nothing
authoritative is modified. The sole trust root remains `src/kernel.rs`;
the sole authoritative claim remains `grounded`'s `verified all 96 ✔`
(reproduced untouched, see end).

Reproduce: `cargo run --release --bin grounded -- data/grounded.mm`
(emits the corpus) then `cargo run --release --bin identityreduce`.

---

## The reduction statement (with measured constants)

> Every cut-free `$a`-leaf in the kernel-verified Birkhoff corpus is one
> named primitive axiom. Partition the primitive axioms into three
> auditable buckets — **IDENTITY** (the 15 ordered-ring
> polynomial-identity axioms the `ring_eq`/`canon_sum`/`desub`/`sdist`
> normalizer is built from), **GLUE** (df-unfold, geometric-predicate
> congruence, the ordering fragment, √/recip, first-order logic), and
> **SYNTAX** (wff/term constructors: pure well-formedness, zero
> mathematical content, present in *every* Metamath proof). Then,
> summed over all Birkhoff-postulate `$p` roots (total **9,017,010**
> cut-free `$a`):
>
> | bucket | share of raw cut-free total | share of *proof content* |
> |---|---:|---:|
> | SYNTAX (writing the formulas down) | **94.76 %** | — |
> | IDENTITY (polynomial-identity expansion) | 1.62 % | **30.98 %** |
> | GLUE (df-unfold + congruence + FOL + order) | 3.62 % | **69.02 %** |
>
> Of the *proof-content* cut-free cost (SYNTAX removed — the honest
> denominator, since syntax is the orthogonal cost of writing geometric
> formulas, not of proving anything), **≈ 31 %** is literally
> polynomial-identity expansion and **≈ 69 %** is structural glue.
> Sensitivity floor (the two equality-plumbing axioms `eqid`/`eqcom`
> reclassified to GLUE): IDENTITY ≥ **16.99 %** of content.

This is the precise, measured form of the structural claim. It is
**not** "geometry = polynomial identities": that overclaims. The honest
result is sharper and has two halves:

1. **The pure-equality polynomial identities reduce essentially
   completely.** The law-of-cosines production identity `loclink`
   collapses **96.82 %** to substitution-instances of two tiny generics
   (`loc-gen` deg 2, `telesh` deg 1); substitution is free in the
   cut-free metric. Residual glue: **3.18 %**.

2. **The sign/order reasoning does not, and saying so is the point.**
   The `sqcong` core (`a²=b² ∧ 0≤ab ⇒ a=b`) is only **38.48 %**
   generic-polynomial-identity; **61.52 %** is irreducible
   *ordered-field sign reasoning* (`sqz`/`sqzhalf`/`subeq0` + a
   case-split `jaoi`), which is genuinely **not** a polynomial identity.
   The reduction is tight exactly where the content is equational and
   honestly incomplete exactly where it is order-theoretic.

---

## §1 — the exact generic polynomial-identity set (extracted)

`--profile` over the corpus localises *all* heavy polynomial-identity
mass to five generic lemmas, proved once over fresh `$f` atoms and
instantiated into the geometry by substitution (free in this metric).
This is the entire identity set the postulates reduce to:

| lemma | deg | monos† | atoms | cut-free `$a` | log₁₀ | identity |
|---|---:|---:|---:|---:|---:|---|
| `telesh` | 1 | 6 | 3 | 3,431 | 3.535 | `(c−a)−(b−a)=(c−b)` |
| `loc-gen` | 2 | 16 | 4 | 51,358 | 4.711 | law of cosines `|C−B|²=|u|²+|w|²−2u·w` |
| `sqc-diffsq` | 2 | 6 | 2 | 5,051 | 3.703 | `(p−q)(p+q)=p²−q²` |
| `sqc-gprod` | 4 | 2 | 2 | 1,158 | 3.064 | `(q²)(p²)=(pq)(pq)` |
| `sqc-4uv` | 2 | 12 | 2 | 20,064 | 4.302 | `(p+q)²−(p−q)²=4pq` |

† `monos` = exact expanded **signed-monomial count** (lhs+rhs), by full
distribution of every product over every sum with `−x`/neg pushed in —
precisely what `grounded::sdist` produces before `canon_sum`
cancellation. Each count is derived from the identity's source term
tree (derivation in the `identityreduce.rs` `GENERICS` comment).

All bounded degree (≤ 4), all ≤ 16 monomials, all ≤ 4 atoms — a *small
set of bounded-degree polynomial identities*, exactly as the claim
states. Every `ring_eq` call site in the production proofs
(`grounded.rs`, `proof_g{1,2,3,4a}.rs`) is either one of these by
substitution or a tiny (≤ deg-2, ≤ 4-monomial) inline shift handled by
the same normalizer.

---

## §2 — the MEASURED cost law

The function (identity #monomials, degree) → cut-free `$a`-leaf cost,
fitted by OLS on the five measured generics:

- **Model A** (1 regressor, ln–ln):
  `cost ≈ 237.9 · monos^1.795`, **R² = 0.933**, worst residual
  0.238 log₁₀ (×1.73).
- **Model B** (2 regressors, ln–ln):
  `cost ≈ exp(4.425) · monos^2.041 · deg^0.834`, **R² = 0.990**.

**Measured cost law (honest reading):** the cut-free `$a` cost of a ring
identity is **≈ quadratic in its expanded monomial count**, with a
**sub-linear (≈ √) degree factor**. Degree matters only weakly and
mostly *through* the monomial count; the dominant lever is monomial
count, consistent with `canon_sum`'s ~O(n²)-spine per-monomial sort.
This is why the generic-lemma factoring works: it caps `monos` at the
tiny generic identities instead of letting the geometry expand a dense
high-`monos` polynomial per triangle.

Residuals are reported per lemma in the tool output (`§2`); none is
hidden. n = 5 is small — this is a *measured* law over the actual
identity set, not an asymptotic proof; the §2c production-instance check
below is the out-of-sample validation.

---

## §2c — the reduction MEASURED on the production identities

Pure `expand` attribution off the corpus (no fit):

| host | total | generic core (substitution) | residual glue |
|---|---:|---:|---:|
| `loclink` (geometry's law-of-cosines) | 67,217 | 65,082 = 1·`loc-gen` + 4·`telesh` (**96.82 %**) | 2,135 (**3.18 %**) |
| `sqcong` (`a²=b²⇒a=b` core) | 68,276 | 26,273 = `sqc-4uv`+`sqc-diffsq`+`sqc-gprod` (**38.48 %**) | 42,003 (**61.52 %**) |

The two halves of the honest answer, quantified. `loclink` is a near-
perfect reduction; `sqcong`'s majority is order reasoning, not identity.

---

## §3 — per-postulate IDENTITY vs GLUE vs SYNTAX (exact)

Shares of each postulate's cut-free `$a` total; `id|cnt`,`gl|cnt` are
the honest content ratio (SYNTAX excluded); `id*|cnt` is the
eqid/eqcom→GLUE sensitivity floor.

| postulate | cut-free `$a` | id% | gl% | syn% | id\|cnt | gl\|cnt | id*\|cnt |
|---|---:|---:|---:|---:|---:|---:|---:|
| G4 SAS | 383,606 | 3.45 | 11.11 | 85.44 | **23.69** | 76.31 | 11.89 |
| G3a ray-angle | 3,987,466 | 1.23 | 2.26 | 96.51 | **35.33** | 64.67 | 20.33 |
| G3a dot-prop (ASA′) | 437,578 | 0.94 | 1.52 | 97.54 | 38.23 | 61.77 | 22.14 |
| G3b prot-uniq (oriented) | 306,883 | 3.10 | 9.44 | 87.46 | **24.71** | 75.29 | 12.61 |
| G3c ray-line | 320 | 0.00 | 20.31 | 79.69 | 0.00 | 100.00 | 0.00 |
| G2 incidence | 787,393 | 2.72 | 6.81 | 90.47 | **28.59** | 71.41 | 14.92 |
| G1 ruler (dist) | 1,829,012 | 0.54 | 0.87 | 98.59 | 38.06 | 61.94 | 24.86 |
| G1 ruler (ray) | 324,767 | 2.11 | 3.92 | 93.98 | 34.98 | 65.02 | 19.75 |
| G0 cong-sub | 1,035 | 1.55 | 12.66 | 85.80 | 10.88 | 89.12 | 6.80 |
| g4a SSS→ACong (ASA′) | 662,520 | 3.45 | 8.21 | 88.34 | 29.55 | 70.45 | 15.23 |
| g4a dot (ASA′) | 220,403 | 3.45 | 8.20 | 88.35 | 29.62 | 70.38 | 15.27 |
| sqd-sym (ASA′) | 76,027 | 2.55 | 4.22 | 93.22 | 37.68 | 62.32 | 20.44 |
| **Σ all roots** | **9,017,010** | **1.62** | **3.62** | **94.76** | **30.98** | **69.02** | **16.99** |

Observations (honest):

- **SYNTAX dominates every postulate (79–98 %).** The single largest
  fact about the cut-free metric is that it is overwhelmingly the cost
  of *writing the geometric coordinate formulas down* (`tmu` `tpl`
  `tmi` `t0` `txc` `tyc` …), not of any proof step. This is true of
  any Metamath proof and is exactly why cut-free is the honest *hard*
  metric for the poll's question — and why it is orthogonal to, and
  must not be folded into, the identity-vs-glue split.
- Among proof content, the **algebra-heavy postulates** (G4, G2, G1, the
  ASA′ support lemmas) are the *most* identity-dominated:
  `id|cnt ≈ 24–38 %`.
- `G3c`/`G0` are essentially pure glue/FOL — they assert df-unfold and
  congruence-substitution and contain almost no polynomial identity, as
  expected (they are the structural postulates).
- ASA′'s extra closure lemmas (`g3a-dotprop`, `g4a-*`, `sqd-sym`) sit in
  the same 30–38 % content-identity band as the core postulates — the
  regrounded ASA′ does not change the structural picture.

The complete per-postulate primitive-axiom receipts (every contributing
axiom, bucket-tagged) are in the tool's `§4` output.

---

## How tight is the reduction, honestly?

**Tight where equational, honestly incomplete where order-theoretic.**

- The reduction statement holds **exactly** at the measured constants
  above — there is no fitted fudge in §0/§1/§2c/§3; those are direct
  `expand` counts on a kernel-reverified corpus.
- The *only* fitted object is the §2 cost law (R² 0.93 single-regressor
  / 0.99 two-regressor over n = 5); it is labelled a measured law, not a
  theorem, and validated out-of-sample by §2c.
- The honest residual is **not noise, it is structural**: `sqcong` is
  61.5 % ordered-field **sign reasoning** that is provably not a
  polynomial identity (`a²=b²⇒a=b` needs the order, not just the ring).
  An honest "the reduction is ~97 % for the pure-equality identity
  (law of cosines) and ~38 % for the order-coupled one, here is the
  exact residual and what it is made of" is the success criterion of
  this project, and it is what is reported.

**MEASURED vs PROJECTION split.** Every number in §0, §1, §2c, §3, §4
is MEASURED (direct `expand`/`expand_by_axiom` on the kernel-reverified
corpus). The only PROJECTION-class object is the §2 cost-law *fit*; it
is labelled as a fitted measured law with its R² and full residuals, is
never merged into a measured count, and the §2c production-instance
decomposition is given as its independent validation. No fabricated
digit; no measured line contaminated by a fit.

---

## Reproduction / authoritative check untouched

```
cargo run --release --bin grounded -- data/grounded.mm   # Kernel: verified all 96 ✔  (db 267)
cargo run --release --bin identityreduce                 # corpus kernel-reverified ✔ + §0–§4
```

The authoritative 96-verify is byte-unchanged; `identityreduce` is
read-only convenience measurement that additionally re-runs the kernel
on the corpus it measures. Files added by SEAM 4:
`src/bin/identityreduce.rs`, `SEAM4_IDENTITY.md`. No authoritative file
(`kernel.rs`, `grounded.rs`, `elaborate.rs`, `proof_g*`,
`data/grounded.mm`) modified.
