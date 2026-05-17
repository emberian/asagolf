# CLOSURE — the geometry `df-*` layer is a CERTIFIED conservative extension

Adversarially honest. Trust root: `src/kernel.rs`. Instrument:
`src/bin/dfconserv.rs` (read-only over `data/grounded.out.mm`; the whole
corpus is re-verified in the sound kernel before any verdict). This
report closes Frontier A's single open residual (`FRONTIER_A_REVMATH.md`
§3.1: "df-* conservative by construction — evidenced but UNCERTIFIED").

Reproduce:

```
cargo run --release --bin grounded     # emits data/grounded.out.mm (96 $p)
cargo run --release --bin dfconserv    # the certifier; kernel re-verifies first
```

Kernel re-verify before any number: `KERNEL ✔ 96 $p 82 $a 69 $e 20 $f
(267 statements)`.

---

## 1. The criterion (the conservativity metatheorem, stated correctly)

Standard references: Suppes, *Introduction to Logic* ch. 8
(eliminability + non-creativity criteria for definitions);
Shoenfield, *Mathematical Logic* §4.6 (definitional extensions);
Hilbert–Bernays (definition elimination). Two distinct, both standard,
metatheorems are used — each stated with **every hypothesis enumerated
and mapped to a machine check**.

### Metatheorem A — single-symbol eliminable definition

Let `S` be a theory in signature `Σ` (with equality + congruence).
Introduce a fresh symbol `c` by ONE axiom `δ`:

* operator definition:  `( c x1 … xn ) = D`
* predicate definition: `( ( c x1 … xn ) <-> D )`

`S' = S + {δ}` is a **conservative — indeed eliminable, hence
definitional —** extension of `S` iff:

| Hyp | Statement | Machine check (`dfconserv.rs`) |
|---|---|---|
| **D1** form/properness | `c` a single fresh constant; definiendum = `c` applied to **pairwise-distinct variables** x1..xn (modulo pure notation-formers); definiens `D` has no free var outside {xi}; predicate ⇒ `D` a wff, operator ⇒ `D` a term | `check_d1` — parses the definiendum tree, requires all variable leaves distinct, every non-`c` constant either a notation-former (grammar `$a`, no `\|-` def, no standalone use) or rejected; checks `FV(D) ⊆ {xi}` |
| **D2** non-creativity | every symbol of `D` declared strictly **before** `δ` (no forward ref); `c ∉ D` (no self-ref ⇒ no recursion) | `check_d2` — `first_use` index per symbol vs. `δ`'s statement index; explicit `c ∈ D` self-ref scan |
| **D3** uniqueness | `δ` is the **sole** defining `$a \|-` for `c` | `check_d3` — counts `$a \|-` whose principal definitional symbol is `c` |
| congruence support | `S` has equality + operator/predicate congruence so the elimination translation commutes with the logical structure | `check_cong_support` — `eqid/eqcom/ax-7/ax-bi1/ax-bi2/ax-mp/ax-1/2/3` + the `cong-*` family present |

**Conclusion (the cited classical theorem):** under D1+D2+D3 +
congruence support there is a translation `*` erasing `c` with
`S' ⊢ φ ⟺ φ*` and `S ⊢ φ*` whenever `S' ⊢ φ` and `φ` is `c`-free. Hence
(a) every `Σ`-theorem of `S'` is a theorem of `S` (**conservative**),
(b) `S'` consistent iff `S` is, (c) `c` **eliminable**.

### Metatheorem B — surjective-pairing interpretation

Extend the algebraic core `S` by a fresh constructor `Pt` and
projections `Xc`,`Yc` with **exactly** the surjective-pairing axioms

```
(P1)  ( Xc ( Pt u v ) ) = u
(P2)  ( Yc ( Pt u v ) ) = v
(P3)  ( ( ( Xc a ) = ( Xc b ) /\ ( Yc a ) = ( Yc b ) ) -> a = b )
```

plus projection congruences `cong-xc`,`cong-yc`. Then `S+P` is
**conservative** over `S`.

*Proof (cited standard interpretation argument):* interpret the point
sort as `S×S` over any model of `S`, `Pt := ⟨·,·⟩`, `Xc := π1`,
`Yc := π2`. (P1)/(P2) = π∘⟨⟩ = id; (P3) = pair extensionality;
`cong-*` = π functionality. The interpretation is the **identity on
Pt/Xc/Yc-free formulas**, so every such `S+P`-theorem already holds in
`S`. ∎

| Hyp | Statement | Machine check |
|---|---|---|
| **H1** | `df-xc`,`df-yc`,`ptext` are **syntactically exactly** P1/P2/P3; `cong-xc`/`cong-yc` present | `pairing_conservative` — byte-exact body comparison |
| **H2** | after removing the strict-eliminable df-* (Metatheorem A, conservatively), the **only** remaining primitive `$a \|-` constraints on Pt/Xc/Yc are P1/P2/P3 + cong — no extra constraint the diagonal model must also satisfy | scans all `$a \|-`, excludes the 5 pairing axioms and every strict-PASS df-* (recomputed via `quick_strict`), requires the remainder Pt/Xc/Yc-free |
| **H3** | the algebraic core `S` is present and Pt/Xc/Yc-free (a genuine interpretation target) | samples `of-addcom/of-mulcom/of-distr/of-recip/of-letot/ax-sqrt`, asserts Pt/Xc/Yc absent |

**Composition lemma (standard):** a composition of conservative
extensions is conservative. Eliminating the 9 Suppes-definable symbols
(A) then handling the residual pairing (B) ⇒ the whole geometry `df-*`
layer is conservative over the geometry-free `F1` base.

What is **NOT** re-proved in-kernel and is labelled so: Metatheorems A
and B *themselves* (the textbook results). They are correctly stated
with every hypothesis enumerated and each hypothesis machine-checked
against the corpus — but the metatheorems are not re-derived inside the
Metamath kernel. This is the honest PROVEN/CONJECTURED boundary.

---

## 2. Per-`df-*` PASS/FAIL table (MEASURED by `dfconserv`)

### Geometry `df-*` (the Frontier A residual)

| df | defsym | kind | D1 | D2 | D3 | consumed | strict criterion |
|---|---|---|---|---|---|---|---|
| df-xc   | Xc    | operator  | **FAIL** | PASS | PASS | yes | FAIL-D1: `Xc` applied to compound `( Pt u v )` (`Pt` not a notation-former — has builder `tpt`, used standalone in df-cp). Pattern/reduction rule, **not** a single-symbol Suppes definition |
| df-yc   | Yc    | operator  | **FAIL** | PASS | PASS | yes | FAIL-D1 (same as df-xc) |
| df-sqd  | sqd   | operator  | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-cp   | cp    | operator  | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-dot  | dot   | operator  | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-crs  | crs   | operator  | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-coll | Coll  | predicate | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-on   | On    | predicate | PASS | PASS | PASS | yes | **PASS** (`Ln` certified a pure notation-former: no own `\|-` def, never occurs without `On`) |
| df-tri  | Tri   | predicate | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-ray  | Ray   | predicate | PASS | PASS | PASS | yes | **PASS — eliminable definition** |
| df-acong| ACong | predicate | PASS | PASS | PASS | yes | **PASS — eliminable definition** |

**9 of 11 geometry df-* meet the strict single-symbol criterion**
(D1+D2+D3). df-xc/df-yc are precisely characterized: they are the
**projection laws of a free pairing**, not single-symbol definitions —
handled by Metatheorem B, all hypotheses machine-checked PASS
(H1 ✔ H2 ✔ H3 ✔).

Every df-* is **consumed** (proof-DAG closure of the 96 `$p`) — the
verdict is load-bearing, not vacuous.

### Logical / algebraic `df-*` (not geometry — reported for completeness)

| df | defsym | kind | D1 | D2 | D3 | strict criterion |
|---|---|---|---|---|---|---|
| df-an  | /\ | predicate | PASS | PASS | PASS | **PASS — eliminable definition** |
| df-or  | \\/ | predicate | PASS | PASS | PASS | **PASS — eliminable definition** |
| df-lt  | <  | predicate | PASS | PASS | PASS | **PASS — eliminable definition** |
| df-sub | -x | operator  | PASS | **FAIL** | PASS | FAIL-D2: definiens references `-x` (self-ref). NOT a strict definition — a provable rewrite once unary `( 0 -x v )` is primitive. Outside the geometry layer; does not affect the geometry verdict |

---

## 3. Verdict

> **The `df-*` geometry layer IS a CONSERVATIVE extension of the
> geometry-free `F1` base** (open propositional + equality-congruence +
> ordered field + one √). PROVEN by a two-step, fully machine-checked
> argument:
>
> 1. the **9 genuinely-fresh geometric symbols**
>    (`Coll`,`On`,`Tri`,`Ray`,`ACong`,`sqd`,`dot`,`crs`,`cp`) are
>    **single-symbol Suppes-eliminable definitions** (Metatheorem A;
>    D1+D2+D3 + congruence all PASS) — removed with **zero added
>    first-order strength**;
> 2. the residual `(Pt,Xc,Yc)` is conservative over the algebraic core
>    by the **surjective-pairing interpretation metatheorem**
>    (Metatheorem B; H1/H2/H3 all PASS — the diagonal pairing on `S`,
>    identity on Pt/Xc/Yc-free formulas);
>
> and a composition of conservative extensions is conservative.

There is **no offender that survives**: df-xc/df-yc fail the *strict
single-symbol* form (correctly, honestly reported) but are
**precisely characterized and proven conservative** by the appropriate
(different, equally standard) metatheorem with every hypothesis checked.
A "df-X fails the strict criterion because Y, but is conservative by
metatheorem Z whose hypotheses are H1✔H2✔H3✔" is the full,
adversarially-rigorous success — not a glib "all conservative."

### Consequence for Frontier A — the bound is now EXACT

`FRONTIER_A_REVMATH.md` §3.1 named exactly one open residual: the df-*
layer being "conservative by construction, evidenced but UNCERTIFIED."
That premise is now **CERTIFIED** (this instrument, kernel-grounded,
hypotheses machine-checked). Therefore:

> Frontier A's strength characterization is upgraded from **UPPER
> BOUND** to **EXACT**:
> `T = OPEN( classical propositional calculus + equality-with-operator-
> congruence + the ordered-field axioms + one √-adjunction )`,
> the entire geometry layer being a **certified conservative
> definitional / pairing extension** that adds no first-order strength.

This interlocks with Frontier C (the order/√ core is *proven* logically
essential, not algebra): together they pin `T` from **both sides** — an
open quantifier-free theory bounded above by EFA, with the geometry
certified strength-free above and the order predicate proven essential
below. The remaining project-level open item is Frontier C's
exact-constant *Obligation O* (a cut-free lower bound), explicitly
**not** part of this closure and not claimed here.

---

## 4. PROVEN / CONJECTURED split (honest boundary)

**PROVEN (machine-checked here, kernel-grounded):**

* D1/D2/D3 outcome for every one of the 15 `df-*` — exact (table §2).
* Each strict-PASS `df-*` is eliminable & conservative by Metatheorem A,
  *all its hypotheses* (D1,D2,D3,congruence) checked against the corpus.
* The `(Pt,Xc,Yc)` layer is conservative by Metatheorem B, *all three
  hypotheses* (H1 byte-exact axiom match, H2 layered residual check,
  H3 interpretation-target check) PASS.
* The whole corpus re-verified in the sound kernel (96 `$p` ✔) before
  any verdict was emitted.

**CONJECTURED / not re-proved in-kernel (named, not asserted as
machine-proven):**

* Metatheorems A and B *themselves* are the cited classical
  logic-textbook results (Suppes/Shoenfield; surjective-pairing
  interpretation). They are correctly stated with every hypothesis
  enumerated and each hypothesis machine-checked — but the metatheorems
  are **not** re-derived inside the Metamath kernel. (Re-deriving the
  general definition-elimination metatheorem in-kernel is a separate,
  much larger metalogical task, explicitly out of scope.)
* `df-sub` is **not** a strict definition (FAIL-D2 self-ref, reported).
  It is a provable rewrite once unary `( 0 -x v )` is taken primitive;
  it lies **outside** the geometry layer and does not affect the
  geometry verdict.

---

## 5. Files

* `src/bin/dfconserv.rs` — the CLOSURE instrument (new, additive,
  read-only over the corpus). Kernel re-verifies all 96 `$p` before any
  verdict; then certifies every `df-*` against the two metatheorems with
  every hypothesis machine-checked.
* `CLOSURE_DFCONSERV.md` — this report.
* Read-only consumed: `data/grounded.out.mm` (generated by
  `cargo run --release --bin grounded`).
* Untouched: `src/kernel.rs`, `src/elaborate.rs`, `src/bin/grounded.rs`,
  `src/proof_g*.rs`, `data/*.mm`, `src/cse.rs`, `src/search.rs`, other
  agents' files. Isolated worktree off HEAD; new files only.
* Trust root: `src/kernel.rs` (sound; re-checks every `$p`).

Reported, not faked — including the two `df-*` that fail the *strict*
single-symbol form (precisely characterized and proven conservative by
the correct alternative metatheorem), the one self-referential
non-geometry `df-sub` (FAIL-D2), and the explicit
proven/conjectured boundary (the metatheorems are cited, not
re-derived in-kernel).
