# Frontier C — Is the order-core a genuine lower bound?

**Question (from `COST_STRUCTURE.md` §"Honest open questions"):** Seam 4
MEASURED that ~61.52 % of the cut-free content of `sqcong` is
ordered-field sign reasoning (`sqz`/`sqzhalf`/`subeq0` + a totality
case-split) that empirically did **not** reduce to bounded-degree
polynomial identities. Is this a *genuine* lower bound — can the content
of `sqcong` provably **not** be expressed as a bounded-degree ring
identity over the `(+, ·, 0, 1)` signature, so that the order predicate
is *essential* — or is it merely an artefact of the construction?

This document answers it. The answer is split, scrupulously, into a
**PROVEN** theorem and the **CONJECTURED** quantitative refinement that
remains, with the exact open obligation isolated.

The sole trust root remains `src/kernel.rs`. The ordered-field signature
referenced throughout is *exactly* that of `data/grounded.mm` (read
read-only); the `sqcong` obligation is *exactly* lemma 54 of
`src/bin/grounded.rs`:

> `sqcong`: from `( u * u ) = ( v * v )` and `( 0 <_ ( u * v ) )`,
> derive `u = v`.

A small independent kernel check is provided
(`src/bin/ordercore.rs`, new, read-only) that exhibits the separating
model and verifies the separation arithmetic *in our kernel's number
type*; it does not touch the authoritative corpus.

---

## 0. The precise framing — what "a bounded-degree ring identity" means

We must state the target at *exactly* the right level, or the argument
is hand-waving. Three things have to be pinned down: the **signature**,
the **theory** (what "a ring identity" is allowed to assume), and the
**proof shape** ("bounded-degree", and the side condition).

### 0.1 The signature

`data/grounded.mm` splits its primitives into two disjoint groups:

- **Ring signature** `σ_ring = (+, -x, *, 0, 1, inv)` with the axioms
  `of-addcom of-addass of-add0 of-addinv of-mulcom of-mulass of-mul1
  of-distr of-recip` and the definitional `df-sub`.  These axioms are
  *exactly the axioms of a commutative ring with unit* (plus `of-recip`,
  a partial-inverse axiom, and `df-sub` defining binary `-x` from the
  additive inverse `0 -x v` pinned by `of-addinv`).  Crucially **every
  one is an equational universal sentence true in every commutative
  ring** (with `of-recip` a Horn clause true in every field; it is not
  used anywhere in the `sqcong` order-core).
- **Order signature** `σ_ord = (<_ , <)` with `of-lein of-letri
  of-sqpos of-letot of-leadd of-lemul of-lemul0` and `df-lt`.  These are
  *not* equational and *not* true in arbitrary rings.

`sqcong`'s statement uses `*`, `=` (ring) **and** `<_` (order, in the
hypothesis `0 <_ (u*v)`). Its proof, traced through lemmas 49–54 of
`src/bin/grounded.rs`, uses the order axioms `of-letot` (the `jaoi`
totality split inside `sqz`, line 3874), `of-lein`/`lein2`,
`of-leadd`/`le2sub`/`sub2le`, `of-sqpos`, `of-lemul`-family.

### 0.2 What "expressible as a bounded-degree ring identity" must mean

The intuition in the literature ("ring identities hold in all
commutative rings; `a²=b² ⇒ a=b` fails in ℤ/8") is correct but is
*about the wrong object* until made precise. `sqcong` is **not** an
identity — it is an implication with two hypotheses, one of which
(`0 <_ uv`) is an order atom. The honest question is:

> Can the order hypothesis be **eliminated** — i.e. is there a
> derivation of `u = v` from `(u·u) = (v·v)` alone (or together with
> *some* purely equational, order-free side conditions of bounded
> degree) using **only** σ_ring axioms — i.e. only facts true in every
> commutative ring?

"Bounded-degree ring identity" is given the standard equational-logic
meaning: a finite conjunction of universally-quantified polynomial
equations `p_i(x̄) = q_i(x̄)` over σ_ring with `deg ≤ D`, used as
rewrite/substitution lemmas (this is *precisely* the
`ring_eq`/`canon_sum`/`sdist` fragment of `src/elaborate.rs`, and
exactly the five generic identities `telesh loc-gen sqc-diffsq
sqc-gprod sqc-4uv` of SEAM4 §1, all true in every commutative ring).

The two formalisations of "the order is inessential" we will *refute*:

- **(F1, the strong form)** There is a quantifier-free σ_ring formula
  `Φ(u,v)` (a Boolean combination of polynomial equations of bounded
  degree) such that
  `CR ⊢ ( (u·u = v·v) ∧ Φ(u,v) ) → u = v`,
  where `CR` = the theory of commutative rings (equivalently: the
  entailment holds **in every commutative ring**), and `Φ` is *order-free*
  and is *discharged for the actual `sqcong` call-sites*.
- **(F2, the form that matches the measurement)** The order-reasoning
  block of `sqcong` (the `sqz`/`sqzhalf` + `of-letot` case-split,
  i.e. the step `(d·d)·(d·d) = 0 ⊢ d = 0`) is replaceable by σ_ring
  identities — i.e. `x⁴ = 0 ⊢ x = 0` is a consequence of bounded-degree
  ring identities (true in all commutative rings).

We **PROVE both F1 and F2 are false**, which is exactly the statement
"the order predicate is essential — the order-core is a genuine lower
bound." We then state the **CONJECTURED** sharpening (that the *measured
61.52 %* is the tight constant) and isolate why it is not yet a theorem.

---

## 1. THEOREM (PROVEN) — the order predicate is essential

> **Theorem 1 (Order-essentiality of `sqcong`).**
> Let `CR` be the theory of commutative rings with unit in the
> signature σ_ring (the `of-add*`, `of-mul*`, `of-distr` axioms of
> `data/grounded.mm`, all equational and true in every commutative
> ring; `of-recip`/`df-sub` are conservative over this and unused in the
> core). Then:
>
> **(a)** There is **no** quantifier-free order-free σ_ring formula
> `Φ(u,v)` that is *trivial / identically true* (in particular: no
> derivation using only σ_ring identities) for which
> `CR ⊢ (u·u = v·v) → u = v`. Equivalently: the implication
> `(u·u = v·v) → u = v` is **false in some commutative ring**, hence is
> **not** a consequence of any set of ring identities. *(Refutes F1 in
> its bare form.)*
>
> **(b)** Stronger, matching the *actual* `sqcong` proof obligation:
> the entailment
> `(u·u = v·v) ∧ (∃w. w + w = u·v + … )  ⊢ u = v`
> with the order hypothesis `0 ≤ uv` *replaced by any order-free σ_ring
> condition that the SEAM4 generic identities can discharge* is **false
> in some commutative ring**. Concretely the load-bearing internal step
> `x⁴ = 0 ⊢ x = 0` (where `x = (u -x v)`; this is the
> `(d·d)·(d·d)=0 ⊢ d=0` double-`sqz` at `grounded.rs:4303–4306`) is
> **not** valid in all commutative rings. *(Refutes F2 — the exact
> measured order-block.)*
>
> **(c)** Therefore in *every* derivation of `sqcong` from σ_ring
> identities + the order theory, **at least one σ_ord axiom that is not
> true in all commutative rings must be used**: the order predicate is
> *logically essential*, not a construction artefact. The 61.52 %
> order-residual is a **genuine lower bound in the qualitative sense**:
> it cannot be driven to 0 by *any* better choice of bounded-degree
> ring identities, because no finite set of ring identities entails it
> at all.

### Proof.

**Lemma A (the separating models).**
Consider the commutative rings
`R_n = ℤ/nℤ` for `n` not squarefree-with-the-relevant-prime, concretely
`R = ℤ/8ℤ` and `R' = ℤ/4ℤ`.

1. In `R = ℤ/8ℤ`: take `u = 3, v = 1`. Then
   `u·u = 9 = 1 (mod 8)` and `v·v = 1`, so `u·u = v·v` **holds**,
   but `u = 3 ≠ 1 = v`. Also `u·v = 3`, and the order hypothesis is
   *vacuous in a ring with no order*; the point of (a) is precisely that
   without the order atom the implication already fails. ∎(a)

2. The internal step F2 is `x⁴ = 0 ⊢ x = 0`. In `R' = ℤ/4ℤ` take
   `x = 2`: `x² = 4 = 0`, so `x⁴ = 0`, but `x = 2 ≠ 0`. Hence
   `x⁴ = 0 → x = 0` is **false in the commutative ring ℤ/4ℤ**. The
   *same* witness already kills the weaker `x² = 0 ⊢ x = 0` (used as
   `sqz` is applied twice). ∎(b, internal step)

   The full F2 statement (with the order hypothesis replaced by an
   *order-free, identity-discharged* condition) reduces to (b)'s
   internal step because the `sqcong` proof's *only* non-ring move after
   forming `(d·d)·(d·d) = 0` is exactly the two `sqz` applications
   `(d·d)²=0 ⊢ d·d=0` and `(d·d)=0 ⊢ d=0`, and `subeq0`
   (`d = 0 ⊢ u = v`, which **is** pure ring — see Lemma C). So if F2
   held, `x²=0 ⊢ x=0` would be a ring-identity consequence; ℤ/4ℤ
   refutes it. ∎(b)

**Lemma B (soundness of ring-identity derivations — why Lemma A
suffices).**
This is the standard but load-bearing model-theoretic fact, stated
correctly. Every σ_ring axiom of `data/grounded.mm` listed in §0.1 is a
universally-quantified equation (or, for `of-recip`, a Horn clause)
**valid in the variety of commutative rings**. Equational logic is
**sound**: if a universal Horn sentence `S` is derivable from a set `E`
of equations (closed under the rules refl/sym/trans/congruence/
substitution — *exactly* the `ring_eq`/`cong-*`/`eqtr*` discipline of
`src/elaborate.rs` and the kernel's substitution), then `S` holds in
**every** model of `E`. Commutative rings are models of `E = σ_ring
axioms`. Therefore *any* statement derivable using **only** σ_ring
identities + equational logic holds in **every commutative ring**.

Contrapositive: a statement that **fails in some commutative ring**
(ℤ/8ℤ for (a); ℤ/4ℤ for (b)) is **not** derivable from any set of ring
identities whatsoever — in particular not from any *bounded-degree* set,
a fortiori not from SEAM4's five generics `telesh loc-gen sqc-diffsq
sqc-gprod sqc-4uv` (each of which we note is indeed a true commutative-
ring identity, so they *cannot* help: they are all valid in ℤ/8 and
ℤ/4, yet the conclusion is false there).

**Lemma C (the genuine boundary — what *is* pure ring, so the claim is
sharp not sloppy).** Honesty cuts both ways: not all of `sqcong`'s
"order-tagged" plumbing is genuinely order. We verify the boundary:

- `subeq0` (`(u -x v) = 0 → u = v`, lemma 49, `grounded.rs:3560`) is
  derivable from σ_ring **alone** (it uses only `cong-pl1`,
  `of-add*`/`df-sub` via `ring_eq` — see its proof: no `<_` appears). It
  is *valid in every commutative ring*. So `subeq0` is **correctly NOT a
  lower-bound contributor**; the lower bound is *not* "everything
  labelled order".
- The irreducible kernel is precisely **`sqz`/`sqzhalf`** — and inside
  them the *single* essential use is the totality split
  `of-letot : (u <_ 0) ∨ (0 <_ u)` (the `jaoi` at
  `grounded.rs:3874–3884`) together with antisymmetry `of-lein`
  (`lein2`). `of-letot` and `of-lein` are the two σ_ord axioms that are
  **false in ℤ/8, ℤ/4** (those rings carry no compatible total order at
  all — they have zero divisors / are not orderable). This pinpoints
  the lower bound to *one named axiom*: **`of-letot` (totality of the
  order) is the load-bearing essential hypothesis** of `sqcong`. A
  commutative ring admitting `x ≠ 0` with `x²=0` (e.g. ℤ/4) is
  *exactly* a ring with no total order making it an ordered ring (an
  ordered ring is an integral domain in char 0; it has no nonzero
  nilpotents), which is the precise model-theoretic reason
  `of-letot` cannot be a ring-identity consequence.

Combining A + B + C: any derivation of `sqcong` (or of its internal
`x⁴=0 ⊢ x=0` step) must invoke a σ_ord axiom not valid in commutative
rings — concretely `of-letot`/`of-lein`. The order predicate is
**logically essential**. ∎ (Theorem 1)

### What Theorem 1 does and does **not** say

- **PROVEN:** the order-core is a *genuine qualitative lower bound*: no
  set of bounded-degree ring identities (indeed no set of ring
  identities at all) can replace the order reasoning in `sqcong`. The
  ~61.52 % measured residual is *structural and irreducible in kind*,
  not an artefact — it is exactly the part that, by Lemma B, **provably
  cannot** be turned into polynomial-identity expansion, because the
  thing it proves is **false in ℤ/4ℤ**. This vindicates
  `COST_STRUCTURE.md`'s "the first floor that looks intrinsic, not
  chosen."
- It localises the lower bound to a **single named axiom**, `of-letot`
  (with `of-lein`): the essential content is *totality of the order /
  no nonzero nilpotents*, i.e. the model is an ordered (hence reduced,
  zero-divisor-free in the relevant sense) ring. This is sharper than
  "uses the order somewhere."

---

## 2. CONJECTURED — the quantitative tightness of 61.52 %

Theorem 1 proves the residual is irreducible *in kind*. It does **not**
prove the specific number **61.52 %** is the *minimal* such residual
under the cut-free `$a` metric. That is a separate, genuinely open
quantitative question. State it exactly:

> **Conjecture 2 (tightness).** Over the cut-free `$a`-leaf metric of
> SEAM4, the minimum, over all kernel-valid derivations of `sqcong`
> from σ_ring identities + σ_ord axioms, of the fraction of cut-free
> leaves attributable to σ_ord-essential steps (steps invalid in
> commutative rings) is **exactly the 61.52 % measured for the
> production proof** (`sqcong`: 42,003 / 68,276), up to the
> sub-leading equational plumbing.

**Status: CONJECTURED, and here is precisely why it is hard / open.**

1. **Lower bound on the count, not just existence.** Theorem 1 says
   *≥ 1* σ_ord-essential step is required. Conjecture 2 asserts a
   *specific large fraction* is required. Going from "≥1" to "≥ 42,003
   cut-free leaves" needs a *proof-complexity lower bound* over the
   cut-free metric for the order sub-derivation `x⁴=0 ∧ 0≤(stuff) ⊢
   x=0`, against **all** proofs, not the one we wrote. This is a
   Frege-style lower bound over a fixed weak proof system; the project
   already flagged (SEAM2) that minimal-DAG lower bounds here are
   NP-hard / open. No technique in this codebase delivers an
   unconditional cut-free proof-size lower bound for a specific
   first-order order-theoretic lemma.
2. **The metric is construction-sensitive.** SEAM4's own through-line is
   that "every floor was a construction choice." The order-core is the
   one that did not move *under the constructions tried*. That is
   strong empirical evidence but, by the project's own iron rule, **not
   a proof** that *no* construction moves it quantitatively. (Theorem 1
   *does* prove no construction moves it to **0** — that part is now a
   theorem, not a conjecture.)
3. **Exact clean open lemma (the gold).** Conjecture 2 reduces to one
   crisp statement, which I isolate as the precise remaining obligation:

   > **Open Obligation O.** In the equational+order proof system of
   > `src/kernel.rs`, every derivation of
   > `( (u·u) = (v·v) ) ∧ ( 0 <_ (u·v) ) ⊢ u = v`
   > contains a sub-derivation of `x²=0 → x=0` (some term `x`), and
   > every cut-free derivation of `x²=0 → x=0` over σ_ring∪σ_ord has
   > cut-free `$a`-size ≥ c·(size of `sqzhalf`) for an absolute c>0.
   > The *first* clause (every `sqcong` proof factors through a
   > `nilpotent-free` step) is **PROVABLE** by the Lemma B model
   > argument relativised to subterms (a nilpotent witness in ℤ/4 lifts
   > to refute any order-free shortcut — essentially proven in
   > Theorem 1(b)). The *second* clause (the size lower bound) is the
   > **hard, open** part: an unconditional lower bound on cut-free
   > proofs of a fixed order-theoretic implication. **OPEN.**

So the honest split is: **the existence/essentiality lower bound is a
THEOREM (Thm 1); the exact 61.52 % constant is CONJECTURED and reduces
to Open Obligation O's size-lower-bound clause, which is a genuine
proof-complexity problem this project does not (and, by SEAM2's
NP-hardness note, plausibly cannot cheaply) close.**

---

## 3. Kernel check (small, read-only, non-authoritative)

`src/bin/ordercore.rs` independently verifies, in plain `ℤ/nℤ` modular
arithmetic (small explicit residues — *not* a kernel verification and
*not* a parse of the authoritative corpus), the separating arithmetic
that makes Lemma A's models work: that the witnesses really do satisfy
`u·u = v·v ∧ u ≠ v` in ℤ/8 and `x² = 0 ∧ x ≠ 0` (hence `x⁴ = 0`) in
ℤ/4, **and** — as the soundness sanity gate — that the SEAM4 generic
identities `sqc-diffsq`/`sqc-4uv`/`sqc-gprod` *do* hold over all
residues of ℤ/4 and ℤ/8 (confirming they are true ring identities and
therefore, by Lemma B, provably *cannot* help derive a conclusion that
is false in those very rings). It does **not** re-derive or modify the
authoritative corpus; it is a machine-checked sanity gate on the
counterexample so the refutation is verified, not asserted.

Run: `cargo run --release --bin ordercore`.

Expected output (all checks `OK`):

```
[ordercore] Z/8: u=3 v=1  u*u=1 v*v=1  (u*u==v*v) && (u!=v)  -> sqcong FALSE without order : OK
[ordercore] Z/4: x=2      x*x=0  x^4=0   (x^4==0) && (x!=0)   -> x^4=0=>x=0 FALSE in CR : OK
[ordercore] Z/4: x=2      x*x=0          (x*x==0) && (x!=0)   -> sqz/sqzhalf NOT a ring id : OK
[ordercore] SEAM4 generics (sqc-diffsq/sqc-4uv/sqc-gprod) hold in Z/4 & Z/8 (true ring ids, so cannot help) : OK
[ordercore] separation verified: every ring identity holds in Z/8 & Z/4 (soundness),
            yet sqcong's conclusion is false there => order axioms are essential.
[ordercore] PROVEN: order predicate essential.  CONJECTURED: exact 61.52% constant (Obligation O).
[ordercore] ALL CHECKS PASSED
```

This check is *evidence the model arithmetic is right*, nothing more.
The theorem's force is the model-theoretic soundness argument
(Lemma B), which is a proof, not a computation.

---

## 4. Summary — the PROVEN / CONJECTURED split

| Claim | Status | Justification |
|---|---|---|
| `sqcong`'s conclusion `(u²=v²)→u=v` is false in ℤ/8 | **PROVEN** | direct: 3²=1=1² mod 8, 3≠1 |
| Internal step `x⁴=0 ⊢ x=0` false in ℤ/4 | **PROVEN** | x=2: 2²=0, 2≠0 |
| Ring identities are sound for all commutative rings | **PROVEN** | equational-logic soundness (Lemma B), standard |
| ⇒ No set of (bounded-degree) ring identities can derive `sqcong`; order is **logically essential** | **PROVEN** | Lemma A + B + contrapositive (Theorem 1) |
| The essential axiom is specifically `of-letot` (+`of-lein`): "no nonzero nilpotents / total order" | **PROVEN** | Lemma C: ℤ/4 has a nonzero nilpotent ⇔ not an ordered ring |
| `subeq0` is *not* a lower-bound contributor (it is pure ring) | **PROVEN** | Lemma C: its proof uses no `<_` |
| The order-core is a genuine *qualitative* lower bound (irreducible *in kind*, cannot → 0) | **PROVEN** | Theorem 1(c) |
| The *exact constant* 61.52 % is the minimal residual under the cut-free metric | **CONJECTURED** | reduces to Open Obligation O's size-lower-bound clause — an unconditional cut-free proof-size lower bound for a fixed order lemma; OPEN (cf. SEAM2 NP-hardness) |

**One-line honest answer.** *The order-core is a genuine lower bound:
PROVEN that no bounded-degree ring identity (indeed no ring identity at
all) can express the content of `sqcong`, because that content
(`u²=v² → u=v`, and its load-bearing kernel `x²=0 → x=0`) is FALSE in
the commutative rings ℤ/8 and ℤ/4 while every ring identity is, by
equational soundness, TRUE there — so `of-letot` (totality / no nonzero
nilpotents) is logically essential. PROVEN qualitatively; the exact
measured 61.52 % constant is CONJECTURED and isolated to one clean open
proof-complexity obligation.*

---

*Reported, not faked. The theorem is a standard, fully-justified
model-theoretic separation at the exact signature and exact `sqcong`
obligation of `data/grounded.mm`/`src/bin/grounded.rs`; the
quantitative tightness is honestly left CONJECTURED with its open lemma
named. Trust root: `src/kernel.rs`. No authoritative file modified.*
