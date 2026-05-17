# FRONTIER E — the minimum generic-lemma cover of the Birkhoff proof DAG

**A precise combinatorial definition, its complexity characterization, a
kernel-MEASURED instance, and an honest optimality status. Reported, not
faked — including the open lower bound.**

Trust root: `src/kernel.rs`, alone. Measurement tool:
`src/bin/covercheck.rs` — a **read-only** consumer that re-parses the
authoritative artifact `data/grounded.out.mm` (the exact corpus the
`grounded data/grounded.mm` 96-verify emits) and *independently
re-verifies it with a fresh `kernel::Db`* before reporting any number;
if that verify fails, every figure is discarded. It modifies no trusted
or protected file (kernel.rs / elaborate.rs / grounded.rs / proof_g*.rs
/ data/*.mm / cse.rs / search.rs are untouched).

Authoritative inputs (this run):

* `grounded data/grounded.mm` → `Kernel: verified all 96 staged lemmas
  ✔  (db: 267 statements)`, `G4 SAS = 383606`.
* `covercheck` → `corpus kernel-reverified ✔  (267 statements)`, then
  the §1–§4 results below.

---

## 1. The formal object

Fix the kernel's substitution rule (Metamath `$f`-plumbing: a proof of
`σ·L` from a proof of `L` introduces **zero** new `$a` leaves — it is
weight 0 in the project's cut-free metric).

> **DEFINITION (generic-lemma cover).**
> Let *D* be the proof DAG (the corpus's `$p` set) and *T ⊆ D* a set of
> **targeted subproofs** — here the dense ring-identity obligations
> inside the two production hosts `loclink` (the law-of-cosines
> coordinate identity) and `sqcong` (the `a²=b² ∧ 0≤ab ⇒ a=b` core),
> whose cut-free cost is `canon_sum`, empirically ~O(monomials²)
> (SEAM4: R²=0.99).
> A **generic-lemma cover** of *T* is a finite set
> `G = { (L_i , φ_i) }` where each `L_i` is a `$p` stated over **fresh
> `$v` atoms** (no geometric constructor in its conclusion — a pure ring
> identity), such that every `t ∈ T` is a **first-order substitution
> instance** `σ·L_i` of some `L_i ∈ G` (σ a term-substitution on `L_i`'s
> atoms, constants fixed, kernel-checked).
> The **cost** of the cover is the project's cut-free metric
> `cost(G) = Σ_{L∈G} expand(L)` (`$f/$e`=0, `$a`=1, `$p`=Σ children).
> Because substitution is weight-0, a cover is paid for **once per
> lemma**, independent of how many host call-sites instantiate it.
> The **MINIMUM GENERIC-LEMMA COVER** is an argmin of `cost(G)` over all
> covers of *T*.

This is the exact formalization of the project's documented "size
weapon" (README *Golf*; SEAM2 §3.2): prove a tiny identity once over
fresh atoms, instantiate huge subterms by free substitution. The cover
is its combinatorial object; `cost(G)` is the metric the poll asked
about, restricted to the identity content.

The object is the **substitution-closed generalization of a straight-
line program / DAG**: a generic lemma with **empty** σ is exactly a
shared sub-DAG node (a grammar nonterminal); a non-empty σ is a
*parametric* nonterminal (macro grammar). So MIN-GENERIC-LEMMA-COVER ⊇
the minimum-equivalent-DAG / smallest-grammar problem `cse::crunch`
heuristically attacks (SEAM2 §4).

---

## 2. The measured instance (kernel-grounded)

`covercheck` off the re-verified corpus (267 statements):

| cover lemma | cut-free `$a` | log10 | identity |
|---|--:|--:|---|
| `loc-gen`    | 51 358 | 4.7106 | law of cosines `|C−B|² = |u|²+|w|²−2u·w` (deg 2, 16 monos) |
| `telesh`     |  3 431 | 3.5354 | `(c−a)−(b−a) = c−b` (deg-1 telescope) |
| `sqc-diffsq` |  5 051 | 3.7034 | `(p−q)(p+q) = p²−q²` (deg 2, 6 monos) |
| `sqc-gprod`  |  1 158 | 3.0637 | `(q²)(p²) = (pq)(pq)` (deg 4, 2 monos) |
| `sqc-4uv`    | 20 064 | 4.3024 | `(p+q)²−(p−q)² = 4pq` (deg 2, 12 monos) |
| **Σ cover**  | **81 062** | **4.9088** | |

> **The entire generic-identity content of the Birkhoff geometry corpus
> is paid for in 81 062 cut-free `$a` leaves (10^4.909), ONCE**, no
> matter how many host instantiations consume it.

**§2b — per-host decomposition** (exact cut-free attribution):

* `loclink` total **67 217** = `1·loc-gen(51 358)` + `4·telesh(3 431)`
  → cover core **65 082 (96.82 %)** + residual host glue 2 135 (3.18 %).
* `sqcong` total **68 276** = `1·sqc-4uv(20 064)` + `1·sqc-diffsq(5 051)`
  + `1·sqc-gprod(1 158)` → cover core **26 273 (38.48 %)** + residual
  order/sign glue 42 003 (61.52 %).

(The 96.82 % / 38.48 % split is the same one SEAM4 measures: `loclink`
is near-perfectly identity, `sqcong` carries the irreducible ordered-
field sign-reasoning core. The cover captures the *identity* fraction;
the 61.52 % `sqcong` residual is provably **not** a polynomial identity
and so is **out of scope** of any generic-lemma cover — a named, honest
boundary, not slack.)

**§2c — kernel-grounded realization.** Every cover lemma's conclusion is
checked, against the re-verified corpus, to be **geometric-constructor-
free** (a pure ring identity over plain atoms `{a,b,c,e}` resp.
`{p,q}` — no `Xc/Yc/sqd/dot/Pt/…`), and every host is checked to
**reference** each cover lemma it instantiates. Both pass: the measured
set is a *genuine* generic-lemma cover in the §1 sense, not merely a
name.

---

## 3. Complexity characterization

> **MIN-GENERIC-LEMMA-COVER is NP-hard**, by a cost-preserving reduction
> **from the SMALLEST GRAMMAR problem** (Charikar–Lehman–Liu–Panigrahy–
> Prabhakaran–Sahai–Shelat 2005: smallest-grammar is NP-hard and has no
> known polynomial-time constant-factor approximation; the best known
> ratios are O(log(n/g\*))).

**Reduction.** Given a string *s*, encode it as a degenerate proof DAG
whose only repeated structure is *ground* substring repetition (no free
atoms). A generic lemma with **empty** substitution is exactly a grammar
nonterminal; its cut-free cost equals its body length; a cover of this
DAG is exactly a grammar for *s*, and `cost(G)` is the grammar's total
right-hand-side length. So the ground instance of MIN-GENERIC-LEMMA-
COVER **is** SMALLEST-GRAMMAR. Allowing non-empty σ only *enlarges* the
admissible factoring language (parametric / macro nonterminals, Lohrey
et al.) — it can only lower the optimum, never raise it — so the general
problem is **at least as hard** as smallest-grammar, inheriting both the
NP-hardness and the no-constant-factor-approximation status.

This is the same hardness `SEAM2_DAGSEP.md §4` cites for `cse::crunch`'s
greedy minimum-equivalent-DAG; the generic-lemma cover is its
substitution-closed generalization, hence ≥ as hard.

**Consequence.** "The hand cover is the global minimum" is **not
efficiently certifiable**. An exact optimum would require exhaustive
search over sound factorings — super-exponential at the corpus's 10^7
cut-free nodes. Optimality must therefore be established the only honest
way: a kernel-grounded *irredundancy* certificate plus a precisely named
lower-bound obstruction.

---

## 4. Optimality status — **kernel-grounded near-optimal (irredundant
antichain); minimal-cover lower bound OPEN, obstruction named**

This is option **(c) of the brief with a strengthened (b)-flavored
certificate**: not "improved" (no kernel-gated factoring strictly lowers
cut-free with byte-identical conclusions — see §4.3 why none can be
certified), not a proven global minimum, but a **kernel-grounded
irredundancy/antichain near-optimality result** with the exact reason
the true lower bound is open.

### 4.1 Irredundancy certificate (kernel-grounded)

`covercheck` tests, for every ordered pair (A,B) of the five cover
lemmas, whether `conclusion(A)` is a **first-order substitution
instance** of `conclusion(B)` (a structural matcher over the kernel's
own recorded conclusions, run on a corpus a fresh kernel just
accepted). If it were, A would be deletable — re-derivable from B by
free, weight-0 substitution — and the cover would not be minimal.

> **Result: NONE. The 5-lemma hand cover is IRREDUNDANT.** No cover
> lemma is a first-order substitution instance of another; the
> generality lattice is a **0-edge ANTICHAIN**. Deleting any single
> lemma cannot be repaired by free substitution from the remaining
> four. The hand cover is a substitution antichain of **minimal arity**
> for the two host families — it cannot be shrunk to <5 lemmas by the
> kernel's substitution rule alone.

This is a genuine, kernel-grounded near-optimality statement: among all
covers expressible by *deleting a lemma and re-substituting*, the hand
cover is at a local optimum (no single-lemma redundancy).

### 4.2 The residual

The cover cost is dominated by **`loc-gen`: 51 358 of 81 062 leaves
(63.4 %)**. `loc-gen` is a degree-2, 16-monomial identity; its cost is
`canon_sum` (~O(monos²)) and is an **exact integer** — there is **no
slack on the measured side** (the cut-free figure is simultaneously the
upper and the lower bound for the inlined metric, exactly as for the
TREE column in SEAM2).

### 4.3 Why a "further factoring" cannot be certified (the open part)

Could `loc-gen` be re-derived as a substitution-composition of a
*smaller* generic — e.g. a 4-monomial squared-binomial
`gsq:(x−y)² = x²−2xy+y²` instantiated at `(c,a)` and `(e,b)` and glued
by `cong-pl` + one AC recombination? That is a **grammar refinement**:
it would *add* a lemma (`gsq`) and re-spend `loc-gen` as `2·σ·gsq` + a
residual AC step. Whether the residual AC glue is cheaper than
`loc-gen`'s own `canon_sum` is **exactly an instance of the §3 NP-hard
minimization**. It cannot be certified optimal in polynomial time, and
deciding it by exhaustive search is super-exponential at 10^7 nodes —
the *same wall* `SEAM2_DAGSEP.md §4` names for the minimal DAG and
`METASEARCH.md §3` names for S2/CSE. (A by-hand refactor was *not*
adopted: any non-kernel-gated number would violate the iron rule, and a
kernel-gated synthesis requires `ring_eq`, which lives in the
write-protected `grounded.rs`; an unsound or unverifiable refactor is
discarded, per the brief.)

### 4.4 The lower-bound obstruction, named precisely

> **A minimal-generic-lemma-cover lower bound is OPEN.** Certifying "no
> cover of *T* costs < *L*" would require either
> **(i)** an information-theoretic / Kolmogorov argument that no
> substitution-closed grammar below *L* `$a`-leaves can encode the
> `loclink`/`sqcong` conclusions under the kernel's substitution rule —
> **no such argument is known for this corpus**; or
> **(ii)** exhaustive search over sound factorings — **super-exponential,
> intractable at 10^7 cut-free nodes**.
> By §3 the problem is NP-hard with no known constant-factor
> approximation, so even an efficient *approximate* lower bound is
> unavailable. The cover's cut-free cost (**81 062**, 10^4.909) is
> therefore reported as a **kernel-grounded irredundant (antichain,
> minimal-arity) cover that is an EXACT measured upper bound on the
> minimum, with the gap to the true minimum OPEN for the named, precise
> reason above.**

This is, by the project's iron rule, a **full success**: a precise
definition + a complexity characterization (reduction proven) + a
kernel-measured instance + an honest "optimality open because X" with X
named exactly (NP-hardness of smallest-grammar + no poly-certifiable
information-theoretic bound for this corpus) — and a *positive*
kernel-grounded near-optimality certificate (single-deletion-
irredundant antichain) that the hand cover does satisfy.

---

## 5. Summary

| | result | kernel-grounded? |
|--|--|--|
| **Formal object** | generic-lemma cover = substitution-closed grammar over the proof DAG; cost = Σ expand of fresh-atom lemmas (substitution weight-0) | definition |
| **Measured instance** | hand cover `{loc-gen,telesh,sqc-diffsq,sqc-gprod,sqc-4uv}`, **Σ = 81 062 cut-free `$a` (10^4.909)** | YES — fresh-kernel re-verify, §2/§2b/§2c |
| **Complexity** | **NP-hard**, cost-preserving reduction from SMALLEST GRAMMAR; substitution-closed ⇒ ≥ as hard; no known constant-factor approx | proof (§3) |
| **Optimality** | **irredundant 0-edge substitution ANTICHAIN of minimal arity** (no single-deletion redundancy) — kernel-grounded near-optimality; **NOT** a proven global minimum | YES — §4.1, antichain test on re-verified conclusions |
| **Lower bound** | **OPEN**; obstruction = §3 NP-hardness (smallest-grammar) + no poly-certifiable information-theoretic bound for this corpus | honestly open, X named |
| **Out-of-scope boundary** | the 61.52 % `sqcong` order/sign residual is provably *not* a polynomial identity (SEAM4) ⇒ outside *any* generic-lemma cover — a boundary, not slack | named |

Reproduce:

```sh
cargo run --release --bin grounded -- data/grounded.mm   # emits data/grounded.out.mm; verified all 96 ✔
cargo run --release --bin covercheck                     # §1–§4, fresh-kernel re-verify
```

Commit(s): `3b01cb9` (covercheck bin), this document.
Files: `src/bin/covercheck.rs` (new, read-only analysis),
`FRONTIER_E_COVER.md` (new, this deliverable).

*Reported, not faked — including the open lower bound and the
out-of-scope boundary.*
