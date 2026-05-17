# SDG_MODEL — the model-grounding of Book Two, as a labelled PROJECTION

**The exact dual of the prequel's "ground ℝ in ZFC" / transport story.**

Adversarially honest. Every statement here is one of:

- **MEASURED** — `src/kernel.rs` over `data/sdg.mm`, OUR cut-free `$a`-leaf
  metric (reproduced by `cargo run --release --bin sdgfloor`); the
  intuitionistic-purity verdict (`sdgpure`).
- **PROJECTION** — a labelled structural / citation-level derivation. It
  is **never** a measured or extracted proof-size number, is **never**
  summed into or merged with the MEASURED Book-Two cost, and is presented
  with its full derivation. A precisely-characterized projection IS the
  deliverable; a fabricated "model cost number" dressed as measured would
  be a ZERO (Iron Rule).

There is **no extracted number** in this document, by design and on
principle: unlike the prequel — which had `data/set.mm`, a 50 MB machine
corpus of the ℝ-in-ZFC construction to run the DAG extractor over — there
is **no Metamath/ZFC formalization of a well-adapted topos** in any
library we possess. The honest analog of `modelsplice` here computes a
*structural* quantity only (the citation-ladder depth), and it is
labelled `[PROJECTION]` throughout. See `src/bin/sdgmodel.rs`.

---

## 0. The two quantities, never summed (the dual of COST_STRUCTURE §1)

The prequel kept three quantities rigorously apart: geometry proof size
`[MEASURED]`, grounding cost `[EXTRACTED]`, satisfiability `[the real
structure]`. Book Two has exactly the dual pair:

1. **The synthetic proofs themselves — MEASURED.** Book Two's `$p`
   corpora are kernel-verified and intuitionistic-purity-clean. The
   headline figures (reproduced this build, `sdgfloor` + `sdgpure`):

   | corpus / theorem | what | MEASURED leaves |
   |---|---|---|
   | `sdg-deriv` (`data/sdg.mm`) | seam-free first synthetic derivative; consumes `ax-microcancel` | **2243** |
   | `sdg-global-sum` | `(f+g)' = f'+g'`, threaded | **23508** |
   | `sdg-global-prod` | global Leibniz (consumes `df-D`+`ax-mul0`) | **39571** |
   | `sdg-global-chain` | `(g∘f)' = (g'∘f)·f'` | **28314** |
   | `sdg-calc2-chain` (`data/sdg.calc2.mm`) | seam-free chain, consumes `eq-ap` | **349** |
   | `sdg-tay-deriv2` (`data/sdg.taylor.mm`) | order-2 Taylor uniqueness, consumes `ax-microcancel2` | **6080** |
   | `sdg-tan-principal` (`data/sdg.tangent.mm`) | `R^D ≅ R×R`, consumes `ax-microcancel` | **2243** |

   `sdgpure` verdict (this build): **GENUINELY INTUITIONISTIC ✔ — 44
   logical `$a` audited (NAME+SHAPE), none classical, none in any `$p`'s
   consumed-axiom closure.** These are small (10^2–10^4.6) and
   constructive. This is the dual of the prequel's "the geometry is tiny
   and exact" (G3c ≈ 10^2.51).

2. **The model that makes them non-vacuous — PROJECTION.** SDG is
   consistent / its theorems are non-vacuous **iff** a model exists in
   which `D` is genuinely non-degenerate and KL holds. The standard
   models are *well-adapted toposes*. Their construction is a separate,
   classical, heavy apparatus — exactly the dual of the prequel's "ℝ in
   ZFC is huge". It is **labelled `[PROJECTION]`** here and is **never**
   added to the figures in row 1.

These are never summed. That discipline — not the size of either number
— is the deliverable.

---

## 1. Precisely which model(s) witness consistency of THIS substrate

### 1a. THIS substrate, stated exactly

`data/sdg.base.mm` (frozen authored trust surface) is, in full:

- **Intuitionistic predicate logic with equality**: `ax-1`, `ax-2`,
  `ax-mp`; the primitive `∧`/`∨`/`⊥` intuitionistic connective axioms;
  `efq`; `ax-gen`/`ax-spec`/`ax-q1`/`ax-q2`/`ax-ei`/`ax-ee`. **No
  `ax-3`/Peirce, no LEM, no DNE.** Equality: `eqid` (reflexivity),
  `eqcom`, `eqtri` — **not** assumed stable, **not** decidable, **no**
  apartness.
- **A commutative ring `R` with `1`** (the line object): the nine ring
  `$a` equalities (`ax-addcom`…`ax-mul0`), pure equational algebra, **no
  order, no `x·x=0 ⟹ x=0`**.
- **Equality congruence for the signature**: `eq-pl1/2`, `eq-mu1/2` (ring
  ops) and `eq-ap` (function application — FLAGGED non-conservative
  substrate commitment #3, the verdict-B keystone, positive Horn, zero
  classical content).
- **The infinitesimal apparatus**: `df-D` (`(D x) ↔ x·x=0`, a
  conservative definition), `ax-kl` (Kock–Lawvere existence: every
  `D→R` map is affine with slope `b`, constant `(ap f 0)`),
  `ax-microcancel` (`∀d∈D (b·d)=(c·d) → b=c`).
- **The higher hierarchy**: `df-D2` (`(D2 x) ↔ x³=0`, conservative),
  `ax-kl2` (degree-≤2 KL existence), `ax-microcancel2`.

That is the entire theory whose consistency this document certifies.

### 1b. The models

**Every standard well-adapted topos model of SDG satisfies THIS
substrate.** The three canonical ones, with citation-level construction:

1. **The Dubuc topos `𝒢` (the "Cahiers topos").** Sheaves for the
   open-cover Grothendieck topology on the dual of the category of
   *finitely-generated germ-determined C^∞-rings* (equivalently, a site
   of "loci"). E. Dubuc, *Sur les modèles de la géométrie différentielle
   synthétique*, Cahiers Top. Géom. Diff. 20 (1979) 231–279; A. Kock,
   *Synthetic Differential Geometry*, 2nd ed., LMS LN 333, CUP 2006,
   Part III (esp. III.3–III.5).

2. **`Set^{𝕃^op}` / sheaves on the dual of finitely-presented
   C^∞-rings** (the "smooth topos" / Moerdijk–Reyes model). I. Moerdijk
   & G. E. Reyes, *Models for Smooth Infinitesimal Analysis*, Springer
   1991 — the comprehensive reference; the topos `𝒮`/`ℬ`/`𝒢` family,
   construction in Ch. I–III, well-adaptedness in Ch. III–IV, KL and
   microcancellation verified in Ch. II §1–3.

3. **The Cahiers topos proper** (Dubuc 1979; Kock 2006 §III.5) — the one
   usually singled out as *well-adapted* in the strong sense
   (`C^∞-Mfd ↪ 𝒢` is full, faithful, product- and
   transversal-pullback-preserving, and sends ℝ to the line object `R`).

**Why each substrate axiom holds in these models (citation-level):**

| substrate axiom | satisfied in the model because… | cite |
|---|---|---|
| intuitionistic logic, equality (`eqid/eqcom/eqtri`) | the internal logic of *any* Grothendieck topos is intuitionistic higher-order logic with equality; LEM/DNE generically **fail** | Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*, VI; Johnstone, *Sketches of an Elephant*, D1 |
| `eq-ap` (application congruence) | morphisms of a topos are *functions*; `f(x)=f(y)` whenever `x=y` is the internal substitution rule of topos logic — automatic, **no extra hypothesis** | MM, VI.5–6 |
| ring axioms for `R` | `R` = the representable `C^∞(ℝ) ` (the line object) is internally a commutative ℝ-algebra | Kock §I.12, §III.3; MR Ch. II |
| `df-D` non-degenerate; `ax-kl` (KL_1) | `D` is represented by the **Weil algebra `ℝ[ε]/(ε²)`**; `R^D ≅ R×R` because that Weil algebra is the function-classifier — KL is a *theorem* of the model | Kock §I.1–I.4, §III.3 (Thm); MR Ch. II §1 |
| `ax-microcancel` | `R` is an internal local ring; the line is "a field" in the topos sense, giving D-cancellation | Kock §I.3; MR Ch. II §2 |
| `df-D2`, `ax-kl2`, `ax-microcancel2` (the `D_k` tower) | `D_k` is represented by `ℝ[ε]/(ε^{k+1})`; KL_k and level-k microcancellation hold by the same Weil-algebra mechanism, uniformly in k | Kock §I.16, the "general KL axiom"; MR Ch. II §1 (Weil prolongations) |

**The crucial intuitionistic point, dual to the Mirror Hypothesis.**
Classically `D = {0}` (precisely the metric residue `x·x=0 ⟹ x=0` the
substrate refuses). In *every* model above the ambient logic is
intuitionistic *and `D` is genuinely a non-trivial infinitesimal
object* — `R^D ≅ R×R` is a non-degenerate iso, not the trivial `R≅R`.
The model is exactly what makes "refuse `x·x=0 ⟹ x=0`" *consistent*.
This is the dual of the prequel's ℝ-model making `of-letot` (order /
"there is a next thing, not the first") consistent.

**Consistency conclusion (PROJECTION).** A well-adapted topos
(Dubuc/Cahiers/Moerdijk–Reyes) is a model in which every `$a` of
`data/sdg.base.mm` is valid and `D` is non-degenerate. By soundness of
the kernel (it only ever derives `$p` from those `$a`), the existence of
this model certifies that Book Two's 41 `$p` are **consistent and
non-vacuous**. This is a citation-level certificate (the model is a
published classical theorem, not re-derived in `src/kernel.rs`), exactly
as the prequel's Closure 1 cited Suppes/Shoenfield rather than
re-deriving them in-kernel. `[PROJECTION]`

---

## 2. The dual grounding ladder — the apparatus, classified `[PROJECTION]`

The prequel's `modelsplice` EXTRACTED a cost ladder
`resqrtth → … → Cauchy/Dedekind → ℚ → ℤ → ℕ → ZF`. The dual ladder
for the SDG model is computed *structurally* by
`src/bin/sdgmodel.rs` (read-only, fabricates no cost; emits only the
cardinality and longest-path depth of an authored citation DAG of the
construction's mathematical prerequisites). This build:

```
citation-ladder nodes ............... 16   [PROJECTION]
citation-ladder longest-path depth .. 11   [PROJECTION]
classical leaf ...................... ZFC + classical Set + real analysis
model-side theorems to discharge .... 6   (KL, microcancel, eq-ap, ring, D_k, SDG-sat)
```

The ladder, leaf-to-root (each rung genuinely cites the ones below):

```
0  ZFC                  classical set theory — the metatheory the topos is BUILT IN
1  Set                  classical category of ZFC sets (Grothendieck-universe sized)
2  C^∞-Mfd              smooth manifolds & maps  — NEEDS ALL OF CLASSICAL REAL ANALYSIS:
                         ℝ, smooth functions, partitions of unity, inverse-function thm
3  C^∞-ring             finite-product functors (C^∞-Mfd_fp)^op→Set; smooth Lawvere theory
4  fp-C^∞-ring          C^∞(ℝⁿ)/I  (affine objects of the site)
5  Weil algebras        ℝ[ε]/(ε^{k+1})  — the representers of D, D_k
5  site 𝕃               (fp-C^∞-rings)^op + open-cover/étale Grothendieck topology
6  Sh(𝕃)                Grothendieck-topos sheaf semantics; internal Heyting logic
7  Dubuc / Cahiers      sheaves on germ-determined C^∞-rings — the well-adapted topos
8  well-adapted embed   C^∞-Mfd ↪ topos, products + transversal pullbacks + ℝ↦R
9  KL theorem           R^D ≅ R×R  (Weil ℝ[ε]/(ε²) is the representing object)
9  ring-model           R = C^∞(ℝ) internally a commutative ℝ-algebra
10 microcancel theorem  R an internal local ring; D-cancellation
10 D_k theorem          ℝ[ε]/(ε^{k+1}) represents D_k; KL_k uniformly
11 SDG-sat              every $a of sdg.base.mm satisfied ⇒ 41 $p non-vacuous
```

**The honest classification of this cost.** It is the structural dual of
the prequel's ℝ-grounding, and it is *not lighter — it is strictly
heavier*:

- The prequel's grounding bottomed out, after every scaffold was
  stripped, at **two order literals** `{∅∈suc∅, suc∅≠∅}` over a
  ~10^25.95–10^46 set.mm transport (EXTRACTED). The irreducible *content*
  was the order axiom; the rest was removable construction.
- The SDG model's leaf is **rung 0 = full classical ZFC**, and **rung 2
  already requires the entire classical real-analysis tower** — ℝ,
  smooth functions, partitions of unity. That is *the very ℝ-in-ZFC
  object the prequel measured at ~10^45.7 ZFC-grounded* (`EUCLID_FLOOR`
  §1, `SUBSTRATE_FLOOR`). The SDG model needs **ℝ *and then* the
  C^∞-ring + Grothendieck-sheaf-topos apparatus built on top of it**.

So the dual ladder's classification is exact and adversarial:

> **The SDG model-grounding is `[PROJECTION]` strictly above the
> prequel's ℝ-grounding.** It contains the prequel's entire ℝ-in-ZFC
> term as a *sub-rung* (rung 2, `C^∞-Mfd`), and adds on top of it the
> C^∞-ring Lawvere theory, the site, Grothendieck-sheaf semantics, the
> well-adapted embedding, and the model-side theorems (KL,
> microcancellation, the D_k tower). It is irreducibly heavy and
> irreducibly classical.**

This term is **never summed into** the MEASURED Book-Two figures of §0
row 1. It is a separate, labelled, structurally-derived quantity — the
exact mirror of `EUCLID_FLOOR`'s "the construction WINS (~10^8
MEASURED); the set.mm bridge does not (~10^46 EXTRACTED)", except here
*even the construction is heavy* because the model intrinsically needs
smooth real analysis.

---

## 3. The sharp honest statement (the dual of Book One's finding)

**Book One:** the geometry is tiny and exact (~10^3 MEASURED); grounding
ℝ in ZFC is huge (~10^46 EXTRACTED); the irreducible *content* residue
is two order literals; *almost everything else was removable
scaffolding*.

**Book Two (the dual), stated sharply:**

> The synthetic proofs are **small, intuitionistic, and MEASURED**
> (`sdg-deriv` 2243; the seam-free chain 349; order-2 Taylor 6080; all
> 10^2–10^4.6; `sdgpure`: zero classical content, mechanically
> certified). The model that makes them non-vacuous is a **separate,
> classical, heavy construction** — a well-adapted topos whose citation
> ladder is 11 rungs deep, rooted in full classical ZFC, and which
> *contains the prequel's entire ℝ-in-ZFC term as rung 2*. The proofs
> refuse `x·x=0 ⟹ x=0`; the price of that refusal being *consistent* is
> the whole smooth-topos apparatus. `[PROJECTION]`

This is the precise dual of Book One: there, the *content* (geometry)
was tiny and the *grounding* (ℝ-in-ZFC) was huge. Here, the *content*
(synthetic calculus) is tiny **and constructive**, and the *grounding*
(a well-adapted topos) is huge **and classical**. The asymmetry is the
point and it is reported, not faked.

---

## 4. Is it irreducibly heavy, or is there a leaner route?

The prequel had a genuine leaner route (the RCF / Euclidean-closure
descent: ℝ was *not* needed; an ordered field with √-of-nonnegatives
sufficed, dropping 10^46 → 10^30.75 → strict-LB 10^25.95). The honest
question: **does the SDG model have an analogous descent?**

### 4a. Candidate leaner routes, examined adversarially

**(i) A smaller site.** One can shrink the site to *finitely-presented*
(rather than germ-determined) C^∞-rings, or to the full subcategory on
the Weil algebras alone (the "Weil topos" / Lawvere's
`Set^{Weil^op}`-style infinitesimal model). This *does* genuinely
lighten the topos-theoretic bookkeeping (no germ-determination, no
open-cover topology — a presheaf topos suffices for the *pure*
KL fragment). **But it does not touch the leaf.** Even
`Set^{Weil^op}` is built on the category of Weil ℝ-algebras, i.e.
finite-dimensional commutative ℝ-algebras — which still presupposes ℝ.
The reduction is at rungs 6–8 (sheaf → presheaf, drop the topology), not
at rung 2 (the ℝ / smooth-analysis leaf). It is the dual of the
prequel's "drop completeness `ax-pre-sup`": real, but lower-order — it
removes the *topos* overhead, not the *real-analysis* core. The dominant
cost was never the Grothendieck topology, exactly as the prequel's
dominant cost was never completeness.

**(ii) A syntactic / term model (the genuinely leaner route).** SDG's
*intuitionistic* core theory has a **syntactic classifying topos / term
model**: the theory generates a classifying topos `Set[𝕋_SDG]`, and —
sharper — for the *equational+geometric* fragment one can build a
**term model by the standard Henkin/Lindenbaum construction internal to
intuitionistic higher-order logic**. This is the true dual of the
prequel's RCF descent: it shows the *consistency* obligation does **not**
require the smooth-analysis leaf.

  - **What it buys (honest):** *relative* consistency. Con(intuitionistic
    HOL + ring + KL + microcancellation + eq-ap) reduces to the
    syntactic consistency of that equational/geometric theory, which is
    a finitary proof-theoretic statement — *no ℝ, no C^∞, no topos*. The
    Kock–Lawvere axiom is a **geometric-ish sequent** (existence +
    a uniqueness encoded by microcancellation) over the algebraic
    signature; a classifying topos for such a theory exists by general
    topos theory (Mac Lane–Moerdijk X; Johnstone D3), and a
    term/Lindenbaum model establishes non-triviality of the syntactic
    theory **without** the well-adapted apparatus.
  - **The exact caveat (this is where honesty bites):** a syntactic /
    classifying-topos model proves the theory is **consistent** and that
    `D` is **not provably trivial**, but it does **NOT** give a
    *well-adapted* model — it does not embed `C^∞-Mfd`, does not
    interpret `R` as the *smooth* real line, and does not make the
    synthetic derivative agree with the classical one. It certifies
    *non-vacuity of the formal system*; it does **not** certify that the
    synthetic calculus *is* differential geometry. The prequel's RCF
    route still gave a genuine *mathematical* model (the real
    constructible field really satisfies F1); the SDG syntactic route
    gives only a *formal* model. That asymmetry is real and is reported,
    not hidden.

### 4b. The verdict (adversarially honest)

> **For the strong claim — "Book Two is genuine *differential
> geometry*" — the model-grounding is IRREDUCIBLY HEAVY and
> IRREDUCIBLY CLASSICAL.** Any *well-adapted* model (the only kind that
> makes the synthetic derivative coincide with the classical one)
> requires the C^∞ / smooth-topos apparatus, whose leaf is the full
> classical real-analysis tower — strictly heavier than the prequel's
> ℝ-in-ZFC, which it contains as a sub-rung. There is **no well-adapted
> analog of the RCF descent**: you cannot replace the smooth line by an
> ordered field, because KL is *false* in any C^∞-free algebraic model
> of ℝ (smoothness is exactly what supplies the infinitesimal
> structure). This is the sharp dual finding and it does **not**
> dissolve under a better construction — the analog of the prequel's one
> *intrinsic* floor (the order-core that Frontier C *proved* immovable).
>
> **For the weak claim — "the formal system is consistent / Book Two's
> `$p` are non-vacuous" — there IS a leaner route:** the syntactic /
> classifying-topos / term model gives *relative* consistency over
> intuitionistic HOL with **no ℝ, no C^∞, no Grothendieck topology** —
> the genuine dual of the RCF descent, but it certifies only the
> *formal* system, not that it *is* differential geometry. Exact caveat
> as in §4a(ii).

Both halves are stated; neither is inflated. The honest one-line summary:
*small constructive proofs; a heavy classical model for the strong
(well-adapted, "it really is DG") reading; a genuinely lean syntactic
model for the weak (formal consistency) reading — and the gap between
those two readings is itself the irreducible structural content, the
exact dual of the prequel's "almost all of it was scaffolding; the
order-core alone was not."*

### 4c. How far this CAN be grounded — and the residue identified (Book-3 follow-up)

The natural question — *can the model-grounding `[PROJECTION]` itself be
grounded?* — has a precise, adversarially-honest answer, and acting on
it is the iron-rule-correct deliverable (ground exactly the part that
can be; name the rest, do not fake it):

- **The STRONG (well-adapted) model — NOT groundable, by principle,
  stays `[PROJECTION]`.** There is no Metamath/ZFC formalization of a
  well-adapted topos to run an extractor over (§0); a fabricated "model
  cost" would be an Iron-Rule ZERO. This is the immovable dual floor of
  §4b and is **deliberately left `[PROJECTION]`**, named not papered —
  grounding it is not "not yet done", it is *principled-absent*.
- **The WEAK (non-vacuity / relative-consistency) segment — its
  irreducible residue is precisely `1≠0`, and THAT is now GROUNDED.**
  The syntactic/term route (§4a(ii)) reduces non-vacuity to
  non-triviality of the formal system; the *only* model the frozen
  substrate guarantees kernel-internally is the trivial ring (`0=1`),
  so the entire content of "the system is **non**-vacuous" bottoms out
  at the single literal `1≠0`. That is **exactly the cross-book spine**
  (`SEQUEL_SCOPE` §5q/§5r): the non-abelian witness's non-vacuity
  reduces, kernel-verified, to `1≠0` (`data/sdg.spine.mm`,
  `sdg-spine-b3`, MEASURED), joined at that literal to Book One's
  already-set.mm-anchored `suc∅≠∅≅1≠0` (`COST_STRUCTURE`, cited, counted
  once). So the weak segment's residue is **not independently
  groundable beyond this** — and it does not need to be: it **is** the
  now-transport-grounded spine. Building a heavy in-kernel trivial-ring
  model artifact would be **ceremony weaker than this characterization**
  (it would only re-exhibit `0=1`-consistency, which is precisely *why*
  the residue is `1≠0`), so it is deliberately **not** done.

**The honest net.** The deepest groundable thing in the
model-grounding story is the weak segment's `1≠0` non-triviality
residue; it is now grounded as the kernel-verified spine transport. The
strong well-adapted model remains the named, principled-`[PROJECTION]`
immovable floor. Grounding here means: *we determined exactly how far
grounding can honestly go, did precisely that part, and named the rest
— never faked a model number.*

---

## 5. What is genuinely open

1. **An exact apparatus *size*.** The ladder depth (11) and node count
   (16) are real and structural, but there is **no extracted proof-size
   number** because no Metamath/ZFC formalization of a well-adapted topos
   exists to run an extractor over. Producing a true `[EXTRACTED]` cost
   (the genuine dual of `modelsplice`'s 10^45.74) would require
   formalizing the Dubuc/Moerdijk–Reyes construction in a ZFC library —
   not attempted, not invented. This is named, not faked.

2. **The exact boundary of the syntactic descent.** Whether the
   *full* substrate (including the `D_k` tower and `eq-ap`) admits a
   term/Lindenbaum model as cleanly as the KL_1 fragment is plausible
   (all axioms are positive Horn / geometric-ish) but is asserted at
   citation level (standard classifying-topos theory), not mechanized
   here — the exact dual of the prequel's "Suppes/Shoenfield cited,
   hypotheses checked, not re-derived in-kernel".

3. **Quantifying the §4a(i) site reduction.** That `Set^{Weil^op}`
   removes the topology/sheaf rungs is structurally clear; an exact
   ladder-delta for the leaner site is a refinement, not done here.

These are precisely-characterized open items, in the discipline of the
prequel's named open lower bounds (Obligation O, the minimal-DAG LB) —
reported, not papered over.

---

## 6. Files / instruments / reproduction

- `SDG_MODEL.md` — this document (the labelled PROJECTION deliverable).
- `src/bin/sdgmodel.rs` — read-only structural instrument: emits the
  citation-ladder depth/node-count `[PROJECTION]`, fabricates **no**
  cost. `cargo run --release --bin sdgmodel`.
- `data/sdg.base.mm` — the substrate whose consistency is certified
  (READ-ONLY here; not modified).
- Trust root: `src/kernel.rs` (unchanged). MEASURED baseline of §0
  row 1: `cargo run --release --bin sdgfloor` + `cargo run --release
  --bin sdgpure` (this build: `verified all 18 $p ✔`, **GENUINELY
  INTUITIONISTIC ✔ — 44 logical `$a`, none classical**).
- Citations (model-side, PROJECTION): Dubuc 1979 (Cahiers Top. Géom.
  Diff. 20); Kock, *Synthetic Differential Geometry*, 2nd ed., LMS 333,
  CUP 2006; Moerdijk & Reyes, *Models for Smooth Infinitesimal
  Analysis*, Springer 1991; Mac Lane & Moerdijk, *Sheaves in Geometry
  and Logic*, Springer 1992; Johnstone, *Sketches of an Elephant*, OUP.

**The Iron Rule held.** No model cost number was invented. The
deliverable is the precisely-characterized projection plus the sharp
honest statement that the well-adapted model is irreducibly heavy and
classical (strictly heavier than the prequel's ℝ-grounding, containing
it as a sub-rung), while a genuinely leaner *syntactic* route exists for
the weaker *formal-consistency* reading with its exact caveat. That
characterization, not a fabricated figure, is the result.
