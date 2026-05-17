# asagolf — how big is a "simple" proof, really?

A Twitter poll estimated that the fully-expanded, machine-checked proof of a
basic triangle-congruence theorem (**ASA**, in a Birkhoff
ruler/protractor formalism), reduced all the way down to ZFC, exceeds
**10^1000 steps**. This repository answers that by *building the proof
object and counting* — a small sound Metamath-subset kernel plus
hand-built, kernel-re-checked proofs, with exact step counts.

**The short answer:** the geometry is ≈ **10^5.6** (G4 SAS = 383,606
cut-free, golfed ~19× from 10^6.86 by generic-lemma factoring), and
**ASA′ is closed no-cheating end-to-end** — every Birkhoff postulate a
kernel-verified `$p`, no PENDING axiom, case-free. The poll overshoots
the geometry by roughly **994 orders of magnitude**.

Three quantities are reported, and **never summed** — conflating them is
the cheat this project exists to avoid:

1. **Geometry proof size over F1** — ≈ 10^5.6. The poll's actual subject.
   Stands alone as a formal object.
2. **Grounding cost** — if you additionally expand the F1 axioms into
   their ZFC derivations: ≈ **10^45.7** via set.mm's analytic ℝ; an
   exact machine attribution shows that is not completeness but ℤ→ℚ
   construction multiplicity, ≈ **10^30.75** via a real-closed-field
   route, with a strict extractable floor of **10^25.95**.
3. **Satisfiability certificate** — F1 is consistent/non-vacuous: a
   minimal model (the Euclidean closure of ℚ) is *constructed and
   kernel-MEASURED*. The generic √-extension step is 141 leaves
   (10^2.149); the closed ASA′ proof is *measured* to force exactly **one
   un-nested radical** (K = 1), so the proof-relativized construction is
   a fully MEASURED **10^2.149** — no projection (the former ≤10^8.15 was
   a now-superseded K≤10⁶ projection; a model of the *entire F1 schema*
   stays a separate, explicitly labelled projection). This *proves F1
   does not need ℝ*. But certifying the model *inside externally-
   validated set.mm* costs ≈ **10^46** [extracted], because set.mm
   contains no Euclidean / real-algebraic / real-closed subfield to bind
   to. The sharpened thesis, now sharper: F1's model for this proof is
   ~10^2 (measured); the irreducible ~10^46 is *entirely* a property of
   *set.mm's construction choices*, not of F1.

Every digit is kernel-verified or extractor-exact; anything else is
labelled `PROJECTION` with its derivation, never merged into a measured
figure.

A 15-minute foundations-classroom talk is in `docs/slides.html` (press
`S` for speaker notes + timing); the interactive explorer is
`docs/index.html` (live at emberian.github.io/asagolf); the full project
narrative — including the wrong turns — is in [`HISTORY.md`](HISTORY.md).

## Results (exact, kernel-verified)

| quantity | exact | ≈ |
|---|---|---|
| F0 Birkhoff ASA — postulates *asserted* as axioms | 224 cut-free steps | 10^2.4 |
| **G4 SAS** — derived, no cheating (hardest postulate) | 383,606 | **10^5.58** |
| ↳ before generic-lemma golf (loclink+sqcong) | 7,251,714 | 10^6.86 |
| **G3a** ray-angle — derived | 4,720,242 | 10^6.7 |
| **G2** incidence — derived | 607,583 | 10^5.8 |
| G1 ruler · G3b′ prot-uniq · g4a-sss · g3a-dotprop · G0 · G3c | small | 10^3–10^5 |
| **all of the above, one run** | **96 lemmas, 267-statement DB, `verified all ✔`** | |
| **ASA′ regrounded over the derived `$p`** | **CLOSED, no-cheating, no PENDING `$a`** | |
| shared-DAG (cruncher, kernel-verified, lower bound) | 10,134,529 → 1,916,586 | −81% |
| *grounding cost:* full ZFC model of ℝ (set.mm) | — | 10^45.74 |
| same, real-closed-field route (no completeness) | — | 10^30.75 |
| same, strict extractable floor | — | 10^25.95 |
| *satisfiability:* minimal Euclidean model — proof-relativized, **MEASURED** (K=1 distinct un-nested radical) | 141 leaves | **10^2.149** |
| same, full-F1-schema closure (separate, labelled) | — | [PROJECTION] |
| *Stage 2A:* native ℚ-from-ZF (no `CCfld`/analytic ℝ), F1 consequences **MEASURED** | 256 leaves | **10^2.408** |
| same, bare-ZF discharge of asserted signature (labelled) | — | [PROJECTION] ≤10^4 |
| same, certified *through set.mm* (no cheaper √ to bind) | — | 10^46.10 |

"F0 = 224" is the cheap, vacuous answer (assert the postulates).
Everything else is the honest one: every Birkhoff postulate *derived*,
ASA′ closed end-to-end. The three blocks (geometry · grounding ·
satisfiability) are distinct quantities — read down, not across.

## "No cheating", defined precisely

- **Substrate F1**: an ordered commutative ring with 1, **one** square-root
  primitive (`ax-sqrt`, principal root), and first-order logic with
  equality. Nothing geometric is an axiom.
- Points, lines, distance, dot product, angle congruence, the
  oriented-area discriminator (`crs`), the ruler point (`cp`):
  **conservative definitions** (`df-*`), eliminable, scored *Definition* —
  never GenuineAxiom.
- Every Birkhoff postulate (ruler G1, incidence G2, ray-angle G3a,
  protractor-uniqueness G3b, ray-line G3c, SAS G4,
  congruence-substitution G0) is a **kernel-verified `$p`** proved
  bottom-up from F1 — *none asserted as `$a`*.
- The substrate axioms are non-conservative, but each is **mechanically
  bound to the metamath/set.mm theorem proving the same fact from ZFC**
  (`ax-sqrt ↔ resqrtth`, `of-recip ↔ axrrecex`, …) via `modelsplice` —
  soundness *relative to ZFC* is shown by machine, not asserted. Task #9
  splits that ≈10^45.7 exactly: not completeness, not the completion
  definitions (0.6%) — ℤ→ℚ pair-plumbing over *any* constructed ℝ.

## Trust boundary (the only thing you have to believe)

**Trusted: `src/kernel.rs`, alone.** A faithful sound Metamath-subset
verifier — constants/variables, `$f/$e/$a/$p`, `$d`, `${ $}` scoping,
mandatory-frame computation, substitution, the stack discipline,
disjoint-variable checks. If `verify()` returns `Ok`, every `$p` was
derived from the `$a` axioms by substitution and the stack discipline,
DV side-conditions enforced. That is the entire trust story.

**Untrusted — and the kernel re-checks all of it:**

- the proof elaborator and ring normalizer (`src/elaborate.rs`,
  `src/bin/grounded.rs`), the deduction-form combinator library, every
  `proof_g*.rs` derivation, and *every subagent that wrote any of it*.
  A bug there cannot yield an unsound proof — only a kernel rejection.
- the convenience tooling is convenience, never trust: `--lint`
  (load-time grammar check), the `el.app` key-checker, the `ring_eq`
  degree guard, and `--only <lemma>` — an explicitly **non-authoritative**
  debug fast-path. The *sole* authoritative claim is the full
  `grounded data/grounded.mm` run printing `Kernel: verified all N ✔`.

LCF/de Bruijn discipline: a small trusted core, everything else
disposable. It is why this could be built by an adversarially-honest
swarm and still mean something.

## Honest status

All seven Birkhoff postulates are kernel-verified, no cheating, in one
run (96 lemmas, db 267). The end-to-end re-expression of ASA over those
derived `$p` (`src/bin/asaprime.rs`) is now **a complete no-cheating
closure**: `asap.s4` is derived in-file (vertex-a acong-transitivity via
the verified `g3a-dotprop`, case-free — no `dot≠0`, no right-angle
exclusion, no `0<sqd` cancellation), the no-cheating guard passes 14/14
(all relied-on postulates are real `$p`, none `$a`), and the closing
algebra is kernel-verified against only genuine `$p` — **NO PENDING
`$a`, NO open leaf**. `asaprime` prints `COMPLETE NO-CHEATING CLOSURE of
( sqd a c ) = ( sqd e g )` — "Genuine green, not faked."

The honest refusals along the way (bare prot-uniq is provably false; the
side-output-vs-angle-output SAS gap; the minimal-Euclidean model is
cheap to *construct* but set.mm has no cheaper √-of-nonneg to *certify
it against*, so the transport-anchored floor stays ~10^46 — a result
that *sharpens* the thesis rather than faking a smaller number) have
been among the best outcomes here — see [`HISTORY.md`](HISTORY.md).

## Reproduce

```sh
cargo run --release --bin grounded -- data/grounded.mm          # all 96; verdict + exact sizes + [cse] shared-DAG
cargo run --release --bin grounded -- data/grounded.mm --lint   # load-time grammar check (fail-fast)
cargo run --release --bin grounded -- data/grounded.mm --profile sqcong   # cut-free cost attributor
cargo run --release --bin asa                                   # F0 Birkhoff ASA = 224
cargo run --release --bin asaprime                              # regrounded ASA′ — COMPLETE no-cheating closure
cargo run --release --bin euclidfloor                           # minimal Euclidean model: MEASURED unit step
cargo run --release --bin metasearch                            # kernel-gated superoptimizer (S1 / S2)
bash scripts/fetch-setmm.sh && cargo run --release --bin modelsplice   # grounding cost + RCF + transport-anchored floor
cargo test --release                                            # kernel self-tests + combinator tests
```

`data/set.mm` (~48 MB, public domain, Metamath project) is git-ignored;
the fetch script pulls it. The kernel re-checks every emitted proof.

## Re-verify in your browser (embedded prover)

The trust root `src/kernel.rs` is compiled to WebAssembly — *verification
semantics unchanged* — and embedded in the explorer. The "Re-verify in
your browser" control loads the shipped genuine no-cheating database
(`docs/data/grounded.out.mm.gz`, the shared-DAG proof — **not** the
cut-free expansion, which is 10⁷⁺ nodes by design and only reported) and
runs the real kernel live: a visitor's own browser re-derives every `$p`
from the axioms and prints the true verdict. Tamper one byte → it
rejects (tested).

The wasm wrapper is a standalone crate in `wasm/` (its own lockfile and
target dir; **not** in the main crate's build — `cargo build --release`,
the binaries and the 90-verify are untouched). Rebuild the artifact:

```sh
bash scripts/build-wasm.sh        # wasm-pack → docs/assets/wasmpkg/ + regen the gz
# or directly:
wasm-pack build wasm --release --target web --out-dir ../docs/assets/wasmpkg
cargo run --release --bin grounded -- data/grounded.mm   # emits data/grounded.out.mm
gzip -9 -c data/grounded.out.mm > docs/data/grounded.out.mm.gz
```

Requires the `wasm32-unknown-unknown` target and `wasm-pack`. If the
toolchain is absent the explorer degrades gracefully to a clearly-labelled
static snapshot plus the local re-verify command.

## Reusability

The grounded proof uses no property beyond the F1 axioms — no
completeness, no Archimedean property, no specific construction — so it
holds in *every* Euclidean field (ℝ, the real algebraic numbers,
real-closed fields, the computable reals, …); ℝ is merely the most
expensive such model. Formally F1 ⊆ Th(ℝ), so the result transfers up
unchanged; a proof that leaned on completeness would not transfer down.

## Layout

| path | role |
|---|---|
| `src/kernel.rs` | **the trust root** — sound Metamath-subset verifier (self-tested) |
| `src/elaborate.rs` | proof elaborator + deduction-form combinator library (untrusted) |
| `src/bin/grounded.rs` | staged no-cheating postulate proofs + kernel-checked ring normalizer; `--lint`, `--only` |
| `src/proof_g{1,2,3,4a}.rs` | the G1 / G2 / G3 / angle-LoC derivations (generic-lemma template) |
| `data/grounded.mm` | F1 substrate + conservative `df-*`; the postulate goals |
| `data/birkhoff.mm`, `src/bin/asa.rs` | F0 axiom system; Birkhoff ASA asserted = 224 |
| `src/bin/asaprime.rs` | ASA′ regrounded over the derived `$p` — **complete no-cheating closure** |
| `src/search.rs`, `src/bin/metasearch.rs` | kernel-gated proof superoptimizer (S1 normalizer search / S2 sound CSE) — untrusted |
| `src/cse.rs` | sound proof-DAG/CSE minimizer (shared-total only; kernel re-gated) — untrusted |
| `data/euclid.mm`, `src/bin/euclidfloor.rs` | minimal Euclidean-field model: generic √-extension step, **measured** in-kernel |
| `src/metamath.rs`, `src/bin/{calibrate,modelsplice}.rs` | set.mm extractor; grounding cost + RCF + transport-anchored floor |
| `src/number.rs` | bignum → log → log-log proof-size arithmetic |
| `docs/` | interactive explorer + the 15-minute talk |
| `HISTORY.md` | the full narrative, including the dead ends |

## Golf

The headline counts are deliberately cut-free, fully-inlined, no lemma
reuse — that *is* the metric (it makes "size of a fully-expanded proof"
concrete). The generic-lemma template — prove a tiny identity once over
fresh `$f` atoms, instantiate big subterms by *substitution* (free in
this metric) — is the size weapon: it took `loclink` 3,180,000 → 67,217
and `sqcong` 390,380 → 68,276, so G4 SAS 7,251,714 → **383,606** (~19×,
10^6.86 → 10^5.58), all still `verified all 96 ✔`.

A kernel-gated **metasearcher** (`metasearch`) closes the loop honestly:
**S1** (normalizer-strategy search) returns a *kernel-verified negative*
— the production normalizer is already optimal-spine, so association/
order is not a remaining lever. **S2** + the `cse` minimizer give a
sound, kernel-re-verified **−81%** on the *shared-DAG* total
(10,134,529 → 1,916,586) — but provably *cannot* move the cut-free
figure (CSE is invisible to a fully-inlined metric by construction).
That wall is not a limitation to apologize for: it is exactly why
cut-free is the honest hard metric for the poll's question.

*Reported, not faked — including the parts still in progress.*
