# asagolf — how big is a "simple" proof, really?

A Twitter poll estimated that the fully-expanded, machine-checked proof of a
basic triangle-congruence theorem (**ASA**, in a Birkhoff
ruler/protractor formalism), reduced all the way down to ZFC, exceeds
**10^1000 steps**. This repository answers that by *building the proof
object and counting* — a small sound Metamath-subset kernel plus
hand-built, kernel-re-checked proofs, with exact step counts.

**The short answer:** the geometry is ≈ **10^6.9**. The only astronomical
term anywhere is *constructing ℝ inside ZFC*, ≈ **10^45.7**, and an exact
machine attribution shows even that is not completeness — it is ℤ→ℚ
construction multiplicity, removable by model choice to ≈ 10^37.2 (with a
real-closed-field floor far below). The poll overshoots by roughly **950
orders of magnitude**, and every digit here is, or is becoming,
kernel-checked.

A 15-minute foundations-classroom talk is in `docs/slides.html` (press
`S` for speaker notes + timing); the interactive explorer is
`docs/index.html` (live at emberian.github.io/asagolf); the full project
narrative — including the wrong turns — is in [`HISTORY.md`](HISTORY.md).

## Results (exact, kernel-verified)

| quantity | exact | ≈ |
|---|---|---|
| F0 Birkhoff ASA — postulates *asserted* as axioms | 224 cut-free steps | 10^2.4 |
| **G4 SAS** — derived, no cheating (hardest postulate) | 7,251,714 | 10^6.86 |
| **G3a** ray-angle — derived | 4,720,242 | 10^6.7 |
| **G2** incidence — derived | 607,583 | 10^5.8 |
| G1 ruler · G3b′ oriented prot-uniq · g4a-sss · G0 · G3c — derived | small | 10^3–10^5 |
| **all of the above, one run** | **90 lemmas, 261-statement DB, `verified all ✔`** | |
| F1 substrate vs. a full ZFC model of ℝ (set.mm) | — | 10^45.7 |
| same, √ as a Euclidean-field primitive | — | 10^37.2 |
| analytic-completion *definitions* (#9, exact split) | 0.6% of that | |

"F0 = 224" is the cheap, vacuous answer (assert the postulates).
Everything else is the honest one: every Birkhoff postulate *derived*.

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
run. The end-to-end re-expression of ASA over those derived `$p`
(`src/bin/asaprime.rs`) is *structurally* kernel-verified and its maximal
sound sub-tree (275 statements, no PENDING axiom) checks against the
genuine `$p`; the final faithful wiring — exporting an equality
`g4a-sss` already proves internally, so the protractor-uniqueness bridge
stays sign-free without an **unfaithful** non-degeneracy (Birkhoff ASA
holds for right triangles, so `∠≠90°` must not be assumed) — is the last
in-progress step. `asaprime` **refuses to claim closure until it is
genuine**. The honest refusals (bare prot-uniq is provably false; the
side-output-vs-angle-output SAS gap) have been among the best results
here — see [`HISTORY.md`](HISTORY.md).

## Reproduce

```sh
cargo run --release --bin grounded -- data/grounded.mm          # all postulates; verdict + exact sizes
cargo run --release --bin grounded -- data/grounded.mm --lint   # load-time grammar check (fail-fast)
cargo run --release --bin asa                                   # F0 Birkhoff ASA = 224
cargo run --release --bin asaprime                              # regrounded ASA′ (honest closure guard)
bash scripts/fetch-setmm.sh && cargo run --release --bin modelsplice   # F1↔ZFC splice (#8) + #9 split
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
| `src/bin/asaprime.rs` | ASA′ regrounded over the derived `$p` (closure-guarded) |
| `src/metamath.rs`, `src/bin/{calibrate,modelsplice}.rs` | set.mm extractor; F1↔ZFC splice (#8/#9) |
| `src/number.rs` | bignum → log → log-log proof-size arithmetic |
| `docs/` | interactive explorer + the 15-minute talk |
| `HISTORY.md` | the full narrative, including the dead ends |

## Golf

The headline counts are deliberately cut-free, fully-inlined, no lemma
reuse — that *is* the metric (it makes "size of a fully-expanded proof"
concrete). The shared-subexpression DAG is far smaller; the cruncher
reports both. `loclink` (≈3.18M, invoked twice in SAS) and the
no-common-subexpression ring normalizer dominate the inlined totals; the
generic-lemma template is what kept the high-degree postulates from
exploding cut-free. Sharper normalizer strategies and a more aggressive
sound proof-DAG minimizer remain open directions.

*Reported, not faked — including the parts still in progress.*
