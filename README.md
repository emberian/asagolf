# asagolf

How long is the fully-expanded, machine-checked proof of a triangle-congruence
theorem when reduced to ZFC, in a Birkhoff (ruler/protractor) formalism?

This repository measures it directly: a micro-kernel Metamath verifier plus
hand-built, kernel-checked proof objects, reporting exact step counts. The
motivating context was a poll that estimated the answer at more than 10^1000.

## Results

| quantity | exact, kernel-verified | ≈ |
|---|---|---|
| F0 Birkhoff ASA (postulates + field axioms as primitives) | 224 cut-free steps | 10^2.4 |
| G4 SAS, derived (substrate = ordered ring + one √ axiom) | 7,251,714 steps | 10^6.86 |
| F1 substrate against a full ZFC model of ℝ (set.mm) | — | ≈ 10^45.7 |
| F1 substrate against a minimal Euclidean-field model | — | ≈ 10^37 |

The geometry is small (10^2–10^7). The large numbers come from constructing ℝ
from sets; even fully mechanized that term is ≈ 10^46. The dominant single
substrate fact is √-existence as routed through set.mm's analytic completeness
machinery (`resqrtth`); completeness itself is never used by ASA, and the
field/order construction — not completeness — is what costs.

## What is derived versus asserted

If the Birkhoff postulates (ruler, protractor, SAS, …) are asserted as axioms,
ASA is ~200 steps and the question is trivial. The substrate here instead
*derives* the postulates. `data/grounded.mm` asserts only:

* an ordered commutative ring with 1
  (`of-addcom/addass/add0/addinv/mulcom/mulass/mul1/distr`,
  `of-lein/letri/letot/leadd/lemul/lemul0/sqpos`),
* one further primitive: square roots of non-negatives exist (`ax-sqrt`),
  i.e. a Euclidean field,
* propositional and first-order logic with equality (`ax-1/2/3/mp`, `ax-7`, …),
* conservative definitions (`df-*`) of points, lines, distance, dot product,
  and angle congruence as polynomials over coordinates.

Points/lines/distance/angle are definitions, not axioms, so the class-splitter
scores them `Definition` rather than `GenuineAxiom`. Each Birkhoff postulate is
then a kernel-verified `$p` proved from (field + √ + df-*).

`G4 SAS` (law of cosines, √-free metric reasoning, integral-domain
cancellation) is discharged in 57 staged, kernel-verified lemmas:

```
classical propositional calculus   con3, jca, jaoi, pm2.18, …   from ax-1/2/3/mp
ordered-ring algebra               sqz, sqcong, mulcposcan       square-squeeze;
                                                                 no zero-divisor
                                                                 axiom, no trichotomy
law of cosines                     loclink   decided by a kernel-checked ring
                                              normalizer (desugar −x → distribute
                                              → sign-canonicalize → cancel)
G4 SAS                             df-acong unfold → substitute the two side
                                   equalities → cancel S=(sqd a b)(sqd a c) > 0
                                   → dot a b c = dot e f g → loclink×2 + congruence
```

## Reusability

The grounded proof uses no property beyond the F1 axioms — no completeness, no
Archimedean property, no specific construction — so it is valid in every
Euclidean field (ℝ, the real algebraic numbers, real-closed fields, computable
reals, …); ℝ is the most expensive such model. Formally: F1-axioms ⊆ Th(ℝ),
so SAS ∈ Th(F1) implies SAS holds in ℝ. The converse does not hold: a proof
that used completeness would not transfer down.

`src/bin/modelsplice.rs` mechanizes the transfer: it binds each F1 axiom to the
set.mm theorem proving the same fact over ZFC-constructed ℝ
(`of-addcom → axaddcom`, …, `ax-sqrt → resqrtth`) and reports the
fully-ZFC-grounded cost. The ~10^6.9 geometry skeleton is invariant across
models; only the substrate term changes.

## Architecture

| file | role |
|---|---|
| `src/kernel.rs` | sound Metamath-subset verifier; the trust root (self-tested) |
| `data/birkhoff.mm` | F0 axiom system; `src/bin/asa.rs` proves ASA (224 steps) |
| `data/grounded.mm` | F1 substrate + conservative `df-*` definitions |
| `src/bin/grounded.rs` | 57 staged lemmas + a kernel-checked ring normalizer; emits `grounded.out.mm`, re-verified by the kernel |
| `src/bin/modelsplice.rs` | binds F1 axioms to their set.mm ZFC proofs |
| `src/metamath.rs`, `src/bin/calibrate.rs` | exact fully-expanded extractor over set.mm |
| `src/number.rs` | bignum → log → log-log proof-size arithmetic |

## Reproduce

```sh
cargo run --release --bin grounded     # 57 lemmas; kernel verdict + exact sizes
cargo run --release --bin asa          # F0 Birkhoff ASA = 224
./scripts/fetch-setmm.sh               # set.mm (public domain, Metamath project)
cargo run --release --bin modelsplice  # F1 axioms → set.mm ZFC proofs
cargo run --release --bin calibrate    # set.mm fully-expanded calibration
```

The kernel re-checks every emitted proof object.

## Caveats

* `of-*` / `ax-sqrt` are non-conservative; discharging them requires exhibiting
  a model, which is what `modelsplice` measures. `df-*` are eliminable
  definitions.
* The SAS statement carries non-degeneracy hypotheses (`0 < sqd a b`,
  `0 < sqd a c`).
* A fully end-to-end regrounded ASA′ still requires the remaining Birkhoff
  postulates derived (G1 ruler, G2 incidence, G3a/G3b protractor). G3c and G4
  are done.

## Golf

The headline 7.25M is a deliberately cut-free, fully-inlined count with no
lemma reuse; that is the metric. The shared-subexpression DAG is small
(db = 191 statements). `loclink` (3.18M, invoked twice) and the
no-common-subexpression ring normalizer dominate the inlined total. Sharper
normalizer strategies, common-subexpression elimination in `ring_eq` output,
and a more aggressive sound proof-DAG minimizer are the open directions.
