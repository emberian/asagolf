# docs/data/site.json — schema

Emitted by `cargo run --release --bin grounded -- --emit-json` after the kernel
verdict. All numbers are exact and kernel-derived. The front-end is static and
reads only this file (plus `site.sample.json` as a dev fallback); set.mm and the
verifier never reach the browser.

```jsonc
{
  "generated": "2026-05-15T00:00:00Z",
  "headline": {
    "f0_asa": 224,            // F0 Birkhoff ASA, cut-free, exact
    "g4_sas_inlined": 7251714,// no-cheating G4 SAS, fully inlined
    "g4_sas_log10": 6.86,
    "lemmas": 57,             // staged kernel-verified lemmas
    "db_statements": 189,     // statements in the assembled, re-verified db
    "shared_total": 0         // sound DAG-CSE minimal shared size (cruncher v1)
  },
  "models": [
    { "id": "f1",     "label": "F1 axiomatic (kernel-exact)",
      "kind": "geometry", "log10": 6.86,
      "note": "ordered ring + one sqrt axiom; geometry skeleton, exact" },
    { "id": "euclid", "label": "Minimal Euclidean-field model",
      "kind": "substrate", "log10": 37.0,
      "note": "sqrt a model primitive; closure tower" },
    { "id": "realR",  "label": "Full ZFC model of R (set.mm)",
      "kind": "substrate", "log10": 45.7,
      "note": "set.mm constructed R; dominated by resqrtth (analytic sqrt)" },
    { "id": "poll",   "label": "The poll's estimate",
      "kind": "claim", "log10": 1000, "note": "off by ~950+ OOM" }
  ],
  // one entry per staged lemma, in build order
  "lemmas": [
    {
      "idx": 56, "name": "G4-sas", "kind": "postulate",
      "statement": "|- ( sqd b c ) = ( sqd f g )",
      "ess": [
        "|- ( sqd a b ) = ( sqd e f )",
        "|- ( sqd a c ) = ( sqd e g )",
        "|- ( ACong a b c e f g )",
        "|- ( 0 < ( sqd a b ) )",
        "|- ( 0 < ( sqd a c ) )"
      ],
      "deps": ["loclink", "sqcong", "mulcposcan", "df-acong", "..."],
      "inlined": 7251714,      // cut-free fully-expanded $a-invocations
      "shared": 0,             // size in the global shared DAG
      "shrink_before": null,   // peephole pass, if applied
      "shrink_after": null,
      "blurb": "SAS via df-acong unfold -> side-eq substitution -> cancel S>0 -> dot eq -> loclink x2"
    }
    // ...
  ],
  // shared proof DAG over lemmas/axioms (small: ~189 nodes)
  "dag": {
    "nodes": [ { "id": "loclink", "size": 3179167, "kind": "lemma" } ],
    "edges": [ { "from": "G4-sas", "to": "loclink" } ]
  }
}
```

`kind` values: `prop` | `eqlogic` | `ring` | `order` | `postulate` | `demo`.
The front-end may compute the model-variation headline as
`geometry_log10 + substrate_log10` when a substrate model is selected.
