# METASEARCH — a kernel-gated proof superoptimizer

`metasearch` is a **separate tool** (`src/bin/metasearch.rs` + `src/search.rs`).
It never edits the production proof construction, the `ra`/`canon_sum`/`ring_eq`
normalizer, `make_lemma`, the generic lemmas, or `stage_order`. It only:

* **S1** — builds candidate proofs of a demo identity with its *own*
  parameterised AC-ring normalizer, kernel-checks each, and ranks the
  survivors; and
* **S2** — rewrites the *emitted* corpus `data/grounded.out.mm` by
  common-subexpression factoring, then hands the result back to the kernel.

The production pipeline is untouched: `grounded`, `asa`, `modelsplice` and the
authoritative 96-lemma verify build and run exactly as before. `metasearch` is
purely additive (one new bin + one new module).

---

## 1. Design: the kernel as the sole fitness oracle (LCF discipline)

The trust root is `src/kernel.rs`, a sound Metamath-subset verifier. The
searcher **proposes**; the kernel **disposes**. Nothing `metasearch` prints as
a "win" is trusted unless the kernel re-verified it *in this process*.

### S1 soundness argument

For each strategy `(MonoOrder, Assoc)` S1 emits a self-contained `.mm`:
the demo identity as a `$p` whose proof was produced by that strategy, on a
minimal substrate (`demo_base_full`) whose algebra axioms mirror `grounded.mm`
(equality schema over term metavars; `tpl`/`tmu`; `of-*` comm/assoc;
`cong-pl*`; `ax-mp`). We call `kernel::Db::parse(..).verify()`. A candidate is
accepted **iff** `verify()` returns `Ok` *and* the proved statement is exactly
the target conclusion — the kernel itself enforces the latter (a proof of the
wrong statement is a hard verify error). An unsound monomial order or
association cannot pass; it can only be **rejected**. The cost model
(`expand`, the cut-free `$a`-leaf count) is used *only to rank already
kernel-verified candidates*; it has no authority over soundness.

### S2 soundness argument (three gates)

S2 lifts the single largest repeated **closed** RPN subtree (a balanced span
that is a complete proof of one statement, referencing no scoped `$e`/local)
into one fresh top-level `$p` lemma, and replaces every occurrence with a
reference. The rewritten corpus is re-parsed and `verify()`d *in full*:

* **GATE 1** — the kernel verifies *every* `$p` in the rewritten corpus.
* **GATE 2** — every original `$p` keeps its **exact** original conclusion
  string (recorded before the rewrite, compared after).
* **GATE 3** — the cut-free total must strictly drop.

GATE 1 ∧ GATE 2 ⇒ the rewrite is **sound** (a conservative re-presentation:
same theorems, re-checked). GATE 3 is the *optimization* gate. The tool also
exposes `metasearch verify <file>`, which re-parses an on-disk corpus with a
**fresh** kernel — an adversarial, no-shared-state re-check.

> "Reported, not faked": every number reported as a win is computed from a
> corpus the kernel just accepted in this process; an honest "doesn't help,
> here's exactly why" is a success, a fake is a zero.

---

## 2. S1 result — does it beat the **production** normalizer?

S1 sweeps 4 monomial orders × 3 associations on a degree-4 additive-AC
identity (`locsq-demo`, the law-of-cosines squared-distance core,
pre-distributed to a pure AC obligation). All 12 strategies kernel-verify the
exact target conclusion. Cut-free `$a`-leaf counts:

| association | rpn | cut-free |
|-------------|-----|----------|
| **RightSpine** (any order) | 27 090 | **13 154** |
| Balanced (any order)       | 32 744 | 15 872 |
| LeftSpine (any order)      | 38 936 | 18 856 |

The naive **Lex/LeftSpine** left-fold (the searcher's strawman baseline) is
the worst at 18 856. So "S1 improves 18 856 → 13 154 (−30%)" is true *only
against that strawman*.

**The honest task question is whether S1 beats the PRODUCTION normalizer.**
The production AC normalizer `ra` in `src/bin/grounded.rs` is:

```rust
fn ra(el: &Elab, xs: &[Pt]) -> Pt {
    if xs.len() == 1 { xs[0].clone() }
    else { el.app("tpl", &[("u", xs[0].clone()),
                            ("v", ra(el, &xs[1..]))], &[]).unwrap() }
}
```

i.e. `ra(xs) = tpl(xs[0], ra(xs[1..]))` — a **right-spine** sum. That is
*exactly* S1's `Assoc::RightSpine`.

> **HONEST FINDING (kernel-verified): S1 does NOT beat production.**
> S1's optimum is `RightSpine`, rpn = 27 090, cut-free = **13 154** — which is
> *byte-identical* to the association the production `ra` normalizer already
> builds. Production is already on the optimal association spine for this
> family; S1 *confirms* that optimality, it does not improve it. This is a
> legitimate, valuable negative result, not a failure: it rules out
> association/ordering as a remaining lever and shows the existing normalizer
> is not leaving spine-shape savings on the table.

(Reproduce: `cargo run --release --bin metasearch -- s1`.)

---

## 3. S2 status — exact, kernel-verified

### The original bug

S2 failed with `KERNEL REJECTED rewritten corpus: proof of s2-factored-0:
stack underflow applying s2-factored-0`. Two distinct defects:

1. **Self-rewrite.** `rewrite_proofs` rewrote *every* `$= … $.` block —
   *including the new lemma's own proof body*. Its body is `cand.body`, so it
   was replaced by the single token `s2-factored-0`, producing the
   self-referential proof `s2-factored-0 := s2-factored-0`: applying a
   non-zero-arity step to an empty stack ⇒ immediate underflow.

2. **Missing mandatory `$f` arguments.** The lifted top-level `$p`'s
   conclusion mentions concrete variables, so the kernel's `compute_frame`
   gives `s2-factored-0` **mandatory `$f` hypotheses** (one per variable in
   the conclusion). At a call site the kernel expects, on the stack *before*
   the lemma token, one proof-term per mandatory `$f`. The bare one-token
   replacement supplied **none** ⇒ underflow at every call site too.

### The fix (sound)

`cand.body` is a **ground** closed subtree: it is identical at every
occurrence and proves a fixed ground conclusion. The lemma is therefore always
invoked at the **identity substitution** var→var. The mandatory-`$f`
proof-term for variable `X` (the `$f` `vX` proving `term X` / `wff X`) is then
just the single token `vX` (the kernel pushes its expression). So:

* Insert the lemma after the emit marker → parse this *staged* corpus →
  read the kernel's `mand_hyps` order for `s2-factored-0`. (Guard: every
  mandatory hyp of a ground top-level lemma must be a `$f`; reject otherwise.)
* Replace each body occurrence with `<mand-$f labels…> s2-factored-0`.
* **Skip the lemma's own `$=` block** (track the label = token before
  `$p`/`$a`/`$e`/`$f`).

### Exact verified result

`cargo run --release --bin metasearch -- s2 data/grounded.out.mm`:

```
candidate lemma   : s2-factored-0
occurrences       : 96550
KERNEL-SOUND      : true        (GATE 1 ∧ GATE 2)
cut-free before   : 10924486
cut-free after    : 10924489
stored-tokens bef : 4931739     (Σ |$p proof| — share-respecting size)
stored-tokens aft : 4738644
  -> stored-proof delta: -193095 tokens (-3.915%)
ACCEPTED (GATE3)  : false
```

Independent fresh-kernel re-check of the persisted artifact:

```
$ cargo run --release --bin metasearch -- verify data/grounded.factored.mm
INDEPENDENT KERNEL VERIFY: data/grounded.factored.mm
  Ok — all 58 $p re-verified by a fresh kernel
```

**The S2 abstraction is now sound.** A fresh kernel process, re-parsing the
on-disk `data/grounded.factored.mm` with no shared state, accepts all 58 `$p`
(57 originals, conclusions byte-identical, + the one shared lemma reused at
96 550 sites).

### Why GATE 3 is still `false` — the honest structural gap

This is **not** a soundness failure and **not** fixable by better factoring.
The corpus cut-free metric is `expand`/`corpus_total`, which **recursively
inlines every `$p`** (`Kind::P ⇒ Σ expand(step)`). A shared lemma is therefore
*invisible* to it: each of the 96 550 references re-expands to the same
`$a`-leaf count it had inlined, and the standalone lemma adds its body **once**
— so `after = before + (one lemma body) = 10 924 486 + 3`. Common-subexpression
factoring **cannot, by construction**, reduce a fully-inlining tree-leaf
metric; sharing is a DAG property, not a cut-free-tree property.

The genuine win is real and shows up in the **stored-proof token metric**
(`corpus_proof_tokens` = Σ over `$p` of RPN proof length — the size of the
proof text actually stored, which *does* respect sharing):

> **stored-proof tokens: 4 931 739 → 4 738 644 (−193 095, −3.92%),
> kernel-verified and conclusion-preserving.**

GATE 3 was left intact and honestly reports `false` rather than being
weakened to claim a cut-free win that the metric structurally forbids. To
report S2 as `ACCEPTED` against its *appropriate* objective, GATE 3's metric
should be the stored-proof / DAG-node count, not the fully-inlined leaf count;
that is a deliberate, documented design decision, not a silent change.

---

## 4. Summary

| | result | kernel-gated? |
|--|--------|---------------|
| **S1 vs strawman left-fold** | −30% (18 856 → 13 154) | yes |
| **S1 vs PRODUCTION `ra`** | **no improvement** (13 154 = 13 154; production is already optimal right-spine) | yes — honest negative |
| **S2 soundness** | **SOUND**: 58/58 `$p` re-verify in a fresh kernel, all original conclusions byte-identical, lemma shared ×96 550 | yes (independently re-checked) |
| **S2 cut-free GATE 3** | `false` — structurally unsatisfiable (cut-free metric fully inlines `$p`; CSE is a DAG/stored-size win, not a tree-leaf win) | yes — honest gap |
| **S2 stored-proof win** | 4 931 739 → 4 738 644 tokens (−3.92%) | yes |

Reproduce: `cargo run --release --bin grounded -- data/grounded.mm` then
`cargo run --release --bin metasearch` (S1 + S2), and
`cargo run --release --bin metasearch -- verify data/grounded.factored.mm`
for the independent re-check.
