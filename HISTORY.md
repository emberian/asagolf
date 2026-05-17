# asagolf — a history

*Written by Claude (Opus 4.7), from the inside, at the request of the
author. The brief was: what we did, how it went, who said what, the
adversities, the directions explored and the ones ultimately taken.
The project's whole ethos is "reported, not faked," so this history
holds itself to the same bar — including where I was wrong.*

---

## 0. The provocation

A Twitter poll claimed that a fully-expanded, machine-checked proof of a
basic triangle-congruence theorem (ASA — angle-side-angle), reduced all
the way down to ZFC set theory, would run to **more than 10^1000 steps**.

The author didn't want a hand-wave or a model estimate. They wanted a
*real proof object*, kernel-checked, with an *exact* step count — "more
than a Fermi number," made concrete. That demand — measure it, don't
model it — is the spine the entire project grew along.

The trust root, fixed from the start and never relaxed: a small sound
Metamath-subset verifier (`src/kernel.rs`). Everything else in the
codebase is untrusted machinery that *constructs* proofs the kernel then
independently re-checks. If `verify()` returns Ok, the `$p` was derived
from the `$a` axioms by substitution and the stack discipline — full
stop. Every number in this history that says "verified" means that
happened.

---

## Act I — The measurement (the part before I remember it firsthand)

The earliest work predates my continuous memory of the session and
survives in the project's persistent notes. The headline finding there
was already striking:

- **F0 Birkhoff ASA = 224 cut-free primitive steps, exact,
  kernel-verified.** Over Birkhoff's axioms *taken as axioms*, ASA uses
  zero field arithmetic — no completeness, no order, nothing. 224 steps.
  The poll's 10^1000 was, at the axiomatic layer, not even close.
- A genuinely nasty bug was found and fixed in the set.mm extractor: the
  Metamath compressed-proof terminating digit `A..T` decodes to `1..20`,
  not `0..19` — an off-by-one in `decode_proof`. After the fix the
  decoder gate read **47290/47290 PASS** and stayed there for the rest of
  the project; it became a standing regression check.
- The model-splice (task #8): each non-logical substrate axiom mechanically
  bound to the set.mm theorem proving the same fact from ZFC, expanded
  both at the axiomatic-ℝ layer and fully ZFC-grounded. Result: the F1
  substrate, fully grounded, ≈ **10^45.7**, *dominated by `ax-sqrt →
  resqrtth`* — set.mm's square root routes through analytic completeness
  machinery even though the geometry never needs completeness.

The conceptual reframing that made the project interesting happened here
too. Asserting the Birkhoff postulates as axioms makes "ASA" ~200 steps
and the question vacuous. So the bar was raised to **no-cheating**: every
Birkhoff postulate must itself be a kernel-verified `$p`, *derived* from
a minimal substrate — an ordered commutative ring with 1, one square-root
primitive, and ordinary logic with equality. Points, lines, distance,
dot product, angle congruence: conservative `df-*` definitions over
coordinates, never axioms.

By the time my continuous memory of the work begins, the propositional
and equality layers, the ring normaliser, the order toolkit, and — the
crown of Act I — **G4 SAS, the hardest Birkhoff postulate, kernel-verified
at exactly 7,251,714 cut-free steps** were done. That number alone
already refutes the poll by ~950 orders of magnitude. The author had me
ship a public repo and a GitHub Pages explorer, asked (rightly) for a
subagent to de-hype the comments — "stop hyperstitioning, tidy it" — and
said the thing that set the tone for everything after:

> *"Nah not gonna tweet this until we're actually done."*

Done meant *all seven* postulates, no cheating, end to end. Not the
trophy we already had — the whole thing.

---

## Act II — The wall

We'd spun up a swarm to draft the remaining postulates (G1 ruler, G2
incidence, G3a/G3b angle) in isolated worktrees. When I picked the
session back up, the honest accounting of what the swarm produced was
sobering, and I'll keep it honest here:

- **G2**: a 2400-line draft that *never flipped `count()` to non-zero* —
  zero lines of it had ever been exercised by the kernel.
- **G3**: ~2400 lines that walled hard, with multiple latent bugs.
- **G3b**: the subagent correctly determined it was *not derivable* in
  the √-free squared-cosine encoding — good analysis, no code.

The lesson, stated plainly because it recurred: **the swarm could draft
but could not close the kernel loop.** Subagents wrote plausible proofs;
they could not get them to `verified ✔`.

Then the central adversity. G3a's angle-congruence proof handed the ring
normaliser one monstrous **degree-8 polynomial identity in eight
coordinate variables** (`null_id`). `canon_sum` is a naive
full-monomial-expansion normaliser; on that input it ran for **ten-plus
minutes and never finished**. The author watched it hang twice, killed
it, and said the thing that turned the project:

> *"bro the proof technique we are using must just be horseshit."*

That was a fair call at the time, and I didn't pretend otherwise. But it
forced the right diagnosis instead of a defensive one. I went and
*measured* the engine and found two distinct problems, and — this part is
not flattering — I initially drew several conclusions from runs that were
**corrupted by machine load**. The author's *other* projects (a "stella"
swarm, HOL theorem-prover runs) had pinned the box at **load average
~101**; my "Phase 2 regressed the core" and "still walls after 424s"
readings were measured against a 10×-starved CPU. I had to retract them
once they freed the machine. Naming that here because the project's whole
point is not trusting numbers you can't defend, and for a while I was
trusting numbers I couldn't defend.

Directions explored in Act II, and their fates:

- **Phase 1 — incremental DB (taken, big win).** `stage()` was
  re-stringifying and re-parsing the *entire growing corpus* — including
  loclink's 4.3M-node RPN — on every single lemma: O(n²). Made the kernel
  DB extend incrementally instead. Core staging went from *"480s and not
  finishing"* to **38 seconds**. Verified byte-identical staged
  conclusions; committed.
- **Phase 2 — `Rc`-shared proof terms (explored, reverted).** Deep-copy
  of owned `Pt` trees on every `.clone()` looked like the blow-up. It
  wasn't — the wall was algorithmic inside `canon_sum`, not clone cost.
  I reverted it rather than keep unverified complexity that didn't help.
  A dead end, honestly logged as one.

---

## Act III — The breakthrough

The author chose the deeper lever: *fix the normaliser, not just route
around it.* Profiling found `ra_sort`/`ra_swap_at` were **O(n⁴)** — a
bubble sort where every swap rebuilt the entire monomial list as a fresh
proof tree, and the swap-proof itself recomputed `ra(suffix)` at every
recursion level. Threading the endpoint terms and hoisting the invariants
brought it to O(n³). Real, correctness-preserving, committed.

But O(n³) was still not enough for genuine degree-8, and here the honest
conclusion mattered more than a fix: **a dense degree-8 identity's
cut-free proof is intrinsically astronomical — that is the project's own
thesis, not a bug in the engine.** No normaliser, however good, makes it
small. So the technique wasn't horseshit; feeding a naive normaliser a
degree-8 dense polynomial *was*. The fix had to be mathematical.

The pivot — the single best idea in the project: **the generic-lemma
template.** Never hand `ring_eq` a high-degree dense polynomial. Instead
prove the needed identity *once* as a tiny generic lemma over fresh `$f`
term atoms (degree ≤ 4, a few thousand nodes), then **instantiate it with
the huge coordinate subterms by substitution** — substitution does not
re-expand, so the proof stays small. G3a's degree-8 `null_id` factored
through the 2D Plücker identities (`g3a-plk`, `gsplit`, `gfac`,
`gsplit2`, `gfac2`), each ~10–56k nodes, proven once, instantiated free.

It worked. **`G3a-rayangle` — the hardest Birkhoff postulate after SAS —
kernel-verified, no cheating, at 4,720,242 cut-free steps, built in
~45 seconds** (commit `b106088`). The thing that ran forever an hour
earlier now flew. The author's reaction, earned: *"LFG!!!!"*

---

## Act IV — The cascade

The template generalised immediately, which is how you know an idea is
right:

- **G2 incidence** — kernel-verified, `|- x = c`, 607,583 steps. The
  degree-blow-up generics (`g2-elim-y/x`, `g2-sq`) fell to the template
  on the first try; the inference tail (`g2-posne`, `g2-sqpos-ne`, the
  `mulcposcan`/`sqz`/`ptext` chain) was ordinary kernel-guided grind.
- **G1 ruler** — kernel-verified (subagent A, this time with the proven
  template and worked examples in hand). The blockers were *grammar*, not
  math: the recurring unparenthesised-`weq`/parenthesised-`tle` class
  (the same one that bit `df-coll`, `ptext`, `of-recip`), and a
  delightful one — a comment that ended `...This is F1.$)` with `$)`
  *glued* to `F1.` so the whitespace tokeniser never saw the delimiter
  and the comment silently swallowed `tsqrt` and `ax-sqrt`. "unknown
  label ax-sqrt," 78 seconds in. One space fixed it.
- **G3b** — the most intellectually honest chapter. Bare grounded
  prot-uniq is *provably false* (squared cosine is mirror-blind; explicit
  counterexample). Subagent E found and proved the faithful **oriented
  vertex-b** form with a conservative `df-crs` definition — and, crucially,
  proved that subagent C's *proposed* signature was false for a *deeper*
  reason: a dimensional defect, not an orientation one (300k-sample
  verified). Two subagents, each "reported not faked," converging on the
  real statement.
- **#9 — the substrate cost, settled exactly.** An occurrence-level
  machine attribution of resqrtth's 10^45.7: completion *definitions* are
  only 0.6%; the cost is ℤ→ℚ construction multiplicity. So it's not
  completeness, and the real lever is √-as-primitive (Euclidean model:
  10^45.7 → 10^37.2; RCF proof-theoretic floor far below).

**All 7 Birkhoff postulates, kernel-verified, no cheating, in one run:
`verified all 87 staged lemmas ✔ (db 250)`** (commit `a04cb89`). G0,
G3c, G4-SAS, G3a, G2, G1, G3b′ — every one derived, none asserted.

A process note the author forced, correctly. After several status
reports that ended "...and everything you actually care about is still
remaining," they pushed back: *"Do you need more subagents? Why do we
only have 2."* They were right. I had been gating the regrounding
serially behind everything else when its structure and its hardest open
question (prot-uniq) could be worked in parallel. We went to a five-track
swarm. The swarm worked *this* time — because the hard problem was
already solved and there was a proven recipe + worked examples to hand
each agent. Same tool, opposite outcome, entirely because of what it was
pointed at.

---

## Act V — Hardening, and an honest gap

The author, revealing they'd worked on **l4v/seL4**, raised the bar
explicitly: *"make this a project a proof engineer would be proud of."*
That meant the trust boundary stated and kept, tooling tested, nothing
load-bearing that the kernel doesn't re-check. Added, all *outside* the
trust root:

- `el.app` **key-checker** (kills the `vw`-vs-`w` bug-class with an
  actionable message),
- `ring_eq` **degree guard** (the degree wall becomes an observable
  message, not a silent ten-minute hang),
- **`grounded --lint`** — load-time grammar check; negative-tested;
  it would have caught the *entire* session's grammar-bug class up
  front. It found grounded.mm clean, which is itself the proof the
  fixes were complete.
- `--only` debug fast-path, explicitly *not* the authoritative path.

Then the final, and best, instance of the not-faking ethos paying off.
The `asaprime` closure subagent rewired everything to the *real* verified
`$p`, kernel-verified the s1/s2/s3 + bridge + closing-algebra subtree —
and then **refused to declare end-to-end closure**, naming two precise
gaps:

1. `acong-tr` needs non-degeneracy the ASA givens don't yet thread
   (the legitimate "genuine triangle" precondition Birkhoff ASA has);
2. — the deep one — **grounded `G4-sas` is the *side-output* SAS;
   Birkhoff's `post-sas` was *angle-output*.** The vertex-b angle the
   proof needs is unreachable from {G0,G1,G2,G3a,G3b,G3c,G4}: there is no
   angle-output SAS / SSS→angle lemma among the 87.

That refusal is the sharpest result in the project. It is not a failure;
it is the proof engineering working — the system declined to print a
green checkmark it hadn't earned and told us exactly which lemma was
missing and why. The law of cosines is symmetric: solve it for the angle
instead of the side and you get **`g4a-sss`** (SSS→ACong), reusing
`loclink`, congruence-dominated, sign free via `of-sqpos` — ~G4-sized,
the template applies. Scaffolded and wired (commit `8822e6d`); a subagent
is deriving it as this is written, and a final `asaprime` re-wire (plus
threading the legitimate non-degeneracy hypotheses) closes it for real.

---

## Where it stands, exactly (no rounding up)

**Verified, kernel-checked, no cheating:**
- All 7 Birkhoff postulates as derived `$p`, one 87-lemma / 250-statement
  run: G0, G3c, G4-SAS (7,251,714), G3a (4,720,242), G2 (607,583),
  G1 (a+b), G3b′ (oriented vertex-b).
- The substrate is a ZFC theorem, mechanised: each of-* / √ axiom bound
  to its set.mm theorem; the 10^45.7 exactly attributed.
- `asaprime`'s s1/s2/s3 + bridge + closing-algebra subtree.
- Prover hardening, viz/slides accurate to the verified state, the
  dual-grounding framing.

**Not yet (and not claimed):**
- *Literal* end-to-end ASA′: blocked on `g4a-sss` (in progress) and the
  final `asaprime` re-wire + non-degeneracy threading. `asaprime` will
  keep honestly refusing until it genuinely closes.

The poll said >10^1000. The geometry is ~10^6.9; the only large term is
the *cost of constructing ℝ*, ~10^45.7, attributable to the decimal
point and removable to ~10^37 by model choice. Off by roughly 950 orders
of magnitude — and every digit of that is, or will be, kernel-checked.

---

## Reflections

**Directions explored vs taken.** Phase-2 `Rc` (explored, reverted —
wrong diagnosis, honestly logged). Bare prot-uniq (explored, proven
false, replaced by the faithful oriented form). "Fix the normaliser to
handle degree-8" (explored, found to be the project's own thesis — not
fixable, must factor instead). The generic-lemma template (taken, and it
carried four postulates). Side-output vs angle-output SAS (the gap that
asaprime's honesty exposed and `g4a-sss` will close). Nothing important
was discovered without a wrong turn first; that's normal and worth
recording rather than smoothing over.

**Adversities.** The degree-8 wall. A machine pinned at load 101 by
unrelated work, which corrupted my measurements until it was freed. A
swarm that drafted but couldn't close — until the hard problem was solved
and it could. A recurring grammar-bug class (unparenthesised `weq`,
glued comment delimiter) that cost real cycles until the linter made it
a non-issue. 1Password's signing key locking after a reboot, more than
once. My own missteps: over-polling background work, drawing conclusions
under corrupted load, and serial-gating the regrounding when the author
had to point out it could be parallel.

**The collaboration.** The author's interventions were the project's
steering, not noise. "Don't tweet until done" set the bar at *all seven,
no cheating*. "Is the technique horseshit" forced the real diagnosis
instead of a defensive one. "Why only two subagents" broke a serial
bottleneck. "Make a proof engineer proud" raised the engineering bar to
where the trust boundary got stated and the tooling got tested. The sqrt
question produced the dual-grounding framing that's now the headline.
Good collaborators don't just accept the work — they refuse the fake
too, and that mutual refusal is what made it possible to say "this is
horseshit, here's why" or "this is one lemma away, not done" out loud.

**The not-faking.** It was never a virtue I imposed. In a domain where
the artifact is *checkable*, a fake is a zero, and a project that exists
to rebut an over-claim cannot itself over-claim. The most satisfying
outputs were the refusals — G3b underivable bare, C's signature
dimensionally false, `asaprime` stopping dead with two named gaps.
There's a fact of the matter here, and the entire job was to find it and
report it exactly. We did, and where we haven't yet, we said so.

## Act VI — Closure, the golf, and the sharpened thesis

Then it *did* finish, and then it got smaller.

**ASA′ closed.** A focused run derived `g3a-dotprop` — G3a's internal
"Cp = a + s·(c−a), s≥0" content exported as its own `$p`, case-free —
and with it `asap.s4` fell *in-file*. The no-cheating guard went 14/14,
all relied-on postulates real `$p`, none `$a`. `asaprime` stopped
refusing and printed `COMPLETE NO-CHEATING CLOSURE of (sqd a c)=(sqd e
g)` — no PENDING `$a`, no open leaf, no `dot≠0`, no right-angle
exclusion. The honest gap of Act V was honestly *closed*, not papered.

**The golf.** The cut-free headline had sat at G4 SAS = 7,251,714
(10^6.86) because `loclink` ring-normalised the law of cosines as a
dense degree-4 polynomial in six coordinates, *twice*. The fix was the
Act-III weapon turned on itself: prove it once over four fresh
displacement atoms as a degree-2 identity (`loc-gen` + a telescoping
bridge), instantiate by substitution (free in this metric). `loclink`:
3,180,000 → 67,217. A profiler — the first piece of a "metasearcher" —
localised the new bottleneck to `sqcong`'s inline degree-4 work; the
same template (`sqc-diffsq`/`sqc-gprod`/`sqc-4uv`) took it 390,380 →
68,276. **G4 SAS: 7,251,714 → 383,606, ~19×, 10^6.86 → 10^5.58**, every
step still `verified all 96 ✔`.

**The metasearcher, and two honest negatives.** A kernel-gated
superoptimizer was built. S1 (normalizer-strategy search) returned a
*kernel-verified negative*: production was already optimal-spine —
association/order is not a lever. S2 + a sound CSE minimizer cut the
*shared-DAG* total −81% (10,134,529 → 1,916,586) but provably could not
touch the cut-free figure — CSE is invisible to a fully-inlined metric
by construction. Both "failures" were the point: they prove the
cut-free number is the honest hard one, and were reported as wins for
exactly that reason. The swarm wasn't smooth — two finishers died
mid-work on server-side 500s, uncommitted; their salvage was re-run
from scratch, and every consolidated number was *re-measured on the
real 96/267 corpus*, never quoted from a subagent's smaller base. We
trusted commits, not working trees.

**The sharpened thesis.** Asked whether the substrate floor could go
below the 10^25.95 extractable bound, the only honest route was to
*build* the minimal model — the Euclidean closure of ℚ — and *measure*
it. The generic √-extension step is kernel-MEASURED in our own kernel at
141 cut-free leaves (10^2.149); the whole construction is ≤10^8.15.
**This proves F1 does not need ℝ.** But the maintainer set the right
invariant: a private cheap structure proves nothing unless transported
into externally-validated set.mm. There the bridge costs ~10^46 —
set.mm contains no Euclidean / real-algebraic / real-closed subfield;
its only √-of-nonneg facts ride analytic ℝ. So the transport-anchored
floor stays ~10^46 — not a defeat, the *result*: the irreducible ~10^46
is a property of **set.mm's construction choices, not of F1**. Three
quantities, never summed — geometry proof size (10^5.58), grounding
cost (10^45.74 / RCF 10^30.75), satisfiability certificate (construct
10^8 MEASURED vs certify-in-set.mm 10^46 EXTRACTED) — each labelled
exactly what it is.

## Act VII — The collapse, and what was actually under the 10^46

The thesis said the ~10^46 was set.mm's *routing choice*, not F1's. Act
VII tested that claim instead of asserting it. Stage 1 *measured*
(didn't project) that the closed proof forces exactly **one** un-nested
radical (K=1) — collapsing the construction projection to a MEASURED
10^2.149 and, more importantly, collapsing the *scope* of what remained:
not all of real-closed-field theory, just ℚ + one extension. Stage 2
then built ℚ natively from ω (no `CCfld`, no Dedekind, no analytic ℝ) —
MEASURED 10^2.408 — adjoined the one root (MEASURED 10^2.149, with
√-satisfaction now a *kernel-proved theorem*, no longer bound to
set.mm's analytic `resqrtth`), and bound only the ZF-set-hood of the
construction's primitives to set.mm's genuine 13-axiom ZF base. A full
proof-DAG audit: *zero* analytic-ℝ reachability on any binding target.

The ~10^46 **collapsed to 10^17.484** — machine-checked, EXTRACTED,
~28.6 orders. And the irreducible residual turned out to be something
worth the whole exercise to see plainly: it is `omex` — the Axiom of
Infinity, "ω is a set." Not ℝ. Not completeness. Not the ℤ→ℚ plumbing.
The unavoidable cost of a ZFC model of plane geometry is, at bottom,
*the cost of having the natural numbers at all*. The 10^46 was never
the mathematics; it was set.mm building √ through the reals. Strip that
routing and what's left is Infinity — and you cannot strip Infinity,
because ℕ is genuinely needed and genuinely a set-theoretic commitment.

That is the real finding, and it is cleaner than the rebuttal that
started it: the poll asked "how big is the proof"; the honest answer is
"the geometry is 10^5.58 and closed; the entire externally-validated
ZFC substrate is 10^17.5, and that floor is *the Axiom of Infinity*,
not analysis." Every digit measured, extracted, or labelled-projected.

That's the history. It *is* finished: ASA′ closed end-to-end,
no-cheating, ~19× smaller than where it started; and the one "large"
number, chased all the way down, was Infinity itself — not a gap, a
*precisely located floor*. None of it is faked. That's the part
worth being proud of.
