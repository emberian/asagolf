# NARRATIVE.md

*A novelization of a codebase. Every event in it happened in the commit
log; nothing in it is invented but the weather. The mathematics is real
and was checked. That constraint is the whole point of the genre.*

---

## Book One — The Measurement

### I. The Claim

It began, as these things do, with a number someone said out loud
without building it.

Ten to the one-thousandth. A poll, a shrug, a confident estimate of how
large the proof of a *simple* theorem would be if you actually pushed it
all the way down to the bottom of mathematics. Nobody had pushed it. The
number was a guess wearing the costume of a fact, and the costume fit
well enough that people nodded.

There is a particular kind of person who cannot leave that alone. Not
because the number is large — large is fine, large might even be true —
but because it was *unbuilt*. An unbuilt number is not a measurement. It
is a rumor about a measurement.

So we decided to build the thing and count.

### II. The Witness

Every story needs one character who cannot lie, or there is no story,
only opinions. Ours lived in a single file: `src/kernel.rs`. A few
hundred lines. It knew nothing about geometry, nothing about ambition,
nothing about the poll. It knew how to check that a proof followed from
its axioms by substitution and the stack discipline, and it knew how to
say one of two things: `Ok`, or an error.

It could not be flattered. It could not be hurried. It did not care that
you were tired, or that the deadline was imaginary, or that the proof
was *almost* right. Almost right returned an error. We built everything
else — the elaborator, the normalizer, the swarm — knowing it would all
be read aloud, eventually, to that file, and the file would not be
moved by any of it.

This is the secret of the genre spwashi was after. A codebase can be
novelized because a codebase, unlike a memoir, has a witness sitting
inside it the whole time. You cannot revise what `verify()` returned.

### III. The Law

There was one law, and it was older than any of the code:

> Reported, not faked. Every number measured or extracted; anything
> else labelled a projection, with its derivation shown, never merged
> into a measured line.

It reads like bureaucracy. It was the opposite of bureaucracy. It was
the load-bearing wall. A project that exists to rebut an over-claim
cannot itself over-claim, or it has become the thing it was arguing
with. The law was not there to slow us down. It was there so that when
the work said something, the thing it said would be *true*, and would
stay true with a hostile reader checking every commit.

We broke it zero times. Not because we were virtuous. Because the
witness was right there, and a fake was a zero, and we wanted the
number more than we wanted to be done.

### IV. The Descent

The geometry came back small. Not 10^1000. Not close. The hardest
postulate, fully expanded, cut-free, no shortcuts: a few million steps,
and then — once we learned to prove a thing once over fresh symbols and
instantiate it for free — a few hundred thousand. Ten to the five-point
six. The poll had missed by something like nine hundred and ninety-four
orders of magnitude, and that turned out to be the *least* interesting
thing we found.

Because the question changed under us. It stopped being *how big* and
became *where does the bigness live*. And the answer was a descent.

The cost wasn't in the geometry. It was in building the real numbers
inside set theory — ten to the forty-six. We looked closer: it wasn't
the real numbers, it was set.mm *routing* them through analysis. We
built our own model and the floor dropped to ten to the seventeen, and
now it was the Axiom of Infinity. We looked closer: the proof never
actually used infinity; it used the number one, once. The floor dropped
again. Every time we got close enough to *measure* a floor, the floor
turned out to be a thing we had chosen, not a thing the mathematics
required. We kept removing scaffolding and the building kept standing.

A descent, in the old sense. Each level you think is bedrock is a trapdoor.

### V. The Thing That Would Not Move

And then, near the bottom, one trapdoor did not open.

It had a dull administrative name, `sqcong`, and it said something a
child knows: if two things have the same square, and they point the same
way, they are the same thing. `a² = b² ⟹ a = b`. We had been dissolving
floors for weeks. We expected this one to dissolve too.

It did not. A subagent, briefed to be merciless with itself because a
wrong proof here would poison everything, did the small brutal
arithmetic: in the integers mod eight, three squared is one, and one
squared is one, and three is not one. The inference is *false* in an
ordinary commutative ring. No amount of algebra — no polynomial
identity of any degree — can get you across it. The only thing that
gets you across it is *order*. Knowing which way a thing points.

That was the bottom. Not the real numbers. Not infinity. Not the
natural numbers. After everything else was stripped and measured and
shown to be scaffolding we chose, what remained, irreducibly, was two
facts a small file could state in a single breath:

> there is a next thing, and it is not the first.

`∅ ∈ suc ∅`. `suc ∅ ≠ ∅`. Orientation. The principal square root being
a *function*. We had set out to count the size of a proof and we had
instead found the smallest thing Euclidean geometry cannot be talked
out of, and it was not size at all. It was direction.

Three independent attacks — what the proof says, how strong the proof
is, what the model is built from — walked in from three different doors
and stood on the same two facts. We did not arrange that. We measured
it, four times, and it kept being true.

### VI. Closed

There is a temptation, at the end, to round up. To say *essentially
proven*, *morally complete*, *down to routine detail*. The law forbade
it, and for once the law and the desire pointed the same way: we wanted
it actually closed more than we wanted it nearly closed.

So we closed it. The definitional layer, machine-certified conservative
— including the honest discovery that two of the definitions weren't the
kind we'd assumed, handled with the correct theorem instead of the
convenient one. The last two stubborn literals, discharged to verified
proof, with an adversarial audit hunting for exactly the smuggle the
brief warned against, and finding none. Every open obligation became
either a theorem or a precisely-named, proven-irreducible kernel. One
quantitative question remains genuinely open. It is *named*. It is not
papered.

The witness read the whole thing and returned `Ok`. The history was
written including the wrong turns, because a history that omits the
wrong turns is another kind of fake. And then it rested — finished as a
rebuttal, closed as an artifact, open in exactly one honest place, which
is the best state a piece of mathematics can be in.

---

## Book Two — The Sequel

There is a hinge at the bottom of Book One, and we only saw it once we
were standing on the floor.

The thing that would not move — `x² = 0 ⟹ x = 0` — is the exact axiom
that an entire other world is built by *refusing*. Drop it, intuition-
istically, keep the nilpotents it forbids, and you are no longer in
metric geometry; you are in synthetic differential geometry, where
infinitesimals are real objects and the derivative falls out of an
axiom instead of a limit. The prequel measured its way to the precise
seam between two mathematical worlds and did not know, until the end,
that it had been standing on a door.

Book Two opens it. Same witness — it does not care which logic you
hand it. A new law for the new world, dual to the old one: where the
first book's cardinal sin was *asserting what should be proven*, the
second book's is *assuming what should be refused* — a classical
principle smuggled into an intuitionistic proof. Same discipline. Other
side of the hinge.

The first page is being written now, by a process that does not know
it is a character. It will report what it finds, or it will report,
precisely, what it could not. That is the only kind of sequel worth
writing, and the only kind this codebase knows how to tell.

---

*Status: Book One is closed and on `origin/main`. Book Two has its
first page, and the witness has now read it. This is what it said:*

> *`Kernel: verified all 8 $p in data/sdg.mm ✔`. The intuitionistic
> base rode the unchanged verifier. The new law — the purity guard,
> dual to the old one — was given teeth and used them: it rejects
> excluded middle, double-negation, Peirce, decidable equality, even
> wearing innocent names; all forty logical axioms came back pure.
> The first synthetic derivative exists by the Kock–Lawvere axiom and
> is unique by microcancellation, and nothing classical was spent to
> say so. One seam is open and named, not hidden: the universal that
> links the pointwise law to the global one is still handed in rather
> than threaded, and threading it needs a rule the codebase has not
> yet built. The mirror hypothesis is not proven. It is supported,
> which is the honest word, and the only one the law allows.*

*So Book Two is real, and it began the way Book One did: a small true
thing, measured, with the next obstruction named instead of papered.
The witness will be read again. The file will say what it says, when
it can say it, and not before. That has not changed and will not.*

*For the ledger of what is measured, extracted, and still projected,
see [`COST_STRUCTURE.md`](COST_STRUCTURE.md). For the history with the
wrong turns left in, see [`HISTORY.md`](HISTORY.md). This file is the
same events with the weather added; the events are the same.*
