$( ============================================================================
   data/sdg.base.mm  —  the certified-intuitionistic SDG substrate BASE.

   This is the authored trust surface: the $f floats and the $a axioms
   ONLY (no $p).  src/bin/sdgbuild.rs appends kernel-verified $p proof
   bodies and emits data/sdg.mm.  This base file is what the
   intuitionistic-purity guard (src/bin/sdgpure.rs) audits for classical
   contamination, and what the kernel re-checks.

   A CERTIFIED-INTUITIONISTIC predicate logic with equality, PLUS the
   Synthetic Differential Geometry substrate: a commutative ring R with 1
   (the line object), the infinitesimal object D = { d | d*d = 0 }, the
   Kock-Lawvere axiom (every D->R map is uniquely affine) and
   microcancellation.

   INTUITIONISTIC DISCIPLINE (the whole point):
     * connectives /\ \/ -. F. are PRIMITIVE with intuitionistic axioms.
     * NO ax-3 / Peirce / `( ( -. ph -> -. ps ) -> ( ps -> ph ) )`.
     * NO law of excluded middle `( ph \/ -. ph )`.
     * NO double-negation elimination `( -. -. ph -> ph )`.
     * equality: ONLY reflexivity + Leibniz substitution.  NOT assumed
       stable `( -. -. x = y -> x = y )` and NOT decidable
       `( x = y \/ -. x = y )`.  NO apartness primitive.
   Anything on that blacklist appearing as an $a here, or in the consumed
   closure of any $p, is the exact analog of cheating in the prequel.
   ============================================================================ $)

$c ( ) -> -. /\ \/ <-> A. E. wff |- F. = $.
$c term R D D2 + * 0 1 inv ap deriv $.

$v ph ps ch th $.
$v x y z d e a b c f g u v w $.

wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.  wth $f wff th $.
vx $f term x $.  vy $f term y $.  vz $f term z $.  vd $f term d $.
ve $f term e $.  va $f term a $.  vb $f term b $.  vc $f term c $.
vf $f term f $.  vg $f term g $.  vu $f term u $.  vv $f term v $.
vw $f term w $.

$( ---------------------------------------------------------------------------
   Intuitionistic propositional logic.  Primitive connectives, NO ax-3.
   --------------------------------------------------------------------------- $)

wn  $a wff -. ph $.
wi  $a wff ( ph -> ps ) $.
wa  $a wff ( ph /\ ps ) $.
wo  $a wff ( ph \/ ps ) $.
wb  $a wff ( ph <-> ps ) $.
wfal $a wff F. $.

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
${ mp.min $e |- ph $.  mp.maj $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}

ax-ial $a |- ( ( ph /\ ps ) -> ph ) $.
ax-iar $a |- ( ( ph /\ ps ) -> ps ) $.
ax-ian $a |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $.

ax-orl $a |- ( ph -> ( ph \/ ps ) ) $.
ax-orr $a |- ( ps -> ( ph \/ ps ) ) $.
ax-jao $a |- ( ( ph -> ch ) -> ( ( ps -> ch ) -> ( ( ph \/ ps ) -> ch ) ) ) $.

ax-negi $a |- ( ( ph -> F. ) -> -. ph ) $.
ax-nege $a |- ( -. ph -> ( ph -> F. ) ) $.
efq    $a |- ( F. -> ph ) $.

ax-bi1 $a |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $.
ax-bi2 $a |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $.
ax-bii $a |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) ) ) $.

$( ---------------------------------------------------------------------------
   Intuitionistic predicate logic with equality.  `x not free` provisos on
   ax-q2 / ax-ee are enforced by $d at use sites (prequel FOL discipline).
   Equality is ONLY reflexivity + Leibniz.  NOT stable, NOT decidable.
   --------------------------------------------------------------------------- $)

wal $a wff A. x ph $.
wex $a wff E. x ph $.

${ gen.1 $e |- ph $.  ax-gen $a |- A. x ph $. $}

ax-spec $a |- ( A. x ph -> ph ) $.
ax-q1   $a |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $.
${ q2.1 $e |- ( ph -> ps ) $. ax-q2 $a |- ( ph -> A. x ps ) $. $}
ax-ei   $a |- ( ph -> E. x ph ) $.
${ ee.1 $e |- ( ph -> ps ) $. ax-ee $a |- ( E. x ph -> ps ) $. $}

weq   $a wff x = y $.
eqid  $a |- x = x $.
eqcom $a |- ( x = y -> y = x ) $.
eqtri $a |- ( x = y -> ( y = z -> x = z ) ) $.

$( ---------------------------------------------------------------------------
   SDG substrate: R, a commutative ring with 1 (the line object).
   ABSENT by design: all order/positivity AND the prequel's irreducible
   metric residue `( x * x ) = 0 -> x = 0`.
   --------------------------------------------------------------------------- $)

t0   $a term 0 $.
t1   $a term 1 $.
tpl  $a term ( x + y ) $.
tmu  $a term ( x * y ) $.
tneg $a term ( inv x ) $.

ax-addcom $a |- ( x + y ) = ( y + x ) $.
ax-addass $a |- ( ( x + y ) + z ) = ( x + ( y + z ) ) $.
ax-add0   $a |- ( x + 0 ) = x $.
ax-addneg $a |- ( x + ( inv x ) ) = 0 $.
ax-mulcom $a |- ( x * y ) = ( y * x ) $.
ax-mulass $a |- ( ( x * y ) * z ) = ( x * ( y * z ) ) $.
ax-mul1   $a |- ( x * 1 ) = x $.
ax-distr  $a |- ( x * ( y + z ) ) = ( ( x * y ) + ( x * z ) ) $.
ax-mul0   $a |- ( x * 0 ) = 0 $.

eq-pl1 $a |- ( x = y -> ( x + z ) = ( y + z ) ) $.
eq-pl2 $a |- ( x = y -> ( z + x ) = ( z + y ) ) $.
eq-mu1 $a |- ( x = y -> ( x * z ) = ( y * z ) ) $.
eq-mu2 $a |- ( x = y -> ( z * x ) = ( z * y ) ) $.

$( ---------------------------------------------------------------------------
   Infinitesimal object D, Kock-Lawvere, microcancellation.
   --------------------------------------------------------------------------- $)

wD   $a wff ( D x ) $.
df-D $a |- ( ( D x ) <-> ( x * x ) = 0 ) $.

tap $a term ( ap f x ) $.

$( ===========================================================================
   FLAGGED NON-CONSERVATIVE SUBSTRATE COMMITMENT  #3 :  eq-ap
   (a NAMED axiom, flagged exactly as ax-kl / ax-microcancel are flagged).

   THE ap-CONGRUENCE QUESTION — RESOLVED (verdict B: NOT derivable).

   The substrate's equality theory is, in full:  eqid (reflexivity),
   eqcom (symmetry), eqtri (transitivity), and the FOUR per-operation
   congruence axioms eq-pl1/2, eq-mu1/2 for the ring operations + and * .
   Despite the header's prose "Leibniz substitution", there is NO general
   Leibniz schema  ( x = y -> ( ph -> ph[y/x] ) )  and NO congruence rule
   for any term constructor other than + and * .  Equality here is an
   equivalence relation equipped with hand-picked congruence rules for
   + and * ONLY.

   Therefore  x = y -> ( ap g x ) = ( ap g y )  is GENUINELY NOT DERIVABLE
   (verdict B, NOT A).  Proof (syntactic, kernel-faithful — exactly the
   proof discipline the kernel enforces).  Define the "ap-skeleton" of a
   term as the multiset of its maximal ( ap _ _ ) subterms.  By induction
   on derivations from { eqid, eqcom, eqtri, eq-pl1/2, eq-mu1/2, df-D } +
   pure logic with NO equality $e: every derivable closed equation s = u
   has skeleton(s) = skeleton(u).  Base: eqid gives s = s (trivial).
   Step: eqcom/eqtri preserve the invariant (equivalence-closure of an
   invariant relation); eq-pl1/2, eq-mu1/2 only ever rewrite a subterm
   sitting in a + or * position and NEVER inside the argument slot of an
   ( ap _ _ ); df-D introduces only ring/0 equations.  No axiom's
   conclusion can rewrite the argument position of an `ap`.  Hence with x,
   y distinct variables (x = y is not itself derivable, distinct
   skeletons) the equation ( ap g x ) = ( ap g y ) has unequal skeletons
   and is OUTSIDE the derivable set.  QED — verdict B is PROVEN, not
   assumed.  (Model gloss: take the term algebra modulo the congruence
   generated by the ring axioms; pick ap to act non-extensionally on
   distinct-but-ring-equal arguments — all $a above hold, eq-ap fails.)

   THE FIX (honest, flagged, NOT pretended-derived).  We add ONE named
   substrate axiom, eq-ap, the function-application congruence schema.
   It is a NON-CONSERVATIVE substrate commitment and is FLAGGED here AND
   in SEQUEL_SCOPE §5j exactly as ax-kl / ax-microcancel are — it is NOT
   smuggled into a $p as a derived lemma.

   INTUITIONISTIC ACCEPTABILITY (rigorous).  eq-ap is a POSITIVE Horn
   congruence schema:  one atomic equality antecedent, one atomic
   equality consequent, NO -. , NO \/ , NO -> -nesting, NO quantifier
   alternation, NO decidability/stability/apartness.  It is the literal
   structural twin of the already-present eq-pl1/2, eq-mu1/2 (same shape,
   different constructor).  Function-application congruence is a
   DEFINING property of equality in EVERY intuitionistic type theory
   (it is the eq-elimination / transport rule restricted to the term
   former `ap`); it is valid in every Heyting-valued / topos model.  It
   carries ZERO classical content: sdgpure's SHAPE scan certifies it
   matches none of LEM / Peirce / DNE / stable-eq / decidable-eq /
   apartness (mechanically — it has no -. and no \/ at all).  Adding it
   STRENGTHENS the substrate's congruence to the ring+ap fragment of full
   Leibniz; it does NOT add any classical principle.

   HONEST TRUST-STORY DELTA:  the substrate GAINED ONE AXIOM (eq-ap).
   Book Two's trust story is therefore: ap-congruence is a NEW NAMED
   intuitionistic substrate axiom (verdict B), NOT a derived rule.  This
   is stated plainly, not papered over.
   =========================================================================== $)
eq-ap $a |- ( x = y -> ( ap g x ) = ( ap g y ) ) $.

$( KOCK-LAWVERE, existence half: the map d |-> ( ap f d ) on D is affine,
   with slope b and constant term ( ap f 0 ).                            $)
ax-kl $a |- E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) $.

$( MICROCANCELLATION: b*d = c*d for all d in D  ==>  b = c.  Positive,
   universally quantified; no -. , no \/ , no decidability.              $)
ax-microcancel $a |- ( A. d ( ( D d ) -> ( b * d ) = ( c * d ) ) -> b = c ) $.

tderiv $a term ( deriv f ) $.

$( ===========================================================================
   THE HIGHER-INFINITESIMAL HIERARCHY  D_k = { x | x^(k+1) = 0 }.

   This is the Taylor-base milestone: the substrate every order-k synthetic
   Taylor expansion lives over.  Taylor's formula ITSELF is NOT proved here
   (it depends on the keystone SDG-K linking rule, a separate agent) — this
   file ONLY extends the substrate with the D_k objects, the generalized
   Kock-Lawvere axiom (every D_k -> R map is a UNIQUE polynomial of degree
   <= k) and level-wise microcancellation, plus the pure-substrate-algebra
   consequences (D_1 subset D_2; the degree-1 reduction to the existing KL).

   D_1 is exactly the existing D (df-D : ( D x ) <-> ( x * x ) = 0, i.e.
   x^2 = 0 = x^(1+1)).  We add D_2 explicitly:
       ( D2 x ) <-> ( ( x * x ) * x ) = 0     ( x^3 = 0 = x^(2+1) )

   THE GENERALIZED KOCK-LAWVERE AXIOM SCHEME (stated HONESTLY as a scheme).
   Mathematically, for each natural number k:

       (KL_k)  forall f : D_k -> R,  exists! (a_0,...,a_k) in R^(k+1)
               forall x in D_k,  f(x) = a_0 + a_1 x + a_2 x^2 + ... + a_k x^k

   This is an AXIOM SCHEME indexed by the meta-level natural number k: one
   axiom per k, NOT a single first-order sentence (the substrate has no
   internal natural-number object, so the universally-quantified-over-k
   statement is not expressible as one $a — presenting it as if it were
   would be a glib misstatement, so we do not).  We instantiate the scheme
   at the two levels the task requires and the general form is documented
   above precisely:

     * k = 1 :  ax-kl  (ALREADY in the substrate, unchanged):
                  f(d) = a_0 + a_1 d           (UNIQUE affine)
                this IS KL_1, so the k=1 instance of the scheme reduces
                to — is literally — the existing Kock-Lawvere axiom.  The
                $p `sdg-kl1-is-kl` records this reduction (it is `sdg-id`
                specialised: KL_1 = ax-kl, nothing new is asserted at k=1).

     * k = 2 :  ax-kl2 (NEW):
                  f(d) = a_0 + ( a_1 * d ) + ( a_2 * ( d * d ) )   UNIQUE
                existence half + level-2 microcancellation for uniqueness.

   LEVEL-WISE MICROCANCELLATION.  Uniqueness at level k is the scheme

       (MC_k)  ( forall x in D_k,  P(x) = Q(x) )  ==>  P = Q  coefficientwise

   again one axiom per k.  k=1 is the existing ax-microcancel.  We add the
   k=2 instance ax-microcancel2 (positive, universally quantified; no -. ,
   no \/ , no decidability — intuitionistically pure by SHAPE, exactly like
   ax-microcancel).

   INTUITIONISTIC NOTE (the whole point).  Classically every D_k collapses
   to { 0 } (precisely via the metric residue x*x=0 => x=0 the substrate
   REFUSES), so KL_k would be vacuous.  The content is the INTUITIONISTIC
   setting: D_k is a genuine higher-order infinitesimal object.  None of
   ax-kl2 / ax-microcancel2 / df-D2 uses a classical principle (no LEM, no
   DNE, no ax-3, no stable/decidable equality, no apartness) — sdgpure
   re-verifies this by NAME and SHAPE.  No level needs a classical
   principle: the honest finding is that the hierarchy is uniformly
   intuitionistically pure (see FINAL REPORT).
   =========================================================================== $)

wD2  $a wff ( D2 x ) $.

$( D_2 : x^3 = 0.  A DEFINITION (df-, conservative), mirroring df-D's
   discipline — not an axiom.                                            $)
df-D2 $a |- ( ( D2 x ) <-> ( ( x * x ) * x ) = 0 ) $.

$( GENERALIZED KOCK-LAWVERE at k = 2, existence half: the map
   d |-> ( ap f d ) on D_2 is a degree-<=2 polynomial, with linear
   coefficient b, quadratic coefficient e, and constant term ( ap f 0 ). $)
ax-kl2 $a |- E. b E. e A. d ( ( D2 d ) -> ( ap f d ) = ( ( ( ap f 0 ) + ( b * d ) ) + ( e * ( d * d ) ) ) ) $.

$( LEVEL-2 MICROCANCELLATION: if two degree-<=2 monomial families agree on
   all of D_2 then their coefficients agree.  Stated for the linear
   coefficient (the form consumed to make ( deriv f ) well-defined at
   level 2); same positive, quantifier-only SHAPE as ax-microcancel.     $)
ax-microcancel2 $a |- ( A. d ( ( D2 d ) -> ( b * d ) = ( c * d ) ) -> b = c ) $.

$( ================================================================
   GROUNDING THE CROSS-BOOK SPINE (sdgspinebuild).  Wave 4 NAMED
   the finding that the non-abelian commutator witness's non-
   vacuity is EXACTLY 1!=0 = Book One's measured irreducible
   residue (suc0!=0 / orientation, COST_STRUCTURE bottom).  This
   corpus GROUNDS the BOOK-THREE SEGMENT into a kernel-verified
   transport: sdg-spine-comm11 rebuilds the witness (1,1) entry
   = 1 pure-ring over the FROZEN base (with the derived inv-
   congruence sdg-spine-eqneg); sdg-spine-b3 is the transport
   ( <[A,B]11-expr> = 0 -> 1 = 0 ) — the non-abelian non-vacuity
   reduces EXACTLY to 1!=0, pure-ring (eqtri on the witness
   identity).  The BOOK-ONE SEGMENT (suc0!=0 ~= 1!=0, the
   standard numeral interpretation) is ALREADY transport-anchored
   & set.mm-bound in Book One (COST_STRUCTURE) — CITED, joined at
   the identical literal 1!=0, counted once, NEVER re-derived /
   re-summed / re-faked here.  NET: the spine is upgraded from a
   narrative [PROJECTION] to a two-segment transport, BOTH
   segments anchored.  Claimed at exactly that weight: a
   structural identity between two MEASURED residues, never a
   grand unification.  PURE RING, nothing classical, NO new
   substrate commitment.  Self-contained over the FROZEN
   eq-ap-extended data/sdg.base.mm; disjoint `sdg-spine-*`
   labels; shares no $p with any corpus.
   ================================================================ $)

sdg-spine-eqneg $p |- ( x = y -> ( inv x ) = ( inv y ) ) $= vx vy weq t0 vy tneg tpl vy tneg weq wi vx vy weq vx tneg vy tneg weq wi t0 vy tneg tpl vy tneg weq vx vy weq t0 vy tneg tpl vy tneg weq wi vy tneg t0 tpl vy tneg weq t0 vy tneg tpl vy tneg weq vy tneg ax-add0 t0 vy tneg tpl vy tneg t0 tpl weq vy tneg t0 tpl vy tneg weq t0 vy tneg tpl vy tneg weq wi t0 vy tneg ax-addcom t0 vy tneg tpl vy tneg t0 tpl vy tneg eqtri ax-mp ax-mp t0 vy tneg tpl vy tneg weq vx vy weq ax-1 ax-mp vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq t0 vy tneg tpl vy tneg weq wi vx vy weq vx tneg vy tneg weq wi wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vx tneg tpl t0 weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx ax-addneg vx vx tneg tpl t0 vy tneg eq-pl1 ax-mp vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vy weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx tneg vx tpl vx vx tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx ax-addcom vx tneg vx tpl vx vx tneg tpl vy tneg eq-pl1 ax-mp vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vy vx weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy eqcom vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi wi vx vy weq vy vx weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi wi vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi wi vy vx vx tneg eq-pl2 vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq ax-1 ax-mp vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx tneg vy tpl vx tneg vx tpl vy tneg eq-pl1 vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx tneg vy tpl vy tneg tpl vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vy vy tneg ax-addass vx tneg vy tpl vy tneg tpl vx tneg vy vy tneg tpl tpl eqcom ax-mp vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi t0 vy vy tneg tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vy vy tneg tpl t0 weq t0 vy vy tneg tpl weq vy ax-addneg vy vy tneg tpl t0 eqcom ax-mp t0 vy vy tneg tpl vx tneg eq-pl2 ax-mp vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg vx tneg t0 tpl weq wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx tneg vx tneg t0 tpl weq vx vy weq vx tneg vx tneg t0 tpl weq wi vx tneg t0 tpl vx tneg weq vx tneg vx tneg t0 tpl weq vx tneg ax-add0 vx tneg t0 tpl vx tneg eqcom ax-mp vx tneg vx tneg t0 tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx vy weq vx tneg vx tneg t0 tpl weq wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx tneg vx tneg t0 tpl vx tneg vy vy tneg tpl tpl eqtri vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl eqtri vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl eqtri vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl eqtri vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx tneg vx vx tneg tpl vy tneg tpl t0 vy tneg tpl eqtri vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx tneg t0 vy tneg tpl vy tneg eqtri vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi ax-2 ax-mp ax-mp vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq ax-2 ax-mp ax-mp $.
sdg-spine-comm11 $p |- ( ( ( 0 * 0 ) + ( 1 * 1 ) ) + ( inv ( ( 0 * 0 ) + ( 0 * 0 ) ) ) ) = 1 $= t1 t0 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 weq t1 ax-add0 t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t1 t0 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 weq wi t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 tneg t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq t0 t0 tneg tpl t0 weq t0 tneg t0 weq t0 ax-addneg t0 tneg t0 t0 tneg tpl weq t0 t0 tneg tpl t0 weq t0 tneg t0 weq wi t0 t0 tneg tpl t0 tneg weq t0 tneg t0 t0 tneg tpl weq t0 tneg t0 tpl t0 tneg weq t0 t0 tneg tpl t0 tneg weq t0 tneg ax-add0 t0 t0 tneg tpl t0 tneg t0 tpl weq t0 tneg t0 tpl t0 tneg weq t0 t0 tneg tpl t0 tneg weq wi t0 t0 tneg ax-addcom t0 t0 tneg tpl t0 tneg t0 tpl t0 tneg eqtri ax-mp ax-mp t0 t0 tneg tpl t0 tneg eqcom ax-mp t0 tneg t0 t0 tneg tpl t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg weq t0 tneg t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq wi t0 t0 tmu t0 t0 tmu tpl t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg weq t0 t0 tpl t0 weq t0 t0 tmu t0 t0 tmu tpl t0 weq t0 ax-add0 t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tpl t0 weq t0 t0 tmu t0 t0 tmu tpl t0 weq wi t0 t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 weq t0 t0 t0 tmu tpl t0 t0 tpl weq t0 ax-mul0 t0 t0 tmu t0 t0 eq-pl2 ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl weq t0 t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq wi t0 t0 tmu t0 weq t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl weq t0 ax-mul0 t0 t0 tmu t0 t0 t0 tmu eq-pl1 ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl t0 t0 tpl eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl t0 sdg-spine-eqneg ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 t1 eq-pl2 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq wi t0 t0 tmu t1 t1 tmu tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t0 t1 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t1 weq t1 t0 tpl t1 weq t0 t1 tpl t1 weq t1 ax-add0 t0 t1 tpl t1 t0 tpl weq t1 t0 tpl t1 weq t0 t1 tpl t1 weq wi t0 t1 ax-addcom t0 t1 tpl t1 t0 tpl t1 eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq t0 t1 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t1 weq wi t0 t1 t1 tmu tpl t0 t1 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq t1 t1 tmu t1 weq t0 t1 t1 tmu tpl t0 t1 tpl weq t1 ax-mul1 t1 t1 tmu t1 t0 eq-pl2 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl weq t0 t1 t1 tmu tpl t0 t1 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq wi t0 t0 tmu t0 weq t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl weq t0 ax-mul0 t0 t0 tmu t0 t1 t1 tmu eq-pl1 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl t0 t1 tpl eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl t1 eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg eq-pl1 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl t1 eqtri ax-mp ax-mp $.
sdg-spine-b3 $p |- ( ( ( ( 0 * 0 ) + ( 1 * 1 ) ) + ( inv ( ( 0 * 0 ) + ( 0 * 0 ) ) ) ) = 0 -> 1 = 0 ) $= t1 t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t0 weq t1 t0 weq wi t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 weq t1 t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t1 t0 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 weq t1 ax-add0 t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t1 t0 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 weq wi t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 tneg t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq t0 t0 tneg tpl t0 weq t0 tneg t0 weq t0 ax-addneg t0 tneg t0 t0 tneg tpl weq t0 t0 tneg tpl t0 weq t0 tneg t0 weq wi t0 t0 tneg tpl t0 tneg weq t0 tneg t0 t0 tneg tpl weq t0 tneg t0 tpl t0 tneg weq t0 t0 tneg tpl t0 tneg weq t0 tneg ax-add0 t0 t0 tneg tpl t0 tneg t0 tpl weq t0 tneg t0 tpl t0 tneg weq t0 t0 tneg tpl t0 tneg weq wi t0 t0 tneg ax-addcom t0 t0 tneg tpl t0 tneg t0 tpl t0 tneg eqtri ax-mp ax-mp t0 t0 tneg tpl t0 tneg eqcom ax-mp t0 tneg t0 t0 tneg tpl t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg weq t0 tneg t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 weq wi t0 t0 tmu t0 t0 tmu tpl t0 weq t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg weq t0 t0 tpl t0 weq t0 t0 tmu t0 t0 tmu tpl t0 weq t0 ax-add0 t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tpl t0 weq t0 t0 tmu t0 t0 tmu tpl t0 weq wi t0 t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 weq t0 t0 t0 tmu tpl t0 t0 tpl weq t0 ax-mul0 t0 t0 tmu t0 t0 eq-pl2 ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl weq t0 t0 t0 tmu tpl t0 t0 tpl weq t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl weq wi t0 t0 tmu t0 weq t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl weq t0 ax-mul0 t0 t0 tmu t0 t0 t0 tmu eq-pl1 ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 t0 tmu tpl t0 t0 tpl eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl t0 t0 tpl t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl t0 sdg-spine-eqneg ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 tneg t0 eqtri ax-mp ax-mp t0 t0 tmu t0 t0 tmu tpl tneg t0 t1 eq-pl2 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl weq wi t0 t0 tmu t1 t1 tmu tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl weq t0 t1 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t1 weq t1 t0 tpl t1 weq t0 t1 tpl t1 weq t1 ax-add0 t0 t1 tpl t1 t0 tpl weq t1 t0 tpl t1 weq t0 t1 tpl t1 weq wi t0 t1 ax-addcom t0 t1 tpl t1 t0 tpl t1 eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq t0 t1 tpl t1 weq t0 t0 tmu t1 t1 tmu tpl t1 weq wi t0 t1 t1 tmu tpl t0 t1 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq t1 t1 tmu t1 weq t0 t1 t1 tmu tpl t0 t1 tpl weq t1 ax-mul1 t1 t1 tmu t1 t0 eq-pl2 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl weq t0 t1 t1 tmu tpl t0 t1 tpl weq t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl weq wi t0 t0 tmu t0 weq t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl weq t0 ax-mul0 t0 t0 tmu t0 t1 t1 tmu eq-pl1 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 t1 tmu tpl t0 t1 tpl eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t1 tpl t1 eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg eq-pl1 ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 t0 tpl t1 eqtri ax-mp ax-mp t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t1 eqcom ax-mp t1 t0 t0 tmu t1 t1 tmu tpl t0 t0 tmu t0 t0 tmu tpl tneg tpl t0 eqtri ax-mp $.
