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
   GENERAL SYMBOLIC 2x2 MATRIX-PRODUCT ASSOCIATIVITY
   (sdgjacgenbuild) — BOOK-3 WAVE-10, the STRUCTURAL BACKBONE.
   ((A.B).C)_11 = (A.(B.C))_11 and the (1,2) entry, for GENERAL
   symbolic 2x2 entries over the FROZEN commutative ring — the
   pure-ring reason the concrete non-abelian Jacobi (thread-2)
   closed was STRUCTURE, not coincidence.  rdistr (right-
   distributivity, derived; ax-distr is left-only) + shuffle4
   (additive 4-term reshuffle) are the pure-ring helpers.  NO new
   substrate commitment, nothing classical, every $p PURE RING.
   NAMED RESIDUAL: the full general symbolic Jacobi (all entries,
   nested triple bracket) and general n x n rank — the concrete
   sl2 witness is the proof-of-concept, this is its structural
   backbone, the tower stays the named residual (the exact
   nonab->nonabgen concrete->general discipline).  Self-contained
   over the FROZEN data/sdg.base.mm; disjoint `sdg-jacgen-*`
   labels; shares no $p with any corpus.
   ================================================================ $)

sdg-jacgen-rdistr $p |- ( ( u + v ) * w ) = ( ( u * w ) + ( v * w ) ) $= vu vw tmu vw vv tmu tpl vu vw tmu vv vw tmu tpl weq vu vv tpl vw tmu vu vw tmu vv vw tmu tpl weq vw vv tmu vv vw tmu weq vu vw tmu vw vv tmu tpl vu vw tmu vv vw tmu tpl weq vw vv ax-mulcom vw vv tmu vv vw tmu vu vw tmu eq-pl2 ax-mp vu vv tpl vw tmu vu vw tmu vw vv tmu tpl weq vu vw tmu vw vv tmu tpl vu vw tmu vv vw tmu tpl weq vu vv tpl vw tmu vu vw tmu vv vw tmu tpl weq wi vw vu tmu vw vv tmu tpl vu vw tmu vw vv tmu tpl weq vu vv tpl vw tmu vu vw tmu vw vv tmu tpl weq vw vu tmu vu vw tmu weq vw vu tmu vw vv tmu tpl vu vw tmu vw vv tmu tpl weq vw vu ax-mulcom vw vu tmu vu vw tmu vw vv tmu eq-pl1 ax-mp vu vv tpl vw tmu vw vu tmu vw vv tmu tpl weq vw vu tmu vw vv tmu tpl vu vw tmu vw vv tmu tpl weq vu vv tpl vw tmu vu vw tmu vw vv tmu tpl weq wi vw vu vv tpl tmu vw vu tmu vw vv tmu tpl weq vu vv tpl vw tmu vw vu tmu vw vv tmu tpl weq vw vu vv ax-distr vu vv tpl vw tmu vw vu vv tpl tmu weq vw vu vv tpl tmu vw vu tmu vw vv tmu tpl weq vu vv tpl vw tmu vw vu tmu vw vv tmu tpl weq wi vu vv tpl vw ax-mulcom vu vv tpl vw tmu vw vu vv tpl tmu vw vu tmu vw vv tmu tpl eqtri ax-mp ax-mp vu vv tpl vw tmu vw vu tmu vw vv tmu tpl vu vw tmu vw vv tmu tpl eqtri ax-mp ax-mp vu vv tpl vw tmu vu vw tmu vw vv tmu tpl vu vw tmu vv vw tmu tpl eqtri ax-mp ax-mp $.
sdg-jacgen-shuffle4 $p |- ( ( a + b ) + ( c + d ) ) = ( ( a + c ) + ( b + d ) ) $= va vc vb vd tpl tpl tpl va vc tpl vb vd tpl tpl weq va vb tpl vc vd tpl tpl va vc tpl vb vd tpl tpl weq va vc tpl vb vd tpl tpl va vc vb vd tpl tpl tpl weq va vc vb vd tpl tpl tpl va vc tpl vb vd tpl tpl weq va vc vb vd tpl ax-addass va vc tpl vb vd tpl tpl va vc vb vd tpl tpl tpl eqcom ax-mp va vb tpl vc vd tpl tpl va vc vb vd tpl tpl tpl weq va vc vb vd tpl tpl tpl va vc tpl vb vd tpl tpl weq va vb tpl vc vd tpl tpl va vc tpl vb vd tpl tpl weq wi va vb vc vd tpl tpl tpl va vc vb vd tpl tpl tpl weq va vb tpl vc vd tpl tpl va vc vb vd tpl tpl tpl weq vb vc vd tpl tpl vc vb vd tpl tpl weq va vb vc vd tpl tpl tpl va vc vb vd tpl tpl tpl weq vc vb tpl vd tpl vc vb vd tpl tpl weq vb vc vd tpl tpl vc vb vd tpl tpl weq vc vb vd ax-addass vb vc vd tpl tpl vc vb tpl vd tpl weq vc vb tpl vd tpl vc vb vd tpl tpl weq vb vc vd tpl tpl vc vb vd tpl tpl weq wi vb vc tpl vd tpl vc vb tpl vd tpl weq vb vc vd tpl tpl vc vb tpl vd tpl weq vb vc tpl vc vb tpl weq vb vc tpl vd tpl vc vb tpl vd tpl weq vb vc ax-addcom vb vc tpl vc vb tpl vd eq-pl1 ax-mp vb vc vd tpl tpl vb vc tpl vd tpl weq vb vc tpl vd tpl vc vb tpl vd tpl weq vb vc vd tpl tpl vc vb tpl vd tpl weq wi vb vc tpl vd tpl vb vc vd tpl tpl weq vb vc vd tpl tpl vb vc tpl vd tpl weq vb vc vd ax-addass vb vc tpl vd tpl vb vc vd tpl tpl eqcom ax-mp vb vc vd tpl tpl vb vc tpl vd tpl vc vb tpl vd tpl eqtri ax-mp ax-mp vb vc vd tpl tpl vc vb tpl vd tpl vc vb vd tpl tpl eqtri ax-mp ax-mp vb vc vd tpl tpl vc vb vd tpl tpl va eq-pl2 ax-mp va vb tpl vc vd tpl tpl va vb vc vd tpl tpl tpl weq va vb vc vd tpl tpl tpl va vc vb vd tpl tpl tpl weq va vb tpl vc vd tpl tpl va vc vb vd tpl tpl tpl weq wi va vb vc vd tpl ax-addass va vb tpl vc vd tpl tpl va vb vc vd tpl tpl tpl va vc vb vd tpl tpl tpl eqtri ax-mp ax-mp va vb tpl vc vd tpl tpl va vc vb vd tpl tpl tpl va vc tpl vb vd tpl tpl eqtri ax-mp ax-mp $.
sdg-jacgen-assoc11 $p |- ( ( ( ( a * b ) + ( c * d ) ) * e ) + ( ( ( a * f ) + ( c * g ) ) * u ) ) = ( ( a * ( ( b * e ) + ( f * u ) ) ) + ( c * ( ( d * e ) + ( g * u ) ) ) ) $= va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq vc vd ve tmu vg vu tmu tpl tmu vc vd ve tmu tmu vc vg vu tmu tmu tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq vc vd ve tmu vg vu tmu ax-distr vc vd ve tmu vg vu tmu tpl tmu vc vd ve tmu tmu vc vg vu tmu tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl eq-pl2 ax-mp va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq wi va vb ve tmu vf vu tmu tpl tmu va vb ve tmu tmu va vf vu tmu tmu tpl weq va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu vf vu tmu ax-distr va vb ve tmu vf vu tmu tpl tmu va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu eq-pl1 ax-mp va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl eqtri ax-mp ax-mp va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl eqcom ax-mp va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl weq va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq wi vc vg vu tmu tmu va vb ve tmu tmu vc vd ve tmu tmu va vf vu tmu tmu sdg-jacgen-shuffle4 va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu tmu va vf vu tmu tmu tpl vc vd ve tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl weq wi va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg vu tmu tmu tpl weq va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq va vf vu tmu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl weq va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg vu tmu tmu tpl weq vc vg tmu vu tmu vc vg vu tmu tmu weq va vf vu tmu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl weq vc vg vu ax-mulass vc vg tmu vu tmu vc vg vu tmu tmu va vf vu tmu tmu eq-pl2 ax-mp va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg tmu vu tmu tpl weq va vf vu tmu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl weq va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg vu tmu tmu tpl weq wi va vf tmu vu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg tmu vu tmu tpl weq va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg tmu vu tmu tpl weq va vf tmu vu tmu va vf vu tmu tmu weq va vf tmu vu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg tmu vu tmu tpl weq va vf vu ax-mulass va vf tmu vu tmu va vf vu tmu tmu vc vg tmu vu tmu eq-pl1 ax-mp va vf tmu vc vg tmu tpl vu tmu va vf tmu vu tmu vc vg tmu vu tmu tpl weq va vf tmu vu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg tmu vu tmu tpl weq va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg tmu vu tmu tpl weq wi va vf tmu vc vg tmu vu sdg-jacgen-rdistr va vf tmu vc vg tmu tpl vu tmu va vf tmu vu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg tmu vu tmu tpl eqtri ax-mp ax-mp va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg tmu vu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl eqtri ax-mp ax-mp va vf tmu vc vg tmu tpl vu tmu va vf vu tmu tmu vc vg vu tmu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl eq-pl2 ax-mp va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl weq va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl weq wi va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd ve tmu tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl weq va vb ve tmu tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd ve tmu tmu tpl weq vc vd tmu ve tmu vc vd ve tmu tmu weq va vb ve tmu tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl weq vc vd ve ax-mulass vc vd tmu ve tmu vc vd ve tmu tmu va vb ve tmu tmu eq-pl2 ax-mp va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd tmu ve tmu tpl weq va vb ve tmu tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd ve tmu tmu tpl weq wi va vb tmu ve tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd tmu ve tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd tmu ve tmu tpl weq va vb tmu ve tmu va vb ve tmu tmu weq va vb tmu ve tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd tmu ve tmu tpl weq va vb ve ax-mulass va vb tmu ve tmu va vb ve tmu tmu vc vd tmu ve tmu eq-pl1 ax-mp va vb tmu vc vd tmu tpl ve tmu va vb tmu ve tmu vc vd tmu ve tmu tpl weq va vb tmu ve tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd tmu ve tmu tpl weq va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd tmu ve tmu tpl weq wi va vb tmu vc vd tmu ve sdg-jacgen-rdistr va vb tmu vc vd tmu tpl ve tmu va vb tmu ve tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd tmu ve tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd tmu ve tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl ve tmu va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu eq-pl1 ax-mp va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl ve tmu va vf tmu vc vg tmu tpl vu tmu tpl va vb ve tmu tmu vc vd ve tmu tmu tpl va vf vu tmu tmu vc vg vu tmu tmu tpl tpl va vb ve tmu vf vu tmu tpl tmu vc vd ve tmu vg vu tmu tpl tmu tpl eqtri ax-mp ax-mp $.
sdg-jacgen-assoc12 $p |- ( ( ( ( a * b ) + ( c * d ) ) * v ) + ( ( ( a * f ) + ( c * g ) ) * w ) ) = ( ( a * ( ( b * v ) + ( f * w ) ) ) + ( c * ( ( d * v ) + ( g * w ) ) ) ) $= va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq vc vd vv tmu vg vw tmu tpl tmu vc vd vv tmu tmu vc vg vw tmu tmu tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq vc vd vv tmu vg vw tmu ax-distr vc vd vv tmu vg vw tmu tpl tmu vc vd vv tmu tmu vc vg vw tmu tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl eq-pl2 ax-mp va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq wi va vb vv tmu vf vw tmu tpl tmu va vb vv tmu tmu va vf vw tmu tmu tpl weq va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu vf vw tmu ax-distr va vb vv tmu vf vw tmu tpl tmu va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu eq-pl1 ax-mp va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl eqtri ax-mp ax-mp va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl eqcom ax-mp va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl weq va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq wi vc vg vw tmu tmu va vb vv tmu tmu vc vd vv tmu tmu va vf vw tmu tmu sdg-jacgen-shuffle4 va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu tmu va vf vw tmu tmu tpl vc vd vv tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl weq wi va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg vw tmu tmu tpl weq va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq va vf vw tmu tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl weq va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg vw tmu tmu tpl weq vc vg tmu vw tmu vc vg vw tmu tmu weq va vf vw tmu tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl weq vc vg vw ax-mulass vc vg tmu vw tmu vc vg vw tmu tmu va vf vw tmu tmu eq-pl2 ax-mp va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg tmu vw tmu tpl weq va vf vw tmu tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl weq va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg vw tmu tmu tpl weq wi va vf tmu vw tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg tmu vw tmu tpl weq va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg tmu vw tmu tpl weq va vf tmu vw tmu va vf vw tmu tmu weq va vf tmu vw tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg tmu vw tmu tpl weq va vf vw ax-mulass va vf tmu vw tmu va vf vw tmu tmu vc vg tmu vw tmu eq-pl1 ax-mp va vf tmu vc vg tmu tpl vw tmu va vf tmu vw tmu vc vg tmu vw tmu tpl weq va vf tmu vw tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg tmu vw tmu tpl weq va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg tmu vw tmu tpl weq wi va vf tmu vc vg tmu vw sdg-jacgen-rdistr va vf tmu vc vg tmu tpl vw tmu va vf tmu vw tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg tmu vw tmu tpl eqtri ax-mp ax-mp va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg tmu vw tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl eqtri ax-mp ax-mp va vf tmu vc vg tmu tpl vw tmu va vf vw tmu tmu vc vg vw tmu tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl eq-pl2 ax-mp va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl weq va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl weq wi va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd vv tmu tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl weq va vb vv tmu tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd vv tmu tmu tpl weq vc vd tmu vv tmu vc vd vv tmu tmu weq va vb vv tmu tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl weq vc vd vv ax-mulass vc vd tmu vv tmu vc vd vv tmu tmu va vb vv tmu tmu eq-pl2 ax-mp va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd tmu vv tmu tpl weq va vb vv tmu tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd vv tmu tmu tpl weq wi va vb tmu vv tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd tmu vv tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd tmu vv tmu tpl weq va vb tmu vv tmu va vb vv tmu tmu weq va vb tmu vv tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd tmu vv tmu tpl weq va vb vv ax-mulass va vb tmu vv tmu va vb vv tmu tmu vc vd tmu vv tmu eq-pl1 ax-mp va vb tmu vc vd tmu tpl vv tmu va vb tmu vv tmu vc vd tmu vv tmu tpl weq va vb tmu vv tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd tmu vv tmu tpl weq va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd tmu vv tmu tpl weq wi va vb tmu vc vd tmu vv sdg-jacgen-rdistr va vb tmu vc vd tmu tpl vv tmu va vb tmu vv tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd tmu vv tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd tmu vv tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl vv tmu va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu eq-pl1 ax-mp va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl eqtri ax-mp ax-mp va vb tmu vc vd tmu tpl vv tmu va vf tmu vc vg tmu tpl vw tmu tpl va vb vv tmu tmu vc vd vv tmu tmu tpl va vf vw tmu tmu vc vg vw tmu tmu tpl tpl va vb vv tmu vf vw tmu tpl tmu vc vd vv tmu vg vw tmu tpl tmu tpl eqtri ax-mp ax-mp $.
