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
   NON-ABELIAN BRACKET ALGEBRA (sdgnonabFbuild) — BOOK-3 WAVE-7.
   The pure-ring inv/distribution toolkit underlying the non-
   abelian homogeneous Yang-Mills field equation DF=grad F+[A,F]=0:
   neguniq (additive-inverse uniqueness), eqneg (inv-congruence),
   invinv (involution), invadd, mulneg / mulnegr (scalar through
   inverse), brktantisym (the bracket is antisymmetric, [a,b]=
   inv[b,a]).  GENUINE & NON-VACUOUS: these are inv/distribution
   identities true in ANY ring, NOT commutator-collapse (over the
   commutative base every symbolic [x,y] is 0, so a symbolic
   Jacobi would be VACUOUS and is deliberately NOT shipped).  The
   genuine non-abelian non-vacuity is the structural 2x2 route
   (waves 4-5) whose non-vacuity is the GROUNDED spine 1!=0
   (wave 6).  NOT the full DF=0 assembly, NOT matrix-Jacobi at a
   non-vanishing witness, NOT the inhomogeneous D*F=J, NOT
   action/Hodge/matter/quantization — all NAMED residuals.  PURE
   RING, nothing classical, NO new substrate commitment.  Self-
   contained over the FROZEN eq-ap-extended data/sdg.base.mm;
   disjoint `sdg-nonabF-*` labels; shares no $p with any corpus.
   ================================================================ $)

sdg-nonabF-eqneg $p |- ( x = y -> ( inv x ) = ( inv y ) ) $= vx vy weq t0 vy tneg tpl vy tneg weq wi vx vy weq vx tneg vy tneg weq wi t0 vy tneg tpl vy tneg weq vx vy weq t0 vy tneg tpl vy tneg weq wi vy tneg t0 tpl vy tneg weq t0 vy tneg tpl vy tneg weq vy tneg ax-add0 t0 vy tneg tpl vy tneg t0 tpl weq vy tneg t0 tpl vy tneg weq t0 vy tneg tpl vy tneg weq wi t0 vy tneg ax-addcom t0 vy tneg tpl vy tneg t0 tpl vy tneg eqtri ax-mp ax-mp t0 vy tneg tpl vy tneg weq vx vy weq ax-1 ax-mp vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq t0 vy tneg tpl vy tneg weq wi vx vy weq vx tneg vy tneg weq wi wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vx tneg tpl t0 weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx ax-addneg vx vx tneg tpl t0 vy tneg eq-pl1 ax-mp vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq wi vx vy weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx tneg vx tpl vx vx tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx ax-addcom vx tneg vx tpl vx vx tneg tpl vy tneg eq-pl1 ax-mp vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vy vx weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy eqcom vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi wi vx vy weq vy vx weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi wi vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi wi vy vx vx tneg eq-pl2 vy vx weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq ax-1 ax-mp vx vy weq vy vx weq vx tneg vy tpl vx tneg vx tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi wi vx tneg vy tpl vx tneg vx tpl vy tneg eq-pl1 vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vy tpl vx tneg vx tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx tneg vy tpl vy tneg tpl vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vy vy tneg ax-addass vx tneg vy tpl vy tneg tpl vx tneg vy vy tneg tpl tpl eqcom ax-mp vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi t0 vy vy tneg tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vy vy tneg tpl t0 weq t0 vy vy tneg tpl weq vy ax-addneg vy vy tneg tpl t0 eqcom ax-mp t0 vy vy tneg tpl vx tneg eq-pl2 ax-mp vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg vx tneg t0 tpl weq wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx tneg vx tneg t0 tpl weq vx vy weq vx tneg vx tneg t0 tpl weq wi vx tneg t0 tpl vx tneg weq vx tneg vx tneg t0 tpl weq vx tneg ax-add0 vx tneg t0 tpl vx tneg eqcom ax-mp vx tneg vx tneg t0 tpl weq vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx vy weq vx tneg vx tneg t0 tpl weq wi vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi wi vx tneg vx tneg t0 tpl vx tneg vy vy tneg tpl tpl eqtri vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg t0 tpl weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg t0 tpl vx tneg vy vy tneg tpl tpl weq vx tneg vx tneg vy vy tneg tpl tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq wi vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl eqtri vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vy vy tneg tpl tpl weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vy vy tneg tpl tpl vx tneg vy tpl vy tneg tpl weq vx tneg vx tneg vy tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq wi vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl eqtri vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vy tpl vy tneg tpl weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vy tpl vy tneg tpl vx tneg vx tpl vy tneg tpl weq vx tneg vx tneg vx tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq wi vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi wi vx tneg vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl eqtri vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx tneg vx tpl vy tneg tpl weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx tneg vx tpl vy tneg tpl vx vx tneg tpl vy tneg tpl weq vx tneg vx vx tneg tpl vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq wi vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi wi vx tneg vx vx tneg tpl vy tneg tpl t0 vy tneg tpl eqtri vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg vx vx tneg tpl vy tneg tpl weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq wi ax-2 ax-mp ax-mp vx vy weq vx vx tneg tpl vy tneg tpl t0 vy tneg tpl weq vx tneg t0 vy tneg tpl weq ax-2 ax-mp ax-mp vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx vy weq vx tneg t0 vy tneg tpl weq wi vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi wi vx tneg t0 vy tneg tpl vy tneg eqtri vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi wi vx vy weq ax-1 ax-mp vx vy weq vx tneg t0 vy tneg tpl weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq wi ax-2 ax-mp ax-mp vx vy weq t0 vy tneg tpl vy tneg weq vx tneg vy tneg weq ax-2 ax-mp ax-mp $.
sdg-nonabF-neguniq $p |- ( ( u + v ) = 0 -> v = ( inv u ) ) $= vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq wi vu vv tpl t0 weq vv vu tneg weq wi t0 vu tneg tpl vu tneg weq vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq wi vu tneg t0 tpl vu tneg weq t0 vu tneg tpl vu tneg weq vu tneg ax-add0 t0 vu tneg tpl vu tneg t0 tpl weq vu tneg t0 tpl vu tneg weq t0 vu tneg tpl vu tneg weq wi t0 vu tneg ax-addcom t0 vu tneg tpl vu tneg t0 tpl vu tneg eqtri ax-mp ax-mp t0 vu tneg tpl vu tneg weq vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq wi vu vv tpl t0 weq vv vu tneg weq wi wi vu vv tpl t0 weq vv t0 vu tneg tpl weq wi vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi vu vv tpl t0 weq vv t0 vu tneg tpl weq wi vu vv tpl t0 weq vu vv tpl t0 weq wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl t0 weq wi wi vu vv tpl t0 weq vu vv tpl t0 weq wi vu vv tpl t0 weq vu vv tpl t0 weq ax-1 vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl t0 weq wi vu vv tpl t0 weq wi wi vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl t0 weq wi wi vu vv tpl t0 weq vu vv tpl t0 weq wi wi vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl t0 weq wi ax-1 vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl t0 weq wi vu vv tpl t0 weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vu vv tpl t0 weq wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi wi vu vv tpl t0 vu tneg eq-pl1 vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq wi vu vv tpl t0 weq vv t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq wi vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq wi vv vu tpl vu vv tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu ax-addcom vv vu tpl vu vv tpl vu tneg eq-pl1 ax-mp vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq wi vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq wi vv vu tpl vu tneg tpl vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vu vu tneg ax-addass vv vu tpl vu tneg tpl vv vu vu tneg tpl tpl eqcom ax-mp vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq wi vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq wi vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq wi vv t0 tpl vv vu vu tneg tpl tpl weq vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq wi t0 vu vu tneg tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vu vu tneg tpl t0 weq t0 vu vu tneg tpl weq vu ax-addneg vu vu tneg tpl t0 eqcom ax-mp t0 vu vu tneg tpl vv eq-pl2 ax-mp vv t0 tpl vv vu vu tneg tpl tpl weq vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq wi vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq wi wi vu vv tpl t0 weq vv vv t0 tpl weq wi vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi vv vv t0 tpl weq vu vv tpl t0 weq vv vv t0 tpl weq wi vv t0 tpl vv weq vv vv t0 tpl weq vv ax-add0 vv t0 tpl vv eqcom ax-mp vv vv t0 tpl weq vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vv t0 tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi wi vu vv tpl t0 weq vv vv t0 tpl weq wi vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi wi vv vv t0 tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi vu vv tpl t0 weq vv vv t0 tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi wi vv vv t0 tpl vv vu vu tneg tpl tpl eqtri vv vv t0 tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vv t0 tpl weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq wi ax-2 ax-mp ax-mp vu vv tpl t0 weq vv t0 tpl vv vu vu tneg tpl tpl weq vv vv vu vu tneg tpl tpl weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi wi vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq wi vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi wi vv vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi wi vv vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl eqtri vv vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vv vu vu tneg tpl tpl weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq wi ax-2 ax-mp ax-mp vu vv tpl t0 weq vv vu vu tneg tpl tpl vv vu tpl vu tneg tpl weq vv vv vu tpl vu tneg tpl weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi wi vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq wi vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi wi vv vv vu tpl vu tneg tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi wi vv vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl eqtri vv vv vu tpl vu tneg tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vv vu tpl vu tneg tpl weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq wi ax-2 ax-mp ax-mp vu vv tpl t0 weq vv vu tpl vu tneg tpl vu vv tpl vu tneg tpl weq vv vu vv tpl vu tneg tpl weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi wi vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq wi vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi wi vv vu vv tpl vu tneg tpl weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi wi vv vu vv tpl vu tneg tpl t0 vu tneg tpl eqtri vv vu vv tpl vu tneg tpl weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv vu vv tpl vu tneg tpl weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq wi ax-2 ax-mp ax-mp vu vv tpl t0 weq vu vv tpl vu tneg tpl t0 vu tneg tpl weq vv t0 vu tneg tpl weq ax-2 ax-mp ax-mp vu vv tpl t0 weq vv t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi wi vu vv tpl t0 weq vv t0 vu tneg tpl weq wi vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi wi vv t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi vu vv tpl t0 weq vv t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi wi vv t0 vu tneg tpl vu tneg eqtri vv t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi wi vu vv tpl t0 weq ax-1 ax-mp vu vv tpl t0 weq vv t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg weq wi ax-2 ax-mp ax-mp vu vv tpl t0 weq t0 vu tneg tpl vu tneg weq vv vu tneg weq ax-2 ax-mp ax-mp $.
sdg-nonabF-invinv $p |- ( inv ( inv x ) ) = x $= vx vx tneg tneg weq vx tneg tneg vx weq vx tneg vx tpl t0 weq vx vx tneg tneg weq vx vx tneg tpl t0 weq vx tneg vx tpl t0 weq vx ax-addneg vx tneg vx tpl vx vx tneg tpl weq vx vx tneg tpl t0 weq vx tneg vx tpl t0 weq wi vx vx tneg tpl vx tneg vx tpl weq vx tneg vx tpl vx vx tneg tpl weq vx vx tneg ax-addcom vx vx tneg tpl vx tneg vx tpl eqcom ax-mp vx tneg vx tpl vx vx tneg tpl t0 eqtri ax-mp ax-mp vx tneg vx sdg-nonabF-neguniq ax-mp vx vx tneg tneg eqcom ax-mp $.
sdg-nonabF-invadd $p |- ( inv ( u + v ) ) = ( ( inv u ) + ( inv v ) ) $= vu tneg vv tneg tpl vu vv tpl tneg weq vu vv tpl tneg vu tneg vv tneg tpl weq vu vv tpl vu tneg vv tneg tpl tpl t0 weq vu tneg vv tneg tpl vu vv tpl tneg weq vu vu tneg tpl t0 weq vu vv tpl vu tneg vv tneg tpl tpl t0 weq vu ax-addneg vu vv tpl vu tneg vv tneg tpl tpl vu vu tneg tpl weq vu vu tneg tpl t0 weq vu vv tpl vu tneg vv tneg tpl tpl t0 weq wi vu vv vu tneg vv tneg tpl tpl tpl vu vu tneg tpl weq vu vv tpl vu tneg vv tneg tpl tpl vu vu tneg tpl weq vv vu tneg vv tneg tpl tpl vu tneg weq vu vv vu tneg vv tneg tpl tpl tpl vu vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg vv tneg tpl tpl vu tneg weq vu tneg t0 tpl vu tneg weq t0 vu tneg tpl vu tneg weq vu tneg ax-add0 t0 vu tneg tpl vu tneg t0 tpl weq vu tneg t0 tpl vu tneg weq t0 vu tneg tpl vu tneg weq wi t0 vu tneg ax-addcom t0 vu tneg tpl vu tneg t0 tpl vu tneg eqtri ax-mp ax-mp vv vu tneg vv tneg tpl tpl t0 vu tneg tpl weq t0 vu tneg tpl vu tneg weq vv vu tneg vv tneg tpl tpl vu tneg weq wi vv vv tneg tpl vu tneg tpl t0 vu tneg tpl weq vv vu tneg vv tneg tpl tpl t0 vu tneg tpl weq vv vv tneg tpl t0 weq vv vv tneg tpl vu tneg tpl t0 vu tneg tpl weq vv ax-addneg vv vv tneg tpl t0 vu tneg eq-pl1 ax-mp vv vu tneg vv tneg tpl tpl vv vv tneg tpl vu tneg tpl weq vv vv tneg tpl vu tneg tpl t0 vu tneg tpl weq vv vu tneg vv tneg tpl tpl t0 vu tneg tpl weq wi vv vv tneg vu tneg tpl tpl vv vv tneg tpl vu tneg tpl weq vv vu tneg vv tneg tpl tpl vv vv tneg tpl vu tneg tpl weq vv vv tneg tpl vu tneg tpl vv vv tneg vu tneg tpl tpl weq vv vv tneg vu tneg tpl tpl vv vv tneg tpl vu tneg tpl weq vv vv tneg vu tneg ax-addass vv vv tneg tpl vu tneg tpl vv vv tneg vu tneg tpl tpl eqcom ax-mp vv vu tneg vv tneg tpl tpl vv vv tneg vu tneg tpl tpl weq vv vv tneg vu tneg tpl tpl vv vv tneg tpl vu tneg tpl weq vv vu tneg vv tneg tpl tpl vv vv tneg tpl vu tneg tpl weq wi vu tneg vv tneg tpl vv tneg vu tneg tpl weq vv vu tneg vv tneg tpl tpl vv vv tneg vu tneg tpl tpl weq vu tneg vv tneg ax-addcom vu tneg vv tneg tpl vv tneg vu tneg tpl vv eq-pl2 ax-mp vv vu tneg vv tneg tpl tpl vv vv tneg vu tneg tpl tpl vv vv tneg tpl vu tneg tpl eqtri ax-mp ax-mp vv vu tneg vv tneg tpl tpl vv vv tneg tpl vu tneg tpl t0 vu tneg tpl eqtri ax-mp ax-mp vv vu tneg vv tneg tpl tpl t0 vu tneg tpl vu tneg eqtri ax-mp ax-mp vv vu tneg vv tneg tpl tpl vu tneg vu eq-pl2 ax-mp vu vv tpl vu tneg vv tneg tpl tpl vu vv vu tneg vv tneg tpl tpl tpl weq vu vv vu tneg vv tneg tpl tpl tpl vu vu tneg tpl weq vu vv tpl vu tneg vv tneg tpl tpl vu vu tneg tpl weq wi vu vv vu tneg vv tneg tpl ax-addass vu vv tpl vu tneg vv tneg tpl tpl vu vv vu tneg vv tneg tpl tpl tpl vu vu tneg tpl eqtri ax-mp ax-mp vu vv tpl vu tneg vv tneg tpl tpl vu vu tneg tpl t0 eqtri ax-mp ax-mp vu vv tpl vu tneg vv tneg tpl sdg-nonabF-neguniq ax-mp vu tneg vv tneg tpl vu vv tpl tneg eqcom ax-mp $.
sdg-nonabF-mulneg $p |- ( a * ( inv w ) ) = ( inv ( a * w ) ) $= va vw tmu va vw tneg tmu tpl t0 weq va vw tneg tmu va vw tmu tneg weq va t0 tmu t0 weq va vw tmu va vw tneg tmu tpl t0 weq va ax-mul0 va vw tmu va vw tneg tmu tpl va t0 tmu weq va t0 tmu t0 weq va vw tmu va vw tneg tmu tpl t0 weq wi va vw vw tneg tpl tmu va t0 tmu weq va vw tmu va vw tneg tmu tpl va t0 tmu weq vw vw tneg tpl t0 weq va vw vw tneg tpl tmu va t0 tmu weq vw ax-addneg vw vw tneg tpl t0 va eq-mu2 ax-mp va vw tmu va vw tneg tmu tpl va vw vw tneg tpl tmu weq va vw vw tneg tpl tmu va t0 tmu weq va vw tmu va vw tneg tmu tpl va t0 tmu weq wi va vw vw tneg tpl tmu va vw tmu va vw tneg tmu tpl weq va vw tmu va vw tneg tmu tpl va vw vw tneg tpl tmu weq va vw vw tneg ax-distr va vw vw tneg tpl tmu va vw tmu va vw tneg tmu tpl eqcom ax-mp va vw tmu va vw tneg tmu tpl va vw vw tneg tpl tmu va t0 tmu eqtri ax-mp ax-mp va vw tmu va vw tneg tmu tpl va t0 tmu t0 eqtri ax-mp ax-mp va vw tmu va vw tneg tmu sdg-nonabF-neguniq ax-mp $.
sdg-nonabF-mulnegr $p |- ( ( inv w ) * a ) = ( inv ( w * a ) ) $= va vw tmu tneg vw va tmu tneg weq vw tneg va tmu vw va tmu tneg weq va vw tmu vw va tmu weq va vw tmu tneg vw va tmu tneg weq va vw ax-mulcom va vw tmu vw va tmu sdg-nonabF-eqneg ax-mp vw tneg va tmu va vw tmu tneg weq va vw tmu tneg vw va tmu tneg weq vw tneg va tmu vw va tmu tneg weq wi va vw tneg tmu va vw tmu tneg weq vw tneg va tmu va vw tmu tneg weq va vw sdg-nonabF-mulneg vw tneg va tmu va vw tneg tmu weq va vw tneg tmu va vw tmu tneg weq vw tneg va tmu va vw tmu tneg weq wi vw tneg va ax-mulcom vw tneg va tmu va vw tneg tmu va vw tmu tneg eqtri ax-mp ax-mp vw tneg va tmu va vw tmu tneg vw va tmu tneg eqtri ax-mp ax-mp $.
sdg-nonabF-brktantisym $p |- ( ( a * b ) + ( inv ( b * a ) ) ) = ( inv ( ( b * a ) + ( inv ( a * b ) ) ) ) $= vb va tmu tneg va vb tmu tneg tneg tpl vb va tmu va vb tmu tneg tpl tneg weq va vb tmu vb va tmu tneg tpl vb va tmu va vb tmu tneg tpl tneg weq vb va tmu va vb tmu tneg tpl tneg vb va tmu tneg va vb tmu tneg tneg tpl weq vb va tmu tneg va vb tmu tneg tneg tpl vb va tmu va vb tmu tneg tpl tneg weq vb va tmu va vb tmu tneg sdg-nonabF-invadd vb va tmu va vb tmu tneg tpl tneg vb va tmu tneg va vb tmu tneg tneg tpl eqcom ax-mp va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tneg tneg tpl weq vb va tmu tneg va vb tmu tneg tneg tpl vb va tmu va vb tmu tneg tpl tneg weq va vb tmu vb va tmu tneg tpl vb va tmu va vb tmu tneg tpl tneg weq wi vb va tmu tneg va vb tmu tpl vb va tmu tneg va vb tmu tneg tneg tpl weq va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tneg tneg tpl weq va vb tmu va vb tmu tneg tneg weq vb va tmu tneg va vb tmu tpl vb va tmu tneg va vb tmu tneg tneg tpl weq va vb tmu tneg tneg va vb tmu weq va vb tmu va vb tmu tneg tneg weq va vb tmu sdg-nonabF-invinv va vb tmu tneg tneg va vb tmu eqcom ax-mp va vb tmu va vb tmu tneg tneg vb va tmu tneg eq-pl2 ax-mp va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tpl weq vb va tmu tneg va vb tmu tpl vb va tmu tneg va vb tmu tneg tneg tpl weq va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tneg tneg tpl weq wi va vb tmu vb va tmu tneg ax-addcom va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tpl vb va tmu tneg va vb tmu tneg tneg tpl eqtri ax-mp ax-mp va vb tmu vb va tmu tneg tpl vb va tmu tneg va vb tmu tneg tneg tpl vb va tmu va vb tmu tneg tpl tneg eqtri ax-mp ax-mp $.
