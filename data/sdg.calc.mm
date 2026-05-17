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
   POINTWISE SYNTHETIC DIFFERENTIATION RULES (sdgcalcbuild).
   Self-contained over the data/sdg.base.mm surface; independent of
   data/sdg.mm (no shared $p; disjoint `sdg-calc-*` labels) so the
   two corpora never merge-conflict.  POINTWISE ONLY: no
   ax-microcancel, no ax-gen over a linking universal, no
   pointwise->global seam (that is the separate keystone SDG-K).
   SUM: pure ring.  PRODUCT (Leibniz): genuinely consumes d*d=0.
   Dscale: R-scaling of an infinitesimal is infinitesimal (d*d=0).
   CHAIN: derived modulo ONE explicit ap-Leibniz $e (chain.sub) —
   the substrate instantiates congruence only for + and * , not
   for the application symbol `ap`; surfaced, not faked.
   ================================================================ $)

${
  addcan.h $e |- ( z + u ) = ( z + v ) $.
  sdg-calc-addcan $p |- u = v $= vz tneg vz vu tpl tpl vv weq vu vv weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq vv t0 tpl vv weq t0 vv tpl vv weq vv ax-add0 t0 vv tpl vv t0 tpl weq vv t0 tpl vv weq t0 vv tpl vv weq wi t0 vv ax-addcom t0 vv tpl vv t0 tpl vv eqtri ax-mp ax-mp vz tneg vz tpl vv tpl t0 vv tpl weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vv tpl t0 vv tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vv eq-pl1 ax-mp vz tneg vz tpl vv tpl t0 vv tpl vv eqtri ax-mp ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq wi vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz vv ax-addass vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl eqcom ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl vv eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq addcan.h vz vu tpl vz vv tpl vz tneg eq-pl2 ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl vv eqtri ax-mp ax-mp vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq vu t0 tpl vu weq t0 vu tpl vu weq vu ax-add0 t0 vu tpl vu t0 tpl weq vu t0 tpl vu weq t0 vu tpl vu weq wi t0 vu ax-addcom t0 vu tpl vu t0 tpl vu eqtri ax-mp ax-mp vz tneg vz tpl vu tpl t0 vu tpl weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vu tpl t0 vu tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vu eq-pl1 ax-mp vz tneg vz tpl vu tpl t0 vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq wi vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz vu ax-addass vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl eqcom ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vu eqcom ax-mp vu vz tneg vz vu tpl tpl vv eqtri ax-mp ax-mp $.
$}
sdg-calc-add4 $p |- ( ( x + y ) + ( z + e ) ) = ( ( x + z ) + ( y + e ) ) $= vx vz vy ve tpl tpl tpl vx vz tpl vy ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vz tpl vy ve tpl tpl weq vx vz tpl vy ve tpl tpl vx vz vy ve tpl tpl tpl weq vx vz vy ve tpl tpl tpl vx vz tpl vy ve tpl tpl weq vx vz vy ve tpl ax-addass vx vz tpl vy ve tpl tpl vx vz vy ve tpl tpl tpl eqcom ax-mp vx vy tpl vz ve tpl tpl vx vz vy ve tpl tpl tpl weq vx vz vy ve tpl tpl tpl vx vz tpl vy ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vz tpl vy ve tpl tpl weq wi vx vz vy tpl ve tpl tpl vx vz vy ve tpl tpl tpl weq vx vy tpl vz ve tpl tpl vx vz vy ve tpl tpl tpl weq vz vy tpl ve tpl vz vy ve tpl tpl weq vx vz vy tpl ve tpl tpl vx vz vy ve tpl tpl tpl weq vz vy ve ax-addass vz vy tpl ve tpl vz vy ve tpl tpl vx eq-pl2 ax-mp vx vy tpl vz ve tpl tpl vx vz vy tpl ve tpl tpl weq vx vz vy tpl ve tpl tpl vx vz vy ve tpl tpl tpl weq vx vy tpl vz ve tpl tpl vx vz vy ve tpl tpl tpl weq wi vx vy vz tpl ve tpl tpl vx vz vy tpl ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vz vy tpl ve tpl tpl weq vy vz tpl ve tpl vz vy tpl ve tpl weq vx vy vz tpl ve tpl tpl vx vz vy tpl ve tpl tpl weq vy vz tpl vz vy tpl weq vy vz tpl ve tpl vz vy tpl ve tpl weq vy vz ax-addcom vy vz tpl vz vy tpl ve eq-pl1 ax-mp vy vz tpl ve tpl vz vy tpl ve tpl vx eq-pl2 ax-mp vx vy tpl vz ve tpl tpl vx vy vz tpl ve tpl tpl weq vx vy vz tpl ve tpl tpl vx vz vy tpl ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vz vy tpl ve tpl tpl weq wi vx vy vz ve tpl tpl tpl vx vy vz tpl ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vy vz tpl ve tpl tpl weq vy vz ve tpl tpl vy vz tpl ve tpl weq vx vy vz ve tpl tpl tpl vx vy vz tpl ve tpl tpl weq vy vz tpl ve tpl vy vz ve tpl tpl weq vy vz ve tpl tpl vy vz tpl ve tpl weq vy vz ve ax-addass vy vz tpl ve tpl vy vz ve tpl tpl eqcom ax-mp vy vz ve tpl tpl vy vz tpl ve tpl vx eq-pl2 ax-mp vx vy tpl vz ve tpl tpl vx vy vz ve tpl tpl tpl weq vx vy vz ve tpl tpl tpl vx vy vz tpl ve tpl tpl weq vx vy tpl vz ve tpl tpl vx vy vz tpl ve tpl tpl weq wi vx vy vz ve tpl ax-addass vx vy tpl vz ve tpl tpl vx vy vz ve tpl tpl tpl vx vy vz tpl ve tpl tpl eqtri ax-mp ax-mp vx vy tpl vz ve tpl tpl vx vy vz tpl ve tpl tpl vx vz vy tpl ve tpl tpl eqtri ax-mp ax-mp vx vy tpl vz ve tpl tpl vx vz vy tpl ve tpl tpl vx vz vy ve tpl tpl tpl eqtri ax-mp ax-mp vx vy tpl vz ve tpl tpl vx vz vy ve tpl tpl tpl vx vz tpl vy ve tpl tpl eqtri ax-mp ax-mp $.
sdg-calc-rdistr $p |- ( ( x + y ) * z ) = ( ( x * z ) + ( y * z ) ) $= vx vz tmu vz vy tmu tpl vx vz tmu vy vz tmu tpl weq vx vy tpl vz tmu vx vz tmu vy vz tmu tpl weq vz vy tmu vy vz tmu weq vx vz tmu vz vy tmu tpl vx vz tmu vy vz tmu tpl weq vz vy ax-mulcom vz vy tmu vy vz tmu vx vz tmu eq-pl2 ax-mp vx vy tpl vz tmu vx vz tmu vz vy tmu tpl weq vx vz tmu vz vy tmu tpl vx vz tmu vy vz tmu tpl weq vx vy tpl vz tmu vx vz tmu vy vz tmu tpl weq wi vz vx tmu vz vy tmu tpl vx vz tmu vz vy tmu tpl weq vx vy tpl vz tmu vx vz tmu vz vy tmu tpl weq vz vx tmu vx vz tmu weq vz vx tmu vz vy tmu tpl vx vz tmu vz vy tmu tpl weq vz vx ax-mulcom vz vx tmu vx vz tmu vz vy tmu eq-pl1 ax-mp vx vy tpl vz tmu vz vx tmu vz vy tmu tpl weq vz vx tmu vz vy tmu tpl vx vz tmu vz vy tmu tpl weq vx vy tpl vz tmu vx vz tmu vz vy tmu tpl weq wi vz vx vy tpl tmu vz vx tmu vz vy tmu tpl weq vx vy tpl vz tmu vz vx tmu vz vy tmu tpl weq vz vx vy ax-distr vx vy tpl vz tmu vz vx vy tpl tmu weq vz vx vy tpl tmu vz vx tmu vz vy tmu tpl weq vx vy tpl vz tmu vz vx tmu vz vy tmu tpl weq wi vx vy tpl vz ax-mulcom vx vy tpl vz tmu vz vx vy tpl tmu vz vx tmu vz vy tmu tpl eqtri ax-mp ax-mp vx vy tpl vz tmu vz vx tmu vz vy tmu tpl vx vz tmu vz vy tmu tpl eqtri ax-mp ax-mp vx vy tpl vz tmu vx vz tmu vz vy tmu tpl vx vz tmu vy vz tmu tpl eqtri ax-mp ax-mp $.
${
  sum.hf $e |- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) $.
  sum.hg $e |- ( ap g d ) = ( ( ap g 0 ) + ( c * d ) ) $.
  sum.hh $e |- ( ap w d ) = ( ( ap f d ) + ( ap g d ) ) $.
  sum.hh0 $e |- ( ap w 0 ) = ( ( ap f 0 ) + ( ap g 0 ) ) $.
  sdg-calc-sum $p |- ( ap w d ) = ( ( ap w 0 ) + ( ( b + c ) * d ) ) $= t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl t0 vw tap vb vc tpl vd tmu tpl weq vd vw tap t0 vw tap vb vc tpl vd tmu tpl weq t0 vf tap t0 vg tap tpl t0 vw tap weq t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl t0 vw tap vb vc tpl vd tmu tpl weq t0 vw tap t0 vf tap t0 vg tap tpl weq t0 vf tap t0 vg tap tpl t0 vw tap weq sum.hh0 t0 vw tap t0 vf tap t0 vg tap tpl eqcom ax-mp t0 vf tap t0 vg tap tpl t0 vw tap vb vc tpl vd tmu eq-pl1 ax-mp vd vw tap t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl t0 vw tap vb vc tpl vd tmu tpl weq vd vw tap t0 vw tap vb vc tpl vd tmu tpl weq wi t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq vd vw tap t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq vb vd tmu vc vd tmu tpl vb vc tpl vd tmu weq t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq vb vc tpl vd tmu vb vd tmu vc vd tmu tpl weq vb vd tmu vc vd tmu tpl vb vc tpl vd tmu weq vb vc vd sdg-calc-rdistr vb vc tpl vd tmu vb vd tmu vc vd tmu tpl eqcom ax-mp vb vd tmu vc vd tmu tpl vb vc tpl vd tmu t0 vf tap t0 vg tap tpl eq-pl2 ax-mp vd vw tap t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl weq t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq vd vw tap t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl weq wi t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl weq t0 vf tap vb vd tmu t0 vg tap vc vd tmu sdg-calc-add4 vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl weq wi vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq t0 vf tap vb vd tmu tpl vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq vd vg tap t0 vg tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq sum.hg vd vg tap t0 vg tap vc vd tmu tpl t0 vf tap vb vd tmu tpl eq-pl2 ax-mp vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl vd vg tap tpl weq t0 vf tap vb vd tmu tpl vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl vd vg tap tpl weq sum.hf vd vf tap t0 vf tap vb vd tmu tpl vd vg tap eq-pl1 ax-mp vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl eqtri ax-mp ax-mp vd vw tap vd vf tap vd vg tap tpl weq vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl weq wi sum.hh vd vw tap vd vf tap vd vg tap tpl t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tpl vb vd tmu vc vd tmu tpl tpl t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tpl vb vc tpl vd tmu tpl t0 vw tap vb vc tpl vd tmu tpl eqtri ax-mp ax-mp $.
$}
${
  prod.hf $e |- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) $.
  prod.hg $e |- ( ap g d ) = ( ( ap g 0 ) + ( c * d ) ) $.
  prod.hh $e |- ( ap w d ) = ( ( ap f d ) * ( ap g d ) ) $.
  prod.hh0 $e |- ( ap w 0 ) = ( ( ap f 0 ) * ( ap g 0 ) ) $.
  prod.hD $e |- ( D d ) $.
  sdg-calc-prod $p |- ( ap w d ) = ( ( ap w 0 ) + ( ( ( ( ap f 0 ) * c ) + ( b * ( ap g 0 ) ) ) * d ) ) $= t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vd vw tap t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq t0 vf tap t0 vg tap tmu t0 vw tap weq t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq t0 vw tap t0 vf tap t0 vg tap tmu weq t0 vf tap t0 vg tap tmu t0 vw tap weq prod.hh0 t0 vw tap t0 vf tap t0 vg tap tmu eqcom ax-mp t0 vf tap t0 vg tap tmu t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu eq-pl1 ax-mp vd vw tap t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vd vw tap t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq wi t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vd vw tap t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq vb t0 vg tap tmu t0 vf tap vc tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl weq vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq vb t0 vg tap tmu t0 vf tap vc tmu ax-addcom vb t0 vg tap tmu t0 vf tap vc tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl vd eq-mu1 ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu weq wi vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq vb t0 vg tap tmu t0 vf tap vc tmu vd sdg-calc-rdistr vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl eqcom ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu weq wi vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq t0 vf tap vc vd tmu tmu t0 vf tap vc tmu vd tmu weq vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq t0 vf tap vc tmu vd tmu t0 vf tap vc vd tmu tmu weq t0 vf tap vc vd tmu tmu t0 vf tap vc tmu vd tmu weq t0 vf tap vc vd ax-mulass t0 vf tap vc tmu vd tmu t0 vf tap vc vd tmu tmu eqcom ax-mp t0 vf tap vc vd tmu tmu t0 vf tap vc tmu vd tmu vb t0 vg tap tmu vd tmu eq-pl2 ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl weq vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl weq wi vb vd tmu t0 vg tap tmu vb t0 vg tap tmu vd tmu weq vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl weq vb t0 vg tap vd tmu tmu vb t0 vg tap tmu vd tmu weq vb vd tmu t0 vg tap tmu vb t0 vg tap tmu vd tmu weq vb t0 vg tap tmu vd tmu vb t0 vg tap vd tmu tmu weq vb t0 vg tap vd tmu tmu vb t0 vg tap tmu vd tmu weq vb t0 vg tap vd ax-mulass vb t0 vg tap tmu vd tmu vb t0 vg tap vd tmu tmu eqcom ax-mp vb vd tmu t0 vg tap tmu vb t0 vg tap vd tmu tmu weq vb t0 vg tap vd tmu tmu vb t0 vg tap tmu vd tmu weq vb vd tmu t0 vg tap tmu vb t0 vg tap tmu vd tmu weq wi vb vd t0 vg tap tmu tmu vb t0 vg tap vd tmu tmu weq vb vd tmu t0 vg tap tmu vb t0 vg tap vd tmu tmu weq vd t0 vg tap tmu t0 vg tap vd tmu weq vb vd t0 vg tap tmu tmu vb t0 vg tap vd tmu tmu weq vd t0 vg tap ax-mulcom vd t0 vg tap tmu t0 vg tap vd tmu vb eq-mu2 ax-mp vb vd tmu t0 vg tap tmu vb vd t0 vg tap tmu tmu weq vb vd t0 vg tap tmu tmu vb t0 vg tap vd tmu tmu weq vb vd tmu t0 vg tap tmu vb t0 vg tap vd tmu tmu weq wi vb vd t0 vg tap ax-mulass vb vd tmu t0 vg tap tmu vb vd t0 vg tap tmu tmu vb t0 vg tap vd tmu tmu eqtri ax-mp ax-mp vb vd tmu t0 vg tap tmu vb t0 vg tap vd tmu tmu vb t0 vg tap tmu vd tmu eqtri ax-mp ax-mp vb vd tmu t0 vg tap tmu vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu eq-pl1 ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl eqtri ax-mp ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu vd tmu t0 vf tap vc tmu vd tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu eqtri ax-mp ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl vb t0 vg tap tmu t0 vf tap vc tmu tpl vd tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu eqtri ax-mp ax-mp vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu t0 vf tap t0 vg tap tmu eq-pl2 ax-mp vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq vd vw tap t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl weq wi t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu ax-addass vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl weq wi t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq t0 vf tap vc vd tmu tmu t0 tpl t0 vf tap vc vd tmu tmu weq t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu weq t0 vf tap vc vd tmu tmu ax-add0 t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu t0 tpl weq t0 vf tap vc vd tmu tmu t0 tpl t0 vf tap vc vd tmu tmu weq t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu weq wi vb vd tmu vc vd tmu tmu t0 weq t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu t0 tpl weq vb vc tmu t0 tmu t0 weq vb vd tmu vc vd tmu tmu t0 weq vb vc tmu ax-mul0 vb vd tmu vc vd tmu tmu vb vc tmu t0 tmu weq vb vc tmu t0 tmu t0 weq vb vd tmu vc vd tmu tmu t0 weq wi vb vc tmu vd vd tmu tmu vb vc tmu t0 tmu weq vb vd tmu vc vd tmu tmu vb vc tmu t0 tmu weq vd vd tmu t0 weq vb vc tmu vd vd tmu tmu vb vc tmu t0 tmu weq vd wD vd vd tmu t0 weq prod.hD vd wD vd vd tmu t0 weq wb vd wD vd vd tmu t0 weq wi vd df-D vd wD vd vd tmu t0 weq ax-bi1 ax-mp ax-mp vd vd tmu t0 vb vc tmu eq-mu2 ax-mp vb vd tmu vc vd tmu tmu vb vc tmu vd vd tmu tmu weq vb vc tmu vd vd tmu tmu vb vc tmu t0 tmu weq vb vd tmu vc vd tmu tmu vb vc tmu t0 tmu weq wi vb vc vd vd tmu tmu tmu vb vc tmu vd vd tmu tmu weq vb vd tmu vc vd tmu tmu vb vc tmu vd vd tmu tmu weq vb vc tmu vd vd tmu tmu vb vc vd vd tmu tmu tmu weq vb vc vd vd tmu tmu tmu vb vc tmu vd vd tmu tmu weq vb vc vd vd tmu ax-mulass vb vc tmu vd vd tmu tmu vb vc vd vd tmu tmu tmu eqcom ax-mp vb vd tmu vc vd tmu tmu vb vc vd vd tmu tmu tmu weq vb vc vd vd tmu tmu tmu vb vc tmu vd vd tmu tmu weq vb vd tmu vc vd tmu tmu vb vc tmu vd vd tmu tmu weq wi vb vd vc vd tmu tmu tmu vb vc vd vd tmu tmu tmu weq vb vd tmu vc vd tmu tmu vb vc vd vd tmu tmu tmu weq vd vc vd tmu tmu vc vd vd tmu tmu weq vb vd vc vd tmu tmu tmu vb vc vd vd tmu tmu tmu weq vc vd tmu vd tmu vc vd vd tmu tmu weq vd vc vd tmu tmu vc vd vd tmu tmu weq vc vd vd ax-mulass vd vc vd tmu tmu vc vd tmu vd tmu weq vc vd tmu vd tmu vc vd vd tmu tmu weq vd vc vd tmu tmu vc vd vd tmu tmu weq wi vd vc tmu vd tmu vc vd tmu vd tmu weq vd vc vd tmu tmu vc vd tmu vd tmu weq vd vc tmu vc vd tmu weq vd vc tmu vd tmu vc vd tmu vd tmu weq vd vc ax-mulcom vd vc tmu vc vd tmu vd eq-mu1 ax-mp vd vc vd tmu tmu vd vc tmu vd tmu weq vd vc tmu vd tmu vc vd tmu vd tmu weq vd vc vd tmu tmu vc vd tmu vd tmu weq wi vd vc tmu vd tmu vd vc vd tmu tmu weq vd vc vd tmu tmu vd vc tmu vd tmu weq vd vc vd ax-mulass vd vc tmu vd tmu vd vc vd tmu tmu eqcom ax-mp vd vc vd tmu tmu vd vc tmu vd tmu vc vd tmu vd tmu eqtri ax-mp ax-mp vd vc vd tmu tmu vc vd tmu vd tmu vc vd vd tmu tmu eqtri ax-mp ax-mp vd vc vd tmu tmu vc vd vd tmu tmu vb eq-mu2 ax-mp vb vd tmu vc vd tmu tmu vb vd vc vd tmu tmu tmu weq vb vd vc vd tmu tmu tmu vb vc vd vd tmu tmu tmu weq vb vd tmu vc vd tmu tmu vb vc vd vd tmu tmu tmu weq wi vb vd vc vd tmu ax-mulass vb vd tmu vc vd tmu tmu vb vd vc vd tmu tmu tmu vb vc vd vd tmu tmu tmu eqtri ax-mp ax-mp vb vd tmu vc vd tmu tmu vb vc vd vd tmu tmu tmu vb vc tmu vd vd tmu tmu eqtri ax-mp ax-mp vb vd tmu vc vd tmu tmu vb vc tmu vd vd tmu tmu vb vc tmu t0 tmu eqtri ax-mp ax-mp vb vd tmu vc vd tmu tmu vb vc tmu t0 tmu t0 eqtri ax-mp ax-mp vb vd tmu vc vd tmu tmu t0 t0 vf tap vc vd tmu tmu eq-pl2 ax-mp t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu t0 tpl t0 vf tap vc vd tmu tmu eqtri ax-mp ax-mp t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap vc vd tmu tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl eq-pl2 ax-mp vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl weq wi t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl vc vd tmu tmu t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu vc vd tmu sdg-calc-rdistr t0 vf tap vb vd tmu tpl vc vd tmu tmu t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl eq-pl2 ax-mp t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl weq t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq wi t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl weq t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl weq t0 vf tap vb vd tmu t0 vg tap sdg-calc-rdistr t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu eq-pl1 ax-mp t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl eqtri ax-mp ax-mp t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl weq t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq wi t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu ax-distr t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap vb vd tmu tpl t0 vg tap tmu t0 vf tap vb vd tmu tpl vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl weq wi vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq t0 vf tap vb vd tmu tpl vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq vd vg tap t0 vg tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq sum.hg vd vg tap t0 vg tap vc vd tmu tpl t0 vf tap vb vd tmu tpl eq-mu2 ax-mp vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl vd vg tap tmu weq t0 vf tap vb vd tmu tpl vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl vd vg tap tmu weq sum.hf vd vf tap t0 vf tap vb vd tmu tpl vd vg tap eq-mu1 ax-mp vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu eqtri ax-mp ax-mp vd vw tap vd vf tap vd vg tap tmu weq vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu weq wi prod.hh vd vw tap vd vf tap vd vg tap tmu t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu eqtri ax-mp ax-mp vd vw tap t0 vf tap vb vd tmu tpl t0 vg tap vc vd tmu tpl tmu t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu vb vd tmu vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu tpl t0 vf tap vc vd tmu tmu tpl t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tmu vb vd tmu t0 vg tap tmu t0 vf tap vc vd tmu tmu tpl tpl t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap t0 vg tap tmu t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl t0 vw tap t0 vf tap vc tmu vb t0 vg tap tmu tpl vd tmu tpl eqtri ax-mp ax-mp $.
$}
${
  dsc.hD $e |- ( D d ) $.
  sdg-calc-Dscale $p |- ( D ( b * d ) ) $= vb vd tmu vb vd tmu tmu t0 weq vb vd tmu wD vb vb tmu t0 tmu t0 weq vb vd tmu vb vd tmu tmu t0 weq vb vb tmu ax-mul0 vb vd tmu vb vd tmu tmu vb vb tmu t0 tmu weq vb vb tmu t0 tmu t0 weq vb vd tmu vb vd tmu tmu t0 weq wi vb vb tmu vd vd tmu tmu vb vb tmu t0 tmu weq vb vd tmu vb vd tmu tmu vb vb tmu t0 tmu weq vd vd tmu t0 weq vb vb tmu vd vd tmu tmu vb vb tmu t0 tmu weq vd wD vd vd tmu t0 weq dsc.hD vd wD vd vd tmu t0 weq wb vd wD vd vd tmu t0 weq wi vd df-D vd wD vd vd tmu t0 weq ax-bi1 ax-mp ax-mp vd vd tmu t0 vb vb tmu eq-mu2 ax-mp vb vd tmu vb vd tmu tmu vb vb tmu vd vd tmu tmu weq vb vb tmu vd vd tmu tmu vb vb tmu t0 tmu weq vb vd tmu vb vd tmu tmu vb vb tmu t0 tmu weq wi vb vb vd vd tmu tmu tmu vb vb tmu vd vd tmu tmu weq vb vd tmu vb vd tmu tmu vb vb tmu vd vd tmu tmu weq vb vb tmu vd vd tmu tmu vb vb vd vd tmu tmu tmu weq vb vb vd vd tmu tmu tmu vb vb tmu vd vd tmu tmu weq vb vb vd vd tmu ax-mulass vb vb tmu vd vd tmu tmu vb vb vd vd tmu tmu tmu eqcom ax-mp vb vd tmu vb vd tmu tmu vb vb vd vd tmu tmu tmu weq vb vb vd vd tmu tmu tmu vb vb tmu vd vd tmu tmu weq vb vd tmu vb vd tmu tmu vb vb tmu vd vd tmu tmu weq wi vb vd vb vd tmu tmu tmu vb vb vd vd tmu tmu tmu weq vb vd tmu vb vd tmu tmu vb vb vd vd tmu tmu tmu weq vd vb vd tmu tmu vb vd vd tmu tmu weq vb vd vb vd tmu tmu tmu vb vb vd vd tmu tmu tmu weq vb vd tmu vd tmu vb vd vd tmu tmu weq vd vb vd tmu tmu vb vd vd tmu tmu weq vb vd vd ax-mulass vd vb vd tmu tmu vb vd tmu vd tmu weq vb vd tmu vd tmu vb vd vd tmu tmu weq vd vb vd tmu tmu vb vd vd tmu tmu weq wi vd vb tmu vd tmu vb vd tmu vd tmu weq vd vb vd tmu tmu vb vd tmu vd tmu weq vd vb tmu vb vd tmu weq vd vb tmu vd tmu vb vd tmu vd tmu weq vd vb ax-mulcom vd vb tmu vb vd tmu vd eq-mu1 ax-mp vd vb vd tmu tmu vd vb tmu vd tmu weq vd vb tmu vd tmu vb vd tmu vd tmu weq vd vb vd tmu tmu vb vd tmu vd tmu weq wi vd vb tmu vd tmu vd vb vd tmu tmu weq vd vb vd tmu tmu vd vb tmu vd tmu weq vd vb vd ax-mulass vd vb tmu vd tmu vd vb vd tmu tmu eqcom ax-mp vd vb vd tmu tmu vd vb tmu vd tmu vb vd tmu vd tmu eqtri ax-mp ax-mp vd vb vd tmu tmu vb vd tmu vd tmu vb vd vd tmu tmu eqtri ax-mp ax-mp vd vb vd tmu tmu vb vd vd tmu tmu vb eq-mu2 ax-mp vb vd tmu vb vd tmu tmu vb vd vb vd tmu tmu tmu weq vb vd vb vd tmu tmu tmu vb vb vd vd tmu tmu tmu weq vb vd tmu vb vd tmu tmu vb vb vd vd tmu tmu tmu weq wi vb vd vb vd tmu ax-mulass vb vd tmu vb vd tmu tmu vb vd vb vd tmu tmu tmu vb vb vd vd tmu tmu tmu eqtri ax-mp ax-mp vb vd tmu vb vd tmu tmu vb vb vd vd tmu tmu tmu vb vb tmu vd vd tmu tmu eqtri ax-mp ax-mp vb vd tmu vb vd tmu tmu vb vb tmu vd vd tmu tmu vb vb tmu t0 tmu eqtri ax-mp ax-mp vb vd tmu vb vd tmu tmu vb vb tmu t0 tmu t0 eqtri ax-mp ax-mp vb vd tmu wD vb vd tmu vb vd tmu tmu t0 weq wb vb vd tmu vb vd tmu tmu t0 weq vb vd tmu wD wi vb vd tmu df-D vb vd tmu wD vb vd tmu vb vd tmu tmu t0 weq ax-bi2 ax-mp ax-mp $.
$}
${
  chain.hh $e |- ( ap w d ) = ( ap g ( ap f d ) ) $.
  chain.sub $e |- ( ap g ( ap f d ) ) = ( ap g ( ( ap f 0 ) + ( b * d ) ) ) $.
  chain.hg $e |- ( ap g ( ( ap f 0 ) + ( b * d ) ) ) = ( ( ap g ( ap f 0 ) ) + ( c * ( b * d ) ) ) $.
  chain.hh0 $e |- ( ap w 0 ) = ( ap g ( ap f 0 ) ) $.
  sdg-calc-chain $p |- ( ap w d ) = ( ( ap w 0 ) + ( ( c * b ) * d ) ) $= t0 vf tap vg tap vc vb tmu vd tmu tpl t0 vw tap vc vb tmu vd tmu tpl weq vd vw tap t0 vw tap vc vb tmu vd tmu tpl weq t0 vf tap vg tap t0 vw tap weq t0 vf tap vg tap vc vb tmu vd tmu tpl t0 vw tap vc vb tmu vd tmu tpl weq t0 vw tap t0 vf tap vg tap weq t0 vf tap vg tap t0 vw tap weq chain.hh0 t0 vw tap t0 vf tap vg tap eqcom ax-mp t0 vf tap vg tap t0 vw tap vc vb tmu vd tmu eq-pl1 ax-mp vd vw tap t0 vf tap vg tap vc vb tmu vd tmu tpl weq t0 vf tap vg tap vc vb tmu vd tmu tpl t0 vw tap vc vb tmu vd tmu tpl weq vd vw tap t0 vw tap vc vb tmu vd tmu tpl weq wi t0 vf tap vg tap vc vb vd tmu tmu tpl t0 vf tap vg tap vc vb tmu vd tmu tpl weq vd vw tap t0 vf tap vg tap vc vb tmu vd tmu tpl weq vc vb vd tmu tmu vc vb tmu vd tmu weq t0 vf tap vg tap vc vb vd tmu tmu tpl t0 vf tap vg tap vc vb tmu vd tmu tpl weq vc vb tmu vd tmu vc vb vd tmu tmu weq vc vb vd tmu tmu vc vb tmu vd tmu weq vc vb vd ax-mulass vc vb tmu vd tmu vc vb vd tmu tmu eqcom ax-mp vc vb vd tmu tmu vc vb tmu vd tmu t0 vf tap vg tap eq-pl2 ax-mp vd vw tap t0 vf tap vg tap vc vb vd tmu tmu tpl weq t0 vf tap vg tap vc vb vd tmu tmu tpl t0 vf tap vg tap vc vb tmu vd tmu tpl weq vd vw tap t0 vf tap vg tap vc vb tmu vd tmu tpl weq wi t0 vf tap vb vd tmu tpl vg tap t0 vf tap vg tap vc vb vd tmu tmu tpl weq vd vw tap t0 vf tap vg tap vc vb vd tmu tmu tpl weq chain.hg vd vw tap t0 vf tap vb vd tmu tpl vg tap weq t0 vf tap vb vd tmu tpl vg tap t0 vf tap vg tap vc vb vd tmu tmu tpl weq vd vw tap t0 vf tap vg tap vc vb vd tmu tmu tpl weq wi vd vf tap vg tap t0 vf tap vb vd tmu tpl vg tap weq vd vw tap t0 vf tap vb vd tmu tpl vg tap weq chain.sub vd vw tap vd vf tap vg tap weq vd vf tap vg tap t0 vf tap vb vd tmu tpl vg tap weq vd vw tap t0 vf tap vb vd tmu tpl vg tap weq wi chain.hh vd vw tap vd vf tap vg tap t0 vf tap vb vd tmu tpl vg tap eqtri ax-mp ax-mp vd vw tap t0 vf tap vb vd tmu tpl vg tap t0 vf tap vg tap vc vb vd tmu tmu tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap vg tap vc vb vd tmu tmu tpl t0 vf tap vg tap vc vb tmu vd tmu tpl eqtri ax-mp ax-mp vd vw tap t0 vf tap vg tap vc vb tmu vd tmu tpl t0 vw tap vc vb tmu vd tmu tpl eqtri ax-mp ax-mp $.
$}
