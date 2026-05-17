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
   SYNTHETIC TANGENT STRUCTURE (sdgtanbuild).
   Self-contained over the data/sdg.base.mm surface; independent of
   data/sdg.mm and data/sdg.calc.mm (no shared $p; disjoint
   `sdg-tan-*` labels) so the corpora never merge-conflict.
   R x R -> R^D (sdg-tan-base / sdg-tan-roundtrip): PURE RING.
   R^D -> R x R principal-part UNIQUENESS (sdg-tan-principal):
   GENUINELY CONSUMES ax-microcancel (KL uniqueness), threaded
   seam-free exactly like data/sdg.mm's sdg-deriv — KL consumed,
   not asserted.  LIE BRACKET (sdg-tan-bracket): the D x D
   microsquare commutator; its symmetric zeroth-order part
   vanishes by RING (sdg-tan-bracket-cross); the one genuinely
   off-limits step (compose one flow into the other's argument =
   `ap`-congruence + a globalized/generator-side derivative,
   W2-glob) is surfaced as EXACTLY ONE loud $e (tanbr.flow) —
   a precisely-characterised boundary, reported not faked.
   ================================================================ $)

${
  tanac.h $e |- ( z + u ) = ( z + v ) $.
  sdg-tan-addcan $p |- u = v $= vz tneg vz vu tpl tpl vv weq vu vv weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq vv t0 tpl vv weq t0 vv tpl vv weq vv ax-add0 t0 vv tpl vv t0 tpl weq vv t0 tpl vv weq t0 vv tpl vv weq wi t0 vv ax-addcom t0 vv tpl vv t0 tpl vv eqtri ax-mp ax-mp vz tneg vz tpl vv tpl t0 vv tpl weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vv tpl t0 vv tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vv eq-pl1 ax-mp vz tneg vz tpl vv tpl t0 vv tpl vv eqtri ax-mp ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq wi vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz vv ax-addass vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl eqcom ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl vv eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq tanac.h vz vu tpl vz vv tpl vz tneg eq-pl2 ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl vv eqtri ax-mp ax-mp vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq vu t0 tpl vu weq t0 vu tpl vu weq vu ax-add0 t0 vu tpl vu t0 tpl weq vu t0 tpl vu weq t0 vu tpl vu weq wi t0 vu ax-addcom t0 vu tpl vu t0 tpl vu eqtri ax-mp ax-mp vz tneg vz tpl vu tpl t0 vu tpl weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vu tpl t0 vu tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vu eq-pl1 ax-mp vz tneg vz tpl vu tpl t0 vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq wi vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz vu ax-addass vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl eqcom ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vu eqcom ax-mp vu vz tneg vz vu tpl tpl vv eqtri ax-mp ax-mp $.
$}
sdg-tan-addcan-imp $p |- ( ( z + u ) = ( z + v ) -> u = v ) $= vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq wi vz vu tpl vz vv tpl weq vu vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq wi vz tneg vz vv tpl tpl vv weq vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq wi vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq vv t0 tpl vv weq t0 vv tpl vv weq vv ax-add0 t0 vv tpl vv t0 tpl weq vv t0 tpl vv weq t0 vv tpl vv weq wi t0 vv ax-addcom t0 vv tpl vv t0 tpl vv eqtri ax-mp ax-mp vz tneg vz tpl vv tpl t0 vv tpl weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vv tpl t0 vv tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vv eq-pl1 ax-mp vz tneg vz tpl vv tpl t0 vv tpl vv eqtri ax-mp ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq wi vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz vv ax-addass vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl eqcom ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl vv eqtri ax-mp ax-mp vz tneg vz vv tpl tpl vv weq vz vu tpl vz vv tpl weq ax-1 ax-mp vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq wi vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi vz vu tpl vz vv tpl vz tneg eq-pl2 vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq wi vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi wi vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi wi vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl vv eqtri vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi wi vz vu tpl vz vv tpl weq ax-1 ax-mp vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi ax-2 ax-mp ax-mp vz vu tpl vz vv tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq ax-2 ax-mp ax-mp vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq wi vz vu tpl vz vv tpl weq vu vv weq wi wi vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq wi vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq wi vz tneg vz vu tpl tpl vu weq vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq wi vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq vu t0 tpl vu weq t0 vu tpl vu weq vu ax-add0 t0 vu tpl vu t0 tpl weq vu t0 tpl vu weq t0 vu tpl vu weq wi t0 vu ax-addcom t0 vu tpl vu t0 tpl vu eqtri ax-mp ax-mp vz tneg vz tpl vu tpl t0 vu tpl weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vu tpl t0 vu tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vu eq-pl1 ax-mp vz tneg vz tpl vu tpl t0 vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq wi vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz vu ax-addass vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl eqcom ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vu weq vz vu tpl vz vv tpl weq ax-1 ax-mp vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq wi wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq wi vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq wi wi vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq wi wi vz tneg vz vu tpl tpl vu eqcom vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq wi vz vu tpl vz vv tpl weq ax-1 ax-mp vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq ax-2 ax-mp ax-mp vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi wi vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi wi vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi wi vu vz tneg vz vu tpl tpl vv eqtri vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi wi vz vu tpl vz vv tpl weq ax-1 ax-mp vz vu tpl vz vv tpl weq vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi ax-2 ax-mp ax-mp vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq ax-2 ax-mp ax-mp $.
sdg-tan-base $p |- ( a + ( b * 0 ) ) = a $= va t0 tpl va weq va vb t0 tmu tpl va weq va ax-add0 va vb t0 tmu tpl va t0 tpl weq va t0 tpl va weq va vb t0 tmu tpl va weq wi vb t0 tmu t0 weq va vb t0 tmu tpl va t0 tpl weq vb ax-mul0 vb t0 tmu t0 va eq-pl2 ax-mp va vb t0 tmu tpl va t0 tpl va eqtri ax-mp ax-mp $.
sdg-tan-roundtrip $p |- ( ( a + ( b * 0 ) ) + ( b * d ) ) = ( a + ( b * d ) ) $= va vb t0 tmu tpl va weq va vb t0 tmu tpl vb vd tmu tpl va vb vd tmu tpl weq va t0 tpl va weq va vb t0 tmu tpl va weq va ax-add0 va vb t0 tmu tpl va t0 tpl weq va t0 tpl va weq va vb t0 tmu tpl va weq wi vb t0 tmu t0 weq va vb t0 tmu tpl va t0 tpl weq vb ax-mul0 vb t0 tmu t0 va eq-pl2 ax-mp va vb t0 tmu tpl va t0 tpl va eqtri ax-mp ax-mp va vb t0 tmu tpl va vb vd tmu eq-pl1 ax-mp $.
sdg-tan-slope-imp $p |- ( ( ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) /\ ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) -> ( b * d ) = ( c * d ) ) $= vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-iar vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-ial vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl eqcom vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi t0 vf tap vb vd tmu tpl vd vf tap t0 vf tap vc vd tmu tpl eqtri t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi wi t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi wi t0 vf tap vb vd tmu vc vd tmu sdg-tan-addcan-imp t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq ax-2 ax-mp ax-mp $.
${
  pp.hb $e |- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) $.
  pp.hc $e |- A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) $.
  sdg-tan-principal $p |- b = c $= vd wD vb vd tmu vc vd tmu weq wi vd wal vb vc weq vd wD vb vd tmu vc vd tmu weq wi vd vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi vd wD vb vd tmu vc vd tmu weq wi vd wD vd vf tap t0 vf tap vc vd tmu tpl weq wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi vd wD vd vf tap t0 vf tap vc vd tmu tpl weq wi vd wal vd wD vd vf tap t0 vf tap vc vd tmu tpl weq wi pp.hc vd wD vd vf tap t0 vf tap vc vd tmu tpl weq wi vd ax-spec ax-mp vd wD vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi vd wD vd vf tap t0 vf tap vc vd tmu tpl weq wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wD vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi pp.hb vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd ax-spec ax-mp vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wD vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-ian vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi wi vd wD ax-1 ax-mp vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi ax-2 ax-mp ax-mp vd wD vd vf tap t0 vf tap vc vd tmu tpl weq vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-2 ax-mp ax-mp vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa wi vd wD vb vd tmu vc vd tmu weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-iar vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-ial vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi wi vd vf tap t0 vf tap vb vd tmu tpl eqcom vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi wi t0 vf tap vb vd tmu tpl vd vf tap t0 vf tap vc vd tmu tpl eqtri t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi wi t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi wi t0 vf tap vb vd tmu vc vd tmu sdg-tan-addcan-imp t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq wi vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa ax-1 ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq vb vd tmu vc vd tmu weq ax-2 ax-mp ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq wi vd wD ax-1 ax-mp vd wD vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vb vd tmu vc vd tmu weq ax-2 ax-mp ax-mp ax-gen vd vb vc ax-microcancel ax-mp $.
$}
sdg-tan-bracket-cross $p |- ( ( ( ap g x ) * ( ap u x ) ) * ( d * e ) ) = ( ( ( ap u x ) * ( ap g x ) ) * ( d * e ) ) $= vx vg tap vx vu tap tmu vx vu tap vx vg tap tmu weq vx vg tap vx vu tap tmu vd ve tmu tmu vx vu tap vx vg tap tmu vd ve tmu tmu weq vx vg tap vx vu tap ax-mulcom vx vg tap vx vu tap tmu vx vu tap vx vg tap tmu vd ve tmu eq-mu1 ax-mp $.
${
  tanbr.flow $e |- ( ap w ( d * e ) ) = ( ( ( ap g x ) * ( ap u x ) ) + ( ( ap c x ) * ( d * e ) ) ) $.
  sdg-tan-bracket $p |- ( ap w ( d * e ) ) = ( ( ( ap u x ) * ( ap g x ) ) + ( ( ap c x ) * ( d * e ) ) ) $= vx vg tap vx vu tap tmu vx vc tap vd ve tmu tmu tpl vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl weq vd ve tmu vw tap vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl weq vx vg tap vx vu tap tmu vx vu tap vx vg tap tmu weq vx vg tap vx vu tap tmu vx vc tap vd ve tmu tmu tpl vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl weq vx vg tap vx vu tap ax-mulcom vx vg tap vx vu tap tmu vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu eq-pl1 ax-mp vd ve tmu vw tap vx vg tap vx vu tap tmu vx vc tap vd ve tmu tmu tpl weq vx vg tap vx vu tap tmu vx vc tap vd ve tmu tmu tpl vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl weq vd ve tmu vw tap vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl weq wi tanbr.flow vd ve tmu vw tap vx vg tap vx vu tap tmu vx vc tap vd ve tmu tmu tpl vx vu tap vx vg tap tmu vx vc tap vd ve tmu tmu tpl eqtri ax-mp ax-mp $.
$}
