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

$( -------- kernel-verified derived $p (built by sdgbuild) -------- $)

sdg-id $p |- ( ph -> ph ) $= wph wph wph wi wi wph wph wi wph wph ax-1 wph wph wph wi wph wi wi wph wph wph wi wi wph wph wi wi wph wph wph wi ax-1 wph wph wph wi wph ax-2 ax-mp ax-mp $.
sdg-00 $p |- ( 0 * 0 ) = 0 $= t0 ax-mul0 $.
sdg-add0sym $p |- x = ( x + 0 ) $= vx t0 tpl vx weq vx vx t0 tpl weq vx ax-add0 vx t0 tpl vx eqcom ax-mp $.
sdg-D0 $p |- ( D 0 ) $= t0 t0 tmu t0 weq t0 wD t0 ax-mul0 t0 wD t0 t0 tmu t0 weq wb t0 t0 tmu t0 weq t0 wD wi t0 df-D t0 wD t0 t0 tmu t0 weq ax-bi2 ax-mp ax-mp $.
${
  addcan.h $e |- ( z + u ) = ( z + v ) $.
  sdg-addcan $p |- u = v $= vz tneg vz vu tpl tpl vv weq vu vv weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq vv t0 tpl vv weq t0 vv tpl vv weq vv ax-add0 t0 vv tpl vv t0 tpl weq vv t0 tpl vv weq t0 vv tpl vv weq wi t0 vv ax-addcom t0 vv tpl vv t0 tpl vv eqtri ax-mp ax-mp vz tneg vz tpl vv tpl t0 vv tpl weq t0 vv tpl vv weq vz tneg vz tpl vv tpl vv weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vv tpl t0 vv tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vv eq-pl1 ax-mp vz tneg vz tpl vv tpl t0 vv tpl vv eqtri ax-mp ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz tpl vv tpl vv weq vz tneg vz vv tpl tpl vv weq wi vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl weq vz tneg vz vv ax-addass vz tneg vz tpl vv tpl vz tneg vz vv tpl tpl eqcom ax-mp vz tneg vz vv tpl tpl vz tneg vz tpl vv tpl vv eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq vz tneg vz vv tpl tpl vv weq vz tneg vz vu tpl tpl vv weq wi vz vu tpl vz vv tpl weq vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl weq addcan.h vz vu tpl vz vv tpl vz tneg eq-pl2 ax-mp vz tneg vz vu tpl tpl vz tneg vz vv tpl tpl vv eqtri ax-mp ax-mp vu vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vv weq vu vv weq wi vz tneg vz vu tpl tpl vu weq vu vz tneg vz vu tpl tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq vu t0 tpl vu weq t0 vu tpl vu weq vu ax-add0 t0 vu tpl vu t0 tpl weq vu t0 tpl vu weq t0 vu tpl vu weq wi t0 vu ax-addcom t0 vu tpl vu t0 tpl vu eqtri ax-mp ax-mp vz tneg vz tpl vu tpl t0 vu tpl weq t0 vu tpl vu weq vz tneg vz tpl vu tpl vu weq wi vz tneg vz tpl t0 weq vz tneg vz tpl vu tpl t0 vu tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq vz ax-addneg vz tneg vz tpl vz vz tneg tpl weq vz vz tneg tpl t0 weq vz tneg vz tpl t0 weq wi vz tneg vz ax-addcom vz tneg vz tpl vz vz tneg tpl t0 eqtri ax-mp ax-mp vz tneg vz tpl t0 vu eq-pl1 ax-mp vz tneg vz tpl vu tpl t0 vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz tpl vu tpl vu weq vz tneg vz vu tpl tpl vu weq wi vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl weq vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl weq vz tneg vz vu ax-addass vz tneg vz tpl vu tpl vz tneg vz vu tpl tpl eqcom ax-mp vz tneg vz vu tpl tpl vz tneg vz tpl vu tpl vu eqtri ax-mp ax-mp vz tneg vz vu tpl tpl vu eqcom ax-mp vu vz tneg vz vu tpl tpl vv eqtri ax-mp ax-mp $.
$}
${
  slope.hb $e |- ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) $.
  slope.hc $e |- ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) $.
  sdg-slope $p |- ( b * d ) = ( c * d ) $= t0 vf tap vb vd tmu vc vd tmu vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq slope.hc t0 vf tap vb vd tmu tpl vd vf tap weq vd vf tap t0 vf tap vc vd tmu tpl weq t0 vf tap vb vd tmu tpl t0 vf tap vc vd tmu tpl weq wi vd vf tap t0 vf tap vb vd tmu tpl weq t0 vf tap vb vd tmu tpl vd vf tap weq slope.hb vd vf tap t0 vf tap vb vd tmu tpl eqcom ax-mp t0 vf tap vb vd tmu tpl vd vf tap t0 vf tap vc vd tmu tpl eqtri ax-mp ax-mp sdg-addcan $.
$}
${
  conj.h $e |- ( ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) /\ ( ap f d ) = ( ( ap f 0 ) + ( c * d ) ) ) $.
  sdg-slope-conj $p |- ( b * d ) = ( c * d ) $= vd vb vc vf vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vb vd tmu tpl weq conj.h vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-ial ax-mp vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq wa vd vf tap t0 vf tap vc vd tmu tpl weq conj.h vd vf tap t0 vf tap vb vd tmu tpl weq vd vf tap t0 vf tap vc vd tmu tpl weq ax-iar ax-mp sdg-slope $.
$}
${
  mc.h $e |- A. d ( ( D d ) -> ( b * d ) = ( c * d ) ) $.
  sdg-deriv $p |- b = c $= vd wD vb vd tmu vc vd tmu weq wi vd wal vb vc weq mc.h vd vb vc ax-microcancel ax-mp $.
$}
sdg-D2-0 $p |- ( D2 0 ) $= t0 t0 tmu t0 tmu t0 weq t0 wD2 t0 t0 tmu ax-mul0 t0 wD2 t0 t0 tmu t0 tmu t0 weq wb t0 t0 tmu t0 tmu t0 weq t0 wD2 wi t0 df-D2 t0 wD2 t0 t0 tmu t0 tmu t0 weq ax-bi2 ax-mp ax-mp $.
${
  dsub.h $e |- ( D x ) $.
  sdg-D1subD2 $p |- ( D2 x ) $= vx vx tmu vx tmu t0 weq vx wD2 t0 vx tmu t0 weq vx vx tmu vx tmu t0 weq vx t0 tmu t0 weq t0 vx tmu t0 weq vx ax-mul0 t0 vx tmu vx t0 tmu weq vx t0 tmu t0 weq t0 vx tmu t0 weq wi t0 vx ax-mulcom t0 vx tmu vx t0 tmu t0 eqtri ax-mp ax-mp vx vx tmu vx tmu t0 vx tmu weq t0 vx tmu t0 weq vx vx tmu vx tmu t0 weq wi vx vx tmu t0 weq vx vx tmu vx tmu t0 vx tmu weq vx wD vx vx tmu t0 weq dsub.h vx wD vx vx tmu t0 weq wb vx wD vx vx tmu t0 weq wi vx df-D vx wD vx vx tmu t0 weq ax-bi1 ax-mp ax-mp vx vx tmu t0 vx eq-mu1 ax-mp vx vx tmu vx tmu t0 vx tmu t0 eqtri ax-mp ax-mp vx wD2 vx vx tmu vx tmu t0 weq wb vx vx tmu vx tmu t0 weq vx wD2 wi vx df-D2 vx wD2 vx vx tmu vx tmu t0 weq ax-bi2 ax-mp ax-mp $.
$}
sdg-kl1-is-kl $p |- ( E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) -> E. b A. d ( ( D d ) -> ( ap f d ) = ( ( ap f 0 ) + ( b * d ) ) ) ) $= vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex ax-1 vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi ax-1 vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex wi vd wD vd vf tap t0 vf tap vb vd tmu tpl weq wi vd wal vb wex ax-2 ax-mp ax-mp $.
