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
$c term R D + * 0 1 inv ap deriv $.

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
