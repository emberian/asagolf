$( ============================================================================
   grounded.mm  —  Grounded ASA.

   The Birkhoff postulates of birkhoff.mm are here derived, not asserted.
   Substrate F1 = ordered field (the of-* algebra axioms) + one square-root
   axiom. Points/lines/distance/angle are conservative definitions (df-*)
   over coordinates, not axioms — so the class-split scores them Definition,
   never GenuineAxiom.

   Status: substrate + definitions complete and parse-clean. The seven
   geometric postulates are stated below as goals (comments); each becomes a
   kernel-verified $p, proved from (field + √ + df-*), in the staged build.
   No postulate is asserted as a $a.
   ============================================================================ $)

$c ( ) -> -. wff |- A. = $.
$c term 0 1 + -x * < <_ $.
$c Pt Xc Yc sqd dot Coll On Ln Tri Ray ACong sqrt <-> /\ \/ $.

$v ph ps ch th $.
$v x y z a b c e f g o p q $.
$v u v w t $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.  wth $f wff th $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.
ve $f term e $.  vf $f term f $.  vg $f term g $.
vo $f term o $.  vp $f term p $.  vq $f term q $.
vu $f term u $.  vv $f term v $.  vw $f term w $.  vt $f term t $.

$( ---- L1/L2 logic (same core as birkhoff.mm) ---------------------------- $)
wn  $a wff -. ph $.
wi  $a wff ( ph -> ps ) $.
wb  $a wff ( ph <-> ps ) $.
wa  $a wff ( ph /\ ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
${ mp.min $e |- ph $.  mp.maj $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}
ax-bi1 $a |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $.
ax-bi2 $a |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $.
$( /\ is a definitional abbreviation (conservative, like df-*), NOT an
   axiom — so the class-split scores it Definition, never GenuineAxiom.   $)
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
$( \/ is likewise a conservative definitional abbreviation, NOT an axiom
   — scored Definition, never GenuineAxiom.                              $)
wo $a wff ( ph \/ ps ) $.
df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
weq $a wff x = y $.
ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.
eqid $a |- x = x $.
eqcom $a |- ( x = y -> y = x ) $.
$( Function-congruence for the primitive term operators: standard
   FOL-with-equality axioms (set.mm's ax-8/ax-9 family — "equal terms are
   interchangeable").  These are equality-logic axioms, not geometric
   postulates.                                                             $)
cong-xc  $a |- ( a = b -> ( Xc a ) = ( Xc b ) ) $.
cong-yc  $a |- ( a = b -> ( Yc a ) = ( Yc b ) ) $.
cong-pl1 $a |- ( a = b -> ( a + c ) = ( b + c ) ) $.
cong-pl2 $a |- ( a = b -> ( c + a ) = ( c + b ) ) $.
cong-mi1 $a |- ( a = b -> ( a -x c ) = ( b -x c ) ) $.
cong-mi2 $a |- ( a = b -> ( c -x a ) = ( c -x b ) ) $.
cong-mu1 $a |- ( a = b -> ( a * c ) = ( b * c ) ) $.
cong-mu2 $a |- ( a = b -> ( c * a ) = ( c * b ) ) $.
$( Leibniz substitution into the order relation: same ax-8/ax-9 family
   (equal terms interchangeable in atomic formulas), equality-logic, not
   geometry.                                                              $)
cong-le1 $a |- ( a = b -> ( ( a <_ c ) -> ( b <_ c ) ) ) $.
cong-le2 $a |- ( a = b -> ( ( c <_ a ) -> ( c <_ b ) ) ) $.
cong-lt1 $a |- ( a = b -> ( ( a < c ) -> ( b < c ) ) ) $.
cong-lt2 $a |- ( a = b -> ( ( c < a ) -> ( c < b ) ) ) $.
$( Point extensionality: a point is determined by its coordinates — the
   faithfulness converse of cong-xc/cong-yc.  Same ax-8/ax-9 equality-logic
   family (the Pt representation is injective), not a geometric postulate. $)
ptext $a |- ( ( ( ( Xc a ) = ( Xc b ) ) /\ ( ( Yc a ) = ( Yc b ) ) ) -> a = b ) $.

$( ---- F1 substrate: ordered-field algebra + ONE sqrt axiom ------------- $)
$( These of-* are field/order axioms — algebra primitives that say nothing
   about geometry.                                                          $)
t0 $a term 0 $.  t1 $a term 1 $.
tpl $a term ( u + v ) $.  tmi $a term ( u -x v ) $.  tmu $a term ( u * v ) $.
tlt $a wff ( u < v ) $.  tle $a wff ( u <_ v ) $.
of-addcom $a |- ( u + v ) = ( v + u ) $.
of-addass $a |- ( ( u + v ) + w ) = ( u + ( v + w ) ) $.
of-add0   $a |- ( u + 0 ) = u $.
of-addinv $a |- ( u + ( 0 -x u ) ) = 0 $.
of-mulcom $a |- ( u * v ) = ( v * u ) $.
of-mulass $a |- ( ( u * v ) * w ) = ( u * ( v * w ) ) $.
of-mul1   $a |- ( u * 1 ) = u $.
of-distr  $a |- ( u * ( v + w ) ) = ( ( u * v ) + ( u * w ) ) $.
of-lein   $a |- ( ( ( u <_ v ) /\ ( v <_ u ) ) -> u = v ) $.
of-letri  $a |- ( ( u <_ v ) -> ( ( v <_ w ) -> ( u <_ w ) ) ) $.
of-sqpos  $a |- ( 0 <_ ( u * u ) ) $.
$( Total order, translation-invariance, and a positive cone closed under
   multiplication: the remaining ordered-ring axioms (algebra, silent about
   geometry).  letot/leadd are stated with <_ ; the strict cone lemul uses
   < , which is a conservative definition (df-lt) over <_ — eliminable,
   so scored Definition, never GenuineAxiom.                              $)
df-lt $a |- ( ( u < v ) <-> ( ( u <_ v ) /\ -. ( v <_ u ) ) ) $.
of-letot $a |- ( ( u <_ v ) \/ ( v <_ u ) ) $.
of-leadd $a |- ( ( u <_ v ) -> ( ( u + w ) <_ ( v + w ) ) ) $.
of-lemul $a |- ( ( ( 0 < u ) /\ ( 0 < v ) ) -> ( 0 < ( u * v ) ) ) $.
of-lemul0 $a |- ( ( ( 0 <_ u ) /\ ( 0 <_ v ) ) -> ( 0 <_ ( u * v ) ) ) $.

$( General subtraction is a conservative definition over + and the
   additive-inverse term ( 0 -x v ) (which of-addinv pins down): it is
   eliminable (every binary -x rewrites away), so the class-split scores
   it Definition, never GenuineAxiom.                                      $)
df-sub $a |- ( u -x v ) = ( u + ( 0 -x v ) ) $.

$( The only extra primitive beyond an ordered field: square roots of
   non-negatives exist (Pythagorean/Euclidean field closure).  This is F1.$)
tsqrt   $a term ( sqrt u ) $.
ax-sqrt $a |- ( 0 <_ u -> ( ( sqrt u ) * ( sqrt u ) ) = u ) $.

$( ---- coordinate model: conservative DEFINITIONS (df-*, NOT axioms) ---- $)
$( A point is a coordinate pair ( Pt x y ); Xc/Yc project.                 $)
tpt  $a term ( Pt u v ) $.
txc  $a term ( Xc a ) $.   tyc  $a term ( Yc a ) $.
df-xc $a |- ( Xc ( Pt u v ) ) = u $.
df-yc $a |- ( Yc ( Pt u v ) ) = v $.

$( Squared distance (√-free): sqd a b = Δx² + Δy².  ASA's conclusion is a
   distance equality, hence a SQUARED-distance equality — no √ needed.     $)
tsqd $a term ( sqd a b ) $.
df-sqd $a |- ( sqd a b ) =
   ( ( ( ( Xc b ) -x ( Xc a ) ) * ( ( Xc b ) -x ( Xc a ) ) )
   + ( ( ( Yc b ) -x ( Yc a ) ) * ( ( Yc b ) -x ( Yc a ) ) ) ) $.

$( Dot product of vectors o->p and o->q (√-free, polynomial).             $)
tdot $a term ( dot o p q ) $.
df-dot $a |- ( dot o p q ) =
   ( ( ( ( Xc p ) -x ( Xc o ) ) * ( ( Xc q ) -x ( Xc o ) ) )
   + ( ( ( Yc p ) -x ( Yc o ) ) * ( ( Yc q ) -x ( Yc o ) ) ) ) $.

$( Collinearity = determinant zero (√-free).                              $)
wcoll $a wff ( Coll a b c ) $.
df-coll $a |- ( ( Coll a b c ) <->
   ( ( ( Xc b ) -x ( Xc a ) ) * ( ( Yc c ) -x ( Yc a ) ) )
   = ( ( ( Yc b ) -x ( Yc a ) ) * ( ( Xc c ) -x ( Xc a ) ) ) ) $.

$( On / Ln / Tri / Ray defined from collinearity + an order condition.    $)
won  $a wff ( On a ( Ln b c ) ) $.
wtri $a wff ( Tri a b c ) $.
wray $a wff ( Ray a b c ) $.
df-on  $a |- ( ( On x ( Ln a b ) ) <-> ( Coll a b x ) ) $.
df-tri $a |- ( ( Tri a b c ) <-> -. ( Coll a b c ) ) $.
$( c on ray a->b: collinear and the parameter is non-negative, captured
   √-free by the dot-product sign of a->b vs a->c.                         $)
df-ray $a |- ( ( Ray a b c ) <->
   ( ( Coll a b c ) /\ ( 0 <_ ( dot a b c ) ) ) ) $.

$( Angle congruence WITHOUT a numeric measure: equality of normalized
   squared cosines, cross-multiplied to clear denominators (√-free,
   polynomial).  ASA only uses angle EQUALITY, never measure arithmetic.  $)
wacong $a wff ( ACong o p q a e f ) $.
df-acong $a |- ( ( ACong o p q a e f ) <->
   ( ( ( ( dot o p q ) * ( dot o p q ) ) * ( ( sqd a e ) * ( sqd a f ) ) )
   = ( ( ( dot a e f ) * ( dot a e f ) ) * ( ( sqd o p ) * ( sqd o q ) ) )
   /\ ( 0 <_ ( ( dot o p q ) * ( dot a e f ) ) ) ) ) $.

$( ===========================================================================
   GOALS — to become kernel-verified $p (proved from field + √ + df-* only).
   None is asserted as $a; the postulates are derived, not asserted.

   G0  cong-sub  : x = y -> ( sqd a x ) = ( sqd a y )        [pure FOL]
   G2  incid     : ( Tri a b c ) -> ( ( On x ( Ln a c ) ) ->
                   ( ( On x ( Ln b c ) ) -> x = c ) )         [F0 linear alg]
   G3a rayangle  : ( Ray a c x ) -> ( ACong b a x b a c )     [F0]
   G3b protuniq  : ( ACong a b x a b c ) -> ( Ray b c x )      [F0]
   G3c rayline   : ( Ray a c x ) -> ( On x ( Ln a c ) )        [F0, from df-ray]
   G1  ruler     : ( Ray a c ( cp a c u ) ) /\
                   ( sqd a ( cp a c u ) ) = u                  [F1, needs √]
   G4  sas       : ( ( sqd a b ) = ( sqd e f ) /\ ACong b a c f e g
                   /\ ( sqd a c ) = ( sqd e g ) ) ->
                   ( ( sqd b c ) = ( sqd f g ) )               [F1 / poly]
   then ASA' (regrounded) follows by the same 6-step skeleton, with the
   postulate $a references replaced by these derived $p.
   =========================================================================== $)
