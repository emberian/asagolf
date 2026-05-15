$( ============================================================================
   birkhoff.mm  —  the F0 axiom system for ASA.

   Layers, all as Metamath $a (primitive) statements:
     L1  propositional calculus       (ax-1 ax-2 ax-3, ax-mp)
     L2  predicate calculus + equality (ax-gen ax-4 ax-5 ax-6 ax-7, equality)
     L3  ordered field on reals  (F0: the ASA-minimal number substrate)
     L4  Birkhoff geometry primitives + the 4 postulates
   then the ASA goal.

   The geometry-layer PROOF (a $p) is emitted by the Rust elaborator and
   appended; the sound kernel (src/kernel.rs) verifies the whole file.
   "Down to ZFC" is then: this file's expanded axiom-invocation count
   (geometry layer, exact, kernel-checked) + the exact set.mm subtree count
   for whichever real-number substrate (F0..F3) replaces L3.
   ============================================================================ $)

$(  ---- constants -------------------------------------------------------- $)
$c (  )  ->  -.  wff  |-  $.                  $( logic $)
$c A. =  $.                                   $( quantifier, equality $)
$c term  0  1  +  -x  *  <  $.                $( ordered-field term layer $)
$c pt  Ln  d  m  On  Ray  Btw  Cong  Tri  $.  $( Birkhoff geometry layer $)
$c <->  e.  $.                                $( derived biconditional, membership-style $)

$(  ---- variables ------------------------------------------------------- $)
$v ph ps ch $.                 $( wff metavariables $)
$v x y z $.                    $( individual variables (points/reals) $)
$v a b c e f g  $.             $( individual variables (points)       $)
$v u v w  $.                   $( real-valued terms                   $)

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
vx $f term x $.
vy $f term y $.
vz $f term z $.
va $f term a $.
vb $f term b $.
vc $f term c $.
ve $f term e $.
vf $f term f $.
vg $f term g $.
vu $f term u $.
vv $f term v $.
vw $f term w $.

$( ===========================================================================
   L1  Propositional calculus  (Łukasiewicz / set.mm core)
   =========================================================================== $)
wn  $a wff -. ph $.
wi  $a wff ( ph -> ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
${
  mp.min $e |- ph $.
  mp.maj $e |- ( ph -> ps ) $.
  ax-mp  $a |- ps $.
$}

$( ===========================================================================
   L2  Predicate calculus + equality  (first order, over the `term` sort)
   =========================================================================== $)
wal $a wff ( A. x ph ) $.
weq $a wff x = y $.
$( ax-gen: generalization.  ax-4: instantiation/distribution.  ax-5/6/7:
   the standard predicate axioms.  eqid/eqcom/eqtr/eqsub: equality. $)
${
  gen.h $e |- ph $.
  ax-gen $a |- ( A. x ph ) $.
$}
ax-4 $a |- ( ( A. x ( ph -> ps ) ) -> ( ( A. x ph ) -> ( A. x ps ) ) ) $.
ax-5 $a |- ( ph -> ( A. x ph ) ) $.            $( x not free in ph; DV-guarded $)
$d x ph $.
ax-6 $a |- ( -. ( A. x -. ( x = y ) ) ) $.
ax-7 $a |- ( x = y -> ( x = z -> y = z ) ) $.
eqid $a |- x = x $.
eqcom $a |- ( x = y -> y = x ) $.
${
  sub.h $e |- x = y $.
  $( Leibniz substitution schema for the atomic geometry predicates. $)
  cong.s $e |- ph $.
  ax-sub $a |- ps $.        $( ps is ph with one free x replaced by y $)
$}

$( ===========================================================================
   L3  Ordered field on reals  (F0 — ASA-minimal; NO completeness)
   `term`s 0 1, ( u + v ), ( u -x v ), ( u * v ), order ( u < v ), equality.
   Birkhoff distance d(a,b) and angle measure m(a,b,c) are `term`s.
   =========================================================================== $)
t0  $a term 0 $.
t1  $a term 1 $.
tpl $a term ( u + v ) $.
tmi $a term ( u -x v ) $.
tmu $a term ( u * v ) $.
tlt $a wff ( u < v ) $.
tdist $a term d a b $.
tang  $a term m a b c $.

$(  field + order axioms (the usual ordered-field theory, F0)  $)
of-addcom  $a |- ( u + v ) = ( v + u ) $.
of-addass  $a |- ( ( u + v ) + w ) = ( u + ( v + w ) ) $.
of-add0    $a |- ( u + 0 ) = u $.
of-addinv  $a |- ( u + ( 0 -x u ) ) = 0 $.
of-mulcom  $a |- ( u * v ) = ( v * u ) $.
of-mulass  $a |- ( ( u * v ) * w ) = ( u * ( v * w ) ) $.
of-mul1    $a |- ( u * 1 ) = u $.
of-distr   $a |- ( u * ( v + w ) ) = ( ( u * v ) + ( u * w ) ) $.
of-trich   $a |- ( ( u < v -> -. ( v < u ) ) ) $.
of-lttr    $a |- ( ( u < v -> ( v < w -> u < w ) ) ) $.
of-ltadd   $a |- ( u < v -> ( u + w ) < ( v + w ) ) $.

$( ===========================================================================
   L4  Birkhoff geometry primitives + the 4 postulates.
   Predicates:  ( On a L )            a lies on line L (here lines are coded
                                      by two distinct points: ( Ln b c ) )
                ( Btw a b c )         b between a and c
                ( Ray a b c )         c on ray from a through b
                ( Cong a b c e )      segment ab congruent to ce  (d a b = d c e)
                ( Tri a b c )         a,b,c form a (non-degenerate) triangle
   =========================================================================== $)
$(  Skolemized conditional form (granularity choice: coarser postulates =>
    fewer steps; each is a single Birkhoff postulate instance, not a
    bundled lemma library). `( cp a c u )` is the ruler-constructed point
    on ray a->c at distance u from a.
    Angle convention: `m x y z` = measure of angle with vertex y.        $)
tcp  $a term ( cp a c u ) $.
won  $a wff ( On a ( Ln b c ) ) $.
wray $a wff ( Ray a b c ) $.
wtri $a wff ( Tri a b c ) $.

$( P1  Ruler / segment construction. The constructed point lies on the ray
      and is at the prescribed distance. $)
ax-ruler-ray $a |- ( Ray a c ( cp a c u ) ) $.
ax-ruler-len $a |- d a ( cp a c u ) = u $.

$( A point on ray a->c subtends, from any b, the same angle at vertex a as
   c does; and it lies on line a c. $)
ax-rayangle $a |- ( ( Ray a c x ) -> m b a x = m b a c ) $.
ax-rayline  $a |- ( ( Ray a c x ) -> ( On x ( Ln a c ) ) ) $.

$( P3  Protractor uniqueness: equal angle at vertex b (same side) puts x on
      ray b->c. $)
ax-prot-uniq $a |- ( m a b x = m a b c -> ( Ray b c x ) ) $.

$( P4  SAS: two sides and the included angle (at vertex a / e) give the
      remaining angle (at vertex b / f). Triangles ( a b c ) and ( e f g ). $)
post-sas $a |- ( d a b = d e f -> ( m b a c = m f e g ->
                 ( d a c = d e g -> m a b c = m e f g ) ) ) $.

$( P2  Incidence: with a non-degenerate triangle a b c, the lines a c and
      b c meet only at c. $)
post-incid $a |- ( ( Tri a b c ) -> ( ( On x ( Ln a c ) ) ->
                   ( ( On x ( Ln b c ) ) -> x = c ) ) ) $.

$( Distance respects equality in its second argument (Leibniz instance). $)
ax-dcong $a |- ( x = y -> d a x = d a y ) $.

$( ===========================================================================
   GOAL.  ASA, Birkhoff form.  Triangles ( a b c ) and ( e f g ).
     H1 : m b a c = m f e g      ( angle at a  =  angle at e )
     H2 : d a b   = d e f        ( included side AB = EF )
     H3 : m a b c = m e f g      ( angle at b  =  angle at f )
     HT : Tri a b c              ( non-degenerate )
   conclude  d a c = d e g       ( AC = EG ; the key congruence )
   The kernel-checked $p proof is appended by `cargo run --bin asa`.
   =========================================================================== $)
$( ASA-GOAL:  |- d a c = d e g  — proof appended and verified below $)
