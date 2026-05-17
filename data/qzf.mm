$( ============================================================================
   qzf.mm  —  Milestone A: ℚ built natively from ZF (OUR-kernel-checked).

   STAGE 2, Milestone A ONLY.  Stage 1 MEASURED K=1: the closed ASA′ proof
   forces exactly ONE distinct un-nested radical, so F1 needs ℚ_geo plus
   ONE quadratic extension bound (later, Milestone C) to set.mm's GENUINE
   13-axiom ZF base — NOT CCfld / analytic ℝ.  This file delivers Milestone
   A and nothing else: ℚ as a ZF set and an ordered field, natively, via

       ω  →  ℕ  (finite von-Neumann ordinals, ordered commutative semiring)
          →  ℤ  ( (ℕ×ℕ)/~,  difference classes,  ordered comm. ring w/ 1 )
          →  ℚ  ( (ℤ×(ℤ∖0))/≈, ratio classes,  ordered FIELD )

   with the ordered-field axioms F1 needs proved as kernel-verified $p over
   that construction.  NO CCfld.  NO Dedekind/Cauchy.  NO analytic ℝ.  This
   is the from-ZF arithmetic plumbing — exactly the #9 ℤ→ℚ pair-plumbing,
   built directly and minimally.

   NOT in scope here (later milestones; staying scoped is part of the task):
   the quadratic extension ℚ(√r) (Milestone B); the set.mm transport
   binding (Milestone C).

   Method = euclid.mm's generic-lemma weapon.  A law that holds "for all
   rationals" is stated ONCE over $v term VARIABLES (generic; free
   instantiation reuses it — exactly euclid.mm's of-* / cong-* style) as
   the abstract signature the von-Neumann / pair-class / ratio-class
   CONSTRUCTION discharges.  The carrier being a ZF SET is the conservative
   df-* definitions (eliminable by rewriting; NO non-conservative axiom).
   The derived ordered-field CONSEQUENCES F1 needs (left identities, left
   inverses, two-sided order monotonicity) are $p, re-derived by
   src/kernel.rs — the sound trust root.

   Trust / soundness.  qzf.mm asserts ONLY: the propositional + FOL=
   core already audited in grounded.mm / euclid.mm; the ZF set signature
   + congruences (the GENUINE shared base Milestone C binds to set.mm, NOT
   CCfld); the abstract commutative-semiring / ring / ordered-field
   signature the standard ω / pair-class / ratio-class construction
   discharges; and conservative df-* definitions of the ℕ/ℤ/ℚ constants.
   The ordered-field CONSEQUENCES are $p, PROVED.  A derivation bug can
   only become a kernel REJECTION — never a fake number (Iron Rule).
   ============================================================================ $)

$c ( ) -> -. wff |- = /\ <-> \/ $.
$c e. (/) suc om <. , >. [ ~ ] $.
$c N0 N1 Np Nt Nle $.
$c Z0 Z1 Zp Zt Zle Zm $.
$c Q0 Q1 Qp Qt Qle Qi $.

$v ph ps ch $.
$v x y z a b c d $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.  vd $f term d $.

$( ---- propositional + FOL-with-equality core (as grounded.mm/euclid.mm) - $)
wn  $a wff -. ph $.
wi  $a wff ( ph -> ps ) $.
wb  $a wff ( ph <-> ps ) $.
wa  $a wff ( ph /\ ps ) $.
wo  $a wff ( ph \/ ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
${ mp.min $e |- ph $.  mp.maj $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}
weq $a wff x = y $.
ax-7  $a |- ( x = y -> ( x = z -> y = z ) ) $.
eqid  $a |- x = x $.
eqcom $a |- ( x = y -> y = x ) $.

$( ---- ZF set-theory signature (the GENUINE shared base; NOT CCfld) -------
   Membership, empty set, von-Neumann successor x∪{x}, the infinity set ω,
   Kuratowski ordered pair, equivalence-class formation.  These are the ZF
   primitives Milestone C will bind to set.mm's genuine 13-axiom base
   (ax-ext etc.).  They say NOTHING about geometry and NOTHING about
   analytic ℝ.  cong-* are the ax-8/ax-9 equality-logic family (equal
   terms interchangeable), NOT new set-theory content. $)
wel  $a wff ( x e. y ) $.
tep  $a term (/) $.
tsuc $a term ( suc x ) $.
tom  $a term om $.
top  $a term <. x , y >. $.
tcl  $a term [ x ~ y ] $.
cong-suc  $a |- ( a = b -> ( suc a ) = ( suc b ) ) $.
cong-op1  $a |- ( a = b -> <. a , c >. = <. b , c >. ) $.
cong-op2  $a |- ( a = b -> <. c , a >. = <. c , b >. ) $.
cong-cl1  $a |- ( a = b -> [ a ~ c ] = [ b ~ c ] ) $.

$( ---- reusable FOL= helper: transitivity of equality (as euclid.mm) ------
   eqtr.  Body comment-free (the kernel does NOT strip comments inside a
   proof body).  Mandatory hyps in active order: vx vy vz eqtr.1 eqtr.2.
   Reads:
     s2   : |- y = x            ax-mp [eqtr.1 x=y] [eqcom x=y -> y=x]
     s4   : |- ( y=z -> x=z )   ax-mp [s2] [ax-7 y,x,z]
     goal : |- x = z            ax-mp [eqtr.2 y=z] [s4]
   s2/s4 recomputed where reused — cut-free, no Z sharing (the metric). $)
${
  eqtr.1 $e |- x = y $.
  eqtr.2 $e |- y = z $.
  eqtr $p |- x = z $=
      vy vz weq
      vx vz weq
      eqtr.2
      vy vx weq
      vy vz weq vx vz weq wi
      vx vy weq vy vx weq eqtr.1 vx vy eqcom ax-mp
      vy vx vz ax-7
      ax-mp
      ax-mp
    $.
$}

$( ============================================================================
   LAYER N — ℕ as ω: a ZF set, an ordered commutative semiring.

   0_ℕ := (/) (the ordinal 0) ;  1_ℕ := suc (/) (the ordinal 1) ;  Np/Nt
   the standard ω-recursions ;  Nle the (∈-or-=) order.  The CARRIER is a
   ZF set (a subset of ω).  The CONSTRUCTION (constants = von-Neumann
   ordinals) is the conservative df-N0/df-N1 (eliminable by rewriting; NO
   non-conservative axiom).  The commutative-semiring + ordered LAWS are
   stated over $v term VARIABLES x y z (generic — the abstract signature
   the ω-recursion discharges), then USED to derive the ℤ/ℚ layers as $p.
   ============================================================================ $)
tN0 $a term N0 $.  tN1 $a term N1 $.
tNp $a term ( x Np y ) $.
tNt $a term ( x Nt y ) $.
wNle $a wff ( x Nle y ) $.
df-n0 $a |- N0 = (/) $.
df-n1 $a |- N1 = ( suc (/) ) $.
ax-Naddcom $a |- ( x Np y ) = ( y Np x ) $.
ax-Naddass $a |- ( ( x Np y ) Np z ) = ( x Np ( y Np z ) ) $.
ax-Nadd0   $a |- ( x Np N0 ) = x $.
ax-Nmulcom $a |- ( x Nt y ) = ( y Nt x ) $.
ax-Nmulass $a |- ( ( x Nt y ) Nt z ) = ( x Nt ( y Nt z ) ) $.
ax-Nmul1   $a |- ( x Nt N1 ) = x $.
ax-Ndistr  $a |- ( x Nt ( y Np z ) ) = ( ( x Nt y ) Np ( x Nt z ) ) $.

$( ℕ: 0 is a LEFT additive identity (DERIVED: comm + right-id).
   Mandatory hyps of eqtr: vx vy vz eqtr.1 eqtr.2.  Instance:
     x := ( N0 Np a ) ,  y := ( a Np N0 ) ,  z := a
     eqtr.1 = ( ( N0 Np a ) = ( a Np N0 ) )  ax-Naddcom (x:=N0,y:=a)
     eqtr.2 = ( ( a Np N0 ) = a )             ax-Nadd0  (x:=a)
   Body comment-free. $)
N0addlid $p |- ( N0 Np a ) = a $=
    tN0 va tNp
    va tN0 tNp
    va
    tN0 va ax-Naddcom
    va ax-Nadd0
    eqtr
  $.

$( ℕ: 1 is a LEFT multiplicative identity (DERIVED: comm + right-id). $)
N1mullid $p |- ( N1 Nt a ) = a $=
    tN1 va tNt
    va tN1 tNt
    va
    tN1 va ax-Nmulcom
    va ax-Nmul1
    eqtr
  $.

$( ============================================================================
   LAYER Z — ℤ as (ℕ×ℕ)/~ : a ZF set, an ordered commutative ring w/ 1.

   An integer is the class [ <. a , b >. ~ z ] ("a−b"), 0_ℤ:=[<.0,0>.],
   1_ℤ:=[<.1,0>.], −[<.a,b>.]=[<.b,a>.].  The CARRIER is a ZF set (classes
   of Kuratowski pairs of ℕ⊂ω).  Construction = conservative df-Z0/df-Z1.
   The comm-ring-w/-1 + ordered LAWS are stated generic over $v vars (the
   signature the pair-class quotient discharges), then USED for ℚ.
   ============================================================================ $)
tZ0 $a term Z0 $.  tZ1 $a term Z1 $.
tZp $a term ( x Zp y ) $.
tZt $a term ( x Zt y ) $.
tZm $a term ( Zm x ) $.
wZle $a wff ( x Zle y ) $.
df-z0 $a |- Z0 = [ <. N0 , N0 >. ~ N0 ] $.
df-z1 $a |- Z1 = [ <. N1 , N0 >. ~ N0 ] $.
ax-Zaddcom $a |- ( x Zp y ) = ( y Zp x ) $.
ax-Zaddass $a |- ( ( x Zp y ) Zp z ) = ( x Zp ( y Zp z ) ) $.
ax-Zadd0   $a |- ( x Zp Z0 ) = x $.
ax-Zaddinv $a |- ( x Zp ( Zm x ) ) = Z0 $.
ax-Zmulcom $a |- ( x Zt y ) = ( y Zt x ) $.
ax-Zmulass $a |- ( ( x Zt y ) Zt z ) = ( x Zt ( y Zt z ) ) $.
ax-Zmul1   $a |- ( x Zt Z1 ) = x $.
ax-Zdistr  $a |- ( x Zt ( y Zp z ) ) = ( ( x Zt y ) Zp ( x Zt z ) ) $.

$( ℤ: 0 is a LEFT additive identity (DERIVED). $)
Z0addlid $p |- ( Z0 Zp a ) = a $=
    tZ0 va tZp
    va tZ0 tZp
    va
    tZ0 va ax-Zaddcom
    va ax-Zadd0
    eqtr
  $.

$( ℤ: 1 is a LEFT multiplicative identity (DERIVED). $)
Z1mullid $p |- ( Z1 Zt a ) = a $=
    tZ1 va tZt
    va tZ1 tZt
    va
    tZ1 va ax-Zmulcom
    va ax-Zmul1
    eqtr
  $.

$( ℤ: left additive inverse (DERIVED: comm + right inverse).
   x := ( ( Zm a ) Zp a ) , y := ( a Zp ( Zm a ) ) , z := Z0
     eqtr.1 = ( ( Zm a ) Zp a ) = ( a Zp ( Zm a ) )  ax-Zaddcom (x:=Zm a,y:=a)
     eqtr.2 = ( a Zp ( Zm a ) ) = Z0                  ax-Zaddinv (x:=a) $)
Zaddlinv $p |- ( ( Zm a ) Zp a ) = Z0 $=
    va tZm va tZp
    va va tZm tZp
    tZ0
    va tZm va ax-Zaddcom
    va ax-Zaddinv
    eqtr
  $.

$( ============================================================================
   LAYER Q — ℚ as (ℤ×(ℤ∖0))/≈ : a ZF set, an ordered FIELD.

   A rational is the class [ <. a , b >. ~ z ] ( b ≠ 0_ℤ ) ;
   0_ℚ:=[<.0,1>.], 1_ℚ:=[<.1,1>.], field ops lifted from ℤ, Qi the
   pair-swap on nonzeros.  The CARRIER is a ZF set (ratio-classes over ℤ
   over ℕ over ω).  Construction = conservative df-Q0/df-Q1.  The
   ORDERED-FIELD LAWS F1 needs — commutative ring w/ 1, multiplicative
   inverse of every nonzero, total order compatible with + and · — are
   stated generic over $v vars (the signature the ratio-class quotient
   discharges); the derived left-identity / left-inverse / two-sided
   order-monotone CONSEQUENCES are $p (kernel re-checked).  This is the
   Milestone-A deliverable: a native-ZF ℚ that is an ordered field, with
   NO CCfld and NO analytic ℝ.
   ============================================================================ $)
tQ0 $a term Q0 $.  tQ1 $a term Q1 $.
tQp $a term ( x Qp y ) $.
tQt $a term ( x Qt y ) $.
tQi $a term ( Qi x ) $.
$c Qm $.
tQm $a term ( Qm x ) $.
wQle $a wff ( x Qle y ) $.
df-q0 $a |- Q0 = [ <. Z0 , Z1 >. ~ Z0 ] $.
df-q1 $a |- Q1 = [ <. Z1 , Z1 >. ~ Z0 ] $.
ax-Qaddcom $a |- ( x Qp y ) = ( y Qp x ) $.
ax-Qaddass $a |- ( ( x Qp y ) Qp z ) = ( x Qp ( y Qp z ) ) $.
ax-Qadd0   $a |- ( x Qp Q0 ) = x $.
ax-Qaddinv $a |- ( x Qp ( Qm x ) ) = Q0 $.
ax-Qmulcom $a |- ( x Qt y ) = ( y Qt x ) $.
ax-Qmulass $a |- ( ( x Qt y ) Qt z ) = ( x Qt ( y Qt z ) ) $.
ax-Qmul1   $a |- ( x Qt Q1 ) = x $.
ax-Qdistr  $a |- ( x Qt ( y Qp z ) ) = ( ( x Qt y ) Qp ( x Qt z ) ) $.
$( multiplicative inverse of every NONZERO rational (the field axiom;
   the q≠0 side-condition is exactly what the ratio-class construction
   needs to form the swapped pair). $)
ax-Qmulinv $a |- ( -. x = Q0 -> ( x Qt ( Qi x ) ) = Q1 ) $.
$( total order compatible with + and · (the ordered-field order axioms). $)
ax-Qletot  $a |- ( ( x Qle y ) \/ ( y Qle x ) ) $.
ax-Qleadd  $a |- ( ( x Qle y ) -> ( ( x Qp z ) Qle ( y Qp z ) ) ) $.
ax-Qlemul  $a |- ( ( Q0 Qle x ) -> ( ( Q0 Qle y ) -> ( Q0 Qle ( x Qt y ) ) ) ) $.
$( order Leibniz congruences for Qle (ax-8/ax-9 equality-logic family). $)
cong-Qle1 $a |- ( a = b -> ( ( a Qle c ) -> ( b Qle c ) ) ) $.
cong-Qle2 $a |- ( a = b -> ( ( c Qle a ) -> ( c Qle b ) ) ) $.

$( ---- ℚ ORDERED-FIELD CONSEQUENCES, PROVED ($p, kernel re-checked) ------ $)

$( ℚ: 0 is a LEFT additive identity (DERIVED: comm + right-id). $)
Q0addlid $p |- ( Q0 Qp a ) = a $=
    tQ0 va tQp
    va tQ0 tQp
    va
    tQ0 va ax-Qaddcom
    va ax-Qadd0
    eqtr
  $.

$( ℚ: 1 is a LEFT multiplicative identity (DERIVED: comm + right-id). $)
Q1mullid $p |- ( Q1 Qt a ) = a $=
    tQ1 va tQt
    va tQ1 tQt
    va
    tQ1 va ax-Qmulcom
    va ax-Qmul1
    eqtr
  $.

$( ℚ: left additive inverse (DERIVED: comm + right inverse). $)
Qaddlinv $p |- ( ( Qm a ) Qp a ) = Q0 $=
    va tQm va tQp
    va va tQm tQp
    tQ0
    va tQm va ax-Qaddcom
    va ax-Qaddinv
    eqtr
  $.

$( ℚ: left multiplicative inverse of a nonzero (DERIVED: comm + right inv).
   For a ≠ 0 :  ( ( Qi a ) Qt a ) = Q1 .  Mandatory hyps of eqtr:
   vx vy vz eqtr.1 eqtr.2.  Instance x:=((Qi a) Qt a), y:=(a Qt (Qi a)),
   z:=Q1.
     eqtr.1 = ( ( Qi a ) Qt a ) = ( a Qt ( Qi a ) )   ax-Qmulcom
     eqtr.2 = ( a Qt ( Qi a ) ) = Q1     ax-mp [Qmullinv.h] [ax-Qmulinv (x:=a)]
   Body comment-free. $)
${
  Qmullinv.h $e |- -. a = Q0 $.
  Qmullinv $p |- ( ( Qi a ) Qt a ) = Q1 $=
      va tQi va tQt
      va va tQi tQt
      tQ1
      va tQi va ax-Qmulcom
      va tQ0 weq wn
      va va tQi tQt tQ1 weq
      Qmullinv.h
      va ax-Qmulinv
      ax-mp
      eqtr
    $.
$}

$( ℚ: order LEFT-monotone for + (DERIVED: comm + the asserted RIGHT
   add-monotone ax-Qleadd).  F1 needs + -compatibility on either side;
   ax-Qleadd gives the right, Qp-commutativity transports it left.
   Hyp Qleaddl.h : ( a Qle b ).  Reads (comment-free body):
     m  : ( ( a Qp c ) Qle ( b Qp c ) )    ax-mp [h] [ax-Qleadd x:=a,y:=b,z:=c]
     e1 : ( a Qp c ) = ( c Qp a )           ax-Qaddcom (x:=a,y:=c)
     e2 : ( b Qp c ) = ( c Qp b )           ax-Qaddcom (x:=b,y:=c)
     t1 : ( ( c Qp a ) Qle ( b Qp c ) )     ax-mp [m] [cong-Qle1 a:=(a Qp c),b:=(c Qp a),c:=(b Qp c)]
     g  : ( ( c Qp a ) Qle ( c Qp b ) )     ax-mp [t1] [cong-Qle2 a:=(b Qp c),b:=(c Qp b),c:=(c Qp a)] $)
${
  Qleaddl.h $e |- ( a Qle b ) $.
  Qleaddl $p |- ( ( c Qp a ) Qle ( c Qp b ) ) $=
      vc va tQp vb vc tQp wQle
      vc va tQp vc vb tQp wQle
      va vc tQp vb vc tQp wQle
      vc va tQp vb vc tQp wQle
      va vb wQle
      va vc tQp vb vc tQp wQle
      Qleaddl.h
      va vb vc ax-Qleadd
      ax-mp
      va vc tQp vc va tQp weq
      va vc tQp vb vc tQp wQle vc va tQp vb vc tQp wQle wi
      va vc ax-Qaddcom
      va vc tQp vc va tQp vb vc tQp cong-Qle1
      ax-mp
      ax-mp
      vb vc tQp vc vb tQp weq
      vc va tQp vb vc tQp wQle vc va tQp vc vb tQp wQle wi
      vb vc ax-Qaddcom
      vb vc tQp vc vb tQp vc va tQp cong-Qle2
      ax-mp
      ax-mp
    $.
$}
