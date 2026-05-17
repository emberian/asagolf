$( ============================================================================
   qzfhf_gnd.mm  —  FRONTIER B: discharge the gnd-* substrate residual.

   GOAL.  In Stage 3 (data/qzfhf.mm) the 21 ground representative-arithmetic
   facts  gnd-N* / gnd-Z* / gnd-Q*  were `$a`-ASSERTED.  STAGE3_HF §8 / the
   COST_STRUCTURE residual characterised each as a SINGLE variable-free,
   finite, non-inductive, DECIDABLE ZF computation on concrete
   hereditarily-finite sets — the last substrate projection.

   THIS file discharges that residual.  Every gnd-* arithmetic fact is here
   a kernel-verified `$p`, derived by FINITE GROUND UNFOLDING from:

     - the bare ZF set primitives:  (/) [`0ex`],  ( suc x ) [`sucexg`],
       Kuratowski <. , >. [`opex`/`zfpair2`],  the union inside `suc`
       [`uniex`],  class / quotient [ ~ ] [`axextg`];
     - the CONSERVATIVE primitive-recursive DEFINING equations of the
       von-Neumann ordinal operations  Np/Nt  (df-Np0/df-Nps/df-Nt0/df-Nts:
       n+0=n , n+suc m=suc(n+m) , n*0=0 , n*suc m=n*m+n — the recursion-
       theorem output, used at FIXED FINITE arguments only, NO induction,
       NO ω);
     - the CONSERVATIVE difference-class / ratio-class DEFINING equations of
       Zp/Zt/Zm and Qp/Qt/Qm/Qi (the standard quotient-construction
       operation definitions, eliminable by rewriting).

   WHY this is a genuine reduction (adversarially honest).  qzfhf.mm
   `$a`-asserted the GROUND OUTPUTS ( ( N0 Np N1 ) = N1 , … ).  This file
   `$a`-keeps ONLY the *defining recursion / class-operation equations* —
   conservative definitions in the precise df-* sense (each eliminable by
   rewriting; the recursion equations are exactly the ZF recursion theorem's
   output, applied at FIXED finite arguments, never quantified, never
   iterated past the single ordinal 1 = suc (/)).  Every ARITHMETIC OUTPUT
   the closed proof consumes is now PROVED, kernel re-checked.  No `om`.
   `suc` applied exactly once (df-n1).  NO induction — each proof is a
   finite eqtr/cong chain over {0,1}-built sets.  The ONLY residual kept
   `$a` is the two ORDER / DISEQUALITY literals ( Q0 ≤ Q1 , Q1 ≠ Q0 ): an
   order RELATION decision, not an equational computation — the intrinsic
   order/sign core (COST_STRUCTURE Seam-4), non-inductive, no Infinity.

   Trust / soundness.  A derivation bug can only become a kernel REJECTION,
   never a fake number (Iron Rule).  Trust root: src/kernel.rs re-checks
   every `$p`.  All proof bodies are comment-free.
   ============================================================================ $)

$c ( ) -> -. wff |- = /\ <-> \/ $.
$c e. (/) suc <. , >. [ ~ ] $.
$c N0 N1 Np Nt $.
$c Z0 Z1 Zp Zt Zm $.
$c Q0 Q1 Qp Qt Qi Qm Qle $.

$v ph ps ch $.
$v x y z a b c d $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.  vd $f term d $.

$( ---- propositional + FOL-with-equality core (as qzf.mm / qzfhf.mm) ------ $)
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

$( ---- ZF set signature: the GENUINE shared base, MINUS `om` ------------- $)
wel  $a wff ( x e. y ) $.
tep  $a term (/) $.
tsuc $a term ( suc x ) $.
top  $a term <. x , y >. $.
tcl  $a term [ x ~ y ] $.

$( ax-8/ax-9 Leibniz congruence family for every operator we rewrite under. $)
cong-suc  $a |- ( a = b -> ( suc a ) = ( suc b ) ) $.
cong-op1  $a |- ( a = b -> <. a , c >. = <. b , c >. ) $.
cong-op2  $a |- ( a = b -> <. c , a >. = <. c , b >. ) $.
cong-cl1  $a |- ( a = b -> [ a ~ c ] = [ b ~ c ] ) $.

$( ---- reusable FOL= helper: transitivity of equality (as qzf.mm) -------- $)
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

$( reusable: equality is symmetric, as a $p (eqcom packaged with ax-mp). $)
${
  eqsym.1 $e |- x = y $.
  eqsym $p |- y = x $=
      vx vy weq
      vy vx weq
      eqsym.1
      vx vy eqcom
      ax-mp
    $.
$}

$( reusable: x = z , y = z |- x = y  (rewrite RHS). $)
${
  eqtr3.1 $e |- x = z $.
  eqtr3.2 $e |- y = z $.
  eqtr3 $p |- x = y $=
      vx
      vz
      vy
      eqtr3.1
      vy vz eqtr3.2 eqsym
      eqtr
    $.
$}

$( ---- congruence-APPLICATION helpers: take a PROVED a = b, return the
   rewritten equality.  Each just packages cong-X with ax-mp so no proof
   below ever hand-orders an ax-mp.  Mandatory hyp shown. ---------------- $)
${ apsuc.1 $e |- a = b $.
   apsuc $p |- ( suc a ) = ( suc b ) $=
     va vb weq va tsuc vb tsuc weq apsuc.1 va vb cong-suc ax-mp $. $}
${ apop1.1 $e |- a = b $.
   apop1 $p |- <. a , c >. = <. b , c >. $=
     va vb weq va vc top vb vc top weq apop1.1 va vb vc cong-op1 ax-mp $. $}
${ apop2.1 $e |- a = b $.
   apop2 $p |- <. c , a >. = <. c , b >. $=
     va vb weq vc va top vc vb top weq apop2.1 va vb vc cong-op2 ax-mp $. $}
${ apcl1.1 $e |- a = b $.
   apcl1 $p |- [ a ~ c ] = [ b ~ c ] $=
     va vb weq va vc tcl vb vc tcl weq apcl1.1 va vb vc cong-cl1 ax-mp $. $}

$( ============================================================================
   LAYER N — the two HF ordinals 0 = (/) , 1 = suc (/) , and the
   CONSERVATIVE primitive-recursive defining equations of von-Neumann +/* .
   `suc` applied EXACTLY ONCE (df-n1).  Every gnd-N* OUTPUT is PROVED.
   ============================================================================ $)
tN0 $a term N0 $.  tN1 $a term N1 $.
tNp $a term ( x Np y ) $.
tNt $a term ( x Nt y ) $.
df-n0 $a |- N0 = (/) $.
df-n1 $a |- N1 = ( suc (/) ) $.

df-Np0 $a |- ( x Np N0 ) = x $.
df-Nps $a |- ( x Np ( suc y ) ) = ( suc ( x Np y ) ) $.
df-Nt0 $a |- ( x Nt N0 ) = N0 $.
df-Nts $a |- ( x Nt ( suc y ) ) = ( ( x Nt y ) Np x ) $.

cong-Np1 $a |- ( a = b -> ( a Np c ) = ( b Np c ) ) $.
cong-Np2 $a |- ( a = b -> ( c Np a ) = ( c Np b ) ) $.
cong-Nt1 $a |- ( a = b -> ( a Nt c ) = ( b Nt c ) ) $.
cong-Nt2 $a |- ( a = b -> ( c Nt a ) = ( c Nt b ) ) $.

${ apNp1.1 $e |- a = b $.
   apNp1 $p |- ( a Np c ) = ( b Np c ) $=
     va vb weq va vc tNp vb vc tNp weq apNp1.1 va vb vc cong-Np1 ax-mp $. $}
${ apNp2.1 $e |- a = b $.
   apNp2 $p |- ( c Np a ) = ( c Np b ) $=
     va vb weq vc va tNp vc vb tNp weq apNp2.1 va vb vc cong-Np2 ax-mp $. $}
${ apNt1.1 $e |- a = b $.
   apNt1 $p |- ( a Nt c ) = ( b Nt c ) $=
     va vb weq va vc tNt vb vc tNt weq apNt1.1 va vb vc cong-Nt1 ax-mp $. $}
${ apNt2.1 $e |- a = b $.
   apNt2 $p |- ( c Nt a ) = ( c Nt b ) $=
     va vb weq vc va tNt vc vb tNt weq apNt2.1 va vb vc cong-Nt2 ax-mp $. $}

$( rewrite BOTH Np arguments by PROVED equalities. $)
${ cnp.1 $e |- x = z $.  cnp.2 $e |- y = a $.
   cong-Np-pair $p |- ( x Np y ) = ( z Np a ) $=
     vx vy tNp vz vy tNp vz va tNp
     vx vz vy cnp.1 apNp1
     vy va vz cnp.2 apNp2
     eqtr $. $}

$( reduce a difference-class slot ( ( a Nt c ) Np ( b Nt d ) ) given the
   three PROVED N-facts ( a Nt c )=x , ( b Nt d )=y , ( x Np y )=z . $)
${ rs.1 $e |- ( a Nt c ) = x $.
   rs.2 $e |- ( b Nt d ) = y $.
   rs.3 $e |- ( x Np y ) = z $.
   redslot $p |- ( ( a Nt c ) Np ( b Nt d ) ) = z $=
     va vc tNt vb vd tNt tNp
     vx vy tNp
     vz
     va vc tNt vb vd tNt vx vy rs.1 rs.2 cong-Np-pair
     rs.3
     eqtr $. $}

$( N1 = ( suc N0 )  (df-n1 with (/) rewritten to N0 via eqsym df-n0). $)
n1sucn0 $p |- N1 = ( suc N0 ) $=
    tN1 tep tsuc tN0 tsuc
    df-n1
    tep tN0 tN0 tep df-n0 eqsym apsuc
    eqtr
  $.

$( ---- gnd-N* : the seven ground ℕ outputs, all PROVED ------------------- $)
gnd-N0addN0 $p |- ( N0 Np N0 ) = N0 $=
    tN0 df-Np0
  $.
gnd-N1addN0 $p |- ( N1 Np N0 ) = N1 $=
    tN1 df-Np0
  $.
gnd-N1mulN0 $p |- ( N1 Nt N0 ) = N0 $=
    tN1 df-Nt0
  $.
gnd-N0mulN0 $p |- ( N0 Nt N0 ) = N0 $=
    tN0 df-Nt0
  $.

$( ( N0 Np N1 ) = N1 :
   ( N0 Np N1 ) = ( N0 Np ( suc N0 ) )    apNp2 [n1sucn0]
                = ( suc ( N0 Np N0 ) )    df-Nps  x:=N0 y:=N0
                = ( suc N0 )              apsuc [gnd-N0addN0]
                = N1                      eqsym [n1sucn0] $)
gnd-N0addN1 $p |- ( N0 Np N1 ) = N1 $=
    tN0 tN1 tNp
    tN0 tN0 tsuc tNp
    tN1
    tN1 tN0 tsuc tN0 n1sucn0 apNp2
    tN0 tN0 tsuc tNp tN0 tN0 tNp tsuc tN1
    tN0 tN0 df-Nps
    tN0 tN0 tNp tsuc tN0 tsuc tN1
    tN0 tN0 tNp tN0 gnd-N0addN0 apsuc
    tN1 tN0 tsuc n1sucn0 eqsym
    eqtr
    eqtr
    eqtr
  $.

$( ( N0 Nt N1 ) = N0 :
   ( N0 Nt N1 ) = ( N0 Nt ( suc N0 ) )       apNt2 [n1sucn0]
                = ( ( N0 Nt N0 ) Np N0 )      df-Nts x:=N0 y:=N0
                = ( N0 Np N0 )                apNp1 [gnd-N0mulN0]
                = N0                          gnd-N0addN0 $)
gnd-N0mulN1 $p |- ( N0 Nt N1 ) = N0 $=
    tN0 tN1 tNt
    tN0 tN0 tsuc tNt
    tN0
    tN1 tN0 tsuc tN0 n1sucn0 apNt2
    tN0 tN0 tsuc tNt
    tN0 tN0 tNt tN0 tNp
    tN0
    tN0 tN0 df-Nts
    tN0 tN0 tNt tN0 tNp
    tN0 tN0 tNp
    tN0
    tN0 tN0 tNt tN0 tN0 gnd-N0mulN0 apNp1
    gnd-N0addN0
    eqtr
    eqtr
    eqtr
  $.

$( ( N1 Nt N1 ) = N1 :
   ( N1 Nt N1 ) = ( N1 Nt ( suc N0 ) )       apNt2 [n1sucn0]
                = ( ( N1 Nt N0 ) Np N1 )      df-Nts x:=N1 y:=N0
                = ( N0 Np N1 )                apNp1 [gnd-N1mulN0]
                = N1                          gnd-N0addN1 $)
gnd-N1mulN1 $p |- ( N1 Nt N1 ) = N1 $=
    tN1 tN1 tNt
    tN1 tN0 tsuc tNt
    tN1
    tN1 tN0 tsuc tN1 n1sucn0 apNt2
    tN1 tN0 tsuc tNt
    tN1 tN0 tNt tN1 tNp
    tN1
    tN1 tN0 df-Nts
    tN1 tN0 tNt tN1 tNp
    tN0 tN1 tNp
    tN1
    tN1 tN0 tNt tN0 tN1 gnd-N1mulN0 apNp1
    gnd-N0addN1
    eqtr
    eqtr
    eqtr
  $.

$( ============================================================================
   LAYER Z — named integers as difference-classes  Z = [<.a,b>.~N0] .
   df-z0/df-z1 conservative ; df-Zp/df-Zt/df-Zm conservative class-op defs.
   ============================================================================ $)
tZ0 $a term Z0 $.  tZ1 $a term Z1 $.
tZp $a term ( x Zp y ) $.
tZt $a term ( x Zt y ) $.
tZm $a term ( Zm x ) $.
df-z0 $a |- Z0 = [ <. N0 , N0 >. ~ N0 ] $.
df-z1 $a |- Z1 = [ <. N1 , N0 >. ~ N0 ] $.

df-Zp $a |- ( [ <. a , b >. ~ N0 ] Zp [ <. c , d >. ~ N0 ] )
            = [ <. ( a Np c ) , ( b Np d ) >. ~ N0 ] $.
df-Zm $a |- ( Zm [ <. a , b >. ~ N0 ] ) = [ <. b , a >. ~ N0 ] $.
df-Zt $a |- ( [ <. a , b >. ~ N0 ] Zt [ <. c , d >. ~ N0 ] )
            = [ <. ( ( a Nt c ) Np ( b Nt d ) ) ,
                  ( ( a Nt d ) Np ( b Nt c ) ) >. ~ N0 ] $.

cong-Zp1 $a |- ( a = b -> ( a Zp c ) = ( b Zp c ) ) $.
cong-Zp2 $a |- ( a = b -> ( c Zp a ) = ( c Zp b ) ) $.
cong-Zt1 $a |- ( a = b -> ( a Zt c ) = ( b Zt c ) ) $.
cong-Zt2 $a |- ( a = b -> ( c Zt a ) = ( c Zt b ) ) $.
cong-Zm  $a |- ( a = b -> ( Zm a ) = ( Zm b ) ) $.

${ apZp1.1 $e |- a = b $.
   apZp1 $p |- ( a Zp c ) = ( b Zp c ) $=
     va vb weq va vc tZp vb vc tZp weq apZp1.1 va vb vc cong-Zp1 ax-mp $. $}
${ apZp2.1 $e |- a = b $.
   apZp2 $p |- ( c Zp a ) = ( c Zp b ) $=
     va vb weq vc va tZp vc vb tZp weq apZp2.1 va vb vc cong-Zp2 ax-mp $. $}
${ apZt1.1 $e |- a = b $.
   apZt1 $p |- ( a Zt c ) = ( b Zt c ) $=
     va vb weq va vc tZt vb vc tZt weq apZt1.1 va vb vc cong-Zt1 ax-mp $. $}
${ apZt2.1 $e |- a = b $.
   apZt2 $p |- ( c Zt a ) = ( c Zt b ) $=
     va vb weq vc va tZt vc vb tZt weq apZt2.1 va vb vc cong-Zt2 ax-mp $. $}
${ apZm.1 $e |- a = b $.
   apZm $p |- ( Zm a ) = ( Zm b ) $=
     va vb weq va tZm vb tZm weq apZm.1 va vb cong-Zm ax-mp $. $}
${ czp.1 $e |- x = z $.  czp.2 $e |- y = a $.
   cong-Zp-pair $p |- ( x Zp y ) = ( z Zp a ) $=
     vx vy tZp vz vy tZp vz va tZp
     vx vz vy czp.1 apZp1
     vy va vz czp.2 apZp2
     eqtr $. $}
${ czt.1 $e |- x = z $.  czt.2 $e |- y = a $.
   cong-Zt-pair $p |- ( x Zt y ) = ( z Zt a ) $=
     vx vy tZt vz vy tZt vz va tZt
     vx vz vy czt.1 apZt1
     vy va vz czt.2 apZt2
     eqtr $. $}

$( re-fold helpers: a difference-class on N0/N1 reps collapses to Z0/Z1. $)
clz0 $p |- [ <. N0 , N0 >. ~ N0 ] = Z0 $=
    tZ0 tN0 tN0 top tN0 tcl df-z0 eqsym
  $.
clz1 $p |- [ <. N1 , N0 >. ~ N0 ] = Z1 $=
    tZ1 tN1 tN0 top tN0 tcl df-z1 eqsym
  $.

$( rewrite both pair-slots of a difference-class by PROVED equalities. $)
${ clpr.1 $e |- x = z $.  clpr.2 $e |- y = a $.
   clpr $p |- [ <. x , y >. ~ N0 ] = [ <. z , a >. ~ N0 ] $=
     vx vy top tN0 tcl
     vz vy top tN0 tcl
     vz va top tN0 tcl
     vx vy top vz vy top tN0 vx vz vy clpr.1 apop1 apcl1
     vz vy top vz va top tN0 vy va vz clpr.2 apop2 apcl1
     eqtr $. $}

$( ---- gnd-Z* : the six ground ℤ outputs, all PROVED ------------------- $)

$( ( Z0 Zp Z0 ) = Z0 . $)
gnd-Z0addZ0 $p |- ( Z0 Zp Z0 ) = Z0 $=
    tZ0 tZ0 tZp
    tN0 tN0 top tN0 tcl tN0 tN0 top tN0 tcl tZp
    tZ0
    tZ0 tZ0 tN0 tN0 top tN0 tcl tN0 tN0 top tN0 tcl df-z0 df-z0 cong-Zp-pair
    tN0 tN0 top tN0 tcl tN0 tN0 top tN0 tcl tZp
    tN0 tN0 tNp tN0 tN0 tNp top tN0 tcl
    tZ0
    tN0 tN0 tN0 tN0 df-Zp
    tN0 tN0 tNp tN0 tN0 tNp top tN0 tcl
    tN0 tN0 top tN0 tcl
    tZ0
    tN0 tN0 tNp
    tN0 tN0 tNp
    tN0 tN0
    gnd-N0addN0
    gnd-N0addN0
    clpr
    clz0
    eqtr
    eqtr
    eqtr
  $.

$( ( Z0 Zp Z1 ) = Z1 . $)
gnd-Z0addZ1 $p |- ( Z0 Zp Z1 ) = Z1 $=
    tZ0 tZ1 tZp
    tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZp
    tZ1
    tZ0 tZ1 tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl df-z0 df-z1 cong-Zp-pair
    tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZp
    tN0 tN1 tNp tN0 tN0 tNp top tN0 tcl
    tZ1
    tN0 tN0 tN1 tN0 df-Zp
    tN0 tN1 tNp tN0 tN0 tNp top tN0 tcl
    tN1 tN0 top tN0 tcl
    tZ1
    tN0 tN1 tNp
    tN0 tN0 tNp
    tN1 tN0
    gnd-N0addN1
    gnd-N0addN0
    clpr
    clz1
    eqtr
    eqtr
    eqtr
  $.

$( ( Zm Z0 ) = Z0 . $)
gnd-ZmZ0 $p |- ( Zm Z0 ) = Z0 $=
    tZ0 tZm
    tN0 tN0 top tN0 tcl tZm
    tZ0
    tZ0 tN0 tN0 top tN0 tcl df-z0 apZm
    tN0 tN0 top tN0 tcl tZm
    tN0 tN0 top tN0 tcl
    tZ0
    tN0 tN0 df-Zm
    clz0
    eqtr
    eqtr
  $.

$( ( Z1 Zt Z1 ) = Z1 .
   df-Zt slot1 ( (N1 Nt N1) Np (N0 Nt N0) ) -> ( N1 Np N0 ) -> N1
   slot2 ( (N1 Nt N0) Np (N0 Nt N1) ) -> ( N0 Np N0 ) -> N0 ; re-fold clz1. $)
gnd-Z1mulZ1 $p |- ( Z1 Zt Z1 ) = Z1 $=
    tZ1 tZ1 tZt
    tN1 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZt
    tZ1
    tZ1 tZ1 tN1 tN0 top tN0 tcl tN1 tN0 top tN0 tcl df-z1 df-z1 cong-Zt-pair
    tN1 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZt
    tN1 tN1 tNt tN0 tN0 tNt tNp tN1 tN0 tNt tN0 tN1 tNt tNp top tN0 tcl
    tZ1
    tN1 tN0 tN1 tN0 df-Zt
    tN1 tN1 tNt tN0 tN0 tNt tNp tN1 tN0 tNt tN0 tN1 tNt tNp top tN0 tcl
    tN1 tN0 top tN0 tcl
    tZ1
    tN1 tN1 tNt tN0 tN0 tNt tNp
    tN1 tN0 tNt tN0 tN1 tNt tNp
    tN1 tN0
    tN1 tN0 tN1 tN1 tN0 tN1 tN0 gnd-N1mulN1 gnd-N0mulN0 gnd-N1addN0 redslot
    tN0 tN0 tN0 tN1 tN0 tN0 tN1 gnd-N1mulN0 gnd-N0mulN1 gnd-N0addN0 redslot
    clpr
    clz1
    eqtr
    eqtr
    eqtr
  $.

$( ( Z0 Zt Z1 ) = Z0 . $)
gnd-Z0mulZ1 $p |- ( Z0 Zt Z1 ) = Z0 $=
    tZ0 tZ1 tZt
    tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZt
    tZ0
    tZ0 tZ1 tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl df-z0 df-z1 cong-Zt-pair
    tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZt
    tN0 tN1 tNt tN0 tN0 tNt tNp tN0 tN0 tNt tN0 tN1 tNt tNp top tN0 tcl
    tZ0
    tN0 tN0 tN1 tN0 df-Zt
    tN0 tN1 tNt tN0 tN0 tNt tNp tN0 tN0 tNt tN0 tN1 tNt tNp top tN0 tcl
    tN0 tN0 top tN0 tcl
    tZ0
    tN0 tN1 tNt tN0 tN0 tNt tNp
    tN0 tN0 tNt tN0 tN1 tNt tNp
    tN0 tN0
    tN0 tN0 tN0 tN0 tN0 tN1 tN0 gnd-N0mulN1 gnd-N0mulN0 gnd-N0addN0 redslot
    tN0 tN0 tN0 tN0 tN0 tN0 tN1 gnd-N0mulN0 gnd-N0mulN1 gnd-N0addN0 redslot
    clpr
    clz0
    eqtr
    eqtr
    eqtr
  $.

$( ( Z1 Zt Z0 ) = Z0 . $)
gnd-Z1mulZ0 $p |- ( Z1 Zt Z0 ) = Z0 $=
    tZ1 tZ0 tZt
    tN1 tN0 top tN0 tcl tN0 tN0 top tN0 tcl tZt
    tZ0
    tZ1 tZ0 tN1 tN0 top tN0 tcl tN0 tN0 top tN0 tcl df-z1 df-z0 cong-Zt-pair
    tN1 tN0 top tN0 tcl tN0 tN0 top tN0 tcl tZt
    tN1 tN0 tNt tN0 tN0 tNt tNp tN1 tN0 tNt tN0 tN0 tNt tNp top tN0 tcl
    tZ0
    tN1 tN0 tN0 tN0 df-Zt
    tN1 tN0 tNt tN0 tN0 tNt tNp tN1 tN0 tNt tN0 tN0 tNt tNp top tN0 tcl
    tN0 tN0 top tN0 tcl
    tZ0
    tN1 tN0 tNt tN0 tN0 tNt tNp
    tN1 tN0 tNt tN0 tN0 tNt tNp
    tN0 tN0
    tN0 tN0 tN0 tN1 tN0 tN0 tN0 gnd-N1mulN0 gnd-N0mulN0 gnd-N0addN0 redslot
    tN0 tN0 tN0 tN1 tN0 tN0 tN0 gnd-N1mulN0 gnd-N0mulN0 gnd-N0addN0 redslot
    clpr
    clz0
    eqtr
    eqtr
    eqtr
  $.

$( ============================================================================
   LAYER Q — named rationals as ratio-classes  Q = [<.a,b>.~Z0] .
   Q0 = [<.Z0,Z1>.~Z0] , Q1 = [<.Z1,Z1>.~Z0] .
   df-q0/df-q1 conservative ; df-Qp/df-Qt/df-Qm/df-Qi conservative
   class-op defs.  Order/diseq literals gnd-Q0leQ1/gnd-Q1neQ0 stay `$a`
   (the characterised order residual).
   ============================================================================ $)
tQ0 $a term Q0 $.  tQ1 $a term Q1 $.
tQp $a term ( x Qp y ) $.
tQt $a term ( x Qt y ) $.
tQi $a term ( Qi x ) $.
tQm $a term ( Qm x ) $.
wQle $a wff ( x Qle y ) $.
df-q0 $a |- Q0 = [ <. Z0 , Z1 >. ~ Z0 ] $.
df-q1 $a |- Q1 = [ <. Z1 , Z1 >. ~ Z0 ] $.

df-Qp $a |- ( [ <. a , b >. ~ Z0 ] Qp [ <. c , d >. ~ Z0 ] )
            = [ <. ( ( a Zt d ) Zp ( c Zt b ) ) , ( b Zt d ) >. ~ Z0 ] $.
df-Qt $a |- ( [ <. a , b >. ~ Z0 ] Qt [ <. c , d >. ~ Z0 ] )
            = [ <. ( a Zt c ) , ( b Zt d ) >. ~ Z0 ] $.
df-Qm $a |- ( Qm [ <. a , b >. ~ Z0 ] ) = [ <. ( Zm a ) , b >. ~ Z0 ] $.
df-Qi $a |- ( Qi [ <. a , b >. ~ Z0 ] ) = [ <. b , a >. ~ Z0 ] $.

$( the two ground ORDER / DISEQUALITY literals — an order RELATION
   decision on the concrete ratio-classes, NOT an equational class
   computation: the characterised, irreducible order residual (non-
   inductive, no Infinity).  All ARITHMETIC is PROVED below. $)
gnd-Q0leQ1  $a |- ( Q0 Qle Q1 ) $.
gnd-Q1neQ0  $a |- -. Q1 = Q0 $.

cong-Qp1 $a |- ( a = b -> ( a Qp c ) = ( b Qp c ) ) $.
cong-Qp2 $a |- ( a = b -> ( c Qp a ) = ( c Qp b ) ) $.
cong-Qt1 $a |- ( a = b -> ( a Qt c ) = ( b Qt c ) ) $.
cong-Qt2 $a |- ( a = b -> ( c Qt a ) = ( c Qt b ) ) $.
cong-Qm  $a |- ( a = b -> ( Qm a ) = ( Qm b ) ) $.
cong-Qi  $a |- ( a = b -> ( Qi a ) = ( Qi b ) ) $.

${ apQp1.1 $e |- a = b $.
   apQp1 $p |- ( a Qp c ) = ( b Qp c ) $=
     va vb weq va vc tQp vb vc tQp weq apQp1.1 va vb vc cong-Qp1 ax-mp $. $}
${ apQp2.1 $e |- a = b $.
   apQp2 $p |- ( c Qp a ) = ( c Qp b ) $=
     va vb weq vc va tQp vc vb tQp weq apQp2.1 va vb vc cong-Qp2 ax-mp $. $}
${ apQt1.1 $e |- a = b $.
   apQt1 $p |- ( a Qt c ) = ( b Qt c ) $=
     va vb weq va vc tQt vb vc tQt weq apQt1.1 va vb vc cong-Qt1 ax-mp $. $}
${ apQt2.1 $e |- a = b $.
   apQt2 $p |- ( c Qt a ) = ( c Qt b ) $=
     va vb weq vc va tQt vc vb tQt weq apQt2.1 va vb vc cong-Qt2 ax-mp $. $}
${ apQm.1 $e |- a = b $.
   apQm $p |- ( Qm a ) = ( Qm b ) $=
     va vb weq va tQm vb tQm weq apQm.1 va vb cong-Qm ax-mp $. $}
${ apQi.1 $e |- a = b $.
   apQi $p |- ( Qi a ) = ( Qi b ) $=
     va vb weq va tQi vb tQi weq apQi.1 va vb cong-Qi ax-mp $. $}
${ cqp.1 $e |- x = z $.  cqp.2 $e |- y = a $.
   cong-Qp-pair $p |- ( x Qp y ) = ( z Qp a ) $=
     vx vy tQp vz vy tQp vz va tQp
     vx vz vy cqp.1 apQp1
     vy va vz cqp.2 apQp2
     eqtr $. $}
${ cqt.1 $e |- x = z $.  cqt.2 $e |- y = a $.
   cong-Qt-pair $p |- ( x Qt y ) = ( z Qt a ) $=
     vx vy tQt vz vy tQt vz va tQt
     vx vz vy cqt.1 apQt1
     vy va vz cqt.2 apQt2
     eqtr $. $}

clq0 $p |- [ <. Z0 , Z1 >. ~ Z0 ] = Q0 $=
    tQ0 tZ0 tZ1 top tZ0 tcl df-q0 eqsym
  $.
clq1 $p |- [ <. Z1 , Z1 >. ~ Z0 ] = Q1 $=
    tQ1 tZ1 tZ1 top tZ0 tcl df-q1 eqsym
  $.

$( rewrite both ℤ pair-slots of a ratio-class by PROVED equalities. $)
${ qlpr.1 $e |- x = z $.  qlpr.2 $e |- y = a $.
   qlpr $p |- [ <. x , y >. ~ Z0 ] = [ <. z , a >. ~ Z0 ] $=
     vx vy top tZ0 tcl
     vz vy top tZ0 tcl
     vz va top tZ0 tcl
     vx vy top vz vy top tZ0 vx vz vy qlpr.1 apop1 apcl1
     vz vy top vz va top tZ0 vy va vz qlpr.2 apop2 apcl1
     eqtr $. $}

$( reduce a ℚ-addition slot ( ( a Zt d ) Zp ( c Zt b ) ) given the three
   PROVED ℤ-facts ( a Zt d )=x , ( c Zt b )=y , ( x Zp y )=z . $)
${ rq.1 $e |- ( a Zt d ) = x $.
   rq.2 $e |- ( c Zt b ) = y $.
   rq.3 $e |- ( x Zp y ) = z $.
   redqslot $p |- ( ( a Zt d ) Zp ( c Zt b ) ) = z $=
     va vd tZt vc vb tZt tZp
     vx vy tZp
     vz
     va vd tZt vc vb tZt vx vy rq.1 rq.2 cong-Zp-pair
     rq.3
     eqtr $. $}

$( ---- gnd-Q* : the six ground ℚ ARITHMETIC outputs, all PROVED -------- $)

$( ( Q0 Qp Q0 ) = Q0 .
   df-Qp slot1 ( (Z0 Zt Z1) Zp (Z0 Zt Z1) ) -> ( Z0 Zp Z0 ) -> Z0
   slot2 ( Z1 Zt Z1 ) -> Z1 ; re-fold clq0. $)
gnd-Q0addQ0 $p |- ( Q0 Qp Q0 ) = Q0 $=
    tQ0 tQ0 tQp
    tZ0 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl tQp
    tQ0
    tQ0 tQ0 tZ0 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl df-q0 df-q0 cong-Qp-pair
    tZ0 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl tQp
    tZ0 tZ1 tZt tZ0 tZ1 tZt tZp tZ1 tZ1 tZt top tZ0 tcl
    tQ0
    tZ0 tZ1 tZ0 tZ1 df-Qp
    tZ0 tZ1 tZt tZ0 tZ1 tZt tZp tZ1 tZ1 tZt top tZ0 tcl
    tZ0 tZ1 top tZ0 tcl
    tQ0
    tZ0 tZ1 tZt tZ0 tZ1 tZt tZp
    tZ1 tZ1 tZt
    tZ0 tZ1
    tZ0 tZ0 tZ0 tZ0 tZ1 tZ0 tZ1 gnd-Z0mulZ1 gnd-Z0mulZ1 gnd-Z0addZ0 redqslot
    gnd-Z1mulZ1
    qlpr
    clq0
    eqtr
    eqtr
    eqtr
  $.

$( ( Q1 Qt Q1 ) = Q1 .  df-Qt : slot1 ( Z1 Zt Z1 ) -> Z1 , slot2
   ( Z1 Zt Z1 ) -> Z1 ; re-fold clq1. $)
gnd-Q1mulQ1 $p |- ( Q1 Qt Q1 ) = Q1 $=
    tQ1 tQ1 tQt
    tZ1 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl tQt
    tQ1
    tQ1 tQ1 tZ1 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl df-q1 df-q1 cong-Qt-pair
    tZ1 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl tQt
    tZ1 tZ1 tZt tZ1 tZ1 tZt top tZ0 tcl
    tQ1
    tZ1 tZ1 tZ1 tZ1 df-Qt
    tZ1 tZ1 tZt tZ1 tZ1 tZt top tZ0 tcl
    tZ1 tZ1 top tZ0 tcl
    tQ1
    tZ1 tZ1 tZt
    tZ1 tZ1 tZt
    tZ1 tZ1
    gnd-Z1mulZ1
    gnd-Z1mulZ1
    qlpr
    clq1
    eqtr
    eqtr
    eqtr
  $.

$( ( Q0 Qp Q1 ) = Q1 .
   df-Qp slot1 ( (Z0 Zt Z1) Zp (Z1 Zt Z1) ) -> ( Z0 Zp Z1 ) -> Z1
   slot2 ( Z1 Zt Z1 ) -> Z1 ; re-fold clq1. $)
gnd-Q0addQ1 $p |- ( Q0 Qp Q1 ) = Q1 $=
    tQ0 tQ1 tQp
    tZ0 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl tQp
    tQ1
    tQ0 tQ1 tZ0 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl df-q0 df-q1 cong-Qp-pair
    tZ0 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl tQp
    tZ0 tZ1 tZt tZ1 tZ1 tZt tZp tZ1 tZ1 tZt top tZ0 tcl
    tQ1
    tZ0 tZ1 tZ1 tZ1 df-Qp
    tZ0 tZ1 tZt tZ1 tZ1 tZt tZp tZ1 tZ1 tZt top tZ0 tcl
    tZ1 tZ1 top tZ0 tcl
    tQ1
    tZ0 tZ1 tZt tZ1 tZ1 tZt tZp
    tZ1 tZ1 tZt
    tZ1 tZ1
    tZ0 tZ1 tZ1 tZ0 tZ1 tZ1 tZ1 gnd-Z0mulZ1 gnd-Z1mulZ1 gnd-Z0addZ1 redqslot
    gnd-Z1mulZ1
    qlpr
    clq1
    eqtr
    eqtr
    eqtr
  $.

$( ( Q1 Qt Q0 ) = Q0 .  df-Qt : slot1 ( Z1 Zt Z0 ) -> Z0 , slot2
   ( Z1 Zt Z1 ) -> Z1 ; re-fold clq0. $)
gnd-Q1mulQ0 $p |- ( Q1 Qt Q0 ) = Q0 $=
    tQ1 tQ0 tQt
    tZ1 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl tQt
    tQ0
    tQ1 tQ0 tZ1 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl df-q1 df-q0 cong-Qt-pair
    tZ1 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl tQt
    tZ1 tZ0 tZt tZ1 tZ1 tZt top tZ0 tcl
    tQ0
    tZ1 tZ1 tZ0 tZ1 df-Qt
    tZ1 tZ0 tZt tZ1 tZ1 tZt top tZ0 tcl
    tZ0 tZ1 top tZ0 tcl
    tQ0
    tZ1 tZ0 tZt
    tZ1 tZ1 tZt
    tZ0 tZ1
    gnd-Z1mulZ0
    gnd-Z1mulZ1
    qlpr
    clq0
    eqtr
    eqtr
    eqtr
  $.

$( ( Qm Q0 ) = Q0 .  df-Qm : [<.(Zm Z0),Z1>.~Z0] ; gnd-ZmZ0 ; clq0. $)
gnd-QmQ0 $p |- ( Qm Q0 ) = Q0 $=
    tQ0 tQm
    tZ0 tZ1 top tZ0 tcl tQm
    tQ0
    tQ0 tZ0 tZ1 top tZ0 tcl df-q0 apQm
    tZ0 tZ1 top tZ0 tcl tQm
    tZ0 tZm tZ1 top tZ0 tcl
    tQ0
    tZ0 tZ1 df-Qm
    tZ0 tZm tZ1 top tZ0 tcl
    tZ0 tZ1 top tZ0 tcl
    tQ0
    tZ0 tZm tZ1 tZ0 tZ1
    gnd-ZmZ0
    tZ1 eqid
    qlpr
    clq0
    eqtr
    eqtr
    eqtr
  $.

$( ( Qi Q1 ) = Q1 .  df-Qi swaps : [<.Z1,Z1>.~Z0] = Q1 ; clq1. $)
gnd-QiQ1 $p |- ( Qi Q1 ) = Q1 $=
    tQ1 tQi
    tZ1 tZ1 top tZ0 tcl tQi
    tQ1
    tQ1 tZ1 tZ1 top tZ0 tcl df-q1 apQi
    tZ1 tZ1 top tZ0 tcl tQi
    tZ1 tZ1 top tZ0 tcl
    tQ1
    tZ1 tZ1 df-Qi
    clq1
    eqtr
    eqtr
  $.
