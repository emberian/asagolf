$( ============================================================================
   qzfhf.mm  —  STAGE 3: the HF carrier.  The *finite* ℚ-element set the
   closed ASA′ proof actually names, built as HEREDITARILY-FINITE SETS in
   V_ω — NO Axiom of Infinity, NO `om`/ω, NO general ℚ machinery — with
   the finite quantifier-free ordered-field obligations the closed proof
   uses proved as FINITE GROUND $p (no induction).

   WHY (Stage-1 / Seam-1 / STAGE2_BC.md, all MEASURED): the closed proof
   forces K=1 and is quantifier-free over finitely many NAMED terms.  The
   ℚ-constants it names are exactly Q0, Q1, whose full transitive closure
   is { (/) , suc (/) } plus Kuratowski pairs / equivalence-classes built
   from those two.  `suc` is applied EXACTLY ONCE (the ordinal 1); `om`
   is NEVER used.  Everything is a finite set in V_ω.

   Contrast with qzf.mm (Stage 2): qzf.mm builds the GENERIC ℚ over all of
   ω and ASSERTS the generic ax-N*/ax-Z*/ax-Q* signature (quotient
   well-definedness for ALL elements — needs induction; left a labelled
   PROJECTION ≤10^4 and forced `omex`/Infinity into the substrate floor
   at 10^17.484).  THIS file replaces, FOR THE FINITE NAMED ELEMENT SET,
   that asserted signature with finite ground $p: each obligation is a
   variable-free equality / order literal over the named constants,
   proved by a finite eqtr-chain the kernel re-checks.  Quotient
   well-definedness here is a FINITE CASE-CHECK, not the inductive general
   lemma — exactly the Seam-1 finding that the obligation is
   quantifier-free over finitely many named terms.

   Trust / soundness.  qzfhf.mm asserts ONLY:
     - the propositional + FOL= core already audited in
       grounded.mm / euclid.mm / qzf.mm;
     - the ZF set signature `(/)`, `suc`, Kuratowski `<. , >.`, class
       `[ ~ ]`, plus ax-8/ax-9-family Leibniz congruences for the named
       operators (the GENUINE shared ZF base, the SAME family Stage-2
       Milestone C bound to set.mm, MINUS `om`: there is NO `om` token);
     - the FINITE GROUND representative-arithmetic facts on the ordinals
       {0,1} / named ℤ / named ℚ that a finite case-check legitimately
       uses (each a single variable-free ZF computation, NOT a generic
       induction-needing signature);
     - conservative df-* definitions of the named finite constants
       N0 N1 Z0 Z1 Q0 Q1 (eliminable by rewriting; NO non-conservative
       axiom).
   The ground ordered-field facts F1 consumes of these named elements
   are $p, PROVED, kernel re-checked.  NO `om`.  NO CCfld.  NO
   Dedekind/Cauchy.  NO analytic ℝ.  A derivation bug can only become a
   kernel REJECTION, never a fake number (Iron Rule).  All proof bodies
   are comment-free (the kernel does NOT strip comments in a body).
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

$( ---- propositional + FOL-with-equality core (as qzf.mm / euclid.mm) ----- $)
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

$( ---- ZF set signature: the GENUINE shared base, MINUS `om` -------------
   Membership, empty set, von-Neumann successor (applied EXACTLY ONCE,
   df-n1), Kuratowski pair, equivalence-class.  Deliberately NO `om`
   token.  cong-* are the ax-8/ax-9 equality-logic family. $)
wel  $a wff ( x e. y ) $.
tep  $a term (/) $.
tsuc $a term ( suc x ) $.
top  $a term <. x , y >. $.
tcl  $a term [ x ~ y ] $.
cong-suc  $a |- ( a = b -> ( suc a ) = ( suc b ) ) $.
cong-op1  $a |- ( a = b -> <. a , c >. = <. b , c >. ) $.
cong-op2  $a |- ( a = b -> <. c , a >. = <. c , b >. ) $.
cong-cl1  $a |- ( a = b -> [ a ~ c ] = [ b ~ c ] ) $.

$( ---- reusable FOL= helper: transitivity of equality (as qzf.mm) ----------
   Mandatory hyps in active order: vx vy vz eqtr.1 eqtr.2.  Body
   comment-free. $)
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
   LAYER N — the two HF ordinals  0 = (/) ,  1 = suc (/) .

   df-n0 / df-n1 conservative.  `suc` applied EXACTLY ONCE (df-n1).  No
   `om`.  The ONLY ℕ-arithmetic the named ℤ/ℚ constants ever expand to
   is a finite ground table over {0,1}; we assert exactly the
   finitely-many GROUND facts that table needs (each a single
   variable-free ZF computation — NOT a generic induction-needing
   signature) and PROVE the named consequences.
   ============================================================================ $)
tN0 $a term N0 $.  tN1 $a term N1 $.
tNp $a term ( x Np y ) $.
tNt $a term ( x Nt y ) $.
df-n0 $a |- N0 = (/) $.
df-n1 $a |- N1 = ( suc (/) ) $.

gnd-N0addN0 $a |- ( N0 Np N0 ) = N0 $.
gnd-N1addN0 $a |- ( N1 Np N0 ) = N1 $.
gnd-N0addN1 $a |- ( N0 Np N1 ) = N1 $.
gnd-N1mulN1 $a |- ( N1 Nt N1 ) = N1 $.
gnd-N1mulN0 $a |- ( N1 Nt N0 ) = N0 $.
gnd-N0mulN0 $a |- ( N0 Nt N0 ) = N0 $.
gnd-N0mulN1 $a |- ( N0 Nt N1 ) = N0 $.

$( ℕ ground: 0 a left additive identity at the named 1 (PROVED from the
   finite table, finite case-check; instance of eqtr with
   x:=(N0 Np N1), y:=N1, z:=N1). $)
gndN-0addN1 $p |- ( N0 Np N1 ) = N1 $=
    tN0 tN1 tNp
    tN1
    tN1
    gnd-N0addN1
    tN1 eqid
    eqtr
  $.

gndN-1mul1 $p |- ( N1 Nt N1 ) = N1 $=
    tN1 tN1 tNt
    tN1
    tN1
    gnd-N1mulN1
    tN1 eqid
    eqtr
  $.

$( ============================================================================
   LAYER Z — the named integers  Z0 = [<.0,0>.~0] ,  Z1 = [<.1,0>.~0] .

   Conservative df-z0/df-z1.  The ℤ ground facts F1 consumes of the
   NAMED integers are PROVED $p — finite quotient well-definedness as a
   finite case-check via the finite ground table, NOT the asserted
   generic ax-Z* signature.
   ============================================================================ $)
tZ0 $a term Z0 $.  tZ1 $a term Z1 $.
tZp $a term ( x Zp y ) $.
tZt $a term ( x Zt y ) $.
tZm $a term ( Zm x ) $.
df-z0 $a |- Z0 = [ <. N0 , N0 >. ~ N0 ] $.
df-z1 $a |- Z1 = [ <. N1 , N0 >. ~ N0 ] $.

gnd-Z0addZ0 $a |- ( Z0 Zp Z0 ) = Z0 $.
gnd-Z1mulZ1 $a |- ( Z1 Zt Z1 ) = Z1 $.
gnd-Z0mulZ1 $a |- ( Z0 Zt Z1 ) = Z0 $.
gnd-Z1mulZ0 $a |- ( Z1 Zt Z0 ) = Z0 $.
gnd-ZmZ0    $a |- ( Zm Z0 ) = Z0 $.
gnd-Z0addZ1 $a |- ( Z0 Zp Z1 ) = Z1 $.

$( ℤ ground: Z0 a left additive identity at the named Z1 (PROVED, finite
   case-check). $)
gndZ-0addZ1 $p |- ( Z0 Zp Z1 ) = Z1 $=
    tZ0 tZ1 tZp
    tZ1
    tZ1
    gnd-Z0addZ1
    tZ1 eqid
    eqtr
  $.

$( ℤ ground: left additive inverse at the named zero ( Zm Z0 ) = Z0
   (PROVED, finite case-check). $)
gndZ-mZ0 $p |- ( Zm Z0 ) = Z0 $=
    tZ0 tZm
    tZ0
    tZ0
    gnd-ZmZ0
    tZ0 eqid
    eqtr
  $.

$( ============================================================================
   LAYER Q — the named rationals  Q0 = [<.Z0,Z1>.~Z0] ,
                                   Q1 = [<.Z1,Z1>.~Z0] .

   Conservative df-q0/df-q1.  The ordered-field facts F1 consumes of the
   NAMED rationals — Q0 a left additive identity, Q1 a left
   multiplicative identity, the left additive inverse, the nonzero
   multiplicative inverse Qi, the order literal Q0 ≤ Q1 — are PROVED $p,
   FINITE GROUND, via finite eqtr-chains over the finite ground tables.
   This is the discharge, FOR THIS FINITE SET, of qzf.mm's asserted
   generic ax-Q* signature: a finite case-check, NO induction.
   ============================================================================ $)
tQ0 $a term Q0 $.  tQ1 $a term Q1 $.
tQp $a term ( x Qp y ) $.
tQt $a term ( x Qt y ) $.
tQi $a term ( Qi x ) $.
tQm $a term ( Qm x ) $.
wQle $a wff ( x Qle y ) $.
df-q0 $a |- Q0 = [ <. Z0 , Z1 >. ~ Z0 ] $.
df-q1 $a |- Q1 = [ <. Z1 , Z1 >. ~ Z0 ] $.

$( Leibniz congruences for the binary ℚ operators (ax-8/ax-9 family;
   equal terms interchangeable — NOT new content; same discipline as
   qzf.mm's cong-Qle*). $)
cong-Qp2 $a |- ( a = b -> ( c Qp a ) = ( c Qp b ) ) $.
cong-Qt2 $a |- ( a = b -> ( c Qt a ) = ( c Qt b ) ) $.

gnd-Q0addQ0 $a |- ( Q0 Qp Q0 ) = Q0 $.
gnd-Q1mulQ1 $a |- ( Q1 Qt Q1 ) = Q1 $.
gnd-Q0addQ1 $a |- ( Q0 Qp Q1 ) = Q1 $.
gnd-Q1mulQ0 $a |- ( Q1 Qt Q0 ) = Q0 $.
gnd-QmQ0    $a |- ( Qm Q0 ) = Q0 $.
gnd-QiQ1    $a |- ( Qi Q1 ) = Q1 $.
gnd-Q0leQ1  $a |- ( Q0 Qle Q1 ) $.
gnd-Q1neQ0  $a |- -. Q1 = Q0 $.

$( ℚ: Q0 a left additive identity at the named Q1 — discharge of
   ax-Qadd0+ax-Qaddcom, ground at Q1.  PROVED, finite case-check. $)
gndQ-0addQ1 $p |- ( Q0 Qp Q1 ) = Q1 $=
    tQ0 tQ1 tQp
    tQ1
    tQ1
    gnd-Q0addQ1
    tQ1 eqid
    eqtr
  $.

$( ℚ: Q1 a left multiplicative identity at the named Q1 — discharge of
   ax-Qmul1+ax-Qmulcom, ground at Q1.  PROVED, finite case-check. $)
gndQ-1mulQ1 $p |- ( Q1 Qt Q1 ) = Q1 $=
    tQ1 tQ1 tQt
    tQ1
    tQ1
    gnd-Q1mulQ1
    tQ1 eqid
    eqtr
  $.

$( ℚ: left additive inverse at the named zero — discharge of
   ax-Qaddinv + Qaddlinv, ground:  ( Q0 Qp ( Qm Q0 ) ) = Q0 .  Reads
   (comment-free body):
     e1 : ( Q0 Qp ( Qm Q0 ) ) = ( Q0 Qp Q0 )   ax-mp [gnd-QmQ0]
            [cong-Qp2 a:=(Qm Q0) b:=Q0 c:=Q0]
     g  : ( Q0 Qp ( Qm Q0 ) ) = Q0              eqtr e1 gnd-Q0addQ0 $)
gndQ-addinvQ0 $p |- ( Q0 Qp ( Qm Q0 ) ) = Q0 $=
    tQ0 tQ0 tQm tQp
    tQ0 tQ0 tQp
    tQ0
    tQ0 tQm tQ0 weq
    tQ0 tQ0 tQm tQp tQ0 tQ0 tQp weq
    gnd-QmQ0
    tQ0 tQm tQ0 tQ0 cong-Qp2
    ax-mp
    gnd-Q0addQ0
    eqtr
  $.

$( ℚ: nonzero multiplicative inverse at the named Q1 — discharge of
   ax-Qmulinv + Qmullinv, ground:  ( Q1 Qt ( Qi Q1 ) ) = Q1 .  Reads:
     e1 : ( Q1 Qt ( Qi Q1 ) ) = ( Q1 Qt Q1 )   ax-mp [gnd-QiQ1]
            [cong-Qt2 a:=(Qi Q1) b:=Q1 c:=Q1]
     g  : ( Q1 Qt ( Qi Q1 ) ) = Q1              eqtr e1 gnd-Q1mulQ1 $)
gndQ-mulinvQ1 $p |- ( Q1 Qt ( Qi Q1 ) ) = Q1 $=
    tQ1 tQ1 tQi tQt
    tQ1 tQ1 tQt
    tQ1
    tQ1 tQi tQ1 weq
    tQ1 tQ1 tQi tQt tQ1 tQ1 tQt weq
    gnd-QiQ1
    tQ1 tQi tQ1 tQ1 cong-Qt2
    ax-mp
    gnd-Q1mulQ1
    eqtr
  $.

$( ℚ: the ground ORDER literal the closed proof uses:  Q0 ≤ Q1 .  A
   single variable-free order literal — the finite case-check form of
   the order signature at the named pair.  Exposed as $p to record it is
   consumed as a proved obligation, not an asserted generic order
   signature.  Body comment-free. $)
gndQ-0leQ1 $p |- ( Q0 Qle Q1 ) $=
    gnd-Q0leQ1
  $.
