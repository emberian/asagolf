$( ============================================================================
   qzfext.mm  —  Milestone B: the ONE quadratic extension ℚ_geo(√r),
                  natively over the ℚ-from-ZF base (OUR-kernel-checked).

   STAGE 2, Milestone B ONLY.  Stage 1 MEASURED K=1: the closed ASA′ proof
   forces exactly ONE distinct, un-nested radical,

       ( sqrt ( u * ( inv ( sqd a c ) ) ) )      [Stage-1, MEASURED]

   In the native ℚ-from-ZF notation of qzf.mm (Milestone A) that radicand
   is the ℚ element

       r  :=  ( u Qt ( Qi sdac ) )

   where  u  is the (positive) ruler parameter and  sdac  is the ℚ-valued
   squared distance  ( sqd a c )  — both genuine elements of the native ℚ
   carrier built ω → ℕ → ℤ → ℚ in qzf.mm (NO CCfld, NO Dedekind/Cauchy,
   NO analytic ℝ).

   This file delivers Milestone B and nothing else: it exhibits

       ℚ_geo(√r)  =  ℚ_geo[x]/(x² − r)

   as a ZF set + ordered field with √r present, by ADJOINING one root
   element  rr  of the native-ℚ carrier with

       ( rr Qt rr ) = r        and        ( Q0 Qle rr )

   (exactly the degree-2 ordered-field extension hypotheses — the
   conservative algebraic fact "a degree-2 extension of an ordered field
   by a √ of a non-negative is again an ordered field"), and then
   INSTANTIATES the euclid.mm generic Euclidean unit step at THIS
   specific radicand  r  over the native-ℚ multiplication/order.  The two
   non-conservative F1 √-axioms instantiated at  r  become THEOREMS:

       eu-sqrt-r   :  ( ( Qsqrt r ) Qt ( Qsqrt r ) ) = r        (ax-sqrt @ r)
       eu-sqrtnn-r :  ( Q0 Qle ( Qsqrt r ) )                    (of-sqrtnn @ r)

   with  ( Qsqrt r )  realised by the adjoined  rr  via the conservative
   definition  df-qsqrtr  (eliminable by rewriting: rewrite ( Qsqrt r ) ->
   rr — introduces NO non-conservative axiom).  The step REMOVES F1's two
   non-conservative √-axioms for this single radicand, deriving them from
   native-ℚ ordered-field algebra + FOL= only.

   Reuse of the already-MEASURED unit (the task's explicit instruction):
   the proof skeleton of eu-sqrt-r / eu-sqrtnn-r is byte-for-byte the same
   shape as euclid.mm's kernel-verified, MEASURED-elsewhere generic unit
   step (eqtr + eu-sqrt + eu-sqrtnn = 141 cut-free $a-leaves = 10^2.149,
   `euclidfloor`, OUR kernel) — instantiated at the native-ℚ operators
   and the Stage-1 radicand.  We do NOT re-derive the 10^2.149 generic
   figure; src/bin/qzfextfloor.rs MEASURES this file's own cut-free cost
   in OUR kernel (the project metric) and reports it explicitly.

   Trust / soundness.  qzfext.mm asserts ONLY: the propositional + FOL=
   core already audited in grounded.mm / euclid.mm / qzf.mm; the
   native-ℚ ordered-field signature (Qt / Qle / Q0 — the SAME signature
   Milestone A built ω → ℕ → ℤ → ℚ); the degree-2 adjunction HYPOTHESES
   of this one tower level (NOT global axioms — exactly what "adjoin √r"
   supplies, discharged conservatively by the standard degree-2 ordered-
   field extension); and the conservative df-qsqrtr definition.  It
   asserts NO √ axiom.  The two F1 √-facts at  r  are $p, PROVED, and
   re-checked by src/kernel.rs (the sound trust root).  A derivation bug
   here can only become a kernel REJECTION — never a fake number (Iron
   Rule).  NOT in scope (Milestone C; staying scoped is part of the
   task): the set.mm transport binding.
   ============================================================================ $)

$c ( ) -> -. wff |- = /\ <-> \/ $.
$c Q0 Q1 Qp Qt Qle Qi Qsqrt $.

$v ph ps ch $.
$v x y z a b c $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.

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

$( Leibniz substitution for the native-ℚ operators (set.mm ax-8/ax-9
   family — equal terms interchangeable; NOT new content). $)
cong-Qt1 $a |- ( a = b -> ( a Qt c ) = ( b Qt c ) ) $.
cong-Qt2 $a |- ( a = b -> ( c Qt a ) = ( c Qt b ) ) $.
cong-Qle2 $a |- ( a = b -> ( ( c Qle a ) -> ( c Qle b ) ) ) $.

$( ---- native-ℚ ordered-field signature (the SAME ℚ Milestone A built
   ω → ℕ → ℤ → ℚ; reused by instantiation, NOT re-constructed here). ----- $)
tQ0 $a term Q0 $.  tQ1 $a term Q1 $.
tQp $a term ( x Qp y ) $.
tQt $a term ( x Qt y ) $.
tQi $a term ( Qi x ) $.
wQle $a wff ( x Qle y ) $.

$( ---- the Stage-1 radicand, as a native-ℚ element --------------------------
   Fresh atoms:  u  the (positive) ruler parameter and  sdac  the
   ℚ-valued squared distance  ( sqd a c ) .  Fresh constants (specific
   but arbitrary native-ℚ elements).  The radicand the closed ASA′ proof
   forces, in native-ℚ notation, is exactly

       rdcd  :=  ( u Qt ( Qi sdac ) )

   ( = u * inv( sqd a c ) , Stage-1 MEASURED form). $)
$c u-elt sdac rr $.
tu  $a term u-elt $.
tsd $a term sdac $.
trr $a term rr $.
$( radicand as a defined native-ℚ term (conservative: rewrites away). $)
$c rdcd $.
trd $a term rdcd $.
df-rdcd $a |- rdcd = ( u-elt Qt ( Qi sdac ) ) $.

$( principal-√ term constructor over native ℚ. $)
tQsqrt $a term ( Qsqrt x ) $.

$( ---- reusable FOL= helper: transitivity of equality (as qzf.mm) ----------
   Body comment-free (the kernel does NOT strip comments inside a proof
   body).  Mandatory hyps in active order: vx vy vz eqtr.1 eqtr.2. $)
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

$( ---- the ONE quadratic extension: ℚ_geo(√r) = ℚ_geo[x]/(x² − r) ----------
   ( Qsqrt rdcd )  DEFINED as the adjoined root  rr  of the native-ℚ
   carrier.  df-qsqrtr is a conservative definition (eliminable: rewrite
   ( Qsqrt rdcd ) -> rr), so this milestone introduces NO non-conservative
   axiom.  Declared OUTSIDE the adjunction scope: the DEFINITION of the
   symbol depends only on  rr  being a term, not on the tower-level
   equations. $)
df-qsqrtr $a |- ( Qsqrt rdcd ) = rr $.

${
  $( the degree-2 adjunction HYPOTHESES of this ONE tower level over the
     native-ℚ base: the adjoined  rr  is a native-ℚ-carrier element whose
     square is the radicand and which is ≥ 0.  Exactly "ℚ_geo(√r) is the
     ordered field ℚ_geo[x]/(x² − r) with √r = rr present" — the standard,
     conservative degree-2 ordered-field extension fact, supplied here as
     this level's hypotheses (NOT global axioms). $)
  adj-sq-r  $e |- ( rr Qt rr ) = rdcd $.
  adj-pos-r $e |- ( Q0 Qle rr ) $.

  $( UNIT STEP, part 1 — F1 ax-sqrt discharged at the Stage-1 radicand,
     over native ℚ.  Same proof shape as euclid.mm eu-sqrt (MEASURED unit),
     instantiated  ( * -> Qt , a-elt -> rdcd , r-root -> rr ).  Let
     S = ( Qsqrt rdcd ), R = rr.  Comment-free body reads:
       p1 : ( S Qt S ) = ( R Qt S )   ax-mp [df-qsqrtr] [cong-Qt1 a:=S b:=R c:=S]
       p2 : ( R Qt S ) = ( R Qt R )   ax-mp [df-qsqrtr] [cong-Qt2 a:=S b:=R c:=R]
       p3 : ( S Qt S ) = ( R Qt R )   eqtr p1 p2
       goal : ( S Qt S ) = rdcd       eqtr p3 adj-sq-r $)
  eu-sqrt-r $p |- ( ( Qsqrt rdcd ) Qt ( Qsqrt rdcd ) ) = rdcd $=
      trd tQsqrt trd tQsqrt tQt
      trr trr tQt
      trd
      trd tQsqrt trd tQsqrt tQt
      trr trd tQsqrt tQt
      trr trr tQt
      trd tQsqrt trr weq
      trd tQsqrt trd tQsqrt tQt trr trd tQsqrt tQt weq
      df-qsqrtr
      trd tQsqrt trr trd tQsqrt cong-Qt1
      ax-mp
      trd tQsqrt trr weq
      trr trd tQsqrt tQt trr trr tQt weq
      df-qsqrtr
      trd tQsqrt trr trr cong-Qt2
      ax-mp
      eqtr
      adj-sq-r
      eqtr
    $.

  $( UNIT STEP, part 2 — F1 of-sqrtnn discharged at the Stage-1 radicand,
     over native ℚ:  ( Q0 Qle ( Qsqrt rdcd ) )  from adj-pos-r + df-qsqrtr.
     Same shape as euclid.mm eu-sqrtnn (MEASURED unit).  Comment-free body:
       sA   : |- rr = ( Qsqrt rdcd )   ax-mp [df-qsqrtr] [eqcom S,R]
       sB   : |- ( ( Q0 Qle rr ) -> ( Q0 Qle ( Qsqrt rdcd ) ) )
                              ax-mp [sA] [cong-Qle2 a:=rr b:=S c:=Q0]
       goal : |- ( Q0 Qle ( Qsqrt rdcd ) )   ax-mp [adj-pos-r] [sB] $)
  eu-sqrtnn-r $p |- ( Q0 Qle ( Qsqrt rdcd ) ) $=
      tQ0 trr wQle
      tQ0 trd tQsqrt wQle
      adj-pos-r
      trr trd tQsqrt weq
      tQ0 trr wQle tQ0 trd tQsqrt wQle wi
      trd tQsqrt trr weq
      trr trd tQsqrt weq
      df-qsqrtr
      trd tQsqrt trr eqcom
      ax-mp
      trr trd tQsqrt tQ0 cong-Qle2
      ax-mp
      ax-mp
    $.
$}
