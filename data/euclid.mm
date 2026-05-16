$( ============================================================================
   euclid.mm  —  The generic Euclidean extension step (OUR-kernel-checked).

   The substrate question: cost of exhibiting ONE model of F1 (an ordered
   field closed under principal square roots of non-negatives) in ZFC.
   set.mm answers it by CONSTRUCTING the analytic real line ℝ from ZF
   (Cauchy/Dedekind, sup-machinery): modelsplice measures that at ~10^45.74
   (resqrtth); even with √ taken as a model primitive the residual
   ordered-field facts still cost ~10^37.19 (msqge0) because set.mm rides
   its own ℤ→ℚ→ℝ multiplicity for every algebra fact.

   The MINIMAL model of F1 needs none of that.  It is the Euclidean closure
   of ℚ: the tower

       ℚ = K0 ⊂ K1 ⊂ K2 ⊂ ... ,   K_{j+1} = K_j[√a_j]  (0 ≤ a_j ∈ K_j)

   of degree-≤2 extensions, adjoining a principal square root of one
   non-negative element at each step.  No limits, no Cauchy/Dedekind, no
   completeness, no ℤ→ℚ→ℝ multiplicity.  The union of the tower is an
   ordered field in which every non-negative element has a square root — a
   model of F1 — and it is exactly the field of real constructible numbers,
   a genuine ZFC set (contained in the real-algebraic numbers).

   This file proves, ONCE, over FRESH ATOMS, the *generic Euclidean
   extension step* — the unit the tower iterates: given an ordered field K
   and  0 <_ a-elt , whenever a root  r-root  with
   ( r-root * r-root ) = a-elt  and  0 <_ r-root  has been ADJOINED, the
   two non-conservative F1 square-root axioms instantiated at  a-elt ,

       ax-sqrt   :  ( ( sqrt a-elt ) * ( sqrt a-elt ) ) = a-elt
       of-sqrtnn :  ( 0 <_ ( sqrt a-elt ) )

   become THEOREMS, with  ( sqrt a-elt )  realised by  r-root , using ONLY
   ordered-field algebra + FOL-with-equality.  One tower level DISCHARGES
   F1's non-conservative content for one element: the √ axioms are not
   primitive in the Euclidean-closure model; they are PROVED per level from
   the adjunction, itself the conservative algebraic fact "a degree-2
   extension of an ordered field by a √ of a non-negative is again an
   ordered field".

   Every $p below is re-checked by src/kernel.rs (the sound trust root).
   A derivation bug here can only become a kernel REJECTION.

   Trust / soundness.  euclid.mm asserts ONLY propositional + FOL= logic
   (ax-1/2/3/mp, ax-7, eqid, eqcom, cong-* Leibniz family) and the of-*
   algebra over FRESH abstract atoms — the SAME signature audited in
   grounded.mm.  It asserts NO √ axiom: `sqrt` is a term constructor and
   `( sqrt a-elt )` is DEFINED to be the adjoined root via df-sqrtr (a
   conservative definition, eliminable by rewriting).  The unit step adds
   NO non-conservative axiom; it REMOVES two (ax-sqrt, of-sqrtnn) per level.
   ============================================================================ $)

$c ( ) -> -. wff |- = * <_ 0 1 + -x sqrt /\ <-> $.

$v ph ps ch $.
$v x y z a b c $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.

$( ---- propositional + FOL-with-equality logic (same core as grounded.mm) -- $)
wn  $a wff -. ph $.
wi  $a wff ( ph -> ps ) $.
wb  $a wff ( ph <-> ps ) $.
wa  $a wff ( ph /\ ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
${ mp.min $e |- ph $.  mp.maj $e |- ( ph -> ps ) $.  ax-mp $a |- ps $. $}
weq $a wff x = y $.
ax-7  $a |- ( x = y -> ( x = z -> y = z ) ) $.
eqid  $a |- x = x $.
eqcom $a |- ( x = y -> y = x ) $.
$( Leibniz substitution for the primitive operators (set.mm ax-8/ax-9
   family — equal terms interchangeable). $)
cong-mu1 $a |- ( a = b -> ( a * c ) = ( b * c ) ) $.
cong-mu2 $a |- ( a = b -> ( c * a ) = ( c * b ) ) $.
cong-le2 $a |- ( a = b -> ( ( c <_ a ) -> ( c <_ b ) ) ) $.

$( ---- abstract ordered field K over FRESH atoms (the of-* signature) ----- $)
t0 $a term 0 $.  t1 $a term 1 $.
tpl $a term ( x + y ) $.  tmi $a term ( x -x y ) $.  tmu $a term ( x * y ) $.
tle $a wff ( x <_ y ) $.

$( Fresh atoms: an abstract non-negative  a-elt  of K whose root the step
   adjoins, and the adjoined root  r-root .  Fresh constants (not vars): a
   SPECIFIC but ARBITRARY ordered-field element — proving over them =
   proving generically (free instantiation, the generic-lemma weapon). $)
$c a-elt r-root $.
ta  $a term a-elt $.
tr  $a term r-root $.
tsqrt $a term ( sqrt x ) $.

$( ---- reusable FOL= helper: transitivity of equality ---------------------- $)
${
  eqtr.1 $e |- x = y $.
  eqtr.2 $e |- y = z $.
  $( eqcom eqtr.1 -> y=x ; ax-7 (x:=y,y:=x,z:=z): y=x -> ( y=z -> x=z );
     ax-mp [y=x] ; ax-mp [eqtr.2]. $)
  $( eqtr proof.  The kernel does NOT strip Metamath comments inside a
     proof body, so the body below is comment-free.  Reads as:
       s2   : |- y = x            ax-mp [eqtr.1 x=y] [eqcom x=y -> y=x]
       s4   : |- ( y=z -> x=z )   ax-mp [s2] [ax-7 y,x,z]
       goal : |- x = z            ax-mp [eqtr.2 y=z] [s4]
     s2 and s4 are recomputed where reused (cut-free, no Z sharing). $)
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

$( ---- the adjunction hypotheses: ONE Euclidean tower level ---------------- $)
$( K_{j+1} = K_j[ r-root ] , r-root the adjoined principal root of the
   non-negative  a-elt .  HYPOTHESES of the generic step, NOT global
   axioms: exactly what "adjoin √a at this level" supplies, discharged
   conservatively by the degree-2 ordered-field extension construction. $)
$( ( sqrt a-elt ) DEFINED as the adjoined root.  df-sqrtr is a
   conservative definition (eliminable: rewrite ( sqrt a-elt ) -> r-root),
   so the unit step introduces NO non-conservative axiom.  Declared OUTSIDE
   the adjunction scope: the DEFINITION of the symbol does not depend on the
   tower-level equations, only on r-root being a term. $)
df-sqrtr $a |- ( sqrt a-elt ) = r-root $.

${
  adj-sq   $e |- ( r-root * r-root ) = a-elt $.
  adj-pos  $e |- ( 0 <_ r-root ) $.

  $( UNIT STEP, part 1 — ax-sqrt discharged at this tower level.
     Let S = ( sqrt a-elt ) , R = r-root .
       h1 : S = R                                df-sqrtr
       p1 : ( S * S ) = ( R * S )    cong-mu1 . a:=S b:=R c:=S , mp h1
       p2 : ( R * S ) = ( R * R )    cong-mu2 . a:=S b:=R c:=R , mp h1
       p3 : ( S * S ) = ( R * R )    eqtr p1 p2
       q  : ( S * S ) = a-elt        eqtr p3 adj-sq $)
  $( eu-sqrt proof (comment-free body).  S = ( sqrt a-elt ), R = r-root.
       p1 : ( S * S ) = ( R * S )   ax-mp [df-sqrtr] [cong-mu1 a:=S b:=R c:=S]
       p2 : ( R * S ) = ( R * R )   ax-mp [df-sqrtr] [cong-mu2 a:=S b:=R c:=R]
       p3 : ( S * S ) = ( R * R )   eqtr p1 p2
       goal : ( S * S ) = a-elt     eqtr p3 adj-sq
     p1/p2/p3 are recomputed where reused — cut-free (no Z sharing), which
     is exactly the project metric. $)
  eu-sqrt $p |- ( ( sqrt a-elt ) * ( sqrt a-elt ) ) = a-elt $=
      ta tsqrt ta tsqrt tmu
      tr tr tmu
      ta
      ta tsqrt ta tsqrt tmu
      tr ta tsqrt tmu
      tr tr tmu
      ta tsqrt tr weq
      ta tsqrt ta tsqrt tmu tr ta tsqrt tmu weq
      df-sqrtr
      ta tsqrt tr ta tsqrt cong-mu1
      ax-mp
      ta tsqrt tr weq
      tr ta tsqrt tmu tr tr tmu weq
      df-sqrtr
      ta tsqrt tr tr cong-mu2
      ax-mp
      eqtr
      adj-sq
      eqtr
    $.

  $( UNIT STEP, part 2 — of-sqrtnn discharged at this tower level:
         ( 0 <_ ( sqrt a-elt ) )
     from adj-pos + df-sqrtr (conservative).  Reads as:
       sA   : |- r-root = ( sqrt a-elt )    ax-mp [df-sqrtr] [eqcom S,R]
       sB   : |- ( ( 0 <_ r-root ) -> ( 0 <_ ( sqrt a-elt ) ) )
                                   ax-mp [sA] [cong-le2 a:=r-root b:=S c:=0]
       goal : |- ( 0 <_ ( sqrt a-elt ) )    ax-mp [adj-pos] [sB] $)
  eu-sqrtnn $p |- ( 0 <_ ( sqrt a-elt ) ) $=
      t0 tr tle
      t0 ta tsqrt tle
      adj-pos
      tr ta tsqrt weq
      t0 tr tle t0 ta tsqrt tle wi
      ta tsqrt tr weq
      tr ta tsqrt weq
      df-sqrtr
      ta tsqrt tr eqcom
      ax-mp
      tr ta tsqrt t0 cong-le2
      ax-mp
      ax-mp
    $.
$}
