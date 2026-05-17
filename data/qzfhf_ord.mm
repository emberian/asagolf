$( ============================================================================
   qzfhf_ord.mm  —  CLOSURE of the two ORDER literals (the FINAL substrate
   residual).

   CONTEXT.  Frontier B (data/qzfhf_gnd.mm, FRONTIER_B_GND.md) discharged ALL
   19 ground ARITHMETIC facts to kernel-verified `$p` from bare ZF + the
   conservative recursion / class-operation defining equations.  After that,
   the ENTIRE remaining substrate residual was EXACTLY TWO literals, still
   `$a`:

       gnd-Q0leQ1 :  ( Q0 Qle Q1 )      ( 0/1  ≤  1/1 )
       gnd-Q1neQ0 :  -. Q1 = Q0          ( 1/1  ≠  0/1 )

   on the concrete hereditarily-finite ratio-classes
       Q0 = [ <. Z0 , Z1 >. ~ Z0 ] ,  Q1 = [ <. Z1 , Z1 >. ~ Z0 ]
       Z0 = [ <. N0 , N0 >. ~ N0 ] ,  Z1 = [ <. N1 , N0 >. ~ N0 ]
       N0 = (/) ,                      N1 = ( suc (/) ) .

   THIS file DISCHARGES BOTH, in OUR kernel, as kernel-verified `$p`.

   ========================  ADVERSARIAL-HONESTY NOTICE  ======================
   ||                                                                        ||
   || This discharge CONSUMES THE ORDER PREDICATE.  It is NOT a smuggle and  ||
   || NOT an algebra trick.  The ratio-class order Qle is here DEFINED       ||
   || (conservative df-Qle1 / df-Zle1 / df-Nle, each eliminable by           ||
   || rewriting) and relayed down to TWO primitive bare-ZF von-Neumann       ||
   || ORDER / FOUNDATION facts kept `$a`:                                    ||
   ||                                                                        ||
   ||   el-0-suc : ( (/) e. ( suc (/) ) )                                    ||
   ||       — the von-Neumann reflection of the ORDER axiom of-letot         ||
   ||         (totality / positivity of the order) of data/grounded.mm.      ||
   ||   ne-suc-0 : -. ( suc (/) ) = (/)                                      ||
   ||       — ordinal irreflexivity / Foundation: the successor of a set     ||
   ||         is never that set; the empty set is not its own successor.     ||
   ||                                                                        ||
   || `el-0-suc` is EXACTLY the irreducible essential ingredient Frontier C  ||
   || (FRONTIER_C_ORDERCORE.md) PROVED cannot be a ring identity (no set of  ||
   || ring identities of any degree expresses the order-core; `sqcong`       ||
   || fails in ℤ/8, its kernel x²=0→x=0 in ℤ/4; logically essential,         ||
   || localised to of-letot).  `ne-suc-0` is the Foundation/ordinal-order    ||
   || companion (the von-Neumann order is irreflexive — 0 < 1, 1 ≠ 0).       ||
   ||                                                                        ||
   || These TWO are the ONLY `$a` order/foundation primitives kept.  EVERY   ||
   || other step is propositional logic, FOL=, the Leibniz equality-logic    ||
   || congruences (ax-8/ax-9 family — exactly grounded.mm's cong-le*         ||
   || discipline; equal terms interchangeable in atomic formulas, NO order   ||
   || content), or the conservative df-Nle / df-Zle1 / df-Qle1 / df-Zne1 /   ||
   || df-Qne1 order/injectivity definitions — each eliminable by rewriting,  ||
   || NO induction, NO `om`, `suc` applied exactly once.  ALL kernel         ||
   || re-checked.                                                            ||
   ||                                                                        ||
   || df-Zle1 / df-Qle1 (order, biconditional) and df-Zne1 / df-Qne1         ||
   || (constructor first-coordinate injectivity, contrapositive form) are    ||
   || the canonical-denominator specialisations valid because every named    ||
   || ground constant has offset N0 and denominator Z1 (Frontier D: K=1).    ||
   || They carry NO order content: the order content is ENTIRELY in          ||
   || el-0-suc / ne-suc-0.                                                   ||
   ||                                                                        ||
   || => The loop is CLOSED.  Removing order as a projection still costs     ||
   || PRECISELY the one thing Frontier C proved intrinsic: the order         ||
   || predicate (von-Neumann ∈ / ordinal irreflexivity, reflecting           ||
   || of-letot).  NOT hidden, NOT merged: flagged here and in                ||
   || src/bin/qzfhfordfloor.rs.                                              ||
   ||                                                                        ||
   ============================================================================

   Trust / soundness.  A derivation bug can only become a kernel REJECTION,
   never a fake number (Iron Rule).  Trust root: src/kernel.rs re-checks
   every `$p`.  All proof bodies are comment-free.  New file; consumes
   nothing else; data/qzfhf*.mm / data/grounded.mm read-only.
   ============================================================================ $)

$c ( ) -> -. wff |- = /\ \/ <-> $.
$c e. (/) suc <. , >. [ ~ ] $.
$c N0 N1 Nle $.
$c Z0 Z1 Zle $.
$c Q0 Q1 Qle $.

$v ph ps ch $.
$v x y z a b c d $.
wph $f wff ph $.  wps $f wff ps $.  wch $f wff ch $.
vx $f term x $.  vy $f term y $.  vz $f term z $.
va $f term a $.  vb $f term b $.  vc $f term c $.  vd $f term d $.

$( ---- propositional + FOL-with-equality core (as qzfhf_gnd.mm) ----------- $)
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

$( ---- ZF set signature (as qzfhf_gnd.mm) -------------------------------- $)
wel  $a wff ( x e. y ) $.
tep  $a term (/) $.
tsuc $a term ( suc x ) $.
top  $a term <. x , y >. $.
tcl  $a term [ x ~ y ] $.

$( Leibniz substitution (ax-8/ax-9 family — equal terms interchangeable in
   atomic formulas; equality-logic, the SAME discipline as grounded.mm's
   cong-le1/cong-le2; NO order content):
     - into e.  : cong-el2
     - into  =  : cong-eq2  (RHS rewrite of an equality goal)
     - into -.= : cong-ne1 / cong-ne2  (rewrite either slot of a proved
                  disequality -. ( · = · ) ).  These are the contrapositive
                  Leibniz forms (equal terms interchangeable inside the
                  atomic `-. ( = )`), still pure equality logic. $)
cong-el1  $a |- ( a = b -> ( ( a e. c ) -> ( b e. c ) ) ) $.
cong-el2  $a |- ( a = b -> ( ( c e. a ) -> ( c e. b ) ) ) $.
cong-ne1  $a |- ( a = b -> ( -. a = c -> -. b = c ) ) $.
cong-ne2  $a |- ( a = b -> ( -. c = a -> -. c = b ) ) $.

$( ---- reusable FOL= : transitivity / symmetry (as qzfhf_gnd.mm) --------- $)
${
  eqtr.1 $e |- x = y $.
  eqtr.2 $e |- y = z $.
  eqtr $p |- x = z $=
      vy vz weq vx vz weq eqtr.2 vy vx weq
      vy vz weq vx vz weq wi
      vx vy weq vy vx weq eqtr.1 vx vy eqcom ax-mp
      vy vx vz ax-7 ax-mp ax-mp $.
$}
${
  eqsym.1 $e |- x = y $.
  eqsym $p |- y = x $=
      vx vy weq vy vx weq eqsym.1 vx vy eqcom ax-mp $.
$}

$( ---- propositional helpers (all derived from ax-1/ax-2/ax-3) ----------- $)
${ a1i.1 $e |- ph $.
   a1i $p |- ( ps -> ph ) $=
     wph wps wph wi a1i.1 wph wps ax-1 ax-mp $. $}
${ a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.
   a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
     wph wps wch wi wi
     wph wps wi wph wch wi wi
     a2i.1
     wph wps wch ax-2
     ax-mp $. $}
${ syl.1 $e |- ( ph -> ps ) $.
   syl.2 $e |- ( ps -> ch ) $.
   syl $p |- ( ph -> ch ) $=
     wph wps wi wph wch wi syl.1
     wph wps wch
     wps wch wi wph wps wch wi wi syl.2 wps wch wi wph ax-1 ax-mp
     a2i
     ax-mp $. $}
${ mpid.1 $e |- ps $.
   mpid.2 $e |- ( ph -> ( ps -> ch ) ) $.
   mpid $p |- ( ph -> ch ) $=
     wph wps wi wph wch wi
     wps wph mpid.1 a1i
     wph wps wch mpid.2 a2i
     ax-mp $. $}
ax-bi2 $a |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $.
${ bi2i.1 $e |- ( ph <-> ps ) $.
   bi2i.2 $e |- ps $.
   bi2i $p |- ph $=
     wps wph bi2i.2
     wph wps wb wps wph wi bi2i.1 wph wps ax-bi2 ax-mp
     ax-mp $. $}
ax-orl $a |- ( ph -> ( ph \/ ps ) ) $.
${ orli.1 $e |- ph $.
   orli $p |- ( ph \/ ps ) $=
     wph wph wps wo orli.1 wph wps ax-orl ax-mp $. $}

$( ---- equality / membership application helpers ------------------------- $)
$( elcong1i : |- a = b , |- ( a e. c )  =>  |- ( b e. c ). $)
${ elcong1i.1 $e |- a = b $.
   elcong1i.2 $e |- ( a e. c ) $.
   elcong1i $p |- ( b e. c ) $=
     va vc wel vb vc wel elcong1i.2
     va vb weq va vc wel vb vc wel wi elcong1i.1 va vb vc cong-el1 ax-mp
     ax-mp $. $}
$( elcong2i : |- a = b , |- ( c e. a )  =>  |- ( c e. b ). $)
${ elcong2i.1 $e |- a = b $.
   elcong2i.2 $e |- ( c e. a ) $.
   elcong2i $p |- ( c e. b ) $=
     vc va wel vc vb wel elcong2i.2
     va vb weq vc va wel vc vb wel wi elcong2i.1 va vb vc cong-el2 ax-mp
     ax-mp $. $}
$( necong1i : |- a = b , |- -. a = c  =>  |- -. b = c. $)
${ necong1i.1 $e |- a = b $.
   necong1i.2 $e |- -. a = c $.
   necong1i $p |- -. b = c $=
     va vc weq wn vb vc weq wn necong1i.2
     va vb weq va vc weq wn vb vc weq wn wi necong1i.1
     va vb vc cong-ne1 ax-mp
     ax-mp $. $}
$( necong2i : |- a = b , |- -. c = a  =>  |- -. c = b. $)
${ necong2i.1 $e |- a = b $.
   necong2i.2 $e |- -. c = a $.
   necong2i $p |- -. c = b $=
     vc va weq wn vc vb weq wn necong2i.2
     va vb weq vc va weq wn vc vb weq wn wi necong2i.1
     va vb vc cong-ne2 ax-mp
     ax-mp $. $}

$( ============================================================================
   LAYER N — 0 = (/) , 1 = suc (/) , the ORDINAL-MEMBERSHIP order Nle.
   df-Nle conservative biconditional (eliminable).  ONLY el-0-suc /
   ne-suc-0 kept primitive (the consumed ORDER / FOUNDATION core).
   ============================================================================ $)
tN0 $a term N0 $.  tN1 $a term N1 $.
tNle $a wff ( x Nle y ) $.
df-n0 $a |- N0 = (/) $.
df-n1 $a |- N1 = ( suc (/) ) $.

$( ---- THE primitive ORDER / FOUNDATION facts (the consumed core) -------- $)
el-0-suc $a |- ( (/) e. ( suc (/) ) ) $.
ne-suc-0 $a |- -. ( suc (/) ) = (/) $.

df-Nle $a |- ( ( x Nle y ) <-> ( ( x e. y ) \/ x = y ) ) $.

$( N0 e. N1  (rewrite el-0-suc back through df-n1 then df-n0). $)
n0eln1 $p |- ( N0 e. N1 ) $=
    tep tN0 tN1
    tN0 tep df-n0 eqsym
    tep tsuc tN1 tep
    tN1 tep tsuc df-n1 eqsym
    el-0-suc
    elcong2i
    elcong1i
  $.

$( N0 Nle N1  via df-Nle  <-  ( N0 e. N1 \/ N0 = N1 ). $)
gnd-N0leN1 $p |- ( N0 Nle N1 ) $=
    tN0 tN1 tNle
    tN0 tN1 wel tN0 tN1 weq wo
    tN0 tN1 df-Nle
    tN0 tN1 wel tN0 tN1 weq n0eln1 orli
    bi2i
  $.

$( -. N1 = N0 :  ne-suc-0 ( -. (suc(/)) = (/) ) , rewrite (suc(/)) -> N1
   [necong1i, (suc(/))=N1] then (/) -> N0 [necong2i, (/)=N0]. $)
gnd-N1neN0 $p |- -. N1 = N0 $=
    tep tN0 tN1
    tN0 tep df-n0 eqsym
    tep tsuc tN1 tep
    tN1 tep tsuc df-n1 eqsym
    ne-suc-0
    necong1i
    necong2i
  $.

$( ============================================================================
   LAYER Z — named integers as difference-classes  Z = [<.a,N0>.~N0] .
   df-z0/df-z1 conservative.  df-Zle1 (order, biconditional) / df-Zne1
   (constructor first-coordinate injectivity, contrapositive form) : the
   canonical (offset-N0) specialisations — conservative (eliminable), NO
   order content (the order relays to Nle, ultimately el-0-suc; the
   disequality relays to ne-suc-0).
   ============================================================================ $)
tZ0 $a term Z0 $.  tZ1 $a term Z1 $.
tZle $a wff ( x Zle y ) $.
df-z0 $a |- Z0 = [ <. N0 , N0 >. ~ N0 ] $.
df-z1 $a |- Z1 = [ <. N1 , N0 >. ~ N0 ] $.

$( Leibniz congruence for Zle (ax-8/ax-9 family; equality-logic, NOT order
   content — same as grounded.mm cong-le1/cong-le2). $)
cong-Zle1 $a |- ( a = b -> ( ( a Zle c ) -> ( b Zle c ) ) ) $.
cong-Zle2 $a |- ( a = b -> ( ( c Zle a ) -> ( c Zle b ) ) ) $.

$( conservative canonical-form order / injectivity criteria at offset N0. $)
df-Zle1 $a |- ( ( [ <. a , N0 >. ~ N0 ] Zle [ <. c , N0 >. ~ N0 ] )
               <-> ( a Nle c ) ) $.
df-Zne1 $a |- ( -. a = c
               -> -. [ <. a , N0 >. ~ N0 ] = [ <. c , N0 >. ~ N0 ] ) $.

${ apZle1.1 $e |- a = b $.
   apZle1i.2 $e |- ( a Zle c ) $.
   apZle1i $p |- ( b Zle c ) $=
     va vc tZle vb vc tZle apZle1i.2
     va vb weq va vc tZle vb vc tZle wi apZle1.1 va vb vc cong-Zle1 ax-mp
     ax-mp $. $}
${ apZle2.1 $e |- a = b $.
   apZle2i.2 $e |- ( c Zle a ) $.
   apZle2i $p |- ( c Zle b ) $=
     vc va tZle vc vb tZle apZle2i.2
     va vb weq vc va tZle vc vb tZle wi apZle2.1 va vb vc cong-Zle2 ax-mp
     ax-mp $. $}

$( Z0 Zle Z1 :  df-Zle1 reduces [<.N0,N0>.~N0] Zle [<.N1,N0>.~N0]
   to ( N0 Nle N1 ) [gnd-N0leN1] ; re-fold the classes to Z0/Z1. $)
gnd-Z0leZ1 $p |- ( Z0 Zle Z1 ) $=
    tN1 tN0 top tN0 tcl
    tZ1
    tZ0
    tZ1 tN1 tN0 top tN0 tcl df-z1 eqsym
    tN0 tN0 top tN0 tcl
    tZ0
    tN1 tN0 top tN0 tcl
    tZ0 tN0 tN0 top tN0 tcl df-z0 eqsym
    tN0 tN0 top tN0 tcl tN1 tN0 top tN0 tcl tZle
    tN0 tN1 tNle
    tN0 tN1 df-Zle1
    gnd-N0leN1
    bi2i
    apZle1i
    apZle2i
  $.

$( -. Z1 = Z0 :  df-Zne1 ( a:=N1 c:=N0 ) on gnd-N1neN0 gives
   -. [<.N1,N0>.~N0] = [<.N0,N0>.~N0] ; re-fold to Z1/Z0. $)
gnd-Z1neZ0 $p |- -. Z1 = Z0 $=
    tN0 tN0 top tN0 tcl
    tZ0
    tZ1
    tZ0 tN0 tN0 top tN0 tcl df-z0 eqsym
    tN1 tN0 top tN0 tcl
    tZ1
    tN0 tN0 top tN0 tcl
    tZ1 tN1 tN0 top tN0 tcl df-z1 eqsym
    tN1 tN0 weq wn
    tN1 tN0 top tN0 tcl tN0 tN0 top tN0 tcl weq wn
    gnd-N1neN0
    tN1 tN0 df-Zne1
    ax-mp
    necong1i
    necong2i
  $.

$( ============================================================================
   LAYER Q — named rationals as ratio-classes  Q = [<.a,Z1>.~Z0] .
   df-q0/df-q1 conservative.  df-Qle1 / df-Qne1 : canonical (denominator-Z1)
   specialisations — conservative, NO order content (order relays to Zle ->
   Nle -> el-0-suc ; disequality relays to ne-suc-0).
   ============================================================================ $)
tQ0 $a term Q0 $.  tQ1 $a term Q1 $.
tQle $a wff ( x Qle y ) $.
df-q0 $a |- Q0 = [ <. Z0 , Z1 >. ~ Z0 ] $.
df-q1 $a |- Q1 = [ <. Z1 , Z1 >. ~ Z0 ] $.

cong-Qle1 $a |- ( a = b -> ( ( a Qle c ) -> ( b Qle c ) ) ) $.
cong-Qle2 $a |- ( a = b -> ( ( c Qle a ) -> ( c Qle b ) ) ) $.

df-Qle1 $a |- ( ( [ <. a , Z1 >. ~ Z0 ] Qle [ <. c , Z1 >. ~ Z0 ] )
               <-> ( a Zle c ) ) $.
df-Qne1 $a |- ( -. a = c
               -> -. [ <. a , Z1 >. ~ Z0 ] = [ <. c , Z1 >. ~ Z0 ] ) $.

${ apQle1.1 $e |- a = b $.
   apQle1i.2 $e |- ( a Qle c ) $.
   apQle1i $p |- ( b Qle c ) $=
     va vc tQle vb vc tQle apQle1i.2
     va vb weq va vc tQle vb vc tQle wi apQle1.1 va vb vc cong-Qle1 ax-mp
     ax-mp $. $}
${ apQle2.1 $e |- a = b $.
   apQle2i.2 $e |- ( c Qle a ) $.
   apQle2i $p |- ( c Qle b ) $=
     vc va tQle vc vb tQle apQle2i.2
     va vb weq vc va tQle vc vb tQle wi apQle2.1 va vb vc cong-Qle2 ax-mp
     ax-mp $. $}

$( ====================  LITERAL 1 : gnd-Q0leQ1  =========================== $)
$( ( Q0 Qle Q1 ) :  df-Qle1 reduces [<.Z0,Z1>.~Z0] Qle [<.Z1,Z1>.~Z0]
   to ( Z0 Zle Z1 ) [gnd-Z0leZ1] ; re-fold to Q0/Q1. $)
gnd-Q0leQ1 $p |- ( Q0 Qle Q1 ) $=
    tZ1 tZ1 top tZ0 tcl
    tQ1
    tQ0
    tQ1 tZ1 tZ1 top tZ0 tcl df-q1 eqsym
    tZ0 tZ1 top tZ0 tcl
    tQ0
    tZ1 tZ1 top tZ0 tcl
    tQ0 tZ0 tZ1 top tZ0 tcl df-q0 eqsym
    tZ0 tZ1 top tZ0 tcl tZ1 tZ1 top tZ0 tcl tQle
    tZ0 tZ1 tZle
    tZ0 tZ1 df-Qle1
    gnd-Z0leZ1
    bi2i
    apQle1i
    apQle2i
  $.

$( ====================  LITERAL 2 : gnd-Q1neQ0  =========================== $)
$( -. Q1 = Q0 :  df-Qne1 ( a:=Z1 c:=Z0 ) on gnd-Z1neZ0 gives
   -. [<.Z1,Z1>.~Z0] = [<.Z0,Z1>.~Z0] ; re-fold to Q1/Q0. $)
gnd-Q1neQ0 $p |- -. Q1 = Q0 $=
    tZ0 tZ1 top tZ0 tcl
    tQ0
    tQ1
    tQ0 tZ0 tZ1 top tZ0 tcl df-q0 eqsym
    tZ1 tZ1 top tZ0 tcl
    tQ1
    tZ0 tZ1 top tZ0 tcl
    tQ1 tZ1 tZ1 top tZ0 tcl df-q1 eqsym
    tZ1 tZ0 weq wn
    tZ1 tZ1 top tZ0 tcl tZ0 tZ1 top tZ0 tcl weq wn
    gnd-Z1neZ0
    tZ1 tZ0 df-Qne1
    ax-mp
    necong1i
    necong2i
  $.

$( ============================================================================
   END.  Both order literals are now kernel-verified `$p`.  The ONLY `$a`
   ORDER/FOUNDATION primitives are el-0-suc ( (/) e. (suc(/)) — the
   von-Neumann reflection of of-letot, the C-proven-essential order axiom )
   and ne-suc-0 ( -. (suc(/)) = (/) — ordinal irreflexivity / Foundation ).
   The substrate is projection-free INCLUDING ORDER; the loop is CLOSED —
   the residue is exactly the order predicate Frontier C proved intrinsic.
   ============================================================================ $)
