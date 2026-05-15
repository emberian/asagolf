//! G1 ruler (no-cheating), staged after the core 57 lemmas.
//!
//! The Birkhoff ruler/segment-construction postulate, derived rather
//! than asserted.  This is the only postulate that needs the field
//! inverse and a principal square root (substrate axioms `of-recip`,
//! `of-sqrtnn`; the conservative definition `df-cp`).
//!
//! Goal (two inference lemmas; hyps `g1.1 = |- -. ( ( sqd a c ) = 0 )`
//! i.e. a != c, and `g1.2 = |- ( 0 <_ u )`):
//!   G1b  `|- ( sqd a ( cp a c u ) ) = u`
//!   G1a  `|- ( Ray a c ( cp a c u ) )`
//! with `cp a c u` the df-cp point `a + r*(c-a)`,
//!      `r = ( sqrt ( u * ( inv ( sqd a c ) ) ) )`, `s = ( sqd a c )`.
//!
//! Validated derivation plan (each step kernel-checkable; the friction,
//! as in G4/G2, is that several core lemmas are *inferences* and must
//! be re-expressed in deduction/implication form to use under a
//! hypothetical — build the currified helpers first):
//!
//!  H0 sqdnn   : |- ( 0 <_ ( sqd a b ) )        [df-sqd + of-sqpos + le0add]
//!  H1 posfromne (inf): |-(0<_X), |- -.(X=0)  =>  |-(0<X)
//!                       [ltII + lein2 + eqcom + mt]
//!  H2 lemul0monod : |- ( ( u <_ v ) -> ( ( 0 <_ w ) -> ( (u*w) <_ (v*w) ) ) )
//!                       [deduction form of core lemul0mono, via le2sub/
//!                        lemul02/sub2le + expi]
//!  H3 recippos (inf): |- ( 0 < X )  =>  |- ( 0 < ( inv X ) )
//!       Xne0 (lt0ne + eqcom-contrapose) -> of-recip => |- (X*inv X)=1 ;
//!       0<=X (ltle) ; -.(X<_0) (df-lt bi1 + simpr) ;
//!       of-letot(0,inv X) split by jaoi:
//!         using H2: ( (inv X<_0) -> ( (0<_X) -> ((inv X*X) <_ (0*X)) ) ),
//!         rewrite inv X*X = X*inv X = 1 (mulcom+SI1), 0*X=0 (mul0),
//!         1*X = X (mulcom+mul1) twice  =>  ( (inv X<_0) -> (X<_0) ) ;
//!         con3i + |- -.(X<_0)  =>  |- -.(inv X<_0) ; then ltII => 0<inv X.
//!  G1b:
//!    s := (sqd a c). 0<s : H1(sqdnn, g1.1 as -.(s=0)).
//!    0<inv s : H3(0<s).  0 <_ (u*inv s) : g1.2 (0<=u), 0<=inv s (ltle),
//!      lemul02 .  ax-sqrt(u*inv s) => r*r = (u*inv s).
//!    of-recip(s) (s!=0) => ( s * inv s ) = 1 .
//!    Xc(cp a c u) via df-cp + df-xc = ( (Xc a) + ( r * ( (Xc c) -x (Xc a) ) ) ).
//!    sqd a (cp a c u) via df-sqd ; ring_eq =>  = ( (r*r) * s ).
//!    ( (r*r)*s ) = ( (u*inv s)*s ) = ( u * ( s * inv s ) ) = ( u * 1 )
//!                = u   [ring_eq + recip fact + of-mul1]  => G1b.
//!  G1a: Ray a c (cp) <-> Coll a c (cp) /\ 0 <_ dot a c (cp) [df-ray ax-bi2].
//!    Coll a c (cp): df-coll polynomial = 0 by ring_eq (cp-a = r*(c-a)
//!      parallel to c-a; cross product identically 0).
//!    0 <_ dot a c (cp): dot a c (cp) = ( r * ( sqd a c ) ) [df-dot+ring_eq];
//!      r >= 0 (of-sqrtnn on 0<_(u*inv s)) ; s >= 0 (sqdnn) ; lemul02.
//!    jca + df-ray ax-bi2 => Ray a c (cp).
//!
//! Implement bottom-up: sqdnn, posfromne, lemul0monod, recippos, G1b, G1a.

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
pub fn count() -> usize {
    0
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    unreachable!("proof_g1: derivation scaffolded; implementation pending")
}
