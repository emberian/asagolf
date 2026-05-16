//! G4a — the angle-output law of cosines (`SSS → ACong`), staged last.
//!
//! Closes ASA′ GAP #2. Grounded `G4-sas` is the SIDE-output SAS (two
//! sides + included angle → third side). The regrounded ASA proof also
//! needs the dual ANGLE-output direction: from a triangle congruence in
//! the three squared sides, recover the angle congruence
//!   `g4a-sss` :  ess  ( sqd p q ) = ( sqd P Q ) ,
//!                      ( sqd p r ) = ( sqd P R ) ,
//!                      ( sqd q r ) = ( sqd Q R )
//!                goal  ( ACong q p r Q P R )            (angle at p / P)
//!
//! Derivable, no cheating, ~G4-sized, reusing the proven template:
//!  - `loclink` (already verified): `2·dot p q r` is a fixed ring
//!    expression in { sqd p q, sqd p r, sqd q r } — so the three
//!    sqd-equalities give `dot q p r = dot Q P R` by congruence (NO
//!    big ring_eq: substitution of equals through loclink).
//!  - df-acong EQ conjunct `(dot)²·(sqd·sqd) = (dot')²·(sqd'·sqd')`
//!    then follows from `dot = dot'` + the sqd-equalities by congruence.
//!  - df-acong SGN `0 ≤ (dot)(dot')` = `0 ≤ dot²` (since dot=dot'),
//!    free from `of-sqpos` — so NO non-degeneracy hyp is needed here
//!    (the SSS-congruence form sidesteps the squared-cosine sign issue
//!    that blocks the bare `acong-tr`).
//!  - df-acong `bi_rev` ⇒ ACong.
//!
//! `use super::*` brings the parent lemma library (Elab, Lemma, leaf,
//! mu/mi/pl/ring_eq/eqtr3/cmu*/cpl*/cmi*, and earlier $p — incl.
//! `loclink` — by name through `el.app`).

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
pub fn count() -> usize {
    0
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    unreachable!("proof_g4a: g4a-sss derivation pending")
}
