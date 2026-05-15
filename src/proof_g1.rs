//! PLACEHOLDER (no-cheating), staged after the core 57 lemmas.
//!
//! Two distinct lines through a common point meet only there: from
//! `Tri a b c`, `On x (Ln a c)`, `On x (Ln b c)` derive `x = c`.
//! Unfold df-tri/df-on/df-coll; reduce both collinearity equalities
//! (ring_eq, using the hyps) to the cross-product relations; the
//! non-degeneracy `det != 0` (from -.Coll a b c) gives `0 < det^2`;
//! cancel it (mulcposcan), get `dx = dy = 0` (sqz), then subeq0 +
//! ptext yield `x = c`.
//!
//! Filled in its own git worktree; reuses the parent lemma library
//! via `use super::*` (Elab, Lemma, leaf, pl/mu/ring_eq/eqtr3/cmi*,
//! and earlier $p by name through `el.app`).

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
pub fn count() -> usize {
    0
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    unreachable!("proof_g1: no lemmas yet")
}
