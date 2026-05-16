//! G2 incidence (no-cheating), staged after the core 57 lemmas.
//!
//! Goal (grounded.mm): `( Tri a b c ) -> ( ( On x ( Ln a c ) ) ->
//! ( ( On x ( Ln b c ) ) -> x = c ) )`.
//!
//! Unfold df-tri/df-on/df-coll. With P = c−a, Q = c−b, d = x−c, and
//! X(U,V) = Ux·Vy − Uy·Vx the 2D cross:
//!   * `On x (Ln a c)` ⟺ `Coll a c x` ⟺ X(P, x−a) = 0, and x−a = P+d,
//!     so X(P,d) = 0.
//!   * `On x (Ln b c)` ⟺ `Coll b c x` ⟺ X(Q, x−b) = 0, x−b = Q+d,
//!     so X(Q,d) = 0.
//!   * `Tri a b c` ⟺ ¬Coll a b c ⟺ X(b−a, c−a) ≠ 0; and
//!     X(P,Q) = X(c−a, c−b) = X(b−a, c−a) = det ≠ 0.
//! Eliminate: Qy·X(P,d) − Py·X(Q,d) = det·dy and
//!            Qx·X(P,d) − Px·X(Q,d) = det·dx  (generic, degree-3).
//! Both X(·,d)=0 ⇒ det·dy = det·dx = 0 ⇒ (det·dy)²=(0)·… ; det≠0 ⇒
//! 0<det² ⇒ mulcposcan ⇒ dy²=0 ⇒ sqz ⇒ dy=0 ; same dx ; subeq0 gives
//! Xc x = Xc c, Yc x = Yc c ; jca + ptext ⇒ x = c.
//!
//! The elimination/identity steps are the degree-blowup risk (same as
//! G3a's null_id). The fix is the proven template: prove the elimination
//! as tiny GENERIC lemmas over fresh `$f term` atoms, then instantiate
//! with the big coordinate subterms by substitution — the normaliser
//! never sees a high-degree dense polynomial.
//!
//! Staged before proof_g3 (main() order: core, g2, g3, g1).
//!
//! `use super::*` brings the parent lemma library (Elab, Lemma, leaf,
//! mu/mi/pl/z/ring_eq/eqtr3/cmu*/cpl*/cmi*, earlier $p via el.app).

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
/// Phase 1: the two generic degree-3 elimination identities (validate
/// they stage tiny + kernel-✔, exactly as g3a-plk did). The full G2
/// inference lemma is wired on top of these next.
pub fn count() -> usize {
    2
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    let v = |s: &str| leaf(s);
    // 2D-vector component atoms: P=(a,b), Q=(c,e), d=(f,g).
    let (a, b, c, e, f, g) = (
        v("va"), v("vb"), v("vc"), v("ve"), v("vf"), v("vg"),
    );
    // X(P,d) = a·g − b·f ;  X(Q,d) = c·g − e·f ;  det = a·e − b·c.
    let xpd = mi(el, mu(el, a.clone(), g.clone()), mu(el, b.clone(), f.clone()));
    let xqd = mi(el, mu(el, c.clone(), g.clone()), mu(el, e.clone(), f.clone()));
    let det = mi(el, mu(el, a.clone(), e.clone()), mu(el, b.clone(), c.clone()));
    match idx {
        // g2-elim-y :  e·X(P,d) − b·X(Q,d) = det·g
        //   e(ag−bf) − b(cg−ef) = aeg − bef − bcg + bef = (ae−bc)g
        0 => {
            let lhs = mi(
                el,
                mu(el, e.clone(), xpd.clone()),
                mu(el, b.clone(), xqd.clone()),
            );
            let rhs = mu(el, det.clone(), g.clone());
            Lemma {
                name: "g2-elim-y".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            }
        }
        // g2-elim-x :  c·X(P,d) − a·X(Q,d) = (0 − det)·f
        //   c(ag−bf) − a(cg−ef) = acg − bcf − acg + aef = (ae−bc)·… in f:
        //   = aef − bcf = (ae−bc)f = det·f ; we want it as −det·(−f)?
        //   Keep simple: c·X(P,d) − a·X(Q,d) = det·f  (check below).
        //   c(ag−bf)−a(cg−ef)=acg−bcf−acg+aef = aef−bcf = (ae−bc)f.
        1 => {
            let lhs = mi(
                el,
                mu(el, c.clone(), xpd.clone()),
                mu(el, a.clone(), xqd.clone()),
            );
            let rhs = mu(el, det.clone(), f.clone());
            Lemma {
                name: "g2-elim-x".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            }
        }
        _ => unreachable!(),
    }
}
