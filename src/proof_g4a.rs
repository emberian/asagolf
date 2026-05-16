//! G4a — the angle-output law of cosines (`SSS → ACong`), staged last.
//!
//! Closes ASA′ GAP #2.  Grounded `G4-sas` is the SIDE-output SAS (two
//! sides + included angle → third side).  The regrounded ASA proof also
//! needs the dual ANGLE-output direction: from a triangle congruence in
//! the three squared sides, recover the angle congruence.
//!
//! CHOSEN STATEMENT (validated against df-acong's exact convention).
//! `df-acong $a |- ( ( ACong o p q a e f ) <-> ( EQ /\ SGN ) )` where
//!   EQ  : ( ( dot o p q )*( dot o p q ) )*( ( sqd a e )*( sqd a f ) )
//!       = ( ( dot a e f )*( dot a e f ) )*( ( sqd o p )*( sqd o q ) )
//!   SGN : 0 <_ ( ( dot o p q )*( dot a e f ) )
//! so the FIRST argument is the angle VERTEX (`dot o p q` = (p-o)·(q-o)).
//! To be maximally consumable I mirror G4-sas exactly: the two triangles
//! are `(a,b,c)` and `(e,f,g)`, the angle is at the shared first vertex
//! `a` / `e`.  Goal `( ACong a b c e f g )` — the EXACT dual of G4-sas
//! (G4-sas: sqd ab=ef, sqd ac=eg, ACong abc efg ⊢ sqd bc=fg ; here:
//! sqd ab=ef, sqd ac=eg, sqd bc=fg ⊢ ACong abc efg).  This is the
//! `g4a-sss` of the mission with p,q,r↦a,b,c and P,Q,R↦e,f,g and the
//! vertex taken as df-acong's first arg (the convention df-acong
//! actually unfolds to the squared cosine — documented per mandate).
//!
//!   g4a-sss :  ess  g4a.1 |- ( sqd a b ) = ( sqd e f )
//!                    g4a.2 |- ( sqd a c ) = ( sqd e g )
//!                    g4a.3 |- ( sqd b c ) = ( sqd f g )
//!                    g4a.4 |- ( 0 < ( sqd a b ) )      (NON-DEGENERACY)
//!              goal  |- ( ACong a b c e f g )
//!
//! WHY THE EXTRA `g4a.4` IS GENUINELY NEEDED (reported, not faked).
//! `loclink` (verified $p, side form) gives, per triangle,
//!   ( sqd b c ) = ( ( sqd a b )+( sqd a c ) ) -x ( ( dot a b c )+( dot a b c ) )
//! i.e. the law of cosines in *doubled-dot* form `2·dot = Σsqd − sqd`.
//! Substituting g4a.1/2/3 (pure congruence, NO big ring_eq) collapses the
//! two loclinks to `( D1 + D1 ) = ( D2 + D2 )` where Di = dot.  Recovering
//! `D1 = D2` from `2·D1 = 2·D2` is HALVING, and df-acong's EQ conjunct is
//! the *un-scaled* squared cosine `D1²·… = D2²·…` — there is no scale
//! freedom, so halving is unavoidable (squaring/“×4” the relation can
//! never be cancelled without it either).  In the bare ordered-ring /
//! field substrate the TRIVIAL ring (1 = 0, every axiom vacuously true,
//! `0 <_ u·u` included) is a model, so `0 < ( 1 + 1 )` is NOT provable —
//! halving is impossible without a nontriviality input.  A single
//! triangle non-degeneracy `0 < ( sqd a b )` supplies exactly that:
//! `0 < sqd ⇒ sqd ≠ 0 ⇒ 1 ≠ 0` (else sqd = sqd·1 = sqd·0 = 0) ⇒
//! `0 < 1` ⇒ `0 < ( 1 + 1 )` ⇒ `mulcposcan` halves `2D1 = 2D2` to
//! `D1 = D2`.  `g4a.4` is exactly G4-sas's own `0 < ( sqd a b )` hyp
//! (the construction discharges it just as for G4-sas), so the lemma
//! stays faithful and end-to-end consumable.
//!
//! Derivation (congruence-dominated, reuses the proven template):
//!  1. loclink(a,b,c), loclink(e,f,g)  [verified $p, ×2].
//!  2. g4a.1/2/3 ⇒ `( Σab + Σac ) = ( Σef + Σeg )` and `Σbc = Σfg`
//!     ⇒ (substitute, then `A = P -x ( P -x A )` ring trick)
//!     `( D1 + D1 ) = ( D2 + D2 )`.
//!  3. g4a.4 ⇒ `0 < ( 1 + 1 )` (nontriviality chain above).
//!  4. ring_eq `Di·(1+1) = ( Di + Di )` ⇒ `D1·(1+1) = D2·(1+1)`
//!     ⇒ mulcposcan ⇒ `D1 = D2`.
//!  5. df-acong EQ from `D1 = D2` + g4a.1/2 by cmu* congruence.
//!  6. df-acong SGN `0 <_ D1·D2` = `0 <_ D1·D1` (D1=D2) = of-sqpos (FREE).
//!  7. conj2 + df-acong `bi_rev` ⇒ ( ACong a b c e f g ).

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
///   idx 0 = g4a-sss   (SSS → ACong, the angle-output law of cosines)
///   idx 1 = g4a-dot   (SSS → ( dot a b c ) = ( dot e f g ); g4a-sss's
///                       own already-proven internal D1=D2, factored out)
///   idx 2 = sqd-sym   ( ( sqd a b ) = ( sqd b a ); a degree-2 identity)
pub fn count() -> usize {
    3
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    if idx == 2 {
        return make_sqd_sym(el);
    }
    assert!(
        idx == 0 || idx == 1,
        "proof_g4a: idx 0 (g4a-sss), 1 (g4a-dot), or 2 (sqd-sym)"
    );

    // Metamath statement labels are globally unique even inside a `${ $}`
    // scope, so g4a-sss and g4a-dot — which share the SAME four essential
    // hypotheses — must use distinct hyp labels.  Pick a per-idx prefix;
    // the proof body and the `ess` vec both read it, so the two lemmas are
    // literally the same derivation over differently-named hyps.
    let hp = if idx == 1 { "g4ad" } else { "g4a" };
    let h1 = format!("{hp}.1");
    let h2 = format!("{hp}.2");
    let h3 = format!("{hp}.3");
    let h4 = format!("{hp}.4");

    // ---- point/term constructors ------------------------------------
    let pa = || leaf("va");
    let pb = || leaf("vb");
    let pc = || leaf("vc");
    let pe = || leaf("ve");
    let pf = || leaf("vf");
    let pg = || leaf("vg");
    let z = || t0p(el);
    let one = || el.app("t1", &[], &[]).unwrap();
    let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
    let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
    let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
    let nw = |p: Pt| el.app("wn", &[("ph", p)], &[]).unwrap();
    let iw = |p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let aw = |p: Pt, q: Pt| el.app("wa", &[("ph", p), ("ps", q)], &[]).unwrap();
    let bw = |p: Pt, q: Pt| el.app("wb", &[("ph", p), ("ps", q)], &[]).unwrap();
    let mpp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };
    let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
    let dot = |o: Pt, p: Pt, q: Pt| {
        el.app("tdot", &[("o", o), ("p", p), ("q", q)], &[]).unwrap()
    };

    // ---- the squared sides + dots -----------------------------------
    let sab = sqd(pa(), pb());
    let sac = sqd(pa(), pc());
    let sbc = sqd(pb(), pc());
    let sef = sqd(pe(), pf());
    let seg = sqd(pe(), pg());
    let sfg = sqd(pf(), pg());
    let d1 = dot(pa(), pb(), pc()); // D1 = dot a b c
    let d2 = dot(pe(), pf(), pg()); // D2 = dot e f g

    // ---- 1. loclink ×2 (verified $p) --------------------------------
    //  ( sqd b c ) = ( ( Sab + Sac ) -x ( D1 + D1 ) )
    let lk_abc = el
        .app("loclink", &[("a", pa()), ("b", pb()), ("c", pc())], &[])
        .unwrap();
    //  ( sqd f g ) = ( ( Sef + Seg ) -x ( D2 + D2 ) )
    let lk_efg = el
        .app("loclink", &[("a", pe()), ("b", pf()), ("c", pg())], &[])
        .unwrap();
    let rhs_abc = mi(el, pl(el, sab.clone(), sac.clone()), pl(el, d1.clone(), d1.clone()));
    let rhs_efg = mi(el, pl(el, sef.clone(), seg.clone()), pl(el, d2.clone(), d2.clone()));

    // ---- 2. collapse to ( D1 + D1 ) = ( D2 + D2 ) -------------------
    // ( Sab + Sac ) = ( Sef + Seg )   from g4a.1, g4a.2
    let pe1 = cpl1(el, sab.clone(), sef.clone(), sac.clone(), leaf(&h1)); // (Sab+Sac)=(Sef+Sac)
    let pe2 = cpl2(el, sac.clone(), seg.clone(), sef.clone(), leaf(&h2)); // (Sef+Sac)=(Sef+Seg)
    let sum_s = eqtr3(
        el,
        pl(el, sab.clone(), sac.clone()),
        pl(el, sef.clone(), sac.clone()),
        pl(el, sef.clone(), seg.clone()),
        pe1,
        pe2,
    ); // ( Sab + Sac ) = ( Sef + Seg )
    // Rewrite loclink(abc) RHS minuend: ( Sab+Sac )-x( D1+D1 )
    //   = ( Sef+Seg )-x( D1+D1 )  via sum_s.
    let mid_abc = mi(
        el,
        pl(el, sef.clone(), seg.clone()),
        pl(el, d1.clone(), d1.clone()),
    );
    let cong_min = cmi1(
        el,
        pl(el, sab.clone(), sac.clone()),
        pl(el, sef.clone(), seg.clone()),
        pl(el, d1.clone(), d1.clone()),
        sum_s,
    ); // rhs_abc = mid_abc
    // ( sqd b c ) = ( Sef+Seg )-x( D1+D1 )
    let sbc_mid = eqtr3(el, sbc.clone(), rhs_abc.clone(), mid_abc.clone(), lk_abc.clone(), cong_min);
    // ( sqd b c ) = ( sqd f g )  [g4a.3] ; ( sqd f g ) = rhs_efg [lk_efg]
    let sbc_rhsefg = eqtr3(
        el,
        sbc.clone(),
        sfg.clone(),
        rhs_efg.clone(),
        leaf(&h3),
        lk_efg.clone(),
    ); // ( sqd b c ) = ( Sef+Seg )-x( D2+D2 )
    // mid_abc = ( sqd b c ) = rhs_efg
    let mid_eq_rhsefg = eqtr3(
        el,
        mid_abc.clone(),
        sbc.clone(),
        rhs_efg.clone(),
        eqcomm(el, sbc.clone(), mid_abc.clone(), sbc_mid),
        sbc_rhsefg,
    ); // ( ( Sef+Seg )-x( D1+D1 ) ) = ( ( Sef+Seg )-x( D2+D2 ) )
    // From ( P -x A ) = ( P -x B ) get A = B :  A = P-x(P-xA) = P-x(P-xB) = B
    let pp = || pl(el, sef.clone(), seg.clone()); // P = Sef+Seg
    let aa = || pl(el, d1.clone(), d1.clone()); // A = D1+D1
    let bb = || pl(el, d2.clone(), d2.clone()); // B = D2+D2
    let a_from = ring_eq(el, &aa(), &mi(el, pp(), mi(el, pp(), aa()))); // A = P-x(P-xA)
    let cong_pmpb = cmi2(
        el,
        mi(el, pp(), aa()),
        mi(el, pp(), bb()),
        pp(),
        mid_eq_rhsefg,
    ); // P-x(P-xA) = P-x(P-xB)
    let b_back = ring_eq(el, &mi(el, pp(), mi(el, pp(), bb())), &bb()); // P-x(P-xB) = B
    let a_eq_pmpb = eqtr3(el, aa(), mi(el, pp(), mi(el, pp(), aa())), mi(el, pp(), mi(el, pp(), bb())), a_from, cong_pmpb);
    let two_dd = eqtr3(el, aa(), mi(el, pp(), mi(el, pp(), bb())), bb(), a_eq_pmpb, b_back);
    // two_dd : ( D1 + D1 ) = ( D2 + D2 )

    // ---- 3. nontriviality:  g4a.4 ⇒ 0 < ( 1 + 1 ) -------------------
    // ¬( 0 = Sab )  from  0 < Sab  (lt0ne)
    let lt0ne_s = el.app("lt0ne", &[("u", z()), ("v", sab.clone())], &[]).unwrap(); // (0<Sab)->¬(0=Sab)
    let n_0sab = mpp(lt(z(), sab.clone()), nw(eq(z(), sab.clone())), leaf(&h4), lt0ne_s);
    // ¬( Sab = 0 )  : con3i on ( Sab=0 -> 0=Sab ) [eqcom]
    let eqcom_s = el.app("eqcom", &[("x", sab.clone()), ("y", z())], &[]).unwrap(); // (Sab=0)->(0=Sab)
    let c3a = el
        .app("con3i", &[("ph", eq(sab.clone(), z())), ("ps", eq(z(), sab.clone()))], &[eqcom_s])
        .unwrap(); // ¬(0=Sab) -> ¬(Sab=0)
    let n_sab0 = mpp(nw(eq(z(), sab.clone())), nw(eq(sab.clone(), z())), n_0sab, c3a);
    // ( 1 = 0 ) -> ( Sab = 0 ) :  Sab = Sab*1 = Sab*0 = 0
    let m1s = el.app("of-mul1", &[("u", sab.clone())], &[]).unwrap(); // (Sab*1)=Sab
    let sab_eq_s1 = eqcomm(el, mu(el, sab.clone(), one()), sab.clone(), m1s); // Sab = Sab*1
    let cm2_10 = el
        .app("cong-mu2", &[("a", one()), ("b", z()), ("c", sab.clone())], &[])
        .unwrap(); // ( 1=0 -> ( Sab*1 = Sab*0 ) )
    let s0comm = el.app("of-mulcom", &[("u", sab.clone()), ("v", z())], &[]).unwrap(); // (Sab*0)=(0*Sab)
    let m0 = el.app("mul0", &[("u", sab.clone())], &[]).unwrap(); // (0*Sab)=0
    let sab0_0 = eqtr3(el, mu(el, sab.clone(), z()), mu(el, z(), sab.clone()), z(), s0comm, m0); // (Sab*0)=0
    // ( 1=0 -> ( Sab*1 = Sab*0 ) ) is exactly cong-mu2's implication form.
    let one0 = || eq(one(), z());
    let cm2_imp = cm2_10; // ( 1=0 -> ( Sab*1 = Sab*0 ) )
    // Sab = Sab*1 (const)  -> under (1=0): Sab = Sab*0
    let sab_s1_a1 = el
        .app(
            "a1i",
            &[("ph", eq(sab.clone(), mu(el, sab.clone(), one()))), ("ps", one0())],
            &[sab_eq_s1],
        )
        .unwrap(); // ( 1=0 -> ( Sab = Sab*1 ) )
    let step_a = el
        .app(
            "eqtrd",
            &[
                ("ph", one0()),
                ("x", sab.clone()),
                ("y", mu(el, sab.clone(), one())),
                ("z", mu(el, sab.clone(), z())),
            ],
            &[sab_s1_a1, cm2_imp],
        )
        .unwrap(); // ( 1=0 -> ( Sab = Sab*0 ) )
    let sab0_0_a1 = el
        .app(
            "a1i",
            &[("ph", eq(mu(el, sab.clone(), z()), z())), ("ps", one0())],
            &[sab0_0],
        )
        .unwrap(); // ( 1=0 -> ( Sab*0 = 0 ) )
    let one0_imp_sab0 = el
        .app(
            "eqtrd",
            &[
                ("ph", one0()),
                ("x", sab.clone()),
                ("y", mu(el, sab.clone(), z())),
                ("z", z()),
            ],
            &[step_a, sab0_0_a1],
        )
        .unwrap(); // ( 1=0 -> ( Sab = 0 ) )
    // ¬( 1 = 0 )  by con3i + the ¬(Sab=0) we have
    let c3b = el
        .app("con3i", &[("ph", one0()), ("ps", eq(sab.clone(), z()))], &[one0_imp_sab0])
        .unwrap(); // ¬(Sab=0) -> ¬(1=0)
    let n_one0 = mpp(nw(eq(sab.clone(), z())), nw(one0()), n_sab0, c3b); // ¬( 1 = 0 )
    // 0 <_ 1  : of-sqpos(1) + of-mul1(1) + cong-le2
    let sq1 = el.app("of-sqpos", &[("u", one())], &[]).unwrap(); // 0<_(1*1)
    let m11 = el.app("of-mul1", &[("u", one())], &[]).unwrap(); // (1*1)=1
    let cl2_11 = el
        .app("cong-le2", &[("a", mu(el, one(), one())), ("b", one()), ("c", z())], &[])
        .unwrap(); // ( (1*1)=1 -> ( 0<_(1*1) -> 0<_1 ) )
    let zle1 = mpp(
        eq(mu(el, one(), one()), one()),
        iw(le(z(), mu(el, one(), one())), le(z(), one())),
        m11,
        cl2_11,
    );
    let zle1 = mpp(le(z(), mu(el, one(), one())), le(z(), one()), sq1, zle1); // 0<_1
    // 0 < 1  via g2-posne(1) with ¬(1=0)
    let posne1 = el
        .app("g2-posne", &[("u", one())], &[n_one0])
        .unwrap(); // ( 0<_1 -> 0<1 )
    let zlt1 = mpp(le(z(), one()), lt(z(), one()), zle1.clone(), posne1); // 0 < 1
    // 0 < ( 1 + 1 ) :
    //   0 <_ ( 1 + 1 )       [le0add(1,1)]
    //   ¬( ( 1+1 ) <_ 0 )    [else 1<_(1+1)<_0 ⇒ 1<_0, contradicting ¬(1<_0)]
    //   ltII ⇒ 0 < (1+1)
    let two = || pl(el, one(), one());
    let zle2 = el
        .app("le0add", &[("u", one()), ("v", one())], &[zle1.clone(), zle1.clone()])
        .unwrap(); // 0 <_ ( 1 + 1 )
    // ¬( 1 <_ 0 ) from 0<1 via df-lt
    let dflt1 = el.app("df-lt", &[("u", z()), ("v", one())], &[]).unwrap();
    let rhs_lt1 = aw(le(z(), one()), nw(le(one(), z())));
    let bi1_lt1 = el
        .app("ax-bi1", &[("ph", lt(z(), one())), ("ps", rhs_lt1.clone())], &[])
        .unwrap();
    let lt1_unf = mpp(bw(lt(z(), one()), rhs_lt1.clone()), iw(lt(z(), one()), rhs_lt1.clone()), dflt1, bi1_lt1);
    let conj_lt1 = mpp(lt(z(), one()), rhs_lt1.clone(), zlt1.clone(), lt1_unf);
    let n_1le0 = mpp(
        rhs_lt1.clone(),
        nw(le(one(), z())),
        conj_lt1,
        el.app("simpr", &[("ph", le(z(), one())), ("ps", nw(le(one(), z())))], &[]).unwrap(),
    ); // ¬( 1 <_ 0 )
    // 1 <_ ( 1 + 1 )  from 0<_1 via of-leadd: (0+1)<_(1+1), ring (0+1)=1
    let leadd1 = el
        .app("of-leadd", &[("u", z()), ("v", one()), ("w", one())], &[])
        .unwrap(); // ( 0<_1 -> ( (0+1) <_ (1+1) ) )
    let zp1_le_2 = mpp(le(z(), one()), le(pl(el, z(), one()), two()), zle1.clone(), leadd1);
    let r01 = ring_eq(el, &pl(el, z(), one()), &one()); // (0+1)=1
    let cl1_01 = el
        .app("cong-le1", &[("a", pl(el, z(), one())), ("b", one()), ("c", two())], &[])
        .unwrap(); // ( (0+1)=1 -> ( (0+1)<_(1+1) -> 1<_(1+1) ) )
    let imp01 = mpp(
        eq(pl(el, z(), one()), one()),
        iw(le(pl(el, z(), one()), two()), le(one(), two())),
        r01,
        cl1_01,
    );
    let one_le_two = mpp(le(pl(el, z(), one()), two()), le(one(), two()), zp1_le_2, imp01); // 1 <_ (1+1)
    // ( 1+1 ) <_ 0  ⇒  1 <_ 0   [of-letri: 1<_(1+1) -> ((1+1)<_0 -> 1<_0)]
    let letri = el
        .app("of-letri", &[("u", one()), ("v", two()), ("w", z())], &[])
        .unwrap(); // ( 1<_(1+1) -> ( (1+1)<_0 -> 1<_0 ) )
    let two_le0_imp_1le0 = mpp(
        le(one(), two()),
        iw(le(two(), z()), le(one(), z())),
        one_le_two,
        letri,
    ); // ( (1+1)<_0 -> 1<_0 )
    // ¬( (1+1) <_ 0 )  by con3i + ¬(1<_0)
    let c3_two = el
        .app("con3i", &[("ph", le(two(), z())), ("ps", le(one(), z()))], &[two_le0_imp_1le0])
        .unwrap(); // ¬(1<_0) -> ¬((1+1)<_0)
    let n_2le0 = mpp(nw(le(one(), z())), nw(le(two(), z())), n_1le0, c3_two); // ¬( (1+1)<_0 )
    // ltII( 0, 1+1 ) : ( 0<_(1+1) -> ( ¬((1+1)<_0) -> 0<(1+1) ) )
    let ltii2 = el.app("ltII", &[("u", z()), ("v", two())], &[]).unwrap();
    let step_2 = mpp(le(z(), two()), iw(nw(le(two(), z())), lt(z(), two())), zle2, ltii2);
    let zlt2 = mpp(nw(le(two(), z())), lt(z(), two()), n_2le0, step_2); // 0 < ( 1 + 1 )

    // ---- 4. halve:  D1·(1+1) = D2·(1+1)  ⇒ mulcposcan ⇒ D1 = D2 -----
    // ring_eq does NOT collapse X*1, so do `X*(1+1) = (X+X)` by hand:
    //   of-distr  X*(1+1) = (X*1)+(X*1)
    //   of-mul1   (X*1)=X  (×2 congruence)
    let dbl = |d: Pt| -> Pt {
        let distr = el
            .app("of-distr", &[("u", d.clone()), ("v", one()), ("w", one())], &[])
            .unwrap(); // X*(1+1) = (X*1)+(X*1)
        let m1 = el.app("of-mul1", &[("u", d.clone())], &[]).unwrap(); // (X*1)=X
        let c1 = cpl1(el, mu(el, d.clone(), one()), d.clone(), mu(el, d.clone(), one()), m1.clone()); // ((X*1)+(X*1))=(X+(X*1))
        let c2 = cpl2(el, mu(el, d.clone(), one()), d.clone(), d.clone(), m1); // (X+(X*1))=(X+X)
        let fold = eqtr3(
            el,
            pl(el, mu(el, d.clone(), one()), mu(el, d.clone(), one())),
            pl(el, d.clone(), mu(el, d.clone(), one())),
            pl(el, d.clone(), d.clone()),
            c1,
            c2,
        );
        eqtr3(
            el,
            mu(el, d.clone(), two()),
            pl(el, mu(el, d.clone(), one()), mu(el, d.clone(), one())),
            pl(el, d.clone(), d.clone()),
            distr,
            fold,
        )
    };
    let d1_2 = dbl(d1.clone()); // D1*(1+1)=(D1+D1)
    let d2_2 = dbl(d2.clone()); // D2*(1+1)=(D2+D2)
    // D1*(1+1) = (D1+D1) = (D2+D2) = D2*(1+1)
    let d1m_eq_d2d2 = eqtr3(
        el,
        mu(el, d1.clone(), two()),
        pl(el, d1.clone(), d1.clone()),
        pl(el, d2.clone(), d2.clone()),
        d1_2,
        two_dd,
    );
    let d2d2_eq_d2m = eqcomm(el, mu(el, d2.clone(), two()), pl(el, d2.clone(), d2.clone()), d2_2);
    let d1m_eq_d2m = eqtr3(
        el,
        mu(el, d1.clone(), two()),
        pl(el, d2.clone(), d2.clone()),
        mu(el, d2.clone(), two()),
        d1m_eq_d2d2,
        d2d2_eq_d2m,
    ); // ( D1*(1+1) ) = ( D2*(1+1) )
    let d1_eq_d2 = el
        .app(
            "mulcposcan",
            &[("u", d1.clone()), ("v", d2.clone()), ("w", two())],
            &[zlt2, d1m_eq_d2m],
        )
        .unwrap(); // |- ( D1 = D2 ) i.e. ( dot a b c ) = ( dot e f g )

    // === g4a-dot (idx 1): export exactly this internal dot-equality. ===
    // It is g4a-sss's own steps 1-4 (loclink×2 + collapse + the
    // nontriviality-halving + mulcposcan) with NO downstream df-acong, so
    // its conclusion is sign-free: ( dot a b c ) = ( dot e f g ).  Same
    // four essential hypotheses as g4a-sss.  Re-exposing this lets
    // asaprime build the vertex-b angle by pure congruence-substitution
    // (df-acong SGN then 0 ≤ dot·dot = of-sqpos, free — no dot≠0).
    if idx == 1 {
        return Lemma {
            name: "g4a-dot".into(),
            ess: vec![
                (
                    h1.clone(),
                    toks(&["|-", "(", "sqd", "a", "b", ")", "=", "(", "sqd", "e", "f", ")"]),
                ),
                (
                    h2.clone(),
                    toks(&["|-", "(", "sqd", "a", "c", ")", "=", "(", "sqd", "e", "g", ")"]),
                ),
                (
                    h3.clone(),
                    toks(&["|-", "(", "sqd", "b", "c", ")", "=", "(", "sqd", "f", "g", ")"]),
                ),
                (
                    h4.clone(),
                    toks(&["|-", "(", "0", "<", "(", "sqd", "a", "b", ")", ")"]),
                ),
            ],
            goal: d1_eq_d2,
        };
    }

    // ---- 5. df-acong EQ conjunct ------------------------------------
    //  ( D1*D1 )*( Sef*Seg ) = ( D2*D2 )*( Sab*Sac )
    let d1d1 = mu(el, d1.clone(), d1.clone());
    let d2d2 = mu(el, d2.clone(), d2.clone());
    // D1*D1 = D2*D2
    let dd1 = cmu1(el, d1.clone(), d2.clone(), d1.clone(), d1_eq_d2.clone()); // (D1*D1)=(D2*D1)
    let dd2 = cmu2(el, d1.clone(), d2.clone(), d2.clone(), d1_eq_d2.clone()); // (D2*D1)=(D2*D2)
    let dd_eq = eqtr3(el, d1d1.clone(), mu(el, d2.clone(), d1.clone()), d2d2.clone(), dd1, dd2);
    // Sef*Seg = Sab*Sac   (from g4a.1: Sab=Sef ; g4a.2: Sac=Seg)
    let sef_sab = eqcomm(el, sab.clone(), sef.clone(), leaf(&h1)); // Sef=Sab
    let seg_sac = eqcomm(el, sac.clone(), seg.clone(), leaf(&h2)); // Seg=Sac
    let ss1 = cmu1(el, sef.clone(), sab.clone(), seg.clone(), sef_sab); // (Sef*Seg)=(Sab*Seg)
    let ss2 = cmu2(el, seg.clone(), sac.clone(), sab.clone(), seg_sac); // (Sab*Seg)=(Sab*Sac)
    let ss_eq = eqtr3(
        el,
        mu(el, sef.clone(), seg.clone()),
        mu(el, sab.clone(), seg.clone()),
        mu(el, sab.clone(), sac.clone()),
        ss1,
        ss2,
    ); // ( Sef*Seg ) = ( Sab*Sac )
    // ( D1*D1 )*( Sef*Seg ) = ( D2*D2 )*( Sef*Seg ) = ( D2*D2 )*( Sab*Sac )
    let eq_l = cmu1(
        el,
        d1d1.clone(),
        d2d2.clone(),
        mu(el, sef.clone(), seg.clone()),
        dd_eq,
    ); // ( (D1*D1)*(Sef*Seg) ) = ( (D2*D2)*(Sef*Seg) )
    let eq_r = cmu2(
        el,
        mu(el, sef.clone(), seg.clone()),
        mu(el, sab.clone(), sac.clone()),
        d2d2.clone(),
        ss_eq,
    ); // ( (D2*D2)*(Sef*Seg) ) = ( (D2*D2)*(Sab*Sac) )
    let eq_pf = eqtr3(
        el,
        mu(el, d1d1.clone(), mu(el, sef.clone(), seg.clone())),
        mu(el, d2d2.clone(), mu(el, sef.clone(), seg.clone())),
        mu(el, d2d2.clone(), mu(el, sab.clone(), sac.clone())),
        eq_l,
        eq_r,
    ); // EQ conjunct

    // ---- 6. df-acong SGN conjunct: 0 <_ ( D1*D2 ) -------------------
    // D1*D2 = D1*D1   (cmu2 from D1=D2 :  D1*D2 = D1*D1, via D2=D1)
    let d2_eq_d1 = eqcomm(el, d1.clone(), d2.clone(), d1_eq_d2.clone()); // D2 = D1
    let d1d2_eq_d1d1 = cmu2(el, d2.clone(), d1.clone(), d1.clone(), d2_eq_d1); // (D1*D2)=(D1*D1)
    let sq_d1 = el.app("of-sqpos", &[("u", d1.clone())], &[]).unwrap(); // 0 <_ ( D1*D1 )
    let d1d1_eq_d1d2 = eqcomm(el, mu(el, d1.clone(), d2.clone()), d1d1.clone(), d1d2_eq_d1d1);
    let cl2_sgn = el
        .app(
            "cong-le2",
            &[("a", d1d1.clone()), ("b", mu(el, d1.clone(), d2.clone())), ("c", z())],
            &[],
        )
        .unwrap(); // ( (D1*D1)=(D1*D2) -> ( 0<_(D1*D1) -> 0<_(D1*D2) ) )
    let sgn_step = mpp(
        eq(d1d1.clone(), mu(el, d1.clone(), d2.clone())),
        iw(le(z(), d1d1.clone()), le(z(), mu(el, d1.clone(), d2.clone()))),
        d1d1_eq_d1d2,
        cl2_sgn,
    );
    let sgn_pf = mpp(
        le(z(), d1d1.clone()),
        le(z(), mu(el, d1.clone(), d2.clone())),
        sq_d1,
        sgn_step,
    ); // SGN conjunct : 0 <_ ( D1*D2 )

    // ---- 7. conj2 + df-acong bi_rev ⇒ ( ACong a b c e f g ) ---------
    let eq_a = eq(
        mu(el, d1d1.clone(), mu(el, sef.clone(), seg.clone())),
        mu(el, d2d2.clone(), mu(el, sab.clone(), sac.clone())),
    );
    let sgn_a = le(z(), mu(el, d1.clone(), d2.clone()));
    let conj_pf = conj2(el, eq_a.clone(), sgn_a.clone(), eq_pf, sgn_pf);
    let dfac = el
        .app(
            "df-acong",
            &[
                ("o", pa()),
                ("p", pb()),
                ("q", pc()),
                ("a", pe()),
                ("e", pf()),
                ("f", pg()),
            ],
            &[],
        )
        .unwrap();
    let g = el.bi_rev(dfac, conj_pf).unwrap(); // |- ( ACong a b c e f g )

    Lemma {
        name: "g4a-sss".into(),
        ess: vec![
            (
                h1.clone(),
                toks(&["|-", "(", "sqd", "a", "b", ")", "=", "(", "sqd", "e", "f", ")"]),
            ),
            (
                h2.clone(),
                toks(&["|-", "(", "sqd", "a", "c", ")", "=", "(", "sqd", "e", "g", ")"]),
            ),
            (
                h3.clone(),
                toks(&["|-", "(", "sqd", "b", "c", ")", "=", "(", "sqd", "f", "g", ")"]),
            ),
            (
                h4.clone(),
                toks(&["|-", "(", "0", "<", "(", "sqd", "a", "b", ")", ")"]),
            ),
        ],
        goal: g,
    }
}

/// `sqd-sym` (idx 2):  `|- ( sqd a b ) = ( sqd b a )`.
///
/// df-sqd unfolds `sqd` to `Δx² + Δy²`; symmetry is the degree-2
/// coordinate identity `(Xb-Xa)·(Xb-Xa) + (Yb-Ya)·(Yb-Ya)
/// = (Xa-Xb)·(Xa-Xb) + (Ya-Yb)·(Ya-Yb)` (≈4 monomials, far under the
/// ring_eq degree guard).  Proof: df-unfold both sides to coordinates,
/// ring_eq the polynomial identity, df-fold the RHS back — exactly the
/// loclink template, no geometric axioms.  No essential hypotheses.
/// Needed for asaprime's vertex-b signature alignment (`sqd b a` vs
/// `sqd a b`).
fn make_sqd_sym(el: &Elab) -> Lemma {
    let pa = || leaf("va");
    let pb = || leaf("vb");
    let xc = |t: Pt| el.app("txc", &[("a", t)], &[]).unwrap();
    let yc = |t: Pt| el.app("tyc", &[("a", t)], &[]).unwrap();
    let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
    let mi_ = |x: Pt, y: Pt| mi(el, x, y);
    let muu = |x: Pt, y: Pt| mu(el, x, y);
    let plu = |x: Pt, y: Pt| pl(el, x, y);
    // coordinate expansion matching df-sqd exactly:
    //   sqd p q = (Xq-Xp)*(Xq-Xp) + (Yq-Yp)*(Yq-Yp)
    let sqc = |p: Pt, q: Pt| {
        plu(
            muu(mi_(xc(q.clone()), xc(p.clone())), mi_(xc(q.clone()), xc(p.clone()))),
            muu(mi_(yc(q.clone()), yc(p.clone())), mi_(yc(q.clone()), yc(p.clone()))),
        )
    };
    let s_ab = sqc(pa(), pb()); // = ( sqd a b ) coords
    let s_ba = sqc(pb(), pa()); // = ( sqd b a ) coords

    // ( sqd a b ) = s_ab        [df-sqd a b]
    let df_ab = el.app("df-sqd", &[("a", pa()), ("b", pb())], &[]).unwrap();
    // s_ab = s_ba               [pure ring identity, degree 2]
    let core = ring_eq(el, &s_ab, &s_ba);
    // s_ba = ( sqd b a )        [df-sqd b a, commuted]
    let df_ba = eqcomm(
        el,
        sqd(pb(), pa()),
        s_ba.clone(),
        el.app("df-sqd", &[("a", pb()), ("b", pa())], &[]).unwrap(),
    );
    // ( sqd a b ) = s_ab = s_ba
    let lhs_to_sba = eqtr3(el, sqd(pa(), pb()), s_ab.clone(), s_ba.clone(), df_ab, core);
    // ( sqd a b ) = s_ba = ( sqd b a )
    let g = eqtr3(
        el,
        sqd(pa(), pb()),
        s_ba.clone(),
        sqd(pb(), pa()),
        lhs_to_sba,
        df_ba,
    );

    Lemma {
        name: "sqd-sym".into(),
        ess: vec![],
        goal: g,
    }
}
