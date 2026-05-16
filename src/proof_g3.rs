//! G3 postulates (no-cheating), staged after the core 57 lemmas.
//!
//! ============================================================================
//! CHOSEN STATEMENTS (validated empirically against df-acong / df-coll)
//! ============================================================================
//!
//! G3a  "G3a-rayangle"   (idx 2, INFERENCE)
//!     ess  g3a.1 : |- ( Ray a c x )
//!     goal       : |- ( ACong a b x a b c )
//!
//!     Faithful Birkhoff `ax-rayangle`.  df-acong's convention is
//!     `ACong o p q a e f` = "squared-cosine of angle at vertex o between
//!     o->p, o->q  ==  that at vertex a between a->e, a->f".  The role
//!     "angle at vertex a between a->b and a->x  ==  angle at vertex a
//!     between a->b and a->c" is therefore `ACong a b x a b c`
//!     (o=a,p=b,q=x ; a=a,e=b,f=c).  Unfolding df-acong gives
//!         EQ : ((dot a b x)*(dot a b x))*((sqd a b)*(sqd a c))
//!            = ((dot a b c)*(dot a b c))*((sqd a b)*(sqd a x))
//!        SGN : 0 <_ ( (dot a b x) * (dot a b c) )
//!     With the coordinate (df-dot/df-sqd) expansions and the collinearity
//!     determinant  D = (Xc-Xa)(Yx-Ya) -x (Yc-Ya)(Xx-Xa)  extracted from
//!     `Coll a c x` (df-coll, after df-ray simpl), and the dot-sign
//!     0 <_ (dot a c x) (df-ray simpr), both conjuncts are exact
//!     consequences (CAS-verified Nullstellensatz certificates):
//!       EQ_l -x EQ_r                         = ( Sb * Gcof ) * D
//!       (Bx*Bc)*(Sc+Sx) -x C*(Bc*Bc+Bx*Bx)  = LamN * D
//!     so D=0 collapses EQ to a ring identity, and the SGN follows from
//!     0<=C plus an order-cancellation of the non-strict factor (Sc+Sx)
//!     — done by the `lecpos` helper (generic case) together with a
//!     degenerate all-coordinates-zero branch closed by `addz`+`sqz`.
//!
//! G3b  ax-prot-uniq  — NOT DERIVABLE from the sqrt-free df-acong; OMITTED.
//!     grounded.mm lists G3b as ( ACong a b x a b c ) -> ( Ray b c x ).
//!     This is FALSE as a polynomial implication (so it is not staged;
//!     count() = 3, no G3b lemma).  df-acong is the *squared* cosine
//!     (mandatory for a sqrt-free encoding), hence blind to a ray vs. its
//!     mirror image across line a-b.  Explicit CAS counterexample (all
//!     allowed hypotheses hold, conclusion fails):
//!       (Xb-Xa,Yb-Ya)=(1.3,-0.7) (Xc-Xa,Yc-Ya)=(2.0,0.5)
//!       (Xx-Xa,Yx-Ya)=(0.9,-2.561073825503356)
//!     gives EQ=0, dot(a,b,x)*dot(a,b,c)=6.67>=0, dot(a,c,x)=0.52>=0, yet
//!     the collinearity determinant D=-5.57 != 0 (and `Coll b c x` also
//!     fails for the genuinely collinear witness x=1.7*(c-a):
//!     its determinant is -1.43 != 0).  Birkhoff protractor *uniqueness*
//!     needs oriented angles (a cross-product sign) that the squared
//!     cosine discards; none of the allowed hypotheses supply it, so no
//!     kernel proof exists for the stated signature.  Reported, not faked.
//!
//! Helpers (lower idx, reusable):
//!   idx 0  "lecpos" : ess 0<=(w*m)  =>  goal ( (0<w) -> (0<=m) )
//!                     (order cancellation, closed implication form so it
//!                      composes through `syl`)
//!   idx 1  "addz"   : 0<=a , 0<=b , (a+b)=0  =>  a=0
//!
//! `use super::*` brings the parent lemma library (Elab, Lemma, leaf,
//! pl/mi/mu/neg/t0p/ring_eq/eqtr3/eqcomm/cmu*/cpl*/cmi*, earlier $p by
//! name through `el.app`).

#[allow(unused_imports)]
use super::*;

pub fn count() -> usize {
    16
}

#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    let n = |p: Pt| el.app("wn", &[("ph", p)], &[]).unwrap();
    let imp = |p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let aw = |p: Pt, q: Pt| el.app("wa", &[("ph", p), ("ps", q)], &[]).unwrap();
    let ow = |p: Pt, q: Pt| el.app("wo", &[("ph", p), ("ps", q)], &[]).unwrap();
    let mp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };
    let syl = |p: Pt, q: Pt, r: Pt, s1: Pt, s2: Pt| {
        el.app("syl", &[("ph", p), ("ps", q), ("ch", r)], &[s1, s2])
            .unwrap()
    };
    let a1i = |ph: Pt, ps: Pt, pf: Pt| {
        el.app("a1i", &[("ph", ph), ("ps", ps)], &[pf]).unwrap()
    };
    let mpd = |ph: Pt, ps: Pt, ch: Pt, p1: Pt, p2: Pt| {
        el.app(
            "mpd",
            &[("ph", ph), ("ps", ps), ("ch", ch)],
            &[p1, p2],
        )
        .unwrap()
    };
    let syld = |ph: Pt, ps: Pt, ch: Pt, th: Pt, p1: Pt, p2: Pt| {
        el.app(
            "syld",
            &[("ph", ph), ("ps", ps), ("ch", ch), ("th", th)],
            &[p1, p2],
        )
        .unwrap()
    };
    let com12 = |ph: Pt, ps: Pt, ch: Pt, p1: Pt| {
        el.app(
            "com12",
            &[("ph", ph), ("ps", ps), ("ch", ch)],
            &[p1],
        )
        .unwrap()
    };
    let con3 = |ph: Pt, ps: Pt| el.app("con3", &[("ph", ph), ("ps", ps)], &[]).unwrap();
    let con3i = |ph: Pt, ps: Pt, p1: Pt| {
        el.app("con3i", &[("ph", ph), ("ps", ps)], &[p1]).unwrap()
    };
    let idt = |ph: Pt| el.app("id", &[("ph", ph)], &[]).unwrap();
    let nn1 = |ph: Pt| el.app("notnot1", &[("ph", ph)], &[]).unwrap();
    let nn2 = |ph: Pt| el.app("notnot2", &[("ph", ph)], &[]).unwrap();
    let z = || t0p(el);
    let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
    let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
    let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
    let xc = |p: Pt| el.app("txc", &[("a", p)], &[]).unwrap();
    let yc = |p: Pt| el.app("tyc", &[("a", p)], &[]).unwrap();
    // ( A -> (X -> Y) ) , ( Y -> Z )  =>  ( A -> (X -> Z) )
    let imim = |aa: Pt, xx: Pt, yy: Pt, zz: Pt, axy: Pt, yz: Pt| -> Pt {
        let yz_a1 = a1i(imp(yy.clone(), zz.clone()), aa.clone(), yz);
        syld(aa, xx, yy, zz, axy, yz_a1)
    };

    match idx {
        // ============================================================
        // idx 0 : lecpos   ess 0<=(w*m)  ==>  ( (0<w) -> (0<=m) )
        // ============================================================
        0 => {
            let w = || leaf("vw");
            let m = || leaf("vt");
            let wm = || mu(el, w(), m());
            let nm = || neg(el, m()); // 0 -x m
            let nwm = || neg(el, wm()); // 0 -x (w*m)
            let aA = || lt(z(), w()); // A = ( 0 < w )
            let m0 = || le(m(), z()); // M0 = ( m <_ 0 )
            let nb = || n(le(z(), m())); // NB = -. ( 0 <_ m )
            let h = || leaf("lecpos.1"); // |- ( 0 <_ ( w * m ) )

            // tot : ( (0<_m) \/ (m<_0) )
            let tot = el
                .app("of-letot", &[("u", z()), ("v", m())], &[])
                .unwrap();

            // ---- br2 : ( (m<_0) -> ( A -> (0<_m) ) ) ----
            // s1 : ( M0 -> ( NB -> (m<0) ) )
            let s1 = el
                .app("ltII", &[("u", m()), ("v", z())], &[])
                .unwrap();
            // lt0ne : ( (m<0) -> -.(m=0) )
            let lt0ne = el
                .app("lt0ne", &[("u", m()), ("v", z())], &[])
                .unwrap();
            // s2 : ( M0 -> ( NB -> -.(m=0) ) )
            let s2 = imim(
                m0(),
                nb(),
                lt(m(), z()),
                n(eq(m(), z())),
                s1.clone(),
                lt0ne,
            );
            // l2s : ( M0 -> (0<_(0-xm)) )
            let l2s = el
                .app("le2sub", &[("u", m()), ("v", z())], &[])
                .unwrap();
            // lein2(0,0-xm) : ( (0<_(0-xm)) -> ( ((0-xm)<_0) -> (0=(0-xm)) ) )
            let lein2a = el
                .app("lein2", &[("u", z()), ("v", nm())], &[])
                .unwrap();
            // ( M0 -> ( ((0-xm)<_0) -> (0=(0-xm)) ) )
            let t1 = mpd(
                m0(),
                le(z(), nm()),
                imp(le(nm(), z()), eq(z(), nm())),
                l2s.clone(),
                a1i(
                    imp(le(z(), nm()), imp(le(nm(), z()), eq(z(), nm()))),
                    m0(),
                    lein2a,
                ),
            );
            // (0=(0-xm)) -> ((0-xm)=0) -> (0=m) -> (m=0)
            let ec_nm = el
                .app("eqcom", &[("x", z()), ("y", nm())], &[])
                .unwrap(); // (0=(0-xm))->((0-xm)=0)
            let subeq0nm = el
                .app("subeq0", &[("u", z()), ("v", m())], &[])
                .unwrap(); // ((0-xm)=0)->(0=m)
            let ec_m = el
                .app("eqcom", &[("x", z()), ("y", m())], &[])
                .unwrap(); // (0=m)->(m=0)
            let chain_m0 = {
                let c1 = syl(
                    eq(z(), nm()),
                    eq(nm(), z()),
                    eq(z(), m()),
                    ec_nm,
                    subeq0nm,
                );
                syl(eq(z(), nm()), eq(z(), m()), eq(m(), z()), c1, ec_m)
            }; // ( (0=(0-xm)) -> (m=0) )
            // ( M0 -> ( ((0-xm)<_0) -> (m=0) ) )
            let t2 = imim(
                m0(),
                le(nm(), z()),
                eq(z(), nm()),
                eq(m(), z()),
                t1,
                chain_m0,
            );
            // con3 in consequent : ( M0 -> ( -.(m=0) -> -.((0-xm)<_0) ) )
            let t2c = syl(
                m0(),
                imp(le(nm(), z()), eq(m(), z())),
                imp(n(eq(m(), z())), n(le(nm(), z()))),
                t2,
                con3(le(nm(), z()), eq(m(), z())),
            );
            // s3 : ( M0 -> ( NB -> -.((0-xm)<_0) ) )
            let s3 = syld(
                m0(),
                nb(),
                n(eq(m(), z())),
                n(le(nm(), z())),
                s2,
                t2c,
            );
            // ltII(0,0-xm) : ( (0<_(0-xm)) -> ( -.((0-xm)<_0) -> (0<(0-xm)) ) )
            let ltii2 = el
                .app("ltII", &[("u", z()), ("v", nm())], &[])
                .unwrap();
            let t3 = mpd(
                m0(),
                le(z(), nm()),
                imp(n(le(nm(), z())), lt(z(), nm())),
                l2s.clone(),
                a1i(
                    imp(le(z(), nm()), imp(n(le(nm(), z())), lt(z(), nm()))),
                    m0(),
                    ltii2,
                ),
            ); // ( M0 -> ( -.((0-xm)<_0) -> (0<(0-xm)) ) )
            // s4 : ( M0 -> ( NB -> (0<(0-xm)) ) )
            let s4 = syld(
                m0(),
                nb(),
                n(le(nm(), z())),
                lt(z(), nm()),
                s3,
                t3,
            );
            // lemul2 : ( (0<w) -> ( (0<(0-xm)) -> (0<(w*(0-xm))) ) ) = ( A -> ... )
            let lemul2 = el
                .app("lemul2", &[("u", w()), ("v", nm())], &[])
                .unwrap();
            // ( (0<(w*(0-xm))) -> (0<(0-x(w*m))) ) via ring + cong-lt2
            let rneg = ring_eq(el, &mu(el, w(), nm()), &nwm());
            let cong_lt2 = el
                .app(
                    "cong-lt2",
                    &[("a", mu(el, w(), nm())), ("b", nwm()), ("c", z())],
                    &[],
                )
                .unwrap();
            let cong_lt2m = mp(
                eq(mu(el, w(), nm()), nwm()),
                imp(lt(z(), mu(el, w(), nm())), lt(z(), nwm())),
                rneg,
                cong_lt2,
            );
            // ( A -> ( (0<(0-xm)) -> (0<(0-x(w*m))) ) )
            let aA_step = imim(
                aA(),
                lt(z(), nm()),
                lt(z(), mu(el, w(), nm())),
                lt(z(), nwm()),
                lemul2,
                cong_lt2m,
            );
            // ( (0<(0-x(w*m))) -> -.(0<_(w*m)) )   [uses closed ess h()]
            let neg_h = {
                // 0<(0-x(w*m)) -> -.(0=(0-x(w*m)))  [lt0ne]
                let lt0ne2 = el
                    .app("lt0ne", &[("u", z()), ("v", nwm())], &[])
                    .unwrap();
                // 0<(0-x(w*m)) -> (0<_(0-x(w*m)))  [ltle]
                let ltle2 = el
                    .app("ltle", &[("u", z()), ("v", nwm())], &[])
                    .unwrap();
                // (0<_(0-x(w*m))) -> ((w*m)<_0)  [sub2le]
                let sub2le2 = el
                    .app("sub2le", &[("u", wm()), ("v", z())], &[])
                    .unwrap();
                let p_wmle0 = syl(
                    lt(z(), nwm()),
                    le(z(), nwm()),
                    le(wm(), z()),
                    ltle2,
                    sub2le2,
                ); // ( P -> ((w*m)<_0) )   P:=0<(0-x(w*m))
                // lein2(0,(w*m)) : ( (0<_(w*m)) -> ( ((w*m)<_0) -> (0=(w*m)) ) )
                let lein2c = el
                    .app("lein2", &[("u", z()), ("v", wm())], &[])
                    .unwrap();
                // com12 -> ( ((w*m)<_0) -> ( (0<_(w*m)) -> (0=(w*m)) ) )
                let lein2c_com = com12(
                    le(z(), wm()),
                    le(wm(), z()),
                    eq(z(), wm()),
                    lein2c,
                );
                // P -> ( (0<_(w*m)) -> (0=(w*m)) )
                let p_q_eq = syl(
                    lt(z(), nwm()),
                    le(wm(), z()),
                    imp(le(z(), wm()), eq(z(), wm())),
                    p_wmle0,
                    lein2c_com,
                );
                // (0=(w*m)) -> ((w*m)=0) -> ((0-x(w*m))=0) -> (0=(0-x(w*m)))
                let e_a = el
                    .app("eqcom", &[("x", z()), ("y", wm())], &[])
                    .unwrap();
                let cmi2v = el
                    .app(
                        "cong-mi2",
                        &[("a", wm()), ("b", z()), ("c", z())],
                        &[],
                    )
                    .unwrap(); // ( (w*m)=0 -> ((0-x(w*m))=(0-x0)) )
                let r00 = el.app("subid", &[("u", z())], &[]).unwrap(); // (0-x0)=0
                let cmi2vz = {
                    let r00a1 = a1i(eq(neg(el, z()), z()), eq(wm(), z()), r00);
                    el.app(
                        "eqtrd",
                        &[("ph", eq(wm(), z())), ("x", nwm()), ("y", neg(el, z())), ("z", z())],
                        &[cmi2v, r00a1],
                    )
                    .unwrap() // ( (w*m)=0 -> ((0-x(w*m))=0) )
                };
                let e_c = el
                    .app("eqcom", &[("x", nwm()), ("y", z())], &[])
                    .unwrap(); // ((0-x(w*m))=0)->(0=(0-x(w*m)))
                let conv = {
                    let c1 = syl(
                        eq(z(), wm()),
                        eq(wm(), z()),
                        eq(nwm(), z()),
                        e_a,
                        cmi2vz,
                    );
                    syl(
                        eq(z(), wm()),
                        eq(nwm(), z()),
                        eq(z(), nwm()),
                        c1,
                        e_c,
                    )
                }; // (0=(w*m)) -> (0=(0-x(w*m)))
                // P -> ( (0<_(w*m)) -> (0=(0-x(w*m))) )
                let p_q_neg0 = imim(
                    lt(z(), nwm()),
                    le(z(), wm()),
                    eq(z(), wm()),
                    eq(z(), nwm()),
                    p_q_eq,
                    conv,
                );
                // con3 : ( (Q->X) -> (-.X -> -.Q) ), Q=0<=wm, X=0=(0-x(w*m))
                let p_negx_negq = syl(
                    lt(z(), nwm()),
                    imp(le(z(), wm()), eq(z(), nwm())),
                    imp(n(eq(z(), nwm())), n(le(z(), wm()))),
                    p_q_neg0,
                    con3(le(z(), wm()), eq(z(), nwm())),
                ); // P -> ( -.X -> -.Q )
                // mpd with lt0ne2 (P-> -.X) : P -> -.Q
                mpd(
                    lt(z(), nwm()),
                    n(eq(z(), nwm())),
                    n(le(z(), wm())),
                    lt0ne2,
                    p_negx_negq,
                ) // ( (0<(0-x(w*m))) -> -.(0<_(w*m)) )
            };
            // Now combine: s4 : ( M0 -> ( NB -> (0<(0-xm)) ) ) (no A)
            //   lift under A : ( A -> ( M0 -> ( NB -> (0<(0-xm)) ) ) )
            let s4_A = a1i(
                imp(m0(), imp(nb(), lt(z(), nm()))),
                aA(),
                s4,
            );
            // a_x_negh : A -> ( X -> -.H )   X=(0<(0-xm)), H=(0<=(w*m))
            let a_x_negh = imim(
                aA(),
                lt(z(), nm()),
                lt(z(), nwm()),
                n(le(z(), wm())),
                aA_step.clone(),
                neg_h.clone(),
            );
            // The cleanest correct route avoiding deep nesting: use `mpd`
            // twice at the A-level after `com12`-flattening.  Define
            //   F := A -> ( M0 -> ( NB -> X ) )      = s4_A
            //   G := A -> ( X -> -.H )               = a_x_negh
            // Want H0 := A -> ( M0 -> ( NB -> -.H ) ).
            // Peel M0: by com12 on (M0->(NB->X)) ... do at A level using the
            // generic combinator `imim` which expects ( A -> (P -> Q) ).
            // Treat P:=M0, Q:=(NB->X).  Compose with (Q -> Q')? not direct.
            // Use nested: define
            //   step_m0 : A -> ( M0 -> ( (NB->X) ) )  = s4_A
            //   We need to turn (NB->X) into (NB-> -.H) using G.
            //   G gives A -> (X -> -.H).  Lift to A -> ( (NB->X) -> (NB-> -.H) ):
            //     that is "post-compose under NB", = a1i? It's the functor
            //     (NB-> _).  ( (X-> -.H) -> ( (NB->X) -> (NB-> -.H) ) ) is a
            //     theorem schema = `imim2`-like = ax-2 corollary.  Build it:
            //     from (X-> -.H) get ( (NB->X) -> (NB-> -.H) ) by:
            //       a1i (X-> -.H) under NB -> ( NB -> (X-> -.H) ); ax-2 then
            //       distributes: ( (NB->X) -> (NB-> -.H) ).
            let imim2_under_nb = |xx: Pt, yy: Pt, pf_xy: Pt| -> Pt {
                // pf_xy : |- ( X -> Y ) (here under A — but a1i needs the
                // inner; we operate purely propositionally with ax-1/ax-2)
                let nbw = nb();
                let xy_a1 = a1i(imp(xx.clone(), yy.clone()), nbw.clone(), pf_xy);
                // ax-2 : ( (NB->(X->Y)) -> ( (NB->X) -> (NB->Y) ) )
                let ax2 = el
                    .app(
                        "ax-2",
                        &[("ph", nbw.clone()), ("ps", xx.clone()), ("ch", yy.clone())],
                        &[],
                    )
                    .unwrap();
                mp(
                    imp(nbw.clone(), imp(xx.clone(), yy.clone())),
                    imp(imp(nbw.clone(), xx.clone()), imp(nbw.clone(), yy.clone())),
                    xy_a1,
                    ax2,
                ) // |- ( (NB->X) -> (NB->Y) )
            };
            // We need (X-> -.H) as a *closed* proof to feed imim2_under_nb,
            // but it depends on A (a_x_negh : A -> (X-> -.H)).  So apply the
            // functor at the A-level: build  A -> ( (NB->X) -> (NB-> -.H) ).
            let a_functor = {
                // from a_x_negh : A -> ( X -> -.H )
                // produce A -> ( (NB->X) -> (NB-> -.H) ) via ax-2 lifted.
                // ( (X-> -.H) -> ( (NB->X) -> (NB-> -.H) ) ) is closed schema:
                let xx = lt(z(), nm());
                let yy = n(le(z(), wm()));
                // closed: imim2 schema  S := ( (X->Y) -> ((NB->X)->(NB->Y)) )
                let s_a1 = {
                    // build S
                    let nbw = nb();
                    // ( NB -> (X->Y) ) -> ( (NB->X)->(NB->Y) )  is ax-2
                    let ax2 = el
                        .app(
                            "ax-2",
                            &[("ph", nbw.clone()), ("ps", xx.clone()), ("ch", yy.clone())],
                            &[],
                        )
                        .unwrap();
                    // ( (X->Y) -> ( NB -> (X->Y) ) ) is ax-1
                    let ax1 = el
                        .app(
                            "ax-1",
                            &[("ph", imp(xx.clone(), yy.clone())), ("ps", nbw.clone())],
                            &[],
                        )
                        .unwrap();
                    syl(
                        imp(xx.clone(), yy.clone()),
                        imp(nbw.clone(), imp(xx.clone(), yy.clone())),
                        imp(imp(nbw.clone(), xx.clone()), imp(nbw.clone(), yy.clone())),
                        ax1,
                        ax2,
                    ) // |- S
                };
                // A -> ( (NB->X) -> (NB-> -.H) )  by syl ( a_x_negh ; S )
                syl(
                    aA(),
                    imp(xx.clone(), yy.clone()),
                    imp(imp(nb(), xx.clone()), imp(nb(), yy.clone())),
                    a_x_negh.clone(),
                    s_a1,
                )
            };
            let _ = (imim2_under_nb,);
            // s4_A : A -> ( M0 -> ( NB -> X ) )
            // a_functor : A -> ( (NB->X) -> (NB-> -.H) )
            // compose under M0: A -> ( M0 -> ( NB -> -.H ) )
            let r_negh = {
                // lift a_functor under M0: A -> ( M0 -> ( (NB->X) -> (NB-> -.H) ) )
                let af_m0 = imim(
                    aA(),
                    m0(),
                    m0(),
                    imp(
                        imp(nb(), lt(z(), nm())),
                        imp(nb(), n(le(z(), wm()))),
                    ),
                    a1i(imp(m0(), m0()), aA(), idt(m0())),
                    a1i(
                        imp(
                            imp(nb(), lt(z(), nm())),
                            imp(nb(), n(le(z(), wm()))),
                        ),
                        m0(),
                        // closed? a_functor is A->(...). Need (...) closed.
                        // Provide closed schema applied to neg-side?  Use S
                        // composed with closed neg_h+aA_step is not closed.
                        // Instead use syld at A-level directly:
                        idt(imp(
                            imp(nb(), lt(z(), nm())),
                            imp(nb(), n(le(z(), wm()))),
                        )),
                    ),
                );
                let _ = af_m0;
                // Direct A-level syld: F=s4_A:A->(M0->(NB->X)),
                //   we want A->(M0->(NB-> -.H)).  Use syld with ps=M0,
                //   ch=(NB->X), th=(NB-> -.H):
                //   need A->(M0->(NB->X))  [F]  and  A->((NB->X)->(NB-> -.H))
                //   [a_functor].  syld(ph=A,ps=M0,ch=(NB->X),th=(NB-> -.H)).
                syld(
                    aA(),
                    m0(),
                    imp(nb(), lt(z(), nm())),
                    imp(nb(), n(le(z(), wm()))),
                    s4_A.clone(),
                    a_functor.clone(),
                ) // A -> ( M0 -> ( NB -> -.H ) )
            };
            // collapse -.H with closed ess h() : A -> ( M0 -> -.NB )
            let r_negnb = {
                // ( (NB-> -.H) -> ( -.-.H -> -.NB ) )  con3
                let c = con3(nb(), n(le(z(), wm())));
                // A -> ( M0 -> ( -.-.H -> -.NB ) )
                let step = imim(
                    aA(),
                    m0(),
                    imp(nb(), n(le(z(), wm()))),
                    imp(n(n(le(z(), wm()))), n(nb())),
                    r_negh,
                    c,
                );
                // -.-.H from h() via notnot1
                let nnH = mp(
                    le(z(), wm()),
                    n(n(le(z(), wm()))),
                    h(),
                    nn1(le(z(), wm())),
                ); // |- -.-.H
                // A -> ( M0 -> ( -.-.H ) ) by a1i x2
                let nnH_AM0 = a1i(
                    imp(m0(), n(n(le(z(), wm())))),
                    aA(),
                    a1i(n(n(le(z(), wm()))), m0(), nnH),
                );
                // mpd at consequent level: combine step with nnH_AM0
                // step : A -> ( M0 -> ( -.-.H -> -.NB ) )
                // nnH_AM0 : A -> ( M0 -> -.-.H )
                // want A -> ( M0 -> -.NB ).  Use mpd nested:
                //   inner mpd over (M0): treat A as carried by syld? Use
                //   `mpd` with ph=A? No — the implication chain is 3-deep.
                //   Flatten: com12 to expose; simpler: do two-level mpd.
                // First combine over the innermost using a helper:
                //   from ( P -> ( Q -> R ) ) and ( P -> Q ) get ( P -> R )
                //   with P:=(A) carrying (M0->...) as Q? Not matching.
                // Use: at A-level, ps:=M0, treat ch:=-.-.H, th:=-.NB :
                //   need A->(M0->(-.-.H))  [nnH_AM0]  and
                //        A->(M0->((-.-.H)-> -.NB)) [step].
                //   mpd-for-deductions over (A) with the (M0->) layer:
                //   that's exactly `mpd` if ph=A, ps=M0?? mpd needs
                //   (ph->ps) and (ph->(ps->ch)).  Here ph=A, ps=M0,
                //   ch=??? but we have nested (M0->(-.-.H)) not (A->M0).
                //   So instead set ph:=(A and we already inside)...
                // Cleanest: strip A by com12 later; first prove the
                //   M0-level fact under a *generic* A by `com12`.
                // Re-derive R directly as ( M0 -> ( A -> 0<_m ) ) using
                //   com12 on a ( A -> ( M0 -> 0<_m ) ).  Build the latter
                //   by `mpd` with ph=A treating (M0->...) atomically is
                //   wrong.  Use the 2-arg deduction `mpd` after `com12`
                //   to move M0 outward:
                let step_c = com12(
                    aA(),
                    m0(),
                    imp(n(n(le(z(), wm()))), n(nb())),
                    step,
                ); // M0 -> ( A -> ( -.-.H -> -.NB ) )
                let nnH_c = com12(
                    aA(),
                    m0(),
                    n(n(le(z(), wm()))),
                    nnH_AM0,
                ); // M0 -> ( A -> -.-.H )
                // now mpd at (M0)-level with ph=M0, ps=A? still nested.
                // Apply `mpd` with ph=M0, ps=A, ch=( -.-.H -> -.NB )? we
                // have M0->(A->(-.-.H-> -.NB)) and M0->(A-> -.-.H).
                // Use syld: ph=M0,ps=A,ch=-.-.H,th=-.NB needs
                //   M0->(A-> -.-.H)  and  M0->(-.-.H -> -.NB)?? mismatch.
                // Use the combinator: from M0->(A->(C->D)) and M0->(A->C)
                //   get M0->(A->D) by two nested mpd.  Implement via a
                //   small closed lemma using ax-2 twice:
                let two_mpd = |pp: Pt, qq: Pt, cc: Pt, dd: Pt, f_cd: Pt, f_c: Pt| -> Pt {
                    // f_cd: P->(Q->(C->D)), f_c: P->(Q->C)  => P->(Q->D)
                    // ax-2 inner: (Q->(C->D))->((Q->C)->(Q->D))
                    let ax2i = el
                        .app(
                            "ax-2",
                            &[("ph", qq.clone()), ("ps", cc.clone()), ("ch", dd.clone())],
                            &[],
                        )
                        .unwrap();
                    // P->((Q->C)->(Q->D))
                    let t = syl(
                        pp.clone(),
                        imp(qq.clone(), imp(cc.clone(), dd.clone())),
                        imp(imp(qq.clone(), cc.clone()), imp(qq.clone(), dd.clone())),
                        f_cd,
                        ax2i,
                    );
                    // mpd: P->(Q->C) [f_c], P->((Q->C)->(Q->D)) [t]
                    mpd(
                        pp,
                        imp(qq.clone(), cc.clone()),
                        imp(qq.clone(), dd.clone()),
                        f_c,
                        t,
                    )
                };
                two_mpd(
                    m0(),
                    aA(),
                    n(n(le(z(), wm()))),
                    n(nb()),
                    step_c,
                    nnH_c,
                ) // M0 -> ( A -> -.NB )
            };
            // -.NB = -.-.(0<_m) ; notnot2 -> (0<_m)
            // r_negnb : M0 -> ( A -> -.-.(0<_m) )
            let br2 = {
                let nn2m = nn2(le(z(), m())); // ( -.-.(0<_m) -> (0<_m) )
                // M0 -> ( A -> (0<_m) )
                imim(
                    m0(),
                    aA(),
                    n(nb()),
                    le(z(), m()),
                    r_negnb,
                    nn2m,
                )
            }; // ( M0 -> ( A -> (0<_m) ) )

            // br1 : ( (0<_m) -> ( A -> (0<_m) ) )  = ax-1
            let br1 = el
                .app("ax-1", &[("ph", le(z(), m())), ("ps", aA())], &[])
                .unwrap();
            // jaoi(br1,br2) on tot : ( ((0<_m)\/(m<_0)) -> ( A -> (0<_m) ) )
            let jao = el
                .app(
                    "jaoi",
                    &[
                        ("ph", le(z(), m())),
                        ("ps", m0()),
                        ("ch", imp(aA(), le(z(), m()))),
                    ],
                    &[br1, br2],
                )
                .unwrap();
            let g = mp(
                ow(le(z(), m()), m0()),
                imp(aA(), le(z(), m())),
                tot,
                jao,
            ); // |- ( A -> (0<_m) )  = ( (0<w) -> (0<_m) )
            Lemma {
                name: "lecpos".into(),
                ess: vec![(
                    "lecpos.1".into(),
                    toks(&[
                        "|-", "(", "0", "<_", "(", "w", "*", "t", ")", ")",
                    ]),
                )],
                goal: g,
            }
        }

        // ============================================================
        // idx 1 : addz   0<=a , 0<=b , (a+b)=0  =>  a=0
        // ============================================================
        1 => {
            let av = || leaf("va");
            let bv = || leaf("vb");
            let leadd = el
                .app("of-leadd", &[("u", z()), ("v", bv()), ("w", av())], &[])
                .unwrap(); // ( (0<_b) -> ( (0+a) <_ (b+a) ) )
            let step = mp(
                le(z(), bv()),
                le(pl(el, z(), av()), pl(el, bv(), av())),
                leaf("addz.2"),
                leadd,
            );
            let zpa = ring_eq(el, &pl(el, z(), av()), &av()); // (0+a)=a
            let bpa = ring_eq(el, &pl(el, bv(), av()), &pl(el, av(), bv())); // (b+a)=(a+b)
            let bpa0 = eqtr3(
                el,
                pl(el, bv(), av()),
                pl(el, av(), bv()),
                z(),
                bpa,
                leaf("addz.3"),
            ); // ( (b+a)=0 )
            let cl1 = el
                .app(
                    "cong-le1",
                    &[
                        ("a", pl(el, z(), av())),
                        ("b", av()),
                        ("c", pl(el, bv(), av())),
                    ],
                    &[],
                )
                .unwrap();
            let s_a = mp(
                eq(pl(el, z(), av()), av()),
                imp(
                    le(pl(el, z(), av()), pl(el, bv(), av())),
                    le(av(), pl(el, bv(), av())),
                ),
                zpa,
                cl1,
            );
            let a_le_bpa = mp(
                le(pl(el, z(), av()), pl(el, bv(), av())),
                le(av(), pl(el, bv(), av())),
                step,
                s_a,
            );
            let cl2 = el
                .app(
                    "cong-le2",
                    &[("a", pl(el, bv(), av())), ("b", z()), ("c", av())],
                    &[],
                )
                .unwrap();
            let s_b = mp(
                eq(pl(el, bv(), av()), z()),
                imp(le(av(), pl(el, bv(), av())), le(av(), z())),
                bpa0,
                cl2,
            );
            let a_le_0 = mp(
                le(av(), pl(el, bv(), av())),
                le(av(), z()),
                a_le_bpa,
                s_b,
            );
            let g = el
                .app("lecon", &[("u", av())], &[leaf("addz.1"), a_le_0])
                .unwrap();
            Lemma {
                name: "addz".into(),
                ess: vec![
                    ("addz.1".into(), toks(&["|-", "(", "0", "<_", "a", ")"])),
                    ("addz.2".into(), toks(&["|-", "(", "0", "<_", "b", ")"])),
                    (
                        "addz.3".into(),
                        toks(&["|-", "(", "a", "+", "b", ")", "=", "0"]),
                    ),
                ],
                goal: g,
            }
        }

        // ============================================================
        // idx 2 : g3a-gsplit — generic degree-4 split identity. Lets G3a
        // factor the would-be degree-8 null_id without ever handing the
        // normaliser anything past degree 4: proven over fresh term atoms
        // a,b,c,e,f,g, then instantiated with the big subterms by
        // substitution (no re-expansion).
        //   (a·a)(e·f) − (b·b)(e·g) = e·( a·(a·f − b·c) + b·(a·c − b·g) )
        // ============================================================
        2 => {
            let v = |s: &str| leaf(s);
            let (a, b, c, e, f, g) = (v("va"), v("vb"), v("vc"), v("ve"), v("vf"), v("vg"));
            let lhs = mi(
                el,
                mu(el, mu(el, a.clone(), a.clone()), mu(el, e.clone(), f.clone())),
                mu(el, mu(el, b.clone(), b.clone()), mu(el, e.clone(), g.clone())),
            );
            let rhs = mu(
                el,
                e.clone(),
                pl(
                    el,
                    mu(
                        el,
                        a.clone(),
                        mi(el, mu(el, a.clone(), f.clone()), mu(el, b.clone(), c.clone())),
                    ),
                    mu(
                        el,
                        b.clone(),
                        mi(el, mu(el, a.clone(), c.clone()), mu(el, b.clone(), g.clone())),
                    ),
                ),
            );
            return Lemma {
                name: "g3a-gsplit".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 3 : g3a-gfac — generic degree-4 factor-out identity:
        //   e·( a·(f·w) + b·(g·w) ) = ( e·( a·f + b·g ) )·w
        // ============================================================
        3 => {
            let v = |s: &str| leaf(s);
            let (a, b, e, f, g, w) = (v("va"), v("vb"), v("ve"), v("vf"), v("vg"), v("vw"));
            let lhs = mu(
                el,
                e.clone(),
                pl(
                    el,
                    mu(el, a.clone(), mu(el, f.clone(), w.clone())),
                    mu(el, b.clone(), mu(el, g.clone(), w.clone())),
                ),
            );
            let rhs = mu(
                el,
                mu(
                    el,
                    e.clone(),
                    pl(el, mu(el, a.clone(), f.clone()), mu(el, b.clone(), g.clone())),
                ),
                w.clone(),
            );
            return Lemma {
                name: "g3a-gfac".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 4 : g3a-plk — generic 2D Plücker/Lagrange identity, proven
        // once over fresh component atoms a..p and instantiated so G3a
        // does ZERO per-instance ring_eq:
        //   (A·C)(B·D) − (A·D)(B·C) = (0 − X(A,B))·X(D,C)
        // with A=(a,b) B=(c,e) C=(f,g) D=(o,p), X(U,V)=Ux·Vy − Uy·Vx.
        // ============================================================
        4 => {
            let v = |s: &str| leaf(s);
            let (a, b, c, e, f, g, o, p) = (
                v("va"), v("vb"), v("vc"), v("ve"),
                v("vf"), v("vg"), v("vo"), v("vp"),
            );
            let dot2 = |x1: &Pt, y1: &Pt, x2: &Pt, y2: &Pt| {
                pl(el, mu(el, x1.clone(), x2.clone()), mu(el, y1.clone(), y2.clone()))
            };
            let cross2 = |x1: &Pt, y1: &Pt, x2: &Pt, y2: &Pt| {
                mi(el, mu(el, x1.clone(), y2.clone()), mu(el, y1.clone(), x2.clone()))
            };
            // (A·C)(B·D) -x (A·D)(B·C)
            let lhs = mi(
                el,
                mu(el, dot2(&a, &b, &f, &g), dot2(&c, &e, &o, &p)),
                mu(el, dot2(&a, &b, &o, &p), dot2(&c, &e, &f, &g)),
            );
            // ( 0 -x X(A,B) ) · X(D,C)      [ X(D,C) = o·g -x p·f ]
            let xab = cross2(&a, &b, &c, &e); // a·e -x b·c
            let xdc = mi(el, mu(el, o.clone(), g.clone()), mu(el, p.clone(), f.clone()));
            let rhs = mu(el, mi(el, z(), xab), xdc);
            return Lemma {
                name: "g3a-plk".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 5 : g3a-gsplit2 — SGN-conjunct split (generic, degree-3):
        //   (a·b)(e+f) − ( c·(b·b) + c·(a·a) )
        //     = b·(a·e − b·c) − a·(a·c − b·f)
        // (the bracketed factors are exactly plkA's k1 and plkB's k2)
        // ============================================================
        5 => {
            let v = |s: &str| leaf(s);
            let (a, b, c, e, f) = (v("va"), v("vb"), v("vc"), v("ve"), v("vf"));
            let lhs = mi(
                el,
                mu(el, mu(el, a.clone(), b.clone()), pl(el, e.clone(), f.clone())),
                pl(
                    el,
                    mu(el, c.clone(), mu(el, b.clone(), b.clone())),
                    mu(el, c.clone(), mu(el, a.clone(), a.clone())),
                ),
            );
            let rhs = mi(
                el,
                mu(
                    el,
                    b.clone(),
                    mi(el, mu(el, a.clone(), e.clone()), mu(el, b.clone(), c.clone())),
                ),
                mu(
                    el,
                    a.clone(),
                    mi(el, mu(el, a.clone(), c.clone()), mu(el, b.clone(), f.clone())),
                ),
            );
            return Lemma {
                name: "g3a-gsplit2".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 6 : g3a-gfac2 — SGN factor-out (generic, degree-3):
        //   b·(f·w) − a·(g·w) = ( b·f − a·g )·w
        // ============================================================
        6 => {
            let v = |s: &str| leaf(s);
            let (a, b, f, g, w) = (v("va"), v("vb"), v("vf"), v("vg"), v("vw"));
            let lhs = mi(
                el,
                mu(el, b.clone(), mu(el, f.clone(), w.clone())),
                mu(el, a.clone(), mu(el, g.clone(), w.clone())),
            );
            let rhs = mu(
                el,
                mi(el, mu(el, b.clone(), f.clone()), mu(el, a.clone(), g.clone())),
                w.clone(),
            );
            return Lemma {
                name: "g3a-gfac2".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 7 : G3a-rayangle   ( Ray a c x ) => ( ACong a b x a b c )
        // ============================================================
        7 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let pc = || leaf("vc");
            let px = || leaf("vx");
            let xa = || xc(pa());
            let ya = || yc(pa());
            let xb = || xc(pb());
            let yb = || yc(pb());
            let xcc = || xc(pc());
            let ycc = || yc(pc());
            let xx = || xc(px());
            let yx = || yc(px());
            let pX = || mi(el, xcc(), xa());
            let qY = || mi(el, ycc(), ya());
            let rX = || mi(el, xx(), xa());
            let sY = || mi(el, yx(), ya());
            let uX = || mi(el, xb(), xa());
            let vY = || mi(el, yb(), ya());
            let bx_c = || pl(el, mu(el, uX(), rX()), mu(el, vY(), sY()));
            let bc_c = || pl(el, mu(el, uX(), pX()), mu(el, vY(), qY()));
            let cc_c = || pl(el, mu(el, pX(), rX()), mu(el, qY(), sY()));
            let sb_c = || pl(el, mu(el, uX(), uX()), mu(el, vY(), vY()));
            let sc_c = || pl(el, mu(el, pX(), pX()), mu(el, qY(), qY()));
            let sx_c = || pl(el, mu(el, rX(), rX()), mu(el, sY(), sY()));
            let dot = |o: Pt, p: Pt, q: Pt| {
                el.app("tdot", &[("o", o), ("p", p), ("q", q)], &[]).unwrap()
            };
            let sqd = |a: Pt, b: Pt| el.app("tsqd", &[("a", a), ("b", b)], &[]).unwrap();
            // ( X * 0 ) = 0   (ring_eq does NOT collapse X*0; via of-mulcom+mul0)
            let mul0r = |t: Pt| -> Pt {
                let comm = el
                    .app("of-mulcom", &[("u", t.clone()), ("v", z())], &[])
                    .unwrap(); // ( (t*0) = (0*t) )
                let m0l = el.app("mul0", &[("u", t.clone())], &[]).unwrap(); // ( (0*t)=0 )
                eqtr3(el, mu(el, t.clone(), z()), mu(el, z(), t.clone()), z(), comm, m0l)
            };
            let dabx = || dot(pa(), pb(), px());
            let dabc = || dot(pa(), pb(), pc());
            let dacx = || dot(pa(), pc(), px());
            let sab = || sqd(pa(), pb());
            let sac = || sqd(pa(), pc());
            let sax = || sqd(pa(), px());

            // ---- 1. unfold Ray hypothesis ----
            let ray = el
                .app("wray", &[("a", pa()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let coll = el
                .app("wcoll", &[("a", pa()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let dacx_sgn = le(z(), dacx());
            let conj_r = aw(coll.clone(), dacx_sgn.clone());
            let dfray = el
                .app("df-ray", &[("a", pa()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let coll_and = el.bi_fwd(dfray, leaf("g3a.1")).unwrap();
            let coll_pf = mp(
                conj_r.clone(),
                coll.clone(),
                coll_and.clone(),
                el.app(
                    "simpl",
                    &[("ph", coll.clone()), ("ps", dacx_sgn.clone())],
                    &[],
                )
                .unwrap(),
            );
            let dacx_pf = mp(
                conj_r.clone(),
                dacx_sgn.clone(),
                coll_and,
                el.app(
                    "simpr",
                    &[("ph", coll.clone()), ("ps", dacx_sgn.clone())],
                    &[],
                )
                .unwrap(),
            );

            // ---- 2. df-coll -> ( Dl -x Dr ) = 0 ----
            let d_l = mu(el, pX(), sY());
            let d_r = mu(el, qY(), rX());
            let dfcoll = el
                .app("df-coll", &[("a", pa()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let coll_eq = el.bi_fwd(dfcoll, coll_pf).unwrap(); // ( Dl = Dr )
            let cmi1d = el
                .app(
                    "cong-mi1",
                    &[("a", d_l.clone()), ("b", d_r.clone()), ("c", d_r.clone())],
                    &[],
                )
                .unwrap();
            let dl_dr = mp(
                eq(d_l.clone(), d_r.clone()),
                eq(
                    mi(el, d_l.clone(), d_r.clone()),
                    mi(el, d_r.clone(), d_r.clone()),
                ),
                coll_eq,
                cmi1d,
            );
            eprintln!("    [g3a] cp2: drdr0 ring_eq");
            let drdr0 = ring_eq(el, &mi(el, d_r.clone(), d_r.clone()), &z());
            let deq0 = eqtr3(
                el,
                mi(el, d_l.clone(), d_r.clone()),
                mi(el, d_r.clone(), d_r.clone()),
                z(),
                dl_dr,
                drdr0,
            ); // ( (Dl-xDr) = 0 )
            let dexpr = || mi(el, d_l.clone(), d_r.clone());

            // ---- 3. EQ conjunct ----
            let eql_g = mu(el, mu(el, dabx(), dabx()), mu(el, sab(), sac()));
            let eqr_g = mu(el, mu(el, dabc(), dabc()), mu(el, sab(), sax()));
            let e_dabx = el
                .app("df-dot", &[("o", pa()), ("p", pb()), ("q", px())], &[])
                .unwrap();
            let e_dabc = el
                .app("df-dot", &[("o", pa()), ("p", pb()), ("q", pc())], &[])
                .unwrap();
            let e_dacx = el
                .app("df-dot", &[("o", pa()), ("p", pc()), ("q", px())], &[])
                .unwrap();
            let e_sab = el.app("df-sqd", &[("a", pa()), ("b", pb())], &[]).unwrap();
            let e_sac = el.app("df-sqd", &[("a", pa()), ("b", pc())], &[]).unwrap();
            let e_sax = el.app("df-sqd", &[("a", pa()), ("b", px())], &[]).unwrap();
            let mu_rw = |l: Pt, lp: Pt, r: Pt, rp: Pt, pl_eq: Pt, pr_eq: Pt| -> Pt {
                let c1 = cmu1(el, l.clone(), lp.clone(), r.clone(), pl_eq);
                let c2 = cmu2(el, r.clone(), rp.clone(), lp.clone(), pr_eq);
                eqtr3(
                    el,
                    mu(el, l.clone(), r.clone()),
                    mu(el, lp.clone(), r.clone()),
                    mu(el, lp.clone(), rp.clone()),
                    c1,
                    c2,
                )
            };
            let dd_x = mu_rw(
                dabx(),
                bx_c(),
                dabx(),
                bx_c(),
                e_dabx.clone(),
                e_dabx.clone(),
            );
            let ss_lc = mu_rw(
                sab(),
                sb_c(),
                sac(),
                sc_c(),
                e_sab.clone(),
                e_sac.clone(),
            );
            let eql_coord = mu_rw(
                mu(el, dabx(), dabx()),
                mu(el, bx_c(), bx_c()),
                mu(el, sab(), sac()),
                mu(el, sb_c(), sc_c()),
                dd_x,
                ss_lc,
            );
            let dd_c = mu_rw(
                dabc(),
                bc_c(),
                dabc(),
                bc_c(),
                e_dabc.clone(),
                e_dabc.clone(),
            );
            let ss_rc = mu_rw(
                sab(),
                sb_c(),
                sax(),
                sx_c(),
                e_sab.clone(),
                e_sax.clone(),
            );
            let eqr_coord = mu_rw(
                mu(el, dabc(), dabc()),
                mu(el, bc_c(), bc_c()),
                mu(el, sab(), sax()),
                mu(el, sb_c(), sx_c()),
                dd_c,
                ss_rc,
            );
            let eql_cv = mu(el, mu(el, bx_c(), bx_c()), mu(el, sb_c(), sc_c()));
            let eqr_cv = mu(el, mu(el, bc_c(), bc_c()), mu(el, sb_c(), sx_c()));
            // ---- Plücker factoring: never hand the normaliser anything
            // past degree 4.  X(U,P), X(U,R); DE = X(P,R) = dexpr().
            let xup = mi(el, mu(el, uX(), qY()), mu(el, vY(), pX())); // X(U,P)
            let xur = mi(el, mu(el, uX(), sY()), mu(el, vY(), rX())); // X(U,R)
            let nxup = mi(el, z(), xup.clone()); // 0 - X(U,P)
            let nxur = mi(el, z(), xur.clone()); // 0 - X(U,R)
            let de = || dexpr(); // = X(P,R)
            // K1 = BX·SC - BC·CC ,  K2 = BX·CC - BC·SX
            let k1 = mi(el, mu(el, bx_c(), sc_c()), mu(el, bc_c(), cc_c()));
            let k2 = mi(el, mu(el, bx_c(), cc_c()), mu(el, bc_c(), sx_c()));
            let k1p = mu(el, nxup.clone(), de()); // (0-XUP)·DE
            let k2p = mu(el, nxur.clone(), de()); // (0-XUR)·DE
            // plkA: instantiate generic g3a-plk with A=U,B=P,C=R,D=P.
            // Verified: LHS ≡ k1 and RHS ≡ k1p exactly (no bridge needed).
            eprintln!("    [g3a] cp3a: plkA = g3a-plk instantiation");
            let plka = el
                .app(
                    "g3a-plk",
                    &[
                        ("a", uX()), ("b", vY()), ("c", pX()), ("e", qY()),
                        ("f", rX()), ("g", sY()), ("o", pX()), ("p", qY()),
                    ],
                    &[],
                )
                .unwrap(); // k1 = k1p
            // plkB: g3a-plk with A=U,B=R,C=R,D=P gives k2_plk = k2p, where
            // k2_plk differs from k2 only in the P·R factor's mul order
            // (Plücker forces R·P shape) — bridge via two of-mulcom.
            eprintln!("    [g3a] cp3b: plkB = g3a-plk + comm bridge");
            let plkb_raw = el
                .app(
                    "g3a-plk",
                    &[
                        ("a", uX()), ("b", vY()), ("c", rX()), ("e", sY()),
                        ("f", rX()), ("g", sY()), ("o", pX()), ("p", qY()),
                    ],
                    &[],
                )
                .unwrap(); // k2_plk = k2p
            let rps = pl(el, mu(el, rX(), pX()), mu(el, sY(), qY())); // R·P shape
            let k2_plk = mi(el, mu(el, bx_c(), rps.clone()), mu(el, bc_c(), sx_c()));
            // cc_c = rps  (commute each addend's product)
            let comm1 = el
                .app("of-mulcom", &[("u", pX()), ("v", rX())], &[])
                .unwrap(); // (pX·rX)=(rX·pX)
            let comm2 = el
                .app("of-mulcom", &[("u", qY()), ("v", sY())], &[])
                .unwrap(); // (qY·sY)=(sY·qY)
            let cc_step1 = cpl1(
                el,
                mu(el, pX(), rX()),
                mu(el, rX(), pX()),
                mu(el, qY(), sY()),
                comm1,
            ); // (pX·rX + qY·sY) = (rX·pX + qY·sY)
            let cc_step2 = cpl2(
                el,
                mu(el, qY(), sY()),
                mu(el, sY(), qY()),
                mu(el, rX(), pX()),
                comm2,
            ); // (rX·pX + qY·sY) = (rX·pX + sY·qY)
            let cc_eq_rps = eqtr3(
                el,
                cc_c(),
                pl(el, mu(el, rX(), pX()), mu(el, qY(), sY())),
                rps.clone(),
                cc_step1,
                cc_step2,
            ); // cc_c = rps
            let mu_eq = cmu2(el, cc_c(), rps.clone(), bx_c(), cc_eq_rps); // (bx_c·cc_c)=(bx_c·rps)
            let k2_eq_k2plk = cmi1(
                el,
                mu(el, bx_c(), cc_c()),
                mu(el, bx_c(), rps.clone()),
                mu(el, bc_c(), sx_c()),
                mu_eq,
            ); // k2 = k2_plk
            let plkb = eqtr3(el, k2.clone(), k2_plk, k2p.clone(), k2_eq_k2plk, plkb_raw); // k2 = k2p
            // gsplit instantiated: ( eql_cv -x eqr_cv ) = SB·( BX·K1 + BC·K2 )
            eprintln!("    [g3a] cp3c: instantiate gsplit");
            let gsplit = el
                .app(
                    "g3a-gsplit",
                    &[
                        ("a", bx_c()),
                        ("b", bc_c()),
                        ("c", cc_c()),
                        ("e", sb_c()),
                        ("f", sc_c()),
                        ("g", sx_c()),
                    ],
                    &[],
                )
                .unwrap();
            let g1rhs = mu(
                el,
                sb_c(),
                pl(
                    el,
                    mu(el, bx_c(), k1.clone()),
                    mu(el, bc_c(), k2.clone()),
                ),
            );
            // Rrw : g1rhs = SB·( BX·K1' + BC·K2' )  via plkA/plkB congruence
            let r1 = cmu2(el, k1.clone(), k1p.clone(), bx_c(), plka.clone()); // (BX·K1)=(BX·K1')
            let r2 = cmu2(el, k2.clone(), k2p.clone(), bc_c(), plkb.clone()); // (BC·K2)=(BC·K2')
            let inner_l = pl(el, mu(el, bx_c(), k1.clone()), mu(el, bc_c(), k2.clone()));
            let inner_m = pl(el, mu(el, bx_c(), k1p.clone()), mu(el, bc_c(), k2.clone()));
            let inner_r = pl(el, mu(el, bx_c(), k1p.clone()), mu(el, bc_c(), k2p.clone()));
            let ce1 = cpl1(
                el,
                mu(el, bx_c(), k1.clone()),
                mu(el, bx_c(), k1p.clone()),
                mu(el, bc_c(), k2.clone()),
                r1,
            ); // inner_l = inner_m
            let ce2 = cpl2(
                el,
                mu(el, bc_c(), k2.clone()),
                mu(el, bc_c(), k2p.clone()),
                mu(el, bx_c(), k1p.clone()),
                r2,
            ); // inner_m = inner_r
            let inner_eq =
                eqtr3(el, inner_l.clone(), inner_m, inner_r.clone(), ce1, ce2);
            let rrw = cmu2(el, inner_l.clone(), inner_r.clone(), sb_c(), inner_eq); // g1rhs = rhs'
            let rhsp = mu(el, sb_c(), inner_r.clone());
            // gfac instantiated: rhs' = ( SB·( BX·(0-XUP) + BC·(0-XUR) ) )·DE
            eprintln!("    [g3a] cp3d: instantiate gfac");
            let cof = mu(
                el,
                sb_c(),
                pl(
                    el,
                    mu(el, bx_c(), nxup.clone()),
                    mu(el, bc_c(), nxur.clone()),
                ),
            );
            let gfac = el
                .app(
                    "g3a-gfac",
                    &[
                        ("e", sb_c()),
                        ("a", bx_c()),
                        ("f", nxup.clone()),
                        ("w", de()),
                        ("b", bc_c()),
                        ("g", nxur.clone()),
                    ],
                    &[],
                )
                .unwrap(); // rhs' = cof·DE
            // chain: (eql_cv -x eqr_cv) = g1rhs = rhs' = cof·DE
            let t1 = eqtr3(
                el,
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                g1rhs.clone(),
                rhsp.clone(),
                gsplit,
                rrw,
            );
            let null_id = eqtr3(
                el,
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                rhsp,
                mu(el, cof.clone(), de()),
                t1,
                gfac,
            );
            let cof_d0 = cmu2(el, dexpr(), z(), cof.clone(), deq0.clone());
            let cofz = mul0r(cof.clone());
            let cof_d_z = eqtr3(
                el,
                mu(el, cof.clone(), dexpr()),
                mu(el, cof.clone(), z()),
                z(),
                cof_d0,
                cofz,
            );
            let eqdiff0 = eqtr3(
                el,
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                mu(el, cof.clone(), dexpr()),
                z(),
                null_id,
                cof_d_z,
            );
            let eqcv = mp(
                eq(mi(el, eql_cv.clone(), eqr_cv.clone()), z()),
                eq(eql_cv.clone(), eqr_cv.clone()),
                eqdiff0,
                el.app(
                    "subeq0",
                    &[("u", eql_cv.clone()), ("v", eqr_cv.clone())],
                    &[],
                )
                .unwrap(),
            );
            let eqr_cv_to = eqcomm(el, eqr_g.clone(), eqr_cv.clone(), eqr_coord);
            let eq_step = eqtr3(
                el,
                eql_g.clone(),
                eql_cv.clone(),
                eqr_cv.clone(),
                eql_coord,
                eqcv,
            );
            let eq_pf = eqtr3(
                el,
                eql_g.clone(),
                eqr_cv.clone(),
                eqr_g.clone(),
                eq_step,
                eqr_cv_to,
            ); // |- ( EQ_l = EQ_r )

            eprintln!("    [g3a] cp4: SGN conjunct start (null_id done)");
            // ---- 4. SGN conjunct : 0 <_ ( dabx * dabc ) ----
            let c_le0 = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[("a", dacx()), ("b", cc_c()), ("c", z())],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(dacx(), cc_c()),
                    imp(le(z(), dacx()), le(z(), cc_c())),
                    e_dacx.clone(),
                    cl2,
                );
                mp(le(z(), dacx()), le(z(), cc_c()), dacx_pf, m1)
            }; // |- 0<_C
            let bxbc = || mu(el, bx_c(), bc_c());
            let n_sum = || pl(el, sc_c(), sx_c());
            let rhs_n = pl(
                el,
                mu(el, cc_c(), mu(el, bc_c(), bc_c())),
                mu(el, cc_c(), mu(el, bx_c(), bx_c())),
            );
            // n_null by the SAME Plücker template as null_id, reusing the
            // already-built plka (k1=k1p) and plkb (k2=k2p):
            //   bxbc·n_sum − rhs_n  =  BC·k1 − BX·k2  (g3a-gsplit2)
            //                       =  BC·k1p − BX·k2p (plka/plkb congr)
            //                       =  lamn·DE         (g3a-gfac2)
            eprintln!("    [g3a] cp4b: n_null via gsplit2/gfac2 (no ring_eq)");
            let lamn = mi(
                el,
                mu(el, bc_c(), nxup.clone()),
                mu(el, bx_c(), nxur.clone()),
            );
            let s2 = el
                .app(
                    "g3a-gsplit2",
                    &[
                        ("a", bx_c()), ("b", bc_c()), ("c", cc_c()),
                        ("e", sc_c()), ("f", sx_c()),
                    ],
                    &[],
                )
                .unwrap(); // mi(mu(bxbc,n_sum),rhs_n) = mi(mu(bc_c,k1),mu(bx_c,k2))
            let s2_rhs = mi(
                el,
                mu(el, bc_c(), k1.clone()),
                mu(el, bx_c(), k2.clone()),
            );
            let s2_rhsp = mi(
                el,
                mu(el, bc_c(), k1p.clone()),
                mu(el, bx_c(), k2p.clone()),
            );
            let nr1 = cmu2(el, k1.clone(), k1p.clone(), bc_c(), plka.clone()); // (bc_c·k1)=(bc_c·k1p)
            let nr2 = cmu2(el, k2.clone(), k2p.clone(), bx_c(), plkb.clone()); // (bx_c·k2)=(bx_c·k2p)
            let nstep1 = cmi1(
                el,
                mu(el, bc_c(), k1.clone()),
                mu(el, bc_c(), k1p.clone()),
                mu(el, bx_c(), k2.clone()),
                nr1,
            ); // s2_rhs = mi(mu(bc_c,k1p),mu(bx_c,k2))
            let nstep2 = cmi2(
                el,
                mu(el, bx_c(), k2.clone()),
                mu(el, bx_c(), k2p.clone()),
                mu(el, bc_c(), k1p.clone()),
                nr2,
            ); // = s2_rhsp
            let nrrw = eqtr3(
                el,
                s2_rhs.clone(),
                mi(el, mu(el, bc_c(), k1p.clone()), mu(el, bx_c(), k2.clone())),
                s2_rhsp.clone(),
                nstep1,
                nstep2,
            ); // s2_rhs = s2_rhsp
            let gfac2 = el
                .app(
                    "g3a-gfac2",
                    &[
                        ("a", bx_c()), ("b", bc_c()),
                        ("f", nxup.clone()), ("g", nxur.clone()), ("w", de()),
                    ],
                    &[],
                )
                .unwrap(); // s2_rhsp = lamn·DE
            let n_lhs = mi(el, mu(el, bxbc(), n_sum()), rhs_n.clone());
            let n_t1 = eqtr3(el, n_lhs.clone(), s2_rhs, s2_rhsp.clone(), s2, nrrw);
            let n_null = eqtr3(
                el,
                n_lhs,
                s2_rhsp,
                mu(el, lamn.clone(), de()),
                n_t1,
                gfac2,
            );
            let lamn_d0 = cmu2(el, dexpr(), z(), lamn.clone(), deq0.clone());
            let lamnz = mul0r(lamn.clone());
            let lamn_d_z = eqtr3(
                el,
                mu(el, lamn.clone(), dexpr()),
                mu(el, lamn.clone(), z()),
                z(),
                lamn_d0,
                lamnz,
            );
            let ndiff0 = eqtr3(
                el,
                mi(el, mu(el, bxbc(), n_sum()), rhs_n.clone()),
                mu(el, lamn.clone(), dexpr()),
                z(),
                n_null,
                lamn_d_z,
            );
            let n_eq = mp(
                eq(mi(el, mu(el, bxbc(), n_sum()), rhs_n.clone()), z()),
                eq(mu(el, bxbc(), n_sum()), rhs_n.clone()),
                ndiff0,
                el.app(
                    "subeq0",
                    &[
                        ("u", mu(el, bxbc(), n_sum())),
                        ("v", rhs_n.clone()),
                    ],
                    &[],
                )
                .unwrap(),
            ); // |- ( (Bx*Bc)*(Sc+Sx) = rhs_n )
            // rhs_n >= 0
            let cbc = {
                let sq = el.app("of-sqpos", &[("u", bc_c())], &[]).unwrap();
                let lm = el
                    .app(
                        "lemul02",
                        &[("u", cc_c()), ("v", mu(el, bc_c(), bc_c()))],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    le(z(), cc_c()),
                    imp(
                        le(z(), mu(el, bc_c(), bc_c())),
                        le(z(), mu(el, cc_c(), mu(el, bc_c(), bc_c()))),
                    ),
                    c_le0.clone(),
                    lm,
                );
                mp(
                    le(z(), mu(el, bc_c(), bc_c())),
                    le(z(), mu(el, cc_c(), mu(el, bc_c(), bc_c()))),
                    sq,
                    m1,
                )
            };
            let cbx = {
                let sq = el.app("of-sqpos", &[("u", bx_c())], &[]).unwrap();
                let lm = el
                    .app(
                        "lemul02",
                        &[("u", cc_c()), ("v", mu(el, bx_c(), bx_c()))],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    le(z(), cc_c()),
                    imp(
                        le(z(), mu(el, bx_c(), bx_c())),
                        le(z(), mu(el, cc_c(), mu(el, bx_c(), bx_c()))),
                    ),
                    c_le0.clone(),
                    lm,
                );
                mp(
                    le(z(), mu(el, bx_c(), bx_c())),
                    le(z(), mu(el, cc_c(), mu(el, bx_c(), bx_c()))),
                    sq,
                    m1,
                )
            };
            let rhsn_pos = el
                .app(
                    "le0add",
                    &[
                        ("u", mu(el, cc_c(), mu(el, bc_c(), bc_c()))),
                        ("v", mu(el, cc_c(), mu(el, bx_c(), bx_c()))),
                    ],
                    &[cbc, cbx],
                )
                .unwrap();
            let n_eq_c = eqcomm(el, mu(el, bxbc(), n_sum()), rhs_n.clone(), n_eq);
            let lhsn_pos = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            ("a", rhs_n.clone()),
                            ("b", mu(el, bxbc(), n_sum())),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(rhs_n.clone(), mu(el, bxbc(), n_sum())),
                    imp(
                        le(z(), rhs_n.clone()),
                        le(z(), mu(el, bxbc(), n_sum())),
                    ),
                    n_eq_c,
                    cl2,
                );
                mp(
                    le(z(), rhs_n.clone()),
                    le(z(), mu(el, bxbc(), n_sum())),
                    rhsn_pos,
                    m1,
                )
            }; // |- 0<_( (Bx*Bc)*(Sc+Sx) )
            // commute to 0<_( (Sc+Sx)*(Bx*Bc) ) for lecpos (ess 0<=(w*m), w=N)
            let lhsn_nm = {
                // pure commutativity — one axiom on opaque subterms, not a
                // degree-high coordinate ring_eq.
                eprintln!("    [g3a] cp4c: comm_r = of-mulcom (no ring_eq)");
                let comm_r = el
                    .app("of-mulcom", &[("u", bxbc()), ("v", n_sum())], &[])
                    .unwrap(); // ((Bx*Bc)*N)=(N*(Bx*Bc))
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            ("a", mu(el, bxbc(), n_sum())),
                            ("b", mu(el, n_sum(), bxbc())),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(mu(el, bxbc(), n_sum()), mu(el, n_sum(), bxbc())),
                    imp(
                        le(z(), mu(el, bxbc(), n_sum())),
                        le(z(), mu(el, n_sum(), bxbc())),
                    ),
                    comm_r,
                    cl2,
                );
                mp(
                    le(z(), mu(el, bxbc(), n_sum())),
                    le(z(), mu(el, n_sum(), bxbc())),
                    lhsn_pos.clone(),
                    m1,
                )
            }; // |- 0<_( N*(Bx*Bc) )
            // lecpos( w=N, m=Bx*Bc ) : ess 0<=(N*(Bx*Bc)) ==> ( (0<N) -> (0<=Bx*Bc) )
            let lecpos_impl = el
                .app(
                    "lecpos",
                    &[("w", n_sum()), ("t", bxbc())],
                    &[lhsn_nm.clone()],
                )
                .unwrap(); // |- ( (0<N) -> (0<_(Bx*Bc)) )
            // N>=0
            let sc_pos = el
                .app(
                    "le0add",
                    &[("u", mu(el, pX(), pX())), ("v", mu(el, qY(), qY()))],
                    &[
                        el.app("of-sqpos", &[("u", pX())], &[]).unwrap(),
                        el.app("of-sqpos", &[("u", qY())], &[]).unwrap(),
                    ],
                )
                .unwrap();
            let sx_pos = el
                .app(
                    "le0add",
                    &[("u", mu(el, rX(), rX())), ("v", mu(el, sY(), sY()))],
                    &[
                        el.app("of-sqpos", &[("u", rX())], &[]).unwrap(),
                        el.app("of-sqpos", &[("u", sY())], &[]).unwrap(),
                    ],
                )
                .unwrap();
            let n_pos = el
                .app(
                    "le0add",
                    &[("u", sc_c()), ("v", sx_c())],
                    &[sc_pos.clone(), sx_pos.clone()],
                )
                .unwrap(); // |- 0<_N
            // EM : ( (N<_0) \/ -.(N<_0) )
            let em = {
                let idn = idt(n(le(n_sum(), z())));
                let dfor = el
                    .app(
                        "df-or",
                        &[
                            ("ph", le(n_sum(), z())),
                            ("ps", n(le(n_sum(), z()))),
                        ],
                        &[],
                    )
                    .unwrap();
                el.bi_rev(dfor, idn).unwrap()
            };
            // br_pos : ( -.(N<_0) -> (0<_(Bx*Bc)) )
            let br_pos = {
                let ltii = el
                    .app("ltII", &[("u", z()), ("v", n_sum())], &[])
                    .unwrap(); // ( (0<_N) -> ( -.(N<_0) -> (0<N) ) )
                let nstrict = mp(
                    le(z(), n_sum()),
                    imp(n(le(n_sum(), z())), lt(z(), n_sum())),
                    n_pos.clone(),
                    ltii,
                ); // ( -.(N<_0) -> (0<N) )
                syl(
                    n(le(n_sum(), z())),
                    lt(z(), n_sum()),
                    le(z(), bxbc()),
                    nstrict,
                    lecpos_impl.clone(),
                ) // ( -.(N<_0) -> (0<_(Bx*Bc)) )
            };
            // br_zero : ( (N<_0) -> (0<_(Bx*Bc)) )  [degenerate: N=0 -> coords 0]
            let br_zero = {
                // N=0 from (N<_0) and 0<=N (n_pos) [lecon] -> closed under hyp
                //   ( (N<_0) -> (N=0) )
                let n0_impl = {
                    // lein2(0,N) : (0<=N) -> ( (N<=0) -> (0=N) )
                    let lein2n = el
                        .app("lein2", &[("u", z()), ("v", n_sum())], &[])
                        .unwrap();
                    let p1 = mp(
                        le(z(), n_sum()),
                        imp(le(n_sum(), z()), eq(z(), n_sum())),
                        n_pos.clone(),
                        lein2n,
                    ); // ( (N<=0) -> (0=N) )
                    let ecn = el
                        .app("eqcom", &[("x", z()), ("y", n_sum())], &[])
                        .unwrap(); // (0=N)->(N=0)
                    syl(le(n_sum(), z()), eq(z(), n_sum()), eq(n_sum(), z()), p1, ecn)
                }; // ( (N<_0) -> (N=0) )
                // From N=0 (closed under hyp) get Sc=0, Sx=0 via addz.
                //   addz(a=Sc,b=Sx) needs 0<=Sc,0<=Sx,(Sc+Sx)=0
                //   build closed implications ( (N<_0) -> (Sc=0) ) etc.
                let addz = |a: Pt, b: Pt, p0a: Pt, p0b: Pt, pab: Pt| -> Pt {
                    el.app(
                        "addz",
                        &[("a", a), ("b", b)],
                        &[p0a, p0b, pab],
                    )
                    .unwrap()
                };
                // ( (N<_0) -> (Sc=0) ) : a1i n0_impl-derived (N=0) into addz?
                //   addz is inference needing closed (Sc+Sx)=0.  Under hyp
                //   (N<_0) we have N=0=(Sc+Sx).  Provide via deduction:
                //   prove closed C := ( ((Sc+Sx)=0) -> (Sc=0) ) then syl.
                let sc0_from_n0 = {
                    // C : ( ((Sc+Sx)=0) -> (Sc=0) )
                    //   = addz with (Sc+Sx)=0 as the THIRD ess — but ess must
                    //   be closed.  Instead use the inference with a *local*
                    //   hypothesis is impossible; build C by hand:
                    //   from (Sc+Sx)=0 : of-leadd path identical to addz body
                    //   but with the equality as antecedent.  Reuse addz by
                    //   supplying the equality via `id` is not closed.
                    //   => prove C directly (mirrors addz, equality carried):
                    let av = sc_c();
                    let bv = sx_c();
                    let hyp = || eq(pl(el, av.clone(), bv.clone()), z()); // (Sc+Sx)=0
                    let leadd = el
                        .app(
                            "of-leadd",
                            &[("u", z()), ("v", bv.clone()), ("w", av.clone())],
                            &[],
                        )
                        .unwrap(); // ( (0<=Sx) -> ((0+Sc)<=(Sx+Sc)) )
                    let step = mp(
                        le(z(), bv.clone()),
                        le(
                            pl(el, z(), av.clone()),
                            pl(el, bv.clone(), av.clone()),
                        ),
                        sx_pos.clone(),
                        leadd,
                    ); // |- ((0+Sc)<=(Sx+Sc))
                    let zpa = ring_eq(el, &pl(el, z(), av.clone()), &av);
                    let cl1 = el
                        .app(
                            "cong-le1",
                            &[
                                ("a", pl(el, z(), av.clone())),
                                ("b", av.clone()),
                                ("c", pl(el, bv.clone(), av.clone())),
                            ],
                            &[],
                        )
                        .unwrap();
                    let s_a = mp(
                        eq(pl(el, z(), av.clone()), av.clone()),
                        imp(
                            le(
                                pl(el, z(), av.clone()),
                                pl(el, bv.clone(), av.clone()),
                            ),
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                        ),
                        zpa,
                        cl1,
                    );
                    let a_le_bpa = mp(
                        le(
                            pl(el, z(), av.clone()),
                            pl(el, bv.clone(), av.clone()),
                        ),
                        le(av.clone(), pl(el, bv.clone(), av.clone())),
                        step,
                        s_a,
                    ); // |- ( Sc <= (Sx+Sc) )
                    // (Sx+Sc)=(Sc+Sx) ring ; with hyp (Sc+Sx)=0 -> (Sx+Sc)=0
                    let bpa = ring_eq(
                        el,
                        &pl(el, bv.clone(), av.clone()),
                        &pl(el, av.clone(), bv.clone()),
                    ); // (Sx+Sc)=(Sc+Sx)
                    // ( hyp -> (Sx+Sc)=0 ) : eqtrd( (Sx+Sc)=(Sc+Sx) lifted, hyp )
                    let bpa_a1 = a1i(
                        eq(
                            pl(el, bv.clone(), av.clone()),
                            pl(el, av.clone(), bv.clone()),
                        ),
                        hyp(),
                        bpa,
                    );
                    let bpa0 = el
                        .app(
                            "eqtrd",
                            &[("ph", hyp()), 
                                ("x", pl(el, bv.clone(), av.clone())),
                                ("y", pl(el, av.clone(), bv.clone())),
                                ("z", z()),
                            ],
                            &[bpa_a1, idt(hyp())],
                        )
                        .unwrap(); // ( hyp -> ((Sx+Sc)=0) )
                    // ( hyp -> ( Sc <= 0 ) ) : cong-le2 with (Sx+Sc)=0
                    let cl2 = el
                        .app(
                            "cong-le2",
                            &[
                                ("a", pl(el, bv.clone(), av.clone())),
                                ("b", z()),
                                ("c", av.clone()),
                            ],
                            &[],
                        )
                        .unwrap(); // ( (Sx+Sc)=0 -> ( (Sc<=(Sx+Sc)) -> (Sc<=0) ) )
                    let h_sc_le = mpd(
                        hyp(),
                        eq(pl(el, bv.clone(), av.clone()), z()),
                        imp(
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                            le(av.clone(), z()),
                        ),
                        bpa0,
                        a1i(
                            imp(
                                eq(pl(el, bv.clone(), av.clone()), z()),
                                imp(
                                    le(av.clone(), pl(el, bv.clone(), av.clone())),
                                    le(av.clone(), z()),
                                ),
                            ),
                            hyp(),
                            cl2,
                        ),
                    ); // ( hyp -> ( (Sc<=(Sx+Sc)) -> (Sc<=0) ) )
                    let sc_le0 = mpd(
                        hyp(),
                        le(av.clone(), pl(el, bv.clone(), av.clone())),
                        le(av.clone(), z()),
                        a1i(
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                            hyp(),
                            a_le_bpa,
                        ),
                        h_sc_le,
                    ); // ( hyp -> (Sc<=0) )
                    // lecon : 0<=Sc , Sc<=0 => Sc=0 ; build ( hyp -> Sc=0 )
                    //   need 0<=Sc (sc_pos closed) and (hyp->Sc<=0).
                    //   lein2(0,Sc): (0<=Sc)->((Sc<=0)->(0=Sc))
                    let lein2s = el
                        .app("lein2", &[("u", z()), ("v", av.clone())], &[])
                        .unwrap();
                    let p1 = mp(
                        le(z(), av.clone()),
                        imp(le(av.clone(), z()), eq(z(), av.clone())),
                        sc_pos.clone(),
                        lein2s,
                    ); // ( (Sc<=0) -> (0=Sc) )
                    let ecs = el
                        .app("eqcom", &[("x", z()), ("y", av.clone())], &[])
                        .unwrap(); // (0=Sc)->(Sc=0)
                    let sc0 = syl(
                        le(av.clone(), z()),
                        eq(z(), av.clone()),
                        eq(av.clone(), z()),
                        p1,
                        ecs,
                    ); // ( (Sc<=0) -> (Sc=0) )
                    syl(hyp(), le(av.clone(), z()), eq(av.clone(), z()), sc_le0, sc0)
                }; // ( ((Sc+Sx)=0) -> (Sc=0) )
                let _ = addz;
                // The degenerate branch requires extracting p=q=r=s=0 from
                // Sc=0,Sx=0 and then Bx=Bc=0 — a long but mechanical chain.
                // Given proof size, we instead realise br_zero using `lecpos`
                // as well: in the (N<_0) world we ALSO have 0<N is false, but
                // we can still cancel because (Bx*Bc)*N>=0 and N=0 forces the
                // PRODUCT 0, and 0<=0.  Concretely, from n0_impl (N=0) and
                // lhsn_pos (0<=(Bx*Bc)*N): substitute N=0 -> 0<=(Bx*Bc)*0 ->
                // (Bx*Bc)*0 = 0 (ring) is vacuous; does NOT give 0<=Bx*Bc.
                // So the degenerate extraction is unavoidable.  Implement it:
                //   Sc=0 -> p*p=0 -> p=0 ; q=0 ; (Sx=0) -> r=0,s=0 ; then
                //   Bx,Bc rewrite to 0 ; Bx*Bc=0 ; 0<=Bx*Bc by lerefl+cong.
                let sx0_from_n0 = {
                    // symmetric: ( ((Sc+Sx)=0) -> (Sx=0) ) via addz-style with
                    //   roles swapped (Sx + Sc form).
                    let av = sx_c();
                    let bv = sc_c();
                    let hyp = || eq(pl(el, sc_c(), sx_c()), z()); // (Sc+Sx)=0
                    // (Sc+Sx)=(Sx+Sc) ring ; -> ((Sx+Sc)... use addz directly:
                    // simpler: ( (Sc+Sx)=0 ) -> ( (Sx+Sc)=0 ) ring+eqtrd, then
                    //   reuse the Sc-branch construction with av:=Sx,bv:=Sc and
                    //   antecedent (Sx+Sc)=0.
                    let swap = ring_eq(
                        el,
                        &pl(el, sx_c(), sc_c()),
                        &pl(el, sc_c(), sx_c()),
                    ); // (Sx+Sc)=(Sc+Sx)
                    let swap_a1 = a1i(
                        eq(pl(el, sx_c(), sc_c()), pl(el, sc_c(), sx_c())),
                        hyp(),
                        swap,
                    );
                    let sxsc0 = el
                        .app(
                            "eqtrd",
                            &[("ph", hyp()), 
                                ("x", pl(el, sx_c(), sc_c())),
                                ("y", pl(el, sc_c(), sx_c())),
                                ("z", z()),
                            ],
                            &[swap_a1, idt(hyp())],
                        )
                        .unwrap(); // ( (Sc+Sx)=0 -> ((Sx+Sc)=0) )
                    // now mimic sc0_from_n0 with av=Sx,bv=Sc, antecedent
                    //   K:=((Sx+Sc)=0).  Build ( K -> (Sx=0) ):
                    let hyp2 = || eq(pl(el, av.clone(), bv.clone()), z()); // (Sx+Sc)=0
                    let leadd = el
                        .app(
                            "of-leadd",
                            &[("u", z()), ("v", bv.clone()), ("w", av.clone())],
                            &[],
                        )
                        .unwrap();
                    let step = mp(
                        le(z(), bv.clone()),
                        le(
                            pl(el, z(), av.clone()),
                            pl(el, bv.clone(), av.clone()),
                        ),
                        sc_pos.clone(),
                        leadd,
                    );
                    let zpa = ring_eq(el, &pl(el, z(), av.clone()), &av);
                    let cl1 = el
                        .app(
                            "cong-le1",
                            &[
                                ("a", pl(el, z(), av.clone())),
                                ("b", av.clone()),
                                ("c", pl(el, bv.clone(), av.clone())),
                            ],
                            &[],
                        )
                        .unwrap();
                    let s_a = mp(
                        eq(pl(el, z(), av.clone()), av.clone()),
                        imp(
                            le(
                                pl(el, z(), av.clone()),
                                pl(el, bv.clone(), av.clone()),
                            ),
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                        ),
                        zpa,
                        cl1,
                    );
                    let a_le_bpa = mp(
                        le(
                            pl(el, z(), av.clone()),
                            pl(el, bv.clone(), av.clone()),
                        ),
                        le(av.clone(), pl(el, bv.clone(), av.clone())),
                        step,
                        s_a,
                    );
                    let bpa = ring_eq(
                        el,
                        &pl(el, bv.clone(), av.clone()),
                        &pl(el, av.clone(), bv.clone()),
                    );
                    let bpa_a1 = a1i(
                        eq(
                            pl(el, bv.clone(), av.clone()),
                            pl(el, av.clone(), bv.clone()),
                        ),
                        hyp2(),
                        bpa,
                    );
                    let bpa0 = el
                        .app(
                            "eqtrd",
                            &[("ph", hyp2()), 
                                ("x", pl(el, bv.clone(), av.clone())),
                                ("y", pl(el, av.clone(), bv.clone())),
                                ("z", z()),
                            ],
                            &[bpa_a1, idt(hyp2())],
                        )
                        .unwrap();
                    let cl2 = el
                        .app(
                            "cong-le2",
                            &[
                                ("a", pl(el, bv.clone(), av.clone())),
                                ("b", z()),
                                ("c", av.clone()),
                            ],
                            &[],
                        )
                        .unwrap();
                    let h_sx_le = mpd(
                        hyp2(),
                        eq(pl(el, bv.clone(), av.clone()), z()),
                        imp(
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                            le(av.clone(), z()),
                        ),
                        bpa0,
                        a1i(
                            imp(
                                eq(pl(el, bv.clone(), av.clone()), z()),
                                imp(
                                    le(av.clone(), pl(el, bv.clone(), av.clone())),
                                    le(av.clone(), z()),
                                ),
                            ),
                            hyp2(),
                            cl2,
                        ),
                    );
                    let sx_le0 = mpd(
                        hyp2(),
                        le(av.clone(), pl(el, bv.clone(), av.clone())),
                        le(av.clone(), z()),
                        a1i(
                            le(av.clone(), pl(el, bv.clone(), av.clone())),
                            hyp2(),
                            a_le_bpa,
                        ),
                        h_sx_le,
                    );
                    let lein2s = el
                        .app("lein2", &[("u", z()), ("v", av.clone())], &[])
                        .unwrap();
                    let p1 = mp(
                        le(z(), av.clone()),
                        imp(le(av.clone(), z()), eq(z(), av.clone())),
                        sx_pos.clone(),
                        lein2s,
                    );
                    let ecs = el
                        .app("eqcom", &[("x", z()), ("y", av.clone())], &[])
                        .unwrap();
                    let sx0 = syl(
                        le(av.clone(), z()),
                        eq(z(), av.clone()),
                        eq(av.clone(), z()),
                        p1,
                        ecs,
                    );
                    let k_sx0 = syl(
                        hyp2(),
                        le(av.clone(), z()),
                        eq(av.clone(), z()),
                        sx_le0,
                        sx0,
                    ); // ( (Sx+Sc)=0 -> (Sx=0) )
                    syl(hyp(), eq(pl(el, sx_c(), sc_c()), z()), eq(sx_c(), z()), sxsc0, k_sx0)
                }; // ( ((Sc+Sx)=0) -> (Sx=0) )
                // generic: from (P*P+Q*Q)=0 derive P=0 (addz on P*P,Q*Q then sqz)
                let sq0 = |pp: Pt, qq: Pt, hyp_zero: Pt| -> Pt {
                    // hyp_zero : |- ( (pp*pp + qq*qq) = 0 )
                    let a = mu(el, pp.clone(), pp.clone());
                    let b = mu(el, qq.clone(), qq.clone());
                    let az = el
                        .app(
                            "addz",
                            &[("a", a.clone()), ("b", b.clone())],
                            &[
                                el.app("of-sqpos", &[("u", pp.clone())], &[]).unwrap(),
                                el.app("of-sqpos", &[("u", qq.clone())], &[]).unwrap(),
                                hyp_zero,
                            ],
                        )
                        .unwrap(); // |- ( (pp*pp) = 0 )
                    el.app("sqz", &[("u", pp.clone())], &[az]).unwrap() // |- ( pp = 0 )
                };
                // Build ( (N<_0) -> (Bx*Bc)=0 ):
                //   chain: (N<_0)->(N=0)->((Sc+Sx)=0)  [N_sum is literally
                //   (Sc+Sx)], then Sc=0 & Sx=0, then p,q,r,s=0, then Bx=Bc=0.
                // n0_impl : ( (N<_0) -> (N=0) ) ; N = (Sc+Sx) syntactically.
                // (N=0) is exactly ((Sc+Sx)=0).
                // closed pieces: sc0_from_n0 : ((Sc+Sx)=0)->(Sc=0)
                //                sx0_from_n0 : ((Sc+Sx)=0)->(Sx=0)
                // p=0 etc.: need ( (Sc=0) -> (p=0) ) = sq0 with hyp the
                //   antecedent — make closed implication via the same
                //   addz-as-inference trick (addz ess closed): we need
                //   Sc=0 as a *closed* proof.  Under (N<_0) we get it via
                //   syl(n0_impl, sc0_from_n0).  But sq0 needs it closed.
                //   So thread everything as implications from (N<_0):
                let n0 = el
                    .app(
                        "syl",
                        &[
                            ("ph", le(n_sum(), z())),
                            ("ps", eq(n_sum(), z())),
                            ("ch", eq(n_sum(), z())),
                        ],
                        &[n0_impl.clone(), idt(eq(n_sum(), z()))],
                    )
                    .unwrap(); // ( (N<_0) -> ((Sc+Sx)=0) )
                let nlt = || le(n_sum(), z()); // (N<_0)
                let sc0 = syl(
                    nlt(),
                    eq(n_sum(), z()),
                    eq(sc_c(), z()),
                    n0.clone(),
                    sc0_from_n0,
                ); // ( (N<_0) -> (Sc=0) )
                let sx0 = syl(
                    nlt(),
                    eq(n_sum(), z()),
                    eq(sx_c(), z()),
                    n0.clone(),
                    sx0_from_n0,
                ); // ( (N<_0) -> (Sx=0) )
                // ( (Sc=0) -> (p=0) ) closed via sq0-as-implication:
                //   build closed ( ((p*p+q*q)=0) -> (p=0) ) using addz+sqz
                //   where addz ess (the equality) must be closed — supply it
                //   as the antecedent through the deduction theorem is again
                //   blocked.  Resolve: prove closed
                //   pPQ : ( (Sc=0) -> (p=0) ) by:
                //     (Sc=0) i.e. (p*p+q*q)=0.  addz needs it closed.  Use
                //     `mpd`/`syl` threading: addz is an inference; we cannot
                //     parametrise its ess.  So instead inline addz's body
                //     here too (as we did for sc0_from_n0) with the equality
                //     carried.  For brevity reuse the closed helper `addz`
                //     by noting we DO have, under (N<_0), Sc=0 CLOSED via
                //     `mp` is impossible (it's an implication).  Hence we
                //     keep everything as ( (N<_0) -> _ ) and only call addz
                //     / sqz at the very end where their ess ARE closed,
                //     because by then we will have discharged (N<_0) using
                //     `jaoi`.  => Move the heavy extraction to AFTER jaoi:
                //   Therefore: instead of proving br_zero as an implication,
                //   we prove the WHOLE SGN by jaoi where the (N<_0) branch
                //   simply yields (0<=Bx*Bc) via the SAME lecpos route,
                //   because when N<_0 (hence N=0) we still have
                //   0<=(N*(Bx*Bc)) (lhsn_nm) and N=0 makes N*(Bx*Bc)=0;
                //   lecpos needs 0<N which is false here — so this fails.
                //   The genuine degenerate extraction is required and is
                //   long; given the scope and the fact that G3a's value is
                //   the EQ+generic-SGN, we close br_zero by the explicit
                //   coordinate-zero argument using closed addz/sqz applied
                //   to the (now closed under the branch) equalities via the
                //   `syl`-threaded implications above plus closed
                //   ( eq->eq ) helper lemmas built like sc0_from_n0.
                // p=0,q=0,r=0,s=0 as ( (N<_0) -> *=0 ):
                // ---- coordinate zeros under (N<_0) ----
                // sc0 : (N<_0)->(Sc=0)  Sc=(p*p+q*q)
                // sx0 : (N<_0)->(Sx=0)  Sx=(r*r+s*s)
                // closed ( (Sc=0)->(p=0) ): addz(p*p,q*q)+sqz; addz/sqz are
                // inferences with closed ess — provide ess via the closed
                // implication `mk` (same as mk_a0) + a closed
                // ( ((p*p)=0) -> (p=0) ) which we get from core `sqz` by
                // wrapping: sqz ess is (u*u)=0; we need it as antecedent.
                // Build closed SQZI : ( ((p*p)=0) -> (p=0) ) by re-using the
                // EXISTING core lemma `sqz` is impossible (inference).  Use
                // `sqzhalf` core: ( (0<=p) -> ( ((p*p)=0) -> (p=0) ) ) plus
                // the (p<=0) branch via sqzhalf on (0-xp), exactly the body
                // of core arm 51 — replicate compactly:
                let sqzi = |pp: Pt| -> Pt {
                    // closed ( ((pp*pp)=0) -> (pp=0) )
                    let uu = mu(el, pp.clone(), pp.clone());
                    let nu = neg(el, pp.clone());
                    let hyp = || eq(uu.clone(), z());
                    // branch B: (0<=pp) -> ((pp*pp)=0) -> (pp=0)  [sqzhalf]
                    let shB = el
                        .app("sqzhalf", &[("u", pp.clone())], &[])
                        .unwrap(); // ( (0<=pp) -> ( ((pp*pp)=0) -> (pp=0) ) )
                    // branch A: (pp<=0) similarly via sqzhalf(0-xpp)
                    let l2s = el
                        .app("le2sub", &[("u", pp.clone()), ("v", z())], &[])
                        .unwrap(); // ( (pp<=0) -> (0<=(0-xpp)) )
                    let ren = ring_eq(el, &mu(el, nu.clone(), nu.clone()), &uu);
                    let shA = el
                        .app("sqzhalf", &[("u", nu.clone())], &[])
                        .unwrap(); // ( (0<=(0-xpp)) -> ( ((0-xpp)*(0-xpp)=0) -> ((0-xpp)=0) ) )
                    // ( hyp -> ((0-xpp)*(0-xpp)=0) ) : ren + hyp
                    let nn0 = {
                        let ren_a1 = a1i(
                            eq(mu(el, nu.clone(), nu.clone()), uu.clone()),
                            hyp(),
                            ren,
                        );
                        el.app(
                            "eqtrd",
                            &[("ph", hyp()), 
                                ("x", mu(el, nu.clone(), nu.clone())),
                                ("y", uu.clone()),
                                ("z", z()),
                            ],
                            &[ren_a1, idt(hyp())],
                        )
                        .unwrap() // ( hyp -> ((0-xpp)*(0-xpp)=0) )
                    };
                    // brA : ( (pp<=0) -> ( hyp -> (pp=0) ) )
                    let s_a = syl(
                        le(pp.clone(), z()),
                        le(z(), nu.clone()),
                        imp(
                            eq(mu(el, nu.clone(), nu.clone()), z()),
                            eq(nu.clone(), z()),
                        ),
                        l2s,
                        shA,
                    ); // ( (pp<=0) -> ( ((0-xpp)*(0-xpp)=0) -> ((0-xpp)=0) ) )
                    let se0 = el
                        .app("subeq0", &[("u", z()), ("v", pp.clone())], &[])
                        .unwrap(); // ( ((0-xpp)=0) -> (0=pp) )
                    let ecp = el
                        .app("eqcom", &[("x", z()), ("y", pp.clone())], &[])
                        .unwrap(); // (0=pp)->(pp=0)
                    // ( (pp<=0) -> ( hyp -> (pp=0) ) ):
                    //   from s_a get ((0-xpp)*(0-xpp)=0) -> (0-xpp)=0 -> pp=0
                    let inner_a = {
                        let c1 = syl(
                            eq(nu.clone(), z()),
                            eq(z(), pp.clone()),
                            eq(pp.clone(), z()),
                            se0,
                            ecp,
                        ); // ((0-xpp)=0)->(pp=0)
                        // (pp<=0)->( ((0-xpp)*(0-xpp)=0) -> (pp=0) )
                        imim(
                            le(pp.clone(), z()),
                            eq(mu(el, nu.clone(), nu.clone()), z()),
                            eq(nu.clone(), z()),
                            eq(pp.clone(), z()),
                            s_a,
                            c1,
                        )
                    };
                    // compose with nn0 ( hyp -> ((0-xpp)*(0-xpp)=0) ) under (pp<=0):
                    let nn0_a1 = a1i(
                        imp(
                            hyp(),
                            eq(mu(el, nu.clone(), nu.clone()), z()),
                        ),
                        le(pp.clone(), z()),
                        nn0.clone(),
                    ); // (pp<=0) -> ( hyp -> ((0-xpp)*(0-xpp)=0) )
                    let brA = syld(
                        le(pp.clone(), z()),
                        hyp(),
                        eq(mu(el, nu.clone(), nu.clone()), z()),
                        eq(pp.clone(), z()),
                        nn0_a1,
                        inner_a,
                    ); // ( (pp<=0) -> ( hyp -> (pp=0) ) )
                    // shB is already ( (0<=pp) -> ( hyp -> (pp=0) ) )
                    let brB2 = shB;
                    // jaoi over of-letot(pp,0): ( (pp<=0)\/(0<=pp) ) -> ( hyp -> (pp=0) )
                    let jao = el
                        .app(
                            "jaoi",
                            &[
                                ("ph", le(pp.clone(), z())),
                                ("ps", le(z(), pp.clone())),
                                ("ch", imp(hyp(), eq(pp.clone(), z()))),
                            ],
                            &[brA, brB2],
                        )
                        .unwrap();
                    let tot = el
                        .app("of-letot", &[("u", pp.clone()), ("v", z())], &[])
                        .unwrap();
                    mp(
                        ow(le(pp.clone(), z()), le(z(), pp.clone())),
                        imp(hyp(), eq(pp.clone(), z())),
                        tot,
                        jao,
                    ) // |- ( ((pp*pp)=0) -> (pp=0) )
                };
                // closed ( (Sc=0) -> (p=0) ) : addz(p*p,q*q)+sqzi.  addz is
                // inference; build closed ( ((p*p+q*q)=0) -> ((p*p)=0) ) via
                // mk_a0-style.  Reuse pq_zero's mk_a0 indirectly: simpler to
                // call addz as inference with ess being CLOSED — but ess is
                // the equality (Sc=0) which is closed only post-jaoi.  So we
                // produce ( (N<_0) -> (p=0) ) by syl-threading:
                //   (N<_0)->(Sc=0)  [sc0]
                //   ( (Sc=0) -> ((p*p)=0) )  closed [addz-impl]
                //   ( ((p*p)=0) -> (p=0) )   closed [sqzi]
                let addz_impl = |a: Pt, b: Pt, p0a: Pt, p0b: Pt| -> Pt {
                    // closed ( ((a+b)=0) -> (a=0) )  (= addz body, eq carried)
                    let leadd = el
                        .app(
                            "of-leadd",
                            &[("u", z()), ("v", b.clone()), ("w", a.clone())],
                            &[],
                        )
                        .unwrap();
                    let step = mp(
                        le(z(), b.clone()),
                        le(
                            pl(el, z(), a.clone()),
                            pl(el, b.clone(), a.clone()),
                        ),
                        p0b,
                        leadd,
                    );
                    let zpa = ring_eq(el, &pl(el, z(), a.clone()), &a);
                    let cl1 = el
                        .app(
                            "cong-le1",
                            &[
                                ("a", pl(el, z(), a.clone())),
                                ("b", a.clone()),
                                ("c", pl(el, b.clone(), a.clone())),
                            ],
                            &[],
                        )
                        .unwrap();
                    let s_a = mp(
                        eq(pl(el, z(), a.clone()), a.clone()),
                        imp(
                            le(
                                pl(el, z(), a.clone()),
                                pl(el, b.clone(), a.clone()),
                            ),
                            le(a.clone(), pl(el, b.clone(), a.clone())),
                        ),
                        zpa,
                        cl1,
                    );
                    let a_le_bpa = mp(
                        le(
                            pl(el, z(), a.clone()),
                            pl(el, b.clone(), a.clone()),
                        ),
                        le(a.clone(), pl(el, b.clone(), a.clone())),
                        step,
                        s_a,
                    );
                    let bpa = ring_eq(
                        el,
                        &pl(el, b.clone(), a.clone()),
                        &pl(el, a.clone(), b.clone()),
                    );
                    let bpa_a1 = a1i(
                        eq(
                            pl(el, b.clone(), a.clone()),
                            pl(el, a.clone(), b.clone()),
                        ),
                        eq(pl(el, a.clone(), b.clone()), z()),
                        bpa,
                    );
                    let bpa0 = el
                        .app(
                            "eqtrd",
                            &[("ph", eq(pl(el, a.clone(), b.clone()), z())), 
                                ("x", pl(el, b.clone(), a.clone())),
                                ("y", pl(el, a.clone(), b.clone())),
                                ("z", z()),
                            ],
                            &[bpa_a1, idt(eq(pl(el, a.clone(), b.clone()), z()))],
                        )
                        .unwrap();
                    let cl2 = el
                        .app(
                            "cong-le2",
                            &[
                                ("a", pl(el, b.clone(), a.clone())),
                                ("b", z()),
                                ("c", a.clone()),
                            ],
                            &[],
                        )
                        .unwrap();
                    let h_le = mpd(
                        eq(pl(el, a.clone(), b.clone()), z()),
                        eq(pl(el, b.clone(), a.clone()), z()),
                        imp(
                            le(a.clone(), pl(el, b.clone(), a.clone())),
                            le(a.clone(), z()),
                        ),
                        bpa0,
                        a1i(
                            imp(
                                eq(pl(el, b.clone(), a.clone()), z()),
                                imp(
                                    le(a.clone(), pl(el, b.clone(), a.clone())),
                                    le(a.clone(), z()),
                                ),
                            ),
                            eq(pl(el, a.clone(), b.clone()), z()),
                            cl2,
                        ),
                    );
                    let av_le0 = mpd(
                        eq(pl(el, a.clone(), b.clone()), z()),
                        le(a.clone(), pl(el, b.clone(), a.clone())),
                        le(a.clone(), z()),
                        a1i(
                            le(a.clone(), pl(el, b.clone(), a.clone())),
                            eq(pl(el, a.clone(), b.clone()), z()),
                            a_le_bpa,
                        ),
                        h_le,
                    );
                    let lein2s = el
                        .app("lein2", &[("u", z()), ("v", a.clone())], &[])
                        .unwrap();
                    let p1 = mp(
                        le(z(), a.clone()),
                        imp(le(a.clone(), z()), eq(z(), a.clone())),
                        p0a,
                        lein2s,
                    );
                    let ecs = el
                        .app("eqcom", &[("x", z()), ("y", a.clone())], &[])
                        .unwrap();
                    let av0 = syl(
                        le(a.clone(), z()),
                        eq(z(), a.clone()),
                        eq(a.clone(), z()),
                        p1,
                        ecs,
                    );
                    syl(
                        eq(pl(el, a.clone(), b.clone()), z()),
                        le(a.clone(), z()),
                        eq(a.clone(), z()),
                        av_le0,
                        av0,
                    )
                };
                // ( (N<_0) -> (coord=0) ) for p,q,r,s
                let zero_of = |pp: Pt, qq: Pt, sceq: Pt| -> Pt {
                    // sceq : ( (N<_0) -> ( (pp*pp+qq*qq) = 0 ) )
                    let aa = mu(el, pp.clone(), pp.clone());
                    let bb = mu(el, qq.clone(), qq.clone());
                    let sqp = el.app("of-sqpos", &[("u", pp.clone())], &[]).unwrap();
                    let sqq = el.app("of-sqpos", &[("u", qq.clone())], &[]).unwrap();
                    let a0 = addz_impl(aa.clone(), bb.clone(), sqp, sqq); // ((aa+bb)=0)->(aa=0)
                    let pz = sqzi(pp.clone()); // ((pp*pp)=0)->(pp=0)
                    let n_aa0 = syl(
                        le(n_sum(), z()),
                        eq(pl(el, aa.clone(), bb.clone()), z()),
                        eq(aa.clone(), z()),
                        sceq,
                        a0,
                    );
                    syl(
                        le(n_sum(), z()),
                        eq(aa.clone(), z()),
                        eq(pp.clone(), z()),
                        n_aa0,
                        pz,
                    ) // ( (N<_0) -> (pp=0) )
                };
                // sc0 : (N<_0)->(Sc=0)=( (p*p+q*q)=0 ); sx0 likewise
                let p0 = zero_of(pX(), qY(), sc0.clone());
                let q0 = zero_of(qY(), pX(), {
                    let sw = ring_eq(
                        el,
                        &pl(el, mu(el, qY(), qY()), mu(el, pX(), pX())),
                        &sc_c(),
                    ); // (q*q+p*p)=Sc
                    let sw_a1 = a1i(
                        eq(
                            pl(el, mu(el, qY(), qY()), mu(el, pX(), pX())),
                            sc_c(),
                        ),
                        le(n_sum(), z()),
                        sw,
                    );
                    el.app(
                        "eqtrd",
                        &[("ph", le(n_sum(), z())), 
                            ("x", pl(el, mu(el, qY(), qY()), mu(el, pX(), pX()))),
                            ("y", sc_c()),
                            ("z", z()),
                        ],
                        &[sw_a1, sc0.clone()],
                    )
                    .unwrap() // (N<_0)->((q*q+p*p)=0)
                });
                let r0 = zero_of(rX(), sY(), sx0.clone());
                let s0 = zero_of(sY(), rX(), {
                    let sw = ring_eq(
                        el,
                        &pl(el, mu(el, sY(), sY()), mu(el, rX(), rX())),
                        &sx_c(),
                    );
                    let sw_a1 = a1i(
                        eq(
                            pl(el, mu(el, sY(), sY()), mu(el, rX(), rX())),
                            sx_c(),
                        ),
                        le(n_sum(), z()),
                        sw,
                    );
                    el.app(
                        "eqtrd",
                        &[("ph", le(n_sum(), z())), 
                            ("x", pl(el, mu(el, sY(), sY()), mu(el, rX(), rX()))),
                            ("y", sx_c()),
                            ("z", z()),
                        ],
                        &[sw_a1, sx0.clone()],
                    )
                    .unwrap()
                });
                // Now Bx*Bc = 0 under (N<_0): substitute p,q,r,s -> 0.
                //   Bx = u*r+v*s ; Bc = u*p+v*q.
                //   ( (N<_0) -> (Bx=0) ) : cong rewrite r,s to 0 then ring.
                let to0 = |coordv: Pt, czero: Pt, expr: Pt, expr0: Pt| -> Pt {
                    // czero : ( (N<_0) -> (coordv = 0) ) ; produce
                    //   ( (N<_0) -> (expr = expr0) ) where expr0 = expr[coordv:=0]
                    //   via cong (cmu/cpl) — we instead use ring after we have
                    //   coordv=0 as a closed-under-hyp fact: easier to just
                    //   build ( (N<_0) -> (Bx=0) ) directly with eqtrd chain.
                    let _ = (coordv, czero, expr, expr0);
                    idt(le(n_sum(), z()))
                };
                let _ = to0;
                // ( (N<_0) -> (Bx=0) ):
                //   Bx = (u*r)+(v*s).  r0:(N<_0)->(r=0), s0:(N<_0)->(s=0).
                //   (u*r) -> (u*0) [cong-mu2 with r=0] -> 0 [ring]; sim v*s.
                //   sum -> 0+0 -> 0 [ring].
                let bx0 = {
                    // (N<_0) -> ( (u*r) = 0 )
                    let cmur = el
                        .app(
                            "cong-mu2",
                            &[("a", rX()), ("b", z()), ("c", uX())],
                            &[],
                        )
                        .unwrap(); // ( r=0 -> ( (u*r)=(u*0) ) )
                    let n_ur_u0 = syl(
                        le(n_sum(), z()),
                        eq(rX(), z()),
                        eq(mu(el, uX(), rX()), mu(el, uX(), z())),
                        r0.clone(),
                        cmur,
                    ); // (N<_0)->((u*r)=(u*0))
                    let u0_0 = mul0r(uX()); // (u*0)=0
                    let n_ur0 = el
                        .app(
                            "eqtrd",
                            &[("ph", le(n_sum(), z())), 
                                ("x", mu(el, uX(), rX())),
                                ("y", mu(el, uX(), z())),
                                ("z", z()),
                            ],
                            &[
                                n_ur_u0,
                                a1i(eq(mu(el, uX(), z()), z()), le(n_sum(), z()), u0_0),
                            ],
                        )
                        .unwrap(); // (N<_0)->((u*r)=0)
                    let cmvs = el
                        .app(
                            "cong-mu2",
                            &[("a", sY()), ("b", z()), ("c", vY())],
                            &[],
                        )
                        .unwrap();
                    let n_vs_v0 = syl(
                        le(n_sum(), z()),
                        eq(sY(), z()),
                        eq(mu(el, vY(), sY()), mu(el, vY(), z())),
                        s0.clone(),
                        cmvs,
                    );
                    let v0_0 = mul0r(vY());
                    let n_vs0 = el
                        .app(
                            "eqtrd",
                            &[("ph", le(n_sum(), z())), 
                                ("x", mu(el, vY(), sY())),
                                ("y", mu(el, vY(), z())),
                                ("z", z()),
                            ],
                            &[
                                n_vs_v0,
                                a1i(eq(mu(el, vY(), z()), z()), le(n_sum(), z()), v0_0),
                            ],
                        )
                        .unwrap(); // (N<_0)->((v*s)=0)
                    // Bx = (u*r)+(v*s) ; rewrite both to 0 -> (0+0) -> 0
                    //   cpl1 with (u*r)=0 : Bx = (0+(v*s)) ; cpl2 with (v*s)=0
                    let c1 = {
                        // (N<_0) -> ( Bx = (0+(v*s)) )
                        let cp = el
                            .app(
                                "cong-pl1",
                                &[
                                    ("a", mu(el, uX(), rX())),
                                    ("b", z()),
                                    ("c", mu(el, vY(), sY())),
                                ],
                                &[],
                            )
                            .unwrap(); // ( (u*r)=0 -> ( ((u*r)+(v*s)) = (0+(v*s)) ) )
                        syl(
                            le(n_sum(), z()),
                            eq(mu(el, uX(), rX()), z()),
                            eq(bx_c(), pl(el, z(), mu(el, vY(), sY()))),
                            n_ur0,
                            cp,
                        )
                    };
                    let c2 = {
                        let cp = el
                            .app(
                                "cong-pl2",
                                &[
                                    ("a", mu(el, vY(), sY())),
                                    ("b", z()),
                                    ("c", z()),
                                ],
                                &[],
                            )
                            .unwrap(); // ( (v*s)=0 -> ( (0+(v*s)) = (0+0) ) )
                        syl(
                            le(n_sum(), z()),
                            eq(mu(el, vY(), sY()), z()),
                            eq(
                                pl(el, z(), mu(el, vY(), sY())),
                                pl(el, z(), z()),
                            ),
                            n_vs0,
                            cp,
                        )
                    };
                    let z00 = el.app("of-add0", &[("u", z())], &[]).unwrap(); // (0+0)=0
                    // Bx = (0+(v*s)) = (0+0) = 0
                    let t1 = el
                        .app(
                            "eqtrd",
                            &[("ph", le(n_sum(), z())), 
                                ("x", bx_c()),
                                ("y", pl(el, z(), mu(el, vY(), sY()))),
                                ("z", pl(el, z(), z())),
                            ],
                            &[c1, c2],
                        )
                        .unwrap(); // (N<_0)->( Bx=(0+0) )
                    el.app(
                        "eqtrd",
                        &[("ph", le(n_sum(), z())), ("x", bx_c()), ("y", pl(el, z(), z())), ("z", z())],
                        &[t1, a1i(eq(pl(el, z(), z()), z()), le(n_sum(), z()), z00)],
                    )
                    .unwrap() // (N<_0)->( Bx=0 )
                };
                // (N<_0) -> ( (Bx*Bc) = 0 ) : Bx=0 -> (Bx*Bc)=(0*Bc) -> 0
                let bxbc0 = {
                    let cmu = el
                        .app(
                            "cong-mu1",
                            &[("a", bx_c()), ("b", z()), ("c", bc_c())],
                            &[],
                        )
                        .unwrap(); // ( Bx=0 -> ( (Bx*Bc)=(0*Bc) ) )
                    let n_eq0 = syl(
                        le(n_sum(), z()),
                        eq(bx_c(), z()),
                        eq(bxbc(), mu(el, z(), bc_c())),
                        bx0,
                        cmu,
                    );
                    let z0 = el
                        .app("mul0", &[("u", bc_c())], &[])
                        .unwrap(); // ( (0*Bc)=0 )
                    el.app(
                        "eqtrd",
                        &[("ph", le(n_sum(), z())), 
                            ("x", bxbc()),
                            ("y", mu(el, z(), bc_c())),
                            ("z", z()),
                        ],
                        &[
                            n_eq0,
                            a1i(eq(mu(el, z(), bc_c()), z()), le(n_sum(), z()), z0),
                        ],
                    )
                    .unwrap() // (N<_0)->( (Bx*Bc)=0 )
                };
                // 0<=(Bx*Bc) from (Bx*Bc)=0 : lerefl 0<=0 then cong-le2
                let lerefl0 = el.app("lerefl", &[("u", z())], &[]).unwrap(); // ( 0<=0 )
                // ( (Bx*Bc)=0 ) -> ( 0=(Bx*Bc) ) -> ( (0<=0) -> (0<=Bx*Bc) )
                let bxbc0c = {
                    let ec = el
                        .app("eqcom", &[("x", bxbc()), ("y", z())], &[])
                        .unwrap(); // ((Bx*Bc)=0)->(0=(Bx*Bc))
                    syl(
                        le(n_sum(), z()),
                        eq(bxbc(), z()),
                        eq(z(), bxbc()),
                        bxbc0,
                        ec,
                    )
                }; // (N<_0)->( 0=(Bx*Bc) )
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[("a", z()), ("b", bxbc()), ("c", z())],
                        &[],
                    )
                    .unwrap(); // ( 0=(Bx*Bc) -> ( (0<=0) -> (0<=Bx*Bc) ) )
                let step = syl(
                    le(n_sum(), z()),
                    eq(z(), bxbc()),
                    imp(le(z(), z()), le(z(), bxbc())),
                    bxbc0c,
                    cl2,
                );
                // (N<_0)-> (0<=Bx*Bc) by mp-in-consequent with lerefl0
                mpd(
                    le(n_sum(), z()),
                    le(z(), z()),
                    le(z(), bxbc()),
                    a1i(le(z(), z()), le(n_sum(), z()), lerefl0),
                    step,
                ) // ( (N<_0) -> (0<_(Bx*Bc)) )
            };
            // jaoi(br_zero, br_pos) on EM { (N<_0) , -.(N<_0) }
            let jao = el
                .app(
                    "jaoi",
                    &[
                        ("ph", le(n_sum(), z())),
                        ("ps", n(le(n_sum(), z()))),
                        ("ch", le(z(), bxbc())),
                    ],
                    &[br_zero, br_pos],
                )
                .unwrap();
            let sgn_coord = mp(
                ow(le(n_sum(), z()), n(le(n_sum(), z()))),
                le(z(), bxbc()),
                em,
                jao,
            ); // |- 0<_( (Bx*Bc) )  (coordinate form)
            // rewrite back to dot terms : 0<_( dabx * dabc )
            let dd_xc = mu_rw(
                dabx(),
                bx_c(),
                dabc(),
                bc_c(),
                e_dabx.clone(),
                e_dabc.clone(),
            ); // ( (dabx*dabc) = (Bx*Bc) )
            let sgn_pf = {
                let dd_xc_c = eqcomm(
                    el,
                    mu(el, dabx(), dabc()),
                    bxbc(),
                    dd_xc,
                ); // ( (Bx*Bc) = (dabx*dabc) )
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[("a", bxbc()), ("b", mu(el, dabx(), dabc())), ("c", z())],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(bxbc(), mu(el, dabx(), dabc())),
                    imp(le(z(), bxbc()), le(z(), mu(el, dabx(), dabc()))),
                    dd_xc_c,
                    cl2,
                );
                mp(
                    le(z(), bxbc()),
                    le(z(), mu(el, dabx(), dabc())),
                    sgn_coord,
                    m1,
                )
            }; // |- 0<_( dabx * dabc )

            eprintln!("    [g3a] cp5: fold back via df-acong (SGN done)");
            // ---- 5. fold back via df-acong ----
            let eq_a = eq(eql_g.clone(), eqr_g.clone());
            let sgn_a = le(z(), mu(el, dabx(), dabc()));
            let conj_a = aw(eq_a.clone(), sgn_a.clone());
            let conj_pf = conj2(el, eq_a.clone(), sgn_a.clone(), eq_pf, sgn_pf);
            let acong = el
                .app(
                    "wacong",
                    &[
                        ("o", pa()),
                        ("p", pb()),
                        ("q", px()),
                        ("a", pa()),
                        ("e", pb()),
                        ("f", pc()),
                    ],
                    &[],
                )
                .unwrap();
            let dfac = el
                .app(
                    "df-acong",
                    &[
                        ("o", pa()),
                        ("p", pb()),
                        ("q", px()),
                        ("a", pa()),
                        ("e", pb()),
                        ("f", pc()),
                    ],
                    &[],
                )
                .unwrap();
            eprintln!("    [g3a] cp6: bi_rev df-acong (conj built)");
            let g = el.bi_rev(dfac, conj_pf).unwrap(); // |- ( ACong a b x a b c )
            eprintln!("    [g3a] cp7: G3a-rayangle Lemma built");
            Lemma {
                name: "G3a-rayangle".into(),
                ess: vec![(
                    "g3a.1".into(),
                    toks(&["|-", "(", "Ray", "a", "c", "x", ")"]),
                )],
                goal: g,
            }
        }
        // ============================================================
        // idx 8 : g3b-lagc — generic 2D Lagrange.  A=(a,b) C=(c,e):
        //   (a*a+b*b)*(c*c+e*e) = (a*c+b*e)^2 + (a*e -x b*c)^2
        // ============================================================
        8 => {
            let v = |x: &str| leaf(x);
            let (pa, pb, pc, pe) = (v("va"), v("vb"), v("vc"), v("ve"));
            let aa = pl(el, mu(el, pa.clone(), pa.clone()), mu(el, pb.clone(), pb.clone()));
            let cc = pl(el, mu(el, pc.clone(), pc.clone()), mu(el, pe.clone(), pe.clone()));
            let ac = pl(el, mu(el, pa.clone(), pc.clone()), mu(el, pb.clone(), pe.clone()));
            let xac = mi(el, mu(el, pa.clone(), pe.clone()), mu(el, pb.clone(), pc.clone()));
            let lhs = mu(el, aa, cc);
            let rhs = pl(el, mu(el, ac.clone(), ac.clone()), mu(el, xac.clone(), xac.clone()));
            return Lemma {
                name: "g3b-lagc".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 9 : g3b-lagr — generic 2D Lagrange.  A=(a,b) R=(f,g):
        //   (a*a+b*b)*(f*f+g*g) = (a*f+b*g)^2 + (a*g -x b*f)^2
        // ============================================================
        9 => {
            let v = |x: &str| leaf(x);
            let (pa, pb, pf, pg) = (v("va"), v("vb"), v("vf"), v("vg"));
            let aa = pl(el, mu(el, pa.clone(), pa.clone()), mu(el, pb.clone(), pb.clone()));
            let rr = pl(el, mu(el, pf.clone(), pf.clone()), mu(el, pg.clone(), pg.clone()));
            let ar = pl(el, mu(el, pa.clone(), pf.clone()), mu(el, pb.clone(), pg.clone()));
            let xar = mi(el, mu(el, pa.clone(), pg.clone()), mu(el, pb.clone(), pf.clone()));
            let lhs = mu(el, aa, rr);
            let rhs = pl(el, mu(el, ar.clone(), ar.clone()), mu(el, xar.clone(), xar.clone()));
            return Lemma {
                name: "g3b-lagr".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 10 : g3b-m — generic Plücker for M = AA*XCR.
        //   A=(a,b) C=(c,e) R=(f,g):
        //   (a*a+b*b)*( c*g -x e*f )
        //     = (a*c+b*e)*(a*g -x b*f) -x (a*f+b*g)*(a*e -x b*c)
        // ============================================================
        10 => {
            let v = |x: &str| leaf(x);
            let (pa, pb, pc, pe, pf, pg) =
                (v("va"), v("vb"), v("vc"), v("ve"), v("vf"), v("vg"));
            let aa =
                pl(el, mu(el, pa.clone(), pa.clone()), mu(el, pb.clone(), pb.clone()));
            let xcr =
                mi(el, mu(el, pc.clone(), pg.clone()), mu(el, pe.clone(), pf.clone()));
            let ac =
                pl(el, mu(el, pa.clone(), pc.clone()), mu(el, pb.clone(), pe.clone()));
            let ar =
                pl(el, mu(el, pa.clone(), pf.clone()), mu(el, pb.clone(), pg.clone()));
            let xac =
                mi(el, mu(el, pa.clone(), pe.clone()), mu(el, pb.clone(), pc.clone()));
            let xar =
                mi(el, mu(el, pa.clone(), pg.clone()), mu(el, pb.clone(), pf.clone()));
            let lhs = mu(el, aa, xcr);
            let rhs = mi(
                el,
                mu(el, ac.clone(), xar.clone()),
                mu(el, ar.clone(), xac.clone()),
            );
            return Lemma {
                name: "g3b-m".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 11 : g3b-crs — generic crs Lagrange.  A=(a,b) C=(c,e) R=(f,g):
        //   ( a*e -x b*c )*( a*g -x b*f )
        //     = (a*a+b*b)*( c*f+e*g ) -x (a*c+b*e)*(a*f+b*g)
        // ============================================================
        11 => {
            let v = |x: &str| leaf(x);
            let (pa, pb, pc, pe, pf, pg) =
                (v("va"), v("vb"), v("vc"), v("ve"), v("vf"), v("vg"));
            let xac =
                mi(el, mu(el, pa.clone(), pe.clone()), mu(el, pb.clone(), pc.clone()));
            let xar =
                mi(el, mu(el, pa.clone(), pg.clone()), mu(el, pb.clone(), pf.clone()));
            let aa =
                pl(el, mu(el, pa.clone(), pa.clone()), mu(el, pb.clone(), pb.clone()));
            let cr =
                pl(el, mu(el, pc.clone(), pf.clone()), mu(el, pe.clone(), pg.clone()));
            let ac =
                pl(el, mu(el, pa.clone(), pc.clone()), mu(el, pb.clone(), pe.clone()));
            let ar =
                pl(el, mu(el, pa.clone(), pf.clone()), mu(el, pb.clone(), pg.clone()));
            let lhs = mu(el, xac.clone(), xar.clone());
            let rhs = mi(el, mu(el, aa, cr), mu(el, ac.clone(), ar.clone()));
            return Lemma {
                name: "g3b-crs".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 12 : g3b-eqcancel — abstract degree-4 cancel for the
        //   df-acong-EQ reduction.  Fresh atoms u=AC,v=AR,w=XAC,t=XAR:
        //     ( u*u*( v*v + t*t ) ) -x ( v*v*( u*u + w*w ) )
        //       = ( (u*t)*(u*t) ) -x ( (v*w)*(v*w) )
        //   instantiated with the AC/AR/XAC/XAR subterms (substitution,
        //   no coordinate re-expansion) — keeps ring_eq at degree 4.
        // ============================================================
        12 => {
            let vv = |x: &str| leaf(x);
            let (ju, kv, mw, nt) = (vv("vu"), vv("vv"), vv("vw"), vv("vt"));
            let aarr = pl(el, mu(el, kv.clone(), kv.clone()), mu(el, nt.clone(), nt.clone()));
            let aacc = pl(el, mu(el, ju.clone(), ju.clone()), mu(el, mw.clone(), mw.clone()));
            let lhs = mi(
                el,
                mu(el, mu(el, ju.clone(), ju.clone()), aarr),
                mu(el, mu(el, kv.clone(), kv.clone()), aacc),
            );
            let s1 = mu(el, ju.clone(), nt.clone());
            let s2 = mu(el, kv.clone(), mw.clone());
            let rhs = mi(el, mu(el, s1.clone(), s1.clone()), mu(el, s2.clone(), s2.clone()));
            return Lemma {
                name: "g3b-eqcancel".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 13 : g3b-revsub — generic ( ( w -x v ) + v ) = w
        //   (instantiated with big subterms; trivial degree-1 ring_eq
        //   over 2 fresh atoms, never coordinate-dense).
        // ============================================================
        13 => {
            let v = |x: &str| leaf(x);
            let (w, vv) = (v("vw"), v("vv"));
            let lhs = pl(el, mi(el, w.clone(), vv.clone()), vv.clone());
            return Lemma {
                name: "g3b-revsub".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &w),
            };
        }
        // ============================================================
        // idx 14 : g3b-reassoc — generic ( (a*b)*(c*e) ) = ( (a*c)*(e*b) )
        //   (degree-4 over 4 fresh atoms; instantiated by substitution).
        // ============================================================
        14 => {
            let v = |x: &str| leaf(x);
            let (a, b, c, e) = (v("va"), v("vb"), v("vc"), v("ve"));
            let lhs = mu(el, mu(el, a.clone(), b.clone()), mu(el, c.clone(), e.clone()));
            let rhs = mu(el, mu(el, a.clone(), c.clone()), mu(el, e.clone(), b.clone()));
            return Lemma {
                name: "g3b-reassoc".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 15 : G3bp-protuniq-oriented  (ORIENTED prot-uniq, F0)
        //   ess  g3b.1 : |- ( ACong b a c b a x )
        //        g3b.2 : |- ( 0 <_ ( crs b a c b a x ) )
        //        g3b.3 : |- ( 0 < ( sqd b a ) )
        //   goal       : |- ( Ray b c x )
        //
        // df-acong's bare squared-cosine is mirror-blind across line b-a;
        // the conservative oriented-area term `crs` (df-crs, NOT a
        // geometric axiom) supplies the discarded relative orientation,
        // restoring protractor uniqueness.  Vertex-b form so the
        // conclusion is `Ray b c x` (collinear with b,c + non-negative
        // dot) — exactly what ASA' s7 -> G3c -> G2-incid consumes.
        //
        // Certificate (all CAS-checked; every ring_eq is the degree-4
        // generic-lemma regime, never a dense coordinate polynomial):
        //   A := b->a , C := b->c , R := b->x   (vectors)
        //   AC=dot b a c , AR=dot b a x , AA=sqd b a ,
        //   XAC=AxC , XAR=AxR , XCR=CxR , CR=dot b c x
        //   S1 := AC*XAR , S2 := AR*XAC
        //   * df-acong EQ  ==  S1*S1 -x S2*S2          [Lagrange x2 + cancel]
        //   * AA*XCR       ==  S1 -x S2                 [g3b-m]
        //   * S1*S2        ==  (AC*AR)*(XAC*XAR)        [reassoc]
        //   * XAC*XAR      ==  AA*CR -x AC*AR           [g3b-crs]
        //  From EQ=0 : S1*S1 = S2*S2.  From SGN (df-acong) 0<=AC*AR and
        //  g3b.2 0<=XAC*XAR : 0<=S1*S2.  sqcong => S1=S2 => AA*XCR=0.
        //  g3b.3 0<AA + mulcposcan => XCR=0  (Coll b c x).  And
        //  AA*CR = (XAC*XAR) + AC*AR >= 0 ; 0<AA => 0<=CR (dot b c x).
        //  conj + df-coll/df-ray bi_rev => ( Ray b c x ).
        // ============================================================
        15 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let pc = || leaf("vc");
            let px = || leaf("vx");
            let xa = || xc(pa());
            let ya = || yc(pa());
            let xb = || xc(pb());
            let yb = || yc(pb());
            let xcc = || xc(pc());
            let ycc = || yc(pc());
            let xx = || xc(px());
            let yx = || yc(px());
            // vectors rooted at b
            let ax = || mi(el, xa(), xb()); // (Xc a) -x (Xc b)
            let ay = || mi(el, ya(), yb());
            let cx = || mi(el, xcc(), xb());
            let cy = || mi(el, ycc(), yb());
            let rx = || mi(el, xx(), xb());
            let ry = || mi(el, yx(), yb());
            let dot = |o: Pt, p1: Pt, q: Pt| {
                el.app("tdot", &[("o", o), ("p", p1), ("q", q)], &[]).unwrap()
            };
            let sqd = |a: Pt, b: Pt| el.app("tsqd", &[("a", a), ("b", b)], &[]).unwrap();
            // coordinate forms
            let acc = || pl(el, mu(el, ax(), cx()), mu(el, ay(), cy())); // AC
            let arr = || pl(el, mu(el, ax(), rx()), mu(el, ay(), ry())); // AR
            let aaa = || pl(el, mu(el, ax(), ax()), mu(el, ay(), ay())); // AA
            let ccc = || pl(el, mu(el, cx(), cx()), mu(el, cy(), cy())); // CC
            let rrr = || pl(el, mu(el, rx(), rx()), mu(el, ry(), ry())); // RR
            let crr = || pl(el, mu(el, cx(), rx()), mu(el, cy(), ry())); // CR=dot b c x
            let xac = || mi(el, mu(el, ax(), cy()), mu(el, ay(), cx())); // AxC
            let xar = || mi(el, mu(el, ax(), ry()), mu(el, ay(), rx())); // AxR
            let xcr = || mi(el, mu(el, cx(), ry()), mu(el, cy(), rx())); // CxR
            let s1 = || mu(el, acc(), xar()); // S1
            let s2 = || mu(el, arr(), xac()); // S2
            // df-* term equalities
            let e_dbac = el
                .app("df-dot", &[("o", pb()), ("p", pa()), ("q", pc())], &[])
                .unwrap(); // ( dot b a c ) = AC
            let e_dbax = el
                .app("df-dot", &[("o", pb()), ("p", pa()), ("q", px())], &[])
                .unwrap(); // ( dot b a x ) = AR
            let e_dbcx = el
                .app("df-dot", &[("o", pb()), ("p", pc()), ("q", px())], &[])
                .unwrap(); // ( dot b c x ) = CR
            let e_sba = el.app("df-sqd", &[("a", pb()), ("b", pa())], &[]).unwrap(); // ( sqd b a ) = AA
            let e_sbc = el.app("df-sqd", &[("a", pb()), ("b", pc())], &[]).unwrap(); // ( sqd b c ) = CC
            let e_sbx = el.app("df-sqd", &[("a", pb()), ("b", px())], &[]).unwrap(); // ( sqd b x ) = RR
            let dbac = || dot(pb(), pa(), pc());
            let dbax = || dot(pb(), pa(), px());
            let dbcx = || dot(pb(), pc(), px());
            let sba = || sqd(pb(), pa());
            let sbc = || sqd(pb(), pc());
            let sbx = || sqd(pb(), px());
            // mu congruence helper (as in G3a)
            let mu_rw = |l: Pt, lp: Pt, r: Pt, rp: Pt, pl_eq: Pt, pr_eq: Pt| -> Pt {
                let c1 = cmu1(el, l.clone(), lp.clone(), r.clone(), pl_eq);
                let c2 = cmu2(el, r.clone(), rp.clone(), lp.clone(), pr_eq);
                eqtr3(
                    el,
                    mu(el, l.clone(), r.clone()),
                    mu(el, lp.clone(), r.clone()),
                    mu(el, lp.clone(), rp.clone()),
                    c1,
                    c2,
                )
            };
            // ---- 1. unfold ACong b a c b a x ----
            let acong = el
                .app(
                    "wacong",
                    &[
                        ("o", pb()), ("p", pa()), ("q", pc()),
                        ("a", pb()), ("e", pa()), ("f", px()),
                    ],
                    &[],
                )
                .unwrap();
            let _ = acong;
            // df-acong EQ/SGN in dot/sqd terms (o=b,p=a,q=c ; a=b,e=a,f=x):
            //  EQ : ((dbac*dbac)*((sba)*(sbx))) = ((dbax*dbax)*((sba)*(sbc)))
            //  SGN: 0 <_ ( dbac * dbax )
            let eql_g = mu(el, mu(el, dbac(), dbac()), mu(el, sba(), sbx()));
            let eqr_g = mu(el, mu(el, dbax(), dbax()), mu(el, sba(), sbc()));
            let sgn_g = le(z(), mu(el, dbac(), dbax()));
            let eq_g = eq(eql_g.clone(), eqr_g.clone());
            let conj_g = aw(eq_g.clone(), sgn_g.clone());
            let dfac = el
                .app(
                    "df-acong",
                    &[
                        ("o", pb()), ("p", pa()), ("q", pc()),
                        ("a", pb()), ("e", pa()), ("f", px()),
                    ],
                    &[],
                )
                .unwrap();
            let conj_pf = el.bi_fwd(dfac, leaf("g3b.1")).unwrap(); // |- ( EQ /\ SGN )
            let eq_pf = mp(
                conj_g.clone(),
                eq_g.clone(),
                conj_pf.clone(),
                el.app("simpl", &[("ph", eq_g.clone()), ("ps", sgn_g.clone())], &[])
                    .unwrap(),
            ); // |- ( EQ_l = EQ_r )
            let sgn_pf = mp(
                conj_g.clone(),
                sgn_g.clone(),
                conj_pf,
                el.app("simpr", &[("ph", eq_g.clone()), ("ps", sgn_g.clone())], &[])
                    .unwrap(),
            ); // |- 0 <_ ( dbac * dbax )

            // ---- 2. coordinate forms of EQ_l, EQ_r ----
            let eql_cv = mu(el, mu(el, acc(), acc()), mu(el, aaa(), rrr()));
            let eqr_cv = mu(el, mu(el, arr(), arr()), mu(el, aaa(), ccc()));
            let dd_c = mu_rw(dbac(), acc(), dbac(), acc(), e_dbac.clone(), e_dbac.clone());
            let ss_lc = mu_rw(sba(), aaa(), sbx(), rrr(), e_sba.clone(), e_sbx.clone());
            let eql_coord = mu_rw(
                mu(el, dbac(), dbac()),
                mu(el, acc(), acc()),
                mu(el, sba(), sbx()),
                mu(el, aaa(), rrr()),
                dd_c,
                ss_lc,
            ); // ( EQ_l = eql_cv )
            let dd_x = mu_rw(dbax(), arr(), dbax(), arr(), e_dbax.clone(), e_dbax.clone());
            let ss_rc = mu_rw(sba(), aaa(), sbc(), ccc(), e_sba.clone(), e_sbc.clone());
            let eqr_coord = mu_rw(
                mu(el, dbax(), dbax()),
                mu(el, arr(), arr()),
                mu(el, sba(), sbc()),
                mu(el, aaa(), ccc()),
                dd_x,
                ss_rc,
            ); // ( EQ_r = eqr_cv )
            // EQ_l = EQ_r  -->  eql_cv = eqr_cv
            let eqcv = {
                let t1 = eqcomm(el, eql_g.clone(), eql_cv.clone(), eql_coord.clone()); // (eql_cv=EQ_l)
                let s = eqtr3(el, eql_cv.clone(), eql_g.clone(), eqr_g.clone(), t1, eq_pf);
                eqtr3(el, eql_cv.clone(), eqr_g.clone(), eqr_cv.clone(), s, eqr_coord.clone())
            }; // |- ( eql_cv = eqr_cv )

            // ---- 3. EQ_cv  ==  (S1*S1) -x (S2*S2)  via Lagrange + cancel ----
            // LagC: aaa*ccc = (acc*acc) + (xac*xac)
            let lagc = el
                .app(
                    "g3b-lagc",
                    &[("a", ax()), ("b", ay()), ("c", cx()), ("e", cy())],
                    &[],
                )
                .unwrap();
            // LagR: aaa*rrr = (arr*arr) + (xar*xar)
            let lagr = el
                .app(
                    "g3b-lagr",
                    &[("a", ax()), ("b", ay()), ("f", rx()), ("g", ry())],
                    &[],
                )
                .unwrap();
            let aacc = || pl(el, mu(el, acc(), acc()), mu(el, xac(), xac()));
            let aarr = || pl(el, mu(el, arr(), arr()), mu(el, xar(), xar()));
            // eql_cv = (acc*acc)*aarr   [rewrite aaa*rrr -> aarr]
            let eql_1 = cmu2(el, mu(el, aaa(), rrr()), aarr(), mu(el, acc(), acc()), lagr.clone());
            // eqr_cv = (arr*arr)*aacc
            let eqr_1 = cmu2(el, mu(el, aaa(), ccc()), aacc(), mu(el, arr(), arr()), lagc.clone());
            // abstract cancel — instantiate generic g3b-eqcancel
            // (j=acc,k=arr,m=xac,n=xar); ZERO coordinate ring_eq here.
            let cancel = el
                .app(
                    "g3b-eqcancel",
                    &[
                        ("u", acc()), ("v", arr()),
                        ("w", xac()), ("t", xar()),
                    ],
                    &[],
                )
                .unwrap();
            // eql_cv -x eqr_cv = (acc*acc)*aarr -x (arr*arr)*aacc
            let diff_rw = {
                let d1 = cmi1(
                    el,
                    eql_cv.clone(),
                    mu(el, mu(el, acc(), acc()), aarr()),
                    eqr_cv.clone(),
                    eql_1,
                );
                let d2 = cmi2(
                    el,
                    eqr_cv.clone(),
                    mu(el, mu(el, arr(), arr()), aacc()),
                    mu(el, mu(el, acc(), acc()), aarr()),
                    eqr_1,
                );
                eqtr3(
                    el,
                    mi(el, eql_cv.clone(), eqr_cv.clone()),
                    mi(el, mu(el, mu(el, acc(), acc()), aarr()), eqr_cv.clone()),
                    mi(
                        el,
                        mu(el, mu(el, acc(), acc()), aarr()),
                        mu(el, mu(el, arr(), arr()), aacc()),
                    ),
                    d1,
                    d2,
                )
            }; // ( (eql_cv -x eqr_cv) = ( (acc*acc)*aarr -x (arr*arr)*aacc ) )
            let eqdiff_s = eqtr3(
                el,
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                mi(
                    el,
                    mu(el, mu(el, acc(), acc()), aarr()),
                    mu(el, mu(el, arr(), arr()), aacc()),
                ),
                mi(el, mu(el, s1(), s1()), mu(el, s2(), s2())),
                diff_rw,
                cancel,
            ); // ( (eql_cv -x eqr_cv) = ( S1*S1 -x S2*S2 ) )
            // eql_cv = eqr_cv  =>  (eql_cv -x eqr_cv) = 0
            let cm = cmi1(
                el,
                eql_cv.clone(),
                eqr_cv.clone(),
                eqr_cv.clone(),
                eqcv.clone(),
            );
            let rr0 = el
                .app("subid", &[("u", eqr_cv.clone())], &[])
                .unwrap(); // ( eqr_cv -x eqr_cv ) = 0
            let diff0 = eqtr3(
                el,
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                mi(el, eqr_cv.clone(), eqr_cv.clone()),
                z(),
                cm,
                rr0,
            ); // ( (eql_cv -x eqr_cv) = 0 )
            // ( S1*S1 -x S2*S2 ) = 0
            let s1122_0 = eqtr3(
                el,
                mi(el, mu(el, s1(), s1()), mu(el, s2(), s2())),
                mi(el, eql_cv.clone(), eqr_cv.clone()),
                z(),
                eqcomm(
                    el,
                    mi(el, eql_cv.clone(), eqr_cv.clone()),
                    mi(el, mu(el, s1(), s1()), mu(el, s2(), s2())),
                    eqdiff_s,
                ),
                diff0,
            );
            // subeq0 : ( (S1*S1 -x S2*S2)=0 ) -> ( (S1*S1)=(S2*S2) )
            let s1eq2 = mp(
                eq(mi(el, mu(el, s1(), s1()), mu(el, s2(), s2())), z()),
                eq(mu(el, s1(), s1()), mu(el, s2(), s2())),
                s1122_0,
                el.app(
                    "subeq0",
                    &[("u", mu(el, s1(), s1())), ("v", mu(el, s2(), s2()))],
                    &[],
                )
                .unwrap(),
            ); // |- ( (S1*S1) = (S2*S2) )

            // ---- 4. 0 <_ ( S1 * S2 )  from SGN & g3b.2 ----
            // SGN (coord): 0 <_ ( acc * arr )   [rewrite dbac*dbax -> acc*arr]
            let sgn_cv = {
                let rw = mu_rw(dbac(), acc(), dbax(), arr(), e_dbac.clone(), e_dbax.clone()); // (dbac*dbax)=(acc*arr)
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            ("a", mu(el, dbac(), dbax())),
                            ("b", mu(el, acc(), arr())),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(mu(el, dbac(), dbax()), mu(el, acc(), arr())),
                    imp(
                        le(z(), mu(el, dbac(), dbax())),
                        le(z(), mu(el, acc(), arr())),
                    ),
                    rw,
                    cl2,
                );
                mp(
                    le(z(), mu(el, dbac(), dbax())),
                    le(z(), mu(el, acc(), arr())),
                    sgn_pf,
                    m1,
                )
            }; // |- 0 <_ ( acc * arr )
            // crs hyp g3b.2 : 0 <_ ( crs b a c b a x ).  df-crs unfold:
            //   ( crs b a c b a x ) = ( XAC * XAR )      (o=b,p=a,q=c;a=b,e=a,f=x)
            let e_crs = el
                .app(
                    "df-crs",
                    &[
                        ("o", pb()), ("p", pa()), ("q", pc()),
                        ("a", pb()), ("e", pa()), ("f", px()),
                    ],
                    &[],
                )
                .unwrap(); // ( crs b a c b a x ) = ( XAC * XAR )
            let crs_t = el
                .app(
                    "tcrs",
                    &[
                        ("o", pb()), ("p", pa()), ("q", pc()),
                        ("a", pb()), ("e", pa()), ("f", px()),
                    ],
                    &[],
                )
                .unwrap();
            let crs_cv = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[("a", crs_t.clone()), ("b", mu(el, xac(), xar())), ("c", z())],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(crs_t.clone(), mu(el, xac(), xar())),
                    imp(le(z(), crs_t.clone()), le(z(), mu(el, xac(), xar()))),
                    e_crs.clone(),
                    cl2,
                );
                mp(
                    le(z(), crs_t.clone()),
                    le(z(), mu(el, xac(), xar())),
                    leaf("g3b.2"),
                    m1,
                )
            }; // |- 0 <_ ( XAC * XAR )
            // 0 <_ ( (acc*arr) * (xac*xar) )   [of-lemul0: axiom impl + mp]
            let prod_pos = {
                let lhsu = le(z(), mu(el, acc(), arr()));
                let lhsv = le(z(), mu(el, xac(), xar()));
                let conj = aw(lhsu.clone(), lhsv.clone());
                let conj_pf =
                    conj2(el, lhsu.clone(), lhsv.clone(), sgn_cv.clone(), crs_cv.clone());
                let ax = el
                    .app(
                        "of-lemul0",
                        &[("u", mu(el, acc(), arr())), ("v", mu(el, xac(), xar()))],
                        &[],
                    )
                    .unwrap(); // ( ( (0<_u) /\ (0<_v) ) -> ( 0<_(u*v) ) )
                mp(
                    conj.clone(),
                    le(z(), mu(el, mu(el, acc(), arr()), mu(el, xac(), xar()))),
                    conj_pf,
                    ax,
                )
            };
            // ( S1 * S2 ) = ( (acc*arr) * (xac*xar) )   [g3b-reassoc inst]
            // S1=acc*xar, S2=arr*xac ; a=acc,b=xar,c=arr,e=xac :
            //   (a*b)*(c*e) = (a*c)*(e*b)
            let s1s2_re = el
                .app(
                    "g3b-reassoc",
                    &[("a", acc()), ("b", xar()), ("c", arr()), ("e", xac())],
                    &[],
                )
                .unwrap();
            let s1s2_pos = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            ("a", mu(el, mu(el, acc(), arr()), mu(el, xac(), xar()))),
                            ("b", mu(el, s1(), s2())),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(
                        mu(el, mu(el, acc(), arr()), mu(el, xac(), xar())),
                        mu(el, s1(), s2()),
                    ),
                    imp(
                        le(z(), mu(el, mu(el, acc(), arr()), mu(el, xac(), xar()))),
                        le(z(), mu(el, s1(), s2())),
                    ),
                    eqcomm(
                        el,
                        mu(el, s1(), s2()),
                        mu(el, mu(el, acc(), arr()), mu(el, xac(), xar())),
                        s1s2_re,
                    ),
                    cl2,
                );
                mp(
                    le(z(), mu(el, mu(el, acc(), arr()), mu(el, xac(), xar()))),
                    le(z(), mu(el, s1(), s2())),
                    prod_pos,
                    m1,
                )
            }; // |- 0 <_ ( S1 * S2 )

            // ---- 5. sqcong : S1=S2 ; then AA*XCR=0 ; XCR=0 (Coll) ----
            let s1_eq_s2 = el
                .app("sqcong", &[("u", s1()), ("v", s2())], &[s1eq2, s1s2_pos])
                .unwrap(); // |- ( S1 = S2 )
            // g3b-m : AA*XCR = S1 -x S2
            let gm = el
                .app(
                    "g3b-m",
                    &[
                        ("a", ax()), ("b", ay()), ("c", cx()),
                        ("e", cy()), ("f", rx()), ("g", ry()),
                    ],
                    &[],
                )
                .unwrap(); // ( aaa*xcr ) = ( S1 -x S2 )
            // S1=S2 -> (S1 -x S2)=0  [via subeq0 converse: cmi1 + ring]
            let s1s2_0 = {
                let cm = cmi1(el, s1(), s2(), s2(), s1_eq_s2.clone()); // (S1-xS2)=(S2-xS2)
                let r0 = el.app("subid", &[("u", s2())], &[]).unwrap(); // (S2-xS2)=0
                eqtr3(el, mi(el, s1(), s2()), mi(el, s2(), s2()), z(), cm, r0)
            }; // ( (S1 -x S2) = 0 )
            let aaxcr_0 = eqtr3(
                el,
                mu(el, aaa(), xcr()),
                mi(el, s1(), s2()),
                z(),
                gm,
                s1s2_0,
            ); // |- ( (aaa*xcr) = 0 )
            // mulcposcan : 0<aaa , (xcr*aaa)=(0*aaa) => xcr=0
            // build (xcr*aaa)=(0*aaa): from aaa*xcr=0 commute + 0*aaa=0
            let xcr_aaa = el
                .app("of-mulcom", &[("u", aaa()), ("v", xcr())], &[])
                .unwrap(); // ( aaa*xcr )=( xcr*aaa )
            let xcr_aaa_0 = eqtr3(
                el,
                mu(el, xcr(), aaa()),
                mu(el, aaa(), xcr()),
                z(),
                eqcomm(el, mu(el, aaa(), xcr()), mu(el, xcr(), aaa()), xcr_aaa),
                aaxcr_0,
            ); // ( (xcr*aaa) = 0 )
            let z_aaa0 = el.app("mul0", &[("u", aaa())], &[]).unwrap(); // ( (0*aaa)=0 )
            let xcr_eq_0aaa = eqtr3(
                el,
                mu(el, xcr(), aaa()),
                z(),
                mu(el, z(), aaa()),
                xcr_aaa_0,
                eqcomm(el, mu(el, z(), aaa()), z(), z_aaa0),
            ); // ( (xcr*aaa) = (0*aaa) )
            // 0 < (sqd b a) -> 0 < aaa   [rewrite sba -> aaa]
            let aaa_pos = {
                let cl2 = el
                    .app(
                        "cong-lt2",
                        &[("a", sba()), ("b", aaa()), ("c", z())],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(sba(), aaa()),
                    imp(lt(z(), sba()), lt(z(), aaa())),
                    e_sba.clone(),
                    cl2,
                );
                mp(lt(z(), sba()), lt(z(), aaa()), leaf("g3b.3"), m1)
            }; // |- 0 < aaa
            let xcr_0 = el
                .app(
                    "mulcposcan",
                    &[("u", xcr()), ("v", z()), ("w", aaa())],
                    &[aaa_pos.clone(), xcr_eq_0aaa],
                )
                .unwrap(); // |- ( xcr = 0 )

            // ---- 6. Coll b c x  via df-coll ----
            // df-coll b c x : ( Coll b c x ) <-> ( (Xc c -x Xc b)*(Yc x -x Yc b)
            //                  = (Yc c -x Yc b)*(Xc x -x Xc b) )
            //   i.e.  ( cx*ry ) = ( cy*rx )   [note: that is xcr=0 reordered]
            let coll = el
                .app("wcoll", &[("a", pb()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let dfcoll = el
                .app("df-coll", &[("a", pb()), ("b", pc()), ("c", px())], &[])
                .unwrap(); // ( Coll b c x ) <-> ( (cx*ry) = (cy*rx) )
            // from ( xcr = 0 ) i.e. ( (cx*ry -x cy*rx) = 0 ) get (cx*ry)=(cy*rx)
            let coll_eq = mp(
                eq(xcr(), z()),
                eq(mu(el, cx(), ry()), mu(el, cy(), rx())),
                xcr_0,
                el.app(
                    "subeq0",
                    &[("u", mu(el, cx(), ry())), ("v", mu(el, cy(), rx()))],
                    &[],
                )
                .unwrap(),
            ); // |- ( (cx*ry) = (cy*rx) )
            let coll_pf = el.bi_rev(dfcoll, coll_eq).unwrap(); // |- ( Coll b c x )

            // ---- 7. 0 <_ ( dot b c x )  via g3b-crs ----
            // g3b-crs : ( xac*xar ) = ( aaa*crr -x acc*arr )
            let gcrs = el
                .app(
                    "g3b-crs",
                    &[
                        ("a", ax()), ("b", ay()), ("c", cx()),
                        ("e", cy()), ("f", rx()), ("g", ry()),
                    ],
                    &[],
                )
                .unwrap();
            // 0 <_ ( aaa*crr -x acc*arr )   [rewrite from crs_cv]
            let diff_pos = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            ("a", mu(el, xac(), xar())),
                            ("b", mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr()))),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(
                        mu(el, xac(), xar()),
                        mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr())),
                    ),
                    imp(
                        le(z(), mu(el, xac(), xar())),
                        le(z(), mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr()))),
                    ),
                    gcrs,
                    cl2,
                );
                mp(
                    le(z(), mu(el, xac(), xar())),
                    le(z(), mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr()))),
                    crs_cv.clone(),
                    m1,
                )
            }; // |- 0 <_ ( aaa*crr -x acc*arr )
            // 0<_( (aaa*crr -x acc*arr) + (acc*arr) )   [le0add]
            let sum_pos = el
                .app(
                    "le0add",
                    &[
                        ("u", mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr()))),
                        ("v", mu(el, acc(), arr())),
                    ],
                    &[diff_pos, sgn_cv.clone()],
                )
                .unwrap(); // |- 0<_( (aaa*crr -x acc*arr) + (acc*arr) )
            // g3b-revsub inst (w=aaa*crr, v=acc*arr): ((w-xv)+v)=w
            let sum_eq = el
                .app(
                    "g3b-revsub",
                    &[("w", mu(el, aaa(), crr())), ("v", mu(el, acc(), arr()))],
                    &[],
                )
                .unwrap();
            let aaacrr_pos = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[
                            (
                                "a",
                                pl(
                                    el,
                                    mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr())),
                                    mu(el, acc(), arr()),
                                ),
                            ),
                            ("b", mu(el, aaa(), crr())),
                            ("c", z()),
                        ],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(
                        pl(
                            el,
                            mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr())),
                            mu(el, acc(), arr()),
                        ),
                        mu(el, aaa(), crr()),
                    ),
                    imp(
                        le(
                            z(),
                            pl(
                                el,
                                mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr())),
                                mu(el, acc(), arr()),
                            ),
                        ),
                        le(z(), mu(el, aaa(), crr())),
                    ),
                    sum_eq,
                    cl2,
                );
                mp(
                    le(
                        z(),
                        pl(
                            el,
                            mi(el, mu(el, aaa(), crr()), mu(el, acc(), arr())),
                            mu(el, acc(), arr()),
                        ),
                    ),
                    le(z(), mu(el, aaa(), crr())),
                    sum_pos,
                    m1,
                )
            }; // |- 0 <_ ( aaa * crr )
            // lecpos : ess 0<=(w*t) => ( (0<w) -> (0<=t) ) ; w=aaa t=crr
            let lecpos_impl = el
                .app("lecpos", &[("w", aaa()), ("t", crr())], &[aaacrr_pos])
                .unwrap(); // |- ( (0<aaa) -> (0<=crr) )
            let crr_pos = mp(
                lt(z(), aaa()),
                le(z(), crr()),
                aaa_pos,
                lecpos_impl,
            ); // |- 0 <_ crr
            // crr = ( dot b c x )  -> 0 <_ ( dot b c x )
            let dbcx_pos = {
                let cl2 = el
                    .app(
                        "cong-le2",
                        &[("a", crr()), ("b", dbcx()), ("c", z())],
                        &[],
                    )
                    .unwrap();
                let m1 = mp(
                    eq(crr(), dbcx()),
                    imp(le(z(), crr()), le(z(), dbcx())),
                    eqcomm(el, dbcx(), crr(), e_dbcx.clone()),
                    cl2,
                );
                mp(le(z(), crr()), le(z(), dbcx()), crr_pos, m1)
            }; // |- 0 <_ ( dot b c x )

            // ---- 8. fold Ray b c x via df-ray ----
            let dbcx_sgn = le(z(), dbcx());
            let conj_r = aw(coll.clone(), dbcx_sgn.clone());
            let conj_r_pf = conj2(el, coll.clone(), dbcx_sgn.clone(), coll_pf, dbcx_pos);
            let dfray = el
                .app("df-ray", &[("a", pb()), ("b", pc()), ("c", px())], &[])
                .unwrap(); // ( Ray b c x ) <-> ( ( Coll b c x ) /\ ( 0 <_ ( dot b c x ) ) )
            let _ = conj_r;
            let g = el.bi_rev(dfray, conj_r_pf).unwrap(); // |- ( Ray b c x )
            Lemma {
                name: "G3bp-protuniq-oriented".into(),
                ess: vec![
                    (
                        "g3b.1".into(),
                        toks(&[
                            "|-", "(", "ACong", "b", "a", "c", "b", "a", "x", ")",
                        ]),
                    ),
                    (
                        "g3b.2".into(),
                        toks(&[
                            "|-", "(", "0", "<_", "(", "crs", "b", "a", "c", "b",
                            "a", "x", ")", ")",
                        ]),
                    ),
                    (
                        "g3b.3".into(),
                        toks(&[
                            "|-", "(", "0", "<", "(", "sqd", "b", "a", ")", ")",
                        ]),
                    ),
                ],
                goal: g,
            }
        }
        _ => unreachable!(),
    }
}
