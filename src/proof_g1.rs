//! G1 ruler (no-cheating), staged after the core 57 lemmas + proof_g2/g3.
//!
//! The Birkhoff ruler/segment-construction postulate, derived rather
//! than asserted.  Needs the field inverse and a principal square root
//! (substrate axioms `of-recip`, `of-sqrtnn`, `ax-sqrt`; the
//! conservative definition `df-cp`).
//!
//! Lemmas contributed (idx order):
//!   0  sqdnn       |- ( 0 <_ ( sqd a b ) )                       (no ess)
//!   1  posfromne   ess 0<=X , -.(X=0)  =>  |- ( 0 < X )
//!   2  recipnn     ess -.(X=0) , 0<=X  =>  |- ( 0 <_ ( inv X ) )
//!   3  g1-sqdid    generic deg-4 ring identity (sqd-of-cp factoring)
//!   4  g1-collid   generic deg-2 ring identity (collinearity)
//!   5  g1-dotid    generic deg-3 ring identity (dot factoring)
//!   6  G1b-rulerd  ess g1b.1,g1b.2 => |- ( sqd a ( cp a c u ) ) = u
//!   7  G1a-rulerr  ess g1a.1,g1a.2 => |- ( Ray a c ( cp a c u ) )
//! (distinct ess labels per scope: the kernel db treats $e labels as
//!  globally unique even across separate ${ $} blocks.)
//!
//! Generic identities are proved ONCE over fresh `$f term` atoms and
//! instantiated with the coordinate subterms by substitution (no
//! re-expansion) — the proven template.

#[allow(unused_imports)]
use super::*;

/// Number of staged lemmas this module contributes.
pub fn count() -> usize {
    8
}

/// Build local lemma `idx` against an `Elab` over the current db.
#[allow(unused_variables)]
pub fn make(idx: usize, el: &Elab) -> Lemma {
    let n = |p: Pt| el.app("wn", &[("ph", p)], &[]).unwrap();
    let i = |p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let a = |p: Pt, q: Pt| el.app("wa", &[("ph", p), ("ps", q)], &[]).unwrap();
    let b = |p: Pt, q: Pt| el.app("wb", &[("ph", p), ("ps", q)], &[]).unwrap();
    let mp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };
    let syl = |p: Pt, q: Pt, r: Pt, s1: Pt, s2: Pt| {
        el.app("syl", &[("ph", p), ("ps", q), ("ch", r)], &[s1, s2])
            .unwrap()
    };
    let z = || t0p(el);
    let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
    let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
    let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
    let xc = |p: Pt| el.app("txc", &[("a", p)], &[]).unwrap();
    let yc = |p: Pt| el.app("tyc", &[("a", p)], &[]).unwrap();
    let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
    let dot = |o: Pt, p: Pt, q: Pt| {
        el.app("tdot", &[("o", o), ("p", p), ("q", q)], &[]).unwrap()
    };
    let cong_mu1 = |l: Pt, r: Pt, w: Pt, p: Pt| cmu1(el, l, r, w, p);
    let cong_mu2 = |l: Pt, r: Pt, w: Pt, p: Pt| cmu2(el, l, r, w, p);
    // ( X * 0 ) = 0   (ring_eq does NOT collapse X*0; via of-mulcom+mul0)
    let mul0r = |t: Pt| -> Pt {
        let comm = el
            .app("of-mulcom", &[("u", t.clone()), ("v", z())], &[])
            .unwrap(); // ( (t*0) = (0*t) )
        let m0l = el.app("mul0", &[("u", t.clone())], &[]).unwrap(); // ( (0*t)=0 )
        eqtr3(el, mu(el, t.clone(), z()), mu(el, z(), t.clone()), z(), comm, m0l)
    };

    match idx {
        // ============================================================
        // idx 0 : sqdnn  |- ( 0 <_ ( sqd a b ) )
        //   df-sqd unfolds sqd a b to ( DX*DX + DY*DY ); each square
        //   >=0 (of-sqpos); le0add sums them; cong-le2 folds back.
        // ============================================================
        0 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let dx = || mi(el, xc(pb()), xc(pa()));
            let dy = || mi(el, yc(pb()), yc(pa()));
            let sq_x = mu(el, dx(), dx());
            let sq_y = mu(el, dy(), dy());
            let expr = pl(el, sq_x.clone(), sq_y.clone());
            // 0 <_ (DX*DX) , 0 <_ (DY*DY)
            let pxx = el.app("of-sqpos", &[("u", dx())], &[]).unwrap();
            let pyy = el.app("of-sqpos", &[("u", dy())], &[]).unwrap();
            // le0add : |-(0<_a),|-(0<_b) => |-(0<_(a+b))
            let sum_nn = el
                .app(
                    "le0add",
                    &[("u", sq_x.clone()), ("v", sq_y.clone())],
                    &[pxx, pyy],
                )
                .unwrap(); // |- ( 0 <_ ( (DX*DX)+(DY*DY) ) )
            // df-sqd : ( sqd a b ) = expr ; rewrite 0 <_ expr  ->  0 <_ sqd
            let dfs = el.app("df-sqd", &[("a", pa()), ("b", pb())], &[]).unwrap();
            // ( expr = ( sqd a b ) )
            let expr_eq_sqd = eqcomm(el, sqd(pa(), pb()), expr.clone(), dfs);
            let cl2 = el
                .app(
                    "cong-le2",
                    &[("a", expr.clone()), ("b", sqd(pa(), pb())), ("c", z())],
                    &[],
                )
                .unwrap(); // ( expr = sqd -> ( (0<_expr) -> (0<_sqd) ) )
            let step = mp(
                eq(expr.clone(), sqd(pa(), pb())),
                i(le(z(), expr.clone()), le(z(), sqd(pa(), pb()))),
                expr_eq_sqd,
                cl2,
            );
            let g = mp(
                le(z(), expr.clone()),
                le(z(), sqd(pa(), pb())),
                sum_nn,
                step,
            );
            Lemma { name: "sqdnn".into(), ess: vec![], goal: g }
        }
        // ============================================================
        // idx 1 : posfromne
        //   ess  posfromne.1 : |- ( 0 <_ X )
        //        posfromne.2 : |- -. ( X = 0 )
        //   goal : |- ( 0 < X )
        // ============================================================
        1 => {
            let x = || leaf("vx");
            let h1 = || leaf("posfromne.1"); // |- ( 0 <_ X )
            let h2 = || leaf("posfromne.2"); // |- -. ( X = 0 )
            // ltII(0,X) : ( (0<_X) -> ( -.(X<_0) -> (0<X) ) )
            let ltii = el.app("ltII", &[("u", z()), ("v", x())], &[]).unwrap();
            let after_h1 = mp(
                le(z(), x()),
                i(n(le(x(), z())), lt(z(), x())),
                h1(),
                ltii,
            ); // ( -.(X<_0) -> (0<X) )
            // lein2(0,X) : ( (0<_X) -> ( (X<_0) -> (0=X) ) )
            let lein2 = el.app("lein2", &[("u", z()), ("v", x())], &[]).unwrap();
            let xle0_eq = mp(
                le(z(), x()),
                i(le(x(), z()), eq(z(), x())),
                h1(),
                lein2,
            ); // ( (X<_0) -> (0=X) )
            // eqcom : ( (0=X) -> (X=0) )
            let ec = el.app("eqcom", &[("x", z()), ("y", x())], &[]).unwrap();
            let xle0_x0 = syl(le(x(), z()), eq(z(), x()), eq(x(), z()), xle0_eq, ec);
            // mt : ( (X<_0)->(X=0) ) , -.(X=0)  =>  -.(X<_0)
            let nxle0 = el
                .app(
                    "mt",
                    &[("ph", le(x(), z())), ("ps", eq(x(), z()))],
                    &[xle0_x0, h2()],
                )
                .unwrap(); // |- -.(X<_0)
            let g = mp(n(le(x(), z())), lt(z(), x()), nxle0, after_h1);
            Lemma {
                name: "posfromne".into(),
                ess: vec![
                    (
                        "posfromne.1".into(),
                        toks(&["|-", "(", "0", "<_", "x", ")"]),
                    ),
                    (
                        "posfromne.2".into(),
                        toks(&["|-", "-.", "x", "=", "0"]),
                    ),
                ],
                goal: g,
            }
        }
        // ============================================================
        // idx 2 : recipnn
        //   ess  recipnn.1 : |- -. ( X = 0 )
        //        recipnn.2 : |- ( 0 <_ X )
        //   goal : |- ( 0 <_ ( inv X ) )
        //   By of-letot( inv X , 0 ): both branches yield 0 <_ inv X.
        //     branch (0 <_ inv X): immediate.
        //     branch (inv X <_ 0): lemul0mono(inv X,0,X) gives
        //        ( inv X * X ) <_ ( 0 * X );  inv X*X = X*inv X = 1
        //        (of-mulcom+of-recip), 0*X=0 (mul0)  => 1 <_ 0 ;
        //        with 0 <_ 1 (of-sqpos+of-mul1) of-lein => 1 = 0 ;
        //        then inv X = inv X*1 = inv X*0 = 0  => 0 <_ inv X.
        // ============================================================
        2 => {
            let x = || leaf("vx");
            let h1 = || leaf("recipnn.1"); // |- -. ( X = 0 )
            let h2 = || leaf("recipnn.2"); // |- ( 0 <_ X )
            let ix = || el.app("tinv", &[("u", x())], &[]).unwrap();
            let goal_le = || le(z(), ix());
            // ---- branch B : ( 0 <_ inv X ) -> goal  (identity) ----
            let br_b = el
                .app("id", &[("ph", goal_le())], &[]).unwrap(); // ( (0<_invX) -> (0<_invX) )
            // ---- branch A : ( inv X <_ 0 ) -> ( 0 <_ inv X ) ----
            // lemul0mono : ess (u<_v),(0<_w) => ( (u*w) <_ (v*w) ).
            // We need it as an implication chain; build via expi-free
            // direct: from hyps (inv X <_ 0) and h2 (0 <_ X) produce
            // ( (inv X * X) <_ (0 * X) ).  lemul0mono takes ess proofs,
            // so wrap the branch's antecedent with a deduction.
            //
            // Construct ( (inv X <_ 0) -> ( (inv X*X) <_ (0*X) ) ):
            //   instantiate lemul0mono with u=inv X, v=0, w=X needs the
            //   two ess as *proofs*; the (0<_X) one is h2 (a theorem),
            //   the (inv X<_0) one is the branch hypothesis.  So we use
            //   the closed lemma `lemul0monod` is not available; instead
            //   re-derive via le2sub/lemul02/sub2le inline is heavy.
            //   Simpler: prove the contrapositive-free closed form here.
            //
            // ( inv X <_ 0 ) -> ( (inv X * X) <_ (0 * X) )
            // We get this from of-leadd-style?  No: it is precisely the
            // monotone-multiply.  Use lemul02 + le2sub/sub2le path:
            //   (inv X <_ 0)  =>  0 <_ ( 0 -x inv X )            [le2sub]
            //   lemul02( (0-x inv X), X ) with h2 => 0 <_ ((0-x inv X)*X)
            //   ring: ((0-x inv X)*X) = ( (0*X) -x (inv X*X) )   [ring_eq]
            //   sub2le => ( inv X*X ) <_ ( 0*X )
            let nix = mi(el, z(), ix()); // ( 0 -x inv X )
            // le2sub : ( u <_ v ) -> ( 0 <_ ( v -x u ) )
            let le2sub = el
                .app("le2sub", &[("u", ix()), ("v", z())], &[])
                .unwrap(); // ( (invX<_0) -> ( 0 <_ ( 0 -x invX ) ) )
            // lemul02 : ( 0<_a ) -> ( ( 0<_b ) -> ( 0<_(a*b) ) )
            let lemul02 = el
                .app("lemul02", &[("u", nix.clone()), ("v", x())], &[])
                .unwrap();
            let lm_after_h2 = {
                // lemul02 : ( (0<_nix) -> ( (0<_X) -> (0<_(nix*X)) ) )
                // com12   : ( (0<_X) -> ( (0<_nix) -> (0<_(nix*X)) ) )
                // mp h2   : ( (0<_nix) -> (0<_(nix*X)) )
                let swapped = el
                    .app(
                        "com12",
                        &[
                            ("ph", le(z(), nix.clone())),
                            ("ps", le(z(), x())),
                            ("ch", le(z(), mu(el, nix.clone(), x()))),
                        ],
                        &[lemul02],
                    )
                    .unwrap(); // ( (0<_X) -> ( (0<_nix) -> (0<_(nix*X)) ) )
                mp(
                    le(z(), x()),
                    i(le(z(), nix.clone()), le(z(), mu(el, nix.clone(), x()))),
                    h2(),
                    swapped,
                )
            }; // ( (0<_(0-xinvX)) -> (0<_((0-xinvX)*X)) )
            // chain: (invX<_0) -> (0<_(0-xinvX)) -> (0<_((0-xinvX)*X))
            let s1 = syl(
                le(ix(), z()),
                le(z(), nix.clone()),
                le(z(), mu(el, nix.clone(), x())),
                le2sub,
                lm_after_h2,
            ); // ( (invX<_0) -> (0<_((0-xinvX)*X)) )
            // ring: ((0-xinvX)*X) = ( 0 -x (invX*X) )   (no 0*X term)
            let prod = mu(el, nix.clone(), x());
            let diff = mi(el, z(), mu(el, ix(), x()));
            let ring1 = ring_eq(el, &prod, &diff);
            // rewrite 0<_prod  ->  0<_diff
            let cl2 = el
                .app(
                    "cong-le2",
                    &[("a", prod.clone()), ("b", diff.clone()), ("c", z())],
                    &[],
                )
                .unwrap();
            let prod_to_diff = mp(
                eq(prod.clone(), diff.clone()),
                i(le(z(), prod.clone()), le(z(), diff.clone())),
                ring1,
                cl2,
            );
            let prdla1 = el
                .app(
                    "a1i",
                    &[("ph", i(le(z(), prod.clone()), le(z(), diff.clone()))), ("ps", le(ix(), z()))],
                    &[prod_to_diff],
                )
                .unwrap();
            let s2 = el
                .app(
                    "mpd",
                    &[
                        ("ph", le(ix(), z())),
                        ("ps", le(z(), prod.clone())),
                        ("ch", le(z(), diff.clone())),
                    ],
                    &[s1, prdla1],
                )
                .unwrap(); // ( (invX<_0) -> ( 0 <_ ( 0 -x (invX*X) ) ) )
            // sub2le : ( 0 <_ ( v -x u ) ) -> ( u <_ v )   [u=invX*X, v=0]
            let sub2le = el
                .app(
                    "sub2le",
                    &[("u", mu(el, ix(), x())), ("v", z())],
                    &[],
                )
                .unwrap();
            let s3 = syl(
                le(ix(), z()),
                le(z(), diff.clone()),
                le(mu(el, ix(), x()), z()),
                s2,
                sub2le,
            ); // ( (invX<_0) -> ( (invX*X) <_ 0 ) )
            // invX*X = 1 :  of-mulcom + of-recip
            let comm = el
                .app("of-mulcom", &[("u", ix()), ("v", x())], &[])
                .unwrap(); // ( (invX*X) = (X*invX) )
            let recip = mp(
                n(eq(x(), z())),
                eq(mu(el, x(), ix()), el.app("t1", &[], &[]).unwrap()),
                h1(),
                el.app("of-recip", &[("u", x())], &[]).unwrap(),
            ); // |- ( (X*invX) = 1 )
            let one = || el.app("t1", &[], &[]).unwrap();
            let ixx_eq_1 = eqtr3(
                el,
                mu(el, ix(), x()),
                mu(el, x(), ix()),
                one(),
                comm,
                recip,
            ); // ( (invX*X) = 1 )
            // rewrite s3's conclusion ( (invX*X) <_ 0 ) to ( 1 <_ 0 )
            let cl1 = el
                .app(
                    "cong-le1",
                    &[("a", mu(el, ix(), x())), ("b", one()), ("c", z())],
                    &[],
                )
                .unwrap(); // ( (invX*X)=1 -> ( ((invX*X)<_0) -> (1<_0) ) )
            let to_1le0 = mp(
                eq(mu(el, ix(), x()), one()),
                i(le(mu(el, ix(), x()), z()), le(one(), z())),
                ixx_eq_1,
                cl1,
            ); // ( ((invX*X)<_0) -> (1<_0) )
            let s4 = syl(
                le(ix(), z()),
                le(mu(el, ix(), x()), z()),
                le(one(), z()),
                s3,
                to_1le0,
            ); // ( (invX<_0) -> ( 1 <_ 0 ) )
            // 0 <_ 1   (of-sqpos(1) gives 0<_(1*1); of-mul1 (1*1)=1)
            let sq1 = el.app("of-sqpos", &[("u", one())], &[]).unwrap(); // 0<_(1*1)
            let m11 = el.app("of-mul1", &[("u", one())], &[]).unwrap(); // (1*1)=1
            let cl2c = el
                .app(
                    "cong-le2",
                    &[("a", mu(el, one(), one())), ("b", one()), ("c", z())],
                    &[],
                )
                .unwrap();
            let zle1 = mp(
                eq(mu(el, one(), one()), one()),
                i(le(z(), mu(el, one(), one())), le(z(), one())),
                m11,
                cl2c,
            );
            let zle1 = mp(le(z(), mu(el, one(), one())), le(z(), one()), sq1, zle1); // |- (0<_1)
            // of-lein( 1, 0 ) : ( (1<_0 /\ 0<_1) -> 1=0 )
            let lein = el.app("of-lein", &[("u", one()), ("v", z())], &[]).unwrap();
            // build ( (invX<_0) -> (1=0) ): conj of s4 and (0<_1) const
            let zle1_a1 = el
                .app(
                    "a1i",
                    &[("ph", le(z(), one())), ("ps", le(ix(), z()))],
                    &[zle1],
                )
                .unwrap(); // ( (invX<_0) -> (0<_1) )
            let conj_d = el
                .app(
                    "jca",
                    &[
                        ("ph", le(ix(), z())),
                        ("ps", le(one(), z())),
                        ("ch", le(z(), one())),
                    ],
                    &[s4, zle1_a1],
                )
                .unwrap(); // ( (invX<_0) -> ( (1<_0) /\ (0<_1) ) )
            let s5 = syl(
                le(ix(), z()),
                a(le(one(), z()), le(z(), one())),
                eq(one(), z()),
                conj_d,
                lein,
            ); // ( (invX<_0) -> ( 1 = 0 ) )
            // From (1=0) : inv X = inv X*1 = inv X*0 = 0
            let m1ix = el.app("of-mul1", &[("u", ix())], &[]).unwrap(); // (invX*1)=invX
            let ix_eq_ix1 = eqcomm(el, mu(el, ix(), one()), ix(), m1ix); // invX = invX*1
            // ( 1=0 ) -> ( invX*1 = invX*0 )
            let cm2 = el
                .app(
                    "cong-mu2",
                    &[("a", one()), ("b", z()), ("c", ix())],
                    &[],
                )
                .unwrap(); // ( 1=0 -> ( invX*1 = invX*0 ) )
            // invX*0 = 0
            let ix0_0 = mul0r(ix()); // ( (invX*0)=0 )
            let _ = cm2; // cong-mu2 rebuilt below as an implication for syl
            let cm2_imp = el
                .app(
                    "cong-mu2",
                    &[("a", one()), ("b", z()), ("c", ix())],
                    &[],
                )
                .unwrap(); // ( 1=0 -> ( invX*1 = invX*0 ) )
            let d1 = syl(
                le(ix(), z()),
                eq(one(), z()),
                eq(mu(el, ix(), one()), mu(el, ix(), z())),
                s5,
                cm2_imp,
            ); // ( (invX<_0) -> ( invX*1 = invX*0 ) )
            // chain invX = invX*1 = invX*0 = 0 under (invX<_0)
            let ix_eq_ix1_a1 = el
                .app(
                    "a1i",
                    &[("ph", eq(ix(), mu(el, ix(), one()))), ("ps", le(ix(), z()))],
                    &[ix_eq_ix1],
                )
                .unwrap(); // ( (invX<_0) -> ( invX = invX*1 ) )
            let ix0_0_a1 = el
                .app(
                    "a1i",
                    &[("ph", eq(mu(el, ix(), z()), z())), ("ps", le(ix(), z()))],
                    &[ix0_0],
                )
                .unwrap(); // ( (invX<_0) -> ( invX*0 = 0 ) )
            let t1 = el
                .app(
                    "eqtrd",
                    &[
                        ("ph", le(ix(), z())),
                        ("x", ix()),
                        ("y", mu(el, ix(), one())),
                        ("z", mu(el, ix(), z())),
                    ],
                    &[ix_eq_ix1_a1, d1],
                )
                .unwrap(); // ( (invX<_0) -> ( invX = invX*0 ) )
            let ix_eq_0_d = el
                .app(
                    "eqtrd",
                    &[
                        ("ph", le(ix(), z())),
                        ("x", ix()),
                        ("y", mu(el, ix(), z())),
                        ("z", z()),
                    ],
                    &[t1, ix0_0_a1],
                )
                .unwrap(); // ( (invX<_0) -> ( invX = 0 ) )
            // ( invX = 0 ) -> ( 0 <_ invX )   via 0<_0 (lerefl) + cong-le2
            let lerefl0 = el.app("lerefl", &[("u", z())], &[]).unwrap(); // ( 0 <_ 0 )
            // need ( invX=0 ) -> ( (0<_0) -> (0<_invX) ) : cong-le2(0,invX,0)
            //   cong-le2 : ( a=b -> ( (c<_a) -> (c<_b) ) ) with a=0,b=invX,c=0
            //   needs ( 0 = invX ); from ( invX = 0 ) by eqcom.
            let invx_eq_0_to_0_eq_invx = el
                .app("eqcom", &[("x", ix()), ("y", z())], &[])
                .unwrap(); // ( (invX=0) -> (0=invX) )
            let cl2d = el
                .app(
                    "cong-le2",
                    &[("a", z()), ("b", ix()), ("c", z())],
                    &[],
                )
                .unwrap(); // ( 0=invX -> ( (0<_0) -> (0<_invX) ) )
            let lerefl_a1 = el
                .app(
                    "a1i",
                    &[("ph", le(z(), z())), ("ps", eq(z(), ix()))],
                    &[lerefl0],
                )
                .unwrap(); // ( (0=invX) -> (0<_0) )
            let from_0eqinvx = el
                .app(
                    "mpd",
                    &[
                        ("ph", eq(z(), ix())),
                        ("ps", le(z(), z())),
                        ("ch", le(z(), ix())),
                    ],
                    &[lerefl_a1, cl2d],
                )
                .unwrap(); // ( (0=invX) -> (0<_invX) )
            let from_invx0 = syl(
                eq(ix(), z()),
                eq(z(), ix()),
                le(z(), ix()),
                invx_eq_0_to_0_eq_invx,
                from_0eqinvx,
            ); // ( (invX=0) -> (0<_invX) )
            let br_a = syl(
                le(ix(), z()),
                eq(ix(), z()),
                le(z(), ix()),
                ix_eq_0_d,
                from_invx0,
            ); // ( (invX<_0) -> (0<_invX) )
            // jaoi over of-letot( inv X, 0 ) : ( (invX<_0) \/ (0<_invX) ) -> (0<_invX)
            let jao = el
                .app(
                    "jaoi",
                    &[
                        ("ph", le(ix(), z())),
                        ("ps", le(z(), ix())),
                        ("ch", le(z(), ix())),
                    ],
                    &[br_a, br_b],
                )
                .unwrap();
            let owo = el
                .app("wo", &[("ph", le(ix(), z())), ("ps", le(z(), ix()))], &[])
                .unwrap();
            let tot = el
                .app("of-letot", &[("u", ix()), ("v", z())], &[])
                .unwrap(); // ( (invX<_0) \/ (0<_invX) )
            let g = mp(owo, le(z(), ix()), tot, jao);
            Lemma {
                name: "recipnn".into(),
                ess: vec![
                    (
                        "recipnn.1".into(),
                        toks(&["|-", "-.", "x", "=", "0"]),
                    ),
                    (
                        "recipnn.2".into(),
                        toks(&["|-", "(", "0", "<_", "x", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ============================================================
        // idx 3 : g1-sqdid  (generic, deg 4) — sqd-of-cp factoring
        //   ( ((A+R*(C-A))-A)*((A+R*(C-A))-A)
        //   + ((B+R*(D-B))-B)*((B+R*(D-B))-B) )
        //   = ( (R*R) * ( (C-A)*(C-A) + (D-B)*(D-B) ) )
        // ============================================================
        3 => {
            let v = |s: &str| leaf(s);
            let (av, bv, cv, dv, rv) =
                (v("va"), v("vb"), v("vc"), v("ve"), v("vf"));
            let xcp = pl(el, av.clone(), mu(el, rv.clone(), mi(el, cv.clone(), av.clone())));
            let ycp = pl(el, bv.clone(), mu(el, rv.clone(), mi(el, dv.clone(), bv.clone())));
            let dxx = mi(el, xcp.clone(), av.clone());
            let dyy = mi(el, ycp.clone(), bv.clone());
            let lhs = pl(
                el,
                mu(el, dxx.clone(), dxx.clone()),
                mu(el, dyy.clone(), dyy.clone()),
            );
            let s_coord = pl(
                el,
                mu(el, mi(el, cv.clone(), av.clone()), mi(el, cv.clone(), av.clone())),
                mu(el, mi(el, dv.clone(), bv.clone()), mi(el, dv.clone(), bv.clone())),
            );
            let rhs = mu(el, mu(el, rv.clone(), rv.clone()), s_coord);
            return Lemma {
                name: "g1-sqdid".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 4 : g1-collid  (generic, deg 2) — collinearity
        //   ( (C-A) * ( (B+R*(D-B)) - B ) )
        // = ( (D-B) * ( (A+R*(C-A)) - A ) )
        // ============================================================
        4 => {
            let v = |s: &str| leaf(s);
            let (av, bv, cv, dv, rv) =
                (v("va"), v("vb"), v("vc"), v("ve"), v("vf"));
            let xcp = pl(el, av.clone(), mu(el, rv.clone(), mi(el, cv.clone(), av.clone())));
            let ycp = pl(el, bv.clone(), mu(el, rv.clone(), mi(el, dv.clone(), bv.clone())));
            let ca = mi(el, cv.clone(), av.clone());
            let db = mi(el, dv.clone(), bv.clone());
            let lhs = mu(el, ca.clone(), mi(el, ycp.clone(), bv.clone()));
            let rhs = mu(el, db.clone(), mi(el, xcp.clone(), av.clone()));
            return Lemma {
                name: "g1-collid".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 5 : g1-dotid  (generic, deg 3) — dot factoring
        //   ( (C-A)*((A+R*(C-A))-A) + (D-B)*((B+R*(D-B))-B) )
        // = ( R * ( (C-A)*(C-A) + (D-B)*(D-B) ) )
        // ============================================================
        5 => {
            let v = |s: &str| leaf(s);
            let (av, bv, cv, dv, rv) =
                (v("va"), v("vb"), v("vc"), v("ve"), v("vf"));
            let xcp = pl(el, av.clone(), mu(el, rv.clone(), mi(el, cv.clone(), av.clone())));
            let ycp = pl(el, bv.clone(), mu(el, rv.clone(), mi(el, dv.clone(), bv.clone())));
            let ca = mi(el, cv.clone(), av.clone());
            let db = mi(el, dv.clone(), bv.clone());
            let lhs = pl(
                el,
                mu(el, ca.clone(), mi(el, xcp.clone(), av.clone())),
                mu(el, db.clone(), mi(el, ycp.clone(), bv.clone())),
            );
            let s_coord = pl(
                el,
                mu(el, ca.clone(), ca.clone()),
                mu(el, db.clone(), db.clone()),
            );
            let rhs = mu(el, rv.clone(), s_coord);
            return Lemma {
                name: "g1-dotid".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            };
        }
        // ============================================================
        // idx 6 : G1b-rulerd
        //   ess g1.1 : |- -. ( ( sqd a c ) = 0 )
        //       g1.2 : |- ( 0 <_ u )
        //   goal     : |- ( sqd a ( cp a c u ) ) = u
        // ============================================================
        6 => {
            let pa = || leaf("va");
            let pc = || leaf("vc");
            let pu = || leaf("vu");
            let s = || sqd(pa(), pc()); // ( sqd a c )
            let is = || el.app("tinv", &[("u", s())], &[]).unwrap(); // ( inv ( sqd a c ) )
            let uis = || mu(el, pu(), is()); // ( u * inv s )
            let r = || el.app("tsqrt", &[("u", uis())], &[]).unwrap(); // sqrt( u*inv s )
            let cp = || el.app("tcp", &[("a", pa()), ("c", pc()), ("u", pu())], &[]).unwrap();
            let one = || el.app("t1", &[], &[]).unwrap();
            let h1 = || leaf("g1b.1"); // |- -. ( ( sqd a c ) = 0 )
            let h2 = || leaf("g1b.2"); // |- ( 0 <_ u )

            // ---- 0 <_ ( u * inv s ) ----
            // 0 <_ inv s  via recipnn ( -.(s=0) , 0<_s )
            let sdnn = el.app("sqdnn", &[("a", pa()), ("b", pc())], &[]).unwrap(); // 0<_s
            let is_nn = el
                .app("recipnn", &[("x", s())], &[h1(), sdnn.clone()])
                .unwrap(); // |- ( 0 <_ inv s )
            // lemul02 : (0<_u) -> ( (0<_inv s) -> (0<_(u*inv s)) )
            let lemul02 = el
                .app("lemul02", &[("u", pu()), ("v", is())], &[])
                .unwrap();
            let uis_nn = mp(
                le(z(), is()),
                le(z(), uis()),
                is_nn.clone(),
                mp(
                    le(z(), pu()),
                    i(le(z(), is()), le(z(), uis())),
                    h2(),
                    lemul02,
                ),
            ); // |- ( 0 <_ ( u * inv s ) )
            // ---- ax-sqrt : r*r = ( u * inv s ) ----
            let axsq = el.app("ax-sqrt", &[("u", uis())], &[]).unwrap(); // ( 0<_(u*invs) -> (r*r)=(u*invs) )
            let rr_eq_uis = mp(
                le(z(), uis()),
                eq(mu(el, r(), r()), uis()),
                uis_nn.clone(),
                axsq,
            ); // |- ( (r*r) = (u*inv s) )
            // ---- of-recip : s*inv s = 1 ----
            let recip = mp(
                n(eq(s(), z())),
                eq(mu(el, s(), is()), one()),
                h1(),
                el.app("of-recip", &[("u", s())], &[]).unwrap(),
            ); // |- ( (s*inv s) = 1 )

            // ---- coordinate form of sqd a (cp a c u) ----
            // df-cp : cp = Pt EX EY
            let ex = pl(
                el,
                xc(pa()),
                mu(el, r(), mi(el, xc(pc()), xc(pa()))),
            );
            let ey = pl(
                el,
                yc(pa()),
                mu(el, r(), mi(el, yc(pc()), yc(pa()))),
            );
            let pt = el
                .app("tpt", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap();
            let dfcp = el
                .app("df-cp", &[("a", pa()), ("c", pc()), ("u", pu())], &[])
                .unwrap(); // ( cp = Pt EX EY )
            // Xc cp = EX :  cong-xc(cp,Pt) then df-xc
            let cxc = mp(
                eq(cp(), pt.clone()),
                eq(xc(cp()), xc(pt.clone())),
                dfcp.clone(),
                el.app("cong-xc", &[("a", cp()), ("b", pt.clone())], &[]).unwrap(),
            ); // ( Xc cp = Xc(Pt EX EY) )
            let dfxc = el
                .app("df-xc", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap(); // ( Xc(Pt EX EY) = EX )
            let xc_cp_eq = eqtr3(el, xc(cp()), xc(pt.clone()), ex.clone(), cxc, dfxc);
            let cyc = mp(
                eq(cp(), pt.clone()),
                eq(yc(cp()), yc(pt.clone())),
                dfcp.clone(),
                el.app("cong-yc", &[("a", cp()), ("b", pt.clone())], &[]).unwrap(),
            );
            let dfyc = el
                .app("df-yc", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap();
            let yc_cp_eq = eqtr3(el, yc(cp()), yc(pt.clone()), ey.clone(), cyc, dfyc);

            // df-sqd : sqd a cp = ( (Xc cp - Xc a)*(Xc cp - Xc a)
            //                     + (Yc cp - Yc a)*(Yc cp - Yc a) )
            let dxcp = mi(el, xc(cp()), xc(pa()));
            let dycp = mi(el, yc(cp()), yc(pa()));
            let sqd_coord = pl(
                el,
                mu(el, dxcp.clone(), dxcp.clone()),
                mu(el, dycp.clone(), dycp.clone()),
            );
            let dfsqd = el
                .app("df-sqd", &[("a", pa()), ("b", cp())], &[])
                .unwrap(); // ( sqd a cp = sqd_coord )
            // rewrite sqd_coord substituting Xc cp := EX, Yc cp := EY
            // dxcp = (Xc cp - Xc a) -> (EX - Xc a)
            let exa = mi(el, ex.clone(), xc(pa()));
            let eya = mi(el, ey.clone(), yc(pa()));
            let c_dx = cmi1(el, xc(cp()), ex.clone(), xc(pa()), xc_cp_eq.clone());
            let c_dy = cmi1(el, yc(cp()), ey.clone(), yc(pa()), yc_cp_eq.clone());
            // (dxcp*dxcp) = (exa*exa)
            let dxx_eq = {
                let s1 = cmu1(el, dxcp.clone(), exa.clone(), dxcp.clone(), c_dx.clone());
                let s2 = cmu2(el, dxcp.clone(), exa.clone(), exa.clone(), c_dx.clone());
                eqtr3(el, mu(el, dxcp.clone(), dxcp.clone()),
                      mu(el, exa.clone(), dxcp.clone()),
                      mu(el, exa.clone(), exa.clone()), s1, s2)
            };
            let dyy_eq = {
                let s1 = cmu1(el, dycp.clone(), eya.clone(), dycp.clone(), c_dy.clone());
                let s2 = cmu2(el, dycp.clone(), eya.clone(), eya.clone(), c_dy.clone());
                eqtr3(el, mu(el, dycp.clone(), dycp.clone()),
                      mu(el, eya.clone(), dycp.clone()),
                      mu(el, eya.clone(), eya.clone()), s1, s2)
            };
            // sqd_coord = ( exa*exa + eya*eya )
            let coord_e = pl(el, mu(el, exa.clone(), exa.clone()), mu(el, eya.clone(), eya.clone()));
            let sc_to_e = {
                let s1 = cpl1(el, mu(el, dxcp.clone(), dxcp.clone()),
                              mu(el, exa.clone(), exa.clone()),
                              mu(el, dycp.clone(), dycp.clone()), dxx_eq);
                let s2 = cpl2(el, mu(el, dycp.clone(), dycp.clone()),
                              mu(el, eya.clone(), eya.clone()),
                              mu(el, exa.clone(), exa.clone()), dyy_eq);
                eqtr3(el, sqd_coord.clone(),
                      pl(el, mu(el, exa.clone(), exa.clone()), mu(el, dycp.clone(), dycp.clone())),
                      coord_e.clone(), s1, s2)
            };
            // g1-sqdid instantiated: coord_e = ( (r*r) * S_coord )
            let s_coord = pl(
                el,
                mu(el, mi(el, xc(pc()), xc(pa())), mi(el, xc(pc()), xc(pa()))),
                mu(el, mi(el, yc(pc()), yc(pa())), mi(el, yc(pc()), yc(pa()))),
            );
            let gid = el
                .app(
                    "g1-sqdid",
                    &[
                        ("a", xc(pa())),
                        ("b", yc(pa())),
                        ("c", xc(pc())),
                        ("e", yc(pc())),
                        ("f", r()),
                    ],
                    &[],
                )
                .unwrap(); // ( coord_e = ( (r*r) * S_coord ) )
            // S_coord = ( sqd a c )  via df-sqd (eqcomm)
            let dfsqd_ac = el
                .app("df-sqd", &[("a", pa()), ("b", pc())], &[])
                .unwrap(); // ( sqd a c = S_coord )
            let scoord_eq_s = eqcomm(el, s(), s_coord.clone(), dfsqd_ac); // ( S_coord = sqd a c )
            // ( (r*r)*S_coord ) = ( (r*r)*s )
            let rr_sc_to_rr_s = cmu2(el, s_coord.clone(), s(), mu(el, r(), r()), scoord_eq_s);
            // chain: sqd a cp = sqd_coord = coord_e = (r*r)*S_coord = (r*r)*s
            let t1 = eqtr3(el, sqd(pa(), cp()), sqd_coord.clone(), coord_e.clone(), dfsqd, sc_to_e);
            let t2 = eqtr3(el, sqd(pa(), cp()), coord_e.clone(),
                           mu(el, mu(el, r(), r()), s_coord.clone()), t1, gid);
            let sqd_cp_eq_rrs = eqtr3(
                el,
                sqd(pa(), cp()),
                mu(el, mu(el, r(), r()), s_coord.clone()),
                mu(el, mu(el, r(), r()), s()),
                t2,
                rr_sc_to_rr_s,
            ); // ( sqd a cp = ( (r*r)*s ) )
            // ---- (r*r)*s = u ----
            // (r*r)*s = (u*inv s)*s   [cong-mu1 with rr_eq_uis]
            let rrs_to_uiss = cmu1(el, mu(el, r(), r()), uis(), s(), rr_eq_uis);
            // (u*inv s)*s = u*(s*inv s)   [ring_eq; atoms u,inv s,s]
            let uiss = mu(el, uis(), s());
            let u_s_is = mu(el, pu(), mu(el, s(), is()));
            let ring2 = ring_eq(el, &uiss, &u_s_is);
            // u*(s*inv s) = u*1   [cong-mu2 with recip]
            let to_u1 = cmu2(el, mu(el, s(), is()), one(), pu(), recip);
            // u*1 = u   [of-mul1]
            let u1_u = el.app("of-mul1", &[("u", pu())], &[]).unwrap();
            // chain (r*r)*s = (u*inv s)*s = u*(s*inv s) = u*1 = u
            let c1 = eqtr3(el, mu(el, mu(el, r(), r()), s()), uiss.clone(), u_s_is.clone(), rrs_to_uiss, ring2);
            let c2 = eqtr3(el, mu(el, mu(el, r(), r()), s()), u_s_is.clone(), mu(el, pu(), one()), c1, to_u1);
            let rrs_eq_u = eqtr3(el, mu(el, mu(el, r(), r()), s()), mu(el, pu(), one()), pu(), c2, u1_u);
            // sqd a cp = (r*r)*s = u
            let g = eqtr3(el, sqd(pa(), cp()), mu(el, mu(el, r(), r()), s()), pu(), sqd_cp_eq_rrs, rrs_eq_u);
            Lemma {
                name: "G1b-rulerd".into(),
                ess: vec![
                    (
                        "g1b.1".into(),
                        toks(&["|-", "-.", "(", "sqd", "a", "c", ")", "=", "0"]),
                    ),
                    (
                        "g1b.2".into(),
                        toks(&["|-", "(", "0", "<_", "u", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ============================================================
        // idx 7 : G1a-rulerr
        //   ess g1.1 : |- -. ( ( sqd a c ) = 0 )
        //       g1.2 : |- ( 0 <_ u )
        //   goal     : |- ( Ray a c ( cp a c u ) )
        // ============================================================
        7 => {
            let pa = || leaf("va");
            let pc = || leaf("vc");
            let pu = || leaf("vu");
            let s = || sqd(pa(), pc());
            let is = || el.app("tinv", &[("u", s())], &[]).unwrap();
            let uis = || mu(el, pu(), is());
            let r = || el.app("tsqrt", &[("u", uis())], &[]).unwrap();
            let cp = || el.app("tcp", &[("a", pa()), ("c", pc()), ("u", pu())], &[]).unwrap();
            let h1 = || leaf("g1a.1");
            let h2 = || leaf("g1a.2");

            // coordinate forms of Xc cp / Yc cp (same as G1b)
            let ex = pl(el, xc(pa()), mu(el, r(), mi(el, xc(pc()), xc(pa()))));
            let ey = pl(el, yc(pa()), mu(el, r(), mi(el, yc(pc()), yc(pa()))));
            let pt = el
                .app("tpt", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap();
            let dfcp = el
                .app("df-cp", &[("a", pa()), ("c", pc()), ("u", pu())], &[])
                .unwrap();
            let cxc = mp(
                eq(cp(), pt.clone()),
                eq(xc(cp()), xc(pt.clone())),
                dfcp.clone(),
                el.app("cong-xc", &[("a", cp()), ("b", pt.clone())], &[]).unwrap(),
            );
            let dfxc = el
                .app("df-xc", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap();
            let xc_cp_eq = eqtr3(el, xc(cp()), xc(pt.clone()), ex.clone(), cxc, dfxc); // Xc cp = EX
            let cyc = mp(
                eq(cp(), pt.clone()),
                eq(yc(cp()), yc(pt.clone())),
                dfcp.clone(),
                el.app("cong-yc", &[("a", cp()), ("b", pt.clone())], &[]).unwrap(),
            );
            let dfyc = el
                .app("df-yc", &[("u", ex.clone()), ("v", ey.clone())], &[])
                .unwrap();
            let yc_cp_eq = eqtr3(el, yc(cp()), yc(pt.clone()), ey.clone(), cyc, dfyc); // Yc cp = EY

            // ===== Coll a c cp =====
            // df-coll : ( Coll a c cp ) <-> ( CL = CR ) with
            //   CL = ( (Xc c - Xc a) * (Yc cp - Yc a) )
            //   CR = ( (Yc c - Yc a) * (Xc cp - Xc a) )
            let ca = mi(el, xc(pc()), xc(pa()));
            let db = mi(el, yc(pc()), yc(pa()));
            let cl = mu(el, ca.clone(), mi(el, yc(cp()), yc(pa())));
            let cr = mu(el, db.clone(), mi(el, xc(cp()), xc(pa())));
            // substitute Yc cp := EY in CL, Xc cp := EX in CR
            let cl_e = mu(el, ca.clone(), mi(el, ey.clone(), yc(pa())));
            let cr_e = mu(el, db.clone(), mi(el, ex.clone(), xc(pa())));
            let cl_to_cle = {
                let c = cmi1(el, yc(cp()), ey.clone(), yc(pa()), yc_cp_eq.clone());
                cmu2(el, mi(el, yc(cp()), yc(pa())), mi(el, ey.clone(), yc(pa())), ca.clone(), c)
            }; // ( CL = CL_e )
            let cr_to_cre = {
                let c = cmi1(el, xc(cp()), ex.clone(), xc(pa()), xc_cp_eq.clone());
                cmu2(el, mi(el, xc(cp()), xc(pa())), mi(el, ex.clone(), xc(pa())), db.clone(), c)
            }; // ( CR = CR_e )
            // g1-collid : CL_e = CR_e
            let collid = el
                .app(
                    "g1-collid",
                    &[
                        ("a", xc(pa())),
                        ("b", yc(pa())),
                        ("c", xc(pc())),
                        ("e", yc(pc())),
                        ("f", r()),
                    ],
                    &[],
                )
                .unwrap(); // ( CL_e = CR_e )
            // CL = CL_e = CR_e = CR
            let cre_to_cr = eqcomm(el, cr.clone(), cr_e.clone(), cr_to_cre);
            let t1 = eqtr3(el, cl.clone(), cl_e.clone(), cr_e.clone(), cl_to_cle, collid);
            let cl_eq_cr = eqtr3(el, cl.clone(), cr_e.clone(), cr.clone(), t1, cre_to_cr); // ( CL = CR )
            // df-coll backward : ( CL = CR ) -> Coll a c cp.
            // Build ax-bi2 with explicit Pt operands (G3c style) so the
            // naive wff parser is never invoked on the cp-nested term.
            let collw = el
                .app("wcoll", &[("a", pa()), ("b", pc()), ("c", cp())], &[])
                .unwrap();
            let cleqcr_w = eq(cl.clone(), cr.clone()); // ps : ( CL = CR )
            let dfcoll = el
                .app("df-coll", &[("a", pa()), ("b", pc()), ("c", cp())], &[])
                .unwrap(); // ( Coll a c cp <-> ( CL = CR ) )
            let bi2c = el
                .app(
                    "ax-bi2",
                    &[("ph", collw.clone()), ("ps", cleqcr_w.clone())],
                    &[],
                )
                .unwrap(); // ( (Collcp<->CLeqCR) -> ( CLeqCR -> Collcp ) )
            let coll_back = mp(
                b(collw.clone(), cleqcr_w.clone()),
                i(cleqcr_w.clone(), collw.clone()),
                dfcoll,
                bi2c,
            ); // ( ( CL = CR ) -> Coll a c cp )
            let coll_pf = mp(cleqcr_w.clone(), collw.clone(), cl_eq_cr, coll_back); // |- Coll a c cp

            // ===== 0 <_ ( dot a c cp ) =====
            // df-dot : dot a c cp = ( (Xc c-Xc a)*(Xc cp-Xc a)
            //                       + (Yc c-Yc a)*(Yc cp-Yc a) )
            let dl = mu(el, ca.clone(), mi(el, xc(cp()), xc(pa())));
            let dr = mu(el, db.clone(), mi(el, yc(cp()), yc(pa())));
            let dot_coord = pl(el, dl.clone(), dr.clone());
            let dfdot = el
                .app("df-dot", &[("o", pa()), ("p", pc()), ("q", cp())], &[])
                .unwrap(); // ( dot a c cp = dot_coord )
            // substitute Xc cp := EX, Yc cp := EY
            let dl_e = mu(el, ca.clone(), mi(el, ex.clone(), xc(pa())));
            let dr_e = mu(el, db.clone(), mi(el, ey.clone(), yc(pa())));
            let dl_to_dle = {
                let c = cmi1(el, xc(cp()), ex.clone(), xc(pa()), xc_cp_eq.clone());
                cmu2(el, mi(el, xc(cp()), xc(pa())), mi(el, ex.clone(), xc(pa())), ca.clone(), c)
            };
            let dr_to_dre = {
                let c = cmi1(el, yc(cp()), ey.clone(), yc(pa()), yc_cp_eq.clone());
                cmu2(el, mi(el, yc(cp()), yc(pa())), mi(el, ey.clone(), yc(pa())), db.clone(), c)
            };
            let dotc_e = pl(el, dl_e.clone(), dr_e.clone());
            let dotc_to_e = {
                let s1 = cpl1(el, dl.clone(), dl_e.clone(), dr.clone(), dl_to_dle);
                let s2 = cpl2(el, dr.clone(), dr_e.clone(), dl_e.clone(), dr_to_dre);
                eqtr3(el, dot_coord.clone(),
                      pl(el, dl_e.clone(), dr.clone()),
                      dotc_e.clone(), s1, s2)
            }; // ( dot_coord = dotc_e )
            // g1-dotid : dotc_e = ( r * S_coord )
            let s_coord = pl(
                el,
                mu(el, ca.clone(), ca.clone()),
                mu(el, db.clone(), db.clone()),
            );
            let dotid = el
                .app(
                    "g1-dotid",
                    &[
                        ("a", xc(pa())),
                        ("b", yc(pa())),
                        ("c", xc(pc())),
                        ("e", yc(pc())),
                        ("f", r()),
                    ],
                    &[],
                )
                .unwrap(); // ( dotc_e = ( r * S_coord ) )
            // S_coord = ( sqd a c )
            let dfsqd_ac = el
                .app("df-sqd", &[("a", pa()), ("b", pc())], &[])
                .unwrap();
            let scoord_eq_s = eqcomm(el, s(), s_coord.clone(), dfsqd_ac); // ( S_coord = s )
            let rsc_to_rs = cmu2(el, s_coord.clone(), s(), r(), scoord_eq_s); // ( r*S_coord = r*s )
            // dot a c cp = dot_coord = dotc_e = r*S_coord = r*s
            let d1 = eqtr3(el, dot(pa(), pc(), cp()), dot_coord.clone(), dotc_e.clone(), dfdot, dotc_to_e);
            let d2 = eqtr3(el, dot(pa(), pc(), cp()), dotc_e.clone(),
                           mu(el, r(), s_coord.clone()), d1, dotid);
            let dot_eq_rs = eqtr3(el, dot(pa(), pc(), cp()),
                                  mu(el, r(), s_coord.clone()),
                                  mu(el, r(), s()), d2, rsc_to_rs); // ( dot a c cp = r*s )
            // 0 <_ r   (of-sqrtnn on 0<_(u*inv s))
            let sdnn = el.app("sqdnn", &[("a", pa()), ("b", pc())], &[]).unwrap(); // 0<_s
            let is_nn = el
                .app("recipnn", &[("x", s())], &[h1(), sdnn.clone()])
                .unwrap(); // 0<_inv s
            let lemul02a = el
                .app("lemul02", &[("u", pu()), ("v", is())], &[])
                .unwrap();
            let uis_nn = mp(
                le(z(), is()),
                le(z(), uis()),
                is_nn.clone(),
                mp(
                    le(z(), pu()),
                    i(le(z(), is()), le(z(), uis())),
                    h2(),
                    lemul02a,
                ),
            ); // 0<_(u*inv s)
            let sqrtnn = el.app("of-sqrtnn", &[("u", uis())], &[]).unwrap(); // ( 0<_(u*invs) -> 0<_r )
            let r_nn = mp(le(z(), uis()), le(z(), r()), uis_nn, sqrtnn); // 0<_r
            // 0 <_ ( r * s )  via lemul02 ( r, s )
            let lemul02b = el
                .app("lemul02", &[("u", r()), ("v", s())], &[])
                .unwrap();
            let rs_nn = mp(
                le(z(), s()),
                le(z(), mu(el, r(), s())),
                sdnn.clone(),
                mp(
                    le(z(), r()),
                    i(le(z(), s()), le(z(), mu(el, r(), s()))),
                    r_nn,
                    lemul02b,
                ),
            ); // 0 <_ ( r*s )
            // rewrite to 0 <_ ( dot a c cp )
            let dot_rs_back = eqcomm(el, dot(pa(), pc(), cp()), mu(el, r(), s()), dot_eq_rs); // ( r*s = dot )
            let cl2 = el
                .app(
                    "cong-le2",
                    &[("a", mu(el, r(), s())), ("b", dot(pa(), pc(), cp())), ("c", z())],
                    &[],
                )
                .unwrap();
            let step = mp(
                eq(mu(el, r(), s()), dot(pa(), pc(), cp())),
                i(le(z(), mu(el, r(), s())), le(z(), dot(pa(), pc(), cp()))),
                dot_rs_back,
                cl2,
            );
            let dot_nn = mp(
                le(z(), mu(el, r(), s())),
                le(z(), dot(pa(), pc(), cp())),
                rs_nn,
                step,
            ); // |- ( 0 <_ ( dot a c cp ) )

            // ===== jca + df-ray backward =====
            let conj = conj2(
                el,
                collw.clone(),
                le(z(), dot(pa(), pc(), cp())),
                coll_pf,
                dot_nn,
            ); // |- ( Coll a c cp /\ 0<_(dot a c cp) )
            let rayw = el
                .app("wray", &[("a", pa()), ("b", pc()), ("c", cp())], &[])
                .unwrap();
            let conj_w = a(collw.clone(), le(z(), dot(pa(), pc(), cp()))); // ps
            let dfray = el
                .app("df-ray", &[("a", pa()), ("b", pc()), ("c", cp())], &[])
                .unwrap(); // ( Ray a c cp <-> ( Coll a c cp /\ 0<_dot ) )
            let bi2r = el
                .app(
                    "ax-bi2",
                    &[("ph", rayw.clone()), ("ps", conj_w.clone())],
                    &[],
                )
                .unwrap(); // ( (Ray<->conj) -> ( conj -> Ray ) )
            let ray_back = mp(
                b(rayw.clone(), conj_w.clone()),
                i(conj_w.clone(), rayw.clone()),
                dfray,
                bi2r,
            ); // ( conj -> Ray a c cp )
            let g = mp(conj_w.clone(), rayw.clone(), conj, ray_back); // |- Ray a c cp
            Lemma {
                name: "G1a-rulerr".into(),
                ess: vec![
                    (
                        "g1a.1".into(),
                        toks(&["|-", "-.", "(", "sqd", "a", "c", ")", "=", "0"]),
                    ),
                    (
                        "g1a.2".into(),
                        toks(&["|-", "(", "0", "<_", "u", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        _ => unreachable!("proof_g1: idx {idx} out of range"),
    }
}
