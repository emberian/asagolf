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
    // 3 = the verified generic primitives (g2-elim-y/x, g2-sq).
    // The idx-3 G2-incid inference arm is drafted but has a documented
    // __G2_TODO__ tail (detPQ≠0⇒0<detPQ² → g2-sq → mulcposcan → sqz →
    // subeq0 → ptext); gated off until it kernel-verifies. RESTORE TO 4.
    3
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
        // g2-sq : ( m·n )·( m·n ) = ( m·m )·( n·n )   [generic, tiny]
        // Keeps (det·dy)² = det²·dy² off the normaliser (det,dy are
        // degree-2 coord terms → (det·dy)² would be degree-8 dense).
        2 => {
            let (m, nn) = (v("vu"), v("vv"));
            let lhs = mu(
                el,
                mu(el, m.clone(), nn.clone()),
                mu(el, m.clone(), nn.clone()),
            );
            let rhs = mu(
                el,
                mu(el, m.clone(), m.clone()),
                mu(el, nn.clone(), nn.clone()),
            );
            Lemma {
                name: "g2-sq".into(),
                ess: vec![],
                goal: ring_eq(el, &lhs, &rhs),
            }
        }
        // ====================================================================
        // idx 3 : G2-incid  (INFERENCE)
        //   ess g2.1 |- ( Tri a b c )   g2.2 |- ( On x ( Ln a c ) )
        //       g2.3 |- ( On x ( Ln b c ) )      goal |- x = c
        // ====================================================================
        3 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let pc = || leaf("vc");
            let px = || leaf("vx");
            let n = |p: Pt| el.app("wn", &[("ph", p)], &[]).unwrap();
            let eqp = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let mp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
                el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
            };
            let xc = |p: Pt| el.app("txc", &[("a", p)], &[]).unwrap();
            let yc = |p: Pt| el.app("tyc", &[("a", p)], &[]).unwrap();
            let z = || t0p(el);
            // coordinate difference vectors
            let pxx = || mi(el, xc(pc()), xc(pa())); // P=c-a
            let pyy = || mi(el, yc(pc()), yc(pa()));
            let qxx = || mi(el, xc(pc()), xc(pb())); // Q=c-b
            let qyy = || mi(el, yc(pc()), yc(pb()));
            let dxx = || mi(el, xc(px()), xc(pc())); // d=x-c
            let dyy = || mi(el, yc(px()), yc(pc()));
            let rxx = || mi(el, xc(px()), xc(pa())); // R=x-a
            let ryy = || mi(el, yc(px()), yc(pa()));
            let sxx = || mi(el, xc(px()), xc(pb())); // S=x-b
            let syy = || mi(el, yc(px()), yc(pb()));
            let uxx = || mi(el, xc(pb()), xc(pa())); // U=b-a
            let uyy = || mi(el, yc(pb()), yc(pa()));
            let cross = |ax: Pt, ay: Pt, bx: Pt, by: Pt| {
                mi(el, mu(el, ax, by), mu(el, ay, bx))
            };
            // ---- unfold the three hypotheses via df-tri/df-on/df-coll ----
            // g2.1 : Tri a b c  ->(df-tri)->  -. Coll a b c
            let dftri = el
                .app("df-tri", &[("a", pa()), ("b", pb()), ("c", pc())], &[])
                .unwrap();
            let ncoll_abc = el.bi_fwd(dftri, leaf("g2.1")).unwrap(); // |- -. ( Coll a b c )
            // df-coll a b c : ( Coll a b c ) <-> ( Ux*Py = Uy*Px )
            let coll_abc = el
                .app("wcoll", &[("a", pa()), ("b", pb()), ("c", pc())], &[])
                .unwrap();
            let dfcoll_abc = el
                .app("df-coll", &[("a", pa()), ("b", pb()), ("c", pc())], &[])
                .unwrap();
            let ce_abc = mu(el, uxx(), pyy()); // (Xc b-Xc a)*(Yc c-Yc a)
            let ce_abc_r = mu(el, uyy(), pxx());
            let colleq_abc = eqp(ce_abc.clone(), ce_abc_r.clone());
            // (CollEq_abc -> Coll a b c) via ax-bi2 ; con3i with -.Coll -> -.CollEq
            let bi2_abc = el
                .app(
                    "ax-bi2",
                    &[("ph", coll_abc.clone()), ("ps", colleq_abc.clone())],
                    &[],
                )
                .unwrap(); // ( (Coll<->CollEq) -> (CollEq->Coll) )
            let ceimpl_abc = mp(
                el.app(
                    "wb",
                    &[("ph", coll_abc.clone()), ("ps", colleq_abc.clone())],
                    &[],
                )
                .unwrap(),
                el.app(
                    "wi",
                    &[("ph", colleq_abc.clone()), ("ps", coll_abc.clone())],
                    &[],
                )
                .unwrap(),
                dfcoll_abc.clone(),
                bi2_abc,
            ); // |- ( CollEq_abc -> Coll a b c )
            let con3i_abc = el
                .app(
                    "con3i",
                    &[("ph", colleq_abc.clone()), ("ps", coll_abc.clone())],
                    &[ceimpl_abc],
                )
                .unwrap(); // ( -.Coll -> -.CollEq )
            let ncolleq_abc = mp(
                n(coll_abc.clone()),
                n(colleq_abc.clone()),
                ncoll_abc,
                con3i_abc,
            ); // |- -. ( Ux*Py = Uy*Px )
            // detU = Ux*Py -x Uy*Px ;  -.(detU=0)  via subeq0 contrapositive
            let detu = cross(uxx(), uyy(), pxx(), pyy());
            let subeq0_u = el
                .app("subeq0", &[("u", ce_abc.clone()), ("v", ce_abc_r.clone())], &[])
                .unwrap(); // ( (Ux*Py -x Uy*Px)=0 -> Ux*Py = Uy*Px )
            let con3i_u = el
                .app(
                    "con3i",
                    &[
                        ("ph", eqp(detu.clone(), z())),
                        ("ps", colleq_abc.clone()),
                    ],
                    &[subeq0_u],
                )
                .unwrap(); // ( -.(Ux*Py=Uy*Px) -> -.(detU=0) )
            let ndetu0 = mp(
                n(colleq_abc.clone()),
                n(eqp(detu.clone(), z())),
                ncolleq_abc,
                con3i_u,
            ); // |- -. ( detU = 0 )
            // g2.2 : On x (Ln a c) ->(df-on)-> Coll a c x ->(df-coll)-> X(P,R) eq
            let dfon_ac = el
                .app("df-on", &[("x", px()), ("a", pa()), ("b", pc())], &[])
                .unwrap();
            let coll_acx = el.bi_fwd(dfon_ac, leaf("g2.2")).unwrap(); // |- ( Coll a c x )
            let dfcoll_acx = el
                .app("df-coll", &[("a", pa()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let pr_eq = el.bi_fwd(dfcoll_acx, coll_acx).unwrap();
            // |- ( (Xc c-Xc a)*(Yc x-Yc a) = (Yc c-Yc a)*(Xc x-Xc a) )  [Px*Ry=Py*Rx]
            // g2.3 : On x (Ln b c) -> Coll b c x -> X(Q,S) eq
            let dfon_bc = el
                .app("df-on", &[("x", px()), ("a", pb()), ("b", pc())], &[])
                .unwrap();
            let coll_bcx = el.bi_fwd(dfon_bc, leaf("g2.3")).unwrap();
            let dfcoll_bcx = el
                .app("df-coll", &[("a", pb()), ("b", pc()), ("c", px())], &[])
                .unwrap();
            let qs_eq = el.bi_fwd(dfcoll_bcx, coll_bcx).unwrap();
            // |- ( (Xc c-Xc b)*(Yc x-Yc b) = (Yc c-Yc b)*(Xc x-Xc b) )  [Qx*Sy=Qy*Sx]

            // X(P,R)=0 from pr_eq (subtract sides), then shift to X(P,d)=0.
            let xpr = cross(pxx(), pyy(), rxx(), ryy());
            let xpd = cross(pxx(), pyy(), dxx(), dyy());
            let xqs = cross(qxx(), qyy(), sxx(), syy());
            let xqd = cross(qxx(), qyy(), dxx(), dyy());
            // pr_eq : (Px*Ry)=(Py*Rx)  ->  X(P,R)=0  via eq_to_sub0
            let eq_to_sub0 = |l: Pt, r: Pt, p: Pt| -> Pt {
                // p:l=r ; (l-x r)=(r-x r) [cmi1] ; (r-x r)=0 [subid] ; eqtr3
                let c1 = cmi1(el, l.clone(), r.clone(), r.clone(), p);
                let s0 = el.app("subid", &[("u", r.clone())], &[]).unwrap();
                eqtr3(el, mi(el, l.clone(), r.clone()), mi(el, r.clone(), r.clone()), z(), c1, s0)
            };
            let xpr0 = eq_to_sub0(
                mu(el, pxx(), ryy()),
                mu(el, pyy(), rxx()),
                pr_eq,
            ); // |- ( X(P,R) ) = 0
            let xqs0 = eq_to_sub0(
                mu(el, qxx(), syy()),
                mu(el, qyy(), sxx()),
                qs_eq,
            ); // |- ( X(Q,S) ) = 0
            // shift: X(P,R) = X(P,d)  (R=P+d, small degree-2 ring_eq)
            let shp = ring_eq(el, &xpr, &xpd);
            let shq = ring_eq(el, &xqs, &xqd);
            let xpd0 = eqtr3(el, xpd.clone(), xpr.clone(), z(), eqcomm(el, xpr.clone(), xpd.clone(), shp), xpr0);
            let xqd0 = eqtr3(el, xqd.clone(), xqs.clone(), z(), eqcomm(el, xqs.clone(), xqd.clone(), shq), xqs0);
            // |- X(P,d)=0 , |- X(Q,d)=0

            // instantiate g2-elim-y/x : det·dy , det·dx ; det := detPQ
            let elimy = el
                .app(
                    "g2-elim-y",
                    &[
                        ("a", pxx()), ("b", pyy()), ("c", qxx()),
                        ("e", qyy()), ("f", dxx()), ("g", dyy()),
                    ],
                    &[],
                )
                .unwrap(); // ( Qy·X(P,d) -x Py·X(Q,d) ) = ( detPQ · dy )
            let elimx = el
                .app(
                    "g2-elim-x",
                    &[
                        ("a", pxx()), ("b", pyy()), ("c", qxx()),
                        ("e", qyy()), ("f", dxx()), ("g", dyy()),
                    ],
                    &[],
                )
                .unwrap(); // ( Qx·X(P,d) -x Px·X(Q,d) ) = ( detPQ · dx )
            let detpq = cross(pxx(), pyy(), qxx(), qyy()); // Px*Qy -x Py*Qx
            // substitute X(P,d)=0, X(Q,d)=0 into the elim LHSs -> 0
            let mul0r = |t: Pt| -> Pt {
                let comm = el
                    .app("of-mulcom", &[("u", t.clone()), ("v", z())], &[])
                    .unwrap();
                let m0l = el.app("mul0", &[("u", t.clone())], &[]).unwrap();
                eqtr3(el, mu(el, t.clone(), z()), mu(el, z(), t.clone()), z(), comm, m0l)
            };
            // ( Qy·X(P,d) ) = ( Qy·0 ) = 0
            let qy_xpd0 = eqtr3(
                el,
                mu(el, qyy(), xpd.clone()),
                mu(el, qyy(), z()),
                z(),
                cmu2(el, xpd.clone(), z(), qyy(), xpd0.clone()),
                mul0r(qyy()),
            );
            let py_xqd0 = eqtr3(
                el,
                mu(el, pyy(), xqd.clone()),
                mu(el, pyy(), z()),
                z(),
                cmu2(el, xqd.clone(), z(), pyy(), xqd0.clone()),
                mul0r(pyy()),
            );
            // ( Qy·X(P,d) -x Py·X(Q,d) ) = ( 0 -x 0 ) = 0
            let elimy_lhs = mi(el, mu(el, qyy(), xpd.clone()), mu(el, pyy(), xqd.clone()));
            let lhs_y_zz = {
                let c1 = cmi1(el, mu(el, qyy(), xpd.clone()), z(), mu(el, pyy(), xqd.clone()), qy_xpd0);
                let c2 = cmi2(el, mu(el, pyy(), xqd.clone()), z(), z(), py_xqd0);
                eqtr3(el, elimy_lhs.clone(), mi(el, z(), mu(el, pyy(), xqd.clone())), mi(el, z(), z()), c1, c2)
            };
            let zz0 = ring_eq(el, &mi(el, z(), z()), &z()); // (0-x0)=0
            let elimy_lhs0 = eqtr3(el, elimy_lhs.clone(), mi(el, z(), z()), z(), lhs_y_zz, zz0.clone());
            // detPQ·dy = 0 : eqtr3( elimy : lhs=detPQ·dy ; elimy_lhs0 : lhs=0 )
            let detpq_dy0 = eqtr3(
                el,
                mu(el, detpq.clone(), dyy()),
                elimy_lhs.clone(),
                z(),
                eqcomm(el, elimy_lhs.clone(), mu(el, detpq.clone(), dyy()), elimy),
                elimy_lhs0,
            ); // |- ( detPQ · dy ) = 0
            // same for dx
            let qx_xpd0 = eqtr3(
                el,
                mu(el, qxx(), xpd.clone()),
                mu(el, qxx(), z()),
                z(),
                cmu2(el, xpd.clone(), z(), qxx(), xpd0.clone()),
                mul0r(qxx()),
            );
            let px_xqd0 = eqtr3(
                el,
                mu(el, pxx(), xqd.clone()),
                mu(el, pxx(), z()),
                z(),
                cmu2(el, xqd.clone(), z(), pxx(), xqd0.clone()),
                mul0r(pxx()),
            );
            let elimx_lhs = mi(el, mu(el, qxx(), xpd.clone()), mu(el, pxx(), xqd.clone()));
            let lhs_x_zz = {
                let c1 = cmi1(el, mu(el, qxx(), xpd.clone()), z(), mu(el, pxx(), xqd.clone()), qx_xpd0);
                let c2 = cmi2(el, mu(el, pxx(), xqd.clone()), z(), z(), px_xqd0);
                eqtr3(el, elimx_lhs.clone(), mi(el, z(), mu(el, pxx(), xqd.clone())), mi(el, z(), z()), c1, c2)
            };
            let elimx_lhs0 = eqtr3(el, elimx_lhs.clone(), mi(el, z(), z()), z(), lhs_x_zz, zz0);
            let detpq_dx0 = eqtr3(
                el,
                mu(el, detpq.clone(), dxx()),
                elimx_lhs.clone(),
                z(),
                eqcomm(el, elimx_lhs.clone(), mu(el, detpq.clone(), dxx()), elimx),
                elimx_lhs0,
            ); // |- ( detPQ · dx ) = 0

            // detPQ = detU (small ring_eq) ; -.(detPQ=0) from -.(detU=0)
            let dpq_du = ring_eq(el, &detpq, &detu);
            let ndetpq0 = {
                // -.(detU=0) ; detPQ=detU ; so (detPQ=0)->(detU=0) [cong] -> contra
                let c = cmi1(el, detpq.clone(), detu.clone(), z(), dpq_du.clone());
                // c : (detPQ -x 0)?? need (detPQ=0)->(detU=0). Use weq congruence:
                let cong = el
                    .app(
                        "cong-le1", // placeholder; replaced below if wrong
                        &[("a", detpq.clone()), ("b", detu.clone()), ("c", z())],
                        &[],
                    );
                let _ = (c, cong);
                // (detPQ=0) -> (detU=0) via eqtr: detPQ=detU, detU? Actually:
                // from p:(detPQ=0) and dpq_du:(detPQ=detU): detU = detPQ = 0.
                // Build implication ( (detPQ=0) -> (detU=0) ):
                let imp_pq_u = {
                    // id-style: assume detPQ=0; eqtr3(detU,detPQ,0, eqcomm(dpq_du), hyp)
                    // implement as: con3i of the reverse is simpler.
                    // reverse: (detU=0)->(detPQ=0) via dpq_du: detPQ=detU so
                    //   detPQ = detU = 0.
                    let rev = {
                        // proof of ( (detU=0) -> (detPQ=0) ) by a1i-free deduction:
                        // use eqtr: need term-level. Simplest: cong on weq.
                        el.app(
                            "cong-le1",
                            &[("a", detu.clone()), ("b", detpq.clone()), ("c", z())],
                            &[],
                        )
                        .unwrap();
                        // NOTE: cong-le1 is for <_, not =; this is a known TODO,
                        // kernel will flag — fix to the = -congruence next pass.
                        leaf("__G2_TODO_detpq_eq__")
                    };
                    rev
                };
                let _ = imp_pq_u;
                leaf("__G2_TODO_ndetpq0__")
            };
            let _ = (ndetu0, ndetpq0, detpq_dy0, detpq_dx0, xpd0, xqd0, n, eqp);
            // ---- TODO (next kernel-guided pass): -.(detPQ=0) -> 0<detPQ²,
            // (detPQ·dy)²=detPQ²·dy² [g2-sq], mulcposcan cancel, sqz,
            // subeq0 -> Xc x=Xc c & Yc x=Yc c, conj2+ptext -> x=c. ----
            Lemma {
                name: "G2-incid".into(),
                ess: vec![
                    ("g2.1".into(), toks(&["|-", "(", "Tri", "a", "b", "c", ")"])),
                    ("g2.2".into(), toks(&["|-", "(", "On", "x", "(", "Ln", "a", "c", ")", ")"])),
                    ("g2.3".into(), toks(&["|-", "(", "On", "x", "(", "Ln", "b", "c", ")", ")"])),
                ],
                goal: eqp(px(), pc()),
            }
        }
        _ => unreachable!(),
    }
}
