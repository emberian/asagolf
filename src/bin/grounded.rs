//! Task #7 — stage-prove the grounded geometric postulates.
//!
//! `grounded.mm` asserts only field/order algebra, one √ axiom, propositional
//! + equality logic axioms, and conservative coordinate definitions (df-*).
//! No geometric postulate is a `$a`. Here we derive them as kernel-verified
//! `$p`, bottom-up:
//!
//!   propositional library : id, a1i, syl, pm2.21, pm2.43(W), notnot2,
//!                           notnot1, simpl, simpr   (from ax-1/2/3 + df-an)
//!   first geometric goal  : G3c rayline  Ray a c x -> On x (Ln a c)
//!                           (pure df-ray / df-on unfold; no field arithmetic)
//!
//! Every lemma is appended as a scoped `$p` and re-checked by the sound kernel;
//! a derivation bug becomes a kernel rejection, never an unsound proof.
//! Usage: cargo run --release --bin grounded

#[path = "../kernel.rs"]
mod kernel;
#[path = "../elaborate.rs"]
mod elaborate;
#[path = "../number.rs"]
mod number;
// Extra postulate modules, one per worktree-isolated derivation.  Each
// exposes `count()` and `make(idx, &Elab) -> Lemma`, mirroring the
// per-idx pattern of `make_lemma`, and is staged after the core 57.
#[path = "../proof_g2.rs"]
mod proof_g2;
#[path = "../proof_g3.rs"]
mod proof_g3;
#[path = "../proof_g1.rs"]
mod proof_g1;

use elaborate::{assemble, assemble_one, leaf, Elab, Lemma, Pt};
use number::ProofSize;
use std::collections::HashMap;
use std::process::exit;

fn die(ctx: &str, e: String) -> ! {
    eprintln!("{ctx}: {e}");
    exit(1);
}

/// Exact fully-inlined ($a-invocation) count, set.mm convention:
/// $f/$e = 0 (substitution glue), $a = 1 (primitive leaf), $p = expand.
fn expand(
    db: &kernel::Db,
    label: &str,
    memo: &mut HashMap<String, ProofSize>,
) -> ProofSize {
    if let Some(v) = memo.get(label) {
        return v.clone();
    }
    let st = match db.get(label) {
        Some(s) => s,
        None => {
            eprintln!("expand: MISSING label {:?}", label);
            let z = ProofSize::zero();
            memo.insert(label.to_string(), z.clone());
            return z;
        }
    };
    let out = match st.kind {
        kernel::Kind::F | kernel::Kind::E => ProofSize::zero(),
        kernel::Kind::A => ProofSize::one(),
        kernel::Kind::P => {
            let mut tot = ProofSize::zero();
            for step in st.proof.clone() {
                tot = tot.add(&expand(db, &step, memo));
            }
            tot
        }
    };
    memo.insert(label.to_string(), out.clone());
    out
}

fn toks(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

// ===================================================================
//  Additive-AC normalizer (kernel-checked tactic).
//
//  Flattens a `+`-tree to its multiset of atoms, sorts them into a
//  canonical right-associated sum, and emits a proof `t = canonical`
//  using only of-addcom / of-addass / cong-pl1 / cong-pl2 / eqtr /
//  eqid.  This is the backbone used by every polynomial postulate proof.
// ===================================================================

fn is_pl(t: &Pt) -> bool {
    t.label == "tpl"
}

/// Left-to-right atom list of a `+`-tree (maximal non-`+` subterms).
fn atoms(t: &Pt, out: &mut Vec<Pt>) {
    if is_pl(t) {
        atoms(&t.kids[0], out);
        atoms(&t.kids[1], out);
    } else {
        out.push(t.clone());
    }
}

/// Right-associated sum of `xs` (xs non-empty): a0 + (a1 + (a2 + …)).
fn ra(el: &Elab, xs: &[Pt]) -> Pt {
    if xs.len() == 1 {
        xs[0].clone()
    } else {
        el.app("tpl", &[("u", xs[0].clone()), ("v", ra(el, &xs[1..]))], &[])
            .unwrap()
    }
}

fn eqid(el: &Elab, t: &Pt) -> Pt {
    el.app("eqid", &[("x", t.clone())], &[]).unwrap()
}
fn pl(el: &Elab, u: Pt, v: Pt) -> Pt {
    el.app("tpl", &[("u", u), ("v", v)], &[]).unwrap()
}
fn eqtr3(el: &Elab, x: Pt, y: Pt, z: Pt, p1: Pt, p2: Pt) -> Pt {
    el.app("eqtr", &[("x", x), ("y", y), ("z", z)], &[p1, p2])
        .unwrap()
}
/// congruence: from `p : l = r` get `( l + w ) = ( r + w )`.
fn cpl1(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-pl1", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", pl(el, l, w.clone())), ("y", pl(el, r, w))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}
/// congruence: from `p : l = r` get `( w + l ) = ( w + r )`.
fn cpl2(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-pl2", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", pl(el, w.clone(), l)), ("y", pl(el, w, r))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}

/// Proof `( RA(al) + RA(ar) ) = RA(al ++ ar)`.
fn append_ra(el: &Elab, al: &[Pt], ar: &[Pt]) -> Pt {
    let s_ar = ra(el, ar);
    if al.len() == 1 {
        // ( a0 + RA(ar) ) is *syntactically* RA([a0]++ar)
        eqid(el, &pl(el, al[0].clone(), s_ar))
    } else {
        let a0 = al[0].clone();
        let s_rest = ra(el, &al[1..]);
        let lhs = pl(el, pl(el, a0.clone(), s_rest.clone()), s_ar.clone());
        // ((a0+RArest)+RAar) = (a0+(RArest+RAar))
        let assoc = el
            .app("of-addass", &[("u", a0.clone()), ("v", s_rest.clone()), ("w", s_ar.clone())], &[])
            .unwrap();
        // (RArest+RAar) = RA(rest++ar)
        let inner = append_ra(el, &al[1..], ar);
        let mut tail = al[1..].to_vec();
        tail.extend_from_slice(ar);
        let s_tail = ra(el, &tail);
        let cong = cpl2(el, pl(el, s_rest.clone(), s_ar.clone()), s_tail.clone(), a0.clone(), inner);
        eqtr3(
            el,
            lhs,
            pl(el, a0.clone(), pl(el, s_rest, s_ar)),
            pl(el, a0, s_tail),
            assoc,
            cong,
        )
    }
}

/// Flatten `t`: returns (atoms, proof `t = RA(atoms)`).
fn flatten(el: &Elab, t: &Pt) -> (Vec<Pt>, Pt) {
    if !is_pl(t) {
        return (vec![t.clone()], eqid(el, t));
    }
    let l = &t.kids[0];
    let r = &t.kids[1];
    let (al, pl_) = flatten(el, l);
    let (ar, pr) = flatten(el, r);
    let s_al = ra(el, &al);
    let s_ar = ra(el, &ar);
    // (l+r) = (RAal+r) = (RAal+RAar)
    let c1 = cpl1(el, l.clone(), s_al.clone(), r.clone(), pl_);
    let c2 = cpl2(el, r.clone(), s_ar.clone(), s_al.clone(), pr);
    let step1 = eqtr3(
        el,
        pl(el, l.clone(), r.clone()),
        pl(el, s_al.clone(), r.clone()),
        pl(el, s_al.clone(), s_ar.clone()),
        c1,
        c2,
    );
    let papp = append_ra(el, &al, &ar);
    let mut all = al.clone();
    all.extend_from_slice(&ar);
    let s_all = ra(el, &all);
    let proof = eqtr3(
        el,
        pl(el, l.clone(), r.clone()),
        pl(el, s_al, s_ar),
        s_all,
        step1,
        papp,
    );
    (all, proof)
}

/// Proof `RA(xs) = RA(xs with positions k,k+1 swapped)` (len>=2).
fn ra_swap_at(el: &Elab, xs: &[Pt], k: usize) -> Pt {
    if k == 0 {
        let x = xs[0].clone();
        let y = xs[1].clone();
        if xs.len() == 2 {
            return el
                .app("of-addcom", &[("u", x), ("v", y)], &[])
                .unwrap();
        }
        let s = ra(el, &xs[2..]);
        // (x+(y+S)) = ((x+y)+S) = ((y+x)+S) = (y+(x+S))
        let a1 = el
            .app("of-addass", &[("u", x.clone()), ("v", y.clone()), ("w", s.clone())], &[])
            .unwrap(); // ((x+y)+S)=(x+(y+S))
        let a1r = el
            .app(
                "eqcom",
                &[("x", pl(el, pl(el, x.clone(), y.clone()), s.clone())),
                  ("y", pl(el, x.clone(), pl(el, y.clone(), s.clone())))],
                &[],
            )
            .unwrap();
        let a1r = el
            .app(
                "ax-mp",
                &[("ph", el.app("weq", &[("x", pl(el, pl(el, x.clone(), y.clone()), s.clone())), ("y", pl(el, x.clone(), pl(el, y.clone(), s.clone())))], &[]).unwrap()),
                  ("ps", el.app("weq", &[("x", pl(el, x.clone(), pl(el, y.clone(), s.clone()))), ("y", pl(el, pl(el, x.clone(), y.clone()), s.clone()))], &[]).unwrap())],
                &[a1, a1r],
            )
            .unwrap(); // (x+(y+S)) = ((x+y)+S)
        let comm = el
            .app("of-addcom", &[("u", x.clone()), ("v", y.clone())], &[])
            .unwrap(); // (x+y)=(y+x)
        let b = cpl1(el, pl(el, x.clone(), y.clone()), pl(el, y.clone(), x.clone()), s.clone(), comm); // ((x+y)+S)=((y+x)+S)
        let c = el
            .app("of-addass", &[("u", y.clone()), ("v", x.clone()), ("w", s.clone())], &[])
            .unwrap(); // ((y+x)+S)=(y+(x+S))
        let t1 = eqtr3(
            el,
            pl(el, x.clone(), pl(el, y.clone(), s.clone())),
            pl(el, pl(el, x.clone(), y.clone()), s.clone()),
            pl(el, pl(el, y.clone(), x.clone()), s.clone()),
            a1r,
            b,
        );
        return eqtr3(
            el,
            pl(el, x.clone(), pl(el, y.clone(), s.clone())),
            pl(el, pl(el, y.clone(), x.clone()), s.clone()),
            pl(el, y.clone(), pl(el, x.clone(), s.clone())),
            t1,
            c,
        );
    }
    // recurse under head atom
    let a0 = xs[0].clone();
    let p_tail = ra_swap_at(el, &xs[1..], k - 1);
    let mut swapped_tail = xs[1..].to_vec();
    swapped_tail.swap(k - 1, k);
    cpl2(el, ra(el, &xs[1..]), ra(el, &swapped_tail), a0, p_tail)
}

/// Proof `RA(xs) = RA(sorted)` by canonical token-key bubble sort.
fn ra_sort(el: &Elab, xs: &[Pt]) -> (Vec<Pt>, Pt) {
    let key = |p: &Pt| el.conclusion(p).map(|c| c[1..].join(" ")).unwrap_or_default();
    let mut cur = xs.to_vec();
    let mut proof = eqid(el, &ra(el, &cur));
    let n = cur.len();
    for i in 0..n {
        for j in 0..n - 1 - i {
            if key(&cur[j]) > key(&cur[j + 1]) {
                let before = ra(el, &cur);
                let sw = ra_swap_at(el, &cur, j);
                cur.swap(j, j + 1);
                let after = ra(el, &cur);
                // chain: RA(xs) = before = after
                proof = eqtr3(el, ra(el, xs), before, after, proof, sw);
            }
        }
    }
    (cur, proof)
}

/// Top-level: proof `t = canonical(t)` for a `+`-tree `t`.
fn ac_add(el: &Elab, t: &Pt) -> (Pt, Pt) {
    let (ats, pflat) = flatten(el, t);
    let (sorted, psort) = ra_sort(el, &ats);
    let canon = ra(el, &sorted);
    let proof = eqtr3(el, t.clone(), ra(el, &ats), canon.clone(), pflat, psort);
    (canon, proof)
}

// ===================================================================
//  Multiplicative-AC normalizer — same construction over `*`
//  (of-mulcom / of-mulass / cong-mu1 / cong-mu2).
// ===================================================================

fn is_mu(t: &Pt) -> bool {
    t.label == "tmu"
}
fn matoms(t: &Pt, out: &mut Vec<Pt>) {
    if is_mu(t) {
        matoms(&t.kids[0], out);
        matoms(&t.kids[1], out);
    } else {
        out.push(t.clone());
    }
}
fn mu(el: &Elab, u: Pt, v: Pt) -> Pt {
    el.app("tmu", &[("u", u), ("v", v)], &[]).unwrap()
}
fn rm(el: &Elab, xs: &[Pt]) -> Pt {
    if xs.len() == 1 {
        xs[0].clone()
    } else {
        mu(el, xs[0].clone(), rm(el, &xs[1..]))
    }
}
/// from `p : l = r` get `( l * w ) = ( r * w )`.
fn cmu1(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-mu1", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", mu(el, l, w.clone())), ("y", mu(el, r, w))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}
/// from `p : l = r` get `( w * l ) = ( w * r )`.
fn cmu2(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-mu2", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", mu(el, w.clone(), l)), ("y", mu(el, w, r))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}
fn append_rm(el: &Elab, al: &[Pt], ar: &[Pt]) -> Pt {
    let s_ar = rm(el, ar);
    if al.len() == 1 {
        eqid(el, &mu(el, al[0].clone(), s_ar))
    } else {
        let a0 = al[0].clone();
        let s_rest = rm(el, &al[1..]);
        let lhs = mu(el, mu(el, a0.clone(), s_rest.clone()), s_ar.clone());
        let assoc = el
            .app("of-mulass", &[("u", a0.clone()), ("v", s_rest.clone()), ("w", s_ar.clone())], &[])
            .unwrap();
        let inner = append_rm(el, &al[1..], ar);
        let mut tail = al[1..].to_vec();
        tail.extend_from_slice(ar);
        let s_tail = rm(el, &tail);
        let cong = cmu2(el, mu(el, s_rest.clone(), s_ar.clone()), s_tail.clone(), a0.clone(), inner);
        eqtr3(
            el,
            lhs,
            mu(el, a0.clone(), mu(el, s_rest, s_ar)),
            mu(el, a0, s_tail),
            assoc,
            cong,
        )
    }
}
fn flatten_m(el: &Elab, t: &Pt) -> (Vec<Pt>, Pt) {
    if !is_mu(t) {
        return (vec![t.clone()], eqid(el, t));
    }
    let l = &t.kids[0];
    let r = &t.kids[1];
    let (al, pl_) = flatten_m(el, l);
    let (ar, pr) = flatten_m(el, r);
    let s_al = rm(el, &al);
    let s_ar = rm(el, &ar);
    let c1 = cmu1(el, l.clone(), s_al.clone(), r.clone(), pl_);
    let c2 = cmu2(el, r.clone(), s_ar.clone(), s_al.clone(), pr);
    let step1 = eqtr3(
        el,
        mu(el, l.clone(), r.clone()),
        mu(el, s_al.clone(), r.clone()),
        mu(el, s_al.clone(), s_ar.clone()),
        c1,
        c2,
    );
    let papp = append_rm(el, &al, &ar);
    let mut all = al.clone();
    all.extend_from_slice(&ar);
    let s_all = rm(el, &all);
    let proof = eqtr3(
        el,
        mu(el, l.clone(), r.clone()),
        mu(el, s_al, s_ar),
        s_all,
        step1,
        papp,
    );
    (all, proof)
}
fn rm_swap_at(el: &Elab, xs: &[Pt], k: usize) -> Pt {
    if k == 0 {
        let x = xs[0].clone();
        let y = xs[1].clone();
        if xs.len() == 2 {
            return el.app("of-mulcom", &[("u", x), ("v", y)], &[]).unwrap();
        }
        let s = rm(el, &xs[2..]);
        let a1 = el
            .app("of-mulass", &[("u", x.clone()), ("v", y.clone()), ("w", s.clone())], &[])
            .unwrap();
        let a1r = el
            .app(
                "ax-mp",
                &[("ph", el.app("weq", &[("x", mu(el, mu(el, x.clone(), y.clone()), s.clone())), ("y", mu(el, x.clone(), mu(el, y.clone(), s.clone())))], &[]).unwrap()),
                  ("ps", el.app("weq", &[("x", mu(el, x.clone(), mu(el, y.clone(), s.clone()))), ("y", mu(el, mu(el, x.clone(), y.clone()), s.clone()))], &[]).unwrap())],
                &[a1, el.app("eqcom", &[("x", mu(el, mu(el, x.clone(), y.clone()), s.clone())), ("y", mu(el, x.clone(), mu(el, y.clone(), s.clone())))], &[]).unwrap()],
            )
            .unwrap();
        let comm = el.app("of-mulcom", &[("u", x.clone()), ("v", y.clone())], &[]).unwrap();
        let b = cmu1(el, mu(el, x.clone(), y.clone()), mu(el, y.clone(), x.clone()), s.clone(), comm);
        let c = el
            .app("of-mulass", &[("u", y.clone()), ("v", x.clone()), ("w", s.clone())], &[])
            .unwrap();
        let t1 = eqtr3(
            el,
            mu(el, x.clone(), mu(el, y.clone(), s.clone())),
            mu(el, mu(el, x.clone(), y.clone()), s.clone()),
            mu(el, mu(el, y.clone(), x.clone()), s.clone()),
            a1r,
            b,
        );
        return eqtr3(
            el,
            mu(el, x.clone(), mu(el, y.clone(), s.clone())),
            mu(el, mu(el, y.clone(), x.clone()), s.clone()),
            mu(el, y.clone(), mu(el, x.clone(), s.clone())),
            t1,
            c,
        );
    }
    let a0 = xs[0].clone();
    let p_tail = rm_swap_at(el, &xs[1..], k - 1);
    let mut swapped_tail = xs[1..].to_vec();
    swapped_tail.swap(k - 1, k);
    cmu2(el, rm(el, &xs[1..]), rm(el, &swapped_tail), a0, p_tail)
}
fn rm_sort(el: &Elab, xs: &[Pt]) -> (Vec<Pt>, Pt) {
    let key = |p: &Pt| el.conclusion(p).map(|c| c[1..].join(" ")).unwrap_or_default();
    let mut cur = xs.to_vec();
    let mut proof = eqid(el, &rm(el, &cur));
    let n = cur.len();
    for i in 0..n {
        for j in 0..n - 1 - i {
            if key(&cur[j]) > key(&cur[j + 1]) {
                let before = rm(el, &cur);
                let sw = rm_swap_at(el, &cur, j);
                cur.swap(j, j + 1);
                let after = rm(el, &cur);
                proof = eqtr3(el, rm(el, xs), before, after, proof, sw);
            }
        }
    }
    (cur, proof)
}
/// Top-level: proof `t = canonical(t)` for a `*`-tree `t`.
fn ac_mul(el: &Elab, t: &Pt) -> (Pt, Pt) {
    let mut ats = Vec::new();
    matoms(t, &mut ats);
    let (_, pflat) = flatten_m(el, t);
    let (sorted, psort) = rm_sort(el, &ats);
    let canon = rm(el, &sorted);
    let proof = eqtr3(el, t.clone(), rm(el, &ats), canon.clone(), pflat, psort);
    (canon, proof)
}

// ===================================================================
//  Distribution: expand a `{+,*}`-tree into a flat sum of monomials
//  (no `+` inside any `*`).  Uses of-distr (left) + of-mulcom-derived
//  right distribution.  AC + this = a complete ring normalizer.
// ===================================================================

fn eqcomm(el: &Elab, x: Pt, y: Pt, p: Pt) -> Pt {
    // from p : x = y  produce  y = x
    let ax = el
        .app("eqcom", &[("x", x.clone()), ("y", y.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", x.clone()), ("y", y.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", y), ("y", x)], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}

/// proof `( ( p + q ) * r ) = ( ( p * r ) + ( q * r ) )`  (right distrib.)
fn rdist(el: &Elab, p: Pt, q: Pt, r: Pt) -> Pt {
    let s = pl(el, p.clone(), q.clone());
    let c1 = el
        .app("of-mulcom", &[("u", s.clone()), ("v", r.clone())], &[])
        .unwrap(); // (p+q)*r = r*(p+q)
    let d = el
        .app("of-distr", &[("u", r.clone()), ("v", p.clone()), ("w", q.clone())], &[])
        .unwrap(); // r*(p+q) = r*p + r*q
    let cp = el.app("of-mulcom", &[("u", r.clone()), ("v", p.clone())], &[]).unwrap(); // r*p=p*r
    let cq = el.app("of-mulcom", &[("u", r.clone()), ("v", q.clone())], &[]).unwrap(); // r*q=q*r
    // r*p + r*q  =  p*r + r*q  =  p*r + q*r
    let e1 = cpl1(el, mu(el, r.clone(), p.clone()), mu(el, p.clone(), r.clone()), mu(el, r.clone(), q.clone()), cp);
    let e2 = cpl2(el, mu(el, r.clone(), q.clone()), mu(el, q.clone(), r.clone()), mu(el, p.clone(), r.clone()), cq);
    let rhs1 = pl(el, mu(el, r.clone(), p.clone()), mu(el, r.clone(), q.clone()));
    let rhs2 = pl(el, mu(el, p.clone(), r.clone()), mu(el, r.clone(), q.clone()));
    let rhs3 = pl(el, mu(el, p.clone(), r.clone()), mu(el, q.clone(), r.clone()));
    let t1 = eqtr3(el, mu(el, s.clone(), r.clone()), mu(el, r.clone(), s.clone()), rhs1.clone(), c1, d);
    let t2 = eqtr3(el, mu(el, s.clone(), r.clone()), rhs1, rhs2.clone(), t1, e1);
    eqtr3(el, mu(el, s, r), rhs2, rhs3, t2, e2)
}

/// proof `( RA(xs) * r ) = RA( [ xi * r ] )`.
fn distr_right(el: &Elab, xs: &[Pt], r: Pt) -> Pt {
    if xs.len() == 1 {
        return eqid(el, &mu(el, xs[0].clone(), r));
    }
    let a0 = xs[0].clone();
    let rest = ra(el, &xs[1..]);
    let head = rdist(el, a0.clone(), rest.clone(), r.clone()); // ((a0+rest)*r)=(a0*r + rest*r)
    let pr = distr_right(el, &xs[1..], r.clone()); // (rest*r)=RA([xi*r]rest)
    let tailmons: Vec<Pt> = xs[1..].iter().map(|x| mu(el, x.clone(), r.clone())).collect();
    let cong = cpl2(el, mu(el, rest.clone(), r.clone()), ra(el, &tailmons), mu(el, a0.clone(), r.clone()), pr);
    eqtr3(
        el,
        mu(el, ra(el, xs), r.clone()),
        pl(el, mu(el, a0.clone(), r.clone()), mu(el, rest, r.clone())),
        pl(el, mu(el, a0, r), ra(el, &tailmons)),
        head,
        cong,
    )
}

/// proof `( a * RA(ys) ) = RA( [ a * yj ] )`.
fn distr_left(el: &Elab, a: Pt, ys: &[Pt]) -> Pt {
    if ys.len() == 1 {
        return eqid(el, &mu(el, a, ys[0].clone()));
    }
    let b0 = ys[0].clone();
    let rest = ra(el, &ys[1..]);
    let head = el
        .app("of-distr", &[("u", a.clone()), ("v", b0.clone()), ("w", rest.clone())], &[])
        .unwrap(); // a*(b0+rest)=a*b0 + a*rest
    let pr = distr_left(el, a.clone(), &ys[1..]); // a*rest = RA([a*yj]rest)
    let tailmons: Vec<Pt> = ys[1..].iter().map(|y| mu(el, a.clone(), y.clone())).collect();
    let cong = cpl2(el, mu(el, a.clone(), rest.clone()), ra(el, &tailmons), mu(el, a.clone(), b0.clone()), pr);
    eqtr3(
        el,
        mu(el, a.clone(), ra(el, ys)),
        pl(el, mu(el, a.clone(), b0.clone()), mu(el, a.clone(), rest)),
        pl(el, mu(el, a.clone(), b0), ra(el, &tailmons)),
        head,
        cong,
    )
}

/// proof `RA(xs) = RA(concat over xi of expand_each(xi))`, where each xi
/// becomes the sum list `f(xi)`; pure congruence + append plumbing.
fn map_sum(el: &Elab, xs: &[Pt], f: &dyn Fn(&Elab, &Pt) -> (Vec<Pt>, Pt)) -> (Vec<Pt>, Pt) {
    let (l0, p0) = f(el, &xs[0]);
    if xs.len() == 1 {
        return (l0, p0);
    }
    let rest = &xs[1..];
    let (lr, pr) = map_sum(el, rest, f);
    // RA(xs) = ( x0 + RA(rest) ) = ( RA(l0) + RA(rest) ) = ( RA(l0) + RA(lr) ) = RA(l0++lr)
    let s_rest = ra(el, rest);
    let s_l0 = ra(el, &l0);
    let s_lr = ra(el, &lr);
    let c1 = cpl1(el, xs[0].clone(), s_l0.clone(), s_rest.clone(), p0);
    let c2 = cpl2(el, s_rest.clone(), s_lr.clone(), s_l0.clone(), pr);
    let step = eqtr3(
        el,
        pl(el, xs[0].clone(), s_rest.clone()),
        pl(el, s_l0.clone(), s_rest),
        pl(el, s_l0.clone(), s_lr.clone()),
        c1,
        c2,
    );
    let app = append_ra(el, &l0, &lr);
    let mut all = l0.clone();
    all.extend_from_slice(&lr);
    let proof = eqtr3(
        el,
        ra(el, xs),
        pl(el, s_l0, s_lr),
        ra(el, &all),
        step,
        app,
    );
    (all, proof)
}

/// Fully distribute `t` into a flat sum of monomials; returns
/// (monomial list, proof `t = RA(monomials)`).
fn distribute(el: &Elab, t: &Pt) -> (Vec<Pt>, Pt) {
    if is_pl(t) {
        let (lm, lp) = distribute(el, &t.kids[0]);
        let (rm_, rp) = distribute(el, &t.kids[1]);
        let s_l = ra(el, &lm);
        let s_r = ra(el, &rm_);
        let c1 = cpl1(el, t.kids[0].clone(), s_l.clone(), t.kids[1].clone(), lp);
        let c2 = cpl2(el, t.kids[1].clone(), s_r.clone(), s_l.clone(), rp);
        let step = eqtr3(
            el,
            pl(el, t.kids[0].clone(), t.kids[1].clone()),
            pl(el, s_l.clone(), t.kids[1].clone()),
            pl(el, s_l.clone(), s_r.clone()),
            c1,
            c2,
        );
        let app = append_ra(el, &lm, &rm_);
        let mut all = lm.clone();
        all.extend_from_slice(&rm_);
        let proof = eqtr3(el, t.clone(), pl(el, s_l, s_r), ra(el, &all), step, app);
        (all, proof)
    } else if is_mu(t) {
        let (lm, lp) = distribute(el, &t.kids[0]);
        let (rm_, rp) = distribute(el, &t.kids[1]);
        let s_l = ra(el, &lm);
        let s_r = ra(el, &rm_);
        // t = (l*r) = (s_l * r) = (s_l * s_r)
        let c1 = cmu1(el, t.kids[0].clone(), s_l.clone(), t.kids[1].clone(), lp);
        let c2 = cmu2(el, t.kids[1].clone(), s_r.clone(), s_l.clone(), rp);
        let base = eqtr3(
            el,
            mu(el, t.kids[0].clone(), t.kids[1].clone()),
            mu(el, s_l.clone(), t.kids[1].clone()),
            mu(el, s_l.clone(), s_r.clone()),
            c1,
            c2,
        );
        // (s_l * s_r) = RA([ li * s_r ])  then each li*s_r -> RA([li*rj])
        let dr = distr_right(el, &lm, s_r.clone()); // (s_l*s_r) = RA([li*s_r])
        let limons: Vec<Pt> = lm.iter().map(|li| mu(el, li.clone(), s_r.clone())).collect();
        let rm_clone = rm_.clone();
        let (mons, pmap) = map_sum(el, &limons, &move |el, m: &Pt| {
            // m = li * s_r ; expand to [li*rj]
            let li = m.kids[0].clone();
            let pl_ = distr_left(el, li.clone(), &rm_clone);
            let outs: Vec<Pt> = rm_clone.iter().map(|rj| mu(el, li.clone(), rj.clone())).collect();
            (outs, pl_)
        });
        let s_lim = ra(el, &limons);
        let proof = eqtr3(
            el,
            t.clone(),
            mu(el, s_l, s_r),
            ra(el, &mons),
            base,
            eqtr3(el, mu(el, ra(el, &lm), ra(el, &rm_)), s_lim, ra(el, &mons), dr, pmap),
        );
        (mons, proof)
    } else {
        (vec![t.clone()], eqid(el, t))
    }
}

/// Top-level ring normalizer: proof `t = canonical` (distribute, then
/// canonical-sort monomials, each monomial mul-canonicalized).
fn ring_norm(el: &Elab, t: &Pt) -> (Pt, Pt) {
    let (mons, pdist) = distribute(el, t); // t = RA(mons)
    // canonicalize each monomial (multiplicative AC)
    let canon_mons: Vec<Pt> = mons
        .iter()
        .map(|m| ac_mul(el, m).0)
        .collect();
    let pmono = {
        let mons2 = mons.clone();
        map_sum(el, &mons2, &move |el, m: &Pt| {
            let (c, p) = ac_mul(el, m);
            (vec![c], p)
        })
        .1
    };
    let after_mono = ra(el, &canon_mons);
    let step1 = eqtr3(el, t.clone(), ra(el, &mons), after_mono.clone(), pdist, pmono);
    // sort the monomials additively
    let (sorted, psort) = ra_sort(el, &canon_mons);
    let canon = ra(el, &sorted);
    let proof = eqtr3(el, t.clone(), after_mono, canon.clone(), step1, psort);
    (canon, proof)
}

// ===================================================================
//  Subtraction / negation layer.  `( a -x b )` is desugared (df-sub)
//  to `( a + ( 0 -x b ) )`; negation `( 0 -x s )` is the primitive.
//  A polynomial becomes a SIGNED multiset of monomials; identities are
//  decided by expanding both sides to a canonical signed sum and
//  matching syntactically.  All glue is kernel-checked via the derived
//  ring lemmas mul0 / neginv / negneg / negadd / mulneg1 / mulneg2.
// ===================================================================

fn t0p(el: &Elab) -> Pt {
    el.app("t0", &[], &[]).unwrap()
}
fn mi(el: &Elab, u: Pt, v: Pt) -> Pt {
    el.app("tmi", &[("u", u), ("v", v)], &[]).unwrap()
}
/// primitive negation `( 0 -x t )`.
fn neg(el: &Elab, t: Pt) -> Pt {
    mi(el, t0p(el), t)
}
fn is_t0(t: &Pt) -> bool {
    t.label == "t0"
}
fn is_mi(t: &Pt) -> bool {
    t.label == "tmi"
}
fn is_neg(t: &Pt) -> bool {
    is_mi(t) && is_t0(&t.kids[0])
}
/// structural Pt equality.
fn same(a: &Pt, b: &Pt) -> bool {
    a.label == b.label
        && a.kids.len() == b.kids.len()
        && a.kids.iter().zip(&b.kids).all(|(x, y)| same(x, y))
}
/// from `p : l = r` get `( l -x w ) = ( r -x w )`.
fn cmi1(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-mi1", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", mi(el, l, w.clone())), ("y", mi(el, r, w))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}
/// from `p : l = r` get `( w -x l ) = ( w -x r )`.
fn cmi2(el: &Elab, l: Pt, r: Pt, w: Pt, p: Pt) -> Pt {
    let ax = el
        .app("cong-mi2", &[("a", l.clone()), ("b", r.clone()), ("c", w.clone())], &[])
        .unwrap();
    el.app(
        "ax-mp",
        &[("ph", el.app("weq", &[("x", l.clone()), ("y", r.clone())], &[]).unwrap()),
          ("ps", el.app("weq", &[("x", mi(el, w.clone(), l)), ("y", mi(el, w, r))], &[]).unwrap())],
        &[p, ax],
    )
    .unwrap()
}
/// apply the `neginv` inference: from `p : ( u + v ) = 0` get `v = ( 0 -x u )`.
fn ninv(el: &Elab, u: Pt, v: Pt, p: Pt) -> Pt {
    el.app("neginv", &[("u", u), ("v", v)], &[p]).unwrap()
}

/// conjunction introduction (pm3.2i): from `pa : |- A` and `pb : |- B`
/// produce `|- ( A /\ B )`.  Requires the `pm3.2` lemma in the db.
fn conj2(el: &Elab, aw: Pt, bw: Pt, pa: Pt, pb: Pt) -> Pt {
    let p32 = el
        .app("pm3.2", &[("ph", aw.clone()), ("ps", bw.clone())], &[])
        .unwrap();
    let and = el
        .app("wa", &[("ph", aw.clone()), ("ps", bw.clone())], &[])
        .unwrap();
    let bi = el.app("wi", &[("ph", bw.clone()), ("ps", and.clone())], &[]).unwrap();
    let m1 = el
        .app("ax-mp", &[("ph", aw.clone()), ("ps", bi)], &[pa, p32])
        .unwrap();
    el.app("ax-mp", &[("ph", bw), ("ps", and)], &[pb, m1])
        .unwrap()
}

/// A signed monomial: (negated?, multiplicative atom list).
type SM = (bool, Vec<Pt>);

fn render(el: &Elab, m: &SM) -> Pt {
    let b = rm(el, &m.1);
    if m.0 { neg(el, b) } else { b }
}
fn renders(el: &Elab, ms: &[SM]) -> Vec<Pt> {
    ms.iter().map(|m| render(el, m)).collect()
}

/// Desugar every binary `( a -x b )` (a ≠ 0) to `( a + ( 0 -x b ) )`;
/// returns (rewritten term, proof `t = t'`).  Primitive negation
/// `( 0 -x s )` is preserved (its `s` still recursively desugared).
fn desub(el: &Elab, t: &Pt) -> (Pt, Pt) {
    match t.label.as_str() {
        "tmi" => {
            let (l1, lp) = desub(el, &t.kids[0]);
            let (r1, rp) = desub(el, &t.kids[1]);
            if is_t0(&t.kids[0]) {
                // ( 0 -x r ) -> ( 0 -x r1 ) : keep negation, recurse arg
                let res = neg(el, r1.clone());
                let pf = cmi2(el, t.kids[1].clone(), r1, t0p(el), rp);
                (res, pf)
            } else {
                // ( l -x r ) = ( l1 -x r1 ) = ( l1 + ( 0 -x r1 ) )
                let c1 = cmi1(el, t.kids[0].clone(), l1.clone(), t.kids[1].clone(), lp);
                let c2 = cmi2(el, t.kids[1].clone(), r1.clone(), l1.clone(), rp);
                let e0 = eqtr3(
                    el,
                    mi(el, t.kids[0].clone(), t.kids[1].clone()),
                    mi(el, l1.clone(), t.kids[1].clone()),
                    mi(el, l1.clone(), r1.clone()),
                    c1,
                    c2,
                );
                let ds = el
                    .app("df-sub", &[("u", l1.clone()), ("v", r1.clone())], &[])
                    .unwrap();
                let res = pl(el, l1.clone(), neg(el, r1.clone()));
                let pf = eqtr3(
                    el,
                    mi(el, t.kids[0].clone(), t.kids[1].clone()),
                    mi(el, l1, r1),
                    res.clone(),
                    e0,
                    ds,
                );
                (res, pf)
            }
        }
        "tpl" => {
            let (l1, lp) = desub(el, &t.kids[0]);
            let (r1, rp) = desub(el, &t.kids[1]);
            let c1 = cpl1(el, t.kids[0].clone(), l1.clone(), t.kids[1].clone(), lp);
            let c2 = cpl2(el, t.kids[1].clone(), r1.clone(), l1.clone(), rp);
            let res = pl(el, l1.clone(), r1.clone());
            let pf = eqtr3(
                el,
                pl(el, t.kids[0].clone(), t.kids[1].clone()),
                pl(el, l1.clone(), t.kids[1].clone()),
                res.clone(),
                c1,
                c2,
            );
            (res, pf)
        }
        "tmu" => {
            let (l1, lp) = desub(el, &t.kids[0]);
            let (r1, rp) = desub(el, &t.kids[1]);
            let c1 = cmu1(el, t.kids[0].clone(), l1.clone(), t.kids[1].clone(), lp);
            let c2 = cmu2(el, t.kids[1].clone(), r1.clone(), l1.clone(), rp);
            let res = mu(el, l1.clone(), r1.clone());
            let pf = eqtr3(
                el,
                mu(el, t.kids[0].clone(), t.kids[1].clone()),
                mu(el, l1.clone(), t.kids[1].clone()),
                res.clone(),
                c1,
                c2,
            );
            (res, pf)
        }
        _ => (t.clone(), eqid(el, t)),
    }
}

/// Flip a single rendered monomial: proof `( 0 -x render(m) ) = render(flip)`.
fn flip1(el: &Elab, m: &SM) -> (SM, Pt) {
    let base = rm(el, &m.1);
    if m.0 {
        // ( 0 -x ( 0 -x base ) ) = base
        let f = (false, m.1.clone());
        let p = el.app("negneg", &[("u", base.clone())], &[]).unwrap();
        (f, p)
    } else {
        // ( 0 -x base ) is already render(flip) — identity
        let f = (true, m.1.clone());
        (f, eqid(el, &neg(el, base)))
    }
}

/// proof `( 0 -x RA(render ms) ) = RA(render flip(ms))`.
fn negate_sum(el: &Elab, ms: &[SM]) -> (Vec<SM>, Pt) {
    if ms.len() == 1 {
        let (f, p) = flip1(el, &ms[0]);
        return (vec![f], p);
    }
    let m0 = &ms[0];
    let r0 = render(el, m0);
    let rest = &ms[1..];
    let rrest = ra(el, &renders(el, rest));
    // ( 0 -x ( r0 + RArest ) ) = ( ( 0 -x r0 ) + ( 0 -x RArest ) )
    let na = el
        .app("negadd", &[("u", r0.clone()), ("v", rrest.clone())], &[])
        .unwrap();
    let (f0, q0) = flip1(el, m0);
    let (frest, qr) = negate_sum(el, rest);
    let rf0 = render(el, &f0);
    let rfrest = ra(el, &renders(el, &frest));
    let c1 = cpl1(el, neg(el, r0.clone()), rf0.clone(), neg(el, rrest.clone()), q0);
    let c2 = cpl2(el, neg(el, rrest.clone()), rfrest.clone(), rf0.clone(), qr);
    let mid = pl(el, neg(el, r0.clone()), neg(el, rrest.clone()));
    let step = eqtr3(
        el,
        mid.clone(),
        pl(el, rf0.clone(), neg(el, rrest.clone())),
        pl(el, rf0.clone(), rfrest.clone()),
        c1,
        c2,
    );
    let lhs = neg(el, pl(el, r0, rrest));
    let proof = eqtr3(el, lhs, mid, pl(el, rf0, rfrest), na, step);
    let mut all = vec![f0];
    all.extend(frest);
    (all, proof)
}

/// proof `( render(lm) * render(rm) ) = render(prod)`, prod sign = xor.
fn signprod(el: &Elab, lm: &SM, rm_: &SM) -> (SM, Pt) {
    let bx = rm(el, &lm.1);
    let by = rm(el, &rm_.1);
    let mut atoms = lm.1.clone();
    atoms.extend(rm_.1.clone());
    let app = append_rm(el, &lm.1, &rm_.1); // ( bx * by ) = rm(atoms)
    let bxy = mu(el, bx.clone(), by.clone());
    let rmab = rm(el, &atoms);
    match (lm.0, rm_.0) {
        (false, false) => ((false, atoms), app),
        (true, false) => {
            // ( ( 0 -x bx ) * by ) = ( 0 -x ( bx * by ) ) = ( 0 -x rm(atoms) )
            let m1 = el
                .app("mulneg1", &[("u", bx.clone()), ("v", by.clone())], &[])
                .unwrap();
            let c = cmi2(el, bxy.clone(), rmab.clone(), t0p(el), app);
            let pf = eqtr3(
                el,
                mu(el, neg(el, bx), by),
                neg(el, bxy),
                neg(el, rmab),
                m1,
                c,
            );
            ((true, atoms), pf)
        }
        (false, true) => {
            let m2 = el
                .app("mulneg2", &[("u", bx.clone()), ("v", by.clone())], &[])
                .unwrap();
            let c = cmi2(el, bxy.clone(), rmab.clone(), t0p(el), app);
            let pf = eqtr3(
                el,
                mu(el, bx, neg(el, by)),
                neg(el, bxy),
                neg(el, rmab),
                m2,
                c,
            );
            ((true, atoms), pf)
        }
        (true, true) => {
            // ( (0-bx) * (0-by) ) = ( 0 -x ( bx * (0-by) ) )      [mulneg1]
            //                     = ( 0 -x ( 0 -x ( bx*by ) ) )   [mulneg2 in arg]
            //                     = ( bx * by )                    [negneg]
            //                     = rm(atoms)                      [append_rm]
            let nby = neg(el, by.clone());
            let m1 = el
                .app("mulneg1", &[("u", bx.clone()), ("v", nby.clone())], &[])
                .unwrap(); // ((0-bx)*(0-by)) = (0 -x (bx*(0-by)))
            let m2 = el
                .app("mulneg2", &[("u", bx.clone()), ("v", by.clone())], &[])
                .unwrap(); // (bx*(0-by)) = (0 -x (bx*by))
            let c = cmi2(el, mu(el, bx.clone(), nby.clone()), neg(el, bxy.clone()), t0p(el), m2);
            let nn = el.app("negneg", &[("u", bxy.clone())], &[]).unwrap(); // (0-(0-(bx*by))) = (bx*by)
            let s1 = eqtr3(
                el,
                mu(el, neg(el, bx.clone()), nby.clone()),
                neg(el, mu(el, bx.clone(), nby.clone())),
                neg(el, neg(el, bxy.clone())),
                m1,
                c,
            );
            let s2 = eqtr3(
                el,
                mu(el, neg(el, bx.clone()), nby),
                neg(el, neg(el, bxy.clone())),
                bxy.clone(),
                s1,
                nn,
            );
            let pf = eqtr3(el, mu(el, neg(el, bx), neg(el, by)), bxy, rmab, s2, app);
            ((false, atoms), pf)
        }
    }
}

/// Sign-aware distribute: returns (signed monomials, proof `t = RA(render)`).
fn sdist(el: &Elab, t: &Pt) -> (Vec<SM>, Pt) {
    if is_neg(t) {
        let (ms, p) = sdist(el, &t.kids[1]);
        let inner = ra(el, &renders(el, &ms));
        // ( 0 -x arg ) = ( 0 -x RA(render ms) )
        let c = cmi2(el, t.kids[1].clone(), inner.clone(), t0p(el), p);
        let (flipped, np) = negate_sum(el, &ms);
        let out = ra(el, &renders(el, &flipped));
        let proof = eqtr3(el, neg(el, t.kids[1].clone()), neg(el, inner), out, c, np);
        (flipped, proof)
    } else if is_pl(t) {
        let (ll, lp) = sdist(el, &t.kids[0]);
        let (lr, rp) = sdist(el, &t.kids[1]);
        let rl = ra(el, &renders(el, &ll));
        let rr = ra(el, &renders(el, &lr));
        let c1 = cpl1(el, t.kids[0].clone(), rl.clone(), t.kids[1].clone(), lp);
        let c2 = cpl2(el, t.kids[1].clone(), rr.clone(), rl.clone(), rp);
        let step = eqtr3(
            el,
            pl(el, t.kids[0].clone(), t.kids[1].clone()),
            pl(el, rl.clone(), t.kids[1].clone()),
            pl(el, rl.clone(), rr.clone()),
            c1,
            c2,
        );
        let mut all = ll.clone();
        all.extend(lr.clone());
        let app = append_ra(el, &renders(el, &ll), &renders(el, &lr));
        let proof = eqtr3(
            el,
            t.clone(),
            pl(el, rl, rr),
            ra(el, &renders(el, &all)),
            step,
            app,
        );
        (all, proof)
    } else if is_mu(t) {
        let (ll, lp) = sdist(el, &t.kids[0]);
        let (lr, rp) = sdist(el, &t.kids[1]);
        let rll = renders(el, &ll);
        let rlr = renders(el, &lr);
        let rl = ra(el, &rll);
        let rr = ra(el, &rlr);
        let c1 = cmu1(el, t.kids[0].clone(), rl.clone(), t.kids[1].clone(), lp);
        let c2 = cmu2(el, t.kids[1].clone(), rr.clone(), rl.clone(), rp);
        let base = eqtr3(
            el,
            mu(el, t.kids[0].clone(), t.kids[1].clone()),
            mu(el, rl.clone(), t.kids[1].clone()),
            mu(el, rl.clone(), rr.clone()),
            c1,
            c2,
        ); // t = ( rl * rr )
        let dr = distr_right(el, &rll, rr.clone()); // (rl*rr) = RA([ Li * rr ])
        let limons: Vec<Pt> = rll.iter().map(|li| mu(el, li.clone(), rr.clone())).collect();
        let rlr_c = rlr.clone();
        let (mons1, pmap1) = map_sum(el, &limons, &move |el, m: &Pt| {
            let li = m.kids[0].clone();
            let pl_ = distr_left(el, li.clone(), &rlr_c);
            let outs: Vec<Pt> = rlr_c.iter().map(|rj| mu(el, li.clone(), rj.clone())).collect();
            (outs, pl_)
        }); // RA([Li*rr]) = RA([ Li * Rj ])
        // build product SMs and replace each Li*Rj by render(prod)
        let mut prods: Vec<SM> = Vec::new();
        for a in &ll {
            for b in &lr {
                prods.push(signprod(el, a, b).0);
            }
        }
        let ll_c = ll.clone();
        let lr_c = lr.clone();
        let (mons2, pmap2) = map_sum(el, &mons1, &move |el, m: &Pt| {
            // recover indices by scanning (sizes are small)
            for a in &ll_c {
                for b in &lr_c {
                    let want = mu(el, render(el, a), render(el, b));
                    if same(&want, m) {
                        let (sm, pf) = signprod(el, a, b);
                        return (vec![render(el, &sm)], pf);
                    }
                }
            }
            unreachable!("signprod term not found")
        });
        let _ = mons2;
        let s_lim = ra(el, &limons);
        let dr_map = eqtr3(
            el,
            mu(el, ra(el, &rll), ra(el, &rlr)),
            s_lim.clone(),
            ra(el, &mons1),
            dr,
            pmap1,
        );
        let mid = eqtr3(
            el,
            mu(el, rl.clone(), rr.clone()),
            ra(el, &mons1),
            ra(el, &renders(el, &prods)),
            dr_map,
            pmap2,
        );
        let proof = eqtr3(
            el,
            t.clone(),
            mu(el, rl, rr),
            ra(el, &renders(el, &prods)),
            base,
            mid,
        );
        (prods, proof)
    } else {
        (vec![(false, vec![t.clone()])], eqid(el, t))
    }
}

/// proof `RA(xs) = RA(xs with index i replaced by y)`, given `p : xs[i] = y`.
fn replace_in_ra(el: &Elab, xs: &[Pt], i: usize, y: Pt, p: Pt) -> Pt {
    if i == 0 {
        if xs.len() == 1 {
            return p;
        }
        let tail = ra(el, &xs[1..]);
        return cpl1(el, xs[0].clone(), y, tail, p);
    }
    let head = xs[0].clone();
    let sub = replace_in_ra(el, &xs[1..], i - 1, y.clone(), p);
    let mut z = xs[1..].to_vec();
    z[i - 1] = y;
    cpl2(el, ra(el, &xs[1..]), ra(el, &z), head, sub)
}

/// Generic right-assoc sort by an arbitrary key (mirror of `ra_sort`).
fn ra_sort_by(el: &Elab, xs: &[Pt], key: &dyn Fn(&Pt) -> String) -> (Vec<Pt>, Pt) {
    let mut cur = xs.to_vec();
    let mut proof = eqid(el, &ra(el, &cur));
    let n = cur.len();
    for i in 0..n {
        for j in 0..n - 1 - i {
            if key(&cur[j]) > key(&cur[j + 1]) {
                let before = ra(el, &cur);
                let sw = ra_swap_at(el, &cur, j);
                cur.swap(j, j + 1);
                let after = ra(el, &cur);
                proof = eqtr3(el, ra(el, xs), before, after, proof, sw);
            }
        }
    }
    (cur, proof)
}

/// `a` and `b` are additive inverses (`b = 0-x a` or `a = 0-x b`).
fn inverse(a: &Pt, b: &Pt) -> bool {
    (is_neg(b) && same(&b.kids[1], a)) || (is_neg(a) && same(&a.kids[1], b))
}

/// proof `( a + b ) = 0` when `inverse(a,b)`.
fn ab_zero(el: &Elab, a: &Pt, b: &Pt) -> Pt {
    if is_neg(b) && same(&b.kids[1], a) {
        el.app("of-addinv", &[("u", a.clone())], &[]).unwrap()
    } else {
        // a = ( 0 -x b ):  (a+b) = ((0-b)+b) = (b+(0-b)) = 0
        let comm = el
            .app("of-addcom", &[("u", a.clone()), ("v", b.clone())], &[])
            .unwrap(); // ((0-b)+b)=(b+(0-b))
        let inv = el.app("of-addinv", &[("u", b.clone())], &[]).unwrap(); // (b+(0-b))=0
        eqtr3(
            el,
            pl(el, a.clone(), b.clone()),
            pl(el, b.clone(), neg(el, b.clone())),
            t0p(el),
            comm,
            inv,
        )
    }
}

/// Collapse the inverse pair at positions (i,i+1); proof `RA(ys)=RA(reduced)`.
fn collapse_at(el: &Elab, ys: &[Pt], i: usize) -> (Vec<Pt>, Pt) {
    if i > 0 {
        let head = ys[0].clone();
        let (red_tail, p) = collapse_at(el, &ys[1..], i - 1);
        let g = cpl2(el, ra(el, &ys[1..]), ra(el, &red_tail), head.clone(), p);
        let mut red = vec![head];
        red.extend(red_tail);
        return (red, g);
    }
    let a = ys[0].clone();
    let b = ys[1].clone();
    let ab0 = ab_zero(el, &a, &b);
    if ys.len() == 2 {
        return (vec![t0p(el)], ab0); // ( a + b ) = 0
    }
    let rest = ys[2..].to_vec();
    let rr = ra(el, &rest);
    let assoc = el
        .app("of-addass", &[("u", a.clone()), ("v", b.clone()), ("w", rr.clone())], &[])
        .unwrap(); // ((a+b)+rr)=(a+(b+rr))
    let assoc_r = eqcomm(
        el,
        pl(el, pl(el, a.clone(), b.clone()), rr.clone()),
        pl(el, a.clone(), pl(el, b.clone(), rr.clone())),
        assoc,
    );
    let c = cpl1(el, pl(el, a.clone(), b.clone()), t0p(el), rr.clone(), ab0);
    let zc = el
        .app("of-addcom", &[("u", t0p(el)), ("v", rr.clone())], &[])
        .unwrap();
    let z0 = el.app("of-add0", &[("u", rr.clone())], &[]).unwrap();
    let z = eqtr3(el, pl(el, t0p(el), rr.clone()), pl(el, rr.clone(), t0p(el)), rr.clone(), zc, z0);
    let lhs = pl(el, a.clone(), pl(el, b.clone(), rr.clone()));
    let e1 = eqtr3(el, lhs.clone(), pl(el, pl(el, a, b), rr.clone()), pl(el, t0p(el), rr.clone()), assoc_r, c);
    let e2 = eqtr3(el, lhs, pl(el, t0p(el), rr.clone()), rr.clone(), e1, z);
    (rest, e2)
}

/// Repeatedly cancel adjacent inverse pairs; proof `RA(xs)=RA(reduced)`.
fn collapse(el: &Elab, xs: &[Pt]) -> (Vec<Pt>, Pt) {
    let mut idx = None;
    for i in 0..xs.len().saturating_sub(1) {
        if inverse(&xs[i], &xs[i + 1]) {
            idx = Some(i);
            break;
        }
    }
    match idx {
        None => (xs.to_vec(), eqid(el, &ra(el, xs))),
        Some(i) => {
            let (red, p) = collapse_at(el, xs, i);
            let (red2, p2) = collapse(el, &red);
            let proof = eqtr3(el, ra(el, xs), ra(el, &red), ra(el, &red2), p, p2);
            (red2, proof)
        }
    }
}

/// Remove the additive-identity element `ys[i]` (which must be `0`);
/// proof `RA(ys) = RA(ys without i)`.  Requires `ys.len() >= 2`.
fn strip_at(el: &Elab, ys: &[Pt], i: usize) -> (Vec<Pt>, Pt) {
    if ys.len() == 2 {
        // ys[i] == 0
        if i == 0 {
            // ( 0 + b ) = b
            let bb = ys[1].clone();
            let zc = el
                .app("of-addcom", &[("u", t0p(el)), ("v", bb.clone())], &[])
                .unwrap();
            let z0 = el.app("of-add0", &[("u", bb.clone())], &[]).unwrap();
            let e = eqtr3(
                el,
                pl(el, t0p(el), bb.clone()),
                pl(el, bb.clone(), t0p(el)),
                bb.clone(),
                zc,
                z0,
            );
            return (vec![bb], e);
        }
        // i == 1 :  ( a + 0 ) = a
        let aa = ys[0].clone();
        let e = el.app("of-add0", &[("u", aa.clone())], &[]).unwrap();
        return (vec![aa], e);
    }
    if i > 0 {
        let head = ys[0].clone();
        let (tail_red, p) = strip_at(el, &ys[1..], i - 1);
        let g = cpl2(el, ra(el, &ys[1..]), ra(el, &tail_red), head.clone(), p);
        let mut red = vec![head];
        red.extend(tail_red);
        return (red, g);
    }
    // i == 0, len >= 3 :  RA(ys) = ( 0 + R ) ,  R = RA(ys[1..])
    let rest = ys[1..].to_vec();
    let r = ra(el, &rest);
    let zc = el
        .app("of-addcom", &[("u", t0p(el)), ("v", r.clone())], &[])
        .unwrap(); // ( 0 + R ) = ( R + 0 )
    let z0 = el.app("of-add0", &[("u", r.clone())], &[]).unwrap(); // ( R + 0 ) = R
    let e = eqtr3(
        el,
        pl(el, t0p(el), r.clone()),
        pl(el, r.clone(), t0p(el)),
        r.clone(),
        zc,
        z0,
    );
    (rest, e)
}

/// Drop spurious `0` summands left by `collapse` (keeping a lone `[0]`);
/// proof `RA(xs) = RA(stripped)`.  Makes the canonical form stable w.r.t.
/// the number of additive cancellations (so one-sided-cancellation
/// identities like `( u -x v ) + v = u` decide correctly).
fn strip0(el: &Elab, xs: &[Pt]) -> (Vec<Pt>, Pt) {
    if xs.len() < 2 {
        return (xs.to_vec(), eqid(el, &ra(el, xs)));
    }
    match xs.iter().position(is_t0) {
        None => (xs.to_vec(), eqid(el, &ra(el, xs))),
        Some(i) => {
            let (red, p) = strip_at(el, xs, i);
            let (red2, p2) = strip0(el, &red);
            let proof = eqtr3(el, ra(el, xs), ra(el, &red), ra(el, &red2), p, p2);
            (red2, proof)
        }
    }
}

/// Per-monomial atom-sort; returns (canonical monomials, proof
/// `RA(render ms) = RA(work)`).
fn canon_monos(el: &Elab, ms: &[SM]) -> (Vec<Pt>, Pt) {
    let src_rendered = renders(el, ms);
    let mut acc = eqid(el, &ra(el, &src_rendered));
    let mut work = src_rendered.clone();
    for i in 0..ms.len() {
        let (sa, pa) = rm_sort(el, &ms[i].1); // rm(atoms) = rm(sorted)
        let new_r = render(el, &(ms[i].0, sa.clone()));
        let p_one = if ms[i].0 {
            cmi2(el, rm(el, &ms[i].1), rm(el, &sa), t0p(el), pa)
        } else {
            pa
        };
        let p_rep = replace_in_ra(el, &work, i, new_r.clone(), p_one);
        let mut nw = work.clone();
        nw[i] = new_r;
        acc = eqtr3(el, ra(el, &src_rendered), ra(el, &work), ra(el, &nw), acc, p_rep);
        work = nw;
    }
    (work, acc)
}

/// Full canonical signed sum: per-monomial sort → group-sort so each
/// monomial sits next to its negation → cancel inverse pairs → final
/// sort.  Returns (canonical term, proof `RA(render ms) = canon`).
fn canon_sum(el: &Elab, ms: &[SM]) -> (Pt, Pt) {
    let (work, p_mono) = canon_monos(el, ms);
    let src = ra(el, &renders(el, ms));
    // group key: base monomial token, negation flag secondary (M next to -M)
    let gkey = |p: &Pt| {
        let (base, sk) = if is_neg(p) {
            (p.kids[1].clone(), "1")
        } else {
            (p.clone(), "0")
        };
        format!("{}|{}", el.conclusion(&base).map(|c| c[1..].join(" ")).unwrap_or_default(), sk)
    };
    let (grouped, pg) = ra_sort_by(el, &work, &gkey);
    let (canceled, pc) = collapse(el, &grouped);
    let (stripped, pst) = strip0(el, &canceled);
    let (sorted, ps) = ra_sort(el, &stripped);
    let canon = ra(el, &sorted);
    let e1 = eqtr3(el, src.clone(), ra(el, &work), ra(el, &grouped), p_mono, pg);
    let e2 = eqtr3(el, src.clone(), ra(el, &grouped), ra(el, &canceled), e1, pc);
    let e3 = eqtr3(el, src.clone(), ra(el, &canceled), ra(el, &stripped), e2, pst);
    let proof = eqtr3(el, src, ra(el, &stripped), canon.clone(), e3, ps);
    (canon, proof)
}

/// Decide a polynomial identity `lhs = rhs` over the F1 ring with
/// subtraction; returns a kernel proof or panics with the diff.
fn ring_eq(el: &Elab, lhs: &Pt, rhs: &Pt) -> Pt {
    let (l1, lp) = desub(el, lhs);
    let (r1, rp) = desub(el, rhs);
    let (lsm, lps) = sdist(el, &l1);
    let (rsm, rps) = sdist(el, &r1);
    let (lc, lcp) = canon_sum(el, &lsm);
    let (rc, rcp) = canon_sum(el, &rsm);
    if !same(&lc, &rc) {
        let lt = el.conclusion(&lc).map(|c| c.join(" ")).unwrap_or_default();
        let rt = el.conclusion(&rc).map(|c| c.join(" ")).unwrap_or_default();
        panic!("ring_eq: NOT an identity\n  lhs canon = {lt}\n  rhs canon = {rt}");
    }
    // lhs = l1 = RA(render lsm) = lc ;  rhs = r1 = RA(render rsm) = rc = lc
    let l_to_sum = eqtr3(el, lhs.clone(), l1.clone(), ra(el, &renders(el, &lsm)), lp, lps);
    let l_to_c = eqtr3(el, lhs.clone(), ra(el, &renders(el, &lsm)), lc.clone(), l_to_sum, lcp);
    let r_to_sum = eqtr3(el, rhs.clone(), r1.clone(), ra(el, &renders(el, &rsm)), rp, rps);
    let r_to_c = eqtr3(el, rhs.clone(), ra(el, &renders(el, &rsm)), rc.clone(), r_to_sum, rcp);
    let c_to_r = eqcomm(el, rhs.clone(), rc.clone(), r_to_c);
    eqtr3(el, lhs.clone(), lc, rhs.clone(), l_to_c, c_to_r)
}

/// Build the lemma at position `idx` (0-based) against the elaborator `el`,
/// whose database already contains lemmas `0..idx` as `$p`.
fn make_lemma(idx: usize, el: &Elab) -> Lemma {
    // wff/term constructor + rule shorthands over `el`
    let php = || leaf("wph");
    let pps = || leaf("wps");
    let pch = || leaf("wch");
    let n = |p: Pt| el.app("wn", &[("ph", p)], &[]).unwrap();
    let i = |p: Pt, q: Pt| el.app("wi", &[("ph", p), ("ps", q)], &[]).unwrap();
    let b = |p: Pt, q: Pt| el.app("wb", &[("ph", p), ("ps", q)], &[]).unwrap();
    let a = |p: Pt, q: Pt| el.app("wa", &[("ph", p), ("ps", q)], &[]).unwrap();
    // modus ponens with explicit (already-known) ph, ps
    let mp = |pw: Pt, qw: Pt, mn: Pt, mj: Pt| {
        el.app("ax-mp", &[("ph", pw), ("ps", qw)], &[mn, mj]).unwrap()
    };
    let ax1 = |p: Pt, q: Pt| el.app("ax-1", &[("ph", p), ("ps", q)], &[]).unwrap();
    let ax2 = |p: Pt, q: Pt, r: Pt| {
        el.app("ax-2", &[("ph", p), ("ps", q), ("ch", r)], &[]).unwrap()
    };
    let ax3 = |p: Pt, q: Pt| el.app("ax-3", &[("ph", p), ("ps", q)], &[]).unwrap();
    let syl = |p: Pt, q: Pt, r: Pt, s1: Pt, s2: Pt| {
        el.app("syl", &[("ph", p), ("ps", q), ("ch", r)], &[s1, s2])
            .unwrap()
    };

    match idx {
        // ---- 0: id  |- ( ph -> ph ) ----------------------------------
        0 => {
            let a1 = ax1(php(), i(php(), php()));
            let a2 = ax2(php(), i(php(), php()), php());
            let m1 = mp(
                i(php(), i(i(php(), php()), php())),
                i(i(php(), i(php(), php())), i(php(), php())),
                a1,
                a2,
            );
            let a1b = ax1(php(), php());
            let id = mp(i(php(), i(php(), php())), i(php(), php()), a1b, m1);
            Lemma { name: "id".into(), ess: vec![], goal: id }
        }
        // ---- 1: a1i   |- ph  =>  |- ( ps -> ph ) ---------------------
        1 => {
            let g = mp(php(), i(pps(), php()), leaf("a1i.1"), ax1(php(), pps()));
            Lemma {
                name: "a1i".into(),
                ess: vec![("a1i.1".into(), toks(&["|-", "ph"]))],
                goal: g,
            }
        }
        // ---- 2: syl  |- (ph->ps), |- (ps->ch)  =>  |- (ph->ch) -------
        2 => {
            let s2a1 = mp(
                i(pps(), pch()),
                i(php(), i(pps(), pch())),
                leaf("syl.2"),
                ax1(i(pps(), pch()), php()),
            );
            let m1 = mp(
                i(php(), i(pps(), pch())),
                i(i(php(), pps()), i(php(), pch())),
                s2a1,
                ax2(php(), pps(), pch()),
            );
            let g = mp(i(php(), pps()), i(php(), pch()), leaf("syl.1"), m1);
            Lemma {
                name: "syl".into(),
                ess: vec![
                    ("syl.1".into(), toks(&["|-", "(", "ph", "->", "ps", ")"])),
                    ("syl.2".into(), toks(&["|-", "(", "ps", "->", "ch", ")"])),
                ],
                goal: g,
            }
        }
        // ---- 3: pm2.21  |- ( -. ph -> ( ph -> ps ) ) -----------------
        3 => {
            let p1 = ax1(n(php()), n(pps()));
            let p2 = ax3(pps(), php());
            let g = syl(
                n(php()),
                i(n(pps()), n(php())),
                i(php(), pps()),
                p1,
                p2,
            );
            Lemma { name: "pm2.21".into(), ess: vec![], goal: g }
        }
        // ---- 4: pm2.43 (W)  |- ( (ph->(ph->ps)) -> (ph->ps) ) --------
        4 => {
            let hh = i(php(), i(php(), pps()));
            let u1 = ax2(php(), php(), pps());
            let idph = el.app("id", &[("ph", php())], &[]).unwrap();
            // a1i : |- (ph->ph)  =>  |- ( H -> (ph->ph) )
            let u2 = el
                .app("a1i", &[("ph", i(php(), php())), ("ps", hh.clone())], &[idph])
                .unwrap();
            let u3 = ax2(hh.clone(), i(php(), php()), i(php(), pps()));
            let u4 = mp(
                i(hh.clone(), i(i(php(), php()), i(php(), pps()))),
                i(i(hh.clone(), i(php(), php())), i(hh.clone(), i(php(), pps()))),
                u1,
                u3,
            );
            let g = mp(
                i(hh.clone(), i(php(), php())),
                i(hh.clone(), i(php(), pps())),
                u2,
                u4,
            );
            Lemma { name: "pm2.43".into(), ess: vec![], goal: g }
        }
        // ---- 5: notnot2  |- ( -. -. ph -> ph ) -----------------------
        5 => {
            // C = pm2.21[ph:=-.ph, ps:=-.-.-.ph] : ( --ph -> ( -ph -> ---ph ) )
            let c = el
                .app("pm2.21", &[("ph", n(php())), ("ps", n(n(n(php()))))], &[])
                .unwrap();
            // T1 = ax-3[ph:=ph, ps:=-.-.ph] : ( ( -ph -> ---ph ) -> ( --ph -> ph ) )
            let t1 = ax3(php(), n(n(php())));
            // syl(C,T1) : ( --ph -> ( --ph -> ph ) )
            let s = syl(
                n(n(php())),
                i(n(php()), n(n(n(php())))),
                i(n(n(php())), php()),
                c,
                t1,
            );
            // pm2.43[ph:=--ph, ps:=ph] : ( ( --ph -> (--ph -> ph) ) -> ( --ph -> ph ) )
            let w = el
                .app("pm2.43", &[("ph", n(n(php()))), ("ps", php())], &[])
                .unwrap();
            let g = mp(
                i(n(n(php())), i(n(n(php())), php())),
                i(n(n(php())), php()),
                s,
                w,
            );
            Lemma { name: "notnot2".into(), ess: vec![], goal: g }
        }
        // ---- 6: notnot1  |- ( ph -> -. -. ph ) -----------------------
        6 => {
            // T2 = ax-3[ph:=--ph, ps:=ph] : ( ( ---ph -> -ph ) -> ( ph -> --ph ) )
            let t2 = ax3(n(n(php())), php());
            // M = notnot2[ph:=-.ph] : ( ---ph -> -ph )
            let m = el.app("notnot2", &[("ph", n(php()))], &[]).unwrap();
            let g = mp(
                i(n(n(n(php()))), n(php())),
                i(php(), n(n(php()))),
                m,
                t2,
            );
            Lemma { name: "notnot1".into(), ess: vec![], goal: g }
        }
        // ---- 7: simpl  |- ( ( ph /\ ps ) -> ph ) ---------------------
        7 => {
            let k = i(php(), n(pps())); // K = (ph -> -.ps)
            let dfan = el.app("df-an", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi1 = el
                .app("ax-bi1", &[("ph", a(php(), pps())), ("ps", n(k.clone()))], &[])
                .unwrap();
            let aa = mp(
                b(a(php(), pps()), n(k.clone())),
                i(a(php(), pps()), n(k.clone())),
                dfan,
                bi1,
            ); // A : ( (ph/\ps) -> -.K )
            let p = el
                .app("pm2.21", &[("ph", php()), ("ps", n(pps()))], &[])
                .unwrap(); // P : ( -.ph -> K )
            let nn1k = el.app("notnot1", &[("ph", k.clone())], &[]).unwrap(); // ( K -> --K )
            let q = syl(n(php()), k.clone(), n(n(k.clone())), p, nn1k); // ( -.ph -> --K )
            let t3 = ax3(php(), n(k.clone())); // ( ( -ph -> --K ) -> ( -K -> ph ) )
            let bb = mp(
                i(n(php()), n(n(k.clone()))),
                i(n(k.clone()), php()),
                q,
                t3,
            ); // B : ( -.K -> ph )
            let g = syl(a(php(), pps()), n(k.clone()), php(), aa, bb);
            Lemma { name: "simpl".into(), ess: vec![], goal: g }
        }
        // ---- 8: simpr  |- ( ( ph /\ ps ) -> ps ) ---------------------
        8 => {
            let k = i(php(), n(pps()));
            let dfan = el.app("df-an", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi1 = el
                .app("ax-bi1", &[("ph", a(php(), pps())), ("ps", n(k.clone()))], &[])
                .unwrap();
            let aa = mp(
                b(a(php(), pps()), n(k.clone())),
                i(a(php(), pps()), n(k.clone())),
                dfan,
                bi1,
            ); // A : ( (ph/\ps) -> -.K )
            let r = ax1(n(pps()), php()); // R : ( -.ps -> ( ph -> -.ps ) ) = ( -.ps -> K )
            let nn1k = el.app("notnot1", &[("ph", k.clone())], &[]).unwrap();
            let q2 = syl(n(pps()), k.clone(), n(n(k.clone())), r, nn1k); // ( -.ps -> --K )
            let t4 = ax3(pps(), n(k.clone())); // ( ( -ps -> --K ) -> ( -K -> ps ) )
            let bp = mp(
                i(n(pps()), n(n(k.clone()))),
                i(n(k.clone()), pps()),
                q2,
                t4,
            ); // B' : ( -.K -> ps )
            let g = syl(a(php(), pps()), n(k.clone()), pps(), aa, bp);
            Lemma { name: "simpr".into(), ess: vec![], goal: g }
        }
        // ---- 9: G3c rayline  |- ( ( Ray a c x ) -> ( On x ( Ln a c ) ) ) ----
        9 => {
            let va = || leaf("va");
            let vc = || leaf("vc");
            let vx = || leaf("vx");
            let ray = el
                .app("wray", &[("a", va()), ("b", vc()), ("c", vx())], &[])
                .unwrap();
            let coll = el
                .app("wcoll", &[("a", va()), ("b", vc()), ("c", vx())], &[])
                .unwrap();
            // ( 0 <_ ( dot a c x ) ) — rebuilt wherever needed (terms are pure)
            let le = || {
                let dot = el
                    .app("tdot", &[("o", va()), ("p", vc()), ("q", vx())], &[])
                    .unwrap();
                let t0 = el.app("t0", &[], &[]).unwrap();
                el.app("tle", &[("u", t0), ("v", dot)], &[]).unwrap()
            };
            let conj = a(coll.clone(), le());
            let onx = el
                .app("won", &[("a", vx()), ("b", va()), ("c", vc())], &[])
                .unwrap();

            let dfray = el
                .app("df-ray", &[("a", va()), ("b", vc()), ("c", vx())], &[])
                .unwrap();
            let bi1r = el
                .app("ax-bi1", &[("ph", ray.clone()), ("ps", conj.clone())], &[])
                .unwrap();
            let r1 = mp(
                b(ray.clone(), conj.clone()),
                i(ray.clone(), conj.clone()),
                dfray,
                bi1r,
            ); // ( Ray a c x ) -> conj
            let spl = el
                .app("simpl", &[("ph", coll.clone()), ("ps", le())], &[])
                .unwrap();
            let r3 = syl(ray.clone(), conj.clone(), coll.clone(), r1, spl);
            let dfon = el
                .app("df-on", &[("x", vx()), ("a", va()), ("b", vc())], &[])
                .unwrap();
            let bi2o = el
                .app("ax-bi2", &[("ph", onx.clone()), ("ps", coll.clone())], &[])
                .unwrap();
            let r4 = mp(
                b(onx.clone(), coll.clone()),
                i(coll.clone(), onx.clone()),
                dfon,
                bi2o,
            ); // ( Coll a c x ) -> ( On x ( Ln a c ) )
            let g = syl(ray.clone(), coll.clone(), onx.clone(), r3, r4);
            Lemma { name: "G3c-rayline".into(), ess: vec![], goal: g }
        }
        // ---- 10: eqtrd  (ph->x=y),(ph->y=z) => (ph->x=z) -------------
        10 => {
            let vx = || leaf("vx");
            let vy = || leaf("vy");
            let vz = || leaf("vz");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            // EQT (closed transitivity): ( x=y -> ( y=z -> x=z ) )
            let eqc = el.app("eqcom", &[("x", vx()), ("y", vy())], &[]).unwrap();
            let a7 = el
                .app("ax-7", &[("x", vy()), ("y", vx()), ("z", vz())], &[])
                .unwrap();
            let eqt = syl(
                eq(vx(), vy()),
                eq(vy(), vx()),
                i(eq(vy(), vz()), eq(vx(), vz())),
                eqc,
                a7,
            ); // ( x=y -> ( y=z -> x=z ) )
            let s1 = syl(
                php(),
                eq(vx(), vy()),
                i(eq(vy(), vz()), eq(vx(), vz())),
                leaf("eqtrd.1"),
                eqt,
            ); // ( ph -> ( y=z -> x=z ) )
            let m1 = mp(
                i(php(), i(eq(vy(), vz()), eq(vx(), vz()))),
                i(i(php(), eq(vy(), vz())), i(php(), eq(vx(), vz()))),
                s1,
                ax2(php(), eq(vy(), vz()), eq(vx(), vz())),
            );
            let g = mp(
                i(php(), eq(vy(), vz())),
                i(php(), eq(vx(), vz())),
                leaf("eqtrd.2"),
                m1,
            );
            Lemma {
                name: "eqtrd".into(),
                ess: vec![
                    (
                        "eqtrd.1".into(),
                        toks(&["|-", "(", "ph", "->", "x", "=", "y", ")"]),
                    ),
                    (
                        "eqtrd.2".into(),
                        toks(&["|-", "(", "ph", "->", "y", "=", "z", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 11: G0 cong-sub  |- ( x = y -> ( sqd a x ) = ( sqd a y ) ) ----
        11 => {
            let va = || leaf("va");
            let vx = || leaf("vx");
            let vy = || leaf("vy");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let xc = |t: Pt| el.app("txc", &[("a", t)], &[]).unwrap();
            let yc = |t: Pt| el.app("tyc", &[("a", t)], &[]).unwrap();
            let pl = |u: Pt, v: Pt| el.app("tpl", &[("u", u), ("v", v)], &[]).unwrap();
            let mi = |u: Pt, v: Pt| el.app("tmi", &[("u", u), ("v", v)], &[]).unwrap();
            let mu = |u: Pt, v: Pt| el.app("tmu", &[("u", u), ("v", v)], &[]).unwrap();
            let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
            let cxc = |p: Pt, q: Pt| el.app("cong-xc", &[("a", p), ("b", q)], &[]).unwrap();
            let cyc = |p: Pt, q: Pt| el.app("cong-yc", &[("a", p), ("b", q)], &[]).unwrap();
            let cpl1 = |p: Pt, q: Pt, r: Pt| {
                el.app("cong-pl1", &[("a", p), ("b", q), ("c", r)], &[]).unwrap()
            };
            let cpl2 = |p: Pt, q: Pt, r: Pt| {
                el.app("cong-pl2", &[("a", p), ("b", q), ("c", r)], &[]).unwrap()
            };
            let cmi1 = |p: Pt, q: Pt, r: Pt| {
                el.app("cong-mi1", &[("a", p), ("b", q), ("c", r)], &[]).unwrap()
            };
            let cmu1 = |p: Pt, q: Pt, r: Pt| {
                el.app("cong-mu1", &[("a", p), ("b", q), ("c", r)], &[]).unwrap()
            };
            let cmu2 = |p: Pt, q: Pt, r: Pt| {
                el.app("cong-mu2", &[("a", p), ("b", q), ("c", r)], &[]).unwrap()
            };
            let eqtrd = |ph: Pt, x: Pt, y: Pt, z: Pt, p1: Pt, p2: Pt| {
                // eqtrd ess are scoped ph,x,y,z — bind via mandatory $f
                el.app(
                    "eqtrd",
                    &[("ph", ph), ("x", x), ("y", y), ("z", z)],
                    &[p1, p2],
                )
                .unwrap()
            };

            let ph = || eq(vx(), vy()); // antecedent ph := ( x = y )
            let dx = || mi(xc(vx()), xc(va())); // ( Xc x -x Xc a )
            let dy = || mi(xc(vy()), xc(va()));
            let qx = || mi(yc(vx()), yc(va())); // ( Yc x -x Yc a )
            let qy = || mi(yc(vy()), yc(va()));
            let ex = || pl(mu(dx(), dx()), mu(qx(), qx()));
            let ey = || pl(mu(dy(), dy()), mu(qy(), qy()));
            let sx = || sqd(va(), vx());
            let sy = || sqd(va(), vy());

            // X-coordinate difference: ( ph -> dx = dy )
            let cxx = cxc(vx(), vy()); // ( x=y -> Xc x = Xc y )
            let dxe = syl(
                ph(),
                eq(xc(vx()), xc(vy())),
                eq(dx(), dy()),
                cxx,
                cmi1(xc(vx()), xc(vy()), xc(va())),
            );
            // ( ph -> dx*dx = dy*dy )
            let m1 = syl(
                ph(),
                eq(dx(), dy()),
                eq(mu(dx(), dx()), mu(dy(), dx())),
                dxe.clone(),
                cmu1(dx(), dy(), dx()),
            );
            let m2 = syl(
                ph(),
                eq(dx(), dy()),
                eq(mu(dy(), dx()), mu(dy(), dy())),
                dxe,
                cmu2(dx(), dy(), dy()),
            );
            let px = eqtrd(ph(), mu(dx(), dx()), mu(dy(), dx()), mu(dy(), dy()), m1, m2);
            // Y-coordinate difference: ( ph -> qx*qx = qy*qy )
            let cyx = cyc(vx(), vy());
            let qxe = syl(
                ph(),
                eq(yc(vx()), yc(vy())),
                eq(qx(), qy()),
                cyx,
                cmi1(yc(vx()), yc(vy()), yc(va())),
            );
            let n1 = syl(
                ph(),
                eq(qx(), qy()),
                eq(mu(qx(), qx()), mu(qy(), qx())),
                qxe.clone(),
                cmu1(qx(), qy(), qx()),
            );
            let n2 = syl(
                ph(),
                eq(qx(), qy()),
                eq(mu(qy(), qx()), mu(qy(), qy())),
                qxe,
                cmu2(qx(), qy(), qy()),
            );
            let py = eqtrd(ph(), mu(qx(), qx()), mu(qy(), qx()), mu(qy(), qy()), n1, n2);
            // combine the two summands: ( ph -> Ex = Ey )
            let s1 = syl(
                ph(),
                eq(mu(dx(), dx()), mu(dy(), dy())),
                eq(ex(), pl(mu(dy(), dy()), mu(qx(), qx()))),
                px,
                cpl1(mu(dx(), dx()), mu(dy(), dy()), mu(qx(), qx())),
            );
            let s2 = syl(
                ph(),
                eq(mu(qx(), qx()), mu(qy(), qy())),
                eq(pl(mu(dy(), dy()), mu(qx(), qx())), ey()),
                py,
                cpl2(mu(qx(), qx()), mu(qy(), qy()), mu(dy(), dy())),
            );
            let ee = eqtrd(
                ph(),
                ex(),
                pl(mu(dy(), dy()), mu(qx(), qx())),
                ey(),
                s1,
                s2,
            );
            // connect to sqd via df-sqd (unconditional -> antecedent via a1i)
            let dfx = el.app("df-sqd", &[("a", va()), ("b", vx())], &[]).unwrap();
            let sxe = el
                .app("a1i", &[("ph", eq(sx(), ex())), ("ps", ph())], &[dfx])
                .unwrap(); // ( ph -> ( sqd a x ) = Ex )
            let dfy = el.app("df-sqd", &[("a", va()), ("b", vy())], &[]).unwrap();
            let eyr = mp(
                eq(sy(), ey()),
                eq(ey(), sy()),
                dfy,
                el.app("eqcom", &[("x", sy()), ("y", ey())], &[]).unwrap(),
            ); // Ey = ( sqd a y )
            let syr = el
                .app("a1i", &[("ph", eq(ey(), sy())), ("ps", ph())], &[eyr])
                .unwrap(); // ( ph -> Ey = ( sqd a y ) )
            let t1 = eqtrd(ph(), sx(), ex(), ey(), sxe, ee);
            let g = eqtrd(ph(), sx(), ey(), sy(), t1, syr);
            Lemma { name: "G0-congsub".into(), ess: vec![], goal: g }
        }
        // ---- 12: eqtr (inference)  |- x=y, |- y=z  =>  |- x=z ---------
        12 => {
            let vx = || leaf("vx");
            let vy = || leaf("vy");
            let vz = || leaf("vz");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let yx = mp(
                eq(vx(), vy()),
                eq(vy(), vx()),
                leaf("eqtr.1"),
                el.app("eqcom", &[("x", vx()), ("y", vy())], &[]).unwrap(),
            );
            let a7 = el
                .app("ax-7", &[("x", vy()), ("y", vx()), ("z", vz())], &[])
                .unwrap();
            let t = mp(eq(vy(), vx()), i(eq(vy(), vz()), eq(vx(), vz())), yx, a7);
            let g = mp(eq(vy(), vz()), eq(vx(), vz()), leaf("eqtr.2"), t);
            Lemma {
                name: "eqtr".into(),
                ess: vec![
                    ("eqtr.1".into(), toks(&["|-", "x", "=", "y"])),
                    ("eqtr.2".into(), toks(&["|-", "y", "=", "z"])),
                ],
                goal: g,
            }
        }
        // ---- 13: addcan  |- ( a + c ) = ( b + c )  =>  |- a = b ------
        //  Additive cancellation — derived from the of-* ring axioms (no new
        //  axiom): the ordered ring suffices for the field algebra the geometry
        //  needs.
        13 => {
            let aa = || leaf("va");
            let bb = || leaf("vb");
            let cc = || leaf("vc");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let pl = |u: Pt, v: Pt| el.app("tpl", &[("u", u), ("v", v)], &[]).unwrap();
            let mi = |u: Pt, v: Pt| el.app("tmi", &[("u", u), ("v", v)], &[]).unwrap();
            let t0 = || el.app("t0", &[], &[]).unwrap();
            let ninv = |t: Pt| mi(t0(), t); // ( 0 -x t )
            let eqcom = |s: Pt, t: Pt| el.app("eqcom", &[("x", s), ("y", t)], &[]).unwrap();
            let eqtr = |x: Pt, y: Pt, z: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", z)], &[p1, p2])
                    .unwrap()
            };
            // shrink ( ( s + c ) + (0-c) )  to  s   (s = a or b)
            let shrink = |s: Pt| -> Pt {
                let inner = pl(s.clone(), cc()); // ( s + c )
                let lhs = pl(inner.clone(), ninv(cc())); // ( (s+c) + (0-c) )
                let assoc = el
                    .app(
                        "of-addass",
                        &[("u", s.clone()), ("v", cc()), ("w", ninv(cc()))],
                        &[],
                    )
                    .unwrap(); // ( (s+c)+(0-c) ) = ( s + ( c + (0-c) ) )
                let invc = el.app("of-addinv", &[("u", cc())], &[]).unwrap(); // ( c + (0-c) ) = 0
                let cpl2 = el
                    .app(
                        "cong-pl2",
                        &[("a", pl(cc(), ninv(cc()))), ("b", t0()), ("c", s.clone())],
                        &[],
                    )
                    .unwrap(); // ( (c+(0-c))=0 -> ( s+(c+(0-c)) )=( s+0 ) )
                let to_s0 = mp(
                    eq(pl(cc(), ninv(cc())), t0()),
                    eq(pl(s.clone(), pl(cc(), ninv(cc()))), pl(s.clone(), t0())),
                    invc,
                    cpl2,
                ); // ( s+(c+(0-c)) ) = ( s + 0 )
                let add0 = el.app("of-add0", &[("u", s.clone())], &[]).unwrap(); // ( s + 0 ) = s
                // ( (s+c)+(0-c) ) = ( s+(c+(0-c)) ) = ( s+0 ) = s
                let e1 = eqtr(
                    lhs.clone(),
                    pl(s.clone(), pl(cc(), ninv(cc()))),
                    pl(s.clone(), t0()),
                    assoc,
                    to_s0,
                );
                eqtr(lhs, pl(s.clone(), t0()), s.clone(), e1, add0)
            };
            let lred = shrink(aa()); // ( (a+c)+(0-c) ) = a
            let rred = shrink(bb()); // ( (b+c)+(0-c) ) = b
            // congruence of the hypothesis by (+ (0-c)):
            let cpl1 = el
                .app(
                    "cong-pl1",
                    &[
                        ("a", pl(aa(), cc())),
                        ("b", pl(bb(), cc())),
                        ("c", ninv(cc())),
                    ],
                    &[],
                )
                .unwrap(); // ( (a+c)=(b+c) -> ( (a+c)+(0-c) )=( (b+c)+(0-c) ) )
            let e1 = mp(
                eq(pl(aa(), cc()), pl(bb(), cc())),
                eq(
                    pl(pl(aa(), cc()), ninv(cc())),
                    pl(pl(bb(), cc()), ninv(cc())),
                ),
                leaf("addcan.1"),
                cpl1,
            );
            // a = ( (a+c)+(0-c) ) = ( (b+c)+(0-c) ) = b
            let a_eq_l = mp(
                eq(pl(pl(aa(), cc()), ninv(cc())), aa()),
                eq(aa(), pl(pl(aa(), cc()), ninv(cc()))),
                lred,
                eqcom(pl(pl(aa(), cc()), ninv(cc())), aa()),
            ); // a = ( (a+c)+(0-c) )
            let a_eq_r = eqtr(
                aa(),
                pl(pl(aa(), cc()), ninv(cc())),
                pl(pl(bb(), cc()), ninv(cc())),
                a_eq_l,
                e1,
            ); // a = ( (b+c)+(0-c) )
            let g = eqtr(
                aa(),
                pl(pl(bb(), cc()), ninv(cc())),
                bb(),
                a_eq_r,
                rred,
            ); // a = b
            Lemma {
                name: "addcan".into(),
                ess: vec![(
                    "addcan.1".into(),
                    toks(&["|-", "(", "a", "+", "c", ")", "=", "(", "b", "+", "c", ")"]),
                )],
                goal: g,
            }
        }
        // ---- 14: ac-demo — exercise the additive-AC mini-prover -------
        //  ( ( c + a ) + ( b + c ) ) = ( a + ( b + ( c + c ) ) )
        14 => {
            let va = leaf("va");
            let vb = leaf("vb");
            let vc = leaf("vc");
            let lhs = pl(
                el,
                pl(el, vc.clone(), va.clone()),
                pl(el, vb.clone(), vc.clone()),
            );
            let (_canon, proof) = ac_add(el, &lhs);
            Lemma { name: "ac-demo".into(), ess: vec![], goal: proof }
        }
        // ---- 15: ac-mul-demo — exercise the multiplicative-AC prover -
        //  ( ( c * a ) * ( b * c ) ) = ( a * ( b * ( c * c ) ) )
        15 => {
            let va = leaf("va");
            let vb = leaf("vb");
            let vc = leaf("vc");
            let lhs = mu(
                el,
                mu(el, vc.clone(), va.clone()),
                mu(el, vb.clone(), vc.clone()),
            );
            let (_canon, proof) = ac_mul(el, &lhs);
            Lemma { name: "ac-mul-demo".into(), ess: vec![], goal: proof }
        }
        // ---- 16: ring-demo — full ring normalizer end-to-end ---------
        //  ( ( a + b ) * ( c + a ) ) = canonical sum of monomials
        16 => {
            let va = leaf("va");
            let vb = leaf("vb");
            let vc = leaf("vc");
            let lhs = mu(
                el,
                pl(el, va.clone(), vb.clone()),
                pl(el, vc.clone(), va.clone()),
            );
            let (_canon, proof) = ring_norm(el, &lhs);
            Lemma { name: "ring-demo".into(), ess: vec![], goal: proof }
        }
        // ---- 17: mul0  |- ( 0 * u ) = 0  (derived; needs addcan) -----
        17 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let muu = |x: Pt, y: Pt| mu(el, x, y);
            let plu = |x: Pt, y: Pt| pl(el, x, y);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let m0u = muu(z(), u());
            let add00 = el.app("of-add0", &[("u", z())], &[]).unwrap(); // (0+0)=0
            let ea = eqcomm(el, plu(z(), z()), z(), add00); // 0=(0+0)
            let c1 = cmu1(el, z(), plu(z(), z()), u(), ea); // (0*u)=((0+0)*u)
            let rd = rdist(el, z(), z(), u()); // ((0+0)*u)=(0*u)+(0*u)
            let dup = eqtr(m0u.clone(), muu(plu(z(), z()), u()), plu(m0u.clone(), m0u.clone()), c1, rd);
            let left_eq = eqcomm(el, m0u.clone(), plu(m0u.clone(), m0u.clone()), dup); // ((0*u)+(0*u))=(0*u)
            let r1 = el.app("of-addcom", &[("u", z()), ("v", m0u.clone())], &[]).unwrap(); // (0+(0*u))=((0*u)+0)
            let r2 = el.app("of-add0", &[("u", m0u.clone())], &[]).unwrap(); // ((0*u)+0)=(0*u)
            let r12 = eqtr(plu(z(), m0u.clone()), plu(m0u.clone(), z()), m0u.clone(), r1, r2);
            let r12c = eqcomm(el, plu(z(), m0u.clone()), m0u.clone(), r12); // (0*u)=(0+(0*u))
            let eqn = eqtr(
                plu(m0u.clone(), m0u.clone()),
                m0u.clone(),
                plu(z(), m0u.clone()),
                left_eq,
                r12c,
            ); // ((0*u)+(0*u))=(0+(0*u))
            let g = el
                .app("addcan", &[("a", m0u.clone()), ("b", z()), ("c", m0u.clone())], &[eqn])
                .unwrap();
            Lemma { name: "mul0".into(), ess: vec![], goal: g }
        }
        // ---- 18: neginv  |- (u+v)=0  =>  |- v = ( 0 -x u ) ----------
        18 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let nn = |x: Pt| neg(el, x);
            let plu = |x: Pt, y: Pt| pl(el, x, y);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let h = leaf("neginv.1"); // ( u + v ) = 0
            let pa = el.app("of-add0", &[("u", nn(u()))], &[]).unwrap(); // ((0-u)+0)=(0-u)
            let hc = cpl2(el, plu(u(), v()), z(), nn(u()), h.clone()); // ((0-u)+(u+v))=((0-u)+0)
            let assoc = el
                .app("of-addass", &[("u", nn(u())), ("v", u()), ("w", v())], &[])
                .unwrap(); // (((0-u)+u)+v)=((0-u)+(u+v))
            let comm = el.app("of-addcom", &[("u", nn(u())), ("v", u())], &[]).unwrap(); // ((0-u)+u)=(u+(0-u))
            let inv = el.app("of-addinv", &[("u", u())], &[]).unwrap(); // (u+(0-u))=0
            let p_iu = eqtr(plu(nn(u()), u()), plu(u(), nn(u())), z(), comm, inv); // ((0-u)+u)=0
            let cong1 = cpl1(el, plu(nn(u()), u()), z(), v(), p_iu); // (((0-u)+u)+v)=(0+v)
            let zc = el.app("of-addcom", &[("u", z()), ("v", v())], &[]).unwrap(); // (0+v)=(v+0)
            let z0 = el.app("of-add0", &[("u", v())], &[]).unwrap(); // (v+0)=v
            let p_z = eqtr(plu(z(), v()), plu(v(), z()), v(), zc, z0); // (0+v)=v
            let s1 = eqcomm(el, plu(nn(u()), z()), nn(u()), pa); // (0-u)=((0-u)+0)
            let s2 = eqcomm(el, plu(nn(u()), plu(u(), v())), plu(nn(u()), z()), hc); // ((0-u)+0)=((0-u)+(u+v))
            let s3 = eqcomm(
                el,
                plu(plu(nn(u()), u()), v()),
                plu(nn(u()), plu(u(), v())),
                assoc,
            ); // ((0-u)+(u+v))=(((0-u)+u)+v)
            let e1 = eqtr(nn(u()), plu(nn(u()), z()), plu(nn(u()), plu(u(), v())), s1, s2);
            let e2 = eqtr(
                nn(u()),
                plu(nn(u()), plu(u(), v())),
                plu(plu(nn(u()), u()), v()),
                e1,
                s3,
            );
            let e3 = eqtr(nn(u()), plu(plu(nn(u()), u()), v()), plu(z(), v()), e2, cong1);
            let e4 = eqtr(nn(u()), plu(z(), v()), v(), e3, p_z); // (0-u)=v
            let g = eqcomm(el, nn(u()), v(), e4); // v=(0-u)
            Lemma {
                name: "neginv".into(),
                ess: vec![(
                    "neginv.1".into(),
                    toks(&["|-", "(", "u", "+", "v", ")", "=", "0"]),
                )],
                goal: g,
            }
        }
        // ---- 19: negneg  |- ( 0 -x ( 0 -x u ) ) = u -----------------
        19 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let nn = |x: Pt| neg(el, x);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let comm = el.app("of-addcom", &[("u", nn(u())), ("v", u())], &[]).unwrap();
            let inv = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let p_iu = eqtr(pl(el, nn(u()), u()), pl(el, u(), nn(u())), z(), comm, inv);
            let ni = ninv(el, nn(u()), u(), p_iu); // u = ( 0 -x (0-u) )
            let g = eqcomm(el, u(), nn(nn(u())), ni);
            Lemma { name: "negneg".into(), ess: vec![], goal: g }
        }
        // ---- 20: negadd  |- ( 0 -x (u+v) ) = ( (0-u) + (0-v) ) ------
        20 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let nn = |x: Pt| neg(el, x);
            let plu = |x: Pt, y: Pt| pl(el, x, y);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let na = || nn(u());
            let nb = || nn(v());
            let s1 = el
                .app("of-addass", &[("u", u()), ("v", v()), ("w", plu(na(), nb()))], &[])
                .unwrap();
            let i1 = el
                .app("of-addass", &[("u", v()), ("v", na()), ("w", nb())], &[])
                .unwrap();
            let i1r = eqcomm(el, plu(plu(v(), na()), nb()), plu(v(), plu(na(), nb())), i1);
            let bcomm = el.app("of-addcom", &[("u", v()), ("v", na())], &[]).unwrap();
            let i2 = cpl1(el, plu(v(), na()), plu(na(), v()), nb(), bcomm);
            let i3 = el
                .app("of-addass", &[("u", na()), ("v", v()), ("w", nb())], &[])
                .unwrap();
            let inv_b = el.app("of-addinv", &[("u", v())], &[]).unwrap();
            let i4 = cpl2(el, plu(v(), nb()), z(), na(), inv_b);
            let i5 = el.app("of-add0", &[("u", na())], &[]).unwrap();
            let x1 = eqtr(
                plu(v(), plu(na(), nb())),
                plu(plu(v(), na()), nb()),
                plu(plu(na(), v()), nb()),
                i1r,
                i2,
            );
            let x2 = eqtr(
                plu(v(), plu(na(), nb())),
                plu(plu(na(), v()), nb()),
                plu(na(), plu(v(), nb())),
                x1,
                i3,
            );
            let x3 = eqtr(
                plu(v(), plu(na(), nb())),
                plu(na(), plu(v(), nb())),
                plu(na(), z()),
                x2,
                i4,
            );
            let xeq = eqtr(
                plu(v(), plu(na(), nb())),
                plu(na(), z()),
                na(),
                x3,
                i5,
            ); // (B+(nA+nB)) = nA
            let axe = cpl2(el, plu(v(), plu(na(), nb())), na(), u(), xeq);
            let inv_a = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let r = eqtr(
                plu(u(), plu(v(), plu(na(), nb()))),
                plu(u(), na()),
                z(),
                axe,
                inv_a,
            );
            let ee = eqtr(
                plu(plu(u(), v()), plu(na(), nb())),
                plu(u(), plu(v(), plu(na(), nb()))),
                z(),
                s1,
                r,
            );
            let ni = ninv(el, plu(u(), v()), plu(na(), nb()), ee); // (nA+nB) = (0 -x (u+v))
            let g = eqcomm(el, plu(na(), nb()), nn(plu(u(), v())), ni);
            Lemma { name: "negadd".into(), ess: vec![], goal: g }
        }
        // ---- 21: mulneg1  |- ( (0-u) * v ) = ( 0 -x ( u * v ) ) -----
        21 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let nn = |x: Pt| neg(el, x);
            let plu = |x: Pt, y: Pt| pl(el, x, y);
            let muu = |x: Pt, y: Pt| mu(el, x, y);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let rd = rdist(el, u(), nn(u()), v()); // ((u+(0-u))*v)=((u*v)+((0-u)*v))
            let r0 = eqcomm(
                el,
                muu(plu(u(), nn(u())), v()),
                plu(muu(u(), v()), muu(nn(u()), v())),
                rd,
            );
            let inv = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let c = cmu1(el, plu(u(), nn(u())), z(), v(), inv); // ((u+(0-u))*v)=(0*v)
            let m0 = el.app("mul0", &[("u", v())], &[]).unwrap(); // (0*v)=0
            let h1 = eqtr(
                plu(muu(u(), v()), muu(nn(u()), v())),
                muu(plu(u(), nn(u())), v()),
                muu(z(), v()),
                r0,
                c,
            );
            let hyp = eqtr(
                plu(muu(u(), v()), muu(nn(u()), v())),
                muu(z(), v()),
                z(),
                h1,
                m0,
            );
            let g = ninv(el, muu(u(), v()), muu(nn(u()), v()), hyp);
            Lemma { name: "mulneg1".into(), ess: vec![], goal: g }
        }
        // ---- 22: mulneg2  |- ( u * (0-v) ) = ( 0 -x ( u * v ) ) -----
        22 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let nn = |x: Pt| neg(el, x);
            let muu = |x: Pt, y: Pt| mu(el, x, y);
            let eqtr = |x: Pt, y: Pt, zz: Pt, p1: Pt, p2: Pt| {
                el.app("eqtr", &[("x", x), ("y", y), ("z", zz)], &[p1, p2]).unwrap()
            };
            let c1 = el.app("of-mulcom", &[("u", u()), ("v", nn(v()))], &[]).unwrap();
            let mn1 = el.app("mulneg1", &[("u", v()), ("v", u())], &[]).unwrap();
            let mc = el.app("of-mulcom", &[("u", v()), ("v", u())], &[]).unwrap();
            let cm = cmi2(el, muu(v(), u()), muu(u(), v()), t0p(el), mc);
            let h1 = eqtr(muu(u(), nn(v())), muu(nn(v()), u()), nn(muu(v(), u())), c1, mn1);
            let g = eqtr(muu(u(), nn(v())), nn(muu(v(), u())), nn(muu(u(), v())), h1, cm);
            Lemma { name: "mulneg2".into(), ess: vec![], goal: g }
        }
        // ---- 23: loclink — the law of cosines as a reusable lemma ----
        //  |- ( sqd b c ) = ( ( ( sqd a b ) + ( sqd a c ) )
        //                      -x ( ( dot a b c ) + ( dot a b c ) ) )
        //  Stated over the sqd/dot symbols (df-unfold -> ring_eq on the
        //  coordinate polynomials -> df-fold).  G4 SAS calls this twice
        //  (once per triangle).  No geometric axioms are used.
        23 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let pc = || leaf("vc");
            let xc = |t: Pt| el.app("txc", &[("a", t)], &[]).unwrap();
            let yc = |t: Pt| el.app("tyc", &[("a", t)], &[]).unwrap();
            let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
            let dot = |o: Pt, p: Pt, q: Pt| {
                el.app("tdot", &[("o", o), ("p", p), ("q", q)], &[]).unwrap()
            };
            let mi_ = |x: Pt, y: Pt| mi(el, x, y);
            let muu = |x: Pt, y: Pt| mu(el, x, y);
            let plu = |x: Pt, y: Pt| pl(el, x, y);
            // coordinate expansions matching df-sqd / df-dot exactly
            let sqc = |p: Pt, q: Pt| {
                plu(
                    muu(mi_(xc(q.clone()), xc(p.clone())), mi_(xc(q.clone()), xc(p.clone()))),
                    muu(mi_(yc(q.clone()), yc(p.clone())), mi_(yc(q.clone()), yc(p.clone()))),
                )
            };
            let dtc = |o: Pt, p: Pt, q: Pt| {
                plu(
                    muu(mi_(xc(p.clone()), xc(o.clone())), mi_(xc(q.clone()), xc(o.clone()))),
                    muu(mi_(yc(p.clone()), yc(o.clone())), mi_(yc(q.clone()), yc(o.clone()))),
                )
            };
            let s_bc = sqc(pb(), pc());
            let s_ab = sqc(pa(), pb());
            let s_ac = sqc(pa(), pc());
            let d_abc = dtc(pa(), pb(), pc());
            let rhs_u = mi_(plu(s_ab.clone(), s_ac.clone()), plu(d_abc.clone(), d_abc.clone()));
            // core ring identity (this is the law of cosines)
            let core = ring_eq(el, &s_bc, &rhs_u);
            // df handles
            let dlhs = el.app("df-sqd", &[("a", pb()), ("b", pc())], &[]).unwrap(); // (sqd b c)=s_bc
            let f_ab = eqcomm(el, sqd(pa(), pb()), s_ab.clone(),
                el.app("df-sqd", &[("a", pa()), ("b", pb())], &[]).unwrap()); // s_ab=(sqd a b)
            let f_ac = eqcomm(el, sqd(pa(), pc()), s_ac.clone(),
                el.app("df-sqd", &[("a", pa()), ("b", pc())], &[]).unwrap()); // s_ac=(sqd a c)
            let f_d = eqcomm(el, dot(pa(), pb(), pc()), d_abc.clone(),
                el.app("df-dot", &[("o", pa()), ("p", pb()), ("q", pc())], &[]).unwrap()); // d_abc=(dot a b c)
            // rebuild rhs from rhs_u by folding df back
            let qab = sqd(pa(), pb());
            let qac = sqd(pa(), pc());
            let dab = dot(pa(), pb(), pc());
            let s1 = cpl1(el, s_ab.clone(), qab.clone(), s_ac.clone(), f_ab);
            let s2 = cpl2(el, s_ac.clone(), qac.clone(), qab.clone(), f_ac);
            let sumeq = eqtr3(
                el,
                plu(s_ab.clone(), s_ac.clone()),
                plu(qab.clone(), s_ac.clone()),
                plu(qab.clone(), qac.clone()),
                s1,
                s2,
            );
            let d1 = cpl1(el, d_abc.clone(), dab.clone(), d_abc.clone(), f_d.clone());
            let d2 = cpl2(el, d_abc.clone(), dab.clone(), dab.clone(), f_d);
            let doteq = eqtr3(
                el,
                plu(d_abc.clone(), d_abc.clone()),
                plu(dab.clone(), d_abc.clone()),
                plu(dab.clone(), dab.clone()),
                d1,
                d2,
            );
            let m1 = cmi1(el, plu(s_ab.clone(), s_ac.clone()), plu(qab.clone(), qac.clone()),
                plu(d_abc.clone(), d_abc.clone()), sumeq);
            let m2 = cmi2(el, plu(d_abc.clone(), d_abc.clone()), plu(dab.clone(), dab.clone()),
                plu(qab.clone(), qac.clone()), doteq);
            let fold_r = eqtr3(
                el,
                rhs_u.clone(),
                mi_(plu(qab.clone(), qac.clone()), plu(d_abc.clone(), d_abc.clone())),
                mi_(plu(qab.clone(), qac.clone()), plu(dab.clone(), dab.clone())),
                m1,
                m2,
            );
            let c1 = eqtr3(el, sqd(pb(), pc()), s_bc.clone(), rhs_u.clone(), dlhs, core);
            let g = eqtr3(
                el,
                sqd(pb(), pc()),
                rhs_u,
                mi_(plu(qab, qac), plu(dab.clone(), dab)),
                c1,
                fold_r,
            );
            Lemma { name: "loclink".into(), ess: vec![], goal: g }
        }
        // ---- 24: mpd  (ph->ps),(ph->(ps->ch)) => (ph->ch) -----------
        24 => {
            let a2 = ax2(php(), pps(), pch());
            let m1 = mp(
                i(php(), i(pps(), pch())),
                i(i(php(), pps()), i(php(), pch())),
                leaf("mpd.2"),
                a2,
            );
            let g = mp(i(php(), pps()), i(php(), pch()), leaf("mpd.1"), m1);
            Lemma {
                name: "mpd".into(),
                ess: vec![
                    ("mpd.1".into(), toks(&["|-", "(", "ph", "->", "ps", ")"])),
                    (
                        "mpd.2".into(),
                        toks(&["|-", "(", "ph", "->", "(", "ps", "->", "ch", ")", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 25: syld (ph->(ps->ch)),(ph->(ch->th)) =>(ph->(ps->th)) -
        25 => {
            let pth = || leaf("wth");
            let h2p = syl(
                php(),
                i(pch(), pth()),
                i(pps(), i(pch(), pth())),
                leaf("syld.2"),
                ax1(i(pch(), pth()), pps()),
            );
            let a2 = ax2(pps(), pch(), pth());
            let t = syl(
                php(),
                i(pps(), i(pch(), pth())),
                i(i(pps(), pch()), i(pps(), pth())),
                h2p,
                a2,
            );
            let g = el
                .app(
                    "mpd",
                    &[("ph", php()), ("ps", i(pps(), pch())), ("ch", i(pps(), pth()))],
                    &[leaf("syld.1"), t],
                )
                .unwrap();
            Lemma {
                name: "syld".into(),
                ess: vec![
                    (
                        "syld.1".into(),
                        toks(&["|-", "(", "ph", "->", "(", "ps", "->", "ch", ")", ")"]),
                    ),
                    (
                        "syld.2".into(),
                        toks(&["|-", "(", "ph", "->", "(", "ch", "->", "th", ")", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 26: com12  (ph->(ps->ch)) => (ps->(ph->ch)) ------------
        26 => {
            let m1 = mp(
                i(php(), i(pps(), pch())),
                i(i(php(), pps()), i(php(), pch())),
                leaf("com12.1"),
                ax2(php(), pps(), pch()),
            );
            let g = syl(pps(), i(php(), pps()), i(php(), pch()), ax1(pps(), php()), m1);
            Lemma {
                name: "com12".into(),
                ess: vec![(
                    "com12.1".into(),
                    toks(&["|-", "(", "ph", "->", "(", "ps", "->", "ch", ")", ")"]),
                )],
                goal: g,
            }
        }
        // ---- 27: con3i  (ph->ps) => ( -.ps -> -.ph ) ----------------
        27 => {
            let t1 = el.app("notnot2", &[("ph", php())], &[]).unwrap();
            let sa = syl(n(n(php())), php(), pps(), t1, leaf("con3i.1"));
            let t2 = el.app("notnot1", &[("ph", pps())], &[]).unwrap();
            let sb = syl(n(n(php())), pps(), n(n(pps())), sa, t2);
            let a3 = ax3(n(php()), n(pps()));
            let g = mp(
                i(n(n(php())), n(n(pps()))),
                i(n(pps()), n(php())),
                sb,
                a3,
            );
            Lemma {
                name: "con3i".into(),
                ess: vec![(
                    "con3i.1".into(),
                    toks(&["|-", "(", "ph", "->", "ps", ")"]),
                )],
                goal: g,
            }
        }
        // ---- 28: con3  |- ( ( ph -> ps ) -> ( -.ps -> -.ph ) ) ------
        28 => {
            let hh = i(php(), pps());
            let nn2 = el.app("notnot2", &[("ph", php())], &[]).unwrap();
            let a_a = el
                .app("a1i", &[("ph", i(n(n(php())), php())), ("ps", hh.clone())], &[nn2])
                .unwrap();
            let b_b = el.app("id", &[("ph", hh.clone())], &[]).unwrap();
            let ab = el
                .app(
                    "syld",
                    &[
                        ("ph", hh.clone()),
                        ("ps", n(n(php()))),
                        ("ch", php()),
                        ("th", pps()),
                    ],
                    &[a_a, b_b],
                )
                .unwrap();
            let nn1 = el.app("notnot1", &[("ph", pps())], &[]).unwrap();
            let c_c = el
                .app("a1i", &[("ph", i(pps(), n(n(pps())))), ("ps", hh.clone())], &[nn1])
                .unwrap();
            let d_d = el
                .app(
                    "syld",
                    &[
                        ("ph", hh.clone()),
                        ("ps", n(n(php()))),
                        ("ch", pps()),
                        ("th", n(n(pps()))),
                    ],
                    &[ab, c_c],
                )
                .unwrap();
            let a3 = ax3(n(php()), n(pps()));
            let a3i = el
                .app(
                    "a1i",
                    &[
                        (
                            "ph",
                            i(i(n(n(php())), n(n(pps()))), i(n(pps()), n(php()))),
                        ),
                        ("ps", hh.clone()),
                    ],
                    &[a3],
                )
                .unwrap();
            let g = el
                .app(
                    "mpd",
                    &[
                        ("ph", hh.clone()),
                        ("ps", i(n(n(php())), n(n(pps())))),
                        ("ch", i(n(pps()), n(php()))),
                    ],
                    &[d_d, a3i],
                )
                .unwrap();
            Lemma { name: "con3".into(), ess: vec![], goal: g }
        }
        // ---- 29: pm2.18  |- ( ( -.ph -> ph ) -> ph ) ----------------
        29 => {
            let hh = i(n(php()), php());
            let p1 = el
                .app("pm2.21", &[("ph", php()), ("ps", n(hh.clone()))], &[])
                .unwrap();
            let a_a = el.app("id", &[("ph", hh.clone())], &[]).unwrap();
            let b_b = el
                .app(
                    "a1i",
                    &[
                        ("ph", i(n(php()), i(php(), n(hh.clone())))),
                        ("ps", hh.clone()),
                    ],
                    &[p1],
                )
                .unwrap();
            let a2 = ax2(n(php()), php(), n(hh.clone()));
            let a2h = el
                .app(
                    "a1i",
                    &[
                        (
                            "ph",
                            i(
                                i(n(php()), i(php(), n(hh.clone()))),
                                i(i(n(php()), php()), i(n(php()), n(hh.clone()))),
                            ),
                        ),
                        ("ps", hh.clone()),
                    ],
                    &[a2],
                )
                .unwrap();
            let mm = el
                .app(
                    "mpd",
                    &[
                        ("ph", hh.clone()),
                        ("ps", i(n(php()), i(php(), n(hh.clone())))),
                        (
                            "ch",
                            i(i(n(php()), php()), i(n(php()), n(hh.clone()))),
                        ),
                    ],
                    &[b_b, a2h],
                )
                .unwrap();
            let s1 = el
                .app(
                    "mpd",
                    &[
                        ("ph", hh.clone()),
                        ("ps", i(n(php()), php())),
                        ("ch", i(n(php()), n(hh.clone()))),
                    ],
                    &[a_a, mm],
                )
                .unwrap();
            let a3 = ax3(php(), hh.clone());
            let s2 = syl(
                hh.clone(),
                i(n(php()), n(hh.clone())),
                i(hh.clone(), php()),
                s1,
                a3,
            );
            let w = el
                .app("pm2.43", &[("ph", hh.clone()), ("ps", php())], &[])
                .unwrap();
            let g = mp(i(hh.clone(), i(hh.clone(), php())), i(hh.clone(), php()), s2, w);
            Lemma { name: "pm2.18".into(), ess: vec![], goal: g }
        }
        // ---- 30: jca  (ph->ps),(ph->ch) => ( ph -> ( ps /\ ch ) ) ---
        30 => {
            let k = i(pps(), n(pch()));
            let dfan = el.app("df-an", &[("ph", pps()), ("ps", pch())], &[]).unwrap();
            let bi2 = el
                .app(
                    "ax-bi2",
                    &[("ph", a(pps(), pch())), ("ps", n(k.clone()))],
                    &[],
                )
                .unwrap();
            let n_n = mp(
                b(a(pps(), pch()), n(k.clone())),
                i(n(k.clone()), a(pps(), pch())),
                dfan,
                bi2,
            );
            let p1 = syl(
                php(),
                pps(),
                i(k.clone(), pps()),
                leaf("jca.1"),
                ax1(pps(), k.clone()),
            );
            let idk = el.app("id", &[("ph", k.clone())], &[]).unwrap();
            let p3 = el
                .app("a1i", &[("ph", i(k.clone(), k.clone())), ("ps", php())], &[idk])
                .unwrap();
            let a2inner = ax2(k.clone(), pps(), n(pch()));
            let p4 = syl(
                php(),
                i(k.clone(), i(pps(), n(pch()))),
                i(i(k.clone(), pps()), i(k.clone(), n(pch()))),
                p3,
                a2inner,
            );
            let p2 = el
                .app(
                    "mpd",
                    &[
                        ("ph", php()),
                        ("ps", i(k.clone(), pps())),
                        ("ch", i(k.clone(), n(pch()))),
                    ],
                    &[p1, p4],
                )
                .unwrap();
            let con3kc = el
                .app("con3", &[("ph", k.clone()), ("ps", n(pch()))], &[])
                .unwrap();
            let nn1c = el.app("notnot1", &[("ph", pch())], &[]).unwrap();
            let x_k = i(k.clone(), n(pch()));
            let nn1c_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(pch(), n(n(pch())))), ("ps", x_k.clone())],
                    &[nn1c],
                )
                .unwrap();
            let ct = el
                .app(
                    "syld",
                    &[
                        ("ph", x_k.clone()),
                        ("ps", pch()),
                        ("ch", n(n(pch()))),
                        ("th", n(k.clone())),
                    ],
                    &[nn1c_a1, con3kc],
                )
                .unwrap();
            let pc = syl(
                php(),
                x_k.clone(),
                i(pch(), n(k.clone())),
                p2,
                ct,
            );
            let pnk = el
                .app(
                    "mpd",
                    &[("ph", php()), ("ps", pch()), ("ch", n(k.clone()))],
                    &[leaf("jca.2"), pc],
                )
                .unwrap();
            let g = syl(php(), n(k.clone()), a(pps(), pch()), pnk, n_n);
            Lemma {
                name: "jca".into(),
                ess: vec![
                    ("jca.1".into(), toks(&["|-", "(", "ph", "->", "ps", ")"])),
                    ("jca.2".into(), toks(&["|-", "(", "ph", "->", "ch", ")"])),
                ],
                goal: g,
            }
        }
        // ---- 31: orri  |- ( ph -> ( ph \/ ps ) ) -------------------
        31 => {
            let owo = el.app("wo", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let dfor = el.app("df-or", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi2 = el
                .app(
                    "ax-bi2",
                    &[("ph", owo.clone()), ("ps", i(n(php()), pps()))],
                    &[],
                )
                .unwrap();
            let ordbwd = mp(
                b(owo.clone(), i(n(php()), pps())),
                i(i(n(php()), pps()), owo.clone()),
                dfor,
                bi2,
            );
            let p221 = el
                .app("pm2.21", &[("ph", php()), ("ps", pps())], &[])
                .unwrap();
            let c = el
                .app(
                    "com12",
                    &[("ph", n(php())), ("ps", php()), ("ch", pps())],
                    &[p221],
                )
                .unwrap();
            let g = syl(php(), i(n(php()), pps()), owo.clone(), c, ordbwd);
            Lemma { name: "orri".into(), ess: vec![], goal: g }
        }
        // ---- 32: orli  |- ( ps -> ( ph \/ ps ) ) -------------------
        32 => {
            let owo = el.app("wo", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let dfor = el.app("df-or", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi2 = el
                .app(
                    "ax-bi2",
                    &[("ph", owo.clone()), ("ps", i(n(php()), pps()))],
                    &[],
                )
                .unwrap();
            let ordbwd = mp(
                b(owo.clone(), i(n(php()), pps())),
                i(i(n(php()), pps()), owo.clone()),
                dfor,
                bi2,
            );
            let a1 = ax1(pps(), n(php()));
            let g = syl(pps(), i(n(php()), pps()), owo.clone(), a1, ordbwd);
            Lemma { name: "orli".into(), ess: vec![], goal: g }
        }
        // ---- 33: jaoi  (ph->ch),(ps->ch) => ( (ph\/ps) -> ch ) ------
        33 => {
            let owo = el.app("wo", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let dfor = el.app("df-or", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi1 = el
                .app(
                    "ax-bi1",
                    &[("ph", owo.clone()), ("ps", i(n(php()), pps()))],
                    &[],
                )
                .unwrap();
            let ordfwd = mp(
                b(owo.clone(), i(n(php()), pps())),
                i(owo.clone(), i(n(php()), pps())),
                dfor,
                bi1,
            );
            let h2a1 = el
                .app(
                    "a1i",
                    &[("ph", i(pps(), pch())), ("ps", n(php()))],
                    &[leaf("jaoi.2")],
                )
                .unwrap();
            let a2 = ax2(n(php()), pps(), pch());
            let imim = mp(
                i(n(php()), i(pps(), pch())),
                i(i(n(php()), pps()), i(n(php()), pch())),
                h2a1,
                a2,
            );
            let step1 = syl(
                owo.clone(),
                i(n(php()), pps()),
                i(n(php()), pch()),
                ordfwd,
                imim,
            );
            let dh1 = el
                .app(
                    "a1i",
                    &[("ph", i(php(), pch())), ("ps", owo.clone())],
                    &[leaf("jaoi.1")],
                )
                .unwrap();
            let c3 = el
                .app("con3", &[("ph", n(php())), ("ps", pch())], &[])
                .unwrap();
            let s1 = syl(
                owo.clone(),
                i(n(php()), pch()),
                i(n(pch()), n(n(php()))),
                step1,
                c3,
            );
            let nn2 = el.app("notnot2", &[("ph", php())], &[]).unwrap();
            let nn2a = el
                .app(
                    "a1i",
                    &[("ph", i(n(n(php())), php())), ("ps", owo.clone())],
                    &[nn2],
                )
                .unwrap();
            let s2 = el
                .app(
                    "syld",
                    &[
                        ("ph", owo.clone()),
                        ("ps", n(pch())),
                        ("ch", n(n(php()))),
                        ("th", php()),
                    ],
                    &[s1, nn2a],
                )
                .unwrap();
            let s3 = el
                .app(
                    "syld",
                    &[
                        ("ph", owo.clone()),
                        ("ps", n(pch())),
                        ("ch", php()),
                        ("th", pch()),
                    ],
                    &[s2, dh1],
                )
                .unwrap();
            let p218 = el.app("pm2.18", &[("ph", pch())], &[]).unwrap();
            let g = syl(owo.clone(), i(n(pch()), pch()), pch(), s3, p218);
            Lemma {
                name: "jaoi".into(),
                ess: vec![
                    ("jaoi.1".into(), toks(&["|-", "(", "ph", "->", "ch", ")"])),
                    ("jaoi.2".into(), toks(&["|-", "(", "ps", "->", "ch", ")"])),
                ],
                goal: g,
            }
        }
        // ---- 34: subid  |- ( u -x u ) = 0 ---------------------------
        34 => {
            let u = || leaf("vu");
            let dfs = el.app("df-sub", &[("u", u()), ("v", u())], &[]).unwrap();
            let inv = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let g = eqtr3(
                el,
                mi(el, u(), u()),
                pl(el, u(), neg(el, u())),
                t0p(el),
                dfs,
                inv,
            );
            Lemma { name: "subid".into(), ess: vec![], goal: g }
        }
        // ---- 35: sub0r  |- ( u -x 0 ) = u ---------------------------
        35 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let dfs = el.app("df-sub", &[("u", u()), ("v", z())], &[]).unwrap();
            let sub00 = el.app("subid", &[("u", z())], &[]).unwrap();
            let c = cpl2(el, neg(el, z()), z(), u(), sub00);
            let a0 = el.app("of-add0", &[("u", u())], &[]).unwrap();
            let e1 = eqtr3(el, pl(el, u(), neg(el, z())), pl(el, u(), z()), u(), c, a0);
            let g = eqtr3(el, mi(el, u(), z()), pl(el, u(), neg(el, z())), u(), dfs, e1);
            Lemma { name: "sub0r".into(), ess: vec![], goal: g }
        }
        // ---- 36: le2sub  |- ( ( u <_ v ) -> ( 0 <_ ( v -x u ) ) ) ---
        36 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let nu = || neg(el, u());
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let leadd = el
                .app("of-leadd", &[("u", u()), ("v", v()), ("w", nu())], &[])
                .unwrap();
            let inv = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let cl1 = el
                .app(
                    "cong-le1",
                    &[
                        ("a", pl(el, u(), nu())),
                        ("b", z()),
                        ("c", pl(el, v(), nu())),
                    ],
                    &[],
                )
                .unwrap();
            let c1 = mp(
                eq(pl(el, u(), nu()), z()),
                i(
                    le(pl(el, u(), nu()), pl(el, v(), nu())),
                    le(z(), pl(el, v(), nu())),
                ),
                inv,
                cl1,
            );
            let dfs = el.app("df-sub", &[("u", v()), ("v", u())], &[]).unwrap();
            let dfsr = eqcomm(el, mi(el, v(), u()), pl(el, v(), nu()), dfs);
            let cl2 = el
                .app(
                    "cong-le2",
                    &[
                        ("a", pl(el, v(), nu())),
                        ("b", mi(el, v(), u())),
                        ("c", z()),
                    ],
                    &[],
                )
                .unwrap();
            let c2 = mp(
                eq(pl(el, v(), nu()), mi(el, v(), u())),
                i(
                    le(z(), pl(el, v(), nu())),
                    le(z(), mi(el, v(), u())),
                ),
                dfsr,
                cl2,
            );
            let s_a = syl(
                le(u(), v()),
                le(pl(el, u(), nu()), pl(el, v(), nu())),
                le(z(), pl(el, v(), nu())),
                leadd,
                c1,
            );
            let g = syl(
                le(u(), v()),
                le(z(), pl(el, v(), nu())),
                le(z(), mi(el, v(), u())),
                s_a,
                c2,
            );
            Lemma { name: "le2sub".into(), ess: vec![], goal: g }
        }
        // ---- 37: sub2le  |- ( ( 0 <_ ( v -x u ) ) -> ( u <_ v ) ) ---
        37 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let nu = || neg(el, u());
            let vmu = || mi(el, v(), u());
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let leadd = el
                .app("of-leadd", &[("u", z()), ("v", vmu()), ("w", u())], &[])
                .unwrap();
            let zc = el.app("of-addcom", &[("u", z()), ("v", u())], &[]).unwrap();
            let z0 = el.app("of-add0", &[("u", u())], &[]).unwrap();
            let lhs_eq = eqtr3(el, pl(el, z(), u()), pl(el, u(), z()), u(), zc, z0);
            let dfs = el.app("df-sub", &[("u", v()), ("v", u())], &[]).unwrap();
            let c_dfs = cpl1(el, vmu(), pl(el, v(), nu()), u(), dfs);
            let assoc = el
                .app("of-addass", &[("u", v()), ("v", nu()), ("w", u())], &[])
                .unwrap();
            let icom = el.app("of-addcom", &[("u", nu()), ("v", u())], &[]).unwrap();
            let iinv = el.app("of-addinv", &[("u", u())], &[]).unwrap();
            let ip = eqtr3(el, pl(el, nu(), u()), pl(el, u(), nu()), z(), icom, iinv);
            let cinv = cpl2(el, pl(el, nu(), u()), z(), v(), ip);
            let v0 = el.app("of-add0", &[("u", v())], &[]).unwrap();
            let r1 = eqtr3(
                el,
                pl(el, v(), pl(el, nu(), u())),
                pl(el, v(), z()),
                v(),
                cinv,
                v0,
            );
            let r2 = eqtr3(
                el,
                pl(el, pl(el, v(), nu()), u()),
                pl(el, v(), pl(el, nu(), u())),
                v(),
                assoc,
                r1,
            );
            let rhs_eq = eqtr3(
                el,
                pl(el, vmu(), u()),
                pl(el, pl(el, v(), nu()), u()),
                v(),
                c_dfs,
                r2,
            );
            let cl1 = el
                .app(
                    "cong-le1",
                    &[
                        ("a", pl(el, z(), u())),
                        ("b", u()),
                        ("c", pl(el, vmu(), u())),
                    ],
                    &[],
                )
                .unwrap();
            let c1 = mp(
                eq(pl(el, z(), u()), u()),
                i(
                    le(pl(el, z(), u()), pl(el, vmu(), u())),
                    le(u(), pl(el, vmu(), u())),
                ),
                lhs_eq,
                cl1,
            );
            let cl2 = el
                .app(
                    "cong-le2",
                    &[
                        ("a", pl(el, vmu(), u())),
                        ("b", v()),
                        ("c", u()),
                    ],
                    &[],
                )
                .unwrap();
            let c2 = mp(
                eq(pl(el, vmu(), u()), v()),
                i(le(u(), pl(el, vmu(), u())), le(u(), v())),
                rhs_eq,
                cl2,
            );
            let s_a = syl(
                le(z(), vmu()),
                le(pl(el, z(), u()), pl(el, vmu(), u())),
                le(u(), pl(el, vmu(), u())),
                leadd,
                c1,
            );
            let g = syl(
                le(z(), vmu()),
                le(u(), pl(el, vmu(), u())),
                le(u(), v()),
                s_a,
                c2,
            );
            Lemma { name: "sub2le".into(), ess: vec![], goal: g }
        }
        // ---- 38: lerefl  |- ( u <_ u ) ------------------------------
        38 => {
            let u = || leaf("vu");
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let tot = el
                .app("of-letot", &[("u", u()), ("v", u())], &[])
                .unwrap();
            let idle = el.app("id", &[("ph", le(u(), u()))], &[]).unwrap();
            let jao = el
                .app(
                    "jaoi",
                    &[
                        ("ph", le(u(), u())),
                        ("ps", le(u(), u())),
                        ("ch", le(u(), u())),
                    ],
                    &[idle.clone(), idle],
                )
                .unwrap();
            let owo = el
                .app("wo", &[("ph", le(u(), u())), ("ps", le(u(), u()))], &[])
                .unwrap();
            let g = mp(owo, le(u(), u()), tot, jao);
            Lemma { name: "lerefl".into(), ess: vec![], goal: g }
        }
        // ---- 39: pm3.2  |- ( ph -> ( ps -> ( ph /\ ps ) ) ) --------
        39 => {
            let k = i(php(), n(pps()));
            let dfan = el.app("df-an", &[("ph", php()), ("ps", pps())], &[]).unwrap();
            let bi2 = el
                .app(
                    "ax-bi2",
                    &[("ph", a(php(), pps())), ("ps", n(k.clone()))],
                    &[],
                )
                .unwrap();
            let bwd = mp(
                b(a(php(), pps()), n(k.clone())),
                i(n(k.clone()), a(php(), pps())),
                dfan,
                bi2,
            );
            let idk = el.app("id", &[("ph", k.clone())], &[]).unwrap();
            let d = el
                .app(
                    "com12",
                    &[("ph", k.clone()), ("ps", php()), ("ch", n(pps()))],
                    &[idk],
                )
                .unwrap();
            let con3kp = el
                .app("con3", &[("ph", k.clone()), ("ps", n(pps()))], &[])
                .unwrap();
            let nn1p = el.app("notnot1", &[("ph", pps())], &[]).unwrap();
            let xkp = i(k.clone(), n(pps()));
            let nn1p_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(pps(), n(n(pps())))), ("ps", xkp.clone())],
                    &[nn1p],
                )
                .unwrap();
            let ct = el
                .app(
                    "syld",
                    &[
                        ("ph", xkp.clone()),
                        ("ps", pps()),
                        ("ch", n(n(pps()))),
                        ("th", n(k.clone())),
                    ],
                    &[nn1p_a1, con3kp],
                )
                .unwrap();
            let m = syl(php(), xkp.clone(), i(pps(), n(k.clone())), d, ct);
            let bwd_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(n(k.clone()), a(php(), pps()))), ("ps", php())],
                    &[bwd],
                )
                .unwrap();
            let g = el
                .app(
                    "syld",
                    &[
                        ("ph", php()),
                        ("ps", pps()),
                        ("ch", n(k.clone())),
                        ("th", a(php(), pps())),
                    ],
                    &[m, bwd_a1],
                )
                .unwrap();
            Lemma { name: "pm3.2".into(), ess: vec![], goal: g }
        }
        // ---- 40: expi  ( (ph/\ps)->ch ) => ( ph -> ( ps -> ch ) ) --
        40 => {
            let p32 = el
                .app("pm3.2", &[("ph", php()), ("ps", pps())], &[])
                .unwrap();
            let h_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(a(php(), pps()), pch())), ("ps", php())],
                    &[leaf("expi.1")],
                )
                .unwrap();
            let g = el
                .app(
                    "syld",
                    &[
                        ("ph", php()),
                        ("ps", pps()),
                        ("ch", a(php(), pps())),
                        ("th", pch()),
                    ],
                    &[p32, h_a1],
                )
                .unwrap();
            Lemma {
                name: "expi".into(),
                ess: vec![(
                    "expi.1".into(),
                    toks(&["|-", "(", "(", "ph", "/\\", "ps", ")", "->", "ch", ")"]),
                )],
                goal: g,
            }
        }
        // ---- 41: ltle  |- ( ( u < v ) -> ( u <_ v ) ) -------------
        41 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let dflt = el.app("df-lt", &[("u", u()), ("v", v())], &[]).unwrap();
            let rhs = a(le(u(), v()), n(le(v(), u())));
            let bi1 = el
                .app("ax-bi1", &[("ph", lt(u(), v())), ("ps", rhs.clone())], &[])
                .unwrap();
            let e = mp(
                b(lt(u(), v()), rhs.clone()),
                i(lt(u(), v()), rhs.clone()),
                dflt,
                bi1,
            );
            let spl = el
                .app(
                    "simpl",
                    &[("ph", le(u(), v())), ("ps", n(le(v(), u())))],
                    &[],
                )
                .unwrap();
            let g = syl(lt(u(), v()), rhs.clone(), le(u(), v()), e, spl);
            Lemma { name: "ltle".into(), ess: vec![], goal: g }
        }
        // ---- 42: lt0ne  |- ( ( u < v ) -> -. ( u = v ) ) ----------
        42 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let lr = el.app("lerefl", &[("u", u())], &[]).unwrap();
            let cl1 = el
                .app(
                    "cong-le1",
                    &[("a", u()), ("b", v()), ("c", u())],
                    &[],
                )
                .unwrap();
            let lr_a1 = el
                .app(
                    "a1i",
                    &[("ph", le(u(), u())), ("ps", eq(u(), v()))],
                    &[lr],
                )
                .unwrap();
            let e_vu = el
                .app(
                    "mpd",
                    &[
                        ("ph", eq(u(), v())),
                        ("ps", le(u(), u())),
                        ("ch", le(v(), u())),
                    ],
                    &[lr_a1, cl1],
                )
                .unwrap();
            let dflt = el.app("df-lt", &[("u", u()), ("v", v())], &[]).unwrap();
            let rhs = a(le(u(), v()), n(le(v(), u())));
            let bi1 = el
                .app("ax-bi1", &[("ph", lt(u(), v())), ("ps", rhs.clone())], &[])
                .unwrap();
            let ee = mp(
                b(lt(u(), v()), rhs.clone()),
                i(lt(u(), v()), rhs.clone()),
                dflt,
                bi1,
            );
            let spr = el
                .app(
                    "simpr",
                    &[("ph", le(u(), v())), ("ps", n(le(v(), u())))],
                    &[],
                )
                .unwrap();
            let nvu = syl(lt(u(), v()), rhs.clone(), n(le(v(), u())), ee, spr);
            let c3 = el
                .app(
                    "con3i",
                    &[("ph", eq(u(), v())), ("ps", le(v(), u()))],
                    &[e_vu],
                )
                .unwrap();
            let g = syl(lt(u(), v()), n(le(v(), u())), n(eq(u(), v())), nvu, c3);
            Lemma { name: "lt0ne".into(), ess: vec![], goal: g }
        }
        // ---- 43: lein2  |- ( (u<_v) -> ( (v<_u) -> (u=v) ) ) -------
        43 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lein = el.app("of-lein", &[("u", u()), ("v", v())], &[]).unwrap();
            let g = el
                .app(
                    "expi",
                    &[
                        ("ph", le(u(), v())),
                        ("ps", le(v(), u())),
                        ("ch", eq(u(), v())),
                    ],
                    &[lein],
                )
                .unwrap();
            Lemma { name: "lein2".into(), ess: vec![], goal: g }
        }
        // ---- 44: ltII  |- ( (u<_v) -> ( -.(v<_u) -> (u<v) ) ) ------
        44 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let dflt = el.app("df-lt", &[("u", u()), ("v", v())], &[]).unwrap();
            let rhs = a(le(u(), v()), n(le(v(), u())));
            let bi2 = el
                .app("ax-bi2", &[("ph", lt(u(), v())), ("ps", rhs.clone())], &[])
                .unwrap();
            let back = mp(
                b(lt(u(), v()), rhs.clone()),
                i(rhs.clone(), lt(u(), v())),
                dflt,
                bi2,
            );
            let g = el
                .app(
                    "expi",
                    &[
                        ("ph", le(u(), v())),
                        ("ps", n(le(v(), u()))),
                        ("ch", lt(u(), v())),
                    ],
                    &[back],
                )
                .unwrap();
            Lemma { name: "ltII".into(), ess: vec![], goal: g }
        }
        // ---- 45: lemul2  |- ( (0<u) -> ( (0<v) -> (0<(u*v)) ) ) ----
        45 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let lemul = el.app("of-lemul", &[("u", u()), ("v", v())], &[]).unwrap();
            let g = el
                .app(
                    "expi",
                    &[
                        ("ph", lt(z(), u())),
                        ("ps", lt(z(), v())),
                        ("ch", lt(z(), mu(el, u(), v()))),
                    ],
                    &[lemul],
                )
                .unwrap();
            Lemma { name: "lemul2".into(), ess: vec![], goal: g }
        }
        // ---- 46: lemul02  |- ( (0<_u) -> ( (0<_v) -> (0<_(u*v)) ) ) -
        46 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lemul0 = el.app("of-lemul0", &[("u", u()), ("v", v())], &[]).unwrap();
            let g = el
                .app(
                    "expi",
                    &[
                        ("ph", le(z(), u())),
                        ("ps", le(z(), v())),
                        ("ch", le(z(), mu(el, u(), v()))),
                    ],
                    &[lemul0],
                )
                .unwrap();
            Lemma { name: "lemul02".into(), ess: vec![], goal: g }
        }
        // ---- 47: mt  (ph->ps),-.ps => -.ph -------------------------
        47 => {
            let c3 = el
                .app("con3i", &[("ph", php()), ("ps", pps())], &[leaf("mt.1")])
                .unwrap();
            let g = mp(n(pps()), n(php()), leaf("mt.2"), c3);
            Lemma {
                name: "mt".into(),
                ess: vec![
                    (
                        "mt.1".into(),
                        toks(&["|-", "(", "ph", "->", "ps", ")"]),
                    ),
                    ("mt.2".into(), toks(&["|-", "-.", "ps"])),
                ],
                goal: g,
            }
        }
        // ---- 48: lecon  |-(0<_u),|-(u<_0) => |-(u=0) ---------------
        48 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lein = el.app("of-lein", &[("u", z()), ("v", u())], &[]).unwrap();
            let cj = conj2(
                el,
                le(z(), u()),
                le(u(), z()),
                leaf("lecon.1"),
                leaf("lecon.2"),
            );
            let m = mp(
                a(le(z(), u()), le(u(), z())),
                eq(z(), u()),
                cj,
                lein,
            );
            let g = eqcomm(el, z(), u(), m);
            Lemma {
                name: "lecon".into(),
                ess: vec![
                    (
                        "lecon.1".into(),
                        toks(&["|-", "(", "0", "<_", "u", ")"]),
                    ),
                    (
                        "lecon.2".into(),
                        toks(&["|-", "(", "u", "<_", "0", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 49: subeq0  |- ( ( ( u -x v ) = 0 ) -> ( u = v ) ) ----
        49 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let dv = || mi(el, u(), v());
            let re = ring_eq(el, &pl(el, dv(), v()), &u());
            let re_c = eqcomm(el, pl(el, dv(), v()), u(), re);
            let z0 = ring_eq(el, &pl(el, z(), v()), &v());
            let h = eq(dv(), z());
            let cpl1ax = el
                .app(
                    "cong-pl1",
                    &[("a", dv()), ("b", z()), ("c", v())],
                    &[],
                )
                .unwrap();
            let a_re = el
                .app(
                    "a1i",
                    &[("ph", eq(u(), pl(el, dv(), v()))), ("ps", h.clone())],
                    &[re_c],
                )
                .unwrap();
            let a_z0 = el
                .app(
                    "a1i",
                    &[("ph", eq(pl(el, z(), v()), v())), ("ps", h.clone())],
                    &[z0],
                )
                .unwrap();
            let t1 = el
                .app(
                    "eqtrd",
                    &[
                        ("ph", h.clone()),
                        ("x", u()),
                        ("y", pl(el, dv(), v())),
                        ("z", pl(el, z(), v())),
                    ],
                    &[a_re, cpl1ax],
                )
                .unwrap();
            let g = el
                .app(
                    "eqtrd",
                    &[
                        ("ph", h.clone()),
                        ("x", u()),
                        ("y", pl(el, z(), v())),
                        ("z", v()),
                    ],
                    &[t1, a_z0],
                )
                .unwrap();
            Lemma { name: "subeq0".into(), ess: vec![], goal: g }
        }
        // ---- 50: sqzhalf  |- ( (0<_u) -> ( ((u*u)=0) -> (u=0) ) ) --
        50 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let uu = || mu(el, u(), u());
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let aa = || le(z(), u()); // A = ( 0 <_ u )
            let bb = || eq(uu(), z()); // B = ( ( u * u ) = 0 )
            // hpos : ( (0<u) -> (0<(u*u)) )  via lemul2 + contraction
            let lemul2 = el
                .app("lemul2", &[("u", u()), ("v", u())], &[])
                .unwrap(); // ( (0<u) -> ( (0<u) -> (0<(u*u)) ) )
            let w43 = el
                .app(
                    "pm2.43",
                    &[("ph", lt(z(), u())), ("ps", lt(z(), uu()))],
                    &[],
                )
                .unwrap();
            let hpos = mp(
                i(lt(z(), u()), i(lt(z(), u()), lt(z(), uu()))),
                i(lt(z(), u()), lt(z(), uu())),
                lemul2,
                w43,
            );
            // ltII(0,u) : ( (0<_u) -> ( -.(u<_0) -> (0<u) ) )
            let ltii = el
                .app("ltII", &[("u", z()), ("v", u())], &[])
                .unwrap();
            // hpne : ( (0<u) -> -.(0=(u*u)) )
            let lt0ne = el
                .app("lt0ne", &[("u", z()), ("v", uu())], &[])
                .unwrap(); // ( (0<(u*u)) -> -.(0=(u*u)) )
            let hpne = syl(lt(z(), u()), lt(z(), uu()), n(eq(z(), uu())), hpos, lt0ne);
            let hpne_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(lt(z(), u()), n(eq(z(), uu())))), ("ps", aa())],
                    &[hpne],
                )
                .unwrap(); // ( A -> ( (0<u) -> -.(0=(u*u)) ) )
            let s1 = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", n(le(u(), z()))),
                        ("ch", lt(z(), u())),
                        ("th", n(eq(z(), uu()))),
                    ],
                    &[ltii, hpne_a1],
                )
                .unwrap(); // ( A -> ( -.(u<_0) -> -.(0=(u*u)) ) )
            // con3 inner: ( -.(u<_0) -> -.(0=(u*u)) ) -> ( (0=(u*u)) -> -.-.(u<_0) )
            let con3a = el
                .app(
                    "con3",
                    &[("ph", n(le(u(), z()))), ("ps", n(eq(z(), uu())))],
                    &[],
                )
                .unwrap();
            let s2 = syl(
                aa(),
                i(n(le(u(), z())), n(eq(z(), uu()))),
                i(n(n(eq(z(), uu()))), n(n(le(u(), z())))),
                s1,
                con3a,
            ); // ( A -> ( -.-.(0=(u*u)) -> -.-.(u<_0) ) )
            // (u*u)=0 -> 0=(u*u) -> -.-.(0=(u*u))
            let ecom = el
                .app("eqcom", &[("x", uu()), ("y", z())], &[])
                .unwrap(); // ( (u*u)=0 -> 0=(u*u) )
            let ecom_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(bb(), eq(z(), uu()))), ("ps", aa())],
                    &[ecom],
                )
                .unwrap(); // ( A -> ( B -> (0=(u*u)) ) )
            let nn1 = el
                .app("notnot1", &[("ph", eq(z(), uu()))], &[])
                .unwrap(); // ( (0=(u*u)) -> -.-.(0=(u*u)) )
            let nn1_a1 = el
                .app(
                    "a1i",
                    &[
                        ("ph", i(eq(z(), uu()), n(n(eq(z(), uu()))))),
                        ("ps", aa()),
                    ],
                    &[nn1],
                )
                .unwrap(); // ( A -> ( (0=(u*u)) -> -.-.(0=(u*u)) ) )
            let s3 = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", bb()),
                        ("ch", eq(z(), uu())),
                        ("th", n(n(eq(z(), uu())))),
                    ],
                    &[ecom_a1, nn1_a1],
                )
                .unwrap(); // ( A -> ( B -> -.-.(0=(u*u)) ) )
            let s4 = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", bb()),
                        ("ch", n(n(eq(z(), uu())))),
                        ("th", n(n(le(u(), z())))),
                    ],
                    &[s3, s2],
                )
                .unwrap(); // ( A -> ( B -> -.-.(u<_0) ) )
            // -.-.(u<_0) -> (u<_0)
            let nn2 = el
                .app("notnot2", &[("ph", le(u(), z()))], &[])
                .unwrap();
            let nn2_a1 = el
                .app(
                    "a1i",
                    &[
                        ("ph", i(n(n(le(u(), z()))), le(u(), z()))),
                        ("ps", aa()),
                    ],
                    &[nn2],
                )
                .unwrap(); // ( A -> ( -.-.(u<_0) -> (u<_0) ) )
            let s5 = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", bb()),
                        ("ch", n(n(le(u(), z())))),
                        ("th", le(u(), z())),
                    ],
                    &[s4, nn2_a1],
                )
                .unwrap(); // ( A -> ( B -> (u<_0) ) )
            // lein2(0,u) : ( (0<_u) -> ( (u<_0) -> (0=u) ) )   (A is (0<_u))
            let lein2 = el
                .app("lein2", &[("u", z()), ("v", u())], &[])
                .unwrap();
            let s6 = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", bb()),
                        ("ch", le(u(), z())),
                        ("th", eq(z(), u())),
                    ],
                    &[s5, lein2],
                )
                .unwrap(); // ( A -> ( B -> (0=u) ) )
            let ecu = el
                .app("eqcom", &[("x", z()), ("y", u())], &[])
                .unwrap(); // ( (0=u) -> (u=0) )
            let ecu_a1 = el
                .app(
                    "a1i",
                    &[("ph", i(eq(z(), u()), eq(u(), z()))), ("ps", aa())],
                    &[ecu],
                )
                .unwrap();
            let g = el
                .app(
                    "syld",
                    &[
                        ("ph", aa()),
                        ("ps", bb()),
                        ("ch", eq(z(), u())),
                        ("th", eq(u(), z())),
                    ],
                    &[s6, ecu_a1],
                )
                .unwrap(); // ( A -> ( B -> (u=0) ) )
            Lemma { name: "sqzhalf".into(), ess: vec![], goal: g }
        }
        // ---- 51: sqz  |- (u*u)=0  =>  |- u=0 -----------------------
        51 => {
            let u = || leaf("vu");
            let z = || t0p(el);
            let uu = || mu(el, u(), u());
            let nu = || neg(el, u());
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let uu0 = || leaf("sqz.1");
            // branch B : ( (0<_u) -> (u=0) )
            let shB = el.app("sqzhalf", &[("u", u())], &[]).unwrap(); // ( (0<_u) -> ( ((u*u)=0) -> (u=0) ) )
            let uu0_a1B = el
                .app(
                    "a1i",
                    &[("ph", eq(uu(), z())), ("ps", le(z(), u()))],
                    &[uu0()],
                )
                .unwrap(); // ( (0<_u) -> ((u*u)=0) )
            let br_b = el
                .app(
                    "mpd",
                    &[
                        ("ph", le(z(), u())),
                        ("ps", eq(uu(), z())),
                        ("ch", eq(u(), z())),
                    ],
                    &[uu0_a1B, shB],
                )
                .unwrap(); // ( (0<_u) -> (u=0) )
            // branch A : ( (u<_0) -> (u=0) )  via sqzhalf on (0-xu)
            let l2s = el
                .app("le2sub", &[("u", u()), ("v", z())], &[])
                .unwrap(); // ( (u<_0) -> (0<_(0-xu)) )
            let ren = ring_eq(el, &mu(el, nu(), nu()), &uu());
            let nn0 = eqtr3(el, mu(el, nu(), nu()), uu(), z(), ren, uu0());
            // |- ( (0-xu)*(0-xu) = 0 )
            let shA = el.app("sqzhalf", &[("u", nu())], &[]).unwrap();
            // ( (0<_(0-xu)) -> ( ((0-xu)*(0-xu)=0) -> ((0-xu)=0) ) )
            let s_a = syl(
                le(u(), z()),
                le(z(), nu()),
                i(eq(mu(el, nu(), nu()), z()), eq(nu(), z())),
                l2s,
                shA,
            ); // ( (u<_0) -> ( ((0-xu)*(0-xu)=0) -> ((0-xu)=0) ) )
            let nn0_a1 = el
                .app(
                    "a1i",
                    &[("ph", eq(mu(el, nu(), nu()), z())), ("ps", le(u(), z()))],
                    &[nn0],
                )
                .unwrap();
            let s_b = el
                .app(
                    "mpd",
                    &[
                        ("ph", le(u(), z())),
                        ("ps", eq(mu(el, nu(), nu()), z())),
                        ("ch", eq(nu(), z())),
                    ],
                    &[nn0_a1, s_a],
                )
                .unwrap(); // ( (u<_0) -> ((0-xu)=0) )
            let se0 = el
                .app("subeq0", &[("u", z()), ("v", u())], &[])
                .unwrap(); // ( ((0-xu)=0) -> (0=u) )
            let s_c = syl(le(u(), z()), eq(nu(), z()), eq(z(), u()), s_b, se0);
            let ec = el
                .app("eqcom", &[("x", z()), ("y", u())], &[])
                .unwrap(); // ( (0=u) -> (u=0) )
            let br_a = syl(le(u(), z()), eq(z(), u()), eq(u(), z()), s_c, ec);
            // jaoi(br_a, br_b) on of-letot(u,0) : ( (u<_0) \/ (0<_u) ) -> (u=0)
            let jao = el
                .app(
                    "jaoi",
                    &[
                        ("ph", le(u(), z())),
                        ("ps", le(z(), u())),
                        ("ch", eq(u(), z())),
                    ],
                    &[br_a, br_b],
                )
                .unwrap();
            let owo = el
                .app("wo", &[("ph", le(u(), z())), ("ps", le(z(), u()))], &[])
                .unwrap();
            let tot = el
                .app("of-letot", &[("u", u()), ("v", z())], &[])
                .unwrap(); // ( (u<_0) \/ (0<_u) )
            let g = mp(owo, eq(u(), z()), tot, jao);
            Lemma {
                name: "sqz".into(),
                ess: vec![(
                    "sqz.1".into(),
                    toks(&["|-", "(", "u", "*", "u", ")", "=", "0"]),
                )],
                goal: g,
            }
        }
        // ---- 52: le0add  |-(0<_u),|-(0<_v) => |-(0<_(u+v)) --------
        52 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let leadd = el
                .app("of-leadd", &[("u", z()), ("v", v()), ("w", u())], &[])
                .unwrap(); // ( (0<_v) -> ( (0+u) <_ (v+u) ) )
            let s = mp(
                le(z(), v()),
                le(pl(el, z(), u()), pl(el, v(), u())),
                leaf("le0add.2"),
                leadd,
            );
            let zu = ring_eq(el, &pl(el, z(), u()), &u());
            let vu = ring_eq(el, &pl(el, v(), u()), &pl(el, u(), v()));
            let cl1 = el
                .app(
                    "cong-le1",
                    &[
                        ("a", pl(el, z(), u())),
                        ("b", u()),
                        ("c", pl(el, v(), u())),
                    ],
                    &[],
                )
                .unwrap();
            let imp1 = mp(
                eq(pl(el, z(), u()), u()),
                i(
                    le(pl(el, z(), u()), pl(el, v(), u())),
                    le(u(), pl(el, v(), u())),
                ),
                zu,
                cl1,
            );
            let s1 = mp(
                le(pl(el, z(), u()), pl(el, v(), u())),
                le(u(), pl(el, v(), u())),
                s,
                imp1,
            );
            let cl2 = el
                .app(
                    "cong-le2",
                    &[
                        ("a", pl(el, v(), u())),
                        ("b", pl(el, u(), v())),
                        ("c", u()),
                    ],
                    &[],
                )
                .unwrap();
            let imp2 = mp(
                eq(pl(el, v(), u()), pl(el, u(), v())),
                i(
                    le(u(), pl(el, v(), u())),
                    le(u(), pl(el, u(), v())),
                ),
                vu,
                cl2,
            );
            let s2 = mp(
                le(u(), pl(el, v(), u())),
                le(u(), pl(el, u(), v())),
                s1,
                imp2,
            );
            let letri = el
                .app(
                    "of-letri",
                    &[("u", z()), ("v", u()), ("w", pl(el, u(), v()))],
                    &[],
                )
                .unwrap(); // ( (0<_u) -> ( (u<_(u+v)) -> (0<_(u+v)) ) )
            let t = mp(
                le(z(), u()),
                i(le(u(), pl(el, u(), v())), le(z(), pl(el, u(), v()))),
                leaf("le0add.1"),
                letri,
            );
            let g = mp(
                le(u(), pl(el, u(), v())),
                le(z(), pl(el, u(), v())),
                s2,
                t,
            );
            Lemma {
                name: "le0add".into(),
                ess: vec![
                    (
                        "le0add.1".into(),
                        toks(&["|-", "(", "0", "<_", "u", ")"]),
                    ),
                    (
                        "le0add.2".into(),
                        toks(&["|-", "(", "0", "<_", "v", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 53: lemul0mono  |-(u<_v),|-(0<_w) => |-((u*w)<_(v*w)) -
        53 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let w = || leaf("vw");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let dv = || mi(el, v(), u());
            let l2s = el
                .app("le2sub", &[("u", u()), ("v", v())], &[])
                .unwrap(); // ( (u<_v) -> (0<_(v-xu)) )
            let p_vu = mp(le(u(), v()), le(z(), dv()), leaf("lemul0mono.1"), l2s);
            let lemul02 = el
                .app("lemul02", &[("u", dv()), ("v", w())], &[])
                .unwrap(); // ( (0<_(v-xu)) -> ( (0<_w) -> (0<_((v-xu)*w)) ) )
            let m1 = mp(
                le(z(), dv()),
                i(le(z(), w()), le(z(), mu(el, dv(), w()))),
                p_vu,
                lemul02,
            );
            let pm0 = mp(
                le(z(), w()),
                le(z(), mu(el, dv(), w())),
                leaf("lemul0mono.2"),
                m1,
            ); // |- ( 0 <_ ((v-xu)*w) )
            let re = ring_eq(
                el,
                &mu(el, dv(), w()),
                &mi(el, mu(el, v(), w()), mu(el, u(), w())),
            );
            let cl2 = el
                .app(
                    "cong-le2",
                    &[
                        ("a", mu(el, dv(), w())),
                        ("b", mi(el, mu(el, v(), w()), mu(el, u(), w()))),
                        ("c", z()),
                    ],
                    &[],
                )
                .unwrap();
            let step = mp(
                eq(mu(el, dv(), w()), mi(el, mu(el, v(), w()), mu(el, u(), w()))),
                i(
                    le(z(), mu(el, dv(), w())),
                    le(z(), mi(el, mu(el, v(), w()), mu(el, u(), w()))),
                ),
                re,
                cl2,
            );
            let p2 = mp(
                le(z(), mu(el, dv(), w())),
                le(z(), mi(el, mu(el, v(), w()), mu(el, u(), w()))),
                pm0,
                step,
            ); // |- ( 0 <_ ((v*w)-x(u*w)) )
            let s2l = el
                .app(
                    "sub2le",
                    &[("u", mu(el, u(), w())), ("v", mu(el, v(), w()))],
                    &[],
                )
                .unwrap(); // ( (0<_((v*w)-x(u*w))) -> ((u*w)<_(v*w)) )
            let g = mp(
                le(z(), mi(el, mu(el, v(), w()), mu(el, u(), w()))),
                le(mu(el, u(), w()), mu(el, v(), w())),
                p2,
                s2l,
            );
            Lemma {
                name: "lemul0mono".into(),
                ess: vec![
                    (
                        "lemul0mono.1".into(),
                        toks(&["|-", "(", "u", "<_", "v", ")"]),
                    ),
                    (
                        "lemul0mono.2".into(),
                        toks(&["|-", "(", "0", "<_", "w", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 54: sqcong  |-(u*u)=(v*v),|-(0<_(u*v)) => |- u=v ------
        54 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let d = || mi(el, u(), v()); // d = (u -x v)
            let s = || pl(el, u(), v()); // s = (u + v)
            let dd = || mu(el, d(), d());
            let ss = || mu(el, s(), s());
            let uv = || mu(el, u(), v());
            // dS0 : |- ( (d*s) = 0 )
            let rds = ring_eq(el, &mu(el, d(), s()), &mi(el, mu(el, u(), u()), mu(el, v(), v())));
            // (d*s) = (u*u)-x(v*v)
            let cm1 = el
                .app(
                    "cong-mi1",
                    &[
                        ("a", mu(el, u(), u())),
                        ("b", mu(el, v(), v())),
                        ("c", mu(el, v(), v())),
                    ],
                    &[],
                )
                .unwrap(); // ( (u*u)=(v*v) -> ( ((u*u)-x(v*v)) = ((v*v)-x(v*v)) ) )
            let e1 = mp(
                eq(mu(el, u(), u()), mu(el, v(), v())),
                eq(
                    mi(el, mu(el, u(), u()), mu(el, v(), v())),
                    mi(el, mu(el, v(), v()), mu(el, v(), v())),
                ),
                leaf("sqcong.1"),
                cm1,
            );
            let sub00 = ring_eq(el, &mi(el, mu(el, v(), v()), mu(el, v(), v())), &z());
            let e2 = eqtr3(
                el,
                mi(el, mu(el, u(), u()), mu(el, v(), v())),
                mi(el, mu(el, v(), v()), mu(el, v(), v())),
                z(),
                e1,
                sub00,
            ); // ( (u*u)-x(v*v) ) = 0
            let ds0 = eqtr3(
                el,
                mu(el, d(), s()),
                mi(el, mu(el, u(), u()), mu(el, v(), v())),
                z(),
                rds,
                e2,
            ); // |- ( (d*s) = 0 )
            // 4uv : the sum (((uv)+(uv))+((uv)+(uv)))
            let two = pl(el, uv(), uv());
            let four = pl(el, two.clone(), two.clone());
            let p1 = el
                .app(
                    "le0add",
                    &[("u", uv()), ("v", uv())],
                    &[leaf("sqcong.2"), leaf("sqcong.2")],
                )
                .unwrap(); // |- ( 0 <_ ((uv)+(uv)) )
            let p4 = el
                .app(
                    "le0add",
                    &[("u", two.clone()), ("v", two.clone())],
                    &[p1.clone(), p1],
                )
                .unwrap(); // |- ( 0 <_ (((uv)+(uv))+((uv)+(uv))) )
            // (s*s) -x (d*d) = 4uv  (ring)
            let r4 = ring_eq(el, &mi(el, ss(), dd()), &four);
            let r4c = eqcomm(el, mi(el, ss(), dd()), four.clone(), r4); // 4uv = (s*s)-x(d*d)
            let cl2a = el
                .app(
                    "cong-le2",
                    &[("a", four.clone()), ("b", mi(el, ss(), dd())), ("c", z())],
                    &[],
                )
                .unwrap();
            let imp = mp(
                eq(four.clone(), mi(el, ss(), dd())),
                i(le(z(), four.clone()), le(z(), mi(el, ss(), dd()))),
                r4c,
                cl2a,
            );
            let p_sd = mp(
                le(z(), four.clone()),
                le(z(), mi(el, ss(), dd())),
                p4,
                imp,
            ); // |- ( 0 <_ ((s*s)-x(d*d)) )
            let s2l = el
                .app("sub2le", &[("u", dd()), ("v", ss())], &[])
                .unwrap(); // ( (0<_((s*s)-x(d*d))) -> ((d*d)<_(s*s)) )
            let dd_le_ss = mp(
                le(z(), mi(el, ss(), dd())),
                le(dd(), ss()),
                p_sd,
                s2l,
            ); // |- ( (d*d) <_ (s*s) )
            // 0 <_ (d*d)  [sqpos]
            let sqpd = el.app("of-sqpos", &[("u", d())], &[]).unwrap(); // ( 0 <_ (d*d) )
            // lemul0mono : (d*d)<_(s*s), 0<_(d*d)  =>  ((d*d)*(d*d)) <_ ((s*s)*(d*d))
            let mono = el
                .app(
                    "lemul0mono",
                    &[("u", dd()), ("v", ss()), ("w", dd())],
                    &[dd_le_ss, sqpd.clone()],
                )
                .unwrap(); // |- ( ((d*d)*(d*d)) <_ ((s*s)*(d*d)) )
            // ((s*s)*(d*d)) = (d*s)*(d*s) = 0
            let rsd = ring_eq(el, &mu(el, ss(), dd()), &mu(el, mu(el, d(), s()), mu(el, d(), s())));
            let dsds0 = {
                let cm = el
                    .app(
                        "cong-mu1",
                        &[
                            ("a", mu(el, d(), s())),
                            ("b", z()),
                            ("c", mu(el, d(), s())),
                        ],
                        &[],
                    )
                    .unwrap(); // ( (d*s)=0 -> ( (d*s)*(d*s) = 0*(d*s) ) )
                let e = mp(
                    eq(mu(el, d(), s()), z()),
                    eq(
                        mu(el, mu(el, d(), s()), mu(el, d(), s())),
                        mu(el, z(), mu(el, d(), s())),
                    ),
                    ds0.clone(),
                    cm,
                );
                let z0 = el
                    .app("mul0", &[("u", mu(el, d(), s()))], &[])
                    .unwrap(); // ( 0 * (d*s) ) = 0
                eqtr3(
                    el,
                    mu(el, mu(el, d(), s()), mu(el, d(), s())),
                    mu(el, z(), mu(el, d(), s())),
                    z(),
                    e,
                    z0,
                ) // |- ( (d*s)*(d*s) = 0 )
            };
            let ssdd0 = eqtr3(
                el,
                mu(el, ss(), dd()),
                mu(el, mu(el, d(), s()), mu(el, d(), s())),
                z(),
                rsd,
                dsds0,
            ); // |- ( (s*s)*(d*d) = 0 )
            // rewrite mono's rhs ((s*s)*(d*d)) to 0  →  ((d*d)*(d*d)) <_ 0
            // cong-le2 : ( a=b -> ( ( c <_ a ) -> ( c <_ b ) ) )
            //   c=((d*d)*(d*d)), a=((s*s)*(d*d)), b=0
            let cl2b = el
                .app(
                    "cong-le2",
                    &[
                        ("a", mu(el, ss(), dd())),
                        ("b", z()),
                        ("c", mu(el, dd(), dd())),
                    ],
                    &[],
                )
                .unwrap();
            let impb = mp(
                eq(mu(el, ss(), dd()), z()),
                i(
                    le(mu(el, dd(), dd()), mu(el, ss(), dd())),
                    le(mu(el, dd(), dd()), z()),
                ),
                ssdd0,
                cl2b,
            );
            let d4le0 = mp(
                le(mu(el, dd(), dd()), mu(el, ss(), dd())),
                le(mu(el, dd(), dd()), z()),
                mono,
                impb,
            ); // |- ( ((d*d)*(d*d)) <_ 0 )
            // NOTE: mono's lhs is ((d*d)*(d*d)); cong-le2 c-slot must be that.
            // 0 <_ ((d*d)*(d*d))  [sqpos on (d*d)]
            let sqpdd = el.app("of-sqpos", &[("u", dd())], &[]).unwrap(); // ( 0 <_ ((d*d)*(d*d)) )
            // lein2(0, (d*d)*(d*d)) : ( (0<_X) -> ( (X<_0) -> (0=X) ) )
            let lein2 = el
                .app("lein2", &[("u", z()), ("v", mu(el, dd(), dd()))], &[])
                .unwrap();
            let t1 = mp(
                le(z(), mu(el, dd(), dd())),
                i(le(mu(el, dd(), dd()), z()), eq(z(), mu(el, dd(), dd()))),
                sqpdd,
                lein2,
            );
            let z_eq_d4 = mp(
                le(mu(el, dd(), dd()), z()),
                eq(z(), mu(el, dd(), dd())),
                d4le0,
                t1,
            ); // |- ( 0 = ((d*d)*(d*d)) )
            let d4_eq0 = eqcomm(el, z(), mu(el, dd(), dd()), z_eq_d4); // |- ( ((d*d)*(d*d)) = 0 )
            // sqz : ((d*d)*(d*d))=0 => (d*d)=0 ;  then (d*d)=0 => d=0
            let dd0 = el
                .app("sqz", &[("u", dd())], &[d4_eq0])
                .unwrap(); // |- ( (d*d) = 0 )
            let d0 = el.app("sqz", &[("u", d())], &[dd0]).unwrap(); // |- ( d = 0 )  i.e. ( (u-xv)=0 )
            let se0 = el
                .app("subeq0", &[("u", u()), ("v", v())], &[])
                .unwrap(); // ( ((u-xv)=0) -> (u=v) )
            let g = mp(eq(d(), z()), eq(u(), v()), d0, se0);
            Lemma {
                name: "sqcong".into(),
                ess: vec![
                    (
                        "sqcong.1".into(),
                        toks(&[
                            "|-", "(", "u", "*", "u", ")", "=", "(", "v", "*", "v", ")",
                        ]),
                    ),
                    (
                        "sqcong.2".into(),
                        toks(&[
                            "|-", "(", "0", "<_", "(", "u", "*", "v", ")", ")",
                        ]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 55: mulcposcan  |-(0<w),|-((u*w)=(v*w)) => |- u=v -----
        55 => {
            let u = || leaf("vu");
            let v = || leaf("vv");
            let w = || leaf("vw");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let d = || mi(el, u(), v());
            // dw0 : |- ( (d*w) = 0 )
            let rdw = ring_eq(
                el,
                &mu(el, d(), w()),
                &mi(el, mu(el, u(), w()), mu(el, v(), w())),
            ); // (d*w) = (u*w)-x(v*w)
            let cm1 = el
                .app(
                    "cong-mi1",
                    &[
                        ("a", mu(el, u(), w())),
                        ("b", mu(el, v(), w())),
                        ("c", mu(el, v(), w())),
                    ],
                    &[],
                )
                .unwrap(); // ( (u*w)=(v*w) -> ( ((u*w)-x(v*w)) = ((v*w)-x(v*w)) ) )
            let e1 = mp(
                eq(mu(el, u(), w()), mu(el, v(), w())),
                eq(
                    mi(el, mu(el, u(), w()), mu(el, v(), w())),
                    mi(el, mu(el, v(), w()), mu(el, v(), w())),
                ),
                leaf("mulcposcan.2"),
                cm1,
            );
            let sub00 = ring_eq(el, &mi(el, mu(el, v(), w()), mu(el, v(), w())), &z());
            let e2 = eqtr3(
                el,
                mi(el, mu(el, u(), w()), mu(el, v(), w())),
                mi(el, mu(el, v(), w()), mu(el, v(), w())),
                z(),
                e1,
                sub00,
            );
            let dw0 = eqtr3(
                el,
                mu(el, d(), w()),
                mi(el, mu(el, u(), w()), mu(el, v(), w())),
                z(),
                rdw,
                e2,
            ); // |- ( (d*w) = 0 )
            // (d*d)*(w*w) = (d*w)*(d*w) = 0
            let rddww = ring_eq(
                el,
                &mu(el, mu(el, d(), d()), mu(el, w(), w())),
                &mu(el, mu(el, d(), w()), mu(el, d(), w())),
            );
            let dwdw0 = {
                let cm = el
                    .app(
                        "cong-mu1",
                        &[
                            ("a", mu(el, d(), w())),
                            ("b", z()),
                            ("c", mu(el, d(), w())),
                        ],
                        &[],
                    )
                    .unwrap();
                let e = mp(
                    eq(mu(el, d(), w()), z()),
                    eq(
                        mu(el, mu(el, d(), w()), mu(el, d(), w())),
                        mu(el, z(), mu(el, d(), w())),
                    ),
                    dw0.clone(),
                    cm,
                );
                let z0 = el
                    .app("mul0", &[("u", mu(el, d(), w()))], &[])
                    .unwrap(); // ( 0 * (d*w) ) = 0
                eqtr3(
                    el,
                    mu(el, mu(el, d(), w()), mu(el, d(), w())),
                    mu(el, z(), mu(el, d(), w())),
                    z(),
                    e,
                    z0,
                )
            };
            let ddww0 = eqtr3(
                el,
                mu(el, mu(el, d(), d()), mu(el, w(), w())),
                mu(el, mu(el, d(), w()), mu(el, d(), w())),
                z(),
                rddww,
                dwdw0,
            ); // |- ( (d*d)*(w*w) = 0 )
            // 0 < (w*w)  [lemul2 on 0<w twice]
            let lemul2 = el
                .app("lemul2", &[("u", w()), ("v", w())], &[])
                .unwrap(); // ( (0<w) -> ( (0<w) -> (0<(w*w)) ) )
            let m1 = mp(
                lt(z(), w()),
                i(lt(z(), w()), lt(z(), mu(el, w(), w()))),
                leaf("mulcposcan.1"),
                lemul2,
            );
            let ww_pos = mp(
                lt(z(), w()),
                lt(z(), mu(el, w(), w())),
                leaf("mulcposcan.1"),
                m1,
            ); // |- ( 0 < (w*w) )
            // Suppose 0 < (d*d): then 0 < (d*d)*(w*w) contradicting ddww0.
            //   from lemul2 (on d*d, w*w) and ww_pos: ( (0<(d*d)) -> (0<((d*d)*(w*w))) )
            let lemul2b2 = el
                .app("lemul2", &[("u", mu(el, d(), d())), ("v", mu(el, w(), w()))], &[])
                .unwrap();
            let com = el
                .app(
                    "com12",
                    &[
                        ("ph", lt(z(), mu(el, d(), d()))),
                        ("ps", lt(z(), mu(el, w(), w()))),
                        ("ch", lt(z(), mu(el, mu(el, d(), d()), mu(el, w(), w())))),
                    ],
                    &[lemul2b2],
                )
                .unwrap(); // ( (0<(w*w)) -> ( (0<(d*d)) -> (0<((d*d)*(w*w))) ) )
            let hpos = mp(
                lt(z(), mu(el, w(), w())),
                i(
                    lt(z(), mu(el, d(), d())),
                    lt(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))),
                ),
                ww_pos,
                com,
            ); // |- ( (0<(d*d)) -> (0<((d*d)*(w*w))) )
            let lt0ne = el
                .app(
                    "lt0ne",
                    &[("u", z()), ("v", mu(el, mu(el, d(), d()), mu(el, w(), w())))],
                    &[],
                )
                .unwrap(); // ( (0<((d*d)*(w*w))) -> -.(0=((d*d)*(w*w))) )
            let hne = syl(
                lt(z(), mu(el, d(), d())),
                lt(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))),
                n(eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w())))),
                hpos,
                lt0ne,
            ); // ( (0<(d*d)) -> -.(0=((d*d)*(w*w))) )
            // 0 = ((d*d)*(w*w))  from ddww0
            let ddww0c = eqcomm(
                el,
                mu(el, mu(el, d(), d()), mu(el, w(), w())),
                z(),
                ddww0,
            ); // |- ( 0 = ((d*d)*(w*w)) )
            let nn1 = el
                .app(
                    "notnot1",
                    &[("ph", eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))))],
                    &[],
                )
                .unwrap();
            let nnf = mp(
                eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))),
                n(n(eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))))),
                ddww0c,
                nn1,
            ); // |- -.-.( 0 = ((d*d)*(w*w)) )
            let c3 = el
                .app(
                    "con3i",
                    &[
                        ("ph", lt(z(), mu(el, d(), d()))),
                        ("ps", n(eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))))),
                    ],
                    &[hne],
                )
                .unwrap(); // ( -.-.(0=((d*d)*(w*w))) -> -.(0<(d*d)) )
            let n_ddpos = mp(
                n(n(eq(z(), mu(el, mu(el, d(), d()), mu(el, w(), w()))))),
                n(lt(z(), mu(el, d(), d()))),
                nnf,
                c3,
            ); // |- -.( 0 < (d*d) )
            // 0 <_ (d*d) [sqpos];  with -.(0<(d*d)) and ltII => need (d*d) <_ 0 then lecon => (d*d)=0
            let sqpdd = el.app("of-sqpos", &[("u", d())], &[]).unwrap(); // |- ( 0 <_ (d*d) )
            // ltII(0,(d*d)) : ( (0<_(d*d)) -> ( -.((d*d)<_0) -> (0<(d*d)) ) )
            let ltii = el
                .app("ltII", &[("u", z()), ("v", mu(el, d(), d()))], &[])
                .unwrap();
            let m_ii = mp(
                le(z(), mu(el, d(), d())),
                i(
                    n(le(mu(el, d(), d()), z())),
                    lt(z(), mu(el, d(), d())),
                ),
                sqpdd.clone(),
                ltii,
            ); // |- ( -.((d*d)<_0) -> (0<(d*d)) )
            let nn_ddle0 = el
                .app(
                    "mt",
                    &[
                        ("ph", n(le(mu(el, d(), d()), z()))),
                        ("ps", lt(z(), mu(el, d(), d()))),
                    ],
                    &[m_ii, n_ddpos],
                )
                .unwrap(); // |- -.-.((d*d)<_0)
            let nn2 = el
                .app("notnot2", &[("ph", le(mu(el, d(), d()), z()))], &[])
                .unwrap();
            let dd_le0 = mp(
                n(n(le(mu(el, d(), d()), z()))),
                le(mu(el, d(), d()), z()),
                nn_ddle0,
                nn2,
            ); // |- ( (d*d) <_ 0 )
            let dd0 = el
                .app(
                    "lecon",
                    &[("u", mu(el, d(), d()))],
                    &[sqpdd, dd_le0],
                )
                .unwrap(); // |- ( (d*d) = 0 )
            let d0 = el.app("sqz", &[("u", d())], &[dd0]).unwrap(); // |- ( (u-xv) = 0 )
            let se0 = el
                .app("subeq0", &[("u", u()), ("v", v())], &[])
                .unwrap();
            let g = mp(eq(d(), z()), eq(u(), v()), d0, se0);
            Lemma {
                name: "mulcposcan".into(),
                ess: vec![
                    (
                        "mulcposcan.1".into(),
                        toks(&["|-", "(", "0", "<", "w", ")"]),
                    ),
                    (
                        "mulcposcan.2".into(),
                        toks(&[
                            "|-", "(", "u", "*", "w", ")", "=", "(", "v", "*", "w", ")",
                        ]),
                    ),
                ],
                goal: g,
            }
        }
        // ---- 56: G4 sas — the SAS postulate, derived over F1 ----------
        //  ess: (sqd a b)=(sqd e f), (sqd a c)=(sqd e g),
        //       ACong a b c e f g, 0<(sqd a b), 0<(sqd a c)
        //  ==> (sqd b c)=(sqd f g)
        //  via df-acong unfold -> side-eq substitution -> cancel the
        //  positive factor S=(sqd a b)*(sqd a c) [mulcposcan] ->
        //  (dot a b c)=(dot e f g) [sqcong] -> loclink x2 + congruence.
        56 => {
            let pa = || leaf("va");
            let pb = || leaf("vb");
            let pc = || leaf("vc");
            let pe = || leaf("ve");
            let pf = || leaf("vf");
            let pg = || leaf("vg");
            let z = || t0p(el);
            let eq = |s: Pt, t: Pt| el.app("weq", &[("x", s), ("y", t)], &[]).unwrap();
            let le = |s: Pt, t: Pt| el.app("tle", &[("u", s), ("v", t)], &[]).unwrap();
            let lt = |s: Pt, t: Pt| el.app("tlt", &[("u", s), ("v", t)], &[]).unwrap();
            let sqd = |p: Pt, q: Pt| el.app("tsqd", &[("a", p), ("b", q)], &[]).unwrap();
            let dot = |o: Pt, p: Pt, q: Pt| {
                el.app("tdot", &[("o", o), ("p", p), ("q", q)], &[]).unwrap()
            };
            let p = dot(pa(), pb(), pc()); // dot a b c
            let q = dot(pe(), pf(), pg()); // dot e f g
            let sab = sqd(pa(), pb());
            let sac = sqd(pa(), pc());
            let sef = sqd(pe(), pf());
            let seg = sqd(pe(), pg());
            let pp = mu(el, p.clone(), p.clone());
            let qq = mu(el, q.clone(), q.clone());
            let s = mu(el, sab.clone(), sac.clone()); // S
            // --- unfold df-acong ( ACong a b c e f g ) ---
            let eq_a = eq(
                mu(el, pp.clone(), mu(el, sef.clone(), seg.clone())),
                mu(el, qq.clone(), mu(el, sab.clone(), sac.clone())),
            );
            let sgn_a = le(z(), mu(el, p.clone(), q.clone()));
            let conj_a = a(eq_a.clone(), sgn_a.clone());
            let acong = el
                .app(
                    "wacong",
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
            let bi1 = el
                .app(
                    "ax-bi1",
                    &[("ph", acong.clone()), ("ps", conj_a.clone())],
                    &[],
                )
                .unwrap();
            let unf = mp(
                b(acong.clone(), conj_a.clone()),
                i(acong.clone(), conj_a.clone()),
                dfac,
                bi1,
            );
            let cj = mp(acong.clone(), conj_a.clone(), leaf("sas.3"), unf);
            let eqf = mp(
                conj_a.clone(),
                eq_a.clone(),
                cj.clone(),
                el.app(
                    "simpl",
                    &[("ph", eq_a.clone()), ("ps", sgn_a.clone())],
                    &[],
                )
                .unwrap(),
            ); // |- EQ
            let sgnf = mp(
                conj_a.clone(),
                sgn_a.clone(),
                cj,
                el.app(
                    "simpr",
                    &[("ph", eq_a.clone()), ("ps", sgn_a.clone())],
                    &[],
                )
                .unwrap(),
            ); // |- ( 0 <_ (p*q) )
            // --- substitute H1,H3 into EQ's left factor ---
            let h1c = eqcomm(el, sab.clone(), sef.clone(), leaf("sas.1")); // Sef=Sab
            let h3c = eqcomm(el, sac.clone(), seg.clone(), leaf("sas.2")); // Seg=Sac
            let ca = cmu1(el, sef.clone(), sab.clone(), seg.clone(), h1c); // (Sef*Seg)=(Sab*Seg)
            let cb = cmu2(el, seg.clone(), sac.clone(), sab.clone(), h3c); // (Sab*Seg)=(Sab*Sac)
            let sefseg = eqtr3(
                el,
                mu(el, sef.clone(), seg.clone()),
                mu(el, sab.clone(), seg.clone()),
                s.clone(),
                ca,
                cb,
            ); // (Sef*Seg)=S
            let left_eq = cmu2(
                el,
                mu(el, sef.clone(), seg.clone()),
                s.clone(),
                pp.clone(),
                sefseg,
            ); // (pp*(Sef*Seg))=(pp*S)
            let left_eq_c = eqcomm(
                el,
                mu(el, pp.clone(), mu(el, sef.clone(), seg.clone())),
                mu(el, pp.clone(), s.clone()),
                left_eq,
            ); // (pp*S)=(pp*(Sef*Seg))
            let eq2 = eqtr3(
                el,
                mu(el, pp.clone(), s.clone()),
                mu(el, pp.clone(), mu(el, sef.clone(), seg.clone())),
                mu(el, qq.clone(), s.clone()),
                left_eq_c,
                eqf,
            ); // |- ( (pp*S) = (qq*S) )
            // --- 0 < S ---
            let lemul2 = el
                .app("lemul2", &[("u", sab.clone()), ("v", sac.clone())], &[])
                .unwrap();
            let m1 = mp(
                lt(z(), sab.clone()),
                i(lt(z(), sac.clone()), lt(z(), s.clone())),
                leaf("sas.4"),
                lemul2,
            );
            let spos = mp(
                lt(z(), sac.clone()),
                lt(z(), s.clone()),
                leaf("sas.5"),
                m1,
            ); // |- ( 0 < S )
            // --- cancel S [mulcposcan] then sqcong ---
            let ppqq = el
                .app(
                    "mulcposcan",
                    &[("u", pp.clone()), ("v", qq.clone()), ("w", s.clone())],
                    &[spos, eq2],
                )
                .unwrap(); // |- ( (p*p)=(q*q) )
            let pq = el
                .app(
                    "sqcong",
                    &[("u", p.clone()), ("v", q.clone())],
                    &[ppqq, sgnf],
                )
                .unwrap(); // |- ( (dot a b c)=(dot e f g) )
            // --- loclink x2 + congruence ---
            let lk_abc = el
                .app(
                    "loclink",
                    &[("a", pa()), ("b", pb()), ("c", pc())],
                    &[],
                )
                .unwrap(); // (sqd b c) = ( (Sab+Sac) -x (p+p) )
            let lk_efg = el
                .app(
                    "loclink",
                    &[("a", pe()), ("b", pf()), ("c", pg())],
                    &[],
                )
                .unwrap(); // (sqd f g) = ( (Sef+Seg) -x (q+q) )
            let rhs_abc = mi(
                el,
                pl(el, sab.clone(), sac.clone()),
                pl(el, p.clone(), p.clone()),
            );
            let rhs_efg = mi(
                el,
                pl(el, sef.clone(), seg.clone()),
                pl(el, q.clone(), q.clone()),
            );
            let mid = mi(
                el,
                pl(el, sef.clone(), seg.clone()),
                pl(el, p.clone(), p.clone()),
            );
            let pe1 = cpl1(el, sab.clone(), sef.clone(), sac.clone(), leaf("sas.1")); // (Sab+Sac)=(Sef+Sac)
            let pe2 = cpl2(el, sac.clone(), seg.clone(), sef.clone(), leaf("sas.2")); // (Sef+Sac)=(Sef+Seg)
            let sum_s = eqtr3(
                el,
                pl(el, sab.clone(), sac.clone()),
                pl(el, sef.clone(), sac.clone()),
                pl(el, sef.clone(), seg.clone()),
                pe1,
                pe2,
            );
            let pp1 = cpl1(el, p.clone(), q.clone(), p.clone(), pq.clone()); // (p+p)=(q+p)
            let pp2 = cpl2(el, p.clone(), q.clone(), q.clone(), pq.clone()); // (q+p)=(q+q)
            let sum_p = eqtr3(
                el,
                pl(el, p.clone(), p.clone()),
                pl(el, q.clone(), p.clone()),
                pl(el, q.clone(), q.clone()),
                pp1,
                pp2,
            );
            let mi1 = cmi1(
                el,
                pl(el, sab.clone(), sac.clone()),
                pl(el, sef.clone(), seg.clone()),
                pl(el, p.clone(), p.clone()),
                sum_s,
            ); // rhs_abc = mid
            let mi2 = cmi2(
                el,
                pl(el, p.clone(), p.clone()),
                pl(el, q.clone(), q.clone()),
                pl(el, sef.clone(), seg.clone()),
                sum_p,
            ); // mid = rhs_efg
            let rhs_eq = eqtr3(el, rhs_abc.clone(), mid.clone(), rhs_efg.clone(), mi1, mi2);
            let lk_efg_c = eqcomm(el, sqd(pf(), pg()), rhs_efg.clone(), lk_efg); // rhs_efg=(sqd f g)
            let t = eqtr3(
                el,
                sqd(pb(), pc()),
                rhs_abc.clone(),
                rhs_efg.clone(),
                lk_abc,
                rhs_eq,
            ); // (sqd b c)=rhs_efg
            let g = eqtr3(
                el,
                sqd(pb(), pc()),
                rhs_efg.clone(),
                sqd(pf(), pg()),
                t,
                lk_efg_c,
            ); // (sqd b c)=(sqd f g)
            Lemma {
                name: "G4-sas".into(),
                ess: vec![
                    (
                        "sas.1".into(),
                        toks(&[
                            "|-", "(", "sqd", "a", "b", ")", "=", "(", "sqd", "e", "f",
                            ")",
                        ]),
                    ),
                    (
                        "sas.2".into(),
                        toks(&[
                            "|-", "(", "sqd", "a", "c", ")", "=", "(", "sqd", "e", "g",
                            ")",
                        ]),
                    ),
                    (
                        "sas.3".into(),
                        toks(&[
                            "|-", "(", "ACong", "a", "b", "c", "e", "f", "g", ")",
                        ]),
                    ),
                    (
                        "sas.4".into(),
                        toks(&["|-", "(", "0", "<", "(", "sqd", "a", "b", ")", ")"]),
                    ),
                    (
                        "sas.5".into(),
                        toks(&["|-", "(", "0", "<", "(", "sqd", "a", "c", ")", ")"]),
                    ),
                ],
                goal: g,
            }
        }
        _ => unreachable!(),
    }
}

const NAMES: [&str; 57] = [
    "id", "a1i", "syl", "pm2.21", "pm2.43", "notnot2", "notnot1", "simpl",
    "simpr", "G3c-rayline", "eqtrd", "G0-congsub", "eqtr", "addcan",
    "ac-demo", "ac-mul-demo", "ring-demo", "mul0", "neginv", "negneg",
    "negadd", "mulneg1", "mulneg2", "loclink",
    "mpd", "syld", "com12", "con3i", "con3", "pm2.18", "jca", "orri",
    "orli", "jaoi", "subid", "sub0r", "le2sub", "sub2le", "lerefl",
    "pm3.2", "expi", "ltle", "lt0ne", "lein2", "ltII", "lemul2",
    "lemul02", "mt", "lecon", "subeq0", "sqzhalf", "sqz", "le0add",
    "lemul0mono", "sqcong", "mulcposcan", "G4-sas",
];

/// Stage one lemma: sound peephole-shrink, show the conclusion, append,
/// reassemble + reparse, and (only with GROUNDED_VERIFY_EACH) re-verify.
/// Used identically for the core 57 and the extra postulate modules.
fn stage(
    _base: &str,
    db: &mut kernel::Db,
    lemmas: &mut Vec<Lemma>,
    concls: &mut Vec<String>,
    shrinks: &mut Vec<Option<(usize, usize)>>,
    label_idx: usize,
    mut lm: Lemma,
) {
    {
        let el = Elab::new(db);
        let before = elaborate::pt_nodes(&lm.goal);
        eprintln!("  staged[{label_idx}] {}: {before} raw nodes; shrinking...", lm.name);
        lm.goal = el.shrink(&lm.goal);
        let after = elaborate::pt_nodes(&lm.goal);
        if before != after {
            eprintln!("  shrink[{label_idx}] {}: {before} -> {after} nodes", lm.name);
            shrinks.push(Some((before, after)));
        } else {
            shrinks.push(None);
        }
    }
    let locals: HashMap<String, Vec<String>> = lm.ess.iter().cloned().collect();
    {
        let el = Elab::new(db);
        match el.conclusion_l(&lm.goal, &locals) {
            Ok(c) => {
                println!("  [{label_idx}] {:<14} {}", lm.name, c.join(" "));
                concls.push(c.join(" "));
            }
            Err(e) => die(&format!("conclusion({})", lm.name), e),
        }
    }
    let name = lm.name.clone();
    // Incremental append: emit only this lemma's kernel text and extend the
    // in-memory db, instead of re-stringifying + re-parsing the entire
    // growing corpus every stage (which was O(n²) in total proof size — the
    // 4.3M-node loclink RPN was being re-tokenised ~34+ times). The final
    // cumulative `db.verify()` in main remains the authoritative check and
    // is byte-identical to verifying a monolithic parse of base + lemmas.
    let frag = {
        let el = Elab::new(db);
        assemble_one(&el, &lm).unwrap_or_else(|e| die(&format!("assemble {name}"), e))
    };
    lemmas.push(lm);
    db.extend(&frag)
        .unwrap_or_else(|e| die(&format!("append {name}"), e));
    if std::env::var("GROUNDED_VERIFY_EACH").is_ok() {
        if let Err(e) = db.verify() {
            die(&format!("KERNEL REJECTED at {name}"), e);
        }
    }
}

fn main() {
    let base = std::fs::read_to_string("data/grounded.mm").expect("read grounded.mm");
    // Start the incremental db from the same truncated base `assemble` uses
    // (everything before the F0 ASA-GOAL section), so the cumulative db is
    // exactly base-prefix + staged lemmas — identical to the old reparse path.
    let cut_base = base
        .find("$( ASA-GOAL:")
        .map(|i| base[..i].to_string())
        .unwrap_or_else(|| base.clone());
    let mut db = kernel::Db::parse(&cut_base).unwrap_or_else(|e| die("base parse", e));
    let mut lemmas: Vec<Lemma> = Vec::new();
    let mut concls: Vec<String> = Vec::new();
    let mut shrinks: Vec<Option<(usize, usize)>> = Vec::new();

    println!("=== Task #7: staged proofs of geometric postulates over F1 (field + √ + df-*) ===\n");
    // core 57
    for idx in 0..NAMES.len() {
        let lm = {
            let el = Elab::new(&db);
            make_lemma(idx, &el)
        };
        stage(&base, &mut db, &mut lemmas, &mut concls, &mut shrinks, idx, lm);
    }
    // extra postulate modules (worktree-isolated), staged after the core.
    let mut next = NAMES.len();
    for k in 0..proof_g2::count() {
        let lm = {
            let el = Elab::new(&db);
            proof_g2::make(k, &el)
        };
        stage(&base, &mut db, &mut lemmas, &mut concls, &mut shrinks, next, lm);
        next += 1;
    }
    for k in 0..proof_g3::count() {
        eprintln!("  building[{next}] proof_g3::make({k})...");
        let lm = {
            let el = Elab::new(&db);
            proof_g3::make(k, &el)
        };
        eprintln!("  built[{next}] proof_g3::make({k}) ok");
        stage(&base, &mut db, &mut lemmas, &mut concls, &mut shrinks, next, lm);
        next += 1;
    }
    for k in 0..proof_g1::count() {
        let lm = {
            let el = Elab::new(&db);
            proof_g1::make(k, &el)
        };
        stage(&base, &mut db, &mut lemmas, &mut concls, &mut shrinks, next, lm);
        next += 1;
    }
    // Write the full assembled corpus once (inspection artifact only; no
    // longer on the per-stage hot path).
    if let Ok(src) = assemble(&base, &db, &lemmas) {
        std::fs::write("data/grounded.out.mm", &src).ok();
    }

    // single authoritative cumulative kernel verification.
    if let Err(e) = db.verify() {
        die("KERNEL REJECTED (final)", e);
    }

    println!(
        "\nKernel: verified all {} staged lemmas ✔  (db: {} statements)",
        lemmas.len(),
        db.stmts.len()
    );

    let mut memo = HashMap::new();
    let simpl = expand(&db, "simpl", &mut memo);
    let g3c = expand(&db, "G3c-rayline", &mut memo);
    let eqtrd = expand(&db, "eqtrd", &mut memo);
    let g0 = expand(&db, "G0-congsub", &mut memo);
    let mulneg1 = expand(&db, "mulneg1", &mut memo);
    let loc = expand(&db, "loclink", &mut memo);
    let sqcong = expand(&db, "sqcong", &mut memo);
    let mulcpos = expand(&db, "mulcposcan", &mut memo);
    let sas = expand(&db, "G4-sas", &mut memo);
    println!(
        "\n=== Exact fully-inlined $a-invocations (F1-grounded) ===\n\
         simpl  (propositional core)        : {}\n\
         eqtrd  (deduction transitivity)    : {}\n\
         G3c rayline  (postulate, df-unfold): {}\n\
         G0  cong-sub (postulate, congr.)   : {}\n\
         mulneg1 (derived ring negation)    : {}\n\
         loclink  (law of cosines, reusable) : {}\n\
         sqcong (a²=b² ∧ 0≤ab → a=b)        : {}\n\
         mulcposcan (cancel positive factor): {}\n\
         G4 SAS  (derived postulate)        : {}\n\
         \nThe √-free algebraic core of G4 SAS — the law-of-cosines\n\
         coordinate identity sqd(b,c) = sqd(a,b)+sqd(a,c)-2·dot(a,b,c) —\n\
         is discharged by the kernel-checked ring_eq procedure\n\
         (desugar -x → distribute → sign-canonicalize → cancel),\n\
         using no geometric axioms. Postulate and algebra costs are small\n\
         constants (~10^2-10^4); the dominant blow-up in a full ZFC grounding\n\
         is the ℝ-construction, not the geometry.",
        simpl.pretty(),
        eqtrd.pretty(),
        g3c.pretty(),
        g0.pretty(),
        mulneg1.pretty(),
        loc.pretty(),
        sqcong.pretty(),
        mulcpos.pretty(),
        sas.pretty()
    );

    if std::env::args().any(|a| a == "--emit-json") {
        emit_json(&db, &lemmas, &concls, &shrinks);
    }
}

/// Coarse classification of a staged lemma by name, for the explorer.
fn kind_of(name: &str) -> &'static str {
    match name {
        "id" | "a1i" | "syl" | "pm2.21" | "pm2.43" | "notnot2" | "notnot1"
        | "simpl" | "simpr" | "mpd" | "syld" | "com12" | "con3i" | "con3"
        | "pm2.18" | "jca" | "orri" | "orli" | "jaoi" | "pm3.2" | "expi"
        | "mt" => "prop",
        "eqtrd" | "eqtr" => "eqlogic",
        "G3c-rayline" | "G0-congsub" | "G4-sas" => "postulate",
        "ac-demo" | "ac-mul-demo" | "ring-demo" => "demo",
        "le2sub" | "sub2le" | "lerefl" | "ltle" | "lt0ne" | "lein2" | "ltII"
        | "lemul2" | "lemul02" | "lecon" | "sqzhalf" | "sqz" | "le0add"
        | "lemul0mono" | "sqcong" | "mulcposcan" => "order",
        _ => "ring",
    }
}

/// Is `lbl` an "interesting" dependency (a staged lemma or a genuine
/// axiom/definition), as opposed to a pure syntax constructor?
fn interesting_dep(lbl: &str) -> bool {
    NAMES.contains(&lbl)
        || lbl.starts_with("of-")
        || lbl.starts_with("ax-")
        || lbl.starts_with("df-")
        || lbl.starts_with("cong-")
        || lbl == "eqcom"
        || lbl == "eqid"
}

fn json_str(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// Emit docs/data/site.json (schema in docs/SCHEMA.md): per-lemma exact
/// inlined (cut-free) vs shared (DAG, stored RPN) sizes + the dependency
/// graph + the model-variation table.  The shared total is the sound
/// proof-cruncher figure: the same kernel-checked proofs kept as a DAG
/// with sub-proofs shared once.
fn emit_json(
    db: &kernel::Db,
    lemmas: &[Lemma],
    concls: &[String],
    shrinks: &[Option<(usize, usize)>],
) {
    let mut memo = HashMap::new();
    // shared total = sum of stored RPN proof lengths over every $p
    let shared_total: usize = db
        .stmts
        .iter()
        .filter(|s| matches!(s.kind, kernel::Kind::P))
        .map(|s| s.proof.len())
        .sum();

    let mut lem_json: Vec<String> = Vec::new();
    let mut node_set: Vec<(String, f64, String)> = Vec::new(); // (id, log10 size, kind)
    let mut edges: Vec<(String, String)> = Vec::new();
    let mut g4_log = 0.0_f64;
    let mut g4_pretty = String::new();

    for (idx, lm) in lemmas.iter().enumerate() {
        let name = &lm.name;
        let inlined = expand(db, name, &mut memo);
        let ilog = inlined.log10();
        let st = db.get(name);
        let shared = st.map(|s| s.proof.len()).unwrap_or(0);
        // interesting deps, dedup preserving order
        let mut deps: Vec<String> = Vec::new();
        if let Some(s) = st {
            for l in &s.proof {
                let is_thm = db.get(l).map_or(false, |s| matches!(s.kind, kernel::Kind::P));
                if (interesting_dep(l) || is_thm) && !deps.iter().any(|d| d == l) {
                    deps.push(l.clone());
                }
            }
        }
        let kind = kind_of(name);
        if name == "G4-sas" {
            g4_log = ilog;
            g4_pretty = inlined.pretty();
        }
        node_set.push((name.clone(), ilog, kind.to_string()));
        for d in &deps {
            edges.push((name.clone(), d.clone()));
        }
        let ess: Vec<String> = lm
            .ess
            .iter()
            .map(|(_, toks)| json_str(&toks.join(" ")))
            .collect();
        let deps_j: Vec<String> = deps.iter().map(|d| json_str(d)).collect();
        let (sb, sa) = match shrinks.get(idx).and_then(|x| *x) {
            Some((b, a)) => (b.to_string(), a.to_string()),
            None => ("null".into(), "null".into()),
        };
        let concl = concls.get(idx).cloned().unwrap_or_default();
        lem_json.push(format!(
            "{{\"idx\":{idx},\"name\":{},\"kind\":{},\"statement\":{},\"ess\":[{}],\"deps\":[{}],\"inlined\":{},\"inlined_pretty\":{},\"inlined_log10\":{:.4},\"shared\":{},\"shrink_before\":{},\"shrink_after\":{}}}",
            json_str(name),
            json_str(kind),
            json_str(&concl),
            ess.join(","),
            deps_j.join(","),
            // exact integer when it fits a u64-ish range, else log10
            if ilog < 18.0 { inlined.pretty() } else { format!("{:.4e}", 10f64.powf(ilog)) },
            json_str(&inlined.pretty()),
            ilog,
            shared,
            sb,
            sa
        ));
    }

    // dependency-graph axiom/def nodes (referenced but not staged)
    let mut seen: Vec<String> = node_set.iter().map(|(n, _, _)| n.clone()).collect();
    for (_, d) in &edges {
        if !seen.iter().any(|s| s == d) {
            seen.push(d.clone());
            let k = if d.starts_with("df-") {
                "def"
            } else {
                "axiom"
            };
            node_set.push((d.clone(), 0.0, k.to_string()));
        }
    }

    let nodes_j: Vec<String> = node_set
        .iter()
        .map(|(n, sz, k)| {
            format!(
                "{{\"id\":{},\"log10\":{:.4},\"kind\":{}}}",
                json_str(n),
                sz,
                json_str(k)
            )
        })
        .collect();
    let edges_j: Vec<String> = edges
        .iter()
        .map(|(f, t)| format!("{{\"from\":{},\"to\":{}}}", json_str(f), json_str(t)))
        .collect();

    let models = r#"[
    {"id":"f1","label":"F1 axiomatic (kernel-exact)","kind":"geometry","log10":G4LOG,"note":"ordered ring + one sqrt axiom; geometry skeleton, exact"},
    {"id":"euclid","label":"Minimal Euclidean-field model","kind":"substrate","log10":37.0,"note":"sqrt a model primitive; algebraic closure tower"},
    {"id":"realR","label":"Full ZFC model of R (set.mm)","kind":"substrate","log10":45.7,"note":"set.mm constructed R; dominated by resqrtth (analytic sqrt)"},
    {"id":"poll","label":"The poll's estimate","kind":"claim","log10":1000.0,"note":"off by ~950+ orders of magnitude"}
  ]"#
        .replace("G4LOG", &format!("{:.4}", g4_log));

    let out = format!(
        "{{\n  \"generated\": {},\n  \"headline\": {{\"f0_asa\": 224, \"g4_sas_inlined\": {}, \"g4_sas_log10\": {:.4}, \"lemmas\": {}, \"db_statements\": {}, \"shared_total\": {}}},\n  \"models\": {},\n  \"lemmas\": [\n    {}\n  ],\n  \"dag\": {{\"nodes\": [{}], \"edges\": [{}]}}\n}}\n",
        json_str(&chrono_stamp()),
        g4_pretty,
        g4_log,
        lemmas.len(),
        db.stmts.len(),
        shared_total,
        models,
        lem_json.join(",\n    "),
        nodes_j.join(","),
        edges_j.join(",")
    );
    std::fs::create_dir_all("docs/data").ok();
    std::fs::write("docs/data/site.json", &out)
        .unwrap_or_else(|e| die("write docs/data/site.json", e.to_string()));
    println!(
        "\n[emit-json] docs/data/site.json written — inlined G4 SAS = {}, shared total = {} steps (cruncher: {:.1}x smaller than the cut-free total)",
        g4_pretty,
        shared_total,
        10f64.powf(g4_log) / shared_total.max(1) as f64
    );
}

/// Best-effort UTC timestamp without pulling a date crate.
fn chrono_stamp() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format!("unix:{secs}")
}
