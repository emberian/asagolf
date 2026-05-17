//! Frontier C — order-core lower bound: separating-model sanity check.
//!
//!   cargo run --release --bin ordercore
//!
//! This is a small, READ-ONLY, NON-AUTHORITATIVE check. It does not parse,
//! re-derive, or modify the authoritative corpus (`data/grounded.mm` /
//! `src/bin/grounded.rs`) and it is NOT a kernel verification. Its sole job
//! is to machine-check the *arithmetic of the separating models* used in
//! `FRONTIER_C_ORDERCORE.md` Theorem 1, so the refutation is verified rather
//! than asserted:
//!
//!   * In Z/8Z: u=3, v=1 witness (u*u = v*v) /\ (u != v)
//!       => `sqcong`'s conclusion `(u^2=v^2) -> u=v` is FALSE in a
//!          commutative ring  (refutes the bare order-free form, F1).
//!   * In Z/4Z: x=2 witness (x*x = 0) /\ (x != 0), hence x^4 = 0 /\ x != 0
//!       => the load-bearing internal step `x^4=0 |- x=0` (the double
//!          `sqz` at grounded.rs:4303-4306) and `sqz`/`sqzhalf` itself are
//!          FALSE in a commutative ring  (refutes F2 — the exact measured
//!          61.52% order-block).
//!
//! The THEOREM's force is the model-theoretic soundness argument (Lemma B:
//! equational logic is sound for the variety of commutative rings, so any
//! ring-identity-only derivation holds in every commutative ring; a
//! statement false in Z/8 or Z/4 is therefore not such a derivation). That
//! is a proof, not a computation. This binary only certifies the witnesses.

/// Multiplication in Z/nZ on small nonnegative residues.
fn mul_mod(a: u64, b: u64, n: u64) -> u64 {
    (a % n) * (b % n) % n
}

fn main() {
    let mut all_ok = true;
    let mut check = |label: &str, cond: bool| {
        println!(
            "[ordercore] {label} : {}",
            if cond { "OK" } else { "FAIL" }
        );
        all_ok &= cond;
    };

    // ---- Lemma A.1 : Z/8Z, u=3 v=1 refutes sqcong without the order ----
    let n8 = 8u64;
    let (u, v) = (3u64, 1u64);
    let uu = mul_mod(u, u, n8); // 9 mod 8 = 1
    let vv = mul_mod(v, v, n8); // 1
    check(
        "Z/8: u=3 v=1  u*u=1 v*v=1  (u*u==v*v) && (u!=v)  -> sqcong FALSE without order",
        uu == vv && u != v,
    );

    // ---- Lemma A.2 : Z/4Z, x=2 refutes x^4=0 |- x=0 (and x^2=0|-x=0) ----
    let n4 = 4u64;
    let x = 2u64;
    let x2 = mul_mod(x, x, n4); // 4 mod 4 = 0
    let x4 = mul_mod(x2, x2, n4); // 0
    check(
        "Z/4: x=2      x*x=0  x^4=0   (x^4==0) && (x!=0)   -> x^4=0=>x=0 FALSE in CR",
        x4 == 0 && x != 0,
    );
    check(
        "Z/4: x=2      x*x=0          (x*x==0) && (x!=0)   -> sqz/sqzhalf NOT a ring id",
        x2 == 0 && x != 0,
    );

    // ---- Soundness sanity: the SEAM4 generic identities used by sqcong
    //      really are true commutative-ring identities, hence USELESS here
    //      (they hold in Z/8 & Z/4 yet the conclusion is false there). ----
    // sqc-diffsq: (p-q)(p+q) = p*p - q*q ; sqc-4uv: (p+q)^2-(p-q)^2 = 4pq ;
    // sqc-gprod : (p*p)*(q*q) = (p*q)*(p*q). Check over all residues mod 8.
    let mut identities_hold = true;
    for n in [4u64, 8u64] {
        for p in 0..n {
            for q in 0..n {
                let pm = |a: i64| ((a % n as i64 + n as i64) % n as i64) as u64;
                let diffsq_l = mul_mod(pm(p as i64 - q as i64), (p + q) % n, n);
                let diffsq_r = pm(mul_mod(p, p, n) as i64 - mul_mod(q, q, n) as i64);
                let s = (p + q) % n;
                let d = pm(p as i64 - q as i64);
                let uv4_l = pm(mul_mod(s, s, n) as i64 - mul_mod(d, d, n) as i64);
                let uv4_r = (4 * mul_mod(p, q, n)) % n;
                let gprod_l = mul_mod(mul_mod(p, p, n), mul_mod(q, q, n), n);
                let gprod_r = mul_mod(mul_mod(p, q, n), mul_mod(p, q, n), n);
                identities_hold &= diffsq_l == diffsq_r
                    && uv4_l == uv4_r
                    && gprod_l == gprod_r;
            }
        }
    }
    check(
        "SEAM4 generics (sqc-diffsq/sqc-4uv/sqc-gprod) hold in Z/4 & Z/8 (true ring ids, so cannot help)",
        identities_hold,
    );

    println!(
        "[ordercore] separation verified: every ring identity holds in Z/8 & Z/4 (soundness),"
    );
    println!(
        "            yet sqcong's conclusion is false there => order axioms are essential."
    );
    println!(
        "[ordercore] PROVEN: order predicate essential.  CONJECTURED: exact 61.52% constant (Obligation O)."
    );

    if all_ok {
        println!("[ordercore] ALL CHECKS PASSED");
    } else {
        eprintln!("[ordercore] A CHECK FAILED");
        std::process::exit(1);
    }
}
