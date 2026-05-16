//! Sound common-subproof factoring (proof-DAG minimizer).
//!
//! Operates *only* on the kernel's parsed database and the flat RPN proof
//! lists.  It introduces extra `$p` helper lemmas for frequently-occurring,
//! self-contained ("closed": no local `$e` hypothesis leaf) subproofs and
//! rewrites every occurrence to a single call.  Statements of the original
//! `$p`s are never touched, so the only correctness obligation is that the
//! rewritten database still kernel-verifies — which the caller checks, and
//! which, if it ever failed (or a conclusion drifted), makes the caller
//! discard the whole pass and report the un-crunched figure.  Soundness
//! therefore reduces entirely to the kernel re-verification.
//!
//! `shared_total` = Σ stored RPN length over every `$p`.  A subproof S of
//! RPN length L occurring k times, with v distinct free `$f` variables,
//! becomes one helper of length L plus k calls of length v+1: net change
//! L + k·(v+1) − k·L, strongly negative for the deeply-shared algebra
//! subproofs in this corpus.
//!
//! Scaling note (current corpus is ~10^5.6 and one lemma has >3·10^5
//! nodes): subtree identity is a recursively-computed 128-bit content
//! hash, *not* a materialised RPN string, so memory is O(#nodes) rather
//! than O(#nodes²).  A content-hash collision can at worst make two
//! distinct subtrees share a helper, which the kernel re-verification then
//! rejects (=> discard, report un-crunched) — it can never produce an
//! unsound accept.  Each round extracts a batch of non-overlapping
//! profitable patterns in one reparse; rounds iterate to a fixpoint.

use crate::kernel::{Db, Kind};
use std::collections::HashMap;

/// 128-bit FNV-1a over the kernel-canonical RPN, computed recursively so
/// it costs O(#nodes) total rather than O(#nodes²) of an RPN string.
type Sig = u128;

#[derive(Clone)]
struct Node {
    label: String,
    kids: Vec<Node>,
    sig: Sig,
    size: u32, // RPN length of this subtree (saturating)
}

fn fnv_bytes(mut h: Sig, bytes: &[u8]) -> Sig {
    for &b in bytes {
        h ^= b as Sig;
        h = h.wrapping_mul(0x0000_0000_0100_0000_0000_0000_0000_013B);
    }
    h
}

fn arity(db: &Db, label: &str) -> Option<usize> {
    let s = db.get(label)?;
    Some(match s.kind {
        Kind::F | Kind::E => 0,
        Kind::A | Kind::P => s.mand_hyps.len(),
    })
}

fn mk(label: String, kids: Vec<Node>) -> Node {
    // sig = H(label ‖ 0x00 ‖ child sigs ‖ 0x01) — prefix-free, so distinct
    // RPN trees get distinct preimages.
    let mut h: Sig = 0x6C62_272E_07BB_0142_62B8_2175_6295_C58D;
    h = fnv_bytes(h, label.as_bytes());
    h = fnv_bytes(h, &[0x00]);
    let mut size: u32 = 1;
    for k in &kids {
        h = fnv_bytes(h, &k.sig.to_le_bytes());
        size = size.saturating_add(k.size);
    }
    h = fnv_bytes(h, &[0x01]);
    Node { label, kids, sig: h, size }
}

/// Rebuild a proof tree from flat RPN exactly as the kernel's stack
/// verifier would (pop `arity`, push self). `None` if it is not a single
/// well-formed tree.
fn rebuild(db: &Db, proof: &[String]) -> Option<Node> {
    let mut stack: Vec<Node> = Vec::new();
    for lbl in proof {
        let a = arity(db, lbl)?;
        if stack.len() < a {
            return None;
        }
        let kids = stack.split_off(stack.len() - a);
        stack.push(mk(lbl.clone(), kids));
    }
    if stack.len() == 1 {
        stack.pop()
    } else {
        None
    }
}

fn flatten(n: &Node, out: &mut Vec<String>) {
    for k in &n.kids {
        flatten(k, out);
    }
    out.push(n.label.clone());
}
fn rpn(n: &Node) -> Vec<String> {
    let mut v = Vec::new();
    flatten(n, &mut v);
    v
}

/// Tally every closed subtree (no `$e` leaf anywhere inside).  Returns
/// whether this subtree references an `$e` leaf, for the caller's
/// recursion.  Stores one representative `Node` per content hash; on a
/// (vanishingly unlikely) hash collision two different subtrees would map
/// to one entry and the kernel re-verification rejects the pass.
fn collect(
    db: &Db,
    n: &Node,
    table: &mut HashMap<Sig, (usize, Node)>,
) -> bool {
    let self_e = matches!(db.get(&n.label).map(|s| &s.kind), Some(Kind::E));
    let mut any_e = self_e;
    for k in &n.kids {
        any_e |= collect(db, k, table);
    }
    // Memory guard: only tally closed subtrees up to a size cap.  A helper
    // is one stored copy + small calls, so very large verbatim-repeated
    // subtrees are rare and dominate table memory on the >3·10^5-node
    // lemmas; excluding them only forgoes candidates (still sound) while
    // keeping the round O(#nodes) in memory.  Patterns above the cap are
    // still reachable indirectly: their profitable sub-patterns (≤ cap)
    // get factored in earlier rounds, shrinking the enclosing proof.
    const MAX_SUBTREE: u32 = 4096;
    if !any_e && !n.kids.is_empty() && n.size <= MAX_SUBTREE {
        let e = table.entry(n.sig).or_insert_with(|| (0, n.clone()));
        e.0 += 1;
    }
    any_e
}

fn free_fvars(db: &Db, n: &Node, seen: &mut Vec<String>) {
    if n.kids.is_empty() {
        if matches!(db.get(&n.label).map(|s| &s.kind), Some(Kind::F))
            && !seen.iter().any(|x| x == &n.label)
        {
            seen.push(n.label.clone());
        }
        return;
    }
    for k in &n.kids {
        free_fvars(db, k, seen);
    }
}

/// Structurally evaluate a closed subtree's conclusion via the kernel's
/// substitution rule (identical to `verify_proof`'s).
fn eval_concl(db: &Db, n: &Node) -> Option<Vec<String>> {
    let s = db.get(&n.label)?;
    match s.kind {
        Kind::F | Kind::E => Some(s.expr.clone()),
        Kind::A | Kind::P => {
            if n.kids.len() != s.mand_hyps.len() {
                return None;
            }
            let mut subst: HashMap<String, Vec<String>> = HashMap::new();
            for (hl, kid) in s.mand_hyps.iter().zip(&n.kids) {
                let h = db.get(hl)?;
                let kc = eval_concl(db, kid)?;
                match h.kind {
                    Kind::F => {
                        if kc.is_empty() || kc[0] != h.expr[0] {
                            return None;
                        }
                        subst.insert(h.expr[1].clone(), kc[1..].to_vec());
                    }
                    Kind::E => {}
                    _ => return None,
                }
            }
            let mut out = Vec::new();
            for tok in &s.expr {
                if let Some(rep) = subst.get(tok) {
                    out.extend(rep.iter().cloned());
                } else {
                    out.push(tok.clone());
                }
            }
            Some(out)
        }
    }
}

/// Multi-pattern top-down rewrite: if this node's content hash is a chosen
/// helper, splice in the call (helper label preceded by its $f-arg leaves
/// in the helper's kernel-frame order); else recurse into kids.  Top-down
/// so a replaced subtree is never descended into (no double rewrite).
fn rewrite(
    n: &Node,
    helpers: &HashMap<Sig, (String, Vec<String>)>,
) -> Node {
    if let Some((hname, fvar_order)) = helpers.get(&n.sig) {
        let kids = fvar_order
            .iter()
            .map(|fl| mk(fl.clone(), vec![]))
            .collect();
        return mk(hname.clone(), kids);
    }
    let kids = n.kids.iter().map(|k| rewrite(k, helpers)).collect();
    mk(n.label.clone(), kids)
}

/// One batched CSE round.  `base` numbers new helpers uniquely across
/// rounds.  Returns `(new_source, next_base, helpers_added)`.
fn one_round(src: &str, base: usize) -> Option<(String, usize, usize)> {
    let db = Db::parse(src).ok()?;

    let mut trees: Vec<(String, Node)> = Vec::new();
    for s in &db.stmts {
        if s.kind == Kind::P {
            let t = rebuild(&db, &s.proof)?;
            trees.push((s.label.clone(), t));
        }
    }

    let mut table: HashMap<Sig, (usize, Node)> = HashMap::new();
    for (_, t) in &trees {
        collect(&db, t, &mut table);
    }

    // Profitable candidates: net = (L-(v+1))*k - L > 0, k >= 2.
    struct Cand {
        sig: Sig,
        node: Node,
        len: usize,
        net: i64,
    }
    let mut cands: Vec<Cand> = Vec::new();
    for (sg, (k, node)) in &table {
        if *k < 2 {
            continue;
        }
        let l = node.size as usize;
        let mut fv = Vec::new();
        free_fvars(&db, node, &mut fv);
        let v = fv.len();
        let saving = l as i64 - (v as i64 + 1);
        if saving <= 0 {
            continue;
        }
        let net = saving * (*k as i64) - l as i64;
        if net <= 0 {
            continue;
        }
        cands.push(Cand { sig: *sg, node: node.clone(), len: l, net });
    }
    if cands.is_empty() {
        return None;
    }
    // Largest patterns first so a chosen big pattern is preferred over its
    // own sub-patterns at the same root (top-down rewrite enforces this);
    // tie-break by net benefit.
    cands.sort_by(|a, b| b.len.cmp(&a.len).then(b.net.cmp(&a.net)));

    // Take a bounded batch per round (keeps reparse count tiny while still
    // converging fast).
    const BATCH: usize = 400;
    cands.truncate(BATCH);

    // Emit helper statements; record (sig -> (hname, fvar frame order)).
    // Conclusion via kernel substitution; frame order learned by a single
    // reparse below.
    let mut helper_lines = String::new();
    let mut provisional: Vec<(String, Sig, Node)> = Vec::new(); // hname, sig, node
    for (i, c) in cands.iter().enumerate() {
        let hname = format!("cse{}", base + i);
        let concl = match eval_concl(&db, &c.node) {
            Some(x) => x,
            None => continue,
        };
        // Only hoist genuine derivations / well-typed terms (concl has a
        // typecode token first; always true for our $a/$p outputs).
        if concl.is_empty() {
            continue;
        }
        let body = rpn(&c.node).join(" ");
        helper_lines.push_str(&format!(
            "{hname} $p {} $= {body} $.\n",
            concl.join(" ")
        ));
        provisional.push((hname, c.sig, c.node.clone()));
    }
    if provisional.is_empty() {
        return None;
    }

    let marker = "$( ---- elaborator-emitted, kernel-checked proofs ---- $)";
    let mpos = src.find(marker)? + marker.len();
    let mut staged = String::with_capacity(src.len() + helper_lines.len() + 64);
    staged.push_str(&src[..mpos]);
    staged.push('\n');
    staged.push_str(&helper_lines);
    staged.push_str(&src[mpos..]);

    // Single reparse to learn every helper's mandatory-$f frame order.
    let db2 = Db::parse(&staged).ok()?;
    let mut helpers: HashMap<Sig, (String, Vec<String>)> = HashMap::new();
    for (hname, hsig, _node) in &provisional {
        let hst = db2.get(hname)?;
        let mut order = Vec::new();
        for hl in &hst.mand_hyps {
            let h = db2.get(hl)?;
            if h.kind != Kind::F {
                return None; // helper must be $f-only in hyps
            }
            order.push(hl.clone());
        }
        helpers.insert(*hsig, (hname.clone(), order));
    }

    // Rewrite every $p body (skip the helper lines themselves) by emitting
    // the source after the marker line-by-line.
    let mut out = String::with_capacity(staged.len());
    let head_end = staged.find(marker)? + marker.len();
    out.push_str(&staged[..head_end]);
    out.push('\n');
    let added = provisional.len();
    let helper_names: std::collections::HashSet<&str> =
        provisional.iter().map(|(h, _, _)| h.as_str()).collect();

    for raw in staged[head_end..].split('\n') {
        let line = raw.trim_start();
        if let (Some(p), Some(eq)) = (line.find(" $p "), line.find(" $= ")) {
            if p < eq {
                let name = line[..p].trim();
                let stmt = line[p + 4..eq].trim();
                let proofs =
                    line[eq + 4..].trim_end_matches(" $.").trim();
                if helper_names.contains(name) {
                    out.push_str(raw);
                    out.push('\n');
                    continue;
                }
                let plist: Vec<String> =
                    proofs.split_whitespace().map(|s| s.to_string()).collect();
                if let Some(tree) = rebuild(&db2, &plist) {
                    let nt = rewrite(&tree, &helpers);
                    let nb = rpn(&nt).join(" ");
                    let indent = &raw[..raw.len() - line.len()];
                    out.push_str(indent);
                    out.push_str(name);
                    out.push_str(" $p ");
                    out.push_str(stmt);
                    out.push_str(" $= ");
                    out.push_str(&nb);
                    out.push_str(" $.\n");
                    continue;
                }
            }
        }
        out.push_str(raw);
        out.push('\n');
    }
    while out.ends_with("\n\n") {
        out.pop();
    }

    Some((out, base + added, added))
}

/// Run batched CSE rounds to a fixpoint.  Every produced source is
/// parse-checked here; the caller re-verifies the final result with the
/// kernel and discards it entirely (reporting the un-crunched figure) if
/// it does not check or any conclusion drifted.
pub fn crunch(src: &str) -> String {
    // Wall-clock budget: each round is a full-corpus reparse + tree
    // rebuild, and this corpus has multi-million-node `$p` proofs, so an
    // unbounded fixpoint can run for many minutes.  Stopping early only
    // yields a *less* aggressively shared (but still valid) DAG — the
    // caller kernel-verifies whatever we return, so a budget cut can
    // never affect soundness, only how small the reported figure gets.
    let budget = std::time::Duration::from_secs(
        std::env::var("CSE_BUDGET_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(180),
    );
    let start = std::time::Instant::now();
    let mut cur = src.to_string();
    let mut base = 0usize;
    let mut prev_total = total(&cur);
    for round in 0..60 {
        if start.elapsed() >= budget {
            eprintln!(
                "  [cse] time budget reached after {round} round(s); \
                 returning best DAG so far (kernel re-verified by caller)"
            );
            break;
        }
        match one_round(&cur, base) {
            Some((next, nb, _added)) => {
                if Db::parse(&next).is_err() {
                    break;
                }
                let t = total(&next);
                if t >= prev_total {
                    break; // no further profit; keep last good
                }
                cur = next;
                base = nb;
                prev_total = t;
            }
            None => break,
        }
    }
    cur
}

fn total(src: &str) -> usize {
    Db::parse(src)
        .map(|d| {
            d.stmts
                .iter()
                .filter(|s| s.kind == Kind::P)
                .map(|s| s.proof.len())
                .sum()
        })
        .unwrap_or(usize::MAX)
}
