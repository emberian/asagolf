//! Sound common-subproof factoring (proof-DAG minimizer).
//!
//! Operates *only* on the kernel's parsed database and the flat RPN proof
//! lists.  It introduces extra `$p` helper lemmas for frequently-occurring,
//! self-contained ("closed": no local `$e` hypothesis leaf) subproofs and
//! rewrites every occurrence to a single call.  Statements of the original
//! `$p`s are never touched, so the only correctness obligation is that the
//! rewritten database still kernel-verifies — which the caller checks, and
//! which, if it ever failed, makes us discard the whole pass and keep the
//! original source.  Soundness therefore reduces entirely to the kernel.
//!
//! `shared_total` = Σ stored RPN length over every `$p`.  A subproof S of
//! RPN length L occurring k times, with v distinct free `$f` variables,
//! becomes one helper of length L plus k calls of length v+1: net change
//! L + k·(v+1) − k·L, strongly negative for the deeply-shared algebra
//! subproofs in this corpus.
//!
//! Each round extracts a *batch* of non-overlapping profitable patterns in
//! a single reparse (the assembled source is large; per-helper reparsing
//! would be quadratic).  Helpers are themselves `$p`, so later rounds CSE
//! them too; we iterate to a fixpoint.

use crate::kernel::{Db, Kind};
use std::collections::HashMap;

#[derive(Clone)]
struct Node {
    label: String,
    kids: Vec<Node>,
}

fn arity(db: &Db, label: &str) -> Option<usize> {
    let s = db.get(label)?;
    Some(match s.kind {
        Kind::F | Kind::E => 0,
        Kind::A | Kind::P => s.mand_hyps.len(),
    })
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
        stack.push(Node { label: lbl.clone(), kids });
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
/// Structural signature = RPN string (kernel is deterministic on it).
fn sig(n: &Node) -> String {
    rpn(n).join(" ")
}

/// Tally every closed subtree (no `$e` leaf anywhere inside).  Returns the
/// shared bool "subtree references an $e leaf" for the caller's recursion.
fn collect(
    db: &Db,
    n: &Node,
    table: &mut HashMap<String, (usize, Node)>,
) -> bool {
    let self_e = matches!(db.get(&n.label).map(|s| &s.kind), Some(Kind::E));
    let mut any_e = self_e;
    for k in &n.kids {
        any_e |= collect(db, k, table);
    }
    if !any_e && !n.kids.is_empty() {
        let e = table.entry(sig(n)).or_insert_with(|| (0, n.clone()));
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

/// Multi-pattern top-down rewrite: if this node's signature is a chosen
/// helper, splice in the call (helper label preceded by its $f-arg leaves
/// in the helper's kernel-frame order); else recurse into kids.  Top-down
/// so a replaced subtree is never descended into (no double rewrite).
fn rewrite(n: &Node, helpers: &HashMap<String, (String, Vec<String>)>) -> Node {
    if let Some((hname, fvar_order)) = helpers.get(&sig(n)) {
        let kids = fvar_order
            .iter()
            .map(|fl| Node { label: fl.clone(), kids: vec![] })
            .collect();
        return Node { label: hname.clone(), kids };
    }
    Node {
        label: n.label.clone(),
        kids: n.kids.iter().map(|k| rewrite(k, helpers)).collect(),
    }
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

    let mut table: HashMap<String, (usize, Node)> = HashMap::new();
    for (_, t) in &trees {
        collect(&db, t, &mut table);
    }

    // Profitable candidates: net = (L-(v+1))*k - L > 0, k >= 2.
    struct Cand {
        sig: String,
        node: Node,
        len: usize,
        net: i64,
    }
    let mut cands: Vec<Cand> = Vec::new();
    for (s, (k, node)) in &table {
        if *k < 2 {
            continue;
        }
        let l = rpn(node).len();
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
        cands.push(Cand { sig: s.clone(), node: node.clone(), len: l, net });
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
    let mut provisional: Vec<(String, String, Node)> = Vec::new(); // hname, sig, node
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
        provisional.push((hname, c.sig.clone(), c.node.clone()));
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
    let mut helpers: HashMap<String, (String, Vec<String>)> = HashMap::new();
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
        helpers.insert(hsig.clone(), (hname.clone(), order));
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
/// kernel and discards it entirely if it does not check.
pub fn crunch(src: &str) -> String {
    let mut cur = src.to_string();
    let mut base = 0usize;
    let mut prev_total = total(&cur);
    for _ in 0..60 {
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
