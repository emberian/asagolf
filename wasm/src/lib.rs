//! WASM shim over the asagolf trust-root kernel.
//!
//! `../src/kernel.rs` is included **verbatim** via `#[path]` — its
//! verification semantics are byte-for-byte the native ones; this file adds
//! only a thin JS-facing surface (parse → verify → label lookup). No kernel
//! logic lives here. If `verify()` says Ok, the same soundness guarantee the
//! native binary gives holds in the browser.

// The trust root, unchanged. The `#[cfg(test)] mod tests` inside it is
// inert without `--cfg test`, so this is a faithful, complete inclusion of
// the verifier and nothing else.
#[path = "../../src/kernel.rs"]
mod kernel;

use kernel::{Db, Kind};
use std::cell::RefCell;
use wasm_bindgen::prelude::*;

// Memoized parse for repeated single-statement `lookup` browsing only.
// `verify` / `parse_summary` deliberately never touch this — each of those
// re-parses from scratch so a re-verify is always a clean re-derivation,
// preserving the trust semantics. The cache key is (len, fnv1a) of the
// source; a hit means byte-identical input, so the parsed DB is the same
// one `Db::parse` would produce.
thread_local! {
    static PARSE_CACHE: RefCell<Option<(u64, Db)>> = const { RefCell::new(None) };
}

fn src_key(src: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in src.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    (src.len() as u64) ^ h.rotate_left(32)
}

/// Run `f` against a parsed view of `src`, parsing at most once per distinct
/// source. Used only by the read-only `lookup`.
fn with_parsed<R>(src: &str, f: impl FnOnce(&Db) -> R) -> Result<R, String> {
    let key = src_key(src);
    PARSE_CACHE.with(|c| {
        {
            let cur = c.borrow();
            if let Some((k, db)) = cur.as_ref() {
                if *k == key {
                    return Ok(f(db));
                }
            }
        }
        let db = Db::parse(src)?;
        let r = f(&db);
        *c.borrow_mut() = Some((key, db));
        Ok(r)
    })
}

fn kind_str(k: &Kind) -> &'static str {
    match k {
        Kind::F => "$f",
        Kind::E => "$e",
        Kind::A => "$a",
        Kind::P => "$p",
    }
}

/// JSON-escape a string (we hand-roll tiny JSON to avoid a serde dependency
/// in the trust-adjacent shim).
fn jstr(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

/// Parse a `.mm` source string and run the kernel's `verify()` over every
/// `$p`. Returns a JSON object:
///
/// `{"ok":true,"statements":N,"provable":M}` on success, or
/// `{"ok":false,"error":"...","stage":"parse"|"verify"}` on rejection.
///
/// This is the genuine trust boundary made interactive: the verdict is
/// exactly what the native kernel would return for the same bytes.
#[wasm_bindgen]
pub fn verify(src: &str) -> String {
    let db = match Db::parse(src) {
        Ok(db) => db,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"stage\":\"parse\",\"error\":{}}}",
                jstr(&e)
            )
        }
    };
    let n_stmts = db.stmts.len();
    let n_prov = db.stmts.iter().filter(|s| s.kind == Kind::P).count();
    match db.verify() {
        Ok(()) => format!(
            "{{\"ok\":true,\"statements\":{},\"provable\":{}}}",
            n_stmts, n_prov
        ),
        Err(e) => format!(
            "{{\"ok\":false,\"stage\":\"verify\",\"statements\":{},\"provable\":{},\"error\":{}}}",
            n_stmts, n_prov, jstr(&e)
        ),
    }
}

/// Parse once and return a JSON object of useful summary data plus a label
/// index, so the page can do parse+verify+browse with a single WASM call.
///
/// `{"ok":true,"statements":N,"provable":M,"verified":bool,
///   "error":<null|str>,"labels":["id","syl",...]}`
#[wasm_bindgen]
pub fn parse_summary(src: &str) -> String {
    let db = match Db::parse(src) {
        Ok(db) => db,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"stage\":\"parse\",\"error\":{}}}",
                jstr(&e)
            )
        }
    };
    let n_stmts = db.stmts.len();
    let n_prov = db.stmts.iter().filter(|s| s.kind == Kind::P).count();
    let (verified, err) = match db.verify() {
        Ok(()) => (true, "null".to_string()),
        Err(e) => (false, jstr(&e)),
    };
    let mut labels = String::from("[");
    for (i, s) in db.stmts.iter().enumerate() {
        if i > 0 {
            labels.push(',');
        }
        labels.push_str(&jstr(&s.label));
    }
    labels.push(']');
    format!(
        "{{\"ok\":true,\"statements\":{},\"provable\":{},\"verified\":{},\"error\":{},\"labels\":{}}}",
        n_stmts, n_prov, verified, err, labels
    )
}

/// Look up one label in the parsed DB. Returns
/// `{"ok":true,"label":"..","kind":"$p","statement":"|- ..",
///   "hyps":[..],"proof":[..],"proof_len":K}` or `{"ok":false,...}`.
///
/// `proof` (the stored RPN label list) is returned in full; the page lazily
/// renders it. For non-`$p` statements `proof` is `[]`.
#[wasm_bindgen]
pub fn lookup(src: &str, label: &str) -> String {
    let res = with_parsed(src, |db| match db.get(label) {
        None => format!(
            "{{\"ok\":false,\"error\":{}}}",
            jstr(&format!("unknown label {label}"))
        ),
        Some(s) => {
            let stmt = s.expr.join(" ");
            let hyps: Vec<String> = s.mand_hyps.iter().map(|h| jstr(h)).collect();
            let proof: Vec<String> = s.proof.iter().map(|p| jstr(p)).collect();
            format!(
                "{{\"ok\":true,\"label\":{},\"kind\":{},\"statement\":{},\"hyps\":[{}],\"proof\":[{}],\"proof_len\":{}}}",
                jstr(&s.label),
                jstr(kind_str(&s.kind)),
                jstr(&stmt),
                hyps.join(","),
                proof.join(","),
                s.proof.len()
            )
        }
    });
    match res {
        Ok(json) => json,
        Err(e) => format!("{{\"ok\":false,\"stage\":\"parse\",\"error\":{}}}", jstr(&e)),
    }
}

/// Version/identity marker so the page can show which kernel it loaded.
#[wasm_bindgen]
pub fn kernel_id() -> String {
    "asagolf sound Metamath-subset kernel (src/kernel.rs, unchanged) → wasm32".to_string()
}
