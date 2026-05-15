//! Parse + kernel-verify the Birkhoff F0 database.
//! Usage: cargo run --release --bin prove

#[path = "../kernel.rs"]
mod kernel;

use std::process::exit;

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "data/birkhoff.mm".into());
    let path = path.as_str();
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            exit(1);
        }
    };
    let db = match kernel::Db::parse(&src) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("PARSE ERROR: {e}");
            exit(1);
        }
    };
    let n_ax = db
        .stmts
        .iter()
        .filter(|s| s.kind == kernel::Kind::A)
        .count();
    let n_p = db
        .stmts
        .iter()
        .filter(|s| s.kind == kernel::Kind::P)
        .count();
    println!(
        "parsed {} statements: {} axioms ($a), {} theorems ($p)",
        db.stmts.len(),
        n_ax,
        n_p
    );
    match db.verify() {
        Ok(()) => println!("KERNEL: all {n_p} proof(s) verified ✔"),
        Err(e) => {
            eprintln!("KERNEL REJECTED: {e}");
            exit(1);
        }
    }
}
