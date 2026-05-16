#!/usr/bin/env bash
# Build the embedded-prover artifacts for docs/:
#   1. compile the unchanged kernel (src/kernel.rs) to wasm via the
#      standalone wasm/ crate  ->  docs/assets/wasmpkg/
#   2. (re)emit the genuine no-cheating DB and ship it gzipped
#
# This does NOT touch `cargo build --release` of the main crate, the
# binaries, or the 88-verify: the wasm/ crate is independent.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> wasm-pack build (kernel -> wasm32)"
if ! command -v wasm-pack >/dev/null 2>&1; then
  echo "ERROR: wasm-pack not found. Install: cargo install wasm-pack" >&2
  echo "       (and: rustup target add wasm32-unknown-unknown)" >&2
  exit 1
fi
wasm-pack build wasm --release --target web --out-dir ../docs/assets/wasmpkg
# wasm-pack drops a '*'-only .gitignore in the pkg dir; we ship the pkg.
rm -f docs/assets/wasmpkg/.gitignore

echo "==> emit + gzip the genuine no-cheating DB"
cargo run --release --bin grounded -- data/grounded.mm >/dev/null
gzip -9 -c data/grounded.out.mm > docs/data/grounded.out.mm.gz

echo "==> done"
ls -la docs/assets/wasmpkg/*.wasm docs/data/grounded.out.mm.gz
