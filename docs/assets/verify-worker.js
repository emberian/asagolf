/**
 * verify-worker.js — runs the real WASM kernel off the main thread.
 *
 * The kernel verify over the genuine 51 MB shared-DAG corpus takes ~20 s of
 * pure compute; doing it here keeps the page responsive. The worker loads
 * `../data/grounded.out.mm.gz`, decompresses it, instantiates the unchanged
 * `src/kernel.rs` (compiled to wasm), and runs `verify()` / `parse_summary()`.
 *
 * Messages in:  {type:'verify'}            -> full re-verify of shipped corpus
 *               {type:'lookup', label}     -> single-statement lookup
 * Messages out: {type:'status', stage, msg}
 *               {type:'result', verdict, stmts, prov, ms, kernelId}
 *               {type:'lookup', label, data}
 *               {type:'error', msg}
 */

let wasmMod = null;     // { verify, parse_summary, lookup, kernel_id }
let corpus = null;      // decompressed .mm source string (cached)

async function ensureWasm() {
  if (wasmMod) return wasmMod;
  postMessage({ type: 'status', stage: 'wasm', msg: 'loading kernel (wasm)…' });
  const m = await import('./wasmpkg/asagolf_kernel_wasm.js');
  await m.default(); // fetches asagolf_kernel_wasm_bg.wasm relative to the module
  wasmMod = m;
  return m;
}

async function ensureCorpus() {
  if (corpus) return corpus;
  postMessage({ type: 'status', stage: 'fetch', msg: 'fetching genuine no-cheating DB…' });
  const r = await fetch('../data/grounded.out.mm.gz');
  if (!r.ok) throw new Error(`corpus fetch failed: HTTP ${r.status}`);
  const gz = await r.arrayBuffer();

  postMessage({ type: 'status', stage: 'decompress', msg: 'decompressing corpus…' });
  let bytes;
  if (typeof DecompressionStream === 'function') {
    const ds = new DecompressionStream('gzip');
    const stream = new Response(gz).body.pipeThrough(ds);
    bytes = new Uint8Array(await new Response(stream).arrayBuffer());
  } else {
    throw new Error('DecompressionStream unavailable in this browser');
  }
  corpus = new TextDecoder('utf-8').decode(bytes);
  return corpus;
}

self.onmessage = async (ev) => {
  const { type } = ev.data || {};
  try {
    if (type === 'verify') {
      const m = await ensureWasm();
      const src = await ensureCorpus();
      postMessage({
        type: 'status', stage: 'verify',
        msg: `re-deriving every $p from the axioms (${src.length.toLocaleString()} chars)…`
      });
      const t0 = performance.now();
      const out = JSON.parse(m.parse_summary(src));
      const ms = Math.round(performance.now() - t0);
      postMessage({
        type: 'result',
        verdict: out,
        ms,
        kernelId: m.kernel_id(),
      });
    } else if (type === 'lookup') {
      const m = await ensureWasm();
      const src = await ensureCorpus();
      const data = JSON.parse(m.lookup(src, ev.data.label));
      postMessage({ type: 'lookup', label: ev.data.label, data });
    } else {
      postMessage({ type: 'error', msg: `unknown message type: ${type}` });
    }
  } catch (e) {
    postMessage({ type: 'error', msg: String(e && e.message || e) });
  }
};
