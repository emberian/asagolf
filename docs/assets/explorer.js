/**
 * explorer.js — the interactive, embedded-prover theorem explorer.
 *
 *   • "Re-verify in your browser": loads the shipped genuine no-cheating DB
 *     (grounded.out.mm.gz, the shared-DAG proof — NOT the cut-free expansion),
 *     runs the real WASM kernel in a Worker, shows the true verdict + timing.
 *     This is the project's trust boundary made interactive: a visitor's own
 *     browser re-derives every $p from the axioms. A tampered byte → REJECT.
 *
 *   • Theorem browser: pick any lemma → statement / kind / deps / inlined-vs-
 *     shared sizes (from site.json) / stored RPN proof (from the live WASM
 *     lookup over the shipped DB). Dependencies are click-through.
 *
 * Graceful fallback if WASM / Worker / DecompressionStream is unavailable:
 * a clearly-labelled static-snapshot notice plus the local re-verify command.
 */

const REVERIFY_CMD = 'cargo run --release --bin grounded -- data/grounded.mm';

function esc(s) {
  return String(s ?? '')
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}
function fmtNum(n) {
  return n == null ? '—' : Number(n).toLocaleString('en-US');
}

// Feature detection for the genuine in-browser path.
function wasmSupported() {
  return (
    typeof WebAssembly === 'object' &&
    typeof Worker === 'function' &&
    typeof DecompressionStream === 'function'
  );
}

let worker = null;
function getWorker() {
  if (worker) return worker;
  worker = new Worker('assets/verify-worker.js', { type: 'module' });
  return worker;
}

// ─── Re-verify panel ─────────────────────────────────────────────────────────

function renderReverify(data) {
  const host = document.getElementById('reverify-body');
  if (!host) return;

  const h = data.headline || {};
  const supported = wasmSupported();

  host.innerHTML = `
    <p class="rv-intro">
      The headline numbers on this page are emitted by a run of the sound
      Metamath-subset kernel. You don't have to trust that run. The button
      below loads the <strong>genuine no-cheating database</strong> shipped
      with this site and re-checks it <em>in your browser</em>, with the
      <strong>same kernel code</strong> (<code>src/kernel.rs</code>, compiled
      to WebAssembly, verification semantics unchanged). If it says
      <code>verified</code>, every one of the
      <strong>${fmtNum(h.lemmas ?? 87)}</strong> staged
      <code>$p</code> was re-derived from the axioms, in your tab.
    </p>
    <p class="rv-note">
      What is re-checked: the assembled <strong>shared-DAG</strong> proof
      (lemma reuse — the real, shippable artifact, ~0.8&nbsp;MB gzipped). The
      fully-inlined cut-free expansion is 10<sup>7</sup>+ nodes
      <em>by design</em> and is <strong>reported, never materialized</strong>
      — the cut-free counts come from the size cruncher, not from expanding
      anything here.
    </p>
    <div class="rv-controls">
      <button id="rv-run" class="rv-btn"${supported ? '' : ' disabled'}>
        ▶ Re-verify in your browser
      </button>
      <span id="rv-state" class="rv-state" role="status" aria-live="polite"></span>
    </div>
    <div id="rv-output" class="rv-output" hidden></div>
    ${supported ? '' : `
      <div class="rv-fallback">
        <strong>Static snapshot.</strong> This browser lacks
        <code>WebAssembly</code>/<code>Worker</code>/<code>DecompressionStream</code>,
        so the live re-verify is unavailable. The numbers shown are from the
        kernel run that generated this page. To re-verify locally:
        <pre><code>${esc(REVERIFY_CMD)}</code></pre>
        (prints <code>Kernel: verified all 88 staged lemmas ✔</code>).
      </div>`}
  `;

  if (!supported) return;

  const btn = document.getElementById('rv-run');
  const stateEl = document.getElementById('rv-state');
  const outEl = document.getElementById('rv-output');

  btn.addEventListener('click', () => {
    btn.disabled = true;
    btn.textContent = '⏳ verifying…';
    stateEl.textContent = '';
    outEl.hidden = true;
    outEl.className = 'rv-output';

    const w = getWorker();
    const t0 = performance.now();

    const onMsg = (ev) => {
      const m = ev.data;
      if (m.type === 'status') {
        stateEl.textContent = m.msg;
      } else if (m.type === 'result') {
        w.removeEventListener('message', onMsg);
        btn.disabled = false;
        btn.textContent = '▶ Re-verify again';
        const v = m.verdict;
        const wall = ((performance.now() - t0) / 1000).toFixed(1);
        if (v.ok && v.verified) {
          stateEl.textContent = '';
          outEl.classList.add('rv-ok');
          outEl.innerHTML = `
            <div class="rv-verdict rv-verdict-ok">✔ verified all
              ${fmtNum(v.provable)} staged <code>$p</code></div>
            <div class="rv-detail">
              kernel re-derived every provable statement from the axioms;
              database = <strong>${fmtNum(v.statements)}</strong> statements.
              Wall time ≈ <strong>${wall}s</strong>
              (kernel ${fmtNum(m.ms)} ms).
            </div>
            <div class="rv-kernel">${esc(m.kernelId)}</div>
            <div class="rv-detail rv-tamper-hint">
              This is real. Edit one token of
              <code>docs/data/grounded.out.mm</code>, rebuild the gzip, reload
              — the verdict flips to a precise rejection. A re-verify that
              always says ✔ would be a fake.
            </div>`;
        } else {
          outEl.classList.add('rv-bad');
          const err = v.error ? esc(v.error) : '(no detail)';
          outEl.innerHTML = `
            <div class="rv-verdict rv-verdict-bad">✗ REJECTED
              (${esc(v.stage || 'verify')})</div>
            <div class="rv-detail">
              The shipped database did <strong>not</strong> verify. The
              kernel's exact objection:
            </div>
            <pre class="rv-err">${err}</pre>
            <div class="rv-detail">
              (If you see this on the unmodified site, that is itself the
              honest signal — the kernel is not rubber-stamping.)
            </div>`;
        }
        outEl.hidden = false;
      } else if (m.type === 'error') {
        w.removeEventListener('message', onMsg);
        btn.disabled = false;
        btn.textContent = '▶ Re-verify in your browser';
        stateEl.textContent = '';
        outEl.classList.add('rv-bad');
        outEl.innerHTML = `
          <div class="rv-verdict rv-verdict-bad">⚠ could not run</div>
          <div class="rv-detail">${esc(m.msg)}</div>
          <div class="rv-fallback">
            Re-verify locally instead:
            <pre><code>${esc(REVERIFY_CMD)}</code></pre>
          </div>`;
        outEl.hidden = false;
      }
    };
    w.addEventListener('message', onMsg);
    w.postMessage({ type: 'verify' });
  });
}

// ─── Theorem browser ─────────────────────────────────────────────────────────

let browserState = { lemmas: [], byName: new Map(), proofCache: new Map() };

function renderBrowser(data) {
  const lemmas = data.lemmas || [];
  browserState.lemmas = lemmas;
  browserState.byName = new Map(lemmas.map(l => [l.name, l]));

  const sel = document.getElementById('tb-select');
  const out = document.getElementById('tb-detail');
  if (!sel || !out) return;

  sel.innerHTML = '<option value="">— pick a lemma —</option>' +
    lemmas.map(l =>
      `<option value="${esc(l.name)}">${esc(l.name)} · ${esc(l.kind)}</option>`
    ).join('');

  sel.addEventListener('change', () => selectLemma(sel.value));

  // Deep-link / cross-nav via location hash (#thm=NAME)
  const fromHash = () => {
    const m = /thm=([^&]+)/.exec(location.hash);
    if (m) {
      const name = decodeURIComponent(m[1]);
      if (browserState.byName.has(name)) {
        sel.value = name;
        selectLemma(name, false);
      }
    }
  };
  window.addEventListener('hashchange', fromHash);
  fromHash();
}

function selectLemma(name, updateHash = true) {
  const out = document.getElementById('tb-detail');
  if (!out) return;
  const l = browserState.byName.get(name);
  if (!l) { out.hidden = true; return; }

  if (updateHash) {
    history.replaceState(null, '', `#thm=${encodeURIComponent(name)}`);
  }

  const depLinks = (l.deps && l.deps.length)
    ? l.deps.map(d => {
        const known = browserState.byName.has(d);
        return known
          ? `<a href="#thm=${encodeURIComponent(d)}" class="tb-dep"
                data-dep="${esc(d)}"><code>${esc(d)}</code></a>`
          : `<code class="tb-dep-axiom" title="axiom / hypothesis (no proof)">${esc(d)}</code>`;
      }).join(' ')
    : '<span class="text-muted">none</span>';

  const essHtml = (l.ess && l.ess.length)
    ? `<ul class="ess-list">${l.ess.map(e => `<li><code>${esc(e)}</code></li>`).join('')}</ul>`
    : '<span class="text-muted">none</span>';

  const ratio = (l.inlined && l.shared)
    ? (l.inlined / l.shared >= 1
        ? `${(l.inlined / l.shared).toFixed(1)}× smaller shared`
        : `${(l.shared / l.inlined).toFixed(1)}× larger shared`)
    : '—';

  out.innerHTML = `
    <h3><code>${esc(l.name)}</code>
      <span class="kind-badge kind-${esc((l.kind||'').toLowerCase())}"
            style="margin-left:.5rem">${esc(l.kind)}</span></h3>
    <dl class="lemma-detail-grid">
      <dt>Statement</dt><dd><code>${esc(l.statement)}</code></dd>
      <dt>Hypotheses</dt><dd>${essHtml}</dd>
      <dt>Depends on</dt><dd class="tb-deps">${depLinks}</dd>
      <dt>Inlined (cut-free)</dt><dd><code>${fmtNum(l.inlined)}</code>
        ${l.inlined_log10 != null ? ` ≈ 10<sup>${Number(l.inlined_log10).toFixed(2)}</sup>` : ''}</dd>
      <dt>Shared (DAG)</dt><dd><code>${fmtNum(l.shared)}</code> &nbsp;(${esc(ratio)})</dd>
    </dl>
    <div class="tb-proof-wrap">
      <button class="rv-btn rv-btn-sm" id="tb-proof-btn"
        ${wasmSupported() ? '' : 'disabled title="WASM unavailable — proof shown after local build"'}>
        Show stored proof (RPN) from the shipped DB
      </button>
      <span id="tb-proof-state" class="rv-state"></span>
      <pre id="tb-proof" class="tb-proof" hidden></pre>
    </div>
  `;
  out.hidden = false;

  // Wire dependency click-through (anchor href already does it; keep select in sync)
  out.querySelectorAll('a.tb-dep').forEach(a => {
    a.addEventListener('click', () => {
      const d = a.dataset.dep;
      const sel = document.getElementById('tb-select');
      if (sel) sel.value = d;
    });
  });

  const pbtn = document.getElementById('tb-proof-btn');
  if (pbtn && wasmSupported()) {
    pbtn.addEventListener('click', () => loadProof(name));
  }
}

function loadProof(name) {
  const pre = document.getElementById('tb-proof');
  const st = document.getElementById('tb-proof-state');
  const btn = document.getElementById('tb-proof-btn');
  if (!pre) return;

  if (browserState.proofCache.has(name)) {
    showProof(name, browserState.proofCache.get(name));
    return;
  }
  btn.disabled = true;
  st.textContent = 'loading kernel + DB (first lookup decompresses the 51 MB corpus)…';

  const w = getWorker();
  const onMsg = (ev) => {
    const m = ev.data;
    if (m.type === 'status') {
      st.textContent = m.msg;
    } else if (m.type === 'lookup' && m.label === name) {
      w.removeEventListener('message', onMsg);
      btn.disabled = false;
      st.textContent = '';
      browserState.proofCache.set(name, m.data);
      showProof(name, m.data);
    } else if (m.type === 'error') {
      w.removeEventListener('message', onMsg);
      btn.disabled = false;
      st.textContent = 'lookup failed: ' + (m.msg || 'error');
    }
  };
  w.addEventListener('message', onMsg);
  w.postMessage({ type: 'lookup', label: name });
}

function showProof(name, d) {
  const pre = document.getElementById('tb-proof');
  const st = document.getElementById('tb-proof-state');
  if (!pre) return;
  if (!d || !d.ok) {
    pre.textContent = (d && d.error) || 'not found';
    pre.hidden = false;
    return;
  }
  const proof = d.proof || [];
  st.innerHTML = `<span class="text-muted">${proof.length.toLocaleString()} RPN steps
    · kind ${esc(d.kind)} · live from the in-browser kernel's parse of the shipped DB</span>`;
  // Lazy / chunked render: huge proofs (G4-sas ≈ 2.8k labels here, but the
  // cut-free expansion is 10^7 — never shown) are wrapped, not pretty-printed.
  const MAX = 6000;
  const head = proof.slice(0, MAX).join(' ');
  pre.textContent = head + (proof.length > MAX
    ? `\n\n… (${(proof.length - MAX).toLocaleString()} more labels truncated for display; this is the shared-DAG proof — the cut-free expansion is reported by the size cruncher, never expanded here)`
    : '');
  pre.hidden = false;
}

export function initExplorer(data) {
  try { renderReverify(data); } catch (e) { console.warn('[explorer] reverify:', e); }
  try { renderBrowser(data); } catch (e) { console.warn('[explorer] browser:', e); }
}
