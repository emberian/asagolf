/**
 * asagolf — app.js  (ES module, no bundler, no framework)
 *
 * Loads site.json (with site.sample.json fallback), then renders:
 *   1. Hero stats
 *   2. Results table + log-scale bar
 *   3. Proof DAG (Cytoscape.js, CDN, with table fallback)
 *   4. Lemma table (sortable, filterable, click-to-detail)
 *   5. Model variation controls
 */

// ─── Data loading ────────────────────────────────────────────────────────────

async function loadData() {
  for (const path of ['data/site.json', 'data/site.sample.json']) {
    try {
      const r = await fetch(path);
      if (!r.ok) throw new Error(`HTTP ${r.status}`);
      const data = await r.json();
      console.info(`[asagolf] loaded ${path}`);
      return data;
    } catch (e) {
      console.warn(`[asagolf] ${path} unavailable: ${e.message}`);
    }
  }
  throw new Error('Neither site.json nor site.sample.json could be loaded.');
}

// ─── Helpers ─────────────────────────────────────────────────────────────────

/** Format a number with thousands-separators */
function fmtNum(n) {
  if (n == null) return '—';
  return Number(n).toLocaleString('en-US');
}

/** Format log10 value like "10^6.86" */
function fmtLog(log10) {
  if (log10 == null) return '—';
  return `10<sup>${Number(log10).toFixed(2)}</sup>`;
}

/** Plain-text version for non-innerHTML contexts */
function fmtLogText(log10) {
  if (log10 == null) return '—';
  return `10^${Number(log10).toFixed(2)}`;
}

/** Escape HTML special chars */
function esc(s) {
  return String(s ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * CSS class name for a node/row kind.
 * Maps the kind string from the data to a CSS class suffix.
 */
function kindClass(kind) {
  return 'kind-' + (kind ?? 'demo').toLowerCase().replace(/[^a-z]/g, '');
}

/**
 * Color to use in Cytoscape for a given kind.
 * Must match the CSS variables defined in styles.css.
 */
const KIND_COLORS = {
  postulate: '#0d6efd',
  ring:      '#198754',
  order:     '#fd7e14',
  prop:      '#6f42c1',
  eqlogic:   '#20c997',
  axiom:     '#dc3545',
  claim:     '#dc3545',
  geometry:  '#0d6efd',
  substrate: '#fd7e14',
  demo:      '#adb5bd',
};

function kindColor(kind) {
  return KIND_COLORS[(kind ?? '').toLowerCase()] ?? '#adb5bd';
}

// ─── 1. Hero ─────────────────────────────────────────────────────────────────

function renderHero(data) {
  const h = data.headline;

  // Stat cards already stamped in HTML with data-stat attributes;
  // fill them in now.
  const fill = (selector, value) => {
    const el = document.querySelector(selector);
    if (el) el.textContent = value;
  };

  fill('#stat-f0',      fmtNum(h.f0_asa));
  fill('#stat-g4',      fmtNum(h.g4_sas_inlined));
  fill('#stat-log',     `~10^${Number(h.g4_sas_log10).toFixed(2)}`);
  fill('#stat-lemmas',  fmtNum(h.lemmas));
  fill('#stat-stmts',   fmtNum(h.db_statements));

  // Update generated date
  const genEl = document.getElementById('generated-date');
  if (genEl && data.generated) {
    genEl.textContent = data.generated.split('T')[0];
  }
}

// ─── 2. Results table + log-scale bar ────────────────────────────────────────

function renderResults(data) {
  renderResultsTable(data.models);
  renderLogScale(data.models);
}

function renderResultsTable(models) {
  const tbody = document.getElementById('results-tbody');
  if (!tbody) return;

  tbody.innerHTML = models.map(m => {
    const exact = m.log10 < 10
      ? ` (${fmtNum(Math.round(Math.pow(10, m.log10)))} exact)`
      : '';
    return `
      <tr>
        <td>${esc(m.label)}</td>
        <td><span class="kind-badge ${kindClass(m.kind)}">${esc(m.kind)}</span></td>
        <td class="num-cell"><span>${fmtLogText(m.log10)}</span></td>
        <td>${esc(m.note)}${exact}</td>
      </tr>`;
  }).join('');
}

/**
 * Render a horizontal log-scale bar from 10^0 to 10^1000,
 * with coloured markers for each model.
 */
function renderLogScale(models) {
  const container = document.getElementById('log-scale-track');
  if (!container) return;

  const LOG_MIN = 0;
  const LOG_MAX = 1000;
  const range = LOG_MAX - LOG_MIN;

  /** Map a log10 value to a percentage left position */
  const pct = (log10) => ((log10 - LOG_MIN) / range) * 100;

  const MARKER_COLORS = {
    geometry:  '#3b82f6',
    substrate: '#f97316',
    claim:     '#ef4444',
  };

  // Sort models so labels don't stack on top of each other
  const sorted = [...models].sort((a, b) => a.log10 - b.log10);

  // Build markers HTML
  let markersHtml = '';
  sorted.forEach((m, i) => {
    const left = pct(m.log10).toFixed(2);
    const color = MARKER_COLORS[m.kind] ?? '#8b949e';
    const label = `${m.label}: ${fmtLogText(m.log10)}`;
    // Alternate label side to reduce overlap for very close markers
    markersHtml += `
      <div
        class="log-scale-marker"
        role="presentation"
        data-label="${esc(label)}"
        title="${esc(label)}"
        style="left:${left}%; background:${color};"
        aria-label="${esc(label)}"
      ></div>`;
  });

  container.innerHTML = markersHtml;

  // Also update the axis labels
  const axis = document.getElementById('log-scale-axis');
  if (axis) {
    // Ticks at 0, 50, 100, 250, 500, 750, 1000
    const ticks = [0, 50, 100, 250, 500, 750, 1000];
    axis.innerHTML = ticks.map(t => {
      const p = pct(t).toFixed(1);
      return `<span style="position:absolute;left:${p}%;transform:translateX(-50%)">10<sup>${t}</sup></span>`;
    }).join('');
  }
}

// ─── 3. Proof DAG ─────────────────────────────────────────────────────────────

/**
 * Build Cytoscape elements from dag nodes/edges plus any lemma data
 * (for node sizing from lemma.inlined when not in dag.nodes).
 */
function buildCyElements(dag, lemmaMap) {
  const elements = [];

  // Nodes
  for (const n of dag.nodes) {
    const lemma = lemmaMap.get(n.id);
    const size = n.size ?? lemma?.inlined ?? 1;
    // Log-scale node size: min 24, max 80
    const logSize = Math.log10(Math.max(size, 1));
    const maxLog = Math.log10(10_000_000); // 10^7
    const nodeSize = 24 + 56 * Math.min(1, logSize / maxLog);

    elements.push({
      data: {
        id: n.id,
        label: n.id,
        kind: n.kind ?? lemma?.kind ?? 'unknown',
        size: size,
        nodeSize: Math.round(nodeSize),
        color: kindColor(n.kind ?? lemma?.kind),
        // Full lemma data for detail panel
        lemma: lemma ?? null,
      }
    });
  }

  // Edges
  for (const e of dag.edges) {
    elements.push({
      data: {
        id: `${e.from}__${e.to}`,
        source: e.from,
        target: e.to,
      }
    });
  }

  return elements;
}

let cyInstance = null;

async function renderDag(data) {
  const cyEl = document.getElementById('cy');
  const fallback = document.getElementById('dag-fallback');
  if (!cyEl) return;

  const lemmaMap = new Map(data.lemmas.map(l => [l.name, l]));
  const elements = buildCyElements(data.dag, lemmaMap);

  // Try loading Cytoscape from CDN
  let cy;
  try {
    if (!window.cytoscape) {
      await loadScript('https://unpkg.com/cytoscape@3/dist/cytoscape.min.js');
    }

    cy = window.cytoscape({
      container: cyEl,
      elements,
      style: [
        {
          selector: 'node',
          style: {
            'label':           'data(label)',
            'width':           'data(nodeSize)',
            'height':          'data(nodeSize)',
            'background-color':'data(color)',
            'font-size':       10,
            'text-valign':     'bottom',
            'text-margin-y':   4,
            'color':           'var(--clr-text, #212529)',
            'text-outline-color': 'var(--clr-surface, #fff)',
            'text-outline-width': 2,
            'text-outline-opacity': 1,
          }
        },
        {
          selector: 'edge',
          style: {
            'width':             2,
            'line-color':        '#8b949e',
            'target-arrow-color':'#8b949e',
            'target-arrow-shape':'triangle',
            'curve-style':       'bezier',
            'opacity':           0.7,
          }
        },
        {
          selector: 'node:selected',
          style: {
            'border-width': 3,
            'border-color': '#58a6ff',
          }
        }
      ],
      layout: {
        name: 'breadthfirst',
        directed: true,
        padding: 30,
        spacingFactor: 1.4,
      },
      wheelSensitivity: 0.3,
    });

    cyInstance = cy;

    // Click handler: show detail panel
    cy.on('tap', 'node', function(evt) {
      const node = evt.target;
      showDagDetail(node.data());
    });

    // Tap on background: close panel
    cy.on('tap', function(evt) {
      if (evt.target === cy) closeDagDetail();
    });

    renderDagLegend(data.dag);
    console.info('[asagolf] Cytoscape DAG rendered');

  } catch (err) {
    console.warn('[asagolf] Cytoscape unavailable, showing table fallback:', err.message);
    cyEl.classList.add('hidden');
    if (fallback) {
      fallback.classList.add('active');
      renderDagFallback(data.dag, lemmaMap, fallback);
    }
  }
}

function loadScript(src) {
  return new Promise((resolve, reject) => {
    const s = document.createElement('script');
    s.src = src;
    s.onload  = resolve;
    s.onerror = () => reject(new Error(`Failed to load: ${src}`));
    document.head.appendChild(s);
  });
}

function renderDagLegend(dag) {
  const legend = document.getElementById('dag-legend');
  if (!legend) return;

  // Collect unique kinds from DAG nodes
  const kinds = [...new Set(dag.nodes.map(n => n.kind).filter(Boolean))];
  legend.innerHTML = kinds.map(k => `
    <span class="dag-legend-item">
      <span class="dag-legend-dot" style="background:${kindColor(k)}"></span>
      ${esc(k)}
    </span>`).join('');
}

function showDagDetail(nodeData) {
  const panel = document.getElementById('detail-panel');
  if (!panel) return;

  const l = nodeData.lemma;
  const size = nodeData.size;

  let html = `
    <button class="close-btn" id="dag-detail-close" aria-label="Close detail panel">×</button>
    <h4><code>${esc(nodeData.id)}</code></h4>
    <dl>`;

  html += detailRow('Kind', `<span class="kind-badge ${kindClass(nodeData.kind)}">${esc(nodeData.kind)}</span>`);
  html += detailRow('Size (inlined)', `<code>${fmtNum(size)}</code>`);

  if (l) {
    html += detailRow('Statement', `<code>${esc(l.statement)}</code>`);

    if (l.ess && l.ess.length > 0) {
      html += detailRow('Hypotheses',
        `<ul class="ess-list">${l.ess.map(e => `<li><code>${esc(e)}</code></li>`).join('')}</ul>`);
    }

    if (l.deps && l.deps.length > 0) {
      html += detailRow('Deps', `<code>${esc(l.deps.join(', '))}</code>`);
    }

    if (l.inlined != null) html += detailRow('Inlined', `<code>${fmtNum(l.inlined)}</code>`);
    if (l.shared  != null) html += detailRow('Shared',  `<code>${fmtNum(l.shared)}</code>`);

    if (l.shrink_before != null || l.shrink_after != null) {
      html += detailRow('Shrink',
        `<code>${fmtNum(l.shrink_before)} → ${fmtNum(l.shrink_after)}</code>`);
    }

    if (l.blurb) {
      html += `</dl><div class="detail-blurb">${esc(l.blurb)}</div>`;
    } else {
      html += `</dl>`;
    }
  } else {
    html += `</dl>`;
  }

  panel.innerHTML = html;
  panel.classList.add('open');

  document.getElementById('dag-detail-close')?.addEventListener('click', closeDagDetail);
}

function detailRow(label, valueHtml) {
  return `<div class="detail-row"><dt>${esc(label)}</dt><dd>${valueHtml}</dd></div>`;
}

function closeDagDetail() {
  const panel = document.getElementById('detail-panel');
  panel?.classList.remove('open');
}

/** Fallback: render a sortable table of DAG nodes */
function renderDagFallback(dag, lemmaMap, container) {
  const rows = dag.nodes.map(n => {
    const l = lemmaMap.get(n.id);
    return `<tr>
      <td><code>${esc(n.id)}</code></td>
      <td><span class="kind-badge ${kindClass(n.kind)}">${esc(n.kind ?? '')}</span></td>
      <td class="num-cell">${fmtNum(n.size)}</td>
      <td class="stmt-cell monospace">${esc(l?.statement ?? '')}</td>
    </tr>`;
  }).join('');

  container.innerHTML = `
    <h3 class="mt-2">DAG nodes (Cytoscape unavailable)</h3>
    <div class="results-table-wrap mt-1">
      <table class="results-table" role="table">
        <thead>
          <tr>
            <th>Name</th><th>Kind</th><th>Inlined size</th><th>Statement</th>
          </tr>
        </thead>
        <tbody>${rows}</tbody>
      </table>
    </div>`;
}

// ─── 4. Lemma table ───────────────────────────────────────────────────────────

/** State for the lemma table */
const lemmaState = {
  data:    [],          // full lemma array from JSON
  sorted:  [],          // current display order
  sortKey: 'idx',
  sortAsc: true,
  filter:  '',
  selected: null,       // currently selected lemma name
};

function renderLemmaSection(lemmas) {
  lemmaState.data   = lemmas;
  lemmaState.sorted = [...lemmas];

  const filterInput = document.getElementById('lemma-filter');
  filterInput?.addEventListener('input', (e) => {
    lemmaState.filter = e.target.value.trim().toLowerCase();
    lemmaState.selected = null;
    refreshLemmaTable();
    closeLemmaDetail();
  });

  // Sort header click
  document.querySelectorAll('#lemma-table thead th[data-sort]').forEach(th => {
    th.addEventListener('click', () => {
      const key = th.dataset.sort;
      if (lemmaState.sortKey === key) {
        lemmaState.sortAsc = !lemmaState.sortAsc;
      } else {
        lemmaState.sortKey = key;
        lemmaState.sortAsc = true;
      }
      refreshLemmaTable();
      updateSortHeaders();
    });
    // Keyboard support
    th.setAttribute('tabindex', '0');
    th.setAttribute('role', 'columnheader');
    th.setAttribute('aria-sort', 'none');
    th.addEventListener('keydown', (e) => {
      if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); th.click(); }
    });
  });

  refreshLemmaTable();
}

function refreshLemmaTable() {
  const { data, sortKey, sortAsc, filter } = lemmaState;

  // Filter
  let rows = filter
    ? data.filter(l =>
        l.name.toLowerCase().includes(filter) ||
        (l.statement ?? '').toLowerCase().includes(filter) ||
        (l.kind ?? '').toLowerCase().includes(filter) ||
        (l.blurb ?? '').toLowerCase().includes(filter))
    : data;

  // Sort
  rows = [...rows].sort((a, b) => {
    const av = a[sortKey] ?? '';
    const bv = b[sortKey] ?? '';
    const cmp = typeof av === 'number' ? av - bv : String(av).localeCompare(String(bv));
    return sortAsc ? cmp : -cmp;
  });

  lemmaState.sorted = rows;

  const tbody = document.getElementById('lemma-tbody');
  if (!tbody) return;

  if (rows.length === 0) {
    tbody.innerHTML = `<tr><td colspan="6" class="text-muted" style="padding:1.5rem;text-align:center">No lemmas match the filter.</td></tr>`;
    return;
  }

  tbody.innerHTML = rows.map(l => `
    <tr
      data-name="${esc(l.name)}"
      class="${lemmaState.selected === l.name ? 'selected' : ''}"
      tabindex="0"
      role="row"
      aria-selected="${lemmaState.selected === l.name}"
    >
      <td class="num-cell">${esc(l.idx)}</td>
      <td><code>${esc(l.name)}</code></td>
      <td><span class="kind-badge ${kindClass(l.kind)}">${esc(l.kind)}</span></td>
      <td class="stmt-cell"><code>${esc(l.statement)}</code></td>
      <td class="num-cell">${fmtNum(l.inlined)}</td>
      <td class="num-cell">${fmtNum(l.shared)}</td>
    </tr>`).join('');

  // Row click/keyboard handlers
  tbody.querySelectorAll('tr[data-name]').forEach(row => {
    const select = () => {
      const name = row.dataset.name;
      const lemma = lemmaState.data.find(l => l.name === name);
      if (lemma) {
        lemmaState.selected = name;
        showLemmaDetail(lemma);
        refreshLemmaTable();
      }
    };
    row.addEventListener('click', select);
    row.addEventListener('keydown', (e) => {
      if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); select(); }
    });
  });
}

function updateSortHeaders() {
  document.querySelectorAll('#lemma-table thead th[data-sort]').forEach(th => {
    const isActive = th.dataset.sort === lemmaState.sortKey;
    th.classList.toggle('sorted', isActive);
    const ind = th.querySelector('.sort-indicator');
    if (ind) ind.textContent = isActive ? (lemmaState.sortAsc ? ' ▲' : ' ▼') : ' ⇅';
    th.setAttribute('aria-sort', isActive ? (lemmaState.sortAsc ? 'ascending' : 'descending') : 'none');
  });
}

function showLemmaDetail(l) {
  const panel = document.getElementById('lemma-detail');
  if (!panel) return;

  const essHtml = (l.ess && l.ess.length > 0)
    ? `<ul class="ess-list">${l.ess.map(e => `<li><code>${esc(e)}</code></li>`).join('')}</ul>`
    : '<span class="text-muted">none</span>';

  const depsHtml = (l.deps && l.deps.length > 0)
    ? `<code>${esc(l.deps.join(', '))}</code>`
    : '<span class="text-muted">none</span>';

  const shrinkHtml = (l.shrink_before != null)
    ? `<code>${fmtNum(l.shrink_before)} → ${fmtNum(l.shrink_after)}</code>`
    : '<span class="text-muted">—</span>';

  panel.innerHTML = `
    <h3><code>${esc(l.name)}</code>
      <span class="kind-badge ${kindClass(l.kind)}" style="margin-left:.5rem">${esc(l.kind)}</span>
    </h3>
    <dl class="lemma-detail-grid">
      <dt>Index</dt>   <dd>${esc(l.idx)}</dd>
      <dt>Statement</dt><dd><code>${esc(l.statement)}</code></dd>
      <dt>Hypotheses</dt><dd>${essHtml}</dd>
      <dt>Deps</dt>    <dd>${depsHtml}</dd>
      <dt>Inlined</dt> <dd><code>${fmtNum(l.inlined)}</code></dd>
      <dt>Shared</dt>  <dd><code>${fmtNum(l.shared)}</code></dd>
      <dt>Shrink</dt>  <dd>${shrinkHtml}</dd>
    </dl>
    ${l.blurb ? `<p class="mt-2">${esc(l.blurb)}</p>` : ''}
  `;
  panel.classList.add('open');

  // Scroll the panel into view if off-screen
  panel.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
}

function closeLemmaDetail() {
  const panel = document.getElementById('lemma-detail');
  panel?.classList.remove('open');
}

// ─── 5. Model variation ───────────────────────────────────────────────────────

/**
 * State for the model-variation panel.
 * We always keep geometry=F1 fixed and let the user pick a substrate.
 */
const modelState = {
  data:        [],
  geomId:      'f1',
  substrateId: 'realR',  // default to the "full ZFC" model
};

function renderModelVariation(models) {
  modelState.data = models;

  const geomModels = models.filter(m => m.kind === 'geometry');
  const subModels  = models.filter(m => m.kind === 'substrate');

  renderSegmentGroup('geom-buttons',     geomModels,  'geomId',      true);
  renderSegmentGroup('substrate-buttons', subModels,  'substrateId', false);

  updateModelResult();
}

function renderSegmentGroup(containerId, items, stateKey, disabledIfSingle) {
  const container = document.getElementById(containerId);
  if (!container) return;

  container.innerHTML = items.map((m, i) => {
    const isActive = modelState[stateKey] === m.id ||
      (i === 0 && !items.find(x => x.id === modelState[stateKey]));
    const disabled = disabledIfSingle && items.length === 1;
    return `<button
      class="seg-btn ${isActive ? 'active' : ''}"
      data-id="${esc(m.id)}"
      data-key="${esc(stateKey)}"
      ${disabled ? 'aria-disabled="true" title="Only one geometry model"' : ''}
      aria-pressed="${isActive}"
    >${esc(m.label)}</button>`;
  }).join('');

  container.querySelectorAll('.seg-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      const key = btn.dataset.key;
      const id  = btn.dataset.id;
      modelState[key] = id;

      // Update active state on buttons in this group
      container.querySelectorAll('.seg-btn').forEach(b => {
        const active = b.dataset.id === id;
        b.classList.toggle('active', active);
        b.setAttribute('aria-pressed', active);
      });

      updateModelResult();
    });
  });
}

function updateModelResult() {
  const { data, geomId, substrateId } = modelState;

  const geom = data.find(m => m.id === geomId);
  const sub  = data.find(m => m.id === substrateId);
  const poll = data.find(m => m.kind === 'claim');

  if (!geom) return;

  const geomLog = geom.log10;
  const subLog  = sub?.log10 ?? 0;
  const totalLog = sub ? geomLog + subLog : geomLog;

  // Display the total
  const totalEl = document.getElementById('model-total');
  if (totalEl) {
    totalEl.innerHTML = fmtLog(totalLog);
  }

  const noteEl = document.getElementById('model-note');
  if (noteEl && poll) {
    const gap = poll.log10 - totalLog;
    noteEl.textContent = `The poll's 10^${poll.log10} is ~${gap.toFixed(0)} orders of magnitude larger.`;
  }

  // Breakdown table
  const breakdownEl = document.getElementById('model-breakdown');
  if (breakdownEl) {
    const rows = [];
    rows.push({ label: `Geometry (${geom.label})`, val: fmtLogText(geomLog), note: geom.note });
    if (sub) {
      rows.push({ label: `Substrate (${sub.label})`, val: fmtLogText(subLog), note: sub.note });
      rows.push({ label: 'Total (geometry + substrate)', val: fmtLogText(totalLog), note: 'combined' });
    }
    if (poll) {
      rows.push({ label: poll.label, val: fmtLogText(poll.log10), note: poll.note });
    }

    breakdownEl.innerHTML = rows.map(r => `
      <div class="row">
        <span>${esc(r.label)}</span>
        <span class="val">${esc(r.val)}</span>
      </div>`).join('');
  }
}

// ─── Entry point ─────────────────────────────────────────────────────────────

async function main() {
  let data;
  try {
    data = await loadData();
  } catch (e) {
    document.body.insertAdjacentHTML('afterbegin',
      `<div style="background:#ffd7d7;color:#6d0000;padding:1rem 1.5rem;font-weight:600">
        Error loading data: ${esc(e.message)}
      </div>`);
    return;
  }

  renderHero(data);
  renderResults(data);
  await renderDag(data);
  renderLemmaSection(data.lemmas);
  renderModelVariation(data.models);
  updateSortHeaders();
}

main();
