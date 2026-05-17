const fallbackData = {
  generated: '',
  headline: {
    f0_asa: 224,
    g4_sas_inlined: 7251714,
    g4_sas_log10: 6.8604,
    lemmas: 57,
    db_statements: 195,
    shared_total: 4931739,
  },
  models: [
    { id: 'f1', label: 'F1 axiomatic', kind: 'geometry', log10: 6.8604 },
    { id: 'euclid', label: 'Minimal Euclidean-field model', kind: 'substrate', log10: 37.0 },
    { id: 'realR', label: 'Full ZFC model of R', kind: 'substrate', log10: 45.7 },
    { id: 'poll', label: 'The poll estimate', kind: 'claim', log10: 1000.0 },
  ],
  lemmas: [
    { name: 'loclink', inlined: 3179167, inlined_log10: 6.5023 },
    { name: 'sqcong', inlined: 390380, inlined_log10: 5.5915 },
    { name: 'mulcposcan', inlined: 54316, inlined_log10: 4.7349 },
    { name: 'G4-sas', inlined: 7251714, inlined_log10: 6.8604 },
  ],
};

const deck = document.getElementById('deck');
const slides = [...document.querySelectorAll('.slide')];
const statusEl = document.getElementById('slide-status');
const progressBar = document.getElementById('progress-bar');
const prevButton = document.getElementById('prev-slide');
const nextButton = document.getElementById('next-slide');
const overviewButton = document.getElementById('overview-toggle');
const fullscreenButton = document.getElementById('fullscreen-toggle');

let current = initialSlideIndex();

function initialSlideIndex() {
  const hash = window.location.hash.replace('#', '');
  const index = slides.findIndex((slide) => slide.id === hash);
  return index >= 0 ? index : 0;
}

function clampIndex(index) {
  return Math.max(0, Math.min(slides.length - 1, index));
}

function showSlide(index, updateHash = true) {
  current = clampIndex(index);

  slides.forEach((slide, slideIndex) => {
    const active = slideIndex === current;
    slide.classList.toggle('is-current', active);
    slide.setAttribute('aria-hidden', active ? 'false' : 'true');
  });

  if (statusEl) statusEl.textContent = `${current + 1} / ${slides.length}`;
  if (progressBar) progressBar.style.transform = `scaleX(${(current + 1) / slides.length})`;

  if (updateHash && slides[current]) {
    history.replaceState(null, '', `#${slides[current].id}`);
  }
}

function nextSlide() {
  if (deck.classList.contains('is-overview')) return;
  showSlide(current + 1);
}

function previousSlide() {
  if (deck.classList.contains('is-overview')) return;
  showSlide(current - 1);
}

prevButton?.addEventListener('click', previousSlide);
nextButton?.addEventListener('click', nextSlide);

overviewButton?.addEventListener('click', () => {
  deck.classList.toggle('is-overview');
});

fullscreenButton?.addEventListener('click', async () => {
  if (!document.fullscreenElement) {
    await document.documentElement.requestFullscreen?.();
  } else {
    await document.exitFullscreen?.();
  }
});

deck?.addEventListener('click', (event) => {
  const target = event.target;
  if (!(target instanceof Element)) return;
  if (target.closest('.deck-controls, a, button')) return;

  const clickedSlide = target.closest('.slide');
  if (deck.classList.contains('is-overview') && clickedSlide) {
    const index = slides.indexOf(clickedSlide);
    deck.classList.remove('is-overview');
    showSlide(index);
    return;
  }

  nextSlide();
});

window.addEventListener('keydown', (event) => {
  if (event.defaultPrevented) return;

  switch (event.key) {
    case 'ArrowRight':
    case 'PageDown':
    case ' ':
      event.preventDefault();
      nextSlide();
      break;
    case 'ArrowLeft':
    case 'PageUp':
      event.preventDefault();
      previousSlide();
      break;
    case 'Home':
      event.preventDefault();
      showSlide(0);
      break;
    case 'End':
      event.preventDefault();
      showSlide(slides.length - 1);
      break;
    case 'o':
    case 'O':
      event.preventDefault();
      deck.classList.toggle('is-overview');
      break;
    case 'f':
    case 'F':
      event.preventDefault();
      fullscreenButton?.click();
      break;
    case 'Escape':
      deck.classList.remove('is-overview');
      break;
    default:
      break;
  }
});

window.addEventListener('hashchange', () => {
  const index = initialSlideIndex();
  showSlide(index, false);
});

async function loadData() {
  try {
    const response = await fetch('data/site.json');
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return await response.json();
  } catch (error) {
    console.warn('[asagolf slides] using fallback data:', error.message);
    return fallbackData;
  }
}

function formatNumber(value) {
  return Number(value).toLocaleString('en-US');
}

function formatLog(value) {
  return `10^${Number(value).toFixed(2)}`;
}

function setText(selector, value) {
  document.querySelectorAll(selector).forEach((element) => {
    element.textContent = value;
  });
}

function setHtml(selector, value) {
  document.querySelectorAll(selector).forEach((element) => {
    element.innerHTML = value;
  });
}

function formatGenerated(value) {
  if (!value) return 'generated from site data';
  if (String(value).startsWith('unix:')) {
    const seconds = Number(String(value).slice(5));
    if (Number.isFinite(seconds)) {
      return `generated ${new Date(seconds * 1000).toISOString().slice(0, 10)}`;
    }
  }
  return `generated ${String(value).split('T')[0]}`;
}

function hydrateMetrics(data) {
  const headline = data.headline ?? fallbackData.headline;
  const models = data.models ?? fallbackData.models;
  const geometryLog = Number(headline.g4_sas_log10);
  const realModel = models.find((model) => model.id === 'realR');
  const minimalModel = models.find((model) => model.id === 'euclid');
  const poll = models.find((model) => model.kind === 'claim') ?? { log10: 1000 };
  const fullZfcLog = geometryLog + Number(realModel?.log10 ?? 45.7);
  const minimalTotalLog = geometryLog + Number(minimalModel?.log10 ?? 37);
  const pollGap = Number(poll.log10) - fullZfcLog;

  setText('[data-metric="f0-exact"]', formatNumber(headline.f0_asa));
  setText('[data-metric="g4-exact"]', formatNumber(headline.g4_sas_inlined));
  setText('[data-metric="g4-log"]', formatLog(headline.g4_sas_log10));
  setText('[data-metric="lemma-count"]', formatNumber(headline.lemmas));
  setText('[data-metric="db-statements"]', formatNumber(headline.db_statements));
  setText('[data-metric="shared-total"]', formatNumber(headline.shared_total));
  setText('[data-metric="poll-gap"]', `~${pollGap.toFixed(0)}`);
  setText('[data-generated-date]', formatGenerated(data.generated));
  setText('[data-metric="full-zfc-log"]', formatLog(fullZfcLog));
  setText('[data-metric="minimal-total-log"]', formatLog(minimalTotalLog));

  renderRuler(geometryLog, fullZfcLog, Number(poll.log10));
  renderLemmaBars(data.lemmas ?? fallbackData.lemmas);
}

function renderRuler(geometryLog, fullZfcLog, pollLog) {
  const container = document.getElementById('order-ruler');
  if (!container) return;

  const axis = container.querySelector('.ruler-axis')?.outerHTML ?? '<div class="ruler-axis"></div>';
  const markers = [
    { label: 'G4 geometry', log: geometryLog, color: '#2563eb', lane: -98, side: 'left' },
    { label: 'full real-model route', log: fullZfcLog, color: '#c77700', lane: 84, side: 'left' },
    { label: 'poll', log: pollLog, color: '#e11d48', lane: -38, side: 'right' },
  ];

  container.innerHTML = axis + markers.map((marker) => {
    const x = Math.max(0, Math.min(100, (marker.log / 1000) * 100));
    const sideClass = marker.side === 'right' ? ' is-right' : '';
    return `
      <div class="order-marker${sideClass}" style="--x:${x}%;--label-y:${marker.lane}px;--marker-color:${marker.color}">
        <div class="marker-label">
          <strong>${escapeHtml(marker.label)}</strong>
          <span>${escapeHtml(formatLog(marker.log))}</span>
        </div>
      </div>`;
  }).join('');
}

function renderLemmaBars(lemmas) {
  const container = document.getElementById('lemma-bars');
  if (!container) return;

  const wanted = ['G4-sas', 'loclink', 'sqcong', 'mulcposcan', 'sqz'];
  const rows = wanted
    .map((name) => lemmas.find((lemma) => lemma.name === name))
    .filter(Boolean);
  const maxLog = Math.max(...rows.map((lemma) => Number(lemma.inlined_log10 ?? Math.log10(lemma.inlined))));

  container.innerHTML = rows.map((lemma) => {
    const log = Number(lemma.inlined_log10 ?? Math.log10(lemma.inlined));
    const width = Math.max(7, (log / maxLog) * 100);
    return `
      <div class="lemma-bar-row">
        <span>${escapeHtml(lemma.name)}</span>
        <strong>${formatNumber(lemma.inlined)}</strong>
        <div><i style="width:${width.toFixed(1)}%"></i></div>
      </div>`;
  }).join('');
}

function escapeHtml(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

showSlide(current, false);
loadData().then(hydrateMetrics);
