 

'use strict';

// ══════════════════════════════════════════════════════════════
// §1  WORLD CONFIGURATION
// ══════════════════════════════════════════════════════════════

const State = {
  ROWS: 4, COLS: 4, PITS: 3,
  world: {},          // key → { pit, wumpus, gold }
  percepts: {},       // key → { breeze, stench, glitter }

  agentR: 0, agentC: 0,
  agentAlive: false,
  gameOver:   false,
  gameWon:    false,
  wumpusAlive: true,
  revealed:   false,

  visited:         new Set(),
  safeDeduced:     new Set(),
  suspectCells:    new Set(),
  pitConfirmed:    new Set(),
  wumpusConfirmed: new Set(),

  stepCount:       0,
  inferenceCount:  0,
  resolutionCount: 0,
  hazardsFound:    0,

  movePlan: [],
  autoTimer: null,
  logCount:  0,
};

// ══════════════════════════════════════════════════════════════
// §2  KNOWLEDGE BASE — CNF REPRESENTATION
// ══════════════════════════════════════════════════════════════

const KB = {
  clauses: [],   // Array of clause arrays; clause = array of literal strings
  log: [],       // Human-readable clause descriptions

  clear() {
    this.clauses = [];
    this.log = [];
  },

  /**
   * Add clauses to the KB.
   * @param {string[][]} clauses  - CNF clauses to add
   * @param {string}     [human]  - Human-readable description
   */
  tell(clauses, human) {
    for (const c of clauses) this.clauses.push(c);
    if (human) this.log.push(human);
  },

  /**
   * Resolution Refutation:
   * Proves ⊢ alpha by adding {¬alpha} and deriving ⊥.
   *
   * Algorithm (Robinson 1965):
   *   1.  Working set S = KB ∪ {¬alpha}
   *   2.  For every pair of clauses that share a complementary literal:
   *         form their resolvent (union minus the complement pair)
   *   3.  If resolvent = {} (empty clause) → contradiction → alpha proved
   *   4.  Add new resolvents; repeat until no new clauses or contradiction
   *
   * @param  {string} alpha - Literal to prove (e.g. "~P_1_2")
   * @returns {{ proved: boolean, steps: number }}
   */
  ask(alpha) {
    State.inferenceCount++;
    let steps = 0;

    const negAlpha = negate(alpha);
    const working = this.clauses.map(c => [...c]);
    working.push([negAlpha]);

    const seen = new Set(working.map(clauseKey));
    let changed = true;

    while (changed) {
      changed = false;
      const len = working.length;

      for (let i = 0; i < len; i++) {
        for (let j = i + 1; j < len; j++) {
          const ci = working[i];
          const cj = working[j];

          for (const lit of ci) {
            const comp = negate(lit);
            if (!cj.includes(comp)) continue;

            steps++;
            State.resolutionCount++;

            // Resolvent = (ci \ {lit}) ∪ (cj \ {comp})
            const resolvent = [
              ...new Set([
                ...ci.filter(l => l !== lit),
                ...cj.filter(l => l !== comp),
              ]),
            ];

            // Empty clause → contradiction found
            if (resolvent.length === 0) {
              State.inferenceCount++;
              return { proved: true, steps };
            }

            const rk = clauseKey(resolvent);
            if (!seen.has(rk)) {
              seen.add(rk);
              working.push(resolvent);
              changed = true;
            }
            break; // only resolve on first complementary literal per pair
          }
        }
      }
    }

    return { proved: false, steps };
  },
};

// Literal helpers
const negate = lit => lit.startsWith('~') ? lit.slice(1) : '~' + lit;
const clauseKey = clause => [...clause].sort().join(',');

// Cell coordinate key
const ck = (r, c) => `${r}_${c}`;

// ══════════════════════════════════════════════════════════════
// §3  ENVIRONMENT — WORLD GENERATION & PERCEPTS
// ══════════════════════════════════════════════════════════════

/** Fisher-Yates shuffle (in-place) */
function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

/** Adjacent cells (von Neumann neighbourhood) */
function neighbours(r, c) {
  return [[-1,0],[1,0],[0,-1],[0,1]]
    .map(([dr, dc]) => [r + dr, c + dc])
    .filter(([nr, nc]) => nr >= 0 && nr < State.ROWS && nc >= 0 && nc < State.COLS);
}

/** Compute and cache percepts for a cell (called lazily on visit) */
function computePercepts(r, c) {
  const k = ck(r, c);
  if (State.percepts[k]) return State.percepts[k];

  let breeze = false, stench = false, glitter = false;

  for (const [nr, nc] of neighbours(r, c)) {
    const nk = ck(nr, nc);
    if (State.world[nk]?.pit)                          breeze = true;
    if (State.world[nk]?.wumpus && State.wumpusAlive)  stench = true;
  }
  if (State.world[k]?.gold) glitter = true;

  State.percepts[k] = { breeze, stench, glitter };
  return State.percepts[k];
}

/** Place hazards and gold; initialise agent */
function generateWorld() {
  State.world = {};
  State.percepts = {};

  const avoid = new Set(['0_0', '0_1', '1_0']);
  const pool = [];
  for (let r = 0; r < State.ROWS; r++)
    for (let c = 0; c < State.COLS; c++)
      if (!avoid.has(ck(r, c))) pool.push([r, c]);

  shuffle(pool);

  // Wumpus — first cell in shuffled pool
  const [wr, wc] = pool[0];
  State.world[ck(wr, wc)] = { ...(State.world[ck(wr, wc)] || {}), wumpus: true };

  // Pits
  const maxPits = Math.min(State.PITS, pool.length - 1);
  for (let i = 1; i <= maxPits; i++) {
    const [pr, pc] = pool[i];
    State.world[ck(pr, pc)] = { ...(State.world[ck(pr, pc)] || {}), pit: true };
  }

  // Gold — a random remaining safe cell
  const remaining = pool.slice(maxPits + 1);
  if (remaining.length > 0) {
    const [gr, gc] = remaining[Math.floor(Math.random() * remaining.length)];
    State.world[ck(gr, gc)] = { ...(State.world[ck(gr, gc)] || {}), gold: true };
  }
}

// ══════════════════════════════════════════════════════════════
// §4  INFERENCE ENGINE — KB UPDATE + SAFETY QUERIES
// ══════════════════════════════════════════════════════════════

/**
 * TELL the KB percepts observed at (r, c).
 *
 * CNF encoding of Wumpus World axioms:
 *   ¬Breeze[r,c]  →  ∀ adj: ¬P[adj]
 *   Breeze[r,c]   →  ∨ adj: P[adj]          (at-least-one clause)
 *   ¬Stench[r,c]  →  ∀ adj: ¬W[adj]
 *   Stench[r,c]   →  ∨ adj: W[adj]
 */
function updateKBForCell(r, c) {
  const { breeze, stench } = computePercepts(r, c);
  const adjs = neighbours(r, c);
  const adjKeys = adjs.map(([ar, ac]) => ck(ar, ac));

  // The visited cell is safe
  KB.tell(
    [['~P_' + ck(r, c)], ['~W_' + ck(r, c)]],
    `¬P[${r},${c}] ∧ ¬W[${r},${c}]  ← visited`
  );

  if (!breeze) {
    for (const ak of adjKeys) {
      KB.tell([['~P_' + ak]], `¬P[${ak}]  ← no-breeze at [${r},${c}]`);
    }
  } else {
    if (adjKeys.length > 0) {
      KB.tell(
        [adjKeys.map(ak => 'P_' + ak)],
        `P[${adjKeys.join(']∨P[')}]  ← breeze at [${r},${c}]`
      );
      for (const [ar, ac] of adjs) {
        const ak = ck(ar, ac);
        if (!State.safeDeduced.has(ak) && !State.pitConfirmed.has(ak))
          State.suspectCells.add(ak);
      }
    }
  }

  if (!stench) {
    for (const ak of adjKeys) {
      KB.tell([['~W_' + ak]], `¬W[${ak}]  ← no-stench at [${r},${c}]`);
    }
  } else {
    if (adjKeys.length > 0) {
      KB.tell(
        [adjKeys.map(ak => 'W_' + ak)],
        `W[${adjKeys.join(']∨W[')}]  ← stench at [${r},${c}]`
      );
      for (const [ar, ac] of adjs) {
        const ak = ck(ar, ac);
        if (!State.safeDeduced.has(ak) && !State.wumpusConfirmed.has(ak))
          State.suspectCells.add(ak);
      }
    }
  }
}

/**
 * ASK the KB if cell (r, c) is provably safe.
 * Uses Resolution Refutation twice: once for ¬P, once for ¬W.
 * Also opportunistically confirms hazards.
 *
 * @returns {boolean}
 */
function isSafe(r, c) {
  const k = ck(r, c);
  if (State.safeDeduced.has(k))     return true;
  if (State.pitConfirmed.has(k))    return false;
  if (State.wumpusConfirmed.has(k)) return false;
  if (State.visited.has(k))         return true;

  const pitSafe     = KB.ask('~P_' + k);
  const wumpusSafe  = KB.ask('~W_' + k);

  if (pitSafe.proved && wumpusSafe.proved) {
    State.safeDeduced.add(k);
    State.suspectCells.delete(k);
    return true;
  }

  // Try to confirm hazards
  if (!pitSafe.proved) {
    const isPit = KB.ask('P_' + k);
    if (isPit.proved && !State.pitConfirmed.has(k)) {
      State.pitConfirmed.add(k);
      State.suspectCells.delete(k);
      State.hazardsFound++;
    }
  }
  if (!wumpusSafe.proved) {
    const isWumpus = KB.ask('W_' + k);
    if (isWumpus.proved && !State.wumpusConfirmed.has(k)) {
      State.wumpusConfirmed.add(k);
      State.suspectCells.delete(k);
      State.hazardsFound++;
    }
  }

  return false;
}

// ══════════════════════════════════════════════════════════════
// §5  AGENT NAVIGATION — FRONTIER & PATH PLANNING
// ══════════════════════════════════════════════════════════════

/** Deduped frontier of unvisited safe cells reachable from any visited cell */
function safeFrontier() {
  const seen = new Set();
  const out  = [];
  for (const vk of State.visited) {
    const [r, c] = vk.split('_').map(Number);
    for (const [ar, ac] of neighbours(r, c)) {
      const ak = ck(ar, ac);
      if (!State.visited.has(ak) && !seen.has(ak) && isSafe(ar, ac)) {
        seen.add(ak);
        out.push([ar, ac]);
      }
    }
  }
  return out;
}

/** All unvisited, non-confirmed-hazard neighbours of visited cells */
function unknownFrontier() {
  const seen = new Set();
  const out  = [];
  for (const vk of State.visited) {
    const [r, c] = vk.split('_').map(Number);
    for (const [ar, ac] of neighbours(r, c)) {
      const ak = ck(ar, ac);
      if (!State.visited.has(ak) && !seen.has(ak)
          && !State.pitConfirmed.has(ak) && !State.wumpusConfirmed.has(ak)) {
        seen.add(ak);
        out.push([ar, ac]);
      }
    }
  }
  return out;
}

/**
 * BFS shortest path from (fromR, fromC) to (toR, toC).
 * Only traverses visited or deduced-safe cells (plus the target itself).
 *
 * @returns {[number,number][]|null}  Array of [r,c] steps including target
 */
function bfsPath(fromR, fromC, toR, toC) {
  const queue = [[fromR, fromC, []]];
  const seen  = new Set([ck(fromR, fromC)]);

  while (queue.length) {
    const [r, c, path] = queue.shift();
    if (r === toR && c === toC) return path;

    for (const [nr, nc] of neighbours(r, c)) {
      const nk = ck(nr, nc);
      if (seen.has(nk)) continue;
      const passable = State.visited.has(nk) || State.safeDeduced.has(nk)
                       || (nr === toR && nc === toC);
      if (!passable) continue;
      seen.add(nk);
      queue.push([nr, nc, [...path, [nr, nc]]]);
    }
  }
  return null;
}

// ══════════════════════════════════════════════════════════════
// §6  AGENT STEP EXECUTION
// ══════════════════════════════════════════════════════════════

/** Execute one agent step. Returns true if agent can continue. */
function agentStep() {
  if (State.gameOver) return false;

  // Consume pre-planned moves first
  if (State.movePlan.length > 0) {
    const [nr, nc] = State.movePlan.shift();
    moveAgent(nr, nc);
    return !State.gameOver;
  }

  // Find safe frontier cells
  const sf = safeFrontier();

  if (sf.length > 0) {
    // Prefer closest (Manhattan distance)
    sf.sort(([ar, ac], [br, bc]) =>
      (Math.abs(ar - State.agentR) + Math.abs(ac - State.agentC)) -
      (Math.abs(br - State.agentR) + Math.abs(bc - State.agentC))
    );
    const [tr, tc] = sf[0];
    const path = bfsPath(State.agentR, State.agentC, tr, tc);

    if (path && path.length > 0) {
      log(`Planning route → [${tr},${tc}]`, 'info');
      State.movePlan = path.slice(1);   // remaining steps after first
      moveAgent(path[0][0], path[0][1]);
      return !State.gameOver;
    }
  }

  // Check if exploration is complete
  if (unknownFrontier().length === 0) {
    log('All reachable cells explored — episode complete.', 'success');
    State.gameOver = true;
    State.gameWon  = true;
    updateStatus();
    UI.render();
    return false;
  }

  log('No logically safe move available — agent halted.', 'warn');
  State.gameOver = true;
  updateStatus();
  UI.render();
  return false;
}

/** Physically move agent to (r, c) and process consequences */
function moveAgent(r, c) {
  State.agentR = r;
  State.agentC = c;
  State.stepCount++;

  const k = ck(r, c);
  State.visited.add(k);
  State.suspectCells.delete(k);

  const cell = State.world[k] || {};

  if (cell.pit) {
    State.agentAlive = false;
    State.gameOver   = true;
    State.pitConfirmed.add(k);
    State.hazardsFound++;
    log(`☠ Fell into pit at [${r},${c}]!`, 'danger');

  } else if (cell.wumpus && State.wumpusAlive) {
    State.agentAlive = false;
    State.gameOver   = true;
    State.wumpusConfirmed.add(k);
    State.hazardsFound++;
    log(`☠ Devoured by the Wumpus at [${r},${c}]!`, 'danger');

  } else {
    const { breeze, stench, glitter } = computePercepts(r, c);
    const parts = [];
    if (breeze)  parts.push('Breeze');
    if (stench)  parts.push('Stench');
    if (glitter) parts.push('Glitter');
    log(
      `Moved → [${r},${c}]. ` + (parts.length ? parts.join(', ') : 'No percepts.'),
      'info'
    );

    updateKBForCell(r, c);

    // Re-run inference on suspect cells after new KB facts
    for (const sk of [...State.suspectCells]) {
      const [sr, sc] = sk.split('_').map(Number);
      isSafe(sr, sc);
    }

    if (glitter) {
      log('✦ GOLD found at [' + r + ',' + c + ']! Grabbed — episode won!', 'success');
      State.gameOver = true;
      State.gameWon  = true;
    }
  }

  updateStatus();
  UI.render();
  updateMetrics();
}

// ══════════════════════════════════════════════════════════════
// §7  EPISODE INITIALISATION
// ══════════════════════════════════════════════════════════════

function newEpisode() {
  stopAuto();

  // Read configuration
  State.ROWS  = clamp(parseInt(document.getElementById('inp-rows').value)  || 4, 3, 9);
  State.COLS  = clamp(parseInt(document.getElementById('inp-cols').value)  || 4, 3, 9);
  State.PITS  = clamp(parseInt(document.getElementById('inp-pits').value)  || 3, 1, Math.floor(State.ROWS * State.COLS * 0.4));

  // Reset all state
  State.world = {};
  State.percepts = {};
  State.visited         = new Set();
  State.safeDeduced     = new Set();
  State.suspectCells    = new Set();
  State.pitConfirmed    = new Set();
  State.wumpusConfirmed = new Set();
  State.wumpusAlive     = true;
  State.agentR          = 0;
  State.agentC          = 0;
  State.agentAlive      = true;
  State.gameOver        = false;
  State.gameWon         = false;
  State.revealed        = false;
  State.stepCount       = 0;
  State.inferenceCount  = 0;
  State.resolutionCount = 0;
  State.hazardsFound    = 0;
  State.movePlan        = [];
  State.logCount        = 0;

  KB.clear();
  generateWorld();

  // Bootstrap: agent starts at (0,0) — known safe
  State.visited.add('0_0');
  State.safeDeduced.add('0_0');
  KB.tell(
    [['~P_0_0'], ['~W_0_0']],
    '¬P[0,0] ∧ ¬W[0,0]  ← start axiom'
  );
  updateKBForCell(0, 0);
  for (const [ar, ac] of neighbours(0, 0)) isSafe(ar, ac);

  // Enable controls
  ['btn-step', 'btn-auto', 'btn-reveal'].forEach(id => {
    document.getElementById(id).disabled = false;
  });
  document.getElementById('btn-reveal').textContent = 'Reveal World';
  document.getElementById('btn-auto').textContent   = 'Auto Run';
  document.getElementById('btn-auto').className     = 'btn btn-success';

  log(`Episode started — ${State.ROWS}×${State.COLS} grid, ${State.PITS} pits`, 'success');

  UI.buildGrid();
  updateStatus();
  UI.render();
  updateMetrics();
}

// ══════════════════════════════════════════════════════════════
// §8  AUTO-RUN
// ══════════════════════════════════════════════════════════════

function startAuto() {
  const btn = document.getElementById('btn-auto');
  btn.textContent = 'Stop Auto';
  btn.className   = 'btn btn-auto-active';
  State.autoTimer = setInterval(() => {
    const cont = agentStep();
    if (!cont || State.gameOver) stopAuto();
  }, 550);
}

function stopAuto() {
  if (State.autoTimer) { clearInterval(State.autoTimer); State.autoTimer = null; }
  const btn = document.getElementById('btn-auto');
  if (btn) {
    btn.textContent = 'Auto Run';
    btn.className   = 'btn btn-success';
  }
}

function toggleAuto() {
  State.autoTimer ? stopAuto() : startAuto();
}

// ══════════════════════════════════════════════════════════════
// §9  UI LAYER
// ══════════════════════════════════════════════════════════════

const UI = {
  /** Build the grid DOM from scratch */
  buildGrid() {
    const container = document.getElementById('grid-container');
    container.innerHTML = '';

    const grid = document.createElement('div');
    grid.id = 'grid';
    grid.style.gridTemplateColumns = `repeat(${State.COLS}, 1fr)`;
    container.appendChild(grid);

    // Rows rendered top-to-bottom (row ROWS-1 first for correct y-axis)
    for (let r = State.ROWS - 1; r >= 0; r--) {
      for (let c = 0; c < State.COLS; c++) {
        const cell = document.createElement('div');
        cell.className = 'cell state-unknown';
        cell.dataset.r = r;
        cell.dataset.c = c;
        if (r === 0 && c === 0) cell.classList.add('state-start');
        grid.appendChild(cell);
      }
    }

    document.getElementById('grid-coords').textContent =
      `${State.ROWS} × ${State.COLS}`;
  },

  /** Repaint all cells */
  render() {
    if (!State.agentAlive && State.gameOver) {
      // Reveal world on death
      State.revealed = true;
    }

    const grid = document.getElementById('grid');
    if (!grid) return;

    const cells = grid.querySelectorAll('.cell');
    for (const cell of cells) {
      const r = parseInt(cell.dataset.r);
      const c = parseInt(cell.dataset.c);
      const k = ck(r, c);

      // ── Determine cell class ─────────────────────────────
      let state = 'unknown';
      if (r === State.agentR && c === State.agentC && State.agentAlive) {
        state = 'agent';
      } else if (State.pitConfirmed.has(k)) {
        state = 'pit';
      } else if (State.wumpusConfirmed.has(k)) {
        state = 'wumpus';
      } else if (State.safeDeduced.has(k)) {
        state = 'safe';
      } else if (State.visited.has(k)) {
        state = 'visited';
      } else if (State.suspectCells.has(k)) {
        state = 'suspect';
      }

      cell.className = 'cell state-' + state + (r === 0 && c === 0 ? ' state-start' : '');

      // ── Icons ─────────────────────────────────────────────
      let iconHtml = '';
      const wdata = State.world[k] || {};

      if (r === State.agentR && c === State.agentC && State.agentAlive) {
        iconHtml = '<span class="cell-icon">🤖</span>';
      }

      if (State.revealed || State.gameOver) {
        if (wdata.pit)    iconHtml += '<span class="cell-icon">🕳️</span>';
        if (wdata.wumpus) iconHtml += '<span class="cell-icon">👾</span>';
        if (wdata.gold)   iconHtml += '<span class="cell-icon">🏆</span>';
      } else {
        if (State.pitConfirmed.has(k))    iconHtml += '<span class="cell-icon">🕳️</span>';
        if (State.wumpusConfirmed.has(k)) iconHtml += '<span class="cell-icon">👾</span>';
      }

      // ── Percept tags ──────────────────────────────────────
      let tagHtml = '';
      const p = State.percepts[k];
      if (p && (State.visited.has(k) || (r === State.agentR && c === State.agentC))) {
        if (p.breeze)  tagHtml += '<span class="tag tag-b">B</span>';
        if (p.stench)  tagHtml += '<span class="tag tag-s">S</span>';
        if (p.glitter) tagHtml += '<span class="tag tag-g">G</span>';
      }
      if (State.safeDeduced.has(k) && !State.visited.has(k)) {
        tagHtml += '<span class="tag tag-ok">✓</span>';
      }

      cell.innerHTML = `
        <span class="cell-coord">${r},${c}</span>
        <div class="cell-body">${iconHtml}</div>
        ${tagHtml ? `<div class="cell-tags">${tagHtml}</div>` : ''}
      `;
    }
  },
};

// ══════════════════════════════════════════════════════════════
// §10  METRICS & STATUS DISPLAY
// ══════════════════════════════════════════════════════════════

function updateMetrics() {
  const set = (id, val) => {
    const el = document.getElementById(id);
    if (el) el.textContent = val;
  };

  set('m-pos',     State.agentAlive ? `[${State.agentR},${State.agentC}]` : '—');
  set('m-steps',   State.stepCount);
  set('m-infer',   State.inferenceCount);
  set('m-resol',   State.resolutionCount);
  set('m-safe',    State.safeDeduced.size);
  set('m-haz',     State.hazardsFound);
  set('m-kb',      KB.clauses.length);
  set('m-visited', State.visited.size);

  // Percept display
  updatePerceptDisplay();
  updateKBDisplay();
}

function updatePerceptDisplay() {
  const el = document.getElementById('percept-display');
  if (!el) return;

  if (!State.agentAlive || State.stepCount === 0) {
    el.innerHTML = '<span class="percept-chip p-none"><span class="percept-chip-dot"></span>none</span>';
    return;
  }

  const p = computePercepts(State.agentR, State.agentC);
  let html = '';
  if (p.breeze)  html += '<span class="percept-chip p-breeze"><span class="percept-chip-dot"></span>Breeze</span>';
  if (p.stench)  html += '<span class="percept-chip p-stench"><span class="percept-chip-dot"></span>Stench</span>';
  if (p.glitter) html += '<span class="percept-chip p-glitter"><span class="percept-chip-dot"></span>Glitter</span>';
  if (!html)     html  = '<span class="percept-chip p-none"><span class="percept-chip-dot"></span>none</span>';
  el.innerHTML = html;
}

function updateKBDisplay() {
  const el = document.getElementById('kb-display');
  if (!el) return;
  el.innerHTML = '';
  const recent = KB.log.slice(-30).reverse();
  for (const entry of recent) {
    const d = document.createElement('div');
    d.className = 'kb-clause';
    d.textContent = entry;
    el.appendChild(d);
  }
  const badge = document.getElementById('kb-count');
  if (badge) badge.textContent = KB.clauses.length;
}

function updateStatus() {
  const bar  = document.getElementById('status-banner');
  const dot  = document.getElementById('status-dot');
  const text = document.getElementById('status-text');
  const badge = document.getElementById('status-badge-text');
  if (!bar || !dot || !text) return;

  bar.className = 'status-banner';
  dot.className = 'status-dot';

  if (State.gameOver) {
    if (!State.agentAlive) {
      bar.classList.add('state-dead');
      dot.classList.add('dead');
      text.textContent = 'Agent terminated — hazard encountered at [' + State.agentR + ',' + State.agentC + ']';
      if (badge) badge.textContent = 'DEAD';
      document.getElementById('btn-step').disabled = true;
      document.getElementById('btn-auto').disabled  = true;
    } else if (State.gameWon) {
      bar.classList.add('state-won');
      dot.classList.add('won');
      text.textContent = 'Episode complete — all safe cells explored' + (State.world[ck(State.agentR, State.agentC)]?.gold ? ', gold retrieved!' : '.');
      if (badge) badge.textContent = 'COMPLETE';
      document.getElementById('btn-step').disabled = true;
      document.getElementById('btn-auto').disabled  = true;
    } else {
      bar.classList.add('state-stuck');
      dot.classList.add('dead');
      text.textContent = 'Agent halted — no logically safe moves remain.';
      if (badge) badge.textContent = 'STUCK';
    }
  } else if (State.stepCount > 0) {
    bar.classList.add('state-running');
    dot.classList.add('active');
    text.textContent = `Active at [${State.agentR},${State.agentC}] — step ${State.stepCount} — KB: ${KB.clauses.length} clauses`;
    if (badge) badge.textContent = 'RUNNING';
  } else {
    bar.classList.add('state-idle');
    text.textContent = 'Episode initialised — press Step or Auto Run to begin.';
    if (badge) badge.textContent = 'READY';
  }
}

// ══════════════════════════════════════════════════════════════
// §11  LOGGING
// ══════════════════════════════════════════════════════════════

function log(msg, type = '') {
  const container = document.getElementById('log');
  if (!container) return;

  const n = ++State.logCount;
  const entry = document.createElement('div');
  entry.className = 'log-entry' + (type ? ' l-' + type : '');
  entry.innerHTML = `<span class="log-n">${n}</span><span class="log-msg">${msg}</span>`;
  container.prepend(entry);

  // Keep log bounded
  while (container.children.length > 80) {
    container.removeChild(container.lastChild);
  }
}

// ══════════════════════════════════════════════════════════════
// §12  HELPERS
// ══════════════════════════════════════════════════════════════

const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));

// ══════════════════════════════════════════════════════════════
// §13  BOOTSTRAP — EVENT LISTENERS & INITIAL RENDER
// ══════════════════════════════════════════════════════════════

document.addEventListener('DOMContentLoaded', () => {
  document.getElementById('btn-new').addEventListener('click', newEpisode);

  document.getElementById('btn-step').addEventListener('click', () => {
    if (!State.gameOver) agentStep();
  });

  document.getElementById('btn-auto').addEventListener('click', toggleAuto);

  document.getElementById('btn-reveal').addEventListener('click', () => {
    State.revealed = !State.revealed;
    document.getElementById('btn-reveal').textContent =
      State.revealed ? 'Hide World' : 'Reveal World';
    UI.render();
  });

  // Initial log message
  log('System initialised. Configure grid parameters and press New Episode.', 'info');
});