// germs — a bouncing logo that multiplies, ages and dies, run as a
// cellular automaton and rendered to look like the classic DVD screensaver.
//
// Under the hood it is a discrete-velocity lattice-gas CA:
//
//   Lattice   a fixed grid of CFG.cellSize-px cells (default 180 x 320).
//   Velocity  8 fixed vectors, all length sqrt(5), NONE axis-aligned — every
//             germ always travels on a diagonal, never straight up/down or
//             left/right. One vector per "direction slot".
//   Token     sits in a slot; carries a generation, a cooldown, a child
//             count, a birth tick and a fractional movement budget.
//
//   Per tick (one tick every CFG.tickEvery render frames):
//     1. STREAM   token advances along its velocity vector. gen 1 moves one
//                 vector/tick; each generation is CFG.childSpeedup faster, an
//                 accumulator spending whole hops and keeping the remainder.
//     2. BOUNCE   a hop landing within one ring-radius of the wall is
//                 reflected specularly (component flips, position mirrors
//                 back), so the RING EDGE bounces, not the centre.
//     3. SPLIT    cooldown-- each tick; a token that bounced this tick with an
//                 expired cooldown resets it and writes one child into a slot
//                 rotated 1-2 steps off its heading (deterministic hash).
//                 childGen = min(gen+1, CFG.gmax); childCooldown halves per gen.
//     WARM-UP     after every restart (seed or cull) nobody splits for
//                 CFG.warmupSeconds — the lone ring just bounces.
//     4. DEATH    a token that has produced CFG.maxSplits children dies making
//                 its last one; and once population hits CFG.cullAt, all die
//                 except the most recently born, which resets to gen 1 and
//                 re-populates in place. No burn wave.
//
//   Rendering    each token drawn as the full germs ring in one colour, at a
//                position advanced at its constant nominal per-generation speed.

const canvas = document.getElementById("c");
const ctx = canvas.getContext("2d");

// 8 velocity vectors, ordered by angle, all length sqrt(5), all diagonal.
const VX = [2, 1, -1, -2, -2, -1, 1, 2];
const VY = [1, 2, 2, 1, -1, -2, -2, -1];
const ND = 8;
const VKEY = new Int8Array(25).fill(-1); // (vx+2)*5+(vy+2) -> slot
for (let d = 0; d < ND; d++) VKEY[(VX[d] + 2) * 5 + (VY[d] + 2)] = d;

const SPEED_SCALE = 1000; // fixed-point unit: 1000 = one velocity vector
const COLOR = "#29A2DC"; // ring stroke colour
const LINE_COLOR = "#fff";

// Live-tunable values (wired to the on-screen panel).
const CFG = {
  tSeconds: 15, // gen-1 cooldown, seconds
  warmupSeconds: 10, // quiet bouncing after each restart (slider step is 5s)
  maxSplits: 3, // children a germ makes before dying
  cullAt: 90, // population that triggers "all die except the latest"
  childSpeedup: 0.15, // extra speed per generation
  gmax: 3, // deepest generation
  tickEvery: 4, // render frames per CA tick (higher = slower motion)
  ringRadius: 150, // ring outer radius, px
  cellSize: 6, // lattice resolution, px per cell (rebuilds the grid)
  lineInset: 70, // px from top/bottom edge to each boundary line
  lineThick: 4, // px, boundary line thickness
};
const DEFAULTS = { ...CFG }; // for the "Reset to defaults" button

// Grid dimensions, (re)built from CFG.cellSize.
let CS, GW, GH, N, S;
function computeDims() {
  CS = CFG.cellSize;
  GW = Math.floor(canvas.width / CS);
  GH = Math.floor(canvas.height / CS);
  N = GW * GH;
  S = N * ND;
}

// Derived values, refreshed by recompute() whenever CFG changes.
let T_TICKS, WARMUP_TICKS, MARGIN_X, MARGIN_Y, R_OUTER, STROKE;
let WALL_LEFT, WALL_RIGHT, WALL_TOP, WALL_BOTTOM;
function recompute() {
  R_OUTER = CFG.ringRadius;
  STROKE = R_OUTER * 0.26;
  // Exact pixel wall positions the ring's edge bounces off. Top/bottom stay
  // at the canvas edges; left/right are the boundary lines instead.
  WALL_LEFT = CFG.lineInset + R_OUTER;
  WALL_RIGHT = canvas.width - CFG.lineInset - R_OUTER;
  WALL_TOP = R_OUTER;
  WALL_BOTTOM = canvas.height - R_OUTER;
  // Same boundaries, in grid cells, for the simulation's own bounds check.
  MARGIN_X = Math.min(Math.floor(GW / 2) - 2, Math.round(WALL_LEFT / CS));
  MARGIN_Y = Math.min(Math.floor(GH / 2) - 2, Math.round(WALL_TOP / CS));
  T_TICKS = Math.max(1, Math.round((CFG.tSeconds * 60) / CFG.tickEvery));
  WARMUP_TICKS = Math.round((CFG.warmupSeconds * 60) / CFG.tickEvery);
}

function speedFor(gen) {
  return Math.round(SPEED_SCALE * (1 + CFG.childSpeedup * (gen - 1)));
}

function cooldownFor(gen) {
  return Math.max(1, Math.round(T_TICKS / Math.pow(2, gen - 1)));
}

// Deterministic integer hash of (x, y, t) -> uint32.
function hash(x, y, t) {
  let h = (x * 374761393 + y * 668265263 + t * 2246822519) | 0;
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return (h ^ (h >>> 16)) >>> 0;
}

// Per-slot state arrays, (re)allocated by allocArrays() when the grid changes.
let occ, gen, cd, spl, born, acc;
let nocc, ngen, ncd, nspl, nborn, nacc;
let bounced;
// Per-slot record of where a token bounced FROM this tick (only meaningful
// when bounced[ti] is set) — lets render() draw the true pre-bounce leg
// instead of guessing it from the post-bounce heading.
let srcCX, srcCY, srcDIR, srcACC;
function allocArrays() {
  occ = new Uint8Array(S); gen = new Uint8Array(S); cd = new Int16Array(S);
  spl = new Uint8Array(S); born = new Int32Array(S); acc = new Int16Array(S);
  nocc = new Uint8Array(S); ngen = new Uint8Array(S); ncd = new Int16Array(S);
  nspl = new Uint8Array(S); nborn = new Int32Array(S); nacc = new Int16Array(S);
  bounced = new Uint8Array(S);
  srcCX = new Uint16Array(S); srcCY = new Uint16Array(S);
  srcDIR = new Uint8Array(S); srcACC = new Int16Array(S);
}

let tickNo = 0;
let tickAccumulatorMs = 0;
let restartTick = 0; // tick of the last seed / cull; warm-up counts from here
let paused = false;

function seed(t) {
  restartTick = t;
  const h = hash(7, 11, t);
  const x = MARGIN_X + (h % (GW - 2 * MARGIN_X));
  const y = MARGIN_Y + ((h >>> 8) % (GH - 2 * MARGIN_Y));
  const d = (h >>> 16) % ND;
  const si = (y * GW + x) * ND + d;
  occ[si] = 1;
  gen[si] = 1;
  cd[si] = cooldownFor(1);
  spl[si] = 0;
  born[si] = t;
  acc[si] = 0;
}

function hardRestart() {
  occ.fill(0);
  seed(tickNo);
}

// Full grid rebuild — used when CFG.cellSize changes.
function rebuildGrid() {
  computeDims();
  allocArrays();
  recompute();
  tickNo = 0;
  tickAccumulatorMs = 0;
  seed(0);
}

function tick(t) {
  nocc.fill(0);
  bounced.fill(0);

  const loX = MARGIN_X, hiX = GW - 1 - MARGIN_X;
  const loY = MARGIN_Y, hiY = GH - 1 - MARGIN_Y;

  // --- 1 & 2: stream + bounce ---
  for (let y = 0; y < GH; y++) {
    for (let x = 0; x < GW; x++) {
      const base = (y * GW + x) * ND;
      for (let d = 0; d < ND; d++) {
        const si = base + d;
        if (!occ[si]) continue;

        // Spend the movement budget as whole velocity-vector hops, keeping
        // the remainder for next tick. Faster generations make more hops.
        let a = acc[si] + speedFor(gen[si]);
        let cx = x, cy = y, cdir = d, hitAny = false;
        while (a >= SPEED_SCALE) {
          a -= SPEED_SCALE;
          let nx = cx + VX[cdir], ny = cy + VY[cdir];
          let vx = VX[cdir], vy = VY[cdir];
          if (nx < loX) { nx = 2 * loX - nx; vx = -vx; }
          else if (nx > hiX) { nx = 2 * hiX - nx; vx = -vx; }
          if (ny < loY) { ny = 2 * loY - ny; vy = -vy; }
          else if (ny > hiY) { ny = 2 * hiY - ny; vy = -vy; }
          if (vx !== VX[cdir] || vy !== VY[cdir]) {
            hitAny = true;
            const nd = VKEY[(vx + 2) * 5 + (vy + 2)];
            cdir = nd < 0 ? (cdir + ND / 2) % ND : nd;
          }
          cx = nx; cy = ny;
        }
        // safety clamp (e.g. right after the ring radius / cell size changed)
        if (cx < loX) cx = loX; else if (cx > hiX) cx = hiX;
        if (cy < loY) cy = loY; else if (cy > hiY) cy = hiY;

        const ti = (cy * GW + cx) * ND + cdir;
        if (!nocc[ti]) {
          nocc[ti] = 1;
          ngen[ti] = gen[si];
          ncd[ti] = cd[si];
          nspl[ti] = spl[si];
          nborn[ti] = born[si];
          nacc[ti] = a;
          if (hitAny) {
            bounced[ti] = 1;
            // (x, y, d, acc[si]) is exactly the state this token had at the
            // end of the previous tick — the true anchor render() needs for
            // the pre-bounce leg.
            srcCX[ti] = x;
            srcCY[ti] = y;
            srcDIR[ti] = d;
            srcACC[ti] = acc[si];
          }
        }
        // target slot already taken -> tokens merge (rare)
      }
    }
  }

  // --- 3 & 4: split, then death ---
  const warming = t - restartTick < WARMUP_TICKS;
  let population = 0;
  for (let y = 0; y < GH; y++) {
    for (let x = 0; x < GW; x++) {
      const base = (y * GW + x) * ND;
      for (let d = 0; d < ND; d++) {
        const si = base + d;
        if (!nocc[si]) continue;

        if (!warming) {
          const g = ngen[si];
          let c = ncd[si] - 1;
          if (bounced[si] && c <= 0) {
            c = cooldownFor(g);
            const h = hash(x, y, t);
            const sign = h & 1 ? 1 : -1;
            const mag = 1 + ((h >>> 1) & 1); // 1 or 2 slots
            const cslot = base + ((d + sign * mag + ND) % ND);
            if (!nocc[cslot]) {
              const cg = Math.min(g + 1, CFG.gmax);
              nocc[cslot] = 1;
              ngen[cslot] = cg;
              ncd[cslot] = cooldownFor(cg);
              nspl[cslot] = 0;
              nborn[cslot] = t;
              nacc[cslot] = 0;

              if (++nspl[si] >= CFG.maxSplits) {
                nocc[si] = 0; // died producing its last child
                continue;
              }
            }
          }
          ncd[si] = c;
        }
        population++;
      }
    }
  }

  // Global cull: past cullAt, everything dies except the most recently born
  // token, which resets to a fresh progenitor and re-populates in place.
  if (population >= CFG.cullAt) {
    let bestBorn = -1, bestIdx = -1;
    for (let i = 0; i < S; i++) {
      if (nocc[i] && nborn[i] > bestBorn) { bestBorn = nborn[i]; bestIdx = i; }
    }
    if (bestIdx >= 0) {
      for (let i = 0; i < S; i++) if (i !== bestIdx) nocc[i] = 0;
      ngen[bestIdx] = 1;
      ncd[bestIdx] = cooldownFor(1);
      nspl[bestIdx] = 0;
      nborn[bestIdx] = t;
      restartTick = t; // warm-up restarts too
    }
  }

  [occ, nocc] = [nocc, occ];
  [gen, ngen] = [ngen, gen];
  [cd, ncd] = [ncd, cd];
  [spl, nspl] = [nspl, spl];
  [born, nborn] = [nborn, born];
  [acc, nacc] = [nacc, acc];

  if (population === 0) seed(t + 1);
}

// Pixel position of a token sitting at cell (cx,cy) with leftover movement
// budget accVal along heading d. Used both as a tick's end-of-motion point
// and, for the following tick, as its exact start-of-motion anchor — same
// formula both times, so frame-to-frame position is always continuous.
function anchorPx(cx, cy, accVal, d) {
  const f = accVal / SPEED_SCALE;
  return [(cx + 0.5 + VX[d] * f) * CS, (cy + 0.5 + VY[d] * f) * CS];
}

// Fraction (0-1) along the straight run from (p0x,p0y) with displacement
// (dx,dy) at which it first crosses a wall — i.e. where the true bounce
// point sits.
function kinkFraction(p0x, p0y, dx, dy) {
  let f = 1;
  if (dx > 0) f = Math.min(f, (WALL_RIGHT - p0x) / dx);
  else if (dx < 0) f = Math.min(f, (WALL_LEFT - p0x) / dx);
  if (dy > 0) f = Math.min(f, (WALL_BOTTOM - p0y) / dy);
  else if (dy < 0) f = Math.min(f, (WALL_TOP - p0y) / dy);
  if (!isFinite(f)) f = 0.5;
  return Math.min(0.98, Math.max(0.02, f));
}

function render(alpha) {
  ctx.fillStyle = "#000";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  // Boundary lines — the left/right bounce walls, drawn where they are.
  // Germs never overlap them (the wall sits R_OUTER inside each line), so
  // draw order relative to the germs below doesn't matter.
  ctx.fillStyle = LINE_COLOR;
  ctx.fillRect(CFG.lineInset - CFG.lineThick / 2, 0, CFG.lineThick, canvas.height);
  ctx.fillRect(canvas.width - CFG.lineInset - CFG.lineThick / 2, 0, CFG.lineThick, canvas.height);

  ctx.lineWidth = STROKE;
  ctx.strokeStyle = COLOR;

  // Smooth motion: a token's true grid speed pulses (whole hops per tick), so
  // instead of interpolating this tick's integer displacement directly, each
  // tick is drawn as a continuous pixel-space path from where it ended up
  // last tick to where it lands this tick.
  //
  // A tick with no bounce is a single straight leg at the token's current
  // heading (algebraically the same line the old single-formula version
  // drew). A tick where the token bounced is drawn as two legs meeting
  // exactly at the wall — leg 1 at the pre-bounce heading, leg 2 at the
  // post-bounce heading — so frame-to-frame position never snaps, but the
  // corner at the wall stays sharp instead of getting rounded off.
  for (let ci = 0; ci < N; ci++) {
    const base = ci * ND;
    const cx = ci % GW;
    const cy = (ci / GW) | 0;
    for (let d = 0; d < ND; d++) {
      const si = base + d;
      if (!occ[si]) continue;

      const nomV = speedFor(gen[si]) / SPEED_SCALE; // vectors advanced per tick
      const pEnd = anchorPx(cx, cy, acc[si], d);
      let px, py;

      if (!bounced[si]) {
        const p0x = pEnd[0] - nomV * CS * VX[d];
        const p0y = pEnd[1] - nomV * CS * VY[d];
        px = p0x + (pEnd[0] - p0x) * alpha;
        py = p0y + (pEnd[1] - p0y) * alpha;
      } else {
        const sd = srcDIR[si];
        const [p0x, p0y] = anchorPx(srcCX[si], srcCY[si], srcACC[si], sd);
        const naiveX = p0x + nomV * CS * VX[sd];
        const naiveY = p0y + nomV * CS * VY[sd];
        const f = kinkFraction(p0x, p0y, naiveX - p0x, naiveY - p0y);
        const kx = p0x + (naiveX - p0x) * f;
        const ky = p0y + (naiveY - p0y) * f;
        if (alpha < f) {
          px = p0x + (kx - p0x) * (alpha / f);
          py = p0y + (ky - p0y) * (alpha / f);
        } else {
          const t = (alpha - f) / (1 - f);
          px = kx + (pEnd[0] - kx) * t;
          py = ky + (pEnd[1] - ky) * t;
        }
      }

      ctx.beginPath();
      ctx.arc(px, py, R_OUTER - STROKE / 2, 0, Math.PI * 2);
      ctx.stroke();
    }
  }
}

// ---- control panel ----

const CONTROLS = [
  { key: "tSeconds", label: "Cooldown", min: 2, max: 60, step: 1, unit: "s" },
  {
    key: "warmupSeconds", label: "Warm-up", min: 0, max: 360, step: 5, unit: "s",
    fmt: (v) => (v < 60 ? v + "s" : (v / 60).toFixed(v % 60 ? 1 : 0) + "m"),
  },
  { key: "maxSplits", label: "Max splits", min: 1, max: 8, step: 1, unit: "" },
  { key: "cullAt", label: "Cull at", min: 10, max: 400, step: 5, unit: "" },
  { key: "childSpeedup", label: "Child speed-up", min: 0, max: 50, step: 1, unit: "%", pct: true },
  { key: "gmax", label: "Max generation", min: 1, max: 8, step: 1, unit: "" },
  { key: "tickEvery", label: "Motion pace", min: 2, max: 10, step: 1, unit: "" },
  { key: "ringRadius", label: "Ring radius", min: 40, max: 260, step: 5, unit: "px" },
  { key: "cellSize", label: "Cell size", min: 4, max: 12, step: 1, unit: "px", rebuild: true },
  { key: "lineInset", label: "Line inset", min: 10, max: 300, step: 5, unit: "px" },
  { key: "lineThick", label: "Line thickness", min: 1, max: 20, step: 1, unit: "px" },
];

function buildPanel() {
  const host = document.getElementById("controls");
  if (!host) return;
  const rows = [];

  for (const c of CONTROLS) {
    const row = document.createElement("label");
    row.className = "row";
    const name = document.createElement("span");
    name.className = "name";
    name.textContent = c.label;
    const val = document.createElement("span");
    val.className = "val";
    const input = document.createElement("input");
    input.id = c.key;
    input.type = "range";
    input.min = c.min; input.max = c.max; input.step = c.step;
    const toSlider = (v) => (c.pct ? Math.round(v * 100) : v);
    input.value = toSlider(CFG[c.key]);
    const sync = () => {
      const raw = +input.value;
      CFG[c.key] = c.pct ? raw / 100 : raw;
      val.textContent = c.fmt ? c.fmt(raw) : raw + c.unit;
      if (c.rebuild) rebuildGrid();
      else recompute();
    };
    input.addEventListener("input", sync);
    sync();
    row.append(name, val, input);
    host.appendChild(row);
    rows.push({ c, set: (v) => { input.value = toSlider(v); sync(); } });
  }

  const on = (id, fn) => {
    const el = document.getElementById(id);
    if (el) el.onclick = fn;
  };

  on("reset", () => { for (const r of rows) r.set(DEFAULTS[r.c.key]); });
  on("restart", () => hardRestart());
  on("pause", () => {
    paused = !paused;
    document.getElementById("pause").textContent = paused ? "Resume" : "Pause";
  });

  const panel = document.getElementById("panel");
  on("toggle", () => {
    panel.classList.toggle("collapsed");
    document.getElementById("toggle").textContent =
      panel.classList.contains("collapsed") ? "show" : "hide";
  });

  // Readme overlay — text is embedded in index.html (#readme-src) so this works
  // straight from file:// with no server.
  const overlay = document.getElementById("readme-overlay");
  const textEl = document.getElementById("readme-text");
  const src = document.getElementById("readme-src");
  if (textEl && src) textEl.textContent = src.textContent.trim();
  on("readme", () => { if (overlay) overlay.hidden = false; });
  on("readme-close", () => { overlay.hidden = true; });
  if (overlay) overlay.addEventListener("click", (e) => {
    if (e.target === overlay) overlay.hidden = true;
  });
}

// ---- responsive layout ----

// The panel sits beside the canvas (see CSS) as long as there's room for
// both, at its own fixed size — it does not resize or scale with the
// window. When the viewport is too narrow for that, add .narrow to
// <body> — CSS floats the panel over the canvas instead of reserving flex
// space for it — and auto-collapse it to its small header-only state.
// Crossing back over the threshold auto-expands it again. The manual
// hide/show toggle still works independently of this within either mode.
const PANEL_WIDTH = 220; // keep in sync with #panel's CSS width
const LAYOUT_GAP = 14; // keep in sync with body's CSS gap

function layoutResponsive() {
  const panel = document.getElementById("panel");
  if (!panel) return;
  const aspect = canvas.width / canvas.height;
  const canvasW = window.innerHeight * aspect;
  const narrow = window.innerWidth < canvasW + PANEL_WIDTH + LAYOUT_GAP;

  const wasNarrow = document.body.classList.contains("narrow");
  document.body.classList.toggle("narrow", narrow);
  if (narrow !== wasNarrow) {
    panel.classList.toggle("collapsed", narrow);
    const btn = document.getElementById("toggle");
    if (btn) btn.textContent = narrow ? "show" : "hide";
  }
}

// ---- boot ----

rebuildGrid();
buildPanel();
layoutResponsive();
window.addEventListener("resize", layoutResponsive);

// Ticks are paced by wall-clock time, not by how many frames actually get
// rendered — so the simulation runs at the same real-world speed whether
// the browser manages 60fps or a much lower rate (e.g. on a slower mobile
// device). CFG.tickEvery is "render frames per tick" at a nominal 60fps,
// so one tick nominally takes (tickEvery / 60) seconds of real time;
// that's the interval ticksMsPerTick() reproduces regardless of the
// actual frame rate achieved.
const NOMINAL_FPS = 60;
const MAX_FRAME_DT_MS = 250; // clamp a stall (e.g. backgrounded tab) so it can't cause a huge catch-up burst
const MAX_TICKS_PER_FRAME = 10; // cap how much a single frame can catch up by

let lastFrameT = null;

function msPerTick() {
  return (CFG.tickEvery / NOMINAL_FPS) * 1000;
}

function frame(now) {
  if (lastFrameT === null) lastFrameT = now;
  const dt = Math.min(now - lastFrameT, MAX_FRAME_DT_MS);
  lastFrameT = now;

  if (!paused) {
    tickAccumulatorMs += dt;
    const tickMs = msPerTick();
    let ticksRun = 0;
    while (tickAccumulatorMs >= tickMs && ticksRun < MAX_TICKS_PER_FRAME) {
      tick(tickNo++);
      tickAccumulatorMs -= tickMs;
      ticksRun++;
    }
    render(Math.min(1, tickAccumulatorMs / tickMs));
  }

  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);
