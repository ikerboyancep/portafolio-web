/*--------------------------------------------------------------*\
 |  Iker Boyancé — Portafolio Interactivo (JS Completo)
 |--------------------------------------------------------------|
 |  - Loops gapless sincronizados (mute/unmute por GainNode)
 |  - Fluido reactivo con drag sostenido + filtro lowpass
 |  - Paletas dinámicas según combinaciones activas (suaves)
 |  - DevMixer (UI de volúmenes) activable por constante
 |  - Fade de audio al reproducir YouTube en overlays
 |  - Overlays “Proyectos” / “Sobre mí” sin duplicaciones
 |  - Intro con “Haz click para comenzar” (blink sutil)
\*--------------------------------------------------------------*/


/*==============================================================*\
 |  Configuración visual y flags globales
\*==============================================================*/
const TEXT_COLOR = '#ffd7a3';
const ACCENT_COLOR = '#ffb366';

// DevMixer: cambia a true para ver el mezclador de volúmenes por pista
const DEV_MIXER_ENABLED = false;

// Control de creación para evitar duplicados
let STATE = {
  introMounted: false,
  introStarted: false,
  loopPanelCreated: false,
  overlayCreated: false,
  devMixerOpen: false,
};


/*==============================================================*\
 |  Referencias iniciales del DOM
\*==============================================================*/
let introEl;
let startHintEl;   // “Haz click para comenzar”
let canvasEl;


/*==============================================================*\
 |  Audio Graph y Control de Loops
\*==============================================================*/

// Allow runtime override (useful when swapping files without rebuilding):
// window.TRACKS_OVERRIDE = [ { name: 'Drums', url: '...' }, ... ];
let TRACKS = window.TRACKS_OVERRIDE || [
  { name: "Drums", url: "https://cdn.jsdelivr.net/gh/ikerboyancep/Portafolio@10d436d16ceebb5ee942cea8b27352ba5b8377a0/LobbyDRUMS.wav" },
  { name: "Pad",   url: "https://cdn.jsdelivr.net/gh/ikerboyancep/Portafolio@10d436d16ceebb5ee942cea8b27352ba5b8377a0/LobbyPADS.wav" },
  { name: "Piano",  url: "https://cdn.jsdelivr.net/gh/ikerboyancep/Portafolio@10d436d16ceebb5ee942cea8b27352ba5b8377a0/LobbyBASS.wav" },
];

// FFT y configuración base de análisis espectral
const TOTAL_BANDS = 256;
const FFT_SIZE = TOTAL_BANDS * 2;

// Contexto y nodos de audio
let audioCtx, analyser, analyserData;
let masterGain, bgGain;
let filterNode;

// Buffers y estados de las pistas
let trackBuffers = new Array(TRACKS.length).fill(null);
let trackGains   = new Array(TRACKS.length).fill(null);
let trackSources = new Array(TRACKS.length).fill(null);
let trackMuted   = new Array(TRACKS.length).fill(true);  // Por defecto muteadas
// References to the DOM buttons for each track so we can update visuals when state changes
let trackButtons  = new Array(TRACKS.length).fill(null);

// Sincronización temporal
let masterStartTime = null;
let LOOP_DURATION = 8.0; // segundos (ajustar si los archivos duran diferente)
let spectrumPullRAF = null;



/*==============================================================*\
 |  Paletas Dinámicas y Colores
\*==============================================================*/

/**
 * Paletas base (armonía “luz – sombra – fuego – agua – aire”)
 * Cada pista aporta un conjunto cromático para el fluido reactivo.
 */
const COLOR_THEMES = {
  Bass:       { top: "#0E4FBF", mid: "#17A39D", bot: "#0A347A" },
  Drums:      { top: "#D44B00", mid: "#F26B2E", bot: "#FF8C4A" },
  Percussion: { top: "#FFD43B", mid: "#FFE071", bot: "#FFF3A1" },
  "Vocal 1":  { top: "#B56AF0", mid: "#BA68F7", bot: "#8845E5" },
  "Vocal 2":  { top: "#F5429E", mid: "#FF7BBF", bot: "#FFB3D9" },
  "Vocal 3":  { top: "#26E0FF", mid: "#10B8E3", bot: "#0A91C5" },
  Strings:    { top: "#10DE98", mid: "#40E9AD", bot: "#05966E" },
};

// If you swap track names / add new files, ensure there's a theme for each track
function ensureThemesForTracks() {
  if (!Array.isArray(TRACKS)) return;
  TRACKS.forEach((t) => {
    if (!t || !t.name) return;
    // Automatic mappings for renamed/new tracks -> reuse existing themes
    if (!COLOR_THEMES[t.name]) {
      if (t.name === "Pad" && COLOR_THEMES["Percussion"]) {
        COLOR_THEMES[t.name] = Object.assign({}, COLOR_THEMES["Percussion"]);
        console.info(`Mapped theme: Pad -> Percussion`);
        return;
      }
      if (t.name === "Piano" && COLOR_THEMES["Strings"]) {
        COLOR_THEMES[t.name] = Object.assign({}, COLOR_THEMES["Strings"]);
        console.info(`Mapped theme: Piano -> Strings`);
        return;
      }

      // Generate a neutral fallback palette (subtle desaturated blue-purple)
      COLOR_THEMES[t.name] = { top: "#7f7fb0", mid: "#6a6a90", bot: "#3f3f6a" };
      console.warn(`Added fallback COLOR_THEME for unknown track name: ${t.name}`);
    }
  });
}

// Run once on load to guarantee themes exist for all TRACKS entries
ensureThemesForTracks();


/**
 * Fondo frío ↔ cálido para el gradiente general (mezcla según actividad)
 */
const BG_COLD = { bg1: "#060918", bg2: "#0e1030" };
const BG_WARM = { bg1: "#30130b", bg2: "#3a1a0e" };

/**
 * Mezcla cromática global
 * 0 = frío | 1 = cálido
 */
let paletteMix = 0.45;

/**
 * Energía del fluido → brillo / saturación leve
 */
let energyLumaBoost = 0; // rango 0..1

// Runtime tunables (used by DevMixer and nav positioning)
let navOffsetPx = -35; // pixels between intro bottom and nav top (negative moves nav up)


/*==============================================================*\
 |  Canvas Fluid Engine — Interacción y Renderizado
\*==============================================================*/

const NUM_POINTS = 120;
const INTERACTIVE_SPREAD = Math.ceil(NUM_POINTS / 10);
const MOUSE_POW = 0.002;
let baseYFactor = 1.6;

/*--------------------------------------------------------------*\
 |  Clases base: Point y Wave
\*--------------------------------------------------------------*/
class Point {
  constructor(x, y) {
    this.x = x;
    this.y = y;
    this.vy = 0;
    this.mass = 1.3;
  }
}

class Wave {
  constructor(points, p1, p2) {
    const dx = (p2.x - p1.x) / (points - 1);
    this.points = Array.from({ length: points }, (_, i) => new Point(p1.x + dx * i, p1.y));
  }
}

/*--------------------------------------------------------------*\
 |  Clase principal: CanvasFluid
\*--------------------------------------------------------------*/
class CanvasFluid {
  constructor() {
    this.canvas = document.getElementById("canvas");
    canvasEl = this.canvas;
    this.dpr = window.devicePixelRatio || 1;
    this.ctx = this.canvas.getContext("2d");
    this.ctx.scale(this.dpr, this.dpr);
    this.ctx.imageSmoothingEnabled = true;

    // Propiedades físicas base
    this.SPRING = 0.005;
    this.DAMPING = 0.75;
    this.WAVE_HEIGHT = 300;
    this.WAVE_DETAIL = 0.05;
    this.PULSE_SPEED = 0.002;

    // Campos de energía y velocidad
    this.energyField = new Array(NUM_POINTS).fill(0);
    this.velocityField = new Array(NUM_POINTS).fill(0);
    this.motionBlurAlpha = 0; // se eleva con interacción

    // Control de interacción
    this.mouse = {
      x: 0,
      y: 0,
      startY: 0,
      mousedown: false,
      dragAmount: 0,
      holdForce: 0,
    };

    // Eventos principales
    this.setCanvasSize();
    window.addEventListener("resize", () => this.setCanvasSize());
    window.addEventListener("mousedown", (e) => this.onDown(e));
    window.addEventListener("mousemove", (e) => this.onMove(e));
    window.addEventListener("mouseup", () => this.onUp());
    window.addEventListener("touchstart", (e) => this.onTouchStart(e), { passive: true });
    window.addEventListener("touchmove", (e) => this.onTouchMove(e), { passive: true });
    window.addEventListener("touchend", () => this.onUp());

    // Construcción y render loop
    this.constructWave();
    requestAnimationFrame(this.render.bind(this));
  }

  /*------------------------------------------------------------*\
   |  Ajuste de tamaño dinámico
  \*------------------------------------------------------------*/
  setCanvasSize() {
    const w = window.innerWidth, h = window.innerHeight;
    this.canvas.width = w * this.dpr;
    this.canvas.height = h * this.dpr;
    this.canvas.style.width = w + "px";
    this.canvas.style.height = h + "px";
    this.baseY = this.canvas.height / baseYFactor;
    this.constructWave();
  }

  constructWave() {
    const offset = this.canvas.width * 0.08;
    this.wave = new Wave(NUM_POINTS, new Point(-offset, this.baseY), new Point(this.canvas.width + offset, this.baseY));
  }

  /*------------------------------------------------------------*\
   |  Interacción de usuario (Mouse / Touch)
  \*------------------------------------------------------------*/
  onDown(e) {
    this.mouse.mousedown = true;
    this.mouse.startY = e.clientY;
    this.mouse.x = e.clientX * this.dpr;
    this.mouse.holdForce = 0;
    this.triggerWave(this.mouse.x, 3.0);
    this.motionBlurAlpha = 0.06;
  }

  onMove(e) {
    this.mouse.x = e.clientX * this.dpr;
    this.mouse.y = e.clientY * this.dpr;
    if (this.mouse.mousedown) {
      this.applyFilterDrag(e.clientY);
      this.mouse.holdForce = this.mouse.dragAmount;
    }
  }

  onUp() {
    this.mouse.mousedown = false;
    this.mouse.dragAmount = 0;
    this.mouse.holdForce = 0;
    this.setFilterTarget(filterBaseFreq);
  }

  onTouchStart(e) {
    const t = e.touches[0];
    this.mouse.mousedown = true;
    this.mouse.startY = t.clientY;
    this.mouse.x = t.clientX * this.dpr;
    this.mouse.holdForce = 0;
    this.triggerWave(this.mouse.x, 3.0);
    this.motionBlurAlpha = 0.06;
  }

  onTouchMove(e) {
    const t = e.touches[0];
    this.mouse.x = t.clientX * this.dpr;
    this.mouse.y = t.clientY * this.dpr;
    if (this.mouse.mousedown) {
      this.applyFilterDrag(t.clientY);
      this.mouse.holdForce = this.mouse.dragAmount;
    }
  }

  /*------------------------------------------------------------*\
   |  Control del filtro de audio (arrastre vertical)
  \*------------------------------------------------------------*/
  applyFilterDrag(currentClientY) {
    const deltaY = currentClientY - this.mouse.startY;
    this.mouse.dragAmount = Math.max(-250, Math.min(250, deltaY));
    if (this.mouse.dragAmount > 0) {
      const norm = Math.min(1, this.mouse.dragAmount / 250);
      const freq = filterBaseFreq - norm * 1700;
      this.setFilterTarget(Math.max(300, freq));
    } else {
      this.setFilterTarget(filterBaseFreq);
    }
  }

  setFilterTarget(freq) {
    if (!filterNode) return;
    this.filterTargetFreq = freq;
  }

  /*------------------------------------------------------------*\
   |  Fuerza continua (click sostenido)
  \*------------------------------------------------------------*/
  injectHoldForce() {
    if (!this.mouse.mousedown) return;
    const pts = this.wave.points;
    let closest = 0, minDist = Infinity;
    for (let i = 0; i < pts.length; i++) {
      const d = Math.abs(pts[i].x - this.mouse.x);
      if (d < minDist) { minDist = d; closest = i; }
    }
    const strength = 8000 * (Math.abs(this.mouse.holdForce) / 250);
    const spread = Math.floor(INTERACTIVE_SPREAD * 4);
    for (let n = -spread; n <= spread; n++) {
      const i = Math.min(Math.max(closest + n, 0), pts.length - 1);
      const falloff = Math.exp(-(n * n) / (spread * 1.4));
      this.velocityField[i] += falloff * (MOUSE_POW * 0.8) * strength;
    }
    this.motionBlurAlpha = Math.min(0.12, this.motionBlurAlpha + 0.005);
  }

  /*------------------------------------------------------------*\
   |  Ondas y Renderizado
  \*------------------------------------------------------------*/
  triggerWave(x, intensity = 1) {
    const pts = this.wave.points;
    let closest = 0, minDist = Infinity;
    for (let i = 0; i < pts.length; i++) {
      const d = Math.abs(pts[i].x - x);
      if (d < minDist) { minDist = d; closest = i; }
    }
    for (let n = -INTERACTIVE_SPREAD; n <= INTERACTIVE_SPREAD; n++) {
      const i = Math.min(Math.max(closest + n, 0), pts.length - 1);
      const falloff = Math.exp(-((n * n) / (INTERACTIVE_SPREAD * 1.3)));
      this.velocityField[i] += falloff * intensity * 3.2;
    }
  }

  updateAudioFilterAndPalette() {
    if (!filterNode) return;
    if (this.filterCurrentFreq === undefined) this.filterCurrentFreq = filterBaseFreq;
    if (this.filterTargetFreq === undefined)  this.filterTargetFreq  = filterBaseFreq;

    this.filterCurrentFreq += (this.filterTargetFreq - this.filterCurrentFreq) * 0.08;
    filterNode.frequency.value = this.filterCurrentFreq;

    const norm = (this.filterCurrentFreq - 300) / (filterBaseFreq - 300);
    const targetMix = Math.min(1, Math.max(0, norm));
    paletteMix += (targetMix - paletteMix) * 0.03;
  }

  /*------------------------------------------------------------*\
   |  Render loop principal
  \*------------------------------------------------------------*/
  drawBackground() {
    const { bg1, bg2 } = getBgColors(1 - paletteMix);
    const g = this.ctx.createLinearGradient(0, 0, 0, this.canvas.height);
    const l = 0.15 * energyLumaBoost;
    g.addColorStop(0, addLuma(bg1, l));
    g.addColorStop(1, addLuma(bg2, -l * 0.5));
    this.ctx.globalAlpha = 0.25;
    this.ctx.fillStyle = g;
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
    this.ctx.globalAlpha = 1;

    if (this.motionBlurAlpha > 0.01) {
      this.ctx.globalCompositeOperation = "screen";
      this.ctx.fillStyle = `rgba(255,255,255,${this.motionBlurAlpha * 0.06})`;
      this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
      this.ctx.globalCompositeOperation = "source-over";
    }
  }

  drawCurve() {
    const ctx = this.ctx;
    const fluid = getFluidColors(paletteMix);
    const highest = Math.min(...this.wave.points.map(p => p.y));
    const grad = ctx.createLinearGradient(0, highest, 0, this.canvas.height);
    const l = 0.25 * energyLumaBoost;
    grad.addColorStop(0, addLuma(fluid.top, l));
    grad.addColorStop(0.5, addLuma(fluid.mid, l * 0.5));
    grad.addColorStop(1, addLuma(fluid.bot, 0));
    ctx.fillStyle = grad;

    ctx.beginPath();
    ctx.moveTo(this.wave.points[0].x, this.wave.points[0].y);
    for (let i = 1; i < this.wave.points.length - 2; i++) {
      const p0 = this.wave.points[i - 1], p1 = this.wave.points[i], p2 = this.wave.points[i + 1], p3 = this.wave.points[i + 2];
      const cp1x = p1.x + (p2.x - p0.x) / 6, cp1y = p1.y + (p2.y - p0.y) / 6;
      const cp2x = p2.x - (p3.x - p1.x) / 6, cp2y = p2.y - (p3.y - p1.y) / 6;
      ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, p2.x, p2.y);
    }
    const first = this.wave.points[0];
    const last = this.wave.points[this.wave.points.length - 1];
    ctx.lineTo(last.x, this.canvas.height);
    ctx.lineTo(first.x, this.canvas.height);
    ctx.closePath();
    ctx.fill();
  }

  updateWave() {
    const pts = this.wave.points;
    if (analyserData) {
      const step = Math.max(1, Math.floor(analyserData.length / NUM_POINTS));
      for (let i = 0; i < NUM_POINTS; i++) {
        let sum = 0;
        for (let j = 0; j < step; j++) sum += analyserData[i * step + j] || 0;
        this.energyField[i] = (sum / step) / 255;
      }
    }

    const avgEnergy = this.energyField.reduce((a, b) => a + b, 0) / (this.energyField.length || 1);
    energyLumaBoost += ((avgEnergy * 1.2) - energyLumaBoost) * 0.05;

    const basePhase = performance.now() * (0.001 + avgEnergy * 0.0015);
    const phaseShift = Math.sin(basePhase) * Math.PI;
    const lateral = Math.sin(basePhase * 0.4) * 1.2;

    if (this.mouse.mousedown) this.injectHoldForce();

    for (let i = 0; i < pts.length; i++) {
      const e = this.energyField[i];
      const wave = Math.sin((i * this.WAVE_DETAIL + lateral) + phaseShift);
      const targetY = this.baseY - wave * (this.WAVE_HEIGHT * (0.35 + e * 1.2));
      const dy = targetY - pts[i].y;
      this.velocityField[i] += this.SPRING * dy;
      this.velocityField[i] *= this.DAMPING;
      pts[i].y += this.velocityField[i];
    }

    this.motionBlurAlpha *= 0.93;
    this.updateAudioFilterAndPalette();
  }

  render() {
    this.drawBackground();
    this.drawCurve();
    this.updateWave();
    requestAnimationFrame(this.render.bind(this));
  }
}


/*==============================================================*\
 |  Funciones de Color y Mezclas
\*==============================================================*/

/**
 * Convierte un color hexadecimal o RGB string a objeto {r, g, b}.
 */
function hexToRgb(hex) {
  if (hex.startsWith("rgb")) {
    const m = hex.match(/rgb\((\d+),\s*(\d+),\s*(\d+)\)/);
    if (!m) return { r: 0, g: 0, b: 0 };
    return { r: +m[1], g: +m[2], b: +m[3] };
  }
  const v = parseInt(hex.replace('#', ''), 16);
  return { r: (v >> 16) & 255, g: (v >> 8) & 255, b: v & 255 };
}

/**
 * Convierte {r, g, b} en string RGB.
 */
function rgbToHex({ r, g, b }) {
  const c = (n) => Math.max(0, Math.min(255, Math.round(n)));
  return `rgb(${c(r)},${c(g)},${c(b)})`;
}

/**
 * Mezcla dos colores RGB (t = 0..1).
 */
function mixRgb(c1, c2, t) {
  return rgbToHex({
    r: c1.r * (1 - t) + c2.r * t,
    g: c1.g * (1 - t) + c2.g * t,
    b: c1.b * (1 - t) + c2.b * t
  });
}

/**
 * Ajusta la luminosidad agregando un valor de brillo (amt = 0..1).
 */
function addLuma(hex, amt) {
  const c = hexToRgb(hex);
  const l = 255 * amt;
  return rgbToHex({ r: c.r + l, g: c.g + l, b: c.b + l });
}

/**
 * Obtiene los colores del fluido según el “paletteMix” (frío ↔ cálido).
 */
function getFluidColors(t) {
  const target = combinedThemeFromActive();
  const top = mixRgb(hexToRgb(target.cold.top), hexToRgb(target.warm.top), t);
  const mid = mixRgb(hexToRgb(target.cold.mid), hexToRgb(target.warm.mid), t);
  const bot = mixRgb(hexToRgb(target.cold.bot), hexToRgb(target.warm.bot), t);
  return { top, mid, bot };
}

/**
 * Obtiene los colores de fondo gradiente mezclando entre BG_COLD y BG_WARM.
 */
function getBgColors(invT) {
  const bg1 = mixRgb(hexToRgb(BG_COLD.bg1), hexToRgb(BG_WARM.bg1), 1 - invT);
  const bg2 = mixRgb(hexToRgb(BG_COLD.bg2), hexToRgb(BG_WARM.bg2), 1 - invT);
  return { bg1, bg2 };
}

/**
 * Calcula mezcla de paletas según pistas activas.
 * Retorna { cold: {...}, warm: {...} }
 */
function combinedThemeFromActive() {
  let coldAcc = { top: [0, 0, 0], mid: [0, 0, 0], bot: [0, 0, 0], w: 0 };
  let warmAcc = { top: [0, 0, 0], mid: [0, 0, 0], bot: [0, 0, 0], w: 0 };

  TRACKS.forEach((t, i) => {
    const active = !trackMuted[i];
    const weight = active ? 1 : 0.25;
    const theme = COLOR_THEMES[t.name];
    if (!theme) return;

  const isWarm = (t.name === "Drums" || t.name === "Percussion" || t.name === "Pad");
    const target = isWarm ? warmAcc : coldAcc;

    const top = hexToRgb(theme.top);
    const mid = hexToRgb(theme.mid);
    const bot = hexToRgb(theme.bot);

    target.top[0] += top.r * weight; target.top[1] += top.g * weight; target.top[2] += top.b * weight;
    target.mid[0] += mid.r * weight; target.mid[1] += mid.g * weight; target.mid[2] += mid.b * weight;
    target.bot[0] += bot.r * weight; target.bot[1] += bot.g * weight; target.bot[2] += bot.b * weight;
    target.w += weight;
  });

  function avg(arr, w) {
    return w ? rgbToHex({ r: arr[0] / w, g: arr[1] / w, b: arr[2] / w }) : "rgb(0,0,0)";
  }

  const cold = {
    top: avg(coldAcc.top, coldAcc.w),
    mid: avg(coldAcc.mid, coldAcc.w),
    bot: avg(coldAcc.bot, coldAcc.w),
  };
  const warm = {
    top: avg(warmAcc.top, warmAcc.w),
    mid: avg(warmAcc.mid, warmAcc.w),
    bot: avg(warmAcc.bot, warmAcc.w),
  };

  return { cold, warm };
}


/*==============================================================*\
 |  Componentes UI: Intro, Botones, Overlays, Email, LoopPanel
\*==============================================================*/

/*--------------------------------------------------------------*\
 |  Enlace superior de contacto por correo
\*--------------------------------------------------------------*/
function createTopRightEmail() {
  if (document.getElementById("topRightEmailLink")) return;

  const style = document.createElement("style");
  style.textContent = `
    #topRightEmailLink {
      position: fixed; top: 16px; right: 18px; z-index: 1000;
      display: inline-flex; align-items: center; gap: 10px;
      padding: 10px 14px; border-radius: 10px;
      border: 1px solid rgba(200,180,255,0.5);
      background: rgba(255,255,255,0.08);
      box-shadow: 0 0 10px rgba(255,180,120,0.25);
      text-decoration: none;
      -webkit-backdrop-filter: blur(6px);
      backdrop-filter: blur(6px);
      transition: transform .2s ease, background .2s ease,
                  box-shadow .2s ease, border-color .2s ease;
    }
    #topRightEmailLink:hover {
      background: rgba(255,255,255,0.18);
      transform: translateY(-1px);
      box-shadow: 0 4px 16px rgba(255,180,120,0.35);
      border-color: rgba(220,200,255,0.8);
    }
    #topRightEmailLink .label {
      font-family: Cinzel, serif;
      font-size: 0.95rem;
      letter-spacing: .2px;
      color: ${TEXT_COLOR};
    }
    #topRightEmailLink .dot {
      width: 6px; height: 6px; border-radius: 999px;
      opacity: .9; background: ${ACCENT_COLOR};
    }
  `;
  document.head.appendChild(style);

  const a = document.createElement("a");
  a.id = "topRightEmailLink";
  const subject = encodeURIComponent("Portafolio 2025 — Contacto");
  const body = encodeURIComponent("Hola Iker,\n\nTe escribo a partir de tu portafolio. Me gustaría conversar sobre...\n\n—");
  a.href = `mailto:iker.boyancep@gmail.com?subject=${subject}&body=${body}`;
  a.rel = "noopener";
  a.title = "Escríbeme por correo";
  a.innerHTML = `<span style="font-size:1.05rem">✉︎</span><span class="label">Contacto</span><span class="dot"></span>`;
  document.body.appendChild(a);
}

/*--------------------------------------------------------------*\
 |  Texto de inicio “Haz click para comenzar”
\*--------------------------------------------------------------*/
function createStartHint() {
  const old = document.getElementById("startHint");
  if (old) old.remove();

  startHintEl = document.createElement("div");
  startHintEl.id = "startHint";
  Object.assign(startHintEl.style, {
    position: "absolute",
    top: "calc(50% + 72px)",
    left: "50%",
    transform: "translateX(-50%)",
    color: TEXT_COLOR,
    fontFamily: "Cinzel, serif",
    fontSize: "0.95rem",
    letterSpacing: "0.4px",
    opacity: "0.85",
    animation: "blink 1.8s ease-in-out infinite",
    zIndex: 21,
    userSelect: "none",
    pointerEvents: "none",
  });
  startHintEl.textContent = "Haz click para comenzar";

  const style = document.createElement("style");
  style.textContent = `
    @keyframes blink {
      0%, 100% { opacity: .85; transform: translateX(-50%) translateY(0); }
      50%      { opacity: .45; transform: translateX(-50%) translateY(1px); }
    }
  `;
  document.head.appendChild(style);
  document.body.appendChild(startHintEl);
}

/*--------------------------------------------------------------*\
 |  Overlays de secciones (Proyectos / Sobre mí)
\*--------------------------------------------------------------*/
let overlayEl = null;
let currentSection = null;

const PROJECTS = [
  {
    titulo: "Concept Art — Warrior Rabbit",
    imagen: "AnimWarriorRabbit.png",
    descripcion:
      "Exploración visual de personaje y atmósfera mediante composición cinematográfica, silueta expresiva y dirección de color.",
    herramientas: "Photoshop",
  },

  {
    titulo: "Ilustración Digital — Parcial 2",
    imagen: "Dib_Parcial2_IkerBoyance_Ilustración.jpg",
    descripcion:
      "Ilustración digital enfocada en narrativa visual, iluminación dramática y acabado atmosférico dentro de una composición de formato panorámico.",
    herramientas: "Photoshop",
  },

  {
    titulo: "Dibujo Digital — Actividad 15",
    imagen: "Dib_Actividad15_IkerBoyance.png",
    descripcion:
      "Pieza de dibujo digital desarrollada para explorar textura, lectura visual y construcción de una identidad gráfica con presencia editorial.",
    herramientas: "Photoshop",
  },

  {
    titulo: "Ilustración Digital — Ordinario",
    imagen: "DibDigital_IkerBoyance_ORDINARIO_Exportación.jpg",
    descripcion:
      "Ilustración digital de formato vertical centrada en composición, tratamiento de luz y construcción de una escena con intención narrativa.",
    herramientas: "Photoshop",
  },

  {
    titulo: "Uri — Primera Demo (2026)",
    video: "https://www.youtube.com/embed/dEJej40Inxo",
    descripcion:
      "Primera demostración jugable de Uri, explorando dirección visual, atmósfera interactiva y diseño de experiencia dentro del proyecto.",
  },

  {
    titulo: "Clip de Rotoscopia (2026)",
    video: "https://www.youtube.com/embed/RMnEIsnHzgY",
    descripcion:
      "Clip experimental de rotoscopia digital enfocado en movimiento, composición visual y atmósfera cinematográfica.",
  },

  {
    titulo: "Walk Cycle + Parallax (2026)",
    video: "https://www.youtube.com/embed/uwqp9ZimmWw",
    descripcion:
      "Animación 2D con walk cycle y efecto parallax para generar profundidad y movimiento cinematográfico dentro del escenario.",
  },

  {
    titulo: "Hand Pattern Recognition System (En desarrollo)",
    video: "https://www.youtube.com/embed/qgqHpcSFZDQ",
    descripcion:
      "Desarrollo experimental de un sistema de reconocimiento de patrones de la mano para interacción en entornos digitales utilizando únicamente la webcam. El modelo identifica articulaciones y gestos sin sensores adicionales, explorando aplicaciones en arte generativo, control por gestos y experiencias inmersivas. Música por Iker Boyancé.",
  },

  {
    titulo: "Uri — Menú principal (2025)",
    video: "https://www.youtube.com/embed/JoyD_b_xtUA",
    descripcion:
      "Menú principal del proyecto Uri. Todo el contenido es de desarrollo propio, ilustración por Isa Choxóm.",
  },

  {
    titulo: "Fractals (2025)",
    video: "https://www.youtube.com/embed/rp6Q4swlmvE",
    descripcion:
      "Prototipo de FPS con gravedad omnidireccional y mecánicas reactivas a la música. Proyecto de desarrollo propio que integra concepto, programación y dirección audiovisual.",
  },
];

function getYouTubeEmbedUrl(videoUrl) {
  let src = videoUrl || "";
  if (src.indexOf("enablejsapi=1") === -1) {
    src +=
      (src.indexOf("?") === -1 ? "?" : "&") +
      "enablejsapi=1&rel=0&origin=" +
      encodeURIComponent(location.origin);
  }
  return src;
}

function openProjectLightbox(project) {
  const lightbox = document.createElement("div");
  lightbox.className = "projectLightbox";

  const panel = document.createElement("div");
  panel.className = "projectLightboxPanel";

  const closeButton = document.createElement("button");
  closeButton.className = "projectLightboxClose";
  closeButton.type = "button";
  closeButton.setAttribute("aria-label", "Cerrar vista ampliada");
  closeButton.textContent = "×";

  const title = document.createElement("h2");
  title.className = "projectLightboxTitle";
  title.textContent = project.titulo;

  const media = document.createElement("div");
  media.className = "projectLightboxMedia";

  if (project.video) {
    const iframe = document.createElement("iframe");
    iframe.src = getYouTubeEmbedUrl(project.video);
    iframe.setAttribute("frameborder", "0");
    iframe.setAttribute("allow", "autoplay; fullscreen; encrypted-media");
    iframe.setAttribute("allowfullscreen", "");
    media.appendChild(iframe);
  } else if (project.imagen) {
    const image = document.createElement("img");
    image.src = project.imagen;
    image.alt = project.titulo || "Proyecto ampliado";
    media.appendChild(image);
  }

  const desc = document.createElement("p");
  desc.className = "projectLightboxDescription";
  desc.textContent = project.descripcion;

  panel.appendChild(closeButton);
  panel.appendChild(title);
  panel.appendChild(media);
  panel.appendChild(desc);

  if (project.herramientas) {
    const tools = document.createElement("p");
    tools.className = "projectLightboxTools";
    tools.textContent = project.herramientas;
    panel.appendChild(tools);
  }

  lightbox.appendChild(panel);
  document.body.appendChild(lightbox);

  const closeLightbox = () => {
    document.removeEventListener("keydown", handleKeydown);
    lightbox.classList.remove("visible");
    setTimeout(() => {
      lightbox.remove();
      rebindYouTubePlayers();
    }, 180);
  };
  const handleKeydown = (event) => {
    if (event.key === "Escape") closeLightbox();
  };

  closeButton.addEventListener("click", closeLightbox);
  lightbox.addEventListener("click", (event) => {
    if (event.target === lightbox) closeLightbox();
  });
  document.addEventListener("keydown", handleKeydown);

  requestAnimationFrame(() => lightbox.classList.add("visible"));
  closeButton.focus();
  rebindYouTubePlayers();
}

function createProjectMedia(project, onExpand) {
  const mediaWrap = document.createElement("div");
  mediaWrap.className = "projectMedia";

  mediaWrap.addEventListener("click", (event) => {
    if (event.target.tagName === "IFRAME") return;
    event.stopPropagation();
    onExpand();
  });

  if (project.video) {
    const iframe = document.createElement("iframe");
    iframe.src = getYouTubeEmbedUrl(project.video);
    iframe.setAttribute("frameborder", "0");
    iframe.setAttribute("allow", "autoplay; fullscreen; encrypted-media");
    iframe.setAttribute("allowfullscreen", "");
    iframe.style.cssText = "position:absolute;top:0;left:0;width:100%;height:100%;";
    mediaWrap.appendChild(iframe);
  }

  if (project.imagen) {
    const image = document.createElement("img");
    image.className = "projectImage";
    image.src = project.imagen;
    image.alt = project.titulo || "Ilustración del proyecto";
    image.loading = "lazy";
    mediaWrap.appendChild(image);
  }

  const expandButton = document.createElement("button");
  expandButton.className = "projectExpandButton";
  expandButton.type = "button";
  expandButton.setAttribute("aria-label", "Ampliar " + project.titulo);
  expandButton.textContent = "⤢";
  expandButton.addEventListener("click", (event) => {
    event.stopPropagation();
    onExpand();
  });
  mediaWrap.appendChild(expandButton);

  return mediaWrap;
}

function createProjectCard(project) {
  const card = document.createElement("div");
  card.className = "projectCard";
  Object.assign(card.style, {
    background: "rgba(15,10,30,0.95)",
    border: "1px solid rgba(255,200,150,0.4)",
    borderRadius: "12px",
    boxShadow: "0 0 25px rgba(255,150,100,0.3)",
    width: "320px",
    flex: "0 0 320px",
    padding: "15px",
    transform: "scale(0.96)",
    opacity: "0",
    transition: "transform 200ms ease, opacity 180ms ease, box-shadow 200ms ease",
  });

  card.onmouseenter = () => {
    card.style.transform = "scale(1.05)";
    card.style.boxShadow = "0 0 35px rgba(255,180,120,0.6)";
  };
  card.onmouseleave = () => {
    card.style.transform = "scale(1)";
    card.style.boxShadow = "0 0 25px rgba(255,150,100,0.3)";
  };
  card.addEventListener("click", (event) => {
    if (event.target.closest("iframe, button")) return;
    openProjectLightbox(project);
  });

  const title = document.createElement("h3");
  title.style.cssText = "font-family:'Cinzel',serif;color:" + TEXT_COLOR + ";text-align:center;";
  title.textContent = project.titulo;

  const desc = document.createElement("p");
  desc.style.cssText =
    "font-family:'Cinzel',serif;color:" +
    ACCENT_COLOR +
    ";font-size:0.9rem;text-align:center;margin-top:10px;";
  desc.textContent = project.descripcion;

  card.appendChild(title);
  card.appendChild(createProjectMedia(project, () => openProjectLightbox(project)));
  card.appendChild(desc);

  if (project.herramientas) {
    const tools = document.createElement("p");
    tools.className = "projectTools";
    tools.textContent = project.herramientas;
    card.appendChild(tools);
  }

  return card;
}

function createCarouselHoverZone(direction, track) {
  const zone = document.createElement("div");
  zone.className = "projectCarouselHoverZone projectCarouselHoverZone--" + direction;
  zone.setAttribute("aria-hidden", "true");
  return zone;
}

function buildProjectsGrid(projects) {
  const carousel = document.createElement("div");
  carousel.className = "projectCarousel";

  const track = document.createElement("div");
  track.className = "projectCarouselTrack";

  projects.forEach((project) => track.appendChild(createProjectCard(project)));

  let hoverFrameId = null;
  let hoverSpeed = 0;

  const stopHoverScroll = () => {
    hoverSpeed = 0;
    if (!hoverFrameId) return;
    cancelAnimationFrame(hoverFrameId);
    hoverFrameId = null;
  };

  const hoverScroll = () => {
    track.scrollLeft += hoverSpeed;
    hoverFrameId = hoverSpeed === 0 ? null : requestAnimationFrame(hoverScroll);
  };

  const startHoverScroll = (speed) => {
    hoverSpeed = speed;
    if (hoverFrameId) return;
    hoverFrameId = requestAnimationFrame(hoverScroll);
  };

  const handleHoverScroll = (event) => {
    const rect = carousel.getBoundingClientRect();
    const edgeSize = Math.min(140, rect.width * 0.18);

    if (event.clientX < rect.left + edgeSize) {
      startHoverScroll(-7);
    } else if (event.clientX > rect.right - edgeSize) {
      startHoverScroll(7);
    } else {
      stopHoverScroll();
    }
  };

  carousel.addEventListener("mousemove", handleHoverScroll);
  carousel.addEventListener("pointermove", handleHoverScroll);
  carousel.addEventListener("mouseleave", stopHoverScroll);
  carousel.addEventListener("pointerleave", stopHoverScroll);

  track.addEventListener(
    "wheel",
    (event) => {
      if (Math.abs(event.deltaY) <= Math.abs(event.deltaX)) return;
      event.preventDefault();
      track.scrollLeft += event.deltaY;
    },
    { passive: false }
  );

  const prevZone = createCarouselHoverZone("prev", track);
  const nextZone = createCarouselHoverZone("next", track);

  prevZone.addEventListener("mouseenter", () => startHoverScroll(-7));
  nextZone.addEventListener("mouseenter", () => startHoverScroll(7));
  prevZone.addEventListener("mouseleave", stopHoverScroll);
  nextZone.addEventListener("mouseleave", stopHoverScroll);

  carousel.appendChild(prevZone);
  carousel.appendChild(track);
  carousel.appendChild(nextZone);

  return carousel;
}

function setupProjectPopups() {
  if (STATE.overlayCreated) return;
  STATE.overlayCreated = true;

  overlayEl = document.createElement("div");
  Object.assign(overlayEl.style, {
    position: "fixed",
    inset: 0,
    display: "none",
    flexDirection: "column",
    justifyContent: "center",
    alignItems: "center",
    gap: "30px",
    background: "rgba(0,0,10,0.75)",
    backdropFilter: "blur(10px)",
    zIndex: 999,
    opacity: "0",
    transition: "opacity 180ms ease",
  });
  document.body.appendChild(overlayEl);



  /*----------  Grid de proyectos  ----------*/
function createProjectsGrid() {
  return buildProjectsGrid(PROJECTS);
}


  /*----------  Grid “Sobre mí”  ----------*/
  const aboutGrid = document.createElement("div");
  Object.assign(aboutGrid.style, {
    display: "flex",
    flexWrap: "wrap",
    justifyContent: "center",
    alignItems: "stretch",
    gap: "25px",
    width: "90%",
    maxWidth: "1200px",
  });

  const aboutSections = [
    {
      titulo: "Biotecnología",
      texto: `
        <p>Soy estudiante de Biotecnología con enfoque en química de alimentos,
        especializado en el diseño de productos funcionales.</p>
        <p>He desarrollado proyectos como <em>Mel Mortis</em>, una hidromiel roja
        que cambia de color con el primer sorbo, e investigo el uso de bacterias
        electroactivas con integración futura en cultivos autosustentables que reciclan más
        agua y requieren menos energía eléctrica para su monitoreo y cuidado.</p>
        <p>Estudié un minor en Negocios Internacionales en Países Bajos.
        Domino español e inglés, y tengo nivel intermedio de italiano.</p>
      `,
    },
    {
      titulo: "Desarrollo de Videojuegos y Experiencias Interactivas",
      texto: `
        <p>Soy desarrollador creativo con enfoque en programación (JS, Python, C#, C++),
        diseño sonoro y motores como Unity, TouchDesigner y FMOD. Busco crear experiencias
        inmersivas que transmitan un mensaje transformador en cada proyecto.</p>
        <p>Cuento con experiencia en impresión 3D, DaVinci Resolve, gameplay design
        y herramientas para desarrollo de software interactivo enfocado en VR.</p>
      `,
    },
  ];

  aboutSections.forEach((sec) => {
    const card = document.createElement("div");
    card.className = "aboutCard";
    Object.assign(card.style, {
      background: "rgba(15,10,30,0.95)",
      border: "1px solid rgba(255,200,150,0.4)",
      borderRadius: "12px",
      boxShadow: "0 0 25px rgba(255,150,100,0.3)",
      width: "340px",
      padding: "20px",
      color: ACCENT_COLOR,
      fontFamily: "Cinzel, serif",
      textAlign: "justify",
      fontSize: "0.9rem",
      transform: "scale(0.96)",
      opacity: "0",
      transition: "transform 200ms ease, opacity 180ms ease, box-shadow 200ms ease",
    });
    card.onmouseenter = () => {
      card.style.transform = "scale(1.05)";
      card.style.boxShadow = "0 0 35px rgba(255,180,120,0.6)";
    };
    card.onmouseleave = () => {
      card.style.transform = "scale(1)";
      card.style.boxShadow = "0 0 25px rgba(255,150,100,0.3)";
    };
    card.innerHTML = `<h3 style="text-align:center;color:${TEXT_COLOR}">${sec.titulo}</h3>${sec.texto}`;
    aboutGrid.appendChild(card);
  });

  /*----------  Botón de regreso  ----------*/
  const backBtn = document.createElement("button");
  backBtn.textContent = "← Regresar";
  Object.assign(backBtn.style, {
    marginTop: "20px",
    background: "rgba(255,255,255,0.08)",
    border: "1px solid rgba(200,180,255,0.5)",
    color: TEXT_COLOR,
    padding: "10px 22px",
    fontFamily: "Cinzel, serif",
    fontSize: "1rem",
    borderRadius: "8px",
    cursor: "pointer",
    transition: "all 0.3s ease",
    boxShadow: "0 0 10px rgba(255,180,120,0.25)",
  });
  backBtn.onmouseover = () => (backBtn.style.background = "rgba(255,255,255,0.18)");
  backBtn.onmouseout = () => (backBtn.style.background = "rgba(255,255,255,0.08)");

  /*----------  Lógica de despliegue  ----------*/
  function mount(contentEl) {
    overlayEl.innerHTML = "";
    overlayEl.appendChild(contentEl);
    overlayEl.appendChild(backBtn);
  }

  function animateInCards(scopeEl) {
    const cards = scopeEl.querySelectorAll(".projectCard, .aboutCard");
    cards.forEach((c) => {
      c.style.transform = "scale(0.96)";
      c.style.opacity = "0";
      requestAnimationFrame(() => {
        c.style.transform = "scale(1)";
        c.style.opacity = "1";
      });
    });
  }

  function animateOutCards(scopeEl) {
    const cards = scopeEl.querySelectorAll(".projectCard, .aboutCard");
    cards.forEach((c) => {
      c.style.transform = "scale(0.96)";
      c.style.opacity = "0";
    });
  }

  const ANIM_MS = 180;
  let visible = false;

  function openSection(sectionEl, sectionName) {
    currentSection = sectionName;
    mount(sectionEl);
    overlayEl.style.display = "flex";
    overlayEl.style.pointerEvents = "none";
    requestAnimationFrame(() => {
      overlayEl.style.opacity = "1";
      animateInCards(overlayEl);
      setTimeout(() => (overlayEl.style.pointerEvents = "auto"), ANIM_MS);
      // Move focus into the overlay to avoid aria-hidden focus issues (YouTube player retains focus otherwise)
      try {
        if (document.activeElement && document.activeElement !== document.body) {
          document.activeElement.blur();
        }
        // focus the back button (declared in outer scope)
        if (backBtn && typeof backBtn.focus === 'function') {
          setTimeout(() => backBtn.focus(), ANIM_MS + 30);
        }
      } catch (e) {
        /* ignore focus errors */
      }
    });
    visible = true;
    if (sectionName === "proyectos") {
      const newGrid = createProjectsGrid();
      mount(newGrid);
      rebindYouTubePlayers();
    }

    try {
      const loopPanel = document.getElementById("loopPanel");
      const nav = document.getElementById("main-nav");
      if (loopPanel) {
        // store previous inline styles for restoration
        loopPanel.dataset._prevPointer = loopPanel.style.pointerEvents || "";
        loopPanel.dataset._prevFilter = loopPanel.style.filter || "";
        loopPanel.dataset._prevTransform = loopPanel.style.transform || "";
        loopPanel.dataset._prevZ = loopPanel.style.zIndex || "";
        loopPanel.style.pointerEvents = "none";
        loopPanel.style.filter = "blur(6px) brightness(0.75)";
        loopPanel.style.transform = (loopPanel.style.transform || "translate(-50%, 40px)") + " scale(0.98)";
        loopPanel.style.zIndex = "25";
      }
      if (nav) {
        nav.dataset._prevPointer = nav.style.pointerEvents || "";
        nav.dataset._prevFilter = nav.style.filter || "";
        nav.dataset._prevZ = nav.style.zIndex || "";
        nav.style.pointerEvents = "none";
        nav.style.filter = "blur(4px) brightness(0.85)";
        nav.style.zIndex = "24";
      }
    } catch (e) {
      console.warn('Failed to push UI behind overlay:', e);
    }
  }

  function closeOverlay() {
    if (!visible) return;
    overlayEl.style.pointerEvents = "none";
    animateOutCards(overlayEl);
    overlayEl.style.opacity = "0";
    setTimeout(() => {
      overlayEl.style.display = "none";
      visible = false;
      currentSection = null;
      // restore loop UI and nav styles
      try {
        const loopPanel = document.getElementById("loopPanel");
        const nav = document.getElementById("main-nav");
        if (loopPanel) {
          loopPanel.style.pointerEvents = loopPanel.dataset._prevPointer || "auto";
          loopPanel.style.filter = loopPanel.dataset._prevFilter || "";
          loopPanel.style.transform = loopPanel.dataset._prevTransform || "translate(-50%, 40px)";
          loopPanel.style.zIndex = loopPanel.dataset._prevZ || "25";
          delete loopPanel.dataset._prevPointer;
          delete loopPanel.dataset._prevFilter;
          delete loopPanel.dataset._prevTransform;
          delete loopPanel.dataset._prevZ;
        }
        if (nav) {
          nav.style.pointerEvents = nav.dataset._prevPointer || "auto";
          nav.style.filter = nav.dataset._prevFilter || "";
          nav.style.zIndex = nav.dataset._prevZ || "30";
          delete nav.dataset._prevPointer;
          delete nav.dataset._prevFilter;
          delete nav.dataset._prevZ;
        }
      } catch (e) {
        console.warn('Failed to restore UI after overlay close:', e);
      }
    }, ANIM_MS);
  }

  overlayEl.addEventListener("click", (e) => {
    if (e.target === overlayEl) closeOverlay();
  });
  backBtn.addEventListener("click", closeOverlay);

  window.__openProyectos = () => openSection(createProjectsGrid(), "proyectos");
  window.__openSobreMi = () => openSection(aboutGrid, "sobreMi");
}



/*==============================================================*\
 |  Loop UI (Mute toggles)
\*==============================================================*/
function createLoopButtons() {
  if (STATE.loopPanelCreated) return;
  STATE.loopPanelCreated = true;

  const panel = document.createElement("div");
  panel.id = "loopPanel";
  Object.assign(panel.style, {
    position: "fixed",
    top: "calc(50% + 60px)", // Más arriba que antes
    left: "50%",
    transform: "translate(-50%, 40px)", // Empezamos 40px más abajo
    display: "flex",
    flexDirection: "row",
    gap: "24px", // Un poco más de espacio entre botones
    zIndex: 25,
    opacity: 0,
    transition: "all 1.2s cubic-bezier(0.16, 1, 0.3, 1)", // Animación suave con easing profesional
  });

  TRACKS.forEach((t, i) => {
    const b = document.createElement("button");
    b.textContent = t.name;
    // store reference so we can update appearance from other places
    trackButtons[i] = b;
    Object.assign(b.style, {
      background: "rgba(255,255,255,0.06)",
      border: "1px solid rgba(200,180,255,0.4)",
      color: TEXT_COLOR,
      padding: "10px 24px",
      borderRadius: "12px",
      fontFamily: "Cinzel, serif",
      fontSize: "0.95em",
      letterSpacing: "0.5px",
      cursor: "pointer",
      transition: "all 0.4s cubic-bezier(0.16, 1, 0.3, 1)",
      transform: "translateY(40px) scale(0.95)",
      opacity: "0",
      backdropFilter: "blur(8px)",
      boxShadow: "0 4px 12px rgba(0,0,0,0.1)",
    });

    // Efecto hover más suave (no override del estado activo)
    b.onmouseenter = () => {
      b.style.transform = "translateY(-2px) scale(1.02)";
      b.style.boxShadow = "0 6px 16px rgba(0,0,0,0.15)";
      if (!b.classList.contains('loop-active')) b.style.background = "rgba(255,255,255,0.12)";
    };

    b.onmouseleave = () => {
      b.style.transform = "translateY(0) scale(1)";
      b.style.boxShadow = "0 4px 12px rgba(0,0,0,0.1)";
      // restore visual according to active state
      if (b.classList.contains('loop-active')) {
        b.style.background = "rgba(255,200,100,0.28)";
      } else {
        b.style.background = "rgba(255,255,255,0.06)";
      }
    };
    
    // Anima entrada de cada botón secuencialmente con timing profesional
    setTimeout(() => {
      b.style.transform = "translateY(0) scale(1)";
      b.style.opacity = "1";
    }, 1200 + i * 160); // Comienza después del panel y más rápido entre botones

    const applyVisual = () => {
      if (trackMuted[i]) {
        b.classList.remove('loop-active');
        b.style.background = "rgba(255,255,255,0.06)";
      } else {
        b.classList.add('loop-active');
        b.style.background = "rgba(255,200,100,0.28)";
      }
    };

    b.onclick = () => {
      setTrackMuted(i, !trackMuted[i]);
      applyVisual();
    };

    // initial visual
    applyVisual();
    panel.appendChild(b);
  });

  document.body.appendChild(panel);
}

/*==============================================================*\
 |  DevMixer (Control de volumenes por pista)
\*==============================================================*/
function createDevMixer() {
  if (!DEV_MIXER_ENABLED) return;
  if (document.getElementById("devMixer")) return;

  const wrap = document.createElement("div");
  wrap.id = "devMixer";
  Object.assign(wrap.style, {
    position: "fixed",
    left: "12px",
    bottom: "14px",
    background: "rgba(10,0,20,.7)",
    border: "1px solid rgba(255,200,150,.3)",
    borderRadius: "10px",
    padding: "10px 12px",
    backdropFilter: "blur(8px)",
    zIndex: 1100,
    color: TEXT_COLOR,
    fontFamily: "Cinzel, serif",
    width: "260px",
    maxHeight: "55vh",
    overflow: "auto",
  });

  wrap.innerHTML = `
    <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;">
      <strong>DevMixer</strong>
      <button id="devMixerClose"
        style="background:rgba(255,255,255,.08);
               border:1px solid rgba(200,180,255,.5);
               color:${TEXT_COLOR};
               padding:2px 8px;
               border-radius:6px;
               cursor:pointer">✕</button>
    </div>
  `;

  /*----------  Control master  ----------*/
  const masterRow = document.createElement("div");
  masterRow.style.marginBottom = "8px";
  masterRow.innerHTML = `
    <div style="display:flex;justify-content:space-between;margin-bottom:4px;">
      <span>Master</span><span id="masterVal">1.00</span>
    </div>
    <input id="masterSlider" type="range" min="0" max="1.5"
           step="0.01" value="1" style="width:100%">
  `;
  wrap.appendChild(masterRow);

  /*----------  Extra dev controls (tunable)  ----------*/
  const extraRow = document.createElement('div');
  extraRow.style.marginBottom = '8px';
  extraRow.innerHTML = `
    <div style="display:flex;justify-content:space-between;margin-bottom:4px;">
      <span>YT fade target</span><span id="ytFadeVal">${ytFadeTarget.toFixed(2)}</span>
    </div>
    <input id="ytFadeSlider" type="range" min="0" max="1" step="0.01" value="${ytFadeTarget.toFixed(2)}" style="width:100%">
    <div style="height:8px"></div>
    <div style="display:flex;justify-content:space-between;margin-bottom:4px;">
      <span>Nav offset (px)</span><span id="navOffsetVal">${navOffsetPx}</span>
    </div>
    <input id="navOffsetSlider" type="range" min="0" max="32" step="1" value="${navOffsetPx}" style="width:100%">
  `;
  wrap.appendChild(extraRow);

  /*----------  Controles individuales por pista  ----------*/
  TRACKS.forEach((t, i) => {
    const row = document.createElement("div");
    row.style.marginBottom = "8px";
    row.innerHTML = `
      <div style="display:flex;justify-content:space-between;margin-bottom:4px;">
        <span>${t.name}</span><span id="trkVal${i}">0.80</span>
      </div>
      <input id="trk${i}" type="range" min="0" max="1.5"
             step="0.01" value="0.8" style="width:100%">
    `;
    wrap.appendChild(row);
  });

  document.body.appendChild(wrap);

  /*----------  Handlers de interacción  ----------*/
  document.getElementById("devMixerClose").onclick = () => {
    wrap.remove();
    STATE.devMixerOpen = false;
  };

  const masterSlider = document.getElementById("masterSlider");
  const masterVal = document.getElementById("masterVal");
  masterSlider.oninput = () => {
    const v = +masterSlider.value;
    if (masterGain) masterGain.gain.value = v;
    masterVal.textContent = v.toFixed(2);
  };

  TRACKS.forEach((t, i) => {
    const sld = document.getElementById(`trk${i}`);
    const lbl = document.getElementById(`trkVal${i}`);
    sld.oninput = () => {
      const v = +sld.value;
      if (trackGains[i])
        trackGains[i].gain.value = v * (trackMuted[i] ? 0 : 1);
      lbl.textContent = v.toFixed(2);
    };
  });

  // Extra controls handlers
  const ytFadeSlider = document.getElementById('ytFadeSlider');
  const ytFadeVal = document.getElementById('ytFadeVal');
  if (ytFadeSlider) {
    ytFadeSlider.oninput = () => {
      ytFadeTarget = +ytFadeSlider.value;
      ytFadeVal.textContent = ytFadeTarget.toFixed(2);
      // if currently some player is playing, apply the new target smoothly
      if (playingCount > 0) fadeBgVolume(ytFadeTarget, 250);
    };
  }

  const navOffsetSlider = document.getElementById('navOffsetSlider');
  const navOffsetVal = document.getElementById('navOffsetVal');
  if (navOffsetSlider) {
    navOffsetSlider.oninput = () => {
      navOffsetPx = +navOffsetSlider.value;
      navOffsetVal.textContent = navOffsetPx;
      // reposition immediately
      try {
        const nav = document.getElementById('main-nav');
        if (nav && introEl) {
          const r = introEl.getBoundingClientRect();
          const topPx = Math.max(8, r.bottom + navOffsetPx);
          nav.style.top = topPx + 'px';
        }
      } catch (e) {
        console.warn('Failed to reposition nav from DevMixer', e);
      }
    };
  }

  STATE.devMixerOpen = true;
}


/*==============================================================*\
 |  Audio Engine — Inicialización, Looping y Control
\*==============================================================*/

let filterBaseFreq = 2000;

/*--------------------------------------------------------------*\
 |  Inicialización del grafo de audio
\*--------------------------------------------------------------*/
async function initAudioGraph() {
  if (audioCtx) return;
  audioCtx = new (window.AudioContext || window.webkitAudioContext)();

  analyser = audioCtx.createAnalyser();
  analyser.fftSize = FFT_SIZE;
  analyser.smoothingTimeConstant = 0.85;

  filterNode = audioCtx.createBiquadFilter();
  filterNode.type = "lowpass";
  filterNode.frequency.value = filterBaseFreq;

  masterGain = audioCtx.createGain();
  masterGain.gain.value = 1.0;

  bgGain = audioCtx.createGain();
  bgGain.gain.value = 1.0;

  analyser.connect(filterNode);
  filterNode.connect(masterGain).connect(bgGain).connect(audioCtx.destination);

  analyserData = new Uint8Array(analyser.frequencyBinCount);

  // Loop de análisis espectral (frecuencia)
  const pull = () => {
    analyser.getByteFrequencyData(analyserData);
    spectrumPullRAF = requestAnimationFrame(pull);
  };
  pull();

  // Crear nodos Gain por pista
  for (let i = 0; i < TRACKS.length; i++) {
    trackGains[i] = audioCtx.createGain();
    trackGains[i].gain.value = 0; // muteadas por defecto
    trackGains[i].connect(analyser);
  }
}

/*--------------------------------------------------------------*\
 |  Carga de buffers de audio
\*--------------------------------------------------------------*/
async function loadAllBuffers() {
  await Promise.all(
    TRACKS.map(async (t, i) => {
      const res = await fetch(t.url);
      const buf = await res.arrayBuffer();
      trackBuffers[i] = await audioCtx.decodeAudioData(buf);
    })
  );
}

/*--------------------------------------------------------------*\
 |  Inicio de todas las pistas (gapless loop)
\*--------------------------------------------------------------*/
function startAllSourcesGapless() {
  if (masterStartTime) return;

  const startAt = audioCtx.currentTime + 0.3;

  TRACKS.forEach((t, i) => {
    const src = audioCtx.createBufferSource();
    src.buffer = trackBuffers[i];
    src.loop = true;
    src.loopStart = 0.0;
    src.loopEnd = src.buffer.duration; // usa duración real del archivo
    src.connect(trackGains[i]);
    src.start(startAt);
    trackSources[i] = src;
  });

  // Pequeño fade-in maestro para evitar clicks
  const now = audioCtx.currentTime;
  masterGain.gain.cancelScheduledValues(now);
  masterGain.gain.setValueAtTime(0, now);
  masterGain.gain.linearRampToValueAtTime(1.0, now + 0.08);

  masterStartTime = startAt;
}

/*--------------------------------------------------------------*\
 |  Mute dinámico por pista (con crossfade)
\*--------------------------------------------------------------*/
function setTrackMuted(i, muted) {
  trackMuted[i] = muted;
  const defaultVol = 0.8;
  const target = muted
    ? 0
    : trackGains[i].gain.value === 0
    ? defaultVol
    : trackGains[i].gain.value;

  if (!muted && trackGains[i].gain.value === 0)
    trackGains[i].gain.value = defaultVol;

  // Transición suave
  const now = audioCtx.currentTime;
  trackGains[i].gain.cancelScheduledValues(now);
  const from = trackGains[i].gain.value;
  trackGains[i].gain.setValueAtTime(from, now);
  trackGains[i].gain.linearRampToValueAtTime(muted ? 0 : target, now + 0.15);

  updatePaletteFromActive();
  // update button visual if present
  try {
    const b = trackButtons[i];
    if (b) {
      if (!muted) {
        b.classList.add('loop-active');
        b.style.background = "rgba(255,200,100,0.28)";
      } else {
        b.classList.remove('loop-active');
        b.style.background = "rgba(255,255,255,0.06)";
      }
    }
  } catch (e) {
    console.warn('Failed to update loop button visual:', e);
  }
}

/*--------------------------------------------------------------*\
 |  Actualización de paleta según pistas activas
\*--------------------------------------------------------------*/
function updatePaletteFromActive() {
  let warmCount = 0,
    coldCount = 0;

  TRACKS.forEach((t, i) => {
    const active = !trackMuted[i];
    if (!active) return;
  if (t.name === "Drums" || t.name === "Percussion" || t.name === "Pad") warmCount++;
    else coldCount++;
  });

  const total = warmCount + coldCount;
  let target = 0.45;
  if (total > 0) {
    const ratioWarm = warmCount / total;
    target = 0.25 + ratioWarm * 0.6;
  }

  const step = () => {
    paletteMix += (target - paletteMix) * 0.06;
    if (Math.abs(target - paletteMix) > 0.005) requestAnimationFrame(step);
  };
  requestAnimationFrame(step);
}



/* (Removed duplicate audio initialization block — single audio graph is declared earlier.) */

/*==============================================================*\
 |  🎬 Integración con YouTube — Fade automático de música
\*==============================================================*/

let activePlayers = [];
let fadeTarget = 1.0;
let ytFadeTarget = 0; // volumen mínimo mientras se reproduce video
let playingCount = 0;
let fadeInterval = null; // used by fadeBgVolume

/*--------------------------------------------------------------*\
 |  Función de fade progresivo para el gain final (bgGain)
\*--------------------------------------------------------------*/
function fadeBgVolume(target, duration = 400) {
  // Prefer to fade the masterGain if available (so DevMixer master reflects overall level),
  // otherwise fallback to bgGain. Use AudioParam ramps when audioCtx is available.
  const gainNode = (typeof masterGain !== 'undefined' && masterGain) ? masterGain : (typeof bgGain !== 'undefined' ? bgGain : null);
  if (!gainNode) return;

  // If we have an AudioContext and the gain is an AudioParam, schedule a smooth ramp.
  try {
    if (audioCtx && audioCtx.currentTime && gainNode.gain && typeof gainNode.gain.cancelScheduledValues === 'function') {
      const now = audioCtx.currentTime;
      gainNode.gain.cancelScheduledValues(now);
      // set immediate current value to avoid jumps
      gainNode.gain.setValueAtTime(gainNode.gain.value, now);
      gainNode.gain.linearRampToValueAtTime(target, now + duration / 1000);
      return;
    }
  } catch (e) {
    // fall through to interval-based fallback
  }

  // Fallback: interval-based linear interpolation
  if (fadeInterval) clearInterval(fadeInterval);
  const start = (gainNode.gain && typeof gainNode.gain.value === 'number') ? gainNode.gain.value : 1;
  const diff = target - start;
  const steps = 30;
  let c = 0;
  fadeInterval = setInterval(() => {
    c++;
    const t = c / steps;
    try { gainNode.gain.value = start + diff * t; } catch (e) {}
    if (c >= steps) {
      clearInterval(fadeInterval);
      fadeInterval = null;
      try { gainNode.gain.value = target; } catch (e) {}
    }
  }, Math.max(10, duration / steps));
}

/*--------------------------------------------*\
 | Detección del estado de los videos
\*--------------------------------------------*/
function handlePlayerStateChange(event) {
  const PLAYING = 1;
  const PAUSED = 2;
  const ENDED = 0;

  if (event.data === PLAYING) {
    playingCount++;
  } else if (event.data === PAUSED || event.data === ENDED) {
    playingCount = Math.max(0, playingCount - 1);
  }

  // Si hay videos reproduciéndose → baja el volumen global
  if (playingCount > 0) {
    if (fadeTarget !== ytFadeTarget) {
      fadeTarget = ytFadeTarget;
      fadeBgVolume(ytFadeTarget, 1200);
    }
  } else {
    if (fadeTarget !== 1.0) {
      fadeTarget = 1.0;
      fadeBgVolume(1.0, 1600);
    }
  }
}

/*--------------------------------------------*\
 | Vinculación de iframes con la API de YouTube
\*--------------------------------------------*/
function rebindYouTubePlayers() {
  if (typeof window.YT === "undefined" || !window.YT.Player) {
    console.log("⏳ Cargando API de YouTube...");
    if (!document.getElementById("yt-api")) {
      const tag = document.createElement("script");
      tag.id = "yt-api";
      tag.src = "https://www.youtube.com/iframe_api";
      document.head.appendChild(tag);
    }
    window.onYouTubeIframeAPIReady = rebindYouTubePlayers;
    return;
  }

  console.log("✅ API de YouTube lista, vinculando players...");

  // Destruye cualquier instancia anterior
  activePlayers.forEach((p) => p.destroy && p.destroy());
  activePlayers = [];

  const iframes = document.querySelectorAll("iframe[src*='youtube']");
  iframes.forEach((iframe) => {
    const player = new window.YT.Player(iframe, {
      events: { onStateChange: handlePlayerStateChange },
    });
    activePlayers.push(player);
  });
}

/*==============================================================*\
 |  Grid dinámico de proyectos
\*==============================================================*/
function createProjectsGrid() {
  return buildProjectsGrid(PROJECTS);
}

/*==============================================================*\
 |  🪟 Apertura dinámica de secciones (Proyectos, Sobre mí, etc.)
\*==============================================================*/
function openSection(sectionEl, sectionName) {
  if (STATE.overlayCreated) return;
  STATE.overlayCreated = true;

  const overlay = document.createElement("div");
  overlay.className = "overlay";
  Object.assign(overlay.style, {
    position: "fixed",
    inset: "0",
    background: "rgba(5,5,10,0.92)",
    display: "flex",
    justifyContent: "center",
    alignItems: "center",
    zIndex: "999",
    backdropFilter: "blur(12px)",
  });

  const content = document.createElement("div");
  Object.assign(content.style, {
    maxWidth: "1400px",
    width: "95%",
    minHeight: "80%",
    padding: "40px 20px",
    borderRadius: "16px",
    background: "rgba(20,15,25,0.95)",
    border: "1px solid rgba(255,200,150,0.3)",
    boxShadow: "0 0 40px rgba(255,160,100,0.25)",
    overflowY: "auto",
    position: "relative",
  });

  const closeBtn = document.createElement("button");
  closeBtn.textContent = "Regresar";
  Object.assign(closeBtn.style, {
    position: "absolute",
    top: "20px",
    right: "20px",
    background: "none",
    color: TEXT_COLOR,
    fontSize: "1.2rem",
    border: "none",
    cursor: "pointer",
  });
  closeBtn.onclick = () => {
    overlay.remove();
    STATE.overlayCreated = false;
    playingCount = 0;
    fadeBgVolume(1.0, 800);
  };

  content.appendChild(closeBtn);

  const mount = (el) => {
    el.style.opacity = "0";
    el.style.transition = "opacity 400ms ease";
    content.appendChild(el);
    setTimeout(() => (el.style.opacity = "1"), 20);
  };

  // ---------- CONTENIDO DINÁMICO ----------
  if (sectionName === "proyectos") {
    const newGrid = createProjectsGrid();
    mount(newGrid);
    setTimeout(() => {
      rebindYouTubePlayers();
    }, 400);
  } else if (sectionName === "sobre") {
    const aboutText = document.createElement("p");
    aboutText.innerHTML =
      "Este portafolio fue diseñado como una obra interactiva entre código, sonido y estética visual. Explora proyectos que integran música, diseño procedural y programación creativa.";
    Object.assign(aboutText.style, {
      color: TEXT_COLOR,
      fontFamily: "Cinzel, serif",
      lineHeight: "1.6",
      maxWidth: "800px",
      textAlign: "center",
      margin: "0 auto",
    });
    mount(aboutText);
  }

  overlay.appendChild(content);
  document.body.appendChild(overlay);
}


/*==============================================================*\
 |  Intro y Flujo de Interacción
\*==============================================================*/

/**
 * Crea los botones del menú inicial una sola vez (“Proyectos” y “Sobre mí”).
 */
function createIntroButtonsOnce() {
  if (STATE.navCreated) return;
  STATE.navCreated = true;

  const nav = document.getElementById("main-nav");
  if (!nav) return;

  const makeButton = (label, callback) => {
    const btn = document.createElement("button");
    btn.textContent = label;
    btn.className = "nav-button";
    
    // Efectos hover
    btn.onmouseenter = () => {
      btn.style.background = "rgba(255,255,255,0.12)";
      btn.style.transform = "translateY(-2px) scale(1.02)";
      btn.style.boxShadow = "0 6px 16px rgba(0,0,0,0.15)";
    };
    
    btn.onmouseleave = () => {
      btn.style.background = "rgba(255,255,255,0.06)";
      btn.style.transform = "translateY(0) scale(1)";
      btn.style.boxShadow = "0 4px 12px rgba(0,0,0,0.1)";
    };
    
    btn.onclick = callback;
    return btn;
  };

  // Crear botones
  const proyectosBtn = makeButton("Proyectos", () => {
    setupProjectPopups();
    window.__openProyectos();
  });

  const sobreMiBtn = makeButton("Sobre mí", () => {
    setupProjectPopups();
    window.__openSobreMi();
  });

  nav.appendChild(proyectosBtn);
  nav.appendChild(sobreMiBtn);
}

/**
 * Se ejecuta cuando el usuario hace click por primera vez (“Haz click para comenzar”)
 */
async function handleIntroClick() {
  if (STATE.introStarted) return;
  STATE.introStarted = true;

  // Remueve el hint inicial
  if (startHintEl) {
    startHintEl.remove();
    startHintEl = null;
  }

  // Inicializa audio y carga todos los loops
  await initAudioGraph();
  await loadAllBuffers();
  startAllSourcesGapless();

  // Crea paneles de control
  createLoopButtons();
  if (DEV_MIXER_ENABLED && !STATE.devMixerOpen) createDevMixer();

  // 1. Título sube con animación suave
  introEl.style.transition = "all 1.2s cubic-bezier(0.16, 1, 0.3, 1)";
  introEl.classList.add("hideSubtitle");
  
  // 2. Secuencia de animaciones
  setTimeout(() => {
    introEl.classList.add("moveUp");
  }, 400);

  // 3. Crear y mostrar botones de navegación
  setTimeout(() => {
    createIntroButtonsOnce();
    const nav = document.getElementById("main-nav");
    if (nav) {
      // position nav slightly below intro title so it's closer to the name
      positionNavNearIntro();
      nav.style.transition = "all 1.2s cubic-bezier(0.16, 1, 0.3, 1)";
      nav.classList.add("visible");
    }
  }, 800);

  // 4. Panel de loops aparece y se desliza
  setTimeout(() => {
    const loopPanel = document.getElementById("loopPanel");
    if (loopPanel) {
      loopPanel.style.opacity = "1";
      loopPanel.style.transform = "translate(-50%, 0)";
    }
  }, 800);

  // Position nav near intro and provide a resize handler
  function positionNavNearIntro() {
    const nav = document.getElementById('main-nav');
    if (!nav || !introEl) return;
    try {
    const r = introEl.getBoundingClientRect();
    const topPx = Math.max(8, r.bottom + navOffsetPx);
    nav.style.top = topPx + 'px';
      nav.style.left = '0';
      nav.style.right = '0';
    } catch (e) {
      console.warn('positionNavNearIntro failed', e);
    }
  }

  window.addEventListener('resize', () => {
    clearTimeout(window._navPosTO);
    window._navPosTO = setTimeout(() => {
      positionNavNearIntro();
    }, 100);
  });

  // 3. Botones de navegación con animaciones elegantes
  const nav = document.getElementById('main-nav');
  if (nav) {
    const navButtons = nav.querySelectorAll('.nav-button');
    navButtons.forEach((btn, idx) => {
      animate(btn, { transform: 'translateY(0) scale(1)', opacity: '1' }, 1100 + idx * 120);
    });
  }
}

/**
 * Montaje general del portafolio
 */
window.addEventListener("DOMContentLoaded", () => {
  introEl = document.getElementById("intro");
  canvasEl = document.getElementById("canvas");

  // Inicializa fluido visual y correo (antes del click)
  new CanvasFluid();
  createTopRightEmail();

  // “Haz click para comenzar” debajo del subtítulo
  createStartHint();

  // Crear ya los controles visibles (loop buttons / dev mixer) para facilitar testing
  // Las funciones manejan guardas internas para no duplicar elementos.
  try {
    createLoopButtons();
    if (DEV_MIXER_ENABLED && !STATE.devMixerOpen) createDevMixer();
  } catch (e) {
    console.warn('No fue posible crear los controles en DOMContentLoaded:', e);
  }

  // Click en intro o canvas inicia la experiencia
  const startAny = () => handleIntroClick();
  introEl.addEventListener("click", startAny);
  canvasEl.addEventListener("click", startAny);

  STATE.introMounted = true;
});
