'use strict';
/*
 * ZeroLegend Agar - server di gioco WebSocket (modalita' ffa / teams / party)
 * Compatibile con il client lib/js/datad23b.js (protocollo binario stile Ogar).
 *
 * Variabili ambiente (tutte opzionali):
 *   PORT            porta (su Plesk/Passenger la assegna Passenger)
 *   AUTH_SECRET     stessa stringa di api/config.local.php  -> verifica i token di login
 *   SERVER_KEY      stessa stringa di api/config.local.php  -> firma i salvataggi
 *   SAVE_URL        https://agar.master-elettroerosioni.it/api/save.php
 *   BOTS            numero di bot per stanza ffa/teams (default 12)
 *   BOT_KEY         chiave segreta dei bot esterni (script Tampermonkey). Senza chiave i bot sono rifiutati
 *   BOT_MAX         massimo bot esterni contemporanei su tutto il server (default 1000, max 2000)
 *   BOT_MAX_MASS    massa iniziale massima concessa ai bot esterni (default 22500 = massa massima di una cella)
 *   FOOD_TARGET     quantita' di cibo sulla mappa (default 700; con molti bot conviene alzarla, es. 3000)
 *   ALLOWED_ORIGINS elenco di origin ammessi, separati da virgola (vuoto = tutti)
 *   ADMIN_USERS     nomi utente admin, separati da virgola (default ZeroTheLegend) - vedi zl_admin.js
 *   ADMIN_KEY       chiave del pannello admin dello script (se vuota usa BOT_KEY)
 *   BAN_FILE        file dei ban (default ./bans.json)
 */
const http = require('http');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');
const account = require('./zl_account');

// ---------------------------------------------------------------- configurazione
const TICK_MS = 40;                 // 25 aggiornamenti al secondo
const DT = TICK_MS / 1000;
const BORDER = { x0: 0, y0: 0, x1: 11180, y1: 11180 };
const START_MASS = 10;
const MAX_CELLS = 16;
const MAX_CELL_MASS = 22500;
const MIN_SPLIT_MASS = 35;
const MIN_EJECT_MASS = 32;
const EJECT_LOSS = 16;
const EJECT_MASS = 13;
let FOOD_TARGET = Math.max(100, Math.min(20000, parseInt(process.env.FOOD_TARGET || '700', 10) || 700));
const VIRUS_TARGET = 16;
const VIRUS_MASS = 100;
const VIRUS_FEEDS = 7;
const MAX_PLAYERS_PER_ROOM = 80;
const MAX_CONN_PER_IP = 8;
const BOTS = Math.max(0, Math.min(60, parseInt(process.env.BOTS || '12', 10) || 0));
const BOT_KEY = process.env.BOT_KEY || '';
let BOT_MAX = Math.max(0, Math.min(2000, parseInt(process.env.BOT_MAX || '1000', 10) || 0));
const BOT_MAX_MASS = Math.max(START_MASS, Math.min(MAX_CELL_MASS, parseInt(process.env.BOT_MAX_MASS || String(MAX_CELL_MASS), 10) || MAX_CELL_MASS));
const BOT_VIEW_W = 1800, BOT_VIEW_H = 1100;      // area massima vista da un bot esterno (meno dati da inviare)
const GRID_CS = 256, GRID_N = Math.ceil((BORDER.x1 - BORDER.x0) / GRID_CS) + 1;   // griglia spaziale per le collisioni
const gridIdx = v => { const i = (v / GRID_CS) | 0; return i < 0 ? 0 : (i >= GRID_N ? GRID_N - 1 : i); };
const HUB_BACKLOG = 4 * 1024 * 1024;             // se la connessione dei bot e' intasata si saltano gli aggiornamenti
let BOT_FIGHT = (process.env.BOT_FIGHT || '1') !== '0';   // i bot esterni possono mangiarsi tra loro (e farsi mangiare dai giocatori)
let minionCount = 0;                             // bot esterni collegati in questo momento
const ALLOWED_ORIGINS = (process.env.ALLOWED_ORIGINS || '').split(',').map(s => s.trim()).filter(Boolean);
const TEAM_COLORS = [[255, 70, 70], [60, 220, 100], [70, 130, 255]];
const BOT_NAMES = ['Zero', 'Nova', 'Pixel', 'Blaze', 'Orbit', 'Echo', 'Rogue', 'Comet', 'Viper', 'Mochi', 'Titan', 'Pulse', 'Ghost', 'Drift', 'Ninja'];

const TYPE_CELL = 0, TYPE_FOOD = 1, TYPE_VIRUS = 2, TYPE_EJECT = 3;
const sizeOf = mass => Math.sqrt(mass * 100);
const rnd = (a, b) => a + Math.random() * (b - a);

function hsl(h, s, l) {
  s /= 100; l /= 100;
  const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l);
  const f = n => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
  return [Math.round(255 * f(0)), Math.round(255 * f(8)), Math.round(255 * f(4))];
}
const randomColor = () => hsl(Math.floor(rnd(0, 360)), 90, 55);

// ---------------------------------------------------------------- scrittura pacchetti
class Writer {
  constructor(n) { this.b = Buffer.allocUnsafe(n || 256); this.o = 0; }
  need(n) { if (this.o + n > this.b.length) { const nb = Buffer.allocUnsafe(Math.max(this.b.length * 2, this.o + n)); this.b.copy(nb, 0, 0, this.o); this.b = nb; } }
  u8(v) { this.need(1); this.b.writeUInt8(v & 255, this.o); this.o += 1; }
  u16(v) { this.need(2); this.b.writeUInt16LE(v & 65535, this.o); this.o += 2; }
  i16(v) { this.need(2); this.b.writeInt16LE(Math.max(-32768, Math.min(32767, Math.round(v))), this.o); this.o += 2; }
  u32(v) { this.need(4); this.b.writeUInt32LE(v >>> 0, this.o); this.o += 4; }
  f32(v) { this.need(4); this.b.writeFloatLE(v, this.o); this.o += 4; }
  f64(v) { this.need(8); this.b.writeDoubleLE(v, this.o); this.o += 8; }
  str(s) { s = String(s || ''); this.need(s.length * 2 + 2); for (let i = 0; i < s.length; i++) this.u16(s.charCodeAt(i)); this.u16(0); }
  done() { return this.b.subarray(0, this.o); }
}
function readUtf16(buf, from) { return buf.subarray(from, from + ((buf.length - from) & ~1)).toString('utf16le'); }
function cleanName(s) { return String(s || '').replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 15); }

// ---------------------------------------------------------------- entita' e giocatori
let uidCounter = 0;
class Player {
  constructor(game, conn, isBot) {
    this.game = game; this.conn = conn; this.isBot = !!isBot;
    this.pid = ++uidCounter;
    this.name = ''; this.user = null; this.team = 0; this.ip = '';
    this.color = randomColor();
    this.cells = []; this.alive = false;
    this.mx = 0; this.my = 0;
    this.spawnAt = 0; this.sessionUid = ''; this.kills = 0; this.maxMass = 0;
    this.lastEject = 0; this.lastChat = 0; this.lastSpawn = 0;
    this.known = new Set(); this.pendingAdd = [];
    this.spectate = false;
    this.botThink = 0; this.respawnAt = 0;
    this.isMinion = false; this.hub = null; this.hubId = 0; this.startMass = 0;   // bot esterni (script)
  }
  totalMass() { let m = 0; for (const c of this.cells) m += c.mass; return m; }
  center() {
    let x = 0, y = 0, m = 0;
    for (const c of this.cells) { x += c.x * c.mass; y += c.y * c.mass; m += c.mass; }
    return m ? { x: x / m, y: y / m } : null;
  }
}

class Game {
  constructor(key, mode) {
    this.key = key; this.mode = mode;
    this.ents = []; this.nextId = 1;
    this.players = new Set();
    this.eats = []; this.tickN = 0;
    this.lb = null;
    this.foodCount = 0; this.virusCount = 0;
    this.emptySince = Date.now();
    this.persistent = (mode !== 'party');
    this.hubs = new Set(); this.tickMs = 0;
    this.grid = { b: [], used: [] };
    for (let i = 0; i < FOOD_TARGET; i++) this.spawnFood();
    for (let i = 0; i < VIRUS_TARGET; i++) this.spawnVirus();
    if (this.persistent) for (let i = 0; i < BOTS; i++) this.addBot();
    this.timer = setInterval(() => { try { this.tick(); } catch (e) { console.error('tick error', e); } }, TICK_MS);
  }
  newEnt(type, x, y, mass, color) {
    const e = { id: this.nextId++, type, x, y, mass, r: sizeOf(mass), color, owner: null, name: '',
      bx: 0, by: 0, bspeed: 0, mergeAt: 0, feeds: 0, dead: false, dirty: false };
    this.ents.push(e);
    return e;
  }
  spawnFood() {
    const e = this.newEnt(TYPE_FOOD, rnd(BORDER.x0 + 20, BORDER.x1 - 20), rnd(BORDER.y0 + 20, BORDER.y1 - 20), 1, randomColor());
    this.foodCount++;
    return e;
  }
  spawnVirus(x, y) {
    const e = this.newEnt(TYPE_VIRUS, x === undefined ? rnd(300, BORDER.x1 - 300) : x, y === undefined ? rnd(300, BORDER.y1 - 300) : y, VIRUS_MASS, [51, 255, 51]);
    this.virusCount++;
    return e;
  }
  kill(e) { if (!e.dead) { e.dead = true; if (e.type === TYPE_FOOD) this.foodCount--; else if (e.type === TYPE_VIRUS) this.virusCount--; } }

  // ----- giocatori
  humans() { let n = 0; for (const p of this.players) if (!p.isBot && !p.isMinion) n++; return n; }
  addBot() {
    const p = new Player(this, null, true);
    p.name = BOT_NAMES[Math.floor(Math.random() * BOT_NAMES.length)] + Math.floor(rnd(1, 99));
    this.assignTeam(p);
    this.players.add(p);
    this.spawnPlayer(p);
    return p;
  }
  assignTeam(p) {
    if (this.mode !== 'teams') return;
    const counts = [0, 0, 0];
    for (const o of this.players) if (o !== p) counts[o.team]++;
    p.team = counts.indexOf(Math.min(...counts));
    p.color = TEAM_COLORS[p.team];
  }
  spawnPlayer(p) {
    if (p.alive) return;
    const x = rnd(BORDER.x0 + 400, BORDER.x1 - 400), y = rnd(BORDER.y0 + 400, BORDER.y1 - 400);
    const mass = p.startMass || START_MASS;      // i bot esterni nascono con la massa scelta nel menu (massa reale)
    const e = this.newEnt(TYPE_CELL, x, y, mass, p.color);
    e.owner = p; e.name = p.name;
    p.cells = [e]; p.alive = true; p.spectate = false;
    p.mx = x; p.my = y; p.kills = 0; p.maxMass = mass;
    p.spawnAt = Date.now(); p.sessionUid = crypto.randomBytes(16).toString('hex');
    p.pendingAdd.push(e.id);
  }
  playerDied(p, killer) {
    p.alive = false; p.cells = [];
    if (killer && killer.owner) killer.owner.kills++;
    if (p.user) {
      const stats = { kills: p.kills, maxMass: p.maxMass, seconds: Math.floor((Date.now() - p.spawnAt) / 1000) };
      account.saveSession(p.user, p.sessionUid, stats).catch(err => console.error('save fallito:', err.message));
    }
    if (p.isBot) p.respawnAt = Date.now() + 3000;
    if (p.hub) p.hub.push(p.hubId, DEAD_PKT);
  }
  removePlayer(p) {
    if (p.alive) {
      for (const c of p.cells) this.kill(c);
      this.playerDied(p, null);
    }
    this.players.delete(p);
    if (this.players.size === 0 || this.humans() === 0) this.emptySince = this.emptySince || Date.now();
  }

  // ----- azioni del giocatore
  split(p) {
    if (!p.alive) return;
    const cells = p.cells.slice().sort((a, b) => b.mass - a.mass);
    for (const c of cells) {
      if (p.cells.length >= MAX_CELLS) break;
      if (c.mass < MIN_SPLIT_MASS) continue;
      let dx = p.mx - c.x, dy = p.my - c.y, d = Math.hypot(dx, dy);
      if (d < 1) { dx = 1; dy = 0; d = 1; }
      this.launchCell(p, c, dx / d, dy / d, 780);
    }
  }
  launchCell(p, c, dx, dy, speed) {
    const half = c.mass / 2;
    c.mass = half; c.r = sizeOf(half);
    const n = this.newEnt(TYPE_CELL, c.x, c.y, half, p.color);
    n.owner = p; n.name = p.name; n.bx = dx; n.by = dy; n.bspeed = speed;
    const t = Date.now() + 15000 + half * 10;
    n.mergeAt = t; c.mergeAt = t;
    p.cells.push(n); p.pendingAdd.push(n.id);
    return n;
  }
  eject(p) {
    if (!p.alive) return;
    const now = Date.now();
    if (now - p.lastEject < 50) return;
    p.lastEject = now;
    for (const c of p.cells) {
      if (c.mass < MIN_EJECT_MASS) continue;
      let dx = p.mx - c.x, dy = p.my - c.y, d = Math.hypot(dx, dy);
      if (d < 1) { dx = 1; dy = 0; d = 1; }
      dx /= d; dy /= d;
      c.mass -= EJECT_LOSS; c.r = sizeOf(c.mass);
      const e = this.newEnt(TYPE_EJECT, c.x + dx * c.r, c.y + dy * c.r, EJECT_MASS, p.color);
      e.bx = dx; e.by = dy; e.bspeed = 650;
    }
  }
  chat(p, text) {
    const now = Date.now();
    if (now - p.lastChat < 1000) return;
    p.lastChat = now;
    text = String(text).replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 120);
    if (!text) return;
    const w = new Writer(64 + text.length * 2);
    w.u8(99); w.u8(0);
    w.u8(p.color[0]); w.u8(p.color[1]); w.u8(p.color[2]);
    w.str(p.name || 'Guest'); w.str(text);
    const buf = w.done();
    for (const o of this.players) if (o.conn) send(o.conn, buf);
  }

  // ----- simulazione
  tick() {
    const t0 = performance.now();
    this.tickN++;
    const now = Date.now();
    this.eats.length = 0;
    // bot: ripresa e decisioni
    for (const p of this.players) {
      if (!p.isBot) continue;
      if (!p.alive) { if (now >= p.respawnAt) this.spawnPlayer(p); continue; }
      if (now >= p.botThink) { p.botThink = now + 200; this.botThink(p); }
    }
    // movimento
    for (const e of this.ents) {
      if (e.dead) continue;
      if (e.type === TYPE_CELL) {
        const p = e.owner;
        const dx = p.mx - e.x, dy = p.my - e.y, d = Math.hypot(dx, dy);
        if (d > 1) {
          const step = Math.min(d, 2200 * Math.pow(e.r, -0.439) * DT);
          e.x += dx / d * step; e.y += dy / d * step;
        }
        if (e.mass > START_MASS) { e.mass = Math.max(START_MASS, e.mass * (1 - 0.002 * DT)); e.r = sizeOf(e.mass); }
      }
      if (e.bspeed > 0) {
        e.x += e.bx * e.bspeed * DT; e.y += e.by * e.bspeed * DT;
        e.bspeed *= Math.pow(0.9, DT * 25);
        if (e.bspeed < 8) e.bspeed = 0;
      }
      if (e.x < BORDER.x0 + e.r * 0.5) e.x = BORDER.x0 + e.r * 0.5;
      if (e.x > BORDER.x1 - e.r * 0.5) e.x = BORDER.x1 - e.r * 0.5;
      if (e.y < BORDER.y0 + e.r * 0.5) e.y = BORDER.y0 + e.r * 0.5;
      if (e.y > BORDER.y1 - e.r * 0.5) e.y = BORDER.y1 - e.r * 0.5;
    }
    this.collisions(now);
    // aggiorna statistiche e raggi
    for (const p of this.players) {
      if (!p.alive) continue;
      p.cells = p.cells.filter(c => !c.dead);
      const tm = p.totalMass();
      if (tm > p.maxMass) p.maxMass = tm;
    }
    // rimpiazza cibo e virus
    for (let i = 0; i < 12 && this.foodCount < FOOD_TARGET; i++) this.spawnFood();
    if (this.virusCount < VIRUS_TARGET && this.tickN % 50 === 0) this.spawnVirus();
    if (this.tickN % 20 === 0) this.buildLeaderboard();
    // invio (i bot esterni ricevono aggiornamenti piu' rari e raggruppati per connessione)
    const every = minionEvery();
    for (const p of this.players) {
      if (p.conn) this.sendUpdate(p);
      else if (p.hub && p.alive && (this.tickN + p.pid) % every === 0) this.sendUpdate(p);
    }
    for (const h of this.hubs) h.flush();
    // pulizia
    if (this.ents.some(e => e.dead)) this.ents = this.ents.filter(e => !e.dead);
    for (const e of this.ents) e.dirty = false;
    this.tickMs = this.tickMs * 0.9 + (performance.now() - t0) * 0.1;
  }

  friendly(a, b) { return a.owner === b.owner || (!BOT_FIGHT && a.owner.isMinion && b.owner.isMinion) || (this.mode === 'teams' && a.owner.team === b.owner.team); }

  collisions(now) {
    const ents = this.ents;
    const cells = [];
    // griglia: cibo, virus e massa espulsa divisi in quadrati, cosi' ogni cella controlla solo quelli vicini
    const G = this.grid, ejs = [];
    for (const k of G.used) G.b[k].length = 0;
    G.used.length = 0;
    for (const e of ents) {
      if (e.dead) continue;
      if (e.type === TYPE_CELL) { cells.push(e); continue; }
      if (e.type === TYPE_EJECT && e.bspeed > 0) ejs.push(e);
      const k = gridIdx(e.y - BORDER.y0) * GRID_N + gridIdx(e.x - BORDER.x0);
      let a = G.b[k];
      if (!a) a = G.b[k] = [];
      if (a.length === 0) G.used.push(k);
      a.push(e);
    }
    // cellule vs cellule
    for (let i = 0; i < cells.length; i++) {
      const a = cells[i]; if (a.dead) continue;
      for (let j = i + 1; j < cells.length; j++) {
        const b = cells[j]; if (b.dead) continue;
        const dx = b.x - a.x, dy = b.y - a.y;
        const rs = a.r + b.r;
        if (Math.abs(dx) > rs || Math.abs(dy) > rs) continue;
        const d = Math.hypot(dx, dy);
        const big = a.mass >= b.mass ? a : b, small = big === a ? b : a;
        if (a.owner === b.owner) {
          if (now >= a.mergeAt && now >= b.mergeAt) {
            if (d < big.r - small.r * 0.3) this.absorb(big, small);
          } else if (d < rs && d > 0.001) {
            const push = (rs - d) * 0.5, nx = dx / d, ny = dy / d;
            a.x -= nx * push; a.y -= ny * push; b.x += nx * push; b.y += ny * push;
          }
        } else if (!this.friendly(a, b)) {
          if (big.mass > small.mass * 1.25 && d < big.r - small.r * 0.4) this.absorb(big, small);
        }
      }
    }
    // cellule vs resto
    for (const c of cells) {
      if (c.dead) continue;
      const pad = c.r + 24;                       // margine: il raggio cresce mentre mangia
      const gx0 = gridIdx(c.x - pad - BORDER.x0), gx1 = gridIdx(c.x + pad - BORDER.x0);
      const gy0 = gridIdx(c.y - pad - BORDER.y0), gy1 = gridIdx(c.y + pad - BORDER.y0);
      for (let gy = gy0; gy <= gy1; gy++) {
        for (let gx = gx0; gx <= gx1; gx++) {
          const a = G.b[gy * GRID_N + gx];
          if (!a) continue;
          for (let i = 0; i < a.length; i++) {
            const e = a[i];
            if (e.dead) continue;
            if (Math.abs(e.x - c.x) > c.r || Math.abs(e.y - c.y) > c.r) continue;
            const d = Math.hypot(e.x - c.x, e.y - c.y);
            if (e.type === TYPE_VIRUS) {
              if (c.mass > e.mass * 1.25 && d < c.r - e.r * 0.4) this.pop(c, e);
            } else if (d < c.r - e.r * 0.4 && c.mass > e.mass * 1.25) {
              this.absorb(c, e);
            }
          }
        }
      }
    }
    // massa espulsa contro virus
    for (const v of ents) {
      if (v.dead || v.type !== TYPE_VIRUS) continue;
      for (const e of ejs) {
        if (e.dead || e.bspeed <= 0) continue;
        if (Math.hypot(e.x - v.x, e.y - v.y) < v.r) {
          this.kill(e);
          v.mass += e.mass; v.r = sizeOf(v.mass); v.feeds++; v.dirty = true;
          if (v.feeds >= VIRUS_FEEDS) {
            v.feeds = 0; v.mass = VIRUS_MASS; v.r = sizeOf(v.mass);
            const n = this.spawnVirus(v.x, v.y);
            const l = Math.hypot(e.bx, e.by) || 1;
            n.bx = e.bx / l; n.by = e.by / l; n.bspeed = 780;
          }
        }
      }
    }
  }
  absorb(big, small) {
    this.kill(small);
    this.eats.push([big.id, small.id]);
    if (big.type === TYPE_CELL) big.mass = Math.min(MAX_CELL_MASS, big.mass + small.mass);
    big.r = sizeOf(big.mass);
    if (small.type === TYPE_CELL) {
      const p = small.owner;
      if (p.cells.every(c => c.dead || c === small) ) {
        this.playerDied(p, big.type === TYPE_CELL ? big : null);
      }
    }
  }
  pop(c, v) {
    this.kill(v);
    this.eats.push([c.id, v.id]);
    const p = c.owner;
    const total = Math.min(MAX_CELL_MASS, c.mass + v.mass);
    const avail = MAX_CELLS - p.cells.filter(x => !x.dead).length;
    let k = Math.min(avail, 7, Math.floor(total / 10) - 1);
    if (k <= 0) { c.mass = total; c.r = sizeOf(c.mass); return; }
    const m = total / (k + 1);
    c.mass = m; c.r = sizeOf(m);
    const a0 = rnd(0, Math.PI * 2), t = Date.now() + 15000 + m * 10;
    c.mergeAt = t;
    for (let i = 0; i < k; i++) {
      const a = a0 + i * (Math.PI * 2 / k);
      const n = this.newEnt(TYPE_CELL, c.x, c.y, m, p.color);
      n.owner = p; n.name = p.name; n.bx = Math.cos(a); n.by = Math.sin(a); n.bspeed = 620; n.mergeAt = t;
      p.cells.push(n); p.pendingAdd.push(n.id);
    }
  }

  // ----- bot
  botThink(p) {
    const me = p.cells.filter(c => !c.dead);
    if (!me.length) return;
    const c = me.reduce((a, b) => (b.mass > a.mass ? b : a));
    p.cells = me;
    let best = null, bestScore = -Infinity, flee = null, fleeD = 1e9;
    const range = 700 + c.r;
    for (const e of this.ents) {
      if (e.dead || e === c || e.owner === p) continue;
      const dx = e.x - c.x, dy = e.y - c.y;
      if (Math.abs(dx) > range || Math.abs(dy) > range) continue;
      const d = Math.hypot(dx, dy);
      if (e.type === TYPE_CELL) {
        if (this.mode === 'teams' && e.owner.team === p.team) continue;
        if (e.mass > c.mass * 1.25) { if (d < fleeD && d < e.r + 400) { flee = e; fleeD = d; } continue; }
        if (c.mass > e.mass * 1.3) { const s = e.mass * 3 - d; if (s > bestScore) { bestScore = s; best = e; } }
      } else if (e.type === TYPE_VIRUS) {
        if (c.mass > e.mass * 1.25 && d < c.r + 120) { flee = e; fleeD = d; }
      } else {
        const s = e.mass - d * 0.6;
        if (s > bestScore) { bestScore = s; best = e; }
      }
    }
    if (flee) { p.mx = c.x - (flee.x - c.x) * 3; p.my = c.y - (flee.y - c.y) * 3; }
    else if (best) { p.mx = best.x; p.my = best.y; }
    else if (Math.random() < 0.3) { p.mx = rnd(BORDER.x0, BORDER.x1); p.my = rnd(BORDER.y0, BORDER.y1); }
  }

  // ----- classifica
  buildLeaderboard() {
    const list = [];
    for (const p of this.players) if (p.alive) list.push({ p, m: p.totalMass() });
    list.sort((a, b) => b.m - a.m);
    this.top = list.length ? list[0].p : null;
    let w;
    if (this.mode === 'teams') {
      const sums = [0, 0, 0]; let tot = 0;
      for (const { p, m } of list) { sums[p.team] += m; tot += m; }
      w = new Writer(32); w.u8(50); w.u32(3);
      for (let i = 0; i < 3; i++) w.f32(tot ? sums[i] / tot : 1 / 3);
    } else {
      const top = list.slice(0, 10);
      w = new Writer(256); w.u8(49); w.u32(top.length);
      for (const { p } of top) { w.u32(p.cells[0] ? p.cells[0].id : 0); w.str(p.name || 'Guest'); }
    }
    const buf = w.done();
    for (const p of this.players) if (p.conn) send(p.conn, buf);
  }

  // ----- invio aggiornamenti
  viewOf(p) {
    let cx, cy, total = 0;
    if (p.alive) {
      const c = p.center(); cx = c.x; cy = c.y;
      for (const k of p.cells) total += k.r;
      p.spectate = false;
    } else {
      const t = this.top && this.top.alive ? this.top : null;
      const c = t ? t.center() : null;
      if (c) { cx = c.x; cy = c.y; for (const k of t.cells) total += k.r; }
      else { cx = (BORDER.x0 + BORDER.x1) / 2; cy = (BORDER.y0 + BORDER.y1) / 2; total = 64; }
      p.spectate = true;
    }
    const scale = Math.pow(Math.min(64 / Math.max(total, 1), 1), 0.4);
    const hw = 1500 / scale, hh = 900 / scale;
    if (p.hub) return { cx, cy, hw: Math.min(hw, BOT_VIEW_W), hh: Math.min(hh, BOT_VIEW_H), total };
    return { cx, cy, hw, hh, total };
  }
  sendUpdate(p) {
    const conn = p.conn, hub = p.hub;
    if (hub) { if (hub.ws.readyState !== 1 || hub.ws.bufferedAmount > HUB_BACKLOG) return; }
    else if (!conn || conn.readyState !== 1) return;
    const out = hub ? (b => hub.push(p.hubId, b)) : (b => send(conn, b));
    for (const id of p.pendingAdd) { const w = new Writer(5); w.u8(32); w.u32(id); out(w.done()); }
    p.pendingAdd.length = 0;
    const v = this.viewOf(p);
    const visible = new Set(), upd = [];
    for (const e of this.ents) {
      if (e.dead) continue;
      if (Math.abs(e.x - v.cx) > v.hw + e.r || Math.abs(e.y - v.cy) > v.hh + e.r) continue;
      visible.add(e.id);
      if (!p.known.has(e.id) || e.type === TYPE_CELL || e.type === TYPE_EJECT || e.bspeed > 0 || e.dirty) upd.push(e);
    }
    const removed = [];
    for (const id of p.known) if (!visible.has(id)) removed.push(id);
    const eats = this.eats.filter(([k, d]) => p.known.has(k) && p.known.has(d));
    const w = new Writer(64 + upd.length * 24);
    w.u8(16); w.u16(eats.length);
    for (const [k, d] of eats) { w.u32(k); w.u32(d); }
    for (const e of upd) {
      w.u32(e.id); w.i16(e.x); w.i16(e.y); w.i16(e.r);
      w.u8(e.color[0]); w.u8(e.color[1]); w.u8(e.color[2]);
      if (hub) { w.u8((e.type === TYPE_VIRUS ? 1 : 0) | (e.type === TYPE_CELL ? 2 : 0) | (e.type === TYPE_EJECT ? 4 : 0)); w.str(''); }
      else { w.u8(e.type === TYPE_VIRUS ? 1 : 0); w.str(e.type === TYPE_CELL ? e.name : ''); }
    }
    w.u32(0);
    w.u32(removed.length);
    for (const id of removed) w.u32(id);
    out(w.done());
    p.known = visible;
    if (p.spectate && !hub) { const s = new Writer(13); s.u8(17); s.f32(v.cx); s.f32(v.cy); s.f32(1); send(conn, s.done()); }
  }
}

function send(ws, buf) { if (ws.readyState === 1) ws.send(buf, { binary: true }, () => {}); }

// ---------------------------------------------------------------- bot esterni (script Tampermonkey)
// Una sola connessione WebSocket ("hub") trasporta tanti bot: i browser limitano le connessioni per scheda (~200-255),
// quindi 1000 bot non potrebbero avere una connessione ciascuno.
//   client -> server : [0xB0] { [id u16][len u8][pacchetto normale: 192 nome, 16 mouse, 17 split, 21 eject] }...
//                      [0xB3][id u16]  = rimuovi il bot
//   server -> client : [0xB1] { [id u16][len u16][pacchetto normale] }...   [0xB4][testo utf16] = avviso
const DEAD_PKT = Buffer.from([0xB5]);                 // "il tuo bot e' morto"
const BORDER_PKT = (() => { const b = new Writer(33); b.u8(64); b.f64(BORDER.x0); b.f64(BORDER.y0); b.f64(BORDER.x1); b.f64(BORDER.y1); return b.done(); })();
function minionEvery() { return minionCount <= 40 ? 1 : Math.max(2, Math.min(12, Math.ceil(minionCount / 100) + 1)); }

class Hub {
  constructor(ws, game, startMass) {
    this.ws = ws; this.game = game; this.startMass = startMass;
    this.bots = new Map(); this.msgs = 0; this.lastNote = 0;
    this.buf = Buffer.allocUnsafe(1 << 16); this.buf[0] = 0xB1; this.o = 1;
  }
  push(id, b) {
    if (b.length > 65535) return;
    const need = 4 + b.length;
    if (this.o + need > 262144) this.flush();
    if (this.o + need > this.buf.length) { const nb = Buffer.allocUnsafe(Math.max(this.buf.length * 2, this.o + need)); this.buf.copy(nb, 0, 0, this.o); this.buf = nb; }
    this.buf.writeUInt16LE(id, this.o); this.buf.writeUInt16LE(b.length, this.o + 2); b.copy(this.buf, this.o + 4);
    this.o += need;
  }
  flush() {
    if (this.o <= 1) return;
    if (this.ws.readyState === 1) this.ws.send(Buffer.from(this.buf.subarray(0, this.o)), { binary: true }, () => {});
    this.o = 1;
  }
  note(text) {
    const now = Date.now();
    if (now - this.lastNote < 5000) return;
    this.lastNote = now;
    const w = new Writer(8 + text.length * 2); w.u8(0xB4); w.str(text); send(this.ws, w.done());
  }
  remove(id) {
    const p = this.bots.get(id);
    if (!p) return;
    this.bots.delete(id); minionCount = Math.max(0, minionCount - 1);
    this.game.removePlayer(p);
  }
  closeAll() { for (const id of Array.from(this.bots.keys())) this.remove(id); this.game.hubs.delete(this); }
}

function hubPacket(hub, id, pk) {
  const game = hub.game, op = pk[0];
  let p = hub.bots.get(id);
  if (!p) {
    if (op !== 192) return;                           // il primo pacchetto di un bot e' sempre il nome
    if (minionCount >= BOT_MAX) { hub.note('Limite bot raggiunto sul server (BOT_MAX=' + BOT_MAX + ')'); return; }
    p = new Player(game, null, false);
    p.isMinion = true; p.hub = hub; p.hubId = id; p.startMass = hub.startMass;
    game.assignTeam(p); game.players.add(p);
    hub.bots.set(id, p); minionCount++;
    hub.push(id, BORDER_PKT);
  }
  switch (op) {
    case 192: {
      if (p.alive || Date.now() - p.lastSpawn < 800) break;
      p.lastSpawn = Date.now();
      p.name = cleanName(readUtf16(pk, 1));
      game.spawnPlayer(p);
      break;
    }
    case 16: {
      if (pk.length >= 17) {
        const x = pk.readDoubleLE(1), y = pk.readDoubleLE(9);
        if (Number.isFinite(x) && Number.isFinite(y)) {
          p.mx = Math.max(BORDER.x0 - 500, Math.min(BORDER.x1 + 500, x));
          p.my = Math.max(BORDER.y0 - 500, Math.min(BORDER.y1 + 500, y));
        }
      }
      break;
    }
    case 17: game.split(p); break;
    case 21: game.eject(p); break;
    default: break;
  }
}

const keyHash = k => crypto.createHash('sha256').update(String(k)).digest();
const BOT_KEY_HASH = BOT_KEY ? keyHash(BOT_KEY) : null;
const keyFails = new Map();                           // ip -> { n, t }  (anti tentativi a raffica)
function keyOk(k) { return !!BOT_KEY_HASH && typeof k === 'string' && k.length > 0 && crypto.timingSafeEqual(keyHash(k), BOT_KEY_HASH); }
function keyBlocked(ip) { const f = keyFails.get(ip); return !!f && Date.now() - f.t < 60000 && f.n >= 8; }
function keyFail(ip) { const f = keyFails.get(ip); if (!f || Date.now() - f.t >= 60000) keyFails.set(ip, { n: 1, t: Date.now() }); else { f.n++; } }

function onHub(ws, ip, url) {
  if (keyBlocked(ip)) return ws.close(4001, 'Troppi tentativi con chiave errata');
  if (admin.isIpBanned(ip)) return ws.close(4001, 'IP bannato');
  if (admin.botsLocked()) return ws.close(4002, 'Bot esterni bloccati dall\'amministratore');
  if (!BOT_KEY_HASH) return ws.close(4001, 'BOT_KEY non impostata sul server');
  if (!keyOk(url.searchParams.get('bk'))) { keyFail(ip); return ws.close(4001, 'Chiave bot errata'); }
  if (BOT_MAX <= 0) return ws.close(4002, 'Bot esterni disattivati (BOT_MAX=0)');
  const game = getGame(url.searchParams.get('mode'), url.searchParams.get('room'));
  const sm = Math.max(START_MASS, Math.min(BOT_MAX_MASS, parseInt(url.searchParams.get('sm') || '', 10) || START_MASS));
  const hub = new Hub(ws, game, sm);
  game.hubs.add(hub);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });
  ws.on('message', (data, isBinary) => {
    if (!isBinary || ++hub.msgs > 1000) return;
    const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
    if (buf.length < 3) return;
    if (buf[0] === 0xB0) {
      let o = 1;
      while (o + 3 <= buf.length) {
        const id = buf.readUInt16LE(o), len = buf[o + 2]; o += 3;
        if (len < 1 || o + len > buf.length) break;
        hubPacket(hub, id, buf.subarray(o, o + len));
        o += len;
      }
    } else if (buf[0] === 0xB3) hub.remove(buf.readUInt16LE(1));
  });
  ws.on('close', () => { hub.closeAll(); });
  ws.on('error', () => {});
}
const hubTimer = setInterval(() => {
  for (const g of games.values()) for (const h of g.hubs) h.msgs = 0;
  const now = Date.now();
  for (const [ip, f] of keyFails) if (now - f.t >= 60000) keyFails.delete(ip);
}, 1000);

// ---------------------------------------------------------------- stanze
const games = new Map();
function getGame(mode, room) {
  if (!['ffa', 'ffa2', 'experimental', 'teams', 'party'].includes(mode)) mode = 'ffa';
  room = String(room || '').replace(/[^A-Za-z0-9_-]/g, '').slice(0, 24);
  if (mode === 'party' && !room) room = 'public';
  const key = mode === 'party' ? 'party:' + room : mode;
  let g = games.get(key);
  if (!g) { g = new Game(key, mode); games.set(key, g); }
  return g;
}
setInterval(() => {
  for (const [key, g] of games) {
    if (g.humans() === 0 && !g.persistent && Date.now() - g.emptySince > 60000) { clearInterval(g.timer); for (const h of Array.from(g.hubs)) { try { h.ws.close(1001, 'stanza chiusa'); } catch (e) {} h.closeAll(); } games.delete(key); }
  }
}, 15000);

// ---------------------------------------------------------------- amministrazione (comandi in chat e canale del pannello)
const admin = require('./zl_admin')({
  games: () => games, minions: () => minionCount,
  getBotMax: () => BOT_MAX, setBotMax: v => { BOT_MAX = v; },
  getBotFight: () => BOT_FIGHT, setBotFight: v => { BOT_FIGHT = !!v; },
  getFood: () => FOOD_TARGET,
  setFood: v => { FOOD_TARGET = v; for (const g of games.values()) for (const e of g.ents) if (g.foodCount > v && e.type === TYPE_FOOD && !e.dead) g.kill(e); },
  kickBots: () => { for (const g of games.values()) for (const h of Array.from(g.hubs)) { try { h.ws.close(4002, 'Bot scollegati dall\'amministratore'); } catch (e) {} } },
  MAX_CELL_MASS, START_MASS, sizeOf, BORDER
});

// ---------------------------------------------------------------- server HTTP + WebSocket
const server = http.createServer((req, res) => {
  if (req.url === '/health') {
    let humans = 0; for (const g of games.values()) humans += g.humans();
    let tickMs = 0; for (const g of games.values()) tickMs = Math.max(tickMs, g.tickMs);
    res.writeHead(200, { 'Content-Type': 'application/json' });
    return res.end(JSON.stringify({ ok: true, rooms: games.size, players: humans, bots: minionCount, tickMs: Math.round(tickMs * 10) / 10 }));
  }
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('ZeroLegend Agar server OK');
});

const ipCount = new Map();
const wss = new WebSocketServer({
  server, maxPayload: 8192,
  verifyClient: (info) => {
    if (!ALLOWED_ORIGINS.length) return true;
    const o = info.origin || info.req.headers.origin || '';
    return ALLOWED_ORIGINS.includes(o);
  }
});

wss.on('connection', (ws, req) => {
  const ip = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').toString().split(',')[0].trim();
  let url; try { url = new URL(req.url, 'http://x'); } catch (e) { url = new URL('http://x/'); }
  if (url.searchParams.has('ak')) return admin.onChannel(ws, ip, url);                                  // pannello admin
  if (url.searchParams.has('bk') || url.searchParams.get('hub') === '1') return onHub(ws, ip, url);   // bot esterni
  if (admin.isIpBanned(ip)) return ws.close(4003, 'IP bannato');

  const n = (ipCount.get(ip) || 0) + 1;
  if (n > MAX_CONN_PER_IP) return ws.close(1013, 'troppe connessioni');
  ipCount.set(ip, n);
  const game = getGame(url.searchParams.get('mode'), url.searchParams.get('room'));
  if (game.humans() >= MAX_PLAYERS_PER_ROOM) { ipCount.set(ip, n - 1); return ws.close(1013, 'stanza piena'); }

  const player = new Player(game, ws, false);
  player.ip = ip;
  game.assignTeam(player);
  game.players.add(player);
  game.emptySince = 0;
  ws.isAlive = true;

  const b = new Writer(33); b.u8(64);
  b.f64(BORDER.x0); b.f64(BORDER.y0); b.f64(BORDER.x1); b.f64(BORDER.y1);
  send(ws, b.done());

  let msgs = 0;
  const rate = setInterval(() => { msgs = 0; }, 1000);

  ws.on('pong', () => { ws.isAlive = true; });
  ws.on('message', (data, isBinary) => {
    if (!isBinary || ++msgs > 150) return;
    const buf = Buffer.isBuffer(data) ? data : Buffer.from(data);
    if (!buf.length) return;
    const op = buf[0];
    switch (op) {
      case 150: { // token di login
        player.user = account.verifyToken(readUtf16(buf, 1));
        if (player.user && admin.isUserBanned(player.user.name)) return ws.close(4003, 'Account bannato: ' + admin.banReason(player.user.name, ip));
        break;
      }
      case 192: { // nickname -> entra in partita
        if (player.alive || Date.now() - player.lastSpawn < 800) break;
        player.lastSpawn = Date.now();
        player.name = player.user ? player.user.name : cleanName(readUtf16(buf, 1));
        game.spawnPlayer(player);
        break;
      }
      case 16: { // mouse
        if (buf.length >= 17) {
          const x = buf.readDoubleLE(1), y = buf.readDoubleLE(9);
          if (Number.isFinite(x) && Number.isFinite(y)) {
            player.mx = Math.max(BORDER.x0 - 500, Math.min(BORDER.x1 + 500, x));
            player.my = Math.max(BORDER.y0 - 500, Math.min(BORDER.y1 + 500, y));
          }
        }
        break;
      }
      case 17: game.split(player); break;
      case 21: game.eject(player); break;
      case 206: if (buf.length > 2) {
        const text = readUtf16(buf, 2).replace(/[\u0000-\u001f]/g, '');
        if (text.charAt(0) === '/' && admin.isAdmin(player.user)) {          // comando admin: risposta solo a lui
          for (const l of admin.run(text.slice(1)).slice(0, 6)) {
            const w = new Writer(64 + l.length * 2); w.u8(99); w.u8(0); w.u8(255); w.u8(200); w.u8(0); w.str('SERVER'); w.str(l.slice(0, 120)); send(ws, w.done());
          }
        } else game.chat(player, text);
      } break;
      default: break; // 254, 255, 56, 18, 19, 65, 1...: ignorati
    }
  });
  ws.on('close', () => {
    clearInterval(rate);
    ipCount.set(ip, Math.max(0, (ipCount.get(ip) || 1) - 1));
    game.removePlayer(player);
    if (game.humans() === 0) game.emptySince = Date.now();
  });
  ws.on('error', () => {});
});

setInterval(() => {
  for (const ws of wss.clients) { if (!ws.isAlive) { ws.terminate(); continue; } ws.isAlive = false; try { ws.ping(); } catch (e) {} }
}, 30000);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('ZeroLegend Agar in ascolto su ' + PORT + (process.env.AUTH_SECRET ? '' : ' (AUTH_SECRET mancante: solo ospiti)') + (BOT_KEY ? ' | bot esterni: max ' + BOT_MAX + ', massa max ' + BOT_MAX_MASS : ' | BOT_KEY mancante: bot esterni disattivati')));
