'use strict';
/*
 * zl_admin.js - comandi di amministrazione per il server ZeroLegend Agar.
 *
 * Variabili ambiente:
 *   ADMIN_USERS  nomi utente admin separati da virgola (default: ZeroTheLegend). Riconosciuti dal token di login verificato dal server.
 *   ADMIN_KEY    chiave del canale per il pannello dello script (se vuota usa BOT_KEY)
 *   BAN_FILE     file dei ban (default ./bans.json). Su Railway senza volume si azzera ad ogni deploy.
 */
const fs = require('fs');
const crypto = require('crypto');

module.exports = function createAdmin(ctx) {
  const ADMINS = new Set((process.env.ADMIN_USERS || 'ZeroTheLegend').split(',').map(s => s.trim().toLowerCase()).filter(Boolean));
  const KEY = process.env.ADMIN_KEY || process.env.BOT_KEY || '';
  const BAN_FILE = process.env.BAN_FILE || './bans.json';
  const hash = k => crypto.createHash('sha256').update(String(k)).digest();
  const KEY_HASH = KEY ? hash(KEY) : null;
  let bans = { users: {}, ips: {} };
  let botsLocked = false;

  try { const j = JSON.parse(fs.readFileSync(BAN_FILE, 'utf8')); bans = { users: j.users || {}, ips: j.ips || {} }; } catch (e) {}
  const saveBans = () => { try { fs.writeFileSync(BAN_FILE, JSON.stringify(bans)); } catch (e) { console.error('ban non salvati:', e.message); } };
  const active = b => b && (!b.until || b.until > Date.now());
  const lc = s => String(s || '').toLowerCase();

  const isAdmin = user => !!user && ADMINS.has(lc(user.name));
  const isUserBanned = name => { const b = bans.users[lc(name)]; if (b && !active(b)) { delete bans.users[lc(name)]; saveBans(); return false; } return !!b; };
  const isIpBanned = ip => { const b = bans.ips[ip]; if (b && !active(b)) { delete bans.ips[ip]; saveBans(); return false; } return !!b; };
  const banReason = (name, ip) => ((bans.users[lc(name)] || bans.ips[ip] || {}).reason) || 'ban';

  function allPlayers() { const a = []; for (const g of ctx.games().values()) for (const p of g.players) if (!p.isBot) a.push(p); return a; }
  function find(q) {
    q = lc(q); if (!q) return null;
    const list = allPlayers().filter(p => !p.isMinion);
    return list.find(p => String(p.pid) === q) || list.find(p => lc(p.name) === q) || list.find(p => lc(p.name).startsWith(q)) || null;
  }
  const num = (v, a, b) => { const n = Number(v); return Number.isFinite(n) ? Math.max(a, Math.min(b, n)) : NaN; };
  const kickPlayer = (p, why) => { try { if (p.conn) p.conn.close(4004, why || 'Espulso dall\'amministratore'); } catch (e) {} };

  const HELP = [
    '/list  /kick n  /ban n [min] [motivo]  /unban nome|ip  /bans',
    '/mass n massa  /kill n  /tp n x y  /botmax N  /botlock on|off',
    '/kickbots  /food N  /status   (n = nome o id)'
  ];

  // esegue un comando (senza "/" iniziale) e restituisce un array di righe di risposta
  function run(line) {
    const parts = String(line).trim().split(/\s+/);
    const cmd = lc(parts.shift());
    const A = parts;
    switch (cmd) {
      case 'help': return HELP;
      case 'status': {
        let rooms = 0, hum = 0; for (const g of ctx.games().values()) { rooms++; hum += g.humans(); }
        return ['stanze ' + rooms + ' | giocatori ' + hum + ' | bot esterni ' + ctx.minions() + '/' + ctx.getBotMax() + (botsLocked ? ' (BLOCCATI)' : '') + ' | cibo ' + ctx.getFood()];
      }
      case 'list': {
        const l = allPlayers().filter(p => !p.isMinion).slice(0, 30).map(p => p.pid + ':' + (p.name || '?') + (p.alive ? ' m' + Math.round(p.totalMass()) : ' -'));
        return [l.length ? l.join(' | ') : 'nessun giocatore'];
      }
      case 'kick': {
        const p = find(A[0]); if (!p) return ['giocatore non trovato'];
        kickPlayer(p); return ['espulso ' + p.name];
      }
      case 'ban': {
        const p = find(A[0]); if (!p) return ['giocatore non trovato'];
        let min = 0, rest = A.slice(1);
        if (rest.length && /^\d+$/.test(rest[0])) { min = parseInt(rest.shift(), 10); }
        const rec = { until: min > 0 ? Date.now() + min * 60000 : 0, reason: rest.join(' ').slice(0, 80) || 'ban' };
        const out = [];
        if (p.user) { bans.users[lc(p.user.name)] = rec; out.push('account ' + p.user.name); }
        if (p.ip) { bans.ips[p.ip] = rec; out.push('ip'); }
        saveBans(); kickPlayer(p, 'Bannato: ' + rec.reason);
        return ['bannato ' + out.join(' + ') + (min ? ' per ' + min + ' min' : ' (permanente)')];
      }
      case 'unban': {
        const k = A[0]; if (!k) return ['uso: /unban nome|ip'];
        const a = delete bans.users[lc(k)], b = delete bans.ips[k];
        saveBans(); return ['rimosso dai ban (se presente): ' + k];
      }
      case 'bans': {
        const u = Object.keys(bans.users).filter(k => active(bans.users[k])), i = Object.keys(bans.ips).filter(k => active(bans.ips[k]));
        return ['account: ' + (u.join(', ') || '-'), 'ip: ' + (i.join(', ') || '-')];
      }
      case 'mass': {
        const p = find(A[0]), n = num(A[1], 10, ctx.MAX_CELL_MASS * 16);
        if (!p) return ['giocatore non trovato']; if (isNaN(n)) return ['uso: /mass n massa'];
        if (!p.alive || !p.cells.length) return [p.name + ' non e\' in partita'];
        const cells = p.cells.filter(c => !c.dead), tot = cells.reduce((s, c) => s + c.mass, 0), f = n / tot;
        for (const c of cells) { c.mass = Math.max(ctx.START_MASS, Math.min(ctx.MAX_CELL_MASS, c.mass * f)); c.r = ctx.sizeOf(c.mass); c.dirty = true; }
        return [p.name + ': massa ' + Math.round(p.totalMass())];
      }
      case 'kill': {
        const p = find(A[0]); if (!p) return ['giocatore non trovato'];
        if (!p.alive) return [p.name + ' non e\' in partita'];
        for (const c of p.cells) p.game.kill(c);
        p.game.playerDied(p, null);
        return ['eliminato ' + p.name];
      }
      case 'tp': {
        const p = find(A[0]), x = num(A[1], ctx.BORDER.x0, ctx.BORDER.x1), y = num(A[2], ctx.BORDER.y0, ctx.BORDER.y1);
        if (!p) return ['giocatore non trovato']; if (isNaN(x) || isNaN(y)) return ['uso: /tp n x y'];
        if (!p.alive) return [p.name + ' non e\' in partita'];
        for (const c of p.cells) { c.x = x; c.y = y; c.bspeed = 0; }
        p.mx = x; p.my = y;
        return [p.name + ' -> ' + Math.round(x) + ',' + Math.round(y)];
      }
      case 'botmax': {
        const n = num(A[0], 0, 2000); if (isNaN(n)) return ['uso: /botmax N (0-2000)'];
        ctx.setBotMax(Math.floor(n)); return ['BOT_MAX = ' + Math.floor(n) + ' (fino al riavvio)'];
      }
      case 'botlock': {
        if (!/^(on|off)$/i.test(A[0] || '')) return ['uso: /botlock on|off'];
        botsLocked = lc(A[0]) === 'on'; if (botsLocked) ctx.kickBots();
        return ['bot esterni ' + (botsLocked ? 'bloccati e scollegati' : 'di nuovo ammessi')];
      }
      case 'kickbots': { ctx.kickBots(); return ['bot esterni scollegati']; }
      case 'food': {
        const n = num(A[0], 100, 20000); if (isNaN(n)) return ['uso: /food N (100-20000)'];
        ctx.setFood(Math.floor(n)); return ['cibo = ' + Math.floor(n)];
      }
      default: return ['comando sconosciuto. /help'];
    }
  }

  // canale per il pannello dello script: wss://server/?ak=CHIAVE ; ogni messaggio di testo e' un comando ("/" facoltativa)
  const fails = new Map();
  function onChannel(ws, ip, url) {
    const f = fails.get(ip);
    if (f && Date.now() - f.t < 60000 && f.n >= 8) return ws.close(4001, 'Troppi tentativi');
    const k = url.searchParams.get('ak') || '';
    if (!KEY_HASH) return ws.close(4001, 'ADMIN_KEY/BOT_KEY non impostata sul server');
    if (!k || !crypto.timingSafeEqual(hash(k), KEY_HASH)) {
      if (!f || Date.now() - f.t >= 60000) fails.set(ip, { n: 1, t: Date.now() }); else f.n++;
      return ws.close(4001, 'Chiave admin errata');
    }
    ws.send('Admin collegato. /help per i comandi');
    ws.on('message', data => {
      const t = String(data).trim().replace(/^\//, '');
      if (!t || t.length > 200) return;
      try { for (const l of run(t)) ws.send(l); } catch (e) { ws.send('errore: ' + e.message); }
    });
    ws.on('error', () => {});
  }

  return { isAdmin, run, isUserBanned, isIpBanned, banReason, onChannel, botsLocked: () => botsLocked };
};
