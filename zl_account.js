// Modulo account per server.js. Nessuna dipendenza (Node 18+).
// Variabili ambiente: AUTH_SECRET, SERVER_KEY (uguali a api/config.local.php), SAVE_URL
const crypto = require('crypto');
const b64u = b => Buffer.from(b).toString('base64').replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');

// Verifica il token emesso da login.php -> { uid, name } oppure null (ospite)
function verifyToken(tok) {
  if (!process.env.AUTH_SECRET) return null;
  if (typeof tok !== 'string' || tok.split('.').length !== 2) return null;
  const [p, sig] = tok.split('.');
  const exp = b64u(crypto.createHmac('sha256', process.env.AUTH_SECRET).update(p).digest());
  const a = Buffer.from(exp), b = Buffer.from(sig);
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  try {
    const d = JSON.parse(Buffer.from(p.replace(/-/g, '+').replace(/_/g, '/'), 'base64').toString());
    return d.exp > Date.now() / 1000 ? { uid: d.uid, name: d.name } : null;
  } catch (e) { return null; }
}

// Salva la partita (statistiche calcolate dal server, mai dal client)
async function saveSession(user, sessionUid, stats) {
  if (!process.env.SERVER_KEY || !process.env.SAVE_URL) return { ok: false, skipped: true };
  const body = JSON.stringify({
    ts: Math.floor(Date.now() / 1000),
    user_id: user.uid,
    session_uid: sessionUid,
    kills: stats.kills | 0,
    max_mass: Math.floor(stats.maxMass) | 0,
    seconds: stats.seconds | 0
  });
  const sig = crypto.createHmac('sha256', process.env.SERVER_KEY).update(body).digest('hex');
  const r = await fetch(process.env.SAVE_URL, { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-Signature': sig }, body });
  const j = await r.json();
  if (!j.ok) throw new Error(j.error || 'save.php ha rifiutato la richiesta');
  return j;
}
module.exports = { verifyToken, saveSession };
