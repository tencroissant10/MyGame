'use strict';
// ランキング予想ゲーム サーバー（外部ライブラリ不要 / Node.js 18+）
// リアルタイム同期は Server-Sent Events、操作は POST /api/action で行う。
// 出題者の正解や他人の予想は、公開フェーズになるまでクライアントへ一切送らない。

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const os = require('os');
const TOPICS = require('./topics');

const PORT = Number(process.env.PORT) || 3000;
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_PLAYERS = 12;
const ROOM_TTL_MS = 3 * 60 * 60 * 1000;

const rooms = new Map(); // code -> room

// ---------- ユーティリティ ----------
const rid = (n = 12) => crypto.randomBytes(n).toString('hex');
const shuffle = (arr) => {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
};
const cleanText = (s, max) => String(s ?? '').replace(/\s+/g, ' ').trim().slice(0, max);

function newRoomCode() {
  for (let i = 0; i < 5000; i++) {
    const c = String(crypto.randomInt(1000, 10000));
    if (!rooms.has(c)) return c;
  }
  return null;
}

function isValidOrder(order) {
  return Array.isArray(order) && order.length === 5 &&
    order.every((n) => Number.isInteger(n) && n >= 0 && n < 5) &&
    new Set(order).size === 5;
}

// ---------- ルーム / プレイヤー ----------
function createRoom() {
  const code = newRoomCode();
  if (!code) return null;
  const room = { code, hostId: null, players: [], phase: 'lobby', game: null, touched: Date.now() };
  rooms.set(code, room);
  return room;
}

function addPlayer(room, name) {
  const p = { id: rid(6), token: rid(16), name, conns: new Set() };
  room.players.push(p);
  if (!room.hostId) room.hostId = p.id;
  return p;
}

const getPlayer = (room, id) => room.players.find((p) => p.id === id);
const online = (p) => p.conns.size > 0;

function removePlayer(room, p, reason) {
  room.players = room.players.filter((x) => x !== p);
  for (const res of p.conns) {
    try { res.write(`data: ${JSON.stringify({ error: reason })}\n\n`); res.end(); } catch {}
  }
  p.conns.clear();
  if (room.hostId === p.id) room.hostId = room.players[0]?.id ?? null;
  if (room.players.length === 0) rooms.delete(room.code);
}

// ---------- ゲーム進行 ----------
function startGame(room) {
  const members = room.players.map((p) => p.id);
  const correct = {};
  for (const a of members) { correct[a] = {}; for (const b of members) if (a !== b) correct[a][b] = 0; }
  room.game = {
    members,
    order: [], // 出題（答え合わせ）の順。全員のランキングが出そろってから決める
    idx: 0,
    scores: Object.fromEntries(members.map((id) => [id, 0])),
    correct, // correct[a][b] = a が b のランキングを当てた個数
    usedTopics: new Set(),
    sheets: {}, // 各自のお題とランキング { topic, choices, answer }
    round: null,
  };
  // 全員に別々のお題を配り、同時にランキングを作ってもらう
  for (const id of members) room.game.sheets[id] = { ...pickTopic(room.game), answer: null };
  room.phase = 'ranking';
}

// ランキング提出済みの人だけで、予想→答え合わせのラウンドを開始する
function beginGuessing(room) {
  const g = room.game;
  g.order = shuffle(g.members.filter((id) => g.sheets[id].answer));
  g.idx = 0;
  beginRound(room);
}

function pickTopic(game) {
  if (game.usedTopics.size >= TOPICS.length) game.usedTopics.clear();
  const unused = TOPICS.map((_, i) => i).filter((i) => !game.usedTopics.has(i));
  const i = unused[crypto.randomInt(unused.length)];
  game.usedTopics.add(i);
  return { topic: TOPICS[i][0], choices: shuffle(TOPICS[i][1]) };
}

function beginRound(room) {
  const g = room.game;
  const presenterId = g.order[g.idx];
  const { topic, choices, answer } = g.sheets[presenterId];
  g.round = { presenterId, topic, choices, answer, guesses: {}, results: null };
  room.phase = 'guessing';
}

const guessersOf = (room) => room.game.members.filter((id) => id !== room.game.round.presenterId);

function reveal(room) {
  const g = room.game, r = g.round;
  r.results = guessersOf(room).map((id) => {
    const guess = r.guesses[id];
    if (!guess) return { id, guess: null, hits: null, count: 0, points: 0 };
    const hits = guess.map((c, i) => c === r.answer[i]);
    const count = hits.filter(Boolean).length;
    const points = count === 5 ? 7 : count; // 全問正解はボーナスで合計7pt
    g.scores[id] += points;
    g.correct[id][r.presenterId] += count;
    return { id, guess, hits, count, points };
  });
  room.phase = 'reveal';
}

function nextRound(room) {
  const g = room.game;
  g.idx++;
  if (g.idx >= g.order.length) { room.phase = 'final'; g.round = null; }
  else beginRound(room);
}

function finalSummary(room) {
  const g = room.game;
  const sorted = g.members
    .map((id) => ({ id, score: g.scores[id] }))
    .sort((a, b) => b.score - a.score);
  sorted.forEach((x, i) => { x.rank = i > 0 && x.score === sorted[i - 1].score ? sorted[i - 1].rank : i + 1; });

  const pairs = [];
  for (let i = 0; i < g.members.length; i++) {
    for (let j = i + 1; j < g.members.length; j++) {
      const a = g.members[i], b = g.members[j];
      pairs.push({ a, b, ab: g.correct[a][b], ba: g.correct[b][a], total: g.correct[a][b] + g.correct[b][a] });
    }
  }
  pairs.sort((x, y) => y.total - x.total);
  const best = pairs.length && pairs[0].total > 0 ? pairs.filter((p) => p.total === pairs[0].total) : [];
  return { ranking: sorted, pairs, best };
}

// ---------- 各プレイヤー向けの状態（秘匿情報はここで制御） ----------
function viewFor(room, me) {
  const g = room.game;
  const v = {
    code: room.code,
    me: me.id,
    hostId: room.hostId,
    phase: room.phase,
    players: room.players.map((p) => ({ id: p.id, name: p.name, online: online(p), score: g ? g.scores[p.id] ?? 0 : 0 })),
  };
  if (g && room.phase === 'ranking') {
    // 自分のお題・ランキングだけを送る。他人については「提出済みか」だけ
    if (g.sheets[me.id]) v.mySheet = g.sheets[me.id];
    v.submitted = g.members.filter((id) => g.sheets[id].answer);
    v.members = g.members;
  }
  if (g && ['guessing', 'reveal', 'final'].includes(room.phase)) {
    v.roundNum = Math.min(g.idx + 1, g.order.length);
    v.roundTotal = g.order.length;
    v.order = g.order;
  }
  const r = g?.round;
  if (r && ['guessing', 'reveal'].includes(room.phase)) {
    const isPresenter = r.presenterId === me.id;
    v.round = { presenterId: r.presenterId, guessers: guessersOf(room), topic: r.topic, choices: r.choices, answered: Object.keys(r.guesses) };
    if (room.phase === 'guessing') {
      if (isPresenter) v.round.answer = r.answer;          // 正解は出題者本人にだけ
      if (r.guesses[me.id]) v.round.myGuess = r.guesses[me.id]; // 予想は本人にだけ
    } else {
      v.round.answer = r.answer;
      v.round.results = r.results;
    }
  }
  if (room.phase === 'final') v.final = finalSummary(room);
  return v;
}

function broadcast(room) {
  room.touched = Date.now();
  for (const p of room.players) {
    if (!p.conns.size) continue;
    const msg = `data: ${JSON.stringify(viewFor(room, p))}\n\n`;
    for (const res of p.conns) { try { res.write(msg); } catch {} }
  }
}

// ---------- アクション ----------
function handleAction(room, me, body) {
  const g = room.game, r = g?.round;
  const isHost = room.hostId === me.id;
  const isPresenter = r && r.presenterId === me.id;
  const mySheet = g?.sheets[me.id];

  switch (body.type) {
    case 'start':
      if (!isHost) return '部屋主だけがゲームを開始できます';
      if (room.phase !== 'lobby') return 'すでにゲーム中です';
      if (room.players.length < 2) return '2人以上で開始できます';
      startGame(room);
      return null;

    case 'kick': {
      if (!isHost) return '部屋主だけが操作できます';
      if (room.phase !== 'lobby') return 'ゲーム中は退出させられません';
      const target = getPlayer(room, body.id);
      if (!target || target === me) return '対象が見つかりません';
      removePlayer(room, target, '部屋主によって退出しました');
      return null;
    }

    case 'leave':
      if (room.phase !== 'lobby' && room.phase !== 'final') return 'ゲーム中は退出できません';
      removePlayer(room, me, '退出しました');
      if (room.phase === 'final' && rooms.has(room.code)) {
        // 退出者がいても最終結果は残す（新しいゲーム開始時にメンバーを再構成）
      }
      return null;

    case 'reroll':
      if (room.phase !== 'ranking' || !mySheet || mySheet.answer) return 'いまはお題を変更できません';
      Object.assign(mySheet, pickTopic(g));
      return null;

    case 'custom': {
      if (room.phase !== 'ranking' || !mySheet || mySheet.answer) return 'いまはお題を変更できません';
      const topic = cleanText(body.topic, 30);
      const choices = Array.isArray(body.choices) ? body.choices.map((c) => cleanText(c, 20)) : [];
      if (!topic) return 'お題を入力してください';
      if (choices.length !== 5 || choices.some((c) => !c)) return '選択肢を5個すべて入力してください';
      if (new Set(choices).size !== 5) return '選択肢が重複しています';
      mySheet.topic = topic;
      mySheet.choices = choices;
      return null;
    }

    case 'unsubmit': // 全員がそろう前なら自分のランキングを修正できる
      if (room.phase !== 'ranking' || !mySheet?.answer) return 'いまは修正できません';
      mySheet.answer = null;
      return null;

    case 'submitRanking': {
      if (!isValidOrder(body.order)) return '1位〜5位をすべて重複なく選んでください';
      if (room.phase === 'ranking') {
        if (!mySheet) return 'このゲームの参加者ではありません';
        if (mySheet.answer) return 'すでにランキングを提出済みです';
        mySheet.answer = body.order.slice();
        if (g.members.every((id) => g.sheets[id].answer)) beginGuessing(room);
        return null;
      }
      if (room.phase === 'guessing') {
        if (isPresenter) return '出題者は予想できません';
        if (!g.members.includes(me.id)) return 'このゲームの参加者ではありません';
        if (r.guesses[me.id]) return 'すでに予想を送信済みです'; // 二重回答防止
        r.guesses[me.id] = body.order.slice();
        if (guessersOf(room).every((id) => r.guesses[id])) reveal(room);
        return null;
      }
      return 'いまは回答できません';
    }

    case 'forceReveal':
      if (!isHost) return '部屋主だけが操作できます';
      if (room.phase !== 'guessing') return 'いまは公開できません';
      reveal(room);
      return null;

    case 'forceStartGuessing': // 未提出の人を待たずに予想タイムへ（未提出者のお題は出題されない）
      if (!isHost) return '部屋主だけが操作できます';
      if (room.phase !== 'ranking') return 'いまは開始できません';
      if (!g.members.some((id) => g.sheets[id].answer)) return 'まだ誰もランキングを提出していません';
      beginGuessing(room);
      return null;

    case 'next':
      if (room.phase !== 'reveal') return 'いまは進めません';
      if (!isHost && !isPresenter) return '部屋主か出題者が進めます';
      nextRound(room);
      return null;

    case 'closeRoom': // 部屋主による強制終了：ルームを解散し、全員を参加前の画面へ戻す
      if (!isHost) return '部屋主だけがゲームを終了できます';
      for (const p of room.players.slice()) {
        for (const res of p.conns) {
          try { res.write(`data: ${JSON.stringify({ error: '部屋主がゲームを終了しました', closed: true })}\n\n`); res.end(); } catch {}
        }
        p.conns.clear();
      }
      rooms.delete(room.code);
      return null;

    case 'replay':
      if (!isHost) return '部屋主だけが再戦を開始できます';
      if (room.phase !== 'final') return 'ゲームが終了していません';
      room.game = null; // ポイント・相性をリセット
      room.phase = 'lobby';
      return null;

    default:
      return '不明な操作です';
  }
}

// ---------- HTTP ----------
function lanUrls() {
  const urls = [];
  for (const list of Object.values(os.networkInterfaces())) {
    for (const ni of list || []) {
      if (ni.family === 'IPv4' && !ni.internal) urls.push(`http://${ni.address}:${PORT}`);
    }
  }
  return urls;
}

function sendJson(res, status, obj) {
  res.writeHead(status, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(JSON.stringify(obj));
}

function readBody(req) {
  return new Promise((resolve) => {
    let data = '';
    req.on('data', (c) => { data += c; if (data.length > 10000) req.destroy(); });
    req.on('end', () => { try { resolve(JSON.parse(data || '{}')); } catch { resolve({}); } });
    req.on('error', () => resolve({}));
  });
}

const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.ico': 'image/x-icon' };

function serveStatic(req, res, pathname) {
  const rel = pathname === '/' ? 'index.html' : decodeURIComponent(pathname).replace(/^\/+/, '');
  const file = path.normalize(path.join(PUBLIC_DIR, rel));
  if (!file.startsWith(PUBLIC_DIR)) { res.writeHead(403); return res.end(); }
  fs.readFile(file, (err, buf) => {
    if (err) { res.writeHead(404); return res.end('Not found'); }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(file)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
    res.end(buf);
  });
}

function nameError(room, name) {
  if (!name) return 'ニックネームを入力してください';
  if (room && room.players.some((p) => p.name === name)) return 'その名前はすでに使われています';
  return null;
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const p = url.pathname;

  if (req.method === 'GET' && p === '/api/info') return sendJson(res, 200, { lanUrls: lanUrls() });

  if (req.method === 'GET' && p === '/api/events') {
    const room = rooms.get(url.searchParams.get('code') || '');
    const me = room?.players.find((x) => x.token === url.searchParams.get('token'));
    res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-cache, no-transform', Connection: 'keep-alive', 'X-Accel-Buffering': 'no' });
    if (!room || !me) {
      res.write(`data: ${JSON.stringify({ error: 'ルームが見つかりません（終了した可能性があります）' })}\n\n`);
      return res.end();
    }
    res.write('retry: 2000\n\n');
    me.conns.add(res);
    broadcast(room);
    req.on('close', () => {
      me.conns.delete(res);
      if (rooms.has(room.code)) broadcast(room);
    });
    return;
  }

  if (req.method === 'POST' && p === '/api/create') {
    const body = await readBody(req);
    const name = cleanText(body.name, 12);
    const err = nameError(null, name);
    if (err) return sendJson(res, 400, { error: err });
    const room = createRoom();
    if (!room) return sendJson(res, 503, { error: 'ルームを作成できませんでした' });
    const me = addPlayer(room, name);
    return sendJson(res, 200, { code: room.code, token: me.token });
  }

  if (req.method === 'POST' && p === '/api/join') {
    const body = await readBody(req);
    const room = rooms.get(cleanText(body.code, 8));
    if (!room) return sendJson(res, 404, { error: 'ルーム番号が見つかりません' });
    if (room.phase !== 'lobby') return sendJson(res, 409, { error: 'ゲーム中のため入室できません。次のゲームまでお待ちください' });
    if (room.players.length >= MAX_PLAYERS) return sendJson(res, 409, { error: `満員です（最大${MAX_PLAYERS}人）` });
    const name = cleanText(body.name, 12);
    const err = nameError(room, name);
    if (err) return sendJson(res, 400, { error: err });
    const me = addPlayer(room, name);
    broadcast(room);
    return sendJson(res, 200, { code: room.code, token: me.token });
  }

  if (req.method === 'POST' && p === '/api/action') {
    const body = await readBody(req);
    const room = rooms.get(String(body.code || ''));
    const me = room?.players.find((x) => x.token === body.token);
    if (!room || !me) return sendJson(res, 404, { error: 'ルームが見つかりません' });
    const err = handleAction(room, me, body);
    if (err) return sendJson(res, 400, { error: err });
    if (rooms.has(room.code)) broadcast(room);
    return sendJson(res, 200, { ok: true });
  }

  if (req.method === 'GET') return serveStatic(req, res, p);
  res.writeHead(405); res.end();
});

// 接続維持のハートビート & 放置ルームの掃除
setInterval(() => {
  const now = Date.now();
  for (const room of rooms.values()) {
    for (const pl of room.players) for (const c of pl.conns) { try { c.write(': ping\n\n'); } catch {} }
    if (now - room.touched > ROOM_TTL_MS && room.players.every((pl) => !online(pl))) rooms.delete(room.code);
  }
}, 20000);

server.listen(PORT, '0.0.0.0', () => {
  console.log(`\n🎉 ランキング予想ゲーム 起動しました`);
  console.log(`  このPC:        http://localhost:${PORT}`);
  for (const u of lanUrls()) console.log(`  同じWi-Fiの端末: ${u}`);
  console.log('');
});
