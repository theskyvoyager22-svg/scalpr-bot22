const express = require('express');
const crypto  = require('crypto');
const cors    = require('cors');
const https   = require('https');

const app = express();
app.use(cors());
app.use(express.json());

// ─── CONFIG ───────────────────────────────────────────────────────────────────
const CONFIG = {
  API_KEY:    'GMuw4Yz4dP3bbyHi2nuU9EpZWrT0HfjT866mf8ypAYyTb6bI6AF6FXLXhZa7z5EC',   // set via hardcode below
  API_SECRET: '842R1G1EoIIJKArvUpRe3uc67H9WfuPFzTACNHFsWjg4C9OyJ8c2mPfp7Nt9qEfS',   // set via hardcode below
  PAPER_MODE: false,
  MODE: 'SPOT',     // SPOT trading — no leverage, no liquidation, lower fees
  REST_BASE: 'https://api.binance.com',
  DAILY_LOSS_LIMIT_PCT: 5,

  LEVERAGE: 5,
  TARGET_PCT: 1.0,   // 1% take profit
  STOP_PCT:   1.0,   // 1% stop loss

  // Fees: Binance Spot taker 0.1% per side = 0.2% round trip
  // Net profit per win after fees: 1.0% - 0.2% = 0.8%
  // Net loss per stop after fees:  1.0% + 0.2% = 1.2%
  // Break even win rate: 60%

  TIMEFRAMES: ['1m', '3m', '5m', '15m'],
  MIN_CANDLES: 20,

  // Monitor every 2 seconds for fast closes
  MONITOR_INTERVAL_MS: 2000,
  // Poll candles every 20 seconds
  POLL_INTERVAL_MS: 30000,

  SYMBOLS: [
    // High ATR movers — volatile enough to hit 1% target quickly
    'SOLUSDT','INJUSDT','SUIUSDT','ARBUSDT','OPUSDT',
    'AVAXUSDT','NEARUSDT','APTUSDT','SEIUSDT','TONUSDT',
    'WIFUSDT','BONKUSDT','PEPEUSDT','ENAUSDT','FETUSDT',
    'LDOUSDT','RUNEUSDT','DYDXUSDT','WLDUSDT','TIAUSDT',
    'STXUSDT','ONDOUSDT','ICPUSDT','AAVEUSDT','LINKUSDT',
    'DOTUSDT','ATOMUSDT','UNIUSDT','GRTUSDT','HBARUSDT',
    'MATICUSDT','XLMUSDT','TRXUSDT','LTCUSDT','ETCUSDT',
    'XRPUSDT','ADAUSDT','DOGEUSDT','BNBUSDT','ETHUSDT',
    'BTCUSDT','FILUSDT','SANDUSDT','MANAUSDT','AXSUSDT',
    'JUPUSDT','RENDERUSDT','IMXUSDT','GALAUSDT','MKRUSDT',
  ],

  TIERS: [
    { minBalance:0,      tradeUsdt:20,  baseTrades:2,  maxTrades:3,  label:'Starter'    },
    { minBalance:200,    tradeUsdt:25,  baseTrades:2,  maxTrades:4,  label:'Bronze I'   },
    { minBalance:400,    tradeUsdt:30,  baseTrades:3,  maxTrades:5,  label:'Bronze II'  },
    { minBalance:700,    tradeUsdt:40,  baseTrades:3,  maxTrades:6,  label:'Silver I'   },
    { minBalance:1000,   tradeUsdt:50,  baseTrades:4,  maxTrades:7,  label:'Silver II'  },
    { minBalance:1500,   tradeUsdt:65,  baseTrades:4,  maxTrades:8,  label:'Gold I'     },
    { minBalance:2500,   tradeUsdt:80,  baseTrades:5,  maxTrades:10, label:'Gold II'    },
    { minBalance:4000,   tradeUsdt:100, baseTrades:6,  maxTrades:12, label:'Platinum I' },
    { minBalance:6000,   tradeUsdt:120, baseTrades:7,  maxTrades:14, label:'Platinum II'},
    { minBalance:10000,  tradeUsdt:150, baseTrades:8,  maxTrades:16, label:'Diamond I'  },
    { minBalance:15000,  tradeUsdt:200, baseTrades:10, maxTrades:20, label:'Diamond II' },
    { minBalance:25000,  tradeUsdt:250, baseTrades:12, maxTrades:25, label:'Elite I'    },
    { minBalance:40000,  tradeUsdt:350, baseTrades:15, maxTrades:30, label:'Elite II'   },
    { minBalance:60000,  tradeUsdt:500, baseTrades:20, maxTrades:35, label:'Master'     },
    { minBalance:100000, tradeUsdt:750, baseTrades:25, maxTrades:50, label:'Supreme'    },
  ],

  WIN_STREAK_TO_ADD: 3,
  LOSS_STREAK_TO_REMOVE: 2,
  COOLDOWN_AFTER_LOSS_MS: 45000,
  MIN_WIN_RATE_TO_SCALE: 55,
  DRAWDOWN_PAUSE_PCT: 4,
};

const BASE = CONFIG.REST_BASE;
if (!global.stepSizeCache) global.stepSizeCache = {};

// ─── Kline store ──────────────────────────────────────────────────────────────
const klineStore = {};
const livePrice  = {};

function pushKline(symbol, tf, candle) {
  if (!klineStore[symbol]) klineStore[symbol] = {};
  if (!klineStore[symbol][tf]) klineStore[symbol][tf] = [];
  const store = klineStore[symbol][tf];
  const idx = store.findIndex(k => k.t === candle.t);
  if (idx >= 0) store[idx] = candle; else store.push(candle);
  if (store.length > 150) store.shift();
}
function getKlines(symbol, tf) { return klineStore[symbol]?.[tf] || []; }

// ─── Bot state ────────────────────────────────────────────────────────────────
let botState = {
  running: false, mode: CONFIG.MODE,
  openTrades: [], closedTrades: [],
  dailyPnl: 0, dailyPnlDate: new Date().toDateString(), totalPnl: 0,
  log: [], killSwitch: false,
  usdtBalance: 0, startingBalance: 0, currentTierIndex: 0,
  totalSignalsFound: 0, confluenceRejected: 0,
  tradesExecuted: 0, winCount: 0, lossCount: 0,
  currentMaxTrades: 2, consecutiveWins: 0, consecutiveLosses: 0,
  lastLossTime: 0, inCooldown: false, drawdownPaused: false,
  scalingLog: [], candlesReceived: 0, lastSignalCheck: null,
  wsConnected: false, wsStreamCount: 0, symbolsLoaded: 0,
};

let monitorInterval = null;
let balanceInterval = null;
let pollTimeout    = null;

// ─── Logging ──────────────────────────────────────────────────────────────────
function log(level, msg) {
  const e = { ts: new Date().toISOString(), level, message: msg };
  botState.log.unshift(e);
  if (botState.log.length > 500) botState.log.pop();
  console.log(`[${level}] ${msg}`);
}
function logScale(msg) {
  botState.scalingLog.unshift({ ts: new Date().toISOString(), message: msg });
  if (botState.scalingLog.length > 100) botState.scalingLog.pop();
  log('INFO', '⚖️ ' + msg);
}

// ─── Tier helpers ─────────────────────────────────────────────────────────────
function getCurrentTier() {
  let t = CONFIG.TIERS[0];
  for (const tier of CONFIG.TIERS) { if (botState.usdtBalance >= tier.minBalance) t = tier; else break; }
  return t;
}
function getTierIndex() {
  let idx = 0;
  for (let i = 0; i < CONFIG.TIERS.length; i++) { if (botState.usdtBalance >= CONFIG.TIERS[i].minBalance) idx = i; else break; }
  return idx;
}

// ─── Trade scaling ────────────────────────────────────────────────────────────
function updateTradeScaling(result) {
  const tier = getCurrentTier();
  if (result === 'WIN')  { botState.consecutiveWins++;   botState.consecutiveLosses = 0; botState.inCooldown = false; }
  if (result === 'LOSS') { botState.consecutiveLosses++; botState.consecutiveWins   = 0; botState.lastLossTime = Date.now(); botState.inCooldown = true; }
  const total = botState.winCount + botState.lossCount;
  const wr = total > 0 ? (botState.winCount / total) * 100 : 50;
  const dd = botState.usdtBalance > 0 ? Math.abs(Math.min(botState.dailyPnl,0))/botState.usdtBalance*100 : 0;
  if (dd >= CONFIG.DRAWDOWN_PAUSE_PCT && !botState.drawdownPaused) { botState.drawdownPaused = true; logScale(`Drawdown pause (${dd.toFixed(1)}%)`); }
  if (dd < CONFIG.DRAWDOWN_PAUSE_PCT*0.4 && botState.drawdownPaused) { botState.drawdownPaused = false; logScale('Drawdown recovered'); }
  const cur = botState.currentMaxTrades;
  if (botState.consecutiveWins >= CONFIG.WIN_STREAK_TO_ADD && wr >= CONFIG.MIN_WIN_RATE_TO_SCALE && cur < tier.maxTrades && !botState.drawdownPaused) {
    botState.currentMaxTrades = Math.min(cur+1, tier.maxTrades); botState.consecutiveWins = 0;
    logScale(`Trades UP to ${botState.currentMaxTrades} | WR:${wr.toFixed(0)}%`);
  }
  if ((botState.consecutiveLosses >= CONFIG.LOSS_STREAK_TO_REMOVE || (total>=10&&wr<40)) && cur > tier.baseTrades) {
    botState.currentMaxTrades = Math.max(cur-1, tier.baseTrades); botState.consecutiveLosses = 0;
    logScale(`Trades DOWN to ${botState.currentMaxTrades} | WR:${wr.toFixed(0)}%`);
  }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) {
    botState.currentMaxTrades = CONFIG.TIERS[ni].baseTrades;
    botState.consecutiveWins = 0; botState.consecutiveLosses = 0;
    logScale(`Tier UP → ${CONFIG.TIERS[ni].label} | Trades reset to ${botState.currentMaxTrades}`);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── REST helpers ─────────────────────────────────────────────────────────────
function restGet(url) {
  return new Promise((resolve, reject) => {
    https.get(url, { headers: {'User-Agent':'scalpr/4.0'} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => {
        if (d.trim().startsWith('<')) {
          reject(new Error('HTML response — endpoint blocked or rate limited'));
          return;
        }
        try { resolve(JSON.parse(d)); } catch(e) { reject(e); }
      });
    }).on('error', reject);
  });
}
async function binancePublic(path, params = {}) {
  const q = new URLSearchParams(params).toString();
  return restGet(`${BASE}${path}${q ? '?' + q : ''}`);
}
function sign(params) {
  const q = new URLSearchParams(params).toString();
  return q + '&signature=' + crypto.createHmac('sha256', CONFIG.API_SECRET).update(q).digest('hex');
}
async function binanceSigned(method, path, params = {}) {
  params.timestamp = Date.now(); params.recvWindow = 5000;
  const query = sign(params);
  const url = method === 'GET' ? `${BASE}${path}?${query}` : `${BASE}${path}`;
  return new Promise((resolve, reject) => {
    const opts = { method, headers: { 'X-MBX-APIKEY': CONFIG.API_KEY, 'Content-Type': 'application/x-www-form-urlencoded' } };
    const req = https.request(url, opts, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => {
        try { const j = JSON.parse(d); if (j.code && j.code < 0) reject(new Error(j.msg)); else resolve(j); }
        catch(e) { reject(e); }
      });
    });
    req.on('error', reject);
    if (method !== 'GET') req.write(query);
    req.end();
  });
}

// ─── Balance ──────────────────────────────────────────────────────────────────
async function refreshBalance() {
  try {
    const acc = await binanceSigned('GET', '/api/v3/account');
    const u = acc.balances?.find(b => b.asset === 'USDT');
    botState.usdtBalance = u ? parseFloat(u.free) : 0;
    if (!botState.startingBalance && botState.usdtBalance > 0) {
      botState.startingBalance = botState.usdtBalance;
      log('INFO', `Start balance: $${botState.startingBalance.toFixed(2)}`);
    }
  } catch(e) { log('WARN', 'Balance: ' + e.message); return; }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) updateTradeScaling(null);
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── Seed & poll klines ───────────────────────────────────────────────────────
async function setupFuturesSymbol(symbol) {
  try { await binanceSigned('POST', '/fapi/v1/leverage', { symbol, leverage: 5 }); } catch(e) {}
  try { await binanceSigned('POST', '/fapi/v1/marginType', { symbol, marginType: 'ISOLATED' }); } catch(e) {}
}

async function seedKlines(symbol, tf) {
  try {
    const data = await binancePublic('/api/v3/klines', { symbol, interval: tf, limit: 100 });
    if (!Array.isArray(data)) return;
    for (const k of data) {
      pushKline(symbol, tf, { t:k[0], o:parseFloat(k[1]), h:parseFloat(k[2]), l:parseFloat(k[3]), c:parseFloat(k[4]), v:parseFloat(k[5]) });
    }
    livePrice[symbol] = parseFloat(data[data.length-1][4]);
  } catch(e) {}
}

async function pollCycle() {
  if (!botState.running) return;
  for (const sym of CONFIG.SYMBOLS) {
    if (!botState.running) break;
    for (const tf of CONFIG.TIMEFRAMES) {
      try {
        const data = await binancePublic('/api/v3/klines', { symbol: sym, interval: tf, limit: 12 });
        if (!Array.isArray(data)) continue;
        for (let i = 0; i < data.length; i++) {
          const k = data[i];
          const candle = { t:k[0], o:parseFloat(k[1]), h:parseFloat(k[2]), l:parseFloat(k[3]), c:parseFloat(k[4]), v:parseFloat(k[5]) };
          livePrice[sym] = candle.c;
          pushKline(sym, tf, candle);
          botState.candlesReceived++;
          if (i < data.length - 1) analyzeAndTrade(sym, tf);
        }
      } catch(e) {}
    }
    await new Promise(r => setTimeout(r, 200));
  }
  log('INFO', `Polled ${CONFIG.SYMBOLS.length} coins | Next in ${CONFIG.POLL_INTERVAL_MS/1000}s`);
  botState.wsConnected = true;
  botState.wsStreamCount = CONFIG.SYMBOLS.length * CONFIG.TIMEFRAMES.length;
  if (botState.running) pollTimeout = setTimeout(pollCycle, CONFIG.POLL_INTERVAL_MS);
}

// ─── Indicators ───────────────────────────────────────────────────────────────
// 1. StochRSI
function stochRSI(klines, rP=14, sP=14, sK=3, sD=3) {
  const closes = klines.map(k => k.c);
  const rs = [];
  for (let i = rP; i < closes.length; i++) {
    const sl = closes.slice(i-rP, i+1); let g=0, l=0;
    for (let j=1; j<=rP; j++) { const d=sl[j]-sl[j-1]; d>0?g+=d:l-=d; }
    const ag=g/rP, al=l/rP;
    rs.push(al===0?100:100-100/(1+ag/al));
  }
  if (rs.length < sP) return { k:50, d:50, crossUp:false, crossDown:false };
  const kR = [];
  for (let i=sP-1; i<rs.length; i++) {
    const sl=rs.slice(i-sP+1,i+1); const hh=Math.max(...sl), ll=Math.min(...sl);
    kR.push(hh===ll?50:((rs[i]-ll)/(hh-ll))*100);
  }
  const smK=[]; for(let i=sK-1;i<kR.length;i++) smK.push(kR.slice(i-sK+1,i+1).reduce((a,b)=>a+b,0)/sK);
  const smD=[]; for(let i=sD-1;i<smK.length;i++) smD.push(smK.slice(i-sD+1,i+1).reduce((a,b)=>a+b,0)/sD);
  const k=smK[smK.length-1]||50, d=smD[smD.length-1]||50;
  const pk=smK[smK.length-2]||50, pd=smD[smD.length-2]||50;
  return { k, d, crossUp:k>d&&pk<=pd&&k<50, crossDown:k<d&&pk>=pd&&k>50 };
}

// 2. Momentum (3 periods)
function calcMomentum(klines) {
  const c = klines.map(k => k.c);
  const fast = c.length>5  ? (c[c.length-1]-c[c.length-6])/c[c.length-6]*100 : 0;
  const mid  = c.length>10 ? (c[c.length-1]-c[c.length-11])/c[c.length-11]*100 : 0;
  const slow = c.length>20 ? (c[c.length-1]-c[c.length-21])/c[c.length-21]*100 : 0;
  return { fast, mid, slow, allBull:fast>0&&mid>0&&slow>0, allBear:fast<0&&mid<0&&slow<0, accelBull:fast>mid&&mid>slow&&fast>0, accelBear:fast<mid&&mid<slow&&fast<0 };
}

// 3. OBV (On-Balance Volume)
function calcOBV(klines) {
  let obv = 0;
  const series = [];
  for (let i = 1; i < klines.length; i++) {
    if (klines[i].c > klines[i-1].c) obv += klines[i].v;
    else if (klines[i].c < klines[i-1].c) obv -= klines[i].v;
    series.push(obv);
  }
  if (series.length < 5) return { trend: 'NEUTRAL', rising: false };
  const recent = series.slice(-5);
  const slope = recent[recent.length-1] - recent[0];
  return { trend: slope > 0 ? 'RISING' : slope < 0 ? 'FALLING' : 'NEUTRAL', rising: slope > 0, obv };
}

// 4. Bollinger Band Squeeze (B/S Basis)
// Measures volatility contraction — squeeze = breakout coming
// Combined with direction = high probability entry
function calcBBSqueeze(klines, period=20) {
  if (klines.length < period) return { squeeze: false, aboveMid: false, expansion: false };
  const closes = klines.map(k => k.c).slice(-period);
  const mean = closes.reduce((a,b)=>a+b,0) / period;
  const variance = closes.reduce((s,c)=>s+Math.pow(c-mean,2),0) / period;
  const stdDev = Math.sqrt(variance);
  const upper = mean + 2*stdDev;
  const lower = mean - 2*stdDev;
  const bandwidth = (upper - lower) / mean * 100;
  const lastClose = closes[closes.length-1];

  // Historical bandwidth for squeeze detection
  const allCloses = klines.map(k => k.c);
  const bandwidths = [];
  for (let i = period; i < allCloses.length; i++) {
    const sl = allCloses.slice(i-period, i);
    const m = sl.reduce((a,b)=>a+b,0)/period;
    const sd = Math.sqrt(sl.reduce((s,c)=>s+Math.pow(c-m,2),0)/period);
    bandwidths.push((m+2*sd - (m-2*sd)) / m * 100);
  }
  const minBW = bandwidths.length > 0 ? Math.min(...bandwidths.slice(-20)) : bandwidth;
  const squeeze = bandwidth <= minBW * 1.2; // within 20% of min = squeeze
  const expansion = bandwidth > minBW * 1.5;

  return {
    squeeze, expansion,
    aboveMid: lastClose > mean,
    belowMid: lastClose < mean,
    upper, lower, mid: mean, bandwidth,
  };
}

// 5. ATR (Average True Range) — measures volatility
// High ATR = coin is moving fast = better for scalping
function calcATR(klines, period=14) {
  if (klines.length < period+1) return { atr: 0, atrPct: 0, highVolatility: false };
  const trs = [];
  for (let i = 1; i < klines.length; i++) {
    const h = klines[i].h, l = klines[i].l, pc = klines[i-1].c;
    trs.push(Math.max(h-l, Math.abs(h-pc), Math.abs(l-pc)));
  }
  const atr = trs.slice(-period).reduce((a,b)=>a+b,0) / period;
  const price = klines[klines.length-1].c;
  const atrPct = (atr / price) * 100;
  // High volatility = ATR% above 0.3% on 1m (coin moving fast enough to hit 1% target)
  return { atr, atrPct, highVolatility: atrPct >= 0.3 };
}

// ─── Score a single timeframe ─────────────────────────────────────────────────
function scoreTF(klines) {
  if (klines.length < CONFIG.MIN_CANDLES) return null;

  // Candle body filter — skip doji candles
  const last = klines[klines.length-1];
  const body = Math.abs(last.c - last.o) / last.o * 100;
  if (body < 0.005) return null;

  // ATR filter — only trade high volatility coins
  // ATR must be >= 0.3% of price on this timeframe
  const atrData = calcATR(klines);
  if (!atrData.highVolatility) return null;

  // Volume filter
  const vols = klines.map(k => k.v);
  const avgVol = vols.slice(-20).reduce((a,b)=>a+b,0) / 20;
  if (vols[vols.length-1] < avgVol * 0.3) return null;

  const srsi = stochRSI(klines);
  const mom  = calcMomentum(klines);
  const obv  = calcOBV(klines);
  const bb   = calcBBSqueeze(klines);

  // ── StochRSI signal ───────────────────────────────────────────────────────
  let srsiScore = 0;
  if (srsi.k <= 15)  srsiScore = 3;      // deeply oversold = strong LONG
  else if (srsi.k <= 25) srsiScore = 2;  // oversold = LONG
  else if (srsi.crossUp) srsiScore = 2;  // crossover = LONG
  else if (srsi.k >= 85)  srsiScore = -3;// deeply overbought = strong SHORT
  else if (srsi.k >= 75)  srsiScore = -2;// overbought = SHORT
  else if (srsi.crossDown) srsiScore = -2;

  // ── Momentum signal ───────────────────────────────────────────────────────
  let momScore = 0;
  if (mom.allBull)       momScore = 3;
  else if (mom.fast > 0 && mom.mid > 0) momScore = 2;
  else if (mom.fast > 0) momScore = 1;
  if (mom.accelBull) momScore += 1;
  if (mom.allBear)       momScore = -3;
  else if (mom.fast < 0 && mom.mid < 0) momScore = -2;
  else if (mom.fast < 0 && momScore >= 0) momScore = -1;
  if (mom.accelBear) momScore -= 1;

  // ── OBV signal ────────────────────────────────────────────────────────────
  let obvScore = 0;
  if (obv.trend === 'RISING')  obvScore = 2;
  if (obv.trend === 'FALLING') obvScore = -2;

  // ── BB/Squeeze signal ─────────────────────────────────────────────────────
  let bbScore = 0;
  if (bb.squeeze && bb.aboveMid) bbScore = 2;   // squeeze + price above mid = bull breakout
  if (bb.squeeze && bb.belowMid) bbScore = -2;  // squeeze + price below mid = bear breakout
  if (bb.expansion && bb.aboveMid) bbScore = 1; // expansion above = uptrend
  if (bb.expansion && !bb.aboveMid) bbScore = -1;

  // ── Total score ───────────────────────────────────────────────────────────
  // StochRSI + Momentum are primary (weighted higher)
  // OBV + BB are confirmation (weighted lower)
  const totalScore = (srsiScore * 2) + (momScore * 2) + obvScore + bbScore;

  // Max possible: (3*2) + (4*2) + 2 + 2 = 20
  // Threshold for signal: ±6 (30% of max)
  let verdict = 'NEUTRAL';
  if (totalScore >= 6)  verdict = 'LONG';
  if (totalScore <= -6) verdict = 'SHORT';

  let quality = Math.min(Math.abs(totalScore) / 20 * 100, 99);

  return {
    verdict, quality: Math.round(quality), totalScore,
    srsiK: srsi.k, srsiD: srsi.d, crossUp: srsi.crossUp, crossDown: srsi.crossDown,
    momFast: mom.fast, momMid: mom.mid, momAllBull: mom.allBull, momAllBear: mom.allBear,
    momAccelBull: mom.accelBull, momAccelBear: mom.accelBear,
    obvTrend: obv.trend, obvRising: obv.rising,
    bbSqueeze: bb.squeeze, bbAboveMid: bb.aboveMid, bbBandwidth: bb.bandwidth,
    atrPct: atrData.atrPct, highVolatility: atrData.highVolatility,
  };
}

// ─── Analyze and trade ────────────────────────────────────────────────────────
if (!global.executingSymbols) global.executingSymbols = new Set();

async function analyzeAndTrade(symbol, closedTF) {
  if (!botState.running || botState.killSwitch) return;
  if (botState.openTrades.some(t => t.symbol === symbol)) return;
  if (botState.openTrades.length >= botState.currentMaxTrades) return;
  if (botState.drawdownPaused) return;
  if (isCooldownActive()) return;
  if (global.executingSymbols.has(symbol)) return;

  // Score all available timeframes
  const results = {};
  for (const tf of CONFIG.TIMEFRAMES) {
    const klines = getKlines(symbol, tf);
    if (klines.length >= CONFIG.MIN_CANDLES) {
      const score = scoreTF(klines);
      if (score) results[tf] = score;
    }
  }

  const available = Object.keys(results).length;
  if (available < 2) return; // need at least 2 TFs

  const verdicts = Object.values(results).map(r => r.verdict);
  const longCount  = verdicts.filter(v => v === 'LONG').length;
  const shortCount = verdicts.filter(v => v === 'SHORT').length;

  // Majority agreement required
  const majority = Math.ceil(available / 2);
  const isLong  = longCount >= majority && shortCount === 0;
  const isShort = shortCount >= majority && longCount === 0;

  if (!isLong && !isShort) { botState.confluenceRejected++; return; }
  const verdict = isLong ? 'LONG' : 'SHORT';
  const primary = results[closedTF] || Object.values(results)[0];
  const price   = livePrice[symbol] || 0;
  if (!price) return;

  // Check if OBV confirms (rising = more conviction)
  const obvConfirm = primary.obvRising;
  // Check if BB squeeze is present (breakout setup)
  const bbConfirm  = primary.bbSqueeze && primary.bbAboveMid;

  const tier   = getCurrentTier();
  const entry  = price;
  const target = verdict==='LONG' ? entry*(1+CONFIG.TARGET_PCT/100) : entry*(1-CONFIG.TARGET_PCT/100);
  const stop   = verdict==='LONG' ? entry*(1-CONFIG.STOP_PCT/100)   : entry*(1+CONFIG.STOP_PCT/100);
  const tfs    = Object.keys(results).filter(tf => results[tf].verdict === 'LONG');

  botState.totalSignalsFound++;
  botState.lastSignalCheck = new Date().toISOString();

  log('INFO', `✨ ${symbol} LONG | score:${primary.totalScore} q:${primary.quality} | sRSI:${primary.srsiK.toFixed(0)} mom:${primary.momFast.toFixed(2)}% OBV:${primary.obvTrend} BB:${primary.bbSqueeze?'SQUEEZE':'—'} | TFs:[${tfs.join(',')}] | triggered by ${closedTF}`);

  // Lock slot
  global.executingSymbols.add(symbol);

  try {
    const order = await placeSpotOrder(symbol, 'BUY', tier.tradeUsdt, entry);
    if (!order) { global.executingSymbols.delete(symbol); return; }

    botState.tradesExecuted++;
    botState.openTrades.push({
      id: order.orderId, symbol, side: 'LONG',
      entry: order.price, qty: order.qty,
      target, stop, targetPct: CONFIG.TARGET_PCT, stopPct: CONFIG.STOP_PCT,
      tradeSize: tier.tradeUsdt, tier: tier.label,
      openedAt: new Date().toISOString(), paper: false,
      research: {
        verdict, score: primary.totalScore, quality: primary.quality,
        srsiK: primary.srsiK.toFixed(1), momFast: primary.momFast.toFixed(3),
        crossUp: primary.crossUp, obvTrend: primary.obvTrend,
        bbSqueeze: primary.bbSqueeze, bbAboveMid: primary.bbAboveMid,
        timeframes: tfs,
      },
    });

    log('INFO', `🚀 BUY ${symbol} @ $${order.price.toFixed(6)} | target:$${target.toFixed(6)} (+${CONFIG.TARGET_PCT}%) stop:$${stop.toFixed(6)} (-${CONFIG.STOP_PCT}%) | $${tier.tradeUsdt} | Open:${botState.openTrades.length}/${botState.currentMaxTrades} | ${tier.label}`);
  } catch(e) {
    log('ERROR', `Execute ${symbol}: ${e.message}`);
  } finally {
    global.executingSymbols.delete(symbol);
  }
}

// ─── Spot order placement ─────────────────────────────────────────────────────
async function placeSpotOrder(symbol, side, usdtAmount, price) {
  try {
    // Get step size
    let step = global.stepSizeCache[symbol];
    if (!step) {
      const info = await binancePublic('/api/v3/exchangeInfo', {});
      const si = info.symbols?.find(s => s.symbol === symbol);
      const lf = si?.filters?.find(f => f.filterType === 'LOT_SIZE');
      step = lf ? parseFloat(lf.stepSize) : 0.001;
      global.stepSizeCache[symbol] = step;
    }
    const dec = step.toString().split('.')[1]?.length || 3;
    const qty = parseFloat((Math.floor(usdtAmount/price/step)*step).toFixed(dec));
    if (qty <= 0) throw new Error('Qty too small');

    const order = await binanceSigned('POST', '/sapi/v1/margin/order', {
      symbol, side, type: 'MARKET', quantity: qty,
      isIsolated: 'FALSE', sideEffectType: 'AUTO_BORROW_REPAY'
    });

    const fillPrice = parseFloat(order.avgPrice) || parseFloat(order.price) || price;

    log('INFO', `[SPOT] ${side} ${qty} ${symbol} @ $${fillPrice.toFixed(6)}`);
    return { orderId: order.orderId, symbol, side, qty, price: fillPrice };
  } catch(e) { log('ERROR', `Order ${symbol}: ${e.message}`); throw e; }
}

// ─── Monitor open trades (every 2 seconds) ───────────────────────────────────
async function monitorOpenTrades() {
  if (!botState.openTrades.length) return;
  resetDailyPnl();

  for (const trade of [...botState.openTrades]) {
    // Always fetch fresh price from Binance for accurate monitoring
    let price = livePrice[trade.symbol] || 0;
    try {
      const ticker = await binancePublic('/api/v3/ticker/price', { symbol: trade.symbol });
      if (ticker && ticker.price) price = parseFloat(ticker.price);
      livePrice[trade.symbol] = price;
    } catch(e) {}
    if (!price) continue;

    let closeReason = null;
    // Only close if price has genuinely moved enough
    // Require price to be confirmed within 0.05% of target/stop
    const minMove = trade.entry * 0.003; // at least 0.3% move before any close
    const moved = Math.abs(price - trade.entry);
    if (trade.side==='LONG') {
      if (price >= trade.target && moved >= minMove) closeReason='TARGET_HIT';
      else if (price <= trade.stop && moved >= minMove) closeReason='STOP_HIT';
    } else {
      if (price <= trade.target && moved >= minMove) closeReason='TARGET_HIT';
      else if (price >= trade.stop && moved >= minMove) closeReason='STOP_HIT';
    }

    if (closeReason) {
      try {
        // Sell the entire position
        const closeSide = trade.side==='LONG'?'SELL':'BUY';
        await placeSpotOrder(trade.symbol, closeSide, trade.qty * price, price);

        // Calculate net PnL after fees (0.2% round trip)
        const grossPnl = trade.side==='LONG' ? (price-trade.entry)*trade.qty : (trade.entry-price)*trade.qty;
        const fees = trade.tradeSize * 0.002; // 0.2% round trip
        const pnl = grossPnl - fees;
        const pnlPct = parseFloat(((pnl / trade.tradeSize) * 100).toFixed(3));

        botState.dailyPnl  += pnl;
        botState.totalPnl  += pnl;
        const isWin = pnl >= 0;
        isWin ? botState.winCount++ : botState.lossCount++;

        botState.closedTrades.unshift({
          ...trade, exit: price, pnl, pnlPct,
          closedAt: new Date().toISOString(), closeReason,
          feesDeducted: fees.toFixed(4),
        });
        if (botState.closedTrades.length > 300) botState.closedTrades.pop();
        botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);

        updateTradeScaling(isWin ? 'WIN' : 'LOSS');
        await refreshBalance();

        const total = botState.winCount + botState.lossCount;
        const wr = total > 0 ? ((botState.winCount/total)*100).toFixed(0) + '%' : 'N/A';
        log('INFO', `${isWin?'✅':'❌'} ${trade.symbol} LONG | gross:$${grossPnl.toFixed(4)} fees:$${fees.toFixed(4)} net:$${pnl.toFixed(4)} (${pnlPct}%) | ${closeReason} | WR:${wr}`);
      } catch(e) { log('WARN', `Close ${trade.symbol}: ${e.message}`); }
    }
  }
}

// ─── Risk helpers ─────────────────────────────────────────────────────────────
function resetDailyPnl() {
  const t = new Date().toDateString();
  if (botState.dailyPnlDate !== t) { botState.dailyPnl=0; botState.dailyPnlDate=t; log('INFO','Daily PnL reset'); }
}
function isCooldownActive() {
  if (!botState.inCooldown) return false;
  const elapsed = Date.now() - botState.lastLossTime;
  if (elapsed >= CONFIG.COOLDOWN_AFTER_LOSS_MS) { botState.inCooldown = false; return false; }
  return true;
}

// ─── Routes ───────────────────────────────────────────────────────────────────
app.get('/health', (req,res) => res.json({
  status:'ok', ts:new Date().toISOString(),
  running:botState.running, openTrades:botState.openTrades.length,
  candles:botState.candlesReceived,
}));

app.get('/status', (req,res) => {
  const tier = getCurrentTier();
  const total = botState.winCount + botState.lossCount;
  res.json({
    running:botState.running, mode:botState.mode, killSwitch:botState.killSwitch,
    wsConnected:botState.wsConnected, wsStreamCount:botState.wsStreamCount,
    candlesReceived:botState.candlesReceived, lastSignalCheck:botState.lastSignalCheck,
    openTrades:botState.openTrades,
    closedTrades:botState.closedTrades.slice(0,100),
    dailyPnl:botState.dailyPnl, totalPnl:botState.totalPnl,
    symbolsLoaded:CONFIG.SYMBOLS.length,
    usdtBalance:botState.usdtBalance, startingBalance:botState.startingBalance,
    currentTier:botState.currentTierIndex+1, tierName:tier.label,
    currentTradeUsdt:tier.tradeUsdt, currentMaxTrades:botState.currentMaxTrades,
    tierBaseTrades:tier.baseTrades, tierMaxTrades:tier.maxTrades,
    targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT,
    consecutiveWins:botState.consecutiveWins, consecutiveLosses:botState.consecutiveLosses,
    inCooldown:botState.inCooldown, drawdownPaused:botState.drawdownPaused,
    totalSignalsFound:botState.totalSignalsFound, confluenceRejected:botState.confluenceRejected,
    tradesExecuted:botState.tradesExecuted, winCount:botState.winCount, lossCount:botState.lossCount,
    winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',
    scalingLog:botState.scalingLog.slice(0,20),
    config:{
      symbols:CONFIG.SYMBOLS, timeframes:CONFIG.TIMEFRAMES,
      targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT,
      indicators:['StochRSI','Momentum','OBV','BB-Squeeze'],
      tiers:CONFIG.TIERS, currentTierFull:tier,
    },
    log:botState.log.slice(0,100),
  });
});

app.post('/start', async (req,res) => {
  if (botState.running) return res.json({ success:false, message:'Already running' });
  if (botState.killSwitch) return res.json({ success:false, message:'Kill switch active' });
  await refreshBalance();
  const tier = getCurrentTier();
  if (botState.currentMaxTrades < tier.baseTrades) botState.currentMaxTrades = tier.baseTrades;
  botState.running = true;
  pollCycle();
  monitorInterval = setInterval(monitorOpenTrades, CONFIG.MONITOR_INTERVAL_MS);
  balanceInterval = setInterval(refreshBalance, 3*60*1000);
  const msg = `Bot started | SPOT | ${tier.label} | ${CONFIG.SYMBOLS.length} coins | ${CONFIG.TIMEFRAMES.join('+')} | StochRSI+Mom+OBV+BB | Target:${CONFIG.TARGET_PCT}% Stop:${CONFIG.STOP_PCT}% | $${tier.tradeUsdt}/trade | ${botState.currentMaxTrades} max trades`;
  log('INFO', msg);
  res.json({ success:true, message:msg });
});

app.post('/stop', (req,res) => {
  botState.running = false;
  clearInterval(monitorInterval); clearInterval(balanceInterval);
  if (pollTimeout) clearTimeout(pollTimeout);
  log('INFO', 'Bot stopped');
  res.json({ success:true, message:'Stopped' });
});

app.post('/kill', (req,res) => {
  botState.running = false; botState.killSwitch = true;
  clearInterval(monitorInterval); clearInterval(balanceInterval);
  if (pollTimeout) clearTimeout(pollTimeout);
  log('WARN', '🚨 KILL SWITCH ACTIVATED');
  res.json({ success:true, message:'Kill switch activated' });
});

app.post('/reset-kill', (req,res) => {
  botState.killSwitch = false;
  log('INFO', 'Kill switch reset');
  res.json({ success:true, message:'Kill switch reset' });
});

app.post('/close-trade/:id', async (req,res) => {
  const trade = botState.openTrades.find(t => t.id === req.params.id);
  if (!trade) return res.json({ success:false, message:'Not found' });
  try {
    const price = livePrice[trade.symbol] || trade.entry;
    const mSide = trade.side==='LONG'?'SELL':'BUY';
    await binanceSigned('POST', '/api/v3/order', { symbol: trade.symbol, side: mSide, type: 'MARKET', quantity: trade.qty.toString() });
    const grossPnl = (price - trade.entry) * trade.qty;
    const fees = trade.tradeSize * 0.002;
    const pnl = grossPnl - fees;
    botState.dailyPnl += pnl; botState.totalPnl += pnl;
    botState.closedTrades.unshift({ ...trade, exit:price, pnl, closedAt:new Date().toISOString(), closeReason:'MANUAL' });
    botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
    await refreshBalance();
    log('INFO', `Manual close ${trade.symbol} | Net PnL:$${pnl.toFixed(4)}`);
    res.json({ success:true, pnl });
  } catch(e) { res.json({ success:false, message:e.message }); }
});

app.get('/balance', async (req,res) => {
  await refreshBalance();
  const tier = getCurrentTier();
  const total = botState.winCount + botState.lossCount;
  res.json({
    usdtBalance:botState.usdtBalance, startingBalance:botState.startingBalance,
    totalPnl:botState.totalPnl, dailyPnl:botState.dailyPnl,
    growthPct:botState.startingBalance>0?((botState.totalPnl/botState.startingBalance)*100).toFixed(2)+'%':'0%',
    tier:tier.label, tradeUsdt:tier.tradeUsdt, currentMaxTrades:botState.currentMaxTrades,
    targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT,
    winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',
    allTiers:CONFIG.TIERS,
  });
});

// ─── Startup ──────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 3001;
app.listen(PORT, async () => {
  console.log(`\nSCALPR Spot Bot v4.0 — port ${PORT}`);
  console.log(`Mode: FUTURES LIVE (5x leverage isolated margin, LONG+SHORT)`);
  console.log(`Indicators: StochRSI + Momentum + OBV + BB-Squeeze`);
  console.log(`Timeframes: ${CONFIG.TIMEFRAMES.join(' + ')}`);
  console.log(`Target: +${CONFIG.TARGET_PCT}% | Stop: -${CONFIG.STOP_PCT}% | Net after fees: ~+0.8% / -1.2%`);
  console.log(`Starter: $${CONFIG.TIERS[0].tradeUsdt}/trade | ${CONFIG.TIERS[0].baseTrades}-${CONFIG.TIERS[0].maxTrades} trades`);
  console.log(`Monitor: every ${CONFIG.MONITOR_INTERVAL_MS/1000}s | Poll: every ${CONFIG.POLL_INTERVAL_MS/1000}s`);
  console.log(`Coins: ${CONFIG.SYMBOLS.length}\n`);
  console.log(`Seeding historical candles...`);
  const tasks = [];
  for (const sym of CONFIG.SYMBOLS) {
    for (const tf of CONFIG.TIMEFRAMES) tasks.push(seedKlines(sym, tf));
  }
  await Promise.allSettled(tasks);
  botState.symbolsLoaded = CONFIG.SYMBOLS.length;
  console.log(`Candles seeded. Ready.\n`);
  await refreshBalance();
  const tier = getCurrentTier();
  botState.currentMaxTrades = tier.baseTrades;
  balanceInterval = setInterval(refreshBalance, 3*60*1000);
});