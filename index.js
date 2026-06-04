const express = require('express');
const crypto = require('crypto');
const cors = require('cors');
const app = express();
app.use(cors());
app.use(express.json());

// ─── Config ───────────────────────────────────────────────────────────────────
const CONFIG = {
  API_KEY: process.env.BINANCE_API_KEY || '',
  API_SECRET: process.env.BINANCE_API_SECRET || '',
  PAPER_MODE: process.env.PAPER_MODE !== 'false',
  DAILY_LOSS_LIMIT_PCT: parseFloat(process.env.DAILY_LOSS_LIMIT_PCT || '5'),
  MAX_SYMBOLS: parseInt(process.env.MAX_SYMBOLS || '100'),
  MIN_VOLUME_USDT: parseFloat(process.env.MIN_VOLUME_USDT || '5000000'),
  SCAN_BATCH_SIZE: 8,
  SCAN_INTERVAL_MS: 4000,

  // ── Timeframes analyzed per coin ─────────────────────────────────────────
  // Each timeframe is scored independently.
  // A trade only executes when enough timeframes AGREE on the same direction.
  TIMEFRAMES: [
    { interval: '1m',  limit: 80,  weight: 1.0, label: '1min'  },
    { interval: '3m',  limit: 60,  weight: 1.5, label: '3min'  },
    { interval: '5m',  limit: 50,  weight: 2.0, label: '5min'  },
    { interval: '15m', limit: 40,  weight: 2.5, label: '15min' },
  ],
  // Minimum weighted confluence score to fire a trade (out of 7.0 max)
  // Higher = stricter. 5.0 means at least 3 timeframes must strongly agree.
  MIN_CONFLUENCE_SCORE: 5.0,
  // Minimum timeframes that must agree (same direction)
  MIN_AGREEING_TIMEFRAMES: 3,

  // ── Reinvestment Tiers ────────────────────────────────────────────────────
  TIERS: [
    { minBalance:0,     tradeUsdt:10,  baseTrades:2, maxTrades:3,  targetPct:0.25, stopPct:0.15, label:'Starter'  },
    { minBalance:100,   tradeUsdt:15,  baseTrades:2, maxTrades:4,  targetPct:0.28, stopPct:0.16, label:'Bronze'   },
    { minBalance:250,   tradeUsdt:20,  baseTrades:3, maxTrades:5,  targetPct:0.30, stopPct:0.17, label:'Silver'   },
    { minBalance:500,   tradeUsdt:30,  baseTrades:3, maxTrades:6,  targetPct:0.33, stopPct:0.18, label:'Gold'     },
    { minBalance:1000,  tradeUsdt:50,  baseTrades:4, maxTrades:7,  targetPct:0.36, stopPct:0.20, label:'Platinum' },
    { minBalance:2500,  tradeUsdt:75,  baseTrades:5, maxTrades:9,  targetPct:0.40, stopPct:0.22, label:'Diamond'  },
    { minBalance:5000,  tradeUsdt:100, baseTrades:6, maxTrades:12, targetPct:0.45, stopPct:0.25, label:'Elite'    },
    { minBalance:10000, tradeUsdt:150, baseTrades:7, maxTrades:15, targetPct:0.50, stopPct:0.28, label:'Master'   },
  ],

  // ── Dynamic Trade Scaling ─────────────────────────────────────────────────
  WIN_STREAK_TO_ADD: 3,
  LOSS_STREAK_TO_REMOVE: 2,
  COOLDOWN_AFTER_LOSS_MS: 90000,
  MIN_WIN_RATE_TO_SCALE: 55,
  DRAWDOWN_PAUSE_PCT: 3,
};

const BASE = 'https://api.binance.com';
let dynamicSymbols = [];
let currentBatchIndex = 0;
let signalCandidates = [];

let botState = {
  running: false,
  mode: CONFIG.PAPER_MODE ? 'PAPER' : 'LIVE',
  openTrades: [],
  closedTrades: [],
  dailyPnl: 0,
  dailyPnlDate: new Date().toDateString(),
  totalPnl: 0,
  scanCount: 0,
  cycleCount: 0,
  lastScan: null,
  log: [],
  killSwitch: false,
  symbolsLoaded: 0,
  currentBatch: [],
  usdtBalance: 0,
  startingBalance: 0,
  currentTierIndex: 0,
  totalSignalsFound: 0,
  mfiRejected: 0,
  confluenceRejected: 0,
  tradesExecuted: 0,
  winCount: 0,
  lossCount: 0,
  currentMaxTrades: 2,
  consecutiveWins: 0,
  consecutiveLosses: 0,
  lastLossTime: 0,
  inCooldown: false,
  drawdownPaused: false,
  scalingLog: [],
};

let scanInterval = null;
let symbolRefreshInterval = null;
let balanceRefreshInterval = null;

// ─── Logging ──────────────────────────────────────────────────────────────────
function log(level, message) {
  const entry = { ts: new Date().toISOString(), level, message };
  botState.log.unshift(entry);
  if (botState.log.length > 500) botState.log.pop();
  console.log(`[${level}] ${message}`);
}

function logScale(message) {
  botState.scalingLog.unshift({ ts: new Date().toISOString(), message });
  if (botState.scalingLog.length > 100) botState.scalingLog.pop();
  log('INFO', '⚖️ ' + message);
}

// ─── Tier Helpers ─────────────────────────────────────────────────────────────
function getCurrentTier() {
  let tier = CONFIG.TIERS[0];
  for (const t of CONFIG.TIERS) {
    if (botState.usdtBalance >= t.minBalance) tier = t;
    else break;
  }
  return tier;
}

function getTierIndex() {
  let idx = 0;
  for (let i = 0; i < CONFIG.TIERS.length; i++) {
    if (botState.usdtBalance >= CONFIG.TIERS[i].minBalance) idx = i;
    else break;
  }
  return idx;
}

// ─── Dynamic Trade Scaling ────────────────────────────────────────────────────
function updateTradeScaling(lastResult) {
  const tier = getCurrentTier();
  if (lastResult === 'WIN') {
    botState.consecutiveWins++;
    botState.consecutiveLosses = 0;
    botState.inCooldown = false;
  } else if (lastResult === 'LOSS') {
    botState.consecutiveLosses++;
    botState.consecutiveWins = 0;
    botState.lastLossTime = Date.now();
    botState.inCooldown = true;
  }
  const total = botState.winCount + botState.lossCount;
  const winRate = total > 0 ? (botState.winCount / total) * 100 : 50;
  const ddPct = botState.usdtBalance > 0
    ? Math.abs(Math.min(botState.dailyPnl, 0)) / botState.usdtBalance * 100 : 0;

  if (ddPct >= CONFIG.DRAWDOWN_PAUSE_PCT && !botState.drawdownPaused) {
    botState.drawdownPaused = true;
    logScale(`Drawdown pause ON (${ddPct.toFixed(2)}% daily loss)`);
  } else if (ddPct < CONFIG.DRAWDOWN_PAUSE_PCT * 0.5 && botState.drawdownPaused) {
    botState.drawdownPaused = false;
    logScale(`Drawdown recovered. Resuming.`);
  }

  const current = botState.currentMaxTrades;
  if (botState.consecutiveWins >= CONFIG.WIN_STREAK_TO_ADD
    && winRate >= CONFIG.MIN_WIN_RATE_TO_SCALE
    && current < tier.maxTrades && !botState.drawdownPaused) {
    botState.currentMaxTrades = Math.min(current + 1, tier.maxTrades);
    botState.consecutiveWins = 0;
    logScale(`Trades UP → ${botState.currentMaxTrades} | WR:${winRate.toFixed(1)}% | Tier max:${tier.maxTrades}`);
  }
  if ((botState.consecutiveLosses >= CONFIG.LOSS_STREAK_TO_REMOVE
    || (total >= 10 && winRate < 40)) && current > tier.baseTrades) {
    botState.currentMaxTrades = Math.max(current - 1, tier.baseTrades);
    botState.consecutiveLosses = 0;
    logScale(`Trades DOWN → ${botState.currentMaxTrades} | WR:${winRate.toFixed(1)}%`);
  }
  const newTierIdx = getTierIndex();
  if (newTierIdx > botState.currentTierIndex) {
    botState.currentMaxTrades = CONFIG.TIERS[newTierIdx].baseTrades;
    botState.consecutiveWins = 0;
    botState.consecutiveLosses = 0;
    logScale(`Tier → ${CONFIG.TIERS[newTierIdx].label}. Trades reset to ${botState.currentMaxTrades}`);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades) botState.currentMaxTrades = ct.maxTrades;
}

// ─── Binance HTTP ─────────────────────────────────────────────────────────────
async function binancePublic(path, params = {}) {
  const q = new URLSearchParams(params).toString();
  const res = await fetch(`${BASE}${path}${q?'?'+q:''}`);
  if (!res.ok) throw new Error(`HTTP ${res.status}`);
  return res.json();
}
function sign(params) {
  const q = new URLSearchParams(params).toString();
  return q + '&signature=' + crypto.createHmac('sha256', CONFIG.API_SECRET).update(q).digest('hex');
}
async function binanceSigned(method, path, params = {}) {
  params.timestamp = Date.now(); params.recvWindow = 5000;
  const query = sign(params);
  const url = method === 'GET' ? `${BASE}${path}?${query}` : `${BASE}${path}`;
  const opts = { method, headers: { 'X-MBX-APIKEY': CONFIG.API_KEY, 'Content-Type': 'application/x-www-form-urlencoded' } };
  if (method !== 'GET') opts.body = query;
  const res = await fetch(url, opts);
  const json = await res.json();
  if (json.code && json.code < 0) throw new Error(`Binance: ${json.msg}`);
  return json;
}

// ─── Balance & Symbol Management ──────────────────────────────────────────────
async function refreshBalance() {
  if (CONFIG.PAPER_MODE) {
    botState.usdtBalance = Math.max((botState.startingBalance || 100) + botState.totalPnl, 0);
    if (botState.startingBalance === 0) botState.startingBalance = 100;
  } else {
    try {
      const account = await binanceSigned('GET', '/api/v3/account');
      const usdt = account.balances?.find(b => b.asset === 'USDT');
      botState.usdtBalance = usdt ? parseFloat(usdt.free) : 0;
      if (botState.startingBalance === 0 && botState.usdtBalance > 0) {
        botState.startingBalance = botState.usdtBalance;
        log('INFO', `Starting balance: $${botState.startingBalance.toFixed(2)}`);
      }
    } catch(e) { log('WARN', 'Balance refresh failed: ' + e.message); return; }
  }
  const newIdx = getTierIndex();
  if (newIdx > botState.currentTierIndex) updateTradeScaling(null);
  botState.currentTierIndex = newIdx;
  const t = getCurrentTier();
  if (botState.currentMaxTrades < t.baseTrades) botState.currentMaxTrades = t.baseTrades;
  if (botState.currentMaxTrades > t.maxTrades) botState.currentMaxTrades = t.maxTrades;
}

async function fetchTopSymbols() {
  try {
    const tickers = await binancePublic('/api/v3/ticker/24hr');
    const filtered = tickers
      .filter(t => t.symbol.endsWith('USDT')
        && !['DOWN','UP','BEAR','BULL'].some(x => t.symbol.includes(x))
        && parseFloat(t.quoteVolume) >= CONFIG.MIN_VOLUME_USDT
        && parseFloat(t.lastPrice) > 0)
      .sort((a,b) => parseFloat(b.quoteVolume) - parseFloat(a.quoteVolume))
      .slice(0, CONFIG.MAX_SYMBOLS)
      .map(t => t.symbol);
    dynamicSymbols = filtered;
    botState.symbolsLoaded = filtered.length;
    currentBatchIndex = 0;
    log('INFO', `${filtered.length} symbols loaded. Top 5: ${filtered.slice(0,5).join(', ')}`);
  } catch(e) {
    log('ERROR', 'Symbol fetch failed: ' + e.message);
    if (dynamicSymbols.length === 0) {
      dynamicSymbols = ['BTCUSDT','ETHUSDT','SOLUSDT','BNBUSDT','XRPUSDT','DOGEUSDT','ADAUSDT'];
      botState.symbolsLoaded = 7;
    }
  }
}

// ─── Indicators ───────────────────────────────────────────────────────────────
function ema(arr,p){const k=2/(p+1);let e=arr[0];for(let i=1;i<arr.length;i++)e=arr[i]*k+e*(1-k);return e;}
function rsi(c,p=14){let g=0,l=0;for(let i=1;i<=p;i++){const d=c[i]-c[i-1];d>0?g+=d:l-=d;}let ag=g/p,al=l/p;for(let i=p+1;i<c.length;i++){const d=c[i]-c[i-1];ag=(ag*(p-1)+Math.max(d,0))/p;al=(al*(p-1)+Math.max(-d,0))/p;}return al===0?100:100-100/(1+ag/al);}
function vwap(klines){let tv=0,v=0;for(const k of klines){const tp=(+k[2]+ +k[3]+ +k[4])/3;tv+=tp* +k[5];v+= +k[5];}return tv/v;}
function bollinger(c,p=20){const sl=c.slice(-p);const m=sl.reduce((a,b)=>a+b,0)/p;const s=Math.sqrt(sl.reduce((a,b)=>a+(b-m)**2,0)/p);return{upper:m+2*s,middle:m,lower:m-2*s};}
function mfi(klines,p=14){const tps=klines.map(k=>(+k[2]+ +k[3]+ +k[4])/3);const vols=klines.map(k=>+k[5]);let pos=0,neg=0;for(let i=klines.length-p;i<klines.length;i++){const mfv=tps[i]*vols[i];tps[i]>tps[i-1]?pos+=mfv:neg+=mfv;}return neg===0?100:100-100/(1+pos/neg);}
function momentum(c,p=10){return((c[c.length-1]-c[c.length-1-p])/c[c.length-1-p])*100;}
function obv(klines){let o=0;const s=[0];for(let i=1;i<klines.length;i++){const c=+klines[i][4],pc=+klines[i-1][4],v=+klines[i][5];c>pc?o+=v:c<pc?o-=v:null;s.push(o);}const r=s.slice(-10),n=r.length;const sx=n*(n-1)/2,sy=r.reduce((a,b)=>a+b,0);const sxy=r.reduce((s,v,i)=>s+i*v,0),sx2=r.reduce((s,_,i)=>s+i*i,0);const d=n*sx2-sx*sx;const sl=d!==0?(n*sxy-sx*sy)/d:0;return{value:o,trend:sl>50000?'Rising':sl<-50000?'Falling':'Flat'};}
function stoch(c,h,l,p=14){const hh=Math.max(...h.slice(-p)),ll=Math.min(...l.slice(-p));return hh===ll?50:((c[c.length-1]-ll)/(hh-ll))*100;}
function atr(klines,p=14){const trs=[];for(let i=1;i<klines.length;i++){const h=+klines[i][2],l=+klines[i][3],pc=+klines[i-1][4];trs.push(Math.max(h-l,Math.abs(h-pc),Math.abs(l-pc)));}return trs.slice(-p).reduce((a,b)=>a+b,0)/p;}

// ─── Single Timeframe Analysis ────────────────────────────────────────────────
// Returns a score: positive = bullish, negative = bearish, 0 = neutral
// Also returns individual indicator values for display
function analyzeTimeframe(klines) {
  const closes = klines.map(k => +k[4]);
  const highs   = klines.map(k => +k[2]);
  const lows    = klines.map(k => +k[3]);
  const price   = closes[closes.length - 1];

  const rsiV  = rsi(closes);
  const macd  = ema(closes.slice(-26), 12) - ema(closes.slice(-26), 26);
  const e9    = ema(closes.slice(-9), 9);
  const e21   = ema(closes.slice(-21), 21);
  const e50   = ema(closes.slice(-50), 50);
  const bb    = bollinger(closes);
  const vwapV = vwap(klines);
  const mfiV  = mfi(klines, 14);
  const momV  = momentum(closes, 10);
  const obvV  = obv(klines);
  const stochV= stoch(closes, highs, lows);
  const bbPct = (price - bb.lower) / (bb.upper - bb.lower);

  let bull = 0, bear = 0;

  // RSI (weight 3)
  if (rsiV < 30) bull += 3; else if (rsiV > 70) bear += 3;
  else if (rsiV < 45) bull += 1; else if (rsiV > 55) bear += 1;

  // MACD (weight 2)
  macd > 0 ? bull += 2 : bear += 2;

  // EMA 9/21 cross (weight 2)
  e9 > e21 ? bull += 2 : bear += 2;

  // EMA 21/50 trend (weight 2)
  e21 > e50 ? bull += 2 : bear += 2;

  // VWAP position (weight 2)
  price > vwapV ? bull += 2 : bear += 2;

  // Bollinger position (weight 2)
  if (bbPct < 0.2) bull += 2; else if (bbPct > 0.8) bear += 2;

  // MFI — highest weight (weight 4)
  if (mfiV < 20) bull += 4; else if (mfiV > 80) bear += 4;
  else if (mfiV < 35) bull += 3; else if (mfiV > 65) bear += 3;
  else if (mfiV < 50) bull += 1; else bear += 1;

  // Momentum (weight 2)
  if (momV > 0.3) bull += 2; else if (momV < -0.3) bear += 2;
  else if (momV > 0.1) bull += 1; else if (momV < -0.1) bear += 1;

  // OBV trend (weight 2)
  if (obvV.trend === 'Rising') bull += 2; else if (obvV.trend === 'Falling') bear += 2;

  // Stochastic (weight 2)
  if (stochV < 20) bull += 2; else if (stochV > 80) bear += 2;
  else if (stochV < 35) bull += 1; else if (stochV > 65) bear += 1;

  const diff = bull - bear;
  const verdict = diff >= 6 ? 'LONG' : diff <= -6 ? 'SHORT' : 'NEUTRAL';

  // MFI gate per timeframe
  const mfiOk = verdict === 'LONG' ? mfiV <= 65 : verdict === 'SHORT' ? mfiV >= 35 : true;

  return {
    verdict, bull, bear, diff, mfiOk,
    rsiV, mfiV, macd, e9, e21, bbPct, vwapV,
    momV, obvV, stochV, price,
  };
}

// ─── Multi-Timeframe Confluence Engine ───────────────────────────────────────
// This is the core of the system.
// Fetches all 4 timeframes, scores each, then calculates a weighted confluence.
// Only fires a trade when enough timeframes agree on the same direction.
async function analyzeMultiTimeframe(symbol, ob) {
  const tfResults = [];

  // Fetch all timeframes in parallel
  const fetches = CONFIG.TIMEFRAMES.map(tf =>
    binancePublic('/api/v3/klines', { symbol, interval: tf.interval, limit: tf.limit })
      .then(klines => ({ tf, klines, error: null }))
      .catch(e => ({ tf, klines: null, error: e.message }))
  );
  const results = await Promise.all(fetches);

  for (const { tf, klines, error } of results) {
    if (error || !klines || klines.length < 30) continue;
    const analysis = analyzeTimeframe(klines);
    tfResults.push({ ...analysis, interval: tf.interval, label: tf.label, weight: tf.weight });
  }

  if (tfResults.length < 2) return null;

  // Count agreements per direction weighted by timeframe importance
  let longScore = 0, shortScore = 0;
  let longCount = 0, shortCount = 0;
  const tfSummary = [];

  for (const tf of tfResults) {
    if (tf.verdict === 'LONG' && tf.mfiOk) {
      longScore += tf.weight;
      longCount++;
    } else if (tf.verdict === 'SHORT' && tf.mfiOk) {
      shortScore += tf.weight;
      shortCount++;
    }
    tfSummary.push({
      label: tf.label,
      verdict: tf.verdict,
      mfi: tf.mfiV.toFixed(1),
      rsi: tf.rsiV.toFixed(1),
      obv: tf.obvV.trend,
      bull: tf.bull,
      bear: tf.bear,
      mfiOk: tf.mfiOk,
    });
  }

  // Determine dominant direction
  let finalVerdict, confluenceScore, agreeingCount;
  if (longScore > shortScore && longScore >= CONFIG.MIN_CONFLUENCE_SCORE && longCount >= CONFIG.MIN_AGREEING_TIMEFRAMES) {
    finalVerdict = 'LONG';
    confluenceScore = longScore;
    agreeingCount = longCount;
  } else if (shortScore > longScore && shortScore >= CONFIG.MIN_CONFLUENCE_SCORE && shortCount >= CONFIG.MIN_AGREEING_TIMEFRAMES) {
    finalVerdict = 'SHORT';
    confluenceScore = shortScore;
    agreeingCount = shortCount;
  } else {
    return null; // No confluence — skip this coin
  }

  // Use 1m timeframe values for entry levels and primary indicators
  const tf1m = tfResults.find(t => t.interval === '1m') || tfResults[0];
  const spread = (parseFloat(ob.asks[0][0]) - parseFloat(ob.bids[0][0])) / tf1m.price * 100;
  if (spread > 0.12) return null; // Skip wide spread

  const tier = getCurrentTier();
  let entry, target, stop;
  if (finalVerdict === 'LONG') {
    entry  = parseFloat(ob.asks[0][0]);
    target = entry * (1 + tier.targetPct / 100);
    stop   = entry * (1 - tier.stopPct / 100);
  } else {
    entry  = parseFloat(ob.bids[0][0]);
    target = entry * (1 - tier.targetPct / 100);
    stop   = entry * (1 + tier.stopPct / 100);
  }
  const rr = Math.abs(target - entry) / Math.abs(stop - entry);

  // Confidence based on confluence strength
  const maxPossibleScore = CONFIG.TIMEFRAMES.reduce((s, t) => s + t.weight, 0);
  const confluencePct = (confluenceScore / maxPossibleScore) * 100;
  const confidence = Math.min(Math.round(50 + confluencePct * 0.45), 97);
  const grade = confidence >= 85 ? 'A' : confidence >= 73 ? 'B' : confidence >= 60 ? 'C' : 'D';

  // Quality score for best-signal ranking
  let quality = confidence * 0.4;
  quality += (agreeingCount / CONFIG.TIMEFRAMES.length) * 20;
  quality += confluenceScore >= 6 ? 15 : confluenceScore >= 5 ? 8 : 0;
  if (finalVerdict === 'LONG') {
    quality += tf1m.mfiV < 30 ? 15 : tf1m.mfiV < 50 ? 8 : 0;
    quality += tf1m.obvV.trend === 'Rising' ? 8 : 0;
  } else {
    quality += tf1m.mfiV > 70 ? 15 : tf1m.mfiV > 50 ? 8 : 0;
    quality += tf1m.obvV.trend === 'Falling' ? 8 : 0;
  }
  if (rr >= 2) quality += 8; else if (rr >= 1.5) quality += 4;
  quality = Math.min(Math.round(quality), 100);

  return {
    symbol,
    verdict: finalVerdict,
    confidence, grade, quality,
    confluenceScore: parseFloat(confluenceScore.toFixed(2)),
    agreeingCount,
    entry, target, stop, rr,
    targetPct: tier.targetPct,
    stopPct: tier.stopPct,
    tier: tier.label,
    tierIndex: getTierIndex(),
    spread,
    // Primary indicators from 1m for display
    rsiV: tf1m.rsiV,
    mfiV: tf1m.mfiV,
    momV: tf1m.momV,
    obvV: tf1m.obvV,
    macd: tf1m.macd,
    e9: tf1m.e9,
    e21: tf1m.e21,
    stochV: tf1m.stochV,
    bbPct: tf1m.bbPct,
    // Full timeframe breakdown
    timeframes: tfSummary,
  };
}

// ─── Order Execution ──────────────────────────────────────────────────────────
async function placeOrder(symbol, side, usdtAmount, price) {
  if (CONFIG.PAPER_MODE) {
    const qty = parseFloat((usdtAmount / price).toFixed(6));
    log('INFO', `[PAPER] ${side} ${qty} ${symbol} @ $${price.toFixed(6)}`);
    return { orderId: 'PAPER-' + Date.now(), symbol, side, qty, price, paper: true };
  }
  try {
    const info = await binancePublic('/api/v3/exchangeInfo', { symbol });
    const lf = info.symbols?.[0]?.filters?.find(f => f.filterType === 'LOT_SIZE');
    const step = lf ? parseFloat(lf.stepSize) : 0.001;
    const dec = step.toString().split('.')[1]?.length || 3;
    const qty = parseFloat((Math.floor(usdtAmount / price / step) * step).toFixed(dec));
    if (qty <= 0) throw new Error('Qty too small');
    const order = await binanceSigned('POST', '/api/v3/order', { symbol, side, type: 'MARKET', quantity: qty });
    const fp = parseFloat(order.fills?.[0]?.price || price);
    log('INFO', `[LIVE] ${side} ${qty} ${symbol} @ $${fp.toFixed(6)} ($${usdtAmount})`);
    return { orderId: order.orderId, symbol, side, qty, price: fp, paper: false };
  } catch(e) { log('ERROR', `Order failed ${symbol}: ${e.message}`); throw e; }
}

// ─── Risk & Monitor ───────────────────────────────────────────────────────────
function resetDailyPnl() {
  const today = new Date().toDateString();
  if (botState.dailyPnlDate !== today) { botState.dailyPnl = 0; botState.dailyPnlDate = today; log('INFO', 'Daily PnL reset'); }
}

function isCooldownActive() {
  if (!botState.inCooldown) return false;
  const elapsed = Date.now() - botState.lastLossTime;
  if (elapsed >= CONFIG.COOLDOWN_AFTER_LOSS_MS) { botState.inCooldown = false; return false; }
  return Math.ceil((CONFIG.COOLDOWN_AFTER_LOSS_MS - elapsed) / 1000);
}

async function getPrice(symbol) {
  const t = await binancePublic('/api/v3/ticker/price', { symbol });
  return parseFloat(t.price);
}

// ─── Trailing Stop Engine ─────────────────────────────────────────────────────
// Once price reaches the initial target (e.g. 0.25%), the trade enters
// TRAILING mode. In trailing mode the fixed stop is replaced by a dynamic
// trailing stop that sits 1% below the highest price seen (for LONGs) or
// 1% above the lowest price seen (for SHORTs).
// This means profitable moves beyond 0.25% are locked in automatically.
// The trade only closes when price pulls back 1% from its peak.
const TRAIL_PCT = 1.0; // trail distance as % from peak/trough

function activateTrailing(trade, currentPrice) {
  trade.trailing = true;
  trade.trailPeak = currentPrice;          // highest price seen in LONG
  trade.trailTrough = currentPrice;        // lowest price seen in SHORT
  trade.trailStop = trade.side === 'LONG'
    ? currentPrice * (1 - TRAIL_PCT / 100)
    : currentPrice * (1 + TRAIL_PCT / 100);
  trade.trailActivatedAt = currentPrice;
  log('INFO', `🎯 TRAILING activated: ${trade.symbol} ${trade.side} @ $${currentPrice.toFixed(6)} | trail stop: $${trade.trailStop.toFixed(6)}`);
}

function updateTrailingStop(trade, currentPrice) {
  if (trade.side === 'LONG') {
    if (currentPrice > trade.trailPeak) {
      trade.trailPeak = currentPrice;
      trade.trailStop = currentPrice * (1 - TRAIL_PCT / 100);
    }
  } else {
    if (currentPrice < trade.trailTrough) {
      trade.trailTrough = currentPrice;
      trade.trailStop = currentPrice * (1 + TRAIL_PCT / 100);
    }
  }
}

function isTrailStopHit(trade, currentPrice) {
  if (trade.side === 'LONG') return currentPrice <= trade.trailStop;
  return currentPrice >= trade.trailStop;
}

async function monitorOpenTrades() {
  for (const trade of [...botState.openTrades]) {
    try {
      const price = await getPrice(trade.symbol);
      let closeReason = null;

      if (!trade.trailing) {
        // ── Phase 1: Normal stop/target monitoring ───────────────────────────
        if (trade.side === 'LONG') {
          if (price >= trade.target) {
            // Target reached — activate trailing instead of closing immediately
            activateTrailing(trade, price);
          } else if (price <= trade.stop) {
            closeReason = 'STOP_HIT';
          }
        } else {
          if (price <= trade.target) {
            activateTrailing(trade, price);
          } else if (price >= trade.stop) {
            closeReason = 'STOP_HIT';
          }
        }
      } else {
        // ── Phase 2: Trailing stop monitoring ────────────────────────────────
        updateTrailingStop(trade, price);
        if (isTrailStopHit(trade, price)) {
          closeReason = 'TRAIL_STOP';
          const extraPct = trade.side === 'LONG'
            ? ((price - trade.trailActivatedAt) / trade.trailActivatedAt * 100).toFixed(3)
            : ((trade.trailActivatedAt - price) / trade.trailActivatedAt * 100).toFixed(3);
          log('INFO', `🏁 Trail stop hit: ${trade.symbol} | peak:$${(trade.side==='LONG'?trade.trailPeak:trade.trailTrough).toFixed(6)} | exit:$${price.toFixed(6)} | extra:+${extraPct}%`);
        }
      }
      if (closeReason) {
        const closeSide = trade.side === 'LONG' ? 'SELL' : 'BUY';
        let exitPrice = price;
        try { const co = await placeOrder(trade.symbol, closeSide, trade.qty * price, price); exitPrice = co.price; } catch(e) {}
        const pnl = trade.side === 'LONG' ? (exitPrice - trade.entry) * trade.qty : (trade.entry - exitPrice) * trade.qty;
        const pnlPct = ((pnl / trade.tradeSize) * 100).toFixed(3);
        botState.dailyPnl += pnl; botState.totalPnl += pnl;
        const isWin = pnl >= 0;
        isWin ? botState.winCount++ : botState.lossCount++;
        botState.closedTrades.unshift({ ...trade, exit: exitPrice, pnl, pnlPct: parseFloat(pnlPct), closedAt: new Date().toISOString(), closeReason });
        if (botState.closedTrades.length > 300) botState.closedTrades.pop();
        botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
        updateTradeScaling(isWin ? 'WIN' : 'LOSS');
        const total = botState.winCount + botState.lossCount;
        const wr = total > 0 ? ((botState.winCount / total) * 100).toFixed(0) + '%' : 'N/A';
        const peakPrice = trade.side === 'LONG' ? (trade.trailPeak || exitPrice) : (trade.trailTrough || exitPrice);
        const trailInfo = closeReason === 'TRAIL_STOP' ? ` | 🏁peak:$${peakPrice.toFixed(4)} trail:1%` : '';
        const trailStatus = trade.trailing && closeReason !== 'TRAIL_STOP' ? ' [TRAILING]' : '';
        log('INFO', `${isWin?'✅':'❌'} ${trade.symbol} ${trade.side} | PnL:$${pnl.toFixed(4)} (${pnlPct}%)${trailInfo}${trailStatus} | ${closeReason} | WR:${wr} | Trades:${botState.currentMaxTrades}`);
        await refreshBalance();
      }
    } catch(e) { log('WARN', `Monitor ${trade.symbol}: ${e.message}`); }
  }
}

// ─── Main Scan Loop ───────────────────────────────────────────────────────────
async function scanBatch() {
  if (!botState.running || botState.killSwitch) return;
  resetDailyPnl();

  const dailyLimit = botState.usdtBalance * (CONFIG.DAILY_LOSS_LIMIT_PCT / 100);
  if (dailyLimit > 0 && botState.dailyPnl <= -dailyLimit) {
    log('WARN', `🛑 Daily loss limit. Halting.`);
    botState.running = false; clearInterval(scanInterval); return;
  }

  if (dynamicSymbols.length === 0) { await fetchTopSymbols(); return; }
  await monitorOpenTrades();

  const tier = getCurrentTier();
  const cooldown = isCooldownActive();

  // Execute best candidates
  if (signalCandidates.length > 0 && botState.openTrades.length < botState.currentMaxTrades && !cooldown && !botState.drawdownPaused) {
    signalCandidates.sort((a, b) => b.quality - a.quality);
    const slots = botState.currentMaxTrades - botState.openTrades.length;
    for (const r of signalCandidates.slice(0, slots)) {
      if (botState.openTrades.some(t => t.symbol === r.symbol)) continue;
      if (botState.openTrades.length >= botState.currentMaxTrades) break;
      try {
        const side = r.verdict === 'LONG' ? 'BUY' : 'SELL';
        const tfStr = r.timeframes.map(t => `${t.label}:${t.verdict[0]}`).join(' ');
        log('INFO', `⭐ EXECUTE: ${r.symbol} ${r.verdict} | quality:${r.quality}/100 | conf:${r.confidence}% | ${r.agreeingCount}/${CONFIG.TIMEFRAMES.length} TF agree | score:${r.confluenceScore} | [${tfStr}]`);
        const order = await placeOrder(r.symbol, side, tier.tradeUsdt, r.entry);
        botState.tradesExecuted++;
        botState.openTrades.push({
          id: order.orderId, symbol: r.symbol, side: r.verdict,
          entry: order.price, qty: order.qty,
          target: r.target, stop: r.stop,
          targetPct: r.targetPct, stopPct: r.stopPct, rr: r.rr,
          grade: r.grade, confidence: r.confidence, quality: r.quality,
          confluenceScore: r.confluenceScore, agreeingCount: r.agreeingCount,
          tradeSize: tier.tradeUsdt, tier: r.tier, tierIndex: r.tierIndex,
          openedAt: new Date().toISOString(), paper: order.paper,
          research: {
            verdict: r.verdict,
            confluenceScore: r.confluenceScore,
            agreeingTimeframes: r.agreeingCount,
            timeframes: r.timeframes,
            rsi: r.rsiV.toFixed(1),
            mfi: r.mfiV.toFixed(1),
            mfiZone: r.mfiV < 30 ? 'Oversold' : r.mfiV > 70 ? 'Overbought' : r.mfiV < 50 ? 'Bullish' : 'Bearish',
            momentum: r.momV.toFixed(2) + '%',
            obv: r.obvV.trend,
            macd: r.macd > 0 ? 'Positive' : 'Negative',
            ema: r.e9 > r.e21 ? 'Bull Cross' : 'Bear Cross',
            stoch: r.stochV.toFixed(1),
            quality: r.quality,
          },
        });
        log('INFO', `📊 Balance:$${botState.usdtBalance.toFixed(2)} | ${tier.label} | Trades:${botState.openTrades.length}/${botState.currentMaxTrades}`);
      } catch(e) { log('ERROR', `Execute ${r.symbol}: ${e.message}`); }
    }
    signalCandidates = [];
  } else if (cooldown) {
    log('INFO', `⏳ Cooldown ${cooldown}s`);
  } else if (botState.drawdownPaused) {
    log('INFO', `⚠️ Drawdown pause active`);
  }

  // Scan next batch
  const batch = dynamicSymbols.slice(currentBatchIndex, currentBatchIndex + CONFIG.SCAN_BATCH_SIZE);
  if (batch.length === 0) {
    currentBatchIndex = 0; botState.cycleCount++; botState.scanCount++;
    botState.lastScan = new Date().toISOString();
    const total = botState.winCount + botState.lossCount;
    const wr = total > 0 ? ((botState.winCount / total) * 100).toFixed(0) + '%' : 'N/A';
    log('INFO', `🔄 Cycle ${botState.cycleCount} | ${dynamicSymbols.length} coins | ${botState.totalSignalsFound} signals | ${botState.confluenceRejected} no-confluence | WR:${wr} | PnL:$${botState.totalPnl.toFixed(4)}`);
    signalCandidates = []; return;
  }

  botState.currentBatch = batch;

  for (const symbol of batch) {
    if (!botState.running || botState.killSwitch) break;
    if (botState.openTrades.some(t => t.symbol === symbol)) continue;
    try {
      // Fetch order book for spread check and entry levels
      const ob = await binancePublic('/api/v3/depth', { symbol, limit: 10 });
      // Run full multi-timeframe analysis
      const r = await analyzeMultiTimeframe(symbol, ob);
      if (!r) { botState.confluenceRejected++; continue; }
      botState.totalSignalsFound++;
      signalCandidates.push(r);
      const tfStr = r.timeframes.map(t => `${t.label}:${t.verdict.substring(0,1)}(MFI${t.mfi})`).join(' ');
      log('INFO', `✨ Confluence: ${symbol} ${r.verdict} | quality:${r.quality}/100 | ${r.agreeingCount}TF | score:${r.confluenceScore} | ${tfStr}`);
      await new Promise(res => setTimeout(res, 300));
    } catch(e) { log('WARN', `Scan ${symbol}: ${e.message}`); }
  }
  currentBatchIndex += CONFIG.SCAN_BATCH_SIZE;
}

// ─── Routes ───────────────────────────────────────────────────────────────────
app.get('/health', (req,res) => res.json({ status: 'ok', ts: new Date().toISOString() }));

app.get('/status', (req,res) => {
  const tier = getCurrentTier();
  const total = botState.winCount + botState.lossCount;
  const cooldown = isCooldownActive();
  res.json({
    running: botState.running, mode: botState.mode, killSwitch: botState.killSwitch,
    openTrades: botState.openTrades, closedTrades: botState.closedTrades.slice(0, 50),
    dailyPnl: botState.dailyPnl, totalPnl: botState.totalPnl,
    scanCount: botState.scanCount, cycleCount: botState.cycleCount, lastScan: botState.lastScan,
    symbolsLoaded: botState.symbolsLoaded, currentBatch: botState.currentBatch,
    usdtBalance: botState.usdtBalance, startingBalance: botState.startingBalance,
    currentTier: botState.currentTierIndex + 1, tierName: tier.label,
    currentTradeUsdt: tier.tradeUsdt,
    currentMaxTrades: botState.currentMaxTrades,
    tierBaseTrades: tier.baseTrades, tierMaxTrades: tier.maxTrades,
    targetPct: tier.targetPct, stopPct: tier.stopPct,
    consecutiveWins: botState.consecutiveWins, consecutiveLosses: botState.consecutiveLosses,
    inCooldown: !!cooldown, cooldownRemaining: cooldown || 0,
    drawdownPaused: botState.drawdownPaused,
    totalSignalsFound: botState.totalSignalsFound,
    confluenceRejected: botState.confluenceRejected,
    mfiRejected: botState.mfiRejected,
    tradesExecuted: botState.tradesExecuted,
    winCount: botState.winCount, lossCount: botState.lossCount,
    winRate: total > 0 ? ((botState.winCount / total) * 100).toFixed(1) + '%' : 'N/A',
    signalCandidates: signalCandidates.length,
    scalingLog: botState.scalingLog.slice(0, 20),
    config: {
      symbols: dynamicSymbols.slice(0, 20), totalSymbols: dynamicSymbols.length,
      timeframes: CONFIG.TIMEFRAMES.map(t => t.label),
      minConfluenceScore: CONFIG.MIN_CONFLUENCE_SCORE,
      minAgreeingTimeframes: CONFIG.MIN_AGREEING_TIMEFRAMES,
      tiers: CONFIG.TIERS, currentTierFull: tier,
      scalingRules: {
        winStreakToAdd: CONFIG.WIN_STREAK_TO_ADD,
        lossStreakToRemove: CONFIG.LOSS_STREAK_TO_REMOVE,
        cooldownSec: CONFIG.COOLDOWN_AFTER_LOSS_MS / 1000,
        minWinRateToScale: CONFIG.MIN_WIN_RATE_TO_SCALE,
        drawdownPausePct: CONFIG.DRAWDOWN_PAUSE_PCT,
      },
    },
    log: botState.log.slice(0, 100),
  });
});

app.post('/start', async (req,res) => {
  if (botState.running) return res.json({ success: false, message: 'Already running' });
  if (botState.killSwitch) return res.json({ success: false, message: 'Kill switch active' });
  await refreshBalance();
  const tier = getCurrentTier();
  if (botState.currentMaxTrades < tier.baseTrades) botState.currentMaxTrades = tier.baseTrades;
  botState.running = true;
  scanBatch();
  scanInterval = setInterval(scanBatch, CONFIG.SCAN_INTERVAL_MS);
  const msg = `Bot started | ${botState.mode} | ${tier.label} | TF: 1m+3m+5m+15m | min ${CONFIG.MIN_AGREEING_TIMEFRAMES} TF agree | $${tier.tradeUsdt}/trade | ${tier.targetPct}%→${tier.stopPct}% | trades:${botState.currentMaxTrades}→${tier.maxTrades}`;
  log('INFO', msg);
  res.json({ success: true, message: msg });
});

app.post('/stop', (req,res) => {
  botState.running = false; clearInterval(scanInterval);
  log('INFO', 'Bot stopped'); res.json({ success: true, message: 'Stopped' });
});

app.post('/kill', (req,res) => {
  botState.running = false; botState.killSwitch = true; clearInterval(scanInterval);
  log('WARN', '🚨 KILL SWITCH'); res.json({ success: true, message: 'Kill switch activated' });
});

app.post('/reset-kill', (req,res) => {
  botState.killSwitch = false; log('INFO', 'Kill switch reset');
  res.json({ success: true, message: 'Kill switch reset' });
});

app.post('/close-trade/:id', async (req,res) => {
  const trade = botState.openTrades.find(t => t.id === req.params.id);
  if (!trade) return res.json({ success: false, message: 'Not found' });
  try {
    const price = await getPrice(trade.symbol);
    await placeOrder(trade.symbol, trade.side === 'LONG' ? 'SELL' : 'BUY', trade.qty * price, price);
    const pnl = trade.side === 'LONG' ? (price - trade.entry) * trade.qty : (trade.entry - price) * trade.qty;
    botState.dailyPnl += pnl; botState.totalPnl += pnl;
    botState.closedTrades.unshift({ ...trade, exit: price, pnl, closedAt: new Date().toISOString(), closeReason: 'MANUAL_CLOSE' });
    botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
    await refreshBalance();
    log('INFO', `Manual close ${trade.symbol} | PnL:$${pnl.toFixed(4)}`);
    res.json({ success: true, pnl });
  } catch(e) { res.json({ success: false, message: e.message }); }
});

app.get('/balance', async (req,res) => {
  await refreshBalance();
  const tier = getCurrentTier();
  const total = botState.winCount + botState.lossCount;
  res.json({
    usdtBalance: botState.usdtBalance, startingBalance: botState.startingBalance,
    totalPnl: botState.totalPnl,
    growthPct: botState.startingBalance > 0 ? ((botState.totalPnl / botState.startingBalance) * 100).toFixed(2) + '%' : '0%',
    tier: tier.label, tierIndex: botState.currentTierIndex + 1,
    tradeUsdt: tier.tradeUsdt, currentMaxTrades: botState.currentMaxTrades,
    baseTrades: tier.baseTrades, maxTrades: tier.maxTrades,
    targetPct: tier.targetPct, stopPct: tier.stopPct,
    winRate: total > 0 ? ((botState.winCount / total) * 100).toFixed(1) + '%' : 'N/A',
    allTiers: CONFIG.TIERS,
  });
});

const PORT = process.env.PORT || 3001;
app.listen(PORT, async () => {
  console.log(`\nSCALPR Multi-Timeframe Bot — port ${PORT}`);
  console.log(`Mode: ${CONFIG.PAPER_MODE ? 'PAPER' : '⚠ LIVE'}`);
  console.log(`Timeframes: ${CONFIG.TIMEFRAMES.map(t=>t.label+'(w'+t.weight+')').join(' · ')}`);
  console.log(`Confluence: min score ${CONFIG.MIN_CONFLUENCE_SCORE} | min ${CONFIG.MIN_AGREEING_TIMEFRAMES} TF agreeing`);
  console.log(`Profit: 0.25%→0.50% | MFI hard gate | Best-signal picker`);
  console.log(`Scaling: +1 trade per ${CONFIG.WIN_STREAK_TO_ADD} wins | -1 per ${CONFIG.LOSS_STREAK_TO_REMOVE} losses | ${CONFIG.COOLDOWN_AFTER_LOSS_MS/1000}s cooldown`);
  console.log(`Tiers: ${CONFIG.TIERS.map(t=>`${t.label}($${t.tradeUsdt} ${t.baseTrades}-${t.maxTrades}T ${t.targetPct}%)`).join(' | ')}\n`);
  await fetchTopSymbols();
  await refreshBalance();
  const tier = getCurrentTier();
  botState.currentMaxTrades = tier.baseTrades;
  symbolRefreshInterval = setInterval(fetchTopSymbols, 60 * 60 * 1000);
  balanceRefreshInterval = setInterval(refreshBalance, 5 * 60 * 1000);
});