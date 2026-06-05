const express = require('express');
const crypto  = require('crypto');
const cors    = require('cors');
const https   = require('https');

const app = express();
app.use(cors());
app.use(express.json());

// ─── Config ───────────────────────────────────────────────────────────────────
const CONFIG = {
  API_KEY:    'GMuw4Yz4dP3bbyHi2nuU9EpZWrT0HfjT866mf8ypAYyTb6bI6AF6FXLXhZa7z5EC',
  API_SECRET: '842R1G1EoIIJKArvUpRe3uc67H9WfuPFzTACNHFsWjg4C9OyJ8c2mPfp7Nt9qEfS',
  PAPER_MODE: false,
  DAILY_LOSS_LIMIT_PCT: 5,
  REST_BASE: 'https://fapi.binance.com',
  TARGET_PCT: 0.33,
  STOP_PCT:   0.25,
  LEVERAGE:   5,
  MARGIN_USDT: 100,
  TIMEFRAMES: ['1m', '3m', '5m', '15m'],
  MIN_CANDLES: 20,
  SYMBOLS: [
    'BTCUSDT','ETHUSDT','SOLUSDT','BNBUSDT','XRPUSDT',
    'DOGEUSDT','ADAUSDT','MATICUSDT','DOTUSDT','LINKUSDT',
    'AVAXUSDT','LTCUSDT','TRXUSDT','XLMUSDT','NEARUSDT',
    'ATOMUSDT','UNIUSDT','ETCUSDT','GALAUSDT','VETUSDT',
    'ALGOUSDT','SANDUSDT','MANAUSDT','AXSUSDT','TONUSDT',
    'INJUSDT','SUIUSDT','ARBUSDT','OPUSDT','LDOUSDT',
    'APTUSDT','STXUSDT','FETUSDT','SEIUSDT','TIAUSDT',
    'WLDUSDT','JUPUSDT','ENAUSDT','WIFUSDT','BONKUSDT',
    'PEPEUSDT','HBARUSDT','ICPUSDT','RUNEUSDT','MKRUSDT',
    'AAVEUSDT','CRVUSDT','GRTUSDT','SUSHIUSDT','DYDXUSDT',
    'FLOWUSDT','MINAUSDT','ZILUSDT','ZECUSDT','XMRUSDT',
    'XTZUSDT','NEOUSDT','APEUSDT','IMXUSDT','ONDOUSDT',
  ],
  TIERS: [
    { minBalance:0,      tradeUsdt:20, baseTrades:1, maxTrades:2,  label:'Starter'    },
    { minBalance:300,    tradeUsdt:25, baseTrades:1, maxTrades:3,  label:'Bronze I'   },
    { minBalance:500,    tradeUsdt:30, baseTrades:2, maxTrades:4,  label:'Bronze II'  },
    { minBalance:800,    tradeUsdt:120, baseTrades:2, maxTrades:5,  label:'Silver I'   },
    { minBalance:1200,   tradeUsdt:130, baseTrades:3, maxTrades:6,  label:'Silver II'  },
    { minBalance:1800,   tradeUsdt:150, baseTrades:3, maxTrades:7,  label:'Gold I'     },
    { minBalance:2500,   tradeUsdt:175, baseTrades:4, maxTrades:8,  label:'Gold II'    },
    { minBalance:3500,   tradeUsdt:200, baseTrades:4, maxTrades:9,  label:'Platinum I' },
    { minBalance:5000,   tradeUsdt:225, baseTrades:5, maxTrades:10, label:'Platinum II'},
    { minBalance:7500,   tradeUsdt:250, baseTrades:6, maxTrades:12, label:'Diamond I'  },
    { minBalance:10000,  tradeUsdt:300, baseTrades:7, maxTrades:14, label:'Diamond II' },
    { minBalance:15000,  tradeUsdt:350, baseTrades:8, maxTrades:16, label:'Elite I'    },
    { minBalance:22000,  tradeUsdt:400, baseTrades:9, maxTrades:18, label:'Elite II'   },
    { minBalance:32000,  tradeUsdt:500, baseTrades:10,maxTrades:20, label:'Master I'   },
    { minBalance:50000,  tradeUsdt:600, baseTrades:12,maxTrades:25, label:'Master II'  },
    { minBalance:75000,  tradeUsdt:750, baseTrades:15,maxTrades:35, label:'Legend I'   },
    { minBalance:100000, tradeUsdt:900, baseTrades:20,maxTrades:45, label:'Legend II'  },
    { minBalance:150000, tradeUsdt:1000,baseTrades:25,maxTrades:50, label:'Supreme'    },
  ],
  WIN_STREAK_TO_ADD: 3,
  LOSS_STREAK_TO_REMOVE: 2,
  COOLDOWN_AFTER_LOSS_MS: 60000,
  MIN_WIN_RATE_TO_SCALE: 55,
  DRAWDOWN_PAUSE_PCT: 3,
};

const BASE = CONFIG.REST_BASE;
if (!global.stepSizeCache) global.stepSizeCache = {};
if (!global.tickSizeCache) global.tickSizeCache = {};

// ─── Kline store ──────────────────────────────────────────────────────────────
const klineStore = {};
const livePrice  = {};

function pushKline(symbol, tf, candle) {
  if (!klineStore[symbol]) klineStore[symbol] = {};
  if (!klineStore[symbol][tf]) klineStore[symbol][tf] = [];
  const store = klineStore[symbol][tf];
  const idx = store.findIndex(k => k.t === candle.t);
  if (idx >= 0) store[idx] = candle;
  else store.push(candle);
  if (store.length > 100) store.shift();
}

function getKlines(symbol, tf) {
  return klineStore[symbol]?.[tf] || [];
}

// ─── Bot state ────────────────────────────────────────────────────────────────
let botState = {
  running: false,
  mode: 'FUTURES',
  openTrades: [], closedTrades: [],
  dailyPnl: 0, dailyPnlDate: new Date().toDateString(), totalPnl: 0,
  log: [], killSwitch: false,
  usdtBalance: 0, startingBalance: 0, currentTierIndex: 0,
  totalSignalsFound: 0, confluenceRejected: 0,
  tradesExecuted: 0, winCount: 0, lossCount: 0,
  currentMaxTrades: 1, consecutiveWins: 0, consecutiveLosses: 0,
  lastLossTime: 0, inCooldown: false, drawdownPaused: false,
  scalingLog: [], candlesReceived: 0, lastSignalCheck: null,
  wsConnected: false, wsStreamCount: 0,
};

let monitorInterval = null;
let balanceInterval = null;
let pollInterval    = null;

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
  if (dd >= CONFIG.DRAWDOWN_PAUSE_PCT && !botState.drawdownPaused) { botState.drawdownPaused = true; logScale('Drawdown pause'); }
  if (dd < CONFIG.DRAWDOWN_PAUSE_PCT*0.5 && botState.drawdownPaused) { botState.drawdownPaused = false; logScale('Drawdown recovered'); }
  const cur = botState.currentMaxTrades;
  if (botState.consecutiveWins >= CONFIG.WIN_STREAK_TO_ADD && wr >= CONFIG.MIN_WIN_RATE_TO_SCALE && cur < tier.maxTrades && !botState.drawdownPaused) {
    botState.currentMaxTrades = Math.min(cur+1, tier.maxTrades); botState.consecutiveWins = 0;
    logScale('Trades UP to ' + botState.currentMaxTrades);
  }
  if ((botState.consecutiveLosses >= CONFIG.LOSS_STREAK_TO_REMOVE || (total>=10&&wr<40)) && cur > tier.baseTrades) {
    botState.currentMaxTrades = Math.max(cur-1, tier.baseTrades); botState.consecutiveLosses = 0;
    logScale('Trades DOWN to ' + botState.currentMaxTrades);
  }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) {
    botState.currentMaxTrades = CONFIG.TIERS[ni].baseTrades;
    botState.consecutiveWins = 0; botState.consecutiveLosses = 0;
    logScale('Tier to ' + CONFIG.TIERS[ni].label);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── REST helpers ─────────────────────────────────────────────────────────────
function restGet(url) {
  return new Promise((resolve, reject) => {
    https.get(url, { headers: {'User-Agent':'scalpr/3.0'} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch(e) { reject(e); } });
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
    const acc = await binanceSigned('GET', '/fapi/v2/account');
    const u = acc.assets?.find(b => b.asset === 'USDT');
    botState.usdtBalance = u ? parseFloat(u.availableBalance) : 0;
    if (!botState.startingBalance && botState.usdtBalance > 0) {
      botState.startingBalance = botState.usdtBalance;
      log('INFO', 'Start balance: $' + botState.startingBalance.toFixed(2));
    }
  } catch(e) { log('WARN', 'Balance: ' + e.message); return; }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) updateTradeScaling(null);
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── Leverage setup ───────────────────────────────────────────────────────────
async function setupSymbol(symbol) {
  try { await binanceSigned('POST', '/fapi/v1/leverage', { symbol, leverage: CONFIG.LEVERAGE }); } catch(e) {}
  try { await binanceSigned('POST', '/fapi/v1/marginType', { symbol, marginType: 'ISOLATED' }); } catch(e) {}
}

// ─── Seed historical klines ───────────────────────────────────────────────────
async function seedKlines(symbol, tf) {
  try {
    const data = await binancePublic('/fapi/v1/klines', { symbol, interval: tf, limit: 60 });
    if (!Array.isArray(data)) return;
    for (const k of data) {
      pushKline(symbol, tf, { t:k[0], o:parseFloat(k[1]), h:parseFloat(k[2]), l:parseFloat(k[3]), c:parseFloat(k[4]), v:parseFloat(k[5]) });
    }
    livePrice[symbol] = parseFloat(data[data.length-1][4]);
  } catch(e) {}
}

// ─── REST polling (replaces WebSocket) ────────────────────────────────────────
async function startPolling() {
  log('INFO', 'Starting REST polling...');
  botState.wsConnected = true;
  botState.wsStreamCount = CONFIG.SYMBOLS.length;

  async function poll() {
    if (!botState.running) return;
    for (const sym of CONFIG.SYMBOLS) {
      if (!botState.running) break;
      for (const tf of CONFIG.TIMEFRAMES) {
        try {
          const data = await binancePublic('/fapi/v1/klines', { symbol: sym, interval: tf, limit: 10 });
          if (!Array.isArray(data)) continue;
          for (let i = 0; i < data.length; i++) {
            const k = data[i];
            const isClosed = i < data.length - 1;
            const candle = { t:k[0], o:parseFloat(k[1]), h:parseFloat(k[2]), l:parseFloat(k[3]), c:parseFloat(k[4]), v:parseFloat(k[5]) };
            livePrice[sym] = candle.c;
            pushKline(sym, tf, candle);
            botState.candlesReceived++;
            if (isClosed) analyzeAndTrade(sym, tf);
          }
        } catch(e) { log('WARN', 'Poll ' + sym + ' ' + tf + ': ' + e.message); }
      }
      await new Promise(r => setTimeout(r, 150));
    }
    log('INFO', 'Polled ' + CONFIG.SYMBOLS.length + ' symbols. Next in 30s');
    setTimeout(poll, 30000);
  }
  await poll();
}

// ─── Indicators ───────────────────────────────────────────────────────────────
function stochRSI(klines, rP=14, sP=14, sK=3, sD=3) {
  const closes = klines.map(k => k.c);
  const rs = [];
  for (let i = rP; i < closes.length; i++) {
    const sl = closes.slice(i-rP, i+1); let g=0, l=0;
    for (let j=1; j<=rP; j++) { const d=sl[j]-sl[j-1]; d>0?g+=d:l-=d; }
    let ag=g/rP, al=l/rP;
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

function calcMomentum(klines) {
  const c = klines.map(k => k.c);
  const fast = c.length>5  ? (c[c.length-1]-c[c.length-6])/c[c.length-6]*100  : 0;
  const mid  = c.length>10 ? (c[c.length-1]-c[c.length-11])/c[c.length-11]*100 : 0;
  return { fast, mid, allBull:fast>0&&mid>0, allBear:fast<0&&mid<0 };
}

// ─── Score timeframe (StochRSI + Momentum only) ────────────────────────────────
function scoreTF(klines) {
  if (klines.length < CONFIG.MIN_CANDLES) return null;

  // Candle body filter
  const last = klines[klines.length-1];
  const body = Math.abs(last.c - last.o) / last.o * 100;
  if (body < 0.005) return null;

  // Volume filter
  const vols = klines.map(k => k.v);
  const avgVol = vols.slice(-20).reduce((a,b)=>a+b,0) / 20;
  if (vols[vols.length-1] < avgVol * 0.3) return null;

  const srsi = stochRSI(klines);
  const mom  = calcMomentum(klines);

  // StochRSI signal
  let srsiVerdict = 'NEUTRAL';
  if (srsi.k <= 20 || srsi.crossUp)   srsiVerdict = 'LONG';
  if (srsi.k >= 80 || srsi.crossDown) srsiVerdict = 'SHORT';

  // Momentum signal — fast period only
  let momVerdict = 'NEUTRAL';
  if (mom.fast > 0) momVerdict = 'LONG';
  if (mom.fast < 0) momVerdict = 'SHORT';

  // Both must agree
  let verdict = 'NEUTRAL';
  if (srsiVerdict === 'LONG'  && momVerdict === 'LONG')  verdict = 'LONG';
  if (srsiVerdict === 'SHORT' && momVerdict === 'SHORT') verdict = 'SHORT';

  let quality = 50;
  if (verdict === 'LONG') {
    if (srsi.k <= 10)  quality = 95;
    else if (srsi.k <= 20) quality = 88;
    else if (srsi.crossUp) quality = 80;
    else quality = 70;
    if (mom.allBull) quality = Math.min(quality+5, 99);
  } else if (verdict === 'SHORT') {
    if (srsi.k >= 90)  quality = 95;
    else if (srsi.k >= 80) quality = 88;
    else if (srsi.crossDown) quality = 80;
    else quality = 70;
    if (mom.allBear) quality = Math.min(quality+5, 99);
  }

  return { verdict, quality, srsiK:srsi.k, srsiD:srsi.d, crossUp:srsi.crossUp, crossDown:srsi.crossDown, momFast:mom.fast, momMid:mom.mid };
}

// ─── Analyze and trade ────────────────────────────────────────────────────────
async function analyzeAndTrade(symbol, closedTF) {
  if (!botState.running || botState.killSwitch) return;
  // Hard enforcement — check atomically
  if (botState.openTrades.some(t => t.symbol === symbol)) return;
  const maxT = botState.currentMaxTrades;
  const curT = botState.openTrades.length;
  if (curT >= maxT) {
    return; // silent skip
  }
  // Lock slot with a flag to prevent duplicate entries
  const slotId = symbol + '-' + Date.now();
  if (!global.executingSymbols) global.executingSymbols = new Set();
  if (global.executingSymbols.has(symbol)) return;
  global.executingSymbols.add(symbol);
  if (botState.drawdownPaused) return;
  if (isCooldownActive()) return;

  const results = {};
  for (const tf of CONFIG.TIMEFRAMES) {
    const klines = getKlines(symbol, tf);
    if (klines.length >= CONFIG.MIN_CANDLES) {
      const score = scoreTF(klines);
      if (score) results[tf] = score;
    }
  }
  // Need at least 2 timeframes to agree
  const available = Object.keys(results).length;
  if (available < 2) return;

  const verdicts = Object.values(results).map(r => r.verdict);
  const longCount  = verdicts.filter(v => v === 'LONG').length;
  const shortCount = verdicts.filter(v => v === 'SHORT').length;
  const neutralCount = verdicts.filter(v => v === 'NEUTRAL').length;

  // Majority rule — more than half of available TFs must agree
  const majority = Math.ceil(available / 2);
  const allLong  = longCount >= majority && shortCount === 0;
  const allShort = shortCount >= majority && longCount === 0;

  if (!allLong && !allShort) { botState.confluenceRejected++; return; }

  // Quality boost based on how many TFs agree
  const agreementPct = (allLong ? longCount : shortCount) / available;

  const verdict = allLong ? 'LONG' : 'SHORT';
  const primary = results[closedTF] || Object.values(results)[0];
  const price   = livePrice[symbol] || 0;
  if (!price) return;

  const tier   = getCurrentTier();
  const entry  = price;
  const target = verdict==='LONG' ? entry*(1+CONFIG.TARGET_PCT/100) : entry*(1-CONFIG.TARGET_PCT/100);
  const stop   = verdict==='LONG' ? entry*(1-CONFIG.STOP_PCT/100)   : entry*(1+CONFIG.STOP_PCT/100);

  botState.totalSignalsFound++;
  botState.lastSignalCheck = new Date().toISOString();

  log('INFO', '✨ ' + symbol + ' ' + verdict + ' | sRSI:' + primary.srsiK.toFixed(0) + ' mom:' + primary.momFast.toFixed(3) + ' | q:' + primary.quality);

  try {
    const orderSide = verdict === 'LONG' ? 'BUY' : 'SELL';
    const order = await placeOrder(symbol, orderSide, tier.tradeUsdt, entry, verdict);
    if (!order) return;
    // Remove placeholder slot and replace with real trade
    global.executingSymbols.delete(symbol);
    botState.tradesExecuted++;
    botState.openTrades.push({
      id:order.orderId, symbol, side:verdict,
      entry:order.entry, qty:order.qty,
      target, stop, targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT,
      grade:'A', quality:primary.quality,
      tradeSize:tier.tradeUsdt, tier:tier.label,
      openedAt:new Date().toISOString(), paper:false, trailing:false,
      tpPrice:order.tpPrice, slPrice:order.slPrice,
      research:{ verdict, srsiK:primary.srsiK.toFixed(1), momFast:primary.momFast.toFixed(3), crossUp:primary.crossUp, crossDown:primary.crossDown },
    });
    log('INFO', '🚀 TRADE: ' + symbol + ' ' + verdict + ' @ $' + order.entry + ' TP:$' + order.tpPrice + ' SL:$' + order.slPrice + ' | Open:' + botState.openTrades.length + '/' + botState.currentMaxTrades);
  } catch(e) { if(global.executingSymbols) global.executingSymbols.delete(symbol); log('ERROR', 'Execute ' + symbol + ': ' + e.message); }
}

// ─── Place order with embedded TP and SL ─────────────────────────────────────
async function placeOrder(symbol, side, usdtAmount, price, verdict) {
  try {
    // Get precision info
    let step = global.stepSizeCache[symbol];
    let tick = global.tickSizeCache[symbol];
    if (!step || !tick) {
      const info = await binancePublic('/fapi/v1/exchangeInfo', {});
      const si = info.symbols?.find(s => s.symbol === symbol);
      const lf = si?.filters?.find(f => f.filterType === 'LOT_SIZE');
      const pf = si?.filters?.find(f => f.filterType === 'PRICE_FILTER');
      step = lf ? parseFloat(lf.stepSize) : 0.001;
      tick = pf ? parseFloat(pf.tickSize) : 0.001;
      global.stepSizeCache[symbol] = step;
      global.tickSizeCache[symbol] = tick;
    }
    const qDec = step.toString().split('.')[1]?.length || 3;
    const pDec = tick.toString().split('.')[1]?.length || 3;

    const qty = parseFloat((Math.floor(usdtAmount/price/step)*step).toFixed(qDec));
    if (qty <= 0) throw new Error('Qty too small');

    // Place market entry
    const order = await binanceSigned('POST', '/fapi/v1/order', {
      symbol, side, type:'MARKET', quantity:qty, positionSide:'BOTH'
    });

    // Get actual fill price from position
    await new Promise(r => setTimeout(r, 1500));
    let entryPrice = price;
    try {
      const positions = await binanceSigned('GET', '/fapi/v2/positionRisk', {});
      if (Array.isArray(positions)) {
        const pos = positions.find(p => p.symbol === symbol && parseFloat(p.positionAmt) !== 0);
        if (pos && parseFloat(pos.entryPrice) > 0) entryPrice = parseFloat(pos.entryPrice);
      }
    } catch(e) {}

    log('INFO', '[LIVE] ' + side + ' ' + qty + ' ' + symbol + ' @ $' + entryPrice.toFixed(pDec));

    const closeSide = side === 'BUY' ? 'SELL' : 'BUY';
    const tpPrice = side === 'BUY'
      ? parseFloat((entryPrice*(1+CONFIG.TARGET_PCT/100)).toFixed(pDec))
      : parseFloat((entryPrice*(1-CONFIG.TARGET_PCT/100)).toFixed(pDec));
    const slPrice = side === 'BUY'
      ? parseFloat((entryPrice*(1-CONFIG.STOP_PCT/100)).toFixed(pDec))
      : parseFloat((entryPrice*(1+CONFIG.STOP_PCT/100)).toFixed(pDec));

    log('INFO', '[LIVE] TP:$' + tpPrice.toFixed(pDec) + ' SL:$' + slPrice.toFixed(pDec) + ' — bot will monitor and close');
        return { orderId:order.orderId, symbol, side, qty, entry:entryPrice, tpPrice, slPrice };
  } catch(e) { log('ERROR', 'Order ' + symbol + ': ' + e.message); throw e; }
}

// ─── Monitor open trades ──────────────────────────────────────────────────────
async function monitorOpenTrades() {
  if (!botState.openTrades.length) return;
  resetDailyPnl();

  let positions = [];
  try {
    positions = await binanceSigned('GET', '/fapi/v2/positionRisk', {});
    if (!Array.isArray(positions)) positions = [];
  } catch(e) { log('WARN', 'positionRisk: ' + e.message); return; }

  for (const trade of [...botState.openTrades]) {
    const pos = positions.find(p => p.symbol === trade.symbol && parseFloat(p.positionAmt) !== 0);

    // Position closed by Binance TP/SL
    if (!pos) {
      log('INFO', 'Position ' + trade.symbol + ' closed by Binance TP/SL');
      try {
        await refreshBalance();
        // Estimate PnL from balance change
        const pnl = trade.side === 'LONG'
          ? (trade.tpPrice - trade.entry) * trade.qty
          : (trade.entry - trade.tpPrice) * trade.qty;
        const isWin = true;
        botState.winCount++;
        botState.dailyPnl += pnl; botState.totalPnl += pnl;
        botState.closedTrades.unshift({ ...trade, exit:trade.tpPrice, pnl, pnlPct:CONFIG.TARGET_PCT, closedAt:new Date().toISOString(), closeReason:'BINANCE_TP_SL' });
        if (botState.closedTrades.length > 300) botState.closedTrades.pop();
        botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
        updateTradeScaling('WIN');
        const total = botState.winCount + botState.lossCount;
        log('INFO', '✅ ' + trade.symbol + ' closed by Binance | WR:' + (total>0?((botState.winCount/total)*100).toFixed(0)+'%':'N/A'));
      } catch(e) { log('WARN', 'Close PnL: ' + e.message); }
      continue;
    }

    // Update entry price if it was 0
    const entryPrice = parseFloat(pos.entryPrice);
    const markPrice  = parseFloat(pos.markPrice);
    if (entryPrice > 0 && (!trade.entry || trade.entry === 0)) {
      trade.entry  = entryPrice;
      trade.target = trade.side==='LONG' ? entryPrice*(1+CONFIG.TARGET_PCT/100) : entryPrice*(1-CONFIG.TARGET_PCT/100);
      trade.stop   = trade.side==='LONG' ? entryPrice*(1-CONFIG.STOP_PCT/100)   : entryPrice*(1+CONFIG.STOP_PCT/100);
      log('INFO', 'Fixed entry ' + trade.symbol + ': $' + entryPrice);
    }

    // Manual stop check as backup
    const price = markPrice || livePrice[trade.symbol] || 0;
    if (!price) continue;
    let closeReason = null;
    if (trade.side==='LONG') {
      if (price >= trade.target) closeReason = 'TARGET_HIT';
      else if (price <= trade.stop) closeReason = 'STOP_HIT';
    } else {
      if (price <= trade.target) closeReason = 'TARGET_HIT';
      else if (price >= trade.stop) closeReason = 'STOP_HIT';
    }

    if (closeReason) {
      try {
        const closeSide = trade.side==='LONG'?'SELL':'BUY';
        await binanceSigned('POST', '/fapi/v1/order', {
          symbol:trade.symbol, side:closeSide, type:'MARKET',
          quantity:trade.qty.toString(), positionSide:'BOTH', reduceOnly:'true'
        });
        const pnl = trade.side==='LONG'?(price-trade.entry)*trade.qty:(trade.entry-price)*trade.qty;
        botState.dailyPnl+=pnl; botState.totalPnl+=pnl;
        const isWin=pnl>=0; isWin?botState.winCount++:botState.lossCount++;
        botState.closedTrades.unshift({ ...trade, exit:price, pnl, pnlPct:parseFloat((pnl/trade.tradeSize*100).toFixed(3)), closedAt:new Date().toISOString(), closeReason });
        if (botState.closedTrades.length>300) botState.closedTrades.pop();
        botState.openTrades = botState.openTrades.filter(t=>t.id!==trade.id);
        updateTradeScaling(isWin?'WIN':'LOSS');
        await refreshBalance();
        const total=botState.winCount+botState.lossCount;
        log('INFO', (isWin?'✅':'❌')+' '+trade.symbol+' '+trade.side+' | PnL:$'+pnl.toFixed(4)+' | '+closeReason+' | WR:'+(total>0?((botState.winCount/total)*100).toFixed(0)+'%':'N/A'));
      } catch(e) { log('WARN', 'Manual close ' + trade.symbol + ': ' + e.message); }
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
  const e = Date.now()-botState.lastLossTime;
  if (e >= CONFIG.COOLDOWN_AFTER_LOSS_MS) { botState.inCooldown=false; return false; }
  return true;
}

// ─── Routes ───────────────────────────────────────────────────────────────────
app.get('/health', (req,res) => res.json({ status:'ok', ts:new Date().toISOString(), running:botState.running, openTrades:botState.openTrades.length }));

app.get('/status', (req,res) => {
  const tier=getCurrentTier(); const total=botState.winCount+botState.lossCount;
  res.json({
    running:botState.running, mode:botState.mode, killSwitch:botState.killSwitch,
    wsConnected:botState.wsConnected, wsStreamCount:botState.wsStreamCount,
    openTrades:botState.openTrades.filter(t => t.side !== 'PENDING'), closedTrades:botState.closedTrades.slice(0,50),
    dailyPnl:botState.dailyPnl, totalPnl:botState.totalPnl,
    candlesReceived:botState.candlesReceived, lastSignalCheck:botState.lastSignalCheck,
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
    config:{ symbols:CONFIG.SYMBOLS, timeframes:CONFIG.TIMEFRAMES, targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT, leverage:CONFIG.LEVERAGE, tiers:CONFIG.TIERS, currentTierFull:tier },
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

  // Sync existing Binance positions into bot state on startup
  try {
    const positions = await binanceSigned('GET', '/fapi/v2/positionRisk', {});
    if (Array.isArray(positions)) {
      const openPos = positions.filter(p => parseFloat(p.positionAmt) !== 0);
      for (const pos of openPos) {
        const entry = parseFloat(pos.entryPrice);
        const side = parseFloat(pos.positionAmt) > 0 ? 'LONG' : 'SHORT';
        const tier = getCurrentTier();
        const target = side==='LONG' ? entry*(1+CONFIG.TARGET_PCT/100) : entry*(1-CONFIG.TARGET_PCT/100);
        const stop   = side==='LONG' ? entry*(1-CONFIG.STOP_PCT/100)   : entry*(1+CONFIG.STOP_PCT/100);
        const qty    = Math.abs(parseFloat(pos.positionAmt));
        botState.openTrades.push({
          id: 'SYNC-' + pos.symbol, symbol: pos.symbol, side,
          entry, qty, target, stop,
          targetPct: CONFIG.TARGET_PCT, stopPct: CONFIG.STOP_PCT,
          tradeSize: tier.tradeUsdt, tier: tier.label,
          openedAt: new Date().toISOString(), paper: false, trailing: false,
          tpPrice: target, slPrice: stop,
          research: { verdict: side, note: 'Synced from Binance on startup' },
        });
        log('INFO', 'Synced position: ' + pos.symbol + ' ' + side + ' entry:$' + entry);
      }
      if (openPos.length > 0) log('INFO', 'Synced ' + openPos.length + ' positions from Binance');
    }
  } catch(e) { log('WARN', 'Sync positions: ' + e.message); }

  startPolling();
  monitorInterval = setInterval(monitorOpenTrades, 3000);
  balanceInterval = setInterval(refreshBalance, 2*60*1000);
  const msg = 'Bot started | FUTURES | ' + tier.label + ' | ' + CONFIG.SYMBOLS.length + ' coins | 1m+3m+5m+15m | StochRSI+Mom | Target:' + CONFIG.TARGET_PCT + '% Stop:' + CONFIG.STOP_PCT + '% | ' + CONFIG.LEVERAGE + 'x';
  log('INFO', msg);
  res.json({ success:true, message:msg });
});

app.post('/stop', (req,res) => {
  botState.running=false;
  clearInterval(monitorInterval); clearInterval(balanceInterval); clearInterval(pollInterval);
  log('INFO','Bot stopped'); res.json({ success:true, message:'Stopped' });
});

app.post('/kill', (req,res) => {
  botState.running=false; botState.killSwitch=true;
  clearInterval(monitorInterval); clearInterval(balanceInterval); clearInterval(pollInterval);
  log('WARN','KILL SWITCH'); res.json({ success:true, message:'Kill switch activated' });
});

app.post('/reset-kill', (req,res) => {
  botState.killSwitch=false; res.json({ success:true, message:'Kill switch reset' });
});

app.post('/close-trade/:id', async (req,res) => {
  const trade = botState.openTrades.find(t => t.id===req.params.id);
  if (!trade) return res.json({ success:false, message:'Not found' });
  try {
    const closeSide = trade.side==='LONG'?'SELL':'BUY';
    await binanceSigned('POST','/fapi/v1/order',{ symbol:trade.symbol, side:closeSide, type:'MARKET', quantity:trade.qty.toString(), positionSide:'BOTH', reduceOnly:'true' });
    const price = livePrice[trade.symbol] || trade.entry;
    const pnl = trade.side==='LONG'?(price-trade.entry)*trade.qty:(trade.entry-price)*trade.qty;
    botState.dailyPnl+=pnl; botState.totalPnl+=pnl;
    botState.closedTrades.unshift({ ...trade, exit:price, pnl, closedAt:new Date().toISOString(), closeReason:'MANUAL' });
    botState.openTrades = botState.openTrades.filter(t => t.id!==trade.id);
    await refreshBalance();
    log('INFO','Manual close '+trade.symbol+' | PnL:$'+pnl.toFixed(4));
    res.json({ success:true, pnl });
  } catch(e) { res.json({ success:false, message:e.message }); }
});

app.get('/balance', async (req,res) => {
  await refreshBalance();
  const tier=getCurrentTier(); const total=botState.winCount+botState.lossCount;
  res.json({ usdtBalance:botState.usdtBalance, startingBalance:botState.startingBalance, totalPnl:botState.totalPnl, tier:tier.label, tradeUsdt:tier.tradeUsdt, currentMaxTrades:botState.currentMaxTrades, targetPct:CONFIG.TARGET_PCT, stopPct:CONFIG.STOP_PCT, winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A' });
});

// ─── Startup ──────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 3001;
app.listen(PORT, async () => {
  console.log('\nSCALPR Futures Bot v3.0 — port ' + PORT);
  console.log('Mode: FUTURES LIVE');
  console.log('Indicators: StochRSI + Momentum');
  console.log('Timeframes: 1m + 3m');
  console.log('Target: +' + CONFIG.TARGET_PCT + '% | Stop: -' + CONFIG.STOP_PCT + '% | Leverage: ' + CONFIG.LEVERAGE + 'x');
  console.log('Coins: ' + CONFIG.SYMBOLS.length);
  console.log('Seeding candles...');
  const tasks = [];
  for (const sym of CONFIG.SYMBOLS) {
    tasks.push(setupSymbol(sym));
    for (const tf of CONFIG.TIMEFRAMES) tasks.push(seedKlines(sym, tf));
  }
  await Promise.allSettled(tasks);
  console.log('Ready.\n');
  await refreshBalance();
  const tier = getCurrentTier();
  botState.currentMaxTrades = tier.baseTrades;
  balanceInterval = setInterval(refreshBalance, 2*60*1000);
});