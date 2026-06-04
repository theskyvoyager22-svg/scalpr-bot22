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
  MAX_TRADE_USDT: parseFloat(process.env.MAX_TRADE_USDT || '10'),
  DAILY_LOSS_LIMIT: parseFloat(process.env.DAILY_LOSS_LIMIT || '20'),
  MAX_OPEN_TRADES: parseInt(process.env.MAX_OPEN_TRADES || '2'),
  SYMBOLS: (process.env.SYMBOLS || 'BTCUSDT,ETHUSDT,SOLUSDT').split(','),
  SCAN_INTERVAL_MS: parseInt(process.env.SCAN_INTERVAL_MS || '60000'),
};

const BASE = 'https://api.binance.com';

// ─── State ────────────────────────────────────────────────────────────────────
let botState = {
  running: false,
  mode: CONFIG.PAPER_MODE ? 'PAPER' : 'LIVE',
  openTrades: [],
  closedTrades: [],
  dailyPnl: 0,
  dailyPnlDate: new Date().toDateString(),
  totalPnl: 0,
  scanCount: 0,
  lastScan: null,
  log: [],
  killSwitch: false,
};
let scanInterval = null;

// ─── Logging ──────────────────────────────────────────────────────────────────
function log(level, message, data = null) {
  const entry = { ts: new Date().toISOString(), level, message, data };
  botState.log.unshift(entry);
  if (botState.log.length > 200) botState.log.pop();
  console.log(`[${level}] ${message}`, data || '');
}

// ─── Binance HTTP ─────────────────────────────────────────────────────────────
function sign(params) {
  const query = new URLSearchParams(params).toString();
  const sig = crypto.createHmac('sha256', CONFIG.API_SECRET).update(query).digest('hex');
  return query + '&signature=' + sig;
}

async function binanceSigned(method, path, params = {}) {
  params.timestamp = Date.now();
  params.recvWindow = 5000;
  const query = sign(params);
  const url = method === 'GET' ? `${BASE}${path}?${query}` : `${BASE}${path}`;
  const opts = {
    method,
    headers: { 'X-MBX-APIKEY': CONFIG.API_KEY, 'Content-Type': 'application/x-www-form-urlencoded' },
  };
  if (method !== 'GET') opts.body = query;
  const res = await fetch(url, opts);
  const json = await res.json();
  if (json.code && json.code < 0) throw new Error(`Binance error ${json.code}: ${json.msg}`);
  return json;
}

async function binancePublic(path, params = {}) {
  const query = new URLSearchParams(params).toString();
  const res = await fetch(`${BASE}${path}?${query}`);
  return res.json();
}

// ─── Market Data ──────────────────────────────────────────────────────────────
async function getKlines(symbol, interval = '1m', limit = 80) {
  return binancePublic('/api/v3/klines', { symbol, interval, limit });
}
async function getTicker(symbol) {
  return binancePublic('/api/v3/ticker/24hr', { symbol });
}
async function getOrderBook(symbol, limit = 10) {
  return binancePublic('/api/v3/depth', { symbol, limit });
}
async function getPrice(symbol) {
  const t = await binancePublic('/api/v3/ticker/price', { symbol });
  return parseFloat(t.price);
}

// ─── Technical Indicators ─────────────────────────────────────────────────────

function calcEMA(arr, period) {
  const k = 2 / (period + 1);
  let e = arr[0];
  for (let i = 1; i < arr.length; i++) e = arr[i] * k + e * (1 - k);
  return e;
}

function calcRSI(closes, period = 14) {
  let g = 0, l = 0;
  for (let i = 1; i <= period; i++) {
    const d = closes[i] - closes[i - 1];
    d > 0 ? (g += d) : (l -= d);
  }
  let ag = g / period, al = l / period;
  for (let i = period + 1; i < closes.length; i++) {
    const d = closes[i] - closes[i - 1];
    ag = (ag * (period - 1) + Math.max(d, 0)) / period;
    al = (al * (period - 1) + Math.max(-d, 0)) / period;
  }
  return al === 0 ? 100 : 100 - 100 / (1 + ag / al);
}

function calcATR(klines, period = 14) {
  const trs = [];
  for (let i = 1; i < klines.length; i++) {
    const h = +klines[i][2], l = +klines[i][3], pc = +klines[i - 1][4];
    trs.push(Math.max(h - l, Math.abs(h - pc), Math.abs(l - pc)));
  }
  return trs.slice(-period).reduce((a, b) => a + b, 0) / period;
}

function calcVWAP(klines) {
  let tv = 0, v = 0;
  for (const k of klines) {
    const tp = (+k[2] + +k[3] + +k[4]) / 3;
    tv += tp * +k[5];
    v += +k[5];
  }
  return tv / v;
}

function calcBollinger(closes, period = 20) {
  const sl = closes.slice(-period);
  const mean = sl.reduce((a, b) => a + b, 0) / period;
  const std = Math.sqrt(sl.reduce((a, b) => a + (b - mean) ** 2, 0) / period);
  return { upper: mean + 2 * std, middle: mean, lower: mean - 2 * std };
}

/**
 * Money Flow Index (MFI) — volume-weighted RSI.
 * Uses typical price × volume to measure buying vs selling pressure.
 * Overbought > 80, Oversold < 20.
 */
function calcMFI(klines, period = 14) {
  const tps = klines.map(k => (+k[2] + +k[3] + +k[4]) / 3);
  const vols = klines.map(k => +k[5]);
  let posFlow = 0, negFlow = 0;
  for (let i = klines.length - period; i < klines.length; i++) {
    const mf = tps[i] * vols[i];
    if (tps[i] > tps[i - 1]) posFlow += mf;
    else negFlow += mf;
  }
  if (negFlow === 0) return 100;
  return 100 - 100 / (1 + posFlow / negFlow);
}

/**
 * Momentum Indicator — measures rate of price change over N periods.
 * Positive = accelerating upward, Negative = accelerating downward.
 * Simple but powerful for confirming trend direction.
 */
function calcMomentum(closes, period = 10) {
  const current = closes[closes.length - 1];
  const past = closes[closes.length - 1 - period];
  return current - past;
}

/**
 * Momentum as percentage change — more interpretable across assets.
 */
function calcMomentumPct(closes, period = 10) {
  const current = closes[closes.length - 1];
  const past = closes[closes.length - 1 - period];
  return ((current - past) / past) * 100;
}

/**
 * On-Balance Volume (OBV) — cumulative volume indicator.
 * Rising OBV with price confirms trend. Divergence signals reversals.
 * Returns the latest OBV value and its trend (Rising/Falling/Flat).
 */
function calcOBV(klines) {
  let obv = 0;
  const obvSeries = [0];
  for (let i = 1; i < klines.length; i++) {
    const close = +klines[i][4];
    const prevClose = +klines[i - 1][4];
    const vol = +klines[i][5];
    if (close > prevClose) obv += vol;
    else if (close < prevClose) obv -= vol;
    obvSeries.push(obv);
  }
  // Determine OBV trend over last 10 bars using linear slope
  const recent = obvSeries.slice(-10);
  const n = recent.length;
  const sumX = n * (n - 1) / 2;
  const sumY = recent.reduce((a, b) => a + b, 0);
  const sumXY = recent.reduce((s, v, i) => s + i * v, 0);
  const sumX2 = recent.reduce((s, _, i) => s + i * i, 0);
  const slope = (n * sumXY - sumX * sumY) / (n * sumX2 - sumX * sumX);
  const trend = slope > 50000 ? 'Rising' : slope < -50000 ? 'Falling' : 'Flat';
  return { value: obv, trend, slope };
}

// ─── Research Engine (10 indicators + order book) ─────────────────────────────
function analyzeSymbol(symbol, klines, ticker, ob) {
  const closes = klines.map(k => +k[4]);
  const price = closes[closes.length - 1];
  const pct = parseFloat(ticker.priceChangePercent);

  // Existing indicators
  const rsi        = calcRSI(closes);
  const macdVal    = calcEMA(closes.slice(-26), 12) - calcEMA(closes.slice(-26), 26);
  const ema9       = calcEMA(closes.slice(-9), 9);
  const ema21      = calcEMA(closes.slice(-21), 21);
  const bb         = calcBollinger(closes);
  const vwapVal    = calcVWAP(klines);
  const atrVal     = calcATR(klines);

  // New indicators
  const mfi        = calcMFI(klines, 14);
  const momentumPct = calcMomentumPct(closes, 10);
  const obv        = calcOBV(klines);

  // Order book
  const bidLiq = ob.bids.slice(0, 5).reduce((s, b) => s + parseFloat(b[1]), 0);
  const askLiq = ob.asks.slice(0, 5).reduce((s, a) => s + parseFloat(a[1]), 0);
  const obImbalance = bidLiq / (bidLiq + askLiq);
  const bbPct = (price - bb.lower) / (bb.upper - bb.lower);

  // ── Scoring: each indicator contributes weighted points ──────────────────────
  let bull = 0, bear = 0;

  // RSI (weight 3)
  if (rsi < 30) { bull += 3; } else if (rsi > 70) { bear += 3; }
  else if (rsi < 45) { bull += 1; } else if (rsi > 55) { bear += 1; }

  // MACD (weight 2)
  if (macdVal > 0) { bull += 2; } else { bear += 2; }

  // EMA cross (weight 2)
  if (ema9 > ema21) { bull += 2; } else { bear += 2; }

  // VWAP (weight 2)
  if (price > vwapVal) { bull += 2; } else { bear += 2; }

  // Bollinger (weight 2)
  if (bbPct < 0.2) { bull += 2; } else if (bbPct > 0.8) { bear += 2; }

  // Order book imbalance (weight 2)
  if (obImbalance > 0.6) { bull += 2; } else if (obImbalance < 0.4) { bear += 2; }

  // 24h price change bias (weight 1)
  if (pct > 2) { bull += 1; } else if (pct < -2) { bear += 1; }

  // MFI — volume-weighted momentum (weight 3)
  // Oversold MFI confirms long, overbought confirms short
  if (mfi < 20) { bull += 3; }
  else if (mfi > 80) { bear += 3; }
  else if (mfi < 40) { bull += 1; }
  else if (mfi > 60) { bear += 1; }

  // Momentum (weight 2)
  // Strong positive momentum supports longs; negative supports shorts
  if (momentumPct > 0.5) { bull += 2; }
  else if (momentumPct < -0.5) { bear += 2; }
  else if (momentumPct > 0.1) { bull += 1; }
  else if (momentumPct < -0.1) { bear += 1; }

  // OBV trend (weight 2)
  // Rising OBV with price = institutional buying, supports long
  if (obv.trend === 'Rising') { bull += 2; }
  else if (obv.trend === 'Falling') { bear += 2; }

  // ── Triple-confirmation filter ────────────────────────────────────────────
  // All three new indicators must not contradict the signal for high confidence
  const mfiBullish  = mfi < 50;
  const mfiBearish  = mfi > 50;
  const momBullish  = momentumPct > 0;
  const momBearish  = momentumPct < 0;
  const obvBullish  = obv.trend === 'Rising';
  const obvBearish  = obv.trend === 'Falling';

  const newIndicatorBullScore = (mfiBullish ? 1 : 0) + (momBullish ? 1 : 0) + (obvBullish ? 1 : 0);
  const newIndicatorBearScore = (mfiBearish ? 1 : 0) + (momBearish ? 1 : 0) + (obvBearish ? 1 : 0);

  // ── Verdict ───────────────────────────────────────────────────────────────
  const diff = bull - bear;
  let verdict, confidence;

  if (diff >= 6) {
    verdict = 'LONG';
    // Boost confidence when MFI + Momentum + OBV all agree
    const boost = newIndicatorBullScore === 3 ? 8 : newIndicatorBullScore === 2 ? 4 : 0;
    confidence = Math.min(52 + bull * 2 + boost, 93);
  } else if (diff <= -6) {
    verdict = 'SHORT';
    const boost = newIndicatorBearScore === 3 ? 8 : newIndicatorBearScore === 2 ? 4 : 0;
    confidence = Math.min(52 + bear * 2 + boost, 93);
  } else {
    verdict = 'HOLD';
    confidence = 50;
  }

  // ── Price levels ──────────────────────────────────────────────────────────
  let entry, target, stop;
  if (verdict === 'LONG') {
    entry  = parseFloat(ob.asks[0][0]);
    target = entry + atrVal * 1.5;
    stop   = entry - atrVal * 0.8;
  } else if (verdict === 'SHORT') {
    entry  = parseFloat(ob.bids[0][0]);
    target = entry - atrVal * 1.5;
    stop   = entry + atrVal * 0.8;
  } else {
    entry  = price;
    target = price + atrVal;
    stop   = price - atrVal * 0.8;
  }

  const rr    = Math.abs(target - entry) / Math.abs(stop - entry);
  const grade = confidence >= 82 ? 'A' : confidence >= 70 ? 'B' : confidence >= 57 ? 'C' : 'D';

  return {
    symbol, verdict, confidence, entry, target, stop, rr, grade, price,
    // Existing
    rsi, macdVal, ema9, ema21, bb, vwapVal, atrVal, obImbalance, bbPct,
    // New
    mfi, momentumPct, obv,
    // Score breakdown
    bull, bear,
  };
}

// ─── Order Execution ──────────────────────────────────────────────────────────
async function getStepSize(symbol) {
  const info = await binancePublic('/api/v3/exchangeInfo', { symbol });
  const filters = info.symbols?.[0]?.filters || [];
  const lotFilter = filters.find(f => f.filterType === 'LOT_SIZE');
  return lotFilter ? parseFloat(lotFilter.stepSize) : 0.001;
}

function roundToStep(qty, step) {
  const decimals = step.toString().split('.')[1]?.length || 0;
  return parseFloat((Math.floor(qty / step) * step).toFixed(decimals));
}

async function placeOrder(symbol, side, usdtAmount, price) {
  if (CONFIG.PAPER_MODE) {
    const step = 0.001;
    const qty = roundToStep(usdtAmount / price, step);
    log('INFO', `[PAPER] ${side} ${qty} ${symbol} @ $${price.toFixed(4)}`);
    return { orderId: 'PAPER-' + Date.now(), symbol, side, qty, price, paper: true };
  }
  try {
    const step = await getStepSize(symbol);
    const qty = roundToStep(usdtAmount / price, step);
    const order = await binanceSigned('POST', '/api/v3/order', {
      symbol, side, type: 'MARKET', quantity: qty,
    });
    log('INFO', `[LIVE] Order placed: ${side} ${qty} ${symbol}`, order);
    return { orderId: order.orderId, symbol, side, qty, price: parseFloat(order.fills?.[0]?.price || price), paper: false };
  } catch (e) {
    log('ERROR', `Order failed for ${symbol}: ${e.message}`);
    throw e;
  }
}

// ─── Risk Management ──────────────────────────────────────────────────────────
function resetDailyPnlIfNewDay() {
  const today = new Date().toDateString();
  if (botState.dailyPnlDate !== today) {
    botState.dailyPnl = 0;
    botState.dailyPnlDate = today;
    log('INFO', 'Daily PnL reset for new day');
  }
}
function isDailyLossLimitHit() { return botState.dailyPnl <= -Math.abs(CONFIG.DAILY_LOSS_LIMIT); }
function isMaxTradesOpen()     { return botState.openTrades.length >= CONFIG.MAX_OPEN_TRADES; }
function isAlreadyTrading(sym) { return botState.openTrades.some(t => t.symbol === sym); }

// ─── Trade Monitor ────────────────────────────────────────────────────────────
async function monitorOpenTrades() {
  if (botState.openTrades.length === 0) return;
  for (const trade of [...botState.openTrades]) {
    try {
      const price = await getPrice(trade.symbol);
      let closeReason = null;
      if (trade.side === 'LONG') {
        if (price >= trade.target) closeReason = 'TARGET_HIT';
        else if (price <= trade.stop) closeReason = 'STOP_HIT';
      } else if (trade.side === 'SHORT') {
        if (price <= trade.target) closeReason = 'TARGET_HIT';
        else if (price >= trade.stop) closeReason = 'STOP_HIT';
      }
      if (closeReason) {
        const closeSide = trade.side === 'LONG' ? 'SELL' : 'BUY';
        let exitPrice = price;
        try {
          const closeOrder = await placeOrder(trade.symbol, closeSide, trade.qty * price, price);
          exitPrice = closeOrder.price;
        } catch (e) { log('ERROR', `Failed to close trade ${trade.id}: ${e.message}`); }
        const pnl = trade.side === 'LONG'
          ? (exitPrice - trade.entry) * trade.qty
          : (trade.entry - exitPrice) * trade.qty;
        botState.dailyPnl += pnl;
        botState.totalPnl += pnl;
        const closed = { ...trade, exit: exitPrice, pnl, closedAt: new Date().toISOString(), closeReason };
        botState.closedTrades.unshift(closed);
        if (botState.closedTrades.length > 100) botState.closedTrades.pop();
        botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
        log('INFO', `Trade closed: ${trade.symbol} ${trade.side} | PnL: $${pnl.toFixed(4)} | Reason: ${closeReason}`);
      }
    } catch (e) { log('WARN', `Monitor error for ${trade.symbol}: ${e.message}`); }
  }
}

// ─── Main Scan Loop ───────────────────────────────────────────────────────────
async function scan() {
  if (!botState.running || botState.killSwitch) return;
  resetDailyPnlIfNewDay();
  if (isDailyLossLimitHit()) {
    log('WARN', `Daily loss limit hit ($${botState.dailyPnl.toFixed(2)}). Trading halted for today.`);
    botState.running = false;
    return;
  }
  botState.scanCount++;
  botState.lastScan = new Date().toISOString();
  await monitorOpenTrades();
  if (isMaxTradesOpen()) {
    log('INFO', `Max open trades (${CONFIG.MAX_OPEN_TRADES}) reached. Skipping new scan.`);
    return;
  }
  for (const symbol of CONFIG.SYMBOLS) {
    if (botState.killSwitch || !botState.running) break;
    if (isAlreadyTrading(symbol)) continue;
    if (isMaxTradesOpen()) break;
    try {
      const [klines, ticker, ob] = await Promise.all([
        getKlines(symbol, '1m', 80),
        getTicker(symbol),
        getOrderBook(symbol, 10),
      ]);
      const r = analyzeSymbol(symbol, klines, ticker, ob);
      log('INFO', `Scan ${symbol}: ${r.verdict} | conf:${r.confidence}% grade:${r.grade} | RSI:${r.rsi.toFixed(1)} MFI:${r.mfi.toFixed(1)} MOM:${r.momentumPct.toFixed(2)}% OBV:${r.obv.trend}`);

      // Only trade on high-confidence A/B signals — all three new indicators must not flatly contradict
      const mfiOk  = r.verdict === 'LONG' ? r.mfi <= 75  : r.mfi >= 25;
      const momOk  = r.verdict === 'LONG' ? r.momentumPct > -1 : r.momentumPct < 1;
      const obvOk  = r.verdict === 'LONG' ? r.obv.trend !== 'Falling' : r.obv.trend !== 'Rising';
      const newIndOk = mfiOk && momOk && obvOk;

      if (r.verdict !== 'HOLD' && r.confidence >= 70 && ['A', 'B'].includes(r.grade) && newIndOk) {
        const side = r.verdict === 'LONG' ? 'BUY' : 'SELL';
        const order = await placeOrder(symbol, side, CONFIG.MAX_TRADE_USDT, r.entry);
        const trade = {
          id: order.orderId, symbol,
          side: r.verdict,
          entry: order.price,
          qty: order.qty,
          target: r.target,
          stop: r.stop,
          rr: r.rr,
          grade: r.grade,
          confidence: r.confidence,
          openedAt: new Date().toISOString(),
          paper: order.paper,
          research: {
            verdict: r.verdict,
            rsi: r.rsi.toFixed(1),
            mfi: r.mfi.toFixed(1),
            momentum: r.momentumPct.toFixed(2) + '%',
            obv: r.obv.trend,
            macd: r.macdVal > 0 ? 'Positive' : 'Negative',
            emaSignal: r.ema9 > r.ema21 ? 'Bull Cross' : 'Bear Cross',
            vwap: r.price > r.vwapVal ? 'Above' : 'Below',
            obBias: r.obImbalance > 0.55 ? 'Buy-side' : r.obImbalance < 0.45 ? 'Sell-side' : 'Balanced',
            bullScore: r.bull,
            bearScore: r.bear,
          },
        };
        botState.openTrades.push(trade);
        log('INFO', `Trade opened: ${symbol} ${r.verdict} @ $${order.price.toFixed(4)} | Target:$${r.target.toFixed(4)} Stop:$${r.stop.toFixed(4)} | MFI:${r.mfi.toFixed(1)} MOM:${r.momentumPct.toFixed(2)}% OBV:${r.obv.trend}`);
      }
      await new Promise(res => setTimeout(res, 500));
    } catch (e) { log('ERROR', `Scan error for ${symbol}: ${e.message}`); }
  }
}

// ─── API Routes ───────────────────────────────────────────────────────────────
app.get('/health', (req, res) => res.json({ status: 'ok', ts: new Date().toISOString() }));

app.get('/status', (req, res) => {
  res.json({
    running: botState.running, mode: botState.mode, killSwitch: botState.killSwitch,
    openTrades: botState.openTrades, closedTrades: botState.closedTrades.slice(0, 20),
    dailyPnl: botState.dailyPnl, totalPnl: botState.totalPnl,
    scanCount: botState.scanCount, lastScan: botState.lastScan,
    config: {
      symbols: CONFIG.SYMBOLS, maxTradeUsdt: CONFIG.MAX_TRADE_USDT,
      dailyLossLimit: CONFIG.DAILY_LOSS_LIMIT, maxOpenTrades: CONFIG.MAX_OPEN_TRADES,
      paperMode: CONFIG.PAPER_MODE, scanIntervalMs: CONFIG.SCAN_INTERVAL_MS,
    },
    log: botState.log.slice(0, 50),
  });
});

app.post('/start', (req, res) => {
  if (botState.running) return res.json({ success: false, message: 'Bot already running' });
  if (botState.killSwitch) return res.json({ success: false, message: 'Kill switch is active. Reset it first.' });
  botState.running = true;
  scan();
  scanInterval = setInterval(scan, CONFIG.SCAN_INTERVAL_MS);
  log('INFO', `Bot started in ${botState.mode} mode`);
  res.json({ success: true, message: `Bot started in ${botState.mode} mode` });
});

app.post('/stop', (req, res) => {
  botState.running = false;
  clearInterval(scanInterval);
  log('INFO', 'Bot stopped by user');
  res.json({ success: true, message: 'Bot stopped' });
});

app.post('/kill', (req, res) => {
  botState.running = false;
  botState.killSwitch = true;
  clearInterval(scanInterval);
  log('WARN', '🚨 KILL SWITCH ACTIVATED — all trading halted');
  res.json({ success: true, message: 'Kill switch activated.' });
});

app.post('/reset-kill', (req, res) => {
  botState.killSwitch = false;
  log('INFO', 'Kill switch reset');
  res.json({ success: true, message: 'Kill switch reset.' });
});

app.post('/close-trade/:id', async (req, res) => {
  const trade = botState.openTrades.find(t => t.id === req.params.id);
  if (!trade) return res.json({ success: false, message: 'Trade not found' });
  try {
    const price = await getPrice(trade.symbol);
    const closeSide = trade.side === 'LONG' ? 'SELL' : 'BUY';
    await placeOrder(trade.symbol, closeSide, trade.qty * price, price);
    const pnl = trade.side === 'LONG' ? (price - trade.entry) * trade.qty : (trade.entry - price) * trade.qty;
    botState.dailyPnl += pnl;
    botState.totalPnl += pnl;
    botState.closedTrades.unshift({ ...trade, exit: price, pnl, closedAt: new Date().toISOString(), closeReason: 'MANUAL_CLOSE' });
    botState.openTrades = botState.openTrades.filter(t => t.id !== trade.id);
    log('INFO', `Manual close: ${trade.symbol} | PnL: $${pnl.toFixed(4)}`);
    res.json({ success: true, pnl });
  } catch (e) { res.json({ success: false, message: e.message }); }
});

app.get('/market/:symbol', async (req, res) => {
  try {
    const sym = req.params.symbol.toUpperCase();
    const [klines, ticker, ob] = await Promise.all([
      getKlines(sym, '1m', 80), getTicker(sym), getOrderBook(sym, 10)
    ]);
    const research = analyzeSymbol(sym, klines, ticker, ob);
    res.json({ klines, ticker, ob, research, closes: klines.map(k => +k[4]).slice(-30) });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

app.get('/balance', async (req, res) => {
  if (CONFIG.PAPER_MODE) return res.json({ paper: true, balance: 'N/A in paper mode' });
  try {
    const account = await binanceSigned('GET', '/api/v3/account');
    const balances = account.balances.filter(b => parseFloat(b.free) > 0 || parseFloat(b.locked) > 0);
    res.json({ balances });
  } catch (e) { res.status(500).json({ error: e.message }); }
});

const PORT = process.env.PORT || 3001;
app.listen(PORT, () => {
  console.log(`SCALPR Bot Server running on port ${PORT}`);
  console.log(`Mode: ${CONFIG.PAPER_MODE ? 'PAPER TRADING' : '⚠ LIVE TRADING'}`);
  console.log(`Symbols: ${CONFIG.SYMBOLS.join(', ')}`);
  console.log(`Indicators: RSI · MACD · EMA · BB · VWAP · ATR · MFI · Momentum · OBV · OB Imbalance`);
  console.log(`Max trade: $${CONFIG.MAX_TRADE_USDT} | Daily loss limit: $${CONFIG.DAILY_LOSS_LIMIT}`);
});
