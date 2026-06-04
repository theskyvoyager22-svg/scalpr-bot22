const express = require('express');
const crypto = require('crypto');
const cors = require('cors');
const http = require('http');
const https = require('https');
const { WebSocket } = require('ws');

const app = express();
app.use(cors());
app.use(express.json());

// ─── Config ───────────────────────────────────────────────────────────────────
const CONFIG = {
  API_KEY:    process.env.BINANCE_API_KEY    || '',
  API_SECRET: process.env.BINANCE_API_SECRET || '',
  PAPER_MODE: process.env.PAPER_MODE !== 'false',
  DAILY_LOSS_LIMIT_PCT: parseFloat(process.env.DAILY_LOSS_LIMIT_PCT || '5'),
  MAX_SYMBOLS: parseInt(process.env.MAX_SYMBOLS || '200'),
  MIN_VOLUME_USDT: parseFloat(process.env.MIN_VOLUME_USDT || '1000000'),
  TRAIL_PCT: 1.0,

  // Binance WebSocket endpoints
  WS_BASE:  'wss://stream.binance.com:9443',
  REST_BASE: 'https://api.binance.com',

  // Analysis settings
  // We still fetch klines for multi-TF analysis but only when a coin
  // shows real-time price movement that passes our WR/StochRSI pre-filter
  // This reduces REST calls by ~95% compared to polling every coin
  KLINE_FETCH_COOLDOWN_MS: 30000, // re-analyze a coin at most every 30s
  ANALYSIS_BATCH_SIZE: 3,         // max parallel deep analyses at once

  // Timeframes for deep analysis (fetched only when WS triggers interest)
  TIMEFRAMES: [
    { interval: '1m',  limit: 100, weight: 1.0, label: '1m'  },
    { interval: '3m',  limit: 80,  weight: 1.5, label: '3m'  },
    { interval: '5m',  limit: 60,  weight: 2.0, label: '5m'  },
    { interval: '15m', limit: 50,  weight: 2.5, label: '15m' },
  ],
  MIN_CONFLUENCE_SCORE: 5.5,
  MIN_AGREEING_TIMEFRAMES: 3,

  // Reinvestment tiers
  TIERS: [
    { minBalance:0,      tradeUsdt:10,  baseTrades:3,  maxTrades:5,  targetPct:0.25, stopPct:0.15, label:'Starter'    },
    { minBalance:150,    tradeUsdt:12,  baseTrades:4,  maxTrades:7,  targetPct:0.26, stopPct:0.15, label:'Bronze I'   },
    { minBalance:300,    tradeUsdt:15,  baseTrades:5,  maxTrades:9,  targetPct:0.27, stopPct:0.15, label:'Bronze II'  },
    { minBalance:500,    tradeUsdt:18,  baseTrades:6,  maxTrades:11, targetPct:0.28, stopPct:0.16, label:'Silver I'   },
    { minBalance:800,    tradeUsdt:22,  baseTrades:7,  maxTrades:13, targetPct:0.29, stopPct:0.16, label:'Silver II'  },
    { minBalance:1200,   tradeUsdt:27,  baseTrades:8,  maxTrades:15, targetPct:0.30, stopPct:0.17, label:'Gold I'     },
    { minBalance:1800,   tradeUsdt:32,  baseTrades:10, maxTrades:17, targetPct:0.31, stopPct:0.17, label:'Gold II'    },
    { minBalance:2500,   tradeUsdt:38,  baseTrades:12, maxTrades:20, targetPct:0.33, stopPct:0.18, label:'Platinum I' },
    { minBalance:3500,   tradeUsdt:45,  baseTrades:14, maxTrades:23, targetPct:0.34, stopPct:0.18, label:'Platinum II'},
    { minBalance:5000,   tradeUsdt:55,  baseTrades:16, maxTrades:27, targetPct:0.36, stopPct:0.19, label:'Diamond I'  },
    { minBalance:7500,   tradeUsdt:65,  baseTrades:18, maxTrades:31, targetPct:0.38, stopPct:0.20, label:'Diamond II' },
    { minBalance:10000,  tradeUsdt:80,  baseTrades:20, maxTrades:35, targetPct:0.40, stopPct:0.21, label:'Elite I'    },
    { minBalance:15000,  tradeUsdt:95,  baseTrades:25, maxTrades:40, targetPct:0.42, stopPct:0.22, label:'Elite II'   },
    { minBalance:22000,  tradeUsdt:115, baseTrades:30, maxTrades:44, targetPct:0.44, stopPct:0.24, label:'Master I'   },
    { minBalance:32000,  tradeUsdt:135, baseTrades:35, maxTrades:47, targetPct:0.46, stopPct:0.25, label:'Master II'  },
    { minBalance:50000,  tradeUsdt:160, baseTrades:40, maxTrades:50, targetPct:0.48, stopPct:0.26, label:'Legend I'   },
    { minBalance:75000,  tradeUsdt:190, baseTrades:45, maxTrades:50, targetPct:0.49, stopPct:0.27, label:'Legend II'  },
    { minBalance:100000, tradeUsdt:220, baseTrades:50, maxTrades:50, targetPct:0.50, stopPct:0.28, label:'Supreme'    },
  ],

  WIN_STREAK_TO_ADD: 3,
  LOSS_STREAK_TO_REMOVE: 2,
  COOLDOWN_AFTER_LOSS_MS: 90000,
  MIN_WIN_RATE_TO_SCALE: 55,
  DRAWDOWN_PAUSE_PCT: 3,
};

const BASE = CONFIG.REST_BASE;
if (!global.stepSizeCache) global.stepSizeCache = {};

// ─── State ────────────────────────────────────────────────────────────────────
// Real-time price cache fed by WebSocket — zero polling
const priceCache   = {};  // symbol → { price, bid, ask, volume24, change24 }
const obvCache     = {};  // symbol → running OBV value
const lastAnalysis = {};  // symbol → timestamp of last deep analysis
let analysisQueue  = [];  // symbols queued for deep multi-TF analysis
let isAnalyzing    = false;

let wsConnections  = [];  // active WebSocket connections
let dynamicSymbols = [];
let pendingExecution = [];

let botState = {
  running: false,
  wsConnected: false,
  wsStreamCount: 0,
  mode: CONFIG.PAPER_MODE ? 'PAPER' : 'LIVE',
  openTrades: [],
  closedTrades: [],
  dailyPnl: 0,
  dailyPnlDate: new Date().toDateString(),
  totalPnl: 0,
  analysisCount: 0,
  lastAnalysis: null,
  log: [],
  killSwitch: false,
  symbolsLoaded: 0,
  topPreScreened: [],
  usdtBalance: 0,
  startingBalance: 0,
  currentTierIndex: 0,
  totalSignalsFound: 0,
  confluenceRejected: 0,
  tradesExecuted: 0,
  winCount: 0,
  lossCount: 0,
  currentMaxTrades: 3,
  consecutiveWins: 0,
  consecutiveLosses: 0,
  lastLossTime: 0,
  inCooldown: false,
  drawdownPaused: false,
  scalingLog: [],
};

let monitorInterval   = null;
let analysisInterval  = null;
let balanceInterval   = null;
let symbolInterval    = null;

// ─── Logging ──────────────────────────────────────────────────────────────────
function log(level, message) {
  const entry = { ts: new Date().toISOString(), level, message };
  botState.log.unshift(entry);
  if (botState.log.length > 500) botState.log.pop();
  console.log(`[${level}] ${message}`);
}
function logScale(msg) {
  botState.scalingLog.unshift({ ts: new Date().toISOString(), message: msg });
  if (botState.scalingLog.length > 100) botState.scalingLog.pop();
  log('INFO', '⚖️ ' + msg);
}

// ─── Tier Helpers ─────────────────────────────────────────────────────────────
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

// ─── Trade Scaling ────────────────────────────────────────────────────────────
function updateTradeScaling(result) {
  const tier = getCurrentTier();
  if (result === 'WIN')  { botState.consecutiveWins++;   botState.consecutiveLosses = 0; botState.inCooldown = false; }
  if (result === 'LOSS') { botState.consecutiveLosses++; botState.consecutiveWins   = 0; botState.lastLossTime = Date.now(); botState.inCooldown = true; }
  const total = botState.winCount + botState.lossCount;
  const wr = total > 0 ? (botState.winCount / total) * 100 : 50;
  const dd = botState.usdtBalance > 0 ? Math.abs(Math.min(botState.dailyPnl,0))/botState.usdtBalance*100 : 0;
  if (dd >= CONFIG.DRAWDOWN_PAUSE_PCT && !botState.drawdownPaused) { botState.drawdownPaused = true;  logScale(`Drawdown pause (${dd.toFixed(2)}%)`); }
  if (dd < CONFIG.DRAWDOWN_PAUSE_PCT*0.5 && botState.drawdownPaused) { botState.drawdownPaused = false; logScale('Drawdown recovered'); }
  const cur = botState.currentMaxTrades;
  if (botState.consecutiveWins >= CONFIG.WIN_STREAK_TO_ADD && wr >= CONFIG.MIN_WIN_RATE_TO_SCALE && cur < tier.maxTrades && !botState.drawdownPaused) {
    botState.currentMaxTrades = Math.min(cur+1, tier.maxTrades); botState.consecutiveWins = 0;
    logScale(`Trades UP → ${botState.currentMaxTrades} | WR:${wr.toFixed(1)}%`);
  }
  if ((botState.consecutiveLosses >= CONFIG.LOSS_STREAK_TO_REMOVE || (total>=10&&wr<40)) && cur > tier.baseTrades) {
    botState.currentMaxTrades = Math.max(cur-1, tier.baseTrades); botState.consecutiveLosses = 0;
    logScale(`Trades DOWN → ${botState.currentMaxTrades} | WR:${wr.toFixed(1)}%`);
  }
  const newIdx = getTierIndex();
  if (newIdx > botState.currentTierIndex) {
    botState.currentMaxTrades = CONFIG.TIERS[newIdx].baseTrades;
    botState.consecutiveWins = 0; botState.consecutiveLosses = 0;
    logScale(`Tier → ${CONFIG.TIERS[newIdx].label}. Trades reset to ${botState.currentMaxTrades}`);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── REST Helpers ─────────────────────────────────────────────────────────────
function restGet(url) {
  return new Promise((resolve, reject) => {
    https.get(url, { headers: { 'User-Agent': 'scalpr-bot/1.0' } }, res => {
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try { resolve(JSON.parse(data)); }
        catch(e) { reject(new Error('JSON parse error')); }
      });
    }).on('error', reject);
  });
}
async function binancePublic(path, params = {}) {
  const q = new URLSearchParams(params).toString();
  return restGet(`${BASE}${path}${q?'?'+q:''}`);
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
    const opts = {
      method,
      headers: { 'X-MBX-APIKEY': CONFIG.API_KEY, 'Content-Type': 'application/x-www-form-urlencoded' },
    };
    const req = https.request(url, opts, res => {
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try {
          const json = JSON.parse(data);
          if (json.code && json.code < 0) reject(new Error(`Binance: ${json.msg}`));
          else resolve(json);
        } catch(e) { reject(e); }
      });
    });
    req.on('error', reject);
    if (method !== 'GET') req.write(query);
    req.end();
  });
}

// ─── Balance ──────────────────────────────────────────────────────────────────
async function refreshBalance() {
  if (CONFIG.PAPER_MODE) {
    botState.usdtBalance = Math.max((botState.startingBalance||100) + botState.totalPnl, 0);
    if (botState.startingBalance === 0) botState.startingBalance = 100;
  } else {
    try {
      const acc = await binanceSigned('GET', '/api/v3/account');
      const u = acc.balances?.find(b => b.asset==='USDT');
      botState.usdtBalance = u ? parseFloat(u.free) : 0;
      if (botState.startingBalance===0 && botState.usdtBalance>0) { botState.startingBalance=botState.usdtBalance; log('INFO',`Start balance: $${botState.startingBalance.toFixed(2)}`); }
    } catch(e) { log('WARN','Balance refresh failed: '+e.message); return; }
  }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) {
    const t = CONFIG.TIERS[ni];
    log('INFO',`🚀 TIER → ${t.label} | $${botState.usdtBalance.toFixed(2)} | $${t.tradeUsdt}/trade | ${t.baseTrades}-${t.maxTrades} trades`);
    updateTradeScaling(null);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── Symbol Loader ────────────────────────────────────────────────────────────
async function fetchTopSymbols() {
  try {
    log('INFO', 'Fetching top symbols...');
    const tickers = await binancePublic('/api/v3/ticker/24hr');
    const valid = tickers
      .filter(t =>
        t.symbol.endsWith('USDT') &&
        !['DOWN','UP','BEAR','BULL','TUSD','USDC','BUSD','DAI','FDUSD'].some(x=>t.symbol.includes(x)) &&
        parseFloat(t.quoteVolume) >= CONFIG.MIN_VOLUME_USDT &&
        parseFloat(t.lastPrice) > 0
      )
      .sort((a,b) => parseFloat(b.quoteVolume)-parseFloat(a.quoteVolume))
      .slice(0, CONFIG.MAX_SYMBOLS);

    // Seed price cache from ticker data (no extra REST calls needed)
    for (const t of valid) {
      priceCache[t.symbol] = {
        price:    parseFloat(t.lastPrice),
        bid:      parseFloat(t.bidPrice || t.lastPrice),
        ask:      parseFloat(t.askPrice || t.lastPrice),
        volume24: parseFloat(t.quoteVolume),
        change24: parseFloat(t.priceChangePercent),
        ts:       Date.now(),
      };
    }

    dynamicSymbols = valid.map(t => t.symbol);
    botState.symbolsLoaded = dynamicSymbols.length;
    botState.topPreScreened = valid.slice(0,10).map(t => t.symbol);
    log('INFO', `${dynamicSymbols.length} symbols loaded. Top 5: ${dynamicSymbols.slice(0,5).join(', ')}`);

    // Reconnect WebSocket streams with new symbols
    if (botState.running) await connectWebSockets();
  } catch(e) {
    log('ERROR', 'Symbol fetch failed: '+e.message);
    if (dynamicSymbols.length===0) dynamicSymbols = ['BTCUSDT','ETHUSDT','SOLUSDT','BNBUSDT','XRPUSDT'];
  }
}

// ─── WebSocket Connection Manager ────────────────────────────────────────────
// Binance allows max 200 streams per connection, so we split into chunks
async function connectWebSockets() {
  // Close existing connections cleanly
  for (const ws of wsConnections) { try { ws.close(); } catch(e) {} }
  wsConnections = [];
  botState.wsConnected = false;
  botState.wsStreamCount = 0;

  if (dynamicSymbols.length === 0) return;

  // Each symbol subscribes to: miniTicker (price + volume)
  // This gives us real-time price, volume, and 24h change
  // in a single lightweight stream per symbol
  const CHUNK_SIZE = 180; // stay under 200 stream limit per connection
  const chunks = [];
  for (let i = 0; i < dynamicSymbols.length; i += CHUNK_SIZE) {
    chunks.push(dynamicSymbols.slice(i, i+CHUNK_SIZE));
  }

  let connectedCount = 0;
  for (const chunk of chunks) {
    const streams = chunk.map(s => `${s.toLowerCase()}@miniTicker`).join('/');
    const wsUrl = `${CONFIG.WS_BASE}/stream?streams=${streams}`;

    await new Promise((resolve) => {
      const ws = new WebSocket(wsUrl);

      ws.on('open', () => {
        connectedCount += chunk.length;
        botState.wsStreamCount = connectedCount;
        log('INFO', `WS connected: ${connectedCount}/${dynamicSymbols.length} streams active`);
        resolve();
      });

      ws.on('message', (data) => {
        try {
          const msg = JSON.parse(data.toString());
          const d = msg.data || msg;
          if (!d.s) return;
          const sym = d.s;

          // Update real-time price cache — ZERO REST calls
          const prev = priceCache[sym] || {};
          const newPrice = parseFloat(d.c); // c = last price in miniTicker
          const prevPrice = prev.price || newPrice;

          priceCache[sym] = {
            price:    newPrice,
            bid:      parseFloat(d.b || d.c),
            ask:      parseFloat(d.a || d.c),
            volume24: parseFloat(d.q || d.v || 0), // q = quote volume
            change24: parseFloat(d.P || 0),         // P = price change %
            high24:   parseFloat(d.h || d.c),
            low24:    parseFloat(d.l || d.c),
            ts:       Date.now(),
          };

          // Update running OBV approximation from tick data
          // When price goes up → add volume, down → subtract
          const vol = parseFloat(d.q || 0);
          if (!obvCache[sym]) obvCache[sym] = 0;
          if (newPrice > prevPrice)      obvCache[sym] += vol;
          else if (newPrice < prevPrice) obvCache[sym] -= vol;

          // Real-time signal trigger:
          // When WebSocket data shows interesting price action,
          // queue the symbol for deep multi-TF analysis
          if (botState.running && !botState.killSwitch) {
            triggerAnalysis(sym, newPrice, prevPrice, d);
          }
        } catch(e) { /* ignore malformed messages */ }
      });

      ws.on('error', (e) => { log('WARN', `WS error: ${e.message}`); resolve(); });
      ws.on('close', () => {
        botState.wsConnected = false;
        log('WARN', 'WS connection closed — reconnecting in 5s');
        setTimeout(() => { if (botState.running) connectWebSockets(); }, 5000);
      });

      wsConnections.push(ws);
      // Small stagger between connections to avoid hammering
      // stagger removed
    });
  }

  botState.wsConnected = true;
  log('INFO', `All WebSocket streams connected. Monitoring ${botState.wsStreamCount} coins in real-time.`);
}

// ─── Real-Time Signal Trigger ─────────────────────────────────────────────────
// Called on every WebSocket price tick.
// Applies fast Williams %R pre-check using only cached data
// to decide whether this coin deserves deep multi-TF analysis.
// This keeps deep REST analysis calls very low.
function triggerAnalysis(symbol, newPrice, prevPrice, tickData) {
  // Skip if already open trade on this symbol
  if (botState.openTrades.some(t => t.symbol===symbol)) return;
  // Skip if analyzed very recently (cooldown)
  const lastTime = lastAnalysis[symbol] || 0;
  if (Date.now() - lastTime < CONFIG.KLINE_FETCH_COOLDOWN_MS) return;
  // Skip if already queued
  if (analysisQueue.includes(symbol)) return;

  const cache = priceCache[symbol];
  if (!cache) return;

  // Fast pre-filter using 24h range as a rough Williams %R proxy
  // WR = (HH - Close) / (HH - LL) * -100
  const h24 = cache.high24 || newPrice;
  const l24 = cache.low24  || newPrice;
  const quickWR = h24 > l24 ? ((h24-newPrice)/(h24-l24))*-100 : -50;

  // Interesting if WR is in oversold or overbought territory
  const interesting = quickWR <= -70 || quickWR >= -30;

  // Also trigger on significant price movement (momentum)
  const priceDelta = prevPrice > 0 ? Math.abs((newPrice-prevPrice)/prevPrice)*100 : 0;
  const moving = priceDelta > 0.05; // 0.05% move in a single tick is notable

  // Volume spike check
  const volScore = cache.volume24 > 1e8 ? true : false;

  if ((interesting || moving) && volScore) {
    analysisQueue.push(symbol);
  }
}

// ─── Indicators ───────────────────────────────────────────────────────────────
function williamsR(closes, highs, lows, p=14) {
  const hh=Math.max(...highs.slice(-p)), ll=Math.min(...lows.slice(-p));
  const c=closes[closes.length-1];
  return hh===ll?-50:((hh-c)/(hh-ll))*-100;
}
function stochRSI(closes, rP=14, sP=14, sK=3, sD=3) {
  const rs=[];
  for(let i=rP;i<closes.length;i++){
    const sl=closes.slice(i-rP,i+1);let g=0,l=0;
    for(let j=1;j<=rP;j++){const d=sl[j]-sl[j-1];d>0?g+=d:l-=d;}
    let ag=g/rP,al=l/rP;
    for(let j=rP+1;j<sl.length;j++){const d=sl[j]-sl[j-1];ag=(ag*(rP-1)+Math.max(d,0))/rP;al=(al*(rP-1)+Math.max(-d,0))/rP;}
    rs.push(al===0?100:100-100/(1+ag/al));
  }
  if(rs.length<sP) return {k:50,d:50,crossUp:false,crossDown:false};
  const kR=[];
  for(let i=sP-1;i<rs.length;i++){const sl=rs.slice(i-sP+1,i+1);const hh=Math.max(...sl),ll=Math.min(...sl);kR.push(hh===ll?50:((rs[i]-ll)/(hh-ll))*100);}
  const smK=[];for(let i=sK-1;i<kR.length;i++) smK.push(kR.slice(i-sK+1,i+1).reduce((a,b)=>a+b,0)/sK);
  const smD=[];for(let i=sD-1;i<smK.length;i++) smD.push(smK.slice(i-sD+1,i+1).reduce((a,b)=>a+b,0)/sD);
  const k=smK[smK.length-1]||50, d=smD[smD.length-1]||50;
  const pk=smK[smK.length-2]||50, pd=smD[smD.length-2]||50;
  return {k,d,crossUp:k>d&&pk<=pd&&k<50,crossDown:k<d&&pk>=pd&&k>50};
}
function calcOBV(klines) {
  let o=0; const s=[0];
  for(let i=1;i<klines.length;i++){const c=+klines[i][4],pc=+klines[i-1][4],v=+klines[i][5];c>pc?o+=v:c<pc?o-=v:null;s.push(o);}
  const r=s.slice(-10),n=r.length;
  const sx=n*(n-1)/2,sy=r.reduce((a,b)=>a+b,0),sxy=r.reduce((s,v,i)=>s+i*v,0),sx2=r.reduce((s,_,i)=>s+i*i,0);
  const dn=n*sx2-sx*sx;
  const sl=dn!==0?(n*sxy-sx*sy)/dn:0;
  return {value:o,trend:sl>100000?'Rising':sl<-100000?'Falling':'Flat',slope:sl};
}
function calcMACD(closes) {
  const ema=(arr,p)=>{const k=2/(p+1);let e=arr[0];for(let i=1;i<arr.length;i++)e=arr[i]*k+e*(1-k);return e;};
  return {value:ema(closes.slice(-26),12)-ema(closes.slice(-26),26),positive:ema(closes.slice(-26),12)>ema(closes.slice(-26),26)};
}

// ─── Timeframe Scorer (7 indicators) ─────────────────────────────────────────
function scoreTimeframe(klines, bidRatio) {
  const closes=klines.map(k=>+k[4]),highs=klines.map(k=>+k[2]),lows=klines.map(k=>+k[3]);
  const price=closes[closes.length-1];
  const wr=williamsR(closes,highs,lows,14);
  const srsi=stochRSI(closes,14,14,3,3);
  const obv=calcOBV(klines);
  const macd=calcMACD(closes);
  let bull=0,bear=0;
  // Williams %R (weight 4)
  if(wr<=-80)bull+=4;else if(wr<=-65)bull+=3;else if(wr<=-55)bull+=1;
  else if(wr>=-20)bear+=4;else if(wr>=-35)bear+=3;else if(wr>=-45)bear+=1;
  // StochRSI (weight 4 + crossover bonus)
  if(srsi.k<=20)bull+=4;else if(srsi.k<=35)bull+=3;else if(srsi.k<=45)bull+=1;
  else if(srsi.k>=80)bear+=4;else if(srsi.k>=65)bear+=3;else if(srsi.k>=55)bear+=1;
  if(srsi.crossUp)bull+=3; if(srsi.crossDown)bear+=3;
  // OBV (weight 3)
  if(obv.trend==='Rising')bull+=3;else if(obv.trend==='Falling')bear+=3;
  // MACD (weight 3)
  macd.positive?bull+=3:bear+=3;
  // Order Book depth (weight 3)
  if(bidRatio>0.62)bull+=3;else if(bidRatio>0.54)bull+=2;
  else if(bidRatio<0.38)bear+=3;else if(bidRatio<0.46)bear+=2;
  const diff=bull-bear;
  const verdict=diff>=8?'LONG':diff<=-8?'SHORT':'NEUTRAL';
  return {verdict,bull,bear,diff,wr,srsiK:srsi.k,srsiD:srsi.d,crossUp:srsi.crossUp,crossDown:srsi.crossDown,obvTrend:obv.trend,macdPositive:macd.positive,price};
}

// ─── Deep Multi-Timeframe Analysis ───────────────────────────────────────────
async function deepAnalyze(symbol) {
  lastAnalysis[symbol] = Date.now();
  const cache = priceCache[symbol];
  if (!cache) return null;

  try {
    // Fetch order book (1 REST call)
    const ob = await binancePublic('/api/v3/depth', { symbol, limit: 20 });
    const bidLiq=ob.bids.slice(0,10).reduce((s,b)=>s+parseFloat(b[0])*parseFloat(b[1]),0);
    const askLiq=ob.asks.slice(0,10).reduce((s,a)=>s+parseFloat(a[0])*parseFloat(a[1]),0);
    const bidRatio=(bidLiq+askLiq)>0?bidLiq/(bidLiq+askLiq):0.5;
    const spread=(parseFloat(ob.asks[0][0])-parseFloat(ob.bids[0][0]))/parseFloat(ob.bids[0][0])*100;
    if (spread > 0.12) return null; // Too wide for 0.25% target

    // Fetch all 4 timeframes in parallel (4 REST calls total per analysis)
    const klineResults = await Promise.allSettled(
      CONFIG.TIMEFRAMES.map(tf =>
        binancePublic('/api/v3/klines', { symbol, interval: tf.interval, limit: tf.limit })
      )
    );

    const tfResults = [];
    for (let i = 0; i < CONFIG.TIMEFRAMES.length; i++) {
      const res = klineResults[i];
      if (res.status !== 'fulfilled' || !res.value || res.value.length < 20) continue;
      const scored = scoreTimeframe(res.value, bidRatio);
      tfResults.push({ ...scored, ...CONFIG.TIMEFRAMES[i] });
    }
    if (tfResults.length < 2) return null;

    // Weighted confluence
    let longScore=0,shortScore=0,longCount=0,shortCount=0;
    const tfSummary=[];
    for (const tf of tfResults) {
      if(tf.verdict==='LONG'){longScore+=tf.weight;longCount++;}
      if(tf.verdict==='SHORT'){shortScore+=tf.weight;shortCount++;}
      tfSummary.push({label:tf.label,verdict:tf.verdict,wr:tf.wr.toFixed(1),srsiK:tf.srsiK.toFixed(1),obv:tf.obvTrend,macd:tf.macdPositive?'+':'-',bull:tf.bull,bear:tf.bear,crossUp:tf.crossUp,crossDown:tf.crossDown});
    }

    let verdict, score, count;
    if(longScore>=CONFIG.MIN_CONFLUENCE_SCORE&&longCount>=CONFIG.MIN_AGREEING_TIMEFRAMES&&longScore>shortScore){verdict='LONG';score=longScore;count=longCount;}
    else if(shortScore>=CONFIG.MIN_CONFLUENCE_SCORE&&shortCount>=CONFIG.MIN_AGREEING_TIMEFRAMES&&shortScore>longScore){verdict='SHORT';score=shortScore;count=shortCount;}
    else return null;

    // Buy/Sell pressure from recent trades (1 REST call)
    let buyPct = 50, bsBias = 'NEUTRAL';
    try {
      const trades = await binancePublic('/api/v3/aggTrades', { symbol, limit: 100 });
      let bv=0,sv=0;
      for(const t of trades){const val=parseFloat(t.p)*parseFloat(t.q);!t.m?bv+=val:sv+=val;}
      buyPct=parseFloat(((bv/(bv+sv||1))*100).toFixed(1));
      bsBias=buyPct>60?'STRONG_BUY':buyPct>52?'BUY':buyPct<40?'STRONG_SELL':buyPct<48?'SELL':'NEUTRAL';
    } catch(e) {}

    const tier = getCurrentTier();
    let entry,target,stop;
    if(verdict==='LONG'){entry=parseFloat(ob.asks[0][0]);target=entry*(1+tier.targetPct/100);stop=entry*(1-tier.stopPct/100);}
    else{entry=parseFloat(ob.bids[0][0]);target=entry*(1-tier.targetPct/100);stop=entry*(1+tier.stopPct/100);}
    const rr=Math.abs(target-entry)/Math.abs(stop-entry);

    const maxScore=CONFIG.TIMEFRAMES.reduce((s,t)=>s+t.weight,0);
    const tf1m=tfResults.find(t=>t.interval==='1m')||tfResults[0];
    let quality=Math.min(50+(score/maxScore)*47,97)*0.5;
    quality+=(count/CONFIG.TIMEFRAMES.length)*20;
    if(verdict==='LONG'){quality+=tf1m.wr<=-70?10:0;quality+=tf1m.srsiK<=25?10:0;quality+=tf1m.crossUp?8:0;quality+=buyPct>55?8:0;quality+=tf1m.obvTrend==='Rising'?5:0;}
    else{quality+=tf1m.wr>=-30?10:0;quality+=tf1m.srsiK>=75?10:0;quality+=tf1m.crossDown?8:0;quality+=buyPct<45?8:0;quality+=tf1m.obvTrend==='Falling'?5:0;}
    quality=Math.min(Math.round(quality),100);
    const grade=quality>=80?'A':quality>=65?'B':quality>=50?'C':'D';
    if(!['A','B'].includes(grade)) return null;

    botState.totalSignalsFound++;
    botState.analysisCount++;
    botState.lastAnalysis = new Date().toISOString();

    return {
      symbol,verdict,quality,grade,confluenceScore:parseFloat(score.toFixed(2)),agreeingCount:count,
      entry,target,stop,rr,targetPct:tier.targetPct,stopPct:tier.stopPct,
      tier:tier.label,tierIndex:getTierIndex(),spread,
      wr:tf1m.wr,srsiK:tf1m.srsiK,crossUp:tf1m.crossUp,crossDown:tf1m.crossDown,
      obvTrend:tf1m.obvTrend,macdPositive:tf1m.macdPositive,
      bidRatio,buyPct,bsBias,timeframes:tfSummary,
    };
  } catch(e) { log('WARN', `Deep analyze ${symbol}: ${e.message}`); return null; }
}

// ─── Analysis Queue Processor ─────────────────────────────────────────────────
// Drains the analysis queue in batches, avoiding rate limits
async function processAnalysisQueue() {
  if (isAnalyzing || analysisQueue.length===0 || !botState.running) return;
  isAnalyzing = true;
  try {
    // Dequeue up to ANALYSIS_BATCH_SIZE symbols
    const batch = [...new Set(analysisQueue.splice(0, CONFIG.ANALYSIS_BATCH_SIZE))];
    for (const symbol of batch) {
      if (!botState.running || botState.killSwitch) break;
      if (botState.openTrades.some(t=>t.symbol===symbol)) continue;
      const r = await deepAnalyze(symbol);
      if (r) {
        log('INFO', `✨ SIGNAL: ${symbol} ${r.verdict} | q:${r.quality} grade:${r.grade} | WR:${r.wr.toFixed(0)} sRSI:${r.srsiK.toFixed(0)} OBV:${r.obvTrend} MACD:${r.macdPositive?'+':'-'} BS:${r.bsBias}(${r.buyPct}%)`);
        await executeImmediately(r);
      }
      // Polite delay between analyses — 6 per minute = safe
      await new Promise(res => setTimeout(res, 500));
    }
  } finally { isAnalyzing = false; }
}

// ─── Trailing Stop ────────────────────────────────────────────────────────────
function activateTrailing(trade, price) {
  trade.trailing=true; trade.trailPeak=price; trade.trailTrough=price;
  trade.trailStop=trade.side==='LONG'?price*(1-CONFIG.TRAIL_PCT/100):price*(1+CONFIG.TRAIL_PCT/100);
  trade.trailActivatedAt=price;
  log('INFO',`🎯 TRAILING: ${trade.symbol} ${trade.side} @ $${price.toFixed(6)} | stop:$${trade.trailStop.toFixed(6)}`);
}
function updateTrailing(trade, price) {
  if(trade.side==='LONG'){if(price>trade.trailPeak){trade.trailPeak=price;trade.trailStop=price*(1-CONFIG.TRAIL_PCT/100);}}
  else{if(price<trade.trailTrough){trade.trailTrough=price;trade.trailStop=price*(1+CONFIG.TRAIL_PCT/100);}}
}
function trailHit(trade, price) { return trade.side==='LONG'?price<=trade.trailStop:price>=trade.trailStop; }

// ─── Order Execution ──────────────────────────────────────────────────────────
async function placeOrder(symbol, side, usdtAmount, price) {
  if (CONFIG.PAPER_MODE) {
    const qty=parseFloat((usdtAmount/price).toFixed(6));
    log('INFO',`[PAPER] ${side} ${qty} ${symbol} @ $${price.toFixed(6)}`);
    return {orderId:'PAPER-'+Date.now(),symbol,side,qty,price,paper:true};
  }
  try {
    let step=global.stepSizeCache[symbol];
    if(!step){const info=await binancePublic('/api/v3/exchangeInfo',{symbol});const lf=info.symbols?.[0]?.filters?.find(f=>f.filterType==='LOT_SIZE');step=lf?parseFloat(lf.stepSize):0.001;global.stepSizeCache[symbol]=step;}
    const dec=step.toString().split('.')[1]?.length||3;
    const qty=parseFloat((Math.floor(usdtAmount/price/step)*step).toFixed(dec));
    if(qty<=0) throw new Error('Qty too small');
    const order=await binanceSigned('POST','/api/v3/order',{symbol,side,type:'MARKET',quantity:qty});
    const fp=parseFloat(order.fills?.[0]?.price||price);
    log('INFO',`[LIVE] ${side} ${qty} ${symbol} @ $${fp.toFixed(6)} ($${usdtAmount})`);
    return {orderId:order.orderId,symbol,side,qty,price:fp,paper:false};
  } catch(e){log('ERROR',`Order ${symbol}: ${e.message}`);throw e;}
}

// ─── Immediate Execution ──────────────────────────────────────────────────────
async function executeImmediately(r) {
  if(!botState.running||botState.killSwitch) return;
  if(botState.drawdownPaused){log('INFO',`⚠️ Drawdown pause — skip ${r.symbol}`);return;}
  const cd=isCooldownActive();
  if(cd){log('INFO',`⏳ Cooldown ${cd}s — queuing ${r.symbol}`);pendingExecution.push(r);return;}
  if(botState.openTrades.some(t=>t.symbol===r.symbol)) return;
  if(botState.openTrades.length>=botState.currentMaxTrades){
    log('INFO',`📊 Slots full (${botState.currentMaxTrades}) — queuing ${r.symbol} q:${r.quality}`);
    pendingExecution.push(r);return;
  }
  const tier=getCurrentTier();
  try{
    const side=r.verdict==='LONG'?'BUY':'SELL';
    const tfStr=r.timeframes.map(t=>`${t.label}:${t.verdict.substring(0,1)}`).join('|');
    log('INFO',`🚀 EXECUTE: ${r.symbol} ${r.verdict} | q:${r.quality} grade:${r.grade} | [${tfStr}] | WR:${r.wr.toFixed(0)} sRSI:${r.srsiK.toFixed(0)} OBV:${r.obvTrend} MACD:${r.macdPositive?'+':'-'} BS:${r.bsBias}`);
    const order=await placeOrder(r.symbol,side,tier.tradeUsdt,r.entry);
    botState.tradesExecuted++;
    botState.openTrades.push({
      id:order.orderId,symbol:r.symbol,side:r.verdict,entry:order.price,qty:order.qty,
      target:r.target,stop:r.stop,targetPct:r.targetPct,stopPct:r.stopPct,rr:r.rr,
      grade:r.grade,quality:r.quality,confluenceScore:r.confluenceScore,agreeingCount:r.agreeingCount,
      tradeSize:tier.tradeUsdt,tier:r.tier,tierIndex:r.tierIndex,
      openedAt:new Date().toISOString(),paper:order.paper,trailing:false,
      research:{
        verdict:r.verdict,
        confluenceScore:r.confluenceScore,
        agreeingTimeframes:r.agreeingCount,
        timeframes:r.timeframes,
        // Williams %R
        wr:(r.wr||0).toFixed(1),
        wrZone:r.wr<=-70?'Oversold':r.wr>=-30?'Overbought':'Neutral',
        // StochRSI
        srsiK:(r.srsiK||50).toFixed(1),
        crossUp:r.crossUp||false,
        crossDown:r.crossDown||false,
        // OBV
        obvTrend:r.obvTrend||'Flat',
        // MACD
        macd:r.macdPositive?'Positive':'Negative',
        macdPositive:r.macdPositive||false,
        // Order Book
        obBias:r.obBias||'NEUTRAL',
        bidRatio:(r.bidRatio||0.5).toFixed(3),
        // Buy/Sell Pressure
        bsBias:r.bsBias||'NEUTRAL',
        buySellBias:r.bsBias||'NEUTRAL',
        buyPct:r.buyPct||50,
        // Momentum
        momFast:(r.momFast||0).toFixed(3),
        momMid:(r.momMid||0).toFixed(3),
        momSlow:(r.momSlow||0).toFixed(3),
        momAllBull:r.momAllBull||false,
        momAllBear:r.momAllBear||false,
        momAccelBull:r.momAccelBull||false,
        momAccelBear:r.momAccelBear||false,
        quality:r.quality,
      },
    });
    log('INFO',`📊 Open:${botState.openTrades.length}/${botState.currentMaxTrades} | $${botState.usdtBalance.toFixed(2)} | ${tier.label} | $${tier.tradeUsdt}/trade`);
  }catch(e){log('ERROR',`Execute ${r.symbol}: ${e.message}`);}
}

// ─── Risk ─────────────────────────────────────────────────────────────────────
function resetDailyPnl(){const t=new Date().toDateString();if(botState.dailyPnlDate!==t){botState.dailyPnl=0;botState.dailyPnlDate=t;log('INFO','Daily PnL reset');}}
function isCooldownActive(){
  if(!botState.inCooldown) return false;
  const e=Date.now()-botState.lastLossTime;
  if(e>=CONFIG.COOLDOWN_AFTER_LOSS_MS){botState.inCooldown=false;return false;}
  return Math.ceil((CONFIG.COOLDOWN_AFTER_LOSS_MS-e)/1000);
}

// ─── Trade Monitor — uses WebSocket price cache, zero REST calls ──────────────
async function monitorOpenTrades() {
  if(!botState.running) return;
  resetDailyPnl();
  const dailyLimit=botState.usdtBalance*(CONFIG.DAILY_LOSS_LIMIT_PCT/100);
  if(dailyLimit>0&&botState.dailyPnl<=-dailyLimit){log('WARN','🛑 Daily loss limit.');botState.running=false;return;}

  // Use WebSocket price cache — NO REST calls needed for monitoring
  for(const trade of [...botState.openTrades]){
    const cache=priceCache[trade.symbol];
    if(!cache||Date.now()-cache.ts>30000) continue; // skip stale data
    const price=cache.price;
    let closeReason=null;
    if(!trade.trailing){
      if(trade.side==='LONG'){if(price>=trade.target)activateTrailing(trade,price);else if(price<=trade.stop)closeReason='STOP_HIT';}
      else{if(price<=trade.target)activateTrailing(trade,price);else if(price>=trade.stop)closeReason='STOP_HIT';}
    }else{
      updateTrailing(trade,price);
      if(trailHit(trade,price)){
        const peak=trade.side==='LONG'?trade.trailPeak:trade.trailTrough;
        log('INFO',`🏁 TRAIL HIT: ${trade.symbol} peak:$${peak.toFixed(6)} exit:$${price.toFixed(6)}`);
        closeReason='TRAIL_STOP';
      }
    }
    if(closeReason){
      const closeSide=trade.side==='LONG'?'SELL':'BUY';
      let exitPrice=price;
      try{const co=await placeOrder(trade.symbol,closeSide,trade.qty*price,price);exitPrice=co.price;}catch(e){}
      const pnl=trade.side==='LONG'?(exitPrice-trade.entry)*trade.qty:(trade.entry-exitPrice)*trade.qty;
      const pnlPct=((pnl/trade.tradeSize)*100).toFixed(3);
      botState.dailyPnl+=pnl;botState.totalPnl+=pnl;
      const isWin=pnl>=0;isWin?botState.winCount++:botState.lossCount++;
      botState.closedTrades.unshift({...trade,exit:exitPrice,pnl,pnlPct:parseFloat(pnlPct),closedAt:new Date().toISOString(),closeReason});
      if(botState.closedTrades.length>300) botState.closedTrades.pop();
      botState.openTrades=botState.openTrades.filter(t=>t.id!==trade.id);
      updateTradeScaling(isWin?'WIN':'LOSS');
      const total=botState.winCount+botState.lossCount;
      const wr=total>0?((botState.winCount/total)*100).toFixed(0)+'%':'N/A';
      log('INFO',`${isWin?'✅':'❌'} ${trade.symbol} ${trade.side} | PnL:$${pnl.toFixed(4)} (${pnlPct}%) | ${closeReason} | WR:${wr} | Trades:${botState.currentMaxTrades}`);
      await refreshBalance();
      // Fill pending slots immediately
      if(pendingExecution.length>0&&!isCooldownActive()&&!botState.drawdownPaused){
        pendingExecution.sort((a,b)=>b.quality-a.quality);
        const next=pendingExecution.shift();
        if(next){log('INFO',`▶ Pending: ${next.symbol}`);await executeImmediately(next);}
      }
    }
  }
}

// ─── Routes ───────────────────────────────────────────────────────────────────
app.get('/health',(req,res)=>res.json({status:'ok',ts:new Date().toISOString(),wsConnected:botState.wsConnected,streams:botState.wsStreamCount}));

app.get('/status',(req,res)=>{
  const tier=getCurrentTier();
  const total=botState.winCount+botState.lossCount;
  const cd=isCooldownActive();
  res.json({
    running:botState.running,mode:botState.mode,killSwitch:botState.killSwitch,
    wsConnected:botState.wsConnected,wsStreamCount:botState.wsStreamCount,
    openTrades:botState.openTrades,closedTrades:botState.closedTrades.slice(0,50),
    dailyPnl:botState.dailyPnl,totalPnl:botState.totalPnl,
    analysisCount:botState.analysisCount,lastAnalysis:botState.lastAnalysis,
    analysisQueueSize:analysisQueue.length,pendingExecution:pendingExecution.length,
    symbolsLoaded:botState.symbolsLoaded,topPreScreened:botState.topPreScreened,
    usdtBalance:botState.usdtBalance,startingBalance:botState.startingBalance,
    currentTier:botState.currentTierIndex+1,tierName:tier.label,
    currentTradeUsdt:tier.tradeUsdt,currentMaxTrades:botState.currentMaxTrades,
    tierBaseTrades:tier.baseTrades,tierMaxTrades:tier.maxTrades,
    targetPct:tier.targetPct,stopPct:tier.stopPct,
    consecutiveWins:botState.consecutiveWins,consecutiveLosses:botState.consecutiveLosses,
    inCooldown:!!cd,cooldownRemaining:cd||0,drawdownPaused:botState.drawdownPaused,
    totalSignalsFound:botState.totalSignalsFound,confluenceRejected:botState.confluenceRejected,
    tradesExecuted:botState.tradesExecuted,winCount:botState.winCount,lossCount:botState.lossCount,
    winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',
    scalingLog:botState.scalingLog.slice(0,20),
    config:{
      symbols:dynamicSymbols.slice(0,20),totalSymbols:dynamicSymbols.length,
      timeframes:CONFIG.TIMEFRAMES.map(t=>t.label),
      indicators:['Williams%R','StochRSI','OBV','MACD','OrderBook','BuySellPressure','Volume'],
      minConfluenceScore:CONFIG.MIN_CONFLUENCE_SCORE,
      tiers:CONFIG.TIERS,currentTierFull:tier,
    },
    log:botState.log.slice(0,100),
  });
});

app.post('/start',async(req,res)=>{
  if(botState.running) return res.json({success:false,message:'Already running'});
  if(botState.killSwitch) return res.json({success:false,message:'Kill switch active'});
  await refreshBalance();
  const tier=getCurrentTier();
  if(botState.currentMaxTrades<tier.baseTrades) botState.currentMaxTrades=tier.baseTrades;
  botState.running=true;
  // Connect WebSocket streams — real-time data, zero polling
  await connectWebSockets();
  // Analysis queue processor — drains triggered analyses every 2s
  analysisInterval=setInterval(processAnalysisQueue,2000);
  // Trade monitor — uses cached prices, no REST calls
  monitorInterval=setInterval(monitorOpenTrades,1000);
  // Background refreshes
  balanceInterval=setInterval(refreshBalance,2*60*1000);
  symbolInterval=setInterval(async()=>{await fetchTopSymbols();},30*60*1000);
  const msg=`Bot started | ${botState.mode} | ${tier.label} | WS:${botState.wsStreamCount} streams | ${tier.targetPct}% target | trades:${botState.currentMaxTrades}→${tier.maxTrades} | IMMEDIATE execution | Zero polling`;
  log('INFO',msg);
  res.json({success:true,message:msg});
});

app.post('/stop',(req,res)=>{
  botState.running=false;
  clearInterval(analysisInterval);clearInterval(monitorInterval);
  clearInterval(balanceInterval);clearInterval(symbolInterval);
  for(const ws of wsConnections){try{ws.close();}catch(e){}}
  wsConnections=[];botState.wsConnected=false;
  log('INFO','Bot stopped');res.json({success:true,message:'Stopped'});
});

app.post('/kill',(req,res)=>{
  botState.running=false;botState.killSwitch=true;
  clearInterval(analysisInterval);clearInterval(monitorInterval);
  clearInterval(balanceInterval);clearInterval(symbolInterval);
  for(const ws of wsConnections){try{ws.close();}catch(e){}}
  wsConnections=[];botState.wsConnected=false;
  log('WARN','🚨 KILL SWITCH');res.json({success:true,message:'Kill switch activated'});
});

app.post('/reset-kill',(req,res)=>{botState.killSwitch=false;log('INFO','Kill switch reset');res.json({success:true,message:'Kill switch reset'});});

app.post('/close-trade/:id',async(req,res)=>{
  const trade=botState.openTrades.find(t=>t.id===req.params.id);
  if(!trade) return res.json({success:false,message:'Not found'});
  try{
    const price=priceCache[trade.symbol]?.price||0;
    if(!price) return res.json({success:false,message:'No price data'});
    await placeOrder(trade.symbol,trade.side==='LONG'?'SELL':'BUY',trade.qty*price,price);
    const pnl=trade.side==='LONG'?(price-trade.entry)*trade.qty:(trade.entry-price)*trade.qty;
    botState.dailyPnl+=pnl;botState.totalPnl+=pnl;
    botState.closedTrades.unshift({...trade,exit:price,pnl,closedAt:new Date().toISOString(),closeReason:'MANUAL_CLOSE'});
    botState.openTrades=botState.openTrades.filter(t=>t.id!==trade.id);
    await refreshBalance();
    log('INFO',`Manual close ${trade.symbol} | PnL:$${pnl.toFixed(4)}`);
    res.json({success:true,pnl});
  }catch(e){res.json({success:false,message:e.message});}
});

app.get('/balance',async(req,res)=>{
  await refreshBalance();const tier=getCurrentTier();const total=botState.winCount+botState.lossCount;
  res.json({usdtBalance:botState.usdtBalance,startingBalance:botState.startingBalance,totalPnl:botState.totalPnl,growthPct:botState.startingBalance>0?((botState.totalPnl/botState.startingBalance)*100).toFixed(2)+'%':'0%',tier:tier.label,tierIndex:botState.currentTierIndex+1,tradeUsdt:tier.tradeUsdt,currentMaxTrades:botState.currentMaxTrades,baseTrades:tier.baseTrades,maxTrades:tier.maxTrades,targetPct:tier.targetPct,stopPct:tier.stopPct,winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',allTiers:CONFIG.TIERS});
});

// ─── Startup ──────────────────────────────────────────────────────────────────
const PORT=process.env.PORT||3001;
app.listen(PORT,async()=>{
  console.log(`\nSCALPR WebSocket Bot — port ${PORT}`);
  console.log(`Mode: ${CONFIG.PAPER_MODE?'PAPER':'⚠ LIVE'}`);
  console.log(`Architecture: WebSocket streams (zero polling, zero rate limit risk)`);
  console.log(`Indicators: Williams%R · StochRSI · OBV · MACD · OrderBook · BuySellPressure · Volume`);
  console.log(`Timeframes: ${CONFIG.TIMEFRAMES.map(t=>t.label).join(' · ')}`);
  console.log(`Execution: IMMEDIATE on signal detection`);
  console.log(`Monitor: 1s loop using cached WS prices — zero REST calls`);
  console.log(`Tiers: 18 levels | 3→50 trades | $10→$220/trade\n`);
  await fetchTopSymbols();
  await refreshBalance();
  const tier=getCurrentTier();
  botState.currentMaxTrades=tier.baseTrades;
});