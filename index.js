const express = require('express');
const crypto  = require('crypto');
const cors    = require('cors');
const https   = require('https');
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

  // ── Market cap filter ─────────────────────────────────────────────────────
  // Only trade coins with 24h quote volume between 20M and 200M USDT.
  // This targets mid-cap altcoins in active downtrend rallies —
  // liquid enough for tight spreads but not so large they move slowly.
  MIN_VOLUME_USDT: parseFloat(process.env.MIN_VOLUME_USDT || '20000000'),
  MAX_VOLUME_USDT: parseFloat(process.env.MAX_VOLUME_USDT || '200000000'),
  MAX_SYMBOLS: parseInt(process.env.MAX_SYMBOLS || '150'),

  // ── WebSocket endpoints ───────────────────────────────────────────────────
  WS_BASE:   process.env.WS_BASE   || 'wss://stream.binance.com:443',
  REST_BASE: process.env.BINANCE_BASE || 'https://api1.binance.com',
  TRAIL_PCT: 1.0,

  // ── Speed settings ────────────────────────────────────────────────────────
  // Cooldown between re-analyzing same coin (ms)
  KLINE_FETCH_COOLDOWN_MS: 15000,
  // Max parallel deep analyses at once — higher = faster but more API calls
  ANALYSIS_BATCH_SIZE: 6,
  // How often analysis queue is drained (ms)
  ANALYSIS_INTERVAL_MS: 500,
  // Monitor interval — checks stops/targets using WS cache
  MONITOR_INTERVAL_MS: 800,

  // ── Timeframes: 1m, 3m, 5m ONLY ─────────────────────────────────────────
  TIMEFRAMES: [
    { interval: '1m', limit: 80, weight: 1.0, label: '1m' },
    { interval: '3m', limit: 60, weight: 1.5, label: '3m' },
    { interval: '5m', limit: 50, weight: 2.0, label: '5m' },
  ],
  // Max total weight = 4.5. Require 3.5 = all 3 TF must broadly agree
  MIN_CONFLUENCE_SCORE: 3.5,
  MIN_AGREEING_TIMEFRAMES: 2,

  // ── Profit targets & stop loss ────────────────────────────────────────────
  // ALL tiers use 1% target and 0.5% stop loss as specified
  TARGET_PCT: 1.0,
  STOP_PCT:   0.5,

  // ── Downtrend rally filter ─────────────────────────────────────────────
  // Only trade coins that are in a downtrend (24h change negative)
  // and showing a short-term bounce signal (Williams %R oversold).
  // This catches the highest-probability reversals.
  REQUIRE_DOWNTREND: true,
  MIN_DOWNTREND_PCT: -1.0,  // 24h price change must be at least -1%

  // ── Reinvestment tiers (all use TARGET_PCT / STOP_PCT above) ─────────────
  TIERS: [
    { minBalance:0,      tradeUsdt:10,  baseTrades:3,  maxTrades:5,  label:'Starter'    },
    { minBalance:150,    tradeUsdt:12,  baseTrades:4,  maxTrades:7,  label:'Bronze I'   },
    { minBalance:300,    tradeUsdt:15,  baseTrades:5,  maxTrades:9,  label:'Bronze II'  },
    { minBalance:500,    tradeUsdt:18,  baseTrades:6,  maxTrades:11, label:'Silver I'   },
    { minBalance:800,    tradeUsdt:22,  baseTrades:7,  maxTrades:13, label:'Silver II'  },
    { minBalance:1200,   tradeUsdt:27,  baseTrades:8,  maxTrades:15, label:'Gold I'     },
    { minBalance:1800,   tradeUsdt:32,  baseTrades:10, maxTrades:17, label:'Gold II'    },
    { minBalance:2500,   tradeUsdt:38,  baseTrades:12, maxTrades:20, label:'Platinum I' },
    { minBalance:3500,   tradeUsdt:45,  baseTrades:14, maxTrades:23, label:'Platinum II'},
    { minBalance:5000,   tradeUsdt:55,  baseTrades:16, maxTrades:27, label:'Diamond I'  },
    { minBalance:7500,   tradeUsdt:65,  baseTrades:18, maxTrades:31, label:'Diamond II' },
    { minBalance:10000,  tradeUsdt:80,  baseTrades:20, maxTrades:35, label:'Elite I'    },
    { minBalance:15000,  tradeUsdt:95,  baseTrades:25, maxTrades:40, label:'Elite II'   },
    { minBalance:22000,  tradeUsdt:115, baseTrades:30, maxTrades:44, label:'Master I'   },
    { minBalance:32000,  tradeUsdt:135, baseTrades:35, maxTrades:47, label:'Master II'  },
    { minBalance:50000,  tradeUsdt:160, baseTrades:40, maxTrades:50, label:'Legend I'   },
    { minBalance:75000,  tradeUsdt:190, baseTrades:45, maxTrades:50, label:'Legend II'  },
    { minBalance:100000, tradeUsdt:220, baseTrades:50, maxTrades:50, label:'Supreme'    },
  ],

  WIN_STREAK_TO_ADD:      3,
  LOSS_STREAK_TO_REMOVE:  2,
  COOLDOWN_AFTER_LOSS_MS: 60000,
  MIN_WIN_RATE_TO_SCALE:  55,
  DRAWDOWN_PAUSE_PCT:     3,
};

const BASE = CONFIG.REST_BASE;
if (!global.stepSizeCache) global.stepSizeCache = {};

// ─── Real-time state ──────────────────────────────────────────────────────────
const priceCache   = {};   // symbol → live tick data from WS
const obvCache     = {};   // symbol → running OBV
const lastAnalysis = {};   // symbol → last analysis timestamp
let   analysisQueue = [];  // triggered symbols awaiting deep analysis
let   isAnalyzing   = false;
let   wsConnections = [];
let   dynamicSymbols = [];

// Continuous execution queue — signals stack here and fire immediately
// as slots open up, with no waiting for scan cycles
let executionQueue = [];   // sorted by quality desc
let pendingExecution = []; // alias for compat

let botState = {
  running: false, wsConnected: false, wsStreamCount: 0,
  mode: CONFIG.PAPER_MODE ? 'PAPER' : 'LIVE',
  openTrades: [], closedTrades: [],
  dailyPnl: 0, dailyPnlDate: new Date().toDateString(), totalPnl: 0,
  analysisCount: 0, lastAnalysis: null, log: [], killSwitch: false,
  symbolsLoaded: 0, topPreScreened: [],
  usdtBalance: 0, startingBalance: 0, currentTierIndex: 0,
  totalSignalsFound: 0, confluenceRejected: 0, downTrendRejected: 0,
  tradesExecuted: 0, winCount: 0, lossCount: 0,
  currentMaxTrades: 3,
  consecutiveWins: 0, consecutiveLosses: 0,
  lastLossTime: 0, inCooldown: false, drawdownPaused: false,
  scalingLog: [], executionQueueSize: 0,
};

let monitorInterval  = null;
let analysisInterval = null;
let balanceInterval  = null;
let symbolInterval   = null;
let execInterval     = null;

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

// ─── Dynamic Trade Scaling ────────────────────────────────────────────────────
function updateTradeScaling(result) {
  const tier = getCurrentTier();
  if (result === 'WIN')  { botState.consecutiveWins++;   botState.consecutiveLosses = 0; botState.inCooldown = false; }
  if (result === 'LOSS') { botState.consecutiveLosses++; botState.consecutiveWins   = 0; botState.lastLossTime = Date.now(); botState.inCooldown = true; }
  const total = botState.winCount + botState.lossCount;
  const wr = total > 0 ? (botState.winCount / total) * 100 : 50;
  const dd = botState.usdtBalance > 0 ? Math.abs(Math.min(botState.dailyPnl,0))/botState.usdtBalance*100 : 0;
  if (dd >= CONFIG.DRAWDOWN_PAUSE_PCT && !botState.drawdownPaused) { botState.drawdownPaused = true; logScale(`Drawdown pause (${dd.toFixed(2)}%)`); }
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
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) {
    botState.currentMaxTrades = CONFIG.TIERS[ni].baseTrades;
    botState.consecutiveWins = 0; botState.consecutiveLosses = 0;
    logScale(`Tier → ${CONFIG.TIERS[ni].label}. Trades reset to ${botState.currentMaxTrades}`);
  }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── REST Helpers ─────────────────────────────────────────────────────────────
function restGet(url) {
  return new Promise((resolve, reject) => {
    https.get(url, { headers:{'User-Agent':'scalpr/2.0'} }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch(e) { reject(e); } });
    }).on('error', reject);
  });
}
async function binancePublic(path, params={}) {
  const q = new URLSearchParams(params).toString();
  return restGet(`${BASE}${path}${q?'?'+q:''}`);
}
function sign(params) {
  const q = new URLSearchParams(params).toString();
  return q + '&signature=' + crypto.createHmac('sha256', CONFIG.API_SECRET).update(q).digest('hex');
}
async function binanceSigned(method, path, params={}) {
  params.timestamp = Date.now(); params.recvWindow = 5000;
  const query = sign(params);
  const url = method==='GET' ? `${BASE}${path}?${query}` : `${BASE}${path}`;
  return new Promise((resolve, reject) => {
    const opts = { method, headers:{'X-MBX-APIKEY':CONFIG.API_KEY,'Content-Type':'application/x-www-form-urlencoded'} };
    const req = https.request(url, opts, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => {
        try { const j=JSON.parse(d); if(j.code&&j.code<0) reject(new Error(j.msg)); else resolve(j); }
        catch(e) { reject(e); }
      });
    });
    req.on('error', reject);
    if (method!=='GET') req.write(query);
    req.end();
  });
}

// ─── Balance ──────────────────────────────────────────────────────────────────
async function refreshBalance() {
  if (CONFIG.PAPER_MODE) {
    botState.usdtBalance = Math.max((botState.startingBalance||100)+botState.totalPnl,0);
    if (!botState.startingBalance) botState.startingBalance = 100;
  } else {
    try {
      const acc = await binanceSigned('GET','/api/v3/account');
      const u = acc.balances?.find(b=>b.asset==='USDT');
      botState.usdtBalance = u ? parseFloat(u.free) : 0;
      if (!botState.startingBalance && botState.usdtBalance>0) { botState.startingBalance=botState.usdtBalance; log('INFO',`Start: $${botState.startingBalance.toFixed(2)}`); }
    } catch(e) { log('WARN','Balance fail: '+e.message); return; }
  }
  const ni = getTierIndex();
  if (ni > botState.currentTierIndex) { updateTradeScaling(null); }
  botState.currentTierIndex = getTierIndex();
  const ct = getCurrentTier();
  if (botState.currentMaxTrades < ct.baseTrades) botState.currentMaxTrades = ct.baseTrades;
  if (botState.currentMaxTrades > ct.maxTrades)  botState.currentMaxTrades = ct.maxTrades;
}

// ─── Symbol Loader ────────────────────────────────────────────────────────────
// Loads coins in 20M–200M volume range that are in a downtrend (negative 24h)
async function fetchTopSymbols() {
  try {
    log('INFO','Fetching mid-cap downtrend coins (20M–200M vol)...');
    const raw = await binancePublic('/api/v3/ticker/24hr');
    const arr = Array.isArray(raw) ? raw : Object.values(raw||{});
    if (!arr.length) { log('WARN','Empty ticker — using fallback'); useFallback(); return; }

    const valid = arr.filter(t =>
      t.symbol.endsWith('USDT') &&
      !['DOWN','UP','BEAR','BULL','TUSD','USDC','BUSD','DAI','FDUSD'].some(x=>t.symbol.includes(x)) &&
      parseFloat(t.quoteVolume) >= CONFIG.MIN_VOLUME_USDT &&
      parseFloat(t.quoteVolume) <= CONFIG.MAX_VOLUME_USDT &&
      parseFloat(t.lastPrice) > 0 &&
      // Downtrend filter: 24h change negative = coin is in a downtrend
      parseFloat(t.priceChangePercent) <= CONFIG.MIN_DOWNTREND_PCT
    );

    // Sort by most negative 24h change — deepest downtrends first
    // These have the highest probability of a short-term bounce/reversal
    valid.sort((a,b) => parseFloat(a.priceChangePercent)-parseFloat(b.priceChangePercent));
    const top = valid.slice(0, CONFIG.MAX_SYMBOLS);

    // Seed price cache
    for (const t of top) {
      priceCache[t.symbol] = {
        price: parseFloat(t.lastPrice), bid: parseFloat(t.bidPrice||t.lastPrice),
        ask: parseFloat(t.askPrice||t.lastPrice), volume24: parseFloat(t.quoteVolume),
        change24: parseFloat(t.priceChangePercent),
        high24: parseFloat(t.highPrice), low24: parseFloat(t.lowPrice), ts: Date.now(),
      };
    }

    dynamicSymbols = top.map(t=>t.symbol);
    botState.symbolsLoaded = dynamicSymbols.length;
    botState.topPreScreened = top.slice(0,10).map(t=>`${t.symbol}(${parseFloat(t.priceChangePercent).toFixed(1)}%)`);
    log('INFO',`${dynamicSymbols.length} coins loaded | Top downtrends: ${botState.topPreScreened.join(', ')}`);
    if (botState.running) await connectWebSockets();
  } catch(e) {
    log('ERROR','Symbol fetch failed: '+e.message);
    useFallback();
  }
}
function useFallback() {
  dynamicSymbols = ['SOLUSDT','ADAUSDT','DOGEUSDT','XRPUSDT','MATICUSDT','DOTUSDT','LINKUSDT','AVAXUSDT','ATOMUSDT','LTCUSDT','ETCUSDT','XLMUSDT','ALGOUSDT','VETUSDT','FILUSDT','TRXUSDT','NEARUSDT','FTMUSDT','SANDUSDT','MANAUSDT'];
  botState.symbolsLoaded = dynamicSymbols.length;
  log('INFO','Using fallback symbols: '+dynamicSymbols.length);
}

// ─── WebSocket Manager ────────────────────────────────────────────────────────
async function connectWebSockets() {
  for (const ws of wsConnections) { try { ws.close(); } catch(e){} }
  wsConnections = []; botState.wsConnected = false; botState.wsStreamCount = 0;
  if (!dynamicSymbols.length) return;
  const CHUNK = 150;
  let connected = 0;
  for (let ci = 0; ci < dynamicSymbols.length; ci += CHUNK) {
    const chunk = dynamicSymbols.slice(ci, ci+CHUNK);
    const streams = chunk.map(s=>`${s.toLowerCase()}@miniTicker`).join('/');
    const ws = new WebSocket(`${CONFIG.WS_BASE}/stream?streams=${streams}`);
    ws.on('open', () => { connected += chunk.length; botState.wsStreamCount = connected; });
    ws.on('message', data => {
      try {
        const msg = JSON.parse(data.toString());
        const d = msg.data || msg;
        if (!d.s) return;
        const sym = d.s;
        const newPrice = parseFloat(d.c);
        const prev = priceCache[sym]||{};
        priceCache[sym] = {
          price: newPrice, bid: parseFloat(d.b||d.c), ask: parseFloat(d.a||d.c),
          volume24: parseFloat(d.q||d.v||0), change24: parseFloat(d.P||0),
          high24: parseFloat(d.h||d.c), low24: parseFloat(d.l||d.c), ts: Date.now(),
        };
        // Update OBV
        if (!obvCache[sym]) obvCache[sym] = 0;
        const vol = parseFloat(d.q||0);
        if (newPrice > (prev.price||newPrice)) obvCache[sym] += vol;
        else if (newPrice < (prev.price||newPrice)) obvCache[sym] -= vol;
        // Trigger analysis when coin looks interesting
        if (botState.running && !botState.killSwitch) triggerAnalysis(sym, newPrice, prev.price||newPrice, d);
      } catch(e){}
    });
    ws.on('error', e => log('WARN',`WS error: ${e.message}`));
    ws.on('close', () => {
      botState.wsConnected = false;
      if (botState.running) setTimeout(()=>connectWebSockets(), 5000);
    });
    wsConnections.push(ws);
  }
  botState.wsConnected = true;
  log('INFO',`WS connected: ${botState.wsStreamCount} streams`);
}

// ─── Real-Time Trigger ────────────────────────────────────────────────────────
function triggerAnalysis(sym, newPrice, prevPrice, d) {
  if (botState.openTrades.some(t=>t.symbol===sym)) return;
  const now = Date.now();
  if (now - (lastAnalysis[sym]||0) < CONFIG.KLINE_FETCH_COOLDOWN_MS) return;
  if (analysisQueue.includes(sym)) return;
  const cache = priceCache[sym]; if (!cache) return;

  // Only analyze coins still in downtrend (change24 negative)
  if (CONFIG.REQUIRE_DOWNTREND && cache.change24 > -0.5) return;

  // Quick Williams %R using 24h range
  const h = cache.high24||newPrice, l = cache.low24||newPrice;
  const quickWR = h>l ? ((h-newPrice)/(h-l))*-100 : -50;

  // Trigger when: deeply oversold (potential bounce) OR significant tick move
  const oversold = quickWR <= -70;
  const pctMove  = prevPrice>0 ? Math.abs((newPrice-prevPrice)/prevPrice)*100 : 0;
  const moving   = pctMove > 0.03;

  if (oversold || moving) analysisQueue.push(sym);
}

// ─── Indicators ───────────────────────────────────────────────────────────────
function williamsR(c,h,l,p=14) {
  const hh=Math.max(...h.slice(-p)),ll=Math.min(...l.slice(-p));
  return hh===ll?-50:((hh-c[c.length-1])/(hh-ll))*-100;
}
function stochRSI(closes,rP=14,sP=14,sK=3,sD=3) {
  const rs=[];
  for(let i=rP;i<closes.length;i++){
    const sl=closes.slice(i-rP,i+1);let g=0,l=0;
    for(let j=1;j<=rP;j++){const d=sl[j]-sl[j-1];d>0?g+=d:l-=d;}
    let ag=g/rP,al=l/rP;
    rs.push(al===0?100:100-100/(1+ag/al));
  }
  if(rs.length<sP) return{k:50,d:50,crossUp:false,crossDown:false};
  const kR=[];
  for(let i=sP-1;i<rs.length;i++){const sl=rs.slice(i-sP+1,i+1);const hh=Math.max(...sl),ll=Math.min(...sl);kR.push(hh===ll?50:((rs[i]-ll)/(hh-ll))*100);}
  const smK=[];for(let i=sK-1;i<kR.length;i++) smK.push(kR.slice(i-sK+1,i+1).reduce((a,b)=>a+b,0)/sK);
  const smD=[];for(let i=sD-1;i<smK.length;i++) smD.push(smK.slice(i-sD+1,i+1).reduce((a,b)=>a+b,0)/sD);
  const k=smK[smK.length-1]||50,d=smD[smD.length-1]||50;
  const pk=smK[smK.length-2]||50,pd=smD[smD.length-2]||50;
  return{k,d,crossUp:k>d&&pk<=pd&&k<50,crossDown:k<d&&pk>=pd&&k>50};
}
function calcOBV(klines) {
  let o=0;const s=[0];
  for(let i=1;i<klines.length;i++){const c=+klines[i][4],pc=+klines[i-1][4],v=+klines[i][5];c>pc?o+=v:c<pc?o-=v:null;s.push(o);}
  const r=s.slice(-8),n=r.length;
  const sx=n*(n-1)/2,sy=r.reduce((a,b)=>a+b,0),sxy=r.reduce((s,v,i)=>s+i*v,0),sx2=r.reduce((s,_,i)=>s+i*i,0);
  const dn=n*sx2-sx*sx,sl=dn?((n*sxy-sx*sy)/dn):0;
  return{value:o,trend:sl>50000?'Rising':sl<-50000?'Falling':'Flat',slope:sl};
}
function calcMACD(closes) {
  const ema=(arr,p)=>{const k=2/(p+1);let e=arr[0];for(let i=1;i<arr.length;i++)e=arr[i]*k+e*(1-k);return e;};
  return{value:ema(closes.slice(-26),12)-ema(closes.slice(-26),26),positive:ema(closes.slice(-26),12)>ema(closes.slice(-26),26)};
}
function calcMomentum(closes) {
  const fast=closes.length>5?(closes[closes.length-1]-closes[closes.length-6])/closes[closes.length-6]*100:0;
  const mid =closes.length>10?(closes[closes.length-1]-closes[closes.length-11])/closes[closes.length-11]*100:0;
  const slow=closes.length>20?(closes[closes.length-1]-closes[closes.length-21])/closes[closes.length-21]*100:0;
  const allBull=fast>0&&mid>0&&slow>0;
  const allBear=fast<0&&mid<0&&slow<0;
  const accelBull=fast>mid&&mid>slow&&fast>0;
  const accelBear=fast<mid&&mid<slow&&fast<0;
  return{fast,mid,slow,allBull,allBear,accelBull,accelBear};
}

// ─── Timeframe Scorer (1m/3m/5m, downtrend-focused) ──────────────────────────
function scoreTimeframe(klines, bidRatio) {
  const c=klines.map(k=>+k[4]),h=klines.map(k=>+k[2]),l=klines.map(k=>+k[3]);
  const wr   = williamsR(c,h,l,14);
  const srsi = stochRSI(c,14,14,3,3);
  const obv  = calcOBV(klines);
  const macd = calcMACD(c);
  const mom  = calcMomentum(c);
  let bull=0,bear=0;
  // Williams %R (weight 4)
  if(wr<=-80)bull+=4;else if(wr<=-65)bull+=3;else if(wr<=-55)bull+=1;
  else if(wr>=-20)bear+=4;else if(wr>=-35)bear+=3;else if(wr>=-45)bear+=1;
  // StochRSI (weight 4 + crossover)
  if(srsi.k<=20)bull+=4;else if(srsi.k<=35)bull+=3;else if(srsi.k<=45)bull+=1;
  else if(srsi.k>=80)bear+=4;else if(srsi.k>=65)bear+=3;else if(srsi.k>=55)bear+=1;
  if(srsi.crossUp)bull+=3; if(srsi.crossDown)bear+=3;
  // OBV (weight 3)
  if(obv.trend==='Rising')bull+=3;else if(obv.trend==='Falling')bear+=3;
  // MACD (weight 3)
  macd.positive?bull+=3:bear+=3;
  // Order Book (weight 3)
  if(bidRatio>0.62)bull+=3;else if(bidRatio>0.54)bull+=2;
  else if(bidRatio<0.38)bear+=3;else if(bidRatio<0.46)bear+=2;
  // Momentum (weight 4 + accel bonus)
  if(mom.allBull)bull+=4;else if(mom.fast>0&&mom.mid>0)bull+=2;else if(mom.fast>0)bull+=1;
  if(mom.allBear)bear+=4;else if(mom.fast<0&&mom.mid<0)bear+=2;else if(mom.fast<0)bear+=1;
  if(mom.accelBull)bull+=3; if(mom.accelBear)bear+=3;
  // Contradiction penalty
  let finalBull=bull,finalBear=bear;
  if(mom.allBear&&bull>bear) finalBull=Math.floor(bull*0.7);
  if(mom.allBull&&bear>bull) finalBear=Math.floor(bear*0.7);
  const diff=finalBull-finalBear;
  const verdict=diff>=10?'LONG':diff<=-10?'SHORT':'NEUTRAL';
  return{verdict,bull:finalBull,bear:finalBear,diff,wr,srsiK:srsi.k,srsiD:srsi.d,
    crossUp:srsi.crossUp,crossDown:srsi.crossDown,obvTrend:obv.trend,
    macdPositive:macd.positive,momFast:mom.fast,momMid:mom.mid,
    momAllBull:mom.allBull,momAllBear:mom.allBear,
    momAccelBull:mom.accelBull,momAccelBear:mom.accelBear};
}

// ─── Deep Multi-TF Analysis (1m+3m+5m) ───────────────────────────────────────
async function deepAnalyze(symbol) {
  lastAnalysis[symbol] = Date.now();
  const cache = priceCache[symbol]; if(!cache) return null;

  // Hard downtrend check — skip if coin not in downtrend
  if (CONFIG.REQUIRE_DOWNTREND && cache.change24 > 0) {
    botState.downTrendRejected++;
    return null;
  }

  try {
    const ob = await binancePublic('/api/v3/depth',{symbol,limit:20});
    const bidLiq=ob.bids.slice(0,10).reduce((s,b)=>s+parseFloat(b[0])*parseFloat(b[1]),0);
    const askLiq=ob.asks.slice(0,10).reduce((s,a)=>s+parseFloat(a[0])*parseFloat(a[1]),0);
    const bidRatio=(bidLiq+askLiq)>0?bidLiq/(bidLiq+askLiq):0.5;
    const spread=(parseFloat(ob.asks[0][0])-parseFloat(ob.bids[0][0]))/parseFloat(ob.bids[0][0])*100;
    if(spread>0.15) return null;

    // Fetch 1m, 3m, 5m in parallel
    const klineResults = await Promise.allSettled(
      CONFIG.TIMEFRAMES.map(tf => binancePublic('/api/v3/klines',{symbol,interval:tf.interval,limit:tf.limit}))
    );

    const tfResults=[];
    for(let i=0;i<CONFIG.TIMEFRAMES.length;i++){
      const res=klineResults[i];
      if(res.status!=='fulfilled'||!res.value||res.value.length<15) continue;
      const scored=scoreTimeframe(res.value,bidRatio);
      tfResults.push({...scored,...CONFIG.TIMEFRAMES[i]});
    }
    if(tfResults.length<2) return null;

    // Weighted confluence across 1m+3m+5m
    let longScore=0,shortScore=0,longCount=0,shortCount=0;
    const tfSummary=[];
    for(const tf of tfResults){
      if(tf.verdict==='LONG'){longScore+=tf.weight;longCount++;}
      if(tf.verdict==='SHORT'){shortScore+=tf.weight;shortCount++;}
      tfSummary.push({label:tf.label,verdict:tf.verdict,wr:tf.wr.toFixed(1),srsiK:tf.srsiK.toFixed(1),
        obv:tf.obvTrend,macd:tf.macdPositive?'+':'-',bull:tf.bull,bear:tf.bear,
        crossUp:tf.crossUp,crossDown:tf.crossDown,
        momFast:(tf.momFast||0).toFixed(3),momAccel:tf.momAccelBull?'↑':tf.momAccelBear?'↓':'—'});
    }

    // For downtrend rally: prefer LONG signals (catching bounce from downtrend)
    let verdict,score,count;
    if(longScore>=CONFIG.MIN_CONFLUENCE_SCORE&&longCount>=CONFIG.MIN_AGREEING_TIMEFRAMES&&longScore>shortScore)
      {verdict='LONG';score=longScore;count=longCount;}
    else if(shortScore>=CONFIG.MIN_CONFLUENCE_SCORE&&shortCount>=CONFIG.MIN_AGREEING_TIMEFRAMES&&shortScore>longScore)
      {verdict='SHORT';score=shortScore;count=shortCount;}
    else{botState.confluenceRejected++;return null;}

    // Buy/sell pressure
    let buyPct=50,bsBias='NEUTRAL';
    try{
      const trades=await binancePublic('/api/v3/aggTrades',{symbol,limit:100});
      let bv=0,sv=0;
      for(const t of trades){const val=parseFloat(t.p)*parseFloat(t.q);!t.m?bv+=val:sv+=val;}
      buyPct=parseFloat(((bv/(bv+sv||1))*100).toFixed(1));
      bsBias=buyPct>60?'STRONG_BUY':buyPct>52?'BUY':buyPct<40?'STRONG_SELL':buyPct<48?'SELL':'NEUTRAL';
    }catch(e){}

    // Entry levels using CONFIG.TARGET_PCT and CONFIG.STOP_PCT
    const entry  = verdict==='LONG' ? parseFloat(ob.asks[0][0]) : parseFloat(ob.bids[0][0]);
    const target = verdict==='LONG' ? entry*(1+CONFIG.TARGET_PCT/100) : entry*(1-CONFIG.TARGET_PCT/100);
    const stop   = verdict==='LONG' ? entry*(1-CONFIG.STOP_PCT/100)   : entry*(1+CONFIG.STOP_PCT/100);
    const rr     = Math.abs(target-entry)/Math.abs(stop-entry);

    const tf1m   = tfResults.find(t=>t.interval==='1m')||tfResults[0];
    const maxScore = CONFIG.TIMEFRAMES.reduce((s,t)=>s+t.weight,0);
    let quality = Math.min(50+(score/maxScore)*47,97)*0.45;
    quality += (count/CONFIG.TIMEFRAMES.length)*20;
    if(verdict==='LONG'){
      quality += tf1m.wr<=-70?12:tf1m.wr<=-55?6:0;
      quality += tf1m.srsiK<=20?12:tf1m.srsiK<=35?6:0;
      quality += tf1m.crossUp?10:0;
      quality += tf1m.momAllBull?10:tf1m.momFast>0&&tf1m.momMid>0?5:0;
      quality += tf1m.momAccelBull?8:0;
      quality += buyPct>55?6:0;
      quality += tf1m.obvTrend==='Rising'?5:0;
      // Bonus for deeply oversold in downtrend — highest conviction setup
      quality += (cache.change24<=-3&&tf1m.wr<=-70)?10:0;
    } else {
      quality += tf1m.wr>=-30?12:tf1m.wr>=-45?6:0;
      quality += tf1m.srsiK>=80?12:tf1m.srsiK>=65?6:0;
      quality += tf1m.crossDown?10:0;
      quality += tf1m.momAllBear?10:tf1m.momFast<0&&tf1m.momMid<0?5:0;
      quality += tf1m.momAccelBear?8:0;
      quality += buyPct<45?6:0;
    }
    quality = Math.min(Math.round(quality),100);
    const grade = quality>=80?'A':quality>=65?'B':quality>=50?'C':'D';
    if(!['A','B'].includes(grade)){botState.confluenceRejected++;return null;}

    botState.totalSignalsFound++;
    botState.analysisCount++;
    botState.lastAnalysis = new Date().toISOString();
    return {
      symbol,verdict,quality,grade,confluenceScore:parseFloat(score.toFixed(2)),agreeingCount:count,
      entry,target,stop,rr,targetPct:CONFIG.TARGET_PCT,stopPct:CONFIG.STOP_PCT,
      tier:getCurrentTier().label,tierIndex:getTierIndex(),spread,change24:cache.change24,
      wr:tf1m.wr,srsiK:tf1m.srsiK,crossUp:tf1m.crossUp,crossDown:tf1m.crossDown,
      obvTrend:tf1m.obvTrend,macdPositive:tf1m.macdPositive,
      obBias:bidRatio>0.62?'STRONG_BUY':bidRatio>0.54?'BUY':bidRatio<0.38?'STRONG_SELL':bidRatio<0.46?'SELL':'NEUTRAL',
      bidRatio,buyPct,bsBias,
      momFast:tf1m.momFast||0,momMid:tf1m.momMid||0,
      momAllBull:tf1m.momAllBull||false,momAllBear:tf1m.momAllBear||false,
      momAccelBull:tf1m.momAccelBull||false,momAccelBear:tf1m.momAccelBear||false,
      timeframes:tfSummary,
    };
  }catch(e){log('WARN',`Analyze ${symbol}: ${e.message}`);return null;}
}

// ─── Analysis Queue Processor ─────────────────────────────────────────────────
async function processAnalysisQueue() {
  if(isAnalyzing||!analysisQueue.length||!botState.running) return;
  isAnalyzing=true;
  try {
    const batch=[...new Set(analysisQueue.splice(0,CONFIG.ANALYSIS_BATCH_SIZE))];
    await Promise.allSettled(batch.map(async sym => {
      if(!botState.running||botState.killSwitch) return;
      if(botState.openTrades.some(t=>t.symbol===sym)) return;
      const r = await deepAnalyze(sym);
      if(r) {
        log('INFO',`✨ ${sym} ${r.verdict} q:${r.quality} grade:${r.grade} | WR:${r.wr.toFixed(0)} sRSI:${r.srsiK.toFixed(0)} OBV:${r.obvTrend} MACD:${r.macdPositive?'+':'-'} 24h:${r.change24.toFixed(1)}%`);
        // Add to execution queue sorted by quality
        executionQueue.push(r);
        executionQueue.sort((a,b)=>b.quality-a.quality);
        botState.executionQueueSize = executionQueue.length;
      }
    }));
  } finally { isAnalyzing=false; }
}

// ─── Continuous Execution Engine ─────────────────────────────────────────────
// Runs on its own interval — drains execution queue as slots open up
// This is the key to fast, non-stop trade execution
async function drainExecutionQueue() {
  if(!botState.running||botState.killSwitch) return;
  if(botState.drawdownPaused) return;
  const cd=isCooldownActive();
  if(cd) return;
  const dailyLimit=botState.usdtBalance*(CONFIG.DAILY_LOSS_LIMIT_PCT/100);
  if(dailyLimit>0&&botState.dailyPnl<=-dailyLimit){log('WARN','🛑 Daily loss limit');botState.running=false;return;}

  // Fill all available slots from the execution queue
  while(executionQueue.length>0&&botState.openTrades.length<botState.currentMaxTrades){
    const r=executionQueue.shift();
    if(!r) break;
    if(botState.openTrades.some(t=>t.symbol===r.symbol)) continue;
    // Re-check signal is still fresh (within 60s)
    if(Date.now()-(lastAnalysis[r.symbol]||0)>60000){
      log('INFO',`⏰ Stale signal ${r.symbol} — skipping`);continue;
    }
    await executeImmediately(r);
  }
  botState.executionQueueSize=executionQueue.length;
}

// ─── Trailing Stop ────────────────────────────────────────────────────────────
function activateTrailing(trade,price) {
  trade.trailing=true;trade.trailPeak=price;trade.trailTrough=price;
  trade.trailStop=trade.side==='LONG'?price*(1-CONFIG.TRAIL_PCT/100):price*(1+CONFIG.TRAIL_PCT/100);
  trade.trailActivatedAt=price;
  log('INFO',`🎯 TRAILING: ${trade.symbol} @ $${price.toFixed(6)}`);
}
function updateTrailing(trade,price) {
  if(trade.side==='LONG'){if(price>trade.trailPeak){trade.trailPeak=price;trade.trailStop=price*(1-CONFIG.TRAIL_PCT/100);}}
  else{if(price<trade.trailTrough){trade.trailTrough=price;trade.trailStop=price*(1+CONFIG.TRAIL_PCT/100);}}
}
function trailHit(trade,price){return trade.side==='LONG'?price<=trade.trailStop:price>=trade.trailStop;}

// ─── Order Execution ──────────────────────────────────────────────────────────
async function placeOrder(symbol,side,usdtAmount,price) {
  if(CONFIG.PAPER_MODE){
    const qty=parseFloat((usdtAmount/price).toFixed(6));
    log('INFO',`[PAPER] ${side} ${qty} ${symbol} @ $${price.toFixed(6)}`);
    return{orderId:'PAPER-'+Date.now(),symbol,side,qty,price,paper:true};
  }
  try{
    let step=global.stepSizeCache[symbol];
    if(!step){const info=await binancePublic('/api/v3/exchangeInfo',{symbol});const lf=info.symbols?.[0]?.filters?.find(f=>f.filterType==='LOT_SIZE');step=lf?parseFloat(lf.stepSize):0.001;global.stepSizeCache[symbol]=step;}
    const dec=step.toString().split('.')[1]?.length||3;
    const qty=parseFloat((Math.floor(usdtAmount/price/step)*step).toFixed(dec));
    if(qty<=0) throw new Error('Qty too small');
    const order=await binanceSigned('POST','/api/v3/order',{symbol,side,type:'MARKET',quantity:qty});
    const fp=parseFloat(order.fills?.[0]?.price||price);
    log('INFO',`[LIVE] ${side} ${qty} ${symbol} @ $${fp.toFixed(6)}`);
    return{orderId:order.orderId,symbol,side,qty,price:fp,paper:false};
  }catch(e){log('ERROR',`Order ${symbol}: ${e.message}`);throw e;}
}

async function executeImmediately(r) {
  if(!botState.running||botState.killSwitch) return;
  if(botState.openTrades.some(t=>t.symbol===r.symbol)) return;
  if(botState.openTrades.length>=botState.currentMaxTrades) return;
  const tier=getCurrentTier();
  try{
    const side=r.verdict==='LONG'?'BUY':'SELL';
    log('INFO',`🚀 EXECUTE: ${r.symbol} ${r.verdict} | q:${r.quality} ${r.grade} | target:+${CONFIG.TARGET_PCT}% stop:-${CONFIG.STOP_PCT}% | WR:${r.wr.toFixed(0)} sRSI:${r.srsiK.toFixed(0)} | 24h:${r.change24?.toFixed(1)}%`);
    const order=await placeOrder(r.symbol,side,tier.tradeUsdt,r.entry);
    botState.tradesExecuted++;
    botState.openTrades.push({
      id:order.orderId,symbol:r.symbol,side:r.verdict,
      entry:order.price,qty:order.qty,
      target:r.target,stop:r.stop,
      targetPct:CONFIG.TARGET_PCT,stopPct:CONFIG.STOP_PCT,rr:r.rr,
      grade:r.grade,quality:r.quality,
      confluenceScore:r.confluenceScore,agreeingCount:r.agreeingCount,
      tradeSize:tier.tradeUsdt,tier:r.tier,tierIndex:r.tierIndex,
      openedAt:new Date().toISOString(),paper:order.paper,trailing:false,
      research:{
        verdict:r.verdict,confluenceScore:r.confluenceScore,agreeingTimeframes:r.agreeingCount,
        timeframes:r.timeframes,
        wr:r.wr.toFixed(1),srsiK:r.srsiK.toFixed(1),
        crossUp:r.crossUp,crossDown:r.crossDown,
        obvTrend:r.obvTrend,macd:r.macdPositive?'Positive':'Negative',
        obBias:r.obBias,bidRatio:(r.bidRatio||0.5).toFixed(3),
        bsBias:r.bsBias,buySellBias:r.bsBias,buyPct:r.buyPct,
        momFast:(r.momFast||0).toFixed(3),momMid:(r.momMid||0).toFixed(3),
        momAllBull:r.momAllBull,momAllBear:r.momAllBear,
        momAccelBull:r.momAccelBull,momAccelBear:r.momAccelBear,
        change24:r.change24,quality:r.quality,
      },
    });
    log('INFO',`📊 Open:${botState.openTrades.length}/${botState.currentMaxTrades} | Queue:${executionQueue.length} | $${botState.usdtBalance.toFixed(2)} | ${tier.label}`);
  }catch(e){log('ERROR',`Execute ${r.symbol}: ${e.message}`);}
}

// ─── Risk Helpers ─────────────────────────────────────────────────────────────
function resetDailyPnl(){const t=new Date().toDateString();if(botState.dailyPnlDate!==t){botState.dailyPnl=0;botState.dailyPnlDate=t;log('INFO','Daily PnL reset');}}
function isCooldownActive(){
  if(!botState.inCooldown) return false;
  const e=Date.now()-botState.lastLossTime;
  if(e>=CONFIG.COOLDOWN_AFTER_LOSS_MS){botState.inCooldown=false;return false;}
  return Math.ceil((CONFIG.COOLDOWN_AFTER_LOSS_MS-e)/1000);
}

// ─── Trade Monitor (WS price cache — zero REST calls) ─────────────────────────
async function monitorOpenTrades() {
  if(!botState.running) return;
  resetDailyPnl();
  for(const trade of [...botState.openTrades]){
    const cache=priceCache[trade.symbol];
    if(!cache||Date.now()-cache.ts>30000) continue;
    const price=cache.price;
    let closeReason=null;
    if(!trade.trailing){
      if(trade.side==='LONG'){if(price>=trade.target)activateTrailing(trade,price);else if(price<=trade.stop)closeReason='STOP_HIT';}
      else{if(price<=trade.target)activateTrailing(trade,price);else if(price>=trade.stop)closeReason='STOP_HIT';}
    }else{
      updateTrailing(trade,price);
      if(trailHit(trade,price)){
        const pk=trade.side==='LONG'?trade.trailPeak:trade.trailTrough;
        log('INFO',`🏁 TRAIL: ${trade.symbol} peak:$${pk.toFixed(6)} exit:$${price.toFixed(6)}`);
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
      log('INFO',`${isWin?'✅':'❌'} ${trade.symbol} ${trade.side} | PnL:$${pnl.toFixed(4)} (${pnlPct}%) | ${closeReason} | WR:${total>0?((botState.winCount/total)*100).toFixed(0)+'%':'N/A'}`);
      await refreshBalance();
    }
  }
}

// ─── Routes ───────────────────────────────────────────────────────────────────
app.get('/health',(req,res)=>res.json({status:'ok',ts:new Date().toISOString(),wsConnected:botState.wsConnected,streams:botState.wsStreamCount}));

app.get('/status',(req,res)=>{
  const tier=getCurrentTier();const total=botState.winCount+botState.lossCount;const cd=isCooldownActive();
  res.json({
    running:botState.running,mode:botState.mode,killSwitch:botState.killSwitch,
    wsConnected:botState.wsConnected,wsStreamCount:botState.wsStreamCount,
    openTrades:botState.openTrades,closedTrades:botState.closedTrades.slice(0,50),
    dailyPnl:botState.dailyPnl,totalPnl:botState.totalPnl,
    analysisCount:botState.analysisCount,lastAnalysis:botState.lastAnalysis,
    analysisQueueSize:analysisQueue.length,executionQueueSize:executionQueue.length,
    symbolsLoaded:botState.symbolsLoaded,topPreScreened:botState.topPreScreened,
    usdtBalance:botState.usdtBalance,startingBalance:botState.startingBalance,
    currentTier:botState.currentTierIndex+1,tierName:tier.label,
    currentTradeUsdt:tier.tradeUsdt,currentMaxTrades:botState.currentMaxTrades,
    tierBaseTrades:tier.baseTrades,tierMaxTrades:tier.maxTrades,
    targetPct:CONFIG.TARGET_PCT,stopPct:CONFIG.STOP_PCT,
    consecutiveWins:botState.consecutiveWins,consecutiveLosses:botState.consecutiveLosses,
    inCooldown:!!cd,cooldownRemaining:cd||0,drawdownPaused:botState.drawdownPaused,
    totalSignalsFound:botState.totalSignalsFound,confluenceRejected:botState.confluenceRejected,
    downTrendRejected:botState.downTrendRejected,
    tradesExecuted:botState.tradesExecuted,winCount:botState.winCount,lossCount:botState.lossCount,
    winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',
    scalingLog:botState.scalingLog.slice(0,20),
    config:{
      symbols:dynamicSymbols.slice(0,20),totalSymbols:dynamicSymbols.length,
      timeframes:CONFIG.TIMEFRAMES.map(t=>t.label),
      targetPct:CONFIG.TARGET_PCT,stopPct:CONFIG.STOP_PCT,
      minVolume:CONFIG.MIN_VOLUME_USDT,maxVolume:CONFIG.MAX_VOLUME_USDT,
      requireDowntrend:CONFIG.REQUIRE_DOWNTREND,
      indicators:['Williams%R','StochRSI','OBV','MACD','OrderBook','BuySellPressure','Momentum'],
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
  await connectWebSockets();
  // Analysis queue — drains triggered coins
  analysisInterval = setInterval(processAnalysisQueue, CONFIG.ANALYSIS_INTERVAL_MS);
  // Execution queue — continuously fills open slots
  execInterval     = setInterval(drainExecutionQueue, 300);
  // Monitor — checks stops/targets every 800ms using WS cache
  monitorInterval  = setInterval(monitorOpenTrades, CONFIG.MONITOR_INTERVAL_MS);
  // Background
  balanceInterval  = setInterval(refreshBalance, 2*60*1000);
  symbolInterval   = setInterval(fetchTopSymbols, 20*60*1000);
  const msg=`Bot started | ${botState.mode} | ${tier.label} | TF:1m+3m+5m | Target:${CONFIG.TARGET_PCT}% Stop:${CONFIG.STOP_PCT}% | Downtrend hunt ON | ${botState.symbolsLoaded} coins | Continuous execution`;
  log('INFO',msg);
  res.json({success:true,message:msg});
});

app.post('/stop',(req,res)=>{
  botState.running=false;
  [analysisInterval,execInterval,monitorInterval,balanceInterval,symbolInterval].forEach(i=>clearInterval(i));
  for(const ws of wsConnections){try{ws.close();}catch(e){}}
  wsConnections=[];botState.wsConnected=false;
  log('INFO','Bot stopped');res.json({success:true,message:'Stopped'});
});

app.post('/kill',(req,res)=>{
  botState.running=false;botState.killSwitch=true;
  [analysisInterval,execInterval,monitorInterval,balanceInterval,symbolInterval].forEach(i=>clearInterval(i));
  for(const ws of wsConnections){try{ws.close();}catch(e){}}
  wsConnections=[];botState.wsConnected=false;
  log('WARN','🚨 KILL SWITCH');res.json({success:true,message:'Kill switch activated'});
});

app.post('/reset-kill',(req,res)=>{botState.killSwitch=false;res.json({success:true,message:'Kill switch reset'});});

app.post('/close-trade/:id',async(req,res)=>{
  const trade=botState.openTrades.find(t=>t.id===req.params.id);
  if(!trade) return res.json({success:false,message:'Not found'});
  try{
    const price=priceCache[trade.symbol]?.price;
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
  res.json({usdtBalance:botState.usdtBalance,startingBalance:botState.startingBalance,totalPnl:botState.totalPnl,
    growthPct:botState.startingBalance>0?((botState.totalPnl/botState.startingBalance)*100).toFixed(2)+'%':'0%',
    tier:tier.label,tradeUsdt:tier.tradeUsdt,currentMaxTrades:botState.currentMaxTrades,
    targetPct:CONFIG.TARGET_PCT,stopPct:CONFIG.STOP_PCT,
    winRate:total>0?((botState.winCount/total)*100).toFixed(1)+'%':'N/A',allTiers:CONFIG.TIERS});
});

const PORT=process.env.PORT||3001;
app.listen(PORT,async()=>{
  console.log(`\nSCALPR Ultimate Bot — port ${PORT}`);
  console.log(`Mode: ${CONFIG.PAPER_MODE?'PAPER':'⚠ LIVE'}`);
  console.log(`Strategy: Mid-cap downtrend rally (20M–200M vol, 24h negative)`);
  console.log(`Timeframes: 1m · 3m · 5m ONLY`);
  console.log(`Profit: +${CONFIG.TARGET_PCT}% target | -${CONFIG.STOP_PCT}% stop | +${CONFIG.TRAIL_PCT}% trailing`);
  console.log(`Indicators: Williams%R · StochRSI · OBV · MACD · OrderBook · BuySellPressure · Momentum`);
  console.log(`Execution: Continuous — queue drains every 300ms, monitor every 800ms`);
  console.log(`Tiers: 18 levels | 3→50 trades | $10→$220/trade\n`);
  await fetchTopSymbols();
  await refreshBalance();
  const tier=getCurrentTier();
  botState.currentMaxTrades=tier.baseTrades;
  symbolInterval=setInterval(fetchTopSymbols,20*60*1000);
  balanceInterval=setInterval(refreshBalance,2*60*1000);
});