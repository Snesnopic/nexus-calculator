(function (root) {
  'use strict';

  // every quantity that can grow without bound (points, shards, prestige, levels, multipliers)
  // is stored as its natural log; NEG stands for zero. This reaches about 10^(10^307).
  const F = 82087500;          // full prestige cost at P0; rank r->r+1 costs 250 r^2 (P+1)
  const RANK_K = 250;
  const HOLD = Infinity;
  const NEG = -Infinity;
  // primeweekly / primemonthly pay like weekly / monthly; the Rewards upgrade only lists the first four
  // 'run' is a Zombies game the player plays regularly: it pays like a reward (base × Income × IB, uncapped), with its
  // base and cadence worked out by the page from the map profile
  const KINDS = ['daily', 'prime', 'weekly', 'monthly', 'pweekly', 'pmonthly', 'run'];
  const PRIME_ONLY = { prime: true, pweekly: true, pmonthly: true };
  // the Rewards upgrade boosts every reward: confirmed for primeweekly (18.10), assumed for primemonthly
  const REW_BOOSTED = { daily: true, prime: true, weekly: true, monthly: true, pweekly: true, pmonthly: true };
  const DEFERRED = { weekly: true, monthly: true, pweekly: true, pmonthly: true };
  const hasKind = (cfg, k) => k === 'run' ? !!cfg.playRuns && cfg.rewBase.run > 0 && cfg.cooldown.run > 0 : cfg.useRewards && (!PRIME_ONLY[k] || cfg.prime);
  const anyKind = cfg => KINDS.some(k => hasKind(cfg, k));
  // goals measured in points (per day or in total), where the Income held matters more than the shards
  const INCOME_GOALS = { income: true, reachRate: true, networth: true };
  // between Ascends the plan reconsiders purchases and the target once a day
  const DECIDE_EVERY = 24;
  const LN10 = Math.LN10, LN2 = Math.LN2;
  const L_SMALL = Math.log(1e30);
  const L_MAX = 1e300;

  const ln = x => (x > 0 ? Math.log(x) : NEG);
  const sumSq = n => (n <= 0 ? 0 : n * (n + 1) * (2 * n + 1) / 6);
  function lAdd(a, b) {
    if (a === NEG) return b;
    if (b === NEG) return a;
    return a > b ? a + Math.log1p(Math.exp(b - a)) : b + Math.log1p(Math.exp(a - b));
  }
  function lSub(a, b) {
    if (b === NEG) return a;
    if (!(a > b)) return NEG;
    return a + Math.log1p(-Math.exp(b - a));
  }
  const lTenth = lL => lAdd(0, lL + Math.log(0.1));   // ln(1 + 0.1 L)

  // known: Lv12 1.5T .. Lv20 3Qa. Below Lv12 the x3.33 / x3 alternation continues downwards
  function bankCostTable() {
    const t = {};
    for (let L = 2; L <= 14; L++) {
      const k = L - 16;
      const e = Math.floor(k / 2), odd = ((k % 2) + 2) % 2;
      t[L] = (odd ? 500e12 : 150e12) * Math.pow(10, e);
    }
    Object.assign(t, { 15: 50e12, 16: 150e12, 17: 350e12, 18: 750e12, 19: 1.5e15, 20: 3e15 });
    return t;
  }
  // known: Lv13 32h .. Lv15 40h (4h per level), Lv16 48h .. Lv19 72h (8h per level), Lv20 96h
  function storageAt(L) { return L >= 20 ? 96 : L <= 15 ? Math.max(4, 40 + 4 * (L - 15)) : 40 + 8 * (L - 15); }

  function defaults() {
    return {
      shards: 0, prime: false, server: 0, other: 0,
      res: 0, yld: 0, intr: 0, rew: 0, disc: 0,
      P: 0, R: 1, bal: 0, networth: 0,
      bankLv: 1, bankBonus: 1, rate: 0.0025, rawCap: 2.5e11, activeFrom: 0, activeTo: 0, clock0: 0,
      bankCosts: bankCostTable(),
      rewBase: { daily: 1e5, prime: 1e5, weekly: 1e6, monthly: 1e7, pweekly: 1e6, pmonthly: 1e7, run: 0 },
      // since 18.10 #2 each reward is capped after all bonuses
      rewCap: { daily: 2.4e12, prime: 2.4e12, weekly: 2.4e13, monthly: 2.4e14, pweekly: 2.4e13, pmonthly: 2.4e14 },
      cooldown: { daily: 24, prime: 24, weekly: 168, monthly: 720, pweekly: 168, pmonthly: 720, run: 0 },
      nextIn: { daily: 0, prime: 0, weekly: 0, monthly: 0, pweekly: 0, pmonthly: 0, run: 0 },
      loan: false, floorShards: true, allowShop: true, allowBank: true,
      minP: 1000, minBal: 0, minGap: 1, lookahead: 336, useRewards: true, deferFrac: 0.25, buyMargin: Math.log(1.01),
      limitBits: 64, maxClicks: 100,
      objective: 'ib', horizonH: 1400, round: 150, reinvest: false, targetIB: 1000, targetRate: 1e14, mult: 1, privateServer: false
    };
  }

  // ---- plain-number helpers (current state, small values) ----
  function costToPD(P, d) { return d * F * P * (P + 1) / 2; }
  function cumPR(P, R, d) { return d * (F * P * (P + 1) / 2 + (P + 1) * RANK_K * sumSq(R - 1)); }
  function pAffD(W, d) {
    if (!(W > 0)) return 0;
    const x = Math.floor((-1 + Math.sqrt(1 + 8 * W / (d * F))) / 2 + 1e-9);
    return costToPD(x, d) <= W * (1 + 1e-12) ? x : x - 1;
  }

  // ---- base formulas (log domain) ----
  // since the 18.10 rework the Income Bonus is 1 plus the shard bonus only; above 10,000 unspent shards only
  // 10·√(S − 10,000) more count; each counts 0.10 × (1 + 0.1·Resonance) × the shard multiplier /stats shows, which
  // includes Prime ×1.2 and 1 + boost 25% + leaderboard spots 10/5/2% + solo records 10% + Gun Game top 5 30..2.5%
  function constIB(cfg) { return 1; }
  const L_SOFT = Math.log(1e4);
  function lEff(lS) {
    if (lS <= L_SOFT) return lS;
    const l = lAdd(L_SOFT, Math.log(10) + 0.5 * lSub(lS, L_SOFT));
    return l < Math.log(1e15) ? Math.log(Math.floor(Math.exp(l) + 1e-9)) : l;
  }
  function shardMult(cfg) { return cfg.mult > 0 ? cfg.mult : 1; }
  function lShardValue(cfg, st) { return Math.log(0.10 * shardMult(cfg)) + lTenth(st.res); }
  function lIBat(cfg, st, lS) { return lAdd(Math.log(constIB(cfg)), lShardValue(cfg, st) + lEff(lS)); }
  function lIB(cfg, st) { return lIBat(cfg, st, st.S); }
  // +5% per level, but Lv20 jumps from x1.90 to x2.00
  function bonusAt(L) { return L >= 20 ? 2 : 1 + 0.05 * (L - 1); }
  function bankBonusOf(cfg, st) { return bonusAt(st.bankLv); }
  // claiming less often than the storage fills loses the excess hours
  function storageOf(cfg, st) { return storageAt(st.bankLv); }
  // the player acts only inside a daily window of local hours; clock0 is the local hour at t = 0
  function activeHours(cfg) { const a = ((cfg.activeTo - cfg.activeFrom) % 24 + 24) % 24; return a === 0 ? 24 : a; }
  function nextActive(cfg, t) {
    if (!isFinite(t) || activeHours(cfg) >= 24) return t;
    const since = ((cfg.clock0 + t - cfg.activeFrom) % 24 + 24) % 24;
    return since < activeHours(cfg) - 1e-9 ? t : t + (24 - since);
  }
  // interest piles up while you are away, but only for as many hours as the storage holds
  function claimFactor(cfg, st) { return Math.min(1, (activeHours(cfg) + storageOf(cfg, st)) / 24); }
  // since 18.10 the hourly cap (250B since update #3) applies after the Income Bonus and Interest, and only the
  // facility bonus and the stored hours come on top: every balance at or above the reserve earns rawCap × bonus
  function lRate(cfg, st) { return Math.log(cfg.rawCap * bankBonusOf(cfg, st) * claimFactor(cfg, st)); }
  function dOf(st) { return 1 - 0.05 * st.disc; }
  function lReserve(cfg, st) { return Math.log(cfg.rawCap / cfg.rate) - lIB(cfg, st) - lTenth(st.intr); }
  function reserveOf(cfg, st) { return Math.exp(lReserve(cfg, st)); }
  // reward points per hour per unit of Income × Income Bonus (cooldowns spread over time)
  function lRho(cfg, st) {
    if (!anyKind(cfg)) return NEG;
    let boosted = 0, plain = 0;
    for (const k of KINDS) {
      if (!hasKind(cfg, k)) continue;
      if (REW_BOOSTED[k]) boosted += cfg.rewBase[k] / cfg.cooldown[k]; else plain += cfg.rewBase[k] / cfg.cooldown[k];
    }
    return lAdd(boosted > 0 ? ln(boosted) + lTenth(st.rew) : NEG, ln(plain));
  }
  // one claim of kind k at Income lpm (ln), capped
  function lRewAmt(cfg, st, k, lpm, lib) {
    const l = Math.log(cfg.rewBase[k]) + lpm + (lib === undefined ? lIB(cfg, st) : lib) + (REW_BOOSTED[k] ? lTenth(st.rew) : 0);
    return cfg.rewCap && cfg.rewCap[k] > 0 ? Math.min(l, Math.log(cfg.rewCap[k])) : l;
  }
  // reward points per hour at Income lpm, each kind spread over its cooldown and capped
  function lRewH(cfg, st, lpm) {
    if (!anyKind(cfg)) return NEG;
    const lib = lIB(cfg, st);
    let l = NEG;
    for (const k of KINDS) if (hasKind(cfg, k)) l = lAdd(l, lRewAmt(cfg, st, k, lpm, lib) - Math.log(cfg.cooldown[k]));
    return l;
  }
  function lCostToP(lP, d) { return lP === NEG ? NEG : Math.log(d * F / 2) + lP + lAdd(lP, 0); }
  function lPAff(lW, d) {
    if (lW === NEG) return NEG;
    if (lW < L_SMALL) return ln(pAffD(Math.exp(lW), d));
    return 0.5 * (Math.log(2 / (d * F)) + lW);
  }
  // best (P+1)*R affordable with W: sitting at R100 of P is worth 100(P+1)
  function lPm(lW, d) {
    const lQ = lPAff(lW, d);
    if (lQ !== NEG) return Math.log(100) + lQ;
    if (lW === NEG) return 0;
    const W = Math.exp(lW);
    let R = Math.floor(Math.cbrt(3 * W / (RANK_K * d))) + 1;
    while (R > 1 && d * RANK_K * sumSq(R - 1) > W) R--;
    return Math.log(Math.max(1, Math.min(100, R)));
  }
  // bank interest per hour for the balance held: below the reserve it is that share of the cap (a loan being paid
  // back counts as the full reserve)
  function lBankNow(cfg, st) {
    if (st.loanRepay) return lRate(cfg, st);
    const lRes = lReserve(cfg, st);
    return st.L >= lRes ? lRate(cfg, st) : st.L === NEG ? NEG : lRate(cfg, st) + st.L - lRes;
  }
  // the reserve is worth keeping only when the bank grows it quickly (below the cap it at least doubles in a day);
  // otherwise, like on a fresh account, every point is worth more as prestige
  function lKeep(cfg, st) { const lRes = lReserve(cfg, st); return lRate(cfg, st) - lRes >= -Math.log(24) ? lRes : NEG; }
  // points held in prestige or free to buy it
  function lHeld(cfg, st) { return lAdd(st.Wp, lSub(st.L, lKeep(cfg, st))); }
  // points per day with the prestige that lW buys: bank interest (at the cap unless lBank says otherwise) plus
  // rewards on that Income
  function lDayAt(cfg, st, lW, lBank) {
    return Math.log(24) + lAdd(lBank === undefined ? lRate(cfg, st) : lBank, lRewH(cfg, st, lPm(lW, dOf(st))));
  }
  const lDay = (cfg, st) => lDayAt(cfg, st, lHeld(cfg, st), lBankNow(cfg, st));
  // points held after rem hours of putting everything into prestige: each day the rewards pay their daily share on
  // the Income held so far, plus the bank's flat interest. Right after an Ascend the Income starts at 1 and the first
  // days are slow; once a day adds less than half of W, √W grows linearly and the rest is closed-form
  function lWAfter(cfg, st, lW, rem) {
    if (!(rem > 0)) return lW;
    const d = dOf(st), lib = lIB(cfg, st), lRh = lRho(cfg, st);
    const lBankH = lRate(cfg, st);
    let h = rem;
    for (let i = 0; i < 60 && h > 0; i++) {
      const dt = Math.min(24, h);
      const lGain = lAdd(lBankH, lRewH(cfg, st, lPm(lW, d))) + Math.log(dt);
      const steady = lW !== NEG && lGain < lW - LN2;
      lW = lAdd(lW, lGain);
      h -= dt;
      if (steady) break;
    }
    if (h > 0) {
      // with every reward at its cap the points grow linearly; otherwise √W grows linearly
      const lpm = lPm(lW, d);
      if (lRewH(cfg, st, lpm) < lRh + lpm + lib - 1e-9) return lAdd(lW, lAdd(lBankH, lRewH(cfg, st, lpm)) + Math.log(h));
      const lk = lRh + lib + Math.log(100) + 0.5 * Math.log(2 / (d * F)) - LN2;
      lW = 2 * lAdd(0.5 * lAdd(lW, lBankH + Math.log(h)), lk + Math.log(h));
    }
    return lW;
  }
  // points per day after rem hours of holding (no Ascend) from lW
  const lDayAfter = (cfg, st, lW, rem) => lDayAt(cfg, st, lWAfter(cfg, st, lW, rem));
  function lShardsRaw(st, lP) { return Math.log(10) + 2 * (lP - Math.log(1000)) + lTenth(st.yld); }
  function lShardsAt(cfg, st, lP) {
    const l = lShardsRaw(st, lP);
    if (!cfg.floorShards || l > Math.log(1e6)) return l;
    return ln(Math.floor(Math.exp(l) + 1e-9));
  }
  function lMinPforShards(st, k) {
    const y = Math.exp(lTenth(st.yld));
    let P = Math.ceil(1000 * Math.sqrt(k / (10 * y)) - 1e-9);
    for (let i = 0; i < 3 && 10 * (P / 1000) * (P / 1000) * y * (1 + 1e-12) < k; i++) P++;
    return Math.log(P);
  }
  function blockSum(round) {
    let s = 0;
    for (let R = 10; R <= round; R += 5) s += Math.pow(1.4, R / 5 - 1);
    return s;
  }

  // ---- shard shop ----
  const BASE = { res: 5, yld: 5, intr: 5, rew: 3, disc: 5 };
  // Rewards only raises reward claims: without them it is wasted shards
  const shopKeys = cfg => cfg.useRewards ? ['res', 'yld', 'intr', 'rew', 'disc'] : ['res', 'yld', 'intr', 'disc'];
  // next level costs base * (L+1) (Interest Lv3 = 15 confirms it)
  function lUpgradeCost(st, key) {
    if (key === 'disc') return st.disc >= 5 ? Infinity : Math.log(5 * (st.disc + 1));
    return Math.log(BASE[key]) + lAdd(st[key], 0);
  }
  // ln of the number of levels affordable with ln-budget lQ: base * (n L + n(n+1)/2) <= Q
  function lLevelsWithin(st, key, lQ) {
    if (lQ === NEG) return NEG;
    if (key === 'disc') {
      let n = 0, c = 0;
      while (st.disc + n < 5 && c + 5 * (st.disc + n + 1) <= Math.exp(lQ) * (1 + 1e-12)) { c += 5 * (st.disc + n + 1); n++; }
      return ln(n);
    }
    const base = BASE[key], lL = st[key];
    if (lQ < Math.log(1e15) && lL < Math.log(1e7)) {
      const L = Math.round(Math.exp(lL)), q = Math.exp(lQ) / base;
      let n = Math.floor((-(2 * L + 1) + Math.sqrt((2 * L + 1) * (2 * L + 1) + 8 * q)) / 2 + 1e-9);
      for (let i = 0; i < 4 && n > 0 && (n * L + n * (n + 1) / 2) > q * (1 + 1e-12); i++) n--;
      return ln(n);
    }
    const lA = lAdd(LN2 + lL, 0);
    const lB = Math.log(8 / base) + lQ;
    const lN = lB - lAdd(0.5 * lAdd(2 * lA, lB), lA) - LN2;
    return lN >= 0 ? lN : NEG;
  }
  // upgrades are paid when they start to matter, so their shards keep boosting IB until then:
  // Yield right before the Ascend, Discount and Rewards right before the next prestige purchase (reward claim or Ascend)
  function spend(st, key, lc) {
    if (key === 'yld') st.yDebt = lAdd(st.yDebt, lc);
    else if (key === 'disc' || key === 'rew') st.pDebt = lAdd(st.pDebt, lc);
    else st.S = lSub(st.S, lc);
  }
  const spendable = st => lSub(lSub(st.S, st.yDebt), st.pDebt);
  function payPrestigeDebt(st) {
    if (st.pDebt !== NEG) { st.S = lSub(st.S, st.pDebt); st.pDebt = NEG; }
  }
  // decisions treat reserved shards as already spent, so deferring the payment never makes an upgrade look free
  function paidView(st) {
    if (st.yDebt === NEG && st.pDebt === NEG) return st;
    const v = Object.assign({}, st);
    v.S = spendable(st); v.yDebt = NEG; v.pDebt = NEG;
    return v;
  }
  function applyBuy(cfg, st, opt) {
    if (opt.key === 'bank') { st.bankNeed = Math.log(cfg.bankCosts[st.bankLv + 1]); return st.bankNeed; }
    if (opt.key === 'disc') {
      const n = Math.round(Math.exp(opt.n));
      let c = 0;
      for (let i = 0; i < n; i++) c += 5 * (st.disc + i + 1);
      st.disc += n; spend(st, 'disc', Math.log(c));
      settleHeld(cfg, st);
      return Math.log(c);
    }
    const lL = st[opt.key], lN = opt.n;
    const lCost = Math.log(BASE[opt.key]) + lAdd(lN + lL, lN + lAdd(lN, 0) - LN2);
    spend(st, opt.key, lCost);
    st[opt.key] = lAdd(lL, lN);
    return lCost;
  }

  // ---- P* maximizing the IB growth per hour ----
  // points gathered above the reserve during the cycle starting now, along its reward claims sorted by the hour
  // they are taken (te); weekly and monthly kinds wait up to deferFrac of their cooldown for the Ascend.
  // a claim pays on the prestige bought so far, so the path does not depend on the target
  function cyclePath(cfg, st, tMax) {
    const c = [];
    if (anyKind(cfg)) {
      const lib = lIB(cfg, st), lb = lTenth(st.rew);
      for (const k of KINDS) {
        if (!hasKind(cfg, k)) continue;
        const la = Math.log(cfg.rewBase[k]) + lib + (REW_BOOSTED[k] ? lb : 0);
        const w = DEFERRED[k] ? cfg.deferFrac * cfg.cooldown[k] : 0;
        let n = 0;
        for (let tc = Math.max(0, st.next[k] - st.t); tc < tMax && n < 24; tc += cfg.cooldown[k], n++)
          c.push({ t: tc, te: nextActive(cfg, st.t + tc + w) - st.t, la: la, lcap: cfg.rewCap && cfg.rewCap[k] > 0 ? Math.log(cfg.rewCap[k]) : Infinity });
      }
      c.sort((x, y) => x.te - y.te);
    }
    const d = dOf(st), lI = lRate(cfg, st);
    const before = new Array(c.length), after = new Array(c.length);
    let lW = NEG, tau = 0;
    for (let i = 0; i < c.length; i++) {
      if (c[i].te > tau) { lW = lAdd(lW, lI + Math.log(c[i].te - tau)); tau = c[i].te; }
      before[i] = lW;
      lW = lAdd(lW, Math.min(c[i].la + lPm(lW, d), c[i].lcap));
      after[i] = lW;
    }
    return { c: c, before: before, after: after, lI: lI };
  }
  // claims still waiting when the target becomes affordable are taken right before the Ascend and raise the
  // prestige reached
  function growthAt(cfg, st, lP, path) {
    const d = dOf(st);
    const lNeed = lAdd(lCostToP(lP, d), Math.log(cfg.minBal));
    const lIB0 = lIB(cfg, st);
    if (!path) path = cyclePath(cfg, st, Math.exp(lNeed - lRate(cfg, st)));
    const c = path.c, n = c.length;
    let i = 0, j = n;
    while (i < j) { const m = (i + j) >> 1; if (path.after[m] < lNeed) i = m + 1; else j = m; }
    let dt;
    if (i < n && path.before[i] < lNeed) dt = c[i++].te;
    else dt = (i > 0 ? c[i - 1].te : 0) + Math.exp(lSub(lNeed, i > 0 ? path.after[i - 1] : NEG) - path.lI);
    dt = Math.max(cfg.minGap, dt);
    let lEnd = lNeed;
    const lpm = lPm(lNeed, d);
    const tLast = dt + cfg.deferFrac * cfg.cooldown.monthly + 24;
    for (; i < n && c[i].te <= tLast; i++) if (c[i].t <= dt) lEnd = lAdd(lEnd, Math.min(c[i].la + lpm, c[i].lcap));
    const lPend = lEnd > lNeed ? Math.max(lP, lPAff(lSub(lEnd, Math.log(cfg.minBal)), d)) : lP;
    const lGain = lShardsAt(cfg, st, lPend);
    const lIB1 = lIBat(cfg, st, lAdd(st.S, lGain));
    return (lIB1 - lIB0) / dt;
  }
  function snapTarget(cfg, st, lP) {
    lP = Math.max(Math.log(cfg.minP), lP);
    if (lP < L_SMALL) lP = Math.log(Math.round(Math.exp(lP)));
    if (!cfg.floorShards || lShardsRaw(st, lP) >= Math.log(1e6)) return lP;
    const kMin = Math.round(Math.exp(lShardsAt(cfg, st, Math.log(cfg.minP))));
    const k = Math.max(kMin, Math.floor(Math.exp(lShardsRaw(st, lP)) + 1e-9));
    return Math.max(Math.log(cfg.minP), lMinPforShards(st, k));
  }
  function pStar(cfg, st) {
    const lo = Math.log(cfg.minP);
    const hi = Math.max(lo + Math.log(400), Math.log(20) + lPAff(lRate(cfg, st) + Math.log(240), dOf(st)));
    const path = cyclePath(cfg, st, Math.min(24 * 45, Math.exp(lCostToP(hi, dOf(st)) - lRate(cfg, st))));
    const N = 48;
    let best = lo, bg = -Infinity;
    for (let i = 0; i <= N; i++) {
      const x = lo + (hi - lo) * i / N;
      const g = growthAt(cfg, st, x, path);
      if (g > bg) { bg = g; best = x; }
    }
    let a = Math.max(lo, best - (hi - lo) / N), b = Math.min(hi, best + (hi - lo) / N);
    const phi = (Math.sqrt(5) - 1) / 2;
    for (let i = 0; i < 40; i++) {
      const x1 = b - phi * (b - a), x2 = a + phi * (b - a);
      if (growthAt(cfg, st, x1, path) > growthAt(cfg, st, x2, path)) b = x2; else a = x1;
    }
    const lP = (a + b) / 2;
    if (cfg.floorShards && lShardsRaw(st, lP) < Math.log(1e6)) {
      const k0 = Math.floor(Math.exp(lShardsRaw(st, lP)));
      let bk = snapTarget(cfg, st, lP), bgk = -Infinity;
      for (let k = Math.max(1, k0 - 4); k <= k0 + 5; k++) {
        const Pk = Math.max(lo, lMinPforShards(st, k));
        const g = growthAt(cfg, st, Pk, path);
        if (g > bgk) { bgk = g; bk = Pk; }
      }
      return bk;
    }
    return snapTarget(cfg, st, lP);
  }

  // ---- event-driven simulation ----
  function initState(cfg, t0) {
    const st = {
      t: t0 || 0, S: ln(cfg.shards), res: ln(cfg.res), yld: ln(cfg.yld), intr: ln(cfg.intr), rew: ln(cfg.rew), disc: cfg.disc,
      bankLv: cfg.bankLv, Wp: NEG, L: NEG, target: HOLD, bankNeed: NEG, lastAsc: -Infinity, yDebt: NEG, pDebt: NEG,
      next: {}, heldP: cfg.P, heldR: cfg.R, lEarn: NEG, lastDecide: t0 || 0
    };
    for (const k of KINDS) st.next[k] = st.t + Math.max(0, cfg.nextIn[k] !== undefined ? cfg.nextIn[k] : cfg.cooldown[k]);
    return st;
  }
  // held prestige is valued at the current discount
  function settleHeld(cfg, st) {
    if (st.heldP === null) return;
    st.Wp = ln(cumPR(st.heldP, st.heldR, dOf(st)));
    st.L = ln(cfg.bal);
  }
  function clone(st) {
    const c = Object.assign({}, st);
    c.next = Object.assign({}, st.next);
    return c;
  }
  function rebalance(cfg, st) {
    if (st.bankNeed !== NEG) return;
    const lRes = lKeep(cfg, st);
    const lCt = st.target === HOLD ? Infinity : lCostToP(st.target, dOf(st));
    if (st.L > lRes && st.Wp < lCt) {
      const avail = lSub(st.L, lRes);
      const room = lCt === Infinity ? Infinity : lSub(lCt, st.Wp);
      if (avail <= room) { st.Wp = lAdd(st.Wp, avail); st.L = lRes; }
      else { st.Wp = lCt; st.L = lSub(st.L, room); }
    }
  }
  function advance(cfg, st, dt) {
    if (dt <= 0) return;
    const lI = lRate(cfg, st), lRes = lReserve(cfg, st);
    let lInc;
    if (st.loanRepay || st.L >= lRes) lInc = lI + Math.log(dt);
    else if (st.L === NEG) lInc = NEG;
    else {
      // below the reserve the balance grows by k of itself per hour (claimed often) until it reaches the reserve
      const k = Math.exp(lI - lRes), tUp = (lRes - st.L) / k;
      lInc = dt <= tUp ? st.L + Math.log(Math.expm1(k * dt)) : lAdd(lSub(lRes, st.L), lI + Math.log(dt - tUp));
    }
    st.L = lAdd(st.L, lInc);
    st.lEarn = lAdd(st.lEarn, lInc);
    if (st.loanRepay && st.L >= lRes) st.loanRepay = false;
    st.t += dt;
    rebalance(cfg, st);
  }
  function deferOf(cfg, st, k) {
    return DEFERRED[k] && st.target !== HOLD ? cfg.deferFrac * cfg.cooldown[k] : 0;
  }
  // weekly and monthly rewards wait (up to deferFrac of their cooldown) for the next ascend, where prestige peaks
  function claimRewards(cfg, st, log, atAscend) {
    if (!anyKind(cfg)) return;
    const dueNow = k => (atAscend ? st.next[k] : st.next[k] + deferOf(cfg, st, k)) <= st.t + 1e-9;
    // the order is by what each pays per unit of Income: Rewards boosts daily, weekly, monthly and primedaily only
    const per = k => Math.log(cfg.rewBase[k]) + (REW_BOOSTED[k] ? lTenth(st.rew) : 0);
    const due = KINDS.filter(k => hasKind(cfg, k) && dueNow(k)).sort((a, b) => per(a) - per(b));
    if (due.length) payPrestigeDebt(st);
    const lib = lIB(cfg, st);
    // smallest first: each claim pays on all the prestige the points can buy (everything right before an Ascend,
    // otherwise what is above the interest reserve and a pending bank upgrade), earlier claims included
    for (const k of due) {
      const lFree = atAscend ? st.L : lSub(st.L, lAdd(lKeep(cfg, st), st.bankNeed));
      const lpm = lPm(lAdd(st.Wp, lFree), dOf(st));
      const amt = lRewAmt(cfg, st, k, lpm, lib);
      st.L = lAdd(st.L, amt);
      st.lEarn = lAdd(st.lEarn, amt);
      st.next[k] = st.t + cfg.cooldown[k];
      if (log) log.rewards.push({ t: st.t, kind: k, lpm: lpm, lamount: amt });
    }
    rebalance(cfg, st);
  }
  function nextRewardTime(cfg, st) {
    if (!anyKind(cfg)) return Infinity;
    let m = Infinity;
    for (const k of KINDS) {
      if (!hasKind(cfg, k)) continue;
      const due = st.next[k] + deferOf(cfg, st, k);
      if (due < m) m = due;
    }
    return m;
  }
  function restartPenalty(cfg, st) {
    if (cfg.loan || lKeep(cfg, st) === NEG) return 0;
    const lib = lIB(cfg, st);
    const lb0 = Math.log(cfg.rewBase.daily * (cfg.prime ? 2 : 1)) + lib + lTenth(st.rew);
    const lk = Math.log(cfg.rate * bankBonusOf(cfg, st)) + lTenth(st.intr) + lib;
    return Math.max(0, (lReserve(cfg, st) - lb0) / Math.exp(Math.min(lk, 700)));
  }
  // each Yield level adds a tenth of the Ascend's base shards and costs 5 x its level: right before the Ascend,
  // buy the levels that this Ascend alone pays back (shards up front, one click each)
  function yieldTopUp(cfg, st, lP, log) {
    if (!cfg.allowShop || !(cfg.maxClicks >= 1)) return;
    const lB = Math.log(10) + 2 * (lP - Math.log(1000));
    const lTop = lSub(Math.log(0.02) + lB, lAdd(st.yld, 0));
    if (lTop === NEG) return;
    const lN = Math.min(Math.log(Math.floor(cfg.maxClicks)), lTop, lLevelsWithin(st, 'yld', spendable(st)));
    const n = lN < Math.log(1e15) ? Math.floor(Math.exp(lN) + 1e-9) : Math.exp(lN);
    if (!(n >= 1)) return;
    const lfrom = st.yld;
    const lc = applyBuy(cfg, st, { key: 'yld', n: Math.log(n) });
    st.S = lSub(st.S, st.yDebt); st.yDebt = NEG;
    if (log) {
      const rec = { t: st.t, key: 'yld', lfrom: lfrom, lto: st.yld, lcost: lc, asc: log.ascends.length };
      log.buys.push(rec);
      if (log.ascends.length) log.ascends[log.ascends.length - 1].buys.push(rec);
    }
  }
  function doAscend(cfg, st, log) {
    const d = dOf(st);
    const lW = lAdd(st.Wp, st.L);
    const lP = Math.max(st.target === HOLD ? NEG : st.target, lPAff(lSub(lW, Math.log(cfg.minBal)), d));
    if (st.yDebt !== NEG) { st.S = lSub(st.S, st.yDebt); st.yDebt = NEG; }
    payPrestigeDebt(st);
    yieldTopUp(cfg, st, lP, log);
    const gain = lShardsAt(cfg, st, lP);
    st.S = lAdd(st.S, gain);
    const lDayPre = log ? lDay(cfg, st) : NEG;
    st.Wp = NEG; st.L = NEG; st.heldP = null; st.lastAsc = st.t;
    if (log) log.ascends.push({ t: st.t, lP: lP, lgain: gain, lS: st.S, lib: lIB(cfg, st), lrate: lRate(cfg, st), lday: lDay(cfg, st), ldayPre: lDayPre, learn: st.lEarn, buys: [] });
    // with a loan the first reserve-worth of interest pays it back; without one the reserve is rebuilt during pen
    const pen = restartPenalty(cfg, st);
    if (pen > 0) st.t += pen;
    const keep = lKeep(cfg, st) !== NEG;
    st.loanRepay = cfg.loan && keep;
    if (!cfg.loan && keep) st.L = lReserve(cfg, st);
    // purchases after this ascend happen once the bank is rebuilt
    if (log) { const a = log.ascends[log.ascends.length - 1]; a.tNext = st.t; a.restart = pen; }
    return lP;
  }
  function canAscend(cfg, st) {
    return st.bankNeed === NEG && lPAff(lSub(lAdd(st.Wp, st.L), Math.log(cfg.minBal)), dOf(st)) >= Math.log(cfg.minP) - 1e-12;
  }

  // end-of-horizon rule of the base policy
  function baseShouldAscend(cfg, st, T) {
    const rem = T - st.t;
    const d = dOf(st);
    const lW = lAdd(st.Wp, st.L);
    const lP = Math.max(st.target, lPAff(lSub(lW, Math.log(cfg.minBal)), d));
    const after = clone(st);
    after.S = lAdd(after.S, lShardsAt(cfg, st, lP));
    const lI1 = lRate(cfg, after);
    if (cfg.objective === 'bo2') {
      const lRes = lReserve(cfg, st);
      const lIh = lRate(cfg, st);
      const vh = bo2Run(cfg, lSub(lAdd(lW, lIh + Math.log(rem)), lRes), lIB(cfg, st), d).tot;
      const va = bo2Run(cfg, lSub(lI1 + Math.log(rem), lRes), lIB(cfg, after), d).tot;
      return va > vh;
    }
    // an Ascend trades the Income the prestige gives for shards: compare points per day at the end
    if (INCOME_GOALS[cfg.objective]) {
      const lHold = lDayAfter(cfg, st, lHeld(cfg, st), rem);
      const lAsc = lDayAfter(cfg, after, NEG, rem);
      return lAsc > lHold;
    }
    // Income Bonus goals: shards only come from Ascends and count as √ above 10k, while rewards grow with the Income
    // held, so compare Ascending now (and again on the date) with holding until the date and Ascending then
    const lShW = lW2 => lShardsAt(cfg, st, lPAff(lW2, d));
    const lHoldIB = lIBat(cfg, st, lAdd(st.S, lShW(lWAfter(cfg, st, lHeld(cfg, st), rem))));
    const lAscIB = lIBat(cfg, after, lAdd(after.S, lShW(lWAfter(cfg, after, NEG, rem))));
    return lAscIB > lHoldIB;
  }

  // 'reach' targets an Income Bonus, 'reachRate' points per day; reaching it sooner always beats
  // not reaching it, whose value is ln(metric) < ln(target)
  const isReach = cfg => cfg.objective === 'reach' || cfg.objective === 'reachRate';
  const goalOf = cfg => cfg.objective === 'reach' ? Math.log(cfg.targetIB) : cfg.objective === 'reachRate' ? Math.log(cfg.targetRate) : Infinity;
  const metricOf = (cfg, st) => cfg.objective === 'reachRate' ? lDay(cfg, st) : lIB(cfg, st);
  const reachValue = (cfg, t) => goalOf(cfg) + 1e6 - t;

  // one Zombies run entered at R100 of the prestige lWp buys; with reinvest each block's payout buys prestige
  // before the next block
  function bo2Run(cfg, lWp, lib, d) {
    let lpm = lPm(lWp, d), tot = NEG;
    const lpm0 = lpm;
    for (let R = 10; R <= cfg.round; R += 5) {
      const r = Math.log(1500) + lpm + lib + (R / 5 - 1) * Math.log(1.4) + (cfg.privateServer ? LN2 : 0);
      tot = lAdd(tot, r);
      if (cfg.reinvest) { lWp = lAdd(lWp, r); lpm = lPm(lWp, d); }
    }
    return { tot: tot, lpm0: lpm0, lpm: lpm };
  }

  // on the goal date the shards left are worth most as Resonance (Income Bonus) and, for points per day, Rewards;
  // each level is one click, so at most maxClicks of them
  function finalShop(cfg, st) {
    if (!cfg.allowShop || !(cfg.maxClicks >= 1) || cfg.objective === 'networth') return null;
    const rate = INCOME_GOALS[cfg.objective] && anyKind(cfg);
    const C = Math.floor(cfg.maxClicks), sp = spendable(st);
    const lCost = (lL, n, base) => n > 0 ? Math.log(base) + lAdd(Math.log(n) + lL, Math.log(n) + lAdd(Math.log(n), 0) - LN2) : NEG;
    const view = (nr, ni) => {
      const lcr = lCost(st.res, nr, BASE.res), lci = lCost(st.rew, ni, BASE.rew);
      if (lAdd(lcr, lci) > sp) return null;
      return Object.assign({}, st, { S: lSub(sp, lAdd(lcr, lci)), res: lAdd(st.res, ln(nr)), rew: lAdd(st.rew, ln(ni)), yDebt: NEG, pDebt: NEG, lcr: lcr, lci: lci });
    };
    const val = (nr, ni) => { const v = view(nr, ni); return v ? (rate ? lDay(cfg, v) : lIB(cfg, v)) : -Infinity; };
    // integer argmax of a unimodal f on [0, hi]
    const argmax = (f, hi) => {
      let lo = 0;
      while (hi - lo > 8) {
        const m1 = lo + Math.floor((hi - lo) / 3), m2 = hi - Math.floor((hi - lo) / 3);
        if (f(m1) < f(m2)) lo = m1 + 1; else hi = m2 - 1;
      }
      let bn = lo, bv = f(lo);
      for (let n = lo + 1; n <= hi; n++) { const v = f(n); if (v > bv) { bv = v; bn = n; } }
      return [bn, bv];
    };
    const inner = nr => rate ? argmax(ni => val(nr, ni), C - nr) : [0, val(nr, 0)];
    const nr = argmax(n => inner(n)[1], C)[0], ni = inner(nr)[0];
    if (nr + ni === 0 || !(val(nr, ni) > val(0, 0))) return null;
    const v = view(nr, ni), out = [];
    if (nr > 0) out.push({ key: 'res', lfrom: st.res, lto: v.res, lcost: v.lcr });
    if (ni > 0) out.push({ key: 'rew', lfrom: st.rew, lto: v.rew, lcost: v.lci });
    st.S = v.S; st.yDebt = NEG; st.pDebt = NEG; st.res = v.res; st.rew = v.rew;
    return out;
  }

  // ln of the final value for the chosen objective; atEnd: T is the goal date (not the end of a rollout window)
  function finalValue(cfg, st, log, atEnd) {
    if (isReach(cfg) && st.reached !== undefined) {
      if (log) log.final = { lib: lIB(cfg, st), lrate: lRate(cfg, st), lday: lDay(cfg, st), learn: st.lEarn, lS: st.S };
      return reachValue(cfg, st.reached);
    }
    if (cfg.objective === 'bo2') {
      payPrestigeDebt(st);
      const lib = lIB(cfg, st);
      const b = bo2Run(cfg, lHeld(cfg, st), lib, dOf(st));
      if (log) log.final = { lpm: b.lpm0, lpmEnd: b.lpm, lib: lib, lreward: b.tot };
      return st.limitAt !== undefined ? limitValue(st) : b.tot;
    }
    const fs = clone(st);
    // a bank upgrade still saving up on the date is dropped: its points go into the last Ascend
    fs.bankNeed = NEG;
    // point goals keep the prestige: it is the Income that pays the rewards
    if (!INCOME_GOALS[cfg.objective] && canAscend(cfg, fs)) {
      fs.target = HOLD;
      const lP = doAscend(cfg, fs, null);
      if (log) log.finalAscend = { t: fs.t, lP: lP, lgain: lSub(fs.S, spendable(st)), lS: fs.S, lib: lIB(cfg, fs), lrate: lRate(cfg, fs) };
    }
    const fb = atEnd ? finalShop(cfg, fs) : null;
    if (log) {
      if (fb) log.finalBuys = fb;
      log.final = { lib: lIB(cfg, fs), lrate: lRate(cfg, fs), lday: lDay(cfg, fs), learn: st.lEarn, lS: fs.S };
    }
    if (isReach(cfg)) {
      if (metricOf(cfg, fs) >= goalOf(cfg)) { if (log) log.reachedAt = st.t; return reachValue(cfg, st.t); }
      return metricOf(cfg, fs);
    }
    if (st.limitAt !== undefined) return limitValue(st);
    if (cfg.objective === 'networth') return st.lEarn;
    return cfg.objective === 'income' ? lDay(cfg, fs) : lIB(cfg, fs);
  }
  // past the number limit nothing more can be had, so reaching it sooner is better; any ln value under a limit of at
  // most ~14,300 bits stays far below 1e7
  const limitValue = st => 1e7 - st.limitAt;

  // cheap myopic rule used inside rollouts: buy while ln(IB) + growth until min(one week, horizon) improves.
  // bank levels only when withBank (the plan after the rollout budget): inside rollouts they delay every goal
  function heuristicBuys(cfg, st, T, withBank) {
    if (!cfg.allowShop && !(withBank && cfg.allowBank)) return;
    const H = Math.min(168, Math.max(0, T - st.t));
    if (H <= 0) return;
    const P0 = pStar(cfg, paidView(st));
    // point goals: points per day after H hours of holding; otherwise ln(IB) plus its growth over H
    const score = INCOME_GOALS[cfg.objective]
      ? x => { const v = paidView(x); return lDayAfter(cfg, v, lHeld(cfg, v), H); }
      : x => { const v = paidView(x); return lIB(cfg, v) + growthAt(cfg, v, P0) * H; };
    let clicks = cfg.allowShop ? cfg.maxClicks : 0;
    for (let i = 0; i < 40 && clicks >= 1; i++) {
      const cur = score(st);
      let best = null, bv = cur + 1e-6;
      for (const k of shopKeys(cfg)) {
        if (lUpgradeCost(st, k) > spendable(st)) continue;
        const n = Math.min(Math.log(clicks), Math.max(0, lLevelsWithin(st, k, spendable(st) + Math.log(0.02))));
        const s = clone(st);
        applyBuy(cfg, s, { key: k, n: n });
        const v = score(s);
        if (v > bv) { bv = v; best = { key: k, n: n }; }
      }
      if (!best) break;
      applyBuy(cfg, st, best);
      clicks -= Math.round(Math.exp(best.n));
    }
    // bank income is flat since 18.10: a level pays off when its extra interest over H covers its cost
    if (withBank && cfg.allowBank && st.bankLv < 20 && st.bankNeed === NEG && cfg.bankCosts[st.bankLv + 1] > 0) {
      const up = clone(st);
      up.bankLv++;
      const lC = Math.log(cfg.bankCosts[st.bankLv + 1]);
      if (lSub(lRate(cfg, up), lRate(cfg, st)) + Math.log(H) > lC) st.bankNeed = lC;
    }
  }
  // policy: decide() applies purchases and sets st.target; shouldAscend() gates each ascend
  const basePolicy = {
    decide(cfg, st, T) { heuristicBuys(cfg, st, T); st.target = pStar(cfg, paidView(st)); },
    shouldAscend: baseShouldAscend
  };
  const holdPolicy = { decide(cfg, st) { st.target = HOLD; }, shouldAscend: () => false };
  function fixedPolicy(P) {
    return {
      decide(cfg, st) { st.target = snapTarget(cfg, st, Math.log(P)); },
      shouldAscend: baseShouldAscend
    };
  }

  function limitCheck(cfg, st, log) {
    const lW = lAdd(st.Wp, st.L);
    // a b-bit signed integer holds up to 2^(b-1); the networth (bank + everything spent) grows by every point earned
    const lNet = lAdd(ln(cfg.networth || 0), st.lEarn);
    if (Math.max(lW, lNet) > (cfg.limitBits - 1) * LN2) { st.limitAt = st.t; if (log) log.limitAt = st.t; return true; }
    if (lW > L_MAX || st.S > L_MAX) { if (log) log.overflowAt = st.t; return true; }
    return false;
  }

  function run(cfg, st, T, policy, log, firstDone) {
    const lGoal = goalOf(cfg);
    const hit = (t) => {
      if (metricOf(cfg, st) < lGoal) return false;
      st.reached = t; st.stopped = true;
      if (log) log.reachedAt = t;
      return true;
    };
    if (hit(st.t)) return finalValue(cfg, st, log, true);
    if (!firstDone) policy.decide(cfg, st, T, log);
    st.lastDecide = st.t;
    if (hit(st.t)) return finalValue(cfg, st, log, true);
    rebalance(cfg, st);
    const lMinBal = Math.log(cfg.minBal);
    let guard = 0;
    while (st.t < T - 1e-9 && guard++ < 400000) {
      const lI = lBankNow(cfg, st);
      const tr = nextActive(cfg, nextRewardTime(cfg, st));
      const td = nextActive(cfg, st.lastDecide + DECIDE_EVERY);
      // hours until the interest covers a shortfall (none: now; no interest: only rewards can cover it)
      const wait = lShort => lShort === NEG ? 0 : lI === NEG ? Infinity : Math.exp(lShort - lI);
      let te;
      if (st.bankNeed !== NEG) te = nextActive(cfg, st.t + wait(lSub(lAdd(st.bankNeed, lKeep(cfg, st)), st.L)));
      else if (st.target === HOLD) te = Infinity;
      else te = nextActive(cfg, Math.max(st.lastAsc + cfg.minGap, st.t + wait(lSub(lAdd(lCostToP(st.target, dOf(st)), lMinBal), lAdd(st.Wp, st.L)))));
      const tn = Math.min(tr, te, td, T);
      advance(cfg, st, tn - st.t);
      if (limitCheck(cfg, st, log)) { st.stopped = true; break; }
      if (tn >= T - 1e-9) break;
      if (tn === tr && tr <= te) { claimRewards(cfg, st, log); continue; }
      if (tn === td && td < te) {
        if (log) log.samples.push({ t: st.t, lib: lIB(cfg, st), lrate: lRate(cfg, st), lday: lDay(cfg, st), learn: st.lEarn });
        policy.decide(cfg, st, T, log);
        st.lastDecide = st.t;
        if (hit(st.t)) break;
        rebalance(cfg, st);
        continue;
      }
      if (st.bankNeed !== NEG) {
        st.L = lSub(st.L, st.bankNeed); st.bankNeed = NEG; st.bankLv++;
        if (log) log.bank.push({ t: st.t, lv: st.bankLv });
        if (hit(st.t)) break;
        rebalance(cfg, st);
        continue;
      }
      if (policy.shouldAscend(cfg, st, T)) {
        const lPre = lPAff(lSub(lAdd(st.Wp, st.L), lMinBal), dOf(st));
        claimRewards(cfg, st, log, true);
        const tA = st.t;
        doAscend(cfg, st, log);
        if (log) log.ascends[log.ascends.length - 1].lPpre = lPre;
        if (hit(tA)) break;
        policy.decide(cfg, st, T, log);
        st.lastDecide = st.t;
        if (hit(st.t)) break;
        rebalance(cfg, st);
      } else {
        st.target = HOLD;
        rebalance(cfg, st);
      }
    }
    if (!st.stopped) st.t = Math.max(st.t, T);
    return finalValue(cfg, st, log, T >= cfg.horizonH - 1e-9);
  }

  function newLog() { return { ascends: [], rewards: [], bank: [], buys: [], targets: [], samples: [] }; }

  // every level is one click in the bot, so a decision buys at most `clicks` levels in total
  function buyOptions(cfg, st, clicks) {
    const out = [];
    if (clicks < 1) return out;
    if (cfg.allowShop) {
      for (const k of shopKeys(cfg)) {
        if (lUpgradeCost(st, k) > spendable(st)) continue;
        const sp = spendable(st), cap = Math.log(clicks);
        const steps = new Set([0, Math.min(cap, lLevelsWithin(st, k, sp + Math.log(0.04))), Math.min(cap, lLevelsWithin(st, k, sp + Math.log(0.15)))]);
        for (const n of steps) if (n >= 0) out.push({ key: k, n: n });
      }
    }
    if (cfg.allowBank && st.bankLv < 20 && st.bankNeed === NEG && cfg.bankCosts[st.bankLv + 1] > 0) out.push({ key: 'bank', n: 0 });
    return out;
  }

  function rollout(cfg, st, T, targetOverride) {
    const s = clone(st);
    const Te = Math.min(T, st.t + cfg.lookahead);
    const c = Te < T && cfg.objective === 'bo2' ? (cfg._ibCfg || (cfg._ibCfg = Object.assign({}, cfg, { objective: 'ib' }))) : cfg;
    s.target = targetOverride !== undefined ? targetOverride : pStar(cfg, paidView(s));
    return run(c, s, Te, basePolicy, null, true);
  }

  // shards paid to go from level lfrom to lto (both ln)
  function lLevelRangeCost(key, lfrom, lto) {
    const tri = lL => lL === NEG ? NEG : lL + lAdd(lL, 0) - LN2;
    return Math.log(BASE[key]) + lSub(tri(lto), tri(lfrom));
  }
  function logBuy(log, st, key, lfrom, lto, lcost) {
    const rec = { t: st.t, key: key, lfrom: lfrom, lto: lto, lcost: lcost, asc: log.ascends.length };
    log.buys.push(rec);
    const last = log.ascends[log.ascends.length - 1];
    if (last && Math.abs((last.tNext !== undefined ? last.tNext : last.t) - st.t) < 1e-6) last.buys.push(rec);
  }

  // planner: greedy purchases and target choice, each scored by a base-policy rollout
  function plannerPolicy(budget) {
    return {
      decide(cfg, st, T, log) {
        if (budget.left <= 0) {
          if (log && log.fallbackAt === undefined) log.fallbackAt = st.t;
          const before = clone(st);
          heuristicBuys(cfg, st, T, true);
          st.target = pStar(cfg, paidView(st));
          if (log) {
            for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
              const was = k === 'disc' ? ln(before.disc) : before[k], now = k === 'disc' ? ln(st.disc) : st[k];
              if (now > was) logBuy(log, st, k, was, now, lLevelRangeCost(k, was, now));
            }
            if (st.bankNeed !== NEG && before.bankNeed === NEG) logBuy(log, st, 'bank', Math.log(st.bankLv), Math.log(st.bankLv + 1), st.bankNeed);
            log.targets.push({ t: st.t, target: st.target, pstar: st.target, fallback: true });
          }
          return;
        }
        let quota = Math.max(12, Math.min(160, Math.floor(budget.left / 25)));
        let iter = 0, clicks = cfg.maxClicks;
        while (iter++ < 12 && quota > 0 && budget.left > 0) {
          const opts = buyOptions(cfg, st, clicks);
          if (!opts.length) break;
          const base = rollout(cfg, st, T); budget.left--; quota--;
          let best = null, bv = base + cfg.buyMargin;
          for (const o of opts) {
            const s = clone(st);
            applyBuy(cfg, s, o);
            const v = rollout(cfg, s, T); budget.left--; quota--;
            if (v > bv) { bv = v; best = o; }
          }
          if (!best) break;
          const lfrom = best.key === 'bank' ? Math.log(st.bankLv) : best.key === 'disc' ? ln(st.disc) : st[best.key];
          const lcost = applyBuy(cfg, st, best);
          clicks -= best.key === 'bank' ? 1 : Math.round(Math.exp(best.n));
          const lto = best.key === 'bank' ? Math.log(st.bankLv + 1) : best.key === 'disc' ? ln(st.disc) : st[best.key];
          if (log) logBuy(log, st, best.key, lfrom, lto, lcost);
          if (best.key === 'bank') break;
        }
        const ps = pStar(cfg, paidView(st));
        const lW = lAdd(st.Wp, st.L);
        const cands = new Set([HOLD]);
        for (const m of [0.55, 0.75, 0.9, 1, 1.12, 1.3, 1.6, 2, 2.6]) cands.add(snapTarget(cfg, st, ps + Math.log(m)));
        cands.add(snapTarget(cfg, st, Math.log(cfg.minP)));
        const aff = lPAff(lSub(lW, Math.log(cfg.minBal)), dOf(st));
        if (aff >= Math.log(cfg.minP)) {
          cands.add(snapTarget(cfg, st, aff));
          if (aff > ps) for (const m of [1.05, 1.15, 1.3, 1.6, 2]) cands.add(snapTarget(cfg, st, aff + Math.log(m)));
        }
        let bestT = ps, bestV = -Infinity;
        for (const P of cands) {
          const v = rollout(cfg, st, T, P); budget.left--;
          if (v > bestV + 1e-12) { bestV = v; bestT = P; }
        }
        st.target = bestT;
        if (log) log.targets.push({ t: st.t, target: bestT, pstar: ps });
      },
      shouldAscend: baseShouldAscend
    };
  }

  function sample(cfg, st0, T, policy) {
    const st = clone(st0);
    const log = newLog();
    const value = run(cfg, st, T, policy, log, false);
    // chart points: start, daily samples, each Ascend (points per day drop there with the prestige), end
    const pts = [{ t: st0.t, lib: lIB(cfg, st0), lrate: lRate(cfg, st0), lday: lDay(cfg, st0), learn: NEG }];
    const mid = log.samples.slice();
    for (const a of log.ascends) {
      mid.push({ t: a.t - 1e-6, lib: null, lrate: a.lrate, lday: a.ldayPre, learn: a.learn });
      mid.push({ t: a.t, lib: a.lib, lrate: a.lrate, lday: a.lday, learn: a.learn });
    }
    mid.sort((x, y) => x.t - y.t);
    for (const p of mid) pts.push(Object.assign({}, p, { lib: p.lib === null ? pts[pts.length - 1].lib : p.lib }));
    const tEnd = st.stopped ? st.t : T;
    if (log.final && log.final.lrate !== undefined) pts.push({ t: tEnd, lib: log.final.lib, lrate: log.final.lrate, lday: log.final.lday, learn: log.final.learn });
    else pts.push({ t: tEnd, lib: lIB(cfg, st), lrate: lRate(cfg, st), lday: lDay(cfg, st), learn: st.lEarn });
    return { value: value, log: log, pts: pts, stoppedAt: st.stopped ? st.t : null };
  }

  function plan(cfg) {
    const T = cfg.horizonH;
    const st0 = initState(cfg, 0);
    settleHeld(cfg, st0);
    const budget = { left: cfg.budget || 2000 };
    const res = {
      cfg: cfg,
      now: { lib: lIB(cfg, st0), lrate: lRate(cfg, st0), lday: lDay(cfg, st0), lreserve: lReserve(cfg, st0), pm: cfg.R * (cfg.P + 1) },
      optimal: sample(cfg, st0, T, plannerPolicy(budget)),
      baselines: []
    };
    const noShop = Object.assign({}, cfg, { allowShop: false, allowBank: false });
    res.baselines.push({ name: 'hold', run: sample(noShop, st0, T, holdPolicy) });
    res.baselines.push({ name: 'pstar', run: sample(noShop, st0, T, basePolicy) });
    for (const P of [1000, 1500, 2000, 3000]) res.baselines.push({ name: 'p' + P, P: P, run: sample(noShop, st0, T, fixedPolicy(P)) });
    return res;
  }

  const api = {
    F, HOLD, NEG, LN10, defaults, bonusAt, storageAt, storageOf, claimFactor, activeHours, bankCostTable, lAdd, lSub, lIB, lRate, lPm, lPAff, lCostToP, lReserve,
    lEff, lDay, lDayAt, lHeld, lKeep, costToPD, cumPR, pAffD, reserveOf, dOf, initState, settleHeld, plan, blockSum
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.NexusModel = api;
})(typeof window !== 'undefined' ? window : globalThis);
