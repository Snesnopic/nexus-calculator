(function (root) {
  'use strict';

  // every quantity that can grow without bound (points, shards, prestige, levels, multipliers)
  // is stored as its natural log; NEG stands for zero. This reaches about 10^(10^307).
  const F = 82087500;          // full prestige cost at P0; rank r->r+1 costs 250 r^2 (P+1)
  const RANK_K = 250;
  const HOLD = Infinity;
  const NEG = -Infinity;
  const KINDS = ['daily', 'prime', 'weekly', 'monthly'];
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

  // known: Lv12 1.5T .. Lv16 150T; the rest follows the same x3.33 / x3 alternation
  function bankCostTable() {
    const t = {};
    for (let L = 2; L <= 20; L++) {
      const k = L - 16;
      const e = Math.floor(k / 2), odd = ((k % 2) + 2) % 2;
      t[L] = (odd ? 500e12 : 150e12) * Math.pow(10, e);
    }
    return t;
  }

  function defaults() {
    return {
      shards: 70, prime: true, server: 1.0, other: 0,
      res: 1, yld: 0, intr: 1, rew: 0, disc: 0,
      P: 1000, R: 1, bal: 6616699127772,
      bankLv: 15, bankBonus: 1.70, rate: 0.1125, rawCap: 1e11, storage: 40, activeFrom: 9, activeTo: 22, clock0: 0,
      bankCosts: bankCostTable(),
      rewBase: { daily: 1e5, prime: 1e5, weekly: 1e6, monthly: 1e7 },
      cooldown: { daily: 24, prime: 24, weekly: 168, monthly: 720 },
      nextIn: { daily: 24, prime: 24, weekly: 168, monthly: 720 },
      loan: true, floorShards: true, allowShop: true, allowBank: true,
      minP: 1000, minBal: 0, minGap: 1, lookahead: 336, useRewards: true, deferFrac: 0.25, buyMargin: Math.log(1.01),
      limitBits: Infinity, maxClicks: 100,
      objective: 'ib', horizonH: 1400, round: 150, reinvest: false, targetIB: 1000, targetRate: 1e14
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
  function reserveOf(cfg) { return cfg.rawCap / cfg.rate; }

  // ---- base formulas (log domain) ----
  function constIB(cfg) { return 1 + (cfg.prime ? 0.5 : 0) + Math.min(cfg.server + cfg.other, 10); }
  function lShardValue(cfg, st) { return Math.log(cfg.prime ? 0.12 : 0.10) + lTenth(st.res); }
  function lIB(cfg, st) { return lAdd(Math.log(constIB(cfg)), lShardValue(cfg, st) + st.S); }
  function bankBonusOf(cfg, st) { return cfg.bankBonus + 0.05 * (st.bankLv - cfg.bankLv); }
  // storage grows 4h per bank level; claiming less often than it fills loses the excess hours
  function storageOf(cfg, st) { return Math.max(4, cfg.storage + 4 * (st.bankLv - cfg.bankLv)); }
  // the player acts only inside a daily window of local hours; clock0 is the local hour at t = 0
  function activeHours(cfg) { const a = ((cfg.activeTo - cfg.activeFrom) % 24 + 24) % 24; return a === 0 ? 24 : a; }
  function nextActive(cfg, t) {
    if (!isFinite(t) || activeHours(cfg) >= 24) return t;
    const since = ((cfg.clock0 + t - cfg.activeFrom) % 24 + 24) % 24;
    return since < activeHours(cfg) - 1e-9 ? t : t + (24 - since);
  }
  // interest piles up while you are away, but only for as many hours as the storage holds
  function claimFactor(cfg, st) { return Math.min(1, (activeHours(cfg) + storageOf(cfg, st)) / 24); }
  function lRate(cfg, st) { return Math.log(cfg.rawCap * bankBonusOf(cfg, st) * claimFactor(cfg, st)) + lTenth(st.intr) + lIB(cfg, st); }
  function dOf(st) { return 1 - 0.05 * st.disc; }
  function lReserve(cfg) { return Math.log(reserveOf(cfg)); }
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
  function lRho(cfg, st) {
    if (!cfg.useRewards) return NEG;
    const b = cfg.rewBase, c = cfg.cooldown;
    let r = b.daily / c.daily + b.weekly / c.weekly + b.monthly / c.monthly;
    if (cfg.prime) r += b.prime / c.prime;
    return Math.log(r) + lTenth(st.rew);
  }
  function blockSum(round) {
    let s = 0;
    for (let R = 10; R <= round; R += 5) s += Math.pow(1.4, R / 5 - 1);
    return s;
  }

  // ---- shard shop ----
  const BASE = { res: 5, yld: 5, intr: 5, rew: 3, disc: 5 };
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
  function growthAt(cfg, st, lP) {
    const d = dOf(st);
    const lC = lCostToP(lP, d);
    const lI = lRate(cfg, st);
    const lIB0 = lIB(cfg, st);
    const lNeed = lAdd(lC, Math.log(cfg.minBal));
    const lRr = lRho(cfg, st) + lIB0 + Math.log(100 * 2 / 3) + lP + lC - lNeed;
    const dt = Math.max(cfg.minGap, Math.exp(lNeed - lAdd(lI, lRr)));
    const lGain = lShardsAt(cfg, st, lP);
    const lIB1 = lAdd(lIB0, lShardValue(cfg, st) + lGain);
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
    const N = 48;
    let best = lo, bg = -Infinity;
    for (let i = 0; i <= N; i++) {
      const x = lo + (hi - lo) * i / N;
      const g = growthAt(cfg, st, x);
      if (g > bg) { bg = g; best = x; }
    }
    let a = Math.max(lo, best - (hi - lo) / N), b = Math.min(hi, best + (hi - lo) / N);
    const phi = (Math.sqrt(5) - 1) / 2;
    for (let i = 0; i < 40; i++) {
      const x1 = b - phi * (b - a), x2 = a + phi * (b - a);
      if (growthAt(cfg, st, x1) > growthAt(cfg, st, x2)) b = x2; else a = x1;
    }
    const lP = (a + b) / 2;
    if (cfg.floorShards && lShardsRaw(st, lP) < Math.log(1e6)) {
      const k0 = Math.floor(Math.exp(lShardsRaw(st, lP)));
      let bk = snapTarget(cfg, st, lP), bgk = -Infinity;
      for (let k = Math.max(1, k0 - 4); k <= k0 + 5; k++) {
        const Pk = Math.max(lo, lMinPforShards(st, k));
        const g = growthAt(cfg, st, Pk);
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
      next: {}, heldP: cfg.P, heldR: cfg.R
    };
    for (const k of KINDS) st.next[k] = st.t + Math.max(0, cfg.nextIn[k]);
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
    const lRes = lReserve(cfg);
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
    st.L = lAdd(st.L, lRate(cfg, st) + Math.log(dt));
    st.t += dt;
    rebalance(cfg, st);
  }
  function deferOf(cfg, st, k) {
    return (k === 'weekly' || k === 'monthly') && st.target !== HOLD ? cfg.deferFrac * cfg.cooldown[k] : 0;
  }
  // weekly and monthly wait (up to deferFrac of their cooldown) for the next ascend, where prestige peaks
  function claimRewards(cfg, st, log, atAscend) {
    if (!cfg.useRewards) return;
    const dueNow = k => (atAscend ? st.next[k] : st.next[k] + deferOf(cfg, st, k)) <= st.t + 1e-9;
    if (KINDS.some(k => (k !== 'prime' || cfg.prime) && dueNow(k))) payPrestigeDebt(st);
    const lpm = lPm(st.Wp, dOf(st));
    const lib = lIB(cfg, st);
    for (const k of KINDS) {
      if (k === 'prime' && !cfg.prime) continue;
      const due = atAscend ? st.next[k] : st.next[k] + deferOf(cfg, st, k);
      if (due <= st.t + 1e-9) {
        const amt = Math.log(cfg.rewBase[k]) + lpm + lib + lTenth(st.rew);
        st.L = lAdd(st.L, amt);
        st.next[k] = st.t + cfg.cooldown[k];
        if (log) log.rewards.push({ t: st.t, kind: k, lpm: lpm, lamount: amt });
      }
    }
    rebalance(cfg, st);
  }
  function nextRewardTime(cfg, st) {
    if (!cfg.useRewards) return Infinity;
    let m = Infinity;
    for (const k of KINDS) {
      if (k === 'prime' && !cfg.prime) continue;
      const due = st.next[k] + deferOf(cfg, st, k);
      if (due < m) m = due;
    }
    return m;
  }
  function restartPenalty(cfg, st) {
    if (cfg.loan) return 0;
    const lib = lIB(cfg, st);
    const lb0 = Math.log(cfg.rewBase.daily * (cfg.prime ? 2 : 1)) + lib;
    const lk = Math.log(cfg.rate * bankBonusOf(cfg, st)) + lTenth(st.intr) + lib;
    return Math.max(0, (lReserve(cfg) - lb0) / Math.exp(Math.min(lk, 700)));
  }
  function doAscend(cfg, st, log) {
    const d = dOf(st);
    const lW = lAdd(st.Wp, st.L);
    const lP = Math.max(st.target === HOLD ? NEG : st.target, lPAff(lSub(lW, Math.log(cfg.minBal)), d));
    if (st.yDebt !== NEG) { st.S = lSub(st.S, st.yDebt); st.yDebt = NEG; }
    payPrestigeDebt(st);
    const gain = lShardsAt(cfg, st, lP);
    st.S = lAdd(st.S, gain);
    if (log) log.ascends.push({ t: st.t, lP: lP, lgain: gain, lS: st.S, lib: lIB(cfg, st), lrate: lRate(cfg, st), buys: [] });
    st.Wp = NEG; st.L = NEG; st.heldP = null; st.lastAsc = st.t;
    const pen = restartPenalty(cfg, st);
    if (pen > 0) st.t += pen;
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
      const lRes = lReserve(cfg);
      const lIh = lRate(cfg, st);
      const vh = lPm(lSub(lAdd(lW, lIh + Math.log(rem)), lRes), d) + lIB(cfg, st);
      const va = lPm(lSub(lI1 + Math.log(rem), lRes), d) + lIB(cfg, after);
      return va > vh;
    }
    const fresh = Math.exp(lAdd(lCostToP(Math.log(cfg.minP), d), Math.log(cfg.minBal)) - lI1);
    return fresh < rem;
  }

  // 'reach' targets an Income Bonus, 'reachRate' a bank income per hour; reaching it sooner always beats
  // not reaching it, whose value is ln(metric) < ln(target)
  const isReach = cfg => cfg.objective === 'reach' || cfg.objective === 'reachRate';
  const goalOf = cfg => cfg.objective === 'reach' ? Math.log(cfg.targetIB) : cfg.objective === 'reachRate' ? Math.log(cfg.targetRate) : Infinity;
  const metricOf = (cfg, st) => cfg.objective === 'reachRate' ? lRate(cfg, st) : lIB(cfg, st);
  const reachValue = (cfg, t) => goalOf(cfg) + 1e6 - t;

  // ln of the final value for the chosen objective
  function finalValue(cfg, st, log) {
    if (isReach(cfg) && st.reached !== undefined) {
      if (log) log.final = { lib: lIB(cfg, st), lrate: lRate(cfg, st), lS: st.S };
      return reachValue(cfg, st.reached);
    }
    if (cfg.objective === 'bo2') {
      payPrestigeDebt(st);
      const lib = lIB(cfg, st);
      const d = dOf(st);
      let lWp = lAdd(st.Wp, lSub(st.L, lReserve(cfg)));
      let lpm = lPm(lWp, d);
      const lpm0 = lpm;
      let tot = NEG;
      for (let R = 10; R <= cfg.round; R += 5) {
        const r = Math.log(1500) + lpm + lib + (R / 5 - 1) * Math.log(1.4);
        tot = lAdd(tot, r);
        if (cfg.reinvest) { lWp = lAdd(lWp, r); lpm = lPm(lWp, d); }
      }
      if (log) log.final = { lpm: lpm0, lpmEnd: lpm, lib: lib, lreward: tot };
      return tot;
    }
    const fs = clone(st);
    if (canAscend(cfg, fs)) {
      fs.target = HOLD;
      const lP = doAscend(cfg, fs, null);
      if (log) log.finalAscend = { t: fs.t, lP: lP, lgain: lSub(fs.S, spendable(st)), lS: fs.S, lib: lIB(cfg, fs), lrate: lRate(cfg, fs) };
    }
    if (log) log.final = { lib: lIB(cfg, fs), lrate: lRate(cfg, fs), lS: fs.S };
    if (isReach(cfg)) {
      if (metricOf(cfg, fs) >= goalOf(cfg)) { if (log) log.reachedAt = st.t; return reachValue(cfg, st.t); }
      return metricOf(cfg, fs);
    }
    return cfg.objective === 'income' ? lRate(cfg, fs) : lIB(cfg, fs);
  }

  // cheap myopic shop rule used inside rollouts: buy while ln(IB) + growth until min(one week, horizon) improves
  function heuristicBuys(cfg, st, T) {
    if (!cfg.allowShop) return;
    const H = Math.min(168, Math.max(0, T - st.t));
    if (H <= 0) return;
    const P0 = pStar(cfg, paidView(st));
    const score = x => { const v = paidView(x); return lIB(cfg, v) + growthAt(cfg, v, P0) * H; };
    let clicks = cfg.maxClicks;
    for (let i = 0; i < 40 && clicks >= 1; i++) {
      const cur = score(st);
      let best = null, bv = cur + 1e-6;
      for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
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
  }
  // policy: decide() applies purchases and sets st.target; shouldAscend() gates each ascend
  const basePolicy = {
    decide(cfg, st, T) { heuristicBuys(cfg, st, T); st.target = pStar(cfg, paidView(st)); },
    shouldAscend: baseShouldAscend
  };
  function fixedPolicy(P) {
    return {
      decide(cfg, st) { st.target = snapTarget(cfg, st, Math.log(P)); },
      shouldAscend: baseShouldAscend
    };
  }

  function limitCheck(cfg, st, log) {
    const lW = lAdd(st.Wp, st.L);
    if (lW > cfg.limitBits * LN2) { if (log) log.limitAt = st.t; return true; }
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
    if (hit(st.t)) return finalValue(cfg, st, log);
    if (!firstDone) policy.decide(cfg, st, T, log);
    rebalance(cfg, st);
    const lMinBal = Math.log(cfg.minBal);
    let guard = 0;
    while (st.t < T - 1e-9 && guard++ < 400000) {
      const lI = lRate(cfg, st);
      const tr = nextActive(cfg, nextRewardTime(cfg, st));
      let te;
      if (st.bankNeed !== NEG) te = nextActive(cfg, st.t + Math.exp(lSub(st.bankNeed, st.L) - lI));
      else if (st.target === HOLD) te = Infinity;
      else te = nextActive(cfg, Math.max(st.lastAsc + cfg.minGap, st.t + Math.exp(lSub(lAdd(lCostToP(st.target, dOf(st)), lMinBal), lAdd(st.Wp, st.L)) - lI)));
      const tn = Math.min(tr, te, T);
      advance(cfg, st, tn - st.t);
      if (limitCheck(cfg, st, log)) { st.stopped = true; break; }
      if (tn >= T - 1e-9) break;
      if (tn === tr && tr <= te) { claimRewards(cfg, st, log); continue; }
      if (st.bankNeed !== NEG) {
        st.L = lSub(st.L, st.bankNeed); st.bankNeed = NEG; st.bankLv++;
        if (log) log.bank.push({ t: st.t, lv: st.bankLv });
        if (hit(st.t)) break;
        rebalance(cfg, st);
        continue;
      }
      if (policy.shouldAscend(cfg, st, T)) {
        claimRewards(cfg, st, log, true);
        const tA = st.t;
        doAscend(cfg, st, log);
        if (hit(tA)) break;
        policy.decide(cfg, st, T, log);
        if (cfg.objective === 'reachRate' && hit(st.t)) break;
        rebalance(cfg, st);
      } else {
        st.target = HOLD;
        rebalance(cfg, st);
      }
    }
    if (!st.stopped) st.t = Math.max(st.t, T);
    return finalValue(cfg, st, log);
  }

  function newLog() { return { ascends: [], rewards: [], bank: [], buys: [], targets: [] }; }

  // every level is one click in the bot, so a decision buys at most `clicks` levels in total
  function buyOptions(cfg, st, clicks) {
    const out = [];
    if (clicks < 1) return out;
    if (cfg.allowShop) {
      for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
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
    const c = Te < T && !isReach(cfg) ? (cfg._ibCfg || (cfg._ibCfg = Object.assign({}, cfg, { objective: 'ib' }))) : cfg;
    s.target = targetOverride !== undefined ? targetOverride : pStar(cfg, paidView(s));
    return run(c, s, Te, basePolicy, null, true);
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
          const before = clone(st);
          basePolicy.decide(cfg, st, T);
          if (log) {
            for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
              const was = k === 'disc' ? ln(before.disc) : before[k], now = k === 'disc' ? ln(st.disc) : st[k];
              if (now > was) logBuy(log, st, k, was, now, NEG);
            }
            log.targets.push({ t: st.t, target: st.target, pstar: st.target });
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
        if (aff >= Math.log(cfg.minP)) cands.add(snapTarget(cfg, st, aff));
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
    const pts = [{ t: st0.t, lib: lIB(cfg, st0), lrate: lRate(cfg, st0) }];
    for (const a of log.ascends) pts.push({ t: a.t, lib: a.lib, lrate: a.lrate });
    if (log.finalAscend) pts.push({ t: T, lib: log.finalAscend.lib, lrate: log.finalAscend.lrate });
    else pts.push({ t: st.stopped ? st.t : T, lib: lIB(cfg, st), lrate: lRate(cfg, st) });
    return { value: value, log: log, pts: pts, stoppedAt: st.stopped ? st.t : null };
  }

  function plan(cfg) {
    const T = cfg.horizonH;
    const st0 = initState(cfg, 0);
    settleHeld(cfg, st0);
    const budget = { left: cfg.budget || 500 };
    const res = {
      cfg: cfg,
      now: { lib: lIB(cfg, st0), lrate: lRate(cfg, st0), pm: cfg.R * (cfg.P + 1) },
      optimal: sample(cfg, st0, T, plannerPolicy(budget)),
      baselines: []
    };
    const noShop = Object.assign({}, cfg, { allowShop: false, allowBank: false });
    res.baselines.push({ name: 'pstar', run: sample(noShop, st0, T, basePolicy) });
    for (const P of [1000, 1500, 2000, 3000]) res.baselines.push({ name: 'p' + P, P: P, run: sample(noShop, st0, T, fixedPolicy(P)) });
    return res;
  }

  const api = {
    F, HOLD, NEG, LN10, defaults, storageOf, claimFactor, activeHours, bankCostTable, lAdd, lSub, lIB, lRate, lPm, lPAff, lCostToP, lReserve,
    costToPD, cumPR, pAffD, reserveOf, dOf, initState, settleHeld, plan, blockSum
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.NexusModel = api;
})(typeof window !== 'undefined' ? window : globalThis);
