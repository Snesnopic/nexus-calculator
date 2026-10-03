(function (root) {
  'use strict';

  // full prestige cost at P0 (rank 1->100); rank r->r+1 costs 250 r^2 (P+1)
  const F = 82087500;
  const RANK_K = 250;
  const HOLD = Infinity;
  const KINDS = ['daily', 'prime', 'weekly', 'monthly'];

  const sumSq = n => (n <= 0 ? 0 : n * (n + 1) * (2 * n + 1) / 6);

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
      bankLv: 15, bankBonus: 1.70, rate: 0.1125, rawCap: 1e11,
      bankCosts: bankCostTable(),
      rewBase: { daily: 1e5, prime: 1e5, weekly: 1e6, monthly: 1e7 },
      cooldown: { daily: 24, prime: 24, weekly: 168, monthly: 720 },
      nextIn: { daily: 24, prime: 24, weekly: 168, monthly: 720 },
      loan: true, floorShards: true, allowShop: true, allowBank: true,
      minP: 1000, minBal: 50e12, minGap: 12, lookahead: 336, useRewards: true, deferFrac: 0.25, buyMargin: Math.log(1.01),
      objective: 'ib', horizonH: 1400, round: 150, reinvest: false
    };
  }

  // ---- base formulas ----
  function shardValue(cfg, st) { return (cfg.prime ? 0.12 : 0.10) * (1 + 0.1 * st.res); }
  function ibOf(cfg, st) {
    return 1 + (cfg.prime ? 0.5 : 0) + Math.min(cfg.server + cfg.other, 10) + shardValue(cfg, st) * st.S;
  }
  function bankBonusOf(cfg, st) { return cfg.bankBonus + 0.05 * (st.bankLv - cfg.bankLv); }
  function bankRateOf(cfg, st) { return cfg.rawCap * bankBonusOf(cfg, st) * (1 + 0.1 * st.intr) * ibOf(cfg, st); }
  function dOf(st) { return 1 - 0.05 * st.disc; }
  function reserveOf(cfg) { return cfg.rawCap / cfg.rate; }
  function costToP(P, d) { return d * F * P * (P + 1) / 2; }
  function cumPR(P, R, d) { return d * (F * P * (P + 1) / 2 + (P + 1) * RANK_K * sumSq(R - 1)); }
  function pAff(W, d) {
    if (!(W > 0)) return 0;
    const x = Math.floor((-1 + Math.sqrt(1 + 8 * W / (d * F))) / 2 + 1e-9);
    return costToP(x, d) <= W * (1 + 1e-12) ? x : x - 1;
  }
  // best (P+1)*R affordable with W: sitting at R100 of P is worth 100(P+1)
  function pmAt(W, d) {
    const Q = pAff(W, d);
    if (Q >= 1) return 100 * Q;
    if (!(W > 0)) return 1;
    let R = Math.floor(Math.cbrt(3 * W / (RANK_K * d))) + 1;
    while (R > 1 && d * RANK_K * sumSq(R - 1) > W) R--;
    return Math.max(1, Math.min(100, R));
  }
  function shardsRaw(st, P) { return 10 * (P / 1000) * (P / 1000) * (1 + 0.1 * st.yld); }
  function shardsAt(cfg, st, P) {
    const v = shardsRaw(st, P);
    return cfg.floorShards ? Math.floor(v + 1e-9) : v;
  }
  function minPforShards(st, k) {
    let P = Math.ceil(1000 * Math.sqrt(k / (10 * (1 + 0.1 * st.yld))) - 1e-9);
    for (let i = 0; i < 3 && shardsRaw(st, P) * (1 + 1e-12) < k; i++) P++;
    return P;
  }
  function rhoOf(cfg, st) {
    const b = cfg.rewBase, c = cfg.cooldown;
    let r = b.daily / c.daily + b.weekly / c.weekly + b.monthly / c.monthly;
    if (cfg.prime) r += b.prime / c.prime;
    return r * (1 + 0.1 * st.rew);
  }
  function upgradeCost(st, key) {
    const L = st[key];
    if (key === 'rew') return 3 * (L + 1);
    if (key === 'disc' && L >= 5) return Infinity;
    return 5 * (L + 1);
  }
  function blockSum(round) {
    let s = 0;
    for (let R = 10; R <= round; R += 5) s += Math.pow(1.4, R / 5 - 1);
    return s;
  }

  // ---- P* maximizing log growth of IB per hour ----
  function growthAt(cfg, st, P) {
    const d = dOf(st);
    const C = costToP(P, d);
    const I = bankRateOf(cfg, st);
    const ib0 = ibOf(cfg, st);
    const rr = rhoOf(cfg, st) * ib0 * 100 * (2 / 3) * P * (C / (C + cfg.minBal));
    const dt = (C + cfg.minBal) / (I + rr);
    const gain = shardsAt(cfg, st, P);
    const ib1 = ib0 + shardValue(cfg, st) * gain;
    return Math.log(ib1 / ib0) / dt;
  }
  function snapTarget(cfg, st, P) {
    P = Math.max(cfg.minP, Math.round(P));
    if (!cfg.floorShards || shardsRaw(st, P) >= 1e6) return P;
    const k = Math.max(shardsAt(cfg, st, cfg.minP), Math.floor(shardsRaw(st, P) + 1e-9));
    return Math.max(cfg.minP, minPforShards(st, k));
  }
  function pStar(cfg, st) {
    let best = cfg.minP, bg = -Infinity;
    const lo = Math.log(cfg.minP);
    const hi = Math.log(Math.max(cfg.minP * 400, 20 * pAff(bankRateOf(cfg, st) * 240, dOf(st))));
    const N = 48;
    for (let i = 0; i <= N; i++) {
      const P = Math.exp(lo + (hi - lo) * i / N);
      const g = growthAt(cfg, st, P);
      if (g > bg) { bg = g; best = P; }
    }
    let a = Math.max(lo, Math.log(best) - (hi - lo) / N), b = Math.min(hi, Math.log(best) + (hi - lo) / N);
    const phi = (Math.sqrt(5) - 1) / 2;
    for (let i = 0; i < 40; i++) {
      const x1 = b - phi * (b - a), x2 = a + phi * (b - a);
      if (growthAt(cfg, st, Math.exp(x1)) > growthAt(cfg, st, Math.exp(x2))) b = x2; else a = x1;
    }
    let P = Math.exp((a + b) / 2);
    if (cfg.floorShards && shardsRaw(st, P) < 1e6) {
      const k0 = Math.floor(shardsRaw(st, P));
      let bk = snapTarget(cfg, st, P), bgk = -Infinity;
      for (let k = Math.max(1, k0 - 4); k <= k0 + 5; k++) {
        const Pk = Math.max(cfg.minP, minPforShards(st, k));
        const g = growthAt(cfg, st, Pk);
        if (g > bgk) { bgk = g; bk = Pk; }
      }
      return bk;
    }
    return Math.max(cfg.minP, Math.round(P));
  }

  // ---- event-driven simulation ----
  function initState(cfg, t0) {
    const st = {
      t: t0 || 0, S: cfg.shards, res: cfg.res, yld: cfg.yld, intr: cfg.intr, rew: cfg.rew, disc: cfg.disc,
      bankLv: cfg.bankLv, Wp: 0, L: 0, target: HOLD, bankNeed: 0, asc: 0, gained: 0, lastAsc: -Infinity,
      next: {}, heldP: cfg.P, heldR: cfg.R
    };
    for (const k of KINDS) st.next[k] = st.t + Math.max(0, cfg.nextIn[k]);
    return st;
  }
  // held prestige is valued at the current discount
  function settleHeld(cfg, st) {
    if (st.heldP === null) return;
    st.Wp = cumPR(st.heldP, st.heldR, dOf(st));
    st.L = cfg.bal;
  }
  function clone(st) {
    const c = Object.assign({}, st);
    c.next = Object.assign({}, st.next);
    return c;
  }
  function rebalance(cfg, st) {
    if (st.bankNeed > 0) return;
    const res = reserveOf(cfg);
    const Ct = st.target === HOLD ? Infinity : costToP(st.target, dOf(st));
    if (st.L > res && st.Wp < Ct) {
      const mv = Math.min(st.L - res, Ct - st.Wp);
      st.Wp += mv; st.L -= mv;
    }
  }
  const INT64 = 9.223372036854776e18;
  function advance(cfg, st, dt) {
    if (dt <= 0) return;
    st.L += bankRateOf(cfg, st) * dt;
    st.t += dt;
    rebalance(cfg, st);
  }
  function markLimit(st, log, amount) {
    if (log && log.int64At === undefined && (amount > INT64 || st.L > INT64)) log.int64At = st.t;
  }
  function deferOf(cfg, st, k) {
    return (k === 'weekly' || k === 'monthly') && st.target !== HOLD ? cfg.deferFrac * cfg.cooldown[k] : 0;
  }
  // weekly and monthly wait (up to deferFrac of their cooldown) for the next ascend, where prestige peaks
  function claimRewards(cfg, st, log, atAscend) {
    if (!cfg.useRewards) return;
    const pm = pmAt(st.Wp, dOf(st));
    const ib = ibOf(cfg, st);
    for (const k of KINDS) {
      if (k === 'prime' && !cfg.prime) continue;
      const due = atAscend ? st.next[k] : st.next[k] + deferOf(cfg, st, k);
      if (due <= st.t + 1e-9) {
        const amt = cfg.rewBase[k] * pm * ib * (1 + 0.1 * st.rew);
        st.L += amt;
        markLimit(st, log, amt);
        st.next[k] = st.t + cfg.cooldown[k];
        if (log) log.rewards.push({ t: st.t, kind: k, pm: pm, amount: amt });
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
    const ib = ibOf(cfg, st);
    const b0 = cfg.rewBase.daily * ib * (cfg.prime ? 2 : 1);
    const k = cfg.rate * bankBonusOf(cfg, st) * (1 + 0.1 * st.intr) * ib;
    return Math.max(0, Math.log(reserveOf(cfg) / b0) / k);
  }
  function doAscend(cfg, st, log) {
    const d = dOf(st);
    const P = Math.max(st.target === HOLD ? 0 : st.target, pAff(st.Wp + st.L - cfg.minBal, d));
    const Pe = cfg.floorShards ? Math.max(cfg.minP, minPforShards(st, shardsAt(cfg, st, P))) : P;
    const gain = shardsAt(cfg, st, P);
    st.S += gain; st.gained += gain; st.asc++;
    if (log) log.ascends.push({ t: st.t, P: P, Pmin: Pe, gain: gain, S: st.S, ib: ibOf(cfg, st), rate: bankRateOf(cfg, st), buys: [] });
    st.Wp = 0; st.L = 0; st.heldP = null; st.lastAsc = st.t;
    const pen = restartPenalty(cfg, st);
    if (pen > 0) st.t += pen;
    return P;
  }
  function canAscend(cfg, st) {
    return st.bankNeed <= 0 && pAff(st.Wp + st.L - cfg.minBal, dOf(st)) >= cfg.minP;
  }

  // end-of-horizon rule of the base policy
  function baseShouldAscend(cfg, st, T) {
    const rem = T - st.t;
    const gain = shardsAt(cfg, st, Math.max(st.target, pAff(st.Wp + st.L - cfg.minBal, dOf(st))));
    const after = clone(st); after.S += gain;
    const I1 = bankRateOf(cfg, after);
    if (cfg.objective === 'bo2') {
      const res = reserveOf(cfg);
      const Ih = bankRateOf(cfg, st);
      const vh = pmAt(st.Wp + st.L + Ih * rem - res, dOf(st)) * ibOf(cfg, st);
      const va = pmAt(I1 * rem - res, dOf(st)) * ibOf(cfg, after);
      return va > vh;
    }
    const fresh = (costToP(cfg.minP, dOf(st)) + cfg.minBal) / I1;
    return fresh < rem;
  }

  // final value for the chosen objective
  function finalValue(cfg, st, log) {
    if (cfg.objective === 'bo2') {
      const ib = ibOf(cfg, st);
      const d = dOf(st);
      let Wp = st.Wp + Math.max(0, st.L - reserveOf(cfg));
      let pm = pmAt(Wp, d);
      const pm0 = pm;
      let tot = 0;
      for (let R = 10; R <= cfg.round; R += 5) {
        const r = 1500 * pm * ib * Math.pow(1.4, R / 5 - 1);
        tot += r;
        if (cfg.reinvest) { Wp += r; pm = pmAt(Wp, d); }
      }
      if (log) log.final = { pm: pm0, pmEnd: pm, ib: ib, reward: tot };
      return tot;
    }
    const fs = clone(st);
    if (canAscend(cfg, fs)) {
      fs.target = HOLD;
      const P = doAscend(cfg, fs, null);
      if (log) log.finalAscend = { t: fs.t, P: P, gain: fs.S - st.S, S: fs.S, ib: ibOf(cfg, fs), rate: bankRateOf(cfg, fs) };
    }
    if (log) log.final = { ib: ibOf(cfg, fs), rate: bankRateOf(cfg, fs), S: fs.S };
    return cfg.objective === 'income' ? bankRateOf(cfg, fs) : ibOf(cfg, fs);
  }

  // policy: decide() applies purchases and sets st.target; shouldAscend() gates each ascend
  // cheap myopic shop rule used inside rollouts: buy while ln(IB) + one week of growth improves
  function heuristicBuys(cfg, st) {
    if (!cfg.allowShop) return;
    const H = 168;
    const P0 = pStar(cfg, st);
    for (let i = 0; i < 40; i++) {
      const cur = Math.log(ibOf(cfg, st)) + growthAt(cfg, st, P0) * H;
      let best = null, bv = cur + 1e-6;
      for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
        if (upgradeCost(st, k) > st.S) continue;
        const n = Math.max(1, levelsWithin(st, k, 0.02 * st.S));
        const s = clone(st);
        applyBuy(cfg, s, { key: k, n: n });
        const v = Math.log(ibOf(cfg, s)) + growthAt(cfg, s, P0) * H;
        if (v > bv) { bv = v; best = k; }
      }
      if (!best) break;
      applyBuy(cfg, st, { key: best, n: Math.max(1, levelsWithin(st, best, 0.02 * st.S)) });
    }
  }
  const basePolicy = {
    decide(cfg, st) { heuristicBuys(cfg, st); st.target = pStar(cfg, st); },
    shouldAscend: baseShouldAscend
  };
  function fixedPolicy(P) {
    return {
      decide(cfg, st) { st.target = snapTarget(cfg, st, P); },
      shouldAscend: baseShouldAscend
    };
  }

  function run(cfg, st, T, policy, log, firstDone) {
    if (!firstDone) policy.decide(cfg, st, T, log);
    rebalance(cfg, st);
    let guard = 0;
    while (st.t < T - 1e-9 && guard++ < 200000) {
      const I = bankRateOf(cfg, st);
      const tr = nextRewardTime(cfg, st);
      let te;
      if (st.bankNeed > 0) te = st.t + Math.max(0, st.bankNeed - st.L) / I;
      else if (st.target === HOLD) te = Infinity;
      else te = Math.max(st.lastAsc + cfg.minGap, st.t + Math.max(0, costToP(st.target, dOf(st)) + cfg.minBal - st.Wp - st.L) / I);
      const tn = Math.min(tr, te, T);
      advance(cfg, st, tn - st.t);
      if (tn >= T - 1e-9) break;
      if (tn === tr && tr <= te) { claimRewards(cfg, st, log); continue; }
      if (st.bankNeed > 0) {
        st.L -= st.bankNeed; st.bankNeed = 0; st.bankLv++;
        if (log) log.bank.push({ t: st.t, lv: st.bankLv });
        rebalance(cfg, st);
        continue;
      }
      if (st.Wp + st.L > 1e280 || !(st.S < 1e290)) { st.overflow = true; if (log) log.overflowAt = st.t; break; }
      markLimit(st, log, 0);
      if (policy.shouldAscend(cfg, st, T)) {
        claimRewards(cfg, st, log, true);
        doAscend(cfg, st, log);
        policy.decide(cfg, st, T, log);
        rebalance(cfg, st);
      } else {
        st.target = HOLD;
        rebalance(cfg, st);
      }
    }
    if (!st.overflow) st.t = Math.max(st.t, T);
    return finalValue(cfg, st, log);
  }

  function newLog() { return { ascends: [], rewards: [], bank: [], buys: [], targets: [] }; }

  // levels n affordable from level L: base * (n L + n(n+1)/2) <= shards
  function levelsWithin(st, key, shards) {
    const base = key === 'rew' ? 3 : 5;
    const L = st[key];
    const q = shards / base;
    let n = Math.floor((-(2 * L + 1) + Math.sqrt((2 * L + 1) * (2 * L + 1) + 8 * q)) / 2 + 1e-9);
    for (let i = 0; i < 4 && n > 0 && base * (n * L + n * (n + 1) / 2) > shards; i++) n -= Math.max(1, Math.ceil(n * 1e-12));
    if (key === 'disc') n = Math.min(n, 5 - L);
    return Math.max(0, n);
  }
  function applyBuy(cfg, st, opt) {
    if (opt.key === 'bank') {
      st.bankNeed = cfg.bankCosts[st.bankLv + 1];
      return 0;
    }
    const base = opt.key === 'rew' ? 3 : 5;
    const L = st[opt.key], n = opt.n;
    const cost = base * (n * L + n * (n + 1) / 2);
    st.S -= cost; st[opt.key] += n;
    if (opt.key === 'disc') settleHeld(cfg, st);
    return cost;
  }
  function buyOptions(cfg, st) {
    const out = [];
    if (cfg.allowShop) {
      for (const k of ['res', 'yld', 'intr', 'rew', 'disc']) {
        if (levelsWithin(st, k, st.S) < 1) continue;
        const steps = new Set([1, levelsWithin(st, k, 0.04 * st.S), levelsWithin(st, k, 0.15 * st.S)]);
        for (const n of steps) if (n >= 1) out.push({ key: k, n: n });
      }
    }
    if (cfg.allowBank && st.bankLv < 20 && st.bankNeed <= 0 && cfg.bankCosts[st.bankLv + 1] > 0) out.push({ key: 'bank', n: 1 });
    return out;
  }

  function rollout(cfg, st, T, targetOverride) {
    const s = clone(st);
    const Te = Math.min(T, st.t + cfg.lookahead);
    const c = Te < T ? (cfg._ibCfg || (cfg._ibCfg = Object.assign({}, cfg, { objective: 'ib' }))) : cfg;
    s.target = targetOverride !== undefined ? targetOverride : pStar(cfg, s);
    const v = run(c, s, Te, basePolicy, null, true);
    return Math.log(v > 0 ? v : 1e-300);
  }

  // planner: greedy purchases and target choice, each scored by a base-policy rollout
  function plannerPolicy(budget) {
    return {
      decide(cfg, st, T, log) {
        let quota = Math.max(12, Math.min(160, Math.floor(budget.left / 25)));
        let iter = 0;
        while (iter++ < 12 && quota > 0 && budget.left > 0) {
          const opts = buyOptions(cfg, st);
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
          const before = best.key === 'bank' ? st.bankLv : st[best.key];
          const cost = best.key === 'bank' ? cfg.bankCosts[st.bankLv + 1] : applyBuy(cfg, st, best);
          if (best.key === 'bank') applyBuy(cfg, st, best);
          if (log) {
            const rec = { t: st.t, key: best.key, n: best.n, cost: cost, from: before, level: before + best.n };
            log.buys.push(rec);
            const last = log.ascends[log.ascends.length - 1];
            if (last && Math.abs(last.t - st.t) < 1e-6) last.buys.push(rec);
          }
          if (best.key === 'bank') break;
        }
        const ps = pStar(cfg, st);
        const W = st.Wp + st.L;
        const cands = new Set([HOLD]);
        for (const m of [0.55, 0.75, 0.9, 1, 1.12, 1.3, 1.6, 2, 2.6]) cands.add(snapTarget(cfg, st, ps * m));
        cands.add(snapTarget(cfg, st, cfg.minP));
        const aff = pAff(W - cfg.minBal, dOf(st));
        if (aff >= cfg.minP) cands.add(snapTarget(cfg, st, aff));
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
    const pts = [{ t: st0.t, ib: ibOf(cfg, st0), rate: bankRateOf(cfg, st0) }];
    for (const a of log.ascends) pts.push({ t: a.t, ib: a.ib, rate: a.rate });
    if (log.finalAscend) pts.push({ t: T, ib: log.finalAscend.ib, rate: log.finalAscend.rate });
    else pts.push({ t: st.overflow ? st.t : T, ib: ibOf(cfg, st), rate: bankRateOf(cfg, st) });
    return { value: value, log: log, end: st, pts: pts };
  }

  function plan(cfg) {
    const T = cfg.horizonH;
    const st0 = initState(cfg, 0);
    settleHeld(cfg, st0);
    const budget = { left: cfg.budget || 500 };
    const res = {
      cfg: cfg,
      now: { ib: ibOf(cfg, st0), rate: bankRateOf(cfg, st0), W: st0.Wp + st0.L, pm: cfg.R * (cfg.P + 1) },
      optimal: sample(cfg, st0, T, plannerPolicy(budget)),
      baselines: []
    };
    res.budgetLeft = budget.left;
    const noShop = Object.assign({}, cfg, { allowShop: false, allowBank: false });
    res.baselines.push({ name: 'P* senza acquisti', run: sample(noShop, st0, T, basePolicy) });
    for (const P of [1000, 1500, 2000, 3000]) {
      res.baselines.push({ name: 'P' + P + ' fisso', P: P, run: sample(noShop, st0, T, fixedPolicy(P)) });
    }
    return res;
  }

  const api = {
    F, HOLD, defaults, bankCostTable, ibOf, bankRateOf, bankBonusOf, costToP, cumPR, pAff, pmAt, shardsAt, minPforShards,
    pStar, growthAt, plan, INT64, initState, settleHeld, reserveOf, dOf, upgradeCost, blockSum, rhoOf
  };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.NexusModel = api;
})(typeof window !== 'undefined' ? window : globalThis);
