#!/usr/bin/env python3
"""
下场预判模型（从 btc5m-4.py 分离的纯计算核心）

结算定义（Polymarket BTC 5m Up/Down）:
  P0 = 开盘时刻 Chainlink BTC/USD 的 60s TWAP = 开盘前 60s 均价
  C  = 收盘时刻 Chainlink BTC/USD 的 60s TWAP = 最后 60s 均价
  C >= P0 => Up（平局算涨）

预判时机:
  下一场开盘前 LEAD 秒（默认 20s）做一次方向判断。

核心公式:
  1) 用已实现价格 + 当前现货，估计收盘 TWAP 期望 c 与开盘基准 p0
  2) 未实现段用布朗运动，算 Var(C-P0)，得到 sd
  3) 正态近似: p_raw = Φ(mu/sd), mu = c - p0
  4) 可选 Platt 校准: p = calibrate(p_raw, tau)，tau = now - start（开盘前为负）
  5) pred = Up if p>=0.5 else Down；|p-0.5|>=CONF_TH 视为信号较强

依赖:
  仅标准库。调用方负责喂入价格序列（Chainlink / 币安代理）与波动率。

用法示例:
  from pred_model import Series, Predictor
  pred = Predictor()
  pred.ref.add(ts, px)          # Chainlink 现货；没有时用币安
  pred.bn.add(ts, bn_px)        # 可选，用于 nowcast
  pred.update_sigma(now)        # 用近 20 分钟价格更新 sigma
  out = pred.predict_next(now, next_start)
  # out: {pred, p, conf, mu, sd, p0, c, ...}
"""
from __future__ import annotations

import json
import math
import os
from bisect import bisect_left, bisect_right
from typing import Any, Optional

WIN, TW = 300, 60
LEAD = 20
CONF_TH = 0.05
DEFAULT_SIGMA = 6.0  # $/sqrt(s)


class Series:
    """按时间递增的 (ts, px) 序列，支持 bisect 查询。"""

    def __init__(self, keep: float = 1300):
        self.t: list[float] = []
        self.p: list[float] = []
        self.keep = keep

    def add(self, ts: float, px: float, gap: float = 0.0) -> None:
        if self.t and ts < self.t[-1]:
            return
        if self.t and ts - self.t[-1] < gap:
            self.p[-1] = px
            return
        self.t.append(ts)
        self.p.append(px)
        if len(self.t) > self.keep + 400:
            i = bisect_left(self.t, ts - self.keep)
            del self.t[:i], self.p[:i]

    def at(self, t: float) -> Optional[float]:
        i = bisect_right(self.t, t) - 1
        return self.p[i] if i >= 0 else None

    def last(self) -> Optional[float]:
        return self.p[-1] if self.p else None


def _F(x: float, y: float) -> float:
    if x > y:
        x, y = y, x
    return x * x * y / 2 - x ** 3 / 6


def _G(a1: float, b1: float, a2: float, b2: float) -> float:
    """Cov(∫_{a1}^{b1} W, ∫_{a2}^{b2} W) / sigma^2，W 为布朗运动。"""
    return _F(b1, b2) - _F(a1, b2) - _F(b1, a2) + _F(a1, a2)


def fair(
    t: float,
    s0: float,
    ref: Series,
    sigma: float,
    p0_fix: Optional[float] = None,
    shift: float = 0.0,
) -> Optional[dict[str, float]]:
    """
    在时刻 t，估计 P(C >= P0)。

    已发生区间用历史价平均；未发生区间用 (当前现货 + shift) 外推。
    未发生部分的不确定性按布朗运动积分协方差计算。
    """
    e = s0 + WIN
    st = ref.at(t)
    if st is None:
        return None
    st = st + shift

    def avg_part(a: float, b: float) -> float:
        kb = min(b, t)
        k = int(kb - a)
        known = 0.0
        if k > 0:
            known = sum((ref.at(a + i + 1) or st) for i in range(k)) * ((kb - a) / k)
        return known + st * max(0.0, b - max(a, t))

    p0_self = avg_part(s0 - TW, s0) / TW
    c = avg_part(e - TW, e) / TW
    # 开盘后可用官方 TWAP 作 P0；开盘前预判一般只用自算 p0_self
    p0 = p0_fix if (p0_fix is not None and t >= s0) else p0_self
    mu = c - p0

    def rng(a: float, b: float):
        lo, hi = max(a, t) - t, b - t
        return (lo, hi) if hi > lo else None

    A, B = rng(e - TW, e), rng(s0 - TW, s0)
    v = 0.0
    if A:
        v += _G(*A, *A)
    if B:
        v += _G(*B, *B)
    if A and B:
        v -= 2 * _G(*A, *B)
    sd = sigma * math.sqrt(max(v, 0.0)) / TW
    if sd < 1e-9:
        p = 1.0 if mu >= 0 else 0.0
    else:
        p = 0.5 * (1 + math.erf(mu / (sd * math.sqrt(2))))
    return {"p": p, "mu": mu, "sd": sd, "p0": p0, "p0_self": p0_self, "c": c}


def est_sigma_h(h: Series, now: float, lag: float = 30.0, span: float = 1200.0) -> Optional[float]:
    """
    用 lag 秒尺度收益估计波动 $/sqrt(s)。
    不用逐 tick，避免低估 30–60s 尺度波动、导致高概率过度自信。
    """
    n, acc, t = 0, 0.0, now - span
    while t + lag <= now:
        a, b = h.at(t), h.at(t + lag)
        if a is not None and b is not None:
            acc += (b - a) ** 2
            n += 1
        t += 5.0
    return math.sqrt(acc / (n * lag)) if n >= 20 else None


def nowcast_shift(bn: Series, now: float, g: float = 2.0) -> float:
    """币安领先 Chainlink ~2s：用 bn(now)-bn(now-g) 修正现货。"""
    if not bn.t or now - bn.t[-1] > 3:
        return 0.0
    b0 = bn.at(now - g)
    return bn.p[-1] - b0 if b0 is not None else 0.0


def load_calib(path: str) -> list[tuple[float, float, float, float]]:
    """加载 analyze.py --write-calib 生成的 data/calib.json。"""
    try:
        raw = json.load(open(path, encoding="utf-8"))["buckets"]
        return [(float(a), float(b), float(c), float(d)) for a, b, c, d in raw]
    except Exception:
        return []


def calibrate(p: float, tau: float, buckets: list[tuple[float, float, float, float]]) -> float:
    """按 tau 分档的 Platt 校准；无参数则原样返回。"""
    for lo, hi, a, b in buckets:
        if lo <= tau < hi:
            x = min(max(p, 1e-4), 1 - 1e-4)
            return 1 / (1 + math.exp(-(a * math.log(x / (1 - x)) + b)))
    return p


class Predictor:
    """
    下场预判器。

    - ref: 结算参考价序列（优先 Chainlink 现货；缺失时用币安）
    - bn:  币安现货，仅用于 nowcast（可选）
    - sigma: 波动率 $/sqrt(s)，可用 update_sigma() 滚动估计
    """

    def __init__(
        self,
        sigma: float = DEFAULT_SIGMA,
        conf_th: float = CONF_TH,
        lead: float = LEAD,
        calib_path: Optional[str] = None,
        use_nowcast: bool = True,
    ):
        self.ref = Series()
        self.bn = Series()
        self.sigma = sigma
        self.conf_th = conf_th
        self.lead = lead
        self.use_nowcast = use_nowcast
        path = calib_path or os.path.join("data", "calib.json")
        self.calib = load_calib(path)

    def update_sigma(self, now: float) -> Optional[float]:
        sg = est_sigma_h(self.ref if self.ref.last() is not None else self.bn, now)
        if sg:
            self.sigma = 0.8 * self.sigma + 0.2 * sg
        return sg

    def should_predict(self, now: float, next_start: float, done: bool = False) -> bool:
        """是否到达开盘前 lead 秒的预判窗口。"""
        return (not done) and (0 < next_start - now <= self.lead)

    def predict_next(
        self,
        now: float,
        next_start: float,
        p0_fix: Optional[float] = None,
        apply_nowcast: Optional[bool] = None,
    ) -> Optional[dict[str, Any]]:
        """
        对即将开盘的场次 next_start 做一次预判。

        返回 None 表示数据不足；否则:
          pred / p / p_raw / conf / mu / sd / p0 / c / sigma / tau / shift / ref_name
        """
        ref = self.ref if self.ref.last() is not None else self.bn
        if ref.last() is None or len(self.bn.t) + len(self.ref.t) < 120:
            return None

        use_nc = self.use_nowcast if apply_nowcast is None else apply_nowcast
        # 仅当 ref 是 Chainlink、且有币安时 nowcast 才有意义；调用方可自行判断
        shift = nowcast_shift(self.bn, now) if use_nc else 0.0
        r = fair(now, next_start, ref, self.sigma, p0_fix=p0_fix, shift=shift)
        if not r:
            return None

        tau = now - next_start  # 开盘前为负，例如 -20
        p_raw = r["p"]
        p = calibrate(p_raw, tau, self.calib)
        pred = "Up" if p >= 0.5 else "Down"
        return {
            "start": next_start,
            "pred": pred,
            "p": p,
            "p_raw": p_raw,
            "conf": abs(p - 0.5) >= self.conf_th,
            "mu": r["mu"],
            "sd": r["sd"],
            "p0": r["p0"],
            "p0_self": r["p0_self"],
            "c": r["c"],
            "sigma": self.sigma,
            "tau": tau,
            "shift": shift,
        }

    def fair_now(
        self,
        now: float,
        start: float,
        p0_fix: Optional[float] = None,
        apply_nowcast: Optional[bool] = None,
    ) -> Optional[dict[str, Any]]:
        """场中公允概率（与预判同一套 fair + calibrate）。"""
        ref = self.ref if self.ref.last() is not None else self.bn
        if ref.last() is None:
            return None
        use_nc = self.use_nowcast if apply_nowcast is None else apply_nowcast
        shift = nowcast_shift(self.bn, now) if use_nc else 0.0
        r = fair(now, start, ref, self.sigma, p0_fix=p0_fix, shift=shift)
        if not r:
            return None
        tau = now - start
        p_raw = r["p"]
        p = calibrate(p_raw, tau, self.calib)
        out = dict(r)
        out.update(p=p, p_raw=p_raw, tau=tau, shift=shift, sigma=self.sigma)
        return out


def window_start(ts: float, win: float = WIN) -> int:
    return int(ts // win) * int(win)


if __name__ == "__main__":
    # 极简自检: 构造一条上涨路径，开盘前预判应偏 Up
    import time as _time

    now = _time.time()
    s0 = window_start(now) + WIN  # 下一场
    m = Predictor(use_nowcast=False)
    px = 100000.0
    for i in range(400):
        t = now - 400 + i
        px += 2.0  # 缓涨
        m.ref.add(t, px)
        m.bn.add(t, px)
    m.update_sigma(now)
    out = m.predict_next(now, s0, apply_nowcast=False)
    print("next_start", s0)
    print(out)
