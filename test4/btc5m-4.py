#!/usr/bin/env python3
"""
BTC-test4 —— Polymarket BTC 5分钟涨跌盘: 场次预判 + 场中公允概率 + 数据采集 + Web看板(9999)

结算规则(2026-08-14起): Chainlink BTC/USD 60秒TWAP
    Price to beat P0 = 开盘时刻 TWAP60 = 开盘前60秒均价
    结算价 C         = 收盘时刻 TWAP60 = 最后60秒均价
    C >= P0 => Up (平局算Up)
=> 只要知道已发生的价格, 就能算出 P(C>=P0) 的公允概率; 越接近收盘越确定。

环境变量（写在服务器 ~/.btc5m-4.env ，不要放进仓库）:
    POLY_PRIVATE_KEY  钱包私钥。启动时自动换取 API 凭据，不必手填三项
    POLY_API_KEY / POLY_API_SECRET / POLY_API_PASSPHRASE  已经有凭据时直接用
    DASH_TOKEN  可选，设置后访问看板需带 ?token=xxx
服务器一行安装/更新（长久 systemd 服务；已在跑会先停再启）:
  curl -fsSL https://raw.githubusercontent.com/hrf100/btctest4/main/test4/run.sh | bash
"""
import asyncio, json, time, math, csv, os, logging, argparse, io, zipfile, itertools
from bisect import bisect_left, bisect_right
from collections import deque
import aiohttp
from aiohttp import web

GAMMA = "https://gamma-api.polymarket.com"
CLOB = "https://clob.polymarket.com"
POLY_WS = "wss://ws-live-v2.polymarket.com/ws"
BN_WS = "wss://stream.binance.com:9443/stream?streams=btcusdt@aggTrade/btcusdt@depth10@100ms"
OKX_WS = "wss://ws.okx.com:8443/ws/v5/public"

WIN, TW = 300, 60
LEAD = 20                 # 开盘前多少秒做预判
CONF_TH = 0.05            # |p-0.5| 超过此值算"有信心"
DEFAULT_SIGMA = 6.0       # $/sqrt(s), 启动初期用
DATA = "data"
ROUNDS_KEEP = 2000          # 看板内存只保留最近 N 场；命中率统计用全部 CSV
PAPER_CFG_PATH = f"{DATA}/paper_cfg.json"
PAPER_CSV = f"{DATA}/paper_trades.csv"
DASH_TOKEN = os.getenv("DASH_TOKEN", "")
T5 = aiohttp.ClientTimeout(total=5)
# 模拟下单三档, 各自独立开关/参数, 同一场每档最多一笔:
#   strong/weak: 开盘后 max_tau 秒内, 预测侧卖一 <= buy_price 则按卖一成交 amount U
#   pre: 开盘前(预判后到开盘), |p-0.5| >= min_strength 且预测侧卖一 <= buy_price(上限) 则成交
PAPER_DEFAULT = {
    "strong": {"enabled": True, "buy_price": 0.45, "max_tau": 150, "amount": 5.0},
    "weak": {"enabled": False, "buy_price": 0.45, "max_tau": 150, "amount": 5.0},
    "pre": {"enabled": True, "min_strength": 0.08, "buy_price": 0.70, "amount": 5.0},
}
PAPER_PROFILES = ("strong", "weak", "pre")
PAPER_PROFILE_LABEL = {"strong": "信号较强", "weak": "信号较弱", "pre": "开盘前"}

# ---------------------------------------------------------------- ≤10¢ 绝地反转狙击(独立账本)
# 与上面三档完全分开: 独立配置/CDP文件、独立统计、独立列表。
# 逻辑: 某方向被砸到 <= max_entry 时, 若"剩余时间窗 + ATR标准化落差 + 翻转评分"三项同时达标,
#       按卖一建仓; 反弹到 tp_mult 倍(且 >= tp_min)卖出 tp_frac 份额抽回本金, 余仓持有到结算(Free-Roll)。
SNIPE_CFG_PATH = f"{DATA}/snipe_cfg.json"
SNIPE_CSV = f"{DATA}/snipe_trades.csv"
SNIPE_DEFAULT = {
    "enabled": True,
    "max_entry": 0.10,      # 建仓价上限(深虚值, 赔率 10 倍以上)
    "min_entry": 0.03,      # 建仓价下限: 更低说明盘口已基本判定结果, 不是"反转"而是接飞刀
    "bet": 5.0,             # 单笔固定投入 U
    "min_score": 62.0,      # 翻转评分门槛(0~100)
    "tau_min": 60,          # 相对开盘秒下限 => 剩余 <= 240 秒
    "tau_max": 230,         # 相对开盘秒上限 => 剩余 >= 70 秒
    "r_gap_max": 1.65,      # ATR 标准化落差 R_gap 上限
    "tp_mult": 2.5,         # 半仓止盈: 买一达到建仓价的倍数
    "tp_min": 0.18,         # 半仓止盈: 买一最低价
    "tp_frac": 0.5,         # 半仓止盈比例
    "per_round": 1,         # 每场最多狙击次数
}
SNIPE_FIELDS = ("nid", "start", "time_utc", "src", "side", "entry", "shares", "amount",
                "tau", "remain", "spot", "strike", "atr", "r_gap", "score",
                "s_time", "tir", "tir30", "bounce", "s_flow", "s_bounce", "s_gap",
                "tp_target", "tp_hit", "tp_tau", "tp_bid", "tp_shares", "cash1",
                "stage", "outcome", "hit", "settle_value", "pnl", "settled")
# 翻转评分四段权重(合计 100)。看板每张卡片底部显示 "得分/满分"，加总即为总分
SNIPE_W = {"time": 30.0, "flow": 35.0, "bounce": 20.0, "gap": 15.0}
SNIPE_TIME_FULL = 210.0   # 剩余时间达到此秒数时时间窗满分

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
log = logging.getLogger("btc5m")


# ------------------------------------------------------------------ 数据结构
class Series:
    """按时间递增的 (ts, px) 序列, 支持 bisect 查询"""

    def __init__(self, keep=1300):
        self.t, self.p, self.keep = [], [], keep

    def add(self, ts, px, gap=0.0):
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

    def at(self, t):
        i = bisect_right(self.t, t) - 1
        return self.p[i] if i >= 0 else None

    def last(self):
        return self.p[-1] if self.p else None


class Flow:
    """最近 sec 秒的主动成交: 边追加边维护累计和, 避免每次都重扫几万条。

    成交流量到 100 笔/秒时, 原来保留 180 秒要扫 1.8 万条, features() 每次 1.2ms;
    现在只留 sec 秒并增量维护, 每次约 0.01ms。
    """

    def __init__(self, sec=60):
        self.sec, self.dq, self.s, self.a = sec, deque(), 0.0, 0.0

    def add(self, ts, q):
        self.dq.append((ts, q))
        self.s += q
        self.a += abs(q)
        self._trim(ts)

    def _trim(self, now):        # 只留最近 sec 秒, 这样 s/a 就是精确的窗口累计
        lim = now - self.sec
        while self.dq and self.dq[0][0] < lim:
            _, q = self.dq.popleft()
            self.s -= q
            self.a -= abs(q)

    def ratio(self, now):
        self._trim(now)
        return (self.s / self.a) if self.a > 0 else 0.0

    def ratio_since(self, now, sec):
        """最近 sec 秒的方向占比（从尾部倒扫，窗口小所以很快）。"""
        s = a = 0.0
        for ts, q in reversed(self.dq):
            if ts < now - sec:
                break
            s += q
            a += abs(q)
        return (s / a) if a > 0 else 0.0


class St:
    def __init__(self):
        self.cl, self.tw, self.bn, self.okx = Series(), Series(), Series(), Series()
        self.flow = {"bn": Flow(), "okx": Flow()}
        self.obi = {"bn": 0.0, "okx": 0.0}
        self.last_msg = {k: 0 for k in ("cl", "tw", "bn", "okx", "pm")}
        self.cl_src = ""
        self.auth = "no-creds"
        self.pm, self.tokens, self.pm_ws = {}, set(), None
        self.win, self.rounds = {}, deque(maxlen=ROUNDS_KEEP)
        self.view, self.sigma = {}, DEFAULT_SIGMA
        self.sigma_t = 0.0         # 上次重估波动率的时间
        self.ticks_t = 0.0         # 上次写 ticks.csv 的时间
        self.conn_t = 0.0          # 最近一次PolyBolt连接时间
        self.cl_nofilter = False   # 看门狗触发后切换: 不带symbol过滤订阅, 本地过滤btcusd
        self.paper_cfg = {k: dict(v) for k, v in PAPER_DEFAULT.items()}
        self.paper = []                  # 模拟成交记录(全量, 由 CSV 恢复)
        self.paper_n = 0                 # 已结算数
        self.paper_wins = 0              # 命中数
        self.paper_pnl = 0.0             # 累计盈亏
        self.paper_prof = {k: {"n": 0, "wins": 0, "pnl": 0.0, "trades": 0} for k in PAPER_PROFILES}
        # 狙击账本(与上三档分开)
        self.snipe_cfg = dict(SNIPE_DEFAULT)
        self.snipe = []                  # 全部狙击记录(CSV 恢复)
        self.snipe_n = self.snipe_wins = 0
        self.snipe_pnl = 0.0             # 已实现+结算后总盈亏
        self.snipe_cash = 0.0            # 阶段一已落袋现金
        self.snipe_trades = 0            # 建仓次数
        self.snipe_seq = 0               # 建仓序号(账本行唯一 ID)
        self.started = time.time()       # 本次进程启动时间
        # 全量历史统计(不受 ROUNDS_KEEP 截断); 命中率以 CSV 全量为准
        self.round_n = self.round_hits = self.round_cn = self.round_chits = 0
        # 各 WS 消息量与解析耗时累计(用于定位 CPU)
        self.msg = {"poly": 0, "bn": 0, "okx": 0}
        self.msg_cost = {"poly": 0.0, "bn": 0.0, "okx": 0.0}


S = St()


# ------------------------------------------------------------------ 轻量耗时统计
# 只在关键循环里加 process_time 差值, 开销可忽略; 用于定位 CPU 花在哪
PERF = {}
_perf_snap = {"t": 0.0}


def _perf(name, t0):
    d = PERF.get(name)
    if d is None:
        PERF[name] = [time.process_time() - t0, 1]
    else:
        d[0] += time.process_time() - t0
        d[1] += 1


def perf_share():
    """各任务实际消耗的 CPU：ms/s（= 单核占用百分比）与每秒次数。"""
    now = time.time()
    dt = now - (_perf_snap["t"] or now)
    prev_t = _perf_snap.get("cpu", {})
    prev_n = _perf_snap.get("n", {})
    cur_t = {k: v[0] for k, v in PERF.items()}
    cur_n = {k: v[1] for k, v in PERF.items()}
    out = {}
    if dt > 0:
        for k in cur_t:
            d = max(0.0, cur_t[k] - prev_t.get(k, 0.0))
            out[k] = {"ms_per_s": round(1000 * d / dt, 2),
                      "per_s": round((cur_n[k] - prev_n.get(k, 0)) / dt, 1)}
    _perf_snap.update(t=now, cpu=cur_t, n=cur_n)
    return out


def _paper_check(prof, c):
    """校验单档参数, 返回 (归一化dict, 错误文案)。"""
    d = PAPER_DEFAULT[prof]
    lab = PAPER_PROFILE_LABEL[prof]
    try:
        out = {"enabled": bool(c.get("enabled", d["enabled"])),
               "buy_price": round(float(c.get("buy_price", d["buy_price"])), 4),
               "amount": round(float(c.get("amount", d["amount"])), 4)}
        if "max_tau" in d:
            out["max_tau"] = int(c.get("max_tau", d["max_tau"]))
        if "min_strength" in d:
            out["min_strength"] = round(float(c.get("min_strength", d["min_strength"])), 4)
    except Exception:
        return None, f"{lab}参数格式错误"
    if not (0.01 <= out["buy_price"] <= 0.99):
        return None, f"{lab}买价需在 0.01~0.99"
    if not (0.1 <= out["amount"] <= 10000):
        return None, f"{lab}金额需在 0.1~10000 U"
    if "max_tau" in out and not (5 <= out["max_tau"] <= WIN):
        return None, f"{lab}窗口需在 5~{WIN} 秒"
    if "min_strength" in out and not (0.0 <= out["min_strength"] <= 0.49):
        return None, f"{lab}强度需在 0~0.49"
    return out, None


def _norm_paper_cfg(cfg):
    """归一化模拟下单配置; 兼容旧版扁平结构(enabled/buy_price/...); 非法值回落默认。"""
    out = {}
    legacy = {k: cfg[k] for k in ("enabled", "buy_price", "max_tau", "amount") if k in cfg}
    for prof in PAPER_PROFILES:
        d = PAPER_DEFAULT[prof]
        raw = cfg.get(prof)
        if not isinstance(raw, dict):
            raw = dict(d, **legacy) if (legacy and prof == "strong") else d
        c, err = _paper_check(prof, raw)
        out[prof] = c if c else dict(d)
    return out


def load_paper_cfg():
    cfg = dict(PAPER_DEFAULT)
    try:
        if os.path.exists(PAPER_CFG_PATH):
            raw = json.load(open(PAPER_CFG_PATH, encoding="utf-8"))
            if isinstance(raw, dict):
                cfg = raw
    except Exception:
        log.exception("加载模拟下单配置失败")
    S.paper_cfg = _norm_paper_cfg(cfg)
    return S.paper_cfg


def save_paper_cfg(cfg=None):
    cfg = _norm_paper_cfg(cfg or S.paper_cfg)
    os.makedirs(DATA, exist_ok=True)
    with open(PAPER_CFG_PATH, "w", encoding="utf-8") as fh:
        json.dump(cfg, fh, ensure_ascii=False, indent=2)
    S.paper_cfg = cfg
    for prof in PAPER_PROFILES:
        log.info("模拟下单配置已保存[%s]: %s", PAPER_PROFILE_LABEL[prof], cfg[prof])


def _paper_row_num(r):
    for k in ("buy_price", "amount", "shares", "btc", "p0", "btc_diff", "btc_diff_bps",
              "p_pred", "fair_p", "pnl", "tau", "thresh", "strength"):
        if k in r:
            r[k] = _num(r[k], float)
    for k in ("start", "hit", "conf", "settled", "max_tau"):
        if k in r:
            r[k] = _num(r[k], int)
    if not r.get("sig"):
        r["sig"] = "strong" if int(r.get("conf") or 0) else "weak"
    return r


def _add_paper_stat(row, new_trade=True):
    prof = row.get("sig") or "strong"
    p = S.paper_prof.setdefault(prof, {"n": 0, "wins": 0, "pnl": 0.0, "trades": 0})
    if new_trade:
        p["trades"] += 1
    if int(row.get("settled") or 0) == 1:
        hit = int(row.get("hit") or 0)
        pnl = float(row.get("pnl") or 0)
        S.paper_n += 1
        S.paper_wins += hit
        S.paper_pnl += pnl
        p["n"] += 1
        p["wins"] += hit
        p["pnl"] += pnl


def _reset_paper_stats():
    S.paper_n = S.paper_wins = 0
    S.paper_pnl = 0.0
    S.paper_prof = {k: {"n": 0, "wins": 0, "pnl": 0.0, "trades": 0} for k in PAPER_PROFILES}


def load_paper_trades():
    """从 CSV 恢复全部模拟成交，并据此重建统计（分页展示用全量）。"""
    _reset_paper_stats()
    S.paper = []
    if not os.path.exists(PAPER_CSV):
        return
    try:
        with open(PAPER_CSV, newline="", encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh))
        for r in rows:
            if not r.get("start"):
                continue
            _paper_row_num(r)
            S.paper.append(r)
            _add_paper_stat(r)
        log.info("已加载模拟成交 %d 笔 (已结算 %d)", len(S.paper), S.paper_n)
    except Exception:
        log.exception("加载模拟成交失败")


def paper_stats():
    n = S.paper_n
    out = {"n": len(S.paper), "settled": n, "wins": S.paper_wins,
           "win_rate": (S.paper_wins / n) if n else None, "pnl": round(S.paper_pnl, 4),
           "by_sig": {}}
    for prof in PAPER_PROFILES:
        p = S.paper_prof.get(prof) or {}
        pn = int(p.get("n") or 0)
        out["by_sig"][prof] = {"trades": int(p.get("trades") or 0), "settled": pn,
                               "wins": int(p.get("wins") or 0),
                               "win_rate": (p["wins"] / pn) if pn else None,
                               "pnl": round(float(p.get("pnl") or 0), 4),
                               "enabled": bool(S.paper_cfg.get(prof, {}).get("enabled"))}
    return out


def paper_page(page=1, size=20):
    """成交记录分页（最新在前）。"""
    rows = S.paper
    total = len(rows)
    size = max(1, min(int(size or 20), 200))
    pages = max(1, math.ceil(total / size))
    page = max(1, min(int(page or 1), pages))
    start = total - page * size
    end = total - (page - 1) * size
    chunk = rows[max(0, start):max(0, end)]
    return {"page": page, "size": size, "pages": pages, "total": total, "rows": chunk}


def paper_curve(max_points=300):
    """模拟下单累计盈亏曲线：按结算顺序累计，含合计与三档分线。

    返回 [[序号, 合计, 前, 强, 普], ...]，点太多时等距抽样（保留最后一个点）。
    """
    xs = [(r.get("sig") or "strong", float(r.get("pnl") or 0))
          for r in S.paper if int(r.get("settled") or 0) == 1]
    if not xs:
        return []
    cum = {"pre": 0.0, "strong": 0.0, "weak": 0.0}
    pts = []
    for i, (sig, pnl) in enumerate(xs, 1):
        cum[sig] = cum.get(sig, 0.0) + pnl
        pts.append([i, round(sum(cum.values()), 4),
                    round(cum["pre"], 4), round(cum["strong"], 4), round(cum["weak"], 4)])
    if len(pts) > max_points:
        step = len(pts) / max_points
        keep = [pts[int(i * step)] for i in range(max_points)]
        keep[-1] = pts[-1]
        pts = keep
    return pts


def paper_status(s0, now, w, r, spot=None):
    """三档实时状态，供看板顶部展示。判定顺序与 try_paper_pre / try_paper_fill 完全一致，
    保证"显示可买"和"真的会买"不错位。"""
    done = _paper_done(w)
    tau = now - s0
    pred = w.get("pred")
    strength = abs(float(w.get("p_pred") or 0.5) - 0.5)
    sel = ("strong" if w.get("conf") else "weak") if pred else None
    ask = bid = None
    if pred:
        if pred == "Up":
            bid, ask = r.get("up_bid"), r.get("up_ask")
        else:
            bid, ask = r.get("dn_bid"), r.get("dn_ask")
    out = []
    for prof in ("pre", "strong", "weak"):
        cfg = (S.paper_cfg or {}).get(prof) or {}
        cap = float(cfg.get("buy_price") or 0)
        st = {"prof": prof, "enabled": bool(cfg.get("enabled")), "done": prof in done,
              "side": pred, "ask": ask, "cap": cap, "tau": round(tau, 1),
              "state": "", "reason": "", "ready": False}
        if prof in done:
            st["state"], st["reason"] = "done", "本场已成交"
        elif not cfg.get("enabled"):
            st["state"], st["reason"] = "off", "未启用"
        elif prof == "pre":
            if now >= s0:
                st["state"], st["reason"] = "past", "已过开盘"
            elif not pred:
                st["state"], st["reason"] = "wait", "等待预判"
            elif strength < float(cfg.get("min_strength") or 0):
                st["state"] = "weak"
                st["reason"] = f"强度 {strength:.3f} < {float(cfg['min_strength']):.3f}"
            elif ask is None:
                st["state"], st["reason"] = "nodata", "盘口无卖价"
            elif ask > cap:
                st["state"], st["reason"] = "price", f"卖一 {ask:.2f} > 上限 {cap:.2f}"
            else:
                st["state"], st["reason"], st["ready"] = "ready", "可买入", True
        else:
            if prof != sel:
                st["state"] = "skip"
                st["reason"] = f"本场属{'强' if sel == 'strong' else '普'}信号"
            elif not pred:
                st["state"], st["reason"] = "wait", "等待预判"
            elif tau < 0:
                st["state"], st["reason"] = "wait", "未开盘"
            elif tau > float(cfg.get("max_tau") or 0):
                st["state"] = "past"
                st["reason"] = f"已过 {int(cfg.get('max_tau') or 0)}s 窗口"
            elif ask is None:
                st["state"], st["reason"] = "nodata", "盘口无卖价"
            elif ask > cap:
                st["state"], st["reason"] = "price", f"卖一 {ask:.2f} > 上限 {cap:.2f}"
            else:
                st["state"], st["reason"], st["ready"] = "ready", "可买入", True
        out.append(st)
    return {"round": s0, "tau": round(tau, 1), "remain": round(max(0.0, (s0 + WIN) - now), 1),
            "pred": pred, "p_pred": round(float(w.get("p_pred") or 0), 4),
            "strength": round(strength, 4), "sig": sel,
            "rows": out}


def snipe_target(now, w, r, spot, ref=None):
    """雷达锁定：挑出被打到地板的一侧，并给出锁定信息（不判定是否可买）。

    优先在 [min_entry, max_entry] 区间内按更便宜的一侧锁定；若两侧都不在区间内，
    仍锁定更便宜的一侧用于展示评分与说明，但标记 in_range=False。
    """
    cfg = S.snipe_cfg or {}
    lo = float(cfg.get("min_entry") or 0.0)
    cap = float(cfg.get("max_entry") or 0.1)
    ub, ua = r.get("up_bid"), r.get("up_ask")
    db, da = r.get("dn_bid"), r.get("dn_ask")
    offers = []
    if ua is not None:
        offers.append(("Up", ua, ub))
    if da is not None:
        offers.append(("Down", da, db))
    if not offers:
        return None
    side, ask, bid = min(offers, key=lambda x: x[1])
    in_range = lo <= ask <= cap
    strike = r.get("p0")
    atr = snipe_atr(now)
    remain = max(0.0, (w.get("start", 0) + WIN) - now)
    score = detail = None
    if atr and strike and spot is not None:
        score, detail = snipe_score(now, w, side, spot, strike, atr, remain, ref)
    return {"side": side, "ask": round(float(ask), 4),
            "bid": None if bid is None else round(float(bid), 4),
            "in_range": in_range, "lo": lo, "cap": cap,
            "strike": None if not strike else round(float(strike), 2),
            "atr": None if not atr else round(atr, 3),
            "score": score, "detail": detail or {},
            "other": {s: (None if a is None else round(float(a), 4)) for s, a, _ in offers}}


def snipe_status(s0, now, w, r, spot, ref=None):
    """狙击实时状态：雷达头部 + 四张评分卡所需数据。判定条件与 try_snipe 完全一致。"""
    cfg = S.snipe_cfg or {}
    tau = now - s0
    remain = max(0.0, (s0 + WIN) - now)
    tgt = snipe_target(now, w, r, spot, ref)
    atr = tgt["atr"] if tgt else None
    strike = tgt["strike"] if tgt else None
    r_gap = None
    if atr and strike and spot is not None:
        r_gap = abs(spot - strike) / (atr * math.sqrt(max(remain, 1) / 60.0))
    score = tgt["score"] if tgt else None
    min_score = float(cfg.get("min_score") or 62)
    tmin, tmax = float(cfg.get("tau_min") or 0), float(cfg.get("tau_max") or 0)
    done = int(w.get("snipe_cnt") or 0)
    per = int(cfg.get("per_round") or 1)
    checks = [
        {"name": "启用", "ok": bool(cfg.get("enabled")),
         "detail": "已开启" if cfg.get("enabled") else "已关闭"},
        {"name": "本场次数", "ok": done < per, "detail": f"已 {done}/{per}"},
        {"name": "时间窗", "ok": tmin <= tau <= tmax,
         "detail": f"相对开盘 {tau:.0f}s（区间 {tmin:.0f}~{tmax:.0f}s，剩余 {remain:.0f}s）"},
        {"name": "建仓价", "ok": bool(tgt and tgt["in_range"]),
         "detail": (f"{'涨' if tgt['side'] == 'Up' else '跌'} 卖一 {tgt['ask']:.3f}"
                    f"（需 {tgt['lo']:.3f}~{tgt['cap']:.3f}）"
                    if tgt else "盘口无卖价")},
        {"name": "ATR/Strike", "ok": bool(atr and strike),
         "detail": f"ATR {atr:.2f}$ / Strike {strike:.2f}" if (atr and strike) else "数据不足"},
        {"name": "R_gap", "ok": r_gap is not None and r_gap <= float(cfg.get("r_gap_max") or 1.65),
         "detail": f"{r_gap:.2f}（上限 {float(cfg.get('r_gap_max') or 1.65):.2f}）" if r_gap is not None
                   else "数据不足"},
        {"name": "翻转评分", "ok": score is not None and score >= min_score,
         "detail": f"{score:.1f}（门槛 {min_score:.0f}）" if score is not None else "数据不足"},
    ]
    ready = all(c["ok"] for c in checks)
    blocked = [c["name"] for c in checks if not c["ok"]]
    # 兜底：数据不足时 detail 里的观测值为 None，前端统一显示为 "-"（避免 NaN% / $-）
    det = {"s_time": 0.0, "s_flow": 0.0, "s_bounce": 0.0, "s_gap": 0.0,
           "tir": None, "tir30": None, "bounce": None, "gap": None, "tol": None}
    det.update((tgt or {}).get("detail") or {})
    return {"round": s0, "tau": round(tau, 1), "remain": round(remain, 1),
            "spot": None if spot is None else round(float(spot), 2),
            "target": tgt, "side": tgt["side"] if tgt else None,
            "ask": tgt["ask"] if tgt else None, "bid": tgt["bid"] if tgt else None,
            "strike": strike, "atr": atr, "r_gap": None if r_gap is None else round(r_gap, 3),
            "score": score, "detail": det,
            "min_score": min_score, "weights": SNIPE_W,
            "scored": score is not None,
            "bet": float(cfg.get("bet") or 5.0), "auto": bool(cfg.get("enabled")),
            "ready": ready, "blocked": blocked, "checks": checks}


def round_page(page=1, size=20):
    """历史场次分页（最新在前）。只传当前页，避免每秒把几千场全量塞给浏览器。"""
    rows = S.rounds
    total = len(rows)
    size = max(1, min(int(size or 20), 200))
    pages = max(1, math.ceil(total / size))
    page = max(1, min(int(page or 1), pages))
    if total == 0:
        return {"page": 1, "size": size, "pages": 1, "total": 0, "rows": []}
    end = total - (page - 1) * size
    start = max(0, end - size)
    return {"page": page, "size": size, "pages": pages, "total": total,
            "rows": list(itertools.islice(rows, start, end))[::-1]}


PAPER_FIELDS = ("start", "time_utc", "sig", "tau", "side", "buy_price", "amount", "shares",
                "thresh", "max_tau", "strength", "btc", "p0", "btc_diff", "btc_diff_bps",
                "p_pred", "fair_p", "conf", "outcome", "hit", "pnl", "settled")


def _ensure_paper_header():
    """旧 paper_trades.csv 缺新列(sig/strength)时原地补齐表头, 保留全部旧数据。"""
    if not os.path.exists(PAPER_CSV) or _csv_fields.get(PAPER_CSV) == list(PAPER_FIELDS):
        return
    with open(PAPER_CSV, newline="", encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh))
        head = rows and list(rows[0].keys())
    if head and all(k in head for k in PAPER_FIELDS):
        _csv_fields[PAPER_CSV] = head
        return
    for r in rows:
        if not r.get("sig"):
            r["sig"] = "strong" if str(r.get("conf")) == "1" else "weak"
    with open(PAPER_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(PAPER_FIELDS), extrasaction="ignore", restval="")
        w.writeheader()
        w.writerows(rows)
    _csv_fields[PAPER_CSV] = list(PAPER_FIELDS)
    log.info("paper_trades.csv 已补齐表头 (%d 行)", len(rows))


def _paper_done(w):
    """该场次已成交的档位集合。"""
    return w.setdefault("paper_done", set())


def _record_paper(prof, s0, now, w, side, ask, cfg, p0, spot, fair_p, strength):
    amount = float(cfg.get("amount") or 5.0)
    shares = round(amount / float(ask), 4)
    diff = (spot - p0) if (spot is not None and p0 is not None) else None
    diff_bps = (diff / p0 * 1e4) if (diff is not None and p0) else None
    row = {
        "start": s0,
        "time_utc": time.strftime("%m-%d %H:%M:%S", time.gmtime(now)),
        "sig": prof,
        "tau": round(now - s0, 1),
        "side": side,
        "buy_price": round(float(ask), 4),
        "amount": round(amount, 4),
        "shares": shares,
        "thresh": float(cfg["buy_price"]),
        "max_tau": int(cfg["max_tau"]) if "max_tau" in cfg else "",
        "strength": round(strength, 4),
        "btc": None if spot is None else round(float(spot), 2),
        "p0": None if p0 is None else round(float(p0), 2),
        "btc_diff": None if diff is None else round(float(diff), 2),
        "btc_diff_bps": None if diff_bps is None else round(float(diff_bps), 2),
        "p_pred": round(float(w.get("p_pred") or 0), 4),
        "fair_p": round(float(fair_p or 0), 4),
        "conf": int(bool(w.get("conf"))),
        "outcome": "",
        "hit": "",
        "pnl": "",
        "settled": 0,
    }
    _ensure_paper_header()
    append_csv(PAPER_CSV, row)
    S.paper.append(row)
    _add_paper_stat(row)
    _paper_done(w).add(prof)
    w["paper_trade"] = row
    log.info("模拟成交[%s] %s side=%s ask=%.3f<=%.2f amount=%.2fU shares=%.4f tau=%+.0fs 强度=%.3f btc=%s diff=%s",
             PAPER_PROFILE_LABEL[prof], s0, side, ask, row["thresh"], amount, shares,
             row["tau"], strength, row["btc"], row["btc_diff"])
    return row


def try_paper_fill(s0, now, cur, r, spot):
    """开盘后档：按场次信号强弱选 strong/weak，开盘后 max_tau 内预测侧卖一 <= 买价上限则成交。"""
    if not cur.get("pred"):
        return
    prof = "strong" if cur.get("conf") else "weak"
    cfg = (S.paper_cfg or {}).get(prof) or {}
    if not cfg.get("enabled") or prof in _paper_done(cur):
        return
    tau = now - s0
    if tau < 0 or tau > float(cfg["max_tau"]):
        return
    side = cur["pred"]
    ask = r.get("up_ask") if side == "Up" else r.get("dn_ask")
    if ask is None or ask <= 0 or ask > float(cfg["buy_price"]):
        return
    _record_paper(prof, s0, now, cur, side, ask, cfg, r.get("p0"), spot, r.get("p"),
                  abs(float(cur.get("p_pred") or 0.5) - 0.5))


def try_paper_pre(s, now, w, spot):
    """开盘前档：预判完成后、开盘前，|p-0.5| >= min_strength 且预测侧卖一 <= 上限则按卖价成交。
    只看模型强度，不看「模型概率-卖价」；卖价只作为买贵了的上限。"""
    cfg = (S.paper_cfg or {}).get("pre") or {}
    if not cfg.get("enabled") or "pre" in _paper_done(w) or not w.get("pred") or now >= s:
        return
    strength = abs(float(w.get("p_pred") or 0.5) - 0.5)
    if strength < float(cfg["min_strength"]):
        return
    side = w["pred"]
    _, ask = quote(w["up"] if side == "Up" else w["dn"])
    if ask is None or ask <= 0 or ask > float(cfg["buy_price"]):
        return
    rp = w.get("r_pred") or {}
    _record_paper("pre", s, now, w, side, ask, cfg, rp.get("p0"), spot, w.get("p_pred"), strength)


# ---------------------------------------------------------------- ≤10¢ 绝地反转狙击
def _snipe_check(c):
    """校验狙击参数, 返回 (归一化dict, 错误文案)。"""
    d = SNIPE_DEFAULT
    try:
        out = {"enabled": bool(c.get("enabled", d["enabled"])),
               "max_entry": round(float(c.get("max_entry", d["max_entry"])), 4),
               "min_entry": round(float(c.get("min_entry", d["min_entry"])), 4),
               "bet": round(float(c.get("bet", d["bet"])), 4),
               "min_score": round(float(c.get("min_score", d["min_score"])), 2),
               "tau_min": int(c.get("tau_min", d["tau_min"])),
               "tau_max": int(c.get("tau_max", d["tau_max"])),
               "r_gap_max": round(float(c.get("r_gap_max", d["r_gap_max"])), 3),
               "tp_mult": round(float(c.get("tp_mult", d["tp_mult"])), 3),
               "tp_min": round(float(c.get("tp_min", d["tp_min"])), 4),
               "tp_frac": round(float(c.get("tp_frac", d["tp_frac"])), 3),
               "per_round": int(c.get("per_round", d["per_round"]))}
    except Exception:
        return None, "狙击参数格式错误"
    if not (0.01 <= out["max_entry"] <= 0.99):
        return None, "狙击建仓价上限需在 0.01~0.99"
    if not (0.005 <= out["min_entry"] <= out["max_entry"]):
        return None, "狙击建仓价下限需在 0.005 ~ 上限之间"
    if not (0.1 <= out["bet"] <= 10000):
        return None, "狙击单笔投入需在 0.1~10000 U"
    if not (0 <= out["min_score"] <= 100):
        return None, "翻转评分门槛需在 0~100"
    if not (0 <= out["tau_min"] < out["tau_max"] <= WIN):
        return None, f"狙击时间窗需 0 ≤ 下限 < 上限 ≤ {WIN} 秒"
    if not (0.2 <= out["r_gap_max"] <= 10):
        return None, "R_gap 上限需在 0.2~10"
    if not (1.05 <= out["tp_mult"] <= 20):
        return None, "止盈倍数需在 1.05~20"
    if not (0.01 <= out["tp_min"] <= 0.99):
        return None, "止盈最低价需在 0.01~0.99"
    if not (0.05 <= out["tp_frac"] <= 1.0):
        return None, "止盈比例需在 0.05~1"
    if not (1 <= out["per_round"] <= 10):
        return None, "每场次数需在 1~10"
    return out, None


def load_snipe_cfg():
    cfg = SNIPE_DEFAULT
    try:
        if os.path.exists(SNIPE_CFG_PATH):
            raw = json.load(open(SNIPE_CFG_PATH, encoding="utf-8"))
            if isinstance(raw, dict):
                cfg = raw
    except Exception:
        log.exception("加载狙击配置失败")
    c, _ = _snipe_check({**SNIPE_DEFAULT, **cfg})
    S.snipe_cfg = c or dict(SNIPE_DEFAULT)
    return S.snipe_cfg


def save_snipe_cfg(cfg=None):
    c, err = _snipe_check(cfg if cfg is not None else S.snipe_cfg)
    if err:
        return None, err
    os.makedirs(DATA, exist_ok=True)
    with open(SNIPE_CFG_PATH, "w", encoding="utf-8") as fh:
        json.dump(c, fh, ensure_ascii=False, indent=2)
    S.snipe_cfg = c
    log.info("狙击配置已保存: %s", c)
    return c, None


def _snipe_row_num(r):
    for k in ("entry", "shares", "amount", "tau", "remain", "spot", "strike", "atr", "r_gap",
              "score", "s_time", "tir", "tir30", "bounce", "s_flow", "s_bounce", "s_gap",
              "tp_target", "tp_tau", "tp_bid", "tp_shares", "cash1", "settle_value", "pnl"):
        if k in r:
            r[k] = _num(r[k], float)
    for k in ("start", "tp_hit", "hit", "settled"):
        if k in r:
            r[k] = _num(r[k], int)
    return r


def _reset_snipe_stats():
    S.snipe_n = S.snipe_wins = S.snipe_trades = 0
    S.snipe_pnl = 0.0
    S.snipe_cash = 0.0


def _add_snipe_stat(row, new_trade=True):
    """统计增量: 建仓计数、结算命中/盈亏。阶段一落袋现金由 _snipe_add_cash 单独累加,
    避免结算时把同一笔 cash 重复计入。"""
    if new_trade:
        S.snipe_trades += 1
    if int(row.get("settled") or 0) == 1:
        S.snipe_n += 1
        S.snipe_wins += int(row.get("hit") or 0)
        S.snipe_pnl += float(row.get("pnl") or 0)


def _snipe_add_cash(v):
    S.snipe_cash += float(v or 0)


def load_snipe_trades():
    _reset_snipe_stats()
    S.snipe = []
    if not os.path.exists(SNIPE_CSV):
        return
    try:
        with open(SNIPE_CSV, newline="", encoding="utf-8") as fh:
            rows = list(csv.DictReader(fh))
        for r in rows:
            if not r.get("start"):
                continue
            _snipe_row_num(r)
            if not r.get("nid"):
                r["nid"] = f"legacy-{len(S.snipe) + 1}"
            S.snipe.append(r)
            _add_snipe_stat(r)
            if int(r.get("tp_hit") or 0):
                _snipe_add_cash(r.get("cash1"))
        log.info("已加载狙击记录 %d 笔 (已结算 %d)", len(S.snipe), S.snipe_n)
        S.snipe_seq = len(S.snipe)
    except Exception:
        log.exception("加载狙击记录失败")


def snipe_stats():
    n = S.snipe_n
    tp = sum(1 for r in S.snipe if int(r.get("tp_hit") or 0))
    return {"trades": S.snipe_trades, "settled": n, "wins": S.snipe_wins,
            "win_rate": (S.snipe_wins / n) if n else None,
            "pnl": round(S.snipe_pnl, 4), "cash": round(S.snipe_cash, 4),
            "tp_hits": tp, "tp_rate": (tp / S.snipe_trades) if S.snipe_trades else None,
            "avg_entry": round(sum(float(r.get("entry") or 0) for r in S.snipe) / len(S.snipe), 4)
            if S.snipe else None,
            "enabled": bool(S.snipe_cfg.get("enabled"))}


def snipe_page(page=1, size=20):
    rows = S.snipe
    total = len(rows)
    size = max(1, min(int(size or 20), 200))
    pages = max(1, math.ceil(total / size))
    page = max(1, min(int(page or 1), pages))
    start = total - page * size
    end = total - (page - 1) * size
    return {"page": page, "size": size, "pages": pages, "total": total,
            "rows": rows[max(0, start):max(0, end)]}


def snipe_curve(max_points=300):
    """累计总盈亏曲线（含阶段一落袋 + 结算余额），按建仓顺序。"""
    pts = []
    cum = 0.0
    for i, r in enumerate(S.snipe, 1):
        cash = float(r.get("cash1") or 0) if int(r.get("tp_hit") or 0) else 0.0
        sv = float(r.get("settle_value") or 0) if int(r.get("settled") or 0) == 1 else -float(r.get("amount") or 0)
        cum += cash + sv - float(r.get("amount") or 0)
        pts.append([i, round(cum, 4)])
    if len(pts) > max_points:
        step = len(pts) / max_points
        keep = [pts[int(i * step)] for i in range(max_points)]
        keep[-1] = pts[-1]
        pts = keep
    return pts


def snipe_atr(now, sec=60):
    """1 分钟尺度的平均真实波幅($)：用最近 sec 秒的逐段绝对变动均值。"""
    ts, ps = S.bn.t, S.bn.p
    i0 = bisect_left(ts, now - 300)
    if len(ts) - i0 < 30:
        return None
    acc, n = 0.0, 0
    prev = None
    for k in range(i0, len(ts)):
        if prev is not None:
            acc += abs(ps[k] - prev)
            n += 1
        prev = ps[k]
    if n < 10:
        return None
    # 逐段均值换成 60 秒尺度的标准差近似(sqrt(60/平均间隔))
    span = ts[-1] - ts[i0]
    if span <= 0:
        return None
    return math.sqrt(max(acc * acc / n / n, 0.0) * (60.0 * n / span)) if acc > 0 else None


def _round_low_high(w, ref):
    """本场已发生的最低/最高价。必须用与 spot 同一个价格源，否则极值反弹会算错。"""
    if ref is None:
        return None, None
    start = float(w.get("start") or 0)
    i0 = bisect_left(ref.t, start)
    if i0 >= len(ref.t):
        return None, None
    ps = ref.p[i0:]
    return min(ps), max(ps)


def snipe_score(now, w, side, spot, strike, atr, remain, ref=None):
    """翻转评分 0~100，四段权重与看板卡片一一对应：

        时间窗 30  +  5秒订单流 35  +  极值反弹 20  +  预言机缓冲 15

    返回 (总分, 明细dict)。detail 里同时给出各段得分(s_*)和原始观测值，
    看板直接用，保证"卡片显示的分"就是"实际打分"。
    """
    W = SNIPE_W
    detail = {"s_time": 0.0, "s_flow": 0.0, "s_bounce": 0.0, "s_gap": 0.0,
              "tir": None, "tir30": None, "bounce": None, "gap": None, "tol": None}
    # 1) 时间窗: 剩余时间越充裕越容易完成反转(开盘插针与结尾秒数不足都扣分)
    detail["s_time"] = round(W["time"] * min(max(remain, 0.0) / 240.0, 1.0), 2)
    if atr is None or atr <= 0:
        return round(detail["s_time"], 2), detail
    # 2) 5 秒主动成交失衡: 便宜侧要翻转获胜, 需要资金反向回流。
    #    Up 被砸到地板 => 需净买入(空头衰竭); Down 被拉爆 => 需净卖出(多头衰竭)。
    r5 = (S.flow["bn"].ratio_since(now, 5) + S.flow["okx"].ratio_since(now, 5)) / 2
    r30 = (S.flow["bn"].ratio_since(now, 30) + S.flow["okx"].ratio_since(now, 30)) / 2
    tir = r5 if side == "Up" else -r5
    detail["tir"] = round(tir, 4)
    detail["tir30"] = round(r30 if side == "Up" else -r30, 4)
    detail["s_flow"] = round(W["flow"] * min(max((tir + 0.1) / 0.6, 0.0), 1.0), 2)
    # 3) 极值反弹: 从本场极值反抽的美元幅度 / ATR
    lo, hi = _round_low_high(w, ref)
    if lo is not None and hi is not None:
        bounce = (spot - lo) if side == "Up" else (hi - spot)
        detail["bounce"] = round(bounce, 2)
        detail["s_bounce"] = round(W["bounce"] * min(max(bounce / (atr * 0.6), 0.0), 1.0), 2)
    # 4) 缓冲垫: 距离 strike 的落差在可追回范围内, 越近分越高
    gap = abs(spot - strike) if strike else 0.0
    tol = atr * math.sqrt(max(remain, 1) / 60.0)
    detail["gap"], detail["tol"] = round(gap, 2), round(tol, 2)
    if tol > 0:
        detail["s_gap"] = round(W["gap"] * min(max(1.0 - gap / (tol * 1.65), 0.0), 1.0), 2)
    total = detail["s_time"] + detail["s_flow"] + detail["s_bounce"] + detail["s_gap"]
    return round(min(total, 100.0), 2), detail


def _snipe_save():
    """整表重写账本 CSV。狙击记录很少(每场最多几笔)，重写比按值匹配更可靠：
    同一场可能多次建仓，用 start 匹配会命中错误的行。"""
    os.makedirs(DATA, exist_ok=True)
    with open(SNIPE_CSV, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(SNIPE_FIELDS), extrasaction="ignore", restval="")
        w.writeheader()
        w.writerows(S.snipe)
    _csv_fields[SNIPE_CSV] = list(SNIPE_FIELDS)


def _snipe_open(s0, now, w, r, spot, side, ask, atr, strike, r_gap, score, d, src):
    """建仓落账：自动与手动共用，唯一区别是 src 标记。"""
    cfg = S.snipe_cfg or {}
    tau = now - s0
    remain = max(0.0, (s0 + WIN) - now)
    amount = float(cfg["bet"])
    shares = round(amount / float(ask), 6)
    tp_target = round(max(float(ask) * float(cfg["tp_mult"]), float(cfg["tp_min"])), 4)
    row = {
        "nid": f"{s0}-{S.snipe_seq + 1}", "start": s0,
        "time_utc": time.strftime("%m-%d %H:%M:%S", time.gmtime(now)),
        "src": src,
        "side": side, "entry": round(float(ask), 4), "shares": shares,
        "amount": round(amount, 4), "tau": round(tau, 1), "remain": round(remain, 1),
        "spot": round(float(spot), 2), "strike": round(float(strike), 2),
        "atr": round(float(atr), 3), "r_gap": round(float(r_gap), 3),
        "score": score, "s_time": d.get("s_time", 0.0), "tir": d.get("tir", 0.0),
        "tir30": d.get("tir30", 0.0), "bounce": d.get("bounce", 0.0),
        "s_flow": d.get("s_flow", 0.0), "s_bounce": d.get("s_bounce", 0.0),
        "s_gap": d.get("s_gap", 0.0),
        "tp_target": tp_target, "tp_hit": 0, "tp_tau": "", "tp_bid": "", "tp_shares": 0.0,
        "cash1": 0.0,
        "stage": "HOLDING", "outcome": "", "hit": "", "settle_value": "", "pnl": "",
        "settled": 0,
    }
    if not os.path.exists(SNIPE_CSV):
        os.makedirs(DATA, exist_ok=True)
        with open(SNIPE_CSV, "w", newline="", encoding="utf-8") as fh:
            csv.DictWriter(fh, fieldnames=list(SNIPE_FIELDS)).writeheader()
    append_csv(SNIPE_CSV, row)
    S.snipe.append(row)
    _add_snipe_stat(row)
    S.snipe_seq += 1
    w["snipe_cnt"] = int(w.get("snipe_cnt") or 0) + 1
    w.setdefault("snipe_rows", []).append(row)
    log.info("狙击建仓[%s] %s side=%s entry=%.3f shares=%.4f 剩余%.0fs 落差%.1f$ R_gap=%.2f ATR=%.2f "
             "评分%.1f (时间%.0f 流%.0f 反弹%.0f 缓冲%.0f) 止盈线%.3f",
             src, s0, side, ask, shares, remain, abs(spot - strike), r_gap, atr, score,
             d.get("s_time", 0), d.get("s_flow", 0), d.get("s_bounce", 0), d.get("s_gap", 0),
             tp_target)
    return row


def try_snipe(s0, now, w, r, spot, ref=None):
    """盯盘狙击: 任一侧卖一在价格区间内且各项条件达标则自动建仓(每场限 per_round 次)。"""
    cfg = S.snipe_cfg or {}
    if not cfg.get("enabled") or not w.get("up") or spot is None:
        return
    tau = now - s0
    if tau < float(cfg["tau_min"]) or tau > float(cfg["tau_max"]):
        return
    if int(w.get("snipe_cnt") or 0) >= int(cfg["per_round"]):
        return
    cap = float(cfg["max_entry"])
    lo = float(cfg.get("min_entry") or 0.0)
    # 找出被打到地板的一侧（卖一在区间内）；两侧都便宜时取更便宜的一侧
    cand = []
    for side, ask, bid in (("Up", r.get("up_ask"), r.get("up_bid")),
                           ("Down", r.get("dn_ask"), r.get("dn_bid"))):
        if ask is not None and lo <= ask <= cap:
            cand.append((side, ask, bid))
    if not cand:
        return
    side, ask, _bid = min(cand, key=lambda x: x[1])
    strike = r.get("p0")
    atr = snipe_atr(now)
    if not strike or not atr:
        return
    remain = max(0.0, (s0 + WIN) - now)
    r_gap = abs(spot - strike) / (atr * math.sqrt(max(remain, 1) / 60.0))
    if r_gap > float(cfg["r_gap_max"]):
        return
    score, d = snipe_score(now, w, side, spot, strike, atr, remain, ref)
    if score < float(cfg["min_score"]):
        return
    return _snipe_open(s0, now, w, r, spot, side, ask, atr, strike, r_gap, score, d, "auto")


def try_snipe_tp(s0, now, r, rows=None):
    """阶段一止盈: 持仓中且买一 >= 止盈线, 卖出 tp_frac 份额抽回本金。

    只遍历本场记录（由 ticker 传入），避免每秒扫整个账本。
    """
    for row in (rows if rows is not None else S.snipe):
        if row.get("start") != s0 or int(row.get("tp_hit") or 0) or int(row.get("settled") or 0):
            continue
        side = row.get("side")
        bid = r.get("up_bid") if side == "Up" else r.get("dn_bid")
        target = float(row.get("tp_target") or 0)
        if bid is None or target <= 0 or bid < target:
            continue
        shares = float(row.get("shares") or 0)
        frac = float((S.snipe_cfg or {}).get("tp_frac") or 0.5)
        sell = round(shares * frac, 6)
        cash = round(sell * float(bid), 4)
        row.update(tp_hit=1, tp_tau=round(now - s0, 1), tp_bid=round(float(bid), 4),
                   tp_shares=sell, cash1=cash, stage="FREEROLL" if frac < 1 else "CLOSED")
        _snipe_add_cash(cash)
        _snipe_save()
        log.info("狙击半仓止盈 %s side=%s bid=%.3f>=%.3f 卖出%.4f份 落袋%.2fU 余%.4f份",
                 s0, side, bid, target, sell, cash, shares - sell)


def settle_snipe(s, outcome):
    """结算: 剩余份额按 1U 或 0 兑付, 与阶段一已落袋现金合并算总盈亏。"""
    if not outcome:
        return
    for row in S.snipe:
        if row.get("start") != s:
            continue
        hit = int(row.get("side") == outcome)
        shares = float(row.get("shares") or 0)
        amount = float(row.get("amount") or 0)
        sold = float(row.get("tp_shares") or 0) if int(row.get("tp_hit") or 0) else 0.0
        left = max(0.0, round(shares - sold, 6))
        settle_value = round(left * (1.0 if hit else 0.0), 4)
        cash = float(row.get("cash1") or 0) if int(row.get("tp_hit") or 0) else 0.0
        pnl = round(cash + settle_value - amount, 4)
        if (int(row.get("settled") or 0) == 1 and row.get("outcome") == outcome
                and abs(float(row.get("pnl") or 0) - pnl) < 1e-9):
            continue
        old = int(row.get("settled") or 0) == 1
        old_pnl = float(row.get("pnl") or 0) if old else 0.0
        old_hit = int(row.get("hit") or 0) if old else 0
        row.update(outcome=outcome, hit=hit, settle_value=settle_value, pnl=pnl, settled=1,
                   stage="WON_FULL" if (hit and int(row.get("tp_hit") or 0)) else
                         ("WON" if hit else ("FREEROLL_LOST" if int(row.get("tp_hit") or 0) else "LOST")))
        if not old:
            _add_snipe_stat(row, new_trade=False)
        else:
            S.snipe_wins += hit - old_hit
            S.snipe_pnl += pnl - old_pnl
        _snipe_save()
        log.info("狙击结算 %s side=%s outcome=%s %s 落袋%.2f + 结算%.2f - 投入%.2f = %+.3fU [%s]",
                 s, row.get("side"), outcome, "HIT" if hit else "MISS", cash, settle_value,
                 amount, pnl, row["stage"])


def settle_paper(s, outcome):
    """场次结束后回填模拟单。投入 amount U 买 shares=amount/买价 份:
    中则收回 shares*1U, 盈亏 = shares - amount; 错则盈亏 = -amount。
    已结算也可被官方结果覆盖重算。"""
    if not outcome:
        return
    for row in reversed(S.paper):
        if row.get("start") != s:
            continue
        hit = int(row.get("side") == outcome)
        buy = float(row.get("buy_price") or 0)
        amount = float(row.get("amount") or 0)
        if amount <= 0 and buy > 0:
            amount = buy  # 旧记录按 1 份兼容
        shares = float(row.get("shares") or 0)
        if shares <= 0 and buy > 0 and amount > 0:
            shares = amount / buy
        pnl = round((shares - amount) if hit else (-amount), 4)
        if (row.get("outcome") == outcome and int(row.get("hit") or 0) == hit
                and int(row.get("settled") or 0) == 1
                and abs(float(row.get("pnl") or 0) - pnl) < 1e-9):
            continue
        old_hit = int(row.get("hit") or 0) if int(row.get("settled") or 0) == 1 else None
        old_pnl = float(row.get("pnl") or 0) if old_hit is not None else None
        row["outcome"] = outcome
        row["hit"] = hit
        row["pnl"] = pnl
        row["settled"] = 1
        if old_hit is None:
            _add_paper_stat(row, new_trade=False)
        else:
            # 官方结果覆盖: 修正累计
            prof = row.get("sig") or "strong"
            p = S.paper_prof.setdefault(prof, {"n": 0, "wins": 0, "pnl": 0.0, "trades": 0})
            d_hit, d_pnl = hit - old_hit, pnl - old_pnl
            S.paper_wins += d_hit
            S.paper_pnl += d_pnl
            p["wins"] += d_hit
            p["pnl"] += d_pnl
        _patch_csv(PAPER_CSV, s, {"outcome": outcome, "hit": hit, "pnl": pnl, "settled": 1},
                   match={"sig": row.get("sig") or "strong"})
        log.info("模拟结算[%s] %s side=%s outcome=%s %s amount=%.2fU pnl=%+.3f",
                 PAPER_PROFILE_LABEL.get(row.get("sig"), row.get("sig")), s, row.get("side"),
                 outcome, "HIT" if hit else "MISS", amount, pnl)


def cl_fresh(now=None):
    """Chainlink现货是否新鲜: 消息刚到达(<5s) 且 价格自带时间戳也够新(<10s)。
    只看到达时间会漏掉"消息还在来但价格是旧的/重复的"这种情况。"""
    now = now or time.time()
    return bool(S.cl_src == "chainlink" and S.cl.t and now - S.last_msg["cl"] < 5 and now - S.cl.t[-1] < 10)


def cl_near(t, tol=15.0):
    """t±tol 秒内是否有过Chainlink价格点 (用于判断场次开盘/收盘时数据是否有效)"""
    i = bisect_left(S.cl.t, t - tol)
    return i < len(S.cl.t) and S.cl.t[i] <= t + tol


def cl_stalled(now=None, limit=20.0):
    """已认证连接着, 但Chainlink价格流超过limit秒没有新点 -> 视为订阅静默/卡死"""
    now = now or time.time()
    if S.auth != "ok" or S.pm_ws is None or S.pm_ws.closed:
        return False
    if now - S.conn_t < limit:
        return False
    return (not S.cl.t) or now - S.cl.t[-1] > limit or now - S.last_msg["cl"] > limit


def get_ref():
    """结算用的参考价: Chainlink现货优先, 否则退回币安(代理)"""
    if cl_fresh():
        return S.cl, "chainlink"
    return S.bn, "binance*"


# ------------------------------------------------------------------ 公允概率模型
def _F(x, y):
    if x > y:
        x, y = y, x
    return x * x * y / 2 - x ** 3 / 6


def _G(a1, b1, a2, b2):
    """Cov(∫_{a1}^{b1} W, ∫_{a2}^{b2} W) / sigma^2, W为布朗运动"""
    return _F(b1, b2) - _F(a1, b2) - _F(b1, a2) + _F(a1, a2)


def fair(t, s0, ref, sigma, p0_fix=None, shift=0.0):
    """
    在时刻t, 估计 P(C >= P0)。
    P0 = 均值[s0-60, s0], C = 均值[s0+240, s0+300]。已发生部分用历史价, 未发生部分用当前价+布朗运动。
    sigma: 价格波动 $/sqrt(s)
    """
    e = s0 + WIN
    st = ref.at(t)
    if st is None:
        return None
    st += shift          # nowcast: 用币安领先量修正Chainlink的约2秒滞后

    def avg_part(a, b):
        kb = min(b, t)
        k = int(kb - a)
        known = 0.0
        if k > 0:
            known = sum((ref.at(a + i + 1) or st) for i in range(k)) * ((kb - a) / k)
        return known + st * max(0.0, b - max(a, t))

    p0_self = avg_part(s0 - TW, s0) / TW
    c = avg_part(e - TW, e) / TW
    # 开盘后模型可用官方 TWAP 作 P0；自算值始终保留，供对照，避免日志里“自算=官方”
    p0 = p0_fix if (p0_fix is not None and t >= s0) else p0_self
    mu = c - p0

    def rng(a, b):
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


CALIB = []


def load_calib():
    try:
        CALIB[:] = json.load(open(f"{DATA}/calib.json"))["buckets"]
        log.info("已加载校准参数 %d 档", len(CALIB))
    except Exception:
        pass


def _num(v, cast=float):
    if v in ("", None):
        return None
    try:
        return cast(v)
    except Exception:
        return v


def _reset_round_stats():
    S.round_n = S.round_hits = S.round_cn = S.round_chits = 0


def _add_round_stat(row):
    S.round_n += 1
    hit = int(row.get("hit") or 0)
    S.round_hits += hit
    if int(row.get("conf") or 0):
        S.round_cn += 1
        S.round_chits += hit


def _adj_round_hit(old_hit, new_hit, conf):
    """官方结果覆盖时修正命中累计。"""
    d = int(new_hit) - int(old_hit)
    if not d:
        return
    S.round_hits += d
    if int(conf or 0):
        S.round_chits += d


def round_stats():
    n, cn = S.round_n, S.round_cn
    return {"n": n, "acc": (S.round_hits / n) if n else None,
            "cn": cn, "cacc": (S.round_chits / cn) if cn else None,
            "shown": len(S.rounds)}


def load_rounds():
    """重启后从 CSV 恢复：全量计入命中率，内存只保留最近 ROUNDS_KEEP 场供表格翻页。"""
    path = f"{DATA}/rounds_v2.csv"
    if not os.path.exists(path):
        baks = sorted(f for f in os.listdir(DATA) if f.startswith("rounds_v2.csv.") and f.endswith(".bak")) if os.path.isdir(DATA) else []
        if baks:
            log.warning("未找到 %s，但有归档 %s；如需恢复可手动改回原名", path, baks[-1])
        return
    try:
        with open(path, newline="") as fh:
            rows = list(csv.DictReader(fh))
        _reset_round_stats()
        keep = rows[-ROUNDS_KEEP:]
        for r in rows:
            for k in ("hit", "conf", "start"):
                if k in r:
                    r[k] = _num(r[k], int)
            _add_round_stat(r)
        for r in keep:
            for k in ("p_pred", "p0_calc", "c_calc", "p0_tw", "c_tw",
                      "up_bid0", "up_ask0", "dn_bid0", "dn_ask0", "sigma",
                      "r1", "r3", "r5", "r15", "flow", "obi", "bn_cl_bps", "bn_okx_bps"):
                if k in r:
                    r[k] = _num(r[k], float)
            for k in ("hit", "conf", "start"):
                if k in r:
                    r[k] = _num(r[k], int)
            S.rounds.append(r)
        log.info("已加载历史场次 全量=%d 看板=%d", S.round_n, len(S.rounds))
    except Exception:
        log.exception("加载历史场次失败")


def calibrate(p, tau):
    """Platt校准: 按 tau 分档修正模型概率 (参数由 analyze.py 生成)"""
    for lo, hi, a, b in CALIB:
        if lo <= tau < hi:
            x = min(max(p, 1e-4), 1 - 1e-4)
            return 1 / (1 + math.exp(-(a * math.log(x / (1 - x)) + b)))
    return p


def official_p0(s0):
    """开盘时刻的官方 Chainlink TWAP60 (流里离s0最近且不晚于s0的点, 超过3秒视为没有)"""
    i = bisect_right(S.tw.t, s0) - 1
    return S.tw.p[i] if i >= 0 and s0 - S.tw.t[i] <= 3 else None


def est_sigma_h(h, now, lag=30, span=1200):
    """lag秒尺度的波动 ($/sqrt(s))。Chainlink现货方差比随周期上升(60秒约为2秒的1.67倍),
    逐tick估计会低估30-60秒波动约29%, 导致高概率区间过度自信。"""
    n, acc, t = 0, 0.0, now - span
    while t + lag <= now:
        a, b = h.at(t), h.at(t + lag)
        if a is not None and b is not None:
            acc += (b - a) ** 2
            n += 1
        t += 5.0
    return math.sqrt(acc / (n * lag)) if n >= 20 else None


def nowcast_shift(now, g=2.0):
    """币安领先Chainlink约2秒: 用 bn(now)-bn(now-g) 估计Chainlink即将出现的变动"""
    if not S.bn.t or now - S.bn.t[-1] > 3:
        return 0.0
    b0 = S.bn.at(now - g)
    return S.bn.p[-1] - b0 if b0 is not None else 0.0


def est_sigma(h, now, span=300):
    i0 = bisect_left(h.t, now - span)
    ts, ps = h.t[i0:], h.p[i0:]
    if len(ts) < 30:
        return None
    acc = tot = 0.0
    for k in range(1, len(ts)):
        dt = ts[k] - ts[k - 1]
        if dt > 0:
            acc += (ps[k] - ps[k - 1]) ** 2
            tot += dt
    return math.sqrt(acc / tot) if tot > 0 else None


def flow_ratio(dq, now, sec=60):
    """主动成交方向占比。dq 可以是 Flow 对象或旧式 deque。"""
    if hasattr(dq, "ratio"):
        return dq.ratio(now)
    while dq and dq[0][0] < now - 180:
        dq.popleft()
    xs = [q for ts, q in dq if ts >= now - sec]
    tot = sum(abs(x) for x in xs)
    return sum(xs) / tot if tot > 0 else 0.0


def features(t):
    """辅助特征(仅记录, 用于后续拟合)"""
    f, bn = {}, S.bn.last()
    for k, sec in (("r1", 60), ("r3", 180), ("r5", 300), ("r15", 900)):
        p0 = S.bn.at(t - sec)
        f[k] = (bn / p0 - 1) * 1e4 if bn and p0 else 0.0
    f["flow"] = (flow_ratio(S.flow["bn"], t) + flow_ratio(S.flow["okx"], t)) / 2
    f["obi"] = (S.obi["bn"] + S.obi["okx"]) / 2
    cl, okx = S.cl.last(), S.okx.last()
    f["bn_cl_bps"] = (bn / cl - 1) * 1e4 if bn and cl else 0.0
    f["bn_okx_bps"] = (bn / okx - 1) * 1e4 if bn and okx else 0.0
    return {k: round(v, 4) for k, v in f.items()}


# ------------------------------------------------------------------ Polymarket 数据
def fl(x):
    try:
        return float(x)
    except Exception:
        return None


def quote(tok):
    q = S.pm.get(tok)
    return (q[0], q[1]) if q else (None, None)


async def pm_sub(tokens, on=True):
    for t in tokens:
        (S.tokens.add if on else S.tokens.discard)(t)
    ws = S.pm_ws
    if ws is not None and not ws.closed and tokens:
        await ws.send_json({"op": "subscribe" if on else "unsubscribe",
                            "subscriptions": [{"channel": "price.polymarket", "filter": {"asset_id": t}}
                                              for t in tokens]})


def _creds():
    c = (os.getenv("POLY_API_KEY"), os.getenv("POLY_API_SECRET"), os.getenv("POLY_API_PASSPHRASE"))
    return c if all(c) else None


def _g(o, *names):
    for n in names:
        v = getattr(o, n, None)
        if v is None and isinstance(o, dict):
            v = o.get(n)
        if v:
            return v
    return None


_last_derive = [0.0]


async def maybe_derive():
    """没有 POLY_API_* 但有 POLY_PRIVATE_KEY 时, 自动生成API凭据(只放内存, 不落盘)"""
    c = _creds()
    pk = os.getenv("POLY_PRIVATE_KEY")
    if c or not pk:
        return c
    if time.time() - _last_derive[0] < 60:
        return None
    _last_derive[0] = time.time()
    S.auth = "deriving"

    def work():
        from py_clob_client_v2 import ClobClient
        cr = ClobClient(host=CLOB, chain_id=137, key=pk).create_or_derive_api_key()
        return _g(cr, "api_key", "apiKey", "key"), _g(cr, "api_secret", "secret"), _g(cr, "api_passphrase", "passphrase")

    try:
        k, sec, pp = await asyncio.to_thread(work)
        if k and sec and pp:
            os.environ["POLY_API_KEY"], os.environ["POLY_API_SECRET"], os.environ["POLY_API_PASSPHRASE"] = k, sec, pp
            log.info("已用私钥自动生成 Polymarket API 凭据 (仅内存, 未落盘)")
            return (k, sec, pp)
        log.warning("自动生成API凭据: SDK返回内容不完整")
    except ImportError:
        log.warning("缺少 py-clob-client-v2: 请运行 /opt/btc5m/venv/bin/pip install py-clob-client-v2")
    except Exception as e:
        log.warning("自动生成API凭据失败: %s: %s", type(e).__name__, str(e).replace(pk, "***")[:200])
    S.auth = "derive-failed"
    return None


def _crypto_points(pl):
    if not isinstance(pl, dict) or pl.get("symbol") != "btcusd":
        return []
    pts = pl["data"] if isinstance(pl.get("data"), list) else [pl]
    out = []
    for p in pts:
        # 不带过滤订阅时一包里混着其它币种, 必须逐条筛掉, 否则会污染价格序列
        if isinstance(p, dict) and p.get("symbol") not in (None, "btcusd"):
            continue
        v = fl(p.get("full_accuracy_value", p.get("value")))
        if v is not None and "timestamp" in p:
            out.append((p["timestamp"] / 1000, v))
    return out


async def ws_poly(sess):
    while True:
        creds = await maybe_derive()
        try:
            async with sess.ws_connect(POLY_WS, heartbeat=None) as ws:
                S.pm_ws = ws
                S.conn_t = time.time()
                gated = [{"channel": "price.crypto"} if S.cl_nofilter else
                         {"channel": "price.crypto", "filter": {"symbol": "btcusd"}},
                         {"channel": "price.crypto.twap", "filter": {"symbol": "btcusd", "window_seconds": 60}}]
                if S.cl_nofilter:
                    log.info("price.crypto 使用不带过滤的订阅, 本地只保留 btcusd")
                if creds:
                    S.auth = "authenticating"
                    await ws.send_json({"op": "auth", "rid": "a1", "auth": {
                        "apiKey": creds[0], "secret": creds[1], "passphrase": creds[2]}})
                else:
                    log.warning("没有 POLY_PRIVATE_KEY / POLY_API_* : 没有Chainlink价格, 退回币安代理")
                subs = [{"channel": "price.polymarket", "filter": {"asset_id": t}} for t in S.tokens]
                if subs:
                    await ws.send_json({"op": "subscribe", "rid": "s1", "subscriptions": subs})
                async for m in ws:
                    if m.type != aiohttp.WSMsgType.TEXT:
                        continue
                    raw = m.data
                    # 不带过滤订阅时全市场消息都会推过来; 子串预筛比 json.loads 便宜两个数量级。
                    # 控制消息(op)必须放行, 否则认证/订阅回执会被丢掉。
                    if (S.cl_nofilter and '"op"' not in raw and "btcusd" not in raw
                            and "price.polymarket" not in raw):
                        S.msg["drop"] = S.msg.get("drop", 0) + 1
                        continue
                    _t0 = time.process_time()
                    try:
                        d = json.loads(raw)
                    except Exception:
                        continue
                    S.msg["poly"] += 1
                    S.msg_cost["poly"] += time.process_time() - _t0
                    now = time.time()
                    op = d.get("op")
                    if op:
                        if op == "authed":
                            S.auth = "ok"
                            await ws.send_json({"op": "subscribe", "rid": "s2", "subscriptions": gated})
                        elif op == "error":
                            log.warning("polybolt error: %s", d)
                            if str(d.get("code", "")).startswith("auth"):
                                S.auth = "FAILED:" + d["code"]
                        continue
                    ch, pl = d.get("channel"), d.get("payload")
                    if ch == "price.polymarket":
                        if isinstance(pl, dict) and "asset_id" in pl:
                            S.pm[pl["asset_id"]] = (fl(pl.get("best_bid")), fl(pl.get("best_ask")), now)
                            S.last_msg["pm"] = now
                    elif ch == "price.crypto":
                        for ts, v in _crypto_points(pl):
                            S.cl.add(ts, v)
                        S.cl_src = (pl or {}).get("source", "") if isinstance(pl, dict) else S.cl_src
                        S.last_msg["cl"] = now
                    elif ch == "price.crypto.twap":
                        for ts, v in _crypto_points(pl):
                            S.tw.add(ts, v)
                        S.last_msg["tw"] = now
                log.warning("polybolt closed code=%s", ws.close_code)
        except Exception as e:
            log.warning("polybolt ws: %s", e)
        S.pm_ws = None
        await asyncio.sleep(3)


async def get_tokens(sess, start):
    try:
        async with sess.get(f"{GAMMA}/markets", params={"slug": f"btc-updown-5m-{start}"}, timeout=T5) as r:
            m = (await r.json())[0]
        ids, outs = m["clobTokenIds"], m["outcomes"]
        ids = json.loads(ids) if isinstance(ids, str) else ids
        outs = json.loads(outs) if isinstance(outs, str) else outs
        d = {o.lower(): i for o, i in zip(outs, ids)}
        return d.get("up"), d.get("down")
    except Exception:
        return None, None


def official_tw(t, tol=5.0):
    """时刻 t 的官方 Chainlink TWAP60；超过 tol 秒没有点则视为缺失。"""
    i = bisect_right(S.tw.t, t) - 1
    return S.tw.p[i] if i >= 0 and t - S.tw.t[i] <= tol else None


def twap_outcome(start):
    """Polymarket 真正的结算规则: 收盘TWAP60 >= 开盘TWAP60 => Up。这比等 Gamma closed 快得多。"""
    p0, c = official_tw(start), official_tw(start + WIN)
    if p0 is None or c is None:
        return None, p0, c
    return ("Up" if c >= p0 else "Down"), p0, c


async def gamma_outcome(sess, start):
    """Polymarket 盘口结果: outcomePrices 已钉到约 0/1 即采信, 不必再等 closed。
    closed 往往比价格钉住再晚好几分钟。"""
    try:
        async with sess.get(f"{GAMMA}/markets", params={"slug": f"btc-updown-5m-{start}"}, timeout=T5) as r:
            m = (await r.json())[0]
        outs, pr = m["outcomes"], m["outcomePrices"]
        outs = json.loads(outs) if isinstance(outs, str) else outs
        pr = [float(x) for x in (json.loads(pr) if isinstance(pr, str) else pr)]
        if max(pr) >= 0.99 and min(pr) <= 0.01:
            return outs[pr.index(max(pr))]
    except Exception:
        pass
    return None


async def gamma_debug(sess, start):
    """官方结果取不到时, 打印Gamma返回的关键字段以便排查"""
    try:
        async with sess.get(f"{GAMMA}/markets", params={"slug": f"btc-updown-5m-{start}"}, timeout=T5) as r:
            j = await r.json()
        if not j:
            return "empty list (slug不存在?)"
        m = j[0]
        return {k: m.get(k) for k in ("closed", "active", "archived", "umaResolutionStatus",
                                       "outcomePrices", "endDate", "resolvedBy") if k in m}
    except Exception as e:
        return f"error {type(e).__name__}: {e}"


async def rest_best(sess, token):
    try:
        async with sess.get(f"{CLOB}/book", params={"token_id": token}, timeout=T5) as r:
            j = await r.json()
        bids = [float(x["price"]) for x in j.get("bids", [])]
        asks = [float(x["price"]) for x in j.get("asks", [])]
        return (max(bids) if bids else None, min(asks) if asks else None)
    except Exception:
        return None, None


async def pm_fallback(sess):
    """流里一直没有的token, 用REST补一次"""
    while True:
        await asyncio.sleep(5)
        for w in list(S.win.values()):
            for tok in (w.get("up"), w.get("dn")):
                if tok and tok not in S.pm:
                    b, a = await rest_best(sess, tok)
                    if b is not None or a is not None:
                        S.pm[tok] = (b, a, time.time())


# ------------------------------------------------------------------ 币安 / 欧易
async def ws_binance(sess):
    while True:
        try:
            async with sess.ws_connect(BN_WS, heartbeat=20) as ws:
                async for m in ws:
                    if m.type != aiohttp.WSMsgType.TEXT:
                        continue
                    d = json.loads(m.data).get("data", {})
                    now = time.time()
                    S.msg["bn"] += 1
                    if d.get("e") == "aggTrade":
                        px, q = float(d["p"]), float(d["q"])
                        S.flow["bn"].add(now, -q if d["m"] else q)
                        S.bn.add(now, px, gap=1.0)
                    elif "bids" in d:
                        b = sum(float(x[1]) for x in d["bids"])
                        a = sum(float(x[1]) for x in d["asks"])
                        S.obi["bn"] = (b - a) / (b + a) if b + a else 0.0
                    S.last_msg["bn"] = now
        except Exception as e:
            log.warning("binance ws: %s", e)
        await asyncio.sleep(3)


async def ws_okx(sess):
    sub = {"op": "subscribe", "args": [{"channel": "trades", "instId": "BTC-USDT"},
                                       {"channel": "books5", "instId": "BTC-USDT"}]}

    async def ping(ws):
        while True:
            await asyncio.sleep(20)
            await ws.send_str("ping")

    while True:
        try:
            async with sess.ws_connect(OKX_WS) as ws:
                await ws.send_json(sub)
                pt = asyncio.create_task(ping(ws))
                try:
                    async for m in ws:
                        if m.type != aiohttp.WSMsgType.TEXT or m.data == "pong":
                            continue
                        d = json.loads(m.data)
                        ch = (d.get("arg") or {}).get("channel")
                        if ch not in ("trades", "books5"):
                            continue
                        S.msg["okx"] += 1
                        now = time.time()
                        for it in d.get("data", []):
                            if ch == "trades":
                                px, q = float(it["px"]), float(it["sz"])
                                S.flow["okx"].add(now, q if it["side"] == "buy" else -q)
                                S.okx.add(now, px, gap=1.0)
                            elif ch == "books5":
                                b = sum(float(x[1]) for x in it["bids"])
                                a = sum(float(x[1]) for x in it["asks"])
                                S.obi["okx"] = (b - a) / (b + a) if b + a else 0.0
                        S.last_msg["okx"] = now
                finally:
                    pt.cancel()
        except Exception as e:
            log.warning("okx ws: %s", e)
        await asyncio.sleep(3)


# ------------------------------------------------------------------ 场次生命周期
# 默认不覆盖历史 CSV。只有 BTC5M_MIGRATE_CSV=1 时, 表头不兼容才归档旧文件另开新表。
_csv_fields = {}


def append_csv(path, row):
    os.makedirs(DATA, exist_ok=True)
    fields = _csv_fields.get(path)
    if fields is None:
        if os.path.exists(path):
            with open(path, newline="") as fh:
                first = next(csv.reader(fh), [])
            if first:
                new_cols = [k for k in row if k not in first]
                missing = [k for k in first if k not in row]
                if new_cols or missing:
                    if os.getenv("BTC5M_MIGRATE_CSV") == "1":
                        bak = f"{path}.{int(time.time())}.bak"
                        os.rename(path, bak)
                        log.warning("%s 表头变化已归档为 %s (BTC5M_MIGRATE_CSV=1)", path, bak)
                        fields = list(row)
                    else:
                        fields = first
                        if new_cols:
                            log.warning("%s 继续沿用旧表头, 新列未写入: %s; 需要迁移时设 BTC5M_MIGRATE_CSV=1",
                                        path, ",".join(new_cols))
                else:
                    fields = first
            else:
                fields = list(row)
        else:
            fields = list(row)
        _csv_fields[path] = fields
    new = not os.path.exists(path)
    with open(path, "a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", restval="")
        if new:
            w.writeheader()
        w.writerow(row)


async def init_window(sess, s):
    w = S.win[s]
    while time.time() < s + WIN and s in S.win:
        up, dn = await get_tokens(sess, s)
        if up and dn:
            w["up"], w["dn"] = up, dn
            await pm_sub([up, dn], True)
            return
        await asyncio.sleep(3)


def make_pred(s):
    w = S.win[s]
    w["pred_done"] = True
    ref, rn = get_ref()
    if len(S.bn.t) < 120 or ref.last() is None:
        log.info("next %s: 历史数据不足, 跳过预判", s)
        return
    r = fair(time.time(), s, ref, S.sigma, shift=nowcast_shift(time.time()) if rn == "chainlink" else 0.0)
    if not r:
        return
    p = calibrate(r["p"], time.time() - s)
    w.update(pred="Up" if p >= 0.5 else "Down", p_pred=p, conf=abs(p - 0.5) >= CONF_TH,
             f=features(time.time()), r_pred=r, ref_name=rn,
             q0=quote(w["up"]) + quote(w["dn"]))
    log.info("next %s: pred=%s p_up=%.3f (spot-P0估计 %+.1f$, sd %.1f$) ref=%s up=%s dn=%s",
             s, w["pred"], p, r["mu"], r["sd"], rn, quote(w["up"]), quote(w["dn"]))


def _patch_csv(path, start, updates, match=None):
    """按 start(及 match 里的列)更新第一条匹配行; 没有该文件或找不到行则忽略。"""
    if not os.path.exists(path):
        return
    with open(path, newline="", encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh))
    if not rows:
        return
    fields = list(rows[0].keys())
    hit = False
    for row in rows:
        if str(row.get("start")) == str(start) and all(
                str(row.get(k) or "") == str(v) for k, v in (match or {}).items() if k in fields):
            for k, v in updates.items():
                if k in fields:
                    row[k] = v
            hit = True
            break
    if not hit:
        return
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", restval="")
        w.writeheader()
        w.writerows(rows)


def _record_round(w, s, outcome, src, calc, r, p0_tw, c_tw):
    """写入 outcomes; 有预判时同步进看板历史。"""
    r = r or {}
    p0_calc = r.get("p0_self", r.get("p0", 0))
    append_csv(f"{DATA}/outcomes.csv", {
        "start": s, "outcome": outcome, "label": src, "calc_outcome": calc,
        "p0_calc": round(p0_calc, 2) if p0_calc is not None else None,
        "c_calc": round(r.get("c", 0), 2) if r.get("c") is not None else None,
        "p0_tw": round(p0_tw, 2) if p0_tw else None, "c_tw": round(c_tw, 2) if c_tw else None})
    if not w.get("pred"):
        return None
    row = {"start": s, "time_utc": time.strftime("%m-%d %H:%M", time.gmtime(s)),
           "pred": w["pred"], "p_pred": round(w["p_pred"], 4), "conf": int(w["conf"]),
           "outcome": outcome, "label": src, "hit": int(w["pred"] == outcome),
           "calc_outcome": calc, "p0_calc": round(p0_calc, 2) if p0_calc is not None else None,
           "c_calc": round(r.get("c", 0), 2) if r.get("c") is not None else None,
           "p0_tw": round(p0_tw, 2) if p0_tw else None, "c_tw": round(c_tw, 2) if c_tw else None,
           "ref": w["ref_name"], "sigma": round(S.sigma, 3), **w["f"],
           "up_bid0": w["q0"][0], "up_ask0": w["q0"][1], "dn_bid0": w["q0"][2], "dn_ask0": w["q0"][3]}
    append_csv(f"{DATA}/rounds_v2.csv", row)
    S.rounds.append(row)
    _add_round_stat(row)
    settle_paper(s, outcome)
    settle_snipe(s, outcome)
    st = round_stats()
    log.info("round %s pred=%s(%.3f) outcome=%s[%s] %s | n=%d acc=%.1f%% | conf n=%d acc=%s",
             s, w["pred"], w["p_pred"], outcome, src, "HIT" if row["hit"] else "MISS", st["n"],
             (st["acc"] or 0) * 100, st["cn"],
             f"{st['cacc'] * 100:.1f}%" if st["cacc"] is not None else "-")
    return row


def _upgrade_round(s, official, calc):
    """官方结果到位后, 把内存和 CSV 里的自算结果升级为官方。"""
    updates = {"outcome": official, "label": "polymarket", "calc_outcome": calc}
    for row in reversed(S.rounds):
        if row.get("start") == s:
            old_hit = int(row.get("hit") or 0)
            row["outcome"] = official
            row["label"] = "polymarket"
            row["hit"] = int(row["pred"] == official)
            updates["hit"] = row["hit"]
            _adj_round_hit(old_hit, row["hit"], row.get("conf"))
            log.info("round %s 官方结果已更新: %s -> %s[%s] %s",
                     s, calc, official, "polymarket", "HIT" if row["hit"] else "MISS")
            break
    _patch_csv(f"{DATA}/rounds_v2.csv", s, updates)
    _patch_csv(f"{DATA}/outcomes.csv", s, {"outcome": official, "label": "polymarket", "calc_outcome": calc})
    settle_paper(s, official)
    settle_snipe(s, official)


async def settle(sess, s):
    E = s + WIN
    # 多等几秒让收盘时刻的官方 TWAP60 点进来
    await asyncio.sleep(max(0, E + 3 - time.time()))
    w = S.win.get(s)
    try:
        if w:
            cl_ok = cl_near(s) and cl_near(E)
            p0_tw = official_p0(s)
            r = fair(E + 1, s, S.cl, 1.0, p0_fix=p0_tw) if cl_ok and S.cl.last() is not None else None
            calc = ("Up" if r["c"] >= r["p0_self"] else "Down") if r else None

            # 1) 最快官方源: 已订阅的 Chainlink TWAP60 (就是 Polymarket 结算规则)
            tw_out, p0_official, c_official = twap_outcome(s)
            if tw_out is None:
                for _ in range(8):  # 再等最多约8秒补齐收盘 TWAP
                    await asyncio.sleep(1)
                    tw_out, p0_official, c_official = twap_outcome(s)
                    if tw_out:
                        break
            p0_tw = p0_official if p0_official is not None else p0_tw
            c_tw = c_official

            recorded = False
            if tw_out:
                _record_round(w, s, tw_out, "twap", calc, r, p0_tw, c_tw)
                recorded = True
            elif calc:
                _record_round(w, s, calc, "calc", calc, r, p0_tw, c_tw)
                recorded = True
            else:
                log.warning("round %s 暂无 TWAP/自算结果", s)

            # 2) Polymarket Gamma: 价格钉到 0/1 即可, 不必等 closed (closed 往往更慢)
            official = None
            for it in range(36):
                official = await gamma_outcome(sess, s)
                if official:
                    break
                if it in (3, 12, 35):
                    log.info("gamma盘口未钉住 %s (第%d次): %s", s, it, await gamma_debug(sess, s))
                await asyncio.sleep(5)

            if official:
                if recorded:
                    if any(row.get("start") == s and row.get("outcome") != official for row in S.rounds):
                        log.warning("round %s TWAP/自算=%s 与 Gamma=%s 不一致, 以 Gamma 为准",
                                    s, tw_out or calc, official)
                    _upgrade_round(s, official, calc)
                else:
                    _record_round(w, s, official, "polymarket", calc, r, p0_tw, c_tw)
            elif not recorded:
                log.warning("round %s 跳过: 无 TWAP/自算且 Gamma 未钉住", s)
    except Exception:
        log.exception("settle")
    if w and w.get("up"):
        await pm_sub([w["up"], w["dn"]], False)
    S.win.pop(s, None)


async def ticker(sess):
    while True:
        try:
            _pt = time.process_time()
            now = time.time()
            s0 = int(now // WIN) * WIN
            for s in (s0, s0 + WIN):
                if s not in S.win:
                    done = {x.get("sig") or "strong" for x in S.paper if int(x.get("start") or 0) == s}
                    S.win[s] = {"start": s, "up": None, "dn": None, "pred": None, "pred_done": False,
                                "ticks": [], "paper_done": done, "snipe_cnt": 0, "snipe_rows": []}
                    asyncio.create_task(init_window(sess, s))
                    asyncio.create_task(settle(sess, s))
            nxt = s0 + WIN
            if nxt - now <= LEAD and not S.win[nxt]["pred_done"]:
                make_pred(nxt)
            ref, rn = get_ref()
            if S.win[nxt]["pred_done"]:
                try_paper_pre(nxt, now, S.win[nxt], ref.last())
            if now - S.sigma_t >= 5:
                S.sigma_t = now
                sg = est_sigma_h(ref, now)
                if sg:
                    S.sigma = 0.8 * S.sigma + 0.2 * sg
            shift = nowcast_shift(now) if rn == "chainlink" else 0.0
            v = {"now": now, "s0": s0, "ref": rn, "spot": ref.last(), "bn": S.bn.last(), "okx": S.okx.last(),
                 "sigma": S.sigma, "cur": None, "paper": None}
            cur = S.win[s0]
            if ref.last() is not None:
                op0 = official_p0(s0)
                r = fair(now, s0, ref, S.sigma, p0_fix=op0, shift=shift)
                if r:
                    r["p_raw"] = r["p"]
                    r["p"] = calibrate(r["p"], now - s0)
                    ub, ua = quote(cur["up"])
                    db, da = quote(cur["dn"])
                    r.update(end=s0 + WIN, up_bid=ub, up_ask=ua, dn_bid=db, dn_ask=da,
                             edge_up=(r["p"] - ua) if ua is not None else None,
                             edge_dn=((1 - r["p"]) - da) if da is not None else None,
                             pred=cur.get("pred"), p_pred=cur.get("p_pred"), conf=cur.get("conf"),
                             p0_src="official" if op0 is not None else "calc")
                    try_paper_fill(s0, now, cur, r, ref.last())
                    try_snipe(s0, now, cur, r, ref.last(), ref)
                    try_snipe_tp(s0, now, r, cur.get("snipe_rows"))
                    if cur.get("paper_trade"):
                        r["paper"] = cur["paper_trade"]
                    v["paper_status"] = paper_status(s0, now, cur, r, ref.last())
                    v["snipe_status"] = snipe_status(s0, now, cur, r, ref.last(), ref)
                    v["cur"] = r
                    cur["ticks"].append([round(now - s0, 1), round(r["p"], 4), ub, ua, db, da])
                    if now - S.ticks_t >= 2:
                        S.ticks_t = now
                        ft = features(now)
                        append_csv(f"{DATA}/ticks.csv", {
                            "ts": round(now, 1), "start": s0, "tau": round(now - s0, 1), "ref": rn,
                            "spot": round(ref.last(), 2), "bn": S.bn.last(), "okx": S.okx.last(),
                            "twap": S.tw.last(), "p0": round(r["p0"], 2), "p0_src": r["p0_src"],
                            "c_est": round(r["c"], 2), "p_up": round(r["p"], 4), "p_raw": round(r["p_raw"], 4),
                            "sd": round(r["sd"], 2), "up_bid": ub, "up_ask": ua, "dn_bid": db, "dn_ask": da,
                            "flow": ft["flow"], "obi": ft["obi"], "r1": ft["r1"], "bn_cl_bps": ft["bn_cl_bps"],
                            "shift": round(shift, 2), "sigma": round(S.sigma, 3)})
            nw = S.win[nxt]
            v["nxt"] = {"start": nxt, "pred": nw.get("pred"), "p": nw.get("p_pred"), "conf": nw.get("conf")}
            S.view = v
            _perf("ticker", _pt)
        except Exception:
            log.exception("ticker")
        await asyncio.sleep(max(0.05, 1 - (time.time() % 1)))


async def cl_watchdog():
    """订阅成功但价格流静默(只回一包快照后不再推送)时, 切换订阅方式并强制重连"""
    while True:
        await asyncio.sleep(5)
        try:
            if cl_stalled():
                S.cl_nofilter = not S.cl_nofilter
                log.warning("Chainlink价格流超过20秒无新数据, 强制重连并切换订阅方式(不带过滤=%s)", S.cl_nofilter)
                S.conn_t = time.time()
                await S.pm_ws.close()
        except Exception:
            log.exception("watchdog")


async def status():
    while True:
        await asyncio.sleep(30)
        now = time.time()
        age = {k: (f"{now - v:.0f}s" if v else "NEVER") for k, v in S.last_msg.items()}
        log.info("feeds %s | poly-auth=%s cl_src=%s | cl=%s tw=%s bn=%s okx=%s sigma=%.2f",
                 age, S.auth, S.cl_src, S.cl.last(), S.tw.last(), S.bn.last(), S.okx.last(), S.sigma)
        perf = perf_share()
        if perf:
            log.info("cpu %s", " | ".join(f"{k} {v['ms_per_s']}ms/s({v['per_s']}/s)" for k, v in
                                          sorted(perf.items(), key=lambda kv: -kv[1]["ms_per_s"])))
        tot = S.msg["poly"] + S.msg["bn"] + S.msg["okx"]
        if tot and now > S.started:
            el = now - S.started
            log.info("ws消息 poly=%d(%.1f/s,解析%.0fms) bn=%d(%.1f/s) okx=%d(%.1f/s)",
                     S.msg["poly"], S.msg["poly"] / el, S.msg_cost["poly"] * 1000,
                     S.msg["bn"], S.msg["bn"] / el, S.msg["okx"], S.msg["okx"] / el)


# ------------------------------------------------------------------ Web 看板
_cpu_sample = None
_proc_sample = None
_net_sample = None  # (ts, rx_bytes, tx_bytes)
_host_cache = {"t": 0.0, "v": None}


def _net_bytes():
    """整机网卡累计收/发字节(排除 lo)。"""
    rx = tx = 0
    with open("/proc/net/dev") as fh:
        for line in fh:
            if ":" not in line or line.lstrip().startswith("lo:"):
                continue
            parts = line.split(":")[1].split()
            if len(parts) >= 9:
                rx += int(parts[0])
                tx += int(parts[8])
    return rx, tx


def host_stats():
    """读本机 CPU / 内存 / 网卡流量 (Linux /proc)。不额外装依赖。
    多开看板时同一秒内只读一次 /proc。"""
    global _cpu_sample, _net_sample
    now_t = time.time()
    if _host_cache["v"] is not None and now_t - _host_cache["t"] < 1.0:
        out = dict(_host_cache["v"])
        out["uptime_sec"] = max(0, int(now_t - S.started))
        return out
    up = max(0, int(time.time() - S.started))
    out = {"cpu": None, "proc_cpu": None, "mem_used_mb": None, "mem_total_mb": None, "proc_mb": None,
           "uptime_sec": up, "started": round(S.started, 1),
           "net_rx": None, "net_tx": None, "net_rx_bps": None, "net_tx_bps": None}
    try:
        with open("/proc/stat") as fh:
            parts = fh.readline().split()
        total = sum(int(x) for x in parts[1:8])
        idle = int(parts[4]) + (int(parts[5]) if len(parts) > 5 else 0)
        now = (total, idle)
        if _cpu_sample and now[0] > _cpu_sample[0]:
            out["cpu"] = round((1 - (now[1] - _cpu_sample[1]) / (now[0] - _cpu_sample[0])) * 100, 1)
        _cpu_sample = now
    except Exception:
        pass
    try:
        # 本进程 CPU: 只算本进程的 utime+stime, 与整机负载区分开
        global _proc_sample
        with open("/proc/self/stat") as fh:
            sf = fh.read().rsplit(") ", 1)[1].split()
        ticks = (int(sf[11]) + int(sf[12])) / os.sysconf("SC_CLK_TCK")
        if _proc_sample and now_t > _proc_sample[0]:
            dt = now_t - _proc_sample[0]
            if dt > 0:
                out["proc_cpu"] = round(100 * (ticks - _proc_sample[1]) / dt, 1)
        _proc_sample = (now_t, ticks)
    except Exception:
        pass
    try:
        info = {}
        with open("/proc/meminfo") as fh:
            for line in fh:
                if line.startswith(("MemTotal:", "MemAvailable:")):
                    k, v, *_ = line.split()
                    info[k[:-1]] = int(v)
        if "MemTotal" in info and "MemAvailable" in info:
            out["mem_total_mb"] = round(info["MemTotal"] / 1024)
            out["mem_used_mb"] = round((info["MemTotal"] - info["MemAvailable"]) / 1024)
        with open("/proc/self/status") as fh:
            for line in fh:
                if line.startswith("VmRSS:"):
                    out["proc_mb"] = round(int(line.split()[1]) / 1024, 1)
                    break
    except Exception:
        pass
    try:
        t = time.time()
        rx, tx = _net_bytes()
        out["net_rx"], out["net_tx"] = rx, tx
        if _net_sample and t > _net_sample[0]:
            dt = t - _net_sample[0]
            if dt > 0:
                out["net_rx_bps"] = max(0, (rx - _net_sample[1]) / dt)
                out["net_tx_bps"] = max(0, (tx - _net_sample[2]) / dt)
        _net_sample = (t, rx, tx)
    except Exception:
        pass
    _host_cache["t"], _host_cache["v"] = now_t, out
    return out


def _auth(req):
    return not DASH_TOKEN or req.query.get("token") == DASH_TOKEN


async def api_state(req):
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    now = time.time()
    ref, _ = get_ref()
    chart = [[t, ref.at(t), S.bn.at(t), S.okx.at(t), S.tw.at(t)] for t in range(int(now) - 420, int(now), 2)]
    cur = S.win.get(int(now // WIN) * WIN)
    feeds = {k: (now - v if v else None) for k, v in S.last_msg.items()}
    try:
        ppage = int(req.query.get("ppage") or 1)
    except Exception:
        ppage = 1
    try:
        psize = int(req.query.get("psize") or 20)
    except Exception:
        psize = 20
    try:
        rpage = int(req.query.get("rpage") or 1)
    except Exception:
        rpage = 1
    try:
        rsize = int(req.query.get("rsize") or 20)
    except Exception:
        rsize = 20
    try:
        spage = int(req.query.get("spage") or 1)
    except Exception:
        spage = 1
    try:
        ssize = int(req.query.get("ssize") or 20)
    except Exception:
        ssize = 20
    return web.json_response({**S.view, "chart": chart, "ticks": cur["ticks"] if cur else [],
                              "rounds": round_page(rpage, rsize), "stats": round_stats(), "feeds": feeds,
                              "auth": S.auth, "cl_src": S.cl_src, "host": host_stats(),
                              "paper_cfg": S.paper_cfg, "paper": paper_page(ppage, psize),
                              "paper_stats": paper_stats(), "paper_curve": paper_curve(),
                              "snipe_cfg": S.snipe_cfg, "snipe": snipe_page(spage, ssize),
                              "snipe_stats": snipe_stats(), "snipe_curve": snipe_curve()})


DATA_FILES = ("rounds_v2.csv", "outcomes.csv", "ticks.csv", "paper_trades.csv",
              "paper_cfg.json", "snipe_trades.csv", "snipe_cfg.json", "calib.json")


async def api_export_rounds(req):
    """导出历史场次 CSV（只含 rounds_v2.csv）。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    path = f"{DATA}/rounds_v2.csv"
    name = f"btctest4-rounds-{time.strftime('%Y%m%d-%H%M%S', time.gmtime())}.csv"
    if not os.path.exists(path):
        return web.Response(status=404, text="no rounds data")
    with open(path, "rb") as fh:
        body = fh.read()
    if body.startswith(b"\xef\xbb\xbf"):   # 已有 BOM 就不重复加
        pass
    else:
        body = b"\xef\xbb\xbf" + body      # 加 BOM，Excel 直接打开不乱码
    log.info("导出历史场次 %s (%d 字节)", name, len(body))
    return web.Response(body=body, content_type="text/csv", charset="utf-8",
                        headers={"Content-Disposition": f'attachment; filename="{name}"'})


async def api_export_data(req):
    """打包导出全部策略数据文件(zip): 场次/结果/行情 tick/模拟成交/配置/校准。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    with_bak = req.query.get("bak") in ("1", "true", "yes")
    stamp = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    buf = io.BytesIO()
    included, skipped = [], []
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        names = list(DATA_FILES)
        if with_bak:
            for f in sorted(os.listdir(DATA)):
                if any(k in f for k in (".bak", ".cleared.")) and f not in names:
                    names.append(f)
        for f in names:
            p = f"{DATA}/{f}"
            if not os.path.exists(p):
                skipped.append(f)
                continue
            data = open(p, "rb").read()
            if f.endswith((".csv", ".json")) and not data.startswith(b"\xef\xbb\xbf"):
                data = b"\xef\xbb\xbf" + data   # Excel 直开不乱码
            zf.writestr(f, data)
            included.append(f)
        meta = {
            "exported_utc": stamp,
            "files": included,
            "rounds_total": S.round_n,
            "rounds_accuracy": round_stats()["acc"],
            "paper_stats": paper_stats(),
            "paper_cfg": S.paper_cfg,
            "snipe_stats": snipe_stats(),
            "snipe_cfg": S.snipe_cfg,
            "columns": {
                "rounds_v2.csv": "每场预判与结果：start/pred/p_pred/conf/outcome/hit/label/P0/收盘均价/预判时卖价/特征",
                "outcomes.csv": "每场结算结果(p0/c 自算与官方 TWAP)",
                "ticks.csv": "场中每 2 秒 tick：p_up/盘口买卖价/P0/特征",
                "paper_trades.csv": "模拟成交：sig(pre前/strong强/weak普)/tau相对开盘秒/strength模型强度/buy_price/amount/shares/btc/p0/btc_diff/pnl",
                "paper_cfg.json": "模拟下单参数",
                "snipe_trades.csv": "≤10¢绝地反转狙击：entry建仓价/shares份额/r_gap/score评分/tp_*半仓止盈/cash1落袋/settle_value结算值/pnl",
                "snipe_cfg.json": "狙击参数",
                "calib.json": "Platt 校准参数",
            },
        }
        zf.writestr("meta.json", json.dumps(meta, ensure_ascii=False, indent=2))
    body = buf.getvalue()
    name = f"btctest4-data-{stamp}.zip"
    log.info("导出策略数据 %s: %s (%d 字节)%s", name, ",".join(included), len(body),
             f"；缺失 {','.join(skipped)}" if skipped else "")
    return web.Response(body=body, content_type="application/zip",
                        headers={"Content-Disposition": f'attachment; filename="{name}"'})


async def api_clear_rounds(req):
    """清空看板历史场次；CSV 先归档为 .cleared.*.bak，不直接砸掉。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    n = S.round_n
    S.rounds.clear()
    _reset_round_stats()
    path = f"{DATA}/rounds_v2.csv"
    archived = None
    if os.path.exists(path):
        archived = f"{path}.cleared.{int(time.time())}.bak"
        os.rename(path, archived)
    _csv_fields.pop(path, None)
    log.info("已清空历史场次 %d 场%s", n, f"，归档 {archived}" if archived else "")
    return web.json_response({"ok": True, "cleared": n, "archived": archived})


async def api_paper_clear(req):
    """清空模拟成交记录；CSV 先归档为 .cleared.*.bak，不直接删。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    n = len(S.paper)
    S.paper = []
    _reset_paper_stats()
    path = PAPER_CSV
    archived = None
    if os.path.exists(path):
        archived = f"{path}.cleared.{int(time.time())}.bak"
        os.rename(path, archived)
    _csv_fields.pop(path, None)
    for w in S.win.values():
        w["paper_done"] = set()
        w.pop("paper_trade", None)
    log.info("已清空模拟成交 %d 笔%s", n, f"，归档 {archived}" if archived else "")
    return web.json_response({"ok": True, "cleared": n, "archived": archived})


async def api_paper_cfg(req):
    """读取/保存模拟下单参数。每档: enabled / buy_price / max_tau / amount。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    if req.method == "GET":
        return web.json_response(S.paper_cfg)
    try:
        body = await req.json()
    except Exception:
        return web.json_response({"ok": False, "error": "bad json"}, status=400)
    cfg = {k: dict(v) for k, v in S.paper_cfg.items()}
    for prof in PAPER_PROFILES:
        patch = body.get(prof)
        if not isinstance(patch, dict):
            continue
        cur = dict(cfg.get(prof) or PAPER_DEFAULT[prof])
        cur.update({k: v for k, v in patch.items() if k in PAPER_DEFAULT[prof]})
        c, err = _paper_check(prof, cur)
        if err:
            return web.json_response({"ok": False, "error": err}, status=400)
        cfg[prof] = c
    save_paper_cfg(cfg)
    return web.json_response({"ok": True, "cfg": S.paper_cfg})


async def api_snipe_cfg(req):
    """读取/保存 ≤10¢ 狙击参数（与三档模拟单完全分开）。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    if req.method == "GET":
        return web.json_response(S.snipe_cfg)
    try:
        body = await req.json()
    except Exception:
        return web.json_response({"ok": False, "error": "bad json"}, status=400)
    cfg = dict(S.snipe_cfg)
    cfg.update({k: v for k, v in body.items() if k in SNIPE_DEFAULT})
    c, err = save_snipe_cfg(cfg)
    if err:
        return web.json_response({"ok": False, "error": err}, status=400)
    return web.json_response({"ok": True, "cfg": c})


async def api_snipe_manual(req):
    """手动以固定金额建仓（对应看板红色按钮）。默认强制三维条件；
    ?force=1 时忽略条件但仍需价格在区间内，供人工判断使用。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    now = time.time()
    s0 = int(now // WIN) * WIN
    w = S.win.get(s0)
    if not w or not w.get("up"):
        return web.json_response({"ok": False, "error": "本场盘口还没就绪"}, status=409)
    r = (S.view or {}).get("cur") or {}
    if not r.get("p0") or r.get("up_ask") is None:
        return web.json_response({"ok": False, "error": "本场数据未就绪（缺 Strike 或盘口）"}, status=409)
    cfg = S.snipe_cfg or {}
    spot = (S.view or {}).get("spot")
    ref, _ = get_ref()
    tgt = snipe_target(now, w, r, spot, ref)
    if not tgt:
        return web.json_response({"ok": False, "error": "盘口无卖价"}, status=409)
    if not tgt["in_range"]:
        return web.json_response({"ok": False,
                                  "error": f"卖一 {tgt['ask']:.3f} 不在 "
                                           f"{tgt['lo']:.3f}~{tgt['cap']:.3f} 区间"}, status=409)
    if int(w.get("snipe_cnt") or 0) >= int(cfg.get("per_round") or 1):
        return web.json_response({"ok": False, "error": "本场狙击次数已用满"}, status=409)
    if not tgt["atr"] or tgt["strike"] is None:
        return web.json_response({"ok": False, "error": "ATR 或 Strike 数据不足"}, status=409)
    force = req.query.get("force") in ("1", "true", "yes")
    st = snipe_status(s0, now, w, r, spot, ref)
    warn = None
    if not st["ready"] and not force:
        return web.json_response({"ok": False, "error": "未达标：" + "、".join(st["blocked"])}, status=409)
    if not st["ready"]:
        warn = "手动建仓：当前未达标（" + "、".join(st["blocked"]) + "）"
    remain = max(0.0, (s0 + WIN) - now)
    r_gap = abs(spot - tgt["strike"]) / (tgt["atr"] * math.sqrt(max(remain, 1) / 60.0))
    row = _snipe_open(s0, now, w, r, spot, tgt["side"], tgt["ask"], tgt["atr"],
                      tgt["strike"], r_gap, tgt["score"] or 0.0, tgt["detail"], "manual")
    return web.json_response({"ok": True, "row": row, "warn": warn})


async def api_snipe_clear(req):
    """清空狙击账本；CSV 归档备份。"""
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    n = len(S.snipe)
    S.snipe = []
    _reset_snipe_stats()
    archived = None
    if os.path.exists(SNIPE_CSV):
        archived = f"{SNIPE_CSV}.cleared.{int(time.time())}.bak"
        os.rename(SNIPE_CSV, archived)
    _csv_fields.pop(SNIPE_CSV, None)
    log.info("已清空狙击记录 %d 笔%s", n, f"，归档 {archived}" if archived else "")
    return web.json_response({"ok": True, "cleared": n, "archived": archived})


async def index(req):
    if not _auth(req):
        return web.Response(status=401, text="bad token")
    return web.Response(text=HTML, content_type="text/html")


HTML = r'''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>BTC-test4 · 监控</title><style>
body{background:#0e1116;color:#d6dbe3;font:13px/1.6 -apple-system,"PingFang SC","Microsoft YaHei","Noto Sans CJK SC",ui-monospace,Menlo,Consolas,monospace;margin:12px}
h2{margin:0 0 8px;font-size:16px;color:#e6edf3}h3{margin:16px 0 6px;color:#8aa;font-size:13px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:8px}
.card{background:#161b22;border:1px solid #232a34;border-radius:6px;padding:8px}.k{color:#7d8590;font-size:11px}.v{font-size:17px}
.up{color:#3fb950}.dn{color:#f85149}.warn{color:#d29922}.mut{color:#7d8590}
table{border-collapse:collapse;width:100%}td,th{padding:3px 6px;border-bottom:1px solid #232a34;text-align:right;white-space:nowrap}th{color:#7d8590}
.wrap{overflow-x:auto}canvas{width:100%;height:230px;background:#161b22;border:1px solid #232a34;border-radius:6px}
.tip{color:#7d8590;font-size:12px;margin:2px 0 6px}
.pager{display:flex;align-items:center;gap:6px;flex-wrap:wrap;margin:8px 0}
.pager button{background:#161b22;border:1px solid #30363d;color:#d6dbe3;border-radius:4px;padding:3px 10px;cursor:pointer}
.pager button:hover{border-color:#58a6ff;color:#58a6ff}
.pager button:disabled{opacity:.35;cursor:default;border-color:#232a34;color:#7d8590}
.pager button.on{border-color:#58a6ff;color:#58a6ff}
.pager .info{color:#7d8590;margin-left:4px}
.pager button.danger{border-color:#f85149;color:#f85149;margin-left:auto}
.pager button.danger:hover{background:#3d1214}
.paper-bar{display:flex;align-items:center;gap:10px;flex-wrap:wrap;background:#161b22;border:1px solid #232a34;border-radius:6px;padding:8px 10px;margin:4px 0 8px}
.paper-bar label{color:#7d8590;font-size:12px;display:flex;align-items:center;gap:4px}
.paper-bar input[type=number]{width:72px;background:#0e1116;border:1px solid #30363d;color:#d6dbe3;border-radius:4px;padding:3px 6px}
.paper-bar button{background:#21262d;border:1px solid #30363d;color:#d6dbe3;border-radius:4px;padding:3px 12px;cursor:pointer}
.paper-bar button:hover{border-color:#58a6ff;color:#58a6ff}
.tabs{display:flex;gap:6px;margin:6px 0 8px;border-bottom:1px solid #232a34}
.tabs button{background:transparent;border:1px solid transparent;border-bottom:none;color:#7d8590;border-radius:6px 6px 0 0;padding:5px 14px;cursor:pointer;font-size:13px}
.tabs button:hover{color:#58a6ff}
.tabs button.on{background:#161b22;border-color:#232a34;color:#e6edf3;position:relative;top:1px}
.tabs .cnt{color:#7d8590;font-size:11px;margin-left:4px}
.sstat{background:#161b22;border:1px solid #232a34;border-radius:6px;padding:8px 10px;margin:0 0 8px}
.sstat .hd{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:6px}
.sstat .hd b{font-size:13px}
.sstat .pill{border-radius:10px;padding:1px 9px;font-size:11px;border:1px solid #30363d;color:#7d8590}
.sstat .pill.ready{background:#0d2f1a;border-color:#2ea043;color:#3fb950}
.sstat .pill.wait{background:#2b2410;border-color:#9e6a03;color:#d29922}
.sstat .pill.stop{background:#2b1416;border-color:#8b2c31;color:#f85149}
.sstat .pill.off{opacity:.6}
.sstat .kv{display:flex;gap:14px;flex-wrap:wrap;font-size:12px;color:#7d8590;font-variant-numeric:tabular-nums}
.sstat .kv b{color:#d6dbe3;font-weight:400}
.sstat table{margin-top:4px;width:auto;min-width:60%}
.sstat td,.sstat th{padding:2px 10px 2px 0;font-size:12px;border-bottom:1px solid #1c222b}
.sstat th{font-weight:400}
.sstat .ok{color:#3fb950}.sstat .no{color:#f85149}
/* 狙击雷达：头部一行 + 四张评分卡 */
.radar{background:linear-gradient(180deg,#131b26,#10151c);border:1px solid #26303d;border-radius:8px;padding:10px 12px;margin:0 0 8px}
.radar .r1{display:flex;align-items:center;gap:16px;flex-wrap:wrap}
.radar .lock{font-size:16px;color:#e6edf3;font-weight:600;display:flex;align-items:center;gap:6px}
.radar .lock .up{color:#3fb950}.radar .lock .dn{color:#f85149}
.radar .lock .px{font-size:12px;color:#7d8590;font-weight:400}
.radar .r2{color:#7d8590;font-size:12px;margin-top:2px;font-variant-numeric:tabular-nums}
.radar .r2 b{color:#9fb0c3;font-weight:400}
.radar .grow{flex:1}
.radar .inp{display:flex;flex-direction:column;gap:2px;font-size:11px;color:#7d8590}
.radar .inp input{width:78px;background:#0b1016;border:1px solid #30363d;border-radius:4px;padding:3px 6px;font-size:13px;font-variant-numeric:tabular-nums}
.radar .inp.a input{color:#d29922;border-color:#5c4413}
.radar .inp.b input{color:#a371f7;border-color:#3d2d5c}
.radar .auto{display:flex;align-items:center;gap:5px;font-size:12px;color:#9fb0c3}
.radar .go{background:#8b2c31;border:1px solid #b62324;color:#fff;border-radius:6px;padding:8px 16px;font-size:13px;cursor:pointer;font-weight:600;white-space:nowrap}
.radar .go:hover{background:#a83236}
.radar .go:disabled{background:#2b1416;border-color:#4a2224;color:#7d8590;cursor:not-allowed}
.radar .go.armed{background:#b62324;box-shadow:0 0 0 2px rgba(182,35,36,.25)}
.radar .note{font-size:11px;color:#d29922;margin-top:4px}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:8px;margin:0 0 8px}
.mcard{background:linear-gradient(180deg,#161d27,#121821);border:1px solid #26303d;border-radius:8px;padding:8px 10px}
.mcard .t{font-size:11px;color:#7d8590;display:flex;justify-content:space-between;gap:8px}
.mcard .v{font-size:17px;margin:2px 0 4px;font-variant-numeric:tabular-nums}
.mcard .bar{height:5px;background:#1d2530;border-radius:3px;overflow:hidden}
.mcard .bar i{display:block;height:100%;background:linear-gradient(90deg,#d29922,#f0883e);border-radius:3px}
.mcard .f{font-size:10px;color:#7d8590;margin-top:4px;font-variant-numeric:tabular-nums}
.topline{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin:0 0 8px}
.topline h2{margin:0}
.host-meters{display:flex;gap:8px;flex-wrap:wrap}
.meter{display:flex;align-items:center;gap:8px;background:linear-gradient(180deg,#1a212b,#141a22);border:1px solid #2a3340;border-radius:12px;padding:5px 12px 5px 5px;min-width:118px;box-shadow:inset 0 1px 0 rgba(255,255,255,.03)}
.ring{--p:0;--c:#58a6ff;width:38px;height:38px;border-radius:50%;background:conic-gradient(var(--c) calc(var(--p) * 1%), #232a34 0);display:grid;place-items:center;position:relative;flex:0 0 auto}
.ring:after{content:"";width:28px;height:28px;border-radius:50%;background:#12161c;border:1px solid #1f2630;position:absolute}
.ring span{position:relative;z-index:1;font-size:9px;color:#e6edf3;font-variant-numeric:tabular-nums;letter-spacing:-.02em}
.meter .lab{font-size:10px;color:#7d8590;line-height:1.15}
.meter .val{font-size:12px;color:#d6dbe3;font-variant-numeric:tabular-nums;line-height:1.2}
.meter .sub{font-size:10px;color:#7d8590;line-height:1.15}
#feeds{margin-bottom:2px}
#netline{color:#7d8590;font-size:12px;margin:0 0 6px;font-variant-numeric:tabular-nums}</style></head><body>
<div class="topline"><h2>BTC-test4 · 实时监控</h2><div id="host" class="host-meters"></div></div>
<div id="netline"></div>
<div id="feeds"></div>
<h3>当前场次</h3><div id="top" class="grid"></div>
<h3>价格走势（近7分钟）</h3><div class="tip">竖线 = 场次边界；绿色虚线 = 本场开盘基准价（收盘均价高于它则“涨”）</div><canvas id="c1"></canvas>
<h3>本场盘口</h3><div class="tip">绿=P(涨)　红=涨卖　黄=涨买　青=跌买</div><canvas id="c2"></canvas>
<h3>下一场预判</h3><div id="nxt"></div>
<h3>模拟下单</h3>
<div class="tabs" id="paperTabs"></div>
<div id="tabPred">
<div id="paperState"></div>
<div class="tip">三档独立，同一场每档最多一笔。<b>开盘前</b>：预判后到开盘，模型强度 |p−0.5| ≥ 设定值且预判方向卖一 ≤ 卖价上限即按卖一买入（只看模型强度，卖价只防买贵）。<b>强 / 普</b>：开盘后设定秒数内，预判方向卖一 ≤ 买价上限才买。份额 = 金额 / 买价；盈亏：中 +金额×(1/买价−1)，错 −金额；差值 = BTC − 开盘基准价 P0。</div>
<div class="paper-bar" id="paperBar"></div>
<div id="paperStats" class="tip"></div>
<canvas id="c3"></canvas>
<div class="tip">收益曲线：按结算顺序累计每笔模拟单盈亏（U）。绿线=合计，橙=开盘前，蓝=强信号，紫=普通信号。</div>
<div id="paperPager" class="pager"></div>
<div class="wrap" id="paperTbl"></div>
</div>
<div id="tabSnipe" style="display:none">
<div id="snipeState"></div>
<div class="tip"><b>≤10¢ 绝地反转狙击</b>（独立账本，与上面三档分开统计）。某方向被砸到建仓价上限以下，且同时满足：<b>时间窗</b>、<b>ATR 标准化落差</b> R_gap ≤ 上限、<b>翻转评分</b> ≥ 门槛（5 秒订单流反转 + 极值反弹 + 预言机缓冲垫）时按卖一建仓。<b>两段式止盈</b>：买一达到建仓价的倍数且不低于止盈最低价时，卖出设定比例抽回本金（Free-Roll），余仓持有到结算，正确按 1U 兑付。</div>
<div class="paper-bar" id="snipeBar"></div>
<div id="snipeStats" class="tip"></div>
<canvas id="c4"></canvas>
<div class="tip">狙击收益曲线：每笔的总盈亏（落袋现金 + 结算余额 − 投入）累计。</div>
<div id="snipePager" class="pager"></div>
<div class="wrap" id="snipeTbl"></div>
</div>
<h3>历史场次</h3><div id="stats"></div><div id="pager" class="pager"></div><div class="wrap" id="tbl"></div>
<script>
const Q=location.search,$=id=>document.getElementById(id),f=(x,d=2)=>x==null?'-':Number(x).toFixed(d);
const ud=x=>({Up:'涨',Down:'跌'}[x]||x||'-');
const REF={'chainlink':'Chainlink','binance*':'币安(代理，未连上Chainlink)'};
const LAB={'calc':'自算','twap':'官方TWAP','polymarket':'盘口钉死'};
const AUTH=a=>a=='ok'?'已认证':a=='no-creds'?'未配置凭据':a=='deriving'?'正在生成凭据':a=='derive-failed'?'凭据生成失败':a=='authenticating'?'认证中':(a||'').startsWith('FAILED')?'认证失败':a;
const card=(k,v,c='',tip='')=>`<div class="card" title="${tip}"><div class="k">${k}</div><div class="v ${c}">${v}</div></div>`;
const hm=s=>new Date(s*1000).toISOString().slice(11,16)+' UTC';
const age=a=>a==null?'<span class=dn>无数据</span>':(a<5?`<span class=up>${a.toFixed(1)}秒</span>`:`<span class=warn>${a.toFixed(0)}秒</span>`);
const PAGE_SIZE=20; let page=1; let roundsPage={rows:[],page:1,pages:1,total:0,size:20};
// 只在内容变化时写 DOM：每秒刷一次时，表格和分页条多数轮次其实是同一个 HTML
const setH=(id,h)=>{const e=$(id);if(e&&e._h!==h){e._h=h;e.innerHTML=h}};
const PAPER_PAGE_SIZE=20; let paperPage=1;
const SIGT={pre:'前',strong:'强',weak:'普'}, SIGN={pre:'开盘前买入',strong:'强信号·开盘后',weak:'普通信号·开盘后'}, SIGC={pre:'#f0883e',strong:'#58a6ff',weak:'#a371f7'};
// 配置保存结果写在配置栏里，不用弹窗；4 秒后自动消失
let paperHint='', paperHintC='#7d8590', paperHintTimer=null;
function showHint(msg,col='#7d8590'){
paperHint=msg; paperHintC=col;
if(paperHintTimer) clearTimeout(paperHintTimer);
paperHintTimer=setTimeout(()=>{paperHint='';const e=$('paperHint');if(e){e.textContent='';e.style.color='#7d8590'}},4000);
const e=$('paperHint'); if(e){e.textContent=msg; e.style.color=col}}
function plot(cv,lines,o={}){const dpr=devicePixelRatio||1,W=cv.clientWidth,H=cv.clientHeight;cv.width=W*dpr;cv.height=H*dpr;
const g=cv.getContext('2d');g.scale(dpr,dpr);let xs=[],ys=[];lines.forEach(l=>l.d.forEach(p=>{if(p[1]!=null){xs.push(p[0]);ys.push(p[1])}}));
(o.h||[]).forEach(h=>ys.push(h.y));if(!xs.length)return;
let x0=o.x0??Math.min(...xs),x1=o.x1??Math.max(...xs),y0=o.y0??Math.min(...ys),y1=o.y1??Math.max(...ys);if(y1-y0<1e-9){y1+=1;y0-=1}
if(o.y0==null){const p=(y1-y0)*.08;y0-=p;y1+=p}const X=x=>44+(x-x0)/(x1-x0||1)*(W-52),Y=y=>H-16-(y-y0)/(y1-y0)*(H-28);
g.font='10px monospace';g.lineWidth=1;for(let i=0;i<=4;i++){const y=y0+(y1-y0)*i/4;g.strokeStyle='#232a34';g.beginPath();g.moveTo(44,Y(y));g.lineTo(W-8,Y(y));g.stroke();g.fillStyle='#7d8590';g.fillText(y.toFixed(o.dec??1),2,Y(y)+3)}
(o.v||[]).forEach(v=>{if(v<x0||v>x1)return;g.strokeStyle='#555';g.beginPath();g.moveTo(X(v),10);g.lineTo(X(v),H-16);g.stroke()});
(o.h||[]).forEach(h=>{g.strokeStyle=h.c;g.setLineDash([4,3]);g.beginPath();g.moveTo(44,Y(h.y));g.lineTo(W-8,Y(h.y));g.stroke();g.setLineDash([])});
lines.forEach(l=>{g.strokeStyle=l.c;g.lineWidth=1.5;g.beginPath();let on=false;l.d.forEach(p=>{if(p[1]==null){on=false;return}const x=X(p[0]),y=Y(p[1]);if(on)g.lineTo(x,y);else{g.moveTo(x,y);on=true}});g.stroke()});
let lx=48;g.font='11px sans-serif';lines.forEach(l=>{g.fillStyle=l.c;const label=l.v==null?l.n:`${l.n} ${l.v}`;g.fillText(label,lx,9);lx+=g.measureText(label).width+18})}
// 曲线数据没变时不重绘 canvas（每秒一次全量重绘是纯浪费）
function plotCached(cv,lines,o={}){const last=l=>l.d.length?l.d[l.d.length-1]:0;
const sig=JSON.stringify([lines.map(l=>[l.n,l.v,l.d.length,last(l)]),o.h||[],cv.clientWidth]);
if(cv._sig===sig) return; cv._sig=sig; plot(cv,lines,o)}
function clearPlot(cv){if(!cv||!cv._sig)return;cv._sig=null;const g=cv.getContext('2d');g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,cv.width,cv.height)}
function pages(){return Math.max(1, roundsPage.pages||1)}
function gotoPage(p){page=Math.min(Math.max(1,p), pages()); tick()}
function renderRounds(){
const tp=pages();
if(page>tp) page=tp;
const total=roundsPage.total||0, rows=(roundsPage.rows||[]);
let t='<table><tr><th>场次(UTC)</th><th>预判</th><th>预判概率</th><th>结果</th><th>命中</th><th>预判时卖价 涨/跌</th><th>结果来源</th><th>开盘基准(自算)</th><th>收盘均价(自算)</th><th>开盘基准(官方)</th><th>收盘均价(官方)</th></tr>';
rows.forEach(r=>{t+=`<tr><td>${r.time_utc}</td><td>${ud(r.pred)}</td><td>${f(r.p_pred,3)}</td><td>${ud(r.outcome)}</td><td class="${r.hit?'up':'dn'}">${r.hit?'✔ 中':'✘ 错'}</td><td>${f(r.up_ask0,2)} / ${f(r.dn_ask0,2)}</td><td>${LAB[r.label]||r.label}</td><td>${f(r.p0_calc)}</td><td>${f(r.c_calc)}</td><td>${f(r.p0_tw)}</td><td>${f(r.c_tw)}</td></tr>`});
setH('tbl',t+'</table>');
let nums=''; const from=Math.max(1,page-2), to=Math.min(tp, page+2);
for(let i=from;i<=to;i++) nums+=`<button class="${i===page?'on':''}" onclick="gotoPage(${i})">${i}</button>`;
setH('pager',`<button ${page<=1?'disabled':''} onclick="gotoPage(1)">首页</button>
<button ${page<=1?'disabled':''} onclick="gotoPage(${page-1})">上一页</button>${nums}
<button ${page>=tp?'disabled':''} onclick="gotoPage(${page+1})">下一页</button>
<button ${page>=tp?'disabled':''} onclick="gotoPage(${tp})">末页</button>
<span class="info">第 ${page}/${tp} 页，每页 ${roundsPage.size||PAGE_SIZE} 场，共 ${total} 场</span>
<button onclick="exportData()">导出数据包</button>
<button class="danger" onclick="clearRounds()">清空重置</button>`)}
function exportData(){window.open('/api/data/export'+Q,'_blank')}
async function clearRounds(){
if(!confirm('确定清空历史场次？命中率会归零。\n当前 rounds_v2.csv 会归档为 .cleared 备份，不会直接删除。\nticks/outcomes 分析文件保留。')) return;
try{
const r=await fetch('/api/rounds/clear'+Q,{method:'POST'});
if(!r.ok){alert(r.status==401?'口令错误':'清空失败 HTTP '+r.status);return}
const j=await r.json();
page=1;roundsPage={rows:[],page:1,pages:1,total:0,size:PAGE_SIZE};renderRounds();
alert('已清空 '+j.cleared+' 场'+(j.archived?'\n已归档: '+j.archived:''));
tick();
}catch(e){alert('清空失败: '+e)}}
const meterColor=p=>p==null?'#58a6ff':(p<55?'#3fb950':(p<80?'#d29922':'#f85149'));
const meter=(lab,pct,val,sub='')=>{const p=pct==null?0:Math.max(0,Math.min(100,pct));const shown=pct==null?'--':Math.round(p);
return `<div class="meter" title="${lab}"><div class="ring" style="--p:${p};--c:${meterColor(pct)}"><span>${shown}</span></div><div><div class="lab">${lab}</div><div class="val">${val}</div>${sub?`<div class="sub">${sub}</div>`:''}</div></div>`};
function fmtUp(sec){sec=Math.max(0,Math.floor(Number(sec)||0));const d=Math.floor(sec/86400),h=Math.floor(sec%86400/3600),m=Math.floor(sec%3600/60),s=sec%60;
if(d>0)return `${d}天 ${h}时${String(m).padStart(2,'0')}分`;
if(h>0)return `${h}时${String(m).padStart(2,'0')}分${String(s).padStart(2,'0')}秒`;
return `${m}分${String(s).padStart(2,'0')}秒`}
function fmtBytes(n){n=Number(n);if(!isFinite(n)||n<0)return'-';
const u=['B','KB','MB','GB','TB'];let i=0;while(n>=1024&&i<u.length-1){n/=1024;i++}
return(i===0?Math.round(n):n.toFixed(n>=100?0:n>=10?1:2))+u[i]}
function fmtRate(bps){return bps==null?'-':fmtBytes(bps)+'/s'}
function drawHost(H){H=H||{};
const cpu=H.cpu, memPct=(H.mem_used_mb!=null&&H.mem_total_mb)?(100*H.mem_used_mb/H.mem_total_mb):null;
const cpuVal=cpu==null?'采样中…':`${Number(cpu).toFixed(1)}%`;
const memVal=(H.mem_used_mb!=null&&H.mem_total_mb!=null)?`${H.mem_used_mb} / ${H.mem_total_mb} MB`:'-';
const procVal=H.proc_mb==null?'-':`${H.proc_mb} MB`;
const up=H.uptime_sec, upRing=up==null?0:Math.min(100,(up%(24*3600))/(24*3600)*100);
const upSub=H.started?('启动 '+new Date(H.started*1000).toISOString().slice(5,16).replace('T',' ')+' UTC'):'本次进程';
$('host').innerHTML=meter('本进程 CPU',H.proc_cpu,`${H.proc_cpu==null?'--':H.proc_cpu.toFixed(1)+'%'}`,`RSS ${procVal}`)+meter('整机 CPU',cpu,cpuVal,'全部进程')+meter('内存',memPct,memVal,'已用 / 总量')+meter('已运行',upRing,up==null?'-':fmtUp(up),upSub);
const hasNet=H.net_rx!=null||H.net_tx!=null;
$('netline').innerHTML=hasNet?`流量 ↓${fmtRate(H.net_rx_bps)} ↑${fmtRate(H.net_tx_bps)}　累计 ↓${fmtBytes(H.net_rx)} ↑${fmtBytes(H.net_tx)}`:'';}
function draw(d){const c=d.cur,F=d.feeds||{};
drawHost(d.host);
$('feeds').innerHTML=`数据延迟：币安 ${age(F.bn)} ｜ 欧易 ${age(F.okx)} ｜ Chainlink现货 ${age(F.cl)} ｜ Chainlink 60秒均价 ${age(F.tw)} ｜ Polymarket盘口 ${age(F.pm)} ｜ 凭据状态：<b>${AUTH(d.auth)}</b> ｜ 参考价来源：<b>${REF[d.ref]||d.ref}</b>`;
let h=card('参考价',f(d.spot),'','用于结算判断的价格（Chainlink，未连上时用币安代理）')
+card('币安 / 欧易',f(d.bn,1)+' / '+f(d.okx,1),'','两家交易所的最新成交价')
+card('波动率 σ',f(d.sigma,2)+' 美元/√秒','','30秒尺度的价格波动，用于计算不确定度');
if(c){h+=card('本场剩余',Math.max(0,c.end-d.now).toFixed(0)+' 秒')
+card('开盘基准价',f(c.p0),'','开盘前60秒的Chainlink均价，开盘后固定不变。收盘均价≥它则判“涨”')
+card('预计收盘均价',f(c.c)+` (${c.mu>=0?'+':''}${f(c.mu,1)})`,c.mu>=0?'up':'dn','最后60秒的预计均价；括号内为与开盘基准价的差（美元）')
+card('收盘不确定度','± $'+f(c.sd,1),'','预计收盘均价的标准差，越接近收盘越小')
+card('模型：涨的概率',f(c.p,3),c.p>=.5?'up':'dn','模型估计的“涨”概率')
+card('“涨” 买一 / 卖一',f(c.up_bid,2)+' / '+f(c.up_ask,2),'','Polymarket上“涨”份额的最高买价 / 最低卖价')
+card('“跌” 买一 / 卖一',f(c.dn_bid,2)+' / '+f(c.dn_ask,2),'','Polymarket上“跌”份额的最高买价 / 最低卖价')
+card('模型−卖价：涨 / 跌',f(c.edge_up,3)+' / '+f(c.edge_dn,3),'mut','模型概率 减 盘口卖价，仅供参考。回测显示按此差值买入是亏的（差值大通常是盘口对、模型错），不作为买入依据')
+card('本场预判',c.pred?`${ud(c.pred)} (${f(c.p_pred,3)})`:'无',c.pred=='Up'?'up':(c.pred=='Down'?'dn':''),'开盘前20秒做出的预判')}
setH('top',h);
const bounds=[];for(let t=Math.ceil((d.now-420)/300)*300;t<=d.now;t+=300)bounds.push(t);
const L=(i,n,col,v)=>({n,c:col,v,d:d.chart.map(r=>[r[0],r[i]])});
plotCached($('c1'),[L(1,'参考价','#e6edf3',f(d.spot)),L(2,'币安','#58a6ff',f(d.bn,1)),L(3,'欧易','#a371f7',f(d.okx,1)),L(4,'官方60秒均价','#f0883e',f(d.chart&&d.chart.length?d.chart[d.chart.length-1][4]:null))],{v:bounds,h:c?[{y:c.p0,c:'#3fb950'}]:[],dec:0});
const T=d.ticks||[];plotCached($('c2'),[
{n:'P(涨)',v:c?f(c.p,3):'-',c:'#3fb950',d:T.map(r=>[r[0],r[1]])},
{n:'涨卖',v:c?f(c.up_ask,2):'-',c:'#f85149',d:T.map(r=>[r[0],r[3]])},
{n:'涨买',v:c?f(c.up_bid,2):'-',c:'#d29922',d:T.map(r=>[r[0],r[2]])},
{n:'跌买',v:c?f(c.dn_bid,2):'-',c:'#39c5cf',d:T.map(r=>[r[0],r[4]])}
],{x0:0,x1:300,y0:0,y1:1,v:[240],h:[{y:.5,c:'#555'}],dec:2});
const n=d.nxt;setH('nxt',n?`场次 ${hm(n.start)}：`+(n.pred?`<b class="${n.pred=='Up'?'up':'dn'}">${ud(n.pred)}</b>，概率 ${f(n.p,3)} ${n.conf?'（信号较强）':'（信号弱）'}`:`将在开盘前20秒给出预判（还有 ${Math.max(0,n.start-d.now).toFixed(0)} 秒）`):'');
const st=d.stats||{};const shownTip=(st.shown!=null&&st.n>st.shown)?`　<span class=mut>（表内最近 ${st.shown} 场）</span>`:'';
setH('stats',`共 ${st.n||0} 场，命中率 ${st.acc==null?'-':(st.acc*100).toFixed(1)+'%'} ｜ 信号较强 ${st.cn||0} 场，命中率 ${st.cacc==null?'-':(st.cacc*100).toFixed(1)+'%'}　<span class=mut>（开盘前预判长期接近50%属正常，样本需几百场才有意义）</span>${shownTip}`);
roundsPage=d.rounds||roundsPage; page=roundsPage.page||page;
renderRounds();
renderPaper(d);
renderSnipe(d);
renderPaperState(d);
renderSnipeState(d)}
function renderPaper(d){
const cfg=d.paper_cfg||{};
const editing=document.activeElement&&document.activeElement.closest&&document.activeElement.closest('#paperBar');
if(!editing){
let b='';
['pre','strong','weak'].forEach((p)=>{const c=cfg[p]||{};
b+=`<span class="pg" style="display:flex;gap:8px;flex-wrap:wrap;align-items:center;padding:4px 8px;border:1px solid #30363d;border-radius:6px"><b style="color:${SIGC[p]}">${SIGN[p]}</b>
<label><input type="checkbox" id="en_${p}" ${c.enabled?'checked':''}> 启用</label>`
+(p=='pre'?`<label>强度≥ <input type="number" id="ms_${p}" min="0" max="0.49" step="0.01" value="${c.min_strength??0.08}"></label>`:'')
+`<label>${p=='pre'?'卖价上限':'买价上限'} <input type="number" id="bp_${p}" min="0.01" max="0.99" step="0.01" value="${c.buy_price??0.45}"></label>
<label>金额(U) <input type="number" id="am_${p}" min="0.1" max="10000" step="0.1" value="${c.amount??5}"></label>`
+(p=='pre'?'':`<label>窗口(秒) <input type="number" id="mt_${p}" min="5" max="300" step="1" value="${c.max_tau??150}"></label>`)+`</span>`});
b+=`<button onclick="savePaper()">保存</button><span class="mut" id="paperHint"></span>`;
$('paperBar').innerHTML=b;
const he=$('paperHint'); if(he&&paperHint){he.textContent=paperHint;he.style.color=paperHintC}}
const ps=d.paper_stats||{};
const pct=x=>x==null?'-':(x*100).toFixed(1)+'%';
const sg=p=>{const s=(ps.by_sig||{})[p]||{};return `${SIGT[p]} ${s.trades||0}笔/${s.settled||0}结算 胜率 ${pct(s.win_rate)} 盈亏 ${s.pnl==null?'-':((s.pnl>=0?'+':'')+Number(s.pnl).toFixed(3))}U`};
const cp=d.cur&&d.cur.paper;
setH('paperStats',`合计 ${ps.n||0} 笔｜结算 ${ps.settled||0}｜胜率 ${pct(ps.win_rate)}｜盈亏 ${ps.pnl==null?'-':((ps.pnl>=0?'+':'')+Number(ps.pnl).toFixed(3))} U　｜　${sg('pre')}　｜　${sg('strong')}　｜　${sg('weak')}`+(cp?`　｜　本场最近成交[${SIGT[cp.sig]||cp.sig}]：${ud(cp.side)} @ ${f(cp.buy_price,3)} × ${f(cp.amount,2)}U，相对开盘 ${cp.tau>0?'+':''}${f(cp.tau,0)}s`:''));
// 收益曲线：合计 + 三档分线（值域强制包含 0，全亏时也能正常显示）
const CV=d.paper_curve||[];
if(CV.length){const lz=CV[CV.length-1];
const vs=CV.flatMap(r=>[r[1],r[2],r[3],r[4]]);
const lo=Math.min(0,...vs), hi=Math.max(0,...vs), pad=Math.max(0.5,(hi-lo)*0.08);
plotCached($('c3'),[
{n:'合计',v:(lz[1]>=0?'+':'')+f(lz[1],3)+'U',c:'#3fb950',d:CV.map(r=>[r[0],r[1]])},
{n:'前',v:(lz[2]>=0?'+':'')+f(lz[2],3),c:SIGC.pre,d:CV.map(r=>[r[0],r[2]])},
{n:'强',v:(lz[3]>=0?'+':'')+f(lz[3],3),c:SIGC.strong,d:CV.map(r=>[r[0],r[3]])},
{n:'普',v:(lz[4]>=0?'+':'')+f(lz[4],3),c:SIGC.weak,d:CV.map(r=>[r[0],r[4]])}
],{x0:1,x1:lz[0],y0:lo-pad,y1:hi+pad,h:[{y:0,c:'#555'}],dec:1})}
else{clearPlot($('c3'))}
const pp=d.paper||{rows:[],page:1,pages:1,total:0,size:PAPER_PAGE_SIZE};
let t='<table><tr><th>买入时间(UTC)</th><th>信号</th><th>方向</th><th>买入价</th><th>金额(U)</th><th>份额</th><th>相对开盘(秒)</th><th>BTC</th><th>差值($)</th><th>差值(bps)</th><th>预判概率</th><th>结果</th><th>命中</th><th>盈亏(U)</th></tr>';
(pp.rows||[]).slice().reverse().forEach(r=>{const hit=r.settled? (r.hit?'✔ 中':'✘ 错'):'待结';
const hc=r.settled?(r.hit?'up':'dn'):'mut';
const pc=r.settled?(r.pnl>=0?'up':'dn'):'mut';
const sig=r.sig||'strong';
const tag=`<span style="color:${SIGC[sig]||'#7d8590'}">${SIGT[sig]||sig}</span>`;
t+=`<tr><td>${r.time_utc||'-'}</td><td>${tag}</td><td class="${r.side=='Up'?'up':'dn'}">${ud(r.side)}</td><td>${f(r.buy_price,3)}</td><td>${f(r.amount,2)}</td><td>${f(r.shares,3)}</td><td>${r.tau>0?'+':''}${f(r.tau,0)}</td><td>${f(r.btc)}</td><td>${r.btc_diff==null?'-':((r.btc_diff>=0?'+':'')+f(r.btc_diff))}</td><td>${f(r.btc_diff_bps,1)}</td><td>${f(r.p_pred,3)}</td><td>${ud(r.outcome)}</td><td class="${hc}">${hit}</td><td class="${pc}">${r.settled?(r.pnl>=0?'+':'')+f(r.pnl,3):'-'}</td></tr>`});
setH('paperTbl',t+'</table>');const tp=pp.pages||1, pg=pp.page||1;
let nums=''; const from=Math.max(1,pg-2), to=Math.min(tp,pg+2);
for(let i=from;i<=to;i++) nums+=`<button class="${i===pg?'on':''}" onclick="gotoPaper(${i})">${i}</button>`;
setH('paperPager',`<button ${pg<=1?'disabled':''} onclick="gotoPaper(1)">首页</button>
<button ${pg<=1?'disabled':''} onclick="gotoPaper(${pg-1})">上一页</button>${nums}
<button ${pg>=tp?'disabled':''} onclick="gotoPaper(${pg+1})">下一页</button>
<button ${pg>=tp?'disabled':''} onclick="gotoPaper(${tp})">末页</button>
<span class="info">第 ${pg}/${tp} 页，每页 ${pp.size||PAPER_PAGE_SIZE} 笔，共 ${pp.total||0} 笔</span>
<button class="danger" onclick="clearPaper()">清空</button>`)}
function gotoPaper(p){paperPage=Math.max(1,p||1);tick()}

// ---------------------------------------------------------------- ≤10¢ 狙击 tab
const SNIPE_PAGE_SIZE=20; let snipePage=1, snipeTab=false;
function switchTab(s){snipeTab=s;
$('tabPred').style.display=s?'none':'';
$('tabSnipe').style.display=s?'':'none';
renderTabs();
if(s){tick()}}
function renderTabs(){
const ps=d_lastSnipe, pp=d_lastPaper;
setH('paperTabs',`<button class="${snipeTab?'':'on'}" onclick="switchTab(0)">预判策略（前/强/普）<span class="cnt">${pp||0} 笔</span></button>
<button class="${snipeTab?'on':''}" onclick="switchTab(1)">≤10¢ 绝地反转狙击<span class="cnt">${ps||0} 笔</span></button>`)}
let d_lastPaper=0, d_lastSnipe=0;
function renderSnipe(d){
const cfg=d.snipe_cfg||{};
const editing=document.activeElement&&document.activeElement.closest&&document.activeElement.closest('#snipeBar');
if(!editing){
const I=(id,lab,val,step,min,max,tip='')=>`<label title="${tip}">${lab} <input type="number" id="${id}" step="${step}" min="${min}" max="${max}" value="${val}"></label>`;
setH('snipeBar',`<label><input type="checkbox" id="sn_en" ${cfg.enabled?'checked':''} onchange="$('sn_auto').checked&&tick()"> 启用</label>`
+I('sn_entry_min','建仓价下限',cfg.min_entry??0.03,0.005,0.005,0.99,'卖一低于此价说明盘口已基本判定结果，不接飞刀')
+`<span class="mut" style="font-size:11px">上限与评分在雷达头部调节</span>`
+I('sn_bet','单笔(U)',cfg.bet??5,0.5,0.1,10000)
+I('sn_tmin','起(秒)',cfg.tau_min??60,5,0,300,'相对开盘秒下限（= 剩余时间上限）')
+I('sn_tmax','止(秒)',cfg.tau_max??230,5,0,300,'相对开盘秒上限（= 剩余时间下限）')
+I('sn_rgap','R_gap≤',cfg.r_gap_max??1.65,0.05,0.2,10,'ATR 标准化落差上限')
+I('sn_mult','止盈倍数',cfg.tp_mult??2.5,0.1,1.05,20)
+I('sn_tpmin','止盈最低价',cfg.tp_min??0.18,0.01,0.01,0.99)
+I('sn_frac','止盈比例',cfg.tp_frac??0.5,0.05,0.05,1)
+I('sn_per','每场次数',cfg.per_round??1,1,1,10)
+`<button onclick="saveSnipe()">保存</button><span class="mut" id="snipeHint"></span>`)};
const ss=d.snipe_stats||{};
const pct=x=>x==null?'-':(x*100).toFixed(1)+'%';
const U=x=>x==null?'-':((x>=0?'+':'')+Number(x).toFixed(3));
setH('snipeStats',`狙击 ${ss.trades||0} 笔｜结算 ${ss.settled||0}｜命中 ${pct(ss.win_rate)}｜半仓止盈 ${ss.tp_hits||0} 次(${pct(ss.tp_rate)})｜已落袋 ${f(ss.cash,3)} U｜总盈亏 <b class="${(ss.pnl||0)>=0?'up':'dn'}">${U(ss.pnl)} U</b>｜均价 ${f(ss.avg_entry,3)}`);
const CV=d.snipe_curve||[];
if(CV.length){const lz=CV[CV.length-1];
const vs=CV.map(r=>r[1]); const lo=Math.min(0,...vs), hi=Math.max(0,...vs), pad=Math.max(0.5,(hi-lo)*0.08);
plotCached($('c4'),[{n:'狙击累计',v:(lz[1]>=0?'+':'')+f(lz[1],3)+'U',c:'#f0883e',d:CV.map(r=>[r[0],r[1]])}],
{x0:1,x1:lz[0],y0:lo-pad,y1:hi+pad,h:[{y:0,c:'#555'}],dec:1})}
else{clearPlot($('c4'))}
const sp=d.snipe||{rows:[],page:1,pages:1,total:0,size:SNIPE_PAGE_SIZE};
let t='<table><tr><th>建仓时间(UTC)</th><th>方向</th><th>建仓价</th><th>份额</th><th>投入(U)</th><th>相对开盘(秒)</th><th>剩余(秒)</th><th>BTC</th><th>Strike</th><th>ATR</th><th>R_gap</th><th>评分</th><th>流/反弹/缓冲</th><th>止盈线</th><th>止盈</th><th>落袋(U)</th><th>状态</th><th>结果</th><th>结算值</th><th>盈亏(U)</th></tr>';
(sp.rows||[]).slice().reverse().forEach(r=>{
const stg={HOLDING:'持仓',FREEROLL:'零风险',CLOSED:'已平',WON:'命中',WON_FULL:'止盈+命中',LOST:'未中',FREEROLL_LOST:'保本/小亏'}[r.stage]||r.stage||'-';
const sc=(r.score??0)>=62?'up':(r.score??0)>=45?'warn':'mut';
const tp=r.tp_hit?`<span class="up">${f(r.tp_bid,2)}@${f(r.tp_tau,0)}s</span>`:'-';
t+=`<tr><td>${r.time_utc||'-'}</td><td class="${r.side=='Up'?'up':'dn'}">${ud(r.side)}</td><td>${f(r.entry,3)}</td><td>${f(r.shares,3)}</td><td>${f(r.amount,2)}</td><td>${f(r.tau,0)}</td><td>${f(r.remain,0)}</td><td>${f(r.spot)}</td><td>${f(r.strike)}</td><td>${f(r.atr,1)}</td><td>${f(r.r_gap,2)}</td><td class="${sc}">${f(r.score,1)}</td><td class="mut">${f(r.s_flow,0)}/${f(r.s_bounce,0)}/${f(r.s_gap,0)}</td><td>${f(r.tp_target,3)}</td><td>${tp}</td><td>${r.tp_hit?f(r.cash1,3):'-'}</td><td>${stg}</td><td>${ud(r.outcome)}</td><td>${r.settled?f(r.settle_value,3):'-'}</td><td class="${r.settled?((r.pnl>=0)?'up':'dn'):'mut'}">${r.settled?U(r.pnl):'-'}</td></tr>`});
setH('snipeTbl',t+'</table>');
const tp2=sp.pages||1, pg2=sp.page||1;
let n2=''; const f2=Math.max(1,pg2-2), t2=Math.min(tp2,pg2+2);
for(let i=f2;i<=t2;i++) n2+=`<button class="${i===pg2?'on':''}" onclick="gotoSnipe(${i})">${i}</button>`;
setH('snipePager',`<button ${pg2<=1?'disabled':''} onclick="gotoSnipe(1)">首页</button>
<button ${pg2<=1?'disabled':''} onclick="gotoSnipe(${pg2-1})">上一页</button>${n2}
<button ${pg2>=tp2?'disabled':''} onclick="gotoSnipe(${pg2+1})">下一页</button>
<button ${pg2>=tp2?'disabled':''} onclick="gotoSnipe(${tp2})">末页</button>
<span class="info">第 ${pg2}/${tp2} 页，每页 ${sp.size||SNIPE_PAGE_SIZE} 笔，共 ${sp.total||0} 笔</span>
<button class="danger" onclick="clearSnipe()">清空</button>`);
d_lastSnipe=ss.trades||0; d_lastPaper=(d.paper_stats||{}).n||0;
renderTabs()}
function gotoSnipe(p){snipePage=Math.max(1,p||1);tick()}
function snipeHintShow(msg,col){const e=$('snipeHint'); if(e){e.textContent=msg; e.style.color=col||'#7d8590'}}
async function saveSnipe(){
const g=id=>Number($(id).value);
const body={enabled:$('sn_en').checked,min_entry:g('sn_entry_min'),bet:g('sn_bet'),
tau_min:g('sn_tmin'),tau_max:g('sn_tmax'),r_gap_max:g('sn_rgap'),tp_mult:g('sn_mult'),
tp_min:g('sn_tpmin'),tp_frac:g('sn_frac'),per_round:g('sn_per')};
try{const r=await fetch('/api/snipe/cfg'+Q,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
const j=await r.json();
if(!r.ok||!j.ok){snipeHintShow(j.error||('保存失败 '+r.status),'#f85149');return}
snipeHintShow('已保存','#3fb950');tick()}
catch(e){snipeHintShow('保存失败: '+e,'#f85149')}}
async function clearSnipe(){
if(!confirm('确定清空狙击账本？\n统计会归零，snipe_trades.csv 会归档为 .cleared 备份。\n预判策略的三档记录不受影响。')) return;
try{const r=await fetch('/api/snipe/clear'+Q,{method:'POST'});
if(!r.ok){alert(r.status==401?'口令错误':'清空失败 HTTP '+r.status);return}
const j=await r.json(); snipePage=1;
alert('已清空 '+j.cleared+' 笔'+(j.archived?'\n已归档: '+j.archived:''));
tick()}catch(e){alert('清空失败: '+e)}}
async function clearPaper(){
if(!confirm('确定清空模拟成交记录？\n统计会归零，paper_trades.csv 会归档为 .cleared 备份。\n下单参数配置不受影响。')) return;
try{
const r=await fetch('/api/paper/clear'+Q,{method:'POST'});
if(!r.ok){alert(r.status==401?'口令错误':'清空失败 HTTP '+r.status);return}
const j=await r.json();
paperPage=1;
alert('已清空 '+j.cleared+' 笔'+(j.archived?'\n已归档: '+j.archived:''));
tick();
}catch(e){alert('清空失败: '+e)}}
async function savePaper(){
const body={};
['pre','strong','weak'].forEach(p=>{const o={enabled:$('en_'+p).checked,buy_price:Number($('bp_'+p).value),amount:Number($('am_'+p).value)};
if($('mt_'+p))o.max_tau=Number($('mt_'+p).value);
if($('ms_'+p))o.min_strength=Number($('ms_'+p).value);
body[p]=o});
try{const r=await fetch('/api/paper/cfg'+Q,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
const j=await r.json();
if(!r.ok||!j.ok){showHint(j.error||('保存失败 '+r.status),'#f85149');return}
showHint('已保存','#3fb950');tick()}
catch(e){showHint('保存失败: '+e,'#f85149')}}
// ---------------------------------------------------------------- 策略状态（各自 tab 顶部）
const ST_LABEL={ready:['可执行','ready'],wait:['等待','wait'],off:['未启用','off'],stop:['拦截','stop'],
done:['已成交','ready'],past:['已过期','off'],weak:['未达标','wait'],price:['价格不满足','wait'],
nodata:['缺数据','wait'],skip:['本场不适用','off']};
function stPill(state){const x=ST_LABEL[state]||[state,''];return `<span class="pill ${x[1]}">${x[0]}</span>`}
function renderPaperState(d){
const s=d.paper_status;
if(!s){setH('paperState','');return}
const ready=s.rows.filter(r=>r.ready).map(r=>SIGT[r.prof]).join('/');
const hd=`<div class="hd"><b>本场策略状态</b>${stPill(ready?'ready':(s.rows.some(r=>r.state=='wait')?'wait':'off'))}
<span class="pill">${ready?'可执行档：'+ready:'当前无可执行档'}</span>
<div class="kv"><span>场次 <b>${hm(s.round)}</b></span>
<span>相对开盘 <b>${s.tau>0?'+':''}${f(s.tau,0)}s</b></span>
<span>剩余 <b>${f(s.remain,0)}s</b></span>
<span>预判 <b class="${s.pred=='Up'?'up':(s.pred=='Down'?'dn':'')}">${ud(s.pred)}</b></span>
<span>p(涨) <b>${f(s.p_pred,3)}</b></span>
<span>强度 <b>${f(s.strength,3)}</b></span>
<span>档位 <b>${s.sig?SIGN[s.sig].replace('·开盘后',''):'-'}</b></span></div></div>`;
const rows=s.rows.map(r=>`<tr><td style="color:${SIGC[r.prof]}">${SIGT[r.prof]}</td><td>${stPill(r.state)}</td>
<td class="mut">${r.reason}</td><td>${r.side?ud(r.side):'-'}</td><td>${f(r.ask,3)}</td><td>${f(r.cap,2)}</td></tr>`).join('');
setH('paperState',`<div class="sstat">${hd}<table>
<tr><th>档</th><th>状态</th><th>说明</th><th>方向</th><th>当前卖一</th><th>上限</th></tr>${rows}</table></div>`)}

function renderSnipeState(d){
const s=d.snipe_status, cfg=d.snipe_cfg||{};
if(!s){setH('snipeState','');return}
const t=s.target, det=s.detail||{}, W=s.weights||{time:30,flow:35,bounce:20,gap:15};
const bet=cfg.bet??5, ms=cfg.min_score??62;
const cU=x=>x==null?'-':(x>=0.1?Math.round(x*100):(x*100).toFixed(1));
const sideTxt=t?(t.side=='Up'?'UP':'DOWN'):'-';
const sideCls=t?(t.side=='Up'?'up':'dn'):'';
const askC=t&&t.ask!=null?cU(t.ask):null, bidC=t&&t.bid!=null?cU(t.bid):null;
const lock=t?`雷达锁定劣势方：<span class="${sideCls}">${sideTxt}</span> <span class="px">(卖一 ${askC}¢ / 买一 ${bidC==null?'-':bidC+'¢'})</span>`
:`雷达待命：暂无可锁定方向`;
const sub=t?`5s 订单流反转：${det.tir==null?'-':(det.tir*100).toFixed(0)+'%'} · 30s 均值：${det.tir30==null?'-':(det.tir30*100).toFixed(1)+'%'} · 极值收回：${det.bounce==null?'-':'$'+f(det.bounce,2)} · 标准化差值 R：${s.r_gap==null?'-':f(s.r_gap,2)} · 剩余 ${f(s.remain,0)}s`
:`相对开盘 ${f(s.tau,0)}s，剩余 ${f(s.remain,0)}s，等待盘口数据`;
const canBuy=s.ready;
const armTxt=t&&askC!=null&&t.ask>0?`以 $${f(bet,2)} 模拟买入 ${sideTxt} (${askC}¢)`:`暂不可买入`;
setH('snipeState',`<div class="radar">
<div class="r1">
<div><div class="lock">${lock}</div><div class="r2">${sub}</div></div>
<div class="grow"></div>
<label class="inp a">触发上限(¢)<input type="number" id="sn_entry_c" step="1" min="1" max="99" value="${Math.round((cfg.max_entry??0.1)*100)}" onchange="quickSnipeCfg()"></label>
<label class="inp b">最低翻转分<input type="number" id="sn_score_q" step="1" min="0" max="100" value="${Math.round(ms)}" onchange="quickSnipeCfg()"></label>
<label class="auto"><input type="checkbox" id="sn_auto" ${cfg.enabled?'checked':''} onchange="quickSnipeCfg()"> 达标自动 $${f(bet,0)} 狙击</label>
<button class="go ${canBuy?'armed':''}" ${canBuy?'':'disabled'} onclick="manualSnipe()" title="${canBuy?'条件全部满足，可直接建仓':'未达标；如需忽略条件，请在下方配置栏放宽阈值'}">${armTxt}</button>
</div>
${s.blocked&&s.blocked.length?`<div class="note">未达标：${s.blocked.join('、')}${t&&!t.in_range?`（当前 ${askC}¢ 不在 ${Math.round((cfg.min_entry??0.03)*100)}~${Math.round((cfg.max_entry??0.1)*100)}¢ 区间）`:''}</div>`
:`<div class="note" style="color:#3fb950">条件全部满足，可执行</div>`}
</div>
<div class="cards">
<div class="mcard"><div class="t"><span>综合翻转几率评分</span><span>${s.score==null?'-':f(s.score,0)} / 100</span></div>
<div class="bar"><i style="width:${Math.max(0,Math.min(100,s.score||0))}%"></i></div>
<div class="f">时间窗口分 ${f(det.s_time,0)}/${W.time} · 阈值 ≥ ${f(ms,0)}${s.score!=null&&s.score>=ms?' <span class="up">已达标</span>':''}</div></div>
<div class="mcard"><div class="t"><span>5秒订单流脉冲 (TIR_5s)</span></div>
<div class="v" style="color:${det.tir==null?'#7d8590':(det.tir>=0?'#58a6ff':'#f85149')}">${det.tir==null?'-':((det.tir*100).toFixed(1)+'%')}</div>
<div class="f">30s 均值：${det.tir30==null?'-':(det.tir30*100).toFixed(1)+'%'} · 得分 ${f(det.s_flow,0)}/${W.flow}</div></div>
<div class="mcard"><div class="t"><span>本盘极值 Pin-bar 反弹幅度</span></div>
<div class="v" style="color:${det.bounce==null?'#7d8590':(det.bounce>0?'#3fb950':'#7d8590')}">${det.bounce==null?'-':(det.bounce>=0?'+':'')+'$'+f(det.bounce,2)+' USD'}</div>
<div class="f">插针收回得分：${f(det.s_bounce,0)}/${W.bounce}</div></div>
<div class="mcard"><div class="t"><span>Chainlink 预言机缓冲垫优势</span></div>
<div class="v" style="color:#d29922">${!s.scored||s.strike==null||s.spot==null?'-':(s.spot>=s.strike?'+':'-')+'$'+f(Math.abs(s.spot-s.strike),2)+' USD'}</div>
<div class="f">滞后缓冲得分：${f(det.s_gap,0)}/${W.gap}${det.tol==null?'':' · 容差 ±'+f(det.tol,1)+'$'}</div></div>
</div>`)}
async function quickSnipeCfg(){
const body={max_entry:Number($('sn_entry_c').value)/100,min_score:Number($('sn_score_q').value),enabled:$('sn_auto').checked};
try{const r=await fetch('/api/snipe/cfg'+Q,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});
const j=await r.json();
if(!r.ok||!j.ok){alert(j.error||('保存失败 '+r.status));return}
tick()}catch(e){alert('保存失败: '+e)}}
async function manualSnipe(){
try{const r=await fetch('/api/snipe/manual'+Q,{method:'POST'});
const j=await r.json();
if(!r.ok||!j.ok){alert(j.error||('建仓失败 '+r.status));return}
if(j.warn&&!confirm(j.warn+'\n\n仍要建仓？')) return;
tick()}catch(e){alert('建仓失败: '+e)}}

async function tick(){try{const sep=Q?Q+'&':'?';const r=await fetch('/api/state'+Q+sep+'ppage='+paperPage+'&psize='+PAPER_PAGE_SIZE+'&rpage='+page+'&rsize='+PAGE_SIZE+'&spage='+snipePage+'&ssize='+SNIPE_PAGE_SIZE);if(!r.ok){$('feeds').textContent=r.status==401?'访问口令错误：请在网址后加 ?token=你的口令（在服务器执行 btc5m url 查看）':'请求失败 HTTP '+r.status;return}
const j=await r.json();
try{draw(j)}catch(e){$('feeds').textContent='页面渲染出错（数据已收到）：'+e.message;console.error(e)}}
catch(e){$('feeds').textContent='无法连接服务器，稍后自动重试…'}}
tick();setInterval(tick,1000);
</script></body></html>'''


async def main(host, port):
    load_calib()
    load_rounds()
    load_paper_cfg()
    load_paper_trades()
    load_snipe_cfg()
    load_snipe_trades()
    async with aiohttp.ClientSession() as sess:
        app = web.Application()
        app.add_routes([web.get("/", index), web.get("/api/state", api_state),
                        web.post("/api/rounds/clear", api_clear_rounds),
                        web.get("/api/paper/cfg", api_paper_cfg),
                        web.post("/api/paper/cfg", api_paper_cfg),
                        web.post("/api/paper/clear", api_paper_clear),
                        web.get("/api/snipe/cfg", api_snipe_cfg),
                        web.post("/api/snipe/cfg", api_snipe_cfg),
                        web.post("/api/snipe/clear", api_snipe_clear),
                        web.post("/api/snipe/manual", api_snipe_manual),
                        web.get("/api/rounds/export", api_export_rounds),
                        web.get("/api/data/export", api_export_data)])
        runner = web.AppRunner(app, access_log=None)
        await runner.setup()
        await web.TCPSite(runner, host, port).start()
        log.info("看板: http://%s:%s/%s", host, port, f"?token={DASH_TOKEN}" if DASH_TOKEN else "")
        for _prof in PAPER_PROFILES:
            log.info("模拟下单[%s]: %s", PAPER_PROFILE_LABEL[_prof], S.paper_cfg[_prof])
        await asyncio.gather(ws_poly(sess), ws_binance(sess), ws_okx(sess),
                             ticker(sess), pm_fallback(sess), cl_watchdog(), status())


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="0.0.0.0")
    ap.add_argument("--port", type=int, default=9999)
    a = ap.parse_args()
    try:
        asyncio.run(main(a.host, a.port))
    except KeyboardInterrupt:
        pass
