# BTC-test4

Polymarket BTC 5 分钟涨跌盘：下场预判、场中公允概率、数据采集与 Web 看板。

## 一行安装 / 更新

```bash
curl -fsSL https://raw.githubusercontent.com/hrf100/btctest4/main/test4/run.sh | bash
```

## 主要文件

| 路径 | 说明 |
|------|------|
| `test4/btc5m-4.py` | 主服务（看板 + 预判 + 模拟下单） |
| `test4/pred_model.py` | 下场预判模型纯计算核心 |
| `test4/analyze.py` | 回测 / 校准 |
| `test4/run.sh` | 服务器安装与 systemd 服务 |
| `btc5m.py` | 早期采集版 |

## 模拟下单（三档，共用列表，标记 前/强/普）

| 档位 | 触发 | 默认 |
|------|------|------|
| 开盘前 `pre` | 预判后、开盘前，模型强度 \|p−0.5\| ≥ 阈值 且 预判方向卖一 ≤ 上限 | 强度 0.08，上限 0.70，5U |
| 强信号 `strong` | 开盘后窗口内，预判方向卖一 ≤ 买价上限 | 0.45，150s，5U |
| 普通信号 `weak` | 同上（非强信号场次），默认关闭 | 0.45，150s，5U |

「模型−卖价」差值仅作参考，不作为买入依据。配置存 `data/paper_cfg.json`，成交存 `data/paper_trades.csv`。

默认看板端口 `9999`。私钥写在 `~/.btc5m-4.env` 的 `POLY_PRIVATE_KEY`。

顶栏「本进程 CPU」是本服务自身占用（单核百分比），「整机 CPU」是整台机器（含其它进程）。日志每 30 秒输出一行 `cpu ticker ...ms/s` 与 WS 消息量，用于定位负载来源。
