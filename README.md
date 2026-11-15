# BTCtest4

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

默认看板端口 `9999`。私钥写在 `~/.btc5m-4.env` 的 `POLY_PRIVATE_KEY`。
