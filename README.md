# WOWII 第 255、256 题的最小反例与最优系数

Written on the Wall II 第 255、256 题的最小反例阶数分别为 **11**、**14**。原不等式中最大的普适实系数在两题中均为 **1**，对第 256 题限制为连通二分图也无法增大这一系数。

本分支提供 Lean 4.35.0 下的完整形式化。每个题面文件均有实际证明，两组配置分别选取下列定理。每组都包含第 255、256 题。

| 配置 | Lean 定理 |
| --- | --- |
| [最小反例](comparator-minimum.json) | WOWII255.smallest_counterexample_order、WOWII256.smallest_counterexample_order |
| [最优系数](comparator-sharp.json) | WOWII255.sharp_coefficient、WOWII256.sharp_coefficient、WOWII256.sharp_coefficient_bipartite |

固定版本的数学推导、Lean 模块及 Python 复核脚本见[联合研究成果](https://github.com/burgerge/wowii255-total-domination/tree/67878cbe235830fc174bb13c0d03b77d104742f5)。原猜想的在先反例见 [Derek Blair 的公开证明](https://github.com/derekblair/math-proofs/pull/51)。

在支持 bubblewrap 的 Linux 环境中复现验证。

~~~sh
lake exe cache get
lake build
lake comparator --config comparator-minimum.json
lake comparator --config comparator-sharp.json
~~~
