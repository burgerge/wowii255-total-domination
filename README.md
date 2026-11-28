# Lean 4 Certificates for Graffiti WOWII Problems 255 and 256

Written on the Wall II 第 255、256 题的图论证明证书。

本仓库提供第 255、256 题的 Lean 证明和复验脚本。两题的最小反例阶数分别为 **11** 和 **14**，最大的有效系数均为 **1**。第 256 题的系数在连通二分图类中也最优。

联合预印本已于 2026 年 11 月 27 日撤出当前发布版本。

第 256 题原目录记载了 Tony Newton 的 14 点见证和最小性证明。一般连通图上的系数 1 也已有公开证明。[官网注释](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json) · [11 月 19 日在先论文](https://github.com/srikant07-dev/graffiti-pc-conjecture-256/blob/314f74a234703f3860327586054c9fa9e08e45e7/paper.pdf)

## 第 255 题

在有限、连通、至少有两个顶点的简单图中，令 $M$ 为相邻两点的开邻域并集的最大基数，$C$ 为中心顶点集合，$\gamma_t$ 为总支配数。[原目录第 255 题](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)断言 $\gamma_t M\ge 2|C|$。

- 最小反例恰有 11 个顶点，参数为 $(|C|,M,\gamma_t)=(11,7,3)$。编号 0、1、2 分别对应 $a,b,c$，3–6 与 7–10 分别为 $x_i,y_i$。边为 $ab,bc,ax_i,x_iy_i,y_ic$ 及所有 $x_ix_j$。
- 十阶及以下的图满足更强的 $\gamma_t M\ge 2|V|$。证明用度数约束和最小总支配集的邻域覆盖。
- 最大普适系数为 $1$。有序对关联图给出令 $\gamma_tM/|C|$ 趋于 $1$ 的无限二分图族。另保留原来的 184 顶点证书。

Derek Blair 已公开给出与上述 11 点图同构的反例，也已有公开的无限反例族。[Blair 的在先反证](https://github.com/derekblair/math-proofs/blob/af6904cc3fa537b5c4dcea9561b24b69177c6ee1/research/lean-verified-2026-11-25/graffiti-255/PROOF255.md) · [在先反例族](https://github.com/f8bsd9yqgp-maker/Solved-conjectures-/blob/9a49179c1217e4e260e24b9d5d506432d1b328eb/proofs/graffiti-pc-255/README.md)

## 复现环境与 Lean 证明

| 定理 | 文件 |
| --- | --- |
| `WOWII255.smallest_counterexample_order` | `WOWII255Minimum.lean` |
| `WOWII255.order_times_two_le_domination_mul_max_of_card_le_ten` | `WOWII255MinimumLower.lean` |
| `WOWII255.sharp_coefficient` | `WOWII255Sharp.lean` |
| `WOWII255.conjecture255_false` | `WOWII255.lean` |
| `WOWII256.refutes_bound14` | `WOWII256Small.lean` |
| `WOWII256.conjecture256_false` | `WOWII256.lean` |
| `WOWII256.smallest_counterexample_order` | [WOWII256Minimum.lean](WOWII256Minimum.lean) |
| `WOWII256.bound_of_card_le_thirteen` | [WOWII256Minimum.lean](WOWII256Minimum.lean) |
| `WOWII256.sharp_coefficient` | [WOWII256Sharp.lean](WOWII256Sharp.lean) |
| `WOWII256.sharp_coefficient_bipartite` | [WOWII256Sharp.lean](WOWII256Sharp.lean) |

依赖 [Formal Conjectures 的固定提交](https://github.com/google-deepmind/formal-conjectures/commit/9097e2f90e66d2f6244209cb1c07f7120d17ec53)，其中固定了 Lean 4.33.1 及 Mathlib。脚本按模块编译，审计主要定理的依赖公理，并使用 `leanchecker` 重放内核检查。每条主要定理的公理集合为 `propext`、`Classical.choice`、`Quot.sound`。

在 PowerShell 7 中先准备 Formal Conjectures 的构建环境，再运行脚本。Lean 可执行程序不在 PATH 时，为脚本提供 `-LeanBin`。

```powershell
git clone https://github.com/google-deepmind/formal-conjectures.git
git -C formal-conjectures checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
Push-Location formal-conjectures
lake exe cache get
lake build FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
Pop-Location
pwsh -File ./Verify.ps1 -Repository ./formal-conjectures
```

OpenAI Codex 参与了构造、证明推导、Lean 形式化和验证。
