# Written on the Wall II 第 255、256 题

**第 256 题。** 最小反例恰有 **14 个顶点**，最优普适系数恰为 **1**，而且限制为二分图后仍然锐利。完整证明及 Lean 复现入口见[第 256 题研究说明](wowii256/README.md)。

## 第 255 题

在有限、连通、至少有两个顶点的简单图中，令 $M$ 为相邻两点的开邻域并集的最大基数，$C$ 为中心顶点集合，$\gamma_t$ 为总支配数。[原猜想](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf#page=148)断言 $\gamma_t M\ge 2|C|$。

- 最小反例恰有 11 个顶点，参数为 $(|C|,M,\gamma_t)=(11,7,3)$。编号 0、1、2 分别对应 $a,b,c$，3–6 与 7–10 分别为 $x_i,y_i$。边为 $ab,bc,ax_i,x_iy_i,y_ic$ 及所有 $x_ix_j$。
- 十阶及以下的图满足更强的 $\gamma_t M\ge 2|V|$。证明用度数约束和最小总支配集的邻域覆盖。
- 最大普适系数为 $1$。有序对关联图给出令 $\gamma_tM/|C|$ 趋于 $1$ 的无限二分图族。另保留原来的 184 顶点证书。

Derek Blair 已公开给出与上述 11 点图同构的反例。这里另给出最小阶和最优普适系数的证明。[Blair 的在先反证](https://github.com/derekblair/math-proofs/blob/af6904cc3fa537b5c4dcea9561b24b69177c6ee1/research/lean-verified-2026-11-25/graffiti-255/PROOF255.md)

## 复现环境与 Lean 证明

| 定理 | 文件 |
| --- | --- |
| `WOWII255.smallest_counterexample_order` | `WOWII255Minimum.lean` |
| `WOWII255.order_times_two_le_domination_mul_max_of_card_le_ten` | `WOWII255MinimumLower.lean` |
| `WOWII255.sharp_coefficient` | `WOWII255Sharp.lean` |
| `WOWII255.conjecture255_false` | `WOWII255.lean` |
| `WOWII256.refutes_bound14` | `WOWII256Small.lean` |
| `WOWII256.conjecture256_false` | `WOWII256.lean` |

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

## 独立整数复核

Python 3 脚本从组合规则重建图并核对精确整数参数。十阶及以下的结构论证见 Lean 证明，Python 另检查其整数推论。

```sh
python verify_minimum.py
python verify_pair_family.py
python -m unittest discover -v
```

OpenAI Codex 参与了构造、证明推导、Lean 形式化和验证。
