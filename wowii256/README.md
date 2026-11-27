# WOWII 第 256 题的最小反例与最优系数

**摘要。** Written on the Wall II 第 256 题的最小反例恰有 **14 个顶点**。将原不等式右侧的系数 2 改为普适常数后，最大的可用系数恰为 **1**。这一常数在连通二分图类中同样最优。本文给出两项结论的组合证明及完整 Lean 形式化，并保留 14 点和 59 点反例的 Lean 证书。

设 $G$ 是至少有两个顶点的有限连通简单图。记 $n=|V(G)|$，$A$ 为最小度顶点集合，$N(v)$ 为顶点 $v$ 的开邻域，$N(A)=\bigcup_{v\in A}N(v)$。记 $\gamma_t$ 为总支配数，即使每个顶点都邻接所选顶点的最小集合大小。对每条边 $uv$ 定义 $B(uv)=N(u)\cup N(v)$，令 $M=\max_{uv\in E(G)}|B(uv)|$。原猜想断言 $\gamma_t M\ge 2|N(A)|$。[原目录第 256 题](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

2026 年 11 月 21 日，Tony Newton 向目录提交了下文同构的 14 点反例、最小性证明及紧常数结果。11 月 19 日公开的另一篇稿件用含三角形的图族证明了一般连通图上的最优系数 1。本文给出完整推导，并将二分图上的系数最优性和最小阶结论形式化。[官网注释](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json) · [官方例图](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/ce256.png) · [一般图系数的在先稿件](https://github.com/srikant07-dev/graffiti-pc-conjecture-256/blob/314f74a234703f3860327586054c9fa9e08e45e7/paper.pdf)

Derek Blair 的公开 PR #51 于 2026 年 11 月 25 日 18:04 UTC 创建，给出了 15 点反例与 Lean 证书。其图由两个各含三个三角形的友谊图构成，两侧的中心由一条长度为 2 的路径相连。[公开 PR](https://github.com/derekblair/math-proofs/pull/51) · [第 256 题证明](https://github.com/derekblair/math-proofs/blob/af6904cc3fa537b5c4dcea9561b24b69177c6ee1/research/lean-verified-2026-11-25/graffiti-256/PROOF.md)

## 定理 1。最小反例阶数为 14

### 14 点构造

取三点路径 $a-b-c$ 和一个不相交的 11 点环。将环上一点 $z$ 连到 $b$，其余十点分成两组，每组五点，分别连到 $a$ 和 $c$。所得图连通。

- $a,c$ 的度为 6，其他点的度均为 3。每个顶点有一个度为 3 的邻点，所以 $N(A)=V(G)$。
- 每条边两端度数之和至多为 9。边 $ab$ 两端的开邻域不相交，度数之和为 9。所以 $M=9$。
- $\{a,b,c\}$ 总支配全图。任何二元总支配集的两个顶点必须相邻，但一条边的边邻域最多含 9 个点。所以 $\gamma_t=3$。

从而 $\gamma_t M=27<28=2|N(A)|$。

### 排除至多 13 点的图

设 $G$ 是反例，记 $g=\gamma_t$，取最小总支配集 $D$。有 $gM<2|N(A)|\le 2n$。由于 $g\ge 2$，有 $M<n$。若 $g=2$，$D$ 构成一条边且它的边邻域覆盖全图，与 $M<n$ 矛盾。

先证 $\deg(v)\le M-2$ 对每个 $v$ 成立。若某个闭邻域 $Q=N[v]$ 至少含 $M$ 点，则对任何 $w\in N(v)$，有 $Q\subseteq B(vw)$、$|B(vw)|\le M$，所以 $Q=B(vw)$。于是 $N(w)\subseteq Q$ 对所有 $w\in N(v)$ 成立。这使 $Q$ 对邻接封闭。图连通，所以 $Q=V(G)$，与 $M<n$ 矛盾。

由 $D$ 的开邻域覆盖全图，得 $n\le g(M-2)$。再结合严格不等式 $gM<2n$，得 $2g<n$。因此，若 $n\le13$，只需处理 $g=3,4,5,6$。诱导图 $G[D]$ 无孤立点。在此图中，若若干条边覆盖 $D$，则这些边的边邻域覆盖 $V(G)$。此外，当 $|D|\ge4$ 时，若任意两条诱导边都相交，$G[D]$ 必为星图。事实上，取两条相交边，避开其公共端点的边若存在，就必须与这两条边形成三角形。三角形外的顶点必有入射边，但这条边无法同时与三角形的三条边都相交。

- **$g=3$。** 将 $D$ 写为两边路径 $a-b-c$ 的三个顶点。$B(ab)$ 和 $B(bc)$ 的并覆盖全图，交包含 $a,b,c$，故 $n+3\le2M$。由此及 $3M<2n\le26$，得 $M>6$、$M\le8$，且 $(n,M)$ 只能为 $(11,7)$ 或 $(13,8)$。两种情况都有 $n+3=2M$，故两个边邻域都恰有 $M$ 点，交恰为 $D$。由于 $N(b)$ 在交中，$N(b)=\{a,c\}$。两个边邻域的大小分别至多为 $\deg(a)+2,\deg(c)+2$，所以 $\deg(a),\deg(c)\ge M-2\ge5$。最小度至多为 2，因此 $b\notin N(A)$。两种情况均有 $3M\ge2(n-1)\ge2|N(A)|$，矛盾。
- **$g=4$。** 若 $G[D]$ 有两条不交边，则 $n\le2M$，与 $4M<2n$ 矛盾。否则 $G[D]$ 是四点星。三条边的边邻域均包含 $D$，故 $n\le3M-8$。由 $4M<2n\le26$ 得 $M\le6$。若 $M\le5$，则 $n\le7$，与 $2g<n$ 矛盾。若 $M=6$，则 $n\le10$，与 $4M<2n$ 矛盾。
- **$g=5$。** 由 $5M<2n\le26$ 得 $M\le5$。由于 $n\le5(M-2)$ 且 $n>10$，必有 $M=5$，再由 $5M<2n\le26$ 得 $n=13$。每个顶点的度至多为 3，故 $G[D]$ 无法是五点星，必有两条不交边。再取一条连接余下第五点与 $D$ 中某个邻点的边。这三条边覆盖 $D$，且其中两条边相交。相交两边的边邻域至少共有这两边的三个端点。故 $n\le3M-3=12$，矛盾。
- **$g=6$。** 由 $6M<2n\le26$ 得 $M\le4$。于是 $n\le6(M-2)\le12$，与 $2g<n$ 矛盾。

因此，至多 13 点的图满足原不等式。

## 定理 2。最优普适系数为 1，且在二分图上锐利

每个顶点至少有一个邻点。对任意顶点 $u$，取邻点 $v$ 即得 $|N(u)|\le |B(uv)|\le M$。最小总支配集的开邻域覆盖 $V(G)$，所以 $|N(A)|\le n\le\gamma_t M$。

为证明锐性，固定整数 $k,s,t\ge2$，构造连通二分图 $G_{k,s,t}$。每组有 $s$ 个原左点和 $st$ 个普通右点，两部分间添加完全二分图的全部边。每组的普通右点分成 $t$ 批，每批 $s$ 个。每批增设一个左点，与该批的所有普通右点相连。取 $k$ 个这样的组，最后增加一个共享右枢纽 $z$，将它与所有左点相连。

原左点、普通右点、批次左点以及枢纽的度分别为 $st+1,s+1,s+1,k(s+t)$。因为 $k,s,t\ge2$，最小度顶点正好是普通右点和批次左点。所有左点都邻接普通右点，每个普通右点都邻接自己的批次左点，枢纽也邻接批次左点。因此

$$
|N(A)|=|V(G_{k,s,t})|=k(st+s+t)+1.
$$

总支配集必须在每组选至少一个左点，才能支配该组的普通右点。它还必须包含一个右点，才能支配左点。每组选一个原左点，再选枢纽，就可以支配全图。因此 $\gamma_t=k+1$。

因为图是二分图，每条边两端的开邻域不相交。在左部，原左点达到最大度 $st+1$。在右部，枢纽达到最大度 $k(s+t)$，且枢纽与原左点相邻。故 $M=st+1+k(s+t)$。于是

$$
\gamma_tM-2|N(A)|=(k-1)\bigl(1+k(s+t)-st\bigr).
$$

以 $(k,s,t)=(2,4,5)$ 为例，图有 59 个顶点，$\gamma_t=3$，$M=39$，原不等式成为 $117\ge118$，因而失败。取 $s=t=k^2$ 并令 $k$ 趋于无穷，则

$$
\frac{\gamma_tM}{|N(A)|}
=\frac{(k+1)(k^4+2k^3+1)}{k^5+2k^3+1}
\longrightarrow 1.
$$

所以任何大于 1 的系数都会在这族二分图上失效。

## 复现

| 结论 | Lean 文件 | 定理 |
| --- | --- | --- |
| 14 点反例 | [WOWII256Small.lean](../WOWII256Small.lean) | WOWII256.refutes_bound14 |
| 59 点二分反例 | [WOWII256.lean](../WOWII256.lean) | WOWII256.conjecture256_false |
| 最小阶为 14 | [WOWII256Minimum.lean](../WOWII256Minimum.lean) | WOWII256.smallest_counterexample_order |
| 最大有效系数为 1 | [WOWII256Sharp.lean](../WOWII256Sharp.lean) | WOWII256.sharp_coefficient |
| 二分图上的最大有效系数为 1 | [WOWII256Sharp.lean](../WOWII256Sharp.lean) | WOWII256.sharp_coefficient_bipartite |

按[仓库首页](../README.md)准备 Lean 4.33.1 和固定版本的依赖后，运行 [Verify.ps1](../Verify.ps1)。脚本编译证书、检查公理依赖并重放内核。表内定理仅依赖 Lean 的 propext、Classical.choice 和 Quot.sound。

Lean 的锐性证明使用上述二分图的等参数子族 $s=t=m=k^2$。证明使用有理界 $\gamma_tM/|N(A)|\le1+7/k$，从而给每个实系数 $c>1$ 构造有限反例。

运行以下命令可从组合规则独立重建两张图，检查精确参数、Lean 邻接编码与下界证明中的有限算术情形。

~~~sh
python -m unittest discover -v
~~~

OpenAI Codex 参与了构造、证明推导、Lean 形式化和验证。
