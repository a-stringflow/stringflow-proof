# 全局长度上界与 Q 分族约化

日期：2026-08-05

本文件把 Simons 2008 的链式不等式与 Laurent 型下界翻译成对进入
方程 (E) 和双链闭合方程的具体约束，得到全局长度上界、声音
S7+S4 记录筛，并对旧 G4/G6 的方向错误作勘误：

1. **G3**：对每个 $Q\ge8$，存在可计算的 $P_Q$，任何 7 可达循环
   都满足 $P<P_Q$；
2. **G4'（声音 (SF) 筛）**：对 $Q=9,\dots,14,16,18,23,25,29$，
   任何循环都有 $x_0\le10^6$（$x_0>10^6$ 侧关闭）；但
   $x_0\le10^6$ 侧仍有大量存活记录，没有“唯一候选”；
3. **G6 勘误**：Q=8 只有 $x_0>10^6$ 侧关闭，$x_0\le10^6$ 侧
   未排除（旧“整族排除”作废）。

所有计算由 `verify_global_P_bound.py`、`verify_x0_dichotomy.py`
和 `verify_q8_exclusion.py` 复现，证书分别写在
`global_P_bound_table.txt`、`x0_dichotomy_certificate.txt` 和
`q8_exclusion_certificate.txt`。

---

## 1. 记号与双链结构

沿用 `cyclic_strings_5x1.md` 的记号：

- $\lambda=\log_2 5$，$\rho=\lambda$；
- 加速映射 $V(n)=\operatorname{oddpart}(5n+1)$；
- 循环有 $P$ 个词长、$T$ 个总权重、$Q$ 个 $C_3$ 返回词，
  $\delta=T-P\lambda>0$；
- $N_i$ 是第 $i$ 个 $C_3$ 起点，$t_i=v_2(5N_i+1)\ge3$；
- $X_i=(5N_i+1)/2^{t_i}$ 是紧随其后的局部极小值。

Simons 2008 的局部极小值 $x_i$ 正是这里的 $X_i$。由此得到
“双链”：

$$
X_i=\frac{5N_i+1}{2^{t_i}}<\frac{3N_i}{4},
\qquad
X_{i+1}<b\,X_i^{\rho},
\qquad
b=\frac{(22/7)^{\rho}}{6}.
$$

第二式是 Simons (34) 在 $x_i\ge7$ 时的版本：$q=1$ 时
$(p-2)+q/x_i\le3+1/7=22/7$。

## 2. 新外部约束

### S6（最大局部极小值下界；Simons (33)）

$$
\max_i X_i>\frac{2^{P/Q}}{4}.
$$

### S7（全局最小值下界；Simons (34)+(35)+(33) 的组合）

令

$$
c=\frac{22/7}{6^{1/\rho}},\qquad
A_Q=c^{-\rho/(\rho-1)}\,4^{-1/\rho^{Q-1}}.
$$

则任何 7 可达循环满足

$$
x_0=\min_i X_i>A_Q\,2^{P/(Q\rho^{Q-1})}.
$$

### S4（Simons (32)）

$$
\delta<\frac{Q}{3x_0\ln2}.
$$

### S9（Laurent 型下界；Simons (38) 的全局化）

7 可达循环的所有值 $\ge7$，故
$T/P\le\log_2(36/7)<2.3626$，从而
$b'=P+T/\ln5<2.5P$。Laurent-Mignotte-Nesterenko 的
Corollaire 2 给出

$$
\delta>
\frac{1}{\ln2}
\exp\!\Bigl(-24.34\,\ln5\,
\bigl[\max(\ln P+1.057,\,21)\bigr]^2\Bigr).
$$

## 3. 引理 G3：每个 Q 的全局长度上界

**陈述。** 设 7 可达循环有 $Q\ge8$ 个 $C_3$ 返回词。若 $P_Q$ 是
下列方程的解：

$$
\log_2 A_Q+\frac{P_Q}{Q\rho^{Q-1}}
=\log_2 Q-\log_2(3\ln2)-\log_2\delta_{\mathrm{lb}}(P_Q),
$$

其中 $\delta_{\mathrm{lb}}(P)$ 是 S9 的下界，则 $P<P_Q$。

**证明。** S7 给 $x_0$ 下界，S4 给 $x_0<Q/(3\delta\ln2)$，S9 给
$\delta>\delta_{\mathrm{lb}}(P)$。三项合并：

$$
A_Q2^{P/(Q\rho^{Q-1})}
<\frac{Q}{3\delta\ln2}
<\frac{Q}{3\delta_{\mathrm{lb}}(P)\ln2}.
$$

取 $\log_2$ 即得与 $P\ge P_Q$ 矛盾。∎

数值表（前 23 行，完整表见 `global_P_bound_table.txt`）：

| $Q$ | $\log_{10}P_Q$ | $P_Q$ |
|---|---:|---:|
| 8 | 7.8607 | $7.26\times10^7$ |
| 9 | 8.2777 | $1.90\times10^8$ |
| 10 | 8.6923 | $4.92\times10^8$ |
| 11 | 9.1411 | $1.38\times10^9$ |
| 12 | 9.5839 | $3.84\times10^9$ |
| 13 | 10.0215 | $1.05\times10^{10}$ |
| 14 | 10.4548 | $2.85\times10^{10}$ |
| 15 | 10.8841 | $7.66\times10^{10}$ |
| 16 | 11.3100 | $2.04\times10^{11}$ |
| 17 | 11.7328 | $5.41\times10^{11}$ |
| 18 | 12.1529 | $1.42\times10^{12}$ |
| 19 | 12.5705 | $3.72\times10^{12}$ |
| 20 | 12.9859 | $9.68\times10^{12}$ |
| 21 | 13.3992 | $2.51\times10^{13}$ |
| 22 | 13.8107 | $6.47\times10^{13}$ |
| 23 | 14.2205 | $1.66\times10^{14}$ |
| 24 | 14.6286 | $4.25\times10^{14}$ |
| 25 | 15.0353 | $1.08\times10^{15}$ |
| 26 | 15.4406 | $2.76\times10^{15}$ |
| 27 | 15.8446 | $6.99\times10^{15}$ |
| 28 | 16.2475 | $1.77\times10^{16}$ |
| 29 | 16.6492 | $4.46\times10^{16}$ |
| 30 | 17.0499 | $1.12\times10^{17}$ |

常数校核：$P_{10}=4.92\times10^8$ 与 Simons 表 (40) 的
$K_3(10)=4.92\times10^8$ 一致，说明 S9 与 S7 的组合没有引入
数量级错误。

## 4. 引理 G5：连分数记录归约

对任意 $P$，记 $r$ 为不超过 $P$ 的最大“上方半收敛子”分母
（即 $\lceil P\lambda\rceil/P>\lambda$ 且 $\lceil P\lambda\rceil-P\lambda$
在 $r\le P$ 中取新最小值的那类分母）。标准连分数事实给出

$$
\lceil P\lambda\rceil-P\lambda
\ge\lceil r\lambda\rceil-r\lambda.
$$

证明：令 $d(q)=\lceil q\lambda\rceil-q\lambda$。若
$d(P)<d(r)$，则在 $r<P'\le P$ 中取使 $d(P')$ 最小的 $P'$；
对一切 $q<P'$ 有 $d(q)\ge d(r)>d(P')$，故 $P'$ 本身是一个新的
上方记录分母，与 $r$ 的最大性矛盾。因此 $d(P)\ge d(r)$。∎

因此，要证明区间内所有 $P$ 都违反某条上界，只需检查有限个记录
分母；脚本 `verify_x0_dichotomy.py` 已生成并检查这些记录。
这些记录的上方半收敛射线参数化、$T$ 与 $\delta$ 闭式见
`surv_ray.md`，完整幸存清单见 `surv_ray_certificate.txt`。

## 5. 声音 S7+S4 记录筛（G4'；替代旧 G4）

设 $P_x(Q)$ 由 $x_0\le10^6$ 与 S7 解出：

$$
P_x(Q)=Q\rho^{Q-1}\log_2\frac{10^6}{A_Q}.
$$

对每个记录分母 $P$，令
$\delta(P)=\lceil P\lambda\rceil-P\lambda$。声音必要条件（不依赖
$x_0$ 是否 $\le10^6$）是 S7 下界小于 S4 上界：

$$
A_Q\,2^{P/(Q\rho^{Q-1})}
<\frac{Q}{3\,\delta(P)\ln2}.
\tag{SF}
$$

若 (SF) 对某个记录 $r$ 失败，则对 $[r,\text{下一记录})$ 内所有
$P$ 都失败（$\delta(P)\ge\delta(r)$ 且 $x_0$ 下界随 $P$ 递增）。
脚本 `verify_sound_x0_filter.py` 与 `verify_x0_dichotomy.py` 对
$Q=8,\dots,30$ 输出该筛法，证书
`sound_x0_filter_certificate.txt`、`x0_dichotomy_certificate.txt`。

**勘误（旧 G4）。** 旧版在 $x_0\le10^6$ 一侧额外要求
$\delta<\theta_Q=Q/(3\cdot10^6\ln2)$。这一步方向反了：S4 给
$\delta<Q/(3x_0\ln2)$，而 $x_0\le10^6$ 只会让右边变大。已知循环
$\{13,33,83\}$（$x_0=13\le10^6$，$\delta=0.0342>\theta_1$）是
反例。因此旧 G4 的“候选表”和“唯一候选”结论作废，改用 (SF)。

声音筛法给出的状态：

- $x_0>10^6$ 一侧：$Q=8,\dots,14,16,18,23,25,29$ 零幸存，故这些
  $Q$ 的任何循环都有 $x_0\le10^6$；其余 $Q$（15,17,19..22,24,
  26..28,30）仍有开放记录；
- $x_0\le10^6$ 一侧：**没有**被压成少数候选。例如
  $Q=9..11$ 各有 30--33 个存活记录，$Q=14$ 有 53 个；存活记录
  从 1,3,7,...,21,306,97,879 一直到接近 $P_x(Q)$。旧的
  “Q=9 唯一候选 97,879”不成立。
- **V7ab（值域下界截断）**：7 可达循环所有值 $\ge7$，S4 给
  $\delta<Q/(21\ln2)$。这把 $Q=9..11$ 的存活记录压到 10 个，
  $Q=12,13,14$ 压到 11,13,16 个（`sound_x0_filter_certificate.txt`
  V7 列）。
- **CS（corner scan 计算排除）**：对全部奇数 $n_0\le10^7$ 穷举，
  $L=31,59,205,497,643$ 零循环、$L=351$ 仅非本原重复；框 A 给
  $x_0\le10^6<10^7$，故这些长度对 7 可达全部排除
  （`corner_scan_exclusion_certificate.txt`）。

## 5.5 H1ab 附加排除（不是坍缩）

参数化引理 Hab（`general_analytic_constraints.md` 第 15 节）给

$$
m>\frac1{5(2^\delta-1)}.
$$

在 $x_0\le10^6$ 框内，这只排除
$1/(5(2^\delta-1))>10^6$ 的记录，即 $\delta$ 很小的长度
（约 $\delta<2.9\times10^{-7}$）。证书
`h1_candidate_exclusion_certificate.txt`（脚本
`verify_h1_candidate_exclusion.py`）给出：$Q=12,13$ 排除
1,936,274，$Q=14$ 排除 1,936,274 与 15,392,313；但
1,3,7,...,21,306,97,879 等大量小长度全部存活。因此 H1ab 只是
附加过滤，**不能**把 $Q=9..14$ 坍缩成单一候选。结合 SF+L0+V7+CS
后，$Q=9..12$ 各剩 4 个存活记录（4647,8651,21306,97879），
$Q=13$ 6 个、$Q=14$ 8 个。

## 6. Q=8 的状态（G6 勘误）

**旧声明“不存在 8-循环”不成立为已证。** 旧证明的 $x_0\le10^6$
一侧用 $\delta\ge1.033\times10^{-5}>\theta_8$ 与 S4 矛盾，但
$\delta<\theta_8$ 在 $x_0\le10^6$ 下并不由 S4 推出（方向错误）。

声音筛法（`verify_q8_exclusion.py`、
`q8_exclusion_certificate.txt`）给出：

- $x_0>10^6$：零幸存，关闭；
- $x_0\le10^6$：28 个存活记录（1,3,4,7,10,13,...,21,306），
  **未排除**。

因此 Q=8 仍开放；S2' 只能把它的最小值压到 $x_0\le10^6$。

## 7. 开放点

1. G3 的 $P_Q$ 用的是 Laurent 的保守常数；若用更好的显式下界，
   阈值会显著下降；
2. $Q=9..14,16,18,23,25,29$ 的 $x_0>10^6$ 侧已关闭，但
   $x_0\le10^6$ 侧仍有大量存活记录（见 `sound_x0_filter_certificate.txt`）；
3. $Q=15,17,19,20,21,22,24,26,27,28,30$ 的 $x_0>10^6$
   候选仍需进一步处理。52.7 的 $b=1,2$ 审计见
   `ureq52_7_audit.txt`：这些候选在 $b=1,2$ 时违反
   $U_{\mathrm{req}}\le L$，但 52.7 不限制 $b$ 上界，取大 $b$
   可恢复可行性，因此该审计不排除候选；2026-08-06 的 b 上界与
   MODp 审计（`modular_x0_gt_1e6_audit.txt`、`ph_qb_gc_chain.md`
   53.5）也未关闭这些记录；同日 SURV-RAY 把该前置条件改写为
   连分数半收敛射线族的整族排除，完整 `Q=8..100` 幸存清单
   （236 条）见 `surv_ray_certificate.txt`，证明见 `surv_ray.md`；
4. 97,879 的松弛最优分段障碍（
   `shared_candidate_staging_certificate.txt`）只覆盖这一个
   $(P,T)$ 的松弛最优情形，且仍缺支配引理；它不关闭任何 $Q$。
