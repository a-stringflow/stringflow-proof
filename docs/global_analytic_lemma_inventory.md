# 全局解析引理清单（声音版本）

日期：2026-08-05

本文件是 5x+1 全局解析约束的单一清单，按目标要求的格式给出每个
引理的陈述、证明、适用范围、$(5,1)$ 特化、常数来源与证书路径。
所有“已证”条目都经过声音复核；所有“部分/开放”条目都明确标注。

> **勘误基线**：旧 G4 候选表、旧 G6、旧定理 B、旧 Q=9 唯一候选
> 基于 $x_0\le10^6$ 下 $\delta<\theta_Q$ 的方向错误，已作废
> （见 `global_layer_applicability_audit.md` 与
> `global_P_bound.md` 第 5 节）。本清单只收录声音结论。

---

## 0. 状态总表

| 编号 | 名称 | 状态 | 适用范围 |
|---|---|---|---|
| L0ab | 长度刚性 $P\ge Q+2$ | 已证 | 任意奇数 $a\ge3,b>0$，$Q\ge5$ |
| V7ab | 值域下界截断 $\delta<Q/(3N_0\ln2)$ | 已证 | 任意循环值 $\ge N_0$；7 可达取 $N_0=7$ |
| G1 | 长度-余量整数不等式 | 已证 | 任意 $a$，$4<a<8$ 框架 |
| G1+ | 整数松弛恒等式 | 已证 | 同上 |
| G1++ | $\alpha$ 分数恒等式 | 已证 | 同上 |
| d_i | 整数刚性 | 已证 | 同上 |
| N' | 负词单步上界 | 已证 | 任意 $a\ge3,b>0$ |
| H1ab/H2ab | 全局最小值分子下界 | 已证 | 任意奇数 $a\ge3,b>0$ |
| Hab | $m>1/(a(2^\delta-1))$ | 已证 | 无条件 |
| PMI | 精确前缀余量恒等式 $\sum_j2^{-M_j}=5m(2^\delta-1)$ | 已证 | 任意奇数 $a\ge3,b>0$ |
| PH-1 | 词贡献分解 $C_i=2^{-M_{c_i}}\Lambda_i$，$\Lambda_i$ 只依赖词内部步型 | 已证 | 任意奇数 $a\ge3,b>0$；Lean 当前以 $a=5$ 编译 |
| PH-2 | 首游程局部下界 $\Lambda_i\ge\Phi_{\mathrm{PH}}(t_i,r_i;m)$ | 已证 | $a=5$；清分母整数形式已编译 |
| QB-7 | C3 词刚性：非 $j=0$ 词只有首步 | 已证 | 条件 $(5/4-2^\delta)m>1/5$；Lean 已形式化矛盾核心 |
| QB-8 | 单次上升 + C3 链结构 | 已证 | QB-7 条件下；Lean 已形式化单调性与链结构 |
| GC-3 | 加速步模 3 闭包 | 已证 | $n'\equiv1-n$（$t$ 偶）/ $n-1$（$t$ 奇）；Lean 已编译 |
| GC-4 | C3 链闭式与残差 | 已证 | $2^T m=5^QN_1+A_{\mathrm{chain}}$，$m\equiv A_{\mathrm{chain}}2^{-T}\pmod{5^Q}$；Lean 已编译闭式、残差、逆元残差与 $Q\ge9$ 唯一性 |
| GC-42 | C3 起点按权重模 16 二分 | 已证 | $t_i=3\Rightarrow N_i\equiv11$，$t_i\ge4\Rightarrow N_i\equiv3\pmod{16}$；Lean 已编译 |
| GC-41 | $b=0$ 分支关闭 | 已证 | 全 C3 权重 $=3$ 时残差 $3m\equiv1\pmod{5^Q}$，框 A 内唯一奇候选 $260417$；Lean 已编译完整排除 |
| GC-43 | C3 链精确系数线性上界 | 已证 | $(C_0-B)m\le R_0+A_{\mathrm{chain}}/5^Q$；Lean 已编译清分母形式 |
| GC-7 清分母上界 | 上升段几何和、C3 几何尾、总 PMI 上界与 m 窄窗 | 已证 | `risePart rise c3 <= 4*5^P`、`24*geomTail(Q+1) <= 5*8^(Q+1)`、`gc7_pmi_cleared_bound: 3*pmiTotal <= 3*5^(P+1)+5*2^T`、`gc7_m_cleared_bound: 3*m*(2^T-5^P) <= 3*5^P+2^T`；Lean 已编译；GC-13 分支表已接入；13.1 的 Rat 重读在六个小 `P` 上由 `../lean/Gc7Window.lean` 的 `gc7_window_rat_check` 编译；完整 Real `δ` 重读由 `../lean/Td0Real.lean` 的 `gc7_real_window_delta`/`deltaCeil_eq` 编译 |
| GC-15 清分母上界 | 按 `U` 收紧的上升段 PMI 上界 | 已证 | `gc15_rise_all_one_bound: 3*risePart <= 5*5^P`、`gc15_risePart_bound: 3*5^U*risePart <= 15*5^(P+U)-10*5^P*4^U`；Lean 已编译 |
| GC-13 清分母核心 | 首游程上界证书、`t=1/t=2` 边界与 `U=0` 分支表 | 已证 | `gc13_allOK_check`、`gc13_t1_bound`、`gc13_t2_bound`、`gc13_u0_31/59/205/351/497/643`、`gc13_long_rise_contradicts`、`gc7_window_for_gc13`；Lean 已编译；TD-1 的 B1 刚化与尖盆地拆分由 `../lean/Td1.lean` 编译（`b1_201`、`basin_617_sharp`、`phase2_m_ge_201`）；52.15--52.16 清分母窗口等价由 `../lean/Td1Window.lean` 编译；52.21.2bis 的 `mt>=8/3` 精确 Rat 检查由 `../lean/Td1Phase2.lean` 编译（`phase2_delta_check`），G5' 的 Rat 记录检查由 `phase2_record_rat_check`/`phase2_tRat_ge_t31`/`phase2_tRat_ge_t59` 编译，B0 由 `b0_check`/`b0_spec` 编译，`phase2_upper_bound_check` 合成，派生 Rat 上界 `phase2_mt_ge_of_m_ge_617`/`phase2_mt_ge_of_m_ge_201`、B2 Rat 形式 `phase2_mt_ge_of_b2` 与 B1 桥 `phase2_b1_P_lt_59`/`phase2_b1_bridge`/`phase2_mt_ge_of_b2_of_201` 也已编译，阶段二 `G_up` 抽象 Rat 上界与精确 A/B `Rmax<U iff mt>G_up` 等价由 `../lean/Td0Phase2.lean` 的 `gup_lt_eight_thirds`/`mt_gt_gup_of_ge`/`aUpper_iff`/`bUpper_iff`/`upperAt_of_mt_ge` 编译，修正上分支 `upperBranch`/`upperBranch_of_mt_ge`/`aUpperCorrect_iff`/`bUpperCorrect_iff`/`phase2B_eq`/`upperBranchA_prop`/`upperBranchB_prop` 以及 44.2 词界模块 `../lean/RisingBound.lean`（`wordA_le_amaxWord`、`three_mul_amaxWord_add`、`amaxWord_div_eq_hmax`）也已编译；证书层收口由 `../lean/Td1Final.lean` 的 `td1_cert_components` 编译；实数 `δ` 重读由 `../lean/Td0Real.lean` 编译；链内插界由 `../lean/Td1Interp.lean` 闭合并经 `td1A_closed_of_chain`/`td1B_closed_of_chain` 接入最终窗口矛盾；`../lean/Td0CertBridge.lean` 已给出清分母字级证书与轨道/整循环方程；`Areq` 等价映射已由 `../lean/Td0CertBridge.lean`/`../lean/Td0Final.lean` 闭合并接到最终窗口矛盾；轨道到 `pos` 的成员性已由 `../lean/ScratchOrbit.lean` 编译，真实词 `wordA = auOfPos` 语义桥也已在同一文件编译（`auOfPos_cons_pos`、`wordA_eq_auOfPos_of_twosPositions`、`wordA_eq_auOfPos_of_twosPositions_dropLast`），52.17 同余系统已由 `../lean/Td0CertBridge.lean` 编译（`chainFirst_mod16_of_c3Exact_weight_three`、`chainFirst_mod64_of_c3Exact_weight_five`、`word_endpoint_mod16_of_mod16`、`word_endpoint_mod64_of_mod64`、`table_A_spec`/`table_B_spec`、`congruence_52_17_A`/`congruence_52_17_B`）；最终接线已由 `../lean/Td0Final.lean` 的 `td1A_cert_closed_of_word`/`td1B_cert_closed_of_word`、A/B 分支合成入口 `td0_cert_closed` 与打包接口 `Td0Data`/`td0_closed_of_data` 编译完成；阶段一两个下分支/特殊三元组由 `td0_A_special_false`/`td0_B_special_false` 闭合，`tableUpper_of_feasible_not_special` 将其余可行三元组送回 `td0_cert_closed` |
| HUB | 前缀调和上界 $\sum_{j\ge1}1/n_j$ | 已证 | 任意奇数 $a\ge3,b>0$ |
| Lmin-Q | 多局部极小下界 $m\ge1/(a(2^{\delta/Q}-1))$ | INVALID（方向错误） | 不作为证书 |
| S6ab | 最大局部极小下界 | 外部已证 | Simons 框架 |
| S7ab | 全局最小值下界 | 外部已证 | Simons 框架 |
| Uch | 链式 $P/Q$ 上界 | 已证 | $4<a<8$ |
| H4ab | t=1 游程同余 | 已证 | 任意奇数 $a\ge3,b>0$ |
| G5 | 连分数记录归约 | 已证 | $\lambda=\log_2 a$ 无理 |
| SF | S7+S4 区间筛 | 已证（必要条件） | $a=5$ 已实现 |
| LG1 | G1 长度多重集 DP | 已证（当前零排除） | $a=5$，$P\le643$ 已检查 |
| M16 | 模 16 首/次词同余 | 已证（当前零排除） | $a=5$，$P\le643$ 已检查 |
| M2h | 模 $2^{h(a)+1}$ 首词同余（M16 的一般形式） | 已证 | 任意奇数 $a\ge3,b>0$ |
| D1 | 精确和恒等式 $\sum d_i=P+1+s$ | 已证 | $T=\lceil P\lambda\rceil$ 的循环 |
| M2k | 模 $2^k$ 首词族（M2h 的 k 层族） | 已证（框架），逐 k 待查 | 任意奇数 $a\ge3,b>0$ |
| QG | 松弛缺口量化 $s=k-1-\sum q+\sum p$ | 已证 | $T=\lceil P\lambda\rceil$ 的循环 |
| MODp | 模 $p$ 循环方程分子条件 | 已证 | 任意 $p\nmid a$；7 可达加轨道条件 |
| G3 | 全局长度上界 | 已证 | $a=5$，外部常数 |
| CS | corner scan 计算排除（$n_0\le10^7$） | 外部计算证书 | $a=5$；16,19,22,25,31,59,205,497,643 覆盖，351 仅非本原重复 |
| ST-all | 全存活长度松弛最优分段障碍 | INVALID（Decimal 草稿，待精确整数化；仍缺支配引理） | $a=5$，Q=8..14；4647,8651,21306,97879 复现 20/20 |
| 分段障碍 | 97,879 松弛最优 | INVALID（Decimal 草稿，待精确整数化） | $a=5$，缺支配引理 |
| E | 进入方程 | 必要已证，充分未证 | 一般 $(a,b)$ |

---

## 1. 记号

$$
V_{a,b}(n)=\operatorname{oddpart}(an+b),\qquad
t(n)=v_2(an+b).
$$

$$
\lambda=\log_2 a,\qquad \alpha=\lambda-2,
\qquad g(a)=\lfloor\lambda\rfloor,\quad h(a)=\lceil\lambda\rceil.
$$

返回词：$Q$ 个，第 $i$ 个长度 $L_i$、权重 $S_i$、余量
$m_i=L_i\lambda-S_i$；$P=\sum L_i$、$T=\sum S_i$、
$\delta=T-P\lambda>0$；负余量词个数 $k$；全局最小值 $m=x_0$，
全局最大值 $M$；首步输出 $X_i=(aN_i+b)/2^{t_i}$。

---

## 2. 已证引理

### L0ab：长度刚性

**陈述。** 若 $Q\ge5$，则 $P\ge Q+2$。

**证明。** 长度 1 的返回词只有首步 $t_0\ge h(a)$，余量
$\lambda-t_0\le\lambda-h(a)<0$，故长度 1 的词必为负词，正词长度
至少 2。符号刚性给 $k\le Q-2$（全局最大值出口为负、入口为正、
最小值入口为负，二分结构，见 `cyclic_strings_5x1.md` 9.20--9.36）。
因此

$$
P=\sum L_i\ge2(Q-k)+k=2Q-k\ge Q+2.
$$

**适用范围。** 无条件（任意正循环，$Q\ge5$）。7 可达时 S1 再给
$Q\ge8$。

**$(5,1)$ 特化。** $Q=8\Rightarrow P\ge10$；$Q=9\Rightarrow P\ge11$；
$Q=14\Rightarrow P\ge16$。

**证书。** `verify_sound_x0_filter.py` /
`sound_x0_filter_certificate.txt`（L0 列）。

---

### V7ab：值域下界截断

**陈述。** 若循环的所有值 $\ge N_0$，则

$$
\delta<\frac{Q}{3N_0\ln2}.
$$

特别地，7 可达循环（所有值 $\ge7$）满足

$$
\delta<\frac{Q}{21\ln2}.
$$

**证明。** S4 给 $\delta<Q/(3x_0\ln2)$，而 $x_0\ge N_0$，故
$Q/(3x_0\ln2)\le Q/(3N_0\ln2)$。∎

**适用范围。** 任何循环值 $\ge N_0$ 的循环；对 7 可达目标取
$N_0=7$。注意这与已作废的
$\delta<\theta_Q=Q/(3\cdot10^6\ln2)$ 方向相反：$10^6$ 是 $x_0$ 的
上界（无效），$7$ 是 $x_0$ 的下界（有效）。

**$(5,1)$ 特化。** 7 可达时
$\delta<Q/(21\ln2)$；$Q=9$ 时阈值 $0.6185$，$Q=14$ 时阈值
$0.9618$。

**证书。** `verify_sound_x0_filter.py` /
`sound_x0_filter_certificate.txt`（V7 列）。

---

### G1 / G1+ / G1++

**陈述（G1）。**

$$
\sum_{i=1}^{Q}\lfloor L_i\lambda\rfloor\ge T-k.
$$

**陈述（G1+）。**

$$
\sum_{i=1}^{Q}\lfloor L_i\lambda\rfloor=\lfloor P\lambda\rfloor-s,
\qquad 0\le s\le k-1.
$$

**陈述（G1++，$4<a<8$）。**

$$
\sum_{i=1}^{Q}\lfloor\alpha L_i\rfloor=\lfloor\alpha P\rfloor-s,
\qquad
\sum_{i=1}^{Q}\{\alpha L_i\}=\{\alpha P\}+s.
$$

**证明。** 正词 $S_i\le\lfloor L_i\lambda\rfloor$，负词
$S_i\ge\lceil L_i\lambda\rceil$，求和并消去 $P\lambda$ 得 G1；
与 $T\ge\lceil P\lambda\rceil$ 合并得 G1+；$\lambda=2+\alpha$
代入得 G1++。详见 `general_analytic_constraints.md` 第 3--4 节。

**适用范围。** 任意循环；G1++ 需 $4<a<8$。

**$(5,1)$ 特化。** $\lambda=\log_2 5$，
$\alpha=\log_2(5/4)=0.321928\ldots$。

---

### d_i 整数刚性

**陈述。**

$$
d_i=S_i-L_i-\lfloor\alpha L_i\rfloor\in\mathbb Z,
\qquad d_i\le L_i\ (m_i>0),\quad d_i\ge L_i+1\ (m_i<0),
$$

$$
\sum_id_i=P+\{\alpha P\}+\delta+s\in\mathbb Z_{\ge P}.
$$

**证明。** 直接代入并求和。详见第 5 节。

**适用范围。** $4<a<8$；不依赖 7 可达。

---

### N'：负词单步上界

**陈述。** 对 $a=5,b=1$、$M\ge7$，

$$
-m_i=S_i-L_i\lambda
\le\log_2 M+\log_2\frac{36}{7}-2-\alpha L_i.
$$

一般 $(a,b)$：把 $\log_2(36/7)$ 换成 $\log_2(a+b/7)$。

**证明。** $S_i=t_0^{(i)}+(L_i-1)+b_i$，
$t_0^{(i)}\le\log_2(aM+b)$，$b_i\le L_i-1$。详见第 6 节。

**适用范围。** 任意正循环；常数逐 $(a,b)$ 取。

---

### H1ab / H2ab / Hab

**陈述（H1ab）。** 对任意返回词 $i$：

$$
L_i\ge2\implies X_i>\frac1{a(2^\delta-1)},
\qquad
L_i=1\implies N_i>\frac{b}{a(2^\delta-1)}.
$$

**陈述（H2ab）。** 产生全局最小值 $m$ 的返回词满足 $L_i\ge2$。

**陈述（Hab）。**

$$
m>\frac1{a(2^\delta-1)}.
$$

**证明。** $c_i=\log_2(1+A_i^{(a,b)}/(a^{L_i}N_i))$，$\sum_ic_i=\delta$，
故 $c_i<\delta$；$L_i\ge2$ 时
$A_i^{(a,b)}/a^{L_i}\ge2^{t_i}/a^2$ 且
$N_i=(2^{t_i}X_i-b)/a<2^{t_i}X_i/a$，推出
$X_i>1/(a(2^\delta-1))$。H2ab 用局部极小的 $t(m)\le g(a)$ 与
长度 1 词的 $t(m)\ge h(a)$ 矛盾。详见第 15 节。

**适用范围。** 任意奇数 $a\ge3$、$b>0$ 的正循环，无条件。

**$(5,1)$ 特化。**

$$
m>\frac1{5(2^\delta-1)}.
$$

**证书。** `verify_h1_candidate_exclusion.py` /
`h1_candidate_exclusion_certificate.txt`。

---

### PMI：精确前缀余量恒等式（新增）

**陈述。** 把循环旋转到全局最小值 $m=n_0$，设
$W_0=0$、$W_j=t_0+\cdots+t_{j-1}$、$M_j=j\lambda-W_j$，则

$$
\sum_{j=0}^{P-1}2^{-M_j}=5m(2^\delta-1).
$$

一般 $(a,b)$：

$$
\sum_{j=0}^{P-1}2^{-M_j}=\frac ab\,n_0(2^\delta-1).
$$

**证明。** 由 $2^Tm=5^Pm+A_{\mathrm{tot}}$ 与
$A_{\mathrm{tot}}=\sum_j5^{P-1-j}2^{W_j}$ 除以 $5^P$。
详见 `general_analytic_constraints.md` 第 17 节。

**推论 PMI-B（前缀余量条件）。** 框 A（$m\le10^6$）下，满足
$M_j\le0$ 的中间前缀数至多
$\lfloor5\cdot10^6(2^\delta-1)-1\rfloor$；对
$(97{,}879,227{,}268)$ 这是 $0$，故所有真前缀都满足
$W_j<j\lambda$。

**推论 PMI-C（HUB）。**

$$
\sum_{j=1}^{P-1}\frac1{n_j}
\le\frac{5(5m(2^\delta-1)-1)}{5m+1}.
$$

对 97,879 框 A 给出每个非最小值 $n_j>1.247\times10^6$，
并把 $t(m)=2$ 的情形压到 $m\in[997{,}840,10^6]$ 的窄窗。

**推论 PMI-D（与 S4 合并）。**

$$
\delta\ln2
<\frac13\left(\frac1m+\frac{5(5m(2^\delta-1)-1)}{5m+1}\right).
$$

**Lmin-Q 审计。** 候选引理
$m\ge1/(5(2^{\delta/Q}-1))$ 的推导方向错误：$X_i\ge m$ 只能给出
$\log_2(1+1/(5X_i))\le\log_2(1+1/(5m))$，不能推出
$\delta\ge Q\log_2(1+1/(5m))$。该候选**不作为证书**，脚本
`verify_lminq_exclusion.py` 不运行、不落盘。

**Lean 形式化。** `../lean/Pmi.lean` 已把 PMI 的代数整式形式、
PMI-B 的坏前缀计数界与预算推论形式化并通过编译：
`pmi_algebraic`、`pmi_b_count`、`pmi_b_no_bad_prefix`；
公理仅 `propext`、`Quot.sound`，无 `sorry`/自定义公理。

### PH-1：词贡献分解（新增）

**陈述（PH-1）。** 设词 $i$ 从 $j=c_i$ 开始、长为 $L_i$，词内
偏移 $k$ 处

$$
M_{c_i+k}=M_{c_i}+k\lambda
-\bigl(t_i+t_{c_i+1}+\cdots+t_{c_i+k-1}\bigr).
$$

因此

$$
C_i=\sum_{j=c_i}^{c_{i+1}-1}2^{-M_j}=2^{-M_{c_i}}\Lambda_i,
$$

其中 $\Lambda_i$ 只依赖该词内部步型，不依赖 $P$、$c_i$ 与词序。

**证明。** 由 $W_{c+k}=W_c+W_w(k)$（词内前缀权重）把
$2^{-M_{c+k}}$ 分解为全局首项因子与局部因子，再求和。详见
`ph_qb_gc_chain.md` 第 3 节。

**Lean 形式化。** `../lean/PhOne.lean` 以清分母整式形式编译了
PH-1：`prefixWeight_segment`（$W_{c+k}=W_c+W_w(k)$）、
`ph1_word_decomposition`（$C=2^{W_c}\Lambda$）与
`localLambda_eq_of_wordWeights_agree`（局部因子只依赖词内部
步型）。公理仅 `propext`、`Quot.sound`，无 `sorry`/自定义公理。

### PH-2：首游程局部下界（新增）

**陈述（PH-2）。** 设词以 C3 步 $t$ 开头，随后恰有 $r$ 个
$t=1$ 步，$\alpha=\lambda-1$，则

$$
\Lambda_i\ge
\Phi_{\mathrm{PH}}(t,r)=
\begin{cases}
1,&r=0,\\
1+2^{t-\lambda}\dfrac{1-2^{-r\alpha}}{1-2^{-\alpha}},&r>0.
\end{cases}
$$

**证明。** 词内第 $k$ 个 $t=1$ 步（$1\le k\le r$）的局部因子为
$2^{t+k-1-k\lambda}=2^{t-\lambda}2^{-(k-1)\alpha}$，构成等比
数列；C3 首步的局部因子为 $1$，后续未计入步贡献非负。详见
`ph_qb_gc_chain.md` 第 4 节。

**Lean 形式化。** `../lean/PhTwo.lean` 以清分母整式形式编译了
PH-2。因为 $2^{-\alpha}=2/5$，上下界两边乘 $3\cdot5^r$ 后等价于

$$
3\,\mathrm{localLambda}(\mathrm{firstRunWord}(t,r)\mathbin{++}\mathrm{tail})
\ge5^{|\mathrm{tail}|}\bigl(3\cdot5^r+2^t(5^r-2^r)\bigr).
$$

主要定理为 `localLambda_firstRun_eq`（规范首游程词的精确等比
恒等式）、`ph2_lower_bound`（尾部非负项的单调下界）与
`ph2_lower_bound_of_firstRunPrefix`（按实际词长的形式）。公理仅
`propext`、`Quot.sound`，无 `sorry`/自定义公理。

### QB-7/QB-8：尖峰结构（新增 Lean 形式化）

**QB-7 陈述。** 设 $m\ge7$、PMI-B 成立且
$(5/4-2^\delta)m>1/5$，则除唯一含 $j=0$ 步的词外，每个 C3
返回词都只有首步：$r_i=0$，$X_i$ 本身就是下一个 C3 起点。

**QB-8 陈述。** 在 QB-7 条件下，$c_{i+1}=c_i+1$，
$m\to N_1$ 只有 $t=1/2$ 步，$N_1\to\cdots\to N_Q\to m$ 都是单个
C3 步，且 C3 起点严格下降。

**Lean 形式化。** `../lean/Qb.lean` 把 QB-7 的解析矛盾写成
`qb7_core`/`qb7_no_internal_data`：当 $q=2^\delta=2^T/5^P$ 时，条件
$mq+1/5<(5/4)m$ 与内部步恒等式
$f(m+y)=m+x+e$（$f=2^\Delta\ge5/4$，$m+x\le mq$，$e\le1/5$）
不能同时成立。QB-8 的结构部分形式化为
`c3_step_lt`、`rise_step_gt`、`c3_chain_strictlyDecreasing` 与
`startsFrom_consecutive_of_allOne`，并组装成
`qb8_structure`。公理为
`propext`、`Quot.sound` 与 `Classical.choice`（仅 `Rat` 层），无
`sorry`/自定义公理。

---

### S6ab / S7ab（Simons 外部）

**陈述（S6ab）。**

$$
\max_iX_i>\frac{2^{P/Q}}{a-1}.
$$

**陈述（S7ab）。** 对 $x_i\ge7$，

$$
x_0>A_{a,b,Q}\,2^{P/(Q\rho^{Q-1})},
$$

其中 $c_{a,b}(7)=((a-2)+b/7)/(2(a-2))^{1/\rho}$，
$C=c^{\rho/(\rho-1)}$，
$A_{a,b,Q}=C^{-1}(a-1)^{-1/\rho^{Q-1}}$。

**$(5,1)$ 特化。** $a-1=4$，
$c=(22/7)/6^{1/\rho}$，$C=1.9270\ldots$，
$A_Q=C^{-1}4^{-1/\rho^{Q-1}}$。

**来源。** `external_simons_translation.md` S6/S7；
`verify_global_P_bound.py`。

---

### Uch：链式 $P/Q$ 上界

**陈述。** 局部极小链 $X_{i+1}<B_{a,b}X_i^\rho$ 迭代 $Q-1$ 步，
与 $M>2^{P/Q}/(a-1)$ 合并得

$$
\frac PQ<\rho^{Q-1}\log_2 m
+2+\log_2\frac43
+\frac{\rho^{Q-1}-1}{\rho-1}\log_2B_{a,b}.
$$

框 A（$x_0\le10^6$）下用 $\log_2 m\le\log_2 10^6$。

**证明。** 见 `general_analytic_constraints.md` 第 7 节。

**适用范围。** $4<a<8$；常数逐 $(a,b)$ 取。

---

### H4ab：t=1 游程同余

**陈述。** 若从 $n$ 出发连续 $r$ 步 $t=1$，则

$$
(a-2)n+b\equiv0\pmod{2^r}.
$$

**证明。** 闭式

$$
2^r n_r=a^r n+b\frac{a^r-2^r}{a-2}.
$$

乘 $a-2$ 并对 $2^r$ 取模：左边为 0，右边
$\equiv a^r((a-2)n+b)\pmod{2^r}$；$a^r$ 奇、模 $2^r$ 可逆，得证。

**$(5,1)$ 特化。** $3n+1\equiv0\pmod{2^r}$。

**适用范围。** 任意奇数 $a\ge3$、$b>0$，无条件。

---

### G5：连分数记录归约

**陈述。** 设 $\lambda$ 无理，$r\le P$ 是最大“上方记录”分母，则

$$
\lceil P\lambda\rceil-P\lambda\ge\lceil r\lambda\rceil-r\lambda.
$$

**证明。** 若 $d(P)<d(r)$，取 $d(P')$ 最小者得新记录，矛盾。
详见 `global_P_bound.md` 第 4 节。

**适用范围。** 任意 $\lambda=\log_2 a$ 无理（$a$ 非 2 的幂）。

**SURV-RAY 扩展。** 上方记录分母的半收敛射线参数化、$T$ 与
$\delta$ 的线性闭式、Lucas 递推与全局方程射线形式见
`surv_ray.md`；`Q=8..100` 完整幸存清单（236 条）见
`surv_ray_certificate.txt`，生成器为 `verify_surv_ray.py`。

---

### SF：S7+S4 区间筛（必要条件）

**陈述。** 对每个记录长度 $P$，令
$\delta(P)=\lceil P\lambda\rceil-P\lambda$；循环存在则

$$
A_Q\,2^{P/(Q\rho^{Q-1})}
<\frac{Q}{3\,\delta(P)\ln2}.
$$

若某记录 $r$ 违反 (SF)，则 $[r,\text{下一记录})$ 内所有 $P$ 都
违反。

**证明。** S7 下界 $x_0>A_Q2^{P/(Q\rho^{Q-1})}$，S4 上界
$x_0<Q/(3\delta\ln2)$；$\delta(P)\ge\delta(r)$ 且 $x_0$ 下界随
$P$ 递增。注意：这是必要条件，不能作为“候选表”的充分枚举。

**证书。** `verify_sound_x0_filter.py` /
`sound_x0_filter_certificate.txt`；
`verify_x0_dichotomy.py` / `x0_dichotomy_certificate.txt`。

---

### LG1：G1 长度多重集过滤（当前零排除）

**陈述。** 对候选 $(Q,P)$、$T=\lceil P\lambda\rceil$，若不存在长度
多重集 $L_1,\dots,L_Q$（$\sum L_i=P$，长度 1 的词数 $\le k$）使

$$
\sum_i\lfloor L_i\lambda\rfloor\ge T-k
$$

对某个 $k\in[2,Q-2]$ 成立，则该候选被 G1 排除。

**实现。** 用精确整数 DP（$2^s<5^L$ 判 floor）计算每个
$(Q,P)$ 的最大 floor 和；证书
`survivor_length_filter_certificate.txt`（脚本
`verify_survivor_length_filter.py`）。

**结果（负结果）。** 对当前全部 V7 小存活长度
$P\le643$、$Q=8..14$ 检查后，**没有新增排除**；(31,72) 的旧
可行 $k$ 表也精确复现（RESULT: PASS）。这说明这些长度不能靠
G1 单独排除，下一步需要权重/类型层。

**为什么零排除（解析观察）。** 对 $4<a<8$，

$$
\lfloor L_i\lambda\rfloor=2L_i+\lfloor\alpha L_i\rfloor,
$$

所以最大化 $\sum_i\lfloor L_i\lambda\rfloor$ 等价于最大化
$\sum_i\lfloor\alpha L_i\rfloor$。对固定 $\sum L_i=P$，
$\lfloor\alpha L\rfloor/L$ 在“上方记录分母”处取局部最大值
（$\{L\alpha\}$ 靠近 0 的长度）；V7 存活长度恰好就是这些高效
记录分母（31,59,205,351,497,643,4647,8651,21306,97879）。
因此 G1 层在这些长度上必然可行，排除必须来自权重层（含
$t_0=v_2(5N+1)$ 的 2-adic 刚性）或入口方程。

---

### M16：模 16 首/次词同余（当前零排除）

**陈述。** 对 $a=5,b=1$，$A_i\bmod16$ 只依赖 $L_i$ 与首步权重
$t_0$ 是否等于 3：

$$
A_i\equiv5^{L_i-1}+[t_0=3]\cdot8\cdot5^{L_i-2}\pmod{16}.
$$

总闭合分子

$$
A_{\mathrm{tot}}=\sum_i2^{\text{前缀 }S_i}5^{\text{后缀 }L_i}A_i
$$

模 16 时前缀权重 $\ge4$ 的项消失，只剩首词与（当 $S_0=3$ 时）
次词：

$$
A_{\mathrm{tot}}\equiv5^{P-L_0}A_0
+[S_0=3]\cdot8\cdot5^{P-L_0-L_1}A_1\pmod{16}.
$$

必要条件是 $A_{\mathrm{tot}}\in\{3D,11D\}\pmod{16}$，其中
$D=2^T-5^P\equiv-5^P\pmod{16}$（对应 $N_0\equiv3\pmod8$）。

**实现。** `verify_mod16_firstword.py` /
`mod16_firstword_certificate.txt` 对首/次词做声音扫描，尾词用
区间可加性处理。

**结果（负结果）。** 对 $P\le643$、$Q=9..11$ 的 V7 存活长度全部
通过（首词与次词都有命中），模 16 层也没有新增排除。这与 G1
零排除一致：记录分母正是各 Diophantine 层都可实现的位置。

**一般形式（M2h）。** 设 $h=h(a)=\lceil\log_2 a\rceil$。因为每个
返回词权重 $S_i\ge L_i+h-1\ge h$，所以模 $2^h$ 下除首词外全部
前缀项 $2^{S_i}\equiv0$：

$$
A_{\mathrm{tot}}\equiv a^{P-L_0}A_0\pmod{2^h}.
$$

首词分子模 $2^{h+1}$ 只依赖 $L_0$ 与首步权重是 $t_0=h$ 还是
$t_0\ge h+1$：

$$
A_0\equiv a^{L_0-1}+[t_0=h]\cdot2^h\cdot a^{L_0-2}\pmod{2^{h+1}}.
$$

当第二个词的前缀权重 $S_0=h$ 时，模 $2^{h+1}$ 下还会多一项
$2^h a^{P-L_0-L_1}A_1$。必要同余为

$$
A_{\mathrm{tot}}\equiv N_0\bigl(2^T-a^P\bigr)\pmod{2^{h+1}},
$$

其中 $N_0\equiv-ba^{-1}\pmod{2^h}$ 是访问类 $C_h$ 的剩余类。

**$(5,1)$ 特化。** $h=3$，模 $2^4=16$；
$N_0\equiv-5^{-1}\equiv3\pmod8$，即 M16。

**常数来源。** 只依赖 $h(a)$ 与 $a\bmod2^{h+1}$；这是对一般
$(a,b)$ 成立的参数化形式，5x+1 专用部分只是数值。

---

### D1：精确和恒等式（$\sum d_i=P+1+s$）

**陈述。** 若 $T=\lceil P\lambda\rceil$（即 $\delta=T-P\lambda$，
$\{P\lambda\}=1-\delta$），则

$$
\sum_{i=1}^{Q}d_i=P+1+s,
\qquad 0\le s\le k-1.
$$

**证明。** 第 5 节恒等式 (D) 给
$\sum_id_i=P+\{\alpha P\}+\delta+s$。因为
$\alpha P=P\lambda-2P$，故
$\{\alpha P\}=\{P\lambda\}=1-\delta$，代入即得。∎

**推论。** 由于负词 $d_i\ge L_i+1$、正词 $d_i\le L_i$，求和给出

$$
\sum_{\text{负}}(d_i-L_i-1)-\sum_{\text{正}}(L_i-d_i)
=s-(k-1)\le0,
$$

即“正词松弛量总和”至少等于“负词超额量总和”。紧边界分支
（$s=k-1$）等价于所有正词 $d_i=L_i$、所有负词 $d_i=L_i+1$。

**适用范围。** 任意循环，$T=\lceil P\lambda\rceil$（候选即如此）。

---

### M2k：模 $2^k$ 首词族

**陈述。** 对任意 $k\ge h(a)+1$，总闭合分子满足

$$
A_{\mathrm{tot}}\equiv
\sum_{i:\ \text{前缀 }S_i<k}2^{S_i}a^{P-L_0-\cdots-L_i}A_i
\pmod{2^k}.
$$

即模 $2^k$ 下只有前缀权重 $<k$ 的首若干个词参与，参与词数
$\le k$（每个词权重至少 $h(a)$）。

**证明。** 与 M2h 相同：前缀权重 $\ge k$ 的项含因子
$2^{S_i}\equiv0\pmod{2^k}$。∎

**$(5,1)$ 特化。** $h=3$，$k=4$ 即 M16；$k=5,6,7,\dots$ 给出
M32、M64 等更强的有限同余必要条件。M16 已实现（零排除）；
更高 $k$ 是同一引理族的有限扩展。M32（$k=5$）已实现并检查
（`verify_mod32_firstword.py` / `mod32_firstword_certificate.txt`，
18 秒，四个存活长度全部通过，零排除）；$k=6,7,\dots$ 待检查。

---

### QG：松弛缺口量化

**陈述。** 定义正词松弛 $q_i=L_i-d_i\ge0$、负词超额
$p_i=d_i-(L_i+1)\ge0$。则

$$
s=k-1-\sum_{\text{正}}q_i+\sum_{\text{负}}p_i,
$$

且 $q_i=m_i-\{\alpha L_i\}$、$p_i=\{\alpha L_i\}-m_i-1$。

**证明。** 由 $d_i=L_i+\{\alpha L_i\}-m_i$ 与
$\sum d_i=P+1+s$ 直接代入。∎

**应用。** 非紧边界（$s<k-1$）要求正词总松弛大于负词总超额。
若某个候选的所有可行词型都使 $\sum q_i>\sum p_i$，则
$s<k-1$ 被强制；结合其它层可把搜索限制到非紧边界。

---

### MODp：模 $p$ 循环方程分子条件

**陈述。** 设奇素数 $p\nmid a$，$D=2^T-a^P$，$A_w$ 为整词分子。
循环方程 $D N_0=A_w$ 给出：

$$
p\mid D\implies A_w\equiv0\pmod p;
$$

若 $p\nmid D$，则

$$
N_0\equiv A_wD^{-1}\pmod p,
$$

对 7 可达循环还要求 $N_0$ 属于 7 在 $V_{a,b}$ 下的模 $p$ 轨道。

**$(5,1),p=3$ 特化。** $5\equiv2\equiv-1\pmod3$，故

$$
D\equiv(-1)^T-(-1)^P
=(-1)^P\bigl[(-1)^{T-P}-1\bigr]\pmod3,
$$

即 $3\mid D$ 当且仅当 $T-P$ 为偶数。此时

$$
A_w\equiv\sum_{j=0}^{P-1}(-1)^{P-1-j+W_j}\pmod3,
$$

必须 $\equiv0$。记 $N_-=\#\{j:P-1-j+W_j\text{ 奇}\}$，等价于
$P-2N_-\equiv0\pmod3$，即 $N_-\equiv2P\pmod3$。

**适用范围。** 任意循环无条件；7 可达时附加模 $p$ 轨道条件。
这是对“模素因子层”的具体化：$p\mid D$ 时分子必被 $p$ 整除，
$p\nmid D$ 时把入口值与 7 的轨道接上。

**对四个存活长度的检查（<1 分钟）。** 小模检查给出：

| $(P,T)$ | 使 $p\mid D$ 的小素因子 | $v_p(D)$ |
|---|---|---|
| (4647,10790) | 31 | 1 |
| (8651,20087) | 3 | 1 |
| (21306,49471) | 17 | 1 |
| (97879,227268) | 59, 379 | 1, 1 |

7 的真实模 $p$ 轨道（用实际轨道值约化）对 $p\le59$ 覆盖全部
剩余类，$p=379$ 覆盖 378/379 个。因此 $p\le59$ 时 MODp 的轨道
分支是平凡可满足的；$p=379$ 时只差一个剩余类，需要模
$379^2$ 的词结构检查（该检查不在 1 分钟限制内，留作后续）。

**MODp-lift（$v_p(D)=1$ 的提升条件）。** 若 $v_p(D)=1$，则
$A_w\equiv0\pmod p$ 且

$$
N_0\equiv\frac{A_w/p}{D/p}\pmod p.
$$

7 可达还要求该值落在 7 的模 $p$ 轨道内。这是 MODp 的加强版，
证明同前（$p\mid D$ 时两边除以 $p$ 再取模 $p$）。

---

### CS：corner scan 计算排除（外部证书）

**陈述。** `corner_scan_5x1.py` 对每个长度 $L$、全部奇数
$n_0\le10^7$ 用定理 5.17 的级联构造生成唯一候选词，并独立验证
循环方程。扫描文件给出：

| $L$ | 结果 |
|---|---|
| 16, 22 | 只有 {1,3} 的非本原重复（`corner_scan_L16_25.txt`，L=16..25） |
| 19, 25 | 零循环（同文件） |
| 31, 59 | 零循环（`corner_scan_results.txt`，L=31..100） |
| 205 | 零循环（`corner_scan_results_L201_300.txt`） |
| 351 | 6 条非本原重复（三个已知循环的重复），本原数 0 |
| 497, 643 | 零循环（`corner_scan_L497.txt`、`corner_scan_L643.txt`） |

另：本轮补跑了 `corner_scan_5x1.py 16 25 10000000 8
corner_scan_L16_25.txt`（22 秒，28 个循环全部非本原，本原数 0），
$L=16,19,22,25$ 现在有独立落盘证书。

**应用到 7 可达。** 声音框 A 给 $x_0\le10^6<10^7$；7 不进入三个
已知循环，故非本原重复也不可能。因此
$P\in\{16,19,22,25,31,59,205,351,497,643\}$ 全部排除。特别地
$(31,72)$ 家族（$P=31$）也被计算排除。

**性质。** 这是计算证书，不是纯解析证明；完备性依赖定理 5.17
级联唯一性与 `corner_scan_5x1.py` 的独立循环方程复核。核验脚本
`apply_corner_scan_exclusions.py` /
`corner_scan_exclusion_certificate.txt`（RESULT: PASS）。

---

### ST-all：全存活长度的松弛最优分段障碍（当前 INVALID）

**陈述（草稿）。** 把 97,879 的 H4 分段同余障碍参数化到全部 V7 存活长度
（脚本 `verify_survivor_staging.py`，证书
`survivor_staging_certificate.txt`）。对每个
$(Q,P)\in\{8,\dots,14\}\times\{4647,8651,21306,97879\}$，首游程
$r_1=1,\dots,20$ 的松弛最优序列都迫使唯一 $m\bmod2^R$ 落在
$(7,10^6]$ 之外：**复现 20/20 全部被阻**。

97,879 的旧 `shared_candidate_staging_certificate.txt` 曾写“恰好
8 段”，该表述对 $r_1=1..6$ 不成立（实际需 9 段）。脚本
`verify_shared_candidate_staging.py` 已改为 greedy-until-target，
但 `shared_candidate_staging_certificate.txt` 与
`survivor_staging_certificate.txt` 仍用 80 位 Decimal `ln` 为数千位
$n$ 取 `floor(log2(3n))`，没有精确性保证；当前标记
**INVALID（待精确整数化）**，只作复现线索，不作封闭依据。

$P=16,19,22,25$ 的目标增长为负（不需要增长），不受此障碍覆盖；
它们由 CS 的 $L\le30$ 扫描覆盖。

**限制。** 只覆盖松弛最优分段；非最优分段仍需支配引理。因此
4647,8651,21306,97879 只在“支配引理成立”条件下被排除，不能
视为已证明。

**更深层无效性（2026-08-05 复核）。** 即使把 run 向量改成精确
整数 $v_2(3n+1)$，该障碍仍**不是证书**：run 向量是沿“上端
$n=999999$ 的人工轨迹”生成的，而 `solve_m` 解出的唯一 $m$ 的
真实轨迹一般并不具有这些 run 长度。也就是说“对这组 run 的
同余无解”并不排除“某个 $m$ 的实际 run 序列可行”。ST-all
的 20/20 只是草稿/启发式，不能作为“松弛最优被排除”的证明；
需要支配引理把 run 向量证明为所有可行序列的上界后，才能变成
声音证书。

**为什么朴素支配不成立（负结论）。** 一次最大 t=1 游程后的值
$F_1(m)=2^{\lambda r_1}m+(2^{\lambda r_1}-1)/3$ 对 $m$ **不是**
单调的：$m=349525$ 时 $3m+1=2^{20}$（$r_1=20$），
$F_1\approx2^{44.8}$；而 $m'=349527$ 时 $3m'+1$ 的
$v_2=1$，$F_1\approx2^{21.5}$。因此“从区间上端 $10^6$ 出发的
松弛序列支配所有可行序列”不成立，ST-all 不能直接覆盖这类高
$v_2$ 起点。支配引理必须利用 $v_2(3n+1)$ 的剩余类结构，或对
有限个高 $v_2$ 起点（如 $r_1=20$ 在 $(7,10^6]$ 内唯一
$m=349525$）逐点解析处理。

---

### G3：全局长度上界

**陈述。** 对 $a=5,b=1$、$Q\ge8$，存在可计算 $P_Q$ 使
$P<P_Q$；$P_Q$ 是

$$
\log_2 A_Q+\frac{P_Q}{Q\rho^{Q-1}}
=\log_2 Q-\log_2(3\ln2)-\log_2\delta_{\mathrm{lb}}(P_Q)
$$

的解，$\delta_{\mathrm{lb}}$ 为 Laurent 下界。

**来源。** S7 + S4 + S9；常数 $24.34\ln5$ 是 5x+1 专用。

**证书。** `verify_global_P_bound.py` /
`global_P_bound_table.txt`。

---

### 分段障碍（97,879，当前 INVALID）

**陈述（草稿）。** 对 $(P,T)=(97{,}879,227{,}268)$ 与 $Q=9,\dots,14$，
松弛最优分段（按 $r_1$ 动态到目标，r1=1..6 为 9 段、其余为 8 段）
复现 20/20 个唯一 $m\bmod2^R$ 落在 $(1,10^6]$ 之外；由于 run 向量
由 80 位 Decimal 近似生成，当前 **INVALID（待精确整数化）**。

**证明/证书。** `verify_shared_candidate_staging.py` /
`shared_candidate_staging_certificate.txt`；显式剩余类逐行写入。

**限制。** 只覆盖 97,879 的松弛最优分段；非最优分段需支配引理，
且其他存活长度未处理。**不关闭任何 $Q$。**

---

### E：进入方程

**陈述。** 7 最终进入周期词 $w$ 的必要形式：

$$
\bigl(a^M n+A_u^{(a,b)}\bigr)\bigl(2^T-a^P\bigr)
=2^{S_u}A_w^{(a,b)}.
$$

**适用范围。** 必要方向任意 $(a,b)$；充分方向需一般级联唯一性，
当前只在 5x+1 声明。

---

## 3. 常数来源：5x+1 专用 vs 一般成立

| 常数/公式 | 一般 $(a,b)$ | 5x+1 专用 |
|---|---|---|
| $g(a),h(a)$ | $\lfloor\log_2 a\rfloor,\lceil\log_2 a\rceil$ | $2,3$ |
| $\alpha$ | $\log_2(a/4)$ | $\log_2(5/4)$ |
| 负词单步常数 | $\log_2(a+b/7)$ | $\log_2(36/7)$ |
| 链式 $B_{a,b}$ | $((a-2)+b/7)^\rho/(2(a-2))$ | $(22/7)^\rho/6$ |
| 链式 $C_{a,b}(7)$ | $c^{\rho/(\rho-1)}$ | $1.9270\ldots$ |
| S6 分母 | $a-1$ | $4$ |
| S7 $A_{a,b,Q}$ | 一般公式 | $A_Q$ |
| 游程同余 | $(a-2)n+b\equiv0$ | $3n+1\equiv0$ |
| G5 | 任意 $\lambda$ 无理 | $\lambda=\log_2 5$ |
| Laurent S9 | 需逐 $(a,b)$ 重算 | $24.34\ln5$ |
| $\theta_Q=Q/(3\cdot10^6\ln2)$ | 无（已作废） | 旧错误过滤 |
| $D=2^T-a^P$ 因子分解 | 逐例重算 | $419\cdot122021\cdot1286088921629$ |
| 7 可达 / $n_0=7$ | 无 | 专用 |

---

## 4. 对 (31,72) 的影响

$(31,72)$ 是 $P=31,T=72$ 的候选族。当前声音状态：

> **计算层覆盖（CS）**：corner scan 对全部奇数 $n_0\le10^7$
> 穷举 $L=31$，零循环；框 A 给 $x_0\le10^6<10^7$，因此
> $(31,72)$ 家族已被计算排除（`corner_scan_exclusion_certificate.txt`）。
> 下面的分支表是解析/证书层的历史状态；最终以 CS 覆盖为准。

- L0、V7、Hab 都不排除它（$P=31\ge Q+2$，$\delta=0.0202$）；
- (SF) 下 $P=31$ 对每个 $Q\ge5$ 都是存活长度；
- 旧 G4/唯一候选路径不能覆盖它；
- 97,879 的分段障碍与 $(31,72)$ 无关；
- $Q=1,2,3,4$ 已由旧 tight/sound 证书封闭；
- $Q=5,6,7$ 由 Simons S1 覆盖（7 不命中三个已知循环）；
- 声音 tight 分支（G1 取等、边界词型）已由
  `verify_tight_sound.py` 封闭的 $(Q,k)$：

  $$
  (6,2),(7,2),(8,3),(9,3),(10,3),(11,4),(13,5),(14,6).
  $$

- 其余 $(31,72)$ 分支仍开放：

  | $Q$ | 可行 $k$ | 已封闭 | 仍开放 |
  |---|---|---|---|
  | 8 | 3,4,5,6 | 3 | 4,5,6 |
  | 9 | 3,4,5,6,7 | 3 | 4,5,6,7 |
  | 10 | 3..8 | 3 | 4..8 |
  | 11 | 4..9 | 4 | 5..9 |
  | 12 | 5..10 | 无 | 5..10 |
  | 13 | 5..11 | 5 | 6..11 |
  | 14 | 6..12 | 6 | 7..12 |

  注意：即使已封闭的 $(Q,k)$，也只覆盖 tight 分支；非 tight
  分支（$s<k-1$）仍需单独处理。

---

## 5. 脚本与证书路径

| 脚本 | 证书 |
|---|---|
| `verify_global_P_bound.py` | `global_P_bound_table.txt` |
| `verify_sound_x0_filter.py` | `sound_x0_filter_certificate.txt` |
| `verify_x0_dichotomy.py` | `x0_dichotomy_certificate.txt` |
| `verify_q8_exclusion.py` | `q8_exclusion_certificate.txt` |
| `verify_q5_q14_reduction.py` | `q5_q14_reduction_certificate.txt` |
| `verify_unified_record_screening.py` | `unified_record_screening_certificate.txt` |
| `verify_h1_candidate_exclusion.py` | `h1_candidate_exclusion_certificate.txt` |
| `verify_q9_candidate_bounds.py` | `q9_candidate_bounds.txt` |
| `verify_t1_run_lemma.py` | `t1_run_lemma_certificate.txt` |
| `verify_q9_staging_obstruction.py` | `q9_staging_obstruction_certificate.txt` |
| `verify_shared_candidate_staging.py` | `shared_candidate_staging_certificate.txt` |
| `verify_survivor_length_filter.py` | `survivor_length_filter_certificate.txt` |
| `verify_mod16_firstword.py` | `mod16_firstword_certificate.txt` |
| `verify_mod32_firstword.py` | `mod32_firstword_certificate.txt` |
| `apply_corner_scan_exclusions.py` | `corner_scan_exclusion_certificate.txt` |
| `verify_survivor_staging.py` | `survivor_staging_certificate.txt` |
| `verify_tight_sound.py Q k` | `tight_Q{Q}_k{k}_sound_certificate.txt` |

---

## 6. 结果与卡点

**已证明（声音）：** L0ab、V7ab、G1/G1+/G1++、d_i、N'、
H1ab/H2ab/Hab、PMI（精确前缀余量恒等式）、HUB（前缀调和上界）、
H4ab、G5、SF（必要条件）、Uch；外部证明 S1、S2'、S4、S6、S7、
G3。

**新审计：** 候选 Lmin-Q（
$m\ge1/(5(2^{\delta/Q}-1))$）方向错误，**不作为证书**；
`verify_lminq_exclusion.py` 不运行、不落盘。

**已约化：** $Q=9..14,16,18,23,25,29$ 的 $x_0>10^6$ 侧关闭；
Hab 排除 $\delta$ 很小的长度（如 1,936,274、15,392,313）；
L0 排除 $P<Q+2$ 的长度；V7ab 排除
$\delta\ge Q/(21\ln2)$ 的长度（Q=9..11 的存活记录从 25--28 个
降到 10 个）；CS 计算证书再排除
16,19,22,25,31,59,205,351,497,643（$n_0\le10^7$ 穷举），
Q=8 剩 3 个、Q=9..14 各剩 4 个；
ST-all 再对 4647,8651,21306,97879 全部 $Q=8..14$ 给出松弛最优
20/20 障碍（部分：缺支配引理）。

**仍开放：**

1. $x_0\le10^6$ 侧在 CS 后只剩 4647,8651,21306,97879
   （Q=8 为前三个）；ST-all 对它们全部 $Q=8..14$ 给出松弛最优
   20/20 障碍，但需要支配引理；
2. 支配/近最优引理（把松弛最优障碍升级为全排除）仍是实质卡点；
   PMI-B 前缀余量（见 `general_analytic_constraints.md` 17.4）把同一
   问题压成“真前缀全部低于 $j\lambda$”的路径下界，是当前更小的
   开放候选；
3. $Q=15,17,19..22,24,26..28,30$ 的 $x_0>10^6$ 记录；
4. E 的充分方向、L\* 入口边界排斥。

**卡点：** 支配引理；CS 是计算证书；4647,8651,21306,97879 的
排除目前只覆盖松弛最优分段（20/20）。
