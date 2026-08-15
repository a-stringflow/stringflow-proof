# SURV-EX：幸存射线整族排除

日期：2026-08-06

目标：证明 `surv_ray_certificate.txt` 中的 236 条半收敛射线记录
不可能是 7 可达 QB-8 循环，从而把 53.4 从条件定理升级为无条件
定理。本文按 S-X1..S-X4 组织；凡未闭合的子引理都明确标注为
族级阻塞，不冒充证明。

## 1. S-X1：b 窗口的射线闭式

沿用 SURV-RAY 记号：对射线

$$
P_m=d_{k-1}+m d_k,\qquad
T_m=n_{k-1}+m n_k,
$$

设 $Q\ge8$，$L=P_m-Q$，

$$
K=T_m-P_m-2Q
=(n_{k-1}-d_{k-1})+m(n_k-d_k)-2Q.
$$

令 $U(b)=K-b$ 为上升段中 `t=2` 的步数。QB-8 与 52.11/52.12
给出两类族：

**A 族**（$t_{\mathrm{last}}=1$，$t_1=3$）：

$$
1\le b,\qquad 0\le U(b)\le L-1.
$$

即

$$
b_{\min}^{\mathrm A}(Q,k,m)=\max(0,K-L+1),\qquad
b_{\max}^{\mathrm A}(Q,k,m)=K,
$$

$$
b_{\min}^{\mathrm A}=T_m-2P_m-Q+1,\qquad
b_{\max}^{\mathrm A}=T_m-P_m-2Q.
$$

**B 族**（$t_{\mathrm{last}}=2$，$t_1=5$）：

$$
2\le b,\qquad 1\le U(b)\le L.
$$

即

$$
b_{\min}^{\mathrm B}(Q,k,m)=\max(2,K-L),\qquad
b_{\max}^{\mathrm B}(Q,k,m)=K-1.
$$

**单调性。** 对固定 $Q,k$，

$$
\frac{d}{dm}K=n_k-d_k>0,
$$

而

$$
K-L=T_m-2P_m-Q
$$

的导数为 $n_k-2d_k>0$，故 A/B 两族的 $b_{\min}$、$b_{\max}$
都随 $m$ 严格递增。对固定 $k,m$，$b_{\min}$、$b_{\max}$ 都随
$Q$ 严格递减。对窗口内任意 $b$，

$$
S=T_m-3Q-b
$$

随 $b$ 严格递减，且

$$
S_{\min}=T_m-3Q-b_{\max},\qquad
S_{\max}=T_m-3Q-b_{\min}.
$$

因此 S-X1 的射线闭式完整。它本身不排除任何记录；`Q=21,m=15`
的窗口非空是预期行为。

## 2. S-X2：D_m 的整族数论

沿射线定义

$$
D_m=2^{n_{k-1}}(2^{n_k})^m-5^{d_{k-1}}(5^{d_k})^m.
$$

**已闭合。**

1. Lucas 递推：

   $$
   D_{m+2}=(2^{n_k}+5^{d_k})D_{m+1}
   -2^{n_k}5^{d_k}D_m;
   $$

2. $\gcd(D_m,10)=1$；
3. 若奇素数 $p\ne5$ 同时整除 $D_m,D_{m+1}$，则
   $p\mid 2^{n_k}-5^{d_k}$；
4. 不整除 $2^{n_k}-5^{d_k}$ 的素因子在相邻项之间是隔离的；
   其下界至少为 $p\ge3$。

**族级阻塞（未闭合）。** 尚未证明：对窗口内每个 $m$，存在一个
素因子 $p$ 使全局方程模 $p$ 对全部可行 $b$ 无解。对 37 条不同
射线在 $p\le20000$ 内检查了“公共素因子”与“连续两项同时被小素数
整除”两种候选，均未找到统一素因子；因此目前不存在可引用的
固定族级模数。S-R3.2/3.3 的完整原初素因子定理仍是阻塞点。

**后备切换（2026-08-06）。** 当前主攻已切到 S-X2“周期素因子 +
b 窗口”路线；状态、小素因子表与候选闭合判据见
`s_x2_backup.md`。L-B′ 暂停推进但保持开放，不再阻塞条件版
53.4-LB。

**p=3 奇偶族结构（部分进展，未关闭）。** 若奇素数 $p$ 满足

$$
p\mid 2^{n_k}+5^{d_k},
$$

且 $p\mid D_j$（$j=0$ 或 $1$），则由
$D_{m+2}\equiv-2^{n_k}5^{d_k}D_m\pmod p$，$p$ 整除所有与 $j$
同奇偶的 $D_m$。对 37 条射线中的 29 条，$p=3$ 给出这种奇偶
族结构。其余 8 条射线在 $p\le50000$ 内未找到同样的
$p\mid A+B$ 起点命中，因此该结构不能统一关闭全部射线。

## 3. S-X3：全局方程的射线形式

全局方程

$$
(2^{T_m}-5^{P_m})m_0=A_{\mathrm{total}}
$$

在射线上等价于

$$
m_0
=\frac{2^S A_{\mathrm{chain}}+5^Q A_u}{D_m}
=\frac{A_{\mathrm{chain}}}{2^{3Q+b}(1-2^{-\delta_m})}
+\frac{h}{2^{\delta_m}-1},
$$

其中

$$
\delta_m=\Delta_{k-1}-m\Delta_k,\qquad
h=\frac{A_u}{5^L}\in[h_{\min},h_{\max}].
$$

对固定 $(Q,k,m,b)$，$h_{\min},h_{\max}$ 由 52.16 的闭式给出，
$A_{\mathrm{chain}}$ 的 A/B 族上下界由 52.10 给出。于是
$m_0$ 的全体可能值有显式区间：

$$
m_0\in[m_{\min}(Q,k,m),\,m_{\max}(Q,k,m)].
$$

**阻塞（未闭合）。** 对全部 236 条记录计算该区间与
$[x_0^{\mathrm{S7}},x_0^{\mathrm{S4}}]$ 的交集，区间均非空；
仅靠 A_u/A_chain 上下界与 S7/S4 不能排除任何记录。因此 S-X3
需要新的族级同余或值域约束，当前未闭合。

### 3.1 GC-4 残差收窄（候选，未闭合）

对全部 SURV-RAY 幸存记录，$x_0<Q/(3\delta\ln2)<5^Q$，故
GC-4 的 C3 链残差不是“模 $5^Q$ 的同余类”，而是精确值

$$
x_0=r_c=\bigl(A_{\mathrm{chain}}2^{-T_{\mathrm{chain}}}\bmod 5^Q\bigr).
$$

全局方程于是给出

$$
h_{\mathrm{req}}
=x_0(2^{\delta_m}-1)
\alpha\,2^{\delta_m}
\in[h_{\min},h_{\max}],
$$

其中

$$
\alpha=\frac{A_{\mathrm{chain}}}{2^{T_{\mathrm{chain}}}}
=\frac{A_{\mathrm{chain}}}{2^b5^Q a}
\in[0,1/3].
$$

因为 $h_{\min}\ge1/3$、$h_{\max}\le1$ 且
$\alpha\le1/3$，可得

$$
\frac{1/3}{2^{\delta_m}-1}\le x_0
\le \frac{1+\frac13\,2^{\delta_m}}{2^{\delta_m}-1}
<\frac{4}{3(2^{\delta_m}-1)}.
$$

对 $Q=15,17$，该区间整体位于 S7 下界之下，直接矛盾。对
$Q\ge19$，剩余条件不是简单的“$r_c$ 大于上界”；`Q=21` 的
常数链给出显式反例 `r_c=89,068,263`（
`s_x3_2_counterexample.txt`），它小于下界 `1/(3t2)`，此时
`h_req<h_min` 已直接矛盾。因此原目标中的
`r_c>4/(3(2^δ-1))` 不成立，正确的族级缺口是

$$
r_c\notin\left[\frac{1}{3(2^{\delta_m}-1)},\,
\frac{4}{3(2^{\delta_m}-1)}\right].
$$

区间下方由 `h_req<h_min` 矛盾，区间上方由 S-X3 上界矛盾。
这个修正后的缺口陈述也被否证：`Q=21` 常数链在
`b=4020633257` 及目标表的五个 `b` 处给出严格落在区间内的残差，
且 `h_req\in[1/3,1]`，见 `s_x3_2c_prime_counterexample.txt` 与
`verify_s_x3_2c_prime_counterexample.py`。因此纯 C3 链残差不能
单独排除命中，S-X3.2c′ 不作为可引用引理。

S-X3.3 已把上述命中放回精确上升段集合：`H1--H4` 给出
`H_exact` 的闭式、2-adic 可实现性同余、`2U≤L+1` 分隔判据与首
C3 前缀确定性（见 `s_x3_3_exact_rejection.md`），列出的反例全部
被精确否决。对缺口长度不超过 $10^{12}$ 的 25 条射线
（`Q=15,17,19,20,21,22`），完整区间扫描覆盖缺口内全部可接受
$m$，最大首 C3 前缀 $L_0$ 均小于对应 $L$，因此这些射线的 S-X3.3
已关闭（`run_surv_ex_interval_scans.py` 与
`s_x3_3_interval_cert_*.txt`）。剩余阻塞是其余 211 条射线的
S-X3.3c：这些缺口可大于 $10^{40}$，不能逐 $m$ 扫描，需要解析的
“首 C3 前缀对数上界”。该上界候选的强形式 L-B1
$r(w)\ge2^{S/5}$ 已被 `m=7`、`m=9` 精确反例否证（
`lb0_counterexamples.txt`、`verify_lb0_counterexample.py`），
但弱形式 L-B′ $r(w)\ge2^{S/5}/5$ 仍与全部已知词相容，当前未决；
尚未转入 S-X2 后备。L-B′ 已拆为 L-B′a（`r≡3` 强界，开放）、
L-B′b（`r≡4` 弱界，开放）与 L-B′c（前插递推 `k≥1` 分支，已证），
递推公式与校准点见 `s_x3_3_log_bound_candidate.md` 与
`verify_lb_prime_calibration_points.py`。S-X3 整体仍未关闭。

## 4. S-X4：射线终止与证书完备性

`verify_surv_ray.py` 已给出 `Q=8..100` 的 236 条完整射线记录。
`Q>100` 的窗口是否为空尚未证明；若不为空，需要把证书扩展到
完整射线族并逐条给出被 S-X1..S-X3 排除的见证。

**当前状态。** S-X1 已闭合；S-X2 的 Lucas 递推与整除性已闭合，
但“每项存在族级可排除素因子”未闭合；S-X3.2c′ 已被反例否证，
S-X3.3a/3b 给出精确 H 集合和已知命中点否决，缺口长度不超过
$10^{12}$ 的 25 条射线已由完整区间证书关闭，但其余 211 条射线的
S-X3.3c 未闭合；候选解析上界 L-B1 强形式已被否证，L-B′ 弱形式
未决（L-B′c 已证，L-B′a/b 开放）；S-X4 尚未完成。因此无条件
定理不能在本文件宣告成立。2026-08-06 起 S-X2 为当前主攻后备
路线（`s_x2_backup.md`）。

2026-08-12 修正：S-X4 是过强的有限枚举完备性要求；整族解析路线
（L-B′/U=2 → `S0(m)≤5log2(5m)` → S-X3.3c 对全部射线）将其完全
绕过，不需要证明 `Q>100` 窗口为空，S-X4 从 53.4-LB 依赖中删除。

**条件版定理 53.4-LB（已正式接受）。** 在 53.1--53.3 主链成立的
前提下，把 L-B′ $r(w)\ge2^{S/5}/5$ 写成显式
解析假设；在此假设下 $S_0(m)\le5\log_2(5m)$，结合已闭合的 S-X1、
S-X3.3a/b、25 条区间证书与 53.6 的射线族接口，7 发散。L-B′a/b
闭合后 L-B′ 假设删除，条件定理升级为定理。S-X2 的素因子族级排除
是并行后备，不参与该条件定理的依赖。

**依赖。** SURV-RAY（`surv_ray.md`）、52.7、52.10--52.16、
QB-8、GC-4、S7、S4、G3、S-X1、S-X3.3a/b、25 条区间证书、
53.1--53.3、53.6、Simons S1，以及 L-B′（假设）。S-X4 已被整族
解析路线绕过，不再列入依赖（2026-08-12）。

## 5. 2026-08-06 status appendix

- 25 records (Q=15,17,19,20,21,22) are completely excluded by the
  S-X3.3 interval certificates; verify_surv_ex_interval_certs.py
  outputs RESULT: PASS.
- The remaining 211 records are tracked in s_x2_exclusion_status.md.
- S-X2 has no new complete exclusion chain yet; the p=3/MOD9 examples
  and the S-R3.2 p-adic gap are recorded in s_x2_backup.md and
  s_x2_r32_valuation_lemma.md.
