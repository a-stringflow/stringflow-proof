# SURV-RAY：连分数幸存射线引理族

日期：2026-08-06

本文把 `sound_x0_filter_certificate.txt` 中的 `x0>10^6` 幸存记录
从逐条清单改写为连分数半收敛射线的完整解析刻画。它不把“未找到
反例”当证明；所有筛选不等式都是 S7、S4、G3 与 G5 的显式推论，
完整清单由 `verify_surv_ray.py` 作为有限算术证书重新生成，写入
`surv_ray_certificate.txt`（`Q=8..100`，共 236 条）。证书除逐条
幸存记录外，还给出每条射线的窗口行
`Q base step m_min m_max count`，直接对应 S-R2 的 `m_min/m_max`
区间。

## 1. 记号

设

$$
\lambda=\log_2 5,\qquad
\rho=\lambda,\qquad
T(P)=\lceil P\lambda\rceil,\qquad
\delta(P)=T(P)-P\lambda.
$$

记 $\lambda$ 的连分数收敛子为

$$
\frac{n_k}{d_k}=[a_0;a_1,\dots,a_k],
\qquad
k\ge0.
$$

记绝对误差

$$
\Delta_k=|n_k-d_k\lambda|>0.
$$

当 $k$ 为奇数时 $n_k>d_k\lambda$，收敛子是上方近似；当 $k$ 为
偶数时 $n_k<d_k\lambda$，收敛子是下方近似。由此得到上方记录分母
的半收敛射线参数化。

## 2. S-R1：记录归约

**陈述。** 对 $Q\ge8$，任何满足 S7+S4 声音条件且
$x_0>10^6$ 的幸存长度 $P$ 都落在某条上方半收敛射线上：

$$
P=d_{k-1}+m\,d_k,\qquad
T(P)=n_{k-1}+m\,n_k,
\tag{S-R1.1}
$$

其中 $k$ 为偶数，$d_{k-1}$ 是上方收敛子、$d_k$ 是下一个下方
收敛子，$m$ 满足

$$
0\le m\le a_{k+1}.
\tag{S-R1.2}
$$

若 $m=0$，则 $P=d_{k-1}$ 本身是上方收敛子；若 $m=a_{k+1}$，
则 $P=d_{k+1}$ 是下一个上方收敛子。所有中间 $m$ 给出上方
半收敛子。对应余量满足

$$
\delta(P)=\Delta_{k-1}-m\,\Delta_k.
\tag{S-R1.3}
$$

**证明。** 由连分数标准事实，$q$ 是 $\lambda$ 的“最佳上方逼近”
分母（即在 $q'\le q$ 中使 $\lceil q'\lambda\rceil-q'\lambda$
取新最小值的 $q'$）当且仅当 $q$ 是上方收敛子或位于相邻上方
收敛子之间的上方半收敛子。设相邻上方收敛子为
$d_{k-1}$ 与 $d_{k+1}$，它们之间唯一可能成为最佳上方逼近的
分母正是

$$
d_{k-1}+m\,d_k,\qquad 1\le m<a_{k+1},
$$

其中 $d_k$ 是夹在中间的下方收敛子。端点 $m=0$ 与
$m=a_{k+1}$ 就是 $d_{k-1}$ 与 $d_{k+1}$。该事实是经典连分数
定理：两个相邻收敛子之间没有其他最佳逼近，而半收敛子
$d_{k-1}+m d_k$ 是区间内全部“上方半收敛子”；G5 已把筛法
归约到这些记录分母，本引理补充其分支、端点与线性余量。

因为 $d_{k-1}$ 是上方收敛子而 $d_k$ 是下方收敛子，有

$$
d_{k-1}\lambda-n_{k-1}=-\Delta_{k-1},\qquad
d_k\lambda-n_k=+\Delta_k.
$$

于是

$$
P\lambda-T(P)
=-\Delta_{k-1}+m\Delta_k.
$$

标准连分数不等式给出

$$
\frac{\Delta_{k-1}}{\Delta_k}>a_{k+1}\ge m,
$$

故 $P\lambda-T(P)<0$，从而 $T(P)=\lceil P\lambda\rceil$，且

$$
\delta(P)=T(P)-P\lambda=\Delta_{k-1}-m\Delta_k.
$$

这证明 (S-R1.1)--(S-R1.3)。∎

**推论。** 对固定射线，$P$ 是 $m$ 的线性增函数，$\delta(P)$ 是
$m$ 的线性减函数：

$$
P_m=d_{k-1}+m d_k,\qquad
\delta_m=\Delta_{k-1}-m\Delta_k.
$$

这使后续窗口分析完全化为对单变量 $m$ 的显式不等式。

## 3. S-R2：块参数化与窗口

沿用 `global_P_bound.md` 的记号：

$$
P_x(Q)=Q\rho^{Q-1}\log_2\frac{10^6}{A_Q},
$$

$P_Q$ 是 G3 的逐 $Q$ 上界，即 S7+S4+Laurent 下界首次产生矛盾
的阈值；$A_Q$ 是 S7 常数。

**陈述。** 固定 $Q\ge8$ 与射线 $(k,m)$。若

$$
P_x(Q)<P_m<P_Q(Q),
\tag{S-R2.1}
$$

则幸存条件 (SF) 等价于

$$
A_Q\,2^{P_m/(Q\rho^{Q-1})}
<\frac{Q}{3\,\delta_m\ln2}.
\tag{S-R2.2}
$$

令

$$
F_Q(m)
=\log_2 A_Q+\frac{d_{k-1}+m d_k}{Q\rho^{Q-1}}
+\log_2\!\bigl(3(\Delta_{k-1}-m\Delta_k)\ln2\bigr)
-\log_2 Q.
$$

则 $F_Q(m)$ 对 $m$ 严格递增。因此每条射线的幸存窗口是单区间

$$
m_{\min}(Q)\le m\le m_{\max}(Q),
$$

其中

$$
m_{\min}(Q)=\left\lfloor\frac{P_x(Q)-d_{k-1}}{d_k}\right\rfloor+1,
$$

而 $m_{\max}(Q)$ 是方程 $F_Q(m)=0$ 的唯一解（与端点
$0\le m\le a_{k+1}$ 及 $P_m<P_Q$ 相交）。

**证明。** (S-R2.1) 与 (S-R2.2) 正是 S7、S4 与 G3 的直接代入：
$x_0>10^6$ 对应 $P_m>P_x(Q)$，G3 对应 $P_m<P_Q(Q)$，(SF) 是
两个外部不等式的合并。

固定射线后，$P_m$ 随 $m$ 严格递增，$\delta_m$ 随 $m$ 严格递减，
故

$$
\frac{dP_m}{dm}=d_k>0,\qquad
\frac{d\delta_m}{dm}=-\Delta_k<0.
$$

$F_Q(m)$ 中第一项与第二项之和随 $m$ 严格递增；第三项是
$\log_2(3\delta_m\ln2)$，也随 $m$ 严格递增。因此
$F_Q'(m)>0$，$F_Q(m)=0$ 至多一个解；不等号 $F_Q(m)<0$ 的
集合是从 $m=0$ 开始的单区间。∎

**推论（Q 增大时窗口推进）。** 由显式式可见
$P_x(Q)$ 与 $P_Q(Q)$ 均随 $Q$ 增大，且对同一射线，$F_Q$ 的
常数项 $\log_2 Q-\log_2 A_Q$ 随 $Q$ 增大，故
$m_{\min}(Q)$、$m_{\max}(Q)$ 都单调推进。该单调性用于把
$Q=8..100$ 的清单组织成射线块，不用于证明任何单个记录的排除。

具体地，记 $B_Q=\log_2(10^6/A_Q)$。由
$A_Q=C_1 4^{-1/\rho^{Q-1}}$ 与 $Q\ge8$ 得
$20.87<B_Q<20.89$，故

$$
\frac{P_x(Q+1)}{P_x(Q)}
=\frac{Q+1}{Q}\,\rho\,\frac{B_{Q+1}}{B_Q}
>2.3,
$$

因此 $P_x(Q)$ 在 $Q\ge8$ 时严格递增。$P_Q(Q)$ 的单调性来自 G3
方程：固定 $P$ 时，

$$
\log_2 A_Q+\frac{P}{Q\rho^{Q-1}}
-\log_2 Q+\log_2(3\ln2)+\log_2\delta_{\mathrm{lb}}(P)
$$

随 $Q$ 严格下降（指数分母占优），而它作为 $P$ 的函数最终严格
上升（$\delta_{\mathrm{lb}}(P)$ 的平方指数衰减占优）。因此零点
$P_Q(Q)$ 随 $Q$ 严格递增。本文件只使用该单调性组织射线块，不把
它作为排除论证的一环。

## 4. S-R3：Lucas 结构

**陈述。** 固定射线，令

$$
A=2^{n_k},\qquad B=5^{d_k},\qquad
C=2^{n_{k-1}},\qquad E=5^{d_{k-1}}.
$$

则

$$
D_m=2^{T_m}-5^{P_m}
=C A^m-E B^m,
$$

且对 $m\ge0$ 有

$$
D_{m+2}=(A+B)D_{m+1}-AB\,D_m.
\tag{S-R3.1}
$$

**证明。** 直接代入：

$$
\begin{aligned}
&(A+B)(C A^{m+1}-E B^{m+1})-AB(C A^m-E B^m)\\
&=C A^{m+2}+C A^{m+1}B-EAB^{m+1}-E B^{m+2}
 -C A^{m+1}B+EAB^{m+1}\\
&=C A^{m+2}-E B^{m+2}=D_{m+2}.
\end{aligned}
$$

∎

**整除性。** 对任意 $m\ge0$：

1. $\gcd(D_m,10)=1$，因为 $D_m$ 为奇数且 $5\nmid D_m$；
2. $3\mid D_m$ 当且仅当 $T_m-P_m$ 为偶数，即
   $(-1)^{T_m}=(-1)^{P_m}\pmod3$；
3. 若奇素数 $p\ne5$ 同时整除 $D_m$ 与 $D_{m+1}$，则
   $p\mid A-B=2^{n_k}-5^{d_k}$。

第三条的证明：由 $D_m\equiv0$ 与 $D_{m+1}\equiv0\pmod p$，
从

$$
D_{m+1}=A\,C A^m-E B\,B^m
$$

与 $D_m$ 消去 $C A^m$ 项，得到

$$
E B^m(A-B)\equiv0\pmod p.
$$

因 $p\ne2,5$，$E B^m$ 可逆，故 $A\equiv B\pmod p$。∎

**素因子下界。** 每条射线上的 $D_m$ 不含素因子 $2,5$；若
$p\mid D_m$ 且 $p\nmid A-B$，则 $p$ 是这条射线上 $D_m$ 的
“原初素因子”：在本整族排除框架中，该词指不整除固定因子
$A-B$ 的素因子；由第三条，它不整除 $D_m$ 的相邻项。这类素因子
至少满足 $p\ge3$。进一步证明每条 $D_m$ 都存在原初素因子的任务
留给整族模数排除层，它只需要 S-R3.1 的递推与第三条的相邻项
隔离。

## 5. S-R4：52.7 与全局方程的射线形式

设幸存长度 $P_m=d_{k-1}+m d_k$、总权重
$T_m=n_{k-1}+m n_k$，$Q\ge8$。令

$$
L=P_m-Q,\qquad
K=T_m-P_m-2Q.
$$

对 QB-8 尖峰结构，上升段长度 $L$、$t=2$ 步数 $U$ 与 C3 超出量
$b$ 满足

$$
U+b=K,\qquad
0\le U\le L,\qquad
S=L+U=T_m-3Q-b.
$$

因此 52.7 的必要形式为

$$
U_{\mathrm{req}}(b)=T_m-P_m-2Q-b=K-b,
$$

$$
0\le U_{\mathrm{req}}(b)\le L.
$$

全局方程写成射线形式：

$$
\bigl(2^{n_{k-1}+m n_k}-5^{d_{k-1}+m d_k}\bigr)m_0
=2^S A_{\mathrm{chain}}+5^Q A_u,
$$

其中 $m_0$ 是循环全局最小值，$A_{\mathrm{chain}}$ 是 C3 链分子，
$A_u$ 是上升段分子。左边正是 S-R3 的 $D_m$。于是

$$
m_0=\frac{2^S A_{\mathrm{chain}}+5^Q A_u}{D_m},
$$

这是后续整族排除的统一入口。

**依赖。** G5、S7、S4、G3、QB-8、52.7、GC-4。

## 6. 冰雹猜想迁移评估

同一套 SURV-RAY 结构可直接迁移到 $\lambda=\log_2 3$：

1. 记录归约 S-R1 只依赖连分数上方半收敛子理论，与底数 $2,5$
   无关，替换为 $2,3$ 后逐字成立；
2. 块参数化 S-R2 的 $P_x(Q)$、$P_Q(Q)$ 需要重算 S7/S4/Laurent
   常数（$p=3,q=1$ 的 $A_Q$ 与值域下界），但窗口不等式形式不变；
3. Lucas 结构 S-R3 把 $5^{d_k}$ 换成 $3^{d_k}$，递推

   $$
   D_{m+2}=(2^{n_k}+3^{d_k})D_{m+1}-2^{n_k}3^{d_k}D_m
   $$

   与整除性证明逐字成立；
4. 差异点在 S7 的常数、Simons 的 $Q\le7$ 分类以及 7 的可达性，
   这些需要按 $3x+1$ 的外部文献重新审计。

结论：SURV-RAY 的射线参数化、完整清单生成器和递推证书框架可直接
复用；数值常数与可达性分类不能直接迁移。
