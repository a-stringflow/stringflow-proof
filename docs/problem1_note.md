# 问题 1 研究笔记：$F_b$ 族的循环结构（草稿）

日期：2026-08-03

## 摘要

对奇数 $b\ge1$ 定义

$$
F_b(n)=
\begin{cases}
n/2,&n\text{ 偶},\\
n+b,&n\text{ 奇},
\end{cases}
$$

它是 $T_{a,b}$ 族在 $a=1$ 时的完全可解子类。本文档汇总本阶段关于 $F_b$ 循环结构的可证结果：循环与 $\times2$ 循环一一对应；循环长度等于 $r/b$ 二进制周期中 1 的个数；$T_k$ 有欧几里得闭式；Mersenne 参数有项链生成函数；全进展权重与单位群生成函数满足除数对偶；素幂模数完全由素数的 $G_p$ 决定；第一、二、三、五阶矩有闭式。剩余前沿被精确约化为奇阶素数 $p$ 的“奇偶分圆周期”。

## 1 记号

- $T_d=\operatorname{ord}_d(2)$（奇数 $d$）。
- $M_d=(2^{T_d}-1)/d$：$1/d$ 的二进制周期词数值。
- $U_d=(\mathbb Z/d)^\times$。
- $L(u)=\#\{0\le i<T_d:2^i u\bmod d\text{ 为奇数}\}$：单位 $u$ 的循环长度。
- $G_d(x)=\sum_{u\in U_d}x^{L(u)}$。
- $P_n(y)=\sum_{v=0}^{n-1}y^{s_2(vM_n)}$：全进展权重。
- $B_k(d)=\#\{w<d:w\text{ 奇},\ 2^kw\bmod d\text{ 奇}\}$。
- $M_r(G_d)=\sum_{u\in U_d}L(u)^r$。

## 2 基本定理概要

- 定理 1.1：$F_b$ 循环与 $U_b(o)=\operatorname{oddpart}(o+b)$ 在奇数 $o\le b$ 上的循环一一对应。
- 定理 1.2：所有循环在 $[1,2b]$，所有轨道进入循环；$r(n)=n$ 是下降秩。
- 定理 1.5：Mersenne 参数 $b_m=2^m-1$ 的循环数
  $$
  c_m=\frac1m\sum_{d\mid m}\varphi(d)2^{m/d}-1.
  $$
- 定理 1.8：循环长度等于最小周期中 1 的个数。
- 定理 1.11：一般循环计数
  $$
  c(b)=\sum_{d\mid b}\frac{\varphi(d)}{\operatorname{ord}_d(2)}.
  $$
- 定理 1.13：$L(\mathcal O)=\operatorname{wt}\!\left(0.\overline{b_1\cdots b_T}\right)$。
- 定理 1.15：聚合分布可分解到模 $d\mid b$ 的单位群。
- 定理 1.17：第一矩 $M_1(G_d)=T_d\varphi(d)/2$。
- 定理 1.18：第二矩约化到 $A_k$。
- 定理 1.25：$-1\in\langle2\rangle$ 时 $G_d(x)=\varphi(d)x^{T_d/2}$。
- 定理 1.26：Mersenne 素数 $d=2^p-1$ 时 $G_d(x)=(1+x)^p-1-x^p$。
- 定理 1.27：指标 2 时 $G_d(x)=T(x^w+x^{T-w})$。
- 定理 1.33：对所有奇数 $d$ 的显式 divisor 和闭式。

## 3 本阶段新定理

### 3.1 $T_k$ 的欧几里得闭式（定理 1.36--1.39）

定义

$$
A(s,d)=\sum_{u=0}^{d-1}(-1)^{\lfloor su/d\rfloor},
\qquad
B(s,d)=\sum_{u=0}^{d-1}(-1)^{u+\lfloor su/d\rfloor}.
$$

关键恒等式：

1. 互素奇数 $s,d$：$B(s,d)=1$（配对 $u\leftrightarrow d-u$ 相消）。
2. $s$ 为偶数：$A(s,d)=1$。
3. $s>d$、$s=qd+r$：$A,B$ 按 $q$ 奇偶在 $A(r,d),B(r,d)$ 间切换。
4. $s<d$：$A(s,d)=2-B(d-s,d)$，$B(s,d)=2-A(d-s,d)$。
5. $s$ 奇、$s<d$：把 $d=q_0s+r$、$s=q_1r+s_1$ 代入，得到 $A(s,d)$ 的欧几里得递归，每一步把参数换成更小的余数对。

由此得到

$$
T_k(d)=4B_k(d)-(d-1)=B(2^k,d)-1,
$$

单次计算 $O(\log d)$ 步；再结合定理 1.23，$A_k(d)$ 可在 $O(\tau(d)\log d)$ 步内计算。

### 3.2 Mersenne 循环长度分布生成函数（定理 1.40）

对 $b_m=2^m-1$，设 $N_{m,q}$ 为长度为 $q$ 的循环数，则

$$
\sum_{q=1}^m N_{m,q}x^q
=
\sum_{de\mid m}\mu(d)N_e(x^d)-1,
\qquad
N_e(y)=\frac1e\sum_{f\mid e}\varphi(f)(1+y^f)^{e/f}.
$$

这同时给出 $c_m$ 的精确除数和：

$$
c_m=\frac1m\sum_{d\mid m}\varphi(d)2^{m/d}-1.
$$

### 3.3 全进展权重与除数对偶（定理 1.41、推论 1.42）

$$
P_n(y)=\sum_{m\mid n}G_m\!\left(y^{T_n/T_m}\right),
\qquad
G_d(x)=\sum_{e\mid d}\mu(e)P_{d/e}\!\left(x^{T_d/T_{d/e}}\right).
$$

推论：若 $2^{T_n/2}\equiv-1\pmod n$，则

$$
P_n(y)=1+(n-1)y^{T_n/2}.
$$

### 3.4 矩闭式（定理 1.43、1.49、1.50）

第二矩：

$$
M_2(P_n)=\frac{T_n(n-1)}2+2\sum_{k=1}^{T_n-1}(T_n-k)B_k(n),
$$

且

$$
M_2(G_d)=M_2(P_d)-\sum_{\substack{m\mid d\\m<d}}\left(\frac{T_d}{T_m}\right)^2M_2(G_m).
$$

因此任意奇数 $d$ 的第二矩可在 $O(\tau(d)T_d\log d)$ 步内计算。

循环长度多重集关于 $T/2$ 对称，故奇阶矩由偶阶矩决定：

$$
M_3(G_d)=\frac{3T_d}{2}M_2(G_d)-\frac{\varphi(d)T_d^3}{4},
$$

$$
M_5(G_d)=\frac{\varphi(d)T_d^6}{2}-\frac{5T_d^3}{2}M_2(G_d)+\frac{5T_d}{2}M_4(G_d).
$$

### 3.5 素幂提升（定理 1.44）与奇阶结构（推论 1.45、1.47，观察 1.46、1.48）

设 $T_e=\operatorname{ord}_{p^e}(2)$。若 $T_{e+1}=p\,T_e$，则

$$
L_{p^{e+1}}(u)=L_{p^e}(u\bmod p^e)+\frac{(p-1)T_e}{2},
$$

$$
G_{p^{e+1}}(x)=p\,x^{(p-1)T_e/2}G_{p^e}(x).
$$

标准情形下

$$
G_{p^e}(x)=p^{e-1}x^{(p^{e-1}-1)T_1/2}G_p(x).
$$

奇阶结构：

- 推论 1.45：$T_d$ 为奇数时 $G_d(x)=x^{T_d}G_d(1/x)$。
- 推论 1.47：奇阶素数 $p$ 有 $p\equiv1,7\pmod8$ 且 $K=(p-1)/T_p\not\equiv4\pmod8$。
- 观察 1.46：奇阶素数的循环长度是奇偶函数的分圆周期：
  $$
  L_j=\frac1K\sum_{r=0}^{K-1}c_r\,\zeta_K^{-rj},
  \qquad
  c_r=\sum_{x=1}^{p-1}\varepsilon(x)\zeta_K^{r\,\operatorname{ind}_g(x)}.
  $$
- 观察 1.48：$K\ge6$ 时 $G_p$ 不由 $\operatorname{wt}(M_p)$ 单独决定。
- 定理 1.51：奇阶素数有反周期性 $L_{j+K/2}=T-L_j$，DFT 偶频消失，$G_p$ 由至多 $K/2$ 个整数决定。
- 引理 1.52：$K=6$ 时 $p\equiv7\pmod{24}$，$\langle2\rangle$ 等于六次剩余子群。
- 观察 1.53：$K=6$ 偏差不是 $(A,B,T)$ 的小整数线性公式。
- 定理 1.54：奇偶周期是 Gauss 周期与方波周期的卷积：
  $$
  d_j=\frac{T}{p}+\frac1p\sum_{i=0}^{K-1}S_i\,\eta_{i+j},
  \qquad
  \eta_j=\sum_{x\in C_j}\omega^x,\quad
  S_i=\sum_{a\in C_i}\frac{2}{1+\omega^{-a}}.
  $$

### 3.6 全进展权重的循环分解（定理 1.55）

**定理 1.55（循环恒常性）** 对奇数 $n$，设
$T=\operatorname{ord}_n(2)$，$M_n=(2^T-1)/n$。则

$$
s_2(vM_n)=s_2\bigl((2v\bmod n)M_n\bigr),
\qquad 0\le v<n.
$$

证明要点：$vM_n<2^T-1$，把它写成 $T$ 位二进制串；左循环移位
$x\mapsto 2x\bmod(2^T-1)$ 保持二进制权重。另一方面

$$
2vM_n=(2v\bmod n)M_n+\left\lfloor\frac{2v}{n}\right\rfloor(2^T-1),
$$

所以 $2(vM_n)\bmod(2^T-1)=(2v\bmod n)M_n$，恒等性成立。

**推论（循环分解与快速算法）**

$$
P_n(y)=\sum_{v=0}^{n-1}y^{s_2(vM_n)}
=\sum_{C\in\operatorname{Cyc}(n)}|C|\,y^{s_2(v_CM_n)},
$$

其中 $C$ 跑遍映射 $v\mapsto2v\bmod n$ 在 $\mathbb Z/n$ 上的循环，
每个循环只算一次权重。循环数为

$$
c(n)=\sum_{d\mid n}\frac{\varphi(d)}{T_d},
$$

因此 $P_n$ 只需 $c(n)$ 次权重计算而不是 $n$ 次。对素数 $p$，
取原根 $g$，有

$$
G_p(x)=P_p(x)-1=T\sum_{j=0}^{K-1}x^{s_2(g^jM_p)},
\qquad K=\frac{p-1}{T_p},
$$

即 $G_p$ 可在 $O(p)$ 步（含一次原根计算）内求出，替代逐单位
$O(pT_p)$ 的暴力枚举。

### 3.7 $K=6$ 的奇偶 Fourier 结构（定理 1.56、观察 1.57）

**定理 1.56** 设奇阶素数 $p$ 有 $K=6$（等价于
$p\equiv7\pmod{24}$），$T=(p-1)/6$，$\chi$ 是满足
$\chi(g)=\zeta_6$ 的六次特征。定义奇偶 Fourier 系数

$$
c_r=\sum_{\substack{1\le x\le p-1\\x\text{ 奇}}}\chi^r(x).
$$

则

$$
c_0=3T,\qquad c_2=c_4=0,\qquad c_3=-h(-p),
$$

且

$$
c_1=-\sum_{y=1}^{(p-1)/2}\chi(y).
$$

六个循环长度由

$$
L_j=\frac{3T+2\operatorname{Re}\bigl(c_1\zeta_6^{-j}\bigr)
-h(-p)(-1)^j}{6}
$$

给出，因而 $G_p$ 完全由 $(h(-p),c_1)$ 决定。

证明要点：

1. $c_3=\sum_{x\text{ 奇}}(x/p)$。因为 $(2/p)=1$，偶数项和等于
   半区间二次剩余超量 $E=\sum_{y=1}^{(p-1)/2}(y/p)$，总特征和为 0，
   故奇项和 $-E$；经典二次超量定理在 $p\equiv7\pmod8$ 时给
   $E=h(-p)$。
2. $c_2=c_4=0$ 是定理 1.51 的偶频消失，$c_0$ 是奇数的总数。
3. $c_1$ 的表达式来自 $\chi(2)=1$ 与 $\sum_x\chi(x)=0$。
4. 长度公式是傅里叶反演（观察 1.46）代入
   $c_5=\overline{c_1}$、$\zeta_6^{-3j}=(-1)^j$ 的直接结果。

**定理 1.56 补充（$L(1,\chi)$ 衔接）** 设
$G(\chi)=\sum_{x=1}^{p-1}\chi(x)e^{2\pi i x/p}$。则

$$
c_1=\frac{i}{\pi}\,G(\chi)\,L(1,\overline\chi).
$$

证明要点：奇偶函数 $(-1)^x$ 的加性 Fourier 系数是
$-i\tan(\pi a/p)$；再结合 Lerch 的余切和公式

$$
\sum_{a=1}^{p-1}\chi(a)\cot\frac{\pi a}{p}
=\frac{2p}{\pi}L(1,\chi)
$$

（$\chi$ 为奇特征）即得。数值验证对 $p<20000$ 的全部 81 个
$K=6$ 素数成立。

**观察 1.57（整数参数）** 对 $p<20000$ 的全部 81 个 $K=6$ 素数，
数值上恒有

$$
c_1=U+V\sqrt{-3},\qquad U,V\in\mathbb Z,\qquad U\equiv V\pmod2,
$$

即 $c_1\in\mathbb Z[\sqrt{-3}]$。于是 $G_p$ 由三个整数
$(h(-p),U,V)$ 完全决定。数据见
`odd_prime_K6_structure_table.md`。这里的 $U,V$ 整性尚未给出理论证明，
是下一轮可继续推进的点。

### 3.8 一般奇阶素数的半区间约化（定理 1.58）

**定理 1.58** 设 $p$ 为奇阶素数（$T=\operatorname{ord}_p(2)$ 为奇数），
$K=(p-1)/T$ 为偶数，$\chi$ 是满足 $\chi(g)=\zeta_K$ 的 $K$ 次特征。
定义奇偶 Fourier 系数与半区间特征和

$$
c_r=\sum_{\substack{1\le x\le p-1\\x\text{ 奇}}}\chi^r(x),\qquad
H_r=\sum_{y=1}^{(p-1)/2}\chi^r(y).
$$

则

$$
c_0=\frac{KT}{2},\qquad
c_r=0\ (2\le r\le K-2,\ r\text{ 偶}),\qquad
c_r=-H_r\ (r\text{ 奇}),
$$

因而

$$
L_j=\frac{T}{2}-\frac1K\sum_{\substack{1\le r\le K-1\\r\text{ 奇}}}
H_r\,\zeta_K^{-rj}.
$$

证明要点：

1. $c_0=(p-1)/2=KT/2$ 是奇数的总数。
2. 偶频 $c_r=0$ 是定理 1.51 的直接结果。
3. 对奇数 $r$，$\chi^r$ 为奇特征。因 $2\in\langle2\rangle$，有
   $\chi^r(2)=1$，故偶数项和
   $$
   \sum_{x\text{ 偶}}\chi^r(x)
   =\sum_{y=1}^{(p-1)/2}\chi^r(2y)=H_r;
   $$
   总特征和 $\sum_{x=1}^{p-1}\chi^r(x)=0$，所以 $c_r=-H_r$。
4. 长度公式是观察 1.46 的傅里叶反演代入上述系数。

**推论（问题形式的精确化）** 任意奇阶素数 $p$ 的循环长度分布
完全由 $K/2$ 个半区间特征和

$$
H_1,H_3,\dots,H_{K-1}
$$

决定。特别地，$H_{K/2}=\sum_{y=1}^{(p-1)/2}(y/p)$ 是经典二次超量：
当 $p\equiv7\pmod8$ 时它等于 $h(-p)$；当 $p\equiv1\pmod8$ 时由
$h(-p)$ 的二次超量公式给出。$K=6$ 时 $H_1=-c_1$ 与
$H_3=h(-p)$ 就是定理 1.56 的两个参数。

这把“奇偶分圆周期”问题精确化为“K 次特征在区间
$[1,(p-1)/2]$ 上的超量”这一经典数论对象。脚本
`verify_half_interval_reduction.py` 已对 $p<5000$ 的全部 197 个
奇阶素数验证恒等性与傅里叶反演。

### 3.9 除数缩放恒等式（定理 1.59）

**定理 1.59（块复制）** 对奇数 $n$，设 $d\mid n$，
$u\in(\mathbb Z/d)^\times$。则

$$
s_2\!\left(\frac nd\,u\,M_n\right)
=\frac{T_n}{T_d}\,s_2(uM_d).
$$

证明要点：

$$
\frac nd\,u\,M_n
=\frac{u(2^{T_n}-1)}d
=uM_d\left(1+2^{T_d}+2^{2T_d}+\cdots+2^{T_n-T_d}\right).
$$

因为 $uM_d<2^{T_d}$，乘积的二进制表示就是 $uM_d$ 的
$T_n/T_d$ 份无进位复制，权重按份数倍增。

**推论（除数对偶的直接证明与合数快速算法）**

把 $v\in\mathbb Z/n$ 按精确除数 $d\mid n$ 分解为
$v=(n/d)u$、$\gcd(u,d)=1$，由定理 1.59 得

$$
P_n(y)=1+\sum_{\substack{d\mid n\\d>1}}G_d\!\left(y^{T_n/T_d}\right),
$$

即定理 1.41 的除数对偶不再依赖 Möbius 反演，而由块复制直接给出。
反过来

$$
G_d(x)=\sum_{e\mid d}\mu(e)P_{d/e}\!\left(x^{T_d/T_{d/e}}\right)
$$

仍为 Möbius 反演。对每个 $d\mid n$，$G_d$ 只需在
$\langle2\rangle\subset(\mathbb Z/d)^\times$ 的
$\varphi(d)/T_d$ 个陪集上各算一次权重，总复杂度
$O(\sum_{d\mid n}\varphi(d))=O(n)$，是“每循环一次权重”之外的另一层
约化。脚本 `verify_scaling_identity.py` 对奇数 $n<300$ 全部验证。

### 3.10 半区间特征和的 2-adic 可除性（观察 1.60）

**观察 1.60** 设 $p$ 为奇阶素数，$K=(p-1)/T_p>2$，并沿用定理 1.58
的半区间特征和 $H_r$。对 $p<5000$ 的全部 69 个 $K>2$ 奇阶素数，
在 $\mathbb F_2[x]/(\Phi_K(x)\bmod2)$ 中精确计算得到

$$
\prod_{\gcd(a,K)=1}H_a\equiv0\pmod2.
$$

等价地，$H_1$ 的域范数为偶数，因此理想 $(H_1)$ 被
$\mathbb Z[\zeta_K]$ 中每个位于 $2$ 之上的素理想整除（Galois 共轭
不变性）。特别地：

1. $K=6$ 时 $H_1\in2\mathbb Z[\zeta_6]$，即
   $H_1=-c_1=U+V\sqrt{-3}$ 中的 $U,V$ 为同奇偶整数，这给出了
   观察 1.57 中“三整数参数”整性部分的数值证明；
2. $K=2$ 是唯一例外，此时 $H_1=h(-p)$ 为奇数（二次超量）。

脚本 `verify_2adic_divisibility.py` 用精确的 $\mathbb F_2$ 多项式运算
验证该可除性，并顺带核对 $K=6$ 的 $U\equiv V\pmod2$。给出
$\prod_{\gcd(a,K)=1}H_a\equiv0\pmod2$ 的一般证明，是把观察 1.57
升级为定理的核心后续步骤。

## 4 剩余前沿

一般全进展权重 $P_n(y)$ 的快速算法已由定理 1.55（循环分解）与
定理 1.59（除数块复制）给出：素数情形 $O(p)$，合数情形
$O(\sum_{d\mid n}\varphi(d))=O(n)$ 次权重计算。尚未闭合的是：
(1) 半区间特征和 $H_r$ 的算术闭式；(2) $K=6$ 时 $U,V$ 的整性证明。
前者由定理 1.58 精确化为“$K$ 次特征在 $[1,(p-1)/2]$ 上的超量”，
在 $K=6$ 时经定理 1.56 与观察 1.57 压缩为三整数
$(h(-p),U,V)$，并衔接 order-6 Gauss 和与 $L(1,\chi)$；观察 1.60
把 $U,V$ 的整性进一步归结为“半区间特征和乘积 $\equiv0\pmod2$”
这一可验证的 2-adic 恒等式。数据底稿：

- `odd_prime_G_table.md`：奇阶素数 $p<2000$ 的 $T_p,K$ 与循环长度分布（91 个素数）；
- `odd_prime_D_table.md`：同一批素数的正偏差 $D=|T-2L|$（定理 1.51 的 $K/2$ 参数数据集）。

## 5 验证脚本

- `verify_euclid_Tk.py`：$T_k$ 欧几里得闭式。
- `verify_necklace_gf.py`：Mersenne 生成函数。
- `verify_divisor_duality.py`：除数对偶与推论 1.42。
- `verify_moment_Pn.py`：第二矩公式。
- `verify_third_moment_universal.py`、`verify_symmetric_moments.py`：三阶、五阶矩。
- `verify_prime_power_lift.py`：素幂提升。
- `verify_cyclotomic_periods.py`：分圆周期傅里叶反演。
- `verify_gauss_period_convolution.py`：Gauss 周期卷积（定理 1.54）。
- `collect_odd_prime_D.py`：生成 `odd_prime_D_table.md`。
- `verify_m_weight_independence.py`：$w$ 非充分性。
- `collect_odd_prime_G.py`：生成 `odd_prime_G_table.md`。
- `verify_cycle_decomposition.py`：定理 1.55 的循环恒常性、$P_n$ 循环分解、
  素数快速 $G_p$ 与定理 1.56 的 $K=6$ 结构（含 $L(1,\chi)$ 恒等式）。
- `collect_K6_structure.py`：生成 `odd_prime_K6_structure_table.md`。
- `verify_half_interval_reduction.py`：定理 1.58 的一般奇阶半区间约化
  （$p<5000$ 全部 197 个奇阶素数）。
- `verify_scaling_identity.py`：定理 1.59 的除数块复制恒等式
  （奇数 $n<300$ 全部验证）。
- `verify_2adic_divisibility.py`：观察 1.60 的 2-adic 可除性
  （$p<5000$ 全部 69 个 $K>2$ 奇阶素数，精确 $\mathbb F_2$ 验证）。
