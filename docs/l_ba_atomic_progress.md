# L-B'a 原子进度：U=2, r≡3 情形

日期：2026-08-06

## 目标

对每个满足结构约束的上升词 $w$（$t_j\in\{1,2\}$、$2U\le L+1$、
$t_{L-1}=1$），若 $r(w)\equiv3\pmod5$，则

$$
r(w)\ge 2^{S/5},\qquad S=\sum_j t_j.
$$

现状：$U\ge3$、$U=0$、$U=1$ 已解析闭合（见
`s_x3_3_lb_ub2_reduction.md`）；本文件只处理 $U=2$。

## U=2 精确参数化（本轮复核）

设两个 `t=2` 位于 $j_1<j_2$，令

$$
m_1=j_1+1,\quad m_2=j_2+1,\quad d=m_2-m_1\ge2,\quad e=L-m_2\ge1.
$$

记 $S=L+2$，$R=2^{m_2+1}+2^{m_1}5^d$，$p=5^{m_2+1}$，
$N=R+5^{m_2}$。U=2 的最小起点满足

$$
5^{m_2}(3r+1)+R=2^L Q,\qquad
Q=\frac{40+96k}{5^e}\in\mathbb Z.
$$

当 $r\equiv3\pmod5$ 时 $3r+1\equiv0\pmod5$，因此
$2^L Q-R$ 被 $5^{m_2+1}$ 整除。$Q$ 属于唯一 CRT 类

$$
Q\equiv a\pmod{96},\qquad 2^L Q\equiv R\pmod{5^{m_2+1}},
$$

其中 $a=8$（$e$ 奇）或 $a=40$（$e$ 偶）。令 $q_0$ 为该类的最小正代表，
则（对 $L\le100$ 的全部 $U=2$、$r\equiv3$ 词复核）

$$
r=\frac{2^L q_0-N}{3\cdot5^{m_2}},\qquad 2^L q_0>N.
$$

## 已证部分命题

### P1：$n\ge1$ 子类闭合

令 $c=3r+1$，$c_2$ 为满足 $2^L\mid R+5^{m_2}c$ 的最小正整数，则
$c\equiv c_2\pmod{2^L}$。若 $c=c_2+n2^L$ 且 $n\ge1$，则

$$
r=\frac{c-1}{3}\ge\frac{2^L-1}{3}\ge 2^{(L+2)/5}\qquad(L\ge5).
$$

因此 $n\ge1$ 子类满足 L-B'a。

### P2：$n=0$ 子类的粗下界

$n=0$ 时 $c_2=2^{m_1}u$，其中 $u$ 为奇数，且

$$
u\equiv0\pmod5,\qquad u\equiv(-1)^{m_1}\pmod3.
$$

故 $u\ge5$（$m_1$ 奇）或 $u\ge25$（$m_1$ 偶），从而

$$
r\ge\frac{5\cdot2^{m_1}-1}{3}\quad(m_1\text{ 奇}),\qquad
r\ge\frac{25\cdot2^{m_1}-1}{3}\quad(m_1\text{ 偶}).
$$

这闭合 $n=0$ 中所有满足
$m_1\ge(L+2)/5+\log_2(3/5)$（$m_1$ 奇）或
$m_1\ge(L+2)/5+\log_2(3/25)$（$m_1$ 偶）的词。

### P3：U=1 源类强化不变量的数值校准

若 $w'=t::w$ 且 $k=0$，则

$$
r'=\frac{2^tr-1}{5},\qquad
\delta(w')=\delta(w)-\Lambda_t(r),
$$

其中 $\delta(w)=\log_2 r-S/5$，
$\Lambda_t(r)=\log_2(5r/(2^tr-1))+t/5$。对
$r'\equiv3\pmod5$，$k=0$ 源类只能是
$r\equiv8\pmod{25}$（$t=1$）或 $r\equiv4\pmod{25}$（$t=2$）。

校准：长度 $L\le20$ 的全部约束词中，$r\equiv8\pmod{25}$ 的 29993 个词
与 $r\equiv4\pmod{25}$ 的 30062 个词均满足
$\delta(w)\ge\Lambda_t(r)$（0 反例）。这是校准，不是证明。

### P0：顶层 k=0 步数 $\le2$ 的子类闭合

设 $w=t::w_0$ 且顶层前插为 $k=0$，即
$r=(2^tr_0-1)/5$，而 $w_0$ 的顶层前插为 $k\ge1$（或 $w_0$ 本身不满足
$k=0$ 前插）。由 L-B'c，$r_0\ge(2^{S_0+3}-1)/5$，$S=S_0+t$，故

$$
r\ge\frac{2^{S+3}-9}{25}.
$$

对 $S\ge3$，$\frac{2^{S+3}-9}{25}\ge2^{S/5}$；$S\le2$ 时不存在满足
$r\equiv3\pmod5$ 且顶层 $k=0$ 的词。因此顶层恰一个 $k=0$ 前插的词闭合。

若顶层连续两个 $k=0$ 前插 $w=t_1::t_2::w_0$，则

$$
r=\frac{2^{t_1+t_2}r_0-2^{t_2}-5}{25}
\ge\frac{2^{S+3}-61}{125},
$$

对 $S\ge6$ 有 $\frac{2^{S+3}-61}{125}\ge2^{S/5}$；$S\le5$ 时
$L\le4$，基词只能取 $S_0\le3$ 的 $[1]$（$r=1$）、$[1,1]$（$r=13$）、
$[2,1]$（$r=39$）、$[1,1,1]$（$r=5$），逐一检查残差条件后不存在
两步 $k=0$ 链到达 $r\equiv3\pmod5$ 的词。因此顶层 $k=0$ 步数
$\le2$ 的子类闭合。

## 本轮新增：δ 阈值树框架与两个失效路径

### 阈值树（校准至深度 10）

对每个残差类 $C\bmod5^h$（$h\ge2$），定义

$$
\theta_C=\theta_{C'}+\Lambda_t(\rho_C),
$$

其中 $C'$ 是 $C$ 经 $k=0$ 前插 $t\in\{1,2\}$ 到达的父类，
$\rho_C$ 是类内词级最小起点，$\theta_{3\bmod5}=0$。L-B'a 闭合的
充分条件是：对树中每个类 $C$，

1. 类内最小词的 $\delta$ 至少为 $\theta_C$；
2. 危险区间为空：对所有满足
   $S>5(\log_2\rho_C-\theta_C)$ 的词，$k\ge1$ 分支的
   $B(S)\ge\theta_C$。

对深度 $h\le10$、$\rho_C\le5\cdot10^6$ 的全部已找到类，
两个条件均 0 反例（`bad danger interval: 0`，`bad base delta: 0`）。
这是校准，不是证明。

### 失效路径 1：Q=U+1-n_top 不变量

曾猜测 $Q(w)=U(w)+1-n_{\mathrm{top}}(w)\ge0$（$n_{\mathrm{top}}$
为顶层连续 $k=0$ 前插数）。该猜测对 $L\le18$ 成立，但

| $m$ | $L$ | $U$ | $S$ | $n_{\mathrm{top}}$ | $Q$ | $r\bmod5$ |
|---:|---:|---:|---:|---:|---:|---:|
| 46933 | 20 | 2 | 22 | 4 | $-1$ | 3 |
| 18773 | 21 | 2 | 23 | 5 | $-2$ | 3 |

两个词均满足 $r^5\ge2^S$，说明 $Q\ge0$ 不是 L-B'a 的必要中间量。

### 失效路径 2：v5(3r+1) 上界

$v_5(3r+1)\le U+1$ 对所有词不成立；基词
$m=1833333$（$U=2$，$v_5(3r+1)=6$）为反例。该路径不可用。

## 最小未解子类（更新）

L-B'a 仍开放。当前最精确的剩余困难是阈值树的无穷性：
需要证明对所有 $h$、所有树中类 $C\bmod5^h$，条件 1 与 2 成立。
数值上深度 10 内无违反；解析上需要给出
$\theta_C$ 与 $\rho_C,S_{\min}(C)$ 的闭合增长关系。

## 本轮新增：D 不变量把树闭合化为单一不等式

定义

$$
D_C=0.8\log_2\rho_C-\theta_C.
$$

对源类边（$C_0$ 经 $k=0$ 前插 $t$ 到 $C$）有精确递推

$$
D_C=D_{C_0}+0.8\log_2\frac{\rho_C}{\rho_{C_0}}-\Lambda_t(\rho_C).
$$

由于 $\rho_C\ge(5\rho_{C_0}+1)/2^t$，每步 D 的下降量以
$0.4644$ 为上界（当 $\rho_C$ 接近最小前插时取到）。

**充分条件（已收紧为 $D\ge0$）。** 若对所有树中类 $C$ 有

$$
D_C\ge0,
$$

则危险区间为空：记
$A_C=5(\log_2\rho_C-\theta_C)=\log_2\rho_C+5D_C$，取
$S_0=\max(S_{\min},\lfloor A_C\rfloor+1)$。若
$S_{\min}\le A_C$，则 $B(S_0)\ge0.8A_C+0.678$，而
$0.8A_C+0.678-\theta_C=5D_C+0.678>0$；若 $S_{\min}>A_C$，
同样 $B(S_{\min})-\theta_C>0.678$。于是归纳
（$k\ge1$ 用 $B(S)$，$k=0$ 用源类递推）闭合 L-B'a。

**最小反例化约。** 若某类 $D_C<0$，取 $\rho_C$ 最小者，
则其父类 $D\ge0$，故该边 D 下降，即
$\rho_C$ 接近最小前插 $(5\rho_{C0}+1)/2^t$；沿此下降链必然到达
一个“终端类”（其最小词顶层 $k\ge1$）。因此只需证明所有终端类的
$D\ge0$。

**终端类 D 的链长公式。** 对从基词 $r_0$ 到顶词 $r_n$（$r_n\equiv3$）
的紧 $k=0$ 链，设每步 $r_{i+1}=(2^{t_{i+1}}r_i-1)/5$，则

$$
D=0.8\log_2 r_0-\sum_{i=0}^{n-1}\Lambda_{t_{i+1}}(r_i)
=0.8\log_2 r_n
-\sum_{i=0}^{n-1}\left(0.2\log_2\frac{5}{2^{t_{i+1}}-1/r_i}+\frac{t_{i+1}}5\right).
$$

每项 $\ge0.464386$。因此 $D\ge0$ 等价于链长界

$$
\sum_{i=0}^{n-1}\left(0.2\log_2\frac{5}{2^{t_{i+1}}-1/r_i}+\frac{t_{i+1}}5\right)
\le0.8\log_2 r_n.
$$

**数值验证（校准）。** 深度 $h\le13$、$\rho_C\le2\cdot10^7$
的全部已找到类：最小 $D=0.36217>0$，在类
$3583\bmod5^9$（$r=3583,S=10,\theta=9.083$）取得；
`bad danger interval=0`、`bad base delta=0`。确定性链扫描
$r\le6\cdot10^6$ 得到每个链长 $n$ 的最小 $r_n$：
$n=7$ 时 $r_n=23$ 为最紧（链长界几乎取等），其余 $n$ 均有裕量。

**未完成。** 解析证明终端类 $D\ge0$，即上式的链长界；
最紧情形是 $n=7,r_n=23$。这是 L-B'a 当前唯一剩余解析缺口。

## 本轮新增：链长界化为精确整数不等式

对紧链 $r_0\to\cdots\to r_n$，由
$5r_j+1=2^{t_j}r_{j-1}$ 得

$$
\prod_{j=1}^n\left(5+\frac1{r_j}\right)=\frac{2^T r_0}{r_n},
$$

故 $D\ge0$ 等价于精确整数不等式

$$
2^T r_0\le r_n^5.
$$

又 $2^T r_0=5^n r_n+C_n$（$0<C_n<5^n$），故充分条件为

$$
r_n^4\ge5^n\left(1+\frac1{r_n}\right).
$$

**有限核验（精确）。**

1. 对所有 $r<503$、$r\equiv3\pmod5$ 的词级最小起点，顶层
   $k=0$ 链长至多 7（最长为 $r=23,n=7$）。因此
   $n\ge8\Rightarrow r_n\ge503$。
2. 对基词 $r_0\le5\cdot10^6$ 的全部 2714 条链，整数不等式
   $2^T r_0\le r_n^5$ 零违反；最紧余量
   $r_n^5-2^T r_0=4601847$ 在 $(r_n,n,r_0,T)=(23,7,3583,9)$ 取得。

**最小未解子类（更新）。** 解析证明对所有紧链
$r_n^4\ge5^n(1+1/r_n)$，即等价地证明链长下界
$r_n\ge5^{n/4}(1+1/r_n)^{1/4}$。数值上最紧样本仍是
$n=7,r_n=23$（阈值约 $16.9$）；该不等式一旦证明，
整数不等式成立，D≥0 成立，阈值树归纳闭合 L-B'a。

**松弛自动机失败记录。** 若只要求链的残差条件而忽略
“基词顶层 $k\ge1$”与“每步都是词级最小起点”，则对每个
$n\le12$ 都出现 $r_n\le21$ 的链，且 $r_n^4<5^n$。
因此词级最小性/基词条件是链长界的本质部分，不能去掉。

**数据校准（正确分组）。** 长度 $L\le22$ 的全部约束词中：

| 残差类 | 最小 $\delta$ | 代表 $(r,S)$ |
|---|---:|---:|
| $r\equiv3\pmod5$ | $0.7236$ | $(23,19)$ |
| $r\equiv8\pmod{25}$ | $4.5157$ | $(183,15)$ |
| $r\equiv4\pmod{25}$ | $1.4580$ | $(29,17)$ |
| $r\equiv23\pmod{25}$ | $0.7236$ | $(23,19)$ |

$r\equiv3$ 的最紧余量为 $\eta=5\log_2 23-19\approx3.6178$，即
$r\ge2^{S/5}\cdot2^{0.7236}$。L-B'a 只需 $\eta\ge0$。

另记录：$r\equiv3$、$L\le20$ 的词中，词级 $k=0$ 前插链最长
$n=11$（$S=23,r=1610613$），最大 $n/S=0.478$。

## 攻击角度记录

### 角度 1：前插递推与 5-adic 源类树

已把 L-B'a 的 $k=0$ 前插化为源类阈值系统：

$$
\theta_{C'}\le \theta_C-\Lambda_t(\rho_C),
$$

其中 $C\to C'$ 由 $r'=(2^tr-1)/5$ 决定，$\rho_C$ 是源类最小词起点。
$k\ge1$ 分支由 L-B'c 闭合。逐层类表（mod 25/125）与危险区间为空已记录在
`s_x3_3_log_bound_candidate.md`。未完成：无穷层源类树的解析闭合。

### 角度 2：U=2 精确公式与 2-adic 高位比特

通过 $c=3r+1$ 参数化把 U=2 化为 $n\ge1$（已闭合，P1）与
$n=0$（P2 部分闭合）两个子类。$n=0$ 时
$c_2=2^L-A_0$，$A_0$ 是
$2^{m_2+1}5^{-m_2}+2^{m_1}5^{-m_1}\bmod2^L$ 的最小正代表，
其 2-adic 结构给出 $c_2=2^{m_1}u$ 与 $u\equiv0\pmod5$。未完成：
对 $m_1$ 小的 $u$ 下界。

### 角度 3：反证结构约束

若 $r<T=2^{(L+2)/5}$，则 $C=(3r+1)/5<(3T+1)/5$，而
$C=(2^L q_0-R)/5^{m_2+1}\ge(8\cdot2^L-R)/5^{m_2+1}$，得到

$$
5^{m_2+1}>\frac{40\cdot2^L}{3T+6}.
$$

同时 $n=0$ 时 $c_2<3T+1$ 给
$m_1<\log_2((3T+1)/5)$。二者合并给出
$m_2\gtrsim0.34L$、$m_1\lesssim0.2L$，但尚无矛盾。该角度把
未解子类压缩到 $n=0$ 且 $m_1$ 小的范围。

## 最小未解子类

U=2、$r\equiv3\pmod5$、$n=0$、且
$m_1<(L+2)/5+\log_2(3/5)$（$m_1$ 奇）或
$m_1<(L+2)/5+\log_2(3/25)$（$m_1$ 偶）时，P1 不适用且 P2 的粗下界不足。

具体样本（全部通过数值界，余量远大于 1，但尚无解析证明）：

| $L$ | $m_1$ | $m_2$ | $r$ | $S$ | $r/2^{(L+2)/5}$ |
|---:|---:|---:|---:|---:|---:|
| 19 | 8 | 14 | 117333 | 21 | 6384.02 |
| 20 | 3 | 14 | 168733 | 22 | 7992.23 |
| 20 | 9 | 15 | 46933 | 22 | 2223.04 |
| 21 | 4 | 15 | 67493 | 23 | 2783.05 |
| 21 | 10 | 16 | 18773 | 23 | 774.10 |

## 状态

L-B'a 未闭合。本轮新增：U=2 精确公式的 $n\ge1/n=0$ 二分、P1/P2 部分
闭合、$n=0$ 小 $m_1$ 精确反证约束；未完成的是 $n=0$ 小 $m_1$ 的 $u$
下界。所有计算为校准/精确结构复核，不作为证明步骤。

## 2026-08-06 continuation: unique k=0 parent and weight lemma

### Angle 4: deterministic parent map

For an odd minimal start $r$, at most one k=0 parent can be an odd word
start:

$$
h(r)=\frac{5r+1}{2}\quad(r\equiv1\pmod4),\qquad
h(r)=\frac{5r+1}{4}\quad(r\equiv7\pmod8),
$$

and no odd k=0 parent exists when $r\equiv3\pmod8$.

If $h(r)$ is again a word-level minimal start, then $r$ is the k=0
child of $h(r)$; otherwise $r$ is a root. Hence every k=0 chain is a
path in a directed graph where each node has one child and at most one
odd parent. The relevant terminal chains ending in $r\equiv3\pmod5$
use only nodes congruent to 3 or 4 modulo 5.

### Exact membership test

For odd $r$, let $w(r)$ be the first C3 word obtained by iterating
$V(n)=\operatorname{oddpart}(5n+1)$ until $n\equiv3\pmod8$, stopping if
some step has $v_2(5n+1)>2$. Then

$$
r\in W \iff w(r)\ne\emptyset \quad\text{and}\quad r_{\min}(w(r))=r.
$$

This is exact and gives a decision procedure for all ancestors of a
finite final start, not a bounded-word enumeration.

### Calibration with the exact membership test

For every odd $r\le2\cdot10^6$ with $r\equiv3\pmod5$, the exact
membership test gives the smallest final starts per chain length:

| $n$ | minimal $r_n$ | root $r_0$ |
|---:|---:|---:|
| 7 | 23 | 3583 |
| 8 | 503 | 96029 |
| 9 | 52233 | 24906823 |
| 10 | 20893 | 24906823 |
| 11 | 152583 | 113683583 |
| 12 | 61033 | 113683583 |
| 13 | 24413 | 113683583 |
| 18 | 170073 | 77340443933 |
| 20 | 54423 | 77340443933 |

No chain of length $n\ge21$ has a final start in
$[1,2\cdot10^6]$. These numbers are calibration, not proof.

### Partial proposition: weight lemma closes the chain inequality

Let $S_n$ be the weight of the final word. If a terminal chain of
length $n\ge8$ ending in $r_n\equiv3\pmod5$ satisfies

$$
S_n\ge3n-1,
$$

then the chain inequality holds. Proof sketch: the root is a k>=1
word, so $r_0\ge(2^{S_0+3}-1)/5$; from
$2^Tr_0=5^nr_n+C_n$ with $C_n<5^n$ and $S_n=S_0+T$,

$$
r_n\ge\frac{2^{S_n+3}-2^T-5^{n+1}}{5^{n+1}}
\ge\frac{2^{3n+2}-5^{n+1}-2^{n+1}}{5^{n+1}},
$$

and the right side is already far above $5^{n/4}$ for $n\ge8$.
For $n=7$, the only odd $r\equiv3\pmod5$ below 23 are 3 and 13; both
are ruled out as terminal words of length 7 (3 is the empty word, 13
is a root). For $n\le6$, the same bound plus the exact minimum table
is stronger.

### Minimal unresolved subcase

The remaining analytic task is the weight lemma

$$
S_n\ge3n-1
$$

for every terminal k=0 chain ending in $r_n\equiv3\pmod5$ with
$n\ge8$. Equivalently, with

$$
\varepsilon(r)=\left\lceil\frac{S(r)+2}{3}\right\rceil-d(r),
$$

one needs $\varepsilon(r)\ge1$ for every $r\equiv3\pmod5$ except the
known near-critical word $r=23$ (and the paired $r=9$ in the residue
4 case). Exact calibration up to $2\cdot10^6$ shows only the finite
low-slack list

$$
23,\ 73,\ 503,\ 54423;\qquad 9,\ 29,\ 21769,
$$

so the weight lemma is currently a finite-exception classification
conjecture rather than a proof.

## 关键修正：U≥3 的“defining k≥1 分支”推理无效

`s_x3_3_lb_ub2_reduction.md` 第 3-4 节声称：$U\ge3$ 时
$A_u>3\cdot2^S$，故 defining congruence

$$
5^L r+A_u=3\cdot2^S+k\,2^{S+3}
$$

中的 $k\ge1$，并由此套用 L-B'c 的
$r\ge(2^{S+3}-1)/5$。这一步把两个不同的 $k$ 混为一谈：

- defining congruence 的 $k$ 是无界整数；
- L-B'c 前插公式 $r'=(2^t(r+k2^{S+3})-1)/5$ 的 $k\in\{0,1,2,3,4\}$
  是模 5 提升参数。

精确反例：$m=23$ 的首 C3 词

$$
w=[2,1,1,2,1,1,1,2,2,2,2,1,1],
$$

有 $L=13$、$U=6\ge3$、$S=19$、$r=23$、$A_u=593468829$，
defining $k=6835\ge1$，但

$$
r=23<\frac{2^{22}-1}{5}=838860.
$$

因此“defining $k\ge1\Rightarrow r\ge(2^{S+3}-1)/5$”为假，
`s_x3_3_lb_ub2_reduction.md` 的 $U\ge3$ 闭合不能按现文接受。
L-B'a 的 $U\ge3$ 情形（至少含 $k=0$ 前插链）仍然开放；$m=23$ 本身满足
强界（$23^5\ge2^{19}$），不是 L-B'a 的反例，只是该证明步骤的反例。
