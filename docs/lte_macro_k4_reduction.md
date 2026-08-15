# 宏步窗口不等式的 LTE/K4 归约（2026-08-08 续）

状态：**部分闭合，K4 本体未证**。本文把宏步端点不等式

$$
v_2(5^a C_p-1)\le H_p-2a+1
$$

严格改写为 LTE 三态分解与 K4 的两族等价形式，并给出这一等价的完整证明。
K4 本身（`s=v_2(C-1)` 的 2-adic 前缀控制，以及 `s=n` 时的额外抵消上界）
仍未从 `δ=0` 递推、`q_j` 区间和最小代表元性质推出；块首容量尾部方程
仍未排除。所有语句都标明必要/充分条件。
本轮新增：`L1+L2+K4B` 三候选合取可严格闭合宏步不等式，
证明见 `local_lemma_terminal_s6_equivalence.md` 第 3 节。
块首尾部方程的进一步收窄（`t_j=2` 时 `δ∈{1,3}`，以及缺口
`k≥0.1386j-4.876`）见 `block_head_tail_reduction.md`。

## 1. 记号

沿用 `p_adic_window_route.md` 第 11 节与 `local_lemma_s6_reduction.md`
第 2 节。固定一个 `δ=0` 块，`j` 是最后重置步，`t_j=W_j-W_{j-1}`。
设 `p` 是块内 `u_p=1`、`X_p=2a` 的宏步起点，`i=p+a` 是宏步端点。记

$$
C=\frac{5r_p+3}{2^{2a}},\qquad
m=H_p-2a,\qquad
V=v_2(5^aC-1),
$$

则 `C` 为正奇整数，宏步端点 `i` 的局部引理等价于

$$
V\le m+1,
$$

即失败阈值为 `V\ge m+2`。端点 `H_i=m+2`。

再令

$$
n=2+v_2(a),\qquad
w=\frac{5^a-1}{2^n},\qquad
s=v_2(C-1),\qquad
u=\frac{C-1}{2^s}.
$$

## 2. LTE 三态分解（严格恒等式，充要）

**引理 2.1（LTE 分解）.**
设 `a≥1`，`C≥1` 为奇整数，则

$$
5^aC-1=(5^a-1)C+(C-1)=2^nwC+2^su.
$$

进一步：

1. 若 `s<n`，则 `V=s`；
2. 若 `s>n`，则 `V=n`；
3. 若 `s=n`，则

$$
V=n+v_2(w+u+2^nwu),
$$

且 `w+u+2^nwu=(5^aC-1)/2^n`。

**证明.** 对 `a≥1` 成立

$$
v_2(5^a-1)=2+v_2(a)=n,
$$

这是标准 2-adic LTE：`a` 为奇数时
`(5^a-1)/(5-1)=5^{a-1}+\cdots+1` 是奇数个奇数的和，故赋值为 2；
`a` 为偶数时用 `v_2(5^a-1)=v_2(5-1)+v_2(5+1)+v_2(a)-1=2+v_2(a)`。
因此 `w` 为奇数。又 `C` 为奇数且 `s=v_2(C-1)`，故 `u` 为奇数。

代入恒等式：

- `s<n` 时

$$
5^aC-1=2^s\bigl(2^{n-s}wC+u\bigr),
$$

括号内第一项为偶数、第二项为奇数，括号为奇数，故 `V=s`。
- `s>n` 时

$$
5^aC-1=2^n\bigl(wC+2^{s-n}u\bigr),
$$

括号内第一项为奇数、第二项为偶数，括号为奇数，故 `V=n`。
- `s=n` 时

$$
5^aC-1=2^n(wC+u)
=2^n\bigl(w(1+2^nu)+u\bigr)
=2^n(w+u+2^nwu),
$$

故第三式成立。$\square$

该引理是严格恒等式，不依赖 `q_j` 区间或最小代表元；它只使用
`a,C` 的定义与 2-adic 奇偶结构。

## 3. K4：与宏步不等式严格等价（充要）

**定义 3.1（K4）.**
沿用第 1、2 节记号。K4 是下列两族语句：

1. **族 A**（`v_2(a)≥m`）：
   $$
   s\le m+1.
   $$
2. **族 B**（`v_2(a)<m`）：
   $$
   s\ne n\quad\text{或}\quad
   v_2(w+u+2^nwu)\le m+1-n.
   $$

**引理 3.2（K4 ⇔ 宏步不等式，充要）.**
在 `a≥1`、`C≥3` 为奇整数的前提下，宏步不等式 `V≤m+1` 等价于 K4。

**证明.** 分两族：

- 族 A：`v_2(a)≥m` 蕴含 `n=2+v_2(a)≥m+2`。由引理 2.1，
  `V` 的三种取值 `s`、`n`、`n+v_2(\cdots)` 中，只要 `s≥m+2` 就都有
  `V≥m+2`；反过来若 `V≥m+2`，当 `s<n` 时 `V=s`，当 `s>n` 时
  `V=n≥m+2` 且 `s>n≥m+2`，当 `s=n` 时 `s=n≥m+2`，因此必有
  `s≥m+2`。故
  $$
  \text{失败}\iff s\ge m+2,
  $$
  即
  $$
  \text{成功}\iff s\le m+1.
  $$
- 族 B：`v_2(a)<m` 蕴含 `n=2+v_2(a)≤m+1`。由引理 2.1：
  - `s<n` 时 `V=s≤n-1≤m`，自动成功；
  - `s>n` 时 `V=n≤m+1`，自动成功；
  - `s=n` 时 `V=n+v_2(w+u+2^nwu)`，失败当且仅当
    $$
    v_2(w+u+2^nwu)\ge m+2-n.
    $$
  故成功等价于 `s≠n` 或 `v_2(w+u+2^nwu)≤m+1-n`。$\square$

因此 K4 与原宏步不等式**严格等价**；证明 K4 即可闭合宏步端点。

## 4. `C=1` 不可能：`s` 良定义（严格）

**引理 4.1.**
若 `C=(5r+3)/2^{2a}` 为整数且 `a≥1`，则 `C≠1`。特别地 `C-1>0`，
`s=v_2(C-1)` 有有限良定义。

**证明.** 若 `C=1`，则 `5r+3=4^a`。模 5 得
`3≡4^a≡(-1)^a (mod 5)`，而 `(-1)^a∈{1,4}`，矛盾。$\square$

这是必要条件，用来保证 K4 中 `s` 有限；它不是充分条件。

## 5. K4 的显式 2-adic 线性形式（必要且充分）

把 `C` 的定义代入 `V`：

$$
V=v_2(5^aC-1)
=v_2\Bigl(5^a(5r_p+3)-2^{2a}\Bigr)-2a.
$$

再用 `2^{W_p}r_p=A_p+5^pq_j` 得

$$
L_p:=5^{p+a+1}q_j+5^a\bigl(5A_p+3\cdot2^{W_p}\bigr)-2^{W_p+2a},
$$

$$
V=v_2(L_p)-W_p-2a.
$$

对 `s≥S` 的控制等价于唯一残差类

$$
r_p\equiv5^{-1}(4^a-3)
\pmod{2^{2a+S}},
$$

等价地

$$
5^{p+1}q_j\equiv
2^{W_p+2a}-\bigl(5A_p+3\cdot2^{W_p}\bigr)
\pmod{2^{W_p+2a+S}}.
$$

当 `s=n` 时，额外抵消量满足

$$
v_2(w+u+2^nwu)
=V-n
=v_2(L_p)-W_p-2a-n.
$$

上述同余与线性形式均为**充要**入口：K4 现在只剩两个任务，
一是用 `q_j∈[2^{W_{j-1}},2^{W_j})` 与 `r_p<5^p` 排除
`s≥m+2`（族 A）或 `s=n` 后 `v_2(L_p)` 过大（族 B），
二是证明 `v_2(w+u+2^nwu)` 的上界。两者都还没有从递推闭合。

## 6. 宏链递推（严格恒等式，后续归纳入口）

设 `p→p'` 是同一块内相邻两个 `u=1` 状态，且
`X_p=2a`、`X_{p'}=2a'`（即 `p'` 仍是宏步起点）。记
`C,C'` 为对应正奇部，则

$$
C'=\frac{5^aC-1}{2^{2a'-1}},
$$

$$
p'=p+a,\qquad
m'=m+2-2a'.
$$

**证明.** 由宏步恒等式
`5r_{p'}+3=2(5^aC-1)` 与
`5r_{p'}+3=2^{2a'}C'` 直接相除。$\square$

这条递推是严格的，把 K4 从“单点语句”升级为沿宏链的递推入口；
它本身不闭合 K4，因为 `s` 与 `v_2(w+u+2^nwu)` 的逐点控制
仍需要 `q_j` 区间。

**引理 6.3（`s` 的宏链递推，严格恒等式）.**
沿用第 6 节记号并设 `s'=v_2(C'-1)`，则按 LTE 三态有：

1. 若 `s<n`，则 `V=s`，`2a'=s+1`，且
   $$
   s'=v_2\!\Bigl(u-1+2^{n-s}w(1+2^su)\Bigr);
   $$
2. 若 `s>n`，则 `V=n`，`2a'=n+1`，且
   $$
   s'=v_2\!\Bigl(w-1+2^{s-n}u(1+2^nw)\Bigr);
   $$
3. 若 `s=n`，则 `V=n+e`，`e=v_2(w+u+2^nwu)`，
   `2a'=n+e+1`，且
   $$
   s'=v_2\!\left(\frac{5^aC-1}{2^V}-1\right).
   $$

**证明.** 由第 6 节 `C'=(5^aC-1)/2^{2a'-1}` 与引理 2.1 逐项代入。
情形 1 中 `V=s`，`D=2^s(u+2^{n-s}wC)`；情形 2 中
`V=n`，`D=2^n(wC+2^{s-n}u)`；情形 3 中 `D=2^{n+e}O`。代入
`C'-1=(D-2^V)/2^V` 即得。$\square$

该递推把“逐位进位位”替换成 `u-1`、`w-1` 与
`2^{|s-n|}\cdot\text{odd}` 之间的一次 2-adic 相消；这是后续沿宏链
归纳控制 `s` 与 `e` 的精确入口，仍未闭合。

## 7. 候选归约（sanity 支持，非证明）

下列三个候选语句若被证明，即闭合 K4：

1. **L1（排除族 A，充分条件）：**
   $$
   m\ge v_2(a)+1.
   $$
   若成立，则 `v_2(a)<m` 恒成立，K4 只剩族 B。
   更强的候选 **L1'** 是
   $$
   m\ge 2v_2(a)+1.
   $$
   若 L1' 成立，则 `v_2(a)<m` 且族 A 自动为空，因为
   `v_2(a)≥m≥2v_2(a)+1` 给出 `v_2(a)≤-1`，矛盾。
   基例中 L1' 的最小余量 `m-2v_2(a)` 为 1（紧路径 `p=35` 取等）。
2. **L2（`s` 上界，充分辅助）：**
   $$
   s\le m+2,
   $$
   且当 `s=m+2` 时 `s>n`。在族 B 下该语句蕴含
   `s<n` 或 `s>n` 时自动成功，只剩 `s=n` 情形。
3. **K4B（额外抵消，充分且族 B 下等价于成功）：**
   $$
   s=n\ \Longrightarrow\ v_2(w+u+2^nwu)\le m+1-n.
   $$

L1、L2、K4B 均为充分条件；K4B 在族 B 下同时是必要条件。
当前精确基例（深度 24 全前缀 + 紧路径到 37 + 贪心确定性路径到
深度 2000）中：

- L1 的最小余量 `m-v_2(a)` 为 1（深度 24 的 `i=13`）；
- L1' 的最小余量 `m-2v_2(a)` 为 1（紧路径 `p=35` 取等）；
- L2 的最大超界 `s-(m+2)` 为 0，且该点 `s=m+2>n`，不造成失败；
- K4B 的最小余量在紧路径 `p=35` 处为 0（取等）。

这些只作 sanity，不作证明；证书见 `lte_k4_sanity_certificate.txt`。
深度 2000 贪心路径共检查 396 个宏步，K4 零违反。

## 8. 块首容量尾部方程（现状）

块首容量 `u_j≤2(j-t_j)+11` 已归约为两个尾部候选方程
（`local_lemma_s6_reduction.md` 第 11 节），均尚未排除：

- `t_j=2`：

$$
s''+\delta5^{j-1-k}=2^{u_j+2}t,
\qquad
s''<5^{j-1-k},\quad
t<4\cdot5^{j-1-k}/2^{u_j+2},
$$

其中 `s''` 为奇数、`5∤t`、`δ∈{1,2,3}`；
- `t_j=1`：

$$
5^{k+1}s''+5^j-2=2^{u_j+1}s,
$$

其中 `s` 为奇数、`5∤s`、`s<5^j/2^{u_j}`，且有固定的
模 `5^{k+1}` 残差。

小 `j` 已由大小/模 5 排除（`t_j=2` 时 `j≤35`，`t_j=1` 时
`j≤39`）；无限尾部需要上一偶数终端
`r_{j-1}+1=5^ks''` 的可达性，目前开放。

## 9. 未闭合清单

1. 族 A 排除：证明 `m≥v_2(a)+1`，或直接证明
   `v_2(a)≥m ⇒ s≤m+1`。本轮奇偶收窄见
   `macro_chain_parity_l1_reduction.md`：非首宏步的 L1 只剩
   `V=m` 例外族与 `a>=8`，对应 Lean 算术在 `../lean/MacroWindow.lean`；
2. 族 B：证明 `s=n ⇒ v_2(w+u+2^nwu)≤m+1-n`，
   即 K4B；
3. 块首容量尾部两方程：证明不存在可达的上一偶数终端；
4. 上述闭合后按现成链衔接：
   `局部引理 → B → L → C → G_i≥1 → c_k≥4(4/5)^k
   → m_d≥2^{d+2} → D0 + SURV-EX + TD0 → 5x+1 在 7 发散`。

Lean 接口 `../lean/LteMacro.lean` 已编译。其中
`twoValuation_mul_two_pow_eq`、`twoValuation_mul_two_pow`、
`pow_two_even_mod`、`even_mul_mod_two`、`even_add_odd_mod_two`、
`macroNumerator_split`、`mul_assoc_left_comm`、`lteFactor_lt`、
`lteFactor_gt`、`lteThreeWayStatement`、`four_pow_mod_five`、
`macroOddPartNotOneStatement`、`macroChainRecurrenceStatement`、
`macroSuccess_iff_val_le`、`k4_familyA_iff`、`k4_familyB_iff`、
`k4EquivalentStatement` 已给出证明。
`lteThreeWayStatement` 现采用合取形式，并补充了正确前提
`lteW a % 2 = 1` 与 `C - 1 = 2^s * lteU C s`；三态分解定理
`lteThreeWayTheorem` 及其包装 `lteThreeWayStatement_proof` 已编译通过。
`k4EquivalentStatement` 现在也补充了 `lteW a % 2 = 1` 前提，
并已证明（含族 A、族 B 两个方向与整除性引理
`twoValuation_le_iff_not_dvd_pow`）。宏步分解引理
`macroNextC_lt`、`macroNextC_gt`、`macroNextC_lt_sub`、
`macroNextC_gt_sub` 与三态递推 `macroChainSCasesStatement` 已证明；
后者的前提补充为 `lteW a % 2 = 1`（标准 LTE 奇性），
证明见 `macroChainSCasesStatement_proof`。另外，第 3 节的
`L1+L2+K4B` 充分条件已形式化为 `k4SufficientStatement` 并给出
`k4SufficientStatement_proof`；该定理把宏步不等式闭合缩减为
三个开放语句本身，不声明 K4 本体已证。新增严格 2-adic
三角恒等式 `twoValuation_add_eq_of_lt`、`twoValuation_add_eq_of_gt`，
以及它们在三态递推上的推论 `macroNextC_lt_val_of_u_min`、
`macroNextC_gt_val_of_w_min`、`macroNextC_lt_val_of_u_eq_one`：
当 `v2(u-1)≠n-s`（或
`v2(w-1)≠s-n`）时，下一宏步的 `s'` 精确等于较小者；
进位只能发生在两边 2-adic 估值相等的情形，即第 11 节的
单比特进位位。对 `s=n` 的额外抵消，新增
`lteExtra_eq_val_of_lt` 与 `lteExtra_eq_n_of_gt`：
若 `v2(w+u)<n` 则 `lteExtra=v2(w+u)`，若 `n<v2(w+u)` 则
`lteExtra=n`；等号情形由 `lteExtra_eq_add_of_eq` 给出精确分解
`lteExtra = n + v2(oddPart(w+u)+w*u)`。因此 K4B 的开放点只剩
`v2(w+u)=n` 时对该额外进位项的进一步控制。K4 本体与块首容量
尾部仍为开放缺口；该等号情形的精确语句与同余形式见
`k4b_equality_gap.md`。

## 10. 主链衔接状态

- 宏步不等式 ⇔ K4（本文已证，充要）；
- 局部引理 ⇔ 宏步端点不等式 ∧ 块首估值不等式
  （`local_lemma_s6_reduction.md` 第 12 节，充要）；
- 块内局部引理 ⇔ 最后一个 `u=1` 状态成立
  （余量单调，第 3 节，充要）；
- 局部引理 → B → L → C → `G_i≥1` 的代数衔接已写在
  `capacity_lemma_reduction.md`；
- `G_i≥1 → c_k≥4(4/5)^k → m_d≥2^{d+2} → D0 + SURV-EX + TD0 → 7 发散`
  的衔接见 `5x1_7_divergence_main_chain.md`。

因此当前唯一未闭合点是 K4（第 9 节第 1、2 项）与块首容量尾部
（第 9 节第 3 项）；本文不声明局部引理或 7 发散已完成。
