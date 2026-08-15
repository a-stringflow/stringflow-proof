# K4B 等号情形的精确缺口（2026-08-09）

状态：不闭合 K4。本文把 K4B 的剩余部分压缩成一个精确语句，
并标明每一步是必要条件还是充要条件。

## 1. 已形式化的归约

记号沿用 `lte_macro_k4_reduction.md`：

$$
n=2+v_2(a),\qquad
w=\frac{5^a-1}{2^n},\qquad
s=v_2(C-1),\qquad
u=\frac{C-1}{2^s}.
$$

在 `s=n` 时，K4B 的额外抵消为

$$
e=v_2\!\left(w+u+2^nwu\right).
$$

[LteMacro.lean](C:/Users/Ex_Je/Documents/数学研究/../lean/LteMacro.lean)
中已形式化：

- `twoValuation_add_eq_of_lt`、`twoValuation_add_eq_of_gt`：
  若 `v2(x)<v2(y)`，则 `v2(x+y)=v2(x)`；对称情形同理。
- `lteExtra_eq_val_of_lt`：若 `v2(w+u)<n`，则 `e=v2(w+u)`。
- `lteExtra_eq_n_of_gt`：若 `n<v2(w+u)`，则 `e=n`。
- `lteExtra_eq_add_of_eq`：若 `v2(w+u)=n`，则
  $$
  e=n+v_2\!\left(\mathrm{oddPart}(w+u)+wu\right).
  $$
- `lteExtra_eq_v2_w_add_five_pow_u`：恒等式
  $$
  e=v_2\!\left(w+5^au\right).
  $$
- `twoValuation_add_ge_succ_of_eq`：若 `v2(x)=v2(y)`，则
  `v2(x+y)≥v2(x)+1`。
- `lteExtra_ge_succ_of_eq_val`：若 `v2(w+u)=n`，则 `e≥n+1`。
- `macroValue_ge_two_n_add_one_of_eq_val`：同上条件下
  `V≥2n+1`。
- `../lean/AutomatonInterface.lean` 中：
  `mFailureCongruence_implies_candidate` 与
  `mFailureCongruence_iff_candidate` 把 `m` 型失败同余与
  唯一候选残差 `candidateMClass` 桥接起来。
- `../lean/AutomatonInterface.lean` 中新增
  `mFailureCongruence_iff_failureCongruence`：
  在 `H>=2` 且 `2^(W+1) | A+5^i*q+2^W` 时，`m` 型同余
  `(5m)%2^H=1` 与仿射失败整除
  `2^(W+H+1) | 5A+3*2^W+5^(i+1)*q` 严格等价（充要）。
- 同文件新增 `failureCongruence_height_bound`：若最小代表元
  `r<5^i` 且失败同余成立，则必有
  `2^(H+1) <= 5^(i+1)+3`（必要条件）。该不等式只压掉
  `H` 的尺寸级上限，不闭合局部引理，但给出了失败窗口高度的
  第一个严格形式化尺寸界。
- 同文件新增 `mValue_lower_bound`：由 `q>=2^{W_{j-1}}` 与
  `2^(W+1) | A+5^i*q+2^W` 严格推出
  `m * 2^(W-W_{j-1}+1) >= 5^i + 2^(W-W_{j-1})`
  （必要条件）。这是 `m=(r+1)/2` 的 q 下界尺寸不等式，
  是后续 `m_d>=2^{d+2}` 链的候选入口；单用它仍不足以闭合
  容量或估值条件。
- 同文件新增 `uOne_implies_height_one_failureCongruence` 与
  `capacityCondition_necessary`：在 `u_i=1` 且分子表示成立时，
  `H_i=1` 自动导致失败同余，因此局部引理成立蕴含 `H_i!=1`。
  这是“容量条件是估值条件必要条件”的 Lean 形式化；它没有证明
  `H_i>=3` 本身。
- 同文件新增 `failureCongruence_mono`、
  `uOne_implies_height_zero_failureCongruence`、
  `Hval_zero_or_odd` 与 `capacityCondition_from_localLemma`：
  失败同余随窗口高度单调，`H_i=0` 在 `u_i=1` 下同样自动失败，
  `Hval` 只取 0 或正奇数，因此局部引理成立时严格推出
  `3 <= Hval s`。这是容量条件必要性的完整 Lean 闭合，
  仍不证明从递推出发的 `H_i>=3`。
- 同文件新增 `uOne_implies_numerator_divisible`、
  `mIntervalLocalLemmaStatementFull` 与
  `localLemmaStatement_implies_mIntervalFull`：
  把仿射局部引理语句严格桥接到带 `u=1`、分子表示和最小代表元
  假设的一维 `m` 无候选语句。这是候选残差路线与局部引理本体
  之间的正式接口，仍不证明该一维语句本身。
- 同文件新增 `q_interval_preserved`：`delta=0` 单步保持
  `q in [2^{W_{j-1}},2^{W_j})` 的区间成员关系。该不变量是
  一维候选排除沿块内归纳的入口，本身不排除任何候选。
- 同文件新增 `minimal_representative_preserved`：`delta=0` 单步保持
  `r_i<5^i` 的最小代表元条件，与 `q_interval_preserved` 共同构成
  块内归纳的两个结构前提。
- 同文件新增 `A_bound_of_minimal`：由 `r<5^i` 与分子表示严格推出
  `A < 5^i * (2^W - q)`。这是最小代表元在“前缀分子余量”上的
  精确不等式，可作为候选排除时对 `A` 的尺寸约束。
- 同文件新增 `twoRun` 与 `twoRun_plus_one_mul`：对纯 `t=2` 游程，
  在每步可整性假设下严格证明闭式
  `(r_n+1)*4^n = 5^n*(r_0+1)`。这是块首容量失败候选分类
  `s=2^h` 的直接入口。
- 同文件新增 `twoRun_valuation`：在相同可整性假设下，若
  `r_0+1=2^u*s` 且 `s` 为奇数，则
  `v2(r_n+1)=u-2n`。这是纯 `t=2` 游程的 2-adic 窗口控制：
  每次 `t=2` 精确消耗 2 个 2-adic 位，不产生额外进位。
- 同文件新增 `t1_next_valuation`：对 `u=1` 状态，单步 `t=1` 的
  2-adic 窗口满足
  `v2(r'+1)=v2(5r+3)-1`。这给出 `t=1` 步的精确低位窗口，
  把后续混合游程的进位控制归约到 `v2(5r+3)` 的结构上界。
- 新增 `five_r_plus_three_affine` 作为仿射分子恒等式的共享引理，
  `failureCongruence_height_bound` 与高度一失败证明共用它。

因此 `s=n` 分支的额外抵消已被严格三态分解；只有第三态未闭合。

## 2.1 线性同余闭环

由 `5^a=1+2^nw`，`s=n` 时

$$
e=v_2\!\left(w+5^au\right).
$$

因为 `5^a` 是奇数，在模 `2^M` 下可逆，K4B 失败
`e≥m+2-n` 等价于唯一线性同余

$$
u\equiv -w\cdot5^{-a}\pmod{2^{m+2-n}},
$$

等价地

$$
C\equiv5^{-a}\pmod{2^{m+2}}.
$$

这正是原始宏步窗口同余 `2^{H_i+1}\mid5^aC-1`，因此 K4B
并没有引入新的进位结构；剩余工作仍是证明 `q_j` 的 2-adic
前缀不能命中该唯一残差类。

这一线性估值形式已在 `../lean/LteMacro.lean` 形式化为
`macroSuccessNat_iff_v2_w_add_five_pow_u_le`：在 `s=n` 且
`n≤m+1` 下，`macroSuccessNat a m C` 等价于
`v2(w+5^au)≤m+1-n`。失败侧的模零形式同时由
`macroFailureNat_iff_mod_eq_zero` 给出：
`¬ macroSuccessNat a m C ↔ (w+5^au) % 2^(m+2-n) = 0`。

## 2. 剩余语句（充要分支，整体为必要条件）

固定宏步 `p`，令 `X_p=2a`、`m=H_p-2a`。K4B 在
`v2(a)<m`、`s=n` 下要求

$$
e\le m+1-n.
$$

由第 1 节三态分解，在 `v2(w+u)=n` 分支内，这等价于

$$
\boxed{\;
v_2\!\left(\mathrm{oddPart}(w+u)+wu\right)\le m+1-2n
\;}
$$

这是 K4B 在 `s=n` 分支下的**充要条件**；对完整 K4 而言，
排除该分支或证明该不等式均为**充分**的闭合路线，缺一不可。

## 3. 等价同余形式

`v2(w+u)=n` 等价于 `w+u\equiv0\pmod{2^n}`，代入
`C=1+2^nu` 与 `2^nw=5^a-1` 得

$$
C\equiv 2-5^a\pmod{2^{2n}},
$$

即

$$
5r_p+3\equiv 4^a\left(2-5^a\right)\pmod{2^{2a+2n}}.
$$

在

$$
r_p=\frac{A_p+5^pq_j}{2^{W_p}},\qquad
q_j\in\left[2^{W_{j-1}},2^{W_j}\right)
$$

下，该同余给出 `q_j` 对模 `2^{W_p+2a+2n}` 的唯一残差类。
由于模指数至少 `W_j+4`，区间内至多一个候选；仍需证明该候选
不存在，或对该候选直接验证剩余不等式。

这一唯一性所需的 2-adic 工具已在 `../lean/LteMacro.lean` 形式化：
`twoValuation_mul_odd`、`dvd_two_pow_of_odd_mul`、
`five_pow_odd`、`twoValuation_five_pow_mul`、
`five_inv_unique`（`5` 在模 `2^H` 下的逆元唯一），
并在 `../lean/AutomatonInterface.lean` 中给出
`candidateMClass_unique`。

## 4. 不弱化

常数 `13`、`m` 定义、`j-t_j` 与 `W_{j-1}` 的区分均未改动；
本文不声明 K4、局部引理或 7 发散闭合。

## 5. 与块首尾部候选的耦合（下一步入口）

设当前块的重置步为 `j`，上一块的偶数终端为 `r_{j-1}+1=5^k s''`，
其中 `s''` 就是上一块最后一个宏步的终端奇部 `C'_N`。由
`local_lemma_terminal_s6_equivalence.md` 推论 2.2，
上一块最后一个宏步满足 `V_N=2k`。

若上一块已满足终端 S6（即归纳假设 `H_e≥1`），则对最后一个宏步有

$$
V_N=2k\le m_N+1.
$$

于是 `t_j=2` 的尾部候选

$$
s''+\delta5^{j-1-k}=2^{u_j+2}t,
\qquad 0<s''<5^{j-1-k},
$$

要求在 `s''=C'_N` 上实现一个高 2-adic 残差；而 `C'_N` 的
2-adic 行为由三态 `s'` 递推与 `lteExtra` 三态分解完全控制。
因此闭合顺序应为：

1. 用上一块 S6 的 `V_N=2k≤m_N+1` 约束最后一个宏步的
   `V_N` 与终端奇部 `C'_N`；
2. 把 `C'_N` 的 `s'` 三态递推代入两个尾部候选方程；
3. 证明候选残差与可达的 `C'_N` 不相容。

这一节只给出衔接方向，不声明尾部候选已被排除。

### 5.1 终端奇部的显式三态形式

设上一块最后一个宏步为 `(a,C)`，`s=v2(C-1)`，
`V=2k` 为该宏步的估值。终端奇部 `s''=C'` 按 LTE 三态有
严格显式形式：

- `s<n`：`V=s=2k`，且
  $$
  s''=2^{n-2k}w+2^nwu+u.
  $$
- `n<s`：`V=n=2k`，且
  $$
  s''=w+2^{s-2k}u\left(1+2^{2k}w\right).
  $$
- `s=n`：`V=n+e=2k`，且
  $$
  s''=\frac{w+u+2^nwu}{2^e}.
  $$

前两式已在 `LteMacro.lean` 中形式化为
`macroNextC_lt_expand`、`macroNextC_gt_expand`；第三式是
`lteExtra_eq_add_of_eq` 的直接推论。把这三式代入两个尾部
候选方程，即可把“上一偶数终端不可达”进一步化为
`(s'',u,w,k,u_j,j)` 的纯算术相容性语句。
