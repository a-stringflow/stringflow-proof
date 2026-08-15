# Lean 2-adic 窗口控制状态清单（2026-08-09）

状态：**未闭合**。本文只记录已编译的 Lean 定理、已确认的死路与
剩余精确缺口，不再重复推导同一批小引理。

## 1. 已编译的 Lean 定理

### `../lean/MacroWindow.lean`

- 宏步闭式 `(r_a+1)*2^(2a-1)=5^(a-1)*(5r_0+3)`
- 宏步估值 `v2(r_a+1)=v2(5r_0+3)-(2a-1)`
- 偶宏步端点 `v2(r_a+1)=1`，奇宏步终端 `v2(r_a+1)=v2(5r_0+3)-(2a+1)`
- 宏步端点恒等式 `r_a+1=2*5^(a-1)*C`、`5r_a+3=2(5^a*C-1)`
- 非终段宏步余量奇偶：`V<=m`、`m'` 为正奇数、`V!=m -> m'>=3`
- `V=m` 例外族：`m%4=3` 时下一宏步 L1 必失败

### `../lean/WordWindow.lean`

- 词轨道恒等式 `2^S*orbit=5^L*x+A_L`
- 端点 C3 同余 `(5^L*x+A_L)≡3*2^S (mod 2^(S+3))`
- 同一词在 `x<2^(S+3)` 内代表元唯一
- `t=2` 候选 `40m+23>330` 的低权排除 `S<=6` 不可能
- `A_L<5^L`、`A_L<=5^L-4^L`
- 词末步权重 `wordLast<=S`
- `A_L≡2^(S-last) (mod 5)`
- `2^(n+4)≡2^n (mod 5)`
- `t=2`/`t=1` 父节点模 8 分类与首步权重分类
- `p≡3 (mod 8)` 时 `8 | 5p+1`（首步至少 `t=3`，父节点不在 `W`）
- `invOdd`/`invOdd_spec`：奇数模 `2^(n+1)` 的 Hensel 提升逆元
  `(a*invOdd a n)≡1 (mod 2^(n+1))`
- `wordRepresentative`/`wordRepresentative_spec`：显式代表元
  `((3*2^S+A) 的 wrapped 值 * invOdd (5^L) (S+2)) mod 2^(S+3)`
  满足端点 C3 同余式

## 2. 已确认的死路

- `t=1` 低权排除不成立：`B=213,293` 满足 `B=20m+13`、`S=6`、
  `B<2^(S+3)`；不能仿照 `t=2` 用 `S(B)>=7`。
- d0 文档旧语句 `5p+1≡0 (mod 16), t1>=4` 不成立：
  `m=7` 时 `p=379`、`5p+1≡8 (mod 16)`；精确语句为
  `8 | 5p+1`，即 `t1>=3`。
- 局部引理路线的 L1 奇偶归纳只把范围收窄到首宏步、`V=m`
  （`m≡1 mod 4`）与 `a>=8`，没有闭合族 A。

## 3. 剩余精确缺口

### 3.1 `ρ_w` 显式公式

引理 34.1 的完整 `iff` 形式：

```text
x ∈ W 且首词为 w  ⇔  x = ((3*2^S - A_L) * 5^(-L) mod 2^(S+3))
```

当前 Lean 已把 34.1 的语义拆成两层，均已编译：

- 子语句：窗口内
  `(wordValid w x ∧ wordOrbit w x % 8 = 3) ↔ x=ρ_w`；
- 完整目标：新增 `wordFirst w x`（每个真前缀都未到 C3，末点 C3），
  并证明 `wordFirst w x ↔ x=ρ_w`。

完整定理是 `word_representative_iff_first`：对 `{1,2}` 词
`w`（`wordOK w` 且逐项 `1<=t`），在 `x<2^(S+3)` 窗口内
“首个 C3 词恰为 `w`”当且仅当 `x=ρ_w`。
`wordFirst_of_wordValid` 负责补上此前缺失的“没有更早 C3”。

### 3.2 词端点 CRT

由 `A_L≡2^(S-last) (mod 5)` 继续推出：

```text
末步 t=1  ⇒  y≡3 (mod 40)
末步 t=2  ⇒  y≡19 (mod 40)
```

当前 5-adic 输入已闭合，2-adic `y≡3 (mod 8)` 已闭合，CRT 合并未写。
CRT 合并已于 2026-08-09 闭合：
`c3_mod40_of_mod8_mod5/mod4` + `word_endpoint_crt_last_one/two`，
见第 5 节。

### 3.3 幸存公式 `m_w`

推论 35.4 的完整参数化：

```text
q_0 = (-N/40 * 2^(-S) mod 5^L)
m_w = (2^S * q_0 + N/40) / 5^L
```

推论 35.2 的 `q` 存在性方向已闭合（见第 5 节第 7 项）；
推论 35.4 的正向 `m` 参数化已闭合（见第 5 节第 9 项）：
对合法幸存者 `B=40m+23`，存在整数 `q` 使
`m=(2^S*q+N/40)/5^L`，前提是余额
`N=2^S*y_0-A_L-23*5^L` 非负（`hpos`）。
剩余是：证明 `hpos` 对目标候选区间成立，并把 `q` 写成模
`5^L` 的显式代表元 `q_0=(-N/40)*2^{-S} mod 5^L`。
后者需要模 `5^L` 的逆元。

### 3.4 最终轨道深度条件

```text
d(40m+23)=n    或    d(20m+13)=n
```

这是 D0 的最终解析缺口：候选 `B` 的首个 C3 词轨道必须恰好连续
`n` 步保持 `W` 成员。

## 4. 建议的下一步

1. ~~闭合 `wordRepresentative` 的“合法走完 `w` 且末点 C3”方向~~
   （已完成，见第 5 节）；完整“首词为 `w`”已由
   `wordFirst_of_wordValid` + `word_representative_iff_first` 闭合。
2. ~~用 `wordA_mod_five_of_wordLast` 闭合词端点 CRT~~（已完成，见第 5 节）；
3. 用幸存公式把候选压缩到有限同余类（推论 35.2 已闭合，
   还差推论 35.4 的 `q_0`/`m_w` 显式解）；
4. 对压缩后的候选证明 `d(B)=n` 无解。

本文不声明 D0、局部引理或 7 发散已完成。

## 5. 2026-08-09 新增：`WordWindow.lean` 解析闭合

本轮不再扫描，全部从递推和固定模 CRT 推出，已编译通过：

1. `wordValid_of_endpoint_congruence`：若
   `(5^L*x+A_L) ≡ 3*2^S (mod 2^(S+3))`，则词合法且末点 C3。
   这是 `wordRepresentative` 反方向的归纳核心。
2. `wordRepresentative_lt` / `wordRepresentative_valid` /
   `word_representative_iff`：证明窗口内
   `(wordValid w x ∧ wordOrbit w x % 8 = 3) ↔ x=wordRepresentative w`。
   这只含“合法走完 `w` 且末点 C3”，不含“没有更早 C3”。
   随后用 `wordFirst` / `wordFirst_of_wordValid` /
   `word_representative_iff_first` 补上“没有更早 C3”，
   完整 34.1 已闭合。
3. `c3_mod40_of_mod8_mod5` / `c3_mod40_of_mod8_mod4`：
   固定 CRT，`y≡3 mod 8` 与 `y≡3 mod 5` 得 `y≡3 mod 40`，
   `y≡3 mod 8` 与 `y≡4 mod 5` 得 `y≡19 mod 40`。
4. `wordOrbit_mod_five_of_last_one/two`：末步 `t=1/2` 决定
   末点 `y≡3/4 mod 5`，由 `wordValid` 结构归纳直接推出。
5. `word_endpoint_crt_last_one/two`：完成引理 35.1 的端点 CRT。
6. `mul_two_pow_mod_of_mod8` / `word_valid_of_orbit_affine`：
   把“仿射轨道值等于 `2^S*y` 且 `y≡3 mod 8`”直接桥接到
   词合法与 C3 末点，是幸存公式反方向的入口。
7. `word_valid_of_survivor` / `word_survivor_rev_last_one/two` /
   `word_survivor_iff_last_one/two`：完成推论 35.2 的双向等价，
   即词首合法 C3 端点当且仅当仿射轨道值来自
   `3+40q`（末步 1）或 `19+40q`（末步 2）。
8. `wordFirst` / `wordValid_of_wordFirst` /
   `wordFirst_of_wordValid` / `word_representative_iff_first`：
   闭合完整引理 34.1；“首个 C3 词恰为 `w`”与 `x=ρ_w`
   在窗口内 iff，含“没有更早 C3”的证明。
9. `survivor_balance_ge/eq` / `word_survivor_m_equation` /
   `word_survivor_m_formula_general` /
   `word_survivor_m_formula_last_one/two`：
   闭合推论 35.4 的正向参数化，即合法幸存者
   `B=40m+23` 满足 `m=(2^S*q+N/40)/5^L`
   （在 `hpos` 非负余额假设下）。

剩余精确缺口：
- 推论 35.4 的 `hpos` 非负余额界与显式 `q_0` 逆元形式
  （需模 `5^L` 逆元）；
- 最终轨道深度条件 `d(40m+23)=n` 或 `d(20m+13)=n`；
- 局部引理/K4 路线仍开放。

## 6. 2026-08-09 新增：模 5 逆元、显式 `q_0` 与 `q_V` 窗口

本轮新增两个已编译 Lean 文件，全部无 `sorry`/`admit`：

### `../lean/ScratchLift.lean`

- `invMod5` / `invMod5_spec`：模 5 逆元；
- `invMod5_lift_spec`：Hensel 单步提升；
- `invFive` / `invFive_spec`：任意模 `5^(n+1)` 逆元。

### `../lean/SurvivorExplicit.lean`

- `survivorQ0`：`q_0 = (-N/40 * 2^{-S} mod 5^L)` 的最小非负代表；
- `survivor_q_mod`：`q ≡ q_0 (mod 5^L)`；
- `survivor_m_explicit`：
  `m = (P*q_0+N/40)/5^L + P*k`；
- `word_survivor_m_explicit_general/last_one/last_two`：
  推论 35.4 的显式 `q_0` 参数化，仍以 `hpos` 非负余额为前提。

### `../lean/QWindow.lean`

- `badResidue`：`q_V = (-(5A+3*2^W) * 5^{-(i+1)}) mod 2^E`；
- `carryBalance`：`B_i = ((q_V-q_i)/2^W) mod 2^(H+1)`；
- `carryBit`：`c_i` 是 `q_V` 提升到 `2^(W+H+2)` 时在位置
  `W+H+1` 的位；`badResidueLift` 是带该位的提升值；
- `badResidue_spec`：`5^(i+1)*q_V ≡ -(5A+3*2^W)`；
- `badResidue_eq_of_spec`：满足同一同余且在窗口内的数唯一等于
  `q_V`，这是递推闭合的唯一性前置；
- `wrapped_sub_add`、`mul_wrapped_sub_add`、`mod_sub_of_add_eq`：
  递推所需的环绕减法、乘法分配与“和同余反解被加数”三个模算术工具；
- `mod_minus_self`、`mod_sub_neg_add`：
  负剩余自身与负剩余相加的严格恒等式；
- `badResidue_step_two`：
  `q_V` 的精确 `t=2` 递推已闭合；
- `badResidue_step_one`：
  `q_V` 的精确 `t=1` 递推（提升一个模位）已闭合；
- `qV_ge_of_height_large`：
  当 `5^(i+1)+3 < 2^(H+1)` 时，由最小代表元尺寸界严格推出
  `q_V >= 2^W`；
- `qV_ge_iff_not_two_pow_dvd`：
  `q_V >= 2^W` 与 `¬ 2^(H+1) | 5r+3` 双向等价，把窗口下界
  精确还原为估值条件；
- `qVWindowStatement_iff_valuation`：
  `q_V` 窗口下界语句与估值语句在 `δ=0` 假设下严格同构；
- `failure_iff_q_mod_badResidue`：
  `failureCongruence A W i q H ↔ q ≡ q_V (mod 2^(W+H+1))`；
- `not_failure_of_badResidue_ge`：
  `q_V >= 2^W` 足以排除失败同余（充分方向）；
- `badResidue_ge_iff_not_failure` / `localLemma_iff_qV_ge`：
  在 `q<2^W` 且 `A+5^i*q=2^W*r` 的前提下，
  `q_V >= 2^W` 与失败同余不成立是**双向等价**；
- `badResidue_mod_two_pow_eq_q`：`q_V ≡ q (mod 2^W)`；
- `carryBalance_zero_iff_failure`：
  `B_i = 0` 与失败同余**双向等价**；
- `carryBalance_ne_zero_iff_not_failure`：
  `B_i != 0` 与局部引理侧**双向等价**；
- `qVWindowStatement`：最终开放语句的 Lean 声明，已补入
  `q ∈ [2^Wp,2^Wj)`、`H = 2i+13-2(W-Wp)` 与容量前提 `3≤H`，
  未用 `sorry` 断言。

剩余开放量是 `B_i`/`c_i` 的显式递推表述，以及 `qVWindowStatement`
本身：从
`A+5^i*q=2^W*r`、`r<5^i`、`u=1` 与 `δ=0` 递推推出
`q_V >= 2^W`。这对应审计中“坏残差窗口下界”的唯一缺口。

## 7. 2026-08-09 修正：qVWindowStatement 缺可达性前提

审计发现 `A+5^i*q=2^W*r`、`r<5^i`、`u=1` 与 q 区间本身不足以保证
`q_V>=2^W`。两个反例：
1. `(i,W,Wp,Wj,H,q,r,u,A)=(5,10,0,2,3,2,9,5,2966)` 满足 `A<5^5`，
   但 `q_V=2<2^10`，即 `5r+3=48` 被 `2^(H+1)=16` 整除；
2. 即使 `A=wordA w` 且 `wordValid w q`，仍需块切分约束：词
   `w=(2,1,2,1,1,2,1,1)`、`q=7`、`r=1433`、`A=200409` 没有
   `Wp=1,Wj=3` 的前缀切分；正确的切分是 `Wp=2,Wj=3`，此时
   `H=11` 且 `v2(5r+3)=10<=H`。

QWindow.lean 已在 `qVWindowStatement` 与 `qVWindowStatement_iff_valuation`
两侧加入 `ReachableWindow A W i q r Wp Wj`：存在 `{1,2}` 词 `w`、块起点
`j`，满足 `wordOK`、`wordValid`、`wordA=A`、`wordWeight=W`、前缀宽度
`Wp/Wj` 与 `wordOrbit w q = r`。已编译通过，无 `sorry`。

只加 `A < 5^i` 而不加 `ReachableWindow` 的形式仍是假语句，并已在
`QWindow.lean` 中用定理 `qVWindowStatementABoundOnly_counterexample`
形式化击穿：`(A,W,i,q,H,r,u,Wp,Wj)=(2966,10,5,2,3,9,5,0,2)` 满足全部
前提（含 `A<5^5`），但 `q_V=2<2^10`。因此目标必须保留 `ReachableWindow`，
不能退回到仅 `A<5^i` 的版本。

## 8. 2026-08-09 Lean 分解：大 H 部分已闭合

`QWindow.lean` 新增：
- `qVWindowLargeHeight`：在 `ReachableWindow` 前提下额外假设
  `5^(i+1)+3 < 2^(H+1)`；
- `qVWindowLargeHeight_holds`：该大 H 部分由
  `qV_ge_of_height_large` 严格闭合，已编译；
- `qVWindowRemaining`：剩余小 H 情形，仍开放；
- `qVWindowStatement_iff_large_and_remaining`：完整
  `qVWindowStatement` 与“大 H 部分 ∧ 剩余部分”严格等价，已编译。
- `remaining_height_bound`：剩余情形给出 `2^H <= 5^(i+1)`；
- `remaining_D_height_bound`：代入 `H = 2i+13-2D` 后的同一边界。
- `macro_endpoint_failure_iff`（`MacroWindow.lean`）：宏步末端失败等价于
  `2^(m+2) | 5^a*C-1`，其中 `m=H-2a`，把单比特判据压缩成单一
  2-adic 同余入口。
- `macro_endpoint_success_iff`（`MacroWindow.lean`）：成功侧等价于
  `2^(m+2) ∤ 5^a*C-1`，即剩余目标的直接非失败形式。

## 9. 2026-08-09 解析笔记修正与新增（global_budget_lemma_G.md）

本段记录纯解析侧的新增/修正，不声明闭合；尚未映射到 Lean。

1. **修正 `R_n` 递推**。旧式
   `R_n = 5^(a_{n-1})R_{n-1} + 2^(2a_{n-1}-1)` 仅对 `n=2` 成立；
   正确式为
   `R_n = 5^(a_{n-1})R_{n-1} + 2^(2(a_1+...+a_{n-1})-(n-1))`。
   它影响 `global_budget_lemma_G.md` 第 6 节 `q*` 显式式在
   `n>=3` 的准确性；修正后链头恒等式
   `5^(S_n)C_0-R_n=C_n·2^(m_0+n-m_n)` 逐项精确。
2. **新增提升量恒等式**。设 `q*_0=q+2^(W_j)L`，则
   `L≡-5^(-(S_n+n0+1+j))·2^(2j+13-2t_j+n-m_n)·C_n
   (mod 2^(2j+14-2t_j+n))`；局部引理在 `p_n` 成立当且仅当
   `v_2(q*_0-q)<W_j+(2j+14-2t_j+n)`。
3. **新增最小反例预算结构**。`m_k=H_k-2a_k` 恒为奇数；首次失败
   推出 `a_n>=2`；失败步窄区间为
   `m_{n-1}+2 <= 2a_n-1 < (p_n+1)λ-2a_{n-1}`。
4. **新增重置回代方程**。对上一块终端
   `r_{j-1}+1=5^(k0)s''`（`s''` 奇），
   `N=2^(t_j+2n0+1)s-2^(t_j)+4-δ5^j=5^(k0+1)s''`；
   这是沿块递归下降的精确入口，仍未闭合。
5. **修正旧错误**：`q*` 不恒为奇数（低 `W_j` 位等于 `q`）；
   旧“短链 `G_n<2^(E_n)` 排除”在失败定义下是空条件。
6. **新增 m_n 无关估值控制（充要）**。令
   `Num0=5^(S_n)C_0-R_n`，则
   `L≡-5^(-(S_n+n0+1+j))·2^(2n0+2a0)·Num0
   (mod 2^(M_extra))`；
   局部引理在 `p_n` 成立等价于
   `2^(m0+n) ∤ Num0`，即纯估值
   `v_2(Num0)<=m0+n-1`，不再出现 `m_n`。
   进一步把重置方程代入后，失败等价于前块奇部同余
   `s''≡5^(-(E+k0+1))·(2^(t_j+2n0+1)5^(S_n)
   +2^(t_j+2n0+2a0)R_n-5^E(2^(t_j)-4+δ5^j))
   (mod 2^(2j-t_j+13+n))`，
   其模指数与 `n0,m_n` 无关；配合 `0<s''<5^(j-1-k0)` 得到
   一个 m_n 无关尺寸必要条件。以上全部充要/必要，未声明闭合。
   另由 `C_n>=3`、`C_0<5^(n0+1+j)/2^(2n0+2a0)` 推出失败的
   必要尺寸条件 `3·2^(2j-2t_j+n+14)<5^(S_n+n0+1+j)`；
   与宏链乘积、`C_i` 5-adic 残差一起构成下一步的入口。
   进一步化到纯链参数预算：局部引理在 `p_n` 成立等价于
   `Σ_{i=1}^n(a_i-1) <= j-t_j+6-n0-a0`（`m_n` 已消去），
   并给出宏链乘积恒等式
   `Num_n = 5^(S_n)C_0·Π(1-1/(5^(a_i)C_i))`，
   每个因子在 `(1-4^(a_i)/5^(p_{i+1}+1), 1)` 内；
   这是后续沿宏链归纳的精确入口。另由 `C_n>=3` 与 `q` 区间
   得到失败的必要尺寸条件
   `3·2^(2j-2t_j+n+14) < 5^(S_n+n0+1+j)`，
   以及宏链乘积下界与 `C_n` 上界的精确比较式；
   尺寸层仍未封口，缺口在 `C_i` 的 5-adic 残差或 `s''` 三态。

以上恒等式已用精确整数算术随机核验（链头 40227 例、`L` 3144 例、
重置回代 38 例，以及新 m_n 无关形式 8187 例，全部一致）；
核验不是证明。剩余开放语句仍为
`v_2(q*_0-q)<W_j+(2j+14-2t_j+n)` 对所有可达链成立，
现已等价地写成不含 `m_n` 的 `v_2(5^(S_n)C_0-R_n)<=m0+n-1`。

## 10. 2026-08-09 复核：qVWindowStatement 前提已闭合

审计要求的修法已落在 `../lean/QWindow.lean`：

- `qVWindowStatement` 与 `qVWindowStatement_iff_valuation`
  两侧均带 `A<5^i`；
- 主目标同时带 `ReachableWindow A W i q r Wp Wj`，
  因为只加 `A<5^i` 的形式是假语句；反例
  `(A,W,i,q,H,r,u,Wp,Wj)=(2966,10,5,2,3,9,5,0,2)` 已在
  `qVWindowStatementABoundOnly_counterexample` 中形式化；
- `lean QWindow.lean`（`LEAN_PATH=.`）复核编译通过，无
  `sorry/admit`。

本轮新增 `lte_budget_recurrence.md`：把 K4/LTE 路线写成
预算形式。核心结果是：在 L1（`v2(a_i)<=m_i-1`）成立时，
情形 1、2（`s_i≠n_i`）自动成功，唯一危险点是等号情形
`s_i=n_i`（K4B）；并给出 `s'` 三态递推、势能
`Q_i=m_i+1-s_i` 的逐宏步变化，以及两条新的必要条件
（情形 3 成功 ⇒ `v2(a_i)<=m_i-2`；情形 1/2 失败 ⇒
`v2(a_i)>=m_i`）。L1、L2、K4B 仍未从 δ=0 递推证明，
本文不声明闭合。

预算笔记第 6 节进一步把进位位 `c_i` 换成完整 2-adic 商
`y_k=(q_{V,k}-q_k)/2^(W_k)` 的免进位线性递推：`t=1` 步
`X=2` 时的危险量是 `e=v2(o+5^(-(k+2)))-1`，`t=2` 步
`X=1` 时的宏步端点是 `X'=v2(o-5^(-(k+2)))-1`。这给出
“游程累计 `e` 不超过 `2(K-B)+1`”的精确预算形式，仍未闭合。

预算笔记第 7 节把 X=2 游程完全闭式化：游程长度
`n=v2(3*5^(k0+2)*o_0+5)`，出口进位
`e=v2(5^(n-1)*c-1)`（`c` 为该整数除以 `2^n` 的奇部）。
公式已用 5000 组随机 2-adic 单位精确核验；它把危险点压成
单个仿射函数 `3*5^(k0+2)x+5` 的两个 2-adic 赋值，
仍未闭合预算不等式。

预算笔记第 8 节把局部引理进一步归约为两个单剩余类避让语句
（充要）：对每个可达 `X=2` 状态要求
`C=(5r+3)/4 ≢ 5^(-1) (mod 2^H)`，对每个可达 `X=1`
状态要求 `C=(5r+3)/2 ≢ -5^(-1) (mod 2^H)`；`n0=0`
块首另需单独基例。这是第 6 节免进位递推的直接推论，
把整条局部引理压成 `C` 对固定模剩余类的避让，仍未闭合。

## 11. 2026-08-09 续：K 同余归约

新增 `bad_run_exclusion_reduction.md`：坏 `X=2` 游程已被写成单一
整数方程，并得到新的必要同余

```text
K ≡ (3·2^(H-1))^(-1)  (mod 5^(n+1)),
K = (5r_i+3)/2^(H+1) ∈ Z_{≥1}.
```

这完成“坏 `o_0` → 唯一 `K` 剩余类 → `q` 候选”的前两步；第三步
“对可达词前缀 `A` 证明 `q(m)∉[2^(Wp),2^(Wj))`”仍是开放子引理。
本文不新增 Lean 定理；只更新解析归约状态。

`bad_run_exclusion_reduction.md` 第 6 节进一步把第三步参数化为：
对每个 `q∈[2^(Wp),2^(Wj))`，块首分子
`A_j=A0+2^(W_i+H+1)m-5^j q` 的步长
`2^(W_i+H+1)>5^j`，故每个 `q` 至多对应一个 `A_j∈[0,5^j)`；
剩余开放点是证明这些 `A_j` 都不是 `{1,2}` 词前缀分子。

同一文件第 7--8 节新增两个解析工具：
- 第 7 节给出 `wordA` 的递归逐位判定（充要），把“`A_j` 不是
  `{1,2}` 词前缀分子”变成有限递归词结构检验；
- 推论 7.2 进一步证明该递归判定是唯一贪心剥离：每一步至多一个
  `t∈{1,2}` 满足同余，故词形若存在则唯一确定；
- 第 8 节给出候选计数界：在 `n≥1`、`tj≤2`、`j≤34` 时每个块尾词
  至多一个候选 `q`；`j≥35` 仍允许多候选，需词结构检验。
两者均未闭合第三步，仅压缩归约。

## 12. 2026-08-10 新增：坏游程归约为单步 X=2 排除

新增 `bad_run_x2_n1_reduction.md`：

- 充要式 `v_2(N0)≥Δ+H_i+1`、尾包络 `s0≤5^L-4^L`、一步剥皮均闭合；
- `N0<2^(H0+l+1)` 的尺寸区制闭合；
- 由 F 不变量证明坏 X=2 游程的必要条件：长度 `n=1`；`L0≥1` 时
  块尾前缀为 `1 2^(L0-1)` 且 `X_j=2L0`；
- 归约后坏出口等价于单步条件
  `v_2(5w-1)≥H_k`（`X_k=2`、`w=(5r_k+3)/4`）；
- 单步条件进一步等价于
  `2^(W_k+H_k+2) | 25A_k+11·2^(W_k)+5^(k+2)q`，
  且坏出口至多对应一个 `q`；
- 块首单步在 `t_j=2,k≤19` 或 `t_j=1,k≤25` 由尺寸排除闭合。

当前唯一开放量是该单步 X=2 排除；不再新增 Lean 定理。
