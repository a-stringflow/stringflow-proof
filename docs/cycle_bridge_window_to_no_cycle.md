# 循环桥：窗口定理 ⇒ ¬ OrbitCycle 7

日期：2026-08-13

状态：**解析推导，末端开放**。本文把“窗口定理成立 ⇒ 7 的加速
轨道无正循环”的下游接线写成一个四步循环桥。窗口定理本身不在
本任务中证明；本任务只把 `decisiveWindowValuationBoundCorrected`
作为显式输入前提。旧的无约束 `decisiveWindowValuationBound` 已被
反例否定，本桥不使用它，并禁止扫描证书、Simons S1 与任何 Q/L/S
额外范围假设。

## 1. 输入与目标

输入（由另一线闭合，本任务不证明）：

$$
\mathrm{decisiveWindowBound}:=
\forall\,(\text{全局可达 }\delta=0\text{ 块})\;
v_2\!\bigl(5^{k_0+1}s''+\delta_j5^j+2^{t_j}-4\bigr)
\le 2j-t_j+12.
$$

Lean 中该前提已写成
`StringFlow.BlockAutomaton.decisiveWindowValuationBoundCorrected`
（`lean/BlockAutomaton.lean`）：`t=2` 侧为
`t2WindowValue j k0 δ s ≤ 2j+10`，`t=1` 侧为
`t1WindowValue j k0 s ≤ 2j+11`，两者正对应上式，且每条不等式都
以 `S6Audit.ResetWindowReachability` 作为真实可达性前提，且
`j,k0,t` 与窗口参数一致。

目标：

$$
\mathrm{decisiveWindowBound}
\;\Rightarrow\; \neg\,\mathrm{OrbitCycle}(7)
\;\Rightarrow\; \mathrm{IsUnboundedOrbit}(7).
$$

Lean 目标接口命名为 `CycleBridge.windowBoundToNoCycle`：

```lean
def windowBoundToNoCycle : Prop :=
  BlockAutomaton.decisiveWindowValuationBoundCorrected → ¬ OrbitCycle 7
```

### 统一核心结论接口表

| 统一核心结论 | 状态 | 文档/Lean 位置 |
|---|---|---|
| 词段刚性 `y→x→r_j→z→w` 完整轨道连续段 | 数学层必要方向已证，全局排除未闭合；Lean 只有候选接口 | `docs/odd_exit_terminal_word.md` 36.30.12/13/14；`lean/UnifiedCoreBridge.lean` |
| 完整轨道状态界 `r_k<5^k`（`k≥2`） | 已证；块首版本与精确轨道版本都在 Lean | `docs/odd_exit_terminal_word.md` 36.30.20.2；`lean/S6Audit.lean` `reset_head_lt_five_pow`；`lean/CycleBridge.lean` `fiveXPlusOneOrbit_lt_five_pow` |
| 入步权重刚性 `e≡1 (mod 4)` | 数学层必要方向已证，Lean 未形式化 | `docs/odd_exit_terminal_word.md` 36.30.13.1 |
| `k=0` 剥离与模 25 窗口 | 数学层必要/充分剥离机制已证，Lean 未形式化 | `docs/odd_exit_terminal_word.md` 36.30.14.1/14.3 |
| 首块刚性 `S_stop=8`、`y_b=7` | 数学层已证，Lean 未接线 | `docs/odd_exit_terminal_word.md` 36.30.23.2/23.3 |
| `d=1,d=2` 排除、`d=3` 唯一族 | 数学层已证；`d=3` 基例 Lean 零 `native_decide` | `docs/odd_exit_terminal_word.md` 36.30.23.5；`lean/FinitePrefix.lean` |
| 条件结论与已证结论分离 | 已编码；`unified_core_final_no_hge` 仍为唯一 `sorry` | `lean/UnifiedCoreAudit.lean` |

该表只登记统一核心作为显式输入接口的状态；`unified_core_final_no_hge`
未闭合前，发散桥不把任何统一核心结论当作已证输入。

## 2. 四步桥

### 2.1 循环 ⇒ 全局可达块首

若 `OrbitCycle 7`，则存在 `m<n` 使 `fiveXPlusOneOrbit 7 m =
fiveXPlusOneOrbit 7 n`；确定性轨道此后逐相位常值，循环内每个状态
都是 7 的完整加速轨道状态。Lean 侧已经可证（本任务补上）：

- `fullOrbitIter n = fiveXPlusOneOrbit 7 n`；
- 因此循环每个状态都属于 `FullOrbitFrom7`；
- 每个状态也属于 `GeneralOrbitFrom7`（`FinalStatement` 已有）。
- `orbit_cycle_imp_exists_c3_start`：正循环必含 C3 起点（存在
  一步权重 `t≥3`）。证明只用“t≤2 时加速步严格增大”，无扫描、
  无 Simons、无范围假设。
- `orbit_repeat_period` 与
  `orbit_cycle_imp_periodic_c3_segment`：循环重复给出周期 `p`，
  且存在落在循环段内的 C3 起点 `c`，满足
  `orbit(c+p)=orbit c`。这是把“循环旋转到 C3 起点”写进 Lean 的
  第一步。

把循环旋转到最小元素/C3 起点后，循环中的重置点 `rj` 应当满足
`S6Audit.ResetWindowReachability` 的字段（同一 `j,k0,t`）：上一
终端 `r` 由 `GeneralOrbitFrom7` 覆盖，重置块首 `rj` 由
`FullOrbitFrom7` 覆盖，`ResetHeadEq` 由重置方程给出。这一步的
形式化缺口是“从周期词提取 C3 起点和重置块”的引理：

```lean
orbit_cycle_imp_full_globally_reachable :
  OrbitCycle 7 → ∃ j k0 t δ s, S6Audit.ResetWindowReachability j k0 t δ s
```

### 2.2 循环 ⇒ QB-8 尖峰

现有 `lean/Td0Final.lean` 已有：

- `Qb8Cycle` / `Qb8Orbit` / `Qb8OrbitInput` / `FirstC3Orbit` 接口；
- `qb8_orbit_of_cycleInput`：从真实循环参数构造
  `Qb8OrbitCycleInput`；
- `td0_of_qb8OrbitCycleInput`：用 TD0 内部证书关闭 QB-8。

**范围审计。** `FirstC3Orbit` / `Qb8Orbit` / `Qb8OrbitInput` 的字段
包含 `m≤10^6`、`8≤Q`、`feasible64`、`S≥26` 等范围假设。循环桥
的纪律第 5 条禁止这些额外假设，因此不能直接构造这些现有结构。
本任务新增无范围的 `CycleQb8Input` 作为替代接口，只保留循环本身
能推出的字段。

本任务不能直接使用 `td0_of_qb8OrbitCycleInput`，因为 TD0 当前仍
依赖 `stageOneScanOK`。需要的新引理是从循环的存在性直接给出
QB-8 尖峰参数，而不经过 TD0 闭合：

```lean
qb8_of_orbit_cycle :
  OrbitCycle 7 →
  ∃ b Q L U m M0 w ns ts,
    Qb8Orbit b Q L U m M0 w ns ts
```

这里的 QB-8 分解只依赖周期词本身：循环弦 → 上升段 + C3 链，
尖峰 `t_1=3/5`、其余 `t_i≥3`、首 C3 前缀等全部从循环闭合方程
推导，不需要 Q/L/S 范围假设。

**已闭合的周期词层。** `CycleBridge` 已把“循环 ⇒ 闭合周期词”
写成 Lean：

- `cycleWord c p`：从轨道状态 `c` 出发、长度为 `p` 的精确步长词；
- `cycleWord_orbit_eq`：沿该词从 `orbit c` 走到 `orbit(c+p)`；
- `cycleWord_wordValid`：该词对起点 `orbit c` 合法；
- `cycleWord_length`、`cycleWord_head_eq`：词长 `p`，非空词首步
  等于起点精确步长；
- `cycleWord_take_eq`、`cycleWord_getI_eq`、
  `cycleWord_prefix_orbit_eq`、`cycleWord_step_exact`：周期词前缀
  就是缩短后的周期词，第 `k` 项精确等于
  `v2(5·orbit(c+k)+1)`，且沿前缀走到的状态就是对应的轨道状态。
  这是把“词合法”升级为“词步精确”的接口。
- `twoValuation_five_mul_add_one_ge_one`、
  `cycleWord_mem_ge_one`：奇数轨道态给出步长 `t≥1`，周期词每一项
  都是合法步长；
- `cycleWord_non_c3_rise`：非 C3 项必为 `t=1` 或 `t=2`；
- `cycleWordC3Count`、`cycleWordC3Count_pos`：周期词中 C3 步计数
  `Q≥1`，首步 C3 保证至少一个 C3 步；
- `wordWeight_filter_lt_ge_split`、`cycleWordRiseWeight`、
  `cycleWordC3Weight`、`cycleWord_weight_decomp`：总权重按
  `t<3` 与 `t≥3` 拆成上升段权重与 C3 步权重；
- `cycleWordRiseSteps`、`cycleWordC3Steps` 及其成员引理：
  把周期词显式拆成上升段列表（每项 `t=1/2`）与 C3 链列表
  （每项 `t≥3`）；
- `cycleWord_length_split`、`cycleWordC3Steps_length`：长度拆分
  `p = rise + c3`，C3 步数等于 `cycleWordC3Count`。
- `cycleWordC3Count_le_length`：C3 步数 `Q ≤ P`。
- `c3Step_lt_of_pos`、`orbit_step_lt_of_c3`、
  `cycleWord_mem_at`、`cycleWordRiseSteps_nonempty_of_closed`：
  C3 步严格下降，周期词非空时第 `i` 项确实在词中，且闭合周期词
  至少有一个上升步（非 C3）。
- `cycleWord_rising_equation`：对任意周期词，
  `2^S * orbit(c+p) = 5^p * orbit c + A`；
- `cycleWord_cycle_equation`：闭合周期词给出整循环方程
  `2^S * m = 5^p * m + A`；
- `orbit_cycle_imp_cycle_word_closed`：正循环给出 `c,p`，首步
  `t(c)≥3`，且 `wordOrbit (cycleWord c p) (orbit c) = orbit c`。
- `orbit_cycle_imp_cycle_word_valid_closed`：上述闭合词同时是合法
  词，构成第 2 步 QB-8 翻译的输入。
- `orbit_cycle_imp_cycle_word_qb8_input`：把合法、闭合、首步 C3、
  显式 head 分解打包成 QB-8 翻译的完整输入接口。
- `orbit_cycle_imp_diophantine_cycle_equation`：把合法、闭合、
  首步 C3 的周期词与整循环方程打包，直接作为 QB-8/PMI 下游的
  Diophantine 输入。
- `CycleQb8Input`、`orbit_cycle_imp_cycle_qb8_input`：无范围的
  QB-8 词层接口；从任意正循环直接构造，不含 `m≤10^6`、`Q≥8`、
  `feasible64` 等 TD0 时代假设。`CycleQb8Input` 现带 `hexact` 字段：
  每个词步都是精确 2-adic 估值，不只是一般的 `wordValid` 可除性；
  并携带 `hm_pos`、`hm_odd`、`hm_not_five` 与 `hrise_pos`，即起点
  为正奇数、`5∤m`，且上升段非空；另有 `hrise_filter` 与
  `hc3_filter`，把 `rise`/`c3` 钉为原词按 `t<3` 与 `t≥3` 的精确
  过滤结果。
- `cycleQb8Input_P_ge_two`、`cycleQb8Input_length_ge_two`：
  上升段与 C3 段都非空，因此闭合 QB-8 词长至少 `2`。
- `cycleQb8Input_rise_disjoint_c3`：上升段与 C3 段互斥。
- `exists_c3_index_of_filter_nonempty`：C3 过滤段非空 ⇒ 词内存在
  真实 C3 索引 `j`，供 QB-8 尖峰定位使用。
- `exists_rise_index_of_filter`、`cycleQb8Input_exists_rise_index`：
  上升过滤段非空且成员为 `1/2` ⇒ 词内存在真实上升索引。
- `cycleQb8Input_exists_c3_index`、
  `cycleQb8Input_exists_c3_and_rise_index`：闭合 QB-8 输入同时
  存在真实 C3 索引与真实上升索引。
- `rise_step_next_mod_five`：上升步输出模 5 被步权唯一钉定，
  `t=1→3`、`t=2→4`，是块首模 5 条件的基础。
- `wordOrbit_take_succ`、
  `cycleQb8Input_exists_block_head_mod_five`：闭合 QB-8 输入内
  存在一个上升索引，其下一状态模 5 为 `3` 或 `4`，即真实块首候选。
- `FailureWindow`、`failureWindowExistence`：第 3 步的开放存在性
  陈述，参数约束已写齐：`t=1/2`、`δ` 分支、`s` 为奇数、
  `5∤s`、`k0+1≤j`、`s<5^(j-k0-1)`，以及失败估值
  `2j+12`（`t=1`）/`2j+11`（`t=2`）。2026-08-13 审计后，
  `FailureWindow` 额外携带 `hinput : CycleQb8Input m S P w rise c3`
  、`hj_lt : j < P` 与
  `hreset : ResetHeadEq s j k0 t δ (wordOrbit (w.take j) m)`，
  使失败窗口必须来自给定词的块首，而不是任意全局算术元组。
- `failure_window_contradicts_t1/t2`、
  `failure_window_contradicts_window_corrected`：第 4 步的代数收尾
  （已证）；后者把整个 `FailureWindow` 实例化到
  `decisiveWindowValuationBoundCorrected` 并直接得矛盾。旧的
  `failure_window_contradicts_window_invalid` 只保留审计，不使用。
- `t2Run`、`t2Step_valuation_drop`、`pure_t2_balance`：第 3 步的
  纯 t=2 块局部余额；连续 `n` 个精确 `t=2` 步消耗 `2n` 估值
  （`2n ≤ v2(r+1)`）。
- `pure_t2_block_capacity`：纯 `t=2` 块在窗口内
  `v2(r+1) ≤ 2j+8` 时长度满足 `L ≤ j+4`。
- `riseStep`、`riseRun`、`riseCountTwo`、`riseCharge`、
  `riseChargeSum`、`rise_block_balance`：混合 `t=1/2` 上升块的
  局部余额已零 `sorry` 闭合。`t=2` 每步消耗 `2` 单位
  `v2(r+1)`，`t=1` 步按正增量充值；对任意精确上升词有
  `2·H2 ≤ v2(r0+1) + Σ(充值)`。这是块层 PMI 投影第 2 节
  `2H2 ≤ u+F` 的逐步正增量版本。
- `cycleWord_wordA_pos`、`cycleWord_weight_gt_five_pow`：非空周期词
  的 `A>0`，闭合词给出 `5^P < 2^S`，即周期总权重在
  `P·log2 5` 之上。
- `wordWeight_ge_mul_length_of_ge`、
  `cycleWordC3Weight_ge_three_mul_count`：C3 链权重下界
  `3Q ≤ wordWeight c3`，供 PMI 求和时估计 C3 侧权重。
- `Gc.pmiSum_eq_pmiTotal`：非空 C3 段下 spike 分解的 `pmiTotal`
  与 `rise ++ c3` 的列表 PMI 和逐项相等；第 3 步求和时可从循环
  方程直接接到该列表形式。
- `cycleWord_wordA_eq_pmi_aTotal`、
  `cycleWord_pmi_cycle_equation`、`cycleWord_pmi_algebraic`、
  `cycleWord_pmi_b_count`、`cycleWord_pmi_b_no_bad_prefix`：
  闭合周期词已直接接上 PMI 与 PMI-B；词分子等于列表 PMI 分子，
  整循环方程给出 `aTotal5 = 5 m (2^S - 5^P)`，坏前缀计数有同一
  预算上界，且 `badCount ≤ (5m(2^S-5^P))/5^P - 1`；小预算时
  所有真前缀满足 `2^(W_j) < 5^j`。

这是第 2 步 QB-8 翻译的第一个正式接口：周期词已经闭合，并且起点
是 C3 起点；剩余是把该闭合词分解成上升段 + C3 链并匹配 QB-8
尖峰条件。

**审计：不要使用“t=2 不相邻”。** `s_x3_3_exact_rejection.md` 的
H3 主张 `t=2` 步之后下一步必为 `t=1` 或 C3，但该结论对精确加速
轨道不成立：`31 → 39 → 49` 连续两步都是 `t=2`
（`156/4=39`、`196/4=49`）。循环桥第 2 步的上升段分解不能把
“`t=2` 不相邻”或 `2U≤L+1` 当作从精确轨道自动推出的事实；若需要
该结构，必须单独证明并在证明中显式排除 `31→39→49` 这类残差。

### 2.3 QB-8 ⇒ 至少一个 δ=0 块命中失败窗口

块层 PMI 投影（`docs/pmi_block_projection.md` 第 3--6 节）给出：
若某 `δ=0` 块的块首估值失败

$$
u_j\ge2(j-t_j)+13,
$$

则

$$
v_2(N)\ge2j-t_j+13,
\qquad
N=5^{k_0+1}s''+\delta_j5^j+2^{t_j}-4.
$$

需要证明的解析引理是：QB-8 循环整体闭合 ⇒ 至少存在一个全局可达
的 `δ=0` 块满足上述失败估值。这由 PMI 全局恒等式与块层预算完成：
若所有块都避开失败窗口，则循环整体余量无法闭合。Lean 目标：

```lean
cycle_closed_imp_failure_window :
  Qb8Orbit b Q L U m M0 w ns ts →
  ∃ j k0 t δ s,
    2j - t + 13 ≤ twoValuation
      (5 ^ (k0 + 1) * s + δ * 5 ^ j + 2 ^ t - 4)
```

这一步禁止引用 `stageOneScanOK`、`tripleScan`、`wordBad` 或
Simons S1；所有不等式从循环方程和 PMI 推出。

**记号审计（2026-08-12）。** 这里有两个不同的 `δ`，必须先分开：

1. 循环词残差 `δ_i`：把循环旋转到某状态 `m` 后，词递推
   `2^{t_i}r_{i+1}=5r_i+1+\delta_i5^{i+1}` 的残差。
   `odd_exit_terminal_word.md` 引理 22.6 已证循环内
   `δ_i=0` 对所有 `i` 成立。
2. 块首重置参数 `δ_j`：`ResetHeadEq` 中的
   `2^{t_j}r_j=5r_{j-1}+1+\delta_j5^j`，对 `t_j=2` 有
   `δ_j∈{1,3}`，对 `t_j=1` 有 `δ_j=1`。失败窗口 `N` 中的
   `δ_j` 是这里的重置参数，不是循环词残差。

因此“循环内所有残差 `δ_i=0`”并不排除块首重置参数
`δ_j∈{1,3}`；`odd_exit_terminal_word.md` 推论 22.7 只适用于它
自己定义的 k=0 失败块尾部方程，不能直接用来否定本步。
`pmi_block_projection.md` 的“δ=0 块”是指重置后内部无残差的块，块首本身仍
由非零 `δ_j` 生成。第 3 步的剩余证明必须沿用这套记号，不能把
引理 22.6 的 `δ_i` 与失败窗口的 `δ_j` 混用。

### 2.3.1 PMI 归约模板（开放）

设周期词 `w` 有 `P` 步、总权重 `S`，被 C3 步切成 `K` 个 δ=0 块。
第 `r` 个块的块首估值 `u_r`、块长 `L_r`、`t=2` 步数 `H2_r`、
`t=1` 充值 `F_r`。块层局部余额（纯 `t=2` 部分已在 Lean 闭合，
`pure_t2_balance`）为

$$
2H2_r\le u_r+F_r,
$$

纯 `t=2` 块时 `F_r=0`，即 `2H2_r\le u_r`。

若所有块都满足窗口

$$
u_r\le2(j_r-t_r)+12,
$$

则逐块相加得到

$$
2H2\le\sum_r\bigl(2(j_r-t_r)+12\bigr)+\sum_rF_r.
$$

另一方面，闭合周期词给出整循环方程
`2^S m = 5^P m + A`，故 `S>P\log_2 5`；`S` 又等于上升段权重加
C3 权重（`cycleWord_weight_decomp`）。把这两组不等式合并后，
应推出某个块的失败

$$
u_r\ge2(j_r-t_r)+13.
$$

**剩余开放不等式（未闭合）。** 合并块层求和与周期闭合的精确
代数尚未完成；它正是 `failureWindowExistence` 的解析核心。本模板
不声称闭合，也不把求和当作已证引理引用。

### 2.4 与窗口合取得矛盾

把 `decisiveWindowValuationBoundCorrected` 实例化到同一个失败块：

- `t=2`：`v2(N) ≤ 2j+10 = 2j-t_j+12`；
- `t=1`：`v2(N) ≤ 2j+11 = 2j-t_j+12`。

与失败块的 `v2(N) ≥ 2j-t_j+13` 矛盾，故 `¬ OrbitCycle 7`；再由
`unbounded_of_no_cycle` 得 `IsUnboundedOrbit 7`。

**第 4 步代数已闭合。** `CycleBridge.failure_window_contradicts_t2`
与 `failure_window_contradicts_t1` 已在 Lean 中证明，
`failure_window_contradicts_window_corrected` 进一步把它们打包成：
任意 `FailureWindow j k0 t δ s` 与
`decisiveWindowValuationBoundCorrected` 直接矛盾。

- `t=2`：`v ≥ 2j+11` 与 `v ≤ 2j+10` 矛盾；
- `t=1`：`v ≥ 2j+12` 与 `v ≤ 2j+11` 矛盾。

剩余不是第 4 步的代数，而是第 3 步给出同一块的失败下界。

## 3. 当前 Lean 接口

`lean/CycleBridge.lean`（本任务新增）提供：

- `CycleBridge.windowBoundToNoCycle`：目标陈述；
- `fullOrbitStep_eq_fiveXPlusOneStep`、
  `fullOrbitIter_eq_fiveXPlusOneOrbit`：
  完整轨道与顶层轨道同一；
- `fiveXPlusOneOrbit_full_reachable`、
  `orbit_cycle_states_full_reachable`、
  `orbit_cycle_states_general_reachable`：循环态可达性；
- `fiveXPlusOneOrbit_odd_7`、`fiveXPlusOneOrbit_pos_7`、
  `fiveXPlusOneStep_gt_of_weight_le_two`、
  `orbit_cycle_imp_exists_c3_start`：C3 起点存在性的完整证明；
- `fiveXPlusOneStep_eq_oddPart`、`fiveXPlusOneStep_mul_eq`、
  `fiveXPlusOneStep_not_dvd_five`、`fiveXPlusOneOrbit_not_dvd_five`：
  精确加速步的奇部恒等式、`2^t·x'=5x+1`，以及 7 轨道状态
  永不被 `5` 整除。
- `fiveXPlusOneStep_le_div_two`、`fiveXPlusOneOrbit_lt_five_pow`：
  从奇数状态起精确步至少除以 `2`，并由此零 `sorry` 证明
  `r_n<5^n`（`n≥2`）。
- `orbit_repeat_period`、
  `orbit_cycle_imp_periodic_c3_segment`：周期重复与循环段内 C3
  起点的形式化；
- `cycleWord`、`cycleWord_orbit_eq`、
  `cycleWord_wordValid`、`orbit_cycle_imp_cycle_word_closed`、
  `orbit_cycle_imp_cycle_word_valid_closed`、
  `orbit_cycle_imp_cycle_word_qb8_input`、
  `cycleWord_rising_equation`、`cycleWord_cycle_equation`、
  `orbit_cycle_imp_diophantine_cycle_equation`：闭合周期词的构造、
  合法性、闭合性、Diophantine 方程与 QB-8 输入打包；
- `no_cycle_of_window_bound`、
  `five_x_plus_one_diverges_at_7_of_window_bound`：
  桥闭合后的最终接线。
- `windowBoundToNoCycle_of_failureWindowExistence`、
  `no_cycle_of_window_bound_of_failureWindowExistence`、
  `five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window`：
  第 3 步存在性一旦闭合，就直接把循环桥接到
  `decisiveWindowValuationBoundCorrected → ¬ OrbitCycle 7 → IsUnboundedOrbit 7`。
  这些定理本身不证明 `failureWindowExistence`，只做装配。

该文件无 `sorry`、无自定义 axiom；未闭合的桥引理只以 docs 形式
记录，不写成 `sorry` 定理。

**编译与 axiom 审计。** `lake build CycleBridge` 已通过；
`#print axioms` 对 `no_cycle_of_window_bound` 与
`five_x_plus_one_diverges_at_7_of_window_bound` 分别只返回
`[propext, Quot.sound]` 与 `[propext, Classical.choice,
Quot.sound]`，无 `sorryAx`、无 `native_decide` 信任。当前仓库剩余
`sorry` 是 `UnifiedCoreAudit.unified_core_final_no_hge` 与
`FinalTheorem.five_x_plus_one_diverges_at_7`；本桥不引用它们。

## 4. 待补引理清单

| 引理 | 内容 | 状态 |
|---|---|---|
| `orbit_cycle_imp_full_globally_reachable` | 循环 ⇒ 重置点满足 `ResetWindowReachability j k0 t δ s` | 开放 |
| `qb8_of_orbit_cycle` | 循环 ⇒ QB-8 尖峰参数 | 开放 |
| `cycle_closed_imp_failure_window` | QB-8 闭合 ⇒ 存在失败窗口块 | 开放 |
| `failure_window_contradicts_window_corrected` | 失败窗口与 `decisiveWindowValuationBoundCorrected` 矛盾 | 代数已证，第 3 步存在性开放 |
| `cycle_of_window_bound_contradiction` | 合成：`decisiveWindowValuationBoundCorrected → ¬ OrbitCycle 7` | 开放 |

第 3 步的记号障碍已审计：循环词残差 `δ_i=0`（引理 22.6）与块首
重置参数 `δ_j∈{1,3}` 是不同对象；`cycle_closed_imp_failure_window`
必须以块首重置参数写作，不能直接引用推论 22.7 否定循环内失败块。

已闭合的子引理：

- `orbit_cycle_imp_exists_c3_start`：正循环必有 C3 起点；
- `orbit_cycle_imp_periodic_c3_segment`：正循环含周期 C3 段；
- `orbit_cycle_imp_cycle_word_closed`：正循环给出首步 C3 的闭合
  周期词；
- `orbit_cycle_imp_cycle_word_valid_closed`：闭合周期词对起点合法；
- `orbit_cycle_imp_cycle_word_qb8_input`：QB-8 翻译的完整周期词
  输入接口；
- `orbit_cycle_imp_diophantine_cycle_equation`：正循环给出闭合词的
  整循环方程 `2^S m = 5^p m + A`；
- 循环态全局可达（`GeneralOrbitFrom7` / `FullOrbitFrom7`）；
- `windowBoundToNoCycle` 闭合后的无界接线；
- 条件装配：`failureWindowExistence` 成立时，
  `windowBoundToNoCycle_of_failureWindowExistence` 已零 `sorry`
  证明 `windowBoundToNoCycle`，并由
  `five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window`
  直接给出最终无界语句。
- 块层局部余额：`rise_block_balance` 已零 `sorry` 编译，把
  `2H2 ≤ u+F` 的“逐步正增量”形式闭合；它不依赖窗口定理，也不
  等于大深度窗口排除。

## 5. 纪律

- 不引用 `stageOneScanOK`、`tripleScan`、`wordBad` 的 native_decide
  证书；
- 不引用 Simons S1；
- 不新增自定义 axiom；`#print axioms` 只允许 `propext`、
  `Classical.choice`、`Quot.sound`；
- 除“循环存在”和“窗口定理”外，不引入 Q/L/S 范围假设；所有
  不等式从循环本身推导。

## 6. 当前精确剩余（2026-08-12）

- 第 4 步已在接口层闭合：
  `CycleBridge.failure_window_contradicts_window_corrected` 把任意
  `FailureWindow` 实例化到 `decisiveWindowValuationBoundCorrected`
  并直接得矛盾。
- 条件装配已闭合：`CycleBridge.windowBoundToNoCycle_of_failureWindowExistence`
  把 `failureWindowExistence` 接到
  `windowBoundToNoCycle`，`no_cycle_of_window_bound_of_failureWindowExistence`
  与 `five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window`
  分别给出 `¬ OrbitCycle 7` 与 `IsUnboundedOrbit 7`。因此从 Lean
  接口角度看，数学输入是 corrected 窗口定理与 `failureWindowExistence`
  两者；`failureWindowExistence` 只是其中尚未闭合的存在性陈述。
- 接口审计（2026-08-13）：旧 `FailureWindow` 完全不引用
  `CycleQb8Input`，因此只要存在一个纯算术失败窗口，就会让
  `failureWindowExistence` 变成平凡真命题。实际存在这样的元组，
  例如 `j=36,k0=0,t=2,δ=3,s=2^83-3·5^35`：
  `s` 为奇数、`5∤s`、`s<5^35`，且
  `v2(5s+3·5^36)=v2(5·2^83)=83 > 2j+10`。这意味着旧的
  `decisiveWindowValuationBound` 若不附带真实块首/可达性约束，
  会被该元组直接否定；`FailureWindow`
  现已加上 `hinput`、`j<P`
  与 `hreach`，堵住这条空洞通道。Lean 侧已零 `sorry` 形式化
  `arithmetic_failure_window_witness` 与
  `decisiveWindowValuationBound_contradiction`：后者直接证明旧的
  无约束窗口定义被否定。`FailureWindow` 随后还补上 `hreset`，
  把 `s`、`j`、`t`、`δ` 显式钉到 `wordOrbit (w.take j) m`；
  `hreach` 进一步要求 `ResetWindowReachability`；窗口桥
  只消费 `decisiveWindowValuationBoundCorrected`。
- 第 3 步的 Lean 目标已精确化为 `FailureWindowExistence`：
  每个 `CycleQb8Input` 都必须产生一个带参数约束的 `FailureWindow`。
- PMI-B 层已闭合：`cycleWord_pmi_b_count`、
  `cycleWord_badCount_le`、`cycleWord_pmi_b_no_bad_prefix` 均已编译。
- `Td0Real.margin_balance_necessary` 已把并行线的 11.5.2 形式化：
  非负余量前缀必须满足
  `(3-log2 5)C3 ≤ (log2 5-1)C1 + (log2 5-2)C2`。
- `Td0Real.log2_of_pow_lt_pow` 给出 PMI-B 到余量的实数桥：
  `2^W < 5^j ⇒ W < j·log2 5`。
- `Td0Real.count_sum_length`、`Td0Real.counts_weight_le` 把
  `t=1/t=2/t≥3` 计数接到词长与词权；`CycleBridge.cycleWord_margin_balance`
  已把它们与 `cycleWord_pmi_b_no_bad_prefix` 合成：小预算闭合周期词
  的每个真前缀都满足余额必要条件；`cycleWord_margin_balance_strict`
  给出严格版本 `(3-α)C3 < (α-1)C1 + (α-2)C2`。
- `cycleWord_small_budget_weight_lt` 给出小预算下的总权重窄窗：
  `S < P·log2 5 + 1`，即总权重贴着平均线上方。
- 已形式化：`cycleWord_last_step_c3_of_small_budget`。小预算下
  最后一个加速步必须是 C3：`S<Pα+1`、`W_{P-1}<(P-1)α` 与
  `S=W_{P-1}+t_last` 合起来给 `t_last>α>2`。
- `small_budget_contradicts_c3_start` 已证明小预算本身与 C3 首步
  矛盾；`cycleWord_badCount_ge_one_of_c3_start`、
  `cycleWord_pmi_budget_ge_two_pow` 进一步给出：C3 首步使 `j=1`
  自动成为坏前缀，PMI-B 预算至少 `2·5^P`。因此第 3 步不再依赖
  小预算，下一步应证明“坏前缀 ⇒ 失败窗口”，或由 `badCount≥1`
  直接推出失败。
- 审计修正：上述矛盾说明小预算论证必须从全局最小值起点展开
  （首步 `t=1/2`），不能从任意 C3 起点；否则 `j=1` 必为坏前缀。
  循环桥第 1 步应取“全局最小值”作为周期词起点。
- 已形式化：`orbit_cycle_imp_min_rise_start` 给出每个正循环都有
  以全局最小值为起点、首步 `t≤2` 的闭合周期词。小预算/PMI-B 论证
  现在有正确的起点。
- 已形式化：`orbit_reset_head_eq_of_rise_start` 与
  `orbit_cycle_imp_min_rise_witness`。循环的全局最小值起点给出
  `j=1,k=0,δ=1` 的重置方程，且起点状态是奇数、`5∤s0`。注意这
  只是重置方程分量；`ResetWindowReachability` 还要求
  `s<5^(j-1-k0)` 与上一偶数终端可达，这两项在 `j=1` 下不会自动
  成立，仍需要块分解把深度抬到 `j≥2`。
- 块层余额 `2H2 ≤ u+F` 的 Lean 形式化下一步应“按极大 `t=1` 游程
  整体归纳”，而不是逐状态递推；逐状态版本在中间 `t=1` 状态上
  不保持所需的估值不变量。该归纳是第 3 步剩余 Lean 工作的入口。
- 已形式化的逐步版本：`rise_block_balance` 对每个精确
  `t∈{1,2}` 步按 `t=2` 消耗 `2`、`t=1` 按 `v2(r'+1)-v2(r+1)`
  的正部充值，得到 `2·H2 ≤ v2(r0+1)+F`。它已经不需要极大游程
  归纳；真正的剩余是把这一逐步充值接到块层窗口预算
  `u_r+F_r ≤ 2(j_r-t_r)+12` 与周期 PMI 求和。
