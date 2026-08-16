# 交接：hfail 纯 t=2 游程求和（2026-08-16）

## 措辞修正（2026-08-16 侧边会话）

旧文本把 `cycleQb8InputT2OrbitRankTarget` 称为“开放量 / 唯一缺口”，
这是错误措辞：它是 `OrbitCycle 7` 反证内部应直接推出的证明义务，
输入侧已有具体 7 轨道 rank 工具（`t2_step_rank_ge_three_of_word`、
`fullOrbitIter_rank_drop_two`、`cycleQb8Input_prefix_rank_le_period`
等）与游程求和基础设施。“尚未落成 Lean 证明”不等于“数学上开放”，
下文相关“缺口”标题与“仓库中还没有任何引理”一句按此修正。

## 状态

`lean/amiya.lean` 已加入并编译通过（0 error / 0 warning）的游程求和
基础设施。`lake build amiya`、`lake build trinity` 均成功，
`amiya.lean` / `trinity.lean` 无 `sorry`。

## 已闭合（均在 `lean/amiya.lean`）

- `maxT2RunsFrom` / `maxT2Runs`：极大 t=2 游程枚举，
  `T2Run.start/length = (a, L)`，游程内每步权重为 2。
- `maxT2RunsFrom_mem_two`：`ts.getI (a+i) = 2`。
- `maxT2RunsFrom_bounds`：`a + L ≤ len`。
- `riseCountTwo_append`、`riseCountTwo_takeWhile_two`、
  `dropWhile_eq_drop_length_takeWhile`、`riseCountTwo_leading_two`、
  `maxT2RunsFrom_length_sum`：`Σ run.length = H2`。
- `block_t2_runs_rank_sum`：单块 List.sum 中间式
  `Σ_{run∈maxT2Runs(suffixWord r)} (v2(y_a+1) − v2(y_{a+L}+1))
   = 2·riseCountTwo(suffixWord r)`。
- `t2_runs_global_sum`：全块求和
  `2·H2 = Σ_blocks Σ_{runs in block} (v2(y_a+1) − v2(y_{a+L}+1))`。
- `cycleWord_t2_runs_rank_sum`：整词级
  `2·H2 = Σ_{runs} (v2(y_a+1) − v2(y_{a+L}+1))`。
- `noLongT2Run_run_length_le`：
  `noLongT2Run c p ⇒ run.length ≤ run.start + 6`。
- `cycleWord_noLongT2Run_sum_bound`：
  `noLongT2Run c p ⇒ 2·H2 ≤ Σ_{runs} (2a + 12)`。
- `cycleRiseBlockH2Sum_le_tailRank_charge_sum`：
  `2·H2 ≤ Σ_r (tailRank_r + charge_r)`。
- `wordA_take_ge_of_global_min`：
  `wordA(w.take i) ≥ m·(2^(W_i) − 5^i)`（`i ≤ P`，来自
  `2^(W_i)·y_i = 5^i·m + A_i` 与 `hglobal_min`）。
- `cycleQb8Input_wordA_take_ge_global_min_of_hcycle` /
  `cycleQb8Input_wordA_take_ge_global_min_orbit_prefix`：
  同一不等式显式携带 `w = cycleWord c p`、`m = fiveXPlusOneOrbit 7 c`，
  并给出每个前缀状态 `wordOrbit(w.take j) m = fiveXPlusOneOrbit 7 (c+j)`。
- `wordA_eq_pmi_aTotal` / `wordWeight_eq_pmi_prefixWeight`：
  `wordA` / `wordWeight` 与 PMI `aTotal` / `prefixWeight` 的桥。
- `wordA_take_ge_global_min_aTotal`：上一条的 PMI 前缀形式。
- `aTotal_eq_four_sum_and_pow`：
  `A_P = 4·Σ_{i=1}^{P-1} A_i + Σ_{i=0}^{P-1} 2^(W_i)`。
- `wordA_sum_ge_global_min_aTotal`：
  `A_P ≥ 4·m·Σ_{i=1}^{P-1}(2^(W_i)−5^i) + Σ_{i=0}^{P-1}2^(W_i)`。
- `cycleQb8Input_pmi_sum_ge_global_min`：
  与 PMI 的 `A_P = m(2^S−5^P)` 合并后的同一条不等式。

## 剩余证明任务

把 noLongT2Run 上界

```text
2·H2 ≤ Σ_{runs} (2a + 12)
```

与 PMI 方程 / `cycleQb8Input_aTotal5_equation`
（`aTotal5 = 5m(2^S − 5^P)`，必须用 `m = fiveXPlusOneOrbit 7 c`）
合并成矛盾的那条确切不等式尚未给出。块消项侧目前只有上界

```text
2·H2 ≤ 2 + Σ residual + Σ charge
```

现在已有全局最小前缀求和不等式

```text
m(2^S − 5^P) ≥ 4·m·Σ_{i=1}^{P-1}(2^(W_i)−5^i) + Σ_{i=0}^{P-1}2^(W_i)
```

剩余是把 `Σ(2a+12)` 或 `Σ 2L` 从 noLongT2Run 上界改写成同一侧
的反向下界，并与上式 / PMI 相撞；这一步仍未闭合。注意 13 循环
`[1,1,5]` 与 17 循环 `[1,3,3]` 都满足 `hglobal_min` 与
`noLongT2Run`，所以真正的区分输入是 `hcycle` 给出的
`m = fiveXPlusOneOrbit 7 c` 及具体轨道前缀，不是 `hglobal_min` 本身。

## 待证步骤（2026-08-16 续）

在 `OrbitCycle 7` 反证内部拿到 `hcycle` 后，已把
`wordOrbit(w.take j) m = fiveXPlusOneOrbit 7 (c+j)`、
`w.getI k = twoValuation (5·fiveXPlusOneOrbit 7 (c+k)+1)`、
`wordOrbit(w.take j) m < 5^(c+j)` 三件真实轨道工具与
`cycleQb8Input_pmi_sum_ge_global_min_of_hcycle` 对齐。仍缺少的
不是新的结构不等式，而是一条 7 轨道 valuation/c 界；例如

```text
∃ K, c < K
或 ∃ j, 2j+9 ≤ twoValuation (fiveXPlusOneOrbit 7 (c+j)+1) ∧ w.getI (j-1) = 2
```

单靠 `hglobal_min + PMI + noLongT2Run` 无法推出这样的界：`c`
是 7 第一次进入该周期词的轨道下标，可以远大于 `p`；13/17 周期词
在代数层面并不被排除。因此下一步必须正面使用 7 轨道上的
valuation 增长/下降约束，而不是继续堆 `wordA` 求和。

## 精确 Lean 目标（下一站）

已把剩余证明义务写成带 `hcycle`、带 outgoing 的精确目标
`cycleQb8InputT2OrbitRankTarget`：

```text
∀ h : CycleQb8Input m S P w rise c3,
  w = cycleWord c p →
  m = fiveXPlusOneOrbit 7 c →
  ∃ j,
    1 ≤ j ∧ j < p ∧
    w.getI (j - 1) = 2 ∧
    (w.getI j = 1 ∨ w.getI j = 2) ∧
    2·j + 9 ≤ v2(fiveXPlusOneOrbit 7 (c+j) + 1)
```

并已闭合从它到 hfail 的桥：
`cycleWordInternalRankLowerBound_of_orbit_rank` 与
`hfailRankLowerBoundTarget_of_t2_orbit_rank`。因此当前待证步骤是证明
`cycleQb8InputT2OrbitRankTarget`，即把 7 轨道的 valuation 约束接进
`noLongT2Run` 反证；之后进入
`SelectedHfailBlockData.hrank` → 同块局部窗口上界 → `TrinityBlock`。

## 纪律

- 不新增 ⇔；不复活全局比较 (6)；不攻全局
  `decisiveWindowValuationBoundCorrected`；
- 不标 blocked；不找外部输入；只动 `amiya.lean` / `trinity.lean`。

## 归约（2026-08-16 续：目标归约为游程等号）

把 rank-drop 事实与 `maxT2Runs` 对齐后，`cycleQb8InputT2OrbitRankTarget`
在 `noLongT2Run` 分支下等价于：

```text
∃ run ∈ maxT2Runs (cycleWord c p),
  run.length = run.start + 6
```

推导：

1. 极大游程 `(a, L)` 的起点 rank 为 `2L+1`（出口 `t=1`）或
   `2L+2`（出口 C3）。
2. 目标在游程内取 `j = a+1`，要求 `v2(y_{c+j}+1) ≥ 2j+9`。
3. `noLongT2Run_run_length_le` 给出 `L ≤ a+6`，因此只有
   `L = a+6` 且 `j = a+1` 能满足目标。

该分支下的待证步骤是证明等号情形存在；这是证明义务，不是开放量。
`cycleQb8Input_pmi_sum_ge_global_min` 不能单独承担该证明：13 影子
`(m=13, w=[1,1,5], P=3, S=7)` 满足 `hglobal_min` 与 PMI 求和不等式，
但 `H2=0`、`noLongT2Run` 成立，因此必须由具体 7 轨道 rank 动态供给
区分性下界，这正符合 `agent.md` 的 hcycle 锚点纪律。

`cycleWord_noLongT2Run_sum_bound` 只给出 `2H2 ≤ Σ(2a+12)`，
而 `L = a+6` 的等号情形正是该上界逐项取等。旧文本中“仓库中还没有
任何引理证明逐项取等，也未证明若全部取不到等号会与真实轨道 rank
动态矛盾”一句作废：仓库已有 `t2_step_rank_ge_three_of_word`、
`fullOrbitIter_rank_drop_two`、`cycleQb8Input_prefix_rank_le_period`
等真实轨道 rank 工具，等号情形的推导应直接组合它们与游程求和，
而不是把该目标记为开放量。
