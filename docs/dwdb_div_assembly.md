# DwdbDiv 装配状态与 CycleBridge 审计

日期：2026-08-13

## 1. CycleBridge 已证/条件/开放表

| 类别 | 引理/结构 | 状态 | 依赖 |
|---|---|---|---|
| 已证 | `cycleWord`、`cycleWord_step_exact`、`CycleQb8Input.hexact` | 已证 | 周期词层 |
| 已证 | `fiveXPlusOneOrbit_lt_five_pow` | 已证 | 精确轨道状态界 |
| 已证 | `fiveXPlusOneOrbit_not_dvd_five` | 已证 | 精确轨道 |
| 已证 | `orbit_cycle_imp_min_rise_witness` | 已证 | `j=1,k=0,δ=1` 重置方程 |
| 已证 | `rise_block_balance` | 已证 | 块层逐步余额 |
| 已证 | `failure_window_contradicts_window_corrected` | 已证 | 第 4 步代数 + corrected 窗口上界 |
| 已证 | `RiseDecompositionAssembly.cycleRiseBlockDecompositionExists_of_input` | 已证 | `CycleQb8Input` → 非空循环 rise 分解（结构存在已闭合） |
| 已证（条件装配） | `RiseDecompositionAssembly.cycleRiseBlockTailFailureWindowExistence_of_pmi` | 已证 | `cycleRiseBlockPMIGlobalComparisonHolds` → C3-tail 失败窗口存在性 |
| 已证 | `windowBoundToNoCycle_of_failureWindowExistence` | 已证 | 条件装配 |
| 已证 | `arithmetic_failure_window_witness` | 已证（审计） | 旧无约束窗口反例 |
| 已证 | `decisiveWindowValuationBound_contradiction` | 已证（审计） | 旧无约束窗口定义被否定 |
| 条件 | `decisiveWindowValuationBoundCorrected` | 定义 | 需 corrected 窗口定理输入 |
| 条件 | `windowBoundToNoCycle` | 定义 | 需 corrected 窗口定理输入 |
| 开放 | `decisiveWindowValuationBoundCorrected_of_unified_core` | 条件接口 | 统一核心 → corrected 窗口上界，未证明 |
| 开放 | `failureWindowExistenceOfUnifiedCore` | 条件接口 | 统一核心 → `failureWindowExistence`，未证明 |
| 条件 | `DwdbDiv.dwdbDivFinalAssembly` | 已证 | 无循环结论 |
| 开放 | `failureWindowExistence` | 开放 | 词内 `ResetHeadEq` + `ResetWindowReachability` 块首 |
| 开放 | `cycleRiseBlockTailFailureWindowExistence` | 开放 | 依赖 `cycleRiseBlockPMIGlobalComparisonHolds` |
| 开放 | `orbit_cycle_imp_full_globally_reachable` | 开放 | 块分解到 `ResetWindowReachability`、`GeneralOrbitFrom7` 上一终端 |
| 开放 | `qb8_of_orbit_cycle` | 开放 | 周期词 → 尖峰/上升段 |
| 开放 | `cycle_closed_imp_failure_window` | 开放 | PMI 块层投影 |
| 条件已证 | `cycle_of_window_bound_contradiction` | 已证：`hwin → hfw → ¬ OrbitCycle 7` | `DwdbDiv.cycle_of_window_bound_contradiction` |
| 开放 | `unified_core_final_no_hge` | `sorry` | 唯一统一核心剩余 |
| 开放 | `FinalTheorem.five_x_plus_one_diverges_at_7` | `sorry` | 最终装配目标 |

## 2. 开放引理对统一核心的依赖

- `failureWindowExistence`：不依赖 `unified_core_final_no_hge`；依赖
  `CycleQb8Input` 内 `ResetHeadEq` 与 `ResetWindowReachability`
  块首的构造。
- `orbit_cycle_imp_full_globally_reachable`：主要依赖块分解到
  `ResetWindowReachability`（固定 `j,k0,t`）与
  `GeneralOrbitFrom7` 上一终端；若使用统一核心的
  `FullOrbitFrom7` 词段事实，必须写成
  `unified_core_final_no_hge → 该引理` 的条件形式。
  `DwdbDiv.unifiedCoreClosed` 与
  `DwdbDiv.orbitCycleImpFullGloballyReachableConditional` 已把该
  条件形式编码为显式接口定义，但未写成证明。
- `qb8_of_orbit_cycle`：不依赖统一核心，依赖周期词层的尖峰/上升段
  分解。
- `cycle_closed_imp_failure_window`：不依赖统一核心，依赖 PMI
  恒等式与块层余额。
- `cycle_of_window_bound_contradiction`：不依赖统一核心，依赖
  `failureWindowExistence` 与
  `failure_window_contradicts_window_corrected`。

## 2.5 开放引理推进结果

- `qb8_of_orbit_cycle`：周期词层已接到 `CycleQb8Input`，并带精确
  过滤、上升/C3 互斥与 `P≥2`；QB-8 尖峰参数仍需把真实 C3 链与
  上升段投影成无范围的 QB-8 尖峰结构，该投影未闭合。
- `orbit_cycle_imp_full_globally_reachable`：条件接口
  `unifiedCoreClosed → ...` 已编码；证明需要块分解到
  `ResetWindowReachability` 与 `GeneralOrbitFrom7` 上一终端，
  仍开放。
- `cycle_closed_imp_failure_window`：已等价为带 `hinput`、`j<P`、
  `hreset`、`hreach` 的 `failureWindowExistence`；证明仍开放。
- `cycle_of_window_bound_contradiction`：已条件闭合为
  `DwdbDiv.cycle_of_window_bound_contradiction`。

## 3. DwdbDiv 装配接口

`lean/DwdbDiv.lean` 已建立：

```lean
namespace StringFlow.DwdbDiv

theorem dwdbDivFinalAssembly
    (_hbridge : CycleBridge.windowBoundToNoCycle) :
    ¬ OrbitCycle 7 → IsUnboundedOrbit 7

theorem five_x_plus_one_diverges_at_7_of_window_bound
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hbridge : CycleBridge.windowBoundToNoCycle) :
    IsUnboundedOrbit 7

theorem cycle_of_window_bound_contradiction
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : CycleBridge.failureWindowExistence) :
    ¬ OrbitCycle 7

theorem five_x_plus_one_diverges_at_7_of_failure_window
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : CycleBridge.failureWindowExistence) :
    IsUnboundedOrbit 7

end StringFlow.DwdbDiv
```

该文件零 `sorry`，axiom 审计只有
`[propext, Classical.choice, Quot.sound]`。

## 4. 统一核心闭合后的实例化清单

1. 证明 `decisiveWindowValuationBoundCorrected`（携带
   `ResetWindowReachability` 的真实可达性输入，固定同一
   `j,k0,t`）；旧
   `decisiveWindowValuationBound` 已被
   `decisiveWindowValuationBound_contradiction` 否定并作废。
   当前剩余精确化为 `RealOrbitLocalLemma.rjRankT1LargeBound` /
   `rjRankT2LargeBound`；小深度部分（`j≤34` / `j≤27`）已闭合，
   闭掉两个大深度剩余后可直接调用
   `RealOrbitLocalLemma.decisiveWindowValuationBoundCorrected_of_rjRankBounds`。
2. 闭合 `failureWindowExistence`，即对每个
   `CycleQb8Input` 构造满足 `hinput`、`j<P`、`hreset`、`hreach`
   的失败块首。
3. 调用 `CycleBridge.windowBoundToNoCycle_of_failureWindowExistence`
   得到 `windowBoundToNoCycle`。
4. 调用 `DwdbDiv.five_x_plus_one_diverges_at_7_of_window_bound`
   得到 `IsUnboundedOrbit 7`。
5. 若 corrected 窗口上界或 `failureWindowExistence` 的证明依赖
   统一核心，只能使用
   `decisiveWindowValuationBoundCorrected_of_unified_core` /
   `failureWindowExistenceOfUnifiedCore` 条件接口，且两者均未证明。

## 5. 当前未闭合清单

- `CycleBridge.failureWindowExistence`
- `RealOrbitCharge.cycleRiseBlockPMIGlobalComparisonHolds`
- `RealOrbitCharge.cycleRiseBlockTailFailureWindowExistence`
- `CycleBridge.orbit_cycle_imp_full_globally_reachable`
- `CycleBridge.qb8_of_orbit_cycle`
- `CycleBridge.cycle_closed_imp_failure_window`
- `BlockAutomaton.decisiveWindowValuationBoundCorrected`（证明开放）
- `RealOrbitLocalLemma.rjRankT1LargeBound` / `rjRankT2LargeBound`
- `DwdbDiv.decisiveWindowValuationBoundCorrected_of_unified_core`
- `DwdbDiv.failureWindowExistenceOfUnifiedCore`
- `UnifiedCoreAudit.unified_core_final_no_hge`
- `FinalTheorem.five_x_plus_one_diverges_at_7`

仓库中实际剩余的 `sorry` 语句只有
`FinalTheorem.five_x_plus_one_diverges_at_7`；
`UnifiedCoreAudit.unified_core_final_no_hge` 不是已声明的定理，
它只是状态表中的开放条目；`DwdbDiv` 不引用任何 `sorry`。

## 6. 失败窗口路线当前已闭合的结构层（2026-08-15）

- `cycleRiseBlockSuffixEndpoint_eq_nextHead`：rise 后缀端点是下一块
  块首状态，回绕块按周期归一化；`cycleRiseBlockNextHeadState` 定义
  修正为 `% P`。
- `cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary`：
  块 C3 链末端是真实循环 C3-to-rise 边界。
- `cycleRiseBlockSuffixWord_eq_cyclic_take` / `cycleRiseBlockSuffixHall`
  / `cycleRiseBlockSuffixLastStep` / `cycleRiseBlockSuffixStopC3` /
  `cycleRiseBlockSuffixStopOr`：rise 后缀与循环旋转段逐项一致、每步
  1/2、末步一致、后接 C3 停止条件。
- `premises_of_cycleRiseBlock_of_reset_window`：循环 rise 块的
  `All36_20PremisesNoHge` 实例化，`hhead` 由真实
  `ResetHeadEq`/`ResetWindowReachability` 供给。
- `ResetHeadEq_of_fullOrbit_predecessor_eq`：真实前驱方程 + 精确入步
  权逆向构造 `ResetHeadEq`，是 `hterm` 的代数核心。
- `cyclicDepthFailureWindow_of_cycleRiseBlock`：由 rise 块组装完全
  循环失败窗口，只差真实重置终端（`hrt`/`hterm`/`hk`/`hslt`）与
  失败下界（`hfail_t1`/`hfail_t2`）。
- `cycleRiseBlockWindowFalse`：组装出的失败窗口立即被出边 C3 rank-two
  恒等式否定，不需要 decisive window 上界与大深度估计。

这些结构层全部编译通过、零 `sorry`。剩余开放项仍是
`hterm`/`hfail` 的真实构造、`rjRankT1LargeBound`/`rjRankT2LargeBound`、
完整 `unified_core_final_no_hge` 实例化与最终组装。
