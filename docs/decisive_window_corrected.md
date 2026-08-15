# 窗口上界修正审计：decisiveWindowValuationBoundCorrected

日期：2026-08-13

## 1. 旧定义与反例

旧定义（`lean/BlockAutomaton.lean` 中的
`decisiveWindowValuationBound`）只要求纯算术前提：

```text
a = j - k0 - 1,
δ = 1 ∨ δ = 3,
s % 2 = 1,
¬ 5 ∣ s,
```

然后断言

```text
t2: v2(5^(k0+1)*s + δ*5^j) ≤ 2j + 10,
t1: v2(5^(k0+1)*s + 5^j - 2) ≤ 2j + 11.
```

该定义已被 `CycleBridge.decisiveWindowValuationBound_contradiction`
否定。完整反例元组为：

| 参数 | 值 |
|---|---|
| `j` | `36` |
| `k0` | `0` |
| `t` | `2` |
| `δ` | `3` |
| `s` | `2^83 - 3*5^35` |

它满足旧定义的纯算术前提：

- `a = 35 = j - k0 - 1`；
- `δ = 3`；
- `s % 2 = 1`；
- `¬ 5 ∣ s`；
- `s < 5^35`；
- `k0 + 1 ≤ j`。

但违反的正是 t=2 窗口不等式：

```text
5s + 3*5^36 = 5*2^83,
v2(5s + 3*5^36) = 83,
窗口上界 = 2j + 10 = 82,
83 ≤ 82 不成立。
```

## 2. 旧定义缺少的约束

旧反例说明，窗口上界不能只对“满足尺寸和同余的算术参数”成立。
corrected 版本必须携带：

| 约束 | 作用 |
|---|---|
| `FullOrbitFrom7 rj` | 块首 `rj` 必须落在 7 的真实完整加速轨道上 |
| `GeneralOrbitFrom7 r` | 上一终端 `r`（可为偶数）必须在一般可达轨道上 |
| `ResetHeadEq s j k0 t δ rj` | 块首由精确重置方程给出 |
| `s0 * 5^k = r + 1` 与尺寸界 | 块参数与上一终端之间的字算术关系 |
| 词段约束 | 具体词前缀 `wordOrbit (w.take j) m` 与 `rj` 一致，且 `j < P` |

`BlockAutomaton.decisiveWindowValuationBound` 已标记为 INVALID，
下游 `CycleBridge` 和 `DwdbDiv` 不再消费它。

## 3. Corrected 定义

`lean/BlockAutomaton.lean` 中新增：

```lean
def t2WindowBoundCorrected (j k0 a t delta s : Nat) : Prop :=
  a = j - k0 - 1 ->
  t = 2 ->
  delta = 1 \/ delta = 3 ->
  S6Audit.ResetWindowReachability j k0 t delta s ->
  t2WindowValue j k0 delta s <= 2 * j + 10

def t1WindowBoundCorrected (j k0 a t s : Nat) : Prop :=
  a = j - k0 - 1 ->
  t = 1 ->
  S6Audit.ResetWindowReachability j k0 t 1 s ->
  t1WindowValue j k0 s <= 2 * j + 11

def decisiveWindowValuationBoundCorrected : Prop :=
  ((j k0 a t delta s : Nat) -> t2WindowBoundCorrected j k0 a t delta s) /\
  ((j k0 a t s : Nat) -> t1WindowBoundCorrected j k0 a t s)
```

其中 `S6Audit.ResetWindowReachability j k0 t δ s` 已经携带：
上一终端 `GeneralOrbitFrom7`、`ResetHeadEq`、块首
`FullOrbitFrom7`、`s*5^k0 = r+1`、奇性/非 5 整除/尺寸界，并且
`j,k0,t` 与外层窗口参数完全一致，避免只固定 `N` 却换用不同
`j,k` 的语义漏洞。具体词段约束保留在 `CycleBridge.FailureWindow`
的 `hreset` 与 `hj_lt` 中，不放进窗口上界本身。

## 4. 旧反例与新前提

旧反例元组是否满足新前提，当前状态为**未证明**，不能声称它被新
前提自动排除。原因是新前提的关键字段是
`GeneralOrbitFrom7 r` 与 `FullOrbitFrom7 rj`，而这两个可达性谓词
尚未对 `s=2^83-3*5^35` 的候选块首给出 Lean 排除证明。

需要的新引理：

```text
¬ ResetWindowReachability 36 0 2 3 (2^83 - 3*5^35)
```

Lean 中已把该目标编码为
`CycleBridge.arithmeticFailureWitnessNotCorrected`（`def`，不是
定理）。该引理当前没有 Lean 证明，也不应补成 `sorry`。

## 5. 统一核心到 corrected 窗口上界

`DwdbDiv` 中已编码条件接口：

```lean
def decisiveWindowValuationBoundCorrected_of_unified_core : Prop :=
  unifiedCoreClosed ->
    BlockAutomaton.decisiveWindowValuationBoundCorrected
```

这不是证明。`unified_core_final_no_hge → corrected 窗口上界` 的
完整推导目前缺失，缺下列桥：

| 缺失桥 | 说明 |
|---|---|
| `unified_core_forms_equivalent` | `unified_core_t2` 与局部估值形式之间的桥，仍 missing |
| `rj0_ge_iff_terminal_bound` | CRT/B2/B3 到终态估值界的双向桥，仍 missing |
| 块分解到 `ResetWindowReachability` | 从 `All36_20PremisesNoHge + FullOrbitFrom7 r` 构造完整重置块首与词段，仍未编码 |
| `ResetHeadEq` 实例化 | 从统一核心的词段刚性导出具体 `j,k0,t,δ` 的重置方程 |

## 6. 下游依赖修复表

| 原依赖 | 修复后 | 状态 |
|---|---|---|
| `failure_window_contradicts_window` | 改名 `failure_window_contradicts_window_invalid`，仅保留审计 | 已编译，禁止使用 |
| 新增 `failure_window_contradicts_window_corrected` | 消费 corrected 窗口上界与 `FailureWindow.hreach` | 已编译 |
| `windowBoundToNoCycle` | 重定义为 `decisiveWindowValuationBoundCorrected → ¬ OrbitCycle 7` | 已编译 |
| `windowBoundToNoCycle_of_failureWindowExistence` | 用 corrected 定理装配 | 已编译 |
| `no_cycle_of_window_bound` | 参数改为 corrected | 已编译 |
| `no_cycle_of_window_bound_of_failureWindowExistence` | 参数改为 corrected | 已编译 |
| `five_x_plus_one_diverges_at_7_of_window_bound` | 参数改为 corrected | 已编译 |
| `DwdbDiv.*` 三个窗口接口 | 参数全部改为 corrected | 已编译 |

旧窗口上界在反例修复前不得再作为窗口桥输入。

## 7. failureWindowExistence 输入依赖

`CycleBridge.FailureWindow` 现在包含：

| 字段 | 输入 |
|---|---|
| `hinput` | `CycleQb8Input m S P w rise c3` |
| `hj_lt` | `j < P` |
| `ht` | `t = 1 ∨ t = 2` |
| `hδ` | `t=1 → δ=1`，`t=2 → δ∈{1,3}` |
| `hreset` | `ResetHeadEq s j k0 t δ (wordOrbit (w.take j) m)` |
| `hreach` | `ResetWindowReachability j k0 t δ s` |
| `hs_odd`, `hs_not_five`, `hk`, `hs_lt` | 奇性、非 5 整除、深度、尺寸 |
| `hfail_t1`, `hfail_t2` | 失败估值下界 `2j+12` / `2j+11` |

`failureWindowExistence` 仍是开放 `def`，不是定理。`DwdbDiv` 中已
编码条件接口：

```lean
def failureWindowExistenceOfUnifiedCore : Prop :=
  unifiedCoreClosed ->
    CycleBridge.failureWindowExistence
```

该接口未证明；不得声称 `failureWindowExistence` 可绕过统一核心。

## 8. 当前剩余 sorry

- 统一核心最终估值不等式的 pure 块版本：已由
  `PureCore.unified_core_final_no_hge_pure` 闭合，无 `sorry`；完整
  real-orbit 版本 `unified_core_final_no_hge` 仍未闭合，剩余是真实块词到
  `All36_20PremisesNoHge` 的实例化，以及 decisive-window / failure-window
  桥；
- `FinalTheorem.five_x_plus_one_diverges_at_7`：最终装配占位 `sorry`。

未闭合前，不宣称发散桥或 `7` 发散闭合。

## 9. 失败窗口结构层状态（2026-08-15）

失败窗口路线的结构组装已闭合：`RiseDecompositionAssembly` 提供
`cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary`、
`cycleRiseBlockSuffixWord_eq_cyclic_take`、
`cycleRiseBlockSuffixHall`、`cycleRiseBlockSuffixLastStep`、
`cycleRiseBlockSuffixStopC3`/`cycleRiseBlockSuffixStopOr`，
`RealOrbitLocalLemma.ResetHeadEq_of_fullOrbit_predecessor_eq` 给出
`hterm` 的代数逆向，`cyclicDepthFailureWindow_of_cycleRiseBlock` 组装
完全循环失败窗口，`cycleRiseBlockWindowFalse` 用出边 C3 rank-two
恒等式直接否定已组装的失败窗口。

剩余开放内容不变：`hterm`（真实终端到 `ResetHeadEq` 的构造）、
`hfail_t1/t2`（失败下界）必须由真实轨道可达性与 PMI 供给；
`rjRankT1LargeBound`/`rjRankT2LargeBound` 的大深度界仍需精确结构，
不能用小深度尺寸估计替代。
