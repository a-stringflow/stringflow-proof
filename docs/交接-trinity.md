# 交接：trinity（hterm / 统一核心 / hfail 联合推进）

日期：2026-08-16 晚

## 当前状态

三条线的接口收缩已完成，联合骨架 `lean/trinity.lean` 已建并单文件
编译通过（0 error / 0 warning / 0 sorry）：

- `HtermComponent`、`UnifiedCoreComponent`、`HfailComponent` 三个组件
  def 已定义；
- `TrinityBlock` 块级三合一（同一真实块的 hterm reset、窗口上界、
  失败下界）已定义；
- `trinity_block_contradicts`、`trinity_no_cycle_of_block_exists`、
  `trinity_unbounded_of_block_exists` 已闭合；
- `trinityBlockExistsOfComponents`（三组件 → 块存在）是开放的组装
  接缝，不标 blocked。

## Trinity 核心估值层（2026-08-16 晚补）

三块同源估值统一到 trinity 层，不再按三个组件分别开放。`trinity.lean`
新增（自包含定义，0 warning / 0 error / 0 sorry）：

- `HtermValuation`：selected 版模 `5^(L-1)` 同余（倒数第二步 = 1）；
- `UnifiedCoreValuation`：corrected 窗口上界；
- `HfailValuation`：绑定 `hcycle` 的内部 rank 下界
  （`fiveXPlusOneOrbit 7 c = m`、`w = cycleWord c p` 下存在高 rank
  前缀）；
- `TrinityCoreValuation`：三者合取，是同一 7 轨道估值事实的三个
  投影；
- `trinityBlockExistsOfCoreValuation`：核心估值 → 块存在（开放组装，
  不标 blocked）。

证明策略：闭合 `TrinityCoreValuation` 一次，三个组件各自取用，
而不是分别攻 hterm/hfail/统一核心的估值。

## 定位纠错（下一会话必须先接受）

- 剩余断言是**主定理级内部步骤**，不是独立引理，不标 blocked；
- 没有“外部 2-adic 不变式输入”可等：`CycleQb8Input` 的
  `hstart`/`hcycle` 就是全部输入，缺口是推导没用完，不是输入缺失；
- “13 可达模型满足全部假设却使结论为假”是循环陈述：13 可达模型
  存在 ⟺ 7 进入 13 循环 ⟺ 主定理为假。它不是形式反例；
- 13 影子上断言为假是预期：断言确实绑定了 7 轨道
  （`m = fiveXPlusOneOrbit 7 c`），不是通用结构命题失效。

## 已闭合工具箱（amiya.lean，编译通过）

- `realPrefixDepth` / `realPrefixDepth_of_cycleQb8Input`：真实前缀
  深度来源；
- `cycleQb8Input_state_bound_of_hcycle`：hcycle 下的 5-adic 尺寸上界
  `wordOrbit (w.take j) m < 5^(c+j)`；
- `rank_lower_t1/t2_of_numerator`：层条件 → rank 下界的单向代数桥；
- `cycleWordLayerCondition`：精确层条件
  `2^(W+2j+11) ∣ 5^j·m + A + 2^W`（t=1）、
  `2^(W+2j+9) ∣ 5^j·m + A + 2^W`（t=2）；
- `cycleWordInternalRankLowerBound_of_layer`：层条件 → 内部 rank 下界
  （单向，已闭合）；
- `cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt`：内部 rank
  下界 → hfail 接口；
- `rank_lower_contradicts_corrected_upper_t1/t2`：与 corrected 窗口
  上界的收尾矛盾代数（已闭合）；
- `cycleWordInternalRankLowerBound` 已明确降级为 trinity 内部待填
  断言，不独立开放。

## 剩余主定理级断言

1. **层条件整除性（当前精确卡点）**
   存在 `j`、`t = (cycleWord c p).getI (j-1) ∈ {1,2}`，使
   `t=1`：`2^(W+2j+11) ∣ 5^j·m + A + 2^W`
   `t=2`：`2^(W+2j+9) ∣ 5^j·m + A + 2^W`
   其中 `m = fiveXPlusOneOrbit 7 c`，`W/A` 为 `cycleWord c p`
   在深度 `j` 的前缀权重/分子。
   首层 `j=1` 化简为：
   `t=1`：`v2(5m+3) ≥ 14`；`t=2`：`v2(m+1) ≥ 13`。
2. **hpre 完整同余（hterm 侧）**
   `wordA u' ≡ 2^(wordWeight u' + c - 1)·q (mod 5^(L-1))`；
   模 25 层等价于 `t_prev ≡ t0 (mod 4)`（`t_prev = w.getI (b-2)`），
   更高模继续向更早状态传播（5-adic 望远镜）。
3. **统一核心窗口上界**
   `BlockAutomaton.decisiveWindowValuationBoundCorrected` 仍未闭合。

三者都不是独立引理，都只在 `CycleQb8Input` 假设下作为主定理证明的
内部步骤使用。

## 下一步方向（二选一，先做前者）

a. 在 trinity 内部继续：用 `m = fiveXPlusOneOrbit 7 c` 的具体 5-adic
   模类 + PMI 代数方程 `aTotal5 = 5m(2^S−5^P)` + 真实前缀递推
   `2^(t_i)·y_{i+1} = 5y_i + 1`，逐层推层条件；每层卡住时给出精确
   中间式，不换角度。
b. 评估 hfail 路线是否必须经过 `cycleWordInternalRankLowerBound`：
   如果必须，它与主定理是一体的；如果不必须，调整 hfail 实现
   也是主定理证明的一部分，不属于 blocked。

## 禁止

- 禁止标 blocked；禁止要求外部提供“新的 7 轨道事实”；
- 禁止用“13 可达模型”作为形式反例或不可证理由；
- 禁止把 `cycleWordInternalRankLowerBound` 当作独立开放目标；
- 不新增 ⇔ 等价归约；不换角度；不复活全局比较 (6)；
- 卡住时给出精确中间式，不抛回用户。

## 验证与边界

- 开发只跑 `lake env lean <单文件>.lean`；
- 全量 `lake build` 只在相关文件 sorry 清零后运行；
- 最终标准：0 sorry、0 error、0 axiom；
- hterm 线程只动 `RiseDecompositionAssembly.lean`，hfail 只动
  `amiya.lean`，trinity 骨架在 `trinity.lean`。

## Goal Prompt（给下一个会话）

```text
目标：在 trinity 骨架下闭合剩余主定理级断言，不标 blocked，
不要求外部输入。

先读：docs/交接-trinity.md、docs/交接-hfail.md、docs/交接-hterm.md、
docs/防出错表.md、lean/trinity.lean、lean/amiya.lean、
lean/CycleBridge.lean（CycleQb8Input、hcycle、PMI 段）、
lean/RealOrbitCharge.lean。

步骤：
1. 从 hcycle 展开 m = fiveXPlusOneOrbit 7 c、w = cycleWord c p；
   每一步必须显式使用 hstart 或 hcycle 的具体内容。
2. 攻层条件整除性：用真实前缀递推、wordA 方程、PMI 代数方程
   逐层推 2^(W+2j+11)（t=1）/2^(W+2j+9)（t=2）整除性；
   首层 j=1 的精确中间式是 v2(5m+3) ≥ 14 或 v2(m+1) ≥ 13，
   从这里开始逐层归纳。
3. 层条件成立后，经 cycleWordInternalRankLowerBound_of_layer、
   cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt 接 hfail；
   与 corrected 窗口上界在 rank_lower_contradicts_corrected_upper 处
   矛盾。
4. 把 trinityBlockExistsOfComponents 从 def 变为定理：
   依次填入 HtermComponent（hpre 望远镜）、UnifiedCoreComponent
   （窗口上界）、HfailComponent（层条件）。

纪律：不标 blocked；不找外部输入；13 影子为假是作用域标志；
不新增 ⇔；不换角度；卡住给出精确中间式；单文件验证。
```
