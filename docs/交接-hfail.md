# 交接：hfail

日期：2026-08-16

## 当前状态

hfail 的接口收缩（四阶段）已落到 Lean，相关文件单文件编译通过，
未新增 `sorry/axiom`：

- 阶段 1（hterm 侧，见 `docs/交接-hterm.md`）：纯边界命题
  `cyclic_real_predecessor_identity`，`cycleQb8InputRealPredecessorIdentity`
  只是其平凡实例。
- 阶段 2（hfail 侧）：`badPrefixAt` 定义坏前缀长度；
  `hfailRankLowerBoundTarget` 的 `j` 必须是坏前缀长度；
  `bad_prefix_terminal_alignment` 是 rank 下界到 `ResetHeadEq`
  的显式中间命题。
- 阶段 3：`cycleQb8InputHkBound`、`cycleQb8InputHsLtBound` 独立；
  `cycleQb8Input_cyclic_head_odd_reachable` 已证明，奇偶性与
  `FullOrbitFrom7` 继承不再作为新开放输入。
- 阶段 4：`cycleQb8Input_weak_comparison` 已独立闭合
  `5^P < 2^S`（来自正循环的 PMI 代数方程，与已判死的全局比较 (6)
  无关）；坏前缀存在性显式写成 `cycleQb8Input_bad_prefix_exists`，
  小预算前提不会被当作 `CycleQb8Input` 的免费推论。

## 目标

精确块首 rank 下界（hfail 主链）：

```text
t=1：2j+11 ≤ v2(rj+1)
t=2：2j+9  ≤ v2(rj+1)
```

其中 `j` 是坏前缀长度，`rj = wordOrbit (w.take j) m`。

## 关键定义与开放命题

均在 `lean/amiya.lean`：

- `badPrefixAt P w j`：
  `1 ≤ j ∧ j < P ∧ 5^j ≤ 2^(wordWeight (w.take j))`；
- `hfailRankLowerBoundAt m w j t`：分支 rank 阈值；
- `hfailRankLowerBoundTarget`：每个真实 `CycleQb8Input` 存在坏前缀
  端点及其 rank 下界（hfail 主目标）；
- `bad_prefix_terminal_alignment`：坏前缀 rank 下界 →
  存在真实 `rt` 与 `ResetHeadEq`（关键中间桥）；
- `hfailBudgetLowerBoundAt / hfailBudgetLowerBound`：预算形式
  `2*(tailDepth+1)+11 ≤ 2+2N-F`；
- `cycleQb8Input_bad_prefix_exists`：已撤下，不可作为独立引理。
  13 循环（13, 33, 83），词 (1, 1, 5)，P=3、S=7、m=13，满足
  `CycleQb8Input` 除 `hstart`/`hcycle` 外的全部结构字段且无坏前缀；
  三个旧工具（`cycleWord_pmi_b_count`、
  `cycleQb8Input_weak_comparison`、`cycleQb8Input_last_step_c3`）
  对影子完全相容。要区分 13 与 7 只能靠 `hstart`/`hcycle`，
  而它们等价于假设 `OrbitCycle 7`，独立证明必然循环。
  该命题仅在 `OrbitCycle 7` 假设下可作为主定理内部事实。

注：`hfailRankLowerBoundTarget` 签名已不再带 `5^P < 2^S` 前提
（弱比较已闭合），注释仍写旧前提，待清理。

## 已闭内容

- `cycleQb8Input_weak_comparison`：`5^P < 2^S`（CycleBridge）；
- `cycleRiseBlockSuffixEndpointRank_two_all`：rise 后缀端点 rank=2，
  含 wrap；
- `cycleRiseBlockTailRank_lower_of_endpoint_two`：
  `2+2N-F ≤ v2(r0+1)`；
- `tailRankThreshold_of_hfailBudget`：预算 → tail rank 阈值；
- `hfail_t1/t2_of_rank` 与反向桥：窗口值 ↔ rank 阈值；
- `hfail_t1/t2_of_hfailRankLowerBoundAt`：仅限已构造
  `LocalHidentBlock` 内部的局部转换，不连接裸坏前缀 rank；
- `cycleQb8Input_cyclic_head_odd_reachable`：局部头奇偶与
  `FullOrbitFrom7` 继承。

## 剩余主链

```text
真实轨道前缀（hstart 的 fullOrbitIter 深度）
→ hfailBudgetLowerBound（或直接 hfailRankLowerBoundTarget）
→ tailRankThreshold_of_hfailBudget → tail rank 阈值
→ 真实前缀 rank 下界（2j+11 / 2j+9）
→ bad_prefix_terminal_alignment（真实 rt + ResetHeadEq）
→ 失败窗口下界；与 corrected 窗口上界矛盾
```

路线依据（2026-08-14 主链）：
坏前缀 ⇒ 前缀权重 `W_j ≥ j·log₂5` ⇒ 上升块内 t=2 足够多 ⇒
`rise_block_balance` 逼出 rank 下界。

## 禁止

- 禁止复活全局比较 (6)，禁止把它作为 hfail 来源；
- 禁止把 `j` 定义成任意词位置；`j` 必须是坏前缀长度；
- 禁止再尝试用 `cycleWord_pmi_b_count`、
  `cycleQb8Input_weak_comparison`、`cycleQb8Input_last_step_c3`
  证坏前缀存在：13 影子已否证该路线的数学可行性；
- 禁止把 13 循环当伪反例或排除对象：它是 5x+1 的已知 3-循环，
  是真实轨道可达性的检验器；
- 禁止在词层面停留：没有 `ResetHeadEq` 的高 rank 不接入失败窗口；
- 禁止把 `cycleWord_pmi_b_no_bad_prefix` 的小预算前提当作
  `CycleQb8Input` 的免费推论；
- 禁止新增 ⇔ 等价归约代替正面构造；禁止换角度；
- 禁止 Python/数值扫描找伪反例；
- 开放命题不标 blocked，不要求外部输入；
- 卡住时给出精确中间式，例如
  `2+2N-F ≥ 2*(tailDepth+1)+11`。

## 验证与边界

- 开发阶段只跑单文件 `lake env lean <文件>.lean`；
- hfail 线程只动 `lean/amiya.lean`（接口文件中的既有修复保持
  编译通过即可）；
- 全量 `lake build` 只在相关文件 sorry 清零后运行；
- 最终标准：0 sorry、0 error、0 axiom。

## 装配侧（独立，不阻塞 hfail 主链）

`cycleQb8InputHkBound`、`cycleQb8InputHsLtBound`（kaltsit.lean）、
`cycleQb8InputExistsLocalHidentBlock` → global hident →
`failureWindowExistence`。这些是独立开放输入，与 hfail 主链并行。

## Goal Prompt（给下一个 hfail 会话）

```text
目标：在 hfail 接口收缩完成后，正面闭合 hfail 主链：
真实轨道前缀 rank 下界 → 真实 terminal 对齐（ResetHeadEq）。
坏前缀存在性不可独立证（13 影子，见上文），不得作为前置引理。

先读：docs/交接-hfail.md、docs/交接-hterm.md、
lean/amiya.lean、lean/kaltsit.lean、lean/CycleBridge.lean（PMI 段）、
lean/RealOrbitCharge.lean（cycleRiseBlockBalance）。

步骤：
1. 重写 hfailRankLowerBoundTarget：j 来自真实轨道前缀
   （hstart：fullOrbitIter (n0+j) = wordOrbit (w.take j) m），
   不再以 badPrefixAt P w j 作为 j 的唯一来源；
   或者把“7 的循环词必有坏前缀”并入主定理内部，使用
   hcycle 的 c、p、m = fiveXPlusOneOrbit 7 c 的具体关系，
   不单独开放。
2. 写 j → rise 块的精确映射：真实前缀深度 j 落在真实 rise 块
   （tailDepth ≤ j < tailDepth + L 或等价关系），把 rank 下界
   改写成 hfailBudgetLowerBoundAt d r 形式
   （2*(tailDepth+1)+11 ≤ 2+2N-F）。
3. 闭合 hfailBudgetLowerBound（或直接 hfailRankLowerBoundTarget）：
   用 rise_block_balance / cycleRiseBlockTailRank_lower_of_endpoint_two
   逼出 tail rank 阈值，再经块内前缀递推得坏前缀端点 rank 下界
   （2j+11 / 2j+9）。
4. 闭合 bad_prefix_terminal_alignment：
   从 rj=wordOrbit (w.take j) m 构造真实 rt 与
   ResetHeadEq rt.s j rt.k t delta rj；
   禁止在词层面停留。
5. 闭合后与 corrected 窗口上界矛盾，进入 failureWindowExistence。

纪律：单文件验证；不新增 ⇔；不复活 (6)；不标 blocked；
卡住时给出精确中间式，不换角度。
```
