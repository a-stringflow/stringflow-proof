# Lean 形式化接线图（真实轨道可达性版）

日期：2026-08-13

状态（2026-08-14 航线修正）：`CoreAssembly` 的两处 `sorry` 所在路线作废。
`n16`、`candidate_neq_fullOrbitIter_dge9`、`CrownWindow`、`{8199,131079}`
两值归约全部是空气墙，不再进入依赖链。
唯一目标是纯块定理 `unified_core_final_no_hge_pure`，
由 capacity + valuation / `q_V` / `B_i` 闭合；
`FullOrbitFrom7` 只在最后的 full-orbit 实例化包装中使用。

## 0.0 航线修正（2026-08-14，本节优先于旧文）

旧文把 `FullOrbitFrom7 r` 与 `hReset` 放进统一核心，并按轨道深度拆出
`n≥16` 分支。这一混合架构制造了 n16、皇冠、两值归约等不可证影子。
主链文档 [5x1_7_divergence_main_chain.md](5x1_7_divergence_main_chain.md)
的局部引理从来是纯块语句，不需要轨道深度。

正确拆分：

```lean
-- 唯一主攻击目标：只吃块前提，不碰 FullOrbitFrom7 / hReset / n
theorem unified_core_final_no_hge_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hH : 2 ≤ H_s) :
    twoValuation (5^(L+3) * wTerminal L r_s + 1) ≤ H_s - 2

-- 薄包装：真实块首只是纯定理的一个实例
theorem unified_core_final_no_hge_full_orbit
    (… hPrem …) (hrj : r = (Aj + 5^j*q)/2^Wj)
    (hReach : FullOrbitFrom7 r) :
    twoValuation (5^(L+3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  exact unified_core_final_no_hge_pure … hPrem hH
```

纯块目标等价于主链的
`F_i = X_i + 2D_i − 2i ≤ 13`，
即 `v ≤ 2(j−t_j)+12−2h_i`。

本文第 3、4 节的 d≥3/首大步/n16 装配说明自本节起作废，只作历史记录。

核心原则（2026-08-14 起）：纯块定理 `unified_core_final_no_hge_pure`
只由 `All36_20PremisesNoHge` 证明，不使用 `FullOrbitFrom7` 或 `hReset`；
`FullOrbitFrom7` 仅用于最后的 full-orbit 包装。旧文的候选/段/窗口
实例化原则只对已闭合的 d≤8 等历史分支适用，不再是统一核心的主线。

## 执行优先（铁律）

文档已给出装配步骤时，禁止重新讨论“够不够”；
直接打开对应 Lean 文件写代码，写完立即运行
`lake env lean <文件>.lean`。

- 不写新的计划文档或 goal prompt；
- 不发明新 gap；
- 不先报“缺前提”；
- 只有编译错误才回到文档分析，且只按第 0 节九条找来源。

## 调用前前提映射协议（硬性）

调用任何下游引理前，必须先逐条写清它的每个输入从哪来：

1. 下游引理签名里的每个输入，只允许两个来源：
   - 当前定理签名里的参数；
   - 证明体内已经写出的 `have`。
2. 禁止把 `have` 改成新参数；禁止改定理签名来“补前提”。
3. 调用前先写注释，例如：

```lean
-- d≥4/首大步分支先取真实轨道段方程 orbitSegmentWord_candidate_equation；
-- first_big_step_unique 只能定位首个 t≥3 步（深度 15、权重 3），
-- 其 hsmall 对真实轨道深度 ≥15 不成立，不能直接实例化。
```

4. 如果某个输入映射不上，先过第 0 节九条；
   九条都查完仍没有，才允许新增装配引理，且新引理必须从
   `FullOrbitFrom7` 推出。
5. 只要还有输入没映射，就不调用该引理；先写生成它的 `have`，再继续。

## 0. 遇到所谓“条件不足 / 缺前提”时（铁律）

不许先说缺前提。先用真实轨道可达性
`FullOrbitFrom7` / `fullOrbitIter` 逐条检查：

1. 这个量是不是某个真实轨道状态？
   - `r = fullOrbitIter n`
   - `x = fullOrbitIter (n - 1)`
   - `g = fullOrbitIter (j - 1)`
   - `rj = fullOrbitIter ...`
2. 它是不是由真实轨道桥接引理推出的结论？
   - `candidateRj_eq_fullOrbitIter_of_weight`
   - `candidate_parameterization_of_reset_full_orbit_d_aligned`
   - `fullOrbitStep_eq_of_candidateRj`
   - `orbitSegmentWord_candidate_equation`
3. 它是不是由“首个 `t ≥ 3` 步”的分支结构 + 有限前缀给出？
   - `first_big_step_unique`
   - `fullOrbit_first_t_ge3_is_exactly_3`
   - `candidate_first_big_step_weight_ne_three`
   - `candidate_first_big_step_weight_ge_five`
4. 它是不是由真实段方程 + 候选式推出？
   - `5^(j-1) % L = C`
   - `x = candidateX ...`
   - `j - 2 ≤ 15` / `j ≤ 17`
5. 它是不是由上一终端 / 剥离族推出？
   - `previous_terminal_strip_reaches_eight`
   - `reverseStripN_*`
   - `legal_word_prefix_exact_of_even_terminal`
   - 这是 `j - 2 ≤ 15` / `j ≤ 17` 的真正来源。
6. 它是不是由真实轨道尺寸界推出？
   - `fullOrbitIter_upper_bound`
   - `fullOrbitIter_lt_five_pow`
   - `fullOrbitIter_lt_five_pow_div_four`
   - d=1/d=2 的尺寸矛盾都靠这一类。
7. 它是不是由模 5 刚性 / 模类推出？
   - `fullOrbit_not_dvd_five`（36.30.23.0）
   - `block_head_mod_five_of_premises`（36.30.23.1）
   - `previous_terminal_s0_mod_five_of_k0`
   - `candidateX_mod4_of_e2/e_ge3`
8. 它是否只能在尾部失败上下文推出？
   - `tail_failure_m2_zero_block_head_mod16` → `r % 16 = 5`
   - `predecessor_mod32_of_block_head_mod16_t1` /
     `predecessor_mod64_of_block_head_mod16_t2`
   - 这是 `x ≡ 21/55`、`x ≡ 53/183` 的唯一合法来源；n16 不走这条。
9. 它是不是由循环词 / QB-8 / 窗口投影推出（最终装配层）？
   - `orbit_cycle_imp_cycle_qb8_input`
   - `cycleWord_*`
   - `ResetWindowReachability` 的投影

只有以上九条都推不出时，才允许新增引理；新增的也是“从
`FullOrbitFrom7` 推出的装配引理”，不是新的前提。

这九条是固定记忆清单：遇到卡住先按顺序过一遍，再谈“缺前提”。
九条是完整的；所谓“额外段权上界”不是九条外的新性质，就是
第 6 条真实轨道尺寸界。

典型被误报为“缺前提”的对象：

| 对象 | 真实来源 |
|---|---|
| `hsmall` | 只对真实轨道深度 `< 15` 成立（`t15=3`、`t17=4`）；用于定位首个大步，不能约束深度 `≥ 17` 的后续大步 |
| `x = fullOrbitIter (n - 1)` | `candidateRj_eq_fullOrbitIter_of_weight` |
| `ResetWindowReachability` | `FullOrbitFrom7 rj + ResetHeadEq + 上一终端方程` |
| `j - 2 ≤ 15` / `j ≤ 17` | `hseg` 使第一步剥到 `f(j-2)+1`，随后沿真实轨道反向剥离；若 `j-2 ≥ 16` 则停在 `f(16)+1`，与剥到 `8` 矛盾 |
| `x ≡ 53/183 (mod 160/320)` | 候选剩余类；仅尾部失败上下文可用，n16 不走这条 |
| `e=3,j=17` 排除 | 真实段方程 + 尺寸界；`x≡53/183` 的修正同余引理仅尾部失败上下文可用，n16 不走这条 |
| `r % 16 = 5` | `tail_failure_m2_zero_block_head_mod16`，仅失败分支 |
| `x ≡ 21/55 (mod 32/64)` | `predecessor_mod32/64_of_block_head_mod16_*`，需要上一条 |
| `fullOrbitIter n < 5^n / 4` | `fullOrbitIter_lt_five_pow_div_four` |
| `OrbitCycle 7 → CycleQb8Input` | `orbit_cycle_imp_cycle_qb8_input` |

## 1. 真实轨道可达性

- `FullOrbitFrom7 r` 的定义是 `∃ n, fullOrbitIter n = r`（`S6AuditStage1.lean`）。
- `hiter : fullOrbitIter n = r` 是 `n16_core_impossible` 的真实轨道输入。
- 候选 `x` 只有在 `x = fullOrbitIter (n - 1)` 时才是真实前驱。
- `ResetWindowReachability` 自带 `FullOrbitFrom7 rj`，因此天然是真实轨道对象。
- 写桥接定理时，`fullOrbitIter` 的 witness 必须原样保留，不能用
  `GeneralOrbitFrom7` 或候选算术代替。

## 2. `n16_core_impossible` 已推出事实

以下事实在当前证明体内已经推出，不需要新增前提：

| 量 | 来源 |
|---|---|
| `k = 0` | `reset_k_zero_of_previous_terminal_depth` |
| `s0 % 5 = 4` | `previous_terminal_s0_mod_five_of_k0` |
| `3 ≤ j` | `previous_terminal_at_depth_ge_three` |
| `e = orbitStepWeight (j - 2)` | 定义 |
| `g = fullOrbitIter (j - 1)` | 定义 |
| `x = fullOrbitIter (n - 1)` | `candidateRj_eq_fullOrbitIter_of_weight`，输入 `hstep_t` |
| `x = candidateX j e g δ` | `candidate_parameterization_of_reset_full_orbit_d_aligned` |
| `t = orbitStepWeight (n - 1) ∈ {1,2}` | `orbitStepWeight_of_reset_head_le_two` + `hv2` |
| `r = fullOrbitIter n` | `hiter` |

## 3. d≥3 分支接线

### 3.1 新增装配引理（不是新数学）

1. `j_le_17_of_real_terminal`
   - 输入：`hReset` 展开后的 `PreviousTerminalAtDepth`、
     `s0 * 5^k = r_prev + 1`、`hiter`、`hPrem`、`hrj`、`hH`。
   - 结论：`j - 2 ≤ 15`。
   - 路线：
     - `hseg`：`r_prev = (5 * fullOrbitIter (j-2) + 1) / 2`，所以
       `s0 = (5*f(j-2)+3)/2` 且 `s0 % 5 = 4`；
     - `reverseStripN_t1`：第一步剥离直接得到 `f(j-2)+1`；
     - `reverseStripN_fullOrbit_step_le_two`：`f(i)+1 → f(i-1)+1`
       在 `orbitStepWeight(i-1) ≤ 2` 时精确成立；
     - 若 `j-2 ≥ 16`，真实轨道在深度 15 有权重 3，剥到 `f(16)+1`
       后由 `reverseStripN_fullOrbit_step_16_stop` / `reverseStripN_stop_all`
       永久停止，不能再等于 `8`；
     - `previous_terminal_strip_reaches_eight` 给出的见证保证
       `reverseStripN w.length s0 = 8`，故只能 `j-2 ≤ 15`。
   - 禁止用 canonical word 跑剥离；禁止用 `r % 16`；
     禁止把 `w.length = j-1` 当作前置；此路线不需要轨道单射。

2. `d3_branch_impossible`
   - 输入：`hd3 : n - j = 3`，其余同 `n16_core_impossible`。
   - 当前干净路线是 `CoreBranches.d3_n16_impossible_by_size`：
     由 `j ≤ 17`、`n-j = 3`、`n ≥ 16` 得 `13 ≤ j ≤ 17`，
     再用 `fullOrbitIter_prefix_expand_18/20` 逐项比较
     `x ≥ 5^(j-1)` 与 `x = fullOrbitIter(j+2) < 5^(j-1)`。
   - 21 个 `d3_*_no_pow` 是尾部失败分支的候选排除表（其模 2 分量
     依赖 `x≡21/55 (mod 32/64)`，而后者来自 `r % 16 = 5`）；
     `n16_core_impossible` 没有失败假设，不得调用这张表。

3. `dge4_branch_impossible`
   - 输入：`hdge : 4 ≤ n - j`，其余同上。
   - 分支结构：
     - 主入口是精确、无条件的真实轨道段方程：
       `orbitSegmentWord_candidate_equation j d e g δ`，不需要 `hsmall`；
     - `fullOrbit_first_t_ge3_is_exactly_3` 只用于钉住首个大步：
       深度 15、权重 3；真实轨道 `t17=4`，因此后续大步不能再用
       `first_big_step_unique` 约束；
     - `e ≥ 3`：由 `j-2 ≤ 15` 与深度 15 首大步得 `j=17`、`e=3`、
       `g=34177`；把 `x = candidateX 17 3 34177 δ` 代回段方程，
       用 `fullOrbitIter_lt_five_pow_div_four` 与 `wordA` 尺寸界排除；
     - `e = 2`：把 `x = 2*g + δ*5^(j-1)` 代回段方程，按段内真实
       步权 `u_i` 与 `wordA` 上界推出矛盾。
   - 禁止在 `n ≥ 17` 的真实轨道上实例化
     `candidate_first_big_step_weight_ne_three/ge_five` 或
     `dge4_e2_exclusion_of_orbit`：它们的 `hsmall` 前提为假。

### 3.2 已存在但需要实例化的引理

- `orbitSegmentWord_candidate_equation`：真实段方程，d≥4 与首大步分支的主入口。
- `orbitSegmentWord_getD`：段内精确步权。
- `candidateX_mod4_of_e2` / `candidateX_mod4_of_e_ge3`：候选模 4。
- `previous_terminal_s0_mod_five_of_k0`：`s0 ≡ 4 (mod 5)`。
- `fullOrbitIter_lt_five_pow_div_four`：真实轨道尺寸界。
- `fullOrbitIter_prefix_expand_18` / `fullOrbitIter_prefix_expand_20`：
  d=3 有限分支的轨道值。
- 以下仅尾部失败分支可用，n16 不实例化：
  - `d3_t1_*` / `d3_t2_*` 共 21 个 `d3_*_no_pow`；
  - `dge4_e3_j17_t1_corrected_excluded` /
    `dge4_e3_j17_t2_delta3_corrected_excluded`（输入 `x≡53/183`）。

## 4. 首大步分支接线

位置：`CoreAssembly.lean:126`，`¬ hv2` 且 `n - 1 ≥ 18`。

| 需要 | 来源 |
|---|---|
| `fullOrbitStep x = r` | `fullOrbitStep_eq_of_candidateRj`，输入 `hrx`、`r` 奇、`hdiv_t` |
| `x` 是奇前像 | `candidateRj_predecessor_odd` |
| 深度 15、权重 3 是首个大步 | `fullOrbit_first_t_ge3_is_exactly_3` |
| 步入 `r` 的 `w = orbitStepWeight(n-1) ≥ 3` 不是首个大步 | `omega`（`n-1 ≥ 18 > 15`） |
| 消除 `w` 与 `t∈{1,2}` 的差 | `2^t*r = 5x+1` 与 `2^w*r = 5*f(n-1)+1` 相减，得 `5 | 2^(w-t)-1`，即 `w ≡ t (mod 4)` |
| 最终矛盾 | 把 `f(n-1) = x + 2^t*((2^(w-t)-1)/5)*r` 代回 `orbitSegmentWord_candidate_equation`，配合尺寸界 |

此分支不需要 `x = fullOrbitIter (n - 1)` 对齐，也不需要 `fullOrbitStep` 单射；
`first_big_step_unique` 不能在这里实例化，因为其 `hsmall` 对真实轨道
`n ≥ 17` 为假。当前缺的是上表中最后一步“段方程 + 尺寸界”的纯整数不等式，
不是一个新的前提。

## 5. 最终装配

| 目标 | 输入 | 来源 |
|---|---|---|
| `unified_core_final_no_hge` 闭合 | d≥3 与首大步分支闭合 | 自动 |
| `DwdbDiv.unifiedCoreClosed` | `unifiedCoreClosed_proved` | 已写好 |
| `unifiedCoreClosed → decisiveWindowValuationBoundCorrected` | `ResetWindowReachability` 展开出 `FullOrbitFrom7 rj`、`ResetHeadEq`、上一终端方程 | 对 `unifiedCoreClosed` 做参数实例化 |
| `failureWindowExistence` | 真实 `CycleQb8Input` 来自 `OrbitCycle 7`，词内块首都是 `FullOrbitFrom7` | 用 CycleBridge 已有 margin/budget 结构 + 窗口界构造 `FailureWindow` |
| `FinalTheorem.five_x_plus_one_diverges_at_7` | 上面两个定理 | `CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window` |

## 6. 写代码检查表

写 Lean 4 之前，对每个下游定理签名逐条问：

0. 这个量能不能由 `FullOrbitFrom7` / `fullOrbitIter` 推出？
1. 这个前提是当前定理签名里的哪个变量？
2. 它由哪个已证引理给出？
3. 如果它是 `hsmall`、`x = fullOrbitIter (n - 1)`、
   `ResetWindowReachability` 这类对象，它是否由真实轨道可达性 + 分支结构
   构造，而不是需要新增前提？
4. 如果答不上来，先按第 0 节的四条规则再查一遍，再补装配引理；
   不要先说“缺前提”。

## 7. 文件边界

- 只允许在以下文件新增装配/翻译代码：
  `CoreBranches.lean`、`CoreAssembly.lean`、`DwdbDiv.lean`、`FinalStatement.lean`。
- 不改已编译且已闭合的引理。
- 每写完一个文件/引理，立即运行：
  `lake env lean <文件>.lean`（从 `lean` 目录）。
- 文档已有装配步骤时，直接执行；只有编译错误才回到分析。
- 调用下游引理前先做前提映射，写清“输入 ← 哪个 have / 哪条引理”。
- 最终验收：`lake build` 全绿、`sorry=0`、无自定义 axiom、
  无 `native_decide`、无 `GeneralOrbitFrom7`。
