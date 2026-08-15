# Lean 装配计划：从 FinitePrefix 到 unified_core_final_no_hge

日期：2026-08-13

数学层 36.30.23 的排除链已经闭合，`lean/FinitePrefix.lean` 已编译。
以下是把这条链装配进 `lean/UnifiedCoreAudit.lean` 的
`unified_core_final_no_hge`（当前 `sorry`）所需的 Lean 步骤。

> 2026-08-14 航线修正：本文件的 d 段/n16 装配路线作废。
> 该路线制造的 `candidate_neq_fullOrbitIter_dge9`、CrownWindow、
> `{8199,131079}` 是空气墙。统一核心应拆为
> `unified_core_final_no_hge_pure`（纯块，capacity + valuation /
> `q_V` / `B_i` 闭合）与 `unified_core_final_no_hge_full_orbit`
> （用 `FullOrbitFrom7` 实例化纯定理）。本文件仅作历史记录。

## blocked 撤销记录

本目标从未处于合理 blocked 状态：装配可以继续，不把工作推回用户。
当前 goal 状态为 active，继续逐层接入已编译引理。

## 装配依赖表

| 阶段 | 语句 | 依赖的已编译引理 |
|---|---|---|
| 1a | `All36_20PremisesNoHge + FullOrbitFrom7 r → ResetHeadEq` | 尚未编码；代数端依赖 `block_head_identity_of_reset`、`reset_q0_form`、`q0_interval_iff_rj_bound`，轨道端依赖 `FullOrbitFrom7` 提取 |
| 1b | `k=0` 与首块终端 `s0-1=2^(e-1)g` | 尚未编码；依赖 `fullOrbitFrom7_le15_imp_OrbitFrom7`、`fullOrbitPrefix_imp_OrbitFrom7`、`first_block_terminal_eq` |
| 2a | `d=1` 段长排除 | `d1_segment_equation` + `d1_exclusion` 已封装为 `d1_exclusion_of_orbit` |
| 2b | `d=2` 段长排除 | `d2_segment_equation` + `d2_exclusion` 已封装为 `d2_exclusion_of_orbit` |
| 2c | `d=3` 唯一族排除 | `d3_family_big_weight_excluded`、`d3_family_bridge_contradicts`、`FinitePrefix.d3_family_mod_contradicts_base`；轨道段方程输入待接入 |
| 2d | `d≥4` 排除 | `dge4_e2_a_ge1_excluded`、`dge4_e3_j17_t1/t2_excluded`、`FinitePrefix`；轨道段方程输入待接入 |
| 3 | 候选族为空 → 36.30.7 块首候选排除 | 由 2a--2d 组装，另依赖 `candidateX_mod4_of_e2/e_ge3` 的分支收缩 |
| 4 | 最终估值不等式 `v2(5^(L+3)w+1) ≤ H_s-2` | `terminal_bound_iff_not_dvd`、`yStar_eq_zero_iff_congruence`、`rj0_ge_of_size_conditions_no_hge`、`blockB_bound_of_no_hge` |
| 5 | `unified_core_final_no_hge` | 1a/1b + 2a--2d + 3 + 4 合成 |

## 1. 候选单状态参数化（待编码）

`lean/UnifiedCoreBridge.lean` 已编码并编译：

```text
x = 2^(e-1)·g + δ·5^(j-1),
g = fullOrbitIter (j-1),
```

对应定义 `candidateX`、`candidateRj`、`orbitState`、
`orbitStepWeight`。其中 `e=t_(j-2)=v2(5·g_prev+1)≥2`，
`δ∈{1,3}`，`t_j∈{1,2}`。这一步对应文档
36.30.23.3/36.30.23.4。

### 1a. 修正后的 reset 前提（2026-08-13）

`unified_core_final_no_hge` 与 `DwdbDiv.unifiedCoreClosed` 的 reset
前提现为

```lean
hReset : ∃ s0 k t δ r_prev : Nat,
  S6Audit.ResetHeadEq s0 j k t δ r ∧ s0 * 5 ^ k = r_prev + 1
```

块首可达性保持 `hReach : FullOrbitFrom7 r`（真实完整轨道），不使用
`GeneralOrbitFrom7` 作为新前提。上一终端只以算术方程
`s0 * 5^k = r_prev + 1` 进入；`r_prev` 是算术见证，不是一般轨道
可达性输入。

### 1b. 真实轨道上一终端恒等式（下一个待编码引理）

2026-08-13 已编译的真实轨道桥接：

- `reset_weight_eq_of_premises`：`weight j - weight (j-1) = t`；
- `blockState_pred_eq_of_reset_head`：`blockState weight q (j-1) = x`；
- `orbitStepWeight_of_reset_head_le_two`：小步分支下
  `orbitStepWeight (n0-1) = t`；
- `reset_predecessor_eq_fullOrbitIter_of_le_two`：小步分支下
  `x = fullOrbitIter (n0-1)`；
- `blockState_pred_eq_fullOrbitIter_of_le_two`：
  `blockState weight q (j-1) = fullOrbitIter (n0-1)`。

### 1c. 索引约定待确认

`d1_exclusion_of_reset_candidate` / `d2_exclusion_of_reset_candidate`
把 `ResetHeadEq` 深度写成 `n0-1`（候选 x 的轨道深度）。需要确认
premises 的块深度 `j` 与块首轨道深度 `n0` 的约定：

- 约定 A：`j = n0`；
- 约定 B：`j = n0 - 1`。

该约定决定 d 段实例化桥使用 `n0 := j` 还是 `n0 := j+1`。

从 `All36_20PremisesNoHge` + `FullOrbitFrom7 r` + `hReset` 需要证明

```lean
2 * 5^k * s0 = 5 * g_prev + 3
```

其中 `g_prev = fullOrbitIter (n0 - 2)` 是块首前两步的真实轨道状态。
等价地，`r_prev = (5 * g_prev + 1) / 2`。该恒等式由真实轨道词
（`fullOrbitIter_general` 给出精确词，再接一步 `t=1`）与重置方程
推出，不引入 `GeneralOrbitFrom7` 前提。证明后再调用
`previous_terminal_hr_of_word_and_segment` 与
`terminal_chain_identity_of_full_orbit_d` 得到
`5^k * s0 = 2^(e-1) * g + 1`。

## 2. 段长排除（数学已闭合，Lean 待装配）

桥接层 `UnifiedCoreBridge.d3_family_bridge_contradicts` 与
`UnifiedCoreBridge.candidate_first_big_weight_ge_five_bridge`
已编译，用 `orbitStepWeight` 包装 `FinitePrefix` 的对应排除。
尚未编码的是从 `All36_20PremisesNoHge` 导出这些 `orbitStepWeight`
前提的完整推导。

该缺失推导的精确语句是：对

```text
hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight,
hReach : FullOrbitFrom7 r,   r = (Aj + 5^j q)/2^Wj,
```

证明存在 `g,e,δ,t_j,d` 与段词 `u_1..u_d` 满足
`orbitState (j-1) g`、`candidateX j e g δ = x`，
且首个 `t≥3` 位置/步权落入 `FinitePrefix` 排除分支；然后调用
`d3_family_bridge_contradicts` 或
`candidate_first_big_weight_ge_five_bridge` 得 `False`。

该缺失推导的精确语句是：对

```text
hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight,
hReach : FullOrbitFrom7 r,   r = (Aj + 5^j q)/2^Wj,
```

证明存在 `g,e,δ,t_j,d` 与段词 `u_1..u_d` 满足
`orbitState (j-1) g`、`candidateX j e g δ = x`，
且首个 `t≥3` 位置/步权落入 `FinitePrefix` 排除分支；然后调用
`d3_family_bridge_contradicts` 或
`candidate_first_big_weight_ge_five_bridge` 得 `False`。

## 3. 候选族为空 → 36.30.7 闭合

由候选族为空证明不存在满足 36.30.7 的
`(j,k,s0,δ,t_j,q,A_j,W_j,W_p)`，即块首候选排除闭合。

## 4. 接入最终估值不等式

把 36.30.7 闭合接到
`unified_core_final_no_hge` 的 `FullOrbitFrom7 r` 前提上：

1. 使用 `S6Audit` 已有的 q0/CRT/剥离引理；
2. 使用 `UnifiedCoreAudit` 已有的
   `rj0_ge_iff_terminal_bound`、`rj0_ge_of_size_conditions_no_hge`
   等桥接；
3. 最后把 `sorry` 替换为上述引理合成。

## 当前状态

- 数学层：闭合。
- Lean 基例与关键矛盾引理：`FinitePrefix.lean` 已编译。
- 有限前缀桥接：`FinitePrefix.fullOrbitPrefixWord` 及其
  `fullOrbitPrefix_wordValid` / `fullOrbitPrefix_wordOrbit` /
  `fullOrbitPrefix_imp_OrbitFrom7` 已编译：深度 `n≤15` 的完整轨道
  状态等价地由合法 `{1,2}` 词 `OrbitFrom7` 到达。
- 轨道刚性：36.30.23.0（全轨道状态不被 5 整除）与
  36.30.23.1（块首模 5 类）已在 `UnifiedCoreBridge.lean` 编译。
- 分支收缩表：36.30.23.4 的 `candidateX_mod4_of_e2` 与
  `candidateX_mod4_of_e_ge3` 已编译（`e=2` 时 `x≡2+δ (mod 4)`，
  `e≥3` 时 `x≡δ (mod 4)`）。
- 段长 `d=1` 排除已在 `UnifiedCoreBridge.d1_exclusion` 编译。
- 段长 `d=2` 已完整编译：`d2_size_exclusion`（尺寸分支）、
  `d2_survivor_congruences`（末支两条同余）、
  `d2_survivor_mod_contradicts`（模矛盾）与 `d2_exclusion`。
- `orbitStepWeight_of_mul` 已编译：把 `5y+1=2^k*x`（`x` 为奇轨道态）
  直接转成 `orbitStepWeight n=k`，是 `d=3`/`d≥4` 首大步权输入的
  可复用接口。
- `d3_family_big_weight_excluded` 与 `dge4_e2_a_ge1_excluded` 已编译：
  把 `d=3` 唯一族与 `d≥4` 的 `e=2,a≥1` 分支接到
  `FinitePrefix` 的首大步矛盾上。
- `dge4_e3_j17_t1_excluded` / `dge4_e3_j17_t2_delta3_excluded`
  已编译：`e=3,j=17` 分支的 `mod 640/1280` 候选剩余类排除。
- 参数化桥接的代数核心已编译：
  `reset_head_predecessor`（36.30.9.1）与
  `candidateX_of_reset_and_terminal`（36.30.23.3+23.4）。
- `first_block_terminal_eq`（36.30.23.3）已编译：完整轨道步
  `5·g_prev+1=2^e·g` 与 `r=(5·g_prev+1)/2` 推出 `r=2^(e-1)·g`。
- `reset_q0_form`（36.30.8.2）已编译：精确恒等式
  `A_j+5^j·q=2^L·(B+δ·5^j)` 推出 `q=m+δ·2^L` 且 `m<2^L`。
- `block_head_identity_of_reset` 已编译：块首表示 + `ResetHeadEq`
  推出 36.30.8.2 的精确恒等式
  `A_j+5^j·q=2^Wp·(5^(k+1)·s0-4+δ·5^j)`。
- `fullOrbitFrom7_le15_imp_OrbitFrom7` 已编译：`FullOrbitFrom7`
  的有限前缀分支可以切回 `OrbitFrom7`，供 `local_lemma_final`
  的既有闭合复用（注意：`local_lemma_final` 本身带
  `native_decide` 有限闭包，不进主链）。
- 段词层已编译：`orbitSegmentWord` 及其
  `orbitSegmentWord_orbit` / `orbitSegmentWord_valid` /
  `orbitSegmentWord_equation`，给出完整轨道任意连续段的精确词方程
  `2^W·x = 5^d·g + A`。
- 段方程桥接已编译：`orbitSegmentWord_candidate_equation` 把候选
  `x = candidateX j e g δ` 代入段词方程；
  `d1_segment_equation` / `d2_segment_equation` 给出 `d=1`、`d=2`
  的精确段方程。
- 排除入口已编译：`d1_exclusion_of_orbit` / `d2_exclusion_of_orbit`
  从完整轨道数据直接调用 `d1_exclusion` / `d2_exclusion`。
- 失败定位层已编译（`UnifiedCoreAudit`）：
  `wTerminal_mul_eq`、`failure_cleared_iff`、
  `failure_w_congruence`、`failure_rs_cleared_congruence`、
  `three_cancel_modEq`、`failure_rs_unique`、`r_s_dyadic_bounds_of_no_hge`；
  这些给出“若终态失败，则 `w` 被钉到 `uResidue`，且所有失败
  `r_s` 落在同一个 `mod 2^(L+H_s+3)` 候选类”的干净入口。
- 候选算术级数已编译：`failure_w_progression` /
  `failure_rs_progression` 把失败候选写成
  `3*r_s+1 = 2^(L+4)*(uResidue + k*2^(H_s-1))`；
  `yStar_zero_implies_rs_candidate_class` /
  `terminal_failure_implies_candidate_class` 把 `y*=0` 与终态失败
  直接接到该候选类。
- 尚未编码：`All36_20PremisesNoHge + FullOrbitFrom7 r` 到候选
  参数化的轨道词结构推导（`ResetHeadEq`、`k=0`、首块终端方程），
  以及把 `d=3`、`d≥4` 排除接到候选段方程的完整推导。
- `unified_core_final_no_hge`：仍为 `sorry`，是唯一剩余语句。
