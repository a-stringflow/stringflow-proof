# 交接：crush 正向合并与主线装配

日期：2026-08-17。本文件是主线程 Lean 推进的最新恢复入口；压缩或新对话后先读本文件，
再读 `lean/closure.lean` 对应引理。旧的 `交接-crush-前缀权重同余.md` 的五步方案中，
第 1-4 步与第 5 步逐块桥已落库，本文件记录当前状态与剩余动作。

## 当前状态

- `lean/closure.lean` 编译 0 error；当前有一个 linter warning：
  `cycleRiseBlockWordA_expand_pos`（closure.lean:5885）签名变量 `d` 未引用，
  下一步先改成 `_d`。
- 最后一块新数学（q-和估值）已落库：
  - `cycleRiseBlockQSumTailRank_eq`（closure.lean:5728）：
    `v2(Σ_{r=0}^{K−2} c_{r+1}·q_{r+1}) = W_0`，前提 `2 ≤ blockCount`。
  - `cycleRiseBlockQSumTail_ge_two_pow_W0`（closure.lean:6003）：
    由 q-和估值推出的必要中间式 `2^{W_0} ≤ D`（`D` 同上）。
  - `cycleRiseBlockQSumTermRank_eq`（closure.lean:6072）：
    逐项半边 `v2(c_{r+1}·(q_{r+1}+1)) = T_{r+1} + R_{r+1}`，
    `T_{r+1} = Σ_{i≤r} W_i`。
  - `twoValuation_add_ge_min`（closure.lean:6155）：
    `v2(a+b) ≥ min(v2 a, v2 b)`，求和半边的纯代数工具。
  - `twoValuation_sum_range_ge_min`（closure.lean:6161）：
    Finset 求和版：`∃ j < m, v j ≤ v2(Σ_{r<m} a r)`。
  - `cycleRiseBlockQSumTailPlusC_rank_ge`（closure.lean:6257）：
    求和估值 `W_0 + 1 ≤ v2(Σ_r c_{r+1}·(q_{r+1}+1))`。
  - `cycleRiseBlockQSumTailPlusC_eq`（closure.lean:6263）：
    加法分解 `Σ_r c_{r+1}·(q_{r+1}+1) = D + Σ_r c_{r+1}`。
  - `cycleRiseBlockTailRankSum_add_c3WeightSum_eq_residualSum_add_two_mul_blockCount`
    （closure.lean:6303）：rank-gain 求和恒等式
    `ΣR + Σc3w = Σresidual + 2K`。
  - `cycleRiseBlockResidualBudget_iff_tailRankBudget`（closure.lean:6355）：
    目标改写 `2Σb+13K ≤ ΣR ⇔ Σresidual ≥ Σc3w + 2Σb + 11K`。
  - `cycleRiseBlockC3ResidualSum_add_two_eq_tailRank_add_c3Weight`
    （closure.lean:6381）：逐块残差加法恒等式。
  - `allBelowBudget_imp_residualSum_le`（closure.lean:6415）：
    反证侧残差和上界 `Σresidual ≤ 2Σb + Σc3w + 10K`。
  - `cycleRiseBlockQSumTermRank_eq_residual`（closure.lean:6460）：
    逐项估值配残差：
    `v2(c_{r+1}(q_{r+1}+1)) = T_{r+1} + residual_{r+1} + 2 − Σ(c3Word (r+1))`。
  - `c3_step_residual_ge_weight_sub_two`（closure.lean:6610）：
    真实轨道逐项残差：合法 C3 步的
    `v2(5·((x+1)/4) + 2^{t−2} − 1) ≥ t−2`。
  - `c3_step_residual_eq_weight_sub_two_add_rank`（closure.lean:6700）：
    逐项精确等式 `residual = (t−2) + v2(rj+1)`，
    残差超出 `t−2` 的部分正是 C3 步后状态 `rj` 的 rank。
  - `c3_step_residual_eq_weight_sub_two_add_rank'`（closure.lean:6730）：
    弱条件版（`x+1 = 4q`），C3 链后续步可用。
  - `c3Residuals_sum_eq_weights_sub_two_add_rankSum`（closure.lean:6745）：
    C3 链逐项求和：`Σresidual = Σ(t−2) + Σ_{中间C3态} v2(+1)`。
  - `c3Chain_rankSum_eq_tailRank_add_two_mul_length_sub_two`（closure.lean:6830）：
    链层逐块恒等式
    `Σ_{中间C3态} v2(+1) = tailRank + 2·c3len − 2`。
  - `cycleRiseBlockC3RankSum_eq_tailRank_add_two_mul_length_sub_two`
    （closure.lean:6816）：块级实例化
    `Σ_{块r的中间C3态} v2(+1) = R_r + 2·c3len_r − 2`。
  - `cycleRiseBlockC3RankSumSum_add_two_mul_blockCount_eq_tailRankSum_add_two_mul_c3lenSum`
    （closure.lean:6850）：全局求和（加法形式）
    `Σ_r Σ_{块r中间C3态} v2(+1) + 2K = ΣR + 2·Σc3len`。
  - `cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount_finset`
    （closure.lean:6950）：整圈 period-closure（Finset 版）
    `ΣF + ΣR = 2H2 + 2K`。
  - `cycleRiseBlockTwo_mul_H2Sum_eq_chargeSum_add_tailRankSum_sub_two_mul_blockCount`
    （closure.lean:7000）：对齐收口
    `2H2 = ΣF + ΣR − 2K`。
  - `cycleRiseBlockResidualBudget_iff_H2Budget`（closure.lean:6985）：
    整圈求和版目标改写
    `Σresidual ≥ Σc3w + 2Σb + 11K ↔ 2H2 ≥ ΣF + 2Σb + 11K`。
  - `cycleRiseBlockH2Sum_eq_t2RunRankSum`（closure.lean:7040）：
    游程求和版连接：`∃ c p, 2·H2Sum = t2RunRankSum c p`
    （`t2RunRankSum = Σ_runs (R(start) − R(start+len))`）。
  - `cycleRiseBlockT2RunRankSumBudget_of_H2Budget`（closure.lean:7072）：
    游程求和版义务：`2H2 ≥ ΣF + 2Σb + 11K` 转成具体 `c p` 的
    `t2RunRankSum c p ≥ ΣF + 2Σb + 11K`。
  - `cycleRiseBlockS_ge_two_mul_P_add_one`（closure.lean:7037）：
    `5^P < 2^S ⇒ S ≥ 2P + 1`（`5^P > 4^P = 2^{2P}`）。
  - `cycleRiseBlockS_eq_P_add_H2_add_c3WeightSubOne`（closure.lean:7078）：
    正确权重恒等式 `S = P + H2Sum + Σ_{C3}(t−1)`。
  - `cycleRiseBlock_two_pow_S_eq_two_pow_P_add_H2_add_c3WeightSubOne`
    （closure.lean:7167）与 `cycleRiseBlock_five_pow_lt_two_pow_wholeWordScale`：
    `5^P < 2^S` 的整词规模形式
    `5^P < 2^{P + H2Sum + Σ_{C3}(t−1)}`。
  - `cycleRiseBlockTailRank_eq_residualSum_sub_c3Weight_sub_two`
    （closure.lean:6518）：逐块残差恒等式
    `R_r = residualSum_r − ((c3Word r).sum − 2)`。
  - `cycleRiseBlockC3ResidualSum_eq_c3WeightSubTwo_add_midRankSum`
    （closure.lean:6800）：残差拆开（块级）
    `residualSum_r = Σ_{t∈c3Word r}(t−2) + Σ_{中间C3态} v2(+1)`。
  - `cycleRiseBlockT2RunRank_eq_wordOrbit`（closure.lean:7050）：
    游程对齐桥：块内 `riseRun` 前缀 rank = 全局深度
    `(TailDepth r + j) % P` 的 `wordOrbit` rank。
  - `cycleRiseBlockT2RunGlobalRankSum_eq_two_mul_riseCountTwo`
    （closure.lean:7078）：块级游程 rank 差和（全局深度版）
    `Σ_{runs in suffix_r} (R(全局 start) − R(全局 end)) = 2·N_r`。
  - `cycleRiseBlockT2RunGlobalRankSumSum_eq_two_mul_H2Sum`
    （closure.lean:7106）：全局形式
    `2·H2Sum = Σ_r Σ_{runs in suffix_r} (R(全局 start) − R(全局 end))`。
  - `cycleRiseBlockT2RunStart_mod_eq_add_nonwrap`（closure.lean:7125）：
    非回绕块游程起点 `%P` 消除：
    `b_r + run.start < P`，`(b_r + run.start) % P = b_r + run.start`。
  - `cycleRiseBlockT2RunStart_mod_eq_add_wrap`（closure.lean:7148）：
    回绕块游程起点 `%P` 消除：
    `(b+start) % P = b+start−P`（当 `P ≤ b+start`）或 `b+start`。
- 全链剩余义务：
  1. 正向合并引理（未落库，当前唯一数学缺口）
  2. `cycleRiseBlockAllBelowBudgetCrush`（闭合）
  3. 主线装配（hfail/hterm/trinity/FinalTheorem）

## 已落库关键引理

`lean/closure.lean`：

- `cycleRiseBlockAllBelowBudgetCrush`（2733）：目标定义 `allBelowBudget ⇒ 2^S ≤ 5^P`
- `hfailBudgetLowerBound_of_crush`（2744）：crush ⇒ `hfailBudgetLowerBound`，
  crush 闭合后直接可用
- `cycleRiseBlockAllBelowBudget_iff_tailRank_le`（2769）：
  `allBelowBudget ⟺ ∀r, R_r ≤ 2b_r+12`
- `allBelowBudget_imp_prefixWeight_sum_not_congruent`（3252）：否定侧，
  `R_r ≤ 2b_r+12 ⇒ 前缀和 ≢ 5 [MOD 2^{2b_r+13}]`
- `cyclicSumTelescope`（4487）、`prefixWeightSum_recurrence_unroll`（4590）、
  `prefixWeightSum_recurrence_unroll_simplified`（4810）
- `prefixWeightSumSegment_eq_neg_five_q_mod`（4990）：
  `E_{sc_r} + 5·q_r ≡ 0 [MOD 2^{W(sc_r)}]`
- `modEq_lower`（5098）、`prefixWeightSumList_mod_lower`（5113）
- `cycleRiseBlockSegmentErrorRank_eq`（5172）：`v2(e_r) = W_r`
- `cycleRiseBlockSegmentErrorSumRank_eq`（5423）：`v2(Σ c_r·e_r) = W_0`
- `cycleRiseBlockE0_neg_five_q_mod`（5566）：`E_0 + 5·q_0 ≡ 0 [MOD 2^S]`
- `cycleRiseBlockQSumTailRank_eq`（5728）：q-和估值
- `cycleRiseBlockWordA_expand_pos`（5885）：`5^P < 2^S ⇒ 0 < wordA w`
- `cycleRiseBlockSegmentWeight_le_S`（5902）：段权重 ≤ S

方向事实（已在 q-和证明中使用）：`c 0 = 5^P` 且 `5^P·q_0 ≤ Σ c_r·q_r`，
所以差值写加法形式 `Σ c_r·q_r − 5^P·q_0`，不写反向截断减法。

## 下一步唯一动作

当前 `closure.lean` 唯一编译错误是 `cycleRiseBlockAllBelowBudgetCrush_forward`
内 `hsum` 的最后一个未解目标（真实轨道游程义务，Finset 求和形式）：

```text
t2RunRankSum c p ≥ ΣF + 2Σb + 11K
```

该目标由 `5^P < 2^S` 正面撞出。旋转词正向侧新增三块已编译通过：

- `wordA_join_shift`（closure.lean:6950）：`A(flatten segs)` 的望远镜展开，
  系数为 `Π_{i<r}2^{W_i} · Π_{i=r+1}^{m−1}5^{n_i}`。
- `cycleRiseBlockRotatedSegments_flatten`（closure.lean:7039）：
  `rot(b_0) = sc_0 ++ sc_1 ++ ... ++ sc_{K−1}`，
  `sc_r = suffixWord r ++ cycleNextC3Word r`。
- `cycleRiseBlockRotatedWordA_join_shift`（closure.lean:7229）：
  `A(rot b_0) = Σ_r c_r·A(sc_r)`（旋转词版望远镜，系数与
  `prefixWeightSum_recurrence_unroll` 的 `c_r` 一致）。
- `cycleRiseBlockRotatedWordA_eq_q0_mul_delta`（closure.lean:7271）：
  `A(rot b_0) = q_0·(2^S − 5^P)`，`q_0 = cycleRiseBlockC3TailState d 0`。
- `cycleRiseBlockRotatedWordA_qLinear`（closure.lean:7287）：
  逐段代入 `cycleRiseBlockSegmentWordA_eq` 后的 q-线性组合
  `A(rot b_0) = Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)`。
- `cycleRiseBlockRotatedWordA_qLinear_eq_q0_delta`（closure.lean:7309）：
  `q_0·(2^S − 5^P) = Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)`。
- `cycleRiseBlockC3TailState_pos`（closure.lean:7334）：真实轨道可达性给出
  `0 < q_r`（全程整数，不用对数）。
- `cycleRiseBlockRotatedWordA_pos`（closure.lean:7356）：
  `0 < A(rot b_0)`，由 `q_0 > 0` 与 `2^S > 5^P`。
- `cycleRiseBlockRotatedWordA_qLinear_pos`（closure.lean:7370）：
  正性进入 q-线性组合：`0 < Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)`。

下一步唯一动作：用 `cycleRiseBlockSegmentWordA_eq`
（`A(sc_r) = 2^{W_r}·q_{r+1} − 5^{n_r}·q_r`）代入
`cycleRiseBlockRotatedWordA_join_shift` 的代入已落库（qLinear）。
注意：q-线性组合是望远镜，`q_0·Δ` 是它的整圈闭式；因此
`0 < Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)` 本身不直接给
`ΣR ≥ 2Σb + 13K`。下一步唯一动作：把 q-线性组合按
`2^{W_r}·q_{r+1} = c_{r+1}·q_{r+1}/系数` 与
`5^{n_r}·q_r = c_r·q_r/系数` 的望远镜拆回 `D = Σ_{r<K−1} c_{r+1}·q_{r+1}`
（q-和尾和，`hqval` 给出 `v2(D) = W_0`），
再用 `cycleRiseBlockQSumTailPlusC_eq` / `_rank_ge` 与
`hbelowR` 的逐项上界 `T_{r+1}+R_{r+1} ≤ T_{r+1}+2b_{r+1}+12`
撞出 `v2(D+Σc) ≤ W_0`，与 `W_0+1 ≤ v2(D+Σc)` 矛盾，
从而 `False.elim` 闭合 `hsum`。禁止整词段展开（判死），只允许旋转词版。

## 主线装配（crush 之后）

装配阶段代码统一写到新文件 `lean/Priestess.lean`（当前不存在，先创建并
import 所需模块，例如 `closure`、`trinity`、`amiya`）。以下步骤均在此文件内落库：

1. hfail 下界：`hfailBudgetLowerBound_of_crush` → `hfailBudgetLowerBound`
   （已有桥，crush 闭合即得）
2. hterm 选中块：`cycleQb8InputSelectedRealPredecessorIdentity` 仍是未证 def，
   内部工具已闭（`cyclic_real_predecessor_congruence_selected_of_residue_chain`、
   `cyclic_real_predecessor_identity_to_hterm`、`cycleRiseBlockHterm_of_real_predecessor`）
3. 同一块对齐：`cycleQb8InputSelectedHfailBlock`；hfail 下界来自 hcycle
   真实轨道 rank 自动机，不从 hres 推
4. trinity：`hstop` + `trinityBlockExists_of_selected_hfail_and_stop`
   → `trinityBlockExists`；上界用 `SelectedBlockData_local_window_bounds`
5. 最终：`trinity_block_contradicts` → 无周期 → `IsUnboundedOrbit 7`；
   替换 `FinalTheorem.lean:35` 的 `sorry`

## 纪律

- 不新增 `sorry`/`axiom`/伪引理占位。
- 不复活：全局比较 (6)、`realOrbitChargeBound`、`tailPerBlockCapacity`、
  PMI 前缀不等式作为唯一矛盾来源。
- 主线引理显式携带 hcycle 锚点：
  `m = fiveXPlusOneOrbit 7 c`、`w = cycleWord c p`。
- 状态核对只做一轮；辅助签名最多查 1-2 个；每轮必须有新增可编译代码
  或明确卡点报告。
- 不用对数/估值，只用整数精确恒等式。

## 验证命令

```text
lake env lean closure.lean
lake env lean Priestess.lean
lake env lean FinalTheorem.lean
```

目标 0 error / 0 warning。
