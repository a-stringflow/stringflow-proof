# Goal Prompt：闭合 hsumF（整圈正向腿）

目标：闭合 `lean/closure.lean` 当前唯一编译错误
`cycleRiseBlockAllBelowBudgetCrush_forward` 内的 `hsumF`
（closure.lean:8510 附近）：

```text
2 * Σ_r cycleRiseBlockTailDepth d r + 13 * d.blockCount
  ≤ Σ_r cycleRiseBlockTailRank d r
```

即 `2Σb + 13K ≤ ΣR`。

## 归谬结构（先记住，再动笔）

`hsumF` 是 crush 归谬的**正向腿**，不是独立新引理：

- 反证假设已就位：`hbelowR : ∀ r, R_r ≤ 2b_r + 12`，
  求和即 `ΣR ≤ 2Σb + 12K`；
- 正向腿与上界合起来得到
  `2Σb+13K ≤ ΣR ≤ 2Σb+12K` 的矛盾；
- 最后一步 `allBelowBudget_contradicts_tailRankSum`
  （closure.lean:2547）已闭合，只等 `hsumF`。

**禁止删除 hsumF、禁止把它从 crush 证明来源撤掉。**

## 已落库接线（不要重新搜，直接调用）

- `cycleRiseBlockRotatedWordA_fourTerm_additive`（closure.lean:7715）：
  四项加法闭式，可作桥输入；它是充要恒等式，不是正向腿；
- `prefixWeightSum_wrapMerge`（closure.lean:5292）：
  `(2^S−5^P)·E0 + Σ c_r·s_r ≡ 0 [MOD 2^k]`，加法形式；
- `t2RunRankSum_eq_two_mul_riseCountTwo`：`t2RunRankSum = 2H2`；
- `t2RunStartRankSum_between`（closure.lean:1866）：
  `2H2 + #runs ≤ ΣR(start) ≤ 2H2 + 2#runs`；
- `runStartRankSum_gt_boundSum_of_product_divisibility`
  （closure.lean:1129）：`Σ(2·start+14) < ΣR(start)`；
- `t2RunPrefixNumeratorDivisibility_iff_compensated_t2RunBound`
  （closure.lean:2070）：`t2RunPrefixNumeratorDivisibility ↔
  U + exitPenalty < 2H2`；
- 记账：`ΣF + ΣR = 2H2 + 2K`、
  `cycleRiseBlockResidualBudget_iff_tailRankBudget`
  （closure.lean:6526），所以
  `hsumF ⟺ 2H2 ≥ ΣF + 2Σb + 11K`；
- `cycleQb8Input_forced_two_after_prefix`
  （RealOrbitLocalLemma.lean:2026）、`t2_step_rank_ge_three`、
  `fullOrbitIter_rank_drop_two_iter`、`max_run_of_rank_lower`
  （closure.lean:2339）均已闭合。

## 精确缺口（先写这条）

`cycleQb8Input_rank_lower_prefix c p`
（closure.lean:2330，目前只有 `def`，未证）：

```text
∃ a, 1 ≤ a ∧ a < p ∧ w.getI (a − 1) = 2 ∧
  2a + 13 ≤ cycleWordRank c a
```

即存在一个 `t=2` 前缀，其真实轨道 rank 达到 `2a+13`。
证明必须显式使用 `hcycle` 锚点：
`w = cycleWord c p`、`m = fiveXPlusOneOrbit 7 c`，
以及具体 `c` 的状态界。

落库后接线：

```text
cycleQb8Input_rank_lower_prefix
→ max_run_of_rank_lower
→ 等号游程 → t2RunRankSum 下界 → 记账对齐 → hsumF
```

## 备选整圈入口

若存在性路线暂时推不动，允许走整圈前缀分子整除：

```text
t2RunPrefixNumeratorDivisibility c p :
  2 ^ (Σ W(start) + Σ(2·start+14) + 1)
    ∣ Π (2^W(start) · (fiveXPlusOneOrbit 7 (c+start) + 1))
```

经 `t2RunStartProductDivisibility_of_prefix_numerators` →
`runStartRankSum_gt_boundSum_of_product_divisibility` →
`compensated_t2RunBound` 得 `U + exitPenalty < 2H2`，
再经记账对齐得 `hsumF`。

## 禁止

- 不删除 hsumF、不换路线、不把四项闭式当正向腿；
- 不搜“现成合并定理”，缺口现写；
- 不落“块尾 rank ≥ 块内所有游程起点 rank”的逐块桥
  （`t=1` 跳跃反例：起点 rank 可大于块尾 rank）；
- 不回到逐点 rank 下界、D+Σc 上界、乘积 v2、PMI 唯一矛盾；
- Nat 截断减法下不套 `sum_sub_distrib`，用加法形式移项；
- 不标 blocked；卡住时贴精确中间式与已试引理；
- 13/17 影子不是反例，中间式必须显式含 hcycle 的 `c`。

## 验证

```text
cd lean
lake env lean closure.lean
```

完成后：closure.lean 0 error / 0 warning；
随后 `FinalTheorem.five_x_plus_one_diverges_at_7` 删除 `sorry`。
