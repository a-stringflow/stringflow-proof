# 交接：hsumF 整圈正向腿（2026-08-17）

## 当前状态

- 主攻文件：`lean/closure.lean`，未提交。
- 当前唯一编译错误：`cycleRiseBlockAllBelowBudgetCrush_forward` 内的
  `hsumF`（closure.lean:8510 附近），0 warning。
- `FinalTheorem.five_x_plus_one_diverges_at_7` 仍保留 `sorry`，未动。

## 唯一卡点

```text
hsumF :
  2 * Σ_r cycleRiseBlockTailDepth d r + 13 * d.blockCount
    ≤ Σ_r cycleRiseBlockTailRank d r
```

即 `2Σb + 13K ≤ ΣR`。它是 crush 归谬的**正向腿**，不是独立新引理：

- 正向腿 `hsumF` 与反证假设
  `hbelowR : ∀ r, R_r ≤ 2b_r + 12`（求和即 `ΣR ≤ 2Σb + 12K`）合起来
  得到 `2Σb+13K ≤ ΣR ≤ 2Σb+12K` 的矛盾；
- 最后一步 `allBelowBudget_contradicts_tailRankSum`（closure.lean:2547）
  已闭合。

**禁止删除 hsumF、禁止把它从 crush 证明来源中撤掉。**

## 已落库的接线（只读抽查确认存在）

- `cycleRiseBlockRotatedWordA_fourTerm_additive`（closure.lean:7715）：
  四项加法闭式，可作桥输入，但本身是恒等式，不是正向腿；
- `prefixWeightSum_wrapMerge`（closure.lean:5292）：
  `(2^S−5^P)·E0 + Σ c_r·s_r ≡ 0 [MOD 2^k]`，加法形式，未绕回整圈求和；
- `prefixWeightSum_wrapMerge_qSum`（closure.lean:8709）：
  wrapMerge 与逐块 `E_{sc_r}+5q_r` 提升后的 q-和同余；
- `t2RunRankSum_eq_two_mul_riseCountTwo`：
  `t2RunRankSum = 2H2`；
- `t2RunStartRankSum_between`（closure.lean:1866）：
  `2H2 + #runs ≤ ΣR(start) ≤ 2H2 + 2#runs`；
- `runStartRankSum_gt_boundSum_of_product_divisibility`
  （closure.lean:1129）：
  `Σ(2·start+14) < ΣR(start)`，输入是 `t2RunStartProductDivisibility`；
- `t2RunPrefixNumeratorDivisibility_iff_compensated_t2RunBound`
  （closure.lean:2070）：
  `t2RunPrefixNumeratorDivisibility ↔ U + exitPenalty < 2H2`；
- 记账对齐：`ΣF + ΣR = 2H2 + 2K`、
  `cycleRiseBlockResidualBudget_iff_tailRankBudget`（closure.lean:6526），
  因此 `hsumF ⟺ 2H2 ≥ ΣF + 2Σb + 11K`。

## 精确缺口与推荐正向腿

据主对话核对，除 `cycleQb8Input_rank_lower_prefix` 之外，整条链均已落库；
侧边只读抽查确认主要桥存在。

### 方案 A（整圈前缀分子整除）

证明真实轨道前缀分子乘积整除：

```text
t2RunPrefixNumeratorDivisibility c p :
  2 ^ (Σ W(start) + Σ(2·start+14) + 1)
    ∣ Π (2^W(start) · (fiveXPlusOneOrbit 7 (c+start) + 1))
```

其中 `W(a) = wordWeight (take a w)`，`start` 跑遍
`maxT2Runs (cycleWord c p)`。随后：

```text
t2RunStartProductDivisibility_of_prefix_numerators
→ runStartRankSum_gt_boundSum_of_product_divisibility
→ Σ(2·start+14) < ΣR(start)
→ compensated_t2RunBound：U + exitPenalty < 2H2
→ 记账对齐 → hsumF
```

### 方案 B（等号游程 rank 下界）

`cycleQb8Input_rank_lower_prefix c p`（closure.lean:2330，目前只有 `def`）：

```text
∃ a, 1 ≤ a ∧ a < p ∧ w.getI (a-1) = 2 ∧
  2a + 13 ≤ cycleWordRank c a
```

下游 `max_run_of_rank_lower`（closure.lean:2339）已闭合，只等这个
存在性由 `hcycle` 真实轨道推出。

## 纪律

- 不删除 hsumF，不换路线；
- 不搜“现成合并定理”；缺口要现写；
- 真实轨道可达性：中间式必须显式含
  `m = fiveXPlusOneOrbit 7 c`、`w = cycleWord c p` 与具体 `c`；
- 四项闭式是桥输入，不是正向腿；绕圈合并没有绕回整圈求和；
- 同余是恒等式层，撞 `hsumF` 必须让 `Δ≥1`（`5^P < 2^S`）和
  `hbelowR` 同时进入最终矛盾；
- Nat 截断减法下不套 `sum_sub_distrib`，用加法形式移项；
- 卡住时贴精确中间式，不标 blocked。

## 验证

```text
cd lean
lake env lean closure.lean
```

目标：closure.lean 0 error / 0 warning；hsumF 闭合；
随后接 `FinalTheorem` 并删掉最终 `sorry`。
