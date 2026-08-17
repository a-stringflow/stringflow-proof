# 交接：crush 正向侧（前缀权重 5-adic 望远镜）

日期：2026-08-17。本文件是主线程 Lean 推进的恢复入口；压缩后先读本文件，
再读 `lean/closure.lean` 与 `lean/RiseDecompositionAssembly.lean` 的对应引理。

## 当前状态

- `lean/closure.lean`、`lean/RiseDecompositionAssembly.lean` 均编译通过
  （`lake env lean closure.lean` 0 error / 0 warning）。
- 全链剩余义务只有一条：

  ```text
  cycleRiseBlockAllBelowBudgetCrush :
    cycleRiseBlockAllBelowBudget d ⇒ 2^S ≤ 5^P
  ```

  它闭合后 `hfailBudgetLowerBound_of_crush` 立即给出
  `hfailBudgetLowerBound`，进入 Trinity 装配。

## 已落库并编译的关键引理

`lean/RiseDecompositionAssembly.lean`：

- `wordA_append_shift`：`A(v++u) = 5^|u|·A(v) + 2^W(v)·A(u)`
- `cycleRiseBlockUniformLocalBlockData`：每块 C3-tail 边界处统一实例化
  `cycleQb8Input_cyclic_local_block_data`（不依赖 hterm/rt）
- `cycleRiseBlockUniformSuffixEquationSum` / `cycleRiseBlockRotatedWordAEquationSum`
- `cycleRiseBlockC3ResidualSum_eq_tailRank_add_c3Weight_sub_two`
- `cycleRiseBlockTailRank_eq_v2_rotated_plus_delta`：
  `R_r = v2(wordA(rotation at b_r) + (2^S−5^P))`
- `cycleRiseBlockTailRankSum_eq_v2_rotated_plus_delta_sum`：求和版

`lean/closure.lean`：

- `cycleRiseBlockTailRank_add_prefixWeight_eq_val_prefixPlusOne`：
  `W(b_r) + R_r = v2(5^{b_r}·m + A(b_r) + 2^{W(b_r)})`
- `cycleRiseBlockTailRankSum_add_prefixWeightSum_eq_val_sum`：求和版
- `cycleRiseBlockAllBelowBudget_iff_tailRank_le`：
  `allBelowBudget ⟺ ∀r, R_r ≤ 2b_r+12`
- `two_pow_sub_five_pow_odd`：`2^S−5^P` 奇数
- `cycleRiseBlockTailRankSum_eq_v2_prod_delta_q_add_one`：
  `ΣR = v2(Π_r Δ·(q_r+1))`
- `cycleRiseBlockPrefixPlusOne_eq` / `prod_mul_two_pow` /
  `prod_q_add_one_mul_two_pow_weight_eq_prod_prefixPlusOne`
- `sum_modEq`
- `wordA_cyclic_mod_two_pow_prefixWeight_sum`：
  `A(rot) ≡ 5^{P-1}·Σ_i 2^{W_i}·inv^i [MOD 2^k]`，`inv = pow5Inv 1 k`
- `rotated_plus_delta_add_five_pow_mod_two_pow`：
  `(A(rot)+Δ)+5^P ≡ 5^{P-1}·Σ_i 2^{W_i}·inv^i [MOD 2^k]`
- `hfailBudgetLowerBoundAt_exists_of_tailRankSum`（鸽巢）
- `hfailBudgetLowerBound_of_crush`（crush ⇒ hfail）

逐块同余判定引理 `tailRank_ge_iff_prefixWeight_sum_congruence` 的
**否定侧**已落成正式引理：`R_r ≤ 2b_r+12` 等价于前缀权重和
`Σ_i 2^{W_i}·inv^i ≢ 5 [MOD 2^{2b_r+13}]`。

## 剩余数学：正向侧

正向侧：证明 `2^S > 5^P` 会迫使某个块的前缀权重和满足

```text
Σ_i 2^{W_i}·inv^i ≡ 5 [MOD 2^{2b_r+13}]
```

从而与上面的逐块否定相撞。精确入口是 `ord_{2^k}(5) = 2^{k-2}` 的
前缀权重 5-adic 望远镜。按以下五步写：

1. **ord 引理**（库里大概率没有，直接证）：
   `(5 ^ 2^(k-2)) % 2^k = 1`（`3 ≤ k`）。即 `inv^i` 在模 `2^k` 下
   的周期 ≤ `2^(k-2)`。用 `5^{2^m} = (1+4)^{2^m}` 或逐次平方归纳。

2. **块间旋转递推**：
   `rot_r = suf_r ++ rest_r`，`rot_{r+1} = rest_r ++ suf_r`。
   用 `wordA_append_shift` 得
   `A(rot_r) = 5^{P-L_r}·A(suf_r) + 2^{W_suf}·A(rest_r)`
   `A(rot_{r+1}) = 5^{L_r}·A(rest_r) + 2^{W_rest}·A(suf_r)`
   消去 `A(rest_r)`，代入 `A(rot_r)=q_r·Δ` 与块局部方程
   `2^{W_suf}·y_r = A(suf_r) + 5^{L_r}·q_r`。

3. **`E_r` 同余递推**：定义
   `E_r := Σ_{i=0}^{P-1} 2^{W_i^{(r)}}·inv^i`，由已证展开引理
   `A(rot_r) ≡ 5^{P-1}·E_r [MOD 2^k]`，把第 2 步递推翻译成
   `E_{r+1} ≡ 5^{L_r}·E_r·inv^{L_r} + suffix项 [MOD 2^k]`。

4. **绕一圈合并**：沿 `r=0..K-1` 递推，`E_0` 绕回自己；用 ord 周期
   归约 `inv^{ΣL}`，写成 `E_0 ≡ C + 单位·E_0 [MOD 2^k]`。把
   `2^S ≥ 5^P+1`（即 `Δ ≥ 1`）放进 `C`；尾部块
   （`2b_r+13 > S`）用 `cycleQb8Input_prefix_rank_le_period`
   的 `R_r ≤ 2P+2` 归入 `C`。单位 `≢ 1` 则定出 `E_0`；`≡ 1`
   则回到 `C ≡ 0` 的规模矛盾。

5. **落库顺序**：ord 引理 → 旋转递推 → `E_{r+1}` 同余 → 合并 →
   `cycleRiseBlockAllBelowBudgetCrush`。一次写一个，每个先编译。

## 纪律

- 不新增 `sorry`/`axiom`/伪引理占位。
- 不复活：全局比较 (6)、`realOrbitChargeBound`、`tailPerBlockCapacity`、
  PMI 前缀不等式作为唯一矛盾来源。
- 主线引理显式携带 `hcycle` 锚点：
  `m = fiveXPlusOneOrbit 7 c`、`w = cycleWord c p`。
- 不用对数/估值，只用整数精确恒等式。

## 验证命令

```text
lake env lean RiseDecompositionAssembly.lean
lake env lean closure.lean
```

目标 0 error / 0 warning。
