# 交接：hterm 模 25 判别器落库

日期：2026-08-16 深夜

## 当前状态

- `RiseDecompositionAssembly.lean` 已有模 5 判别器与相关结构
  （相对 HEAD 约 310 行新增，单文件编译通过）；
- `scratch_hterm.lean`（584 行）已完整编译通过，包含：
  - 纯算术引理：`two_pow_mod5_of_mod4`、`two_pow_mod5_eq_iff_mod4_eq`、
    `mul_pow_mod5_eq_one_iff`、`add_mod_eq_add_mod_iff`、
    `five_mod25_eq_mul_mod25_iff`、`mod25_cong_five_iff_mod5_one`、
    `mod25_eq_iff_mul_unit`、`modEq_eq_iff_mul_unit`、`pow2Inv5`、
    `pow2Inv5_spec`、`pow2Inv5_pow_spec`、`mul_five_lift_mod`、
    `mod25_cong_iff_mod5_one`、`take_two_eq`；
  - 模 25 判别器：`cyclic_real_predecessor_congruence_mod25_iff_prev_residue`；
  - **一般模 `5^k` 判别器**：
    `cyclic_real_predecessor_congruence_mod_pow_of_prefix_orbit_eq`，
    是完整 5-adic 望远镜的钥匙，不只是模 25；
- `scratch_test.lean` 是另一临时探针（未迁移）；
- 主对话在迁移/整理阶段反复删改，正文件只落库约 310 行；
  若原会话状态不佳，新会话按本文档一次性干净收口。

## 目标

把 scratch 中已验证的判别器一次落库，让 hterm 侧进入逐层正式推进：

```text
模 5 判别器（已落库）
→ 模 25 判别器（本交接）
→ 一般模 5^k 判别器（望远镜钥匙）
→ selected 完整同余 cyclic_real_predecessor_congruence_selected
→ HtermValuation（trinity 核心估值第一块）
```

## 步骤

1. 把 `scratch_hterm.lean` 中已编译通过的引理一次性迁入
   `RiseDecompositionAssembly.lean`（命名空间同为
   `StringFlow.CycleBridge`；先检查是否与已有符号重名）；
2. 单文件 `lake env lean RiseDecompositionAssembly.lean` 编译，
   0 warning / 0 error / 0 sorry，消除 linter 警告；
3. 编译通过后删除 `scratch_hterm.lean`、`scratch_test.lean`；
4. 把 `HtermValuation`（trinity.lean）与落库判别器对应：确认
   selected 同余可由模 5^k 判别器逐层推出；
5. 下一层目标：用 `cyclic_real_predecessor_congruence_mod_pow_of_prefix_orbit_eq`
   把 selected 完整同余从 def 变成定理。

## 禁止

- 不标 blocked；不要求外部输入；
- 不新增 ⇔ 等价归约代替正面构造；
- 不换角度；不复活已判死路线（C3-tail、全局比较 (6)）；
- 禁止反复删改后再落库：一次性迁移，编译通过即固定；
- 临时探针不得留在工作区（迁移完成后必须删除）。

## 验证

- 开发只跑 `lake env lean <单文件>.lean`；
- 全量 `lake build` 只在相关文件 sorry 清零后运行；
- 最终标准：0 sorry、0 error、0 axiom、0 warning。

## Goal Prompt（给下一个会话）

```text
目标：把 scratch_hterm.lean 的模 25 / 模 5^k 判别器一次落库，
然后沿 5-adic 望远镜把 selected 完整同余闭合。

先读：docs/交接-hterm-模25落库.md、docs/交接-hterm.md、
docs/交接-trinity.md、lean/scratch_hterm.lean、
lean/RiseDecompositionAssembly.lean（模 5 判别器与 selected 同余）、
lean/trinity.lean（HtermValuation）。

步骤：
1. 逐条迁移 scratch 中的纯算术引理与两个判别器到
   RiseDecompositionAssembly.lean，保持命名空间 StringFlow.CycleBridge；
2. 单文件编译通过、0 warning/error/sorry；
3. 删除 scratch_hterm.lean、scratch_test.lean；
4. 用 cyclic_real_predecessor_congruence_mod_pow_of_prefix_orbit_eq
   逐层推 selected 完整同余：每层给出精确中间式，
   从模 25 开始向上归纳到模 5^(L-1)；
5. 同余成立后，经 realPredecessorDelta 与奇偶/尺寸收窄
   （delta ∈ {1,3} 或 =1），再经
   cyclic_real_predecessor_identity_to_hterm 闭合 HtermValuation。

纪律：不标 blocked；不找外部输入；一次性落库不反复删改；
不新增 ⇔；不换角度；卡住时给出精确中间式；单文件验证。
```
