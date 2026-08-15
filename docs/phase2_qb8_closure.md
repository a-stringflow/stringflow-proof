# 阶段二 QB-8 闭包状态（2026-08-11）

本文记录 TD-0 阶段二（`S>=26`）在 Lean 侧的闭包链、剩余解析输入
与证明路径。对应 `ph_qb_gc_chain.md` 52.21.2bis 与 53.1。

## 1. 最终接口

阶段二最终入口为抽象框 A + QB-8 循环：

```lean
td0_of_qb8CycleAbstract : Qb8CycleAbstract b Q L U m M0 w ns ts -> False
```

其中 `Qb8CycleAbstract` 是 `Qb8OrbitB0Input` 的语义化别名。接口链为：

1. `Qb8OrbitB0Input`（词层，`hT` + `hlast`）
2. `Qb8OrbitU1Input`（解析层，`hT` + `hU1`）
3. `Qb8OrbitStructuralInput`（词层，自动推导 `hP205`、`hcyc`、`hD`、`hT`）
4. `Qb8OrbitStructuralU1Input`（解析层，自动推导 `hP205`、`hcyc`、`hD`、`hT`）
5. `Qb8OrbitCycleInput`（自动推导 `hcyc`、`hD`）
6. `Qb8OrbitGC7Input`（自动推导 `hT`）
7. `Qb8OrbitInput` / `qb8_orbit_of_firstWord`
8. `Qb8Orbit` -> `Qb8Cycle2` -> `False`

输入层（词层、解析层、结构层）等价，均编译并通过 `Axioms` 审计。

## 2. 自动推导字段

以下字段不再需要作为输入：

- `hSfirst`、`hwS`：由真实词自动推导
- `hfeas`、`hU`：由 `hT` 与家族 `U` 界推导
- `h201`：由 `h201full_of_real_cycle` 推导
- `hcyc`：由上升段方程与 C3 链闭式推导
- `hD`：由循环方程正分子推导
- `hT`：在 `Qb8OrbitGC7Input` 层由 GC-7 窗口推导
- `hP205`：在 `Qb8OrbitStructuralInput` 层由链上界与循环方程推导
  （`P_lt_205_of_pow_six`）

## 3. 剩余解析输入

阶段二 Lean 侧（结构层）只保留一个定义层输入：

| 输入 | 文档来源 | 类型 |
|---|---|---|
| `hU1` | 52.12 家族 `U` 界（解析层） | 定义层 |
| `hlast` | 52.12 族末步（词层） | 定义层 |

`hU1` 与 `hlast` 二选一，分别对应 `Qb8OrbitU1Input` 与
`Qb8OrbitB0Input`；`hT`（52.7 `uReq` 恒等式）在结构层完全自动。

## 4. B0 范围的形式化

`hP205`（即 `P<205`）已有三条路径：

1. `P_lt_205_of_tCeil_eq`：由 `hT` 直接推出，因为 `tCeil` 在表外为 0。
2. `P_lt_205_of_b0`：独立实数证明，输入 `uReq` 恒等式、`S<=64`、
   `5^P<2^T` 与 `delta<1`，使用 `log2_five_lt_nineteen_eighths`
   （`log2 5 < 19/8`，由 `5^8<2^19` 证明）。
3. `P_lt_205_of_pow_six`：结构证明，由 `wordA < 5^L`、
   `chainA < 2*8^Q`、循环方程与 `S<=64` 推出，不依赖 `hT`。

## 5. 状态与下一步

- 阶段二 Lean 侧已收口：结构层输入只剩 52.12 的 `hU1`（解析层）
  或 `hlast`（词层），`hT`、`hP205`、`hcyc`、`hD` 全部自动推导。
- 52.7 的完整独立证明（从全局最小性与循环方程推出
  `T-1 < P log2 5 < T`）属于上游定义层；`P<205` 分支已由
  `tCeil_eq_of_gc7_and_cycle` 覆盖，`P>=205` 分支需要 B0 或
  2-adic 最小性。
- 52.12 的族分类 `hU1`/`hlast` 是定义输入，不作为 Lean 证明目标。

## 6. 编译验证

- `lake build Td0Final`：通过
- `lake build Axioms`：通过，全部新入口纳入审计
- 无新增 `sorry` / 自定义公理
