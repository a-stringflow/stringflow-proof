# SURV-EX 条件版审计：53.4-LB 是否是假墙

日期：2026-08-11

## 1. Lean 形式化现状

审计前，SURV-EX 没有独立 Lean 形式化。`FinalStatement.lean` 只定义了

- `SurvExTd0 := ¬ OrbitCycle 7`
- `five_x_plus_one_diverges_at_7_of_surv_ex_td0 : SurvExTd0 → IsUnboundedOrbit 7`

这只把“7 的加速轨道无正周期”接到“无界”，没有把 S-X1..S-X4、SURV-RAY、
Simons S1 或 L-B′ 写进 Lean。

本轮新增 `lean/SurvExAudit.lean`，包含：

- `RisingWord`：`t_j ∈ {1,2}`、末项为 `1`、`2U ≤ L+1`
- `MinimalStart`：复用 `Word.wordRepresentative` 作为最小起点残差 `r(w)`
- `LBPrimeWeak`、`LBPrimeA`、`LBPrimeB`、`LBPrimeAll`
- `LBPrimeC`（前插 `k≥1` 分支）、`LBPrimeU0/U1/U2`、`LBPrimeReduction`
- `lb_prime_c`：L-B′c 分支已在 Lean 中闭合（无 `sorry`）
- `SurvExConditions`：把 53.4-LB 的每个前置条件作为显式字段
- `SurvEx53_4LB := SurvExConditions → SurvExTd0`
- 装配桥 `divergence_of_surv_ex_53_4_lb`

该文件没有 `sorry`。`lb_prime_c` 是第一个真正闭合的 L-B′ 分支；其余
`LBPrimeU0/U1/U2` 仍是精确陈述，`LBPrimeReduction` 是文档分解形式，
尚未在 Lean 中证明。

`AxiomAudit.lean` 已加入最终桥的 `#check` 与 `#print axioms`：
`five_x_plus_one_diverges_at_7_of_surv_ex_td0` 只依赖
`propext`、`Classical.choice`、`Quot.sound`，不依赖 `sorryAx`。

## 2. 53.4-LB 的条件分类

| 条件 | 文档状态 | Lean 状态 | 分类 |
|---|---|---|---|
| 53.1--53.3 主链 | 文档称已关闭 | TD0 有 `td0_of_qb8_cycle` 等，但尚未形成 `OrbitCycle 7` 的完整无周期链 | 部分形式化，仍开放 |
| 53.6 SURV-RAY 整族接口 | 证书 `surv_ray_certificate.txt` | 无 Lean 定理 | 未形式化 |
| S-X1 b 窗口闭式 | 文档称已闭合 | 无 Lean 定理 | 数学论断已记录，形式化开放 |
| S-X3.3a/b | 文档称已闭合 | 无 Lean 定理 | 数学论断已记录，形式化开放 |
| 25 条区间证书 | Python 证书 `RESULT: PASS` | 无 Lean 定理 | 外部证书，不是 Lean 证明 |
| S-X3.3c | 211 条射线未闭合 | 无 Lean 定理 | 真开放 |
| S-X4 完备性 | 未完成；Q>100 不为空 | 无 Lean 定理 | 不需要（整族解析绕过，无需证空） |
| Simons S1 | 外部定理 | 无 Lean 定理 | 外部依赖 |
| L-B′a/b | 开放；文档归约到 U=2 | 无 Lean 定理 | 真开放 |
| L-B′c | 文档称已证 | `lb_prime_c` 已闭合 | Lean 已证 |

## 3. 假墙判定

**结论：条件版 53.4-LB 不是逻辑上的假墙，但不是闭合。**

1. 53.4-LB 是显式蕴含 `Assumptions → ¬ OrbitCycle 7`，不是把结论直接
   写成假设；把它形式化为 `SurvEx53_4LB` 是诚实的。
2. 但“正式接受条件版”只意味着把开放条件放进前提，墙没有被拆掉。
   当前 `SurvExTd0` 仍无证明，最终定理 `five_x_plus_one_diverges_at_7`
   仍使用 `sorry`。
3. S-X4 是过强的有限枚举完备性要求：它要求证明 `Q>100` 不再出现新
   射线窗口。2026-08-12 修正依赖判定：L-B′/U=2 闭合给出
   `S0(m)≤5log2(5m)`，对全部射线成立，S-X3.3c 对整族射线解析关闭；
   因此 S-X4 被整族绕过，不需要证明为空，也不再是 53.4-LB 的必要
   依赖。它只对“有限证书路线”有意义，在该路线之外无需保留。
4. L-B1 强形式已被 `m=7,9` 否证；L-B′ 弱形式是独立开放语句，不是已证
   定理。文档中“不再阻塞条件版”应读作“阻塞被移进假设”，不能读作
   “障碍消失”。
5. “只用已可证的 `S_0(m)` 上界替代 L-B′”目前是候选充分条件，不是归约；
   没有 Lean 证明，也没有解析证明。

## 4. 下一步

要删除最终定理的 `sorry`，需要先闭合 `SurvExTd0`。当前最具体的开放入口：

- 完成 L-B′a/b 的 U=2 解析证明并形式化；
- S-X4 不再需要：整族解析路线（L-B′/U=2 → `S0(m)≤5log2(5m)` →
  S-X3.3c 对全部射线）闭合后，直接从 53.4-LB 依赖删除；无需证明
  `Q>100` 窗口为空。
- 把 TD0/QB 排除桥接到 `OrbitCycle 7` 的完整无周期链；
- 或走 D0 直接路线作为并行备份。

在此之前，任何“SURV-EX 已闭合”或“条件版已收口”的表述都是不成立的。
