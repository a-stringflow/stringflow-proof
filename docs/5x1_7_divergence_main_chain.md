# 5x+1 在 7 发散：主证明链（简短版）

日期：2026-08-08

> 2026-08-12 修正：最终下游由 `D0 + SURV-EX + TD0 → 7 发散`
> 改为循环桥版本：
> `D0 → decisiveWindowValuationBoundCorrected → CycleBridge
> → ¬ OrbitCycle 7 → IsUnboundedOrbit 7`。
> SURV-EX 与 TD0 不再出现在最终证明链中。
>
> 2026-08-13 修正：旧 `decisiveWindowValuationBound` 被反例否定，
> 最终链只使用携带真实可达性输入的
> `decisiveWindowValuationBoundCorrected`。

> 2026-08-11 状态更新：S6/局部引理链已在 `lean/S6Audit.lean`
> 中零 `sorry` 闭合（`pure_t2_m1_no_odd_hit`、`local_lemma_final`）；
> 阶段 1 覆盖扩展仍开放（`Stage1PureT2M1Exclusion`）；
> X=1 与下游 D0 链继续开放。本页其余结构不变。

## 1. 结构总览

主证明链由两部分组成：

1. 主证明链（当前）：

   `局部引理 → B → L → C → G_i ≥ 1 → c_k ≥ 4(4/5)^k
   → m_d ≥ 2^{d+2} → D0 → decisiveWindowValuationBoundCorrected
   → CycleBridge → ¬ OrbitCycle 7 → IsUnboundedOrbit 7`

2. 旧 `PMI-B → PH + QB → GC(TD-0/TD-1) → 框 A → SURV-RAY/EX
   → L-B′ / S-X4` 段不再进入当前最终链；循环桥负责“窗口定理
   ⇒ 无正循环 ⇒ 7 发散”的下游接线。

   这两条链不是完全独立的并行线：`E0 引理 9.1`（深度 0 边界点
   `R` 的 g-链长度 `d ≤ S_R`）是两侧的公共前置。D0 链上的命题 B、
   35.5、39.1、39.3 均条件于该引理；L-B′ 侧的 E0 分类归约也条件于
   它。`m_d ≥ 2^{d+2}` 是闭合 E0 9.1 反例窗口的一条充分路线，不能
   因此把 D0 整体说成 E0 的上游。

## 2. 归约来源方向

目标 `D0` 向下分解为最小待证语句：

```text
D0
→ m_d ≥ 2^{d+2}
→ c_k ≥ 4(4/5)^k，等价于 G_i ≥ 1
→ C
→ L
→ B
→ 局部引理
```

因此局部引理是这条最新归约链的末端，不是证明起点。

## 3. 闭合证明方向

证明时反着走：

```text
局部引理
→ B → L → C → G_i ≥ 1
→ c_k ≥ 4(4/5)^k → m_d ≥ 2^{d+2}
→ D0 → decisiveWindowValuationBoundCorrected
→ CycleBridge → ¬ OrbitCycle 7 → IsUnboundedOrbit 7
```

## 4. 关键语句

### PMI-B（基础，位于 PH 之前）

精确前缀余量恒等式：

$$
\sum_j 2^{-M_j}=5m(2^\delta-1)
$$

以及其前缀余量推论。`PMI-B` 是 `PH` 的词贡献分解和 `QB` 的定量
前缀余量预算基础。

### 局部引理（当前唯一待证入口）

对 `u_i=1` 的状态，令
$$
m=\frac{r_i+1}{2},\qquad
v=v_2(5r_i+3)-1=v_2(5m-1).
$$

局部引理需要证明：
$$
v\le 2(j-t_j)+12-2h_i.
$$

等价形式为
$$
X_i=v_2(5r_i+3),\qquad
F_i=X_i+2D_i-2i,
$$
且
$$
\text{局部引理}\iff F_i\le13.
$$

其中 `j-t_j` 是“深度减步长”，不是 `W_{j-1}`。

它拆成两条：

1. 容量条件：`h_i ≤ j-t_j+5`，是局部引理的**必要条件**，不是充分条件；
2. 估值条件：`v ≤ 2(j-t_j)+12-2h_i`，是局部引理**本体**。

### B

$$
u_0+F\le2(j-t_j)+12,
$$

等价于局部形式：
$$
2h_i+u_i\le2(j-t_j)+12.
$$

### L

对 `r_i ≡ 3 mod 4`：
$$
T_i\ge1-\lambda,\qquad
\lambda=\log_2(5/4).
$$

### C

$$
h_i\le j-t_j+\lambda i-2.
$$

C 是 `G_i ≥ 1` 的充分条件。

### G_i 与 c_k

$$
G_i=\frac{c_i}{4(4/5)^i}\ge1
\iff
c_i\ge4(4/5)^i.
$$

### m_d

$$
m_d\ge2^{d+2}.
$$

这一步同时闭合 e0 引理 9.1 的 `m_d < 2^{d+2}` 反例窗口：
这是闭合引理 9.1 的一条充分路线，不代表 D0 是 E0 的上游。
反向依赖仍存在：D0 链的命题 B、35.5、39.1、39.3 都条件于
e0 引理 9.1（`d ≤ S_R`），E0 9.1 未闭合前这些语句不能作已证。

### D0

对终端 k=0 链 `r_0 → ... → r_n`：
$$
D_0(n,r_n)=r_n^5+4^n-5^n(r_n+1)\ge0.
$$

D0 闭合后，还需把 `decisiveWindowValuationBoundCorrected` 交给循环桥；
循环桥闭合后才得到 `¬ OrbitCycle 7` 与 `IsUnboundedOrbit 7`。
旧的无约束 `decisiveWindowValuationBound` 已被
`decisiveWindowValuationBound_contradiction` 否定；单 D0 不足以收口。

## 5. 当前状态

`局部引理` 尚未从递推严格证明。注意“其后的 B、L、C、G_i、c_k、
m_d、D0 与 7 发散均有现成归约衔接”这句**不准确**：按
`main_chain_audit.md` 的逐链接审计，L、C、c_k 尾部、
`m_d>=2^{d+2}`、D0 仍是逐链接开放语句——它们属于同一条归约链
`D0 → m_d → c_k/G_i → C → L → B → 局部引理`，不是相互独立的
平行任务；纯 `t=2` 块的 S6 也需单独证明；不能把主链视为只剩
局部引理。

注意：D0 链与 53.4-LB 的 L-B′ 路线是二选一的收口路线，不是
相互前置；旧 SURV-EX/TD0 侧不再进入最终链，E0 9.1 与 L-B′ 侧的
历史关系保留。

当前唯一开放估值语句为
$$
X_i+2D_i\le2i+13.
$$

## 5.1 记号消歧：三个 C

当前工作区中字母 `C` 至少指三种不同对象：

1. **容量引理 Cap**（主链中的 C）：
   $$
   h_i\le j-t_j+\lambda i-2.
   $$
   这是条件，不是函数。

2. **rank 势能 Rk_i**（e0 中的 C_i）：
   $$
   Rk_i=V_i-i-\log_2 q_i.
   $$
   定义见 `e0_margin_automaton.md`。

3. **B-L 阈值函数 C_BL(S)**（B-L 中的 C(S)）：
   $$
   C_{BL}(S)=\frac{8\cdot2^S}{5^{S/3}}.
   $$
   定义见 `b_l_reduction.md`。

后续引用时建议分别使用 `Cap`、`Rk_i`、`C_BL(S)`，避免三个
`C` 撞名。

## 5.2 猜想记录：容量常数 5 与 5x+1 底数同源

状态：**未证猜想**，仅记录，不用于证明。

陈述：容量条件
$$
h_i\le j-t_j+5
$$
中的常数 `5` 可能不是单纯由局部引理的 `+12` 与 `v≥1` 导出的
算术余量，而可能直接来自 `5x+1` 映射的底数 `5`，即这个 `5`
是 5-adic/源类结构的来源。

现状依据：
- 算术路径只说明整数上界必须取 `+5`；
- 但没有解释为什么局部引理的上界余量恰好落到 `5`；
- 若猜想成立，`5` 应能从模 5 源类、`A_i` 递推或 5-adic 残差
  结构直接推出，而不依赖 `+12` 这个常数。

检验方向：
- 把局部引理推导中出现的 `+12` 拆成与 `5` 有关的结构量；
- 检查紧路径 `i=37` 的 `j-t_j+5` 是否对应某种模 5 临界；
- 尝试从 `r_i=(5^i q+A_i)/2^{W_i}` 的 `5^i` 因子直接导出常数
  `5`。

迁移意图（未证）：如果该猜想成立，则希望把容量条件参数化为
一般的 `a x+1` 形式，例如令
$$
h_i\le j-t_j+K(a),
$$
其中 `K(5)=5`，再把 5-adic/源类结构换成 `a`-adic 结构，尝试
用于冰雹猜想（`3x+1`，即 `a=3`）。此迁移目前只是研究意图，
不保证直接适用：`a=3` 时的源类表、常数、紧路径和 2-adic
估值结构都需要重新推导。

注意：此猜想尚未用于证明；当前仍按普通容量条件推进。

## 6. 方法备忘

- 区分“归约来源方向”与“闭合证明方向”；
- `L-B′`、`S-X4`、`SURV-RAY/EX` 是旧前面协同定理，已由循环桥
  取代，不再进入当前最终链；
- `L-B′` 与 D0 链共享 `E0 引理 9.1`（`d ≤ S_R`）前置：L-B′ 不依赖
  局部引理，但不能把两条链视为完全并行；
- `PMI-B` 是 `PH` 之前的基础，不能从主链中省略；
- 局部引理是 D0 向下分解后的最小待证语句，不是独立的新路线。
