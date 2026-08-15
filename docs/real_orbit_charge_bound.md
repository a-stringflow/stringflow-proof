# realOrbitChargeBound 草稿

这是 `failureWindowExistence` 的块内解析缺口。只处理真实轨道块，
不在这里使用 PMI 坏前缀。

## 1. 对象

固定一个闭合 `CycleQb8Input`，其词为 `w`，起点为 `m`。
由真实 C3-to-rise 分解得到：

```text
b = 当前 rise run 的全局起点；
L = 当前 rise run 的长度；
j = b + L；
t_j = t = w.getI (j - 1) ∈ {1,2}；
rj = wordOrbit (w.take j) m。
```

`rj` 是重置步后的真实块首，与 `FailureWindow` 的

```text
ResetHeadEq s j k0 t δ (wordOrbit (w.take j) m)
```

使用同一个全局深度 `j`。

## 2. 块后缀

从块首 `rj` 开始，取词段

```text
u = blockWordFrom j
```

直到下一个 C3 步或周期末尾。这里 `u` 的每一项都属于
`{1,2}`，且该段是真实轨道段：

```text
riseRun rj u = wordOrbit (w.take E) m，
E = j + u.length。
```

精确定义为：

```text
R(j) = risePrefixLength (w.drop j)
blockWordFrom w j = (w.drop j).take (R(j))
blockEndFrom w j = j + R(j)
```

对应 Lean：

```lean
def blockWordFrom (w : List Nat) (j : Nat) : List Nat :=
  (w.drop j).take (risePrefixLength (w.drop j))
```

由 `risePrefixLength` 的性质：

1. `blockWordFrom w j` 的所有项都是 `1` 或 `2`；
2. 若 `blockEndFrom w j < w.length`，则
   `3 ≤ w.getI (blockEndFrom w j)`；
3. 若 `blockEndFrom w j = w.length`，则该块到周期末尾结束。

所以这是真实 `δ=0` 块的后缀词。

设：

```text
u_j = twoValuation (rj + 1)，
F   = riseChargeSum rj u。
```

其中 `riseChargeSum` 按现有定义，只累计每个 `t=1` 步的正 rank
增量；`t=2` 步不充值。

## 3. 目标

证明：

```text
u_j + F ≤ 2 (j - t_j) + 12。
```

这就是 `block_capacity_of_charge_bound` 目前作为输入接收的
`hcharge`。

## 4. 证明路线

不按单个状态逐步递推，按极大 `t=1` 游程归纳。

1. `t=2` 步：

```text
riseCharge(r,2) = 0，
twoValuation(riseStep(r,2)+1) = twoValuation(r+1)-2。
```

2. `t=1` 游程：

```text
F 只在游程末的 rank 上升处增加，
增加量是 max(v2(next+1)-v2(current+1),0)。
```

3. 对整个真实轨道后缀使用

```text
word_endpoint_rank_bound u rj
```

得到尾端 rank 上界：

```text
twoValuation (riseRun rj u + 1) ≤ 2 u.length + 8。
```

4. 由 rank 望远镜关系：

```text
twoValuation (riseRun rj u + 1)
  = u_j + F - 2 H2，
H2 = riseCountTwo u。
```

所以：

```text
F ≤ 2 u.length + 8 - u_j + 2 H2。
```

5. 用真实块首深度关系：

```text
u.length ≤ j - t_j，
H2 ≤ u.length。
```

并利用 `t=1` 游程结构与 `u_j` 的复位性质，消去 `2 H2` 项，
得到：

```text
u_j + F ≤ 2 (j - t_j) + 12。
```

## 5. 待补的精确子引理

最终 Lean 目标写成：

```lean
theorem realOrbitChargeBound
    (h : CycleQb8Input m S P w rise c3)
    (b L t δ : Nat)
    (rt : AngelinaGilbertaRealTerminal)
    (d : LocalHidentBlock (b + L) Wp Wj q Aj
           (wordOrbit (w.take (b + L)) m) t δ rt)
    :
    twoValuation (wordOrbit (w.take (b + L)) m + 1)
      + riseChargeSum (wordOrbit (w.take (b + L)) m)
          (blockWordFrom w (b + L))
      ≤ 2 * ((b + L) - t) + 12
```

这里不再需要额外谓词 `hu`：`blockWordFrom` 本身已经固定了从块首
到下一 C3 的真实后缀。
