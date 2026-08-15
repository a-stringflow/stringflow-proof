# 交接：hterm

日期：2026-08-16

## 当前目标

证明 `cycleQb8InputRealPredecessorIdentity`，即每个循环 rise 块的真实前驱恒等式：

```text
5^rt.k * rt.s + delta * 5^(L-1) - 1 = wordOrbit u' q
```

等价于：

```text
wordOrbit u' q = rt.r + delta * 5^(L-1)
```

## 状态

- hE5 已闭合：由 hterm 前提推出；禁止重写，禁止用 `by_contra` 证明。
- `cycleRiseBlockHterm_of_real_predecessor` 已编译：前驱恒等式 → `IsLocalResetTerminal`。
- 剩余唯一真实轨道缺口是上述前驱恒等式本身。
- hterm 是开放定理，不是 blocked，不要求外部输入。

## 已知装配

- `cycleQb8Input_cyclic_prefix_occurrence_with_incoming`
  → `fullOrbitIter (n-1) = wordOrbit u' q`
- `cycleQb8Input_boundary_terminal_eq`
  → `rt.r = 2^(c-1) * q`
- `word_orbit_identity` / `hid`
  → `2^W * wordOrbit u' q = 5^(L-1) * q + wordA u'`
- `cycleRiseBlockHterm_of_real_predecessor`
  → 前驱恒等式直接构造 hterm

## 禁止

- 禁止把 hE5 当作开放对象重写。
- 禁止要求用户提供 c 与 wordA u' 的外部恒等式。
- 禁止把“库里没有现成引理”当作不可证；任务就是新增该定理证明。
- 禁止用 Python/数值扫描找伪反例。
- 禁止新增等价归约代替正面构造。

## 验证

- 修改后先单文件：`lake env lean RiseDecompositionAssembly.lean`
- 全量 `lake build` 只在相关文件 sorry 清零后运行。

## 并行边界

hfail 在 `amiya.lean` 平行推进，不在本文件处理；
全局比较 (6) 已判死，禁止复活。
