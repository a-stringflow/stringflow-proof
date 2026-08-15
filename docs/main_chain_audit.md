# 主证明链逐链接审计（2026-08-08）

状态：**主链存在多个未闭合链接**。本文按目标第 6 项的闭合方向
`局部引理 -> B -> L -> C -> G_i>=1 -> c_k>=4(4/5)^k
-> m_d>=2^{d+2} -> D0 + SURV-EX + TD0 -> 7 发散`
逐条核对工作区现有文档，标明每一条是“已证”、“已归约但本体开放”，
还是“仅有证书”。`5x1_7_divergence_main_chain.md` 中“其后各步均有
现成归约衔接”的表述不准确，应以本审计为准。

## 1. 逐链接状态

1. **局部引理（u=1 块）**：开放。
   - 已证：局部引理（整块）等价于终端 `H_e>=1`，即 S6
     `h_e<=j-t_j+6`，见 `local_lemma_terminal_s6_equivalence.md`
     定理 2.1（充要）。
   - 已证：K4 与宏步不等式严格等价，且
     `L1+L2+K4B` 合取 ⇒ 宏步不等式，见同文档第 3 节。
   - 开放：K4 本体、`H_e>=1` 本身。
2. **B（`2h_i+u_i<=2(j-t_j)+12`）**：由局部引理推出的代数步骤已写，
   见 `capacity_lemma_reduction.md` 第 9 节；它不是独立缺口。
3. **L（`r_i≡3 mod 4 => T_i>=1-lambda`）**：开放。
   - 已证：若 S6 对所有块成立，则 `D_i-i<=6` 对所有块内状态成立，
     且对 `i>=27` 有 `T_i>=lambda*i-8>=1-lambda`；`17<=i<=26`
     只剩有限基。见 `capacity_lemma_reduction.md` 第 7 节。
   - 注意：纯 `t=2` 块没有 `u=1` 状态，局部引理真空，S6 仍需单独
     证明；该情形对应 `u_j` 偶数的块首容量，当前文档未闭合。
4. **C（`h_i<=j-t_j+lambda*i-2`）**：开放，但 L ⇒ C 的势能递推已写，
   见 `capacity_lemma_reduction.md` 第 4 节（若 L 成立则 C 闭合）。
5. **G_i>=1**：开放，但 C ⇒ G_i>=1 已写，见
   `capacity_lemma_reduction.md` 第 2 节（充分）。
6. **c_k>=4(4/5)^k**：与 G_i>=1 严格等价，见
   `5x1_7_divergence_main_chain.md` 第 4 节。
   更一般的 c_k 正下界尾部引理仍未闭合，见
   `e0_margin_automaton.md` 第 930 行附近。
7. **m_d>=2^{d+2}**：开放。`e0_margin_automaton.md` 第 891 行
   明确“对 d>=17 解析证明 m_d>=2^{d+2}”仍是剩余开放命题；
   `m_{d+1}>=2m_d` 的模 4 缺口归约在第 893 行标记未闭合。
8. **D0**：开放。`d0_chain_bound_progress.md` 第 240 行
   “当前 ★ 本身尚未证毕”，第 1559--1565 行给出最终缺口：
   候选 `c` 的首个 C3 词轨道必须连续 n 步保持 W 成员。
9. **7 发散**：依赖 D0 链与 SURV-EX/TD0 侧；D0 未闭合前不能视为已完成。

## 2. 已证链接汇总

- 局部引理（u=1 块）⇔ 终端 `H_e>=1`（充要，本轮已证）；
- 宏步不等式 ⇔ K4（充要）；
- `L1+L2+K4B` 合取 ⇒ 宏步不等式（充分）；
- PH-1 词贡献分解的整式形式已在 `../lean/PhOne.lean` 编译：
  `prefixWeight_segment`、`ph1_word_decomposition` 与
  `localLambda_eq_of_wordWeights_agree`，公理仅
  `propext`、`Quot.sound`；
- PH-2 首游程局部下界的整式形式已在 `../lean/PhTwo.lean` 编译：
  `localLambda_firstRun_eq`、`ph2_lower_bound` 与
  `ph2_lower_bound_of_firstRunPrefix`，公理仅
  `propext`、`Quot.sound`；
- QB-7/QB-8 尖峰结构已在 `../lean/Qb.lean` 编译：
  `qb7_core`、`qb7_no_internal_data`、`c3_step_lt`、
  `rise_step_gt`、`c3_chain_strictlyDecreasing`、
  `startsFrom_consecutive_of_allOne`、`qb8_structure`；
  `Rat` 层用 `Classical.choice`，结构层仅 `propext`、`Quot.sound`；
- GC-4 的 C3 链闭式与残差已在 `../lean/Gc.lean` 编译：
  `c3_chain_closed_form`、`c3_chain_residual`、
  `c3_chain_residual_inverse`、`c3_residual_unique_small`；
  闭式、残差与唯一性仅用 `propext`、`Quot.sound`，逆元残差版本经
  Hensel 逆元工具引入 `Classical.choice`；
- GC-3 模 3 闭包已在 `../lean/Gc.lean` 编译：
  `two_pow_mod3`、`c3_mod3_of_even`、`c3_mod3_of_odd`；
- GC-42 C3 起点模 16 二分已在 `../lean/Gc.lean` 编译：
  `gc42_mod16_of_weight_three`、`gc42_mod16_of_weight_ge_four`；
- GC-41 `b=0` 分支关闭已在 `../lean/Gc.lean` 编译：
  `gc41_three_mul_residue`、`gc41_q8_candidate`、
  `gc41_q9_no_odd`、`gc41_q_ge10_no` 与
  `gc41_b_zero_no_solution`；闭合假设
  `2^3 * N_1 = 5 * N_{Q+1} + 1` 作为循环闭合步显式传入；
- GC-43 C3 链精确系数线性上界已在 `../lean/Gc.lean` 编译：
  `gc43_linear_bound` 以清分母形式给出
  `(2^(T+S)-5^(L+Q))m <= 5^Q A_max + 2^S A_chain`；
- GC-7 的上升段几何和子引理已在 `../lean/Gc.lean` 编译：
  `four_pow_le_five_pow`、`geomRise_invariant` 与
  `geomRise_bound`（`geomRise L c <= 4*5^(L+c)`），并由
  `risePart_bound` 给出上升段贡献 `risePart rise c3 <= 4*5^P`；
  另编译 C3 段几何尾和 `geomTail_invariant`/`geomTail_bound`
  （`24*geomTail(Q+1) <= 5*8^(Q+1)`）；
  完整 GC-7 的清分母形式已闭合：`c3PartFrom_le`、
  `c3PartFrom_cleared_bound`、`gc7_pmi_cleared_bound` 与
  `gc7_m_cleared_bound` 均已编译，后者给出
  `3*m*(2^T-5^P) <= 3*5^P + 2^T`；
  该整数形式现已在 `../lean/Td0Real.lean` 中重读为第 13.1 节的
  实数 m 窄窗（`gc7_real_window_ratio`、
  `gc7_real_window_delta`），可继续 GC-13。
- GC-15 清分母上界已在 `../lean/Gc15.lean` 编译：
  `gc15_rise_all_one_bound`（`U=0`）与 `gc15_risePart_bound`
  （`3*5^U*risePart <= 15*5^(P+U)-10*5^P*4^U`）。
- GC-13 清分母核心已在 `../lean/Gc13.lean` 编译：
  `gc13_allOK_check`、`gc13_t1_bound`、`gc13_t2_bound`；
  `gc13_u0_31/59/205/351/497/643` 与
  `gc13_long_rise_contradicts` 已把 `U=0` 分支表接入；
  `gc7_window_for_gc13` 已把 GC-7 m 窗接成 GC-13 的清分母输入；
  TD-1 的 B1 刚化与 617 以下尖盆地拆分已由 `../lean/Td1.lean`
  编译（`b1_201`、`basin_617_sharp`、`phase2_m_ge_201`）；
  52.15--52.16 的清分母窗口等价已由 `../lean/Td1Window.lean` 编译；
  52.21.2bis 的两条 `mt>=8/3` 精确 Rat 检查已由
  `../lean/Td1Phase2.lean` 编译（`phase2_delta_check`）；
  G5' 的精确 Rat 形式（`t(P)>=t(31)`、`t(P)>=t(59)`）与
  `phase2_upper_bound_check` 也已编译；
  派生的 Rat 上界 `phase2_mt_ge_of_m_ge_617`/
  `phase2_mt_ge_of_m_ge_201` 也已编译（分别覆盖 `m>=617` 与
  `m>=201,P<59`），B2 的 Rat 形式 `phase2_mt_ge_of_b2` 也已编译
  （以 B1 桥 `m<617 => m=201,P<59` 为输入），B1 桥定理
  `phase2_b1_P_lt_59`/`phase2_b1_bridge`/`phase2_mt_ge_of_b2_of_201`
  也已编译（`L=20,b=2,U_req=6` 时推出 `Q=28,P=48`）；
  阶段二 `G_up` 的抽象 Rat 上界已由新模块 `../lean/Td0Phase2.lean`
  编译（`gup_lt_eight_thirds`、`mt_gt_gup_of_ge`），精确 A/B
  `Rmax<U iff mt>G_up` 等价（`aUpper_iff`/`bUpper_iff`）与
  `upperAt_of_mt_ge` 也已编译（由 `m*t(P)>=8/3` 得到
  `upperAt = true`）；修正后的精确上分支
  `upperBranch`（含 `1/(3B)` 项）、
  `upperBranch_of_mt_ge`、`aUpperCorrect_iff`/`bUpperCorrect_iff`、
  前缀比值恒等式 `phase2B_eq` 与命题提取
  `upperBranchA_prop`/`upperBranchB_prop` 也已编译；44.2 的上升段
  分子上界由新模块 `../lean/RisingBound.lean` 编译
  （`amaxWord`、`wordA_le_amaxWord`、
  `three_mul_amaxWord_add`、`amaxWord_div_eq_hmax`）；
  B0（`S<=64` 时 `P<=188`）已由同一文件编译
  （`b0_check`、`b0_spec`）；
  TD-1 证书层收口已由 `../lean/Td1Final.lean` 编译
  （`td1_cert_components`）；
  GC-7 第 13.1 的 Rat 重读在六个小 `P` 上已由
  `../lean/Gc7Window.lean` 编译（`gc7_window_rat_check`）；
  完整 Real `δ` 重读已由 `../lean/Td0Real.lean` 编译
  （`gc7_real_window_delta`、`deltaCeil_eq`）；
  TD-1 最终窗口矛盾已由 `../lean/Td0Final.lean` 编译
  （`td1A_closed`、`td1B_closed`：由 C3 闭式得到
  `A_req=A_chain`，再与链内插界和区间排除矛盾）；
  链内插界已由 `../lean/Td1Interp.lean` 闭合，并经
  `td1A_closed_of_chain`/`td1B_closed_of_chain` 接入；
  `../lean/Td0CertBridge.lean` 已给出清分母字级证书与轨道/整循环
  方程；`Areq` 等价映射已由 `../lean/Td0CertBridge.lean`/
  `../lean/Td0Final.lean` 闭合并接到最终窗口矛盾；轨道到 `pos` 的
  成员性已由 `../lean/ScratchOrbit.lean` 编译
  （`twosPositions_mem_combinations`、
  `twosPositions_mem_combinations_of_last_one`、
  `twosPositions_mem_combinations_of_last_two`）；52.17 同余系统
  已由 `../lean/Td0CertBridge.lean` 编译：A/B 端点模类
  （`chainFirst_mod16_of_c3Exact_weight_three`、
  `chainFirst_mod64_of_c3Exact_weight_five`）、最终同余
  （`word_endpoint_mod16_of_mod16`、
  `word_endpoint_mod64_of_mod64`）、表规格提取
  （`table_A_spec`/`table_B_spec`）以及整合同余
  （`congruence_52_17_A`/`congruence_52_17_B`）；真实词的
  `wordA = auOfPos` 语义桥已由 `../lean/ScratchOrbit.lean` 编译
  （`wordOfPos_cons_shift`、`auOfPos_cons_pos`、
  `wordA_eq_auOfPos_of_twosPositions`、
  `wordA_eq_auOfPos_of_twosPositions_dropLast`）；最终接线已由
  `../lean/Td0Final.lean` 的
  `td1A_cert_closed_of_word`/`td1B_cert_closed_of_word` 编译完成，
  真实上升词可直接送入 A/B 族最终矛盾；A/B 分支合成入口
  `td0_cert_closed` 也已编译，全部输入打包为 `Td0Data`，并由
  `td0_closed_of_data` 从单个 datum 闭合，且不再要求
  `tableUpper = true`。阶段一的两个下分支/特殊三元组
  `(1,20,11)` 与 `(2,8,7)` 已分别由 `td0_A_special_false` 与
  `td0_B_special_false` 编译：前者用唯一词的余数 `m = 17749` 对
  `m0 = 31` 矛盾，后者用全局循环方程与 `sixAuOK` 最大值矛盾；
  其余可行三元组由 `tableUpper_of_feasible_not_special` 回到
  `td0_cert_closed`。框 A + QB-8 包装接口 `Qb8Cycle`/
  `td0_of_qb8_cycle` 已编译：阶段一直接吃 `Td0Data`，阶段二由
  `Qb8Cycle2`/`qb8_cycle2_to_td0Data2` 从 B1/B2 + G5' 与
  `tCeil_pow_lt` 组装出
   `Td0Data2`。阶段二真实轨道侧接口已收口：`Qb8OrbitInput`/
   `qb8_orbit_of_firstWord`、`Qb8OrbitGC7Input`/`qb8_orbit_of_gc7Input`、
   `Qb8OrbitCycleInput`/`qb8_orbit_of_cycleInput` 与
   `Qb8OrbitB0Input`/`qb8_orbit_of_b0Input`、`U` 界变体
   `Qb8OrbitU1Input`/`qb8_orbit_of_u1Input` 与结构变体
   `Qb8OrbitStructuralInput`/`qb8_orbit_of_structuralInput` 与结构
   `U` 界变体 `Qb8OrbitStructuralU1Input`/`qb8_orbit_of_structuralU1Input`
   均已编译，`hSfirst`、`hwS`、`hfeas`、`hU`、`h201`、`hcyc`、`hD`、
   `hT` 与 B0 范围 `hP205` 全部自动推导（`hP205` 由
   `P_lt_205_of_pow_six` 从链上界结构推出）；剩余解析输入只剩
   52.12 的族末步 `hlast`（词层）或族 `U` 界 `hU1`（解析层）。
   真实首个 C3 词规范
   `firstC3WordAux_ok_of_hit`/`firstC3WordAux_weight_of_hit` 与
   `FirstC3Orbit`/`qb8_orbit_of_firstC3` 也已编译。
- Lean 接口已闭：`E_L=5^L E+M_L`、failure 仿射等价、
  `S_{a+1}=5S_a+2^{2a-1}`、宏成功/失败互补、宏端点恒等式、
  余量单调、终端容量归约、D 不变量两条
  （`../lean/BalanceRecurrence.lean`，已编译）；
- Lean 宏步窗口已编译（`../lean/MacroWindow.lean`）：宏步闭式与
  估值、`5r_a+3=2(5^aC-1)`、非终段余量奇偶；
  L1 收窄见 `macro_chain_parity_l1_reduction.md`：只剩首宏步、
  `V=m`（`m≡1 mod 4`）与 `a>=8`；`a=8` 候选再收窄为
  上一宏步 `v2(a_prev)>=14`、`v2(a_prev)=13` 或
  `s_prev=n_prev` 三分支；首宏步候选已写成 `s''` 的高位同余
  （模 `2^(2j+8)` 或 `2^(2j+9)`）与 5-adic/2-adic 区间轮廓；
- Lean 词窗口已编译（`../lean/WordWindow.lean`）：任意词的轨道恒等式
  `2^S*orbit=5^L*x+A_L`、端点 C3 同余，以及
  `x<2^(S+3)` 下代表元唯一性（对应 `d0_chain_bound_progress.md`
  引理 34.1 的解析核心）；另已编译 `t2_low_weight_excluded`：
  对 `B=40m+23>330`，首词权重 `S<=6` 与 `B<2^(S+3)` 不可能同时成立；
  还编译了 `wordA_lt_five_pow` 与 `wordA_le_five_pow_sub_four_pow`：
  对 `{1,2}` 词有 `A_L<5^L` 且 `A_L<=5^L-4^L`；
  `word_representative_unique_t2/t1` 证明每个词在 `40m+23` 或
  `20m+13` 候选族中至多对应一个 `m`；
- 修正 d0 文档首步分类：`5p+1≡0 mod16` 不总是成立（`m=7` 反例），
  精确为 `8|5p+1`、`t1>=3`；Lean `t2_parent_not_W_class`、
  `t1_parent_not_W_class` 已编译；
  Lean 另编译 `t2_parent_mod_eight_zero/one`：`m≡0/1 mod4`
  时父节点分别满足 `p≡5/7 mod8`，对应首游程 `k=1/k>=2`；
  `t1_parent_mod_eight_zero/two/three`：`m≡0/2/3 mod4`
  时父节点分别满足 `p≡1/5/7 mod8`；
  `step_weight_one_of_mod8`、`step_weight_two_of_mod8` 与
  `t2_first_step_one/two`、`t1_first_step_one/two` 形式化首步
  权重的 `v2` 分类（`p≡1,5 mod8 -> t=1`，`p≡7 mod8 -> t=2`）；
  `wordLast_le_wordWeight` 给出末步步长不超过总权重；
  `wordA_mod_five_of_wordLast` 给出 `A_L≡2^(S-last) (mod 5)`，
  是词端点 CRT 的 5-adic 输入；
  `pow_two_mod_five_period` 给出 `2^(n+4)≡2^n (mod 5)`，
  用于端点 CRT 的模 5 周期化简；
  `invOdd`/`invOdd_spec` 给出奇数模 `2^(n+1)` 的 Hensel 提升逆元，
  是 `ρ_w` 显式公式的模逆工具；
  `wordRepresentative`/`wordRepresentative_spec` 给出显式代表元并
  证明其满足端点 C3 同余式；
- `t=1` 低权排除已确认不成立：`B=213,293` 是 `B=20m+13`、
  `S=6`、`B<2^(S+3)` 的反例，不能仿照 `t=2` 的 `S(B)>=7`；
- 当前已编译定理、死路与剩余精确缺口的完整清单见
  `lean_2adic_status.md`；
- `t_j=2` 尾部方程有解 ⇒ `delta∈{1,3}` 且
  `k<0.1386j-4.876`（必要，`block_head_tail_reduction.md`）；
- L ⇒ C ⇒ G_i>=1（沿 `capacity_lemma_reduction.md` 的已写推导）；
- G_i>=1 ⇔ c_k>=4(4/5)^k（定义等价）；
- c_k 正下界 ⇒ m_d>=2^{d+2} 的链恒等式入口已写
  （`e0_margin_automaton.md` 第 947--948 行）。

## 3. 结论

目标第 6 项要求的“完整衔接”目前**不能**仅由现成文档给出：
`L`、`C`、c_k 尾部、`m_d>=2^{d+2}`、`D0` 都是逐链接开放语句
（同属 `D0 → m_d → c_k/G_i → C → L → B → 局部引理` 归约链，
非相互独立），且纯 `t=2` 块的 S6 需要单独处理。本审计不改变
局部引理是当前主入口的事实，但后续任何“闭合后衔接”的声明
都必须先闭合这些下游链接。

> 2026-08-11 补充：此后 `lean/S6Audit.lean` 已将局部引理链零
> `sorry` 闭合（含纯 `t=2` 的 `M=1` 基例）；阶段 1 覆盖扩展与
> 下游 D0 链仍开放。

## 4. 精化：S6 是下游链的单一入口

新增定理（`local_lemma_terminal_s6_equivalence.md` 定理 2.5、2.6）：
若 S6 对所有块成立（含纯 `t=2` 块），则：

- `D_i-i<=6` 对所有块内状态成立；
- L 对 `i>=27` 成立，`17<=i<=26` 为有限基；
- C 对 `i>=25` 成立，`17<=i<=24` 为有限基；
- 由 C 的已写推导（`capacity_lemma_reduction.md` 第 2 节）
  `C -> G_i>=1 -> c_k>=4(4/5)^k -> m_d>=2^{d+2}`。

因此下游 L 与 C 不是独立障碍：**S6 一旦对所有块闭合，D0 链侧
只剩 `m_d>=2^{d+2} -> D0`（加上两个有限基），再与 SURV-EX/TD0
侧合起来才得到 7 发散**。而
`u=1` 块的 S6 已等价于局部引理；纯 `t=2` 块的 S6 等价于
`u_j<=2(j-t_j)+12`（`u_j` 偶数），归约为同一尾部方程。
