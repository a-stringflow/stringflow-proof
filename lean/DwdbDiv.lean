import CycleBridge
import PureCore
import UnifiedCoreBridge
import UnifiedCoreAudit

/-!
# DWDB-DIV：前文明发散桥

最外层装配接口。本模块不证明窗口定理，也不假设统一核心已闭合；
它只把 `CycleBridge` 的条件结论组装成

    windowBoundToNoCycle → ¬ OrbitCycle 7 → IsUnboundedOrbit 7。

窗口上界一律使用 `BlockAutomaton.decisiveWindowValuationBoundCorrected`；
旧的无约束 `decisiveWindowValuationBound` 已被反例否定，禁止作为输入。

统一核心闭合后，把窗口定理实例化到
`CycleBridge.windowBoundToNoCycle`，即可完成最终发散语句。
-/

namespace StringFlow.DwdbDiv

/-- Thin full-orbit-facing wrapper over the pure block-local unified core. -/
theorem unified_core_final_no_hge_full_orbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hOrbit : S6Audit.OrbitFrom7 r)
    (hH : 2 ≤ H_s) :
    S6Audit.twoValuation
      (5 ^ (L + 3) * UnifiedCoreAudit.wTerminal L r_s + 1) ≤ H_s - 2 :=
  UnifiedCoreAudit.unified_core_final_no_hge_pure
    j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hOrbit hH

/-- 统一核心闭合接口：所有 36.20 参数实例均成立。修正：显式携带
块首重置前提 `∃ s0 k t δ, ResetHeadEq s0 j k t δ r`，它对应文档
36.20 中“j 是上一偶数终端后的重置步”这一条；上一终端使用
`PreviousTerminalAtDepth`（含深度 `j-1`），与最终核心一致。 -/
def unifiedCoreClosed : Prop :=
  ∀ (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat),
    ∀ (_hPrem : UnifiedCoreAudit.All36_20PremisesNoHge
          j Wp Wj q Aj A_s s W_s r_s L H_s weight)
      (_hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
      (_hReach : S6Audit.OrbitFrom7 r)
      (_hReset : ∃ s0 k t δ r_prev : Nat,
        S6Audit.ResetHeadEq s0 j k t δ r ∧ s0 * 5 ^ k = r_prev + 1 ∧
          S6Audit.PreviousTerminalAtDepth s0 j k r_prev)
      (_hH : 2 ≤ H_s),
      S6Audit.twoValuation
        (5 ^ (L + 3) * UnifiedCoreAudit.wTerminal L r_s + 1) ≤ H_s - 2

/-- 统一核心闭合：由 `unified_core_final_no_hge` 对全部参数实例化。 -/
theorem unifiedCoreClosed_proved : unifiedCoreClosed := by
  intro j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach hReset hH
  exact unified_core_final_no_hge_full_orbit
    j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach hH

/-- 条件引理接口：统一核心闭合后，循环给出全局可达重置点。 -/
def orbitCycleImpFullGloballyReachableConditional : Prop :=
  unifiedCoreClosed →
    ∀ _h : OrbitCycle 7,
      ∃ s0 N δ : Nat, S6Audit.FullIsGloballyReachableCorrected s0 N δ

/-- 条件接口：统一核心闭合后应推出 corrected 窗口上界。该推出目前
未证明；缺口记录在 `docs/decisive_window_corrected.md`。 -/
def decisiveWindowValuationBoundCorrected_of_unified_core : Prop :=
  unifiedCoreClosed →
    BlockAutomaton.decisiveWindowValuationBoundCorrected

/-- 条件接口：`failureWindowExistence` 需要真实可达性块首；若后续
证明依赖统一核心，必须以本条件形式接线，不得宣称绕过统一核心。 -/
def failureWindowExistenceOfUnifiedCore : Prop :=
  unifiedCoreClosed →
    CycleBridge.failureWindowExistence

/-- 最外层接口：循环桥闭合且无 `7` 的正循环时，`7` 的轨道无界。 -/
theorem dwdbDivFinalAssembly
    (_hbridge : CycleBridge.windowBoundToNoCycle) :
    ¬ OrbitCycle 7 → IsUnboundedOrbit 7 := by
  intro hnoCycle
  exact unbounded_of_no_cycle 7 hnoCycle

/-- 直接实例化窗口定理输入的最终形式。 -/
theorem five_x_plus_one_diverges_at_7_of_window_bound
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hbridge : CycleBridge.windowBoundToNoCycle) :
    IsUnboundedOrbit 7 :=
  CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound hwin hbridge

/-- 条件合成：窗口界加第 3 步失败窗口存在性，否定 `7` 的正循环。 -/
theorem cycle_of_window_bound_contradiction
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : CycleBridge.failureWindowExistence) :
    ¬ OrbitCycle 7 :=
  CycleBridge.no_cycle_of_window_bound_of_failureWindowExistence hwin hfw

/-- 条件最终形式：窗口界加第 3 步失败窗口存在性，直接得
`7` 的轨道无界。 -/
theorem five_x_plus_one_diverges_at_7_of_failure_window
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : CycleBridge.failureWindowExistence) :
    IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 (cycle_of_window_bound_contradiction hwin hfw)

end StringFlow.DwdbDiv

#print axioms StringFlow.DwdbDiv.dwdbDivFinalAssembly
#print axioms StringFlow.DwdbDiv.five_x_plus_one_diverges_at_7_of_window_bound
#print axioms StringFlow.DwdbDiv.cycle_of_window_bound_contradiction
#print axioms StringFlow.DwdbDiv.five_x_plus_one_diverges_at_7_of_failure_window
