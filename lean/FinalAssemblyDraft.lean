import CycleBridge
import amiya
import trinity

/-!
# Final assembly draft (side-conversation template)

This file is a standalone skeleton for the final assembly. It is not
imported by the main build and contains `sorry` placeholders for the
parts that are still open.

Final-theorem route used here:

    CycleQb8Input
    -> SelectedBlockData
    -> SelectedHfailBlockData
    -> TrinityBlock_of_selected_block
    -> trinity_block_contradicts
    -> trinity_no_cycle_of_block_exists
    -> IsUnboundedOrbit 7

`FailureWindow` / `failureWindowExistence` and the global
`decisiveWindowValuationBoundCorrected` are deliberately NOT used by
the final theorem.
-/

namespace StringFlow
namespace FinalAssemblyDraft

open StringFlow

/-- New core lower bound:
`A_i >= m * (2^(W_i) - 5^i)` for every real `CycleQb8Input`. -/
lemma wordA_take_ge_of_global_min
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (i : Nat) (hi : i ≤ P) :
    m * (2 ^ StringFlow.wordWeight (w.take i) - 5 ^ i) ≤
      StringFlow.Word.wordA (w.take i) := by
  -- TODO: word_orbit_identity + h.hglobal_min
  sorry

/-- Core contradiction: a real `CycleQb8Input` has no `noLongT2Run`
word for its `hcycle` parameters. -/
theorem cycleQb8Input_noLongT2Run_false
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    ¬ Amiya.noLongT2Run c p := by
  -- TODO: wordA_take_ge_of_global_min + PMI equation +
  -- cycleWord_noLongT2Run_sum_bound
  sorry

/-- Thin wrapper from the core contradiction to the budget interface. -/
theorem cycleQb8InputT2RunBudget_draft
    (hcore : ∀ {m S P : Nat} {w rise c3 : List Nat},
      (h : CycleBridge.CycleQb8Input m S P w rise c3) →
      ∃ c p, w = CycleBridge.cycleWord c p ∧
        m = StringFlow.fiveXPlusOneOrbit 7 c ∧
        ¬ Amiya.noLongT2Run c p) :
    Amiya.cycleQb8InputT2RunBudget := by
  intro m S P w rise c3 h
  rcases hcore h with ⟨c, p, hw, hm, hnot⟩
  exact ⟨c, p, hw, hm,
    Amiya.cycleWordT2RunBudget_of_noLongT2Run_false c p hnot⟩

/-- The hfail rank target follows from the budget by the existing
bridge. -/
theorem hfailRankLowerBoundTarget_draft
    (hbudget : Amiya.cycleQb8InputT2RunBudget) :
    Amiya.hfailRankLowerBoundTarget :=
  Amiya.hfailRankLowerBoundTarget_of_t2_run_budget hbudget

/-- Selected hfail block assembly.

This is the place where the hfail rank target must be attached to the
same `(b, L, hres)` block that hterm selected.  The exact alignment
between `j` and the selected block endpoint is the open proof point.
-/
theorem cycleQb8InputSelectedHfailBlock_draft
    (htarget : Amiya.hfailRankLowerBoundTarget)
    (hpre : CycleBridge.cycleQb8InputSelectedRealPredecessorIdentity) :
    Trinity.cycleQb8InputSelectedHfailBlock := by
  -- TODO: use hpre for SelectedBlockData and htarget for hrank;
  -- attach hfailDepth to the same (b, L, hres)
  sorry

/-- Trinity block existence from the selected hfail block. -/
theorem trinityBlockExists_draft
    (hsel : Trinity.cycleQb8InputSelectedHfailBlock) :
    Trinity.trinityBlockExists := by
  -- TODO: TrinityBlock_of_selected_block + local window bounds +
  -- hfail_t1/hfail_t2 from hrank
  sorry

/-- Final assembly once `trinityBlockExists` is proved. -/
theorem five_x_plus_one_diverges_at_7_draft
    (hA : Trinity.trinityBlockExists) :
    IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

/-- The real final target; remove the placeholder once the draft
declarations above are filled in. -/
theorem five_x_plus_one_diverges_at_7 : IsUnboundedOrbit 7 := by
  sorry

end FinalAssemblyDraft
end StringFlow
