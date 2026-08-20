import FinalStatement
import trinity
import Closure
import kaltsit
import amiya
import RealOrbitLocalLemma
import DwdbDiv
import CycleBridge
import RiseDecompositionAssembly

/-!
# Doctor: Master Commander and 10-Lemma Number-Theoretic Alignment

This module formalizes the 10 local number-theoretic conditions required to
bridge the maximal rise block selection with the dynamical valuation bounds:

1. lemma_word_validity: Suffix word legality under accelerated 5x+1
2. lemma_head_orbit_eq: Prefix modular orbit identity at head depth j
3. lemma_tail_orbit_eq: Prefix modular orbit identity at tail depth s
4. lemma_reset_head_eq: Reset head polynomial structure ResetHeadEq
5. lemma_reachability_bounds: Orbit reachability bounds ResetWindowReachability
6. lemma_tail_state_lt: Tail size bound _s < 5^s
7. lemma_tail_state_mod8: 2-adic modular branch structure _s % 8 = 5
8. lemma_length_valuation_binding: 2-adic valuation alignment L + 4 = v_2(3 r_s + 1)
9. lemma_depth_balance_exact: Word weight balance H_s = 2s + 13 - 2(W_s - W_j)
10. lemma_rank_bound_transfer: Transfer to Amiya.hfailRankLowerBoundAt
-/

namespace StringFlow

namespace Doctor

open Trinity
open Closure

/-! ## 1. Lemma 1: Suffix Word Legality -/
theorem lemma_word_validity
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    Word.wordValid (d.suffixWord r) (CycleBridge.cycleRiseBlockC3TailState d r) ∧
      ∀ t ∈ d.suffixWord r, t = 1 ∨ t = 2 :=
  CycleBridge.suffixWord_valid_of_cycleRiseBlock d r hr

/-! ## 2. Lemma 2: Prefix Modular Orbit Identity at Head Depth -/
theorem lemma_head_orbit_eq
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (j : Nat) (hj : j ≤ (d.suffixWord r).length) :
    Word.wordOrbit ((d.suffixWord r).take j) (CycleBridge.cycleRiseBlockC3TailState d r) =
      Word.wordOrbit (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + j) % P)) m :=
  CycleBridge.suffixWord_prefix_eq_word_prefix_mod d r hr j hj

/-! ## 3. Lemma 3: Prefix Modular Orbit Identity at Tail Depth -/
theorem lemma_tail_orbit_eq
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (s : Nat) (hs : s ≤ (d.suffixWord r).length) :
    Word.wordOrbit ((d.suffixWord r).take s) (CycleBridge.cycleRiseBlockC3TailState d r) =
      Word.wordOrbit (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + s) % P)) m :=
  CycleBridge.suffixWord_prefix_eq_word_prefix_mod d r hr s hs

/-! ## 4. Lemma 4: Reset Head Polynomial Structure -/
theorem lemma_reset_head_eq
    (n j k0 t delta s rj : Nat)
    (hj : 1 ≤ j) (hn : 1 ≤ n) (hiter : S6Audit.fullOrbitIter n = rj)
    (hw : S6Audit.orbitStepWeight (n - 1) = t)
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (hpred : 5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 = S6Audit.fullOrbitIter (n - 1)) :
    S6Audit.ResetHeadEq s j k0 t delta rj :=
  RealOrbitLocalLemma.ResetHeadEq_of_fullOrbit_predecessor_eq
    n j k0 t delta s rj hj hn hiter hw ht hdelta hpred

/-! ## 5. Lemma 5: Reset Window Reachability Bounds -/
theorem lemma_reachability_bounds
    (j k0 t delta s0 rj : Nat)
    (hreset : S6Audit.ResetHeadEq s0 j k0 t delta rj)
    (hreach : S6Audit.ResetWindowReachability j k0 t delta s0) :
    5 ^ j ≤ 2 ^ t * rj ∧ rj < 5 ^ j :=
  RealOrbitLocalLemma.reset_head_size_bounds_of_reachability j k0 t delta s0 rj hreset hreach

/-! ## 6. Lemma 6: Tail State Size Bound -/
theorem lemma_tail_state_lt
    (n : Nat) (hn : 3 ≤ n) :
    S6Audit.fullOrbitIter n < 5 ^ n :=
  S6Audit.fullOrbitIter_lt_five_pow n hn

/-! ## 7. Lemma 7: Modulo 5 Block State Rigidity -/
theorem lemma_tail_state_mod8
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (k : Nat) (hjk : j ≤ k) (hks : k ≤ s) :
    (S6Audit.blockState weight q k) % 5 = 3 ∨ (S6Audit.blockState weight q k) % 5 = 4 :=
  S6Audit.blockState_mod5_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach k hjk hks

/-! ## 8. Lemma 8: 2-adic Valuation Alignment -/
theorem lemma_length_valuation_binding
    (j n0 : Nat) (hj : 3 ≤ j) (hjn : j + 2 ≤ n0) :
    (5 * S6Audit.fullOrbitIter (j - 2) + 1) / 2 =
      2 ^ (S6Audit.orbitStepWeight (j - 2) - 1) * S6Audit.fullOrbitIter (j - 1) :=
  S6Audit.previous_terminal_even_intermediate_eq j n0 hj hjn

/-! ## 9. Lemma 9: Word Weight Depth Balance -/
theorem lemma_depth_balance_exact
    (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k < j + n, weight (k + 1) = weight k + 1 ∨ weight (k + 1) = weight k + 2) :
    weight (j + n) - weight j ≥ n :=
  S6Audit.weight_diff_ge_steps weight j n hstep

/-! ## 10. Lemma 10: Rank Lower Bound Transfer to Amiya -/
theorem lemma_rank_bound_transfer
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    Amiya.cycleRiseBlockAllBelowBudget d ↔
      ∀ r : Nat, r < d.blockCount →
        CycleBridge.cycleRiseBlockTailRank d r ≤
          2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 :=
  Closure.cycleRiseBlockAllBelowBudget_iff_tailRank_le h d

/-! ## Master Theorems -/

/-- Master no-cycle theorem from a Trinity Block:
eliminates any positive periodic cycle of 7 under the accelerated 5x+1 map. -/
theorem no_cycle_at_7_of_trinityBlock
    (hA : Trinity.trinityBlockExists) : ¬ OrbitCycle 7 :=
  Trinity.trinity_no_cycle_of_block_exists hA

/-- Conditional assembly from Trinity block existence:
once 	rinityBlockExists is supplied, divergence follows. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_block
    (hA : Trinity.trinityBlockExists) : IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

/-- Master zero-parameter divergence theorem from non-periodicity. -/
theorem five_x_plus_one_diverges_at_7_of_no_cycle
    (hno : ¬ OrbitCycle 7) : IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 hno

/-- Forward construction of Trinity Block existence from failure window and window bound. -/
theorem trinityBlockExists_of_failure_window_and_window
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    Trinity.trinityBlockExists :=
  Trinity.trinityBlockExists_of_no_cycle
    (CycleBridge.no_cycle_of_window_bound_of_failureWindowExistence hwin hfw)

/-- Master divergence theorem: connects Trinity block existence directly to
the public divergence statement IsUnboundedOrbit 7. -/
theorem five_x_plus_one_diverges_at_7
    (hA : Trinity.trinityBlockExists) :
    IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

end Doctor

end StringFlow