import amiya

/-!
# Closure: remaining hfail run-budget assembly

The heavy orbit/rank infrastructure lives in `amiya.lean`.  This file
is the continuation point for the remaining `L > U` leg and the final
trinity assembly, so the larger files do not need to be recompiled for
each new local lemma.
-/

namespace StringFlow

namespace Closure

open Amiya

/-- Per-block recovery budget: the `t=1` recharge plus the C3 residual
is exactly `2·H2` plus the C3 weight.  This is the period-closure
identity combined with the C3 chain rank-gain telescope. -/
theorem cycleRiseBlockCharge_add_residualSum_eq_two_mul_H2_add_c3WeightSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockCharge d r +
        CycleBridge.cycleRiseBlockC3ResidualSum d r =
      2 * CycleBridge.riseCountTwo (d.suffixWord r) +
        (d.c3Word r).sum := by
  have hper := cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two h d r hr
  have hc3 := CycleBridge.cycleRiseBlockC3ChainRankGain d r hr
  have hc3' : CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum =
      2 + CycleBridge.cycleRiseBlockC3ResidualSum d r := by
    simpa [CycleBridge.cycleRiseBlockC3ResidualSum] using hc3
  omega

/-- The recovery identity instantiated on the concrete cyclic rise
decomposition of a real `CycleQb8Input`. -/
theorem recovery_identity_of_input
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    ∃ d : CycleBridge.CycleRiseBlockDecomposition m S P w,
      1 ≤ d.blockCount ∧
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockCharge d r)).sum +
        ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r)).sum =
        2 * CycleBridge.cycleRiseBlockH2Sum d +
          ((List.range d.blockCount).map (fun r => (d.c3Word r).sum)).sum := by
  rcases CycleBridge.cycleRiseBlockDecompositionExists_of_input h with ⟨d, hpos⟩
  refine ⟨d, hpos,
    cycleRiseBlockChargeSum_add_residualSum_eq_two_mul_H2_add_c3WeightSum h d⟩

/-- If every maximal `t=2` run is short, then the rank-drop leg is
dominated by the `noLongT2Run` bound: `L ≤ U`. -/
theorem t2RunRankSum_le_t2RunBoundSum_of_short_runs
    (c p : Nat)
    (hshort : ∀ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length ≤ run.start + 6) :
    t2RunRankSum c p ≤ t2RunBoundSum c p := by
  rw [t2RunRankSum_eq_two_mul_riseCountTwo]
  unfold t2RunBoundSum
  let w := CycleBridge.cycleWord c p
  have hle : ∀ run ∈ maxT2Runs w, 2 * run.length ≤ 2 * run.start + 12 := by
    intro run hmem
    have hb := hshort run (by simpa [w] using hmem)
    omega
  have hlen : ((maxT2Runs w).map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo w := by
    simpa [w, maxT2Runs] using maxT2RunsFrom_length_sum w 0
  have hmain : 2 * CycleBridge.riseCountTwo w ≤
      ((maxT2Runs w).map (fun run => 2 * run.start + 12)).sum := by
    calc
      2 * CycleBridge.riseCountTwo w
          = ((maxT2Runs w).map (fun run => 2 * run.length)).sum := by
            rw [← hlen, List.sum_map_mul_left (maxT2Runs w)
              (fun run => run.length) 2]
      _ ≤ ((maxT2Runs w).map (fun run => 2 * run.start + 12)).sum :=
            List.sum_le_sum hle
  simpa [w] using hmain

/-- The strict leg `L > U` forces at least one maximal `t=2` run to
exceed the `noLongT2Run` length bound. -/
theorem t2RunRankSumGtBoundSum_imp_exists_long_run
    (c p : Nat) (hgt : t2RunRankSumGtBoundSum c p) :
    ∃ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.start + 6 < run.length := by
  by_contra hnone
  have hshort : ∀ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length ≤ run.start + 6 := by
    intro run hmem
    by_contra hle
    have hgt2 : run.start + 6 < run.length := by omega
    exact hnone ⟨run, hmem, hgt2⟩
  have hle := t2RunRankSum_le_t2RunBoundSum_of_short_runs c p hshort
  unfold t2RunRankSumGtBoundSum at hgt
  omega

/-- The `t=2` count splits over the cyclic segments `[hd r, hd (r+1))`
that partition the word.  This is the `riseCountTwo` analogue of
`CycleBridge.wordWeight_sum_of_segments`: rotation preserves the
multiset of entries, so the count over the wrapped last segment plus
the linear segments is exactly the count over the whole word. -/
theorem riseCountTwo_sum_of_segments
    (w : List Nat) (K : Nat) (hd : Nat → Nat) (seg : Nat → List Nat)
    (hKpos : 0 < K)
    (hseg : ∀ r, r + 1 < K → seg r = (w.take (hd (r + 1))).drop (hd r))
    (hseg_last : seg (K - 1) = (w.drop (hd (K - 1))) ++ (w.take (hd 0)))
    (hlen : ∀ r, r + 1 < K → hd (r + 1) = hd r + (seg r).length)
    (_hlen_last : hd 0 + w.length = hd (K - 1) + (seg (K - 1)).length) :
    ((List.range K).map (fun r => CycleBridge.riseCountTwo (seg r))).sum =
      CycleBridge.riseCountTwo w := by
  have hprefix : ∀ n, n ≤ K - 1 →
      CycleBridge.riseCountTwo (w.take (hd n)) =
        CycleBridge.riseCountTwo (w.take (hd 0)) +
          ((List.range n).map (fun r => CycleBridge.riseCountTwo (seg r))).sum := by
    intro n hn
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hnK : n + 1 ≤ K - 1 := hn
        have hnlt : n + 1 < K := by omega
        have hn1 : n < K - 1 := by omega
        have hnle : hd n ≤ hd (n + 1) := by
          have hlen' := hlen n (by omega)
          omega
        have htake3 : (w.take (hd (n + 1))).take (hd n) = w.take (hd n) := by
          rw [List.take_take]
          rw [Nat.min_comm, Nat.min_eq_right hnle]
        have htake2 : (w.take (hd (n + 1))).take (hd n) ++
            (w.take (hd (n + 1))).drop (hd n) = w.take (hd (n + 1)) :=
          List.take_append_drop (hd n) (w.take (hd (n + 1)))
        have htake : w.take (hd (n + 1)) =
            w.take (hd n) ++ (w.take (hd (n + 1))).drop (hd n) := by
          simpa [htake3] using htake2.symm
        have hseg' : (w.take (hd (n + 1))).drop (hd n) = seg n :=
          (hseg n hnlt).symm
        have hww : CycleBridge.riseCountTwo (w.take (hd (n + 1))) =
            CycleBridge.riseCountTwo (w.take (hd n)) +
              CycleBridge.riseCountTwo (seg n) := by
          rw [htake, hseg']
          rw [riseCountTwo_append]
        calc
          CycleBridge.riseCountTwo (w.take (hd (n + 1))) =
              CycleBridge.riseCountTwo (w.take (hd n)) +
                CycleBridge.riseCountTwo (seg n) := hww
          _ = CycleBridge.riseCountTwo (w.take (hd 0)) +
                ((List.range n).map (fun r => CycleBridge.riseCountTwo (seg r))).sum +
                CycleBridge.riseCountTwo (seg n) := by
              rw [ih (by omega)]
          _ = CycleBridge.riseCountTwo (w.take (hd 0)) +
                ((List.range (n + 1)).map
                  (fun r => CycleBridge.riseCountTwo (seg r))).sum := by
              rw [List.range_succ]
              rw [List.map_append, List.sum_append]
              simp [Nat.add_assoc]
  have htotal : ((List.range K).map (fun r => CycleBridge.riseCountTwo (seg r))).sum =
      ((List.range (K - 1)).map (fun r => CycleBridge.riseCountTwo (seg r))).sum +
        CycleBridge.riseCountTwo (seg (K - 1)) := by
    have hK : K = (K - 1) + 1 := by omega
    rw [hK, List.range_succ]
    rw [List.map_append, List.sum_append]
    simp
  have hpref := hprefix (K - 1) (by omega)
  have hW0le : CycleBridge.riseCountTwo (w.take (hd 0)) ≤
      CycleBridge.riseCountTwo (w.take (hd (K - 1))) := by omega
  have hwwlast : CycleBridge.riseCountTwo (seg (K - 1)) =
      CycleBridge.riseCountTwo (w.drop (hd (K - 1))) +
        CycleBridge.riseCountTwo (w.take (hd 0)) := by
    rw [hseg_last]
    rw [riseCountTwo_append]
  have hdrop : CycleBridge.riseCountTwo w =
      CycleBridge.riseCountTwo (w.take (hd (K - 1))) +
        CycleBridge.riseCountTwo (w.drop (hd (K - 1))) := by
    have hsplit : w.take (hd (K - 1)) ++ w.drop (hd (K - 1)) = w :=
      List.take_append_drop (hd (K - 1)) w
    have hww := riseCountTwo_append (w.take (hd (K - 1))) (w.drop (hd (K - 1)))
    rwa [hsplit] at hww
  calc
    ((List.range K).map (fun r => CycleBridge.riseCountTwo (seg r))).sum
        = ((List.range (K - 1)).map (fun r => CycleBridge.riseCountTwo (seg r))).sum +
            CycleBridge.riseCountTwo (seg (K - 1)) := htotal
    _ = (CycleBridge.riseCountTwo (w.take (hd (K - 1))) -
            CycleBridge.riseCountTwo (w.take (hd 0))) +
            CycleBridge.riseCountTwo (seg (K - 1)) := by
        have htot : ((List.range (K - 1)).map
            (fun r => CycleBridge.riseCountTwo (seg r))).sum =
            CycleBridge.riseCountTwo (w.take (hd (K - 1))) -
              CycleBridge.riseCountTwo (w.take (hd 0)) := by
          omega
        rw [htot]
    _ = (CycleBridge.riseCountTwo (w.take (hd (K - 1))) -
            CycleBridge.riseCountTwo (w.take (hd 0))) +
          (CycleBridge.riseCountTwo (w.drop (hd (K - 1))) +
            CycleBridge.riseCountTwo (w.take (hd 0))) := by
        rw [hwwlast]
    _ = CycleBridge.riseCountTwo (w.take (hd (K - 1))) +
          CycleBridge.riseCountTwo (w.drop (hd (K - 1))) := by omega
    _ = CycleBridge.riseCountTwo w := hdrop.symm

/-- `take` then `drop` of a middle segment followed by the tail is the
drop starting at the segment head. -/
lemma take_drop_append_drop_of_le (w : List Nat) (a b : Nat)
    (hab : a ≤ b) (hb : b ≤ w.length) :
    (w.take b).drop a ++ w.drop b = w.drop a := by
  have hlen : a ≤ (w.take b).length := by
    rw [List.length_take_of_le hb]
    exact hab
  have hsplit : w.take b ++ w.drop b = w := List.take_append_drop b w
  calc
    (w.take b).drop a ++ w.drop b = ((w.take b) ++ w.drop b).drop a := by
      rw [List.drop_append_of_le_length hlen]
    _ = w.drop a := by rw [hsplit]

/-- A block's C3 word plus rise suffix is exactly the linear word
segment `[headDepth r, headDepth (r+1))` when the block does not wrap. -/
lemma cycleRiseBlockSeg_eq_drop_take_nonwrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    d.c3Word r ++ d.suffixWord r =
      (w.take (d.headDepth (r + 1))).drop (d.headDepth r) := by
  let hd := d.headDepth r
  let c3l := (d.c3Word r).length
  let sl := (d.suffixWord r).length
  have hC : d.c3Word r = (w.take (hd + c3l)).drop hd := by
    have h := CycleBridge.cycleRiseBlockC3Word_eq_prefix_drop d r hr
    simpa [hd, c3l] using h
  have hS : d.suffixWord r = (w.drop (hd + c3l)).take sl := by
    have h := CycleBridge.cycleRiseBlockSuffixWord_eq_drop_nonwrap d r hr hrnext
    simpa [hd, c3l, sl] using h
  have hnext : hd + c3l + sl = d.headDepth (r + 1) := by
    have h := d.hnext r hr
    dsimp [hd, c3l, sl]
    rw [if_pos hrnext] at h
    omega
  have hlen : hd + c3l + sl ≤ w.length := by
    rw [hnext]
    have hlt := d.hhead_lt (r + 1) hrnext
    have hP : P = w.length := d.hperiod.symm
    omega
  rw [hC, hS]
  have hmain : (w.take (hd + c3l)).drop hd ++ (w.drop (hd + c3l)).take sl =
      (w.take (hd + c3l + sl)).drop hd := by
    -- list algebra: a middle take/drop followed by a tail take
    have hsplit1 : w.take (hd + c3l + sl) =
        w.take (hd + c3l) ++ (w.take (hd + c3l + sl)).drop (hd + c3l) := by
      have hle2 : hd + c3l ≤ hd + c3l + sl := by omega
      have ht : (w.take (hd + c3l + sl)).take (hd + c3l) = w.take (hd + c3l) := by
        rw [List.take_take]
        rw [Nat.min_comm, Nat.min_eq_right hle2]
      simpa [ht] using (List.take_append_drop (hd + c3l) (w.take (hd + c3l + sl))).symm
    have hdrop : (w.take (hd + c3l + sl)).drop (hd + c3l) = (w.drop (hd + c3l)).take sl := by
      rw [List.take_drop]
    have hleA : hd ≤ (w.take (hd + c3l)).length := by
      rw [List.length_take_of_le (by omega)]
      omega
    calc
      (w.take (hd + c3l)).drop hd ++ (w.drop (hd + c3l)).take sl
          = (w.take (hd + c3l)).drop hd ++ (w.take (hd + c3l + sl)).drop (hd + c3l) := by
              rw [hdrop]
      _ = ((w.take (hd + c3l)) ++ (w.take (hd + c3l + sl)).drop (hd + c3l)).drop hd := by
              rw [List.drop_append_of_le_length hleA]
      _ = (w.take (hd + c3l + sl)).drop hd := by
              rw [← hsplit1]
  rwa [hnext] at hmain

/-- The first block head is no later than every later block head. -/
lemma cycleRiseBlock_headDepth_mono
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    d.headDepth 0 ≤ d.headDepth r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrlt : r < d.blockCount := by omega
      have hrnext : r + 1 < d.blockCount := hr
      have hh := d.hnext r hrlt
      have hhd : d.headDepth (r + 1) =
          d.headDepth r + (d.c3Word r).length + (d.suffixWord r).length := by
        rw [if_pos hrnext] at hh
        omega
      have hpos : 1 ≤ (d.c3Word r).length :=
        List.length_pos_iff.mpr (d.hc3_nonempty r hrlt)
      have hmono := ih hrlt
      omega

/-- A block's C3 word plus rise suffix is the cyclic segment that wraps
from the last block head to the first block head. -/
lemma cycleRiseBlockSeg_eq_drop_take_wrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 1 ≤ d.blockCount) :
    d.c3Word (d.blockCount - 1) ++ d.suffixWord (d.blockCount - 1) =
      (w.drop (d.headDepth (d.blockCount - 1))) ++ (w.take (d.headDepth 0)) := by
  let K := d.blockCount
  let hd := d.headDepth (K - 1)
  let c3l := (d.c3Word (K - 1)).length
  let tail := hd + c3l
  let sl := (d.suffixWord (K - 1)).length
  have hr : K - 1 < K := by omega
  have hwrap : tail + sl = d.headDepth 0 + P := by
    have hh := d.hnext (K - 1) hr
    dsimp [tail, sl]
    rw [if_neg (by omega : ¬ (K - 1) + 1 < K)] at hh
    omega
  have htail_lt : tail - 1 < P := by
    have h := CycleBridge.cycleRiseBlockTailDepth_lt_succ d (K - 1) hr
    dsimp [tail, hd, c3l, CycleBridge.cycleRiseBlockTailDepth] at h
    exact h
  have htail_le : tail ≤ P := by omega
  have hd_le_tail : hd ≤ tail := by dsimp [tail]; omega
  have hd0_le_hd : d.headDepth 0 ≤ hd := by
    have h := cycleRiseBlock_headDepth_mono d (K - 1) hr
    simpa [hd] using h
  have hd0_le_tail : d.headDepth 0 ≤ tail := le_trans hd0_le_hd hd_le_tail
  have hLle : sl ≤ w.length := by
    have hsl : sl = d.headDepth 0 + P - tail := by omega
    have hP : w.length = P := d.hperiod
    omega
  have hrot : d.suffixWord (K - 1) =
      (CycleBridge.cyclicSegmentAt w tail).take sl := by
    have hle_w : sl ≤ w.length := hLle
    exact CycleBridge.cycleRiseBlockSuffixWord_eq_cyclic_take d (K - 1) hr hle_w
  have hsl' : sl - (w.length - tail) = d.headDepth 0 := by
    have hP : w.length = P := d.hperiod
    omega
  have htake : (CycleBridge.cyclicSegmentAt w tail).take sl =
      (w.drop tail) ++ (w.take (d.headDepth 0)) := by
    unfold CycleBridge.cyclicSegmentAt
    rw [List.take_append]
    have hdropTake : (w.drop tail).take sl = w.drop tail :=
      List.take_of_length_le (by
        have hP : w.length = P := d.hperiod
        rw [List.length_drop]
        omega)
    have ht1 : (w.take tail).take (d.headDepth 0) = w.take (d.headDepth 0) := by
      rw [List.take_take]
      rw [Nat.min_eq_left hd0_le_tail]
    rw [hdropTake]
    rw [List.length_drop]
    rw [hsl', ht1]
  have hS : d.suffixWord (K - 1) = (w.drop tail) ++ (w.take (d.headDepth 0)) := by
    rw [hrot]
    exact htake
  have hC : d.c3Word (K - 1) = (w.take tail).drop hd := by
    have h := CycleBridge.cycleRiseBlockC3Word_eq_prefix_drop d (K - 1) hr
    simpa [hd, tail] using h
  have htail_le_w : tail ≤ w.length := by
    rw [d.hperiod]
    exact htail_le
  have hmain : (w.take tail).drop hd ++ ((w.drop tail) ++ (w.take (d.headDepth 0))) =
      (w.drop hd) ++ (w.take (d.headDepth 0)) := by
    rw [← List.append_assoc]
    rw [take_drop_append_drop_of_le w hd tail hd_le_tail htail_le_w]
  rw [hC, hS]
  exact hmain

/-- The total number of `t=2` steps in a nonempty cyclic rise block
decomposition is the total number of `t=2` steps in the whole word. -/
theorem cycleRiseBlockH2Sum_eq_riseCountTwo
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 1 ≤ d.blockCount) :
    CycleBridge.cycleRiseBlockH2Sum d = CycleBridge.riseCountTwo w := by
  let K := d.blockCount
  let hd := d.headDepth
  let seg := fun r => d.c3Word r ++ d.suffixWord r
  have hKpos : 0 < K := by omega
  have hsegs : ∀ r, r + 1 < K → seg r = (w.take (hd (r + 1))).drop (hd r) := by
    intro r hr
    dsimp [seg, hd, K]
    exact cycleRiseBlockSeg_eq_drop_take_nonwrap d r (by omega) hr
  have hseg_last : seg (K - 1) = (w.drop (hd (K - 1))) ++ (w.take (hd 0)) := by
    dsimp [seg, hd, K]
    exact cycleRiseBlockSeg_eq_drop_take_wrap d hpos
  have hlen : ∀ r, r + 1 < K → hd (r + 1) = hd r + (seg r).length := by
    intro r hr
    have hh := d.hnext r (by omega)
    dsimp [hd, seg] at hh ⊢
    rw [if_pos hr] at hh
    rw [List.length_append]
    omega
  have hlen_last : hd 0 + w.length = hd (K - 1) + (seg (K - 1)).length := by
    have hr : K - 1 < K := by omega
    have hh := d.hnext (K - 1) hr
    dsimp [hd, seg] at hh ⊢
    rw [if_neg (by omega : ¬ (K - 1) + 1 < K)] at hh
    rw [List.length_append]
    have hP : P = w.length := d.hperiod.symm
    omega
  have hsum := riseCountTwo_sum_of_segments w K hd seg hKpos hsegs hseg_last hlen hlen_last
  have hc3zero : ∀ r, r < K → CycleBridge.riseCountTwo (d.c3Word r) = 0 := by
    intro r hr
    have hc3zero_aux : ∀ l : List Nat, (∀ t ∈ l, t ≠ 2) →
        CycleBridge.riseCountTwo l = 0 := by
      intro l
      induction l with
      | nil => simp [CycleBridge.riseCountTwo]
      | cons a as ih =>
          intro hok
          have ha : a ≠ 2 := hok a (by simp [List.mem_cons])
          have htail := ih (fun t ht => hok t (by simp [ht]))
          simp [CycleBridge.riseCountTwo, ha, htail]
    exact hc3zero_aux (d.c3Word r) (by
      intro t ht h2
      have hge : 3 ≤ t := d.hc3_entries r hr t ht
      omega)
  have hmap : (List.range K).map (fun r => CycleBridge.riseCountTwo (seg r)) =
      (List.range K).map (fun r => CycleBridge.riseCountTwo (d.suffixWord r)) := by
    apply List.map_congr_left
    intro r hr
    dsimp [seg]
    rw [riseCountTwo_append, hc3zero r (List.mem_range.mp hr)]
    simp
  have hsegSum : ((List.range K).map (fun r => CycleBridge.riseCountTwo (seg r))).sum =
      CycleBridge.cycleRiseBlockH2Sum d := by
    rw [hmap]
    rfl
  rwa [hsegSum] at hsum

/-- Per-run exact rank relation on the concrete `hcycle` word: a
maximal `t=2` run of length `L` starting at `a` drops the concrete
orbit rank by exactly `2L`.  This is the termwise identity behind
`t2RunRankSum_eq_two_mul_riseCountTwo`, stated with the explicit
`cycleWord c p` / `fiveXPlusOneOrbit 7 (c+...)` anchors. -/
theorem t2_run_start_rank_eq_exit_rank_add_two_mul_length
    (c p : Nat) (run : T2Run)
    (hmem : run ∈ maxT2Runs (CycleBridge.cycleWord c p)) :
    cycleWordRank c run.start =
      cycleWordRank c (run.start + run.length) + 2 * run.length := by
  let w := CycleBridge.cycleWord c p
  let y : Nat → Nat := fun i => StringFlow.fiveXPlusOneOrbit 7 (c + i)
  have hmem_two : ∀ i : Nat, i < run.length →
      w.getI (run.start + i) = 2 := by
    intro i hi
    have h := maxT2RunsFrom_mem_two w 0 run hmem i hi
    simpa [w] using h
  have hbnd : run.start + run.length ≤ p := by
    have hbnd' := maxT2RunsFrom_bounds w 0 run hmem
    rw [CycleBridge.cycleWord_length] at hbnd'
    simpa [w] using hbnd'
  have hstep : ∀ i : Nat, i < run.length →
      y (run.start + i + 1) = (5 * y (run.start + i) + 1) / 4 := by
    intro i hi
    have hb : run.start + i < p := by
      have hb' : run.start + i < run.start + run.length := by omega
      exact lt_of_lt_of_le hb' hbnd
    have hsucc := CycleBridge.wordOrbit_take_succ w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    have hpre1 : StringFlow.Word.wordOrbit (w.take (run.start + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i)
        (le_of_lt hb)
    have hpre2 : StringFlow.Word.wordOrbit (w.take (run.start + i + 1))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i + 1) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i + 1)
        (by omega)
    rw [hpre1, hpre2, hmem_two i hi] at hsucc
    simpa using hsucc
  have hdiv : ∀ i : Nat, i < run.length →
      (5 * y (run.start + i) + 1) % 4 = 0 := by
    intro i hi
    have hb : run.start + i < p := by
      have hb' : run.start + i < run.start + run.length := by omega
      exact lt_of_lt_of_le hb' hbnd
    have hdvd := UnifiedCoreAudit.wordValid_drop_head w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (CycleBridge.cycleWord_wordValid c p)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    have hpre1 : StringFlow.Word.wordOrbit (w.take (run.start + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i)
        (le_of_lt hb)
    rw [hpre1, hmem_two i hi] at hdvd
    simpa using hdvd
  have hsingle := t2_run_rank_sum y run.start run.length hstep hdiv
  simpa [cycleWordRank, y] using hsingle

/-- Subtraction form of the exact maximal-run rank telescope. -/
theorem t2_run_rank_drop_eq_two_mul_length
    (c p : Nat) (run : T2Run)
    (hmem : run ∈ maxT2Runs (CycleBridge.cycleWord c p)) :
    2 * run.length =
      cycleWordRank c run.start -
        cycleWordRank c (run.start + run.length) := by
  have hstart :=
    t2_run_start_rank_eq_exit_rank_add_two_mul_length c p run hmem
  omega

/-- Rank drop across a consecutive block of `t=2` steps inside the
concrete cycle word: `R(s) = R(s+k) + 2k`.  This is the word-level
form of `fullOrbitIter_rank_drop_two_iter` used when the start of the
block is not itself a maximal-run start. -/
lemma cycleWord_t2_rank_drop_in_run
    (c p s k : Nat)
    (h : ∀ i : Nat, i < k → (CycleBridge.cycleWord c p).getI (s + i) = 2)
    (hsk : s + k ≤ p) :
    cycleWordRank c s = cycleWordRank c (s + k) + 2 * k := by
  induction k generalizing s with
  | zero => simp [cycleWordRank]
  | succ k ih =>
      have hk : s + k < p := by omega
      have hk2 : (CycleBridge.cycleWord c p).getI (s + k) = 2 := by
        exact h k (by omega)
      have hstep := Amiya.t2_step_rank_ge_three_of_word c p (s + k) hk hk2
      have hdrop : cycleWordRank c (s + k + 1) =
          cycleWordRank c (s + k) - 2 := by
        simpa [cycleWordRank, Nat.add_assoc] using hstep.2
      have hge : 2 ≤ cycleWordRank c (s + k) := by
        have h3 : 3 ≤ cycleWordRank c (s + k) := by
          simpa [cycleWordRank] using hstep.1
        omega
      have hsucc : cycleWordRank c (s + k) =
          cycleWordRank c (s + k + 1) + 2 := by omega
      have hrest : ∀ i : Nat, i < k →
          (CycleBridge.cycleWord c p).getI (s + i) = 2 := by
        intro i hi
        exact h i (by omega)
      have hih := ih s hrest (by omega)
      have hidx : s + (k + 1) = s + k + 1 := by omega
      calc
        cycleWordRank c s = cycleWordRank c (s + k) + 2 * k := hih
        _ = (cycleWordRank c (s + k + 1) + 2) + 2 * k := by rw [hsucc]
        _ = cycleWordRank c (s + k + 1) + 2 * (k + 1) := by omega
        _ = cycleWordRank c (s + (k + 1)) + 2 * (k + 1) := by
          rw [← hidx]

/-- Exact multiplicative telescope on one maximal `t=2` run.  Unlike a
pointwise rank lower bound, this identity keeps the complete odd parts
of the start and endpoint states, so it can be multiplied over all runs
without assigning an individual budget to any one run. -/
theorem t2_run_exit_mul_four_pow_eq_start_mul_five_pow
    (c p : Nat) (run : T2Run)
    (hmem : run ∈ maxT2Runs (CycleBridge.cycleWord c p)) :
    4 ^ run.length *
        (StringFlow.fiveXPlusOneOrbit 7
          (c + (run.start + run.length)) + 1) =
      5 ^ run.length *
        (StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1) := by
  let w := CycleBridge.cycleWord c p
  let r : Nat → Nat := fun i =>
    StringFlow.fiveXPlusOneOrbit 7 (c + run.start + i)
  have hmem_two : ∀ i : Nat, i < run.length →
      w.getI (run.start + i) = 2 := by
    intro i hi
    have h := maxT2RunsFrom_mem_two w 0 run hmem i hi
    simpa [w] using h
  have hbnd : run.start + run.length ≤ p := by
    have hbnd' := maxT2RunsFrom_bounds w 0 run hmem
    rw [CycleBridge.cycleWord_length] at hbnd'
    simpa [w] using hbnd'
  have hsteps : ∀ i : Nat, i < run.length →
      r (i + 1) = (5 * r i + 1) / 4 ∧
        (5 * r i + 1) % 4 = 0 := by
    intro i hi
    have hb : run.start + i < p := by
      have hb' : run.start + i < run.start + run.length := by omega
      exact lt_of_lt_of_le hb' hbnd
    have hsucc := CycleBridge.wordOrbit_take_succ w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    have hpre1 : StringFlow.Word.wordOrbit (w.take (run.start + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) = r i := by
      dsimp [r, w]
      simpa [Nat.add_assoc] using
        CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i)
          (le_of_lt hb)
    have hpre2 : StringFlow.Word.wordOrbit (w.take (run.start + i + 1))
        (StringFlow.fiveXPlusOneOrbit 7 c) = r (i + 1) := by
      dsimp [r, w]
      simpa [Nat.add_assoc] using
        CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i + 1)
          (by omega)
    have hdvd := UnifiedCoreAudit.wordValid_drop_head w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (CycleBridge.cycleWord_wordValid c p)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    rw [hpre1, hpre2, hmem_two i hi] at hsucc
    rw [hpre1, hmem_two i hi] at hdvd
    constructor
    · simpa using hsucc
    · simpa using hdvd
  have hmul := UnifiedCoreAudit.t2_run_mul r run.length hsteps
  simpa [r, Nat.add_assoc] using hmul

/-- Multiplying compatible per-run identities gives one list-level
telescope.  This is the algebraic compensation mechanism: only the
product over the whole list is constrained. -/
lemma t2RunProductTelescope_list
    (runs : List T2Run) (startFactor exitFactor : T2Run → Nat)
    (hper : ∀ run ∈ runs,
      4 ^ run.length * exitFactor run =
        5 ^ run.length * startFactor run) :
    4 ^ (runs.map (fun run => run.length)).sum *
        (runs.map exitFactor).prod =
      5 ^ (runs.map (fun run => run.length)).sum *
        (runs.map startFactor).prod := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hhead := hper run (by simp)
      have htail : ∀ r ∈ runs,
          4 ^ r.length * exitFactor r =
            5 ^ r.length * startFactor r := by
        intro r hr
        exact hper r (by simp [hr])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [Nat.pow_add, Nat.pow_add]
      calc
        (4 ^ run.length *
              4 ^ (runs.map (fun run => run.length)).sum) *
            (exitFactor run * (runs.map exitFactor).prod) =
            (4 ^ run.length * exitFactor run) *
              (4 ^ (runs.map (fun run => run.length)).sum *
                (runs.map exitFactor).prod) := by ring
        _ = (5 ^ run.length * startFactor run) *
              (5 ^ (runs.map (fun run => run.length)).sum *
                (runs.map startFactor).prod) := by rw [hhead, hi]
        _ = (5 ^ run.length *
              5 ^ (runs.map (fun run => run.length)).sum) *
            (startFactor run * (runs.map startFactor).prod) := by ring

/-- Aggregate product telescope over every maximal `t=2` run of the
real cycle word:

`4^H2 · Π(exit+1) = 5^H2 · Π(start+1)`.

No nonemptiness or pointwise surplus is assumed.  Those are separate
strictness inputs at the later `CycleQb8Input` layer. -/
theorem t2RunProductTelescope (c p : Nat) :
    4 ^ CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) *
        ((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => StringFlow.fiveXPlusOneOrbit 7
            (c + (run.start + run.length)) + 1)).prod =
      5 ^ CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) *
        ((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => StringFlow.fiveXPlusOneOrbit 7
            (c + run.start) + 1)).prod := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  have hper : ∀ run ∈ runs,
      4 ^ run.length *
          (StringFlow.fiveXPlusOneOrbit 7
            (c + (run.start + run.length)) + 1) =
        5 ^ run.length *
          (StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1) := by
    intro run hmem
    exact t2_run_exit_mul_four_pow_eq_start_mul_five_pow
      c p run (by simpa [runs] using hmem)
  have ht := t2RunProductTelescope_list runs
    (fun run => StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1)
    (fun run => StringFlow.fiveXPlusOneOrbit 7
      (c + (run.start + run.length)) + 1) hper
  have hlen : (runs.map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
    simpa [runs, maxT2Runs] using
      maxT2RunsFrom_length_sum (CycleBridge.cycleWord c p) 0
  rw [hlen] at ht
  simpa [runs] using ht

/-- Aggregate start-rank identity over all maximal `t=2` runs of the
real cycle word:

`Σ R(start) = 2 * H2 + Σ R(endpoint)`.

This is the addition-form rank telescope used by the strict aggregate
comparison; it exposes the endpoint ranks instead of hiding them behind
natural-number subtraction. -/
theorem t2RunStartRankSum_eq_two_mul_H2_add_exitRankSum
    (c p : Nat) :
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        ((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => cycleWordRank c (run.start + run.length))).sum := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  have hmap : runs.map (fun run => cycleWordRank c run.start) =
      runs.map (fun run =>
        cycleWordRank c (run.start + run.length) + 2 * run.length) := by
    apply List.map_congr_left
    intro run hmem
    exact t2_run_start_rank_eq_exit_rank_add_two_mul_length
      c p run (by simpa [runs] using hmem)
  have hlen : (runs.map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
    simpa [runs, maxT2Runs] using
      maxT2RunsFrom_length_sum (CycleBridge.cycleWord c p) 0
  have htwo : (runs.map (fun run => 2 * run.length)).sum =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
    rw [← hlen]
    exact List.sum_map_mul_left runs (fun run => run.length) 2
  rw [hmap, List.sum_map_add, htwo]
  simp [runs, Nat.add_comm]

/-- The two-adic valuation is additive on a product of positive natural
numbers.  This local list form lets an aggregate run-start rank bound be
attacked as one product divisibility statement: individual factors may
have rank below their individual budget as long as the other factors
compensate. -/
lemma twoValuation_list_prod_eq_sum (xs : List Nat)
    (hpos : ∀ x ∈ xs, 0 < x) :
    twoValuation xs.prod = (xs.map twoValuation).sum := by
  have hmul : ∀ a b : Nat, 0 < a → 0 < b →
      twoValuation (a * b) = twoValuation a + twoValuation b := by
    intro a b ha hb
    have ha_dec := StringFlow.n_eq_two_pow_mul_oddPart a ha
    have hb_dec := StringFlow.n_eq_two_pow_mul_oddPart b hb
    have ha_odd := StringFlow.oddPart_odd_of_pos a ha
    have hb_odd := StringFlow.oddPart_odd_of_pos b hb
    have hab_odd : (StringFlow.oddPart a * StringFlow.oddPart b) % 2 = 1 := by
      rw [Nat.mul_mod, ha_odd, hb_odd]
    have hab : a * b =
        2 ^ (twoValuation a + twoValuation b) *
          (StringFlow.oddPart a * StringFlow.oddPart b) := by
      calc
        a * b =
            (2 ^ twoValuation a * StringFlow.oddPart a) *
              (2 ^ twoValuation b * StringFlow.oddPart b) := by
                exact congrArg₂ (fun x y => x * y) ha_dec hb_dec
        _ = 2 ^ (twoValuation a + twoValuation b) *
              (StringFlow.oddPart a * StringFlow.oddPart b) := by
                rw [Nat.pow_add]
                ac_rfl
    rw [hab]
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq
      (twoValuation a + twoValuation b)
      (StringFlow.oddPart a * StringFlow.oddPart b) hab_odd
  induction xs with
  | nil =>
      simpa using StringFlow.twoValuation_odd 1 (by norm_num)
  | cons a as ih =>
      have ha : 0 < a := hpos a (by simp)
      have htail : ∀ x ∈ as, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      have has : 0 < as.prod := List.prod_pos htail
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      rw [hmul a as.prod ha has, ih htail]

/-- Product-level form of the aggregate rank target.  The exponent is
the *total* run budget plus one; no factor is required to meet its own
`2 * start + 14` threshold. -/
def t2RunStartProductDivisibility (c p : Nat) : Prop :=
  2 ^ (((maxT2Runs (CycleBridge.cycleWord c p)).map
      (fun run => 2 * run.start + 14)).sum + 1) ∣
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
      (fun run => StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1)).prod

/-- A word containing an actual `2` has positive `riseCountTwo`.
This is the small combinatorial half of the run-nonempty boundary; it
does not assert that an arbitrary closed rise word contains a `2`. -/
lemma riseCountTwo_pos_of_mem_two (ts : List Nat) (hmem : 2 ∈ ts) :
    0 < CycleBridge.riseCountTwo ts := by
  induction ts with
  | nil => simp at hmem
  | cons t ts ih =>
      rcases List.mem_cons.mp hmem with ht | htail
      · subst t
        simp [CycleBridge.riseCountTwo]
      · have hpos := ih htail
        by_cases ht : t = 2
        · subst t
          simp [CycleBridge.riseCountTwo]
        · simp [CycleBridge.riseCountTwo, ht, hpos]

/-- Once an upstream real-orbit argument locates a concrete `t=2`
entry, the maximal-run list is nonempty.  This bridge is intentionally
one-way so that no generic closed-word existence claim is smuggled in. -/
lemma maxT2Runs_nonempty_of_mem_two (ts : List Nat) (hmem : 2 ∈ ts) :
    maxT2Runs ts ≠ [] := by
  intro hempty
  have hempty' : maxT2RunsFrom ts 0 = [] := by
    simpa [maxT2Runs] using hempty
  have hlen := maxT2RunsFrom_length_sum ts 0
  have hzero : CycleBridge.riseCountTwo ts = 0 := by
    rw [hempty'] at hlen
    simpa using hlen.symm
  have hpos := riseCountTwo_pos_of_mem_two ts hmem
  omega

/-- Concrete `CycleQb8Input` boundary bridge.  Its premise is exactly
the upstream fact still to be obtained from `hstart`/`hcycle`: an
actual index of weight two.  No aggregate-rank or hfail conclusion is
used here. -/
theorem cycleQb8Input_t2Runs_nonempty_of_exists_t2_index
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hex : ∃ i : Nat, i < w.length ∧ w.getI i = 2) :
    maxT2Runs (CycleBridge.cycleWord c p) ≠ [] := by
  rcases hex with ⟨i, hi, htwo⟩
  have hmem : 2 ∈ w := by
    rw [List.getI_eq_getElem (l := w) (n := i) hi] at htwo
    rw [← htwo]
    exact List.getElem_mem hi
  rw [← hw]
  exact maxT2Runs_nonempty_of_mem_two w hmem

/-- The strict aggregate product divisibility itself excludes the
empty-run case: for an empty product it would require `2 ∣ 1`.
This makes the boundary dependence explicit in the product route. -/
theorem t2Runs_nonempty_of_product_divisibility
    (c p : Nat) (hdiv : t2RunStartProductDivisibility c p) :
    maxT2Runs (CycleBridge.cycleWord c p) ≠ [] := by
  intro hempty
  norm_num [t2RunStartProductDivisibility, hempty] at hdiv

/-- The plus-one prefix numerator at depth `a` of the concrete cycle
occurrence.  The added `2^W` turns the usual orbit numerator for `y_a`
into the numerator for `y_a + 1`. -/
def cycleWordPrefixPlusOneNumerator (c p a : Nat) : Nat :=
  5 ^ a * StringFlow.fiveXPlusOneOrbit 7 c +
      StringFlow.Word.wordA ((CycleBridge.cycleWord c p).take a) +
    2 ^ StringFlow.wordWeight ((CycleBridge.cycleWord c p).take a)

/-- Exact hcycle-prefix factorization

`N_a = 2^(W_a) * (fiveXPlusOneOrbit 7 (c+a) + 1)`.

This is the orbit identity needed to move aggregate divisibility from
the run-start states to one product of concrete prefix numerators. -/
theorem cycleWordPrefixPlusOneNumerator_eq
    (c p a : Nat) (ha : a ≤ p) :
    cycleWordPrefixPlusOneNumerator c p a =
      2 ^ StringFlow.wordWeight ((CycleBridge.cycleWord c p).take a) *
        (StringFlow.fiveXPlusOneOrbit 7 (c + a) + 1) := by
  let u := (CycleBridge.cycleWord c p).take a
  have hulen : u.length = a := by
    dsimp [u]
    rw [List.length_take_of_le]
    simpa [CycleBridge.cycleWord_length] using ha
  have huvalid : StringFlow.Word.wordValid u
      (StringFlow.fiveXPlusOneOrbit 7 c) := by
    have hsplit : u ++ (CycleBridge.cycleWord c p).drop a =
        CycleBridge.cycleWord c p := by
      dsimp [u]
      exact List.take_append_drop a (CycleBridge.cycleWord c p)
    have hfull := CycleBridge.cycleWord_wordValid c p
    have hparts := (S6Audit.wordValid_append u
      ((CycleBridge.cycleWord c p).drop a)
      (StringFlow.fiveXPlusOneOrbit 7 c)).mp (by simpa [hsplit] using hfull)
    exact hparts.1
  have hid := StringFlow.Word.word_orbit_identity u
    (StringFlow.fiveXPlusOneOrbit 7 c) huvalid
  have hid' :
      2 ^ StringFlow.wordWeight u * StringFlow.Word.wordOrbit u
          (StringFlow.fiveXPlusOneOrbit 7 c) =
        5 ^ a * StringFlow.fiveXPlusOneOrbit 7 c +
          StringFlow.Word.wordA u := by
    rwa [hulen] at hid
  have hpre : StringFlow.Word.wordOrbit u
      (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + a) := by
    dsimp [u]
    exact CycleBridge.cycleWord_prefix_orbit_eq c p a ha
  unfold cycleWordPrefixPlusOneNumerator
  change 5 ^ a * StringFlow.fiveXPlusOneOrbit 7 c +
      StringFlow.Word.wordA u + 2 ^ StringFlow.wordWeight u = _
  calc
    5 ^ a * StringFlow.fiveXPlusOneOrbit 7 c +
          StringFlow.Word.wordA u + 2 ^ StringFlow.wordWeight u =
        2 ^ StringFlow.wordWeight u *
            StringFlow.Word.wordOrbit u
              (StringFlow.fiveXPlusOneOrbit 7 c) +
          2 ^ StringFlow.wordWeight u := by rw [hid']
    _ = 2 ^ StringFlow.wordWeight u *
        (StringFlow.Word.wordOrbit u
          (StringFlow.fiveXPlusOneOrbit 7 c) + 1) := by ring
    _ = 2 ^ StringFlow.wordWeight u *
        (StringFlow.fiveXPlusOneOrbit 7 (c + a) + 1) := by rw [hpre]

/-- Product factorization for a list of run starts.  The individual
prefix weights add in the exponent, while the state factors remain in
one compensating product. -/
lemma cycleWordPrefixPlusOneNumerator_product_eq
    (c p : Nat) (runs : List T2Run)
    (hbnd : ∀ run ∈ runs, run.start ≤ p) :
    (runs.map
        (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod =
      2 ^ (runs.map (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum *
        (runs.map (fun run => StringFlow.fiveXPlusOneOrbit 7
          (c + run.start) + 1)).prod := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hrun : run.start ≤ p := hbnd run (by simp)
      have htail : ∀ r ∈ runs, r.start ≤ p := by
        intro r hr
        exact hbnd r (by simp [hr])
      have hi := ih htail
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [cycleWordPrefixPlusOneNumerator_eq c p run.start hrun, hi,
        Nat.pow_add]
      ring

/-- The precise aggregate prefix-numerator condition left for the
real `CycleQb8Input` argument.  It is one divisibility statement over
all maximal runs; no numerator is assigned its own run budget. -/
def t2RunPrefixNumeratorDivisibility (c p : Nat) : Prop :=
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let weightSum := (runs.map (fun run => StringFlow.wordWeight
    ((CycleBridge.cycleWord c p).take run.start))).sum
  let budgetSum := (runs.map (fun run => 2 * run.start + 14)).sum
  2 ^ (weightSum + budgetSum + 1) ∣
    (runs.map
      (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod

/-- The aggregate prefix-numerator condition cancels the common
`2^ΣW` factor and yields the run-start product divisibility.  This is
the exact cancellation bridge where compensation between runs is
preserved. -/
theorem t2RunStartProductDivisibility_of_prefix_numerators
    (c p : Nat) (hdiv : t2RunPrefixNumeratorDivisibility c p) :
    t2RunStartProductDivisibility c p := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let weightSum := (runs.map (fun run => StringFlow.wordWeight
    ((CycleBridge.cycleWord c p).take run.start))).sum
  let budgetSum := (runs.map (fun run => 2 * run.start + 14)).sum
  let factors := runs.map (fun run =>
    StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1)
  have hbnd : ∀ run ∈ runs, run.start ≤ p := by
    intro run hmem
    have h := maxT2RunsFrom_bounds (CycleBridge.cycleWord c p) 0 run
      (by simpa [runs, maxT2Runs] using hmem)
    rw [CycleBridge.cycleWord_length] at h
    omega
  have hprod :
      (runs.map
        (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod =
        2 ^ weightSum * factors.prod := by
    simpa [weightSum, factors] using
      cycleWordPrefixPlusOneNumerator_product_eq c p runs hbnd
  rcases hdiv with ⟨q, hq⟩
  have hcancel : 2 ^ weightSum * factors.prod =
      2 ^ weightSum * (2 ^ (budgetSum + 1) * q) := by
    rw [← hprod, hq]
    dsimp [weightSum, budgetSum] at hq ⊢
    rw [show
      (runs.map (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum +
            (runs.map (fun run => 2 * run.start + 14)).sum + 1 =
        (runs.map (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum +
          ((runs.map (fun run => 2 * run.start + 14)).sum + 1) by omega]
    rw [Nat.pow_add]
    ring
  have hfactor : factors.prod = 2 ^ (budgetSum + 1) * q := by
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ weightSum) hcancel
  refine ⟨q, ?_⟩
  simpa [t2RunStartProductDivisibility, runs, factors, budgetSum] using hfactor

/-- Exact valuation of the aggregate prefix-numerator product.  The
common prefix weights and the run-start ranks appear as two separate
sums; this is the product form of compensation across runs. -/
theorem t2RunPrefixNumeratorProductValuation_eq (c p : Nat) :
    twoValuation
        (((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod) =
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum +
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let weightSum := (runs.map (fun run => StringFlow.wordWeight
    ((CycleBridge.cycleWord c p).take run.start))).sum
  let factors := runs.map (fun run =>
    StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1)
  have hbnd : ∀ run ∈ runs, run.start ≤ p := by
    intro run hmem
    have h := maxT2RunsFrom_bounds (CycleBridge.cycleWord c p) 0 run
      (by simpa [runs, maxT2Runs] using hmem)
    rw [CycleBridge.cycleWord_length] at h
    omega
  have hprod :
      (runs.map
        (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod =
        2 ^ weightSum * factors.prod := by
    simpa [weightSum, factors] using
      cycleWordPrefixPlusOneNumerator_product_eq c p runs hbnd
  have hfactors_pos : ∀ x ∈ factors, 0 < x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨run, _hrun, rfl⟩
    positivity
  have hfactorProd_pos : 0 < factors.prod := List.prod_pos hfactors_pos
  have hfactorVal : twoValuation factors.prod =
      (runs.map (fun run => cycleWordRank c run.start)).sum := by
    rw [twoValuation_list_prod_eq_sum factors hfactors_pos]
    dsimp [factors]
    rw [List.map_map]
    rfl
  rw [show ((maxT2Runs (CycleBridge.cycleWord c p)).map
      (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod =
      (runs.map
        (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod by rfl]
  rw [hprod]
  rw [StringFlow.Lte.twoValuation_mul_two_pow weightSum
    factors.prod hfactorProd_pos]
  rw [hfactorVal]

/-- One aggregate product divisibility gives the required strict
run-start rank sum.  This is the compensation interface for the real
7-orbit prefix argument: valuation can move between different run-start
factors before the final sum is compared. -/
theorem runStartRankSum_gt_boundSum_of_product_divisibility
    (c p : Nat) (hdiv : t2RunStartProductDivisibility c p) :
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => 2 * run.start + 14)).sum <
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let factors := runs.map
    (fun run => StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1)
  have hfactors_pos : ∀ x ∈ factors, 0 < x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨run, _hrun, rfl⟩
    positivity
  have hprod_pos : 0 < factors.prod := List.prod_pos hfactors_pos
  have hexp : ((runs.map (fun run => 2 * run.start + 14)).sum + 1) ≤
      twoValuation factors.prod := by
    apply (StringFlow.Lte.twoValuation_ge_iff_dvd_pow factors.prod
      ((runs.map (fun run => 2 * run.start + 14)).sum + 1) hprod_pos).mpr
    simpa [t2RunStartProductDivisibility, runs, factors] using hdiv
  have hval : twoValuation factors.prod =
      (runs.map (fun run => cycleWordRank c run.start)).sum := by
    rw [twoValuation_list_prod_eq_sum factors hfactors_pos]
    dsimp [factors]
    rw [List.map_map]
    rfl
  rw [hval] at hexp
  simpa [runs] using (show
    (runs.map (fun run => 2 * run.start + 14)).sum <
      (runs.map (fun run => cycleWordRank c run.start)).sum by omega)

/-- Per-block recovery budget: the exact per-block form of
`cycleRiseBlockChargeSum_add_residualSum_eq_two_mul_H2_add_c3WeightSum`,
needed for the termwise aggregation of the `U < L` leg. -/
theorem cycleRiseBlockCharge_add_residualSum_eq_two_mul_H2_add_c3WeightSum_per_block
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockCharge d r +
        CycleBridge.cycleRiseBlockC3ResidualSum d r =
      2 * CycleBridge.riseCountTwo (d.suffixWord r) +
        (d.c3Word r).sum := by
  have hper := cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two h d r hr
  have hc3 := CycleBridge.cycleRiseBlockC3ChainRankGain d r hr
  have hc3' : CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum =
      2 + CycleBridge.cycleRiseBlockC3ResidualSum d r := by
    simpa [CycleBridge.cycleRiseBlockC3ResidualSum] using hc3
  omega

/-- Per-run endpoint rearrangement: the `U` term splits as
`2·endpoint − 2·length + 12`.  Adding `2·length` avoids `Nat`
subtraction in the summed form. -/
lemma run_endpoint_rearrange
    (ts : List Nat) (run : T2Run)
    (_hmem : run ∈ maxT2Runs ts) :
    2 * run.start + 12 + 2 * run.length =
      2 * (run.start + run.length) + 12 := by
  omega

/-- Summed endpoint form of the `U` side:
`U + 2·H2 = 2·Σ(endpoint) + 12·R`.  Combined with
`t2RunRankSum_eq_two_mul_riseCountTwo`, the target `U < 2H2` becomes
`Σ(endpoint + 6) < 2H2`. -/
lemma t2RunBoundSum_add_two_mul_H2_eq_two_endpoint_sum_add_twelve_R
    (c p : Nat) :
    t2RunBoundSum c p +
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) =
      2 * ((maxT2Runs (CycleBridge.cycleWord c p)).map
            (fun run => run.start + run.length)).sum +
        12 * (maxT2Runs (CycleBridge.cycleWord c p)).length := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  have hlen : (runs.map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
    simpa [runs, maxT2Runs] using
      maxT2RunsFrom_length_sum (CycleBridge.cycleWord c p) 0
  have hper : ∀ run ∈ runs, 2 * run.start + 12 + 2 * run.length =
      2 * (run.start + run.length) + 12 := by
    intro run hmem
    omega
  have hleft : t2RunBoundSum c p +
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) =
      (runs.map (fun run => 2 * run.start + 12 + 2 * run.length)).sum := by
    unfold t2RunBoundSum
    rw [← hlen]
    rw [← List.sum_map_mul_left runs (fun run => run.length) 2]
    rw [← List.sum_map_add]
  have hsum : (runs.map
        (fun run => 2 * run.start + 12 + 2 * run.length)).sum =
      2 * (runs.map (fun run => run.start + run.length)).sum +
        12 * runs.length := by
    have hmap : (runs.map
          (fun run => 2 * run.start + 12 + 2 * run.length)) =
        (runs.map (fun run => 2 * (run.start + run.length) + 12)) := by
      refine List.map_congr_left ?_
      intro run hmem
      exact hper run hmem
    rw [hmap]
    rw [List.sum_map_add]
    rw [List.sum_map_mul_left runs (fun run => run.start + run.length) 2]
    simp [List.sum_replicate, Nat.mul_comm]
  rw [hleft, hsum]

/-- Sum over non-`2` positions with their global index plus six.  This
is the position side of the endpoint rearrangement: every maximal run's
endpoint is a distinct non-`2` position, so `Σ(endpoint + 6)` is
bounded by this sum. -/
def nonTwoSumFrom : List Nat → Nat → Nat
  | [], _ => 0
  | t :: ts, k => (if t = 2 then 0 else k + 6) + nonTwoSumFrom ts (k + 1)

/-- Dropping a leading run of twos does not change the non-`2`
position sum. -/
lemma nonTwoSumFrom_drop_leading_twos (ts : List Nat) (k L : Nat)
    (hL : L ≤ ts.length)
    (hall : ∀ i : Nat, i < L → ts.getI i = 2) :
    nonTwoSumFrom ts k = nonTwoSumFrom (ts.drop L) (k + L) := by
  induction L generalizing ts k with
  | zero => simp
  | succ L ih =>
      cases ts with
      | nil => simp at hL
      | cons t rest =>
          have ht : t = 2 := by
            have h0 := hall 0 (by omega)
            simpa using h0
          have htail : ∀ i : Nat, i < L → rest.getI i = 2 := by
            intro i hi
            have h := hall (i + 1) (by omega)
            simpa [List.getI_cons_succ] using h
          have hL' : L ≤ rest.length := by
            have hlen : L + 1 ≤ rest.length + 1 := by simpa using hL
            omega
          have hdrop : (t :: rest).drop (L + 1) = rest.drop L := by
            rfl
          calc
            nonTwoSumFrom (t :: rest) k = nonTwoSumFrom rest (k + 1) := by
              simp [nonTwoSumFrom, ht]
            _ = nonTwoSumFrom (rest.drop L) (k + 1 + L) := by
              exact ih rest (k + 1) hL' htail
            _ = nonTwoSumFrom ((t :: rest).drop (L + 1)) (k + (L + 1)) := by
              rw [hdrop]
              congr 1
              omega

/-- The leading `t=2` run stops exactly before a non-`2` entry: the
entry immediately after `takeWhile t2Pred` is not two whenever it is
in range. -/
lemma takeWhile_two_stop (ts : List Nat) :
    ∀ i : Nat, i = (List.takeWhile t2Pred ts).length →
      i < ts.length → ts.getI i ≠ 2 := by
  induction ts with
  | nil => intro i hi hlt; simp at hlt
  | cons t ts ih =>
      by_cases ht : t = 2
      · have hb : t2Pred t = true := by
          unfold t2Pred
          exact decide_eq_true ht
        rw [List.takeWhile_cons_of_pos hb]
        intro i hi hlt
        cases i with
        | zero =>
            simp at hi
        | succ i =>
            have hi' : i = (List.takeWhile t2Pred ts).length := by
              simpa using hi
            have hlt' : i < ts.length := by
              simpa using hlt
            have hstop := ih i hi' hlt'
            rw [List.getI_cons_succ]
            exact hstop
      · have hb : t2Pred t = false := by
          unfold t2Pred
          exact decide_eq_false ht
        have hb' : ¬ t2Pred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        rw [List.takeWhile_cons_of_neg hb']
        intro i hi hlt
        cases i with
        | zero =>
            rw [List.getI_cons_zero]
            exact ht
        | succ i => simp at hi

/-- Dropping a prefix preserves the non-`2` property of the last entry
whenever the original last entry is not two. -/
lemma last_ne_two_of_drop (ts : List Nat) (k : Nat)
    (hle : k ≤ ts.length)
    (hlast : ts = [] ∨ ts.getI (ts.length - 1) ≠ 2) :
    ts.drop k = [] ∨ (ts.drop k).getI ((ts.drop k).length - 1) ≠ 2 := by
  by_cases hdrop : ts.drop k = []
  · exact Or.inl hdrop
  · right
    have hpos : 0 < (ts.drop k).length := List.length_pos_iff.mpr hdrop
    have hget := getI_drop ts k ((ts.drop k).length - 1)
    have hidx : k + ((ts.drop k).length - 1) = ts.length - 1 := by
      rw [List.length_drop]
      rw [List.length_drop] at hpos
      omega
    rw [hget, hidx]
    rcases hlast with hnil | hlast2
    · exfalso
      rw [hnil] at hdrop
      simp at hdrop
    · exact hlast2

/-- Every maximal `t=2` run contributes at most its endpoint position
to the non-`2` position sum: run endpoints are distinct non-`2`
positions whenever the list does not end in a `2`. -/
lemma endpoint_sum_le_nonTwoSumFrom (ts : List Nat) (k : Nat)
    (hlast : ts = [] ∨ ts.getI (ts.length - 1) ≠ 2) :
    ((maxT2RunsFrom ts k).map (fun run => run.start + run.length + 6)).sum ≤
      nonTwoSumFrom ts k := by
  revert k
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro k
      cases ts with
      | nil => simp [maxT2RunsFrom, nonTwoSumFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · subst t
            let L := (List.takeWhile t2Pred (2 :: rest)).length
            have hLpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred 2 = true := by decide
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hLle : L ≤ (2 :: rest).length := takeWhile_two_length_le (2 :: rest)
            have hLlt : L < (2 :: rest).length := by
              rcases hlast with hnil | hlast2
              · simp at hnil
              · by_contra hnot
                have hle : (2 :: rest).length ≤ L := Nat.le_of_not_gt hnot
                have hLeq : L = (2 :: rest).length := le_antisymm hLle hle
                have hmem2 : (2 :: rest).getI ((2 :: rest).length - 1) = 2 := by
                  have hidx : (2 :: rest).length - 1 < L := by omega
                  have hidx' : (2 :: rest).length - 1 <
                      (List.takeWhile t2Pred (2 :: rest)).length := by
                    simpa [L] using hidx
                  exact takeWhile_two_getI (2 :: rest) ((2 :: rest).length - 1) hidx'
                exact hlast2 hmem2
            have hlt : ((2 :: rest).drop L).length < (2 :: rest).length := by
              rw [List.length_drop]
              omega
            have hstop : (2 :: rest).getI L ≠ 2 := by
              have hbnd : L < (2 :: rest).length := by omega
              have h := takeWhile_two_stop (2 :: rest) L (by rfl) hbnd
              exact h
            have hhead : ((2 :: rest).drop L).getI 0 ≠ 2 := by
              have hget := getI_drop (2 :: rest) L 0
              have hget' : ((2 :: rest).drop L).getI 0 = (2 :: rest).getI L := by
                simpa [Nat.add_comm] using hget
              rwa [← hget'] at hstop
            have hdrop_last1 := last_ne_two_of_drop (2 :: rest) (L + 1) (by omega) hlast
            have hlt1 : ((2 :: rest).drop (L + 1)).length < (2 :: rest).length := by
              rw [List.length_drop]
              have hLle1 : L + 1 ≤ (2 :: rest).length := by omega
              omega
            have hih := ih ((2 :: rest).drop (L + 1)) hlt1 hdrop_last1 (k + (L + 1))
            have hdrop0 : nonTwoSumFrom (2 :: rest) k =
                nonTwoSumFrom ((2 :: rest).drop L) (k + L) := by
              exact nonTwoSumFrom_drop_leading_twos (2 :: rest) k L (le_of_lt hLlt)
                (by
                  intro i hi
                  exact takeWhile_two_getI (2 :: rest) i (by simpa [L] using hi))
            have hdrop1 : nonTwoSumFrom ((2 :: rest).drop L) (k + L) =
                (k + L + 6) +
                  nonTwoSumFrom ((2 :: rest).drop (L + 1)) (k + (L + 1)) := by
              have hnonempty : (2 :: rest).drop L ≠ [] := by
                intro hnil
                have hlen : ((2 :: rest).drop L).length = 0 := by rw [hnil]; rfl
                rw [List.length_drop] at hlen
                omega
              cases hdrop : (2 :: rest).drop L with
              | nil => exact False.elim (hnonempty hdrop)
              | cons a as =>
                  have ha : a ≠ 2 := by
                    have hget : (2 :: rest).drop L = a :: as := hdrop
                    have hget0 : (a :: as).getI 0 = a := rfl
                    rw [hdrop] at hhead
                    simpa [hget0] using hhead
                  have hdrop_eq : (2 :: rest).drop (L + 1) = as := by
                    have hdrop_drop : ((2 :: rest).drop L).drop 1 =
                        (2 :: rest).drop (L + 1) := by
                      rw [List.drop_drop]
                    rw [← hdrop_drop, hdrop]
                    simp
                  have hk : k + L + 6 = (k + L) + 6 := by omega
                  simp [nonTwoSumFrom, ha, hdrop_eq, Nat.add_assoc]
            have hmain : ((maxT2RunsFrom (2 :: rest) k).map
                (fun run => run.start + run.length + 6)).sum =
              (k + L + 6) +
                ((maxT2RunsFrom ((2 :: rest).drop (L + 1)) (k + (L + 1))).map
                  (fun run => run.start + run.length + 6)).sum := by
              rw [maxT2RunsFrom]
              rw [dif_pos (by simp : 2 = 2)]
              have hdropL : (2 :: rest).drop L =
                  (2 :: rest).drop L := rfl
              -- the recorded run is `{ start := k, length := L }`, the tail
              -- is scanned from `(2 :: rest).drop L` at base `k + L`; its
              -- first element is non-`2`, so the recursive scan drops it and
              -- continues at base `k + L + 1`.
              have htail : maxT2RunsFrom ((2 :: rest).drop L) (k + L) =
                  maxT2RunsFrom ((2 :: rest).drop (L + 1)) (k + (L + 1)) := by
                cases hdrop : (2 :: rest).drop L with
                | nil =>
                    have hlen : ((2 :: rest).drop L).length = 0 := by rw [hdrop]; rfl
                    have hLeq : L = (2 :: rest).length := by
                      rw [List.length_drop] at hlen
                      omega
                    have hdrop2 : (2 :: rest).drop (L + 1) = [] :=
                      (List.drop_eq_nil_iff).mpr (by omega)
                    simp [maxT2RunsFrom, hdrop2]
                | cons a as =>
                    have ha : a ≠ 2 := by
                      rw [hdrop] at hhead
                      simpa using hhead
                    have hdrop_eq : (2 :: rest).drop (L + 1) = as := by
                      have hdrop_drop : ((2 :: rest).drop L).drop 1 =
                          (2 :: rest).drop (L + 1) := by
                        rw [List.drop_drop]
                      rw [← hdrop_drop, hdrop]
                      simp
                    rw [hdrop_eq]
                    rw [maxT2RunsFrom]
                    rw [dif_neg ha]
                    congr 1
              simp [L, htail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            rw [hmain]
            rw [hdrop0, hdrop1]
            omega
          · rcases hlast with hnil | hlast2
            · simp at hnil
            · have hlast_rest : rest = [] ∨ rest.getI (rest.length - 1) ≠ 2 := by
                by_cases hrest : rest = []
                · exact Or.inl hrest
                · right
                  have hrest_pos : 0 < rest.length := List.length_pos_iff.mpr hrest
                  have hidx : (t :: rest).length - 1 = rest.length := by simp
                  have hget : (t :: rest).getI rest.length = rest.getI (rest.length - 1) := by
                    have hidx2 : rest.length = (rest.length - 1) + 1 := by omega
                    rw [hidx2]
                    exact List.getI_cons_succ t rest (rest.length - 1)
                  have hlast' : (t :: rest).getI ((t :: rest).length - 1) ≠ 2 := hlast2
                  rwa [hidx, hget] at hlast'
              have hlt_rest : rest.length < (t :: rest).length := by simp
              have hih := ih rest hlt_rest hlast_rest (k + 1)
              have hmain : ((maxT2RunsFrom (t :: rest) k).map
                  (fun run => run.start + run.length + 6)).sum =
                ((maxT2RunsFrom rest (k + 1)).map
                  (fun run => run.start + run.length + 6)).sum := by
                rw [maxT2RunsFrom]
                rw [dif_neg ht]
              have hr : nonTwoSumFrom (t :: rest) k = (k + 6) + nonTwoSumFrom rest (k + 1) := by
                simp [nonTwoSumFrom, ht]
              rw [hmain, hr]
              omega

/-- Every recorded maximal `t=2` run stops before a non-`2` entry. -/
lemma maxT2RunsFrom_next_not_two (ts : List Nat) (base : Nat) :
    ∀ run ∈ maxT2RunsFrom ts base,
      run.start + run.length < base + ts.length →
      ts.getI (run.start + run.length - base) ≠ 2 := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length := takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            intro run hmem
            have hmem0 : run = { start := base, length := L } ∨
                run ∈ maxT2RunsFrom ((t :: rest).drop L) (base + L) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_pos ht] at hmem'
              simpa [List.mem_cons] using hmem'
            intro hbnd
            rcases hmem0 with hrfl | hmem'
            · subst run
              have hLlt : L < (t :: rest).length := by
                have : base + L < base + (t :: rest).length := hbnd
                omega
              have hstop := takeWhile_two_stop (t :: rest) L rfl hLlt
              have hget : (t :: rest).getI L =
                  (t :: rest).getI (base + L - base) := by
                congr 1
                omega
              rwa [hget] at hstop
            · have hbnd' : run.start + run.length < (base + L) +
                  ((t :: rest).drop L).length := by
                have hsum : base + (t :: rest).length =
                    (base + L) + ((t :: rest).drop L).length := by
                  rw [List.length_drop]
                  have hLle : L ≤ (t :: rest).length := takeWhile_two_length_le (t :: rest)
                  omega
                rwa [hsum] at hbnd
              have hrec := hih run hmem' hbnd'
              have hget : ((t :: rest).drop L).getI
                  (run.start + run.length - (base + L)) =
                  (t :: rest).getI (run.start + run.length - base) := by
                have hge : base + L ≤ run.start :=
                  maxT2RunsFrom_start_ge ((t :: rest).drop L) (base + L) run hmem'
                rw [getI_drop (t :: rest) L (run.start + run.length - (base + L))]
                congr 1
                omega
              rwa [hget] at hrec
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            intro run hmem
            have hmem0 : run ∈ maxT2RunsFrom rest (base + 1) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_neg ht] at hmem'
              exact hmem'
            intro hbnd
            have hbnd' : run.start + run.length < (base + 1) + rest.length := by
              have hsum : base + (t :: rest).length = (base + 1) + rest.length := by
                simp [Nat.add_comm, Nat.add_left_comm]
              rwa [hsum] at hbnd
            have hrec := hih run hmem0 hbnd'
            have hget : rest.getI (run.start + run.length - (base + 1)) =
                (t :: rest).getI (run.start + run.length - base) := by
              have hge : base + 1 ≤ run.start :=
                maxT2RunsFrom_start_ge rest (base + 1) run hmem0
              have hdrop_eq : rest = (t :: rest).drop 1 := by simp
              rw [hdrop_eq]
              rw [getI_drop (t :: rest) 1 (run.start + run.length - (base + 1))]
              congr 1
              omega
            rwa [hget] at hrec

/-- `Σ (p − f x) + Σ f x = length·p` when every value is below `p`. -/
lemma sum_map_sub_const_add {α : Type} (l : List α) (f : α → Nat) (p : Nat)
    (h : ∀ x ∈ l, f x ≤ p) :
    (l.map (fun x => p - f x)).sum + (l.map f).sum = l.length * p := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : f a ≤ p := h a (by simp)
      have htail : ∀ x ∈ as, f x ≤ p := by
        intro x hx
        exact h x (by simp [hx])
      have htail_eq := ih htail
      calc
        ((a :: as).map (fun x => p - f x)).sum + ((a :: as).map f).sum
            = (p - f a) + (as.map (fun x => p - f x)).sum +
                (f a + (as.map f).sum) := by
                simp [List.map_cons, List.sum_cons, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm]
        _ = (p - f a + f a) +
              ((as.map (fun x => p - f x)).sum + (as.map f).sum) := by
              ac_rfl
        _ = p + as.length * p := by
              rw [Nat.sub_add_cancel ha, htail_eq]
        _ = (as.length + 1) * p := by ring

/-- `Σ (p − f x) = length·p − Σ f x` when every value is below `p`. -/
lemma sum_map_sub_const {α : Type} (l : List α) (f : α → Nat) (p : Nat)
    (h : ∀ x ∈ l, f x ≤ p) :
    (l.map (fun x => p - f x)).sum =
      l.length * p - (l.map f).sum := by
  have hadd := sum_map_sub_const_add l f p h
  have hle : (l.map f).sum ≤ l.length * p := by
    have hmap : l.map (fun _ => p) = List.replicate l.length p := by
      rw [List.map_const']
    have h := List.sum_le_sum (by
      intro x hx
      have hx' : x ∈ l := by simpa using hx
      exact h x hx')
    rwa [hmap, List.sum_replicate] at h
  omega

/-- Aggregate `Σstart ≤ R·(base+len) − Σlength`: the run starts are
bounded by the end of the list minus each run's own length.  This is
the combinatorial upper bound on the `Σ(2·start + 12)` side. -/
lemma sum_starts_le_mul_length_sub_twos (ts : List Nat) (base : Nat) :
    ((maxT2RunsFrom ts base).map (fun run => run.start)).sum ≤
      (maxT2RunsFrom ts base).length * (base + ts.length) -
        ((maxT2RunsFrom ts base).map (fun run => run.length)).sum := by
  let runs := maxT2RunsFrom ts base
  have hle : ∀ run ∈ runs, run.start ≤ base + ts.length - run.length := by
    intro run hmem
    have hbnd := maxT2RunsFrom_bounds ts base run hmem
    omega
  have hsum : (runs.map (fun run => run.start)).sum ≤
      (runs.map (fun run => base + ts.length - run.length)).sum :=
    List.sum_le_sum hle
  have hsub : (runs.map (fun run => base + ts.length - run.length)).sum =
      runs.length * (base + ts.length) -
        (runs.map (fun run => run.length)).sum := by
    have hL : ∀ run ∈ runs, run.length ≤ base + ts.length := by
      intro run hmem
      have hbnd := maxT2RunsFrom_bounds ts base run hmem
      omega
    simpa using sum_map_sub_const runs (fun run => run.length)
      (base + ts.length) hL
  rwa [hsub] at hsum

/-- Every recorded maximal `t=2` run is nonempty. -/
lemma maxT2RunsFrom_length_pos (ts : List Nat) (base : Nat) :
    ∀ run ∈ maxT2RunsFrom ts base, 0 < run.length := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length := takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            intro run hmem
            have hmem0 : run = { start := base, length := L } ∨
                run ∈ maxT2RunsFrom ((t :: rest).drop L) (base + L) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_pos ht] at hmem'
              simpa [List.mem_cons] using hmem'
            rcases hmem0 with hrfl | hmem'
            · subst run
              simpa [L] using hpos
            · exact hih run hmem'
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            intro run hmem
            have hmem0 : run ∈ maxT2RunsFrom rest (base + 1) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_neg ht] at hmem'
              exact hmem'
            exact hih run hmem0

/-- Every `t=2` entry lies inside exactly one recorded maximal run.
Well-founded on `a`: either the head run covers it, or the index is
strictly smaller after dropping the head run / skipping a non-`2`. -/
theorem maxT2RunsFrom_covering (ts : List Nat) (base a : Nat)
    (ha : a < ts.length) (ht : ts.getI a = 2) :
    ∃ run ∈ maxT2RunsFrom ts base,
      run.start ≤ base + a ∧ base + a < run.start + run.length := by
  cases ts with
  | nil => simp at ha
  | cons t rest =>
      by_cases ha0 : a = 0
      · subst a
        have ht0 : t = 2 := by
          simpa [List.getI_cons_zero] using ht
        let L := (List.takeWhile t2Pred (t :: rest)).length
        have hLpos : 0 < L := by
          dsimp [L]
          have hb : t2Pred t = true := by
            unfold t2Pred
            exact decide_eq_true ht0
          rw [List.takeWhile_cons_of_pos hb]
          simp
        refine ⟨{ start := base, length := L }, ?_, ?_, ?_⟩
        · rw [maxT2RunsFrom]
          rw [dif_pos ht0]
          simp [L]
        · simp
        · dsimp
          omega
      · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
        by_cases ht0 : t = 2
        · let L := (List.takeWhile t2Pred (t :: rest)).length
          have hLpos : 0 < L := by
            dsimp [L]
            have hb : t2Pred t = true := by
              unfold t2Pred
              exact decide_eq_true ht0
            rw [List.takeWhile_cons_of_pos hb]
            simp
          have hLle : L ≤ (t :: rest).length :=
            takeWhile_two_length_le (t :: rest)
          by_cases haL : a < L
          · refine ⟨{ start := base, length := L }, ?_, ?_, ?_⟩
            · rw [maxT2RunsFrom]
              rw [dif_pos ht0]
              simp [L]
            · simp
            · dsimp
              omega
          · have hgeL : L ≤ a := Nat.le_of_not_gt haL
            have ha' : a - L < ((t :: rest).drop L).length := by
              rw [List.length_drop]
              omega
            have htdrop : ((t :: rest).drop L).getI (a - L) = 2 := by
              rw [getI_drop (t :: rest) L (a - L)]
              have hidx : L + (a - L) = a := Nat.add_sub_of_le hgeL
              simpa [hidx] using ht
            have hih := maxT2RunsFrom_covering
              ((t :: rest).drop L) (base + L) (a - L) ha' htdrop
            rcases hih with ⟨run, hmem, hle, hgt⟩
            refine ⟨run, ?_, ?_, ?_⟩
            · rw [maxT2RunsFrom]
              rw [dif_pos ht0]
              simp [L, List.mem_cons, hmem]
            · have hsum : base + L + (a - L) = base + a := by omega
              simpa [hsum] using hle
            · have hsum : base + L + (a - L) = base + a := by omega
              simpa [hsum] using hgt
        · have ha' : a - 1 < rest.length := by
            have hlt : a < rest.length + 1 := by simpa using ha
            omega
          have htdrop : rest.getI (a - 1) = 2 := by
            have hdrop_raw := getI_drop (t :: rest) 1 (a - 1)
            have hdrop : rest.getI (a - 1) =
                (t :: rest).getI (1 + (a - 1)) := by
              simpa using hdrop_raw
            have hidx : 1 + (a - 1) = a := by omega
            rw [hdrop]
            rw [hidx]
            exact ht
          have hih := maxT2RunsFrom_covering
            rest (base + 1) (a - 1) ha' htdrop
          rcases hih with ⟨run, hmem, hle, hgt⟩
          refine ⟨run, ?_, ?_, ?_⟩
          · rw [maxT2RunsFrom]
            rw [dif_neg ht0]
            exact hmem
          · have hsum : base + 1 + (a - 1) = base + a := by omega
            simpa [hsum] using hle
          · have hsum : base + 1 + (a - 1) = base + a := by omega
            simpa [hsum] using hgt
termination_by a
decreasing_by
  all_goals simp_wf; omega

/-- Concrete exit-rank fact on the `hcycle` word: every maximal `t=2`
run ends at a state whose rank is exactly one or two.  The wrap case
`run.start + run.length = p` is excluded because the last step of a
real closed QB-8 word is a C3 step (`cycleQb8Input_last_step_c3`). -/
theorem t2_run_exit_rank_mem_one_two
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (_hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (run : T2Run) (hmem : run ∈ maxT2Runs (CycleBridge.cycleWord c p)) :
    cycleWordRank c (run.start + run.length) = 1 ∨
    cycleWordRank c (run.start + run.length) = 2 := by
  let wc := CycleBridge.cycleWord c p
  have hmem' : run ∈ maxT2Runs wc := by simpa [wc] using hmem
  have hbnd : run.start + run.length ≤ p := by
    have hbnd' := maxT2RunsFrom_bounds wc 0 run hmem'
    rw [CycleBridge.cycleWord_length] at hbnd'
    simpa [wc] using hbnd'
  have he_lt : run.start + run.length < p := by
    by_contra hnot
    have he_le : p ≤ run.start + run.length := Nat.le_of_not_gt hnot
    have he_eq : run.start + run.length = p := le_antisymm hbnd he_le
    have hLpos : 0 < run.length := maxT2RunsFrom_length_pos wc 0 run hmem'
    have hp1 : p - 1 < p := by
      have hP2 : 2 ≤ p := by
        rw [← CycleBridge.cycleWord_length c p]
        have hwlen : w.length = p := by rw [hw, CycleBridge.cycleWord_length]
        have hP2' : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
        rw [← h.hlength, hw] at hP2'
        simpa [hwlen] using hP2'
      omega
    have hlast : (CycleBridge.cycleWord c p).getI (p - 1) = 2 := by
      have hmem_two := maxT2RunsFrom_mem_two wc 0 run hmem' (run.length - 1) (by omega)
      have hidx : run.start + (run.length - 1) = p - 1 := by
        omega
      simpa [wc, hidx] using hmem_two
    have hc3 : 3 ≤ w.getI (P - 1) := CycleBridge.cycleQb8Input_last_step_c3 h
    have hc3' : 3 ≤ (CycleBridge.cycleWord c p).getI (p - 1) := by
      rw [← hw]
      have hP : P = p := by
        rw [← h.hlength, hw, CycleBridge.cycleWord_length]
      simpa [hP] using hc3
    omega
  have hnext_ne_two : (CycleBridge.cycleWord c p).getI (run.start + run.length) ≠ 2 := by
    have hbnd' : run.start + run.length < 0 + wc.length := by
      rw [CycleBridge.cycleWord_length]
      simpa [wc] using he_lt
    have hstop := maxT2RunsFrom_next_not_two wc 0 run hmem' hbnd'
    have hget : wc.getI (run.start + run.length - 0) =
        wc.getI (run.start + run.length) := by
      rfl
    rwa [hget] at hstop
  have hge1 : 1 ≤ (CycleBridge.cycleWord c p).getI (run.start + run.length) := by
    have hmem_entry : (CycleBridge.cycleWord c p).getI (run.start + run.length) ∈
        CycleBridge.cycleWord c p := by
      rw [List.getI_eq_getElem (l := CycleBridge.cycleWord c p)
        (n := run.start + run.length) (by
          rw [CycleBridge.cycleWord_length]
          exact he_lt)]
      exact List.getElem_mem (by
        rw [CycleBridge.cycleWord_length]
        exact he_lt)
    exact CycleBridge.cycleWord_mem_ge_one c p hmem_entry
  have hcases : (CycleBridge.cycleWord c p).getI (run.start + run.length) = 1 ∨
      3 ≤ (CycleBridge.cycleWord c p).getI (run.start + run.length) := by
    have hne2 : (CycleBridge.cycleWord c p).getI (run.start + run.length) ≠ 2 := hnext_ne_two
    omega
  rcases hcases with h1 | hge3
  · left
    have hr := t1_step_rank_eq_one c p (run.start + run.length) he_lt h1
    simpa [cycleWordRank] using hr
  · right
    have hr := c3_step_rank_eq_two c p (run.start + run.length) he_lt hge3
    simpa [cycleWordRank] using hr

/-- Direct aggregate rank sandwich for the real closed word.  Every
endpoint contributes either one or two units, hence

`2H2 + #runs ≤ Σ R(start) ≤ 2H2 + 2#runs`.

This is a genuine aggregate lower bound and does not impose a
pointwise budget on any run. -/
theorem t2RunStartRankSum_between
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        (maxT2Runs (CycleBridge.cycleWord c p)).length ≤
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum ∧
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum ≤
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        2 * (maxT2Runs (CycleBridge.cycleWord c p)).length := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let exits := (runs.map
    (fun run => cycleWordRank c (run.start + run.length))).sum
  have hstart : (runs.map (fun run => cycleWordRank c run.start)).sum =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) + exits := by
    simpa [runs, exits] using
      t2RunStartRankSum_eq_two_mul_H2_add_exitRankSum c p
  have hexit_lower : runs.length ≤ exits := by
    have hper : ∀ run ∈ runs,
        1 ≤ cycleWordRank c (run.start + run.length) := by
      intro run hmem
      rcases t2_run_exit_rank_mem_one_two h c p hw hm run
        (by simpa [runs] using hmem) with hr | hr <;> omega
    have hsum := List.sum_le_sum hper
    have hones : (runs.map (fun _run => 1)).sum = runs.length := by simp
    rw [hones] at hsum
    simpa [exits] using hsum
  have hexit_upper : exits ≤ 2 * runs.length := by
    have hper : ∀ run ∈ runs,
        cycleWordRank c (run.start + run.length) ≤ 2 := by
      intro run hmem
      rcases t2_run_exit_rank_mem_one_two h c p hw hm run
        (by simpa [runs] using hmem) with hr | hr <;> omega
    have hsum := List.sum_le_sum hper
    have htwos : (runs.map (fun _run => 2)).sum = 2 * runs.length := by
      simp [Nat.mul_comm]
    rw [htwos] at hsum
    simpa [exits] using hsum
  constructor
  · change 2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
      runs.length ≤
        (runs.map (fun run => cycleWordRank c run.start)).sum
    rw [hstart]
    exact Nat.add_le_add_left hexit_lower _
  · change (runs.map (fun run => cycleWordRank c run.start)).sum ≤
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        2 * runs.length
    rw [hstart]
    exact Nat.add_le_add_left hexit_upper _

/-- The aggregate penalty for a maximal `t=2` run exiting at rank one
rather than rank two.  On a real closed cycle word every exit rank is
`1` or `2`, so each summand is exactly `1` or `0` respectively. -/
def t2RunExitPenalty (c p : Nat) : Nat :=
  ((maxT2Runs (CycleBridge.cycleWord c p)).map
    (fun run => 2 - cycleWordRank c (run.start + run.length))).sum

/-- Exact compensated rank telescope over all maximal `t=2` runs:

`sum startRank + sum (2 - exitRank) = 2 * H2 + 2 * numberOfRuns`.

The penalty keeps the compensation between runs explicit.  In
particular, no run is required to meet its depth budget on its own. -/
theorem t2RunStartRankSum_add_exitPenalty
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum +
        t2RunExitPenalty c p =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        2 * (maxT2Runs (CycleBridge.cycleWord c p)).length := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let exits := (runs.map
    (fun run => cycleWordRank c (run.start + run.length))).sum
  let penalty := (runs.map
    (fun run => 2 - cycleWordRank c (run.start + run.length))).sum
  have hstart : (runs.map (fun run => cycleWordRank c run.start)).sum =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) + exits := by
    simpa [runs, exits] using
      t2RunStartRankSum_eq_two_mul_H2_add_exitRankSum c p
  have hexit_le : ∀ run ∈ runs,
      cycleWordRank c (run.start + run.length) ≤ 2 := by
    intro run hmem
    rcases t2_run_exit_rank_mem_one_two h c p hw hm run
      (by simpa [runs] using hmem) with hr | hr <;> omega
  have hper : runs.map (fun run =>
      cycleWordRank c (run.start + run.length) +
        (2 - cycleWordRank c (run.start + run.length))) =
      runs.map (fun _run => 2) := by
    apply List.map_congr_left
    intro run hmem
    have hle := hexit_le run hmem
    omega
  have hexitPenalty : exits + penalty = 2 * runs.length := by
    have hsum : exits + penalty =
        (runs.map (fun run =>
          cycleWordRank c (run.start + run.length) +
            (2 - cycleWordRank c (run.start + run.length)))).sum := by
      simp [exits, penalty]
    rw [hsum, hper]
    simp [Nat.mul_comm]
  change (runs.map (fun run => cycleWordRank c run.start)).sum +
      penalty =
    2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
      2 * runs.length
  rw [hstart]
  omega

/-- The desired aggregate rank inequality is exactly the compensated
`U < 2*H2` inequality.  A rank-one exit contributes one unit of
penalty; rank-two exits contribute none.  This is the charge form in
which deficits from individual runs may be paid by other runs. -/
theorem runStartRankSum_gt_boundSum_iff_compensated_t2RunBound
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    (((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => 2 * run.start + 14)).sum <
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum) ↔
      t2RunBoundSum c p + t2RunExitPenalty c p <
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let startRanks := (runs.map (fun run => cycleWordRank c run.start)).sum
  let bound14 := (runs.map (fun run => 2 * run.start + 14)).sum
  let U := (runs.map (fun run => 2 * run.start + 12)).sum
  let penalty := t2RunExitPenalty c p
  let H := CycleBridge.riseCountTwo (CycleBridge.cycleWord c p)
  let R := runs.length
  have hacct : startRanks + penalty = 2 * H + 2 * R := by
    simpa [startRanks, penalty, H, R, runs] using
      t2RunStartRankSum_add_exitPenalty h c p hw hm
  have hbound : bound14 = U + 2 * R := by
    have hsplit : bound14 =
        (runs.map (fun run => (2 * run.start + 12) + 2)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro run _hmem
      omega
    rw [hsplit, List.sum_map_add]
    simp [U, R, Nat.mul_comm]
  change (bound14 < startRanks) ↔
    U + penalty < 2 * H
  omega

/-- The compensated aggregate inequality and the direct aggregate-rank
inequality are the same strict inequality after the exact accounting
identity cancels `exitPenalty` against the two units per run:

`U + exitPenalty < 2*H2 ↔ U + 2*#runs < Σ startRank`. -/
theorem compensated_t2RunBound_iff_direct_aggregate_rank
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    (t2RunBoundSum c p + t2RunExitPenalty c p <
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p)) ↔
      (t2RunBoundSum c p +
          2 * (maxT2Runs (CycleBridge.cycleWord c p)).length <
        ((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => cycleWordRank c run.start)).sum) := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let U := t2RunBoundSum c p
  let penalty := t2RunExitPenalty c p
  let H := CycleBridge.riseCountTwo (CycleBridge.cycleWord c p)
  let R := runs.length
  let startRanks := (runs.map (fun run => cycleWordRank c run.start)).sum
  have hacct : startRanks + penalty = 2 * H + 2 * R := by
    simpa [startRanks, penalty, H, R, runs] using
      t2RunStartRankSum_add_exitPenalty h c p hw hm
  change (U + penalty < 2 * H) ↔ (U + 2 * R < startRanks)
  omega

/-- The prefix-numerator product valuation carries exactly the same
exit penalty as the rank telescope.  This is the product/charge
dictionary with all common prefix weights left visible. -/
theorem t2RunPrefixNumeratorProductValuation_add_exitPenalty
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    twoValuation
        (((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod) +
        t2RunExitPenalty c p =
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum +
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        2 * (maxT2Runs (CycleBridge.cycleWord c p)).length := by
  rw [t2RunPrefixNumeratorProductValuation_eq c p]
  have hacct := t2RunStartRankSum_add_exitPenalty h c p hw hm
  omega

/-- Exact equivalence between the aggregate prefix-product interface
and the compensated run inequality.  Thus the product formulation
does not hide a pointwise budget: it is precisely `U` plus the total
rank-one exit penalty below `2*H2`. -/
theorem t2RunPrefixNumeratorDivisibility_iff_compensated_t2RunBound
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    t2RunPrefixNumeratorDivisibility c p ↔
      t2RunBoundSum c p + t2RunExitPenalty c p <
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
  constructor
  · intro hprefix
    have hprod : t2RunStartProductDivisibility c p :=
      t2RunStartProductDivisibility_of_prefix_numerators c p hprefix
    have hrank := runStartRankSum_gt_boundSum_of_product_divisibility
      c p hprod
    exact (runStartRankSum_gt_boundSum_iff_compensated_t2RunBound
      h c p hw hm).mp hrank
  · intro hcomp
    let runs := maxT2Runs (CycleBridge.cycleWord c p)
    let weightSum := (runs.map (fun run => StringFlow.wordWeight
      ((CycleBridge.cycleWord c p).take run.start))).sum
    let budgetSum := (runs.map (fun run => 2 * run.start + 14)).sum
    let numerators := runs.map
      (fun run => cycleWordPrefixPlusOneNumerator c p run.start)
    have hrank : budgetSum <
        (runs.map (fun run => cycleWordRank c run.start)).sum := by
      have hraw := (runStartRankSum_gt_boundSum_iff_compensated_t2RunBound
        h c p hw hm).mpr hcomp
      simpa [runs, budgetSum] using hraw
    have hnumerators_pos : ∀ x ∈ numerators, 0 < x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨run, _hrun, rfl⟩
      unfold cycleWordPrefixPlusOneNumerator
      positivity
    have hprod_pos : 0 < numerators.prod :=
      List.prod_pos hnumerators_pos
    have hval : twoValuation numerators.prod =
        weightSum +
          (runs.map (fun run => cycleWordRank c run.start)).sum := by
      simpa [numerators, weightSum, runs] using
        t2RunPrefixNumeratorProductValuation_eq c p
    have hexp : weightSum + budgetSum + 1 ≤
        twoValuation numerators.prod := by
      rw [hval]
      omega
    have hdvd : 2 ^ (weightSum + budgetSum + 1) ∣ numerators.prod :=
      (StringFlow.Lte.twoValuation_ge_iff_dvd_pow numerators.prod
        (weightSum + budgetSum + 1) hprod_pos).mp hexp
    simpa [t2RunPrefixNumeratorDivisibility, runs, weightSum,
      budgetSum, numerators] using hdvd

/-- A proved aggregate lower bound on the prefix-numerator valuation:

`ΣW + 2H2 + #runs ≤ v2(Π N_a)`.

The still-needed strict budget is therefore an additional compensated
surplus above this baseline, not a missing per-factor estimate. -/
theorem t2RunPrefixNumeratorProductValuation_ge_base
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c) :
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => StringFlow.wordWeight
          ((CycleBridge.cycleWord c p).take run.start))).sum +
        2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) +
        (maxT2Runs (CycleBridge.cycleWord c p)).length ≤
      twoValuation
        (((maxT2Runs (CycleBridge.cycleWord c p)).map
          (fun run => cycleWordPrefixPlusOneNumerator c p run.start)).prod) := by
  have hrankLower := (t2RunStartRankSum_between h c p hw hm).1
  rw [t2RunPrefixNumeratorProductValuation_eq c p]
  omega

/-- Direct aggregate-rank chain to the endpoint inequality.  The only
strict input is the concrete run-start rank comparison

`Σ (2 * start + 14) < Σ R(start)`.

The exact start-rank telescope rewrites its right side to
`2 * H2 + Σ R(endpoint)`, and every endpoint rank is at most two.
Consequently `Σ start + 6 * #runs < H2`, which is exactly the endpoint
sum target after adding `H2 = Σ length`. -/
theorem endpointSum_lt_two_mul_H2_of_runStartRankSum_gt
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hrank : ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => 2 * run.start + 14)).sum <
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => cycleWordRank c run.start)).sum) :
    ((maxT2Runs (CycleBridge.cycleWord c p)).map
      (fun run => run.start + run.length + 6)).sum <
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
  let runs := maxT2Runs (CycleBridge.cycleWord c p)
  let H := CycleBridge.riseCountTwo (CycleBridge.cycleWord c p)
  let A := (runs.map (fun run => run.start)).sum
  let L := (runs.map (fun run => run.length)).sum
  let X := (runs.map
    (fun run => cycleWordRank c (run.start + run.length))).sum
  let R := runs.length
  have hlen : L = H := by
    simpa [L, H, runs, maxT2Runs] using
      maxT2RunsFrom_length_sum (CycleBridge.cycleWord c p) 0
  have hstart : (runs.map (fun run => cycleWordRank c run.start)).sum =
      2 * H + X := by
    simpa [runs, H, X] using
      t2RunStartRankSum_eq_two_mul_H2_add_exitRankSum c p
  have hXle : X ≤ 2 * R := by
    have hper : ∀ run ∈ runs,
        cycleWordRank c (run.start + run.length) ≤ 2 := by
      intro run hmem
      rcases t2_run_exit_rank_mem_one_two h c p hw hm run
        (by simpa [runs] using hmem) with hexit | hexit <;> omega
    have hsum : X ≤ (runs.map (fun _run => 2)).sum := by
      dsimp [X]
      exact List.sum_le_sum hper
    have hconst : (runs.map (fun _run => 2)).sum = 2 * R := by
      simp [R, Nat.mul_comm]
    rwa [hconst] at hsum
  have hbound : (runs.map (fun run => 2 * run.start + 14)).sum =
      2 * A + 14 * R := by
    rw [List.sum_map_add]
    have hmul : (runs.map (fun run => 2 * run.start)).sum = 2 * A := by
      exact List.sum_map_mul_left runs (fun run => run.start) 2
    rw [hmul]
    simp [A, R, Nat.mul_comm]
  have hrank' : (runs.map (fun run => 2 * run.start + 14)).sum <
      (runs.map (fun run => cycleWordRank c run.start)).sum := by
    simpa [runs] using hrank
  have hstrict : A + 6 * R < H := by
    rw [hbound, hstart] at hrank'
    omega
  have hendpoint : (runs.map
      (fun run => run.start + run.length + 6)).sum = A + L + 6 * R := by
    rw [List.sum_map_add]
    rw [List.sum_map_add]
    simp [A, L, R, Nat.add_assoc, Nat.mul_comm]
  rw [show ((maxT2Runs (CycleBridge.cycleWord c p)).map
      (fun run => run.start + run.length + 6)).sum =
      (runs.map (fun run => run.start + run.length + 6)).sum by rfl]
  rw [hendpoint, hlen]
  simpa [H] using (show A + H + 6 * R < 2 * H by omega)

/-- The last entry of a real closed cycle word is not two: the last
step is a C3 step, so the endpoint-subset bound applies to the whole
word. -/
lemma cycleWord_last_ne_two_of_cycleQb8Input
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p) :
    CycleBridge.cycleWord c p = [] ∨
      (CycleBridge.cycleWord c p).getI ((CycleBridge.cycleWord c p).length - 1) ≠ 2 := by
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hp : 1 ≤ p := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    omega
  right
  have hc3 : 3 ≤ w.getI (P - 1) := CycleBridge.cycleQb8Input_last_step_c3 h
  have hc3' : 3 ≤ (CycleBridge.cycleWord c p).getI (p - 1) := by
    rw [← hw, ← hP]
    exact hc3
  intro h2
  rw [CycleBridge.cycleWord_length] at h2
  omega

/-- The `noLongT2Run` branch of the orbit-rank target is discharged by
a maximal `t=2` run reaching the boundary length `start + 6`: the
prefix `j = start + 1` lies inside the run and its rank is
`2·(start+6) + R(end) - 2 ≥ 2j+9`.  This is the direct route that
does not depend on the aggregate `U < 2·H2` inequality. -/
theorem cycleQb8InputT2OrbitRankTarget_of_eq_run
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hrun : ∃ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length = run.start + 6) :
    ∃ j : Nat,
      1 ≤ j ∧ j < p ∧
      (CycleBridge.cycleWord c p).getI (j - 1) = 2 ∧
      ((CycleBridge.cycleWord c p).getI j = 1 ∨
        (CycleBridge.cycleWord c p).getI j = 2) ∧
      2 * j + 9 ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
  rcases hrun with ⟨run, hmem, hlen⟩
  let a := run.start
  let j := a + 1
  have hmem' : run ∈ maxT2Runs (CycleBridge.cycleWord c p) := hmem
  have hbnd : run.start + run.length ≤ p := by
    have hbnd' := maxT2RunsFrom_bounds (CycleBridge.cycleWord c p) 0 run
      (by simpa [maxT2Runs] using hmem')
    rw [CycleBridge.cycleWord_length] at hbnd'
    simpa using hbnd'
  have hLpos : 0 < run.length :=
    maxT2RunsFrom_length_pos (CycleBridge.cycleWord c p) 0 run hmem'
  have hL : run.length = run.start + 6 := by
    simpa using hlen
  have hL2 : 2 ≤ run.length := by omega
  have h1lt : 1 < run.length := by omega
  have hj1 : 1 ≤ j := by dsimp [j]; omega
  have hjp : j < p := by
    dsimp [j]
    omega
  have hinc0 : (CycleBridge.cycleWord c p).getI run.start = 2 := by
    have h := maxT2RunsFrom_mem_two (CycleBridge.cycleWord c p) 0 run hmem' 0 hLpos
    simpa using h
  have hinc1 : (CycleBridge.cycleWord c p).getI (run.start + 1) = 2 := by
    have h := maxT2RunsFrom_mem_two (CycleBridge.cycleWord c p) 0 run hmem' 1 h1lt
    simpa using h
  have hstep := Amiya.t2_step_rank_ge_three_of_word c p run.start (by omega) hinc0
  have hRj : twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) =
      twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1) - 2 := by
    have h := hstep.2
    have hidx : c + j = c + run.start + 1 := by
      dsimp [j]
      omega
    rw [hidx]
    exact h
  have hstart := t2_run_start_rank_eq_exit_rank_add_two_mul_length c p run hmem'
  have hstart' : twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + run.start) + 1) =
      twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + (run.start + run.length)) + 1) +
        2 * run.length := by
    simpa [cycleWordRank] using hstart
  have hexit : twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + (run.start + run.length)) + 1) = 1 ∨
      twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + (run.start + run.length)) + 1) = 2 := by
    rcases t2_run_exit_rank_mem_one_two h c p hw hm run hmem' with hr1 | hr2
    · exact Or.inl (by simpa [cycleWordRank] using hr1)
    · exact Or.inr (by simpa [cycleWordRank] using hr2)
  refine ⟨j, hj1, hjp, ?_, ?_, ?_⟩
  · have hJ : j - 1 = run.start := by rfl
    rw [hJ]
    exact hinc0
  · right
    have hJ : j = run.start + 1 := by rfl
    rw [hJ]
    exact hinc1
  · dsimp [j] at hRj ⊢
    rw [hRj]
    rcases hexit with h1 | h2
    · rw [hstart']
      omega
    · rw [hstart']
      omega

/-- The equality-run obligation in the `noLongT2Run` branch: some
maximal `t=2` run reaches the boundary length `start + 6`. -/
def cycleQb8Input_noLongT2Run_max_run : Prop :=
  ∀ {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (_hw : w = CycleBridge.cycleWord c p)
    (_hm : m = StringFlow.fiveXPlusOneOrbit 7 c),
    Amiya.noLongT2Run c p →
    ∃ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length = run.start + 6

/-- Concrete rank-lower obligation supplied by the real 7 orbit: some
`t=2` prefix of the `hcycle` word has `R(a) ≥ 2a+13`.  This is the
rank source for the equality run in the `noLongT2Run` branch. -/
def cycleQb8Input_rank_lower_prefix (c p : Nat) : Prop :=
  ∃ a : Nat, a < p ∧ (CycleBridge.cycleWord c p).getI a = 2 ∧
    2 * a + 13 ≤ cycleWordRank c a

/-- A rank lower bound at a concrete `t=2` prefix forces the maximal
run through it to meet the `noLongT2Run` equality boundary.  If the
containing run has start `s`, then `R(a) ≥ 2a+13` and
`R(s) = R(a) + 2(a-s)` push `s` to `a`, and the exit-rank bound
`R(end) ≤ 2` then gives `L = a+6`. -/
theorem max_run_of_rank_lower
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hno : Amiya.noLongT2Run c p)
    (hr : cycleQb8Input_rank_lower_prefix c p) :
    ∃ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length = run.start + 6 := by
  rcases hr with ⟨a, hap, htwo, hrank⟩
  have hcover := maxT2RunsFrom_covering (CycleBridge.cycleWord c p) 0 a (by
    rw [CycleBridge.cycleWord_length]
    exact hap) htwo
  rcases hcover with ⟨run, hmemFrom, hle, hgt⟩
  have hmem : run ∈ maxT2Runs (CycleBridge.cycleWord c p) := by
    simpa [maxT2Runs] using hmemFrom
  have hstart_le : run.start ≤ a := by
    have : run.start ≤ 0 + a := hle
    simpa using this
  let k := a - run.start
  have hk_eq : a = run.start + k := by
    dsimp [k]
    omega
  have hrun_two : ∀ i : Nat, i < k →
      (CycleBridge.cycleWord c p).getI (run.start + i) = 2 := by
    intro i hi
    have hmem_two := maxT2RunsFrom_mem_two (CycleBridge.cycleWord c p) 0 run hmemFrom i (by
      have ha_lt : a < run.start + run.length := by simpa using hgt
      dsimp [k] at hi
      omega)
    simpa using hmem_two
  have hbnd : run.start + k ≤ p := by
    dsimp [k]
    have hbnd' := maxT2RunsFrom_bounds (CycleBridge.cycleWord c p) 0 run hmemFrom
    rw [CycleBridge.cycleWord_length] at hbnd'
    have ha_lt : a < run.start + run.length := by simpa using hgt
    omega
  have hdrop := cycleWord_t2_rank_drop_in_run c p run.start k hrun_two hbnd
  have hdrop' : cycleWordRank c run.start =
      cycleWordRank c a + 2 * (a - run.start) := by
    rw [hk_eq.symm] at hdrop
    simpa [k] using hdrop
  have hlen_le := Amiya.noLongT2Run_run_length_le c p hno run hmem
  have hexit := t2_run_exit_rank_mem_one_two h c p hw hm run hmem
  have hexit_le : cycleWordRank c (run.start + run.length) ≤ 2 := by
    rcases hexit with h1 | h2 <;> omega
  have hstart := t2_run_start_rank_eq_exit_rank_add_two_mul_length c p run hmem
  have hstart_eq : cycleWordRank c run.start =
      cycleWordRank c (run.start + run.length) + 2 * run.length := by
    simpa using hstart
  have hrank_start_le : cycleWordRank c run.start ≤ 2 * run.start + 14 := by
    omega
  have hs : run.start = a := by
    have hle_a : a ≤ run.start := by omega
    exact le_antisymm hstart_le hle_a
  have hL_ge : a + 6 ≤ run.length := by
    have hstart_eq' : cycleWordRank c a =
        cycleWordRank c (a + run.length) + 2 * run.length := by
      simpa [hs] using hstart_eq
    have hexit_le' : cycleWordRank c (a + run.length) ≤ 2 := by
      simpa [hs] using hexit_le
    omega
  have hL_le : run.length ≤ a + 6 := by
    simpa [hs] using hlen_le
  have hL_eq : run.length = a + 6 := by omega
  have hL_eq' : run.length = run.start + 6 := by
    rw [hs]
    exact hL_eq
  exact ⟨run, hmem, hL_eq'⟩

/-- The rank-lower prefix supplies the equality-run obligation. -/
theorem cycleQb8Input_noLongT2Run_max_run_of_rank_lower
    (hr : ∀ {m S P : Nat} {w rise c3 : List Nat}
      (_h : CycleBridge.CycleQb8Input m S P w rise c3)
      (c p : Nat) (_hw : w = CycleBridge.cycleWord c p)
      (_hm : m = StringFlow.fiveXPlusOneOrbit 7 c),
      cycleQb8Input_rank_lower_prefix c p) :
    cycleQb8Input_noLongT2Run_max_run := by
  intro m S P w rise c3 h c p hw hm hno
  exact max_run_of_rank_lower h c p hw hm hno (hr h c p hw hm)

/-- The `noLongT2Run` branch of the orbit-rank target closes from the
equality-run obligation; the `¬ noLongT2Run` branch uses the existing
run-budget bridge. -/
theorem hfailRankLowerBoundTarget_of_noLongT2Run_max_run
    (hmax : cycleQb8Input_noLongT2Run_max_run) :
    Amiya.hfailRankLowerBoundTarget := by
  have htarget : Amiya.cycleQb8InputT2OrbitRankTarget := by
    intro m S P w rise c3 h c p hw hm
    by_cases hno : Amiya.noLongT2Run c p
    · have hres := cycleQb8InputT2OrbitRankTarget_of_eq_run
        h c p hw hm (hmax h c p hw hm hno)
      rw [← hw] at hres
      exact hres
    · exact Amiya.cycleQb8InputT2OrbitRankTarget_of_noLongT2Run_false
        h c p hw hm hno
  exact Amiya.hfailRankLowerBoundTarget_of_t2_orbit_rank htarget

/-- Pigeonhole over the summed tail ranks: once the boundary-rank sum
reaches the summed budget `2·Σb + 13·K`, some cyclic rise block
satisfies `hfailBudgetLowerBoundAt`.  The summation lower bound is the
uniform whole-cycle input; the per-block exact balance
`F_r + R_r = 2N_r + 2` supplies the rewrite from the budget threshold
to the tail-rank threshold. -/
theorem hfailBudgetLowerBoundAt_exists_of_tailRankSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hsum : 2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
          13 * d.blockCount ≤
        ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum) :
    ∃ r : Nat, r < d.blockCount ∧ hfailBudgetLowerBoundAt d r := by
  by_contra hnone
  have hall : ∀ r : Nat, r < d.blockCount →
      CycleBridge.cycleRiseBlockTailRank d r ≤
        2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 := by
    intro r hr
    by_contra hle
    have hge : 2 * CycleBridge.cycleRiseBlockTailDepth d r + 13 ≤
        CycleBridge.cycleRiseBlockTailRank d r := by omega
    have hbal := cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two
      h d r hr
    have hb : hfailBudgetLowerBoundAt d r := by
      unfold hfailBudgetLowerBoundAt
      omega
    exact hnone ⟨r, hr, hb⟩
  have hsumle : ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum ≤
      ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r + 12)).sum :=
    List.sum_le_sum (by
      intro r hr
      exact hall r (List.mem_range.mp hr))
  have hsumadd : ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r + 12)).sum =
      2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
        12 * d.blockCount := by
    rw [List.sum_map_add]
    have hA : ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r)).sum =
        2 * ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum :=
      StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)
    have hconst : ((List.range d.blockCount).map (fun _ => 12)).sum =
        12 * d.blockCount := by
      rw [List.map_const', List.sum_replicate, List.length_range]
      simp [Nat.mul_comm]
    rw [hA, hconst]
  have hle' : ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum ≤
      2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
        12 * d.blockCount := by
    rw [hsumadd] at hsumle
    exact hsumle
  omega

/-- Whole-cycle boundary-rank sum bound with the concrete
decomposition:
`2·Σb + 13·K ≤ ΣR`.  This is the exact sum obligation; it is
deliberately stated with `CycleQb8Input` so that the real 7-orbit
anchors (`hstart`/`hcycle`) are available to the proof. -/
def cycleRiseBlockTailRankSumBound : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    (h : CycleBridge.CycleQb8Input m S P w rise c3) →
      ∃ d : CycleBridge.CycleRiseBlockDecomposition m S P w,
        0 < d.blockCount ∧
        2 * ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
            13 * d.blockCount ≤
          ((List.range d.blockCount).map
            (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum

/-- The summed tail-rank bound closes `hfailBudgetLowerBound` through
the pigeonhole lemma.  No per-block threshold is assumed; the sum is
the whole-cycle input. -/
theorem hfailBudgetLowerBound_of_tailRankSumBound
    (hsum : cycleRiseBlockTailRankSumBound) : hfailBudgetLowerBound := by
  intro m S P w rise c3 h
  rcases hsum m S P w rise c3 h with ⟨d, hpos, hsum'⟩
  rcases hfailBudgetLowerBoundAt_exists_of_tailRankSum h d hpos hsum' with
    ⟨r, hr, hb⟩
  exact ⟨d, r, hr, hb⟩

/-- Summed form of the all-below-budget assumption:
`∀ r, 2N_r−F_r ≤ 2b_r+10` implies the same inequality on the sums. -/
theorem cycleRiseBlockAllBelowBudget_sum_le
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hbelow : Amiya.cycleRiseBlockAllBelowBudget d) :
    ((List.range d.blockCount).map
      (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r) -
        CycleBridge.cycleRiseBlockCharge d r)).sum ≤
      ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r + 10)).sum :=
  List.sum_le_sum (by
    intro r hr
    exact hbelow r (List.mem_range.mp hr))

/-- The all-below-budget assumption contradicts the summed tail-rank
bound: once `2·Σb + 13K ≤ ΣR` is supplied, the per-block budget
thresholds force a pigeonhole block, while `allBelowBudget` excludes
it.  This is the exact contraction shape used against `2^S > 5^P`. -/
theorem allBelowBudget_contradicts_tailRankSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hbelow : Amiya.cycleRiseBlockAllBelowBudget d)
    (hsum : 2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
          13 * d.blockCount ≤
        ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum) : False := by
  rcases hfailBudgetLowerBoundAt_exists_of_tailRankSum h d hpos hsum with
    ⟨r, hr, hb⟩
  have hb1 : 2 * CycleBridge.cycleRiseBlockTailDepth d r + 11 ≤
      2 * CycleBridge.riseCountTwo (d.suffixWord r) -
        CycleBridge.cycleRiseBlockCharge d r :=
    (Amiya.hfailBudgetLowerBoundAt_iff_t2_budget d r).mp hb
  have hle := hbelow r hr
  omega

/-- The non-wrapping block-step `wordA` recurrence: the next-head
numerator is the current-head numerator shifted by the whole block
segment `c3Word r ++ suffixWord r`.  This is the exact block-partition
step that connects `A_P` to the uniform local block equations. -/
theorem cycleRiseBlockSeg_wordA_shift
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    StringFlow.Word.wordA (w.take (d.headDepth (r + 1))) =
      5 ^ ((d.c3Word r).length + (d.suffixWord r).length) *
          StringFlow.Word.wordA (w.take (d.headDepth r)) +
        2 ^ StringFlow.wordWeight (w.take (d.headDepth r)) *
          StringFlow.Word.wordA (d.c3Word r ++ d.suffixWord r) := by
  have hseg := cycleRiseBlockSeg_eq_drop_take_nonwrap d r hr hrnext
  have htake := (List.take_append_drop (d.headDepth r)
      (w.take (d.headDepth (r + 1)))).symm
  have htake3 : (w.take (d.headDepth (r + 1))).take (d.headDepth r) =
      w.take (d.headDepth r) := by
    rw [List.take_take]
    have hle : d.headDepth r ≤ d.headDepth (r + 1) := by
      have hh := d.hnext r hr
      rw [if_pos hrnext] at hh
      omega
    rw [Nat.min_comm, Nat.min_eq_right hle]
  have hsplit : w.take (d.headDepth (r + 1)) =
      w.take (d.headDepth r) ++
        (w.take (d.headDepth (r + 1))).drop (d.headDepth r) := by
    simpa [htake3] using htake
  rw [hsplit]
  rw [← hseg]
  simpa [List.length_append] using
    (CycleBridge.wordA_append_shift (w.take (d.headDepth r))
      (d.c3Word r ++ d.suffixWord r))

/-- The summed tail-rank bound is equivalent to the same bound on the
rotated-word valuation sum `Σ v2(wordA (rotation at b_r) + Δ)`.
This is the exact interface that the `A_P` block expansion must
dominate. -/
theorem tailRankSumBound_of_v2_rotated_plus_delta_sum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hsum : 2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
          13 * d.blockCount ≤
        ((List.range d.blockCount).map
          (fun r => twoValuation
            (StringFlow.Word.wordA
              (CycleBridge.cyclicSegmentAt w
                (CycleBridge.cycleRiseBlockTailDepth d r)) +
              (2 ^ S - 5 ^ P)))).sum) :
    2 * ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailDepth d r)).sum +
          13 * d.blockCount ≤
        ((List.range d.blockCount).map
          (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum := by
  rw [CycleBridge.cycleRiseBlockTailRankSum_eq_v2_rotated_plus_delta_sum h d]
  exact hsum

/-- Boundary rank plus boundary prefix weight equals the 2-adic
valuation of the prefix plus-one numerator:
`W(b_r) + R_r = v2(5^{b_r}·m + A(b_r) + 2^{W(b_r)})`.
This is the exact form in which the summed boundary ranks can be read
from the prefix numerators of the `hcycle` word. -/
theorem cycleRiseBlockTailRank_add_prefixWeight_eq_val_prefixPlusOne
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockTailRank d r +
        StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) =
      twoValuation
        (5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
          StringFlow.Word.wordA
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
          2 ^ StringFlow.wordWeight
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r))) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let W := StringFlow.wordWeight (w.take b)
  let y := StringFlow.Word.wordOrbit (w.take b) m
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hlen : (w.take b).length = b := by
    rw [List.length_take_of_le hb]
  have hvalid : StringFlow.Word.wordValid (w.take b) m := by
    have hsplit : w.take b ++ w.drop b = w := List.take_append_drop b w
    have hv : StringFlow.Word.wordValid (w.take b ++ w.drop b) m := by
      rw [hsplit]
      exact h.hvalid
    exact ((S6Audit.wordValid_append (w.take b) (w.drop b) m).mp hv).1
  have hid := StringFlow.Word.word_orbit_identity (w.take b) m hvalid
  have hid' : 2 ^ W * (y + 1) =
      5 ^ b * m + StringFlow.Word.wordA (w.take b) + 2 ^ W := by
    dsimp [W, y]
    rw [hlen] at hid
    rw [show 2 ^ StringFlow.wordWeight (w.take b) *
          (StringFlow.Word.wordOrbit (w.take b) m + 1) =
        2 ^ StringFlow.wordWeight (w.take b) *
           StringFlow.Word.wordOrbit (w.take b) m +
         2 ^ StringFlow.wordWeight (w.take b) by ring]
    rw [hid]
  have hpos : 0 < y + 1 := by positivity
  have hv2 : twoValuation (2 ^ W * (y + 1)) = W + twoValuation (y + 1) :=
    StringFlow.Lte.twoValuation_mul_two_pow W (y + 1) hpos
  have hval : twoValuation
      (5 ^ b * m + StringFlow.Word.wordA (w.take b) + 2 ^ W) =
      W + twoValuation (y + 1) := by
    rw [← hid', hv2]
  have hR : CycleBridge.cycleRiseBlockTailRank d r = twoValuation (y + 1) := by
    simp [CycleBridge.cycleRiseBlockTailRank, CycleBridge.cycleRiseBlockC3TailState,
      CycleBridge.cycleRiseBlockTailDepth, b, y]
  simpa [b, W] using
    (calc
      CycleBridge.cycleRiseBlockTailRank d r + W
          = twoValuation (y + 1) + W := by rw [hR]
      _ = W + twoValuation (y + 1) := by omega
      _ = twoValuation (5 ^ b * m + StringFlow.Word.wordA (w.take b) + 2 ^ W) :=
          hval.symm)

/-- Summed form of the prefix-numerator valuation bridge:
`Σ R_r + Σ W(b_r) = Σ v2(5^{b_r}·m + A(b_r) + 2^{W(b_r)})`.
This is the exact whole-cycle shape that the `hcycle` word must
dominate; subtracting `Σ W(b_r)` leaves the boundary-rank sum. -/
theorem cycleRiseBlockTailRankSum_add_prefixWeightSum_eq_val_sum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum +
      ((List.range d.blockCount).map
        (fun r => StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)))).sum =
      ((List.range d.blockCount).map
        (fun r => twoValuation
          (5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
            StringFlow.Word.wordA
              (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
            2 ^ StringFlow.wordWeight
              (w.take (CycleBridge.cycleRiseBlockTailDepth d r))))).sum := by
  have hmap : (List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockTailRank d r +
        StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r))) =
    (List.range d.blockCount).map
      (fun r => twoValuation
        (5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
          StringFlow.Word.wordA
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
          2 ^ StringFlow.wordWeight
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r)))) := by
    apply List.map_congr_left
    intro r hr
    exact cycleRiseBlockTailRank_add_prefixWeight_eq_val_prefixPlusOne
      h d r (List.mem_range.mp hr)
  rw [← List.sum_map_add]
  rw [hmap]

/-- The crush core: if every block is below the budget threshold,
then the whole-cycle weight comparison reverses (`2^S ≤ 5^P`).
This is the exact remaining obligation; it is the contradiction shape
that closes the sum route without the PMI inequality. -/
def cycleRiseBlockAllBelowBudgetCrush : Prop :=
  ∀ {m S P : Nat} {w rise c3 : List Nat},
    (h : CycleBridge.CycleQb8Input m S P w rise c3) →
      ∀ d : CycleBridge.CycleRiseBlockDecomposition m S P w,
        Amiya.cycleRiseBlockAllBelowBudget d →
          2 ^ S ≤ 5 ^ P

/-- The crush core closes `hfailBudgetLowerBound`: under
`allBelowBudget`, the reversed comparison contradicts
`5^P < 2^S`, so some cyclic rise block must satisfy the budget. -/
theorem hfailBudgetLowerBound_of_crush
    (hcrush : cycleRiseBlockAllBelowBudgetCrush) : hfailBudgetLowerBound := by
  intro m S P w rise c3 h
  rcases CycleBridge.cycleRiseBlockDecompositionExists_of_input h with
    ⟨d, hpos⟩
  by_contra hnone
  have hbelow : Amiya.cycleRiseBlockAllBelowBudget d := by
    intro r hr
    have hnot : ¬ Amiya.hfailBudgetLowerBoundAt d r := by
      intro hb
      exact hnone ⟨r, hr, hb⟩
    have hiff := Amiya.hfailBudgetLowerBoundAt_iff_t2_budget d r
    have hnot2 : ¬ (2 * CycleBridge.cycleRiseBlockTailDepth d r + 11 ≤
        2 * CycleBridge.riseCountTwo (d.suffixWord r) -
          CycleBridge.cycleRiseBlockCharge d r) := by
      intro h2
      exact hnot (hiff.mpr h2)
    omega
  have hle := hcrush h d hbelow
  have hgt := CycleBridge.cycleQb8Input_weak_comparison h
  omega

end Closure

end StringFlow
