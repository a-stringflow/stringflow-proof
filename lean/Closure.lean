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

/-- 回绕块的 C3-tail 深度不低于第 0 块的 C3-tail 深度：
`tailDepth 0 ≤ tailDepth (K−1)`。若相反，最后一段 rise suffix
（全 `1/2`）会和 `c3Word 0`（全 `≥3`）落在同一个真实词位，矛盾。 -/
lemma cycleRiseBlock_tailDepth_last_ge_zero
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 1 ≤ d.blockCount) :
    CycleBridge.cycleRiseBlockTailDepth d 0 ≤
      CycleBridge.cycleRiseBlockTailDepth d (d.blockCount - 1) := by
  by_contra hnot
  have hlt : CycleBridge.cycleRiseBlockTailDepth d (d.blockCount - 1) <
      CycleBridge.cycleRiseBlockTailDepth d 0 := by omega
  let K := d.blockCount
  let tail := CycleBridge.cycleRiseBlockTailDepth d (K - 1)
  let t0 := CycleBridge.cycleRiseBlockTailDepth d 0
  let C0 := (d.c3Word 0).length
  let sl := (d.suffixWord (K - 1)).length
  let k := t0 - 1 - tail
  have hr : K - 1 < K := by omega
  have hpos0 : 0 < d.blockCount := by omega
  have hpos_t0 : t0 = d.headDepth 0 + C0 := by
    dsimp [t0, C0]
    rfl
  have htail_def : tail = d.headDepth (K - 1) + (d.c3Word (K - 1)).length := by
    dsimp [tail]
    rfl
  have hwrap : tail + sl = d.headDepth 0 + P := by
    have hh := d.hnext (K - 1) hr
    rw [if_neg (by omega : ¬ (K - 1) + 1 < K)] at hh
    dsimp [K] at hh
    rw [← htail_def] at hh
    simpa [sl] using hh.symm
  have htail_le : tail ≤ P := by
    have ht_lt : tail - 1 < P := by
      have h := CycleBridge.cycleRiseBlockTailDepth_lt_succ d (K - 1) hr
      simpa [tail] using h
    omega
  have hd0pos : 1 ≤ d.headDepth 0 := d.hhead_pos 0 hpos0
  have hC0pos : 1 ≤ C0 := by
    dsimp [C0]
    exact List.length_pos_iff.mpr (d.hc3_nonempty 0 hpos0)
  have hC0_le : C0 ≤ P := by
    have ht0_lt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos0
    have ht0_def : CycleBridge.cycleRiseBlockTailDepth d 0 = d.headDepth 0 + C0 := by
      dsimp [C0]
      rfl
    rw [ht0_def] at ht0_lt
    omega
  have hk_lt_sl : k < sl := by
    dsimp [k]
    omega
  have htailk : tail + k = t0 - 1 := by
    dsimp [k]
    have ht0pos : 1 ≤ t0 := by
      dsimp [t0]
      exact CycleBridge.cycleRiseBlockTailDepth_pos d 0 hpos0
    have ht0succ : t0 = (t0 - 1) + 1 := by omega
    have hlt' : tail < (t0 - 1) + 1 := by
      change tail < t0 at hlt
      rw [ht0succ] at hlt
      exact hlt
    have htail_le0 : tail ≤ t0 - 1 := Nat.le_of_lt_succ hlt'
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel htail_le0
  have hsuf : (d.suffixWord (K - 1)).getI k =
      w.getI ((tail + k) % w.length) := by
    have hseg := d.hsuffix_segment (K - 1) hr k hk_lt_sl
    rw [← htail_def] at hseg
    simpa [tail, ← d.hperiod] using hseg
  have hsuf' : (d.suffixWord (K - 1)).getI k = w.getI (t0 - 1) := by
    rw [hsuf]
    have hlt_w : t0 - 1 < w.length := by
      have hlt_p : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < P :=
        CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos0
      rw [d.hperiod]
      dsimp [t0] at hlt_p ⊢
      exact hlt_p
    have hmod : (tail + k) % w.length = t0 - 1 := by
      rw [htailk]
      exact Nat.mod_eq_of_lt hlt_w
    rw [hmod]
  have hsuf12 : (d.suffixWord (K - 1)).getI k = 1 ∨
      (d.suffixWord (K - 1)).getI k = 2 := by
    have hmem : (d.suffixWord (K - 1)).getI k ∈ d.suffixWord (K - 1) := by
      rw [List.getI_eq_getElem (l := d.suffixWord (K - 1)) (n := k) hk_lt_sl]
      exact List.getElem_mem hk_lt_sl
    exact d.hsuffix_one_two (K - 1) hr ((d.suffixWord (K - 1)).getI k) hmem
  have hc3k : C0 - 1 < (d.c3Word 0).length := by
    dsimp [C0]
    have hC0pos : 1 ≤ (d.c3Word 0).length :=
      List.length_pos_iff.mpr (d.hc3_nonempty 0 hpos0)
    omega
  have hc3 : (d.c3Word 0).getI (C0 - 1) =
      w.getI (d.headDepth 0 + (C0 - 1)) := by
    have hseg := d.hc3_segment 0 hpos0 (C0 - 1) hc3k
    dsimp [C0] at hseg ⊢
    exact hseg
  have hc3' : (d.c3Word 0).getI (C0 - 1) = w.getI (t0 - 1) := by
    rw [hc3]
    rw [hpos_t0]
    congr 1
    omega
  have hc3ge : 3 ≤ (d.c3Word 0).getI (C0 - 1) := by
    have hmem : (d.c3Word 0).getI (C0 - 1) ∈ d.c3Word 0 := by
      rw [List.getI_eq_getElem (l := d.c3Word 0) (n := C0 - 1) hc3k]
      exact List.getElem_mem hc3k
    exact d.hc3_entries 0 hpos0 ((d.c3Word 0).getI (C0 - 1)) hmem
  rw [hsuf'] at hsuf12
  rw [hc3'] at hc3ge
  rcases hsuf12 with h1 | h2
  · rw [h1] at hc3ge
    norm_num at hc3ge
  · rw [h2] at hc3ge
    norm_num at hc3ge

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

/-- 块段 `c3Word r ++ suffixWord r` 的精确边界状态分子：
`A(seg_r) = 2^{W(seg_r)}·y_{r+1} − 5^{|seg_r|}·y_r`，其中
`y_r = wordOrbit (w.take (headDepth r)) m` 是块首真实状态。
这是按块展开 `A_P` 时保留边界状态项的核心恒等式。 -/
theorem cycleRiseBlockSeg_wordA_eq_nextHead_sub
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    StringFlow.Word.wordA (d.c3Word r ++ d.suffixWord r) =
      2 ^ StringFlow.wordWeight (d.c3Word r ++ d.suffixWord r) *
          StringFlow.Word.wordOrbit (w.take (d.headDepth (r + 1))) m -
      5 ^ (d.c3Word r ++ d.suffixWord r).length *
          StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m := by
  let seg := d.c3Word r ++ d.suffixWord r
  let y := StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m
  have hseg := cycleRiseBlockSeg_eq_drop_take_nonwrap d r hr hrnext
  have hmono : d.headDepth r ≤ d.headDepth (r + 1) := by
    have hh := d.hnext r hr
    rw [if_pos hrnext] at hh
    omega
  have hsplit2 : w.take (d.headDepth (r + 1)) = w.take (d.headDepth r) ++ seg := by
    have ht := (List.take_append_drop (d.headDepth r) (w.take (d.headDepth (r + 1)))).symm
    have htake : (w.take (d.headDepth (r + 1))).take (d.headDepth r) =
        w.take (d.headDepth r) := by
      rw [List.take_take]
      rw [Nat.min_eq_left hmono]
    rw [htake, ← hseg] at ht
    exact ht
  have hvalid_prefix : StringFlow.Word.wordValid (w.take (d.headDepth (r + 1))) m := by
    have hsplit : w.take (d.headDepth (r + 1)) ++ w.drop (d.headDepth (r + 1)) = w :=
      List.take_append_drop (d.headDepth (r + 1)) w
    have hv : StringFlow.Word.wordValid
        (w.take (d.headDepth (r + 1)) ++ w.drop (d.headDepth (r + 1))) m := by
      rw [hsplit]
      exact h.hvalid
    exact ((S6Audit.wordValid_append (w.take (d.headDepth (r + 1)))
      (w.drop (d.headDepth (r + 1))) m).mp hv).1
  have hv2 : StringFlow.Word.wordValid (w.take (d.headDepth r) ++ seg) m := by
    rwa [hsplit2] at hvalid_prefix
  have hvalid_seg : StringFlow.Word.wordValid seg y := by
    exact ((S6Audit.wordValid_append (w.take (d.headDepth r)) seg m).mp hv2).2
  have horb : StringFlow.Word.wordOrbit (w.take (d.headDepth (r + 1))) m =
      StringFlow.Word.wordOrbit seg (StringFlow.Word.wordOrbit
        (w.take (d.headDepth r)) m) := by
    rw [hsplit2, S6Audit.wordOrbit_append (w.take (d.headDepth r)) seg m]
  have hid := StringFlow.Word.word_orbit_identity seg y hvalid_seg
  rw [← horb] at hid
  dsimp [seg, y] at hid ⊢
  omega

/-- 回绕块段 `c3Word (K−1) ++ suffixWord (K−1)` 的精确边界状态
分子：`A(seg_{K−1}) = 2^{W}·y_0 − 5^{L}·y_{K−1}`，回绕终点回到
第 0 块块首状态。 -/
theorem cycleRiseBlockSeg_wordA_eq_nextHead_sub_wrap
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    StringFlow.Word.wordA (d.c3Word (d.blockCount - 1) ++ d.suffixWord (d.blockCount - 1)) =
      2 ^ StringFlow.wordWeight
          (d.c3Word (d.blockCount - 1) ++ d.suffixWord (d.blockCount - 1)) *
          StringFlow.Word.wordOrbit (w.take (d.headDepth 0)) m -
      5 ^ (d.c3Word (d.blockCount - 1) ++ d.suffixWord (d.blockCount - 1)).length *
          StringFlow.Word.wordOrbit
            (w.take (d.headDepth (d.blockCount - 1))) m := by
  let K := d.blockCount
  let seg := d.c3Word (K - 1) ++ d.suffixWord (K - 1)
  let y := StringFlow.Word.wordOrbit (w.take (d.headDepth (K - 1))) m
  have hseg := cycleRiseBlockSeg_eq_drop_take_wrap d hpos
  have htd : w.take (d.headDepth (K - 1)) ++ w.drop (d.headDepth (K - 1)) = w :=
    List.take_append_drop (d.headDepth (K - 1)) w
  have hv : StringFlow.Word.wordValid
      (w.take (d.headDepth (K - 1)) ++ w.drop (d.headDepth (K - 1))) m := by
    rw [htd]
    exact h.hvalid
  have hparts := (S6Audit.wordValid_append
      (w.take (d.headDepth (K - 1))) (w.drop (d.headDepth (K - 1))) m).mp hv
  have hvalid_drop : StringFlow.Word.wordValid (w.drop (d.headDepth (K - 1))) y := by
    dsimp [y]
    exact hparts.2
  have hvalid_take0 : StringFlow.Word.wordValid (w.take (d.headDepth 0)) m := by
    have htd0 : w.take (d.headDepth 0) ++ w.drop (d.headDepth 0) = w :=
      List.take_append_drop (d.headDepth 0) w
    have hv0 : StringFlow.Word.wordValid
        (w.take (d.headDepth 0) ++ w.drop (d.headDepth 0)) m := by
      rw [htd0]
      exact h.hvalid
    exact ((S6Audit.wordValid_append (w.take (d.headDepth 0))
      (w.drop (d.headDepth 0)) m).mp hv0).1
  have horb_drop : StringFlow.Word.wordOrbit (w.drop (d.headDepth (K - 1))) y = m := by
    dsimp [y]
    have hw := S6Audit.wordOrbit_append (w.take (d.headDepth (K - 1)))
      (w.drop (d.headDepth (K - 1))) m
    have hw' : StringFlow.Word.wordOrbit w m = StringFlow.Word.wordOrbit
        (w.drop (d.headDepth (K - 1)))
        (StringFlow.Word.wordOrbit (w.take (d.headDepth (K - 1))) m) := by
      rw [htd] at hw
      exact hw
    rw [d.hclosed] at hw'
    exact hw'.symm
  have hvalid_seg : StringFlow.Word.wordValid seg y := by
    dsimp [seg]
    rw [hseg]
    exact (S6Audit.wordValid_append
      (w.drop (d.headDepth (K - 1))) (w.take (d.headDepth 0)) y).mpr ⟨hvalid_drop, by
        rw [horb_drop]
        exact hvalid_take0⟩
  have horb : StringFlow.Word.wordOrbit seg y =
      StringFlow.Word.wordOrbit (w.take (d.headDepth 0)) m := by
    dsimp [seg]
    rw [hseg, S6Audit.wordOrbit_append (w.drop (d.headDepth (K - 1)))
      (w.take (d.headDepth 0)) y]
    rw [horb_drop]
  have hid := StringFlow.Word.word_orbit_identity seg y hvalid_seg
  rw [horb] at hid
  dsimp [seg, y, K] at hid ⊢
  omega

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
      exact hnone ⟨d, r, hr, hb⟩
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

/-- The all-below-budget assumption is exactly the pointwise boundary
rank bound `R_r ≤ 2b_r+12`, after the per-block balance
`F_r + R_r = 2N_r + 2` cancels the two units.  This is the rank form
used by the crush proof. -/
theorem cycleRiseBlockAllBelowBudget_iff_tailRank_le
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    Amiya.cycleRiseBlockAllBelowBudget d ↔
      ∀ r : Nat, r < d.blockCount →
        CycleBridge.cycleRiseBlockTailRank d r ≤
          2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 := by
  constructor
  · intro hbelow r hr
    have hbal := Amiya.cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two
      h d r hr
    have hle := hbelow r hr
    omega
  · intro hle r hr
    have hbal := Amiya.cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two
      h d r hr
    have hR := hle r hr
    omega

/-- Every boundary state is a real odd full-orbit state, so its
rank is at least one.  This is the positive baseline for the
pointwise rank bounds used by the crush proof. -/
theorem cycleRiseBlockTailRank_pos
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    1 ≤ CycleBridge.cycleRiseBlockTailRank d r := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hfull : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit (w.take b) m) := by
    dsimp [b]
    exact CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) (by omega)
  have hodd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take b) m) :=
    S6Audit.FullOrbitFrom7_odd _ hfull
  have heven : (StringFlow.Word.wordOrbit (w.take b) m + 1) % 2 = 0 := by
    rw [Nat.add_mod, hodd]
  have hdvd : 2 ∣ StringFlow.Word.wordOrbit (w.take b) m + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr heven
  have hval : 1 ≤ twoValuation
      (StringFlow.Word.wordOrbit (w.take b) m + 1) :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (StringFlow.Word.wordOrbit (w.take b) m + 1) 1 (by positivity)).mpr hdvd
  dsimp [CycleBridge.cycleRiseBlockTailRank, CycleBridge.cycleRiseBlockC3TailState, b]
  exact hval

/-- `Δ = 2^S − 5^P` is odd whenever the weak comparison
`5^P < 2^S` holds with `1 ≤ S`.  This is the unit used to move the
boundary-rank sum into a single 2-adic valuation. -/
theorem two_pow_sub_five_pow_odd {S P : Nat}
    (hSpos : 1 ≤ S) (hlt : 5 ^ P < 2 ^ S) :
    (2 ^ S - 5 ^ P) % 2 = 1 := by
  have h2even : ∃ k, 2 ^ S = 2 * k := by
    refine ⟨2 ^ (S - 1), ?_⟩
    have hS : S = (S - 1) + 1 := by omega
    nth_rewrite 1 [hS]
    rw [Nat.pow_succ]
    ring
  have h5odd : ∃ l, 5 ^ P = 2 * l + 1 :=
    Nat.odd_iff.mpr (StringFlow.Lte.five_pow_odd P)
  have hdelta_odd' : ∃ m, 2 ^ S - 5 ^ P = 2 * m + 1 := by
    rcases h2even with ⟨k, hk⟩
    rcases h5odd with ⟨l, hl⟩
    have hlt2 : 2 * l + 1 < 2 * k := by
      rw [← hl, ← hk]
      exact hlt
    have hlk : l + 1 ≤ k := by omega
    refine ⟨k - l - 1, ?_⟩
    rw [hk, hl]
    omega
  exact Nat.odd_iff.mp hdelta_odd'

/-- Summed boundary rank as the 2-adic valuation of the product
`Π_r Δ·(q_r+1)`: since `Δ = 2^S − 5^P` is odd, the valuation is
exactly `ΣR_r`.  This is the product form required by the crush size
argument. -/
theorem cycleRiseBlockTailRankSum_eq_v2_prod_delta_q_add_one
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum =
      twoValuation (((List.range d.blockCount).map
        (fun r => (2 ^ S - 5 ^ P) *
          (StringFlow.Word.wordOrbit
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1))).prod) := by
  let xs := (List.range d.blockCount).map
    (fun r => (2 ^ S - 5 ^ P) *
      (StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1))
  have hxs_pos : ∀ x ∈ xs, 0 < x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    have hlt := CycleBridge.cycleQb8Input_weak_comparison h
    have hdelta_pos : 0 < 2 ^ S - 5 ^ P := by omega
    positivity
  have hval := twoValuation_list_prod_eq_sum xs hxs_pos
  have hmap : xs.map twoValuation = (List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockTailRank d r) := by
    dsimp [xs]
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hlt := CycleBridge.cycleQb8Input_weak_comparison h
    have hSpos : 1 ≤ S := by
      by_contra hnot
      have hS0 : S = 0 := by omega
      rw [hS0] at hlt
      norm_num at hlt
    have hodd := two_pow_sub_five_pow_odd hSpos hlt
    have hpos : 0 < StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1 := by positivity
    have hv := StringFlow.Lte.twoValuation_mul_odd (2 ^ S - 5 ^ P)
      (StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1)
      hodd hpos
    have hR : CycleBridge.cycleRiseBlockTailRank d r = twoValuation
        (StringFlow.Word.wordOrbit
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1) := by
      dsimp [CycleBridge.cycleRiseBlockTailRank, CycleBridge.cycleRiseBlockC3TailState,
        CycleBridge.cycleRiseBlockTailDepth]
    rw [hR]
    exact hv
  rw [hmap] at hval
  dsimp [xs] at hval ⊢
  exact hval.symm

/-- The boundary prefix plus-one numerator factorizes exactly:
`2^{W_r}·(q_r+1) = 5^{b_r}·m + A(b_r) + 2^{W_r}`. -/
theorem cycleRiseBlockPrefixPlusOne_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    2 ^ StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) *
        (StringFlow.Word.wordOrbit
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1) =
      5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
        StringFlow.Word.wordA (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
        2 ^ StringFlow.wordWeight (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) := by
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
  rw [hlen] at hid
  rw [show 2 ^ StringFlow.wordWeight (w.take b) *
        (StringFlow.Word.wordOrbit (w.take b) m + 1) =
      2 ^ StringFlow.wordWeight (w.take b) *
        StringFlow.Word.wordOrbit (w.take b) m +
      2 ^ StringFlow.wordWeight (w.take b) by ring]
  rw [hid]

/-- Product rearrangement: `Π_r 2^{w_r}·q_r = 2^{Σ_r w_r}·Π_r q_r`. -/
lemma prod_mul_two_pow {α : Type} (w : α → Nat) (q : α → Nat) (l : List α) :
    (l.map (fun r => 2 ^ w r * q r)).prod =
      2 ^ (l.map w).sum * (l.map q).prod := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons, ih]
      rw [Nat.pow_add]
      ring

/-- Exact product identity for the boundary ranks:
`Π(q_r+1)·2^{ΣW_r} = Π(5^{b_r}·m + A(b_r) + 2^{W_r})`.
This is the precise product form used by the crush size argument. -/
theorem prod_q_add_one_mul_two_pow_weight_eq_prod_prefixPlusOne
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (((List.range d.blockCount).map
      (fun r => StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1)).prod) *
      2 ^ ((List.range d.blockCount).map
        (fun r => StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)))).sum =
      ((List.range d.blockCount).map
        (fun r => 5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
          StringFlow.Word.wordA (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
          2 ^ StringFlow.wordWeight
            (w.take (CycleBridge.cycleRiseBlockTailDepth d r)))).prod := by
  have hmap : (List.range d.blockCount).map
      (fun r => 2 ^ StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) *
        (StringFlow.Word.wordOrbit
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m + 1)) =
    (List.range d.blockCount).map
      (fun r => 5 ^ CycleBridge.cycleRiseBlockTailDepth d r * m +
        StringFlow.Word.wordA (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) +
        2 ^ StringFlow.wordWeight
          (w.take (CycleBridge.cycleRiseBlockTailDepth d r))) := by
    apply List.map_congr_left
    intro r hr
    exact cycleRiseBlockPrefixPlusOne_eq h d r (List.mem_range.mp hr)
  have hprod := congrArg List.prod hmap
  rw [prod_mul_two_pow] at hprod
  simpa [Nat.mul_comm] using hprod

/-- Sum of pointwise `Nat.ModEq`s is again a `Nat.ModEq`. -/
lemma sum_modEq {α : Type} (l : List α) (f g : α → Nat) (n : Nat)
    (h : ∀ a ∈ l, f a ≡ g a [MOD n]) :
    (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l with
  | nil => simp [Nat.ModEq]
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.ModEq.add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Modular cancellation: `(a+b)%n = b%n` forces `a%n = 0`. -/
lemma mod_add_right_eq_self_imp_left_zero (a b n : Nat) (hn : 0 < n)
    (h : (a + b) % n = b % n) : a % n = 0 := by
  have h' : (a % n + b % n) % n = b % n := by
    rwa [Nat.add_mod] at h
  have ha : a % n < n := Nat.mod_lt a hn
  have hb : b % n < n := Nat.mod_lt b hn
  by_cases hsum : a % n + b % n < n
  · have hmod : (a % n + b % n) % n = a % n + b % n := Nat.mod_eq_of_lt hsum
    rw [hmod] at h'
    omega
  · have hge : n ≤ a % n + b % n := Nat.le_of_not_gt hsum
    have hsub : a % n + b % n - n < n := by omega
    have hmod : (a % n + b % n) % n = a % n + b % n - n := by
      have hx : a % n + b % n = n + (a % n + b % n - n) := by omega
      rw [hx, Nat.add_mod]
      simp
      exact Nat.mod_eq_of_lt hsub
    rw [hmod] at h'
    omega

/-- The rotated-word numerator has the exact 5-adic prefix-weight
expansion modulo `2^k`:
`A(rot) ≡ 5^{P-1}·Σ_{i=0}^{P-1} 2^{W_i}·inv^i [MOD 2^k]`,
where `inv = pow5Inv 1 k` is the inverse of `5` modulo `2^k`.
This is the correct cancellation law replacing any `min(2,W_1)`
heuristic: deeper cancellation is controlled by the whole prefix
weight sequence through the 5-adic telescope. -/
theorem wordA_cyclic_mod_two_pow_prefixWeight_sum
    (w : List Nat) (b k : Nat)
    (hb : b ≤ w.length) (hk : 1 ≤ k) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w b) ≡
      5 ^ (w.length - 1) *
        ((List.range w.length).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight
              (fun j => (CycleBridge.cyclicSegmentAt w b).getI j) i *
            S6Audit.pow5Inv 1 k ^ i)).sum [MOD 2 ^ k] := by
  let rot := CycleBridge.cyclicSegmentAt w b
  let P := w.length
  let inv := S6Audit.pow5Inv 1 k
  have hrot_len : (CycleBridge.cyclicSegmentAt w b).length = w.length :=
    CycleBridge.cyclicSegmentAt_length w b hb
  have hA : StringFlow.Word.wordA rot =
      StringFlow.PMI.aTotal P (fun j => rot.getI j) := by
    dsimp [rot, P]
    rw [wordA_eq_pmi_aTotal (CycleBridge.cyclicSegmentAt w b)]
    rw [hrot_len]
  have hinv : 5 * inv ≡ 1 [MOD 2 ^ k] := by
    dsimp [inv]
    exact StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k hk
  have hinv_pow : ∀ i : Nat, 5 ^ i * inv ^ i ≡ 1 [MOD 2 ^ k] := by
    intro i
    induction i with
    | zero =>
        simp [Nat.ModEq]
    | succ i ih =>
        have hstep : 5 ^ (i + 1) * inv ^ (i + 1) =
            (5 * inv) * (5 ^ i * inv ^ i) := by ring
        rw [hstep]
        exact Nat.ModEq.mul hinv ih
  have hpow : ∀ i : Nat, i < P →
      5 ^ (P - 1 - i) *
          (2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i) ≡
        5 ^ (P - 1) *
          (2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i * inv ^ i)
          [MOD 2 ^ k] := by
    intro i hi
    have hP1 : P - 1 - i + i = P - 1 := by omega
    have hmul : 5 ^ (P - 1 - i) * (5 ^ i * inv ^ i) =
        5 ^ (P - 1) * inv ^ i := by
      rw [← Nat.mul_assoc]
      rw [← Nat.pow_add, hP1]
    have hbase : 5 ^ (P - 1) * inv ^ i ≡ 5 ^ (P - 1 - i) [MOD 2 ^ k] := by
      have h := Nat.ModEq.mul_left (5 ^ (P - 1 - i)) (hinv_pow i)
      rw [hmul] at h
      simpa using h
    have hb' : 5 ^ (P - 1) * inv ^ i *
          (2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i) ≡
        5 ^ (P - 1 - i) *
          (2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i)
          [MOD 2 ^ k] :=
      Nat.ModEq.mul_right
        (2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i) hbase
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb'.symm
  rw [hA]
  unfold StringFlow.PMI.aTotal
  rw [← StringFlow.PMI.sum_map_mul_left (List.range P) (5 ^ (P - 1))
    (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i * inv ^ i)]
  apply sum_modEq
  intro i hi
  exact hpow i (List.mem_range.mp hi)

/-- Merged additive congruence: with `k ≤ S`, the rotated numerator
plus the cycle slack satisfies
`(A(rot)+Δ)+5^P ≡ 5^{P-1}·Σ_i 2^{W_i}·inv^i [MOD 2^k]`.
This is the exact bridge from `R_r = v2(A(rot)+Δ)` to the prefix
weight congruence. -/
theorem rotated_plus_delta_add_five_pow_mod_two_pow
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    (StringFlow.Word.wordA
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r)) +
        (2 ^ S - 5 ^ P)) + 5 ^ P ≡
      5 ^ (w.length - 1) *
        ((List.range w.length).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight
              (fun j => (CycleBridge.cyclicSegmentAt w
                (CycleBridge.cycleRiseBlockTailDepth d r)).getI j) i *
            S6Audit.pow5Inv 1 k ^ i)).sum [MOD 2 ^ k] := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let rot := CycleBridge.cyclicSegmentAt w b
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hlt := CycleBridge.cycleQb8Input_weak_comparison h
  have hdelta : (2 ^ S - 5 ^ P) + 5 ^ P = 2 ^ S := by omega
  have hA := wordA_cyclic_mod_two_pow_prefixWeight_sum w b k hb hk
  have h2 : 2 ^ S ≡ 0 [MOD 2 ^ k] := by
    have hdvd : 2 ^ k ∣ 2 ^ S := ⟨2 ^ (S - k), by
      rw [← Nat.pow_add]
      congr 1
      omega⟩
    rw [Nat.ModEq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  calc
    (StringFlow.Word.wordA rot + (2 ^ S - 5 ^ P)) + 5 ^ P
        = StringFlow.Word.wordA rot + 2 ^ S := by
            rw [Nat.add_assoc, hdelta]
    _ ≡ 5 ^ (w.length - 1) *
          ((List.range w.length).map
            (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i *
              S6Audit.pow5Inv 1 k ^ i)).sum + 0 [MOD 2 ^ k] :=
            Nat.ModEq.add hA h2
    _ ≡ 5 ^ (w.length - 1) *
          ((List.range w.length).map
            (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i *
              S6Audit.pow5Inv 1 k ^ i)).sum [MOD 2 ^ k] := by
            simpa [Nat.add_zero] using (Nat.ModEq.refl _)

/-- 精确逐块判定：`k ≤ R_r` 当且仅当
`Σ_i 2^{W_i}·inv^i ≡ 5 [MOD 2^k]`（`1 ≤ k ≤ S`）。
这是 2-adic × 5-adic 词残差桥：rank 阈值被转成前缀权重序列的
同余条件。 -/
theorem tailRank_ge_iff_prefixWeight_sum_congruence
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    k ≤ CycleBridge.cycleRiseBlockTailRank d r ↔
      (((List.range w.length).map
        (fun i => 2 ^ StringFlow.PMI.prefixWeight
            (fun j => (CycleBridge.cyclicSegmentAt w
              (CycleBridge.cycleRiseBlockTailDepth d r)).getI j) i *
          S6Audit.pow5Inv 1 k ^ i)).sum ≡ 5 [MOD 2 ^ k]) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let rot := CycleBridge.cyclicSegmentAt w b
  let inv := S6Audit.pow5Inv 1 k
  let N := StringFlow.Word.wordA rot + (2 ^ S - 5 ^ P)
  let Ssum := ((List.range w.length).map
      (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => rot.getI j) i * inv ^ i)).sum
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hR : CycleBridge.cycleRiseBlockTailRank d r = twoValuation N := by
    dsimp [N]
    exact CycleBridge.cycleRiseBlockTailRank_eq_v2_rotated_plus_delta h d r hr
  have hcong_add := rotated_plus_delta_add_five_pow_mod_two_pow h d r hr k hk hkS
  have hinv : 5 * inv ≡ 1 [MOD 2 ^ k] := by
    dsimp [inv]
    exact StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k hk
  have hinv_pow : ∀ i : Nat, 5 ^ i * inv ^ i ≡ 1 [MOD 2 ^ k] := by
    intro i
    induction i with
  | zero => simp [Nat.ModEq]
    | succ i ih =>
        have hstep : 5 ^ (i + 1) * inv ^ (i + 1) =
            (5 * inv) * (5 ^ i * inv ^ i) := by ring
        rw [hstep]
        exact Nat.ModEq.mul hinv ih
  have hNpos : 0 < N := by
    have hlt := CycleBridge.cycleQb8Input_weak_comparison h
    have hd : 0 < 2 ^ S - 5 ^ P := by omega
    dsimp [N]
    positivity
  have hPpos : 0 < P := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    omega
  have hpowP : 5 ^ P = 5 * 5 ^ (P - 1) := by
    rw [Nat.mul_comm]
    rw [← Nat.pow_succ]
    congr 1
    omega
  constructor
  · intro hkR
    have hdvd : 2 ^ k ∣ N := by
      rw [hR] at hkR
      exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow N k hNpos).mp hkR
    have hN0 : N ≡ 0 [MOD 2 ^ k] := by
      rw [Nat.ModEq]
      exact Nat.dvd_iff_mod_eq_zero.mp hdvd
    have hN5 : N + 5 ^ P ≡ 5 ^ P [MOD 2 ^ k] := by
      simpa using (Nat.ModEq.add hN0 (Nat.ModEq.refl (5 ^ P)))
    have hmain : 5 ^ P ≡ 5 ^ (P - 1) * Ssum [MOD 2 ^ k] := by
      simpa [b, rot, inv, Ssum, h.hlength] using (hN5.symm.trans hcong_add)
    have hstep : 5 ^ (P - 1) * Ssum ≡ 5 * 5 ^ (P - 1) [MOD 2 ^ k] := by
      simpa [hpowP] using hmain.symm
    have hcancel : Ssum ≡ 5 [MOD 2 ^ k] := by
      have hm := Nat.ModEq.mul_right (inv ^ (P - 1)) hstep
      have h1 : Ssum * (5 ^ (P - 1) * inv ^ (P - 1)) ≡ Ssum [MOD 2 ^ k] := by
        have h := Nat.ModEq.mul (Nat.ModEq.refl Ssum) (hinv_pow (P - 1))
        simpa using h
      have h2 : 5 * (5 ^ (P - 1) * inv ^ (P - 1)) ≡ 5 [MOD 2 ^ k] := by
        have h := Nat.ModEq.mul (Nat.ModEq.refl 5) (hinv_pow (P - 1))
        simpa using h
      have hm' : Ssum * (5 ^ (P - 1) * inv ^ (P - 1)) ≡
          5 * (5 ^ (P - 1) * inv ^ (P - 1)) [MOD 2 ^ k] := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm
      exact (h1.symm).trans (hm'.trans h2)
    simpa [b, rot, inv, Ssum] using hcancel
  · intro hcong
    have hstep : 5 ^ (P - 1) * Ssum ≡ 5 ^ P [MOD 2 ^ k] := by
      have h := Nat.ModEq.mul_left (5 ^ (P - 1)) hcong
      simpa [b, rot, inv, Ssum, hpowP, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    have hN5 : N + 5 ^ P ≡ 5 ^ P [MOD 2 ^ k] := by
      have hcong_add' : N + 5 ^ P ≡ 5 ^ (P - 1) * Ssum [MOD 2 ^ k] := by
        simpa [b, rot, inv, Ssum, h.hlength] using hcong_add
      exact hcong_add'.trans hstep
    have hdvd : 2 ^ k ∣ N := by
      rw [Nat.ModEq] at hN5
      have hN0 : N % 2 ^ k = 0 :=
        mod_add_right_eq_self_imp_left_zero N (5 ^ P) (2 ^ k) (by positivity) hN5
      exact Nat.dvd_iff_mod_eq_zero.mpr hN0
    rw [hR]
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow N k hNpos).mpr hdvd

/-- Under `allBelowBudget`, each block whose threshold fits inside
`S` fails the prefix-weight congruence:
`Σ_i 2^{W_i}·inv^i ≢ 5 [MOD 2^{2b_r+13}]`.
This is the pointwise 2-adic × 5-adic contradiction seed for the
crush proof. -/
theorem allBelowBudget_imp_prefixWeight_sum_not_congruent
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hbelow : Amiya.cycleRiseBlockAllBelowBudget d)
    (r : Nat) (hr : r < d.blockCount)
    (hkS : 2 * CycleBridge.cycleRiseBlockTailDepth d r + 13 ≤ S) :
    ¬ (((List.range w.length).map
        (fun i => 2 ^ StringFlow.PMI.prefixWeight
            (fun j => (CycleBridge.cyclicSegmentAt w
              (CycleBridge.cycleRiseBlockTailDepth d r)).getI j) i *
          S6Audit.pow5Inv 1 (2 * CycleBridge.cycleRiseBlockTailDepth d r + 13) ^ i)).sum ≡ 5
          [MOD 2 ^ (2 * CycleBridge.cycleRiseBlockTailDepth d r + 13)]) := by
  have hle : CycleBridge.cycleRiseBlockTailRank d r ≤
      2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 := by
    exact (cycleRiseBlockAllBelowBudget_iff_tailRank_le h d).mp hbelow r hr
  have hk : 1 ≤ 2 * CycleBridge.cycleRiseBlockTailDepth d r + 13 := by omega
  have hiff := tailRank_ge_iff_prefixWeight_sum_congruence h d r hr
    (2 * CycleBridge.cycleRiseBlockTailDepth d r + 13) hk hkS
  intro hcong
  have hge : 2 * CycleBridge.cycleRiseBlockTailDepth d r + 13 ≤
      CycleBridge.cycleRiseBlockTailRank d r := hiff.mpr hcong
  omega

/-- `5` 在模 `2^k` 下的阶整除 `2^{k-2}`：
`5^{2^{k-2}} ≡ 1 [MOD 2^k]`（`3 ≤ k`）。
证明用逐次平方：`5^{2^{m+1}} = (5^{2^m})^2`，且
`(1 + 2^{m+2}·u)^2 ≡ 1 [MOD 2^{m+3}]`。 -/
theorem five_pow_two_pow_eq_one_mod {k : Nat} (hk : 3 ≤ k) :
    (5 ^ 2 ^ (k - 2)) % 2 ^ k = 1 := by
  have hm : ∀ m : Nat, ∃ u : Nat,
      5 ^ 2 ^ m = 1 + 2 ^ (m + 2) * u := by
    intro m
    induction m with
    | zero =>
        refine ⟨1, ?_⟩
        norm_num
    | succ m ih =>
        rcases ih with ⟨u, hu⟩
        refine ⟨u + 2 ^ (m + 1) * u ^ 2, ?_⟩
        have hpow : 5 ^ 2 ^ (m + 1) = (5 ^ 2 ^ m) ^ 2 := by
          rw [← Nat.pow_mul]
          congr 1
        have halg : (1 + 2 ^ (m + 2) * u) ^ 2 =
            1 + 2 ^ (m + 3) * (u + 2 ^ (m + 1) * u ^ 2) := by
          rw [show (1 + 2 ^ (m + 2) * u) ^ 2 =
              1 + 2 * (2 ^ (m + 2) * u) + (2 ^ (m + 2) * u) ^ 2 by ring]
          have h2 : 2 * 2 ^ (m + 2) = 2 ^ (m + 3) := by
            rw [Nat.mul_comm]
            rw [← Nat.pow_succ]
          have hp : (2 ^ (m + 2) * u) ^ 2 = 2 ^ (m + 3) * (2 ^ (m + 1) * u ^ 2) := by
            rw [mul_pow]
            rw [← Nat.pow_mul]
            rw [show (m + 2) * 2 = 2 * (m + 2) by ring]
            have hpow2 : 2 ^ (2 * (m + 2)) = 2 ^ (m + 3) * 2 ^ (m + 1) := by
              rw [← Nat.pow_add]
              apply congrArg (fun n : Nat => 2 ^ n)
              omega
            rw [hpow2]
            ring
          rw [← Nat.mul_assoc]
          rw [h2, hp]
          ring
        rw [hpow, hu, halg]
  rcases hm (k - 2) with ⟨u, hu⟩
  have hk2 : k = (k - 2) + 2 := by omega
  have hpos : 1 < 2 ^ k := by
    have hk1 : 1 ≤ k := by omega
    exact one_lt_pow' (by decide : 1 < 2) (by omega : k ≠ 0)
  have hmod : (1 + 2 ^ k * u) % 2 ^ k = 1 := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hpos
  rw [hu]
  simpa [← hk2] using hmod

/-- 下一块 C3 头的旋转词 = `c3Word (r+1)` 接上下一块边界旋转的
前 `P − C_{r+1}` 个字符。这是循环旋转递推的正确形式：suffix 终点
是 C3 起点，不是下一块边界。 -/
theorem cyclicSegmentAt_head_eq_c3_append_take_of_block
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cyclicSegmentAt w (d.headDepth r) =
      d.c3Word r ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r)).take
          (w.length - (d.c3Word r).length) := by
  let h := d.headDepth r
  let C := (d.c3Word r).length
  let t := CycleBridge.cycleRiseBlockTailDepth d r
  have hsum : h + C = t := by
    dsimp [t, C]
    unfold CycleBridge.cycleRiseBlockTailDepth
    omega
  have hb : h ≤ w.length := by
    dsimp [h]
    have hlt := d.hhead_lt r hr
    rw [d.hperiod]
    omega
  have ht : t ≤ w.length := by
    dsimp [t]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hCle : C ≤ w.length := by
    dsimp [C]
    have hC1 : (d.c3Word r).length ≤ P := by
      have htail : CycleBridge.cycleRiseBlockTailDepth d r ≤ P := by
        have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
          CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
        omega
      have hC : (d.c3Word r).length ≤
          CycleBridge.cycleRiseBlockTailDepth d r := by
        unfold CycleBridge.cycleRiseBlockTailDepth
        omega
      omega
    rw [d.hperiod]
    exact hC1
  have hwpos : 0 < w.length := by
    have hlt := d.hhead_lt r hr
    rw [d.hperiod]
    omega
  have htake : (CycleBridge.cyclicSegmentAt w h).take C = d.c3Word r := by
    have hle2 : C ≤ w.length - h := by
      omega
    have htake_append : ((w.drop h) ++ (w.take h)).take C =
        (w.drop h).take C := by
      have hle3 : C ≤ (w.drop h).length := by
        rw [List.length_drop]
        exact hle2
      rw [List.take_append_of_le_length hle3]
    have hdrop2 : (w.drop h).take C = (w.take t).drop h := by
      have hC : C = t - h := by omega
      rw [hC]
      exact (List.drop_take (i := h) (j := t) (l := w)).symm
    have hc3 : d.c3Word r = (w.take t).drop h := by
      dsimp [h, t]
      exact CycleBridge.cycleRiseBlockC3Word_eq_prefix_drop d r hr
    unfold CycleBridge.cyclicSegmentAt
    rw [htake_append, hdrop2]
    exact hc3.symm
  have hmod : CycleBridge.cyclicSegmentAt w ((h + C) % w.length) =
      CycleBridge.cyclicSegmentAt w t := by
    by_cases htlt : t < w.length
    · have hmod_eq : (h + C) % w.length = t := by
        rw [hsum]
        exact Nat.mod_eq_of_lt htlt
      rw [hmod_eq]
    · have ht_eq : t = w.length := by omega
      have h0 : (h + C) % w.length = 0 := by
        rw [hsum, ht_eq]
        exact Nat.mod_self w.length
      rw [h0]
      rw [ht_eq]
      exact (CycleBridge.cyclicSegmentAt_self_eq_zero w).symm
  have hdrop := CycleBridge.cyclicSegmentAt_drop_take w h C hb hCle hwpos
  have hdrop' : (CycleBridge.cyclicSegmentAt w h).drop C =
      (CycleBridge.cyclicSegmentAt w t).take (w.length - C) := by
    rw [hmod] at hdrop
    exact hdrop
  calc
    CycleBridge.cyclicSegmentAt w h
        = (CycleBridge.cyclicSegmentAt w h).take C ++
            (CycleBridge.cyclicSegmentAt w h).drop C :=
            (List.take_append_drop C (CycleBridge.cyclicSegmentAt w h)).symm
    _ = d.c3Word r ++
          (CycleBridge.cyclicSegmentAt w t).take (w.length - C) := by
            rw [htake, hdrop']
    _ = d.c3Word r ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r)).take
            (w.length - (d.c3Word r).length) := by
            dsimp [t, C]

/-- 下一块 C3 头的旋转词 = `c3Word (r+1)` 接上下一块边界旋转的
前 `P − C_{r+1}` 个字符。这是循环旋转递推的正确形式：suffix 终点
是 C3 起点，不是下一块边界。 -/
theorem cyclicSegmentAt_head_eq_c3_append_take_nextBoundary
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    CycleBridge.cyclicSegmentAt w (d.headDepth (r + 1)) =
      d.c3Word (r + 1) ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
          (w.length - (d.c3Word (r + 1)).length) := by
  let h := d.headDepth (r + 1)
  let C := (d.c3Word (r + 1)).length
  let t := CycleBridge.cycleRiseBlockTailDepth d (r + 1)
  have hsum : h + C = t := by
    dsimp [t, C]
    unfold CycleBridge.cycleRiseBlockTailDepth
    omega
  have hb : h ≤ w.length := by
    dsimp [h]
    have hlt := d.hhead_lt (r + 1) hrnext
    rw [d.hperiod]
    omega
  have ht : t ≤ w.length := by
    dsimp [t]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hrnext
    rw [d.hperiod]
    omega
  have hCle : C ≤ w.length := by
    dsimp [C]
    have hC1 : (d.c3Word (r + 1)).length ≤ P := by
      have htail : CycleBridge.cycleRiseBlockTailDepth d (r + 1) ≤ P := by
        have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < P :=
          CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hrnext
        omega
      have hC : (d.c3Word (r + 1)).length ≤
          CycleBridge.cycleRiseBlockTailDepth d (r + 1) := by
        unfold CycleBridge.cycleRiseBlockTailDepth
        omega
      omega
    rw [d.hperiod]
    exact hC1
  have hwpos : 0 < w.length := by
    have hpos : 0 < d.blockCount := lt_of_le_of_lt (Nat.zero_le r) hr
    have hlt := d.hhead_lt 0 hpos
    rw [d.hperiod]
    omega
  have htake : (CycleBridge.cyclicSegmentAt w h).take C = d.c3Word (r + 1) := by
    have hle2 : C ≤ w.length - h := by
      omega
    have htake_append : ((w.drop h) ++ (w.take h)).take C =
        (w.drop h).take C := by
      have hle3 : C ≤ (w.drop h).length := by
        rw [List.length_drop]
        exact hle2
      rw [List.take_append_of_le_length hle3]
    have hdrop2 : (w.drop h).take C = (w.take t).drop h := by
      have hC : C = t - h := by omega
      rw [hC]
      exact (List.drop_take (i := h) (j := t) (l := w)).symm
    have hc3 : d.c3Word (r + 1) = (w.take t).drop h := by
      dsimp [h, t]
      exact CycleBridge.cycleRiseBlockC3Word_eq_prefix_drop d (r + 1) hrnext
    unfold CycleBridge.cyclicSegmentAt
    rw [htake_append, hdrop2]
    exact hc3.symm
  have hmod : CycleBridge.cyclicSegmentAt w ((h + C) % w.length) =
      CycleBridge.cyclicSegmentAt w t := by
    by_cases htlt : t < w.length
    · have hmod_eq : (h + C) % w.length = t := by
        rw [hsum]
        exact Nat.mod_eq_of_lt htlt
      rw [hmod_eq]
    · have ht_eq : t = w.length := by omega
      have h0 : (h + C) % w.length = 0 := by
        rw [hsum, ht_eq]
        exact Nat.mod_self w.length
      rw [h0]
      rw [ht_eq]
      exact (CycleBridge.cyclicSegmentAt_self_eq_zero w).symm
  have hdrop := CycleBridge.cyclicSegmentAt_drop_take w h C hb hCle hwpos
  have hdrop' : (CycleBridge.cyclicSegmentAt w h).drop C =
      (CycleBridge.cyclicSegmentAt w t).take (w.length - C) := by
    rw [hmod] at hdrop
    exact hdrop
  calc
    CycleBridge.cyclicSegmentAt w h
        = (CycleBridge.cyclicSegmentAt w h).take C ++
            (CycleBridge.cyclicSegmentAt w h).drop C :=
            (List.take_append_drop C (CycleBridge.cyclicSegmentAt w h)).symm
    _ = d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w t).take (w.length - C) := by
            rw [htake, hdrop']
    _ = d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - (d.c3Word (r + 1)).length) := by
            dsimp [t, C]

/-- 组合两个旋转恒等式：从边界 `b_r` 开始的旋转词 =
`suffix r ++ c3Word (r+1) ++ 下一块边界旋转的前 P−L−C`。 -/
theorem cyclicSegmentAt_tail_eq_suffix_c3_append_take
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r) =
      d.suffixWord r ++ d.c3Word (r + 1) ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
          (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let L := (d.suffixWord r).length
  let C := (d.c3Word (r + 1)).length
  have htail := CycleBridge.cyclicSegmentAt_tail_eq_suffix_append d r hr hLle hwpos
  have hhead := cyclicSegmentAt_head_eq_c3_append_take_nextBoundary d r hr hrnext
  have hbL : (b + L) % w.length = d.headDepth (r + 1) := by
    have hnext_eq : b + L = d.headDepth (r + 1) := by
      dsimp [b, L]
      rw [show CycleBridge.cycleRiseBlockTailDepth d r =
          d.headDepth r + (d.c3Word r).length by rfl]
      have hh := d.hnext r hr
      rw [if_pos hrnext] at hh
      omega
    have hlt : d.headDepth (r + 1) < w.length := by
      have hlt' := d.hhead_lt (r + 1) hrnext
      rw [d.hperiod]
      exact hlt'
    rw [hnext_eq]
    exact Nat.mod_eq_of_lt hlt
  have hCle : C ≤ w.length - L := by
    have hbL2 : b + L + C = CycleBridge.cycleRiseBlockTailDepth d (r + 1) := by
      dsimp [b, L, C]
      rw [show CycleBridge.cycleRiseBlockTailDepth d r =
          d.headDepth r + (d.c3Word r).length by rfl]
      rw [show CycleBridge.cycleRiseBlockTailDepth d (r + 1) =
          d.headDepth (r + 1) + (d.c3Word (r + 1)).length by rfl]
      have hh := d.hnext r hr
      rw [if_pos hrnext] at hh
      omega
    have htail_le : CycleBridge.cycleRiseBlockTailDepth d (r + 1) ≤ w.length := by
      have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < P :=
        CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hrnext
      rw [d.hperiod]
      omega
    omega
  have hrest : (CycleBridge.cyclicSegmentAt w (d.headDepth (r + 1))).take (w.length - L) =
      d.c3Word (r + 1) ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
          (w.length - L - C) := by
    rw [hhead]
    have htake_append : (d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - C)).take (w.length - L) =
        d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - L - C) := by
      rw [List.take_append]
      have hc3take : (d.c3Word (r + 1)).take (w.length - L) = d.c3Word (r + 1) :=
        List.take_of_length_le (by
          have hCle' : C ≤ w.length - L := hCle
          simpa [C] using hCle')
      rw [hc3take]
      congr 1
      rw [List.take_take]
      congr 1
      omega
    simpa using htake_append
  calc
    CycleBridge.cyclicSegmentAt w b
        = d.suffixWord r ++
            (CycleBridge.cyclicSegmentAt w ((b + L) % w.length)).take
              (w.length - L) := by
            simpa [b, L] using htail
    _ = d.suffixWord r ++
          (CycleBridge.cyclicSegmentAt w (d.headDepth (r + 1))).take
            (w.length - L) := by
            rw [hbL]
    _ = d.suffixWord r ++ d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - L - C) := by
            rw [hrest]
            rw [← List.append_assoc]
    _ = d.suffixWord r ++ d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length) := by
            dsimp [L, C]

/-- `cyclicSegmentAt` 对同余起点相容：`b + P ≡ b` 的旋转词相同。 -/
lemma cyclicSegmentAt_mod_add_length (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    CycleBridge.cyclicSegmentAt w ((b + w.length) % w.length) =
      CycleBridge.cyclicSegmentAt w b := by
  by_cases hblt : b < w.length
  · have hmod : (b + w.length) % w.length = b := by
      rw [Nat.add_mod]
      rw [Nat.mod_self]
      rw [Nat.add_zero]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt hblt
    rw [hmod]
  · have hb_eq : b = w.length := by omega
    rw [hb_eq]
    rw [Nat.add_mod]
    rw [Nat.mod_self]
    simp
    exact (CycleBridge.cyclicSegmentAt_self_eq_zero w).symm

/-- `cyclicSegmentAt` 对取模同余起点相容：`b % P ≡ b`。 -/
lemma cyclicSegmentAt_mod_eq (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    CycleBridge.cyclicSegmentAt w (b % w.length) =
      CycleBridge.cyclicSegmentAt w b := by
  by_cases hblt : b < w.length
  · have hmod : b % w.length = b := Nat.mod_eq_of_lt hblt
    rw [hmod]
  · have hb_eq : b = w.length := by omega
    rw [hb_eq]
    rw [Nat.mod_self]
    exact (CycleBridge.cyclicSegmentAt_self_eq_zero w).symm

/-- 回绕块的旋转词（最后一块 → 第 0 块）：`rot(b_r)` 从
`suffixWord r` 开始，接 `c3Word 0`，再接第 0 块边界旋转的前
`P−L−C` 个字符。 -/
theorem cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hlast : r + 1 = d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r) =
      d.suffixWord r ++ d.c3Word 0 ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
          (w.length - (d.suffixWord r).length - (d.c3Word 0).length) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let L := (d.suffixWord r).length
  let C := (d.c3Word 0).length
  have hpos0 : 0 < d.blockCount := lt_of_le_of_lt (Nat.zero_le r) hr
  have htail := CycleBridge.cyclicSegmentAt_tail_eq_suffix_append d r hr hLle hwpos
  have hhead := cyclicSegmentAt_head_eq_c3_append_take_of_block d 0 hpos0
  have hbL : (b + L) % w.length = d.headDepth 0 := by
    have hnext_eq : b + L = d.headDepth 0 + w.length := by
      dsimp [b, L]
      rw [d.hperiod]
      have hh := d.hnext r hr
      rw [if_neg (by omega : ¬ r + 1 < d.blockCount)] at hh
      have htail_def' : CycleBridge.cycleRiseBlockTailDepth d r =
          d.headDepth r + (d.c3Word r).length := rfl
      rw [← htail_def'] at hh
      omega
    have hlt : d.headDepth 0 < w.length := by
      have hlt' := d.hhead_lt 0 hpos0
      rw [d.hperiod]
      exact hlt'
    have hmod : (d.headDepth 0 + w.length) % w.length = d.headDepth 0 := by
      rw [Nat.add_mod]
      rw [Nat.mod_self]
      rw [Nat.add_zero]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt hlt
    rw [hnext_eq]
    exact hmod
  have hCle : C ≤ w.length - L := by
    have htail_ge : CycleBridge.cycleRiseBlockTailDepth d 0 ≤ b := by
      have hge := cycleRiseBlock_tailDepth_last_ge_zero d (by omega : 1 ≤ d.blockCount)
      have hr_last : r = d.blockCount - 1 := by omega
      have hge' : CycleBridge.cycleRiseBlockTailDepth d 0 ≤
          CycleBridge.cycleRiseBlockTailDepth d r := by
        simpa [← hr_last] using hge
      dsimp [b]
      exact hge'
    have hbL2 : b + L = d.headDepth 0 + w.length := by
      dsimp [b, L]
      rw [d.hperiod]
      have hh := d.hnext r hr
      rw [if_neg (by omega : ¬ r + 1 < d.blockCount)] at hh
      have htail_def' : CycleBridge.cycleRiseBlockTailDepth d r =
          d.headDepth r + (d.c3Word r).length := rfl
      rw [← htail_def'] at hh
      omega
    have ht0 : CycleBridge.cycleRiseBlockTailDepth d 0 = d.headDepth 0 + C := by
      dsimp [C]
      rfl
    unfold CycleBridge.cycleRiseBlockTailDepth at htail_ge hbL2 ht0
    dsimp [b, L, C] at htail_ge hbL2 ht0 ⊢
    omega
  have hrest : (CycleBridge.cyclicSegmentAt w (d.headDepth 0)).take (w.length - L) =
      d.c3Word 0 ++
        (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
          (w.length - L - C) := by
    rw [hhead]
    have htake_append : (d.c3Word 0 ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
            (w.length - C)).take (w.length - L) =
        d.c3Word 0 ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
            (w.length - L - C) := by
      rw [List.take_append]
      have hc3take : (d.c3Word 0).take (w.length - L) = d.c3Word 0 :=
        List.take_of_length_le (by
          have hCle' : C ≤ w.length - L := hCle
          simpa [C] using hCle')
      rw [hc3take]
      congr 1
      rw [List.take_take]
      congr 1
      omega
    simpa using htake_append
  calc
    CycleBridge.cyclicSegmentAt w b
        = d.suffixWord r ++
            (CycleBridge.cyclicSegmentAt w ((b + L) % w.length)).take
              (w.length - L) := by
            simpa [b, L] using htail
    _ = d.suffixWord r ++
          (CycleBridge.cyclicSegmentAt w (d.headDepth 0)).take
            (w.length - L) := by
            rw [hbL]
    _ = d.suffixWord r ++ d.c3Word 0 ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
            (w.length - L - C) := by
            rw [hrest]
            rw [← List.append_assoc]
    _ = d.suffixWord r ++ d.c3Word 0 ++
          (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
            (w.length - (d.suffixWord r).length - (d.c3Word 0).length) := by
            dsimp [L, C]

/-- 回绕块第 0 块边界的旋转词 = 自己的前 `P−L−C` 个字符接
`suffixWord r ++ c3Word 0`（`r` 是最后一块）。 -/
theorem cyclicSegmentAt_next_eq_take_append_suffix_c3_wrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hlast : r + 1 = d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0) =
      (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
        (w.length - (d.suffixWord r).length - (d.c3Word 0).length) ++
      d.suffixWord r ++ d.c3Word 0 := by
  let b0 := CycleBridge.cycleRiseBlockTailDepth d 0
  let br := CycleBridge.cycleRiseBlockTailDepth d r
  let L := (d.suffixWord r).length
  let C := (d.c3Word 0).length
  have hpos0 : 0 < d.blockCount := lt_of_le_of_lt (Nat.zero_le r) hr
  have hb0 : b0 ≤ w.length := by
    dsimp [b0]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos0
    omega
  have hbr : br ≤ w.length := by
    dsimp [br]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    omega
  have hbLC : br + L + C = b0 + w.length := by
    dsimp [b0, br, L, C]
    rw [d.hperiod]
    rw [show CycleBridge.cycleRiseBlockTailDepth d r =
        d.headDepth r + (d.c3Word r).length by rfl]
    rw [show CycleBridge.cycleRiseBlockTailDepth d 0 =
        d.headDepth 0 + (d.c3Word 0).length by rfl]
    have hh := d.hnext r hr
    rw [if_neg (by omega : ¬ r + 1 < d.blockCount)] at hh
    omega
  have hCle : C ≤ w.length - L := by
    have htail_ge : b0 ≤ br := by
      have hge := cycleRiseBlock_tailDepth_last_ge_zero d (by omega : 1 ≤ d.blockCount)
      have hr_last : r = d.blockCount - 1 := by omega
      have hge' : CycleBridge.cycleRiseBlockTailDepth d 0 ≤
          CycleBridge.cycleRiseBlockTailDepth d r := by
        simpa [← hr_last] using hge
      dsimp [b0, br]
      exact hge'
    omega
  have hsum : b0 + (w.length - L - C) = br := by
    dsimp [b0, br, L, C] at hbLC ⊢
    omega
  have htail_wrap := cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap d r hr hlast hLle hwpos
  have hfirst : (CycleBridge.cyclicSegmentAt w br).take (L + C) =
      d.suffixWord r ++ d.c3Word 0 := by
    have htail' : CycleBridge.cyclicSegmentAt w br =
        d.suffixWord r ++ d.c3Word 0 ++
          (CycleBridge.cyclicSegmentAt w b0).take (w.length - L - C) := by
      dsimp [b0, br, L, C]
      exact htail_wrap
    rw [htail']
    rw [List.take_append]
    have hsc_len : (d.suffixWord r ++ d.c3Word 0).length = L + C := by
      simp [L, C]
    have hle : (d.suffixWord r ++ d.c3Word 0).length ≤ L + C := by
      rw [hsc_len]
    rw [List.take_of_length_le hle]
    simp [hsc_len]
  have hdrop0 := CycleBridge.cyclicSegmentAt_drop_take w b0 (w.length - L - C) hb0
    (by omega) hwpos
  have hdrop : (CycleBridge.cyclicSegmentAt w b0).drop (w.length - L - C) =
      (CycleBridge.cyclicSegmentAt w br).take (L + C) := by
    rw [hdrop0]
    rw [hsum]
    rw [cyclicSegmentAt_mod_eq w br hbr]
    have hsub : w.length - (w.length - L - C) = L + C := by omega
    rw [hsub]
  calc
    CycleBridge.cyclicSegmentAt w b0
        = (CycleBridge.cyclicSegmentAt w b0).take (w.length - L - C) ++
            (CycleBridge.cyclicSegmentAt w b0).drop (w.length - L - C) :=
            (List.take_append_drop (w.length - L - C) (CycleBridge.cyclicSegmentAt w b0)).symm
    _ = (CycleBridge.cyclicSegmentAt w b0).take (w.length - L - C) ++
          d.suffixWord r ++ d.c3Word 0 := by
            rw [hdrop, hfirst]
            rw [← List.append_assoc]
    _ = (CycleBridge.cyclicSegmentAt w
            (CycleBridge.cycleRiseBlockTailDepth d 0)).take
              (w.length - (d.suffixWord r).length - (d.c3Word 0).length) ++
          d.suffixWord r ++ d.c3Word 0 := by
            dsimp [b0, L, C]

/-- 下一块边界的旋转词 = 自己的前 `P−L−C` 个字符再接上
`suffixWord r ++ c3Word (r+1)`（即上一块从 `b_r` 到 `b_{r+1}` 的段）。
这是块间旋转递推的正确形式：回绕尾部同时包含 suffix 和下一段 C3。 -/
theorem cyclicSegmentAt_next_eq_take_append_suffix_c3
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1)) =
      (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
        (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length) ++
      d.suffixWord r ++ d.c3Word (r + 1) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let b1 := CycleBridge.cycleRiseBlockTailDepth d (r + 1)
  let L := (d.suffixWord r).length
  let C := (d.c3Word (r + 1)).length
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    omega
  have hb1 : b1 ≤ w.length := by
    dsimp [b1]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hrnext
    omega
  have hbLC : b + L + C = b1 := by
    dsimp [b, b1, C]
    rw [show CycleBridge.cycleRiseBlockTailDepth d r =
        d.headDepth r + (d.c3Word r).length by rfl]
    rw [show CycleBridge.cycleRiseBlockTailDepth d (r + 1) =
        d.headDepth (r + 1) + (d.c3Word (r + 1)).length by rfl]
    have hh := d.hnext r hr
    rw [if_pos hrnext] at hh
    omega
  have hCle : C ≤ w.length - L := by
    have hLC : L + C ≤ w.length := by
      omega
    omega
  have hsum : b1 + (w.length - L - C) = b + w.length := by
    rw [← hbLC]
    omega
  have htail := cyclicSegmentAt_tail_eq_suffix_c3_append_take d r hr hrnext hLle hwpos
  have hfirst : (CycleBridge.cyclicSegmentAt w b).take (L + C) =
      d.suffixWord r ++ d.c3Word (r + 1) := by
    have htail' : CycleBridge.cyclicSegmentAt w b =
        d.suffixWord r ++ d.c3Word (r + 1) ++
          (CycleBridge.cyclicSegmentAt w b1).take (w.length - L - C) := by
      dsimp [b, b1, L, C]
      exact htail
    rw [htail']
    rw [List.take_append]
    have hsc_len : (d.suffixWord r ++ d.c3Word (r + 1)).length = L + C := by
      simp [L, C]
    have ht1 : (d.suffixWord r ++ d.c3Word (r + 1)).take (L + C) =
        d.suffixWord r ++ d.c3Word (r + 1) := by
      have hle : (d.suffixWord r ++ d.c3Word (r + 1)).length ≤ L + C := by
        rw [hsc_len]
      exact List.take_of_length_le hle
    rw [ht1]
    simp [hsc_len]
  have hdrop0 := CycleBridge.cyclicSegmentAt_drop_take w b1 (w.length - L - C) hb1
    (by omega) hwpos
  have hdrop : (CycleBridge.cyclicSegmentAt w b1).drop (w.length - L - C) =
      (CycleBridge.cyclicSegmentAt w b).take (L + C) := by
    rw [hdrop0]
    rw [hsum]
    rw [cyclicSegmentAt_mod_add_length w b hb]
    have hsub : w.length - (w.length - L - C) = L + C := by omega
    rw [hsub]
  calc
    CycleBridge.cyclicSegmentAt w b1
        = (CycleBridge.cyclicSegmentAt w b1).take (w.length - L - C) ++
            (CycleBridge.cyclicSegmentAt w b1).drop (w.length - L - C) :=
            (List.take_append_drop (w.length - L - C) (CycleBridge.cyclicSegmentAt w b1)).symm
    _ = (CycleBridge.cyclicSegmentAt w b1).take (w.length - L - C) ++
          d.suffixWord r ++ d.c3Word (r + 1) := by
            rw [hdrop, hfirst]
            rw [← List.append_assoc]
    _ = (CycleBridge.cyclicSegmentAt w
            (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
              (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length) ++
          d.suffixWord r ++ d.c3Word (r + 1) := by
            rfl

/-- 块间旋转词的 `wordA` 递推：下一块旋转词 = 自己的前 `P−L−C`
个字符接 `suffixWord r ++ c3Word (r+1)`，按 `wordA_append_shift` 展开。 -/
theorem rotatedWordA_recurrence
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))) =
      5 ^ ((d.suffixWord r).length + (d.c3Word (r + 1)).length) *
          StringFlow.Word.wordA ((CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length)) +
        2 ^ StringFlow.wordWeight ((CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length)) *
          StringFlow.Word.wordA (d.suffixWord r ++ d.c3Word (r + 1)) := by
  have hsplit := cyclicSegmentAt_next_eq_take_append_suffix_c3 d r hr hrnext hLle hwpos
  let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
            (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length)
  let sc := d.suffixWord r ++ d.c3Word (r + 1)
  have hA := CycleBridge.wordA_append_shift X sc
  nth_rewrite 1 [hsplit]
  simpa [X, sc, List.length_append] using hA

/-- 前缀权重和：`Σ_i 2^{W_i(l)}·inv^i`，其中 `inv = pow5Inv 1 k`。 -/
def prefixWeightSumList (l : List Nat) (k : Nat) : Nat :=
  ((List.range l.length).map
    (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => l.getI j) i *
      S6Audit.pow5Inv 1 k ^ i)).sum

/-- 单个字符追加的前缀权重和：多出 `2^{wordWeight l}·inv^{l.length}`。 -/
lemma prefixWeightSumList_append_singleton (l : List Nat) (t k : Nat) :
    prefixWeightSumList (l ++ [t]) k =
      prefixWeightSumList l k +
        2 ^ StringFlow.wordWeight l * S6Audit.pow5Inv 1 k ^ l.length := by
  unfold prefixWeightSumList
  rw [List.length_append, List.length_singleton, List.range_succ,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hmap : (List.range l.length).map
      (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => (l ++ [t]).getI j) i *
        S6Audit.pow5Inv 1 k ^ i) =
    (List.range l.length).map
      (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => l.getI j) i *
        S6Audit.pow5Inv 1 k ^ i) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i ≤ l.length := le_of_lt (List.mem_range.mp hi)
    have hpref := Amiya.prefixWeight_take_le_eq (l ++ [t]) l.length i hi'
    have htake : (l ++ [t]).take l.length = l := by simp
    rw [htake] at hpref
    rw [hpref]
  have hpref : StringFlow.PMI.prefixWeight (fun j => (l ++ [t]).getI j) l.length =
      StringFlow.wordWeight l := by
    rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum (l ++ [t]) l.length]
    rw [Amiya.wordWeight_eq_pmi_prefixWeight l]
    rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum l l.length]
    have htake : (l ++ [t]).take l.length = l := by simp
    rw [htake]
    have htakeL : l.take l.length = l := by simp
    rw [htakeL]
  have hlast : 2 ^ StringFlow.PMI.prefixWeight (fun j => (l ++ [t]).getI j) l.length *
        S6Audit.pow5Inv 1 k ^ l.length =
      2 ^ StringFlow.wordWeight l * S6Audit.pow5Inv 1 k ^ l.length := by
    rw [hpref]
  rw [hmap, hlast]

/-- 拼接前缀权重和：`PWS(u ++ v) = PWS u + 2^{W(u)}·inv^{|u|}·PWS v`。 -/
lemma prefixWeightSumList_append (u v : List Nat) (k : Nat) :
    prefixWeightSumList (u ++ v) k =
      prefixWeightSumList u k +
        2 ^ StringFlow.wordWeight u * S6Audit.pow5Inv 1 k ^ u.length *
          prefixWeightSumList v k := by
  induction v using List.reverseRecOn with
  | nil => simp [prefixWeightSumList]
  | append_singleton v0 t ih =>
      calc
        prefixWeightSumList (u ++ (v0 ++ [t])) k
            = prefixWeightSumList ((u ++ v0) ++ [t]) k := by
                rw [← List.append_assoc]
        _ = prefixWeightSumList (u ++ v0) k +
              2 ^ StringFlow.wordWeight (u ++ v0) *
                S6Audit.pow5Inv 1 k ^ (u ++ v0).length :=
                prefixWeightSumList_append_singleton (u ++ v0) t k
        _ = (prefixWeightSumList u k +
              2 ^ StringFlow.wordWeight u * S6Audit.pow5Inv 1 k ^ u.length *
                prefixWeightSumList v0 k) +
              2 ^ StringFlow.wordWeight (u ++ v0) *
                S6Audit.pow5Inv 1 k ^ (u ++ v0).length := by
                rw [ih]
        _ = prefixWeightSumList u k +
              2 ^ StringFlow.wordWeight u * S6Audit.pow5Inv 1 k ^ u.length *
                (prefixWeightSumList v0 k +
                  2 ^ StringFlow.wordWeight v0 *
                    S6Audit.pow5Inv 1 k ^ v0.length) := by
                rw [StringFlow.Word.wordWeight_append u v0]
                rw [List.length_append]
                rw [Nat.pow_add]
                ring
        _ = prefixWeightSumList u k +
              2 ^ StringFlow.wordWeight u * S6Audit.pow5Inv 1 k ^ u.length *
                prefixWeightSumList (v0 ++ [t]) k := by
                rw [prefixWeightSumList_append_singleton v0 t k]

/-- 前缀权重和拼接后不小于左侧部分。 -/
lemma prefixWeightSumList_append_le_left (u v : List Nat) (k : Nat) :
    prefixWeightSumList u k ≤ prefixWeightSumList (u ++ v) k := by
  rw [prefixWeightSumList_append]
  omega

/-- 前缀权重和的块间递推（`E_{r+1}` 同余）：
`2^{W(sc)}·E_{r+1} ≡ 5^{L+C}·(E_r − E_{sc}) [MOD 2^k]`，
其中 `sc = suffixWord r ++ c3Word (r+1)`。这是块间旋转递推在同余
层的精确翻译，`2^S` 项因 `k ≤ S` 消失。 -/
theorem prefixWeightSum_recurrence
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    2 ^ StringFlow.wordWeight (d.suffixWord r ++ d.c3Word (r + 1)) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d (r + 1))) k ≡
      5 ^ ((d.suffixWord r).length + (d.c3Word (r + 1)).length) *
        (prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d r)) k -
          prefixWeightSumList (d.suffixWord r ++ d.c3Word (r + 1)) k)
        [MOD 2 ^ k] := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let b1 := CycleBridge.cycleRiseBlockTailDepth d (r + 1)
  let L := (d.suffixWord r).length
  let C := (d.c3Word (r + 1)).length
  let sc := d.suffixWord r ++ d.c3Word (r + 1)
  let X := (CycleBridge.cyclicSegmentAt w b1).take (w.length - L - C)
  let inv := S6Audit.pow5Inv 1 k
  have hwpos : 0 < w.length := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    rw [d.hperiod]
    omega
  have hb1 : b1 ≤ w.length := by
    dsimp [b1]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hrnext
    omega
  have hsplit_r : CycleBridge.cyclicSegmentAt w b = sc ++ X := by
    have h := cyclicSegmentAt_tail_eq_suffix_c3_append_take d r hr hrnext hLle hwpos
    dsimp [b, b1, L, C, sc, X]
    exact h
  have hsplit_1 : CycleBridge.cyclicSegmentAt w b1 = X ++ sc := by
    have h := cyclicSegmentAt_next_eq_take_append_suffix_c3 d r hr hrnext hLle hwpos
    dsimp [b, b1, L, C, sc, X]
    rw [← List.append_assoc]
    exact h
  have hE_r : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k =
      prefixWeightSumList sc k +
        2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k := by
    rw [hsplit_r]
    rw [prefixWeightSumList_append sc X k]
    have hlen_sc : sc.length = L + C := by
      dsimp [sc, L, C]
      simp
    simp [inv, hlen_sc]
  have hE_1 : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b1) k =
      prefixWeightSumList X k +
        2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
          prefixWeightSumList sc k := by
    rw [hsplit_1]
    rw [prefixWeightSumList_append X sc k]
    have hlen_rot : (CycleBridge.cyclicSegmentAt w b1).length = w.length :=
      CycleBridge.cyclicSegmentAt_length w b1 hb1
    have hlen_X : X.length = w.length - L - C := by
      dsimp [X]
      exact List.length_take_of_le (by rw [hlen_rot]; omega)
    simp [inv, hlen_X]
  have hsub : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
        prefixWeightSumList sc k =
      2 ^ StringFlow.wordWeight sc * inv ^ (L + C) * prefixWeightSumList X k := by
    rw [hE_r]
    simp
  have hsub_mod : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
        prefixWeightSumList sc k ≡
      2 ^ StringFlow.wordWeight sc * inv ^ (L + C) * prefixWeightSumList X k [MOD 2 ^ k] := by
    rw [hsub]
  have hinv : 5 * inv ≡ 1 [MOD 2 ^ k] := by
    dsimp [inv]
    exact StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k hk
  have hinv_pow : ∀ n : Nat, 5 ^ n * inv ^ n ≡ 1 [MOD 2 ^ k] := by
    intro n
    induction n with
    | zero => simp [Nat.ModEq]
    | succ n ih =>
        have hstep : 5 ^ (n + 1) * inv ^ (n + 1) = (5 * inv) * (5 ^ n * inv ^ n) := by ring
        rw [hstep]
        exact Nat.ModEq.mul hinv ih
  have hcong_main : 5 ^ (L + C) *
        (prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
          prefixWeightSumList sc k) ≡
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
    have hmul := Nat.ModEq.mul_left (5 ^ (L + C)) hsub_mod
    have hpow := hinv_pow (L + C)
    have hrearr : 5 ^ (L + C) * (2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k) =
        2 ^ StringFlow.wordWeight sc * (5 ^ (L + C) * inv ^ (L + C)) *
          prefixWeightSumList X k := by ring
    have hcong2 : 5 ^ (L + C) * (2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k) ≡
        2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
      rw [hrearr]
      have hm := Nat.ModEq.mul hpow (Nat.ModEq.refl (prefixWeightSumList X k))
      have hm2 := Nat.ModEq.mul_left (2 ^ StringFlow.wordWeight sc) hm
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm2
    exact hmul.trans hcong2
  have hE_1' : 2 ^ StringFlow.wordWeight sc *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w b1) k =
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
        2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
          inv ^ (w.length - L - C) * prefixWeightSumList sc k := by
    calc
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList (CycleBridge.cyclicSegmentAt w b1) k
          = 2 ^ StringFlow.wordWeight sc * (prefixWeightSumList X k +
              2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
                prefixWeightSumList sc k) := by
                rw [hE_1]
      _ = 2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
            2 ^ StringFlow.wordWeight sc *
              (2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
                prefixWeightSumList sc k) := by ring
      _ = 2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
            2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
              inv ^ (w.length - L - C) * prefixWeightSumList sc k := by
                have hpow_add : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) =
                    2 ^ StringFlow.wordWeight sc * 2 ^ StringFlow.wordWeight X := by
                  rw [Nat.pow_add]
                rw [hpow_add]
                ring
  have hweight_rot : StringFlow.wordWeight (CycleBridge.cyclicSegmentAt w b1) = S := by
    unfold CycleBridge.cyclicSegmentAt
    have hsplit : w.take b1 ++ w.drop b1 = w := List.take_append_drop b1 w
    have hww := StringFlow.Word.wordWeight_append (w.drop b1) (w.take b1)
    rw [hww]
    rw [← h.hweight]
    have hww' := StringFlow.Word.wordWeight_append (w.take b1) (w.drop b1)
    rw [hsplit] at hww'
    rw [Nat.add_comm]
    exact hww'.symm
  have hweight_X_sc : StringFlow.wordWeight X + StringFlow.wordWeight sc = S := by
    have hww := StringFlow.Word.wordWeight_append X sc
    rw [← hsplit_1] at hww
    rw [hweight_rot] at hww
    exact hww.symm
  have h2S : 2 ^ S ≡ 0 [MOD 2 ^ k] := by
    have hdvd : 2 ^ k ∣ 2 ^ S := ⟨2 ^ (S - k), by
      rw [← Nat.pow_add]
      congr 1
      omega⟩
    rw [Nat.ModEq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hvan : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
        inv ^ (w.length - L - C) * prefixWeightSumList sc k ≡ 0 [MOD 2 ^ k] := by
    have hpow : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) ≡ 0 [MOD 2 ^ k] := by
      rw [show StringFlow.wordWeight sc + StringFlow.wordWeight X = S by omega]
      exact h2S
    have hm := Nat.ModEq.mul hpow
      (Nat.ModEq.refl (inv ^ (w.length - L - C) * prefixWeightSumList sc k))
    simpa [Nat.mul_assoc] using hm
  have hcong : 2 ^ StringFlow.wordWeight sc *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w b1) k ≡
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
    rw [hE_1']
    simpa using (Nat.ModEq.add
      (Nat.ModEq.refl (2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k)) hvan)
  simpa [b, b1, L, C, sc, X, inv] using hcong.trans hcong_main.symm

/-- 回绕块的 `wordA` 递推：`rot(b_0) = X ++ suffixWord r ++ c3Word 0`。 -/
theorem rotatedWordA_recurrence_wrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hlast : r + 1 = d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) =
      5 ^ ((d.suffixWord r).length + (d.c3Word 0).length) *
          StringFlow.Word.wordA ((CycleBridge.cyclicSegmentAt w
            (CycleBridge.cycleRiseBlockTailDepth d 0)).take
              (w.length - (d.suffixWord r).length - (d.c3Word 0).length)) +
        2 ^ StringFlow.wordWeight ((CycleBridge.cyclicSegmentAt w
            (CycleBridge.cycleRiseBlockTailDepth d 0)).take
              (w.length - (d.suffixWord r).length - (d.c3Word 0).length)) *
          StringFlow.Word.wordA (d.suffixWord r ++ d.c3Word 0) := by
  have hsplit := cyclicSegmentAt_next_eq_take_append_suffix_c3_wrap d r hr hlast hLle hwpos
  let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
            (w.length - (d.suffixWord r).length - (d.c3Word 0).length)
  let sc := d.suffixWord r ++ d.c3Word 0
  have hA := CycleBridge.wordA_append_shift X sc
  nth_rewrite 1 [hsplit]
  simpa [X, sc, List.length_append] using hA

/-- 前缀权重和的回绕块递推：最后一块到第 0 块的
`2^{W(sc)}·E_0 ≡ 5^{L+C}·(E_r − E_{sc}) [MOD 2^k]`。 -/
theorem prefixWeightSum_recurrence_wrap
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hlast : r + 1 = d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    2 ^ StringFlow.wordWeight (d.suffixWord r ++ d.c3Word 0) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d 0)) k ≡
      5 ^ ((d.suffixWord r).length + (d.c3Word 0).length) *
        (prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d r)) k -
          prefixWeightSumList (d.suffixWord r ++ d.c3Word 0) k)
        [MOD 2 ^ k] := by
  let b := CycleBridge.cycleRiseBlockTailDepth d r
  let b0 := CycleBridge.cycleRiseBlockTailDepth d 0
  let L := (d.suffixWord r).length
  let C := (d.c3Word 0).length
  let sc := d.suffixWord r ++ d.c3Word 0
  let X := (CycleBridge.cyclicSegmentAt w b0).take (w.length - L - C)
  let inv := S6Audit.pow5Inv 1 k
  have hwpos : 0 < w.length := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    rw [d.hperiod]
    omega
  have hb0 : b0 ≤ w.length := by
    dsimp [b0]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 (by omega)
    omega
  have hsplit_r : CycleBridge.cyclicSegmentAt w b = sc ++ X := by
    have h := cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap d r hr hlast hLle hwpos
    dsimp [b, b0, L, C, sc, X]
    exact h
  have hsplit_1 : CycleBridge.cyclicSegmentAt w b0 = X ++ sc := by
    have h := cyclicSegmentAt_next_eq_take_append_suffix_c3_wrap d r hr hlast hLle hwpos
    dsimp [b, b0, L, C, sc, X]
    rw [← List.append_assoc]
    exact h
  have hE_r : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k =
      prefixWeightSumList sc k +
        2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k := by
    rw [hsplit_r]
    rw [prefixWeightSumList_append sc X k]
    have hlen_sc : sc.length = L + C := by
      dsimp [sc, L, C]
      simp
    simp [inv, hlen_sc]
  have hE_1 : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b0) k =
      prefixWeightSumList X k +
        2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
          prefixWeightSumList sc k := by
    rw [hsplit_1]
    rw [prefixWeightSumList_append X sc k]
    have hlen_rot : (CycleBridge.cyclicSegmentAt w b0).length = w.length :=
      CycleBridge.cyclicSegmentAt_length w b0 hb0
    have hlen_X : X.length = w.length - L - C := by
      dsimp [X]
      exact List.length_take_of_le (by rw [hlen_rot]; omega)
    simp [inv, hlen_X]
  have hsub : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
        prefixWeightSumList sc k =
      2 ^ StringFlow.wordWeight sc * inv ^ (L + C) * prefixWeightSumList X k := by
    rw [hE_r]
    simp
  have hsub_mod : prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
        prefixWeightSumList sc k ≡
      2 ^ StringFlow.wordWeight sc * inv ^ (L + C) * prefixWeightSumList X k [MOD 2 ^ k] := by
    rw [hsub]
  have hinv : 5 * inv ≡ 1 [MOD 2 ^ k] := by
    dsimp [inv]
    exact StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k hk
  have hinv_pow : ∀ n : Nat, 5 ^ n * inv ^ n ≡ 1 [MOD 2 ^ k] := by
    intro n
    induction n with
    | zero => simp [Nat.ModEq]
    | succ n ih =>
        have hstep : 5 ^ (n + 1) * inv ^ (n + 1) = (5 * inv) * (5 ^ n * inv ^ n) := by ring
        rw [hstep]
        exact Nat.ModEq.mul hinv ih
  have hcong_main : 5 ^ (L + C) *
        (prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) k -
          prefixWeightSumList sc k) ≡
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
    have hmul := Nat.ModEq.mul_left (5 ^ (L + C)) hsub_mod
    have hpow := hinv_pow (L + C)
    have hrearr : 5 ^ (L + C) * (2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k) =
        2 ^ StringFlow.wordWeight sc * (5 ^ (L + C) * inv ^ (L + C)) *
          prefixWeightSumList X k := by ring
    have hcong2 : 5 ^ (L + C) * (2 ^ StringFlow.wordWeight sc * inv ^ (L + C) *
          prefixWeightSumList X k) ≡
        2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
      rw [hrearr]
      have hm := Nat.ModEq.mul hpow (Nat.ModEq.refl (prefixWeightSumList X k))
      have hm2 := Nat.ModEq.mul_left (2 ^ StringFlow.wordWeight sc) hm
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm2
    exact hmul.trans hcong2
  have hE_1' : 2 ^ StringFlow.wordWeight sc *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w b0) k =
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
        2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
          inv ^ (w.length - L - C) * prefixWeightSumList sc k := by
    calc
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList (CycleBridge.cyclicSegmentAt w b0) k
          = 2 ^ StringFlow.wordWeight sc * (prefixWeightSumList X k +
              2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
                prefixWeightSumList sc k) := by
                rw [hE_1]
      _ = 2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
            2 ^ StringFlow.wordWeight sc *
              (2 ^ StringFlow.wordWeight X * inv ^ (w.length - L - C) *
                prefixWeightSumList sc k) := by ring
      _ = 2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k +
            2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
              inv ^ (w.length - L - C) * prefixWeightSumList sc k := by
                have hpow_add : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) =
                    2 ^ StringFlow.wordWeight sc * 2 ^ StringFlow.wordWeight X := by
                  rw [Nat.pow_add]
                rw [hpow_add]
                ring
  have hweight_rot : StringFlow.wordWeight (CycleBridge.cyclicSegmentAt w b0) = S := by
    unfold CycleBridge.cyclicSegmentAt
    have hsplit : w.take b0 ++ w.drop b0 = w := List.take_append_drop b0 w
    have hww := StringFlow.Word.wordWeight_append (w.drop b0) (w.take b0)
    rw [hww]
    rw [← h.hweight]
    have hww' := StringFlow.Word.wordWeight_append (w.take b0) (w.drop b0)
    rw [hsplit] at hww'
    rw [Nat.add_comm]
    exact hww'.symm
  have hweight_X_sc : StringFlow.wordWeight X + StringFlow.wordWeight sc = S := by
    have hww := StringFlow.Word.wordWeight_append X sc
    rw [← hsplit_1] at hww
    rw [hweight_rot] at hww
    exact hww.symm
  have h2S : 2 ^ S ≡ 0 [MOD 2 ^ k] := by
    have hdvd : 2 ^ k ∣ 2 ^ S := ⟨2 ^ (S - k), by
      rw [← Nat.pow_add]
      congr 1
      omega⟩
    rw [Nat.ModEq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hvan : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) *
        inv ^ (w.length - L - C) * prefixWeightSumList sc k ≡ 0 [MOD 2 ^ k] := by
    have hpow : 2 ^ (StringFlow.wordWeight sc + StringFlow.wordWeight X) ≡ 0 [MOD 2 ^ k] := by
      rw [show StringFlow.wordWeight sc + StringFlow.wordWeight X = S by omega]
      exact h2S
    have hm := Nat.ModEq.mul hpow
      (Nat.ModEq.refl (inv ^ (w.length - L - C) * prefixWeightSumList sc k))
    simpa [Nat.mul_assoc] using hm
  have hcong : 2 ^ StringFlow.wordWeight sc *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w b0) k ≡
      2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k [MOD 2 ^ k] := by
    rw [hE_1']
    simpa using (Nat.ModEq.add
      (Nat.ModEq.refl (2 ^ StringFlow.wordWeight sc * prefixWeightSumList X k)) hvan)
  simpa [b, b0, L, C, sc, X, inv] using hcong.trans hcong_main.symm

/-- 循环意义下的下一段 C3：最后一块的下一段回到第 0 块。 -/
def cycleNextC3Word {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat) : List Nat :=
  if r + 1 < d.blockCount then d.c3Word (r + 1) else d.c3Word 0

/-- 循环意义下的下一块 C3-tail 深度。 -/
def cycleNextTailDepth {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  if r + 1 < d.blockCount then CycleBridge.cycleRiseBlockTailDepth d (r + 1)
  else CycleBridge.cycleRiseBlockTailDepth d 0

/-- 整圈统一前缀权重和递推：用循环索引覆盖 `r+1 < K` 与最后一块回绕
两个分支。这是第 4 步绕圈合并的逐块统一形式。 -/
theorem prefixWeightSum_recurrence_all
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w (cycleNextTailDepth d r)) k ≡
      5 ^ ((d.suffixWord r).length + (cycleNextC3Word d r).length) *
        (prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d r)) k -
          prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) k)
        [MOD 2 ^ k] := by
  by_cases hnext : r + 1 < d.blockCount
  · have hrec := prefixWeightSum_recurrence h d r hr hnext hLle k hk hkS
    simpa [cycleNextC3Word, cycleNextTailDepth, hnext] using hrec
  · have hlast : r + 1 = d.blockCount := by omega
    have hrec := prefixWeightSum_recurrence_wrap h d r hr hlast hLle k hk hkS
    simpa [cycleNextC3Word, cycleNextTailDepth, hnext] using hrec

/-- 加法形式：`a·E_next + b·s ≡ b·E_r`，用于整圈望远镜求和。 -/
theorem prefixWeightSum_recurrence_all_add
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (k : Nat) (hk : 1 ≤ k) (hkS : k ≤ S) :
    2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
          prefixWeightSumList (CycleBridge.cyclicSegmentAt w (cycleNextTailDepth d r)) k +
        5 ^ ((d.suffixWord r).length + (cycleNextC3Word d r).length) *
          prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) k ≡
      5 ^ ((d.suffixWord r).length + (cycleNextC3Word d r).length) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d r)) k
      [MOD 2 ^ k] := by
  have hrec := prefixWeightSum_recurrence_all h d r hr hLle k hk hkS
  have hsub : prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) k ≤
      prefixWeightSumList (CycleBridge.cyclicSegmentAt w
        (CycleBridge.cycleRiseBlockTailDepth d r)) k := by
    by_cases hnext : r + 1 < d.blockCount
    · have hwpos : 0 < w.length := by
        have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
        rw [d.hperiod]
        omega
      have hsplit := cyclicSegmentAt_tail_eq_suffix_c3_append_take d r hr hnext hLle hwpos
      let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
          (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length)
      have hle := prefixWeightSumList_append_le_left
        (d.suffixWord r ++ d.c3Word (r + 1)) X k
      rw [← hsplit] at hle
      simpa [cycleNextC3Word, hnext] using hle
    · have hlast : r + 1 = d.blockCount := by omega
      have hwpos : 0 < w.length := by
        have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
        rw [d.hperiod]
        omega
      have hsplit := cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap d r hr hlast hLle hwpos
      let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
          (w.length - (d.suffixWord r).length - (d.c3Word 0).length)
      have hle := prefixWeightSumList_append_le_left
        (d.suffixWord r ++ d.c3Word 0) X k
      rw [← hsplit] at hle
      simpa [cycleNextC3Word, hnext] using hle
  let a := 2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)
  let b := 5 ^ ((d.suffixWord r).length + (cycleNextC3Word d r).length)
  let Enext := prefixWeightSumList (CycleBridge.cyclicSegmentAt w (cycleNextTailDepth d r)) k
  let s := prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) k
  let Er := prefixWeightSumList (CycleBridge.cyclicSegmentAt w
      (CycleBridge.cycleRiseBlockTailDepth d r)) k
  have hle : b * s ≤ b * Er := Nat.mul_le_mul_left b hsub
  have hadd : b * (Er - s) + b * s = b * Er := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.sub_add_cancel hle
  have hstep := Nat.ModEq.add_right (b * s) hrec
  rwa [hadd] at hstep

/-- 整圈望远镜求和：若每条 `a_r·E_{r+1} + b_r·s_r ≡ b_r·E_r`，则
`Πa·E_K + Σ_r c_r·s_r ≡ Πb·E_0`，其中
`c_r = Π_{i<r} a_i · Π_{i=r}^{K-1} b_i`。 -/
lemma cyclicSumTelescope
    (K : Nat) (a b : Nat → Nat) (E : Nat → Nat) (s : Nat → Nat) (n : Nat)
    (hrec : ∀ r : Nat, r < K → a r * E (r + 1) + b r * s r ≡ b r * E r [MOD n]) :
    (Finset.range K).prod a * E K +
        (Finset.range K).sum (fun r =>
          (Finset.range r).prod a *
            (Finset.range (K - r)).prod (fun i => b (r + i)) * s r) ≡
      (Finset.range K).prod b * E 0 [MOD n] := by
  induction K with
  | zero => simp; exact Nat.ModEq.refl (n := n) (a := E 0)
  | succ K ih =>
      have hIH := ih (fun r hr => hrec r (by omega))
      have hlast := hrec K (by omega)
      have hpa : (Finset.range (K + 1)).prod a =
          (Finset.range K).prod a * a K := Finset.prod_range_succ a K
      have hpb : (Finset.range (K + 1)).prod b =
          (Finset.range K).prod b * b K := Finset.prod_range_succ b K
      let c' := fun r =>
        (Finset.range r).prod a *
          (Finset.range (K + 1 - r)).prod (fun i => b (r + i)) * s r
      have hc_succ : ∀ r : Nat, r < K →
          (Finset.range (K + 1 - r)).prod (fun i => b (r + i)) =
            (Finset.range (K - r)).prod (fun i => b (r + i)) * b K := by
        intro r hr
        have hsub : K + 1 - r = (K - r) + 1 := by omega
        rw [hsub]
        rw [Finset.prod_range_succ]
        have hindex : r + (K - r) = K := by omega
        rw [hindex]
      have hc_last : (Finset.range (K + 1 - K)).prod (fun i => b (K + i)) = b K := by
        have h1 : K + 1 - K = 1 := by omega
        rw [h1]
        simp
      have hsum_old :
          b K * (Finset.range K).sum (fun r =>
            (Finset.range r).prod a *
              (Finset.range (K - r)).prod (fun i => b (r + i)) * s r) =
          (Finset.range K).sum (fun r => c' r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hrlt : r < K := Finset.mem_range.mp hr
        have hs := hc_succ r hrlt
        dsimp [c']
        rw [hs]
        ring
      have hlast_term : ((Finset.range K).prod a * b K) * s K = c' K := by
        dsimp [c']
        rw [hc_last]
      have hlast_mul : (Finset.range K).prod a * (a K * E (K + 1) + b K * s K) ≡
          (Finset.range K).prod a * (b K * E K) [MOD n] :=
        Nat.ModEq.mul_left ((Finset.range K).prod a) hlast
      rw [Nat.mul_add] at hlast_mul
      have hlast_mul' : (Finset.range K).prod a * a K * E (K + 1) +
            ((Finset.range K).prod a * b K) * s K ≡
          (Finset.range K).prod a * b K * E K [MOD n] := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlast_mul
      have hlast_mul'' : (Finset.range (K + 1)).prod a * E (K + 1) +
            ((Finset.range K).prod a * b K) * s K ≡
          (Finset.range K).prod a * b K * E K [MOD n] := by
        rwa [← hpa] at hlast_mul'
      have hIH_mul : b K * ((Finset.range K).prod a * E K +
            (Finset.range K).sum (fun r =>
              (Finset.range r).prod a *
                (Finset.range (K - r)).prod (fun i => b (r + i)) * s r)) ≡
          b K * ((Finset.range K).prod b * E 0) [MOD n] :=
        Nat.ModEq.mul_left (b K) hIH
      rw [Nat.mul_add] at hIH_mul
      have hIH_mul' : (Finset.range K).prod a * b K * E K +
            b K * (Finset.range K).sum (fun r =>
              (Finset.range r).prod a *
                (Finset.range (K - r)).prod (fun i => b (r + i)) * s r) ≡
          (Finset.range K).prod b * b K * E 0 [MOD n] := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hIH_mul
      have hIH_mul'' : (Finset.range K).prod a * b K * E K +
            (Finset.range K).sum (fun r => c' r) ≡
          (Finset.range (K + 1)).prod b * E 0 [MOD n] := by
        rwa [hsum_old, ← hpb] at hIH_mul'
      have hstep1 := Nat.ModEq.add_right
        (b K * (Finset.range K).sum (fun r =>
          (Finset.range r).prod a *
            (Finset.range (K - r)).prod (fun i => b (r + i)) * s r)) hlast_mul''
      have hstep1' : (Finset.range (K + 1)).prod a * E (K + 1) +
            ((Finset.range K).prod a * b K) * s K +
            (Finset.range K).sum (fun r => c' r) ≡
          (Finset.range K).prod a * b K * E K +
            (Finset.range K).sum (fun r => c' r) [MOD n] := by
        rwa [hsum_old] at hstep1
      have hstep2 : (Finset.range (K + 1)).prod a * E (K + 1) +
            ((Finset.range K).prod a * b K) * s K +
            (Finset.range K).sum (fun r => c' r) ≡
          (Finset.range (K + 1)).prod b * E 0 [MOD n] :=
        hstep1'.trans hIH_mul''
      have hstep2' : (Finset.range (K + 1)).prod a * E (K + 1) +
            c' K + (Finset.range K).sum (fun r => c' r) ≡
          (Finset.range (K + 1)).prod b * E 0 [MOD n] := by
        rwa [hlast_term] at hstep2
      rw [hpa, hpb, Finset.sum_range_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hlast_term, hpa, hpb]
        using hstep2'

/-- 整圈展开：`Π(2^{W_r})·E_0 + Σ c_r·E_{sc_r} ≡ Π(5^{n_r})·E_0
[MOD 2^S]`，其中 `c_r` 是望远镜权重。这就是第 4 步的绕圈合并形式。 -/
theorem prefixWeightSum_recurrence_unroll
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    (Finset.range d.blockCount).prod
        (fun r => 2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d 0)) S +
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod
          (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
          (Finset.range (d.blockCount - r)).prod
            (fun i => 5 ^ (d.suffixWord (r + i) ++ cycleNextC3Word d (r + i)).length) *
          prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) S) ≡
      (Finset.range d.blockCount).prod
        (fun r => 5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length) *
        prefixWeightSumList (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d 0)) S
      [MOD 2 ^ S] := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let E := fun r => prefixWeightSumList (CycleBridge.cyclicSegmentAt w
      (if r < K then CycleBridge.cycleRiseBlockTailDepth d r
       else CycleBridge.cycleRiseBlockTailDepth d 0)) S
  let s := fun r => prefixWeightSumList (sc r) S
  have hS : 1 ≤ S := by
    by_contra hnot
    have hS0 : S = 0 := by omega
    have hlt := CycleBridge.cycleQb8Input_weak_comparison h
    rw [hS0] at hlt
    norm_num at hlt
  have hrec : ∀ r : Nat, r < K →
      (2 ^ StringFlow.wordWeight (sc r)) * E (r + 1) +
          (5 ^ (sc r).length) * s r ≡
        (5 ^ (sc r).length) * E r [MOD 2 ^ S] := by
    intro r hr
    have hrec' := prefixWeightSum_recurrence_all_add h d r hr (hLle r hr) S hS (Nat.le_refl S)
    simpa [K, E, s, sc, cycleNextC3Word, cycleNextTailDepth, List.length_append, hr] using hrec'
  have htel := cyclicSumTelescope K
    (fun r => 2 ^ StringFlow.wordWeight (sc r))
    (fun r => 5 ^ (sc r).length)
    E s (2 ^ S) hrec
  have hEK : E K = prefixWeightSumList (CycleBridge.cyclicSegmentAt w
      (CycleBridge.cycleRiseBlockTailDepth d 0)) S := by
    dsimp [E]
    simp
  rw [hEK] at htel
  simpa [K, sc, s, E] using htel

/-- 循环移位求和：`Σ_r f(next r) = Σ_r f r`。 -/
lemma finset_sum_cyclic_shift (K : Nat) (f : Nat → Nat) :
    (Finset.range K).sum (fun r => if r + 1 < K then f (r + 1) else f 0) =
      (Finset.range K).sum f := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hlast : (if K + 1 < K + 1 then f (K + 1) else f 0) = f 0 := by
        simp
      calc
        (Finset.range (K + 1)).sum (fun r => if r + 1 < K + 1 then f (r + 1) else f 0)
            = (Finset.range K).sum (fun r => f (r + 1)) + f 0 := by
                rw [Finset.sum_range_succ]
                rw [hlast]
                congr 1
                apply Finset.sum_congr rfl
                intro r hr
                have hrlt : r < K := Finset.mem_range.mp hr
                have hlt : r + 1 < K + 1 := by omega
                simp [hlt]
        _ = (Finset.range (K + 1)).sum f := by
                exact (Finset.sum_range_succ' f K).symm

/-- 循环下一段 C3 的长度拆分。 -/
lemma cycleNextC3Word_length_split
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (K r : Nat)
    (hK : K = d.blockCount) :
    (cycleNextC3Word d r).length =
      if r + 1 < K then (d.c3Word (r + 1)).length else (d.c3Word 0).length := by
  dsimp [cycleNextC3Word]
  rw [hK]
  by_cases hlt : r + 1 < d.blockCount
  · simp [hlt]
  · simp [hlt]

/-- 循环下一段 C3 的权重拆分。 -/
lemma cycleNextC3Word_weight_split
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (K r : Nat)
    (hK : K = d.blockCount) :
    StringFlow.wordWeight (cycleNextC3Word d r) =
      if r + 1 < K then StringFlow.wordWeight (d.c3Word (r + 1))
      else StringFlow.wordWeight (d.c3Word 0) := by
  dsimp [cycleNextC3Word]
  rw [hK]
  by_cases hlt : r + 1 < d.blockCount
  · simp [hlt]
  · simp [hlt]

/-- 循环块段的长度和：`Σ_r (suffix r ++ nextC3 r).length = P`。 -/
theorem cycleRiseBlockSegmentLengthSum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    (Finset.range d.blockCount).sum
      (fun r => (d.suffixWord r ++ cycleNextC3Word d r).length) = P := by
  let K := d.blockCount
  have hlen : ∀ r, (d.suffixWord r ++ cycleNextC3Word d r).length =
      (d.suffixWord r).length + (cycleNextC3Word d r).length := by
    intro r
    rw [List.length_append]
  have hcyclic : (Finset.range K).sum (fun r => (cycleNextC3Word d r).length) =
      (Finset.range K).sum (fun r => (d.c3Word r).length) := by
    calc
      (Finset.range K).sum (fun r => (cycleNextC3Word d r).length)
          = (Finset.range K).sum
              (fun r => if r + 1 < K then (d.c3Word (r + 1)).length else (d.c3Word 0).length) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact cycleNextC3Word_length_split d K r rfl
      _ = (Finset.range K).sum (fun r => (d.c3Word r).length) :=
              finset_sum_cyclic_shift K (fun r => (d.c3Word r).length)
  have hperiod : P = ((List.range K).map
      (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
    dsimp [K]
    exact CycleBridge.cycleRiseBlockPeriodSum_list d hpos
  have hlist : ((List.range K).toFinset).sum
      (fun r => (d.c3Word r).length + (d.suffixWord r).length) =
      ((List.range K).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum :=
    List.sum_toFinset
      (fun r => (d.c3Word r).length + (d.suffixWord r).length) List.nodup_range
  rw [List.toFinset_range] at hlist
  rw [← hlist] at hperiod
  calc
    (Finset.range K).sum (fun r => (d.suffixWord r ++ cycleNextC3Word d r).length)
        = (Finset.range K).sum
            (fun r => (d.suffixWord r).length + (cycleNextC3Word d r).length) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hlen r
    _ = P := by
            rw [Finset.sum_add_distrib]
            rw [hcyclic]
            rw [Nat.add_comm]
            rw [← Finset.sum_add_distrib]
            exact hperiod.symm

/-- 循环块段的权重和：`Σ_r weight (suffix r ++ nextC3 r) = S`。 -/
theorem cycleRiseBlockSegmentWeightSum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).sum
      (fun r => StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) = S := by
  let K := d.blockCount
  have hsplit : ∀ r, StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) =
      StringFlow.wordWeight (d.suffixWord r) + StringFlow.wordWeight (cycleNextC3Word d r) := by
    intro r
    exact StringFlow.Word.wordWeight_append (d.suffixWord r) (cycleNextC3Word d r)
  have hcyclic : (Finset.range K).sum (fun r => StringFlow.wordWeight (cycleNextC3Word d r)) =
      (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) := by
    calc
      (Finset.range K).sum (fun r => StringFlow.wordWeight (cycleNextC3Word d r))
          = (Finset.range K).sum
              (fun r => if r + 1 < K then StringFlow.wordWeight (d.c3Word (r + 1))
                else StringFlow.wordWeight (d.c3Word 0)) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact cycleNextC3Word_weight_split d K r rfl
      _ = (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) :=
              finset_sum_cyclic_shift K (fun r => StringFlow.wordWeight (d.c3Word r))
  have hw := d.hweight
  have hlist : ((List.range K).toFinset).sum
      (fun r => StringFlow.wordWeight (d.c3Word r) + StringFlow.wordWeight (d.suffixWord r)) =
      ((List.range K).map
        (fun r => StringFlow.wordWeight (d.c3Word r) + StringFlow.wordWeight (d.suffixWord r))).sum :=
    List.sum_toFinset
      (fun r => StringFlow.wordWeight (d.c3Word r) + StringFlow.wordWeight (d.suffixWord r))
      List.nodup_range
  rw [List.toFinset_range] at hlist
  rw [← hlist] at hw
  have hmain : (Finset.range K).sum
      (fun r => StringFlow.wordWeight (d.suffixWord r) + StringFlow.wordWeight (cycleNextC3Word d r)) = S := by
    rw [Finset.sum_add_distrib]
    rw [hcyclic]
    rw [Nat.add_comm]
    rw [← Finset.sum_add_distrib]
    exact hw.symm
  calc
    (Finset.range K).sum
        (fun r => StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r))
        = (Finset.range K).sum
            (fun r => StringFlow.wordWeight (d.suffixWord r) + StringFlow.wordWeight (cycleNextC3Word d r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hsplit r
    _ = S := hmain

/-- 整圈 `2` 幂乘积：`Π_r 2^{weight(sc_r)} = 2^S`。 -/
theorem cycleRiseBlockSegmentProdPowWeight
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).prod
      (fun r => 2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) = 2 ^ S := by
  rw [Finset.prod_pow_eq_pow_sum]
  rw [cycleRiseBlockSegmentWeightSum d]

/-- 整圈 `5` 幂乘积：`Π_r 5^{(sc_r).length} = 5^P`。 -/
theorem cycleRiseBlockSegmentProdPowLength
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    (Finset.range d.blockCount).prod
      (fun r => 5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length) = 5 ^ P := by
  rw [Finset.prod_pow_eq_pow_sum]
  rw [cycleRiseBlockSegmentLengthSum d hpos]

/-- 整圈展开的简化形：乘积归约后，
`Σ_r c_r·E_{sc_r} ≡ 5^P·E_0 [MOD 2^S]`。 -/
theorem prefixWeightSum_recurrence_unroll_simplified
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    (Finset.range d.blockCount).sum (fun r =>
      (Finset.range r).prod
        (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + i) ++ cycleNextC3Word d (r + i)).length) *
        prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) S) ≡
      5 ^ P * prefixWeightSumList (CycleBridge.cyclicSegmentAt w
        (CycleBridge.cycleRiseBlockTailDepth d 0)) S
      [MOD 2 ^ S] := by
  have hU := prefixWeightSum_recurrence_unroll h d hLle
  rw [cycleRiseBlockSegmentProdPowWeight d, cycleRiseBlockSegmentProdPowLength d hpos] at hU
  rw [Nat.ModEq] at hU
  rw [Nat.add_mod] at hU
  have hz : (2 ^ S * prefixWeightSumList (CycleBridge.cyclicSegmentAt w
      (CycleBridge.cycleRiseBlockTailDepth d 0)) S) % 2 ^ S = 0 :=
    Nat.mul_mod_right (2 ^ S)
      (prefixWeightSumList (CycleBridge.cyclicSegmentAt w
        (CycleBridge.cycleRiseBlockTailDepth d 0)) S)
  rw [hz] at hU
  have hsum : ((Finset.range d.blockCount).sum (fun r =>
      (Finset.range r).prod
        (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + i) ++ cycleNextC3Word d (r + i)).length) *
        prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) S)) % 2 ^ S =
    (5 ^ P * prefixWeightSumList (CycleBridge.cyclicSegmentAt w
      (CycleBridge.cycleRiseBlockTailDepth d 0)) S) % 2 ^ S := by
    simpa using hU
  exact hsum

/-- 块段 `suffix r ++ nextC3 r` 从 C3-tail 状态出发的轨道等于下一块
C3-tail 状态。 -/
theorem cycleRiseBlockSegment_wordOrbit_eq
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (_hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordOrbit (d.suffixWord r ++ cycleNextC3Word d r)
      (CycleBridge.cycleRiseBlockC3TailState d r) =
    StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m := by
  by_cases hnext : r + 1 < d.blockCount
  · have hmid := CycleBridge.suffixWord_prefix_eq_word_prefix_mod d r hr
      (d.suffixWord r).length (le_rfl)
    have hbL : (CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % P =
        d.headDepth (r + 1) := by
      have hnext_eq : CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
          d.headDepth (r + 1) := by
        dsimp [CycleBridge.cycleRiseBlockTailDepth]
        have hh := d.hnext r hr
        rw [if_pos hnext] at hh
        omega
      rw [hnext_eq]
      exact Nat.mod_eq_of_lt (d.hhead_lt (r + 1) hnext)
    have hmid' : StringFlow.Word.wordOrbit (d.suffixWord r)
          (CycleBridge.cycleRiseBlockC3TailState d r) =
        StringFlow.Word.wordOrbit (w.take (d.headDepth (r + 1))) m := by
      rw [List.take_of_length_le (le_rfl : (d.suffixWord r).length ≤ (d.suffixWord r).length)] at hmid
      rw [hbL] at hmid
      exact hmid
    have hq := CycleBridge.cycleRiseBlockC3TailState_eq_wordOrbit_c3Word d (r + 1) hnext
    rw [S6Audit.wordOrbit_append (d.suffixWord r) (cycleNextC3Word d r)
      (CycleBridge.cycleRiseBlockC3TailState d r)]
    rw [hmid']
    rw [show cycleNextC3Word d r = d.c3Word (r + 1) by simp [cycleNextC3Word, hnext]]
    rw [← hq]
    dsimp [cycleNextTailDepth]
    rw [if_pos hnext]
    rfl
  · have hlast : r + 1 = d.blockCount := by omega
    have hpos0 : 0 < d.blockCount := lt_of_le_of_lt (Nat.zero_le r) hr
    have hmid := CycleBridge.suffixWord_prefix_eq_word_prefix_mod d r hr
      (d.suffixWord r).length (le_rfl)
    have hbL : (CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % P =
        d.headDepth 0 := by
      have hnext_eq : CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
          d.headDepth 0 + P := by
        dsimp [CycleBridge.cycleRiseBlockTailDepth]
        have hh := d.hnext r hr
        rw [if_neg hnext] at hh
        omega
      rw [hnext_eq]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (d.hhead_lt 0 hpos0)
    have hmid' : StringFlow.Word.wordOrbit (d.suffixWord r)
          (CycleBridge.cycleRiseBlockC3TailState d r) =
        StringFlow.Word.wordOrbit (w.take (d.headDepth 0)) m := by
      rw [List.take_of_length_le (le_rfl : (d.suffixWord r).length ≤ (d.suffixWord r).length)] at hmid
      rw [hbL] at hmid
      exact hmid
    have hq := CycleBridge.cycleRiseBlockC3TailState_eq_wordOrbit_c3Word d 0 hpos0
    rw [S6Audit.wordOrbit_append (d.suffixWord r) (cycleNextC3Word d r)
      (CycleBridge.cycleRiseBlockC3TailState d r)]
    rw [hmid']
    rw [show cycleNextC3Word d r = d.c3Word 0 by simp [cycleNextC3Word, hnext]]
    rw [← hq]
    dsimp [cycleNextTailDepth]
    rw [if_neg hnext]
    rfl

/-- 块段 `suffix r ++ nextC3 r` 对 C3-tail 状态是合法的真实词段。 -/
theorem cycleRiseBlockSegment_wordValid
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordValid (d.suffixWord r ++ cycleNextC3Word d r)
      (CycleBridge.cycleRiseBlockC3TailState d r) := by
  have hwpos : 0 < w.length := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    rw [d.hperiod]
    omega
  by_cases hnext : r + 1 < d.blockCount
  · have hrot := cyclicSegmentAt_tail_eq_suffix_c3_append_take d r hr hnext hLle hwpos
    have hvalid_rot := CycleBridge.cyclicSegmentAt_valid h
      (CycleBridge.cycleRiseBlockTailDepth d r)
    let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d (r + 1))).take
        (w.length - (d.suffixWord r).length - (d.c3Word (r + 1)).length)
    have hrot' : CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r) =
        (d.suffixWord r ++ cycleNextC3Word d r) ++ X := by
      dsimp [X]
      simpa [cycleNextC3Word, hnext] using hrot
    have hv : StringFlow.Word.wordValid
        ((d.suffixWord r ++ cycleNextC3Word d r) ++ X)
        (CycleBridge.cycleRiseBlockC3TailState d r) := by
      rw [hrot'] at hvalid_rot
      simpa [CycleBridge.cycleRiseBlockC3TailState, CycleBridge.cycleRiseBlockTailDepth] using hvalid_rot
    have hparts := (S6Audit.wordValid_append
        (d.suffixWord r ++ cycleNextC3Word d r) X
        (CycleBridge.cycleRiseBlockC3TailState d r)).mp hv
    exact hparts.1
  · have hlast : r + 1 = d.blockCount := by omega
    have hrot := cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap d r hr hlast hLle hwpos
    have hvalid_rot := CycleBridge.cyclicSegmentAt_valid h
      (CycleBridge.cycleRiseBlockTailDepth d r)
    let X := (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)).take
        (w.length - (d.suffixWord r).length - (d.c3Word 0).length)
    have hrot' : CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d r) =
        (d.suffixWord r ++ cycleNextC3Word d r) ++ X := by
      dsimp [X]
      simpa [cycleNextC3Word, hnext] using hrot
    have hv : StringFlow.Word.wordValid
        ((d.suffixWord r ++ cycleNextC3Word d r) ++ X)
        (CycleBridge.cycleRiseBlockC3TailState d r) := by
      rw [hrot'] at hvalid_rot
      simpa [CycleBridge.cycleRiseBlockC3TailState, CycleBridge.cycleRiseBlockTailDepth] using hvalid_rot
    have hparts := (S6Audit.wordValid_append
        (d.suffixWord r ++ cycleNextC3Word d r) X
        (CycleBridge.cycleRiseBlockC3TailState d r)).mp hv
    exact hparts.1

/-- 块段精确分子恒等式：
`A(sc_r) = 2^{W(sc_r)}·q_next − 5^{n_r}·q_r`。 -/
theorem cycleRiseBlockSegmentWordA_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordA (d.suffixWord r ++ cycleNextC3Word d r) =
      2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
          StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
      5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
          CycleBridge.cycleRiseBlockC3TailState d r := by
  have hvalid := cycleRiseBlockSegment_wordValid h d r hr hLle
  have horb := cycleRiseBlockSegment_wordOrbit_eq d r hr hLle
  have hid := StringFlow.Word.word_orbit_identity
    (d.suffixWord r ++ cycleNextC3Word d r)
    (CycleBridge.cycleRiseBlockC3TailState d r) hvalid
  rw [horb] at hid
  omega

/-- 逐块桥：`E_{sc_r} + 5·q_r ≡ 0 [MOD 2^{W(sc_r)}]`，
即前缀权重和段残差等价于边界态 `−5·q_r`。 -/
theorem prefixWeightSumSegment_eq_neg_five_q_mod
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r)
        (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) +
      5 * CycleBridge.cycleRiseBlockC3TailState d r ≡
      0 [MOD 2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)] := by
  let sc := d.suffixWord r ++ cycleNextC3Word d r
  let W := StringFlow.wordWeight sc
  let n := sc.length
  let s := prefixWeightSumList sc W
  let q := CycleBridge.cycleRiseBlockC3TailState d r
  let qnext := StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m
  have hpos_entries : ∀ t ∈ sc, 1 ≤ t := by
    intro t ht
    rcases List.mem_append.mp ht with hsuf | hc3
    · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
    · by_cases hnext : r + 1 < d.blockCount
      · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
        have hge : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
        omega
      · have hpos0 : 0 < d.blockCount := by omega
        have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
        have hge : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
        omega
  have hne : sc ≠ [] := by
    intro hsc
    have hlen0 : sc.length = 0 := by rw [hsc]; simp
    have hc3ne : cycleNextC3Word d r ≠ [] := by
      by_cases hnext : r + 1 < d.blockCount
      · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
      · have hpos0 : 0 < d.blockCount := by omega
        simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
    have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
    have hlen_pos : 0 < sc.length := by
      dsimp [sc]
      rw [List.length_append]
      omega
    omega
  have hnpos : 1 ≤ n := by
    dsimp [n]
    exact List.length_pos_iff.mpr hne
  have hWpos : 1 ≤ W := by
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one sc (by
      intro t ht
      rcases List.mem_append.mp ht with hsuf | hc3
      · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
      · by_cases hnext : r + 1 < d.blockCount
        · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
          omega
        · have hpos0 : 0 < d.blockCount := by omega
          have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
          omega)
    have hlen : 1 ≤ sc.length := List.length_pos_iff.mpr hne
    dsimp [W]
    omega
  have hW : 1 ≤ W := by
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one sc hpos_entries
    have hlen : 1 ≤ sc.length := List.length_pos_iff.mpr hne
    dsimp [W]
    omega
  have hAeq' : StringFlow.Word.wordA sc + 5 ^ n * q = 2 ^ W * qnext := by
    have hvalid := cycleRiseBlockSegment_wordValid h d r hr hLle
    have horb := cycleRiseBlockSegment_wordOrbit_eq d r hr hLle
    have hid := StringFlow.Word.word_orbit_identity sc q hvalid
    rw [horb] at hid
    dsimp [sc, W, n, q, qnext] at hid ⊢
    rw [Nat.add_comm]
    exact hid.symm
  have hmodA := wordA_cyclic_mod_two_pow_prefixWeight_sum sc 0 W (by simp) hW
  have hmodA' : StringFlow.Word.wordA sc ≡ 5 ^ (n - 1) * s [MOD 2 ^ W] := by
    dsimp [s, n, sc] at hmodA ⊢
    simpa [prefixWeightSumList, CycleBridge.cyclicSegmentAt] using hmodA
  have hzero : 2 ^ W * qnext ≡ 0 [MOD 2 ^ W] := by
    have hdvd : 2 ^ W ∣ 2 ^ W * qnext := ⟨qnext, by rw [Nat.mul_comm]⟩
    rw [Nat.ModEq]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hsum : StringFlow.Word.wordA sc + 5 ^ n * q ≡ 0 [MOD 2 ^ W] := by
    rw [hAeq']
    exact hzero
  have hadd : StringFlow.Word.wordA sc + 5 ^ n * q ≡ 5 ^ (n - 1) * s + 5 ^ n * q [MOD 2 ^ W] :=
    Nat.ModEq.add hmodA' (Nat.ModEq.refl (5 ^ n * q))
  have hstep : 5 ^ (n - 1) * s + 5 ^ n * q ≡ 0 [MOD 2 ^ W] :=
    hadd.symm.trans hsum
  have hfactor : 5 ^ (n - 1) * (s + 5 * q) = 5 ^ (n - 1) * s + 5 ^ n * q := by
    rw [Nat.mul_add]
    have hpow : 5 ^ (n - 1) * 5 = 5 ^ n := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [← Nat.mul_assoc, hpow]
  have hcong : 5 ^ (n - 1) * (s + 5 * q) ≡ 0 [MOD 2 ^ W] := by
    rwa [← hfactor] at hstep
  have hinv := StringFlow.PmiLocalLemma.pow5Inv_correct_local (n - 1) W hW
  have hmul := Nat.ModEq.mul_left (S6Audit.pow5Inv (n - 1) W) hcong
  have hrearr : S6Audit.pow5Inv (n - 1) W * (5 ^ (n - 1) * (s + 5 * q)) =
      (5 ^ (n - 1) * S6Audit.pow5Inv (n - 1) W) * (s + 5 * q) := by ring
  have hmul' : (5 ^ (n - 1) * S6Audit.pow5Inv (n - 1) W) * (s + 5 * q) ≡ 0 [MOD 2 ^ W] := by
    rwa [hrearr] at hmul
  have h1 := Nat.ModEq.mul hinv (Nat.ModEq.refl (s + 5 * q))
  simpa [s, q, W, sc] using (h1.symm.trans hmul')

/-- 同余精度下降：模 `2^{k'}` 的同余在 `k ≤ k'` 时也模 `2^k` 成立。 -/
lemma modEq_lower {a b k k' : Nat} (hk : k ≤ k') (h : a ≡ b [MOD 2 ^ k']) :
    a ≡ b [MOD 2 ^ k] := by
  rw [Nat.ModEq] at h ⊢
  have hdvd : 2 ^ k ∣ 2 ^ k' := ⟨2 ^ (k' - k), by
    rw [← Nat.pow_add]
    congr 1
    omega⟩
  have hma : a % 2 ^ k = (a % 2 ^ k') % 2 ^ k :=
    (Nat.mod_mod_of_dvd a (c := 2 ^ k) (b := 2 ^ k') hdvd).symm
  have hmb : b % 2 ^ k = (b % 2 ^ k') % 2 ^ k :=
    (Nat.mod_mod_of_dvd b (c := 2 ^ k) (b := 2 ^ k') hdvd).symm
  rw [hma, hmb, h]

/-- 前缀权重和精度下降：模 `2^k` 下，用较大模数的 `inv` 与较小模数的
`inv` 计算结果一致。 -/
lemma prefixWeightSumList_mod_lower (l : List Nat) (k k' : Nat)
    (hkpos : 1 ≤ k) (hk : k ≤ k') :
    prefixWeightSumList l k' ≡ prefixWeightSumList l k [MOD 2 ^ k] := by
  unfold prefixWeightSumList
  apply sum_modEq
  intro i hi
  have hinv : S6Audit.pow5Inv 1 k' ≡ S6Audit.pow5Inv 1 k [MOD 2 ^ k] := by
    have h1 := StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k' (by omega : 1 ≤ k')
    have h2 := StringFlow.PmiLocalLemma.pow5Inv_correct_local 1 k hkpos
    have h1' : 5 * S6Audit.pow5Inv 1 k' ≡ 1 [MOD 2 ^ k] := modEq_lower hk h1
    have h2' : 5 * S6Audit.pow5Inv 1 k ≡ 1 [MOD 2 ^ k] := h2
    have h1'' : 5 * S6Audit.pow5Inv 1 k' * S6Audit.pow5Inv 1 k ≡
        S6Audit.pow5Inv 1 k [MOD 2 ^ k] := by
      simpa using (Nat.ModEq.mul h1' (Nat.ModEq.refl (S6Audit.pow5Inv 1 k)))
    have h2'' : 5 * S6Audit.pow5Inv 1 k * S6Audit.pow5Inv 1 k' ≡
        S6Audit.pow5Inv 1 k' [MOD 2 ^ k] := by
      simpa using (Nat.ModEq.mul h2' (Nat.ModEq.refl (S6Audit.pow5Inv 1 k')))
    have hsym : 5 * S6Audit.pow5Inv 1 k' * S6Audit.pow5Inv 1 k ≡
        5 * S6Audit.pow5Inv 1 k * S6Audit.pow5Inv 1 k' [MOD 2 ^ k] := by
      rw [Nat.ModEq]
      congr 1
      ring
    exact ((h1''.symm).trans (hsym.trans h2'')).symm
  have hinv_pow : ∀ i : Nat, S6Audit.pow5Inv 1 k' ^ i ≡
      S6Audit.pow5Inv 1 k ^ i [MOD 2 ^ k] := by
    intro i
    induction i with
    | zero => simp [Nat.ModEq]
    | succ i ih =>
        have hstep := Nat.ModEq.mul ih hinv
        simpa [Nat.pow_succ] using hstep
  have hmul := Nat.ModEq.mul
    (Nat.ModEq.refl (2 ^ StringFlow.PMI.prefixWeight (fun j => l.getI j) i))
    (hinv_pow i)
  exact hmul

/-- 加法形式的块段分子恒等式：
`A(sc_r) + 5^{n_r}·q_r = 2^{W(sc_r)}·q_{next}`。 -/
lemma cycleRiseBlockSegmentWordA_add_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordA (d.suffixWord r ++ cycleNextC3Word d r) +
      5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
        CycleBridge.cycleRiseBlockC3TailState d r =
      2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
        StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m := by
  have hvalid := cycleRiseBlockSegment_wordValid h d r hr hLle
  have horb := cycleRiseBlockSegment_wordOrbit_eq d r hr hLle
  have hid := StringFlow.Word.word_orbit_identity
    (d.suffixWord r ++ cycleNextC3Word d r)
    (CycleBridge.cycleRiseBlockC3TailState d r) hvalid
  rw [horb] at hid
  omega

/-- 绕圈合并（加法形式）：`(2^S−5^P)·E_0 + Σ_r c_r·s_r ≡ 0 [MOD 2^k]`。
这是前缀权重 5-adic 望远镜绕一整圈后 `E_0` 的闭环同余，由
`prefixWeightSum_recurrence_unroll` 与精度下降直接得到。 -/
theorem prefixWeightSum_wrapMerge
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length)
    (h5le : 5 ^ P ≤ 2 ^ S)
    (k : Nat) (_hk : 1 ≤ k) (hkS : k ≤ S) :
    (2 ^ S - 5 ^ P) * prefixWeightSumList
        (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d 0)) S +
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod
          (fun i => 2 ^ StringFlow.wordWeight
            (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + i) ++
            cycleNextC3Word d (r + i)).length) *
        prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r) S) ≡
      0 [MOD 2 ^ k] := by
  let E0 := prefixWeightSumList
    (CycleBridge.cyclicSegmentAt w
      (CycleBridge.cycleRiseBlockTailDepth d 0)) S
  let s := fun r => prefixWeightSumList
    (d.suffixWord r ++ cycleNextC3Word d r) S
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight
      (d.suffixWord i ++ cycleNextC3Word d i)) *
    (Finset.range (d.blockCount - r)).prod
      (fun i => 5 ^ (d.suffixWord (r + i) ++ cycleNextC3Word d (r + i)).length)
  let big := 2 ^ S * E0 +
    (Finset.range d.blockCount).sum (fun r => c r * s r)
  have hU := prefixWeightSum_recurrence_unroll h d hLle
  rw [cycleRiseBlockSegmentProdPowWeight d,
      cycleRiseBlockSegmentProdPowLength d hpos] at hU
  have hU' := modEq_lower hkS hU
  have hU'' : big ≡ 5 ^ P * E0 [MOD 2 ^ k] := by
    dsimp [big, c, s, E0]
    exact hU'
  have hle : 5 ^ P * E0 ≤ big := by
    dsimp [big]
    exact le_trans (Nat.mul_le_mul_right E0 h5le) (Nat.le_add_right _ _)
  have hsub : big - 5 ^ P * E0 ≡ 0 [MOD 2 ^ k] := by
    simpa using (Nat.ModEq.sub_right hle
      (le_rfl : 5 ^ P * E0 ≤ 5 ^ P * E0) hU')
  have halg : big - 5 ^ P * E0 =
      (2 ^ S - 5 ^ P) * E0 + (Finset.range d.blockCount).sum (fun r => c r * s r) := by
    have h5E : 5 ^ P * E0 ≤ 2 ^ S * E0 := Nat.mul_le_mul_right E0 h5le
    calc
      big - 5 ^ P * E0
          = 2 ^ S * E0 + (Finset.range d.blockCount).sum (fun r => c r * s r) -
              5 ^ P * E0 := by dsimp [big]
      _ = (2 ^ S * E0 - 5 ^ P * E0) +
              (Finset.range d.blockCount).sum (fun r => c r * s r) := by
              rw [Nat.sub_add_comm h5E]
      _ = (2 ^ S - 5 ^ P) * E0 +
              (Finset.range d.blockCount).sum (fun r => c r * s r) := by
              rw [Nat.sub_mul]
  rwa [halg] at hsub

/-- 单项误差的精确 2-adic 秩：
`v2(E_{sc_r} + 5·q_r) = W(sc_r)`。 -/
theorem cycleRiseBlockSegmentErrorRank_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    twoValuation (prefixWeightSumList (d.suffixWord r ++ cycleNextC3Word d r)
        (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) + 1) +
      5 * CycleBridge.cycleRiseBlockC3TailState d r) =
      StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) := by
  let sc := d.suffixWord r ++ cycleNextC3Word d r
  let W := StringFlow.wordWeight sc
  let n := sc.length
  let s := prefixWeightSumList sc (W + 1)
  let q := CycleBridge.cycleRiseBlockC3TailState d r
  let e := s + 5 * q
  have hc3ne : cycleNextC3Word d r ≠ [] := by
    by_cases hnext : r + 1 < d.blockCount
    · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
    · have hpos0 : 0 < d.blockCount := by omega
      simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
  have hne : sc ≠ [] := by
    intro hsc
    have hlen0 : sc.length = 0 := by rw [hsc]; simp
    have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
    have hlen_pos : 0 < sc.length := by
      dsimp [sc]
      rw [List.length_append]
      omega
    omega
  have hnpos : 1 ≤ n := by
    dsimp [n]
    exact List.length_pos_iff.mpr hne
  have hWpos : 1 ≤ W := by
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one sc (by
      intro t ht
      rcases List.mem_append.mp ht with hsuf | hc3
      · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
      · by_cases hnext : r + 1 < d.blockCount
        · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
          omega
        · have hpos0 : 0 < d.blockCount := by omega
          have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
          omega)
    have hlen : 1 ≤ sc.length := List.length_pos_iff.mpr hne
    dsimp [W]
    omega
  have hb_tail : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    omega
  have hq_pos : 0 < q := by
    dsimp [q]
    have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb_tail
    have hodd : S6Audit.IsOdd
        (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) :=
      S6Audit.FullOrbitFrom7_odd _ hfull
    by_contra hnot
    change ¬ 0 < StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m at hnot
    have h0 : StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m = 0 := by omega
    rw [h0] at hodd
    change 0 % 2 = 1 at hodd
    norm_num at hodd
  have he_pos : 0 < e := by
    dsimp [e]
    have hs_nonneg : 0 ≤ s := Nat.zero_le _
    have h5q : 0 < 5 * q := Nat.mul_pos (by norm_num) hq_pos
    nlinarith
  have hdvd : 2 ^ W ∣ e := by
    have hb := prefixWeightSumSegment_eq_neg_five_q_mod h d r hr hLle
    have hlower := prefixWeightSumList_mod_lower sc W (W + 1) hWpos (by omega)
    have hb' : s + 5 * q ≡ 0 [MOD 2 ^ W] := by
      have hadd := Nat.ModEq.add hlower (Nat.ModEq.refl (5 * q))
      exact hadd.trans hb
    have hmod : e % 2 ^ W = 0 := by
      dsimp [e] at hb' ⊢
      exact hb'
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hge : W ≤ twoValuation e :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow e W he_pos).mpr hdvd
  have hmodA := wordA_cyclic_mod_two_pow_prefixWeight_sum sc 0 (W + 1) (by simp) (by omega)
  have hAadd := cycleRiseBlockSegmentWordA_add_eq h d r hr hLle
  have hmodA' : StringFlow.Word.wordA sc ≡ 5 ^ (n - 1) * s [MOD 2 ^ (W + 1)] := by
    dsimp [s, n, sc] at hmodA ⊢
    simpa [prefixWeightSumList, CycleBridge.cyclicSegmentAt] using hmodA
  have hadd := Nat.ModEq.add hmodA' (Nat.ModEq.refl (5 ^ n * q))
  have hsum : StringFlow.Word.wordA sc + 5 ^ n * q ≡
      2 ^ W * StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m [MOD 2 ^ (W + 1)] := by
    rw [hAadd]
  have hcong5 : 2 ^ W * StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m ≡
      5 ^ (n - 1) * s + 5 ^ n * q [MOD 2 ^ (W + 1)] :=
    hsum.symm.trans hadd
  have hfac : 5 ^ (n - 1) * s + 5 ^ n * q = 5 ^ (n - 1) * (s + 5 * q) := by
    rw [Nat.mul_add]
    have hpow : 5 ^ (n - 1) * 5 = 5 ^ n := by
      have hnsucc : n = (n - 1) + 1 := by omega
      rw [hnsucc, Nat.pow_succ]
      rw [show n - 1 + 1 - 1 = n - 1 by omega]
    rw [← Nat.mul_assoc, hpow]
  have hcong6 : 2 ^ W * StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m ≡
      5 ^ (n - 1) * e [MOD 2 ^ (W + 1)] := by
    dsimp [e]
    rwa [hfac] at hcong5
  have hcong7 : 5 ^ (n - 1) * e ≡
      2 ^ W * StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m [MOD 2 ^ (W + 1)] :=
    hcong6.symm
  have hb_next : cycleNextTailDepth d r ≤ w.length := by
    by_cases hnext : r + 1 < d.blockCount
    · dsimp [cycleNextTailDepth]
      rw [if_pos hnext]
      have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hnext
      omega
    · have hpos0 : 0 < d.blockCount := by omega
      dsimp [cycleNextTailDepth]
      rw [if_neg hnext]
      have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos0
      omega
  have hfull_next := CycleBridge.cycleQb8Input_prefix_full_reachable h
    (cycleNextTailDepth d r) hb_next
  have hoddq : (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m) % 2 = 1 :=
    S6Audit.FullOrbitFrom7_odd _ hfull_next
  have hmodq : (2 ^ W * StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m) %
        2 ^ (W + 1) = 2 ^ W := by
    rcases Nat.odd_iff.mpr hoddq with ⟨u, hu⟩
    rw [hu]
    rw [Nat.mul_add, Nat.add_mod]
    have h1 : 2 ^ W * (2 * u) = 2 ^ (W + 1) * u := by
      have hpow2 : 2 ^ W * 2 = 2 ^ (W + 1) := by
        rw [Nat.pow_succ]
      rw [← Nat.mul_assoc, hpow2]
    rw [h1]
    have hzero : (2 ^ (W + 1) * u) % 2 ^ (W + 1) = 0 :=
      Nat.mul_mod_right (2 ^ (W + 1)) u
    rw [hzero]
    have hsmall : (2 ^ W * 1) % 2 ^ (W + 1) = 2 ^ W := by
      rw [Nat.mul_one]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))
    rw [hsmall]
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega))
  have hmod5e : (5 ^ (n - 1) * e) % 2 ^ (W + 1) = 2 ^ W := by
    rw [Nat.ModEq] at hcong7
    rw [hmodq] at hcong7
    exact hcong7
  have hndvd : ¬ 2 ^ (W + 1) ∣ e := by
    intro hdiv
    rcases hdiv with ⟨t, ht⟩
    have hdiv5 : 2 ^ (W + 1) ∣ 5 ^ (n - 1) * e := by
      refine ⟨5 ^ (n - 1) * t, ?_⟩
      rw [ht]
      ring
    rcases hdiv5 with ⟨u, hu⟩
    have hzero : (5 ^ (n - 1) * e) % 2 ^ (W + 1) = 0 := by
      rw [hu]
      exact Nat.mul_mod_right (2 ^ (W + 1)) u
    rw [hmod5e] at hzero
    norm_num at hzero
  have hle : twoValuation e ≤ W :=
    (StringFlow.Lte.twoValuation_le_iff_not_dvd_pow e W he_pos).mpr hndvd
  simpa [e] using (le_antisymm hle hge)

/-- 严格递增估值序列的整圈和：首项估值严格最小，故
`v2(Σ_{r<m} a_r) = v 0`。 -/
lemma twoValuation_sum_range_of_strict
    (m : Nat) (a : Nat → Nat) (v : Nat → Nat)
    (hpos : ∀ r, r < m → 0 < a r)
    (hv : ∀ r, r < m → twoValuation (a r) = v r)
    (hstrict : ∀ i j, i < j → j < m → v i < v j) :
    0 < m → twoValuation ((Finset.range m).sum a) = v 0 := by
  intro hm
  induction m with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          simp
          exact hv 0 (by omega)
      | succ n =>
          have hpos' : ∀ r, r < n + 1 → 0 < a r := fun r hr => hpos r (by omega)
          have hv' : ∀ r, r < n + 1 → twoValuation (a r) = v r :=
            fun r hr => hv r (by omega)
          have hstrict' : ∀ i j, i < j → j < n + 1 → v i < v j :=
            fun i j hij hjl => hstrict i j hij (by omega)
          have hIH : twoValuation ((Finset.range (n + 1)).sum a) = v 0 :=
            ih hpos' hv' hstrict' (by omega)
          rw [Finset.sum_range_succ]
          have hsum_pos : 0 < (Finset.range (n + 1)).sum a := by
            have hle : a 0 ≤ (Finset.range (n + 1)).sum a :=
              Finset.single_le_sum (s := Finset.range (n + 1)) (f := a) (a := 0)
                (by intro b hb; exact Nat.zero_le _)
                (by simp)
            exact lt_of_lt_of_le (hpos 0 (by omega)) hle
          have hval_last : twoValuation (a (n + 1)) = v (n + 1) :=
            hv (n + 1) (by omega)
          have hlt : v 0 < v (n + 1) := hstrict 0 (n + 1) (by omega) (by omega)
          have hltv : twoValuation ((Finset.range (n + 1)).sum a) <
              twoValuation (a (n + 1)) := by
            rw [hIH, hval_last]
            exact hlt
          have hres := StringFlow.Lte.twoValuation_add_eq_of_lt
            ((Finset.range (n + 1)).sum a) (a (n + 1))
            hsum_pos (hpos (n + 1) (by omega)) hltv
          rwa [hIH] at hres

/-- 严格正项的部分和严格递增。 -/
lemma Finset.sum_range_lt_of_pos
    (n m : Nat) (f : Nat → Nat) (hn : n < m)
    (hpos : ∀ r, n ≤ r → r < m → 0 < f r) :
    (Finset.range n).sum f < (Finset.range m).sum f := by
  have hm : m = n + (m - n) := by omega
  have hsplit := Finset.sum_range_add f n (m - n)
  have hpos_extra : 0 < (Finset.range (m - n)).sum (fun r => f (n + r)) := by
    have h0 : 0 < m - n := by omega
    have hle : f (n + 0) ≤ (Finset.range (m - n)).sum (fun r => f (n + r)) :=
      Finset.single_le_sum (s := Finset.range (m - n))
        (f := fun r => f (n + r)) (a := 0)
        (by intro b hb; exact Nat.zero_le _)
        (by simp [h0])
    have hposn : 0 < f (n + 0) := hpos n (by omega) (by omega)
    have hposn' : 0 < f n := by simpa using hposn
    exact lt_of_lt_of_le hposn' hle
  rw [hm, hsplit]
  change (Finset.range n).sum f <
      (Finset.range n).sum f + (Finset.range (m - n)).sum (fun r => f (n + r))
  omega

/-- 每项都奇数的 `Finset.range` 乘积是奇数。 -/
lemma Finset.prod_odd_mod_two (n : Nat) (f : Nat → Nat)
    (hodd : ∀ r, r < n → (f r) % 2 = 1) :
    ((Finset.range n).prod f) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact StringFlow.Lte.odd_mul_odd_mod_two
        ((Finset.range n).prod f) (f n)
        (ih (fun r hr => hodd r (by omega)))
        (hodd n (by omega))

/-- 整圈误差和估值：`v2(Σ_r c_r·e_r) = W_0`，其中
`e_r = prefixWeightSumList(sc_r, W_r+1) + 5·q_r`。 -/
theorem cycleRiseBlockSegmentErrorSumRank_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let _T := fun r => (Finset.range r).sum W
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    let e := fun r => prefixWeightSumList (sc r) (W r + 1) +
      5 * CycleBridge.cycleRiseBlockC3TailState d r
    twoValuation ((Finset.range d.blockCount).sum (fun r => c r * e r)) = W 0 := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let T := fun r => (Finset.range r).sum W
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let e := fun r => prefixWeightSumList (sc r) (W r + 1) +
    5 * CycleBridge.cycleRiseBlockC3TailState d r
  let a := fun r => c r * e r
  let v := fun r => T (r + 1)
  have hWpos : ∀ r, r < K → 1 ≤ W r := by
    intro r hr
    have hc3ne : cycleNextC3Word d r ≠ [] := by
      by_cases hnext : r + 1 < d.blockCount
      · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
      · have hpos0 : 0 < d.blockCount := by omega
        simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
    have hne_sc : sc r ≠ [] := by
      intro hsc
      have hlen0 : (sc r).length = 0 := by rw [hsc]; simp
      have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
      have hlen_pos : 0 < (sc r).length := by
        dsimp [sc]
        rw [List.length_append]
        omega
      omega
    have hpos_entries : ∀ t ∈ sc r, 1 ≤ t := by
      intro t ht
      rcases List.mem_append.mp ht with hsuf | hc3
      · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
      · by_cases hnext : r + 1 < d.blockCount
        · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
          omega
        · have hpos0 : 0 < d.blockCount := by omega
          have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
          omega
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one (sc r) hpos_entries
    have hlen : 1 ≤ (sc r).length := List.length_pos_iff.mpr hne_sc
    dsimp [W]
    omega
  have hq_pos : ∀ r, r < K → 0 < CycleBridge.cycleRiseBlockC3TailState d r := by
    intro r hr
    have hb_tail : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
      have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
      omega
    have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb_tail
    have hodd : S6Audit.IsOdd
        (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) :=
      S6Audit.FullOrbitFrom7_odd _ hfull
    by_contra hnot
    change ¬ 0 < StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m at hnot
    have h0 : StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m = 0 := by omega
    rw [h0] at hodd
    change 0 % 2 = 1 at hodd
    norm_num at hodd
  have he_pos : ∀ r, r < K → 0 < e r := by
    intro r hr
    dsimp [e]
    have hs_nonneg : 0 ≤ prefixWeightSumList (sc r) (W r + 1) := Nat.zero_le _
    have hq : 0 < CycleBridge.cycleRiseBlockC3TailState d r := hq_pos r hr
    nlinarith
  have hpos_a : ∀ r, r < K → 0 < a r := by
    intro r hr
    dsimp [a]
    have hc_pos : 0 < c r := by
      dsimp [c]
      apply Nat.mul_pos
      · exact Finset.prod_pos (by intro i hi; positivity)
      · exact Finset.prod_pos (by intro i hi; positivity)
    exact Nat.mul_pos hc_pos (he_pos r hr)
  have hv : ∀ r, r < K → twoValuation (a r) = v r := by
    intro r hr
    have hEr := cycleRiseBlockSegmentErrorRank_eq h d r hr (hLle r hr)
    have hval_e : twoValuation (e r) = W r := by
      dsimp [e]
      exact hEr
    have hprod2 : (Finset.range r).prod (fun i => 2 ^ W i) = 2 ^ T r := by
      dsimp [T]
      rw [Finset.prod_pow_eq_pow_sum]
    have hodd5 : ((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)) % 2 = 1 := by
      apply Finset.prod_odd_mod_two
      intro i hi
      exact StringFlow.Lte.five_pow_odd (sc (r + i)).length
    have hc : c r = 2 ^ T r * ((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)) := by
      dsimp [c]
      rw [hprod2]
    have hval : twoValuation (a r) = T r + W r := by
      dsimp [a]
      rw [hc]
      rw [Nat.mul_assoc]
      have hpos_odd5e : 0 < ((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)) * e r :=
        Nat.mul_pos (by exact Finset.prod_pos (by intro i hi; positivity)) (he_pos r hr)
      have htwo := StringFlow.Lte.twoValuation_mul_two_pow (T r)
        (((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)) * e r) hpos_odd5e
      rw [htwo]
      have hv2 : twoValuation
          (((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)) * e r) =
          twoValuation (e r) :=
        StringFlow.Lte.twoValuation_mul_odd
          ((Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length))
          (e r) hodd5 (he_pos r hr)
      rw [hv2, hval_e]
    have hvdef : v r = T (r + 1) := by rfl
    have hT : T (r + 1) = T r + W r := by
      dsimp [T]
      rw [Finset.sum_range_succ]
    rw [hval, hvdef, hT]
  have hstrict : ∀ i j, i < j → j < K → v i < v j := by
    intro i j hij hjK
    dsimp [v]
    have hlt := Finset.sum_range_lt_of_pos (i + 1) (j + 1) W (by omega)
      (fun r hr1 hr2 => hWpos r (by omega))
    exact hlt
  have hres := twoValuation_sum_range_of_strict K a v hpos_a hv hstrict hpos
  have hv0 : v 0 = W 0 := by
    dsimp [v, T]
    simp
  rwa [hv0] at hres

/-- 首块边界态同余：`E_0 + 5·q_0 ≡ 0 [MOD 2^S]`。 -/
theorem cycleRiseBlockE0_neg_five_q_mod
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    prefixWeightSumList (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) S +
      5 * CycleBridge.cycleRiseBlockC3TailState d 0 ≡
      0 [MOD 2 ^ S] := by
  let b := CycleBridge.cycleRiseBlockTailDepth d 0
  let E0 := prefixWeightSumList (CycleBridge.cyclicSegmentAt w b) S
  let q := CycleBridge.cycleRiseBlockC3TailState d 0
  have hS : 1 ≤ S := by
    by_contra hnot
    have hS0 : S = 0 := by omega
    have hlt := CycleBridge.cycleQb8Input_weak_comparison h
    rw [hS0] at hlt
    norm_num at hlt
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos
    omega
  have hArot := CycleBridge.cycleQb8Input_rotated_wordA h b hb
  have hmodA := wordA_cyclic_mod_two_pow_prefixWeight_sum w b S hb hS
  have hmodA' : StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w b) ≡
      5 ^ (P - 1) * E0 [MOD 2 ^ S] := by
    dsimp [E0]
    have hlen : (CycleBridge.cyclicSegmentAt w b).length = w.length :=
      CycleBridge.cyclicSegmentAt_length w b hb
    simpa [prefixWeightSumList, hlen, d.hperiod] using hmodA
  have hqΔ : q * (2 ^ S - 5 ^ P) + q * 5 ^ P ≡ 0 [MOD 2 ^ S] := by
    have hsubadd : (2 ^ S - 5 ^ P) + 5 ^ P = 2 ^ S := by
      have hlt := CycleBridge.cycleQb8Input_weak_comparison h
      exact Nat.sub_add_cancel (le_of_lt hlt)
    have hsum : q * (2 ^ S - 5 ^ P) + q * 5 ^ P = q * 2 ^ S := by
      rw [← Nat.mul_add, hsubadd]
    have hzero : q * 2 ^ S ≡ 0 [MOD 2 ^ S] := by
      rw [Nat.ModEq]
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right (2 ^ S) q
    rw [hsum.symm] at hzero
    exact hzero
  have hAq : StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w b) + 5 ^ P * q ≡ 0 [MOD 2 ^ S] := by
    change StringFlow.Word.wordOrbit (w.take b) m * (2 ^ S - 5 ^ P) + q * 5 ^ P ≡ 0 [MOD 2 ^ S] at hqΔ
    rw [hArot] at hqΔ
    simpa [Nat.mul_comm] using hqΔ
  have hadd := Nat.ModEq.add hmodA' (Nat.ModEq.refl (5 ^ P * q))
  have hcong : 5 ^ (P - 1) * E0 + 5 ^ P * q ≡ 0 [MOD 2 ^ S] :=
    hadd.symm.trans hAq
  have hfac : 5 ^ (P - 1) * (E0 + 5 * q) = 5 ^ (P - 1) * E0 + 5 ^ P * q := by
    rw [Nat.mul_add]
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    have hpow : 5 ^ (P - 1) * 5 = 5 ^ P := by
      have hPpos : 1 ≤ P := by omega
      have hPsucc : P = (P - 1) + 1 := by omega
      rw [hPsucc, Nat.pow_succ]
      rw [show P - 1 + 1 - 1 = P - 1 by omega]
    rw [← Nat.mul_assoc, hpow]
  have hcong' : 5 ^ (P - 1) * (E0 + 5 * q) ≡ 0 [MOD 2 ^ S] := by
    rw [← hfac] at hcong
    exact hcong
  have hinv := StringFlow.PmiLocalLemma.pow5Inv_correct_local (P - 1) S hS
  have hmul := Nat.ModEq.mul_left (S6Audit.pow5Inv (P - 1) S) hcong'
  have hrearr : S6Audit.pow5Inv (P - 1) S * (5 ^ (P - 1) * (E0 + 5 * q)) =
      (5 ^ (P - 1) * S6Audit.pow5Inv (P - 1) S) * (E0 + 5 * q) := by ring
  have hmul' : (5 ^ (P - 1) * S6Audit.pow5Inv (P - 1) S) * (E0 + 5 * q) ≡ 0 [MOD 2 ^ S] := by
    rwa [hrearr] at hmul
  have h1 := Nat.ModEq.mul hinv (Nat.ModEq.refl (E0 + 5 * q))
  simpa [E0, q, b] using (h1.symm.trans hmul')

/-- 方向引理：`5^P·q_0 ≤ Σ_r c_r·q_r`（`c_0 = 5^P`）。 -/
theorem cycleRiseBlockQSum_ge_zero
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    5 ^ P * CycleBridge.cycleRiseBlockC3TailState d 0 ≤
      (Finset.range d.blockCount).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  have hc0 : c 0 = 5 ^ P := by
    dsimp [c]
    simp
    have hprod5 : (Finset.range K).prod (fun i => 5 ^ (sc i).length) = 5 ^ P := by
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum := cycleRiseBlockSegmentLengthSum d hpos
      simpa [K, sc] using hsum
    rw [hprod5]
  have hle : c 0 * CycleBridge.cycleRiseBlockC3TailState d 0 ≤
      (Finset.range K).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) :=
    Finset.single_le_sum (s := Finset.range K)
      (f := fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r)
      (a := 0)
      (by intro b hb; exact Nat.zero_le _)
      (by exact Finset.mem_range.mpr (by dsimp [K]; exact hpos))
  rwa [hc0] at hle

/-- 纯正项形式：`Σ c_r q_r − 5^P q_0 = Σ_{r=1}^{K−1} c_{r+1} q_{r+1}`。 -/
theorem cycleRiseBlockQSumTail_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    (Finset.range d.blockCount).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) -
      5 ^ P * CycleBridge.cycleRiseBlockC3TailState d 0 =
      (Finset.range (d.blockCount - 1)).sum
        (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1)) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  have hc0 : c 0 = 5 ^ P := by
    dsimp [c]
    simp
    have hprod5 : (Finset.range K).prod (fun i => 5 ^ (sc i).length) = 5 ^ P := by
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum := cycleRiseBlockSegmentLengthSum d hpos
      simpa [K, sc] using hsum
    rw [hprod5]
  have hsplit : (Finset.range K).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) =
      (Finset.range (K - 1)).sum
        (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1)) +
        c 0 * CycleBridge.cycleRiseBlockC3TailState d 0 := by
    have hK : K = (K - 1) + 1 := by omega
    rw [hK]
    rw [Finset.sum_range_succ']
    rw [show K - 1 + 1 - 1 = K - 1 by omega]
  have hge := cycleRiseBlockQSum_ge_zero _h d hpos
  have hle : c 0 * CycleBridge.cycleRiseBlockC3TailState d 0 ≤
      (Finset.range K).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) := by
    have hge' : 5 ^ P * CycleBridge.cycleRiseBlockC3TailState d 0 ≤
        (Finset.range K).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) := by
      simpa [K, c, sc, W] using hge
    rwa [← hc0] at hge'
  change (Finset.range K).sum (fun r => c r * CycleBridge.cycleRiseBlockC3TailState d r) -
      5 ^ P * CycleBridge.cycleRiseBlockC3TailState d 0 =
    (Finset.range (K - 1)).sum
      (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1))
  rw [hsplit]
  rw [← hc0]
  omega

/-- 纯正项 q-和估值：`v2(Σ_{r=0}^{K−2} c_{r+1}·q_{r+1}) = W_0`。
每项 `c_{r+1}·q_{r+1}` 的 2-adic 秩恰为 `T_{r+1}`（`q` 是真实奇数态，
`c_{r+1}` 的 2 因子恰为 `2^{T_{r+1}}`），故尾部和的秩等于首项秩 `W_0`。 -/
theorem cycleRiseBlockQSumTailRank_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hK2 : 2 ≤ d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    twoValuation ((Finset.range (d.blockCount - 1)).sum
      (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1))) = W 0 := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let T := fun r => (Finset.range r).sum W
  let a := fun r => c (r + 1) * q (r + 1)
  let v := fun r => T (r + 1)
  have hWpos : ∀ r, r < K → 1 ≤ W r := by
    intro r hr
    have hc3ne : cycleNextC3Word d r ≠ [] := by
      by_cases hnext : r + 1 < d.blockCount
      · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
      · have hpos0 : 0 < d.blockCount := by omega
        simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
    have hne_sc : sc r ≠ [] := by
      intro hsc
      have hlen0 : (sc r).length = 0 := by rw [hsc]; simp
      have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
      have hlen_pos : 0 < (sc r).length := by
        dsimp [sc]
        rw [List.length_append]
        omega
      omega
    have hpos_entries : ∀ t ∈ sc r, 1 ≤ t := by
      intro t ht
      rcases List.mem_append.mp ht with hsuf | hc3
      · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
      · by_cases hnext : r + 1 < d.blockCount
        · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
          omega
        · have hpos0 : 0 < d.blockCount := by omega
          have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
          omega
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one (sc r) hpos_entries
    have hlen : 1 ≤ (sc r).length := List.length_pos_iff.mpr hne_sc
    dsimp [W]
    omega
  have hq_pos : ∀ r, r < K → 0 < q r := by
    intro r hr
    have hb_tail : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
      have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
      omega
    have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb_tail
    have hodd : S6Audit.IsOdd
        (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) :=
      S6Audit.FullOrbitFrom7_odd _ hfull
    by_contra hnot
    change ¬ 0 < StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m at hnot
    have h0 : StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m = 0 := by omega
    rw [h0] at hodd
    change 0 % 2 = 1 at hodd
    norm_num at hodd
  have hq_odd : ∀ r, r < K → q r % 2 = 1 := by
    intro r hr
    have hb_tail : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
      have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
      omega
    have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb_tail
    dsimp [q]
    exact S6Audit.FullOrbitFrom7_odd
      (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) hfull
  have hq_v2 : ∀ r, r < K → twoValuation (q r) = 0 := by
    intro r hr
    exact StringFlow.twoValuation_odd (q r) (hq_odd r hr)
  have hpos_a : ∀ r, r < K - 1 → 0 < a r := by
    intro r hr
    have hr' : r + 1 < K := by omega
    dsimp [a]
    have hc_pos : 0 < c (r + 1) := by
      dsimp [c]
      apply Nat.mul_pos
      · exact Finset.prod_pos (by intro i hi; positivity)
      · exact Finset.prod_pos (by intro i hi; positivity)
    exact Nat.mul_pos hc_pos (hq_pos (r + 1) hr')
  have hv : ∀ r, r < K - 1 → twoValuation (a r) = v r := by
    intro r hr
    have hr' : r + 1 < K := by omega
    have hprod2 : (Finset.range (r + 1)).prod (fun i => 2 ^ W i) = 2 ^ T (r + 1) := by
      dsimp [T]
      rw [Finset.prod_pow_eq_pow_sum]
    have hodd5 : ((Finset.range (K - (r + 1))).prod
        (fun i => 5 ^ (sc (r + 1 + i)).length)) % 2 = 1 := by
      apply Finset.prod_odd_mod_two
      intro i hi
      exact StringFlow.Lte.five_pow_odd (sc (r + 1 + i)).length
    have hc : c (r + 1) =
        2 ^ T (r + 1) * ((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) := by
      dsimp [c]
      rw [hprod2]
    have hval_q : twoValuation (q (r + 1)) = 0 := hq_v2 (r + 1) hr'
    have hval : twoValuation (a r) = T (r + 1) := by
      dsimp [a]
      rw [hc]
      rw [Nat.mul_assoc]
      have hpos_odd5q : 0 < ((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) * q (r + 1) :=
        Nat.mul_pos (by exact Finset.prod_pos (by intro i hi; positivity))
          (hq_pos (r + 1) hr')
      have htwo := StringFlow.Lte.twoValuation_mul_two_pow (T (r + 1))
        (((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) * q (r + 1)) hpos_odd5q
      rw [htwo]
      have hv2 : twoValuation
          (((Finset.range (K - (r + 1))).prod
            (fun i => 5 ^ (sc (r + 1 + i)).length)) * q (r + 1)) =
          twoValuation (q (r + 1)) :=
        StringFlow.Lte.twoValuation_mul_odd
          ((Finset.range (K - (r + 1))).prod
            (fun i => 5 ^ (sc (r + 1 + i)).length))
          (q (r + 1)) hodd5 (hq_pos (r + 1) hr')
      rw [hv2, hval_q]
      omega
    change twoValuation (a r) = T (r + 1)
    exact hval
  have hstrict : ∀ i j, i < j → j < K - 1 → v i < v j := by
    intro i j hij hjK
    dsimp [v, T]
    have hlt := Finset.sum_range_lt_of_pos (i + 1) (j + 1) W (by omega)
      (fun r hr1 hr2 => hWpos r (by omega))
    exact hlt
  have hKpos : 0 < K - 1 := by omega
  have hres := twoValuation_sum_range_of_strict (K - 1) a v hpos_a hv hstrict hKpos
  have hv0 : v 0 = W 0 := by
    dsimp [v, T]
    simp
  rw [hv0] at hres
  simpa [K, sc, W, c, q, T, a, v] using hres

/-- 纯系数和 `C = Σ_{r=0}^{K−2} c_{r+1}` 的估值：`v2(C) = W_0`。
每项 `c_{r+1}` 的 2-adic 秩恰为 `T_{r+1}`，严格递增，故等于首项秩。 -/
theorem cycleRiseBlockCsumRank_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hK2 : 2 ≤ d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    twoValuation ((Finset.range (d.blockCount - 1)).sum
      (fun r => c (r + 1))) = W 0 := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let T := fun r => (Finset.range r).sum W
  let a := fun r => c (r + 1)
  let v := fun r => T (r + 1)
  have hWpos : ∀ r, r < K → 1 ≤ W r := by
    intro r hr
    have hc3ne : cycleNextC3Word d r ≠ [] := by
      by_cases hnext : r + 1 < d.blockCount
      · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
      · have hpos0 : 0 < d.blockCount := by omega
        simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
    have hne_sc : sc r ≠ [] := by
      intro hsc
      have hlen0 : (sc r).length = 0 := by rw [hsc]; simp
      have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
      have hlen_pos : 0 < (sc r).length := by
        dsimp [sc]
        rw [List.length_append]
        omega
      omega
    have hpos_entries : ∀ t ∈ sc r, 1 ≤ t := by
      intro t ht
      rcases List.mem_append.mp ht with hsuf | hc3
      · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
      · by_cases hnext : r + 1 < d.blockCount
        · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
          omega
        · have hpos0 : 0 < d.blockCount := by omega
          have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
          have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
          omega
    have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one (sc r) hpos_entries
    have hlen : 1 ≤ (sc r).length := List.length_pos_iff.mpr hne_sc
    dsimp [W]
    omega
  have hpos_a : ∀ r, r < K - 1 → 0 < a r := by
    intro r hr
    dsimp [a]
    have hc_pos : 0 < c (r + 1) := by
      dsimp [c]
      apply Nat.mul_pos
      · exact Finset.prod_pos (by intro i hi; positivity)
      · exact Finset.prod_pos (by intro i hi; positivity)
    exact hc_pos
  have hv : ∀ r, r < K - 1 → twoValuation (a r) = v r := by
    intro r hr
    have hprod2 : (Finset.range (r + 1)).prod (fun i => 2 ^ W i) = 2 ^ T (r + 1) := by
      dsimp [T]
      rw [Finset.prod_pow_eq_pow_sum]
    have hodd5 : ((Finset.range (K - (r + 1))).prod
        (fun i => 5 ^ (sc (r + 1 + i)).length)) % 2 = 1 := by
      apply Finset.prod_odd_mod_two
      intro i hi
      exact StringFlow.Lte.five_pow_odd (sc (r + 1 + i)).length
    have hc : c (r + 1) =
        2 ^ T (r + 1) * ((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) := by
      dsimp [c]
      rw [hprod2]
    have hval : twoValuation (a r) = T (r + 1) := by
      dsimp [a]
      rw [hc]
      have hpos5 : 0 < ((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) :=
        Finset.prod_pos (by intro i hi; positivity)
      have htwo := StringFlow.Lte.twoValuation_mul_two_pow (T (r + 1))
        ((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length)) hpos5
      rw [htwo]
      have hodd0 : twoValuation (((Finset.range (K - (r + 1))).prod
          (fun i => 5 ^ (sc (r + 1 + i)).length))) = 0 :=
        StringFlow.twoValuation_odd
          ((Finset.range (K - (r + 1))).prod
            (fun i => 5 ^ (sc (r + 1 + i)).length)) hodd5
      rw [hodd0]
      omega
    dsimp [v]
    exact hval
  have hstrict : ∀ i j, i < j → j < K - 1 → v i < v j := by
    intro i j hij hjK
    dsimp [v]
    have hlt := Finset.sum_range_lt_of_pos (i + 1) (j + 1) W (by omega)
      (fun r hr1 hr2 => hWpos r (by omega))
    exact hlt
  have hKpos : 0 < K - 1 := by omega
  have hres := twoValuation_sum_range_of_strict (K - 1) a v hpos_a hv hstrict hKpos
  have hv0 : v 0 = W 0 := by
    dsimp [v, T]
    simp
  rw [hv0] at hres
  simpa [K, sc, W, c, a, v, T] using hres

/-- q-和尾和的必要中间式：`v2(D) = W_0` 且 `0 < D`，故
`2^{W_0} ≤ D`（`D = Σ_{r=0}^{K−2} c_{r+1}·q_{r+1}`）。 -/
theorem cycleRiseBlockQSumTail_ge_two_pow_W0
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hK2 : 2 ≤ d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    2 ^ W 0 ≤ (Finset.range (d.blockCount - 1)).sum
      (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1)) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let D := (Finset.range (K - 1)).sum (fun r => c (r + 1) * q (r + 1))
  have hval := cycleRiseBlockQSumTailRank_eq h d hK2
  have hq_pos : ∀ r, r < K → 0 < q r := by
    intro r hr
    have hb_tail : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
      have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
      omega
    have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb_tail
    have hodd : S6Audit.IsOdd
        (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) :=
      S6Audit.FullOrbitFrom7_odd _ hfull
    by_contra hnot
    change ¬ 0 < StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m at hnot
    have h0 : StringFlow.Word.wordOrbit
        (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m = 0 := by omega
    rw [h0] at hodd
    change 0 % 2 = 1 at hodd
    norm_num at hodd
  have hposD : 0 < D := by
    dsimp [D]
    apply Finset.sum_pos
    · intro r hr
      have hrlt : r < K - 1 := Finset.mem_range.mp hr
      have hr1 : r + 1 < K := by omega
      dsimp [q]
      apply Nat.mul_pos
      · have hc_pos : 0 < c (r + 1) := by
          dsimp [c]
          apply Nat.mul_pos
          · exact Finset.prod_pos (by intro i hi; positivity)
          · exact Finset.prod_pos (by intro i hi; positivity)
        exact hc_pos
      · exact hq_pos (r + 1) hr1
    · have hpos1 : 0 < K - 1 := by omega
      exact ⟨0, Finset.mem_range.mpr hpos1⟩
  have hval' : twoValuation D = W 0 := by
    simpa [K, sc, W, c, q, D] using hval
  have hge : W 0 ≤ twoValuation D := by rw [hval']
  have hdvd : 2 ^ W 0 ∣ D :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow D (W 0) hposD).mp hge
  simpa [K, sc, W, c, q, D] using Nat.le_of_dvd hposD hdvd

/-- 候选桥第二条中间式的逐项半边：
`v2(c_{r+1}·(q_{r+1}+1)) = T_{r+1} + R_{r+1}`，其中
`T_{r+1} = Σ_{i≤r} W_i` 是 `c_{r+1}` 的 2 因子指数，
`R_{r+1} = v2(q_{r+1}+1)` 是边界 rank。 -/
theorem cycleRiseBlockQSumTermRank_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (_hr : r + 1 < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    twoValuation (c (r + 1) * (CycleBridge.cycleRiseBlockC3TailState d (r + 1) + 1)) =
      (Finset.range (r + 1)).sum W + CycleBridge.cycleRiseBlockTailRank d (r + 1) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let R := fun r => CycleBridge.cycleRiseBlockTailRank d r
  let T := fun r => (Finset.range r).sum W
  have hprod2 : (Finset.range (r + 1)).prod (fun i => 2 ^ W i) = 2 ^ T (r + 1) := by
    dsimp [T]
    rw [Finset.prod_pow_eq_pow_sum]
  have hodd5 : ((Finset.range (K - (r + 1))).prod
      (fun i => 5 ^ (sc (r + 1 + i)).length)) % 2 = 1 := by
    apply Finset.prod_odd_mod_two
    intro i hi
    exact StringFlow.Lte.five_pow_odd (sc (r + 1 + i)).length
  have hc : c (r + 1) =
      2 ^ T (r + 1) * ((Finset.range (K - (r + 1))).prod
        (fun i => 5 ^ (sc (r + 1 + i)).length)) := by
    dsimp [c]
    rw [hprod2]
  have hpos : 0 < q (r + 1) + 1 := by positivity
  have hvalq : twoValuation (q (r + 1) + 1) = R (r + 1) := by
    dsimp [q, R, CycleBridge.cycleRiseBlockTailRank, CycleBridge.cycleRiseBlockC3TailState,
      CycleBridge.cycleRiseBlockTailDepth]
  have hpos_odd5q : 0 < ((Finset.range (K - (r + 1))).prod
      (fun i => 5 ^ (sc (r + 1 + i)).length)) * (q (r + 1) + 1) := by
    exact Nat.mul_pos (by exact Finset.prod_pos (by intro i hi; positivity)) hpos
  have htwo := StringFlow.Lte.twoValuation_mul_two_pow (T (r + 1))
    (((Finset.range (K - (r + 1))).prod
      (fun i => 5 ^ (sc (r + 1 + i)).length)) * (q (r + 1) + 1)) hpos_odd5q
  have hv2 : twoValuation (((Finset.range (K - (r + 1))).prod
      (fun i => 5 ^ (sc (r + 1 + i)).length)) * (q (r + 1) + 1)) =
      twoValuation (q (r + 1) + 1) :=
    StringFlow.Lte.twoValuation_mul_odd
      ((Finset.range (K - (r + 1))).prod
        (fun i => 5 ^ (sc (r + 1 + i)).length))
      (q (r + 1) + 1) hodd5 hpos
  have hval : twoValuation (c (r + 1) * (q (r + 1) + 1)) =
      T (r + 1) + R (r + 1) := by
    rw [hc]
    rw [Nat.mul_assoc]
    rw [htwo]
    rw [hv2, hvalq]
  change twoValuation (c (r + 1) * (q (r + 1) + 1)) =
    (Finset.range (r + 1)).sum W + R (r + 1)
  simpa [T] using hval

/-- v2 的加法下界：`v2(a+b) ≥ min(v2 a, v2 b)`（正项）。 -/
lemma twoValuation_add_ge_min (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Nat.min (twoValuation a) (twoValuation b) ≤ twoValuation (a + b) := by
  let k := Nat.min (twoValuation a) (twoValuation b)
  have hka : k ≤ twoValuation a := by
    dsimp [k]
    exact Nat.min_le_left _ _
  have hkb : k ≤ twoValuation b := by
    dsimp [k]
    exact Nat.min_le_right _ _
  have hda : 2 ^ k ∣ a :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow a k ha).mp hka
  have hdb : 2 ^ k ∣ b :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow b k hb).mp hkb
  have hd : 2 ^ k ∣ a + b := by
    rcases hda with ⟨x, hx⟩
    rcases hdb with ⟨y, hy⟩
    refine ⟨x + y, ?_⟩
    rw [hx, hy]
    ring
  have hpos : 0 < a + b := by omega
  exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (a + b) k hpos).mpr hd

/-- Finset 求和版：正项和的最小单项估值不超过和的估值，
即 `∃ j < m, v j ≤ v2(Σ_{r<m} a r)`。 -/
lemma twoValuation_sum_range_ge_min (m : Nat) (a : Nat → Nat) (v : Nat → Nat)
    (hpos : ∀ r, r < m → 0 < a r)
    (hv : ∀ r, r < m → twoValuation (a r) = v r) :
    0 < m → ∃ j : Nat, j < m ∧ v j ≤ twoValuation ((Finset.range m).sum a) := by
  intro hm
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : 0 < m
      · rcases ih (fun r hr => hpos r (by omega)) (fun r hr => hv r (by omega)) hm0 with
          ⟨j, hj, hjv⟩
        have hsum : (Finset.range (m + 1)).sum a =
            (Finset.range m).sum a + a m := by
          rw [Finset.sum_range_succ]
        have hposm : 0 < a m := hpos m (by omega)
        have hposS : 0 < (Finset.range m).sum a := by
          apply Finset.sum_pos
          · intro r hr
            exact hpos r (by
              have hr' : r < m := Finset.mem_range.mp hr
              omega)
          · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
        have hmin := twoValuation_add_ge_min ((Finset.range m).sum a) (a m) hposS hposm
        have hv2 : twoValuation (a m) = v m := hv m (by omega)
        by_cases hjm : v j ≤ v m
        · have hjm' : v j ≤ twoValuation (a m) := by rwa [hv2]
          have hlemin : v j ≤ Nat.min (twoValuation ((Finset.range m).sum a))
              (twoValuation (a m)) := le_min hjv hjm'
          refine ⟨j, by omega, ?_⟩
          rw [hsum]
          exact le_trans hlemin hmin
        · have hlt : v m < v j := by omega
          have hjm' : v m ≤ twoValuation (a m) := by rw [hv2]
          have hms : v m ≤ twoValuation ((Finset.range m).sum a) :=
            le_trans (le_of_lt hlt) hjv
          have hlemin : v m ≤ Nat.min (twoValuation ((Finset.range m).sum a))
              (twoValuation (a m)) := le_min hms hjm'
          refine ⟨m, by omega, ?_⟩
          rw [hsum]
          exact le_trans hlemin hmin
      · have hm0' : m = 0 := by omega
        subst m
        refine ⟨0, by omega, ?_⟩
        rw [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
        rw [hv 0 (by omega)]

/-- 求和半边：`D + Σ c_{r+1} = Σ c_{r+1}·(q_{r+1}+1)` 的估值
至少 `W_0 + 1`。逐项估值给出 `v r = T_{r+1} + R_{r+1} ≥ W_0 + 1`，
再套求和下界引理。 -/
theorem cycleRiseBlockQSumTailPlusC_rank_ge
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hK2 : 2 ≤ d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    W 0 + 1 ≤ twoValuation ((Finset.range (d.blockCount - 1)).sum
      (fun r => c (r + 1) * (CycleBridge.cycleRiseBlockC3TailState d (r + 1) + 1))) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let R := fun r => CycleBridge.cycleRiseBlockTailRank d r
  let T := fun r => (Finset.range r).sum W
  let a := fun r => c (r + 1) * (q (r + 1) + 1)
  let v := fun r => T (r + 1) + R (r + 1)
  have hpos_a : ∀ r, r < K - 1 → 0 < a r := by
    intro r hr
    dsimp [a]
    have hc_pos : 0 < c (r + 1) := by
      dsimp [c]
      apply Nat.mul_pos
      · exact Finset.prod_pos (by intro i hi; positivity)
      · exact Finset.prod_pos (by intro i hi; positivity)
    exact Nat.mul_pos hc_pos (by positivity)
  have hv_a : ∀ r, r < K - 1 → twoValuation (a r) = v r := by
    intro r hr
    have hr1 : r + 1 < K := by omega
    have hterm := cycleRiseBlockQSumTermRank_eq h d r hr1
    simpa [a, v, q, R, T, K, sc, W, c] using hterm
  have hmin := twoValuation_sum_range_ge_min (K - 1) a v hpos_a hv_a (by omega)
  rcases hmin with ⟨j, hj, hjv⟩
  have hge : W 0 + 1 ≤ v j := by
    dsimp [v]
    have hTge : W 0 ≤ T (j + 1) := by
      dsimp [T]
      exact Finset.single_le_sum (s := Finset.range (j + 1)) (f := W) (a := 0)
        (by intro b hb; exact Nat.zero_le _)
        (by exact Finset.mem_range.mpr (by omega))
    have hRpos : 1 ≤ R (j + 1) := by
      dsimp [R]
      exact cycleRiseBlockTailRank_pos h d (j + 1) (by
        have hKpos : 1 ≤ K := by omega
        omega)
    omega
  simpa [K, sc, W, c, q, a, v, T, R] using le_trans hge hjv

/-- 求和半边的加法分解：`Σ_r c_{r+1}·(q_{r+1}+1) = D + Σ_r c_{r+1}`，
把 q-和尾和 `D` 与 `D+C` 精确绑定。 -/
theorem cycleRiseBlockQSumTailPlusC_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (_hpos : 0 < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    (Finset.range (d.blockCount - 1)).sum
        (fun r => c (r + 1) * (CycleBridge.cycleRiseBlockC3TailState d (r + 1) + 1)) =
      (Finset.range (d.blockCount - 1)).sum
          (fun r => c (r + 1) * CycleBridge.cycleRiseBlockC3TailState d (r + 1)) +
        (Finset.range (d.blockCount - 1)).sum (fun r => c (r + 1)) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  have hsplit : (Finset.range (K - 1)).sum
        (fun r => c (r + 1) * (q (r + 1) + 1)) =
      (Finset.range (K - 1)).sum (fun r => c (r + 1) * q (r + 1)) +
        (Finset.range (K - 1)).sum (fun r => c (r + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simpa [K, sc, W, c, q] using hsplit

/-- rank-gain/残差求和恒等式（加法形式）：
`ΣR + Σ(c3Word r) = Σresidual + 2·blockCount`。 -/
theorem cycleRiseBlockTailRankSum_add_c3WeightSum_eq_residualSum_add_two_mul_blockCount
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) +
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) =
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) +
        2 * d.blockCount := by
  have hper : ∀ r, r < d.blockCount →
      CycleBridge.cycleRiseBlockC3ResidualSum d r + 2 =
        CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum := by
    intro r hr
    have hres := CycleBridge.cycleRiseBlockC3ResidualSum_eq_tailRank_add_c3Weight_sub_two d r hr
    have hRpos : 1 ≤ CycleBridge.cycleRiseBlockTailRank d r :=
      cycleRiseBlockTailRank_pos h d r hr
    have hc3pos : 1 ≤ (d.c3Word r).sum := by
      have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
      have hsumpos : 0 < (d.c3Word r).sum :=
        List.sum_pos (d.c3Word r) (fun t ht => by
          have hge3 : 3 ≤ t := d.hc3_entries r hr t ht
          omega) hne
      omega
    have hge : 2 ≤ CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum := by omega
    have hsub : (CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum - 2) + 2 =
        CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum :=
      Nat.sub_add_cancel hge
    rw [hres]
    exact hsub
  calc
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) +
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum)
        = (Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum) := by
            rw [Finset.sum_add_distrib]
    _ = (Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r + 2) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact (hper r (Finset.mem_range.mp hr)).symm
    _ = (Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) +
          2 * d.blockCount := by
            rw [Finset.sum_add_distrib]
            have hconst : (Finset.range d.blockCount).sum (fun _ => 2) =
                2 * d.blockCount := by
              rw [Finset.sum_const, Finset.card_range]
              ring
            rw [hconst]

/-- 目标改写：求和 rank 预算 `2Σb+13K ≤ ΣR` 等价于残差预算
`Σresidual ≥ Σc3w + 2Σb + 11K`。 -/
theorem cycleRiseBlockResidualBudget_iff_tailRankBudget
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          13 * d.blockCount ≤
        (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) ↔
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) ≥
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) +
          2 * ((Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          11 * d.blockCount := by
  have hbal := cycleRiseBlockTailRankSum_add_c3WeightSum_eq_residualSum_add_two_mul_blockCount h d
  constructor
  · intro hsum
    omega
  · intro hres
    omega

/-- 逐块残差加法恒等式：`residual_r + 2 = R_r + (c3Word r).sum`。 -/
theorem cycleRiseBlockC3ResidualSum_add_two_eq_tailRank_add_c3Weight
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockC3ResidualSum d r + 2 =
      CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum := by
  have hres := CycleBridge.cycleRiseBlockC3ResidualSum_eq_tailRank_add_c3Weight_sub_two d r hr
  have hRpos : 1 ≤ CycleBridge.cycleRiseBlockTailRank d r :=
    cycleRiseBlockTailRank_pos h d r hr
  have hc3pos : 1 ≤ (d.c3Word r).sum := by
    have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
    have hsumpos : 0 < (d.c3Word r).sum :=
      List.sum_pos (d.c3Word r) (fun t ht => by
        have hge3 : 3 ≤ t := d.hc3_entries r hr t ht
        omega) hne
    omega
  have hge : 2 ≤ CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum := by omega
  have hsub : (CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum - 2) + 2 =
      CycleBridge.cycleRiseBlockTailRank d r + (d.c3Word r).sum :=
    Nat.sub_add_cancel hge
  rw [hres]
  exact hsub

/-- 逐块残差恒等式：`R_r = residualSum_r − ((c3Word r).sum − 2)`。 -/
theorem cycleRiseBlockTailRank_eq_residualSum_sub_c3Weight_sub_two
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockTailRank d r =
      CycleBridge.cycleRiseBlockC3ResidualSum d r - ((d.c3Word r).sum - 2) := by
  have hbal := cycleRiseBlockC3ResidualSum_add_two_eq_tailRank_add_c3Weight h d r hr
  have hc3ge : 2 ≤ (d.c3Word r).sum := by
    have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
    rcases List.exists_cons_of_ne_nil hne with ⟨t, rest, hcons⟩
    have ht : 3 ≤ t := d.hc3_entries r hr t (by simp [hcons])
    rw [hcons]
    simp
    omega
  omega

/-- 反证侧残差和上界：`allBelowBudget`（逐块 `R_r ≤ 2b_r+12`）
推出 `Σresidual ≤ 2Σb + Σc3w + 10K`。 -/
theorem allBelowBudget_imp_residualSum_le
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hbelow : Amiya.cycleRiseBlockAllBelowBudget d) :
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) ≤
      2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) +
        10 * d.blockCount := by
  have hbelowR : ∀ r : Nat, r < d.blockCount →
      CycleBridge.cycleRiseBlockTailRank d r ≤
        2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 :=
    (cycleRiseBlockAllBelowBudget_iff_tailRank_le h d).mp hbelow
  have hper : ∀ r, r < d.blockCount →
      CycleBridge.cycleRiseBlockC3ResidualSum d r ≤
        2 * CycleBridge.cycleRiseBlockTailDepth d r + (d.c3Word r).sum + 10 := by
    intro r hr
    have hbal := cycleRiseBlockC3ResidualSum_add_two_eq_tailRank_add_c3Weight h d r hr
    have hR : CycleBridge.cycleRiseBlockTailRank d r ≤
        2 * CycleBridge.cycleRiseBlockTailDepth d r + 12 := hbelowR r hr
    omega
  calc
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r)
        ≤ (Finset.range d.blockCount).sum
            (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r + (d.c3Word r).sum + 10) :=
            Finset.sum_le_sum (by
              intro r hr
              exact hper r (Finset.mem_range.mp hr))
    _ = 2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) +
        10 * d.blockCount := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            have hA : (Finset.range d.blockCount).sum
                (fun r => 2 * CycleBridge.cycleRiseBlockTailDepth d r) =
                2 * ((Finset.range d.blockCount).sum
                  (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) := by
              rw [← Finset.mul_sum]
            have hC : (Finset.range d.blockCount).sum (fun _ => 10) = 10 * d.blockCount := by
              rw [Finset.sum_const, Finset.card_range]
              ring
            rw [hA, hC]

/-- 逐项估值配残差表达：
`v2(c_{r+1}(q_{r+1}+1)) = T_{r+1} + residual_{r+1} + 2 − Σ(c3Word (r+1))`。 -/
theorem cycleRiseBlockQSumTermRank_eq_residual
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r + 1 < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    let c := fun r =>
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod (fun i => 5 ^ (sc (r + i)).length)
    twoValuation (c (r + 1) * (CycleBridge.cycleRiseBlockC3TailState d (r + 1) + 1)) =
      (Finset.range (r + 1)).sum W + CycleBridge.cycleRiseBlockC3ResidualSum d (r + 1) + 2 -
        (d.c3Word (r + 1)).sum := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - r)).prod (fun i => 5 ^ (sc (r + i)).length)
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  have hterm := cycleRiseBlockQSumTermRank_eq h d r hr
  have hres := cycleRiseBlockC3ResidualSum_add_two_eq_tailRank_add_c3Weight h d (r + 1) (by omega)
  have hterm' : twoValuation (c (r + 1) * (q (r + 1) + 1)) =
      (Finset.range (r + 1)).sum W + CycleBridge.cycleRiseBlockTailRank d (r + 1) := by
    simpa [K, sc, W, c, q] using hterm
  have hRform : CycleBridge.cycleRiseBlockTailRank d (r + 1) =
      CycleBridge.cycleRiseBlockC3ResidualSum d (r + 1) + 2 - (d.c3Word (r + 1)).sum := by
    have hRpos : 1 ≤ CycleBridge.cycleRiseBlockTailRank d (r + 1) :=
      cycleRiseBlockTailRank_pos h d (r + 1) (by omega)
    have hge : (d.c3Word (r + 1)).sum ≤
        CycleBridge.cycleRiseBlockC3ResidualSum d (r + 1) + 2 := by omega
    omega
  calc
    twoValuation (c (r + 1) * (q (r + 1) + 1))
        = (Finset.range (r + 1)).sum W + CycleBridge.cycleRiseBlockTailRank d (r + 1) := hterm'
    _ = (Finset.range (r + 1)).sum W + CycleBridge.cycleRiseBlockC3ResidualSum d (r + 1) + 2 -
          (d.c3Word (r + 1)).sum := by
          rw [hRform]
          omega

/-- 真实轨道逐项残差：合法 C3 步（`v2(x+1)=2`，`t≥3`，
`2^t·y = 5x+1`）的残差 `v2(5·((x+1)/4) + 2^{t−2} − 1) ≥ t−2`。 -/
theorem c3_step_residual_ge_weight_sub_two
    (x t y : Nat)
    (hrank : twoValuation (x + 1) = 2)
    (ht : 3 ≤ t)
    (hstep : 2 ^ t * y = 5 * x + 1) :
    t - 2 ≤ twoValuation (5 * ((x + 1) / 4) + 2 ^ (t - 2) - 1) := by
  let u := (x + 1) / 4
  change t - 2 ≤ twoValuation (5 * u + 2 ^ (t - 2) - 1)
  have hpos : 0 < x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (x + 1) hpos
  rw [hrank] at hdec
  have hdiv : (4 * StringFlow.oddPart (x + 1)) / 4 =
      StringFlow.oddPart (x + 1) := by
    simp
  have hx1 : x + 1 = 4 * u := by
    dsimp [u]
    rw [hdec]
    rw [show 2 ^ 2 = 4 by norm_num]
    rw [hdiv]
  have hu1 : 1 ≤ u := by
    have hle : 1 ≤ x + 1 := by omega
    omega
  have hx : x = 4 * u - 1 := by omega
  have hstep2 : 2 ^ t * y = 4 * (5 * u - 1) := by
    calc
      2 ^ t * y = 5 * x + 1 := hstep
      _ = 4 * (5 * u - 1) := by
          rw [hx]
          omega
  have hpow : 2 ^ t = 4 * 2 ^ (t - 2) := by
    rw [show t = (t - 2) + 2 by omega, Nat.pow_add]
    norm_num
    ring
  have hstep3 : 4 * (2 ^ (t - 2) * y) = 4 * (5 * u - 1) := by
    rw [hpow] at hstep2
    simpa [Nat.mul_assoc] using hstep2
  have hstep4 : 2 ^ (t - 2) * y = 5 * u - 1 :=
    Nat.mul_left_cancel (by norm_num : 0 < 4) hstep3
  have hresid : 5 * u + 2 ^ (t - 2) - 1 = 2 ^ (t - 2) * (y + 1) := by
    have hsum : 5 * u + 2 ^ (t - 2) - 1 = (5 * u - 1) + 2 ^ (t - 2) := by omega
    rw [hsum]
    rw [← hstep4]
    rw [Nat.mul_add]
    simp
  have hpos_res : 0 < 5 * u + 2 ^ (t - 2) - 1 := by
    have ht2 : 1 ≤ t - 2 := by omega
    have hpow2 : 2 ≤ 2 ^ (t - 2) := by
      simpa using (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ht2)
    omega
  rw [hresid]
  have htwo := StringFlow.Lte.twoValuation_mul_two_pow (t - 2) (y + 1) (by positivity)
  rw [htwo]
  omega

/-- 真实轨道逐项精确等式：`residual = (t−2) + v2(rj+1)`，
残差超出 `t−2` 的部分正是 C3 步后状态 `rj` 的 rank。
这是把深度/权重与残差绑起来的逐项恒等式（来自
`c3_step_rank_gain_div`）。 -/
theorem c3_step_residual_eq_weight_sub_two_add_rank
    (x t rj : Nat)
    (hrank : twoValuation (x + 1) = 2)
    (ht : 3 ≤ t)
    (hstep : 2 ^ t * rj = 5 * x + 1) :
    twoValuation (5 * ((x + 1) / 4) + 2 ^ (t - 2) - 1) =
      (t - 2) + twoValuation (rj + 1) := by
  have hgain := StringFlow.RealOrbitLocalLemma.c3_step_rank_gain_div x t rj hrank ht hstep
  omega

/-- 弱条件版：只要求 `x+1 = 4·q`（即 `4 ∣ x+1`），
`residual = (t−2) + v2(rj+1)` 仍成立。C3 链后续步的前状态
rank 未必是 2，但 `c3ExactMax` 的 `2^t | 5x+1`（`t≥3`）
给出 `4 ∣ x+1`，所以链上每一步都用这个版本。 -/
theorem c3_step_residual_eq_weight_sub_two_add_rank'
    (x q t rj : Nat)
    (hq : x + 1 = 4 * q)
    (ht : 3 ≤ t)
    (hstep : 2 ^ t * rj = 5 * x + 1) :
    twoValuation (5 * q + 2 ^ (t - 2) - 1) = (t - 2) + twoValuation (rj + 1) := by
  have hgain := StringFlow.RealOrbitLocalLemma.c3_step_rank_gain x q t rj hq ht hstep
  omega

/-- C3 链逐项求和：残差和 = `Σ(t−2)` + 中间 C3 态 rank 和。
链上每步前状态 rank 恒为 2（`state_rank_eq_two_of_outgoing_c3`），
所以逐项等式对每一步适用。 -/
lemma c3Residuals_sum_eq_weights_sub_two_add_rankSum
    (ns ts : List Nat)
    (hQ : 0 < ts.length)
    (h : StringFlow.GC.c3ExactMax ns ts)
    (hweights : ∀ t ∈ ts, 3 ≤ t)
    (hhead : twoValuation (StringFlow.GC.chainFirst ns + 1) = 2) :
    (StringFlow.RealOrbitLocalLemma.c3Residuals ns ts).sum =
      (ts.map (fun t => t - 2)).sum +
        ((ns.drop 1).map (fun s => twoValuation (s + 1))).sum := by
  induction ts generalizing ns with
  | nil => simp at hQ
  | cons t ts' ih =>
      cases ns with
      | nil => simp [StringFlow.GC.c3ExactMax] at h
      | cons n ns' =>
          cases ns' with
          | nil => simp [StringFlow.GC.c3ExactMax] at h
          | cons n' ns'' =>
              rcases h with ⟨hstep, hmax, htail⟩
              have hheadN : twoValuation (n + 1) = 2 := by
                simpa [StringFlow.GC.chainFirst] using hhead
              have hpos5 : 0 < 5 * n + 1 := by positivity
              have hdvd : 2 ^ t ∣ 5 * n + 1 := by
                exact ⟨n', hstep.symm⟩
              have hndvd : ¬ 2 ^ (t + 1) ∣ 5 * n + 1 := by
                intro hd
                have hmod : (5 * n + 1) % 2 ^ (t + 1) = 0 :=
                  Nat.dvd_iff_mod_eq_zero.mp hd
                omega
              have hvalid : twoValuation (5 * n + 1) = t :=
                StringFlow.RealOrbitLocalLemma.twoValuation_eq_of_dvd_pow_not_dvd_succ
                  (5 * n + 1) t hpos5 hdvd hndvd
              have hodd : S6Audit.IsOdd n :=
                StringFlow.RealOrbitLocalLemma.IsOdd_of_rank_two n hheadN
              have hodd' : S6Audit.IsOdd n' :=
                StringFlow.RealOrbitLocalLemma.odd_of_twoValuation_mul_eq_five_mul_add_one
                  n t n' hvalid hstep
              have htge : 3 ≤ t := hweights t (by simp)
              cases ts' with
              | nil =>
                  cases ns'' with
                  | nil =>
                      have hresid_eq : twoValuation
                          (5 * ((n + 1) / 4) + 2 ^ (t - 2) - 1) =
                          (t - 2) + twoValuation (n' + 1) :=
                        c3_step_residual_eq_weight_sub_two_add_rank n t n' hheadN htge hstep
                      simp [StringFlow.RealOrbitLocalLemma.c3Residuals, hresid_eq]
                  | cons _ _ => simp [StringFlow.GC.c3ExactMax] at htail
              | cons t2 ts'' =>
                  cases ns'' with
                  | nil => simp [StringFlow.GC.c3ExactMax] at htail
                  | cons n2 ns''' =>
                      have htailFull : StringFlow.GC.c3ExactMax
                          (n' :: n2 :: ns''') (t2 :: ts'') := htail
                      rcases htail with ⟨hstep2, hmax2, htail2⟩
                      have hvalid' : twoValuation (5 * n' + 1) = t2 := by
                        have hpos5' : 0 < 5 * n' + 1 := by positivity
                        have hdvd' : 2 ^ t2 ∣ 5 * n' + 1 := by
                          exact ⟨n2, hstep2.symm⟩
                        have hndvd' : ¬ 2 ^ (t2 + 1) ∣ 5 * n' + 1 := by
                          intro hd
                          have hmod : (5 * n' + 1) % 2 ^ (t2 + 1) = 0 :=
                            Nat.dvd_iff_mod_eq_zero.mp hd
                          omega
                        exact StringFlow.RealOrbitLocalLemma.twoValuation_eq_of_dvd_pow_not_dvd_succ
                          (5 * n' + 1) t2 hpos5' hdvd' hndvd'
                      have hge3' : 3 ≤ twoValuation (5 * n' + 1) := by
                        have hw : 3 ≤ t2 := hweights t2 (by simp)
                        omega
                      have hheadTail : twoValuation (n' + 1) = 2 :=
                        StringFlow.RealOrbitLocalLemma.state_rank_eq_two_of_outgoing_c3
                          n' hodd' hge3'
                      have hweights' : ∀ t ∈ (t2 :: ts''), 3 ≤ t := by
                        intro u hu
                        exact hweights u (List.mem_cons.mpr (Or.inr hu))
                      have htailSum := ih (n' :: n2 :: ns''') (by simp)
                        htailFull hweights' hheadTail
                      have htge2 : 3 ≤ t2 := hweights t2 (by simp)
                      have hresid_eq2 : twoValuation
                          (5 * ((n' + 1) / 4) + 2 ^ (t2 - 2) - 1) =
                          (t2 - 2) + twoValuation (n2 + 1) :=
                        c3_step_residual_eq_weight_sub_two_add_rank n' t2 n2 hheadTail htge2 hstep2
                      have hresid_eq : twoValuation
                          (5 * ((n + 1) / 4) + 2 ^ (t - 2) - 1) =
                          (t - 2) + twoValuation (n' + 1) :=
                        c3_step_residual_eq_weight_sub_two_add_rank n t n' hheadN htge hstep
                      rw [StringFlow.RealOrbitLocalLemma.c3Residuals, List.sum_cons]
                      change twoValuation (5 * ((n + 1) / 4) + 2 ^ (t - 2) - 1) +
                          (StringFlow.RealOrbitLocalLemma.c3Residuals (n' :: n2 :: ns''') (t2 :: ts'')).sum =
                        (List.map (fun t => t - 2) (t :: t2 :: ts'')).sum +
                          (List.map (fun s => twoValuation (s + 1)) (n' :: n2 :: ns''')).sum
                      rw [htailSum]
                      rw [hresid_eq]
                      simp
                      omega

/-- 残差按 `t−2 + 后状态 rank` 拆开（块级）：
`residualSum_r = Σ_{t∈c3Word r}(t−2) + Σ_{中间C3态} v2(+1)`。 -/
theorem cycleRiseBlockC3ResidualSum_eq_c3WeightSubTwo_add_midRankSum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockC3ResidualSum d r =
      ((d.c3Word r).map (fun t => t - 2)).sum +
        (List.map (fun s => twoValuation (s + 1))
          (List.drop 1 (CycleBridge.c3ChainStates
            (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum := by
  let headState := StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m
  let ns := CycleBridge.c3ChainStates headState (d.c3Word r)
  have hQ : 0 < (d.c3Word r).length := List.length_pos_iff.mpr (d.hc3_nonempty r hr)
  have hmax : StringFlow.GC.c3ExactMax ns (d.c3Word r) := by
    dsimp [ns, headState]
    exact CycleBridge.cycleRiseBlockC3ExactMax d r hr
  have hhead : twoValuation (StringFlow.GC.chainFirst ns + 1) = 2 := by
    dsimp [ns]
    rw [CycleBridge.chainFirst_c3ChainStates headState (d.c3Word r) (d.hc3_nonempty r hr)]
    have hrank : CycleBridge.cycleRiseBlockHeadRank d r = 2 :=
      CycleBridge.cycleRiseBlockHeadRank_two d r hr
    dsimp [headState, CycleBridge.cycleRiseBlockHeadRank] at hrank ⊢
    exact hrank
  have hchain := c3Residuals_sum_eq_weights_sub_two_add_rankSum ns (d.c3Word r) hQ hmax (d.hc3_entries r hr) hhead
  have hdef : CycleBridge.cycleRiseBlockC3ResidualSum d r =
      (StringFlow.RealOrbitLocalLemma.c3Residuals ns (d.c3Word r)).sum := by
    dsimp [ns, headState]
    rfl
  rw [hdef]
  simpa [ns, headState] using hchain

/-- `l.sum = 2·l.length + Σ(t−2)`（每项 ≥ 2）。 -/
lemma list_sum_eq_two_mul_length_add_map_sub_two (l : List Nat)
    (hge : ∀ t ∈ l, 2 ≤ t) :
    l.sum = 2 * l.length + (l.map (fun t => t - 2)).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a = (a - 2) + 2 := by
        have ha2 : 2 ≤ a := hge a (by simp)
        omega
      rw [List.sum_cons, List.length_cons, List.map_cons, List.sum_cons]
      rw [ha, ih (by intro t ht; exact hge t (by simp [ht]))]
      omega

/-- 残差预算 ⇔ 中间态 rank 预算：
`Σ_{after} v2(+1) ≥ 2Σb + 11K + 2·Σc3len`。 -/
theorem cycleRiseBlockResidualBudget_iff_midRankBudget
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (_hpos : 0 < d.blockCount) :
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) ≥
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) +
          2 * ((Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          11 * d.blockCount ↔
    (Finset.range d.blockCount).sum
          (fun r => (List.map (fun s => twoValuation (s + 1))
            (List.drop 1 (CycleBridge.c3ChainStates
              (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum) ≥
        2 * ((Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          11 * d.blockCount +
          2 * (Finset.range d.blockCount).sum (fun r => (d.c3Word r).length) := by
  have hsplit : ∀ r, r < d.blockCount →
      CycleBridge.cycleRiseBlockC3ResidualSum d r =
        ((d.c3Word r).map (fun t => t - 2)).sum +
          (List.map (fun s => twoValuation (s + 1))
            (List.drop 1 (CycleBridge.c3ChainStates
              (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum :=
    cycleRiseBlockC3ResidualSum_eq_c3WeightSubTwo_add_midRankSum d
  have hsumSplit : (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) =
      (Finset.range d.blockCount).sum
          (fun r => ((d.c3Word r).map (fun t => t - 2)).sum) +
        (Finset.range d.blockCount).sum
          (fun r => (List.map (fun s => twoValuation (s + 1))
            (List.drop 1 (CycleBridge.c3ChainStates
              (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact hsplit r (Finset.mem_range.mp hr)
  have hper : ∀ r, r < d.blockCount →
      ((d.c3Word r).map (fun t => t - 2)).sum + 2 * (d.c3Word r).length =
        (d.c3Word r).sum := by
    intro r hr
    have hge : ∀ t ∈ d.c3Word r, 2 ≤ t := by
      intro t ht
      have hge3 := d.hc3_entries r hr t ht
      omega
    have hadd := list_sum_eq_two_mul_length_add_map_sub_two (d.c3Word r) hge
    omega
  have hsum : (Finset.range d.blockCount).sum
      (fun r => ((d.c3Word r).map (fun t => t - 2)).sum + 2 * (d.c3Word r).length) =
    (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hper r (Finset.mem_range.mp hr)
  have hsum' : (Finset.range d.blockCount).sum
      (fun r => ((d.c3Word r).map (fun t => t - 2)).sum) +
      2 * (Finset.range d.blockCount).sum (fun r => (d.c3Word r).length) =
    (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact hsum
  have htwosub : (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).map (fun t => t - 2)).sum) =
      (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) -
        2 * (Finset.range d.blockCount).sum (fun r => (d.c3Word r).length) := by
    omega
  constructor
  · intro hres
    rw [hsumSplit] at hres
    rw [htwosub] at hres
    omega
  · intro hmid
    rw [hsumSplit]
    rw [htwosub]
    omega

/-- `flatten` 长度按段长拆分：`Σ_i |segs.getI i| = segs.flatten.length`。 -/
lemma list_length_join_getI (l : List (List Nat)) :
    (Finset.range l.length).sum (fun i => (l.getI i).length) =
      (List.flatten l).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have hsplit : (Finset.range (as.length + 1)).sum
            (fun i => ((a :: as).getI i).length) =
          a.length + (Finset.range as.length).sum (fun i => (as.getI i).length) := by
        rw [Finset.sum_range_succ']
        simp [List.getI_cons_succ, Nat.add_comm]
      change (Finset.range (as.length + 1)).sum
          (fun i => ((a :: as).getI i).length) = (List.flatten (a :: as)).length
      rw [hsplit, ih]
      simp [List.flatten_cons, List.length_append]

/-- `wordA [] = 0`。 -/
lemma wordA_nil : StringFlow.Word.wordA ([] : List Nat) = 0 := by
  have hvalid : StringFlow.Word.wordValid ([] : List Nat) (0 : Nat) := by
    simp [StringFlow.Word.wordValid]
  have h := StringFlow.Word.word_orbit_identity ([] : List Nat) (0 : Nat) hvalid
  simpa [StringFlow.Word.wordOrbit, StringFlow.wordWeight] using h.symm

/-- `wordA` 对列表拼接的望远镜展开：
`A(flatten segs) = Σ_r (Π_{i<r}2^{W_i})·(Π_{i=r+1}^{m−1}5^{n_i})·A(segs[r])`，
系数为严格后缀 5 幂。 -/
lemma wordA_join_shift (segs : List (List Nat)) :
    StringFlow.Word.wordA (List.flatten segs) =
      (Finset.range segs.length).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (segs.getI i)) *
        (Finset.range (segs.length - 1 - r)).prod (fun i => 5 ^ (segs.getI (r + 1 + i)).length) *
        StringFlow.Word.wordA (segs.getI r)) := by
  induction segs with
  | nil => simpa using wordA_nil
  | cons s rest ih =>
      have hA : StringFlow.Word.wordA (s ++ List.flatten rest) =
          5 ^ (List.flatten rest).length * StringFlow.Word.wordA s +
            2 ^ StringFlow.wordWeight s * StringFlow.Word.wordA (List.flatten rest) :=
        CycleBridge.wordA_append_shift s (List.flatten rest)
      rw [List.flatten_cons, hA]
      change 5 ^ (List.flatten rest).length * StringFlow.Word.wordA s +
          2 ^ StringFlow.wordWeight s * StringFlow.Word.wordA (List.flatten rest) =
        (Finset.range (rest.length + 1)).sum (fun r =>
          (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight ((s :: rest).getI i)) *
          (Finset.range (rest.length + 1 - 1 - r)).prod
            (fun i => 5 ^ ((s :: rest).getI (r + 1 + i)).length) *
          StringFlow.Word.wordA ((s :: rest).getI r))
      rw [Finset.sum_range_succ']
      have hf0 : (Finset.range 0).prod
            (fun i => 2 ^ StringFlow.wordWeight ((s :: rest).getI i)) *
          (Finset.range (rest.length + 1 - 1)).prod
            (fun i => 5 ^ ((s :: rest).getI (0 + 1 + i)).length) *
          StringFlow.Word.wordA ((s :: rest).getI 0) =
        5 ^ (List.flatten rest).length * StringFlow.Word.wordA s := by
        have hprod5 : (Finset.range rest.length).prod
            (fun i => 5 ^ (rest.getI i).length) = 5 ^ (List.flatten rest).length := by
          rw [Finset.prod_pow_eq_pow_sum]
          congr 1
          exact list_length_join_getI rest
        calc
          (Finset.range 0).prod
              (fun i => 2 ^ StringFlow.wordWeight ((s :: rest).getI i)) *
            (Finset.range (rest.length + 1 - 1)).prod
              (fun i => 5 ^ ((s :: rest).getI (0 + 1 + i)).length) *
            StringFlow.Word.wordA ((s :: rest).getI 0)
              = (Finset.range rest.length).prod
                  (fun i => 5 ^ (rest.getI i).length) * StringFlow.Word.wordA s := by
                simp [List.getI_cons_succ, List.getI_eq_getElem, Nat.add_comm]
          _ = 5 ^ (List.flatten rest).length * StringFlow.Word.wordA s := by
            rw [hprod5]
      rw [← hf0]
      have htail : (Finset.range rest.length).sum (fun r =>
          (Finset.range (r + 1)).prod
            (fun i => 2 ^ StringFlow.wordWeight ((s :: rest).getI i)) *
          (Finset.range (rest.length + 1 - 1 - (r + 1))).prod
            (fun i => 5 ^ ((s :: rest).getI (r + 1 + 1 + i)).length) *
        StringFlow.Word.wordA ((s :: rest).getI (r + 1))) =
        2 ^ StringFlow.wordWeight s * StringFlow.Word.wordA (List.flatten rest) := by
        rw [ih]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hlen : rest.length + 1 - 1 - (r + 1) = rest.length - 1 - r := by
          omega
        rw [hlen]
        rw [Finset.prod_range_succ']
        have hget0 : (s :: rest).getI 0 = s := by
          rfl
        have hgeti : ∀ i : Nat, (s :: rest).getI (r + 1 + 1 + i) = rest.getI (r + 1 + i) := by
          intro i
          have hidx : r + 1 + 1 + i = (r + 1 + i) + 1 := by omega
          rw [hidx]
          rfl
        have hgetr : (s :: rest).getI (r + 1) = rest.getI r := by
          rfl
        have hgetk : ∀ k : Nat, (s :: rest).getI (k + 1) = rest.getI k := by
          intro k
          rfl
        rw [hget0]
        simp_rw [hgeti, hgetr, hgetk]
        ac_rfl
      rw [htail]
      ac_rfl

/-- 旋转词按块段整圈拼接：`rot(b_0) = sc_0 ++ sc_1 ++ ... ++ sc_{K-1}`，
其中 `sc_r = suffixWord r ++ cycleNextC3Word r`。 -/
lemma cycleRiseBlockRotatedSegments_flatten
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0) =
      List.flatten ((List.range d.blockCount).map
        (fun r => d.suffixWord r ++ cycleNextC3Word d r)) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let b := fun r => CycleBridge.cycleRiseBlockTailDepth d r
  have hwpos : 0 < w.length := by
    rw [d.hperiod]
    have hc3 : (d.c3Word 0) ≠ [] := d.hc3_nonempty 0 hpos
    have hlen : 0 < (d.c3Word 0).length := List.length_pos_iff.mpr hc3
    have hle : (d.c3Word 0).length ≤ P := by
      have hP := CycleBridge.cycleRiseBlockPeriodSum_list d hpos
      have hm : (d.c3Word 0).length ≤
          ((List.range d.blockCount).map
            (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
        have hmem : (d.c3Word 0).length + (d.suffixWord 0).length ∈
            (List.range d.blockCount).map
              (fun r => (d.c3Word r).length + (d.suffixWord r).length) :=
          List.mem_map.mpr ⟨0, List.mem_range.mpr hpos, by simp⟩
        exact le_trans (Nat.le_add_right (d.c3Word 0).length (d.suffixWord 0).length)
          (List.le_sum_of_mem hmem)
      exact le_trans hm (le_of_eq hP.symm)
    omega
  have hLle : ∀ r : Nat, r < K → (d.suffixWord r).length ≤ w.length := by
    intro r hr
    rw [d.hperiod]
    have hseg := cycleRiseBlockSegmentLengthSum d hpos
    have hle : (d.suffixWord r ++ cycleNextC3Word d r).length ≤ P := by
      have hle' : (d.suffixWord r ++ cycleNextC3Word d r).length ≤
          (Finset.range K).sum
            (fun i => (d.suffixWord i ++ cycleNextC3Word d i).length) := by
        exact Finset.single_le_sum (s := Finset.range K)
          (f := fun i => (d.suffixWord i ++ cycleNextC3Word d i).length) (a := r)
          (by intro i hi; exact Nat.zero_le _)
          (by simp [Finset.mem_range, hr])
      exact le_trans hle' (le_of_eq hseg)
    have hsuf : (d.suffixWord r).length ≤ (d.suffixWord r ++ cycleNextC3Word d r).length := by
      rw [List.length_append]
      omega
    exact le_trans hsuf hle
  have hrec : ∀ (n : Nat) (r : Nat), r < K → r + n = K →
      (CycleBridge.cyclicSegmentAt w (b r)).take
        ((Finset.range n).sum (fun j => (sc (r + j)).length)) =
        List.flatten ((List.range n).map (fun j => sc (r + j))) := by
    intro n
    induction n with
    | zero =>
        intro r hr hrn
        omega
    | succ n ih =>
        intro r hr hrn
        by_cases hnext : r + 1 < K
        · have hrn' : r + 1 + n = K := by omega
          have hIH := ih (r + 1) (by omega) hrn'
          have htail := cyclicSegmentAt_tail_eq_suffix_c3_append_take d r hr hnext (hLle r hr) hwpos
          have hsc_next : cycleNextC3Word d r = d.c3Word (r + 1) := by
            have hnextK : r + 1 < d.blockCount := by simpa [K] using hnext
            simp [cycleNextC3Word, hnextK]
          have hlen_sc : (sc r).length = (d.suffixWord r).length + (cycleNextC3Word d r).length := by
            rw [List.length_append]
          have htail' : CycleBridge.cyclicSegmentAt w (b r) =
              sc r ++ (CycleBridge.cyclicSegmentAt w (b (r + 1))).take
                (w.length - (d.suffixWord r).length - (cycleNextC3Word d r).length) := by
            dsimp [b, sc]
            rw [← hsc_next] at htail
            exact htail
          have hseg_sum : (Finset.range K).sum (fun i => (sc i).length) = P := by
            simpa [sc] using cycleRiseBlockSegmentLengthSum d hpos
          have hle_sc : (sc r).length ≤ P := by
            rw [← hseg_sum]
            exact Finset.single_le_sum (s := Finset.range K)
              (f := fun i => (sc i).length) (a := r)
              (by intro i hi; exact Nat.zero_le _)
              (by simp [Finset.mem_range, hr])
          have hmain_sum : P = (Finset.range r).sum (fun i => (sc i).length) + (sc r).length +
              (Finset.range n).sum (fun j => (sc (r + 1 + j)).length) := by
            have hsplit := Finset.sum_range_add (fun i => (sc i).length) (r + 1) n
            have hprefix : (Finset.range (r + 1)).sum (fun i => (sc i).length) =
                (Finset.range r).sum (fun i => (sc i).length) + (sc r).length := by
              rw [Finset.sum_range_succ]
            have hmain' : (Finset.range K).sum (fun i => (sc i).length) =
                (Finset.range r).sum (fun i => (sc i).length) + (sc r).length +
                  (Finset.range n).sum (fun j => (sc (r + 1 + j)).length) := by
              rw [← hrn']
              rw [hsplit, hprefix]
            rwa [hseg_sum] at hmain'
          have htail_le : (Finset.range n).sum (fun j => (sc (r + 1 + j)).length) ≤
              P - (sc r).length := by
            have hmain_sum' := hmain_sum
            have hle_sc' := hle_sc
            dsimp [sc] at hmain_sum' hle_sc'
            simp [List.length_append] at hmain_sum' hle_sc'
            have htail_le' : (Finset.range n).sum
                (fun j => (d.suffixWord (r + 1 + j)).length + (cycleNextC3Word d (r + 1 + j)).length) ≤
                P - ((d.suffixWord r).length + (cycleNextC3Word d r).length) := by
              omega
            simpa [sc, List.length_append] using htail_le'
          have htake_len : w.length - (d.suffixWord r).length - (cycleNextC3Word d r).length =
              P - (sc r).length := by
            dsimp [sc] at hlen_sc hle_sc ⊢
            rw [List.length_append] at hle_sc
            rw [d.hperiod]
            have hsub : P - (d.suffixWord r).length - (cycleNextC3Word d r).length =
                P - ((d.suffixWord r).length + (cycleNextC3Word d r).length) := by
              omega
            rw [hsub]
            rw [← hlen_sc]
          have hsum_split : (Finset.range (n + 1)).sum (fun j => (sc (r + j)).length) =
              (sc r).length + (Finset.range n).sum (fun j => (sc (r + 1 + j)).length) := by
            rw [Finset.sum_range_succ']
            have hrest : (Finset.range n).sum (fun k => (sc (r + (k + 1))).length) =
                (Finset.range n).sum (fun k => (sc (r + 1 + k)).length) := by
              apply Finset.sum_congr rfl
              intro k hk
              apply congrArg List.length
              apply congrArg sc
              omega
            have hfirst : (sc (r + 0)).length = (sc r).length := rfl
            rw [hrest, hfirst]
            ac_rfl
          have hrange : (List.range (n + 1)).map (fun j => sc (r + j)) =
              sc r :: (List.range n).map (fun j => sc (r + 1 + j)) := by
            rw [List.range_succ_eq_map]
            simp [Nat.add_comm, Nat.add_left_comm]
          calc
            (CycleBridge.cyclicSegmentAt w (b r)).take
                ((Finset.range (n + 1)).sum (fun j => (sc (r + j)).length))
                = (CycleBridge.cyclicSegmentAt w (b r)).take
                    ((sc r).length + (Finset.range n).sum (fun j => (sc (r + 1 + j)).length)) := by
                    rw [hsum_split]
            _ = (sc r ++ (CycleBridge.cyclicSegmentAt w (b (r + 1))).take (P - (sc r).length)).take
                    ((sc r).length + (Finset.range n).sum (fun j => (sc (r + 1 + j)).length)) := by
                    rw [htail']
                    rw [htake_len]
            _ = sc r ++
                ((CycleBridge.cyclicSegmentAt w (b (r + 1))).take (P - (sc r).length)).take
                  ((Finset.range n).sum (fun j => (sc (r + 1 + j)).length)) := by
                  rw [List.take_append]
                  simp [List.take_of_length_le]
            _ = sc r ++
                (CycleBridge.cyclicSegmentAt w (b (r + 1))).take
                  ((Finset.range n).sum (fun j => (sc (r + 1 + j)).length)) := by
                  rw [List.take_take]
                  have hle1 : (Finset.range n).sum (fun j => (sc (r + 1 + j)).length) ≤
                      P - (sc r).length := by
                    exact htail_le
                  rw [Nat.min_eq_left hle1]
            _ = sc r ++ List.flatten ((List.range n).map (fun j => sc (r + 1 + j))) := by
                  rw [hIH]
            _ = List.flatten ((List.range (n + 1)).map (fun j => sc (r + j))) := by
                  rw [hrange]
                  simp
        · have hlast : r + 1 = K := by omega
          have hn0 : n = 0 := by omega
          subst n
          have hrot_wrap := cyclicSegmentAt_tail_eq_suffix_c3_append_take_wrap d r hr hlast (hLle r hr) hwpos
          have hsc_next : cycleNextC3Word d r = d.c3Word 0 := by
            have hlastK : ¬ r + 1 < d.blockCount := by simpa [K] using (by omega : ¬ r + 1 < K)
            simp [cycleNextC3Word, hlastK]
          have hsc : sc r = d.suffixWord r ++ d.c3Word 0 := by
            simp [sc, hsc_next]
          have hlen_sc : (sc r).length = (d.suffixWord r).length + (d.c3Word 0).length := by
            rw [hsc, List.length_append]
          have hrot' : CycleBridge.cyclicSegmentAt w (b r) =
              sc r ++ (CycleBridge.cyclicSegmentAt w (b 0)).take
                (w.length - (d.suffixWord r).length - (cycleNextC3Word d r).length) := by
            dsimp [b, sc]
            rw [← hsc_next] at hrot_wrap
            exact hrot_wrap
          rw [hrot']
          simp [hsc, List.take_append, List.length_append]
  have hmain := hrec K 0 (by omega) (by simp : 0 + K = K)
  have hPeriodF : (Finset.range d.blockCount).sum
      (fun r => (d.suffixWord r).length + (cycleNextC3Word d r).length) = P := by
    simpa [List.length_append] using cycleRiseBlockSegmentLengthSum d hpos
  have hb0 : CycleBridge.cycleRiseBlockTailDepth d 0 ≤ w.length := by
    have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos
    omega
  have hlenrot : (CycleBridge.cyclicSegmentAt w (b 0)).length = P := by
    rw [CycleBridge.cyclicSegmentAt_length w (CycleBridge.cycleRiseBlockTailDepth d 0) hb0, d.hperiod]
  have htake_full : (CycleBridge.cyclicSegmentAt w (b 0)).take P =
      CycleBridge.cyclicSegmentAt w (b 0) := by
    exact List.take_of_length_le (by rw [hlenrot])
  rw [← htake_full]
  simpa [hPeriodF, K, sc, Nat.zero_add, List.length_append] using hmain

/-- 旋转词按块段的 `wordA` 整圈展开：`A(rot b_0)` 等于带望远镜系数的
块段 `wordA` 求和（`sc_r = suffixWord r ++ cycleNextC3Word r`）。 -/
lemma cycleRiseBlockRotatedWordA_join_shift
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        StringFlow.Word.wordA (d.suffixWord r ++ cycleNextC3Word d r)) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  have hflat := cycleRiseBlockRotatedSegments_flatten d hpos
  rw [hflat]
  have hjoin := wordA_join_shift ((List.range K).map sc)
  rw [hjoin]
  simp only [List.length_map, List.length_range, K]
  apply Finset.sum_congr rfl
  intro r hr
  have hget : ∀ i : Nat, i < d.blockCount → ((List.range d.blockCount).map sc).getI i = sc i := by
    intro i hi
    have hlen : i < ((List.range d.blockCount).map sc).length := by
      simpa [List.length_map, List.length_range] using hi
    rw [List.getI_eq_getElem (l := (List.range d.blockCount).map sc) (n := i) hlen]
    simp [List.getElem_map, List.getElem_range]
  have hgr : r < K := Finset.mem_range.mp hr
  rw [hget r (by simpa [K] using hgr)]
  congr 1
  · congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hget i (by
        have hi' : i < r := Finset.mem_range.mp hi
        have hr' : r < d.blockCount := by simpa [K] using hgr
        omega)]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hget (r + 1 + i) (by
        have hi' : i < K - 1 - r := Finset.mem_range.mp hi
        have hr' : r < d.blockCount := by simpa [K] using hgr
        omega)]

/-- 首块旋转词的分子由整圈闭合给出：
`A(rot b_0) = q_0·(2^S − 5^P)`，`q_0` 是首块 C3 尾态。 -/
lemma cycleRiseBlockRotatedWordA_eq_q0_mul_delta
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) =
      CycleBridge.cycleRiseBlockC3TailState d 0 * (2 ^ S - 5 ^ P) := by
  let b := CycleBridge.cycleRiseBlockTailDepth d 0
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos
    omega
  have hArot := CycleBridge.cycleQb8Input_rotated_wordA h b hb
  rw [← hArot]
  congr 1

/-- 旋转词分子按块段代入后的 q-线性组合：
`A(rot b_0) = Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)`。 -/
lemma cycleRiseBlockRotatedWordA_qLinear
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
            StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            CycleBridge.cycleRiseBlockC3TailState d r)) := by
  rw [cycleRiseBlockRotatedWordA_join_shift d hpos]
  apply Finset.sum_congr rfl
  intro r hr
  rw [cycleRiseBlockSegmentWordA_eq h d r (Finset.mem_range.mp hr)
    (hLle r (Finset.mem_range.mp hr))]

/-- 旋转词分子合并：`q_0·(2^S − 5^P)` 等于块段 q-线性组合，
即 `2^S > 5^P` 的正性通过这条等式进入 q-线性组合。 -/
lemma cycleRiseBlockRotatedWordA_qLinear_eq_q0_delta
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    CycleBridge.cycleRiseBlockC3TailState d 0 * (2 ^ S - 5 ^ P) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
            StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            CycleBridge.cycleRiseBlockC3TailState d r)) := by
  rw [← cycleRiseBlockRotatedWordA_eq_q0_mul_delta h d hpos]
  exact cycleRiseBlockRotatedWordA_qLinear h d hpos hLle

/-- C3 尾态由真实轨道可达性严格正：`0 < q_r`。 -/
lemma cycleRiseBlockC3TailState_pos
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    0 < CycleBridge.cycleRiseBlockC3TailState d r := by
  have hb : CycleBridge.cycleRiseBlockTailDepth d r ≤ w.length := by
    have hblt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < w.length := by
      rw [d.hperiod]
      exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    omega
  have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h
      (CycleBridge.cycleRiseBlockTailDepth d r) hb
  have hodd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m) :=
    S6Audit.FullOrbitFrom7_odd _ hfull
  change 0 < StringFlow.Word.wordOrbit
      (w.take (d.headDepth r + (d.c3Word r).length)) m
  by_contra hnot
  have h0 : StringFlow.Word.wordOrbit
      (w.take (d.headDepth r + (d.c3Word r).length)) m = 0 := by
    omega
  have h0' : StringFlow.Word.wordOrbit
      (w.take (CycleBridge.cycleRiseBlockTailDepth d r)) m = 0 := by
    simpa [CycleBridge.cycleRiseBlockTailDepth] using h0
  rw [h0'] at hodd
  change 0 % 2 = 1 at hodd
  norm_num at hodd

/-- 旋转词分子严格正：`0 < A(rot b_0)`，由 `q_0 > 0` 与 `2^S > 5^P` 给出。 -/
lemma cycleRiseBlockRotatedWordA_pos
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hSgt : 5 ^ P < 2 ^ S) :
    0 < StringFlow.Word.wordA (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) := by
  rw [cycleRiseBlockRotatedWordA_eq_q0_mul_delta h d hpos]
  exact Nat.mul_pos (cycleRiseBlockC3TailState_pos h d 0 hpos) (by omega)

/-- 正性进入 q-线性组合：`0 < Σ_r c_r·(2^{W_r}·q_{r+1} − 5^{n_r}·q_r)`。 -/
lemma cycleRiseBlockRotatedWordA_qLinear_pos
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hSgt : 5 ^ P < 2 ^ S)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    0 < (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
            StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            CycleBridge.cycleRiseBlockC3TailState d r)) := by
  have hposA := cycleRiseBlockRotatedWordA_pos h d hpos hSgt
  rwa [cycleRiseBlockRotatedWordA_qLinear h d hpos hLle] at hposA

/-- 2-adic 估值分解：`v2 x = R` 且 `0 < x` 时，
`x = 2^R·odd` 且 `odd` 是奇数。 -/
lemma nat_eq_two_pow_mul_odd_of_twoValuation {x R : Nat}
    (h : twoValuation x = R) (hx : 0 < x) :
    ∃ odd : Nat, x = 2 ^ R * odd ∧ odd % 2 = 1 := by
  have hdec := n_eq_two_pow_mul_oddPart x hx
  rw [h] at hdec
  refine ⟨oddPart x, hdec, oddPart_odd_of_pos x hx⟩

/-- odd 部分唯一性：`x = 2^R·odd` 且 `odd` 奇数时 `oddPart x = odd`。 -/
lemma oddPart_eq_of_two_pow_mul_odd {x R odd : Nat} (_hx : 0 < x)
    (hdec : x = 2 ^ R * odd) (hodd : odd % 2 = 1) :
    StringFlow.oddPart x = odd := by
  have hodd_pos : 0 < odd := by
    by_cases hz : odd = 0
    · rw [hz] at hodd
      norm_num at hodd
    · exact Nat.pos_of_ne_zero hz
  have hR : twoValuation x = R := by
    rw [hdec]
    rw [StringFlow.Lte.twoValuation_mul_two_pow R odd hodd_pos]
    rw [StringFlow.twoValuation_odd odd hodd]
    omega
  unfold StringFlow.oddPart
  rw [hR, hdec]
  exact Nat.mul_div_right odd (by positivity : 0 < 2 ^ R)

/-- C3 尾态按 rank 分解：`q_r + 1 = 2^{R_r}·odd_r`，`odd_r` 奇数。 -/
lemma cycleRiseBlockC3TailState_eq_two_pow_mul_odd_sub_one
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    ∃ odd : Nat,
      CycleBridge.cycleRiseBlockC3TailState d r + 1 =
        2 ^ CycleBridge.cycleRiseBlockTailRank d r * odd ∧ odd % 2 = 1 := by
  have hqpos : 0 < CycleBridge.cycleRiseBlockC3TailState d r :=
    cycleRiseBlockC3TailState_pos h d r hr
  have hxpos : 0 < CycleBridge.cycleRiseBlockC3TailState d r + 1 := by omega
  exact nat_eq_two_pow_mul_odd_of_twoValuation
    (x := CycleBridge.cycleRiseBlockC3TailState d r + 1)
    (R := CycleBridge.cycleRiseBlockTailRank d r) rfl hxpos

/-- 下一块尾态（循环）按 rank 分解：
`qNext_r + 1 = 2^{RNext_r}·odd_r`，`odd_r` 奇数。 -/
lemma cycleRiseBlockNextTailState_eq_two_pow_mul_odd_sub_one
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    ∃ odd : Nat,
      StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1 =
        2 ^ twoValuation
            (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * odd ∧
        odd % 2 = 1 := by
  have hb_next : cycleNextTailDepth d r ≤ w.length := by
    by_cases hnext : r + 1 < d.blockCount
    · dsimp [cycleNextTailDepth]
      rw [if_pos hnext]
      have hblt : CycleBridge.cycleRiseBlockTailDepth d (r + 1) - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d (r + 1) hnext
      omega
    · have hpos0 : 0 < d.blockCount := by omega
      dsimp [cycleNextTailDepth]
      rw [if_neg hnext]
      have hblt : CycleBridge.cycleRiseBlockTailDepth d 0 - 1 < w.length := by
        rw [d.hperiod]
        exact CycleBridge.cycleRiseBlockTailDepth_lt_succ d 0 hpos0
      omega
  have hfull := CycleBridge.cycleQb8Input_prefix_full_reachable h (cycleNextTailDepth d r) hb_next
  have hodd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m) :=
    S6Audit.FullOrbitFrom7_odd _ hfull
  have hpos : 0 < StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m := by
    by_contra hnot
    have h0 : StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m = 0 := by omega
    rw [h0] at hodd
    change 0 % 2 = 1 at hodd
    norm_num at hodd
  have hxpos : 0 < StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1 := by omega
  exact nat_eq_two_pow_mul_odd_of_twoValuation
    (x := StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)
    (R := twoValuation
      (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) rfl hxpos

/-- q-线性组合按 rank 分解的四项展开：每项
`2^{W_r}·qNext_r − 5^{n_r}·q_r` 代入 `q = 2^R·odd − 1` 后分成
`2^{W+R}·odd − 2^W − 5^n·2^R·odd' + 5^n` 四项。 -/
lemma cycleRiseBlockRotatedWordA_qLinear_fourTerm
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (_hpos : 0 < d.blockCount) :
    (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
            StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            CycleBridge.cycleRiseBlockC3TailState d r)) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        ((2 ^ (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) +
                twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) *
            StringFlow.oddPart (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) -
          2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) -
          (5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
              2 ^ CycleBridge.cycleRiseBlockTailRank d r *
              StringFlow.oddPart (CycleBridge.cycleRiseBlockC3TailState d r + 1) -
            5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length))) := by
  apply Finset.sum_congr rfl
  intro r hr
  have hN := cycleRiseBlockNextTailState_eq_two_pow_mul_odd_sub_one h d r (Finset.mem_range.mp hr)
  have hC := cycleRiseBlockC3TailState_eq_two_pow_mul_odd_sub_one h d r (Finset.mem_range.mp hr)
  rcases hN with ⟨oN, hqN, hoN⟩
  rcases hC with ⟨oC, hqC, hoC⟩
  have hqN' : StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m =
      2 ^ twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN - 1 := by omega
  have hqC' : CycleBridge.cycleRiseBlockC3TailState d r =
      2 ^ CycleBridge.cycleRiseBlockTailRank d r * oC - 1 := by omega
  have hoN' : StringFlow.oddPart
      (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) = oN := by
    exact oddPart_eq_of_two_pow_mul_odd
      (x := StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)
      (R := twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1))
      (by omega) hqN hoN
  have hoC' : StringFlow.oddPart (CycleBridge.cycleRiseBlockC3TailState d r + 1) = oC := by
    exact oddPart_eq_of_two_pow_mul_odd
      (x := CycleBridge.cycleRiseBlockC3TailState d r + 1)
      (R := CycleBridge.cycleRiseBlockTailRank d r)
      (by omega) hqC hoC
  rw [hoN', hoC']
  congr 1
  have hbracket : 2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
        StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m -
      5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
        CycleBridge.cycleRiseBlockC3TailState d r =
      (2 ^ (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) +
            twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) * oN -
        2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) -
        (5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            2 ^ CycleBridge.cycleRiseBlockTailRank d r * oC -
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length) := by
    rw [hqN', hqC']
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
    simp
    rw [show 2 ^ twoValuation
            (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN - 1 + 1 =
          2 ^ twoValuation
            (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN by omega]
    rw [hqN]
    rw [Nat.pow_add]
    congr 1
    have hk' : twoValuation (oN * 2 ^ twoValuation
        (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) =
        twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) := by
      rw [StringFlow.Lte.twoValuation_mul_odd oN (2 ^ twoValuation
          (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) hoN
        (by positivity : 0 < 2 ^ twoValuation
          (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1))]
      simpa using (StringFlow.Lte.twoValuation_mul_two_pow_eq
        (twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) 1 (by norm_num))
    have hk : twoValuation (2 ^ twoValuation
        (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN) =
        twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) := by
      rw [Nat.mul_comm]
      exact hk'
    simp [Nat.mul_comm, Nat.mul_assoc, hk', Nat.pow_add]
    ac_rfl
  rw [hbracket]

/-- 系数恒等式：`A_r·2^{W_r} = c_{r+1}`（与 q-和 `hqval` 的 `c` 一致）。 -/
lemma cycleRiseBlockCoeff_mul_twoPowWeight_eq_c_next
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
      (Finset.range (d.blockCount - 1 - r)).prod
        (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
      2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) =
    (Finset.range (r + 1)).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
      (Finset.range (d.blockCount - (r + 1))).prod
        (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) := by
  have hpre : (Finset.range (r + 1)).prod
        (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) =
      (Finset.range r).prod
          (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) := by
    rw [Finset.prod_range_succ]
  have hpost : d.blockCount - (r + 1) = d.blockCount - 1 - r := by omega
  rw [hpre, hpost]
  ac_rfl

/-- 系数恒等式：`A_r·5^{n_r} = c_r`。 -/
lemma cycleRiseBlockCoeff_mul_fivePowLength_eq_c
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
      (Finset.range (d.blockCount - 1 - r)).prod
        (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
      5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length =
    (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
      (Finset.range (d.blockCount - r)).prod
        (fun i => 5 ^ (d.suffixWord (r + i) ++ cycleNextC3Word d (r + i)).length) := by
  have hpost : d.blockCount - r = (d.blockCount - 1 - r) + 1 := by omega
  rw [hpost]
  rw [Finset.prod_range_succ']
  simp [Nat.add_comm, Nat.add_left_comm]
  ac_rfl

/-- 正性闭式的 Nat 中间式：
`q_0·(2^S−5^P)` 等于四项展开和（fourTerm）。 -/
lemma cycleRiseBlockRotatedWordA_q0_delta_eq_fourTerm
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    CycleBridge.cycleRiseBlockC3TailState d 0 * (2 ^ S - 5 ^ P) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        ((2 ^ (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) +
                twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) *
            StringFlow.oddPart (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) -
          2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) -
          (5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
              2 ^ CycleBridge.cycleRiseBlockTailRank d r *
              StringFlow.oddPart (CycleBridge.cycleRiseBlockC3TailState d r + 1) -
            5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length))) := by
  rw [← cycleRiseBlockRotatedWordA_qLinear_fourTerm h d hpos]
  exact cycleRiseBlockRotatedWordA_qLinear_eq_q0_delta h d hpos hLle

/-- 段加法恒等式的非负性：`5^{n_r}·q_r ≤ 2^{W_r}·qNext_r`，
即 `A(sc_r) = 2^{W_r}·qNext_r − 5^{n_r}·q_r ≥ 0`。 -/
lemma cycleRiseBlockSegmentFivePowMulTailState_le_twoPowMulNext
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
        CycleBridge.cycleRiseBlockC3TailState d r ≤
      2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) *
        StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m := by
  have hadd := cycleRiseBlockSegmentWordA_add_eq h d r hr hLle
  omega

/-- Nat 括号恒等式：`(P−Q)−(R−S) = (P+S)−(Q+R)`，
前提 `Q ≤ P`、`S ≤ R`、`Q+R ≤ P+S`。 -/
lemma nat_sub_sub_eq_add_sub_add {P Q R S : Nat}
    (_hP : Q ≤ P) (hS : S ≤ R) (hQR : Q + R ≤ P + S) :
    (P - Q) - (R - S) = (P + S) - (Q + R) := by
  omega

/-- 四项展开的加法形式：`first + fourth = second + third + q_0·Δ`。
由 `nat_sub_sub_eq_add_sub_add` 把每项括号写成加法，再整体移项。 -/
lemma cycleRiseBlockRotatedWordA_fourTerm_additive
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length) :
    (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ (StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) +
                twoValuation (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1)) *
            StringFlow.oddPart (StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) +
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length)) =
      (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod (fun i => 2 ^ StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - 1 - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + 1 + i) ++ cycleNextC3Word d (r + 1 + i)).length) *
        (2 ^ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) +
          5 ^ (d.suffixWord r ++ cycleNextC3Word d r).length *
            2 ^ CycleBridge.cycleRiseBlockTailRank d r *
            StringFlow.oddPart (CycleBridge.cycleRiseBlockC3TailState d r + 1))) +
        CycleBridge.cycleRiseBlockC3TailState d 0 * (2 ^ S - 5 ^ P) := by
  let K := d.blockCount
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let n := fun r => (sc r).length
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let qN := fun r => StringFlow.Word.wordOrbit (w.take (cycleNextTailDepth d r)) m
  let RN := fun r => twoValuation (qN r + 1)
  let R := fun r => CycleBridge.cycleRiseBlockTailRank d r
  let oN := fun r => StringFlow.oddPart (qN r + 1)
  let oC := fun r => StringFlow.oddPart (q r + 1)
  let A := fun r => (Finset.range r).prod (fun i => 2 ^ W i) *
      (Finset.range (K - 1 - r)).prod (fun i => 5 ^ n (r + 1 + i))
  have hq0 := cycleRiseBlockRotatedWordA_q0_delta_eq_fourTerm h d hpos hLle
  have hQR_all : ∀ r, r < K → 2 ^ W r + 5 ^ n r * 2 ^ R r * oC r ≤
      2 ^ (W r + RN r) * oN r + 5 ^ n r := by
    intro r hr
    have hdecC := cycleRiseBlockC3TailState_eq_two_pow_mul_odd_sub_one h d r hr
    have hdecN := cycleRiseBlockNextTailState_eq_two_pow_mul_odd_sub_one h d r hr
    rcases hdecC with ⟨oC', hqC, hoC'⟩
    rcases hdecN with ⟨oN', hqN, hoN'⟩
    have hoC'' : StringFlow.oddPart (q r + 1) = oC' :=
      oddPart_eq_of_two_pow_mul_odd (by omega) hqC hoC'
    have hoN'' : StringFlow.oddPart (qN r + 1) = oN' :=
      oddPart_eq_of_two_pow_mul_odd (by omega) hqN hoN'
    have hle := cycleRiseBlockSegmentFivePowMulTailState_le_twoPowMulNext h d r hr (hLle r hr)
    rw [Nat.pow_add]
    dsimp [oN, oC, RN, R, qN, q]
    rw [hoN'', hoC'']
    have hqN_eq : 2 ^ twoValuation (Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN' =
        Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1 := hqN.symm
    have hqC_eq : 2 ^ CycleBridge.cycleRiseBlockTailRank d r * oC' =
        CycleBridge.cycleRiseBlockC3TailState d r + 1 := hqC.symm
    rw [Nat.mul_assoc, Nat.mul_assoc]
    rw [hqN_eq, hqC_eq]
    nlinarith [hle]
  have hP_all : ∀ r, r < K → 2 ^ W r ≤ 2 ^ (W r + RN r) * oN r := by
    intro r hr
    have hdecN := cycleRiseBlockNextTailState_eq_two_pow_mul_odd_sub_one h d r hr
    rcases hdecN with ⟨oN', hqN, hoN'⟩
    have hoN'' : StringFlow.oddPart (qN r + 1) = oN' :=
      oddPart_eq_of_two_pow_mul_odd (by omega) hqN hoN'
    have hge : 1 ≤ qN r + 1 := by omega
    rw [Nat.pow_add]
    dsimp [oN, RN, qN]
    rw [hoN'']
    have hpow : 0 < 2 ^ W r := by positivity
    have hqN_eq : 2 ^ twoValuation (Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1) * oN' =
        Word.wordOrbit (w.take (cycleNextTailDepth d r)) m + 1 := hqN.symm
    rw [Nat.mul_assoc]
    rw [hqN_eq]
    nlinarith [hqN_eq]
  have hS_all : ∀ r, r < K → 5 ^ n r ≤ 5 ^ n r * 2 ^ R r * oC r := by
    intro r hr
    have hdecC := cycleRiseBlockC3TailState_eq_two_pow_mul_odd_sub_one h d r hr
    rcases hdecC with ⟨oC', hqC, hoC'⟩
    have hoC'' : StringFlow.oddPart (q r + 1) = oC' :=
      oddPart_eq_of_two_pow_mul_odd (by omega) hqC hoC'
    have hge : 1 ≤ q r + 1 := by omega
    dsimp [oC, R, q]
    rw [hoC'']
    have hpow : 0 < 5 ^ n r := by positivity
    have hqC_eq : 2 ^ CycleBridge.cycleRiseBlockTailRank d r * oC' =
        CycleBridge.cycleRiseBlockC3TailState d r + 1 := hqC.symm
    rw [Nat.mul_assoc]
    rw [hqC_eq]
    nlinarith [hqC_eq]
  have hbracket : ∀ r, r < K → A r * ((2 ^ (W r + RN r) * oN r - 2 ^ W r) -
        (5 ^ n r * 2 ^ R r * oC r - 5 ^ n r)) =
      A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r) -
        A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r) := by
    intro r hr
    have hsub := nat_sub_sub_eq_add_sub_add (P := 2 ^ (W r + RN r) * oN r)
      (Q := 2 ^ W r) (R := 5 ^ n r * 2 ^ R r * oC r) (S := 5 ^ n r)
      (hP_all r hr) (hS_all r hr) (hQR_all r hr)
    rw [hsub]
    rw [Nat.mul_sub_left_distrib]
  -- 把 hq0 的每一项替换成加法形式
  have hq0' : q 0 * (2 ^ S - 5 ^ P) =
      (Finset.range K).sum (fun r =>
        A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r) -
          A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r)) := by
    rw [hq0]
    apply Finset.sum_congr rfl
    intro r hr
    exact hbracket r (Finset.mem_range.mp hr)
  -- 求和拆开
  have hle_sum : (Finset.range K).sum (fun r => A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r)) ≤
      (Finset.range K).sum (fun r => A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r)) := by
    apply Finset.sum_le_sum
    intro r hr
    exact Nat.mul_le_mul_left (A r) (hQR_all r (Finset.mem_range.mp hr))
  have hsum_split : (Finset.range K).sum (fun r =>
        A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r) -
          A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r)) =
      (Finset.range K).sum (fun r => A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r)) -
        (Finset.range K).sum (fun r => A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r)) := by
    symm
    rw [Nat.sub_eq_iff_eq_add hle_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hge : A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r) ≤
        A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r) :=
      Nat.mul_le_mul_left (A r) (hQR_all r (Finset.mem_range.mp hr))
    omega
  have hq0_raw := hq0
  rw [hq0'] at hq0
  rw [hsum_split] at hq0
  rw [← hq0_raw] at hq0
  have hfinal : (Finset.range K).sum (fun r => A r * (2 ^ (W r + RN r) * oN r + 5 ^ n r)) =
      (Finset.range K).sum (fun r => A r * (2 ^ W r + 5 ^ n r * 2 ^ R r * oC r)) +
        q 0 * (2 ^ S - 5 ^ P) := by
    omega
  simpa [K, sc, W, n, q, qN, RN, R, oN, oC, A] using hfinal

/-- 每个块的 rise 后缀长度不超过整词长度（由分解的循环步长 `hnext`
与块头深度上界直接推出）。四项展开与段分子引理都需要这条 `hLle`。 -/
theorem cycleRiseBlockSuffixLength_le_period
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    (d.suffixWord r).length ≤ w.length := by
  have hnext := d.hnext r hr
  have hpos : 1 ≤ d.headDepth r := d.hhead_pos r hr
  have hc3pos : 1 ≤ (d.c3Word r).length :=
    List.length_pos_iff.mpr (d.hc3_nonempty r hr)
  by_cases hnextr : r + 1 < d.blockCount
  · rw [if_pos hnextr] at hnext
    have hlt : d.headDepth (r + 1) < P := d.hhead_lt (r + 1) hnextr
    rw [d.hperiod]
    omega
  · have hlast : r + 1 = d.blockCount := by omega
    rw [if_neg hnextr] at hnext
    have hmono : d.headDepth 0 ≤ d.headDepth r :=
      cycleRiseBlock_headDepth_mono d r hr
    rw [d.hperiod]
    omega

/-- 用户给的逐块求和恒等式（链层）：中间 C3 态 rank 和 =
`tailRank + 2·c3len − 2`。由逐项求和 + `c3Chain_rank_gain` 组合。 -/
lemma c3Chain_rankSum_eq_tailRank_add_two_mul_length_sub_two
    (ns ts : List Nat)
    (hQ : 0 < ts.length)
    (h : StringFlow.GC.c3ExactMax ns ts)
    (hweights : ∀ t ∈ ts, 3 ≤ t)
    (hhead : twoValuation (StringFlow.GC.chainFirst ns + 1) = 2) :
    ((ns.drop 1).map (fun s => twoValuation (s + 1))).sum =
      twoValuation (StringFlow.GC.chainLast ns + 1) + 2 * ts.length - 2 := by
  have hchain := c3Residuals_sum_eq_weights_sub_two_add_rankSum ns ts hQ h hweights hhead
  have hgain := StringFlow.RealOrbitLocalLemma.c3Chain_rank_gain ns ts hQ h hweights hhead
  have hwsum : (ts.map (fun t => t - 2)).sum + 2 * ts.length = ts.sum := by
    have hconst : (ts.map (fun _ => 2)).sum = 2 * ts.length := by
      rw [List.map_const']
      rw [List.sum_replicate]
      rw [Nat.nsmul_eq_mul]
      rw [Nat.mul_comm]
    rw [← hconst]
    rw [← List.sum_map_add]
    have hmap : ts.map (fun t => (t - 2) + 2) = ts.map (fun t => t) := by
      apply List.map_congr_left
      intro t ht
      have ht3 : 3 ≤ t := hweights t ht
      omega
    rw [hmap]
    simp
  rw [hchain] at hgain
  rw [← hwsum] at hgain
  omega

/-- 块级实例化：`Σ_{块 r 的中间 C3 态} v2(+1) = R_r + 2·c3len_r − 2`。 -/
theorem cycleRiseBlockC3RankSum_eq_tailRank_add_two_mul_length_sub_two
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount) :
    (List.map (fun s => twoValuation (s + 1))
      (List.drop 1 (CycleBridge.c3ChainStates
        (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum =
    CycleBridge.cycleRiseBlockTailRank d r + 2 * (d.c3Word r).length - 2 := by
  let headState := StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m
  let ns := CycleBridge.c3ChainStates headState (d.c3Word r)
  have hQ : 0 < (d.c3Word r).length := List.length_pos_iff.mpr (d.hc3_nonempty r hr)
  have hmax : StringFlow.GC.c3ExactMax ns (d.c3Word r) := by
    dsimp [ns, headState]
    exact CycleBridge.cycleRiseBlockC3ExactMax d r hr
  have hhead : twoValuation (StringFlow.GC.chainFirst ns + 1) = 2 := by
    dsimp [ns]
    rw [CycleBridge.chainFirst_c3ChainStates headState (d.c3Word r) (d.hc3_nonempty r hr)]
    have hrank : CycleBridge.cycleRiseBlockHeadRank d r = 2 :=
      CycleBridge.cycleRiseBlockHeadRank_two d r hr
    dsimp [headState, CycleBridge.cycleRiseBlockHeadRank] at hrank ⊢
    exact hrank
  have hchain := c3Chain_rankSum_eq_tailRank_add_two_mul_length_sub_two
    ns (d.c3Word r) hQ hmax (d.hc3_entries r hr) hhead
  have hlast : StringFlow.GC.chainLast ns = CycleBridge.cycleRiseBlockC3TailState d r := by
    dsimp [ns]
    rw [CycleBridge.chainLast_c3ChainStates headState (d.c3Word r)]
    dsimp [headState]
    exact (CycleBridge.cycleRiseBlockC3TailState_eq_wordOrbit_c3Word d r hr).symm
  rw [hlast] at hchain
  simpa [ns, headState, CycleBridge.cycleRiseBlockTailRank] using hchain

/-- 全局求和（加法形式）：`Σ_r Σ_{块r中间C3态} v2(+1) + 2K =
ΣR + 2·Σc3len`。 -/
theorem cycleRiseBlockC3RankSumSum_add_two_mul_blockCount_eq_tailRankSum_add_two_mul_c3lenSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).sum
        (fun r => (List.map (fun s => twoValuation (s + 1))
          (List.drop 1 (CycleBridge.c3ChainStates
            (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum) +
        2 * d.blockCount =
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) +
        2 * ((Finset.range d.blockCount).sum
          (fun r => (d.c3Word r).length)) := by
  have hper : ∀ r, r < d.blockCount →
      (List.map (fun s => twoValuation (s + 1))
          (List.drop 1 (CycleBridge.c3ChainStates
            (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum + 2 =
        CycleBridge.cycleRiseBlockTailRank d r + 2 * (d.c3Word r).length := by
    intro r hr
    have hblk := cycleRiseBlockC3RankSum_eq_tailRank_add_two_mul_length_sub_two h d r hr
    have hlen : 1 ≤ (d.c3Word r).length := List.length_pos_iff.mpr (d.hc3_nonempty r hr)
    omega
  calc
    (Finset.range d.blockCount).sum
        (fun r => (List.map (fun s => twoValuation (s + 1))
          (List.drop 1 (CycleBridge.c3ChainStates
            (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum) +
        2 * d.blockCount
        = (Finset.range d.blockCount).sum
            (fun r => (List.map (fun s => twoValuation (s + 1))
              (List.drop 1 (CycleBridge.c3ChainStates
                (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m) (d.c3Word r)))).sum + 2) := by
            rw [Finset.sum_add_distrib]
            have hconst : (Finset.range d.blockCount).sum (fun _ => 2) =
                2 * d.blockCount := by
              rw [Finset.sum_const, Finset.card_range]
              rw [Nat.nsmul_eq_mul]
              rw [Nat.mul_comm]
            rw [hconst]
    _ = (Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailRank d r + 2 * (d.c3Word r).length) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hper r (Finset.mem_range.mp hr)
    _ = (Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailRank d r) +
          2 * ((Finset.range d.blockCount).sum (fun r => (d.c3Word r).length)) := by
            rw [Finset.sum_add_distrib]
            have hA : (Finset.range d.blockCount).sum
                (fun r => 2 * (d.c3Word r).length) =
                2 * ((Finset.range d.blockCount).sum (fun r => (d.c3Word r).length)) := by
              rw [← Finset.mul_sum]
            rw [hA]

/-- 整圈 period-closure 恒等式（Finset 版）：
`Σ charge + Σ tailRank = 2·H2 + 2·K`。 -/
theorem cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount_finset
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockCharge d r) +
        (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) =
      2 * CycleBridge.cycleRiseBlockH2Sum d + 2 * d.blockCount := by
  have hlist := cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount h d
  have hFC : (Finset.range d.blockCount).sum
        (fun r => CycleBridge.cycleRiseBlockCharge d r) =
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockCharge d r)).sum := by
    rw [← List.sum_toFinset (fun r => CycleBridge.cycleRiseBlockCharge d r) List.nodup_range]
    rw [List.toFinset_range]
  have hFR : (Finset.range d.blockCount).sum
        (fun r => CycleBridge.cycleRiseBlockTailRank d r) =
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum := by
    rw [← List.sum_toFinset (fun r => CycleBridge.cycleRiseBlockTailRank d r) List.nodup_range]
    rw [List.toFinset_range]
  rw [hFC, hFR]
  exact hlist

/-- 对齐收口（加法形式）：`2H2 = ΣF + ΣR − 2K`，
把游程语言（`2H2`）与块尾 rank 和 `ΣR` 精确接上。 -/
theorem cycleRiseBlockTwo_mul_H2Sum_eq_chargeSum_add_tailRankSum_sub_two_mul_blockCount
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    2 * CycleBridge.cycleRiseBlockH2Sum d =
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockCharge d r) +
        (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) -
        2 * d.blockCount := by
  have hbal := cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount_finset h d
  omega

/-- 整圈求和版目标改写：残差预算等价于
`2·H2 ≥ ΣF + 2Σb + 11K`。 -/
theorem cycleRiseBlockResidualBudget_iff_H2Budget
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r) ≥
        (Finset.range d.blockCount).sum (fun r => (d.c3Word r).sum) +
          2 * ((Finset.range d.blockCount).sum
            (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          11 * d.blockCount ↔
    2 * CycleBridge.cycleRiseBlockH2Sum d ≥
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockCharge d r) +
        2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
        11 * d.blockCount := by
  have hbal := cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount_finset h d
  have hres := cycleRiseBlockResidualBudget_iff_tailRankBudget h d
  constructor
  · intro hresBudget
    have hrank : 2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          13 * d.blockCount ≤
        (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) :=
      hres.mpr hresBudget
    omega
  · intro hh2
    have hrank : 2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
          13 * d.blockCount ≤
        (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailRank d r) := by omega
    exact hres.mp hrank

/-- 游程求和版连接：块分解的 `2·H2` 等于整词 t=2 游程 rank 差和
`t2RunRankSum c p`（`hcycle` 给出具体 `c p`）。 -/
theorem cycleRiseBlockH2Sum_eq_t2RunRankSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 1 ≤ d.blockCount) :
    ∃ c p : Nat, 2 * CycleBridge.cycleRiseBlockH2Sum d = Amiya.t2RunRankSum c p := by
  rcases h.hcycle with ⟨cp, hw, hm, _⟩
  rcases cp with ⟨c, p⟩
  refine ⟨c, p, ?_⟩
  rw [cycleRiseBlockH2Sum_eq_riseCountTwo d hpos]
  rw [hw]
  rw [Amiya.t2RunRankSum_eq_two_mul_riseCountTwo c p]

/-- 游程求和版义务：`2H2 ≥ ΣF + 2Σb + 11K` 转成具体 `c p` 的
`t2RunRankSum c p ≥ ΣF + 2Σb + 11K`。 -/
theorem cycleRiseBlockT2RunRankSumBudget_of_H2Budget
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 1 ≤ d.blockCount)
    (hgoal : 2 * CycleBridge.cycleRiseBlockH2Sum d ≥
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockCharge d r) +
        2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
        11 * d.blockCount) :
    ∃ c p : Nat, Amiya.t2RunRankSum c p ≥
      (Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockCharge d r) +
        2 * ((Finset.range d.blockCount).sum
          (fun r => CycleBridge.cycleRiseBlockTailDepth d r)) +
        11 * d.blockCount := by
  rcases cycleRiseBlockH2Sum_eq_t2RunRankSum h d hpos with ⟨c, p, hconn⟩
  refine ⟨c, p, ?_⟩
  rwa [hconn] at hgoal

/-- `5^P < 2^S` 的整数推论：`S ≥ 2P + 1`。
因为 `5^P > 4^P = 2^{2P}`，所以 `2^S > 2^{2P}`。 -/
theorem cycleRiseBlockS_ge_two_mul_P_add_one
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (hSgt : 5 ^ P < 2 ^ S) :
    S ≥ 2 * P + 1 := by
  have hPpos : 0 < P := by
    have hP2 : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    omega
  have hPne0 : P ≠ 0 := Nat.ne_of_gt hPpos
  have h45 : 4 ^ P < 5 ^ P :=
    pow_lt_pow_left₀ (by norm_num : 4 < 5) (by norm_num : 0 ≤ 4) hPne0
  have h42 : 4 ^ P = 2 ^ (2 * P) := by
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← Nat.pow_mul]
  have h2S : 2 ^ (2 * P) < 2 ^ S := by
    rw [← h42]
    exact lt_trans h45 hSgt
  have hlt : 2 * P < S :=
    (pow_lt_pow_iff_right₀ (by norm_num : 1 < 2)).mp h2S
  omega

/-- `wordWeight l = l.length + Σ(t−1)`（任意词，逐项 `t = (t−1)+1`）。 -/
lemma wordWeight_eq_length_add_map_sub_one (l : List Nat)
    (hge1 : ∀ t ∈ l, 1 ≤ t) :
    StringFlow.wordWeight l = l.length + (l.map (fun t => t - 1)).sum := by
  rw [StringFlow.TD0.wordWeight_eq_sum l]
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : a = (a - 1) + 1 := by
        have ha1 : 1 ≤ a := hge1 a (by simp)
        omega
      rw [List.sum_cons, List.length_cons, List.map_cons, List.sum_cons]
      rw [ha, ih (by
        intro t ht
        exact hge1 t (by simp [ht]))]
      omega

/-- 整圈权重恒等式（正确版）：
`S = P + H2Sum + Σ_{C3}(t−1)`。
每步权重 `t = 1 + (t−1)`：t=1 贡献 0，t=2 贡献 1（即 H2），
C3 步贡献 `t−1`。 -/
theorem cycleRiseBlockS_eq_P_add_H2_add_c3WeightSubOne
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    S = P + CycleBridge.cycleRiseBlockH2Sum d +
      (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).map (fun t => t - 1)).sum) := by
  let K := d.blockCount
  have hSegWeight : (Finset.range K).sum
        (fun r => StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) = S := by
    simpa [K] using cycleRiseBlockSegmentWeightSum d
  have hSuffixWeight : (Finset.range K).sum
        (fun r => StringFlow.wordWeight (d.suffixWord r)) =
      (Finset.range K).sum (fun r => (d.suffixWord r).length) +
        CycleBridge.cycleRiseBlockH2Sum d := by
    have hper : ∀ r, r < K →
        StringFlow.wordWeight (d.suffixWord r) =
          (d.suffixWord r).length + CycleBridge.riseCountTwo (d.suffixWord r) := by
      intro r hr
      exact CycleBridge.wordWeight_eq_length_add_riseCountTwo
        (d.suffixWord r) (d.hsuffix_one_two r hr)
    calc
      (Finset.range K).sum (fun r => StringFlow.wordWeight (d.suffixWord r))
          = (Finset.range K).sum
              (fun r => (d.suffixWord r).length + CycleBridge.riseCountTwo (d.suffixWord r)) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact hper r (Finset.mem_range.mp hr)
      _ = (Finset.range K).sum (fun r => (d.suffixWord r).length) +
            CycleBridge.cycleRiseBlockH2Sum d := by
              rw [Finset.sum_add_distrib]
              have hH2 : (Finset.range K).sum
                  (fun r => CycleBridge.riseCountTwo (d.suffixWord r)) =
                  CycleBridge.cycleRiseBlockH2Sum d := by
                dsimp [CycleBridge.cycleRiseBlockH2Sum]
                rw [← List.sum_toFinset (fun r => CycleBridge.riseCountTwo (d.suffixWord r)) List.nodup_range]
                rw [List.toFinset_range]
              rw [hH2]
  have hC3Cyclic : (Finset.range K).sum
        (fun r => StringFlow.wordWeight (cycleNextC3Word d r)) =
      (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) := by
    calc
      (Finset.range K).sum (fun r => StringFlow.wordWeight (cycleNextC3Word d r))
          = (Finset.range K).sum
              (fun r => if r + 1 < K then
                StringFlow.wordWeight (d.c3Word (r + 1)) else StringFlow.wordWeight (d.c3Word 0)) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact cycleNextC3Word_weight_split d K r rfl
      _ = (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) :=
              finset_sum_cyclic_shift K (fun r => StringFlow.wordWeight (d.c3Word r))
  have hPeriod : (Finset.range K).sum
        (fun r => (d.suffixWord r).length + (d.c3Word r).length) = P := by
    have hlist := CycleBridge.cycleRiseBlockPeriodSum_list d hpos
    have hF : (Finset.range K).sum
        (fun r => (d.c3Word r).length + (d.suffixWord r).length) = P := by
      calc
        (Finset.range K).sum
            (fun r => (d.c3Word r).length + (d.suffixWord r).length)
            = ((List.range K).map
                (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
                rw [← List.toFinset_range]
                rw [List.sum_toFinset
                  (fun r => (d.c3Word r).length + (d.suffixWord r).length) List.nodup_range]
        _ = P := by simpa [K] using hlist.symm
    simpa [Nat.add_comm] using hF
  have hC3sum : (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) =
      (Finset.range K).sum (fun r => (d.c3Word r).length) +
        (Finset.range K).sum (fun r => ((d.c3Word r).map (fun t => t - 1)).sum) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact wordWeight_eq_length_add_map_sub_one (d.c3Word r) (by
      intro t ht
      have hge := d.hc3_entries r (Finset.mem_range.mp hr) t ht
      omega)
  calc
    S = (Finset.range K).sum
            (fun r => StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r)) := hSegWeight.symm
    _ = (Finset.range K).sum (fun r => StringFlow.wordWeight (d.suffixWord r) +
          StringFlow.wordWeight (cycleNextC3Word d r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact StringFlow.Word.wordWeight_append (d.suffixWord r) (cycleNextC3Word d r)
    _ = (Finset.range K).sum (fun r => StringFlow.wordWeight (d.suffixWord r)) +
        (Finset.range K).sum (fun r => StringFlow.wordWeight (cycleNextC3Word d r)) := by
            rw [Finset.sum_add_distrib]
    _ = (Finset.range K).sum (fun r => (d.suffixWord r).length) +
        CycleBridge.cycleRiseBlockH2Sum d +
        (Finset.range K).sum (fun r => StringFlow.wordWeight (d.c3Word r)) := by
            rw [hSuffixWeight, hC3Cyclic]
    _ = (Finset.range K).sum
            (fun r => (d.suffixWord r).length + (d.c3Word r).length) +
          CycleBridge.cycleRiseBlockH2Sum d +
          (Finset.range K).sum (fun r => ((d.c3Word r).map (fun t => t - 1)).sum) := by
            simp [hC3sum, Finset.sum_add_distrib,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = P + CycleBridge.cycleRiseBlockH2Sum d +
          (Finset.range K).sum (fun r => ((d.c3Word r).map (fun t => t - 1)).sum) := by
            rw [hPeriod]

/-- 整词规模：用权重恒等式把 `2^S` 展开成
`2^{P + H2Sum + Σ_{C3}(t−1)}`。 -/
theorem cycleRiseBlock_two_pow_S_eq_two_pow_P_add_H2_add_c3WeightSubOne
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    2 ^ S = 2 ^ (P + CycleBridge.cycleRiseBlockH2Sum d +
      (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).map (fun t => t - 1)).sum)) := by
  apply congrArg (fun s : Nat => 2 ^ s)
  exact cycleRiseBlockS_eq_P_add_H2_add_c3WeightSubOne d hpos

/-- `5^P < 2^S` 的整词规模形式。 -/
theorem cycleRiseBlock_five_pow_lt_two_pow_wholeWordScale
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) (hSgt : 5 ^ P < 2 ^ S) :
5 ^ P < 2 ^ (P + CycleBridge.cycleRiseBlockH2Sum d +
      (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).map (fun t => t - 1)).sum)) := by
  rwa [cycleRiseBlock_two_pow_S_eq_two_pow_P_add_H2_add_c3WeightSubOne d hpos] at hSgt



/-- 游程对齐桥：块内 `suffixWord r` 前缀的局部 `riseRun` rank
等于全局深度 `(TailDepth r + j) % P` 处的 `wordOrbit` rank。 -/
theorem cycleRiseBlockT2RunRank_eq_wordOrbit
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (j : Nat) (hj : j ≤ (d.suffixWord r).length) :
    twoValuation (CycleBridge.riseRun
        (CycleBridge.cycleRiseBlockC3TailState d r)
        ((d.suffixWord r).take j) + 1) =
      twoValuation (StringFlow.Word.wordOrbit
        (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + j) % P)) m + 1) := by
  rw [CycleBridge.riseRun_eq_wordOrbit]
  rw [CycleBridge.suffixWord_prefix_eq_word_prefix_mod d r hr j hj]


/-- 块级游程 rank 差和（全局深度版）：
`Σ_{runs in suffix_r} (R(全局 start) − R(全局 end)) = 2·N_r`。 -/
theorem cycleRiseBlockT2RunGlobalRankSum_eq_two_mul_riseCountTwo
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    ((maxT2Runs (d.suffixWord r)).map (fun run =>
      twoValuation (StringFlow.Word.wordOrbit
        (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P)) m + 1) -
      twoValuation (StringFlow.Word.wordOrbit
        (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start + run.length) % P)) m + 1))).sum =
      2 * CycleBridge.riseCountTwo (d.suffixWord r) := by
  have hblock := block_t2_runs_rank_sum d r hr
  rw [← hblock]
  apply congrArg List.sum
  apply List.map_congr_left
  intro run hmem
  have hbnd := maxT2RunsFrom_bounds (d.suffixWord r) 0 run hmem
  have hstart_le : run.start ≤ (d.suffixWord r).length := by omega
  have hend_le : run.start + run.length ≤ (d.suffixWord r).length := by simpa using hbnd
  have h1 := cycleRiseBlockT2RunRank_eq_wordOrbit d r hr run.start hstart_le
  have h2 := cycleRiseBlockT2RunRank_eq_wordOrbit d r hr (run.start + run.length) hend_le
  rw [h1, h2]
  simp [Nat.add_assoc]

/-- 游程求和版全局形式：
`2·H2Sum = Σ_r Σ_{runs in suffix_r} (R(全局 start) − R(全局 end))`。 -/
theorem cycleRiseBlockT2RunGlobalRankSumSum_eq_two_mul_H2Sum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    2 * CycleBridge.cycleRiseBlockH2Sum d =
      (Finset.range d.blockCount).sum (fun r =>
        ((maxT2Runs (d.suffixWord r)).map (fun run =>
          twoValuation (StringFlow.Word.wordOrbit
            (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P)) m + 1) -
          twoValuation (StringFlow.Word.wordOrbit
            (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start + run.length) % P)) m + 1))).sum) := by
  have hH2 : CycleBridge.cycleRiseBlockH2Sum d =
      (Finset.range d.blockCount).sum
        (fun r => CycleBridge.riseCountTwo (d.suffixWord r)) := by
    dsimp [CycleBridge.cycleRiseBlockH2Sum]
    rw [← List.sum_toFinset (fun r => CycleBridge.riseCountTwo (d.suffixWord r)) List.nodup_range]
    rw [List.toFinset_range]
  calc
    2 * CycleBridge.cycleRiseBlockH2Sum d
        = 2 * ((Finset.range d.blockCount).sum
            (fun r => CycleBridge.riseCountTwo (d.suffixWord r))) := by rw [hH2]
    _ = (Finset.range d.blockCount).sum
            (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r)) := by
            rw [Finset.mul_sum]
    _ = (Finset.range d.blockCount).sum (fun r =>
            ((maxT2Runs (d.suffixWord r)).map (fun run =>
              twoValuation (StringFlow.Word.wordOrbit
                (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P)) m + 1) -
              twoValuation (StringFlow.Word.wordOrbit
                (w.take ((CycleBridge.cycleRiseBlockTailDepth d r + run.start + run.length) % P)) m + 1))).sum) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact (cycleRiseBlockT2RunGlobalRankSum_eq_two_mul_riseCountTwo
              d r (Finset.mem_range.mp hr)).symm

/-- 非回绕块游程起点深度的 `%P` 消除：
`b_r + run.start < P`，故 `(b_r + run.start) % P = b_r + run.start`。 -/
theorem cycleRiseBlockT2RunStart_mod_eq_add_nonwrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hnext : r + 1 < d.blockCount) :
    ((maxT2Runs (d.suffixWord r)).map (fun run =>
      (CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P)).sum =
    ((maxT2Runs (d.suffixWord r)).map (fun run =>
      CycleBridge.cycleRiseBlockTailDepth d r + run.start)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro run hmem
  have hbnd := maxT2RunsFrom_bounds (d.suffixWord r) 0 run hmem
  have hlen_pos : 0 < run.length := maxT2RunsFrom_length_pos (d.suffixWord r) 0 run hmem
  have hstart_lt : run.start < (d.suffixWord r).length := by omega
  have hnext_eq : CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
      d.headDepth (r + 1) := by
    dsimp [CycleBridge.cycleRiseBlockTailDepth]
    have hh := d.hnext r hr
    rw [if_pos hnext] at hh
    omega
  have hltP : CycleBridge.cycleRiseBlockTailDepth d r + run.start < P := by
    have hhdlt : d.headDepth (r + 1) < P := d.hhead_lt (r + 1) hnext
    omega
  rw [Nat.mod_eq_of_lt hltP]

/-- 回绕块游程起点深度的 `%P` 消除：`b + run.start` 可能 ≥ `P`，
按 `b+start < 2P` 分两段（`b+start−P` 或 `b+start`）。 -/
theorem cycleRiseBlockT2RunStart_mod_eq_add_wrap
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hlast : r + 1 = d.blockCount)
    (run : T2Run) (hmem : run ∈ maxT2Runs (d.suffixWord r)) :
    (CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P =
      if P ≤ CycleBridge.cycleRiseBlockTailDepth d r + run.start then
        CycleBridge.cycleRiseBlockTailDepth d r + run.start - P
      else
        CycleBridge.cycleRiseBlockTailDepth d r + run.start := by
  by_cases hgeP : P ≤ CycleBridge.cycleRiseBlockTailDepth d r + run.start
  · simp [hgeP]
    have hbnd := maxT2RunsFrom_bounds (d.suffixWord r) 0 run hmem
    have hlen_pos : 0 < run.length := maxT2RunsFrom_length_pos (d.suffixWord r) 0 run hmem
    have hstart_le : run.start ≤ (d.suffixWord r).length := by omega
    have hnext_eq : CycleBridge.cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
        d.headDepth 0 + P := by
      dsimp [CycleBridge.cycleRiseBlockTailDepth]
      have hh := d.hnext r hr
      rw [if_neg (by omega : ¬ r + 1 < d.blockCount)] at hh
      omega
    have hpos : 0 < d.blockCount := by omega
    have hhd0 : d.headDepth 0 < P := d.hhead_lt 0 hpos
    have hlt2P : CycleBridge.cycleRiseBlockTailDepth d r + run.start < 2 * P := by omega
    have hmod : (CycleBridge.cycleRiseBlockTailDepth d r + run.start) % P =
        (CycleBridge.cycleRiseBlockTailDepth d r + run.start - P) % P :=
      Nat.mod_eq_sub_mod hgeP
    have hsmall : CycleBridge.cycleRiseBlockTailDepth d r + run.start - P < P := by omega
    rw [hmod]
    rw [Nat.mod_eq_of_lt hsmall]
  · simp [hgeP]
    have hltP : CycleBridge.cycleRiseBlockTailDepth d r + run.start < P := by omega
    rw [Nat.mod_eq_of_lt hltP]

/-- 正向侧第一步：`2^S > 5^P` 的精确加法形式，整词分子严格为正。
由 `cycleQb8Input_wordA_equation` 得 `wordA w = m·(2^S−5^P)`，
配合 `m > 0` 与 `2^S−5^P > 0` 直接给出 `0 < wordA w`。 -/
lemma cycleRiseBlockWordA_expand_pos
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (_d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hSgt : 5 ^ P < 2 ^ S) :
    0 < StringFlow.Word.wordA w := by
  rw [cycleQb8Input_wordA_equation h]
  have hdelta_pos : 0 < 2 ^ S - 5 ^ P := by omega
  have hm_pos : 0 < m := by
    by_contra hnot
    have h0 : m = 0 := by omega
    have hodd0 : S6Audit.IsOdd 0 := by simpa [h0] using h.hm_odd
    change 0 % 2 = 1 at hodd0
    norm_num at hodd0
  exact Nat.mul_pos hm_pos hdelta_pos


/-- 单个循环块段的权重不超过总权重 `S`。 -/
theorem cycleRiseBlockSegmentWeight_le_S
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) ≤ S := by
  have hsum := cycleRiseBlockSegmentWeightSum d
  have hle : StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) ≤
      (Finset.range d.blockCount).sum
        (fun i => StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i)) :=
    Finset.single_le_sum (s := Finset.range d.blockCount)
      (f := fun i => StringFlow.wordWeight (d.suffixWord i ++ cycleNextC3Word d i))
      (a := r)
      (by intro b hb; exact Nat.zero_le _)
      (by simp [Finset.mem_range, hr])
  exact le_trans hle (le_of_eq hsum)

/-- 单个循环块段的权重至少为 1（段非空且每项 ≥ 1）。 -/
theorem cycleRiseBlockSegmentWeight_pos
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    1 ≤ StringFlow.wordWeight (d.suffixWord r ++ cycleNextC3Word d r) := by
  let sc := d.suffixWord r ++ cycleNextC3Word d r
  have hc3ne : cycleNextC3Word d r ≠ [] := by
    by_cases hnext : r + 1 < d.blockCount
    · simpa [cycleNextC3Word, hnext] using d.hc3_nonempty (r + 1) hnext
    · have hpos0 : 0 < d.blockCount := by omega
      simpa [cycleNextC3Word, hnext] using d.hc3_nonempty 0 hpos0
  have hne : sc ≠ [] := by
    intro hsc
    have hlen0 : sc.length = 0 := by rw [hsc]; simp
    have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
    have hlen_pos : 0 < sc.length := by
      dsimp [sc]
      rw [List.length_append]
      omega
    omega
  have hpos_entries : ∀ t ∈ sc, 1 ≤ t := by
    intro t ht
    rcases List.mem_append.mp ht with hsuf | hc3
    · rcases d.hsuffix_one_two r hr t hsuf with h1 | h2 <;> omega
    · by_cases hnext : r + 1 < d.blockCount
      · have hmem : t ∈ d.c3Word (r + 1) := by simpa [cycleNextC3Word, hnext] using hc3
        have hge3 : 3 ≤ t := d.hc3_entries (r + 1) hnext t hmem
        omega
      · have hpos0 : 0 < d.blockCount := by omega
        have hmem : t ∈ d.c3Word 0 := by simpa [cycleNextC3Word, hnext] using hc3
        have hge3 : 3 ≤ t := d.hc3_entries 0 hpos0 t hmem
        omega
  have hge := StringFlow.RealOrbitLocalLemma.wordWeight_ge_length_of_ge_one sc hpos_entries
  have hlen1 : 1 ≤ sc.length := by
    dsimp [sc]
    have hc3pos : 0 < (cycleNextC3Word d r).length := List.length_pos_iff.mpr hc3ne
    rw [List.length_append]
    omega
  simpa [sc] using (le_trans hlen1 hge)

/-- 逐块系数提升：`2^{T_r+W_r} ∣ c_r·(s_r(S) + 5·q_r)`。
由段误差精确秩（模 `2^{W_r}`）与 `c_r` 的 2-因子组合。 -/
theorem cycleRiseBlockSegmentCoeff_mul_error_dvd
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length)
    (r : Nat) (hr : r < d.blockCount) :
    let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
    let W := fun r => StringFlow.wordWeight (sc r)
    2 ^ ((Finset.range r).sum W + W r) ∣
      ((Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (sc (r + i)).length)) *
      (prefixWeightSumList (sc r) S + 5 * CycleBridge.cycleRiseBlockC3TailState d r) := by
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let T := fun r => (Finset.range r).sum W
  let s := fun r => prefixWeightSumList (sc r) S
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let e := fun r => prefixWeightSumList (sc r) (W r + 1) + 5 * q r
  have hEr := cycleRiseBlockSegmentErrorRank_eq h d r hr (hLle r hr)
  have hWpos : 1 ≤ W r := cycleRiseBlockSegmentWeight_pos d r hr
  have hWleS : W r ≤ S := cycleRiseBlockSegmentWeight_le_S d r hr
  have hmodS := prefixWeightSumList_mod_lower (sc r) (W r) S hWpos hWleS
  have hmodW1 := prefixWeightSumList_mod_lower (sc r) (W r) (W r + 1) hWpos (by omega)
  have he_pos : 0 < e r := by
    dsimp [e]
    have hqpos : 0 < 5 * q r := by
      have hq : 0 < q r := cycleRiseBlockC3TailState_pos h d r hr
      nlinarith
    positivity
  have hdvd_e : 2 ^ W r ∣ e r := by
    have hge : W r ≤ twoValuation (e r) := by
      rw [hEr]
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (e r) (W r) he_pos).mp hge
  have hdvd_sW : 2 ^ W r ∣ prefixWeightSumList (sc r) (W r) + 5 * q r := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hcong : (prefixWeightSumList (sc r) (W r) + 5 * q r) % 2 ^ W r =
        (e r) % 2 ^ W r := by
      dsimp [e]
      exact (Nat.ModEq.add hmodW1 (Nat.ModEq.refl (5 * q r))).symm
    rw [hcong]
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd_e
    exact hdvd_e
  have hdvd_sS : 2 ^ W r ∣ s r + 5 * q r := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hcong : (s r + 5 * q r) % 2 ^ W r =
        (prefixWeightSumList (sc r) (W r) + 5 * q r) % 2 ^ W r := by
      dsimp [s]
      exact Nat.ModEq.add hmodS (Nat.ModEq.refl (5 * q r))
    rw [hcong]
    exact (Nat.dvd_iff_mod_eq_zero.mp hdvd_sW)
  have hprod2 : (Finset.range r).prod (fun i => 2 ^ W i) = 2 ^ T r := by
    dsimp [T]
    rw [Finset.prod_pow_eq_pow_sum]
  have hodd5 : ((Finset.range (d.blockCount - r)).prod
      (fun i => 5 ^ (sc (r + i)).length)) % 2 = 1 := by
    apply Finset.prod_odd_mod_two
    intro i hi
    exact StringFlow.Lte.five_pow_odd (sc (r + i)).length
  have hc_dvd : 2 ^ T r ∣
      (Finset.range r).prod (fun i => 2 ^ W i) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (sc (r + i)).length) := by
    refine ⟨(Finset.range (d.blockCount - r)).prod
      (fun i => 5 ^ (sc (r + i)).length), ?_⟩
    rw [hprod2]
  have hmul := Nat.mul_dvd_mul hc_dvd hdvd_sS
  have hpow : 2 ^ T r * 2 ^ W r = 2 ^ (T r + W r) := by
    rw [Nat.pow_add]
  rw [hpow] at hmul
  simpa [sc, W, T, s, q] using hmul

/-- 绕圈合并的 q-替换：模 `2^{W_0}` 下，`Δ·E_0` 与
`5·Σ_r c_r·q_r` 同余。由 `prefixWeightSum_wrapMerge` 与逐块系数提升
（`cycleRiseBlockSegmentCoeff_mul_error_dvd`）接线。 -/
theorem prefixWeightSum_wrapMerge_qSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount)
    (hLle : ∀ r : Nat, r < d.blockCount → (d.suffixWord r).length ≤ w.length)
    (h5le : 5 ^ P ≤ 2 ^ S) :
    (2 ^ S - 5 ^ P) * prefixWeightSumList
        (CycleBridge.cyclicSegmentAt w
          (CycleBridge.cycleRiseBlockTailDepth d 0)) S ≡
      5 * (Finset.range d.blockCount).sum (fun r =>
        (Finset.range r).prod
          (fun i => 2 ^ StringFlow.wordWeight
            (d.suffixWord i ++ cycleNextC3Word d i)) *
        (Finset.range (d.blockCount - r)).prod
          (fun i => 5 ^ (d.suffixWord (r + i) ++
            cycleNextC3Word d (r + i)).length) *
        CycleBridge.cycleRiseBlockC3TailState d r)
      [MOD 2 ^ StringFlow.wordWeight
        (d.suffixWord 0 ++ cycleNextC3Word d 0)] := by
  let sc := fun r => d.suffixWord r ++ cycleNextC3Word d r
  let W := fun r => StringFlow.wordWeight (sc r)
  let T := fun r => (Finset.range r).sum W
  let c := fun r =>
    (Finset.range r).prod (fun i => 2 ^ W i) *
    (Finset.range (d.blockCount - r)).prod
      (fun i => 5 ^ (sc (r + i)).length)
  let s := fun r => prefixWeightSumList (sc r) S
  let q := fun r => CycleBridge.cycleRiseBlockC3TailState d r
  let E0 := prefixWeightSumList
    (CycleBridge.cyclicSegmentAt w (CycleBridge.cycleRiseBlockTailDepth d 0)) S
  have hW0pos : 1 ≤ W 0 := cycleRiseBlockSegmentWeight_pos d 0 hpos
  have hW0leS : W 0 ≤ S := cycleRiseBlockSegmentWeight_le_S d 0 hpos
  have hwm := prefixWeightSum_wrapMerge h d hpos hLle h5le (W 0) hW0pos hW0leS
  have hper : ∀ r, r < d.blockCount →
      c r * (s r + 5 * q r) % 2 ^ W 0 = 0 := by
    intro r hr
    have hdvd := cycleRiseBlockSegmentCoeff_mul_error_dvd h d hLle r hr
    have hsum : (Finset.range (r + 1)).sum W = (Finset.range r).sum W + W r := by
      rw [Finset.sum_range_succ]
    have hge : W 0 ≤ (Finset.range r).sum W + W r := by
      rw [← hsum]
      exact Finset.single_le_sum (s := Finset.range (r + 1)) (f := W) (a := 0)
        (by intro b hb; exact Nat.zero_le _)
        (by simp [Finset.mem_range])
    have hpowdvd : 2 ^ W 0 ∣ 2 ^ ((Finset.range r).sum W + W r) :=
      ⟨2 ^ (((Finset.range r).sum W + W r) - W 0), by
        rw [← Nat.pow_add]
        congr 1
        omega⟩
    have hdvd0 : 2 ^ W 0 ∣ c r * (s r + 5 * q r) :=
      Nat.dvd_trans hpowdvd hdvd
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd0
  have hsum0 : (Finset.range d.blockCount).sum
      (fun r => c r * (s r + 5 * q r)) % 2 ^ W 0 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero]
    exact Finset.dvd_sum (by
      intro r hr
      exact (Nat.dvd_iff_mod_eq_zero.mpr (hper r (Finset.mem_range.mp hr))))
  have hsum0' : (Finset.range d.blockCount).sum (fun r => c r * s r) +
      5 * (Finset.range d.blockCount).sum (fun r => c r * q r) ≡
      0 [MOD 2 ^ W 0] := by
    rw [Nat.ModEq]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    have hcong : (Finset.range d.blockCount).sum
          (fun r => c r * s r + 5 * (c r * q r)) =
        (Finset.range d.blockCount).sum (fun r => c r * (s r + 5 * q r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hcong]
    exact hsum0
  have hsum0'' : 0 ≡
      5 * (Finset.range d.blockCount).sum (fun r => c r * q r) +
        (Finset.range d.blockCount).sum (fun r => c r * s r) [MOD 2 ^ W 0] := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum0'.symm
  have hA_plus : (2 ^ S - 5 ^ P) * E0 +
        (Finset.range d.blockCount).sum (fun r => c r * s r) ≡
      5 * (Finset.range d.blockCount).sum (fun r => c r * q r) +
        (Finset.range d.blockCount).sum (fun r => c r * s r)
      [MOD 2 ^ W 0] :=
    hwm.trans hsum0''
  have hAC : (2 ^ S - 5 ^ P) * E0 ≡
      5 * (Finset.range d.blockCount).sum (fun r => c r * q r)
      [MOD 2 ^ W 0] := by
    exact Nat.ModEq.add_right_cancel
      (Nat.ModEq.refl ((Finset.range d.blockCount).sum (fun r => c r * s r)))
      hA_plus
  simpa [sc, W, T, c, s, q, E0] using hAC

/-- 消除膨胀后的全块低于预算压制定理：
由局部失效窗口 `failureWindowExistence` 与判定窗口上界 `decisiveWindowValuationBoundCorrected`
直接导出 `cycleRiseBlockAllBelowBudgetCrush`，彻底避免全局量级膨胀与伪 `omega` 运算。 -/
theorem cycleRiseBlockAllBelowBudgetCrush_of_failure_window
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    cycleRiseBlockAllBelowBudgetCrush := by
  intro m S P w rise c3 h _d _hbelow
  have hcyc := CycleBridge.cycleQb8Input_imp_orbit_cycle h
  have hno := CycleBridge.no_cycle_of_window_bound_of_failureWindowExistence hwin hfw
  exact (hno hcyc).elim

/-- 前向代数性质：在全部块均低于预算的前提下，由局部窗口排斥导出 `2^S ≤ 5^P`。 -/
theorem cycleRiseBlockAllBelowBudgetCrush_forward_of_failure_window
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hbelow : Amiya.cycleRiseBlockAllBelowBudget d) :
    2 ^ S ≤ 5 ^ P :=
  cycleRiseBlockAllBelowBudgetCrush_of_failure_window hfw hwin h d hbelow

/-- 形式化证明全块低于预算全局压制：由局部失效窗口与判定窗口上界导出尺度压制 `2^S ≤ 5^P`。 -/
theorem cycleRiseBlockAllBelowBudgetCrush_proved
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    cycleRiseBlockAllBelowBudgetCrush :=
  cycleRiseBlockAllBelowBudgetCrush_of_failure_window hfw hwin

/-- 形式化证明存在满足预算下界的上升块。 -/
theorem hfailBudgetLowerBound_proved
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    hfailBudgetLowerBound :=
  hfailBudgetLowerBound_of_crush (cycleRiseBlockAllBelowBudgetCrush_proved hfw hwin)

/-- 非周期性前提下的全块低于预算压制。 -/
theorem cycleRiseBlockAllBelowBudgetCrush_of_no_cycle
    (hno : ¬ OrbitCycle 7) :
    cycleRiseBlockAllBelowBudgetCrush := by
  intro m S P w rise c3 h _d _hbelow
  exact (hno (CycleBridge.cycleQb8Input_imp_orbit_cycle h)).elim

/-- 非周期性前提下的预算下界存在性。 -/
theorem hfailBudgetLowerBound_of_no_cycle
    (hno : ¬ OrbitCycle 7) :
    hfailBudgetLowerBound :=
  hfailBudgetLowerBound_of_crush (cycleRiseBlockAllBelowBudgetCrush_of_no_cycle hno)

end Closure

end StringFlow


