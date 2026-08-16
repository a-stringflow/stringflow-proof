import RunDecomposition
import C4C8Tail

set_option maxHeartbeats 800000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace StringFlow.CycleBridge

open StringFlow

/-- The weight of a word equals the sum of the weights of the segments
`[hd r, hd (r+1))` that partition the cyclic word. -/
theorem wordWeight_sum_of_segments
    (w : List Nat) (K : Nat) (hd : Nat → Nat) (seg : Nat → List Nat)
    (hKpos : 0 < K)
    (hseg : ∀ r, r + 1 < K → seg r = (w.take (hd (r + 1))).drop (hd r))
    (hseg_last : seg (K - 1) = (w.drop (hd (K - 1))) ++ (w.take (hd 0)))
    (hlen : ∀ r, r + 1 < K → hd (r + 1) = hd r + (seg r).length)
    (hlen_last : hd 0 + w.length = hd (K - 1) + (seg (K - 1)).length) :
    ((List.range K).map (fun r => StringFlow.wordWeight (seg r))).sum =
      StringFlow.wordWeight w := by
  have hprefix : ∀ n, n ≤ K - 1 →
      StringFlow.wordWeight (w.take (hd n)) =
        StringFlow.wordWeight (w.take (hd 0)) +
          ((List.range n).map (fun r => StringFlow.wordWeight (seg r))).sum := by
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
        have hww : StringFlow.wordWeight (w.take (hd (n + 1))) =
            StringFlow.wordWeight (w.take (hd n)) + StringFlow.wordWeight (seg n) := by
          rw [htake, hseg']
          rw [StringFlow.Word.wordWeight_append]
        calc
          StringFlow.wordWeight (w.take (hd (n + 1))) =
              StringFlow.wordWeight (w.take (hd n)) + StringFlow.wordWeight (seg n) := hww
          _ = StringFlow.wordWeight (w.take (hd 0)) +
                ((List.range n).map (fun r => StringFlow.wordWeight (seg r))).sum +
                StringFlow.wordWeight (seg n) := by
              rw [ih (by omega)]
          _ = StringFlow.wordWeight (w.take (hd 0)) +
                ((List.range (n + 1)).map
                  (fun r => StringFlow.wordWeight (seg r))).sum := by
              rw [List.range_succ]
              rw [List.map_append, List.sum_append]
              simpa [Nat.add_assoc]
  have htotal : ((List.range K).map (fun r => StringFlow.wordWeight (seg r))).sum =
      ((List.range (K - 1)).map (fun r => StringFlow.wordWeight (seg r))).sum +
        StringFlow.wordWeight (seg (K - 1)) := by
    have hK : K = (K - 1) + 1 := by omega
    rw [hK, List.range_succ]
    rw [List.map_append, List.sum_append]
    simp
  have hpref := hprefix (K - 1) (by omega)
  have hW0le : StringFlow.wordWeight (w.take (hd 0)) ≤
      StringFlow.wordWeight (w.take (hd (K - 1))) := by omega
  have hwwlast : StringFlow.wordWeight (seg (K - 1)) =
      StringFlow.wordWeight (w.drop (hd (K - 1))) +
        StringFlow.wordWeight (w.take (hd 0)) := by
    rw [hseg_last]
    rw [StringFlow.Word.wordWeight_append]
  have hdrop : StringFlow.wordWeight w =
      StringFlow.wordWeight (w.take (hd (K - 1))) +
        StringFlow.wordWeight (w.drop (hd (K - 1))) := by
    have hsplit : w.take (hd (K - 1)) ++ w.drop (hd (K - 1)) = w :=
      List.take_append_drop (hd (K - 1)) w
    have hww := StringFlow.Word.wordWeight_append
      (w.take (hd (K - 1))) (w.drop (hd (K - 1)))
    rwa [hsplit] at hww
  calc
    ((List.range K).map (fun r => StringFlow.wordWeight (seg r))).sum
        = ((List.range (K - 1)).map (fun r => StringFlow.wordWeight (seg r))).sum +
            StringFlow.wordWeight (seg (K - 1)) := htotal
    _ = (StringFlow.wordWeight (w.take (hd (K - 1))) -
            StringFlow.wordWeight (w.take (hd 0))) +
            StringFlow.wordWeight (seg (K - 1)) := by
        have htot : ((List.range (K - 1)).map
            (fun r => StringFlow.wordWeight (seg r))).sum =
            StringFlow.wordWeight (w.take (hd (K - 1))) -
              StringFlow.wordWeight (w.take (hd 0)) := by
          omega
        rw [htot]
    _ = (StringFlow.wordWeight (w.take (hd (K - 1))) -
            StringFlow.wordWeight (w.take (hd 0))) +
          (StringFlow.wordWeight (w.drop (hd (K - 1))) +
            StringFlow.wordWeight (w.take (hd 0))) := by
        rw [hwwlast]
    _ = StringFlow.wordWeight (w.take (hd (K - 1))) +
          StringFlow.wordWeight (w.drop (hd (K - 1))) := by omega
    _ = StringFlow.wordWeight w := hdrop.symm

/-- Every real `CycleQb8Input` has a nonempty cyclic rise block
decomposition.  The decomposition is anchored at the rise boundary at
position `0`, and each block is the C3 run ending before a boundary
plus the rise run starting at that boundary. -/
lemma cyclicSegmentAt_self_eq_zero (w : List Nat) :
    cyclicSegmentAt w w.length = cyclicSegmentAt w 0 := by
  unfold cyclicSegmentAt
  rw [List.drop_length, List.take_length]
  simp

theorem cycleRiseBlockDecompositionExists_of_input
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∃ d : CycleRiseBlockDecomposition m S P w, 1 ≤ d.blockCount := by
  have hP2 : 2 ≤ P := cycleQb8Input_P_ge_two h
  have hP : 0 < P := by omega
  have hw : w.length = P := h.hlength
  rcases cycleQb8Input_cycle_params h with ⟨c, p, hwc, hmc, hSc, hrc, hcc⟩
  have hpos : ∀ x, x ∈ w → 1 ≤ x := by
    intro x hx
    rw [hwc] at hx
    exact cycleWord_mem_ge_one c p hx
  have hbnd0 : IsCyclicBoundary w P 0 := cycleQb8Input_isCyclicBoundary_zero h
  have hprev0 : 3 ≤ w.getI (P - 1) := cycleQb8Input_last_step_c3 h
  have hnext0 : w.getI 0 = 1 ∨ w.getI 0 = 2 := h.hrise_start
  let K := blockCountOf w P 0
  have hKpos : 1 ≤ K := blockCountOf_pos w P 0
  have hKle : K ≤ P := blockCountOf_le_P w P 0 hw hP hpos hbnd0
  have hret : riseBoundaryIter w P 0 K = 0 :=
    riseBoundaryIter_blockCount_eq w P 0 hw hP hpos hbnd0
  let raw : Nat → Nat := fun r => riseBoundaryIter w P 0 r
  have hraw_le : ∀ k : Nat, k ≤ K → IsCyclicBoundary w P (raw k) := by
    intro k hk
    by_cases hklt : k < K
    · dsimp [raw]
      exact riseBoundaryIter_is_cyclic_boundary w P 0 k hw hP hpos hbnd0 (by omega)
    · have hkge : K ≤ k := Nat.le_of_not_gt hklt
      have heq : k = K := le_antisymm hk hkge
      dsimp [raw]
      rw [heq, hret]
      exact hbnd0
  let bnd : Nat → Nat := fun r => cyclicBoundaryIndex P (raw r)
  have hbndFacts : ∀ k : Nat, k ≤ K →
      1 ≤ bnd k ∧ bnd k ≤ P ∧
      3 ≤ w.getI (bnd k - 1) ∧
      (w.getI (bnd k % w.length) = 1 ∨ w.getI (bnd k % w.length) = 2) := by
    intro k hk
    dsimp [bnd]
    exact cyclicBoundaryIndex_isBoundary w P (raw k) hw hP (hraw_le k hk) hprev0
  have hbndlt : ∀ k : Nat, 0 < k → k < K → bnd k < P := by
    intro k hkpos hk
    have hne : raw k ≠ 0 :=
      riseBoundaryIter_ne_zero_of_lt_blockCount w P k hkpos hk
    have hbndk : bnd k = raw k := by
      dsimp [bnd]
      exact cyclicBoundaryIndex_of_pos P (raw k) hne
    rw [hbndk]
    exact (hraw_le k (by omega)).1
  let hd : Nat → Nat := fun r => blockHeadDepth w (bnd (r + 1))
  let c3w : Nat → List Nat := fun r => blockC3Word w (bnd (r + 1))
  let sw : Nat → List Nat := fun r => blockSuffixWord w (bnd (r + 1))
  let rwf : Nat → Nat := fun r => w.getI (hd r - 1)
  have hhdC : ∀ r : Nat, r < K → hd r + (c3w r).length = bnd (r + 1) := by
    intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    have hlen : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
      dsimp [c3w]
      exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
    rw [hlen]
    dsimp [hd]
    unfold blockHeadDepth
    have hCle : c3SuffixLengthAt w (bnd (r + 1)) ≤ bnd (r + 1) :=
      c3SuffixLengthAt_le w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
    simpa [blockC3Len] using Nat.sub_add_cancel hCle
  have hhd0 : hd 0 = blockRiseLen w P := by
    have hL : blockRiseLen w P = blockRiseLen w 0 := by
      unfold blockRiseLen
      congr 1
      simpa [hw] using cyclicSegmentAt_self_eq_zero w
    by_cases hK1 : K = 1
    · have hraw1 : raw 1 = 0 := by
        dsimp [raw]
        rw [← hK1, hret]
      have hbnd1 : bnd 1 = P := by
        dsimp [bnd]
        rw [hraw1]
        simp [cyclicBoundaryIndex]
      have hnext0' : nextRiseStart w P 0 = 0 := by
        simpa [raw, riseBoundaryIter] using hraw1
      have hCq := blockC3Len_next_eq_of_cyclic_zero w P hw hP hpos hnext0 hprev0
      have hC' : c3SuffixLengthAt w P =
          c3PrefixLength (cyclicSegmentAt w (blockRiseLen w 0)) := by
        rw [hnext0'] at hCq
        simpa [cyclicBoundaryIndex] using hCq
      have hadvP : blockAdvance w P 0 = P := by
        have hmod0 := nextRiseStart_eq_add_blockAdvance w P 0
        rw [hnext0'] at hmod0
        have hmod : blockAdvance w P 0 % P = 0 := by
          simpa [Nat.zero_add] using hmod0.symm
        have hdvd : P ∣ blockAdvance w P 0 := Nat.dvd_iff_mod_eq_zero.mpr hmod
        rcases hdvd with ⟨q, hq⟩
        have hq0 : q ≠ 0 := by
          intro hz
          rw [hz, mul_zero] at hq
          have h2 : 2 ≤ blockAdvance w P 0 :=
            blockAdvance_two_le_of_cyclic_boundary w P 0 hw hP hpos hbnd0
          omega
        have hqle1 : q ≤ 1 := by
          apply Nat.le_of_mul_le_mul_right (c := P) ?_ hP
          have hle : blockAdvance w P 0 ≤ P := by
            have hnext0m : w.getI (0 % w.length) = 1 ∨ w.getI (0 % w.length) = 2 := by
              simpa using hnext0
            exact blockAdvance_le_P w P 0 hw (by simp) hpos hnext0m
          rw [Nat.mul_comm]
          rw [← hq]
          simp
          exact hle
        have hq1 : q = 1 := by omega
        rw [hq, hq1]
        simp
      have hsum : blockRiseLen w 0 + c3PrefixLength (cyclicSegmentAt w (blockRiseLen w 0)) =
          P := by
        have hadv : blockAdvance w P 0 =
            blockRiseLen w 0 + c3PrefixLength
              (cyclicSegmentAt w ((0 + blockRiseLen w 0) % P)) := rfl
        rw [hadv] at hadvP
        have hmod : (0 + blockRiseLen w 0) % P = blockRiseLen w 0 := by
          rw [Nat.zero_add]
          exact Nat.mod_eq_of_lt (blockRiseLen_zero_lt w P hw hP hpos hprev0)
        rwa [hmod] at hadvP
      have hd0 : hd 0 = P - c3SuffixLengthAt w P := by
        dsimp [hd, bnd]
        rw [hraw1]
        simp [cyclicBoundaryIndex]
        rfl
      rw [hL]
      rw [hd0, hC']
      omega
    · have hne : raw 1 ≠ 0 := by
        exact riseBoundaryIter_ne_zero_of_lt_blockCount w P 1 (by norm_num) (by omega)
      have hbnd1 : bnd 1 = raw 1 := by
        dsimp [bnd]
        exact cyclicBoundaryIndex_of_pos P (raw 1) hne
      have hraw1 : raw 1 = blockAdvance w P 0 := by
        dsimp [raw]
        rw [riseBoundaryIter_succ]
        change nextRiseStart w P 0 = blockAdvance w P 0
        rw [nextRiseStart_eq_add_blockAdvance]
        have hlt : blockAdvance w P 0 < P := by
          have hle : blockAdvance w P 0 ≤ P := by
            have hnext0m : w.getI (0 % w.length) = 1 ∨ w.getI (0 % w.length) = 2 := by
              simpa using hnext0
            exact blockAdvance_le_P w P 0 hw (by simp) hpos hnext0m
          by_cases heq : blockAdvance w P 0 = P
          · exfalso
            apply hne
            dsimp [raw]
            rw [riseBoundaryIter_succ]
            change nextRiseStart w P 0 = 0
            rw [nextRiseStart_eq_add_blockAdvance, heq]
            simp [riseBoundaryIter]
          · omega
        simp [Nat.mod_eq_of_lt hlt]
      have hCq := blockC3Len_next_eq_of_cyclic_zero w P hw hP hpos hnext0 hprev0
      have hbq : cyclicBoundaryIndex P (nextRiseStart w P 0) = raw 1 := by
        have hraw1ns : raw 1 = nextRiseStart w P 0 := by
          dsimp [raw]
          rw [riseBoundaryIter_succ]
          change nextRiseStart w P 0 = nextRiseStart w P 0
          rfl
        rw [hraw1ns]
        have hne0 : nextRiseStart w P 0 ≠ 0 := by
          rw [hraw1ns] at hne
          exact hne
        exact cyclicBoundaryIndex_of_pos P (nextRiseStart w P 0) hne0
      have hC' : c3SuffixLengthAt w (raw 1) =
          c3PrefixLength (cyclicSegmentAt w (blockRiseLen w 0)) := by
        rw [hbq] at hCq
        exact hCq
      have hd0 : hd 0 = raw 1 - c3SuffixLengthAt w (raw 1) := by
        dsimp [hd]
        rw [hbnd1]
        rfl
      rw [hL]
      rw [hd0, hC', hraw1]
      have hadv : blockAdvance w P 0 =
          blockRiseLen w 0 + c3PrefixLength
            (cyclicSegmentAt w ((0 + blockRiseLen w 0) % P)) := rfl
      rw [hadv]
      have hmod : (0 + blockRiseLen w 0) % P = blockRiseLen w 0 := by
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt (blockRiseLen_zero_lt w P hw hP hpos hprev0)
      rw [hmod]
      omega
  have hnext_lt : ∀ r : Nat, r < K → r + 1 < K →
      hd (r + 1) = hd r + (c3w r).length + (sw r).length := by
    intro r hr hrK
    have hbndP : bnd (r + 1) < P := hbndlt (r + 1) (by omega) hrK
    have hb := hbndFacts (r + 1) (by omega)
    have hbd := blockHeadDepth_next_of_boundary w P (bnd (r + 1)) hw hP
      hb.1 hbndP hpos hb.2.2.1 hb.2.2.2 hnext0 hprev0
    have hleft : cyclicBoundaryIndex P (nextRiseStart w P (bnd (r + 1))) = bnd (r + 2) := by
      have hne : raw (r + 1) ≠ 0 :=
        riseBoundaryIter_ne_zero_of_lt_blockCount w P (r + 1) (by omega) hrK
      have hbnd_eq : cyclicBoundaryIndex P (raw (r + 1)) = raw (r + 1) :=
        cyclicBoundaryIndex_of_pos P (raw (r + 1)) hne
      have hsucc : riseBoundaryIter w P 0 (r + 2) =
          nextRiseStart w P (riseBoundaryIter w P 0 (r + 1)) := by
        rw [riseBoundaryIter_succ]
      dsimp [bnd, raw]
      rw [hbnd_eq, ← hsucc]
    have hleft' : blockHeadDepth w
        (cyclicBoundaryIndex P (nextRiseStart w P (bnd (r + 1)))) = hd (r + 1) := by
      rw [hleft]
    have hrhs : blockHeadDepth w (bnd (r + 1)) + blockC3Len w (bnd (r + 1)) +
          blockRiseLen w (bnd (r + 1)) =
        hd r + (c3w r).length + (sw r).length := by
      dsimp [hd, c3w, sw]
      rw [blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)]
      rw [blockSuffixWord_length w (bnd (r + 1))]
    rw [hleft'] at hbd
    rw [hrhs] at hbd
    exact hbd
  have hwrap : ∀ r : Nat, r < K → r + 1 = K →
      hd 0 + P = hd r + (c3w r).length + (sw r).length := by
    intro r hr hrK
    have hbndK : bnd (r + 1) = P := by
      rw [hrK]
      dsimp [bnd, raw]
      rw [hret]
      simp [cyclicBoundaryIndex]
    have hb := hbndFacts (r + 1) (by omega)
    have hlenC' : (c3w r).length = c3SuffixLengthAt w P := by
      dsimp [c3w]
      rw [hbndK]
      exact blockC3Word_length w P (by rw [hw])
    have hlenL' : (sw r).length = blockRiseLen w P := by
      dsimp [sw]
      rw [hbndK]
      exact blockSuffixWord_length w P
    have hhd : hd r = P - c3SuffixLengthAt w P := by
      dsimp [hd]
      rw [hbndK]
      rfl
    have hCle : c3SuffixLengthAt w P ≤ P := c3SuffixLengthAt_le w P (by rw [hw])
    rw [hhd0, hhd, hlenC', hlenL']
    omega
  have hsegs : ∀ r : Nat, r + 1 < K →
      c3w r ++ sw r = (w.take (hd (r + 1))).drop (hd r) := by
    intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    have hbndP : bnd (r + 1) < P := hbndlt (r + 1) (by omega) hr
    have hL : blockRiseLen w (bnd (r + 1)) ≥ 1 :=
      blockRiseLen_pos_of_boundary w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
        (by simpa [hw] using hb.2.2.2)
    have hbL : bnd (r + 1) + blockRiseLen w (bnd (r + 1)) < P :=
      blockRiseLen_boundary_add_lt w P (bnd (r + 1)) hw hP hb.1 hbndP hpos
        (by simpa [hw] using hb.2.2.2) hprev0
    have hhdNext : hd (r + 1) = bnd (r + 1) + blockRiseLen w (bnd (r + 1)) := by
      have hh := hnext_lt r (by omega) hr
      have hlenC' : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
        dsimp [c3w]
        exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
      have hlenL' : (sw r).length = blockRiseLen w (bnd (r + 1)) := by
        dsimp [sw]
        exact blockSuffixWord_length w (bnd (r + 1))
      have hhdC' : hd r + (c3w r).length = bnd (r + 1) := hhdC r (by omega)
      rw [hh, hhdC', hlenL']
    -- c3w r ++ sw r = (w.take (hd (r+1))).drop (hd r)
    have hc3seg : c3w r = (w.take (bnd (r + 1))).drop (hd r) := by
      dsimp [c3w]
      have hlen : (blockC3Word w (bnd (r + 1))).length =
          c3SuffixLengthAt w (bnd (r + 1)) :=
        blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
      -- (w.take b).drop (b - C) = (w.take b).drop (hd r); hd r = b - C
      congr 1
    have hswseg : sw r = (w.take (hd (r + 1))).drop (bnd (r + 1)) := by
      have hdrop_eq : (w.take (hd (r + 1))).drop (bnd (r + 1)) =
          (w.drop (bnd (r + 1))).take (blockRiseLen w (bnd (r + 1))) := by
        rw [hhdNext]
        rw [List.take_drop]
      rw [hdrop_eq]
      dsimp [sw]
      change (cyclicSegmentAt w (bnd (r + 1))).take
          (blockRiseLen w (bnd (r + 1))) =
        (w.drop (bnd (r + 1))).take (blockRiseLen w (bnd (r + 1)))
      unfold cyclicSegmentAt
      rw [List.take_append_of_le_length (by
        rw [List.length_drop]
        omega)]
    have hsplit : w.take (hd (r + 1)) =
        w.take (hd r) ++ (w.take (hd (r + 1))).drop (hd r) := by
      have hle : hd r ≤ hd (r + 1) := by
        have hh := hnext_lt r (by omega) hr
        omega
      have htake3 : (w.take (hd (r + 1))).take (hd r) = w.take (hd r) := by
        rw [List.take_take]
        rw [Nat.min_comm, Nat.min_eq_right hle]
      have htake2 := List.take_append_drop (hd r) (w.take (hd (r + 1)))
      simpa [htake3] using htake2.symm
    have hmid : w.take (hd (r + 1)) =
        (w.take (bnd (r + 1))) ++ (w.take (hd (r + 1))).drop (bnd (r + 1)) := by
      have hle : bnd (r + 1) ≤ hd (r + 1) := by
        have hhdNext' : hd (r + 1) = bnd (r + 1) + blockRiseLen w (bnd (r + 1)) := hhdNext
        omega
      have htake3 : (w.take (hd (r + 1))).take (bnd (r + 1)) = w.take (bnd (r + 1)) := by
        rw [List.take_take]
        rw [Nat.min_comm, Nat.min_eq_right hle]
      have htake2 := List.take_append_drop (bnd (r + 1)) (w.take (hd (r + 1)))
      simpa [htake3] using htake2.symm
    have hsplitDrop : (w.take (hd (r + 1))).drop (hd r) =
        (w.take (bnd (r + 1))).drop (hd r) ++
          (w.take (hd (r + 1))).drop (bnd (r + 1)) := by
      -- from hmid: take(hd(r+1)) = take(bnd) ++ drop(bnd); drop (hd r) of both sides
      have hle : hd r ≤ (w.take (bnd (r + 1))).length := by
        have hbndFacts' := hbndFacts (r + 1) (by omega)
        have hlenb : (w.take (bnd (r + 1))).length = bnd (r + 1) :=
          List.length_take_of_le (by rw [hw]; exact hbndFacts'.2.1)
        rw [hlenb]
        have hhdC' : hd r + (c3w r).length = bnd (r + 1) := hhdC r (by omega)
        omega
      rw [hmid]
      rw [List.drop_append_of_le_length hle]
      simp
      rw [← hmid]
    calc
      c3w r ++ sw r = (w.take (bnd (r + 1))).drop (hd r) ++
          (w.take (hd (r + 1))).drop (bnd (r + 1)) := by rw [hc3seg, hswseg]
      _ = (w.take (hd (r + 1))).drop (hd r) := hsplitDrop.symm
  have hseg_last : c3w (K - 1) ++ sw (K - 1) =
      (w.drop (hd (K - 1))) ++ (w.take (hd 0)) := by
    have hb := hbndFacts K (by omega)
    have hsub : K - 1 + 1 = K := by omega
    have hbndK : bnd K = P := by
      dsimp [bnd, raw]
      rw [hret]
      simp [cyclicBoundaryIndex]
    have hlenC' : (c3w (K - 1)).length = c3SuffixLengthAt w P := by
      dsimp [c3w]
      rw [hsub, hbndK]
      exact blockC3Word_length w P (by rw [hw])
    have hlenL' : (sw (K - 1)).length = blockRiseLen w P := by
      dsimp [sw]
      rw [hsub, hbndK]
      exact blockSuffixWord_length w P
    have hdLast : hd (K - 1) = P - c3SuffixLengthAt w P := by
      dsimp [hd]
      rw [hsub, hbndK]
      rfl
    have hc3eq : c3w (K - 1) = w.drop (hd (K - 1)) := by
      dsimp [c3w]
      rw [hsub, hbndK]
      change (w.take P).drop (P - c3SuffixLengthAt w P) = w.drop (hd (K - 1))
      rw [hdLast]
      have htakeP : w.take P = w := List.take_of_length_le (by rw [hw])
      rw [htakeP]
    have hsweq : sw (K - 1) = w.take (hd 0) := by
      dsimp [sw]
      rw [hsub, hbndK]
      change (cyclicSegmentAt w P).take (blockRiseLen w P) = w.take (hd 0)
      have hL : blockRiseLen w P = hd 0 := hhd0.symm
      rw [hL]
      have hsegP : cyclicSegmentAt w P = cyclicSegmentAt w 0 := by
        simpa [hw] using cyclicSegmentAt_self_eq_zero w
      rw [hsegP]
      have hseg0 : cyclicSegmentAt w 0 = w := by
        unfold cyclicSegmentAt
        simp
      rw [hseg0]
    rw [hc3eq, hsweq]
  have hlenSeg : ∀ r : Nat, r + 1 < K →
      hd (r + 1) = hd r + (c3w r ++ sw r).length := by
    intro r hr
    have hh := hnext_lt r (by omega) hr
    have hlen : (c3w r ++ sw r).length = (c3w r).length + (sw r).length :=
      List.length_append
    rw [hlen]
    omega
  have hlenSeg_last : hd 0 + w.length = hd (K - 1) + (c3w (K - 1) ++ sw (K - 1)).length := by
    have hh := hwrap (K - 1) (by omega) (by omega)
    have hlen : (c3w (K - 1) ++ sw (K - 1)).length =
        (c3w (K - 1)).length + (sw (K - 1)).length := List.length_append
    rw [← hw] at hh
    omega
  have hsegsum := wordWeight_sum_of_segments w K hd (fun r => c3w r ++ sw r) hKpos
    hsegs hseg_last hlenSeg hlenSeg_last
  have hweight' : S =
      ((List.range K).map
        (fun r => StringFlow.wordWeight (c3w r) + StringFlow.wordWeight (sw r))).sum := by
    have hS : S = StringFlow.wordWeight w := h.hweight.symm
    have hwws : ((List.range K).map
        (fun r => StringFlow.wordWeight (c3w r ++ sw r))).sum =
        ((List.range K).map
          (fun r => StringFlow.wordWeight (c3w r) + StringFlow.wordWeight (sw r))).sum := by
      induction K with
      | zero => simp
      | succ K ih =>
          rw [List.range_succ]
          rw [List.map_append, List.sum_append]
          simp [StringFlow.Word.wordWeight_append, ih, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
    rw [hS, ← hwws]
    exact hsegsum.symm
  refine ⟨CycleRiseBlockDecomposition.mk K hd rwf c3w sw hw h.hclosed
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hweight', hKpos⟩
  · intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    exact blockHeadDepth_pos_of_rise_start w (bnd (r + 1))
      (by rw [hw]; exact hb.2.1) hb.1 hb.2.2.1 hnext0
  · intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    exact blockHeadDepth_lt_P w P (bnd (r + 1)) hw
      (by rw [hw]; exact hb.2.1) hb.1 hb.2.2.1
  · intro r hr
    rfl
  · intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    let b := bnd (r + 1)
    have hC_le : c3SuffixLengthAt w b ≤ b := c3SuffixLengthAt_le w b (by rw [hw]; exact hb.2.1)
    have hC_lt : c3SuffixLengthAt w b < b := by
      by_cases hCeq : c3SuffixLengthAt w b = b
      · have hmem := c3SuffixLengthAt_mem w b (by rw [hw]; exact hb.2.1) (b - 1)
          (by
            rw [hCeq]
            exact Nat.sub_lt (by omega : 0 < b) (by decide : 0 < 1))
        have hz : b - 1 - (b - 1) = 0 := by omega
        rw [hz] at hmem
        rcases hnext0 with h1 | h2
        · rw [h1] at hmem
          omega
        · rw [h2] at hmem
          omega
      · exact lt_of_le_of_ne hC_le hCeq
    have hstop := c3SuffixLengthAt_stop w b (by rw [hw]; exact hb.2.1) hpos hC_lt
    have hidx : b - 1 - c3SuffixLengthAt w b = hd r - 1 := by
      dsimp [hd, b]
      unfold blockHeadDepth
      simp [blockC3Len]
      omega
    rwa [hidx] at hstop
  · intro r hr
    have hb := hbndFacts (r + 1) (by omega)
    have hCpos : 0 < c3SuffixLengthAt w (bnd (r + 1)) :=
      c3SuffixLengthAt_pos_of_head w (bnd (r + 1)) hb.1 hb.2.2.1
    have hlen : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
      dsimp [c3w]
      exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
    intro hnil
    have hlen0 : (c3w r).length = 0 := by simp [hnil]
    rw [hlen] at hlen0
    omega
  · intro r hr t ht
    rcases (List.mem_iff_getElem.mp ht) with ⟨k, hklt, hk⟩
    have hkget : (c3w r).getI k = t := by
      have hklt' : k < (c3w r).length := hklt
      rw [List.getI_eq_getElem (l := c3w r) (n := k) hklt']
      exact hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltC : k < c3SuffixLengthAt w (bnd (r + 1)) := by
      have hlen : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
        dsimp [c3w]
        exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
      simpa [hlen] using hklt
    have hCpos : 0 < c3SuffixLengthAt w (bnd (r + 1)) :=
      c3SuffixLengthAt_pos_of_head w (bnd (r + 1)) hb.1 hb.2.2.1
    have hC_le : c3SuffixLengthAt w (bnd (r + 1)) ≤ bnd (r + 1) :=
      c3SuffixLengthAt_le w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
    have hmem := c3SuffixLengthAt_mem w (bnd (r + 1))
      (by rw [hw]; exact hb.2.1)
      (c3SuffixLengthAt w (bnd (r + 1)) - 1 - k) (by omega)
    have hidx : bnd (r + 1) - 1 -
        (c3SuffixLengthAt w (bnd (r + 1)) - 1 - k) =
        bnd (r + 1) - c3SuffixLengthAt w (bnd (r + 1)) + k := by omega
    rw [hidx] at hmem
    have hget2 : (c3w r).getI k = w.getI
        (bnd (r + 1) - c3SuffixLengthAt w (bnd (r + 1)) + k) := by
      dsimp [c3w]
      simpa [blockC3Len] using
        blockC3Word_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltC
    rw [← hkget, hget2]
    exact hmem
  · intro r hr k hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltC : k < c3SuffixLengthAt w (bnd (r + 1)) := by
      have hlen : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
        dsimp [c3w]
        exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
      simpa [hlen] using hk
    have hget2 : (c3w r).getI k = w.getI (hd r + k) := by
      dsimp [c3w]
      have hg := blockC3Word_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltC
      have hidx : bnd (r + 1) - c3SuffixLengthAt w (bnd (r + 1)) + k = hd r + k := by
        dsimp [hd]
        unfold blockHeadDepth
        simp [blockC3Len]
      simpa [blockC3Len, hidx] using hg
    exact hget2
  · intro r hr k hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltC : k < c3SuffixLengthAt w (bnd (r + 1)) := by
      have hlen : (c3w r).length = c3SuffixLengthAt w (bnd (r + 1)) := by
        dsimp [c3w]
        exact blockC3Word_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
      simpa [hlen] using hk
    have hseglt : hd r + k < w.length := by
      have hle0 : hd r + (c3w r).length ≤ w.length := by
        have hhdC' := hhdC r hr
        rw [hhdC']
        rw [hw]
        exact hb.2.1
      have hk' : k < (c3w r).length := hk
      omega
    have hex := h.hexact (hd r + k) hseglt
    have hget2 : (c3w r).getI k = w.getI (hd r + k) := by
      dsimp [c3w]
      have hg := blockC3Word_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltC
      have hidx : bnd (r + 1) - c3SuffixLengthAt w (bnd (r + 1)) + k = hd r + k := by
        dsimp [hd]
        unfold blockHeadDepth
        simp [blockC3Len]
      simpa [blockC3Len, hidx] using hg
    rwa [← hget2] at hex
  · intro r hr t ht
    rcases (List.mem_iff_getElem.mp ht) with ⟨k, hklt, hk⟩
    have hkget : (sw r).getI k = t := by
      have hklt' : k < (sw r).length := hklt
      rw [List.getI_eq_getElem (l := sw r) (n := k) hklt']
      exact hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltL : k < blockRiseLen w (bnd (r + 1)) := by
      have hlen : (sw r).length = blockRiseLen w (bnd (r + 1)) := by
        dsimp [sw]
        exact blockSuffixWord_length w (bnd (r + 1))
      simpa [hlen] using hklt
    have hmem := risePrefixLength_mem (cyclicSegmentAt w (bnd (r + 1))) k
      (by simpa [blockRiseLen] using hkltL)
    have hget2 : (cyclicSegmentAt w (bnd (r + 1))).getI k = w.getI
        ((bnd (r + 1) + k) % w.length) := by
      have hkltw : k < w.length := by
        have hle := risePrefixLength_le (cyclicSegmentAt w (bnd (r + 1)))
        have hseg := cyclicSegmentAt_length w (bnd (r + 1)) (by rw [hw]; exact hb.2.1)
        have hk' : k < blockRiseLen w (bnd (r + 1)) := hkltL
        unfold blockRiseLen at hk'
        omega
      exact cyclicSegmentAt_getI_mod w (bnd (r + 1)) k (by rw [hw]; exact hb.2.1) hkltw
    have hw12 : w.getI ((bnd (r + 1) + k) % w.length) = 1 ∨
        w.getI ((bnd (r + 1) + k) % w.length) = 2 := by
      rwa [hget2] at hmem
    have hget3 : (sw r).getI k = w.getI ((bnd (r + 1) + k) % P) := by
      dsimp [sw]
      simpa [hw] using
        blockSuffixWord_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltL
    rw [← hkget, hget3]
    simpa [hw] using hw12
  · intro r hr k hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltL : k < blockRiseLen w (bnd (r + 1)) := by
      have hlen : (sw r).length = blockRiseLen w (bnd (r + 1)) := by
        dsimp [sw]
        exact blockSuffixWord_length w (bnd (r + 1))
      simpa [hlen] using hk
    have hget := blockSuffixWord_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltL
    have hhdC' : hd r + (c3w r).length = bnd (r + 1) := hhdC r hr
    have hidx : (bnd (r + 1) + k) % w.length =
        (hd r + (c3w r).length + k) % P := by
      rw [← hw]
      rw [hhdC']
    have hget' : (blockSuffixWord w (bnd (r + 1))).getI k =
        w.getI ((hd r + (c3w r).length + k) % P) := by
      simpa [hidx] using hget
    dsimp [sw]
    exact hget'
  · intro r hr k hk
    have hb := hbndFacts (r + 1) (by omega)
    have hkltL : k < blockRiseLen w (bnd (r + 1)) := by
      have hlen : (sw r).length = blockRiseLen w (bnd (r + 1)) := by
        dsimp [sw]
        exact blockSuffixWord_length w (bnd (r + 1))
      simpa [hlen] using hk
    by_cases hrK : r + 1 < K
    · -- non-wrapping boundary
      have hbndP : bnd (r + 1) < P := hbndlt (r + 1) (by omega) hrK
      have hbL : bnd (r + 1) + blockRiseLen w (bnd (r + 1)) < P :=
        blockRiseLen_boundary_add_lt w P (bnd (r + 1)) hw hP hb.1 hbndP hpos
          (by simpa [hw] using hb.2.2.2) hprev0
      have hbnd_k : bnd (r + 1) + k < w.length := by
        rw [hw]
        omega
      have hstate : StringFlow.Word.wordOrbit (w.take (hd r + (c3w r).length)) m =
          StringFlow.Word.wordOrbit (w.take (bnd (r + 1))) m := by
        have hhdC' : hd r + (c3w r).length = bnd (r + 1) := hhdC r hr
        rw [hhdC']
      have hrun : riseRun (StringFlow.Word.wordOrbit (w.take (hd r + (c3w r).length)) m)
          ((sw r).take k) =
        StringFlow.Word.wordOrbit (w.take (bnd (r + 1) + k)) m := by
        rw [riseRun_eq_wordOrbit]
        rw [hstate]
        have htake : (sw r).take k = (cyclicSegmentAt w (bnd (r + 1))).take k := by
          dsimp [sw]
          change ((cyclicSegmentAt w (bnd (r + 1))).take
              (blockRiseLen w (bnd (r + 1)))).take k =
            (cyclicSegmentAt w (bnd (r + 1))).take k
          rw [List.take_take]
          rw [Nat.min_eq_left (by omega)]
        rw [htake]
        exact cyclic_local_head_eq_global_nonwrap
          (m := m) (w := w) (bnd (r + 1)) k (by rw [hw]; omega)
      have hex := h.hexact (bnd (r + 1) + k) (by rw [hw]; omega)
      have hget : (sw r).getI k = w.getI (bnd (r + 1) + k) := by
        have hg := blockSuffixWord_getI w (bnd (r + 1)) (by rw [hw]; exact hb.2.1) k hkltL
        have hmod : (bnd (r + 1) + k) % w.length = bnd (r + 1) + k :=
          Nat.mod_eq_of_lt (by rw [hw]; omega)
        have hg' : (blockSuffixWord w (bnd (r + 1))).getI k =
            w.getI (bnd (r + 1) + k) := by
          simpa [hmod] using hg
        dsimp [sw]
        exact hg'
      rw [hrun]
      exact hex.trans hget.symm
    · -- wrapping boundary: bnd (r+1) = P, reduce to position 0
      have hbndK : bnd (r + 1) = P := by
        have heq : r + 1 = K := le_antisymm (by omega) (Nat.le_of_not_gt hrK)
        rw [heq]
        dsimp [bnd, raw]
        rw [hret]
        simp [cyclicBoundaryIndex]
      have hhdC' : hd r + (c3w r).length = P := by
        have hh := hhdC r hr
        simpa [hbndK] using hh
      have htakeP : w.take P = w := List.take_of_length_le (by rw [hw])
      have hstate : StringFlow.Word.wordOrbit (w.take (hd r + (c3w r).length)) m = m := by
        rw [hhdC', htakeP, h.hclosed]
      have hrun : riseRun (StringFlow.Word.wordOrbit (w.take (hd r + (c3w r).length)) m)
          ((sw r).take k) =
        StringFlow.Word.wordOrbit (w.take k) m := by
        rw [riseRun_eq_wordOrbit]
        rw [hstate]
        have htake : (sw r).take k = (cyclicSegmentAt w 0).take k := by
          dsimp [sw]
          rw [hbndK]
          change ((cyclicSegmentAt w P).take (blockRiseLen w P)).take k =
            (cyclicSegmentAt w 0).take k
          rw [List.take_take]
          have hkL : k ≤ blockRiseLen w P := by
            simpa [hbndK] using Nat.le_of_lt hkltL
          rw [Nat.min_eq_left hkL]
          have hsegP : cyclicSegmentAt w P = cyclicSegmentAt w 0 := by
            simpa [hw] using cyclicSegmentAt_self_eq_zero w
          rw [hsegP]
        rw [htake]
        simpa [StringFlow.Word.wordOrbit] using cyclic_local_head_eq_global_nonwrap
          (m := m) (w := w) 0 k (by
            have hkltP : k < blockRiseLen w P := by
              simpa [hbndK] using hkltL
            have hle : blockRiseLen w P ≤ P :=
              blockRiseLen_le_P w P P (by rw [hw]) (by rw [hw])
            omega)
      have hkw : k < w.length := by
        have hkltP : k < blockRiseLen w P := by
          simpa [hbndK] using hkltL
        have hle : blockRiseLen w P ≤ P :=
          blockRiseLen_le_P w P P (by rw [hw]) (by rw [hw])
        omega
      have hex := h.hexact k hkw
      have hget : (sw r).getI k = w.getI k := by
        have hg := blockSuffixWord_getI w P (by rw [hw]) k (by
          -- k < blockRiseLen w P: from hkltL and hbndK
          simpa [hbndK] using hkltL)
        have hmod : (P + k) % w.length = k := by
          rw [hw]
          simp [Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        have hg' : (blockSuffixWord w P).getI k = w.getI k := by
          simpa [hmod] using hg
        dsimp [sw]
        rw [hbndK]
        exact hg'
      rw [hrun]
      exact hex.trans hget.symm
  · intro r hr
    by_cases hrK : r + 1 < K
    · rw [if_pos hrK]
      exact hnext_lt r hr hrK
    · rw [if_neg hrK]
      exact hwrap r hr (by omega)

/-- INVALID: depends on the rejected tail-charged global comparison
(6).  Kept only for the audit trail; do not use as an hfail source. -/
theorem cycleRiseBlockFailure_of_real_input_and_global_comparison_INVALID
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (hglobal : cycleRiseBlockPMIGlobalComparisonHolds_INVALID) :
    ∃ d : CycleRiseBlockDecomposition m S P w,
      ∃ r : Nat, r < d.blockCount ∧
        2 * (cycleRiseBlockTailDepth d r -
            cycleRiseBlockTailResetWeight d r) + 13 ≤
          cycleRiseBlockTailRank d r := by
  rcases cycleRiseBlockDecompositionExists_of_input h with ⟨d, _hdpos⟩
  exact ⟨d, cycleRiseBlockTailFailure_of_global_comparison_INVALID d
    (hglobal m S P w rise c3 h d)⟩

/-- INVALID: depends on the rejected global comparison (6).  Kept only
for the audit trail; do not use downstream. -/
theorem cycleRiseBlockTailFailureWindowExistence_of_pmi_INVALID
    (hglobal : cycleRiseBlockPMIGlobalComparisonHolds_INVALID) :
    cycleRiseBlockTailFailureWindowExistence := by
  intro m S P w rise c3 h
  rcases cycleRiseBlockDecompositionExists_of_input h with ⟨d, _hdpos⟩
  refine ⟨d, ?_⟩
  exact cycleRiseBlockTailFailureWindow_of_global_comparison_INVALID h d
    (hglobal m S P w rise c3 h d)

/-- A word is valid from a state when every step is exact: the
`twoValuation` of the step numerator equals the step weight. -/
lemma wordValid_of_exact_steps (u : List Nat) (x : Nat)
    (hexact : ∀ k, k < u.length →
      twoValuation (5 * riseRun x (u.take k) + 1) = u.getI k) :
    StringFlow.Word.wordValid u x := by
  induction u generalizing x with
  | nil => simp [StringFlow.Word.wordValid]
  | cons t ts ih =>
      have hfirst : twoValuation (5 * x + 1) = t := by
        simpa [riseRun] using hexact 0 (by simp)
      have hdvd : (5 * x + 1) % 2 ^ t = 0 := by
        have hpos : 0 < 5 * x + 1 := by positivity
        have hge : t ≤ twoValuation (5 * x + 1) := by omega
        have hdvd' : 2 ^ t ∣ 5 * x + 1 :=
          (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * x + 1) t hpos).mp hge
        exact Nat.dvd_iff_mod_eq_zero.mp hdvd'
      have htailExact : ∀ k, k < ts.length →
          twoValuation (5 * riseRun ((5 * x + 1) / 2 ^ t) (ts.take k) + 1) =
            ts.getI k := by
        intro k hk
        have hk' : k + 1 < (t :: ts).length := by simp [hk]
        have h := hexact (k + 1) hk'
        have hrun : riseRun x ((t :: ts).take (k + 1)) =
            riseRun ((5 * x + 1) / 2 ^ t) (ts.take k) := by
          rw [List.take_cons (by omega)]
          simp [riseRun, riseStep]
        have hidx : (t :: ts).getI (k + 1) = ts.getI k := by
          rw [List.getI_cons_succ]
        rwa [hrun, hidx] at h
      have htail := ih ((5 * x + 1) / 2 ^ t) htailExact
      simp [StringFlow.Word.wordValid, hdvd, htail]

/-- The rise suffix of a cyclic rise block is an exact legal word from
the C3-tail state: every step is `1` or `2` and each step divides
exactly.  This supplies the `hvalid`/`hsteps` inputs of the real-word
premises instantiation `premises_of_real_orbit_head`. -/
theorem suffixWord_valid_of_cycleRiseBlock
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    StringFlow.Word.wordValid (d.suffixWord r) (cycleRiseBlockC3TailState d r) ∧
      ∀ t ∈ d.suffixWord r, t = 1 ∨ t = 2 := by
  constructor
  · exact wordValid_of_exact_steps (d.suffixWord r) (cycleRiseBlockC3TailState d r)
      (by
        intro k hk
        have h := d.hsuffix_exact r hr k hk
        simpa [cycleRiseBlockC3TailState] using h)
  · exact d.hsuffix_one_two r hr

/-- Prefixes of a real rise suffix are the corresponding real cycle
prefixes: `wordOrbit (suffix.take j) (C3TailState) = wordOrbit (w.take (tailDepth + j)) m`
for every prefix length `j` of the non-wrapping suffix.  This supplies
the `hrj`/`hrs_eq` inputs of `premises_of_real_orbit_head`. -/
theorem suffixWord_prefix_eq_word_prefix_nonwrap
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount)
    (j : Nat) (hj : j ≤ (d.suffixWord r).length) :
    StringFlow.Word.wordOrbit ((d.suffixWord r).take j)
        (cycleRiseBlockC3TailState d r) =
      StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r + j)) m := by
  let start := cycleRiseBlockTailDepth d r
  have hseg := cycleRiseBlockSuffixWord_eq_drop_nonwrap d r hr hrnext
  have hq : cycleRiseBlockC3TailState d r =
      StringFlow.Word.wordOrbit (w.take start) m := rfl
  have hbL : start + j ≤ w.length := by
    dsimp [start, cycleRiseBlockTailDepth]
    have hnext : d.headDepth r + (d.c3Word r).length + (d.suffixWord r).length =
        d.headDepth (r + 1) := by
      have h := d.hnext r hr
      have hcast : (d.headDepth (r + 1) : Nat) =
          d.headDepth r + (d.c3Word r).length + (d.suffixWord r).length := by
        simpa [hrnext] using h
      exact hcast.symm
    have hlt : d.headDepth (r + 1) < P := d.hhead_lt (r + 1) hrnext
    rw [d.hperiod]
    omega
  have htake : ((w.drop start).take (d.suffixWord r).length).take j =
      (w.drop start).take j := by
    rw [List.take_take]
    rw [Nat.min_eq_left hj]
  have hmain : StringFlow.Word.wordOrbit ((d.suffixWord r).take j)
        (cycleRiseBlockC3TailState d r) =
      StringFlow.Word.wordOrbit ((w.take (start + j)).drop start)
        (StringFlow.Word.wordOrbit (w.take start) m) := by
    rw [hq]
    rw [hseg]
    dsimp [start, cycleRiseBlockTailDepth] at htake
    rw [htake]
    rw [← List.take_drop]
    dsimp [start, cycleRiseBlockTailDepth]
  have hwd := wordOrbit_take_drop w m start j hbL
  exact hmain.trans hwd.symm

/-- Advancing a cyclic prefix past the end wraps to zero:
`wordOrbit (w.take ((k+1) % P)) m = (5*wordOrbit (w.take k) m + 1)/2^{w.getI k}`
for `k < P`, using the cycle closure `wordOrbit w m = m`. -/
lemma wordOrbit_take_succ_mod_of_closed
    {m P : Nat} {w : List Nat}
    (hw : w.length = P)
    (hclosed : StringFlow.Word.wordOrbit w m = m)
    (k : Nat) (hk : k < P) :
    StringFlow.Word.wordOrbit (w.take ((k + 1) % P)) m =
      (5 * StringFlow.Word.wordOrbit (w.take k) m + 1) / 2 ^ w.getI k := by
  by_cases hk1 : k + 1 < P
  · have hmod : (k + 1) % P = k + 1 := Nat.mod_eq_of_lt hk1
    rw [hmod]
    have hkltw : k < w.length := by rw [hw]; exact hk
    exact wordOrbit_take_succ w m k hkltw
  · have hkP : k + 1 = P := by omega
    have hmod : (k + 1) % P = 0 := by
      rw [hkP, Nat.mod_self]
    rw [hmod]
    simp [StringFlow.Word.wordOrbit]
    have hkltw : k < w.length := by rw [hw]; omega
    have htake : w.take (k + 1) = w.take k ++ [w.getI k] :=
      UnifiedCoreAudit.take_succ_append_getI w k hkltw
    have htakeP : w.take (k + 1) = w := by
      rw [hkP]
      exact List.take_of_length_le (by rw [hw])
    have hw' : w = w.take k ++ [w.getI k] := htakeP.symm.trans htake
    have hstep : StringFlow.Word.wordOrbit w m =
        (5 * StringFlow.Word.wordOrbit (w.take k) m + 1) / 2 ^ w.getI k := by
      conv_lhs => rw [hw']
      exact S6Audit.wordOrbit_append_singleton (w.take k) m (w.getI k)
    exact hclosed.symm.trans hstep

/-- Prefixes of a real rise suffix equal the cyclic word prefixes modulo
the period: `wordOrbit (suffix.take j) (C3TailState) =
wordOrbit (w.take ((tailDepth + j) % P)) m`.  This covers both the
non-wrapping and the wrapping block. -/
theorem suffixWord_prefix_eq_word_prefix_mod
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (j : Nat) (hj : j ≤ (d.suffixWord r).length) :
    StringFlow.Word.wordOrbit ((d.suffixWord r).take j)
        (cycleRiseBlockC3TailState d r) =
      StringFlow.Word.wordOrbit
        (w.take ((cycleRiseBlockTailDepth d r + j) % P)) m := by
  have hPpos : 0 < P := by
    have hh := d.hhead_pos r hr
    have hlt := d.hhead_lt r hr
    omega
  have hq : cycleRiseBlockC3TailState d r =
      StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m := rfl
  induction j with
  | zero =>
      rw [hq]
      have htd : cycleRiseBlockTailDepth d r ≤ P := by
        have htd1 : 1 ≤ cycleRiseBlockTailDepth d r :=
          cycleRiseBlockTailDepth_pos d r hr
        have hlt := cycleRiseBlockTailDepth_lt_succ d r hr
        omega
      by_cases htdP : cycleRiseBlockTailDepth d r = P
      · have hmod : (cycleRiseBlockTailDepth d r + 0) % P = 0 := by
          rw [htdP]
          simp
        rw [hmod]
        simp [StringFlow.Word.wordOrbit]
        have htakeP : w.take P = w :=
          List.take_of_length_le (by rw [d.hperiod])
        rw [htdP]
        rw [htakeP]
        exact d.hclosed
      · have htdlt : cycleRiseBlockTailDepth d r < P := by omega
        have hmod : (cycleRiseBlockTailDepth d r + 0) % P =
            cycleRiseBlockTailDepth d r := by
          rw [Nat.add_zero]
          exact Nat.mod_eq_of_lt htdlt
        rw [hmod]
        simp [StringFlow.Word.wordOrbit]
  | succ j ih =>
      have hj' : j ≤ (d.suffixWord r).length := by omega
      have hih := ih hj'
      have hjlt : j < (d.suffixWord r).length := by omega
      have hlhs : StringFlow.Word.wordOrbit ((d.suffixWord r).take (j + 1))
            (cycleRiseBlockC3TailState d r) =
          (5 * StringFlow.Word.wordOrbit ((d.suffixWord r).take j)
              (cycleRiseBlockC3TailState d r) + 1) /
            2 ^ (d.suffixWord r).getI j := by
        exact wordOrbit_take_succ (d.suffixWord r)
          (cycleRiseBlockC3TailState d r) j hjlt
      have hmodStep : (cycleRiseBlockTailDepth d r + (j + 1)) % P =
          (((cycleRiseBlockTailDepth d r + j) % P) + 1) % P := by
        rw [show cycleRiseBlockTailDepth d r + (j + 1) =
            (cycleRiseBlockTailDepth d r + j) + 1 by omega]
        rw [Nat.add_mod]
        rw [Nat.add_mod]
        norm_num
      have hrhs : StringFlow.Word.wordOrbit
            (w.take ((cycleRiseBlockTailDepth d r + (j + 1)) % P)) m =
          (5 * StringFlow.Word.wordOrbit
              (w.take ((cycleRiseBlockTailDepth d r + j) % P)) m + 1) /
            2 ^ w.getI ((cycleRiseBlockTailDepth d r + j) % P) := by
        rw [hmodStep]
        exact wordOrbit_take_succ_mod_of_closed d.hperiod d.hclosed
          ((cycleRiseBlockTailDepth d r + j) % P)
          (Nat.mod_lt (cycleRiseBlockTailDepth d r + j) hPpos)
      have hwget : (d.suffixWord r).getI j =
          w.getI ((cycleRiseBlockTailDepth d r + j) % P) :=
        d.hsuffix_segment r hr j hjlt
      rw [hlhs, hrhs, hih, hwget]

/-- The endpoint of the rise suffix of a cyclic rise block is the
state at the next cyclic block head, with the final block wrapping.  In
the wrapping block the suffix covers the tail of `w` plus the prefix of
length `headDepth 0`, so the endpoint is the block-`0` head state
`wordOrbit (w.take (headDepth 0)) m`, not the periodic-start state. -/
theorem cycleRiseBlockSuffixEndpoint_eq_nextHead
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    cycleRiseBlockSuffixEndpointState d r =
      cycleRiseBlockNextHeadState d r := by
  let len := (d.suffixWord r).length
  have hpre := suffixWord_prefix_eq_word_prefix_mod d r hr len (le_rfl)
  have hpre' : StringFlow.Word.wordOrbit (d.suffixWord r)
        (cycleRiseBlockC3TailState d r) =
      StringFlow.Word.wordOrbit
        (w.take ((cycleRiseBlockTailDepth d r + len) % P)) m := by
    dsimp [len] at hpre ⊢
    rw [List.take_of_length_le (le_refl (d.suffixWord r).length)] at hpre
    exact hpre
  have hsuff : cycleRiseBlockSuffixEndpointState d r =
      StringFlow.Word.wordOrbit
        (w.take ((cycleRiseBlockTailDepth d r + len) % P)) m := by
    dsimp [cycleRiseBlockSuffixEndpointState, len]
    rw [riseRun_eq_wordOrbit]
    exact hpre'
  by_cases hrnext : r + 1 < d.blockCount
  · have hnext' : cycleRiseBlockTailDepth d r + len = d.headDepth (r + 1) := by
      have h := d.hnext r hr
      dsimp [cycleRiseBlockTailDepth, len]
      rw [if_pos hrnext] at h
      exact h.symm
    have hmod : (cycleRiseBlockTailDepth d r + len) % P =
        d.headDepth (r + 1) := by
      rw [hnext']
      exact Nat.mod_eq_of_lt (d.hhead_lt (r + 1) hrnext)
    have hrhs : cycleRiseBlockNextHeadState d r =
        StringFlow.Word.wordOrbit (w.take (d.headDepth (r + 1))) m := by
      dsimp [cycleRiseBlockNextHeadState, cycleRiseBlockNextHeadDepth]
      rw [if_pos hrnext]
      rw [Nat.mod_eq_of_lt (d.hhead_lt (r + 1) hrnext)]
    rw [hsuff, hmod, hrhs]
  · have hpos : 0 < d.blockCount := by omega
    have hnext' : cycleRiseBlockTailDepth d r + len = d.headDepth 0 + P := by
      have h := d.hnext r hr
      dsimp [cycleRiseBlockTailDepth, len]
      rw [if_neg hrnext] at h
      exact h.symm
    have h0lt : d.headDepth 0 < P := d.hhead_lt 0 hpos
    have hmod : (cycleRiseBlockTailDepth d r + len) % P = d.headDepth 0 := by
      rw [hnext']
      have hmod0 : (d.headDepth 0 + P) % P = d.headDepth 0 % P := by
        rw [Nat.add_mod, Nat.mod_self]
        simp
      rw [hmod0]
      exact Nat.mod_eq_of_lt h0lt
    have hrhs : cycleRiseBlockNextHeadState d r =
        StringFlow.Word.wordOrbit (w.take (d.headDepth 0)) m := by
      dsimp [cycleRiseBlockNextHeadState, cycleRiseBlockNextHeadDepth]
      rw [if_neg hrnext]
      have hmod0 : (d.headDepth 0 + P) % P = d.headDepth 0 % P := by
        rw [Nat.add_mod, Nat.mod_self]
        simp
      rw [hmod0, Nat.mod_eq_of_lt h0lt]
    rw [hsuff, hmod, hrhs]

/-- The end of a block's C3 chain is a genuine cyclic C3-to-rise
boundary: the last C3 entry is at least three and the following rise
suffix starts with an entry one or two.  This is the exact structural
input needed to attach the real boundary terminal to the cyclic
failure-window machinery. -/
theorem cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ []) :
    IsCyclicC3RiseBoundaryAt w (cycleRiseBlockTailDepth d r) := by
  have hbpos : 1 ≤ cycleRiseBlockTailDepth d r :=
    cycleRiseBlockTailDepth_pos d r hr
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ P := by omega
  have hPpos : 0 < P := by omega
  have hlenpos : 0 < w.length := by
    rw [d.hperiod]
    exact hPpos
  have hbcase : cycleRiseBlockTailDepth d r = w.length ∨
      (1 ≤ cycleRiseBlockTailDepth d r ∧
        cycleRiseBlockTailDepth d r < w.length) := by
    by_cases hlt : cycleRiseBlockTailDepth d r < P
    · right
      constructor
      · exact hbpos
      · rw [d.hperiod]
        exact hlt
    · left
      have heq : cycleRiseBlockTailDepth d r = P := by omega
      rw [d.hperiod]
      exact heq
  have hprev3 : 3 ≤ w.getI (cycleRiseBlockTailDepth d r - 1) := by
    have hCpos : 0 < (d.c3Word r).length :=
      List.length_pos_iff.mpr (d.hc3_nonempty r hr)
    have hk : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
    have hseg := d.hc3_segment r hr ((d.c3Word r).length - 1) hk
    have hidx : d.headDepth r + ((d.c3Word r).length - 1) =
        cycleRiseBlockTailDepth d r - 1 := by
      dsimp [cycleRiseBlockTailDepth]
      omega
    rw [hidx] at hseg
    have hm : (d.c3Word r).getI ((d.c3Word r).length - 1) ∈ d.c3Word r := by
      rw [List.getI_eq_getElem (l := d.c3Word r)
        (n := (d.c3Word r).length - 1) hk]
      exact List.getElem_mem hk
    have hge := d.hc3_entries r hr
      ((d.c3Word r).getI ((d.c3Word r).length - 1)) hm
    rwa [hseg] at hge
  have hnext12 : w.getI (cycleRiseBlockTailDepth d r % w.length) = 1 ∨
      w.getI (cycleRiseBlockTailDepth d r % w.length) = 2 := by
    have hk : 0 < (d.suffixWord r).length := List.length_pos_iff.mpr hne
    have hseg := d.hsuffix_segment r hr 0 hk
    have hmod : (d.headDepth r + (d.c3Word r).length + 0) % P =
        (d.headDepth r + (d.c3Word r).length) % P := by
      simp
    rw [hmod] at hseg
    rw [d.hperiod]
    dsimp [cycleRiseBlockTailDepth]
    have hm : (d.suffixWord r).getI 0 ∈ d.suffixWord r := by
      rw [List.getI_eq_getElem (l := d.suffixWord r) (n := 0) hk]
      exact List.getElem_mem hk
    rcases d.hsuffix_one_two r hr ((d.suffixWord r).getI 0) hm with h1 | h2
    · left
      rw [← hseg]
      exact h1
    · right
      rw [← hseg]
      exact h2
  exact ⟨hlenpos, hbcase, hprev3, hnext12⟩

/-- The rise suffix of a cyclic rise block is exactly the prefix of
the cyclic rotation at the block's C3-tail depth.  This is the
wrap-invariant word alignment used by the failure-window assembly. -/
theorem cycleRiseBlockSuffixWord_eq_cyclic_take
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hLle : (d.suffixWord r).length ≤ w.length) :
    d.suffixWord r =
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        (d.suffixWord r).length := by
  have hbpos : 1 ≤ cycleRiseBlockTailDepth d r :=
    cycleRiseBlockTailDepth_pos d r hr
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hlen : (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).length =
      w.length :=
    cyclicSegmentAt_length w (cycleRiseBlockTailDepth d r) hble
  refine List.ext_getElem ?_ ?_
  · rw [List.length_take_of_le
      (l := cyclicSegmentAt w (cycleRiseBlockTailDepth d r))
      (by simpa [hlen] using hLle)]
  · intro k hk1 hk2
    have hklt : k < w.length := by omega
    have hseg := d.hsuffix_segment r hr k hk1
    have hrot := cyclicSegmentAt_getI_mod w (cycleRiseBlockTailDepth d r) k
      hble hklt
    have hsegP : (d.suffixWord r).getI k =
        w.getI ((cycleRiseBlockTailDepth d r + k) % P) := by
      dsimp [cycleRiseBlockTailDepth] at hseg ⊢
      exact hseg
    have hmain : (d.suffixWord r).getI k =
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length).getI k := by
      calc
        (d.suffixWord r).getI k = w.getI ((cycleRiseBlockTailDepth d r + k) % P) := hsegP
        _ = w.getI ((cycleRiseBlockTailDepth d r + k) % w.length) := by
          rw [d.hperiod]
        _ = (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI k := hrot.symm
        _ = ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
            (d.suffixWord r).length).getI k := by
          rw [List.getI_eq_getElem
            (l := cyclicSegmentAt w (cycleRiseBlockTailDepth d r))
            (n := k) (by simpa [hlen] using hklt)]
          rw [List.getI_eq_getElem
            (l := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
              (d.suffixWord r).length) (n := k) hk2]
          rw [← List.getElem_take]
    rw [← List.getI_eq_getElem (l := d.suffixWord r) (n := k) hk1]
    rw [← List.getI_eq_getElem
      (l := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        (d.suffixWord r).length) (n := k) hk2]
    exact hmain

/-- The word entry after a block's rise suffix is a C3 entry: in the
non-wrapping case it is the first entry of the next block's C3 chain,
and in the wrapping case it is the first entry of block zero.  This is
the exact stop condition of the cyclic rise run. -/
theorem cycleRiseBlockSuffixStopC3
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hLlt : (d.suffixWord r).length < w.length) :
    3 ≤ (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
      (d.suffixWord r).length := by
  have hpos : 0 < d.blockCount := by omega
  have hbpos : 1 ≤ cycleRiseBlockTailDepth d r :=
    cycleRiseBlockTailDepth_pos d r hr
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hrot := cyclicSegmentAt_getI_mod w (cycleRiseBlockTailDepth d r)
    (d.suffixWord r).length hble hLlt
  by_cases hrnext : r + 1 < d.blockCount
  · have hnext' : cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
        d.headDepth (r + 1) := by
      have h := d.hnext r hr
      dsimp [cycleRiseBlockTailDepth]
      rw [if_pos hrnext] at h
      exact h.symm
    have hmod : (d.headDepth (r + 1)) % P = d.headDepth (r + 1) :=
      Nat.mod_eq_of_lt (d.hhead_lt (r + 1) hrnext)
    have hk0 : 0 < (d.c3Word (r + 1)).length :=
      List.length_pos_iff.mpr (d.hc3_nonempty (r + 1) hrnext)
    have hseg0 := d.hc3_segment (r + 1) hrnext 0 hk0
    have hge0 := d.hc3_entries (r + 1) hrnext
      ((d.c3Word (r + 1)).getI 0)
      (by
        rw [List.getI_eq_getElem (l := d.c3Word (r + 1)) (n := 0) hk0]
        exact List.getElem_mem hk0)
    rw [hrot]
    rw [d.hperiod]
    rw [hnext']
    rw [hmod]
    simpa [hseg0] using hge0
  · have hnext' : cycleRiseBlockTailDepth d r + (d.suffixWord r).length =
        d.headDepth 0 + P := by
      have h := d.hnext r hr
      dsimp [cycleRiseBlockTailDepth]
      rw [if_neg hrnext] at h
      exact h.symm
    have h0lt : d.headDepth 0 < P := d.hhead_lt 0 hpos
    have hmod : (d.headDepth 0 + P) % P = d.headDepth 0 := by
      rw [Nat.add_mod, Nat.mod_self]
      have h0m : d.headDepth 0 % P = d.headDepth 0 :=
        Nat.mod_eq_of_lt h0lt
      simp [h0m]
    have hk0 : 0 < (d.c3Word 0).length :=
      List.length_pos_iff.mpr (d.hc3_nonempty 0 hpos)
    have hseg0 := d.hc3_segment 0 hpos 0 hk0
    have hge0 := d.hc3_entries 0 hpos
      ((d.c3Word 0).getI 0)
      (by
        rw [List.getI_eq_getElem (l := d.c3Word 0) (n := 0) hk0]
        exact List.getElem_mem hk0)
    rw [hrot]
    rw [d.hperiod]
    rw [hnext']
    rw [hmod]
    simpa [hseg0] using hge0

/-- Every entry of a block's rise suffix is a rise entry one or two in
the cyclic rotation at the block's C3-tail depth.  This supplies the
`hall` input of the cyclic failure-window assembly. -/
theorem cycleRiseBlockSuffixHall
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hLle : (d.suffixWord r).length ≤ w.length)
    (k : Nat) (hk : k < (d.suffixWord r).length) :
    (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI k = 1 ∨
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI k = 2 := by
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hklt : k < w.length := by omega
  have hrot := cyclicSegmentAt_getI_mod w (cycleRiseBlockTailDepth d r) k
    hble hklt
  have hseg := d.hsuffix_segment r hr k hk
  rw [hrot]
  rw [d.hperiod]
  dsimp [cycleRiseBlockTailDepth]
  rw [← hseg]
  have hm : (d.suffixWord r).getI k ∈ d.suffixWord r := by
    rw [List.getI_eq_getElem (l := d.suffixWord r) (n := k) hk]
    exact List.getElem_mem hk
  rcases d.hsuffix_one_two r hr ((d.suffixWord r).getI k) hm with h1 | h2
  · left
    exact h1
  · right
    exact h2

/-- The last entry of a block's rise suffix is the corresponding entry
of the cyclic rotation.  This supplies the `ht_last` input of the
cyclic failure-window assembly. -/
theorem cycleRiseBlockSuffixLastStep
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLpos : 1 ≤ (d.suffixWord r).length)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    (d.suffixWord r).getI ((d.suffixWord r).length - 1) =
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
        ((d.suffixWord r).length - 1) := by
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hk : (d.suffixWord r).length - 1 < (d.suffixWord r).length := by omega
  have hklt : (d.suffixWord r).length - 1 < w.length := by omega
  have hseg := d.hsuffix_segment r hr ((d.suffixWord r).length - 1) hk
  have hrot := cyclicSegmentAt_getI_mod w (cycleRiseBlockTailDepth d r)
    ((d.suffixWord r).length - 1) hble hklt
  rw [hseg]
  rw [hrot]
  dsimp [cycleRiseBlockTailDepth]
  rw [d.hperiod]

/-- The maximality stop of a block's rise suffix: either the suffix
fills the whole period or the next rotated entry is a C3 entry.  This
is the wrap-invariant form of the `hstop` input of the cyclic
failure-window assembly. -/
theorem cycleRiseBlockSuffixStopOr
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hLlt : (d.suffixWord r).length < w.length) :
    (d.suffixWord r).length = w.length ∨
      3 ≤ (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
        (d.suffixWord r).length := by
  right
  exact cycleRiseBlockSuffixStopC3 d r hr hLlt

/-- Assemble the fully cyclic failure window from a cyclic rise block.
The block's C3-tail depth supplies the boundary, the rise suffix is the
local word, and the maximality stop is the following C3 entry; only the
genuine reset terminal (`hrt`, `hterm`, `hk`, `hslt`) and the failure
lower bounds (`hfail_t1`, `hfail_t2`) remain as inputs.  These are
exactly the data that real orbit reachability and the block-layer PMI
must supply. -/
theorem cyclicDepthFailureWindow_of_cycleRiseBlock
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hne : d.suffixWord r ≠ [])
    (hLlt : (d.suffixWord r).length < w.length)
    (t delta : Nat) (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hk : rt.k + 1 ≤ (d.suffixWord r).length)
    (hslt : rt.s < 5 ^ ((d.suffixWord r).length - rt.k - 1))
    (hfail_t1 : t = 1 → 2 * (d.suffixWord r).length + 12 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s +
        5 ^ (d.suffixWord r).length - 2))
    (hfail_t2 : t = 2 → 2 * (d.suffixWord r).length + 11 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s +
        delta * 5 ^ (d.suffixWord r).length)) :
    RealOrbitLocalLemma.CyclicDepthFailureWindow m S P w rise c3
      (cycleRiseBlockTailDepth d r) (d.suffixWord r).length t delta rt := by
  have hb := cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  have hLpos : 1 ≤ (d.suffixWord r).length := List.length_pos_iff.mpr hne
  have hLle : (d.suffixWord r).length ≤ w.length := by omega
  have hlast := cycleRiseBlockSuffixLastStep d r hr hLpos hLle
  have ht_last' : t =
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
        ((d.suffixWord r).length - 1) := by
    rw [← hlast]
    exact ht_last
  exact RealOrbitLocalLemma.cyclic_local_block_to_cyclicDepthFailureWindow
    h (cycleRiseBlockTailDepth d r) (d.suffixWord r).length t delta
    hb hLpos hLle rt hrt ht_last' ht hdelta hterm hk hslt hfail_t1 hfail_t2

/-- A fully sourced failure window at a cyclic rise block is
impossible: the following C3 entry fixes the head rank at two, which
contradicts the failure lower bounds.  This is the exact-structure
contradiction behind the failure-window route; it needs no decisive
window bound and no large-depth rank estimate. -/
theorem cycleRiseBlockWindowFalse
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hne : d.suffixWord r ≠ [])
    (hLlt : (d.suffixWord r).length < w.length)
    (t delta : Nat) (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hk : rt.k + 1 ≤ (d.suffixWord r).length)
    (hslt : rt.s < 5 ^ ((d.suffixWord r).length - rt.k - 1))
    (hfail_t1 : t = 1 → 2 * (d.suffixWord r).length + 12 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s +
        5 ^ (d.suffixWord r).length - 2))
    (hfail_t2 : t = 2 → 2 * (d.suffixWord r).length + 11 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s +
        delta * 5 ^ (d.suffixWord r).length)) :
    False := by
  have fw := cyclicDepthFailureWindow_of_cycleRiseBlock
    h d r hr hne hLlt t delta rt hrt ht_last ht hdelta hterm hk hslt
    hfail_t1 hfail_t2
  exact RealOrbitLocalLemma.cyclicDepthFailureWindow_false_of_outgoing_c3
    fw hLlt (cycleRiseBlockSuffixStopC3 d r hr hLlt)

/-- Every cyclic rise block has a genuine real terminal at the depth
before its C3-tail boundary.  This is the real orbit reachability that
supplies the `hrt` input of the cyclic failure-window assembly: the
terminal is constructed from the actual word prefix, not assumed. -/
theorem cycleRiseBlockRealTerminal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
      rt.r = (5 * StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2 := by
  have hbpos : 1 ≤ cycleRiseBlockTailDepth d r :=
    cycleRiseBlockTailDepth_pos d r hr
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hprev3 : 3 ≤ w.getI (cycleRiseBlockTailDepth d r - 1) := by
    have hCpos : 0 < (d.c3Word r).length :=
      List.length_pos_iff.mpr (d.hc3_nonempty r hr)
    have hk : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
    have hseg := d.hc3_segment r hr ((d.c3Word r).length - 1) hk
    have hidx : d.headDepth r + ((d.c3Word r).length - 1) =
        cycleRiseBlockTailDepth d r - 1 := by
      dsimp [cycleRiseBlockTailDepth]
      omega
    rw [hidx] at hseg
    have hm : (d.c3Word r).getI ((d.c3Word r).length - 1) ∈ d.c3Word r := by
      rw [List.getI_eq_getElem (l := d.c3Word r)
        (n := (d.c3Word r).length - 1) hk]
      exact List.getElem_mem hk
    have hge := d.hc3_entries r hr
      ((d.c3Word r).getI ((d.c3Word r).length - 1)) hm
    rwa [hseg] at hge
  exact cycleQb8Input_angelina_real_terminal h (cycleRiseBlockTailDepth d r)
    hbpos hble hprev3

/-- Cycle closure of the rotated word: the rise-start state
`q = wordOrbit (w.take b) m` satisfies
`q * (2^S - 5^P) = wordA (cyclicSegmentAt w b)`.
This is the exact form in which the closed cycle word enters the
`hpred` word equation: it determines `q` without any size estimate. -/
theorem cycleQb8Input_rotated_wordA
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) (b : Nat) (hb : b ≤ w.length) :
    StringFlow.Word.wordOrbit (w.take b) m * (2 ^ S - 5 ^ P) =
      StringFlow.Word.wordA (cyclicSegmentAt w b) := by
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hclosed_rot : StringFlow.Word.wordOrbit (cyclicSegmentAt w b) q = q := by
    dsimp [q]
    exact cyclicSegmentAt_closed h b
  have hvalid_rot : StringFlow.Word.wordValid (cyclicSegmentAt w b) q := by
    dsimp [q]
    exact cyclicSegmentAt_valid h b
  have hid := StringFlow.Word.word_orbit_identity (cyclicSegmentAt w b) q hvalid_rot
  have hlen_rot : (cyclicSegmentAt w b).length = P := by
    rw [cyclicSegmentAt_length w b hb, h.hlength]
  have hweight_rot : StringFlow.wordWeight (cyclicSegmentAt w b) = S := by
    unfold cyclicSegmentAt
    have hsplit : w.take b ++ w.drop b = w := List.take_append_drop b w
    have hww := StringFlow.Word.wordWeight_append (w.drop b) (w.take b)
    rw [hww]
    rw [← h.hweight]
    have hww' := StringFlow.Word.wordWeight_append (w.take b) (w.drop b)
    rw [hsplit] at hww'
    rw [Nat.add_comm]
    exact hww'.symm
  rw [hweight_rot, hlen_rot] at hid
  rw [hclosed_rot] at hid
  have hqpos : 0 < q := by
    dsimp [q]
    have hreach : S6Audit.FullOrbitFrom7
        (StringFlow.Word.wordOrbit (w.take b) m) :=
      cycleQb8Input_prefix_full_reachable h b hb
    have hodd : S6Audit.IsOdd (StringFlow.Word.wordOrbit (w.take b) m) :=
      S6Audit.FullOrbitFrom7_odd _ hreach
    by_contra hnot
    have hz : StringFlow.Word.wordOrbit (w.take b) m = 0 := by omega
    rw [hz] at hodd
    norm_num [S6Audit.IsOdd] at hodd
  have hsub : 2 ^ S * q - 5 ^ P * q =
      StringFlow.Word.wordA (cyclicSegmentAt w b) := by
    have h : 5 ^ P * q + StringFlow.Word.wordA (cyclicSegmentAt w b) =
        2 ^ S * q := by
      simpa [Nat.add_comm] using hid.symm
    omega
  have hgoal : q * (2 ^ S - 5 ^ P) =
      StringFlow.Word.wordA (cyclicSegmentAt w b) := by
    rw [Nat.mul_comm]
    rw [Nat.mul_sub_right_distrib]
    exact hsub
  dsimp [q] at hgoal ⊢
  exact hgoal

/-- Exact numerator decomposition over concatenation:
`wordA (v ++ u)` keeps the `u`-terms at their own positions and
multiplies the `v`-numerator by `5^|u|`, with the `v`-prefix weights
shifted by `weight u` positions. -/
theorem wordA_append (v u : List Nat) :
    StringFlow.Word.wordA (v ++ u) =
      5 ^ u.length * StringFlow.Word.wordA v +
        ((List.range u.length).map
          (fun j => 5 ^ (u.length - 1 - j) *
            2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight (u.take j)))).sum := by
  induction u using List.reverseRecOn with
  | nil =>
      simp [StringFlow.Word.wordA, StringFlow.wordWeight]
  | append_singleton u0 t ih =>
      let m := u0.length
      have hstep := StringFlow.Word.wordA_append_singleton (v ++ u0) t
      have hweight := StringFlow.Word.wordWeight_append v u0
      have hlen : (u0 ++ [t]).length = m + 1 := by
        dsimp [m]
        simp
      have htake : ∀ j, j ≤ m →
          ((u0 ++ [t]).take j) = u0.take j := by
        intro j hj
        exact List.take_append_of_le_length (l₁ := u0) (l₂ := [t]) (i := j)
          (by simpa [m] using hj)
      have hlast : ((u0 ++ [t]).take (m + 1)) = u0 ++ [t] := by
        exact List.take_of_length_le (by simpa [hlen])
      have ih' : StringFlow.Word.wordA (v ++ u0) =
          5 ^ m * StringFlow.Word.wordA v +
            ((List.range m).map
              (fun j => 5 ^ (m - 1 - j) *
                2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight (u0.take j)))).sum := by
        simpa [m] using ih
      rw [← List.append_assoc]
      rw [hstep, hweight, ih']
      rw [hlen]
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [hlen, htake, hlast, m, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      rw [Nat.mul_add]
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc, Nat.mul_comm 5 (5 ^ u0.length)]
      rw [← StringFlow.PMI.sum_map_mul_left (List.range m) 5
        (fun j => 5 ^ (m - 1 - j) *
          2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight (u0.take j)))]
      congr 1
      change (List.map (fun j => 5 * (5 ^ (m - 1 - j) *
          2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight (u0.take j))))
            (List.range m)).sum =
        (List.map (fun j => 5 ^ (m - j) *
          2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight ((u0 ++ [t]).take j)))
            (List.range m)).sum
      apply congrArg List.sum
      apply List.map_congr_left
      intro j hj
      have hjlt : j < m := (List.mem_range.mp hj)
      have hjle : j ≤ m := le_of_lt hjlt
      rw [htake j hjle]
      have hsub : m - j = (m - 1 - j) + 1 := by omega
      rw [hsub, Nat.pow_succ]
      ring

/-- Shifted form of `wordA_append`: appending `u` multiplies the
`v`-numerator by `5^|u|` and the `u`-numerator by `2^weight v`.
This is the exact block-partition identity used to decompose the
whole-cycle `wordA` into the cyclic rise blocks. -/
theorem wordA_append_shift (v u : List Nat) :
    StringFlow.Word.wordA (v ++ u) =
      5 ^ u.length * StringFlow.Word.wordA v +
        2 ^ StringFlow.wordWeight v * StringFlow.Word.wordA u := by
  induction u using List.reverseRecOn with
  | nil =>
      simp [StringFlow.Word.wordA, StringFlow.wordWeight]
  | append_singleton u0 t ih =>
      have hstep := StringFlow.Word.wordA_append_singleton (v ++ u0) t
      have hweight := StringFlow.Word.wordWeight_append v u0
      have hlen : (u0 ++ [t]).length = u0.length + 1 := by simp
      have hlast : StringFlow.Word.wordA (u0 ++ [t]) =
          5 * StringFlow.Word.wordA u0 + 2 ^ StringFlow.wordWeight u0 :=
        StringFlow.Word.wordA_append_singleton u0 t
      calc
        StringFlow.Word.wordA (v ++ (u0 ++ [t]))
            = StringFlow.Word.wordA ((v ++ u0) ++ [t]) := by
                rw [← List.append_assoc]
        _ = 5 * StringFlow.Word.wordA (v ++ u0) +
              2 ^ StringFlow.wordWeight (v ++ u0) := hstep
        _ = 5 * (5 ^ u0.length * StringFlow.Word.wordA v +
              2 ^ StringFlow.wordWeight v * StringFlow.Word.wordA u0) +
              2 ^ (StringFlow.wordWeight v + StringFlow.wordWeight u0) := by
                rw [ih, hweight]
        _ = 5 ^ (u0.length + 1) * StringFlow.Word.wordA v +
              2 ^ StringFlow.wordWeight v *
                (5 * StringFlow.Word.wordA u0 + 2 ^ StringFlow.wordWeight u0) := by ring
        _ = 5 ^ (u0 ++ [t]).length * StringFlow.Word.wordA v +
              2 ^ StringFlow.wordWeight v * StringFlow.Word.wordA (u0 ++ [t]) := by
                rw [hlen, hlast]

/-- Exact `wordA` expansion of one cyclic rise block segment
`c3Word r ++ suffixWord r`: the C3 numerator is shifted by the suffix
length, and the suffix contributes its own power-of-two terms at the
local prefix weights.  This is the block-level entry to the sum lower
bound `Σ R_r ≥ 2Σ b_r + 13K`. -/
theorem cycleRiseBlockSegment_wordA_expansion
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) :
    StringFlow.Word.wordA (d.c3Word r ++ d.suffixWord r) =
      5 ^ (d.suffixWord r).length * StringFlow.Word.wordA (d.c3Word r) +
        ((List.range (d.suffixWord r).length).map
          (fun j => 5 ^ ((d.suffixWord r).length - 1 - j) *
          2 ^ (StringFlow.wordWeight (d.c3Word r) +
               StringFlow.wordWeight ((d.suffixWord r).take j)))).sum :=
  wordA_append (d.c3Word r) (d.suffixWord r)

/-- The cyclic rotation at a block's C3-tail depth starts with the
block's rise suffix, followed by the rotated remainder.  This is the
wrap-invariant decomposition used to expand
`cycleQb8Input_rotated_wordA` block by block. -/
theorem cyclicSegmentAt_tail_eq_suffix_append
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hwpos : 0 < w.length) :
    cyclicSegmentAt w (cycleRiseBlockTailDepth d r) =
      d.suffixWord r ++
        (cyclicSegmentAt w
          ((cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % w.length)).take
            (w.length - (d.suffixWord r).length) := by
  let b := cycleRiseBlockTailDepth d r
  let L := (d.suffixWord r).length
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
      cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hL : L ≤ w.length := hLle
  have htake : d.suffixWord r = (cyclicSegmentAt w b).take L := by
    dsimp [b, L]
    exact cycleRiseBlockSuffixWord_eq_cyclic_take d r hr hLle
  have hsplit : cyclicSegmentAt w b =
      (cyclicSegmentAt w b).take L ++ (cyclicSegmentAt w b).drop L :=
    (List.take_append_drop L (cyclicSegmentAt w b)).symm
  have hdrop := cyclicSegmentAt_drop_take w b L hb hL
  calc
    cyclicSegmentAt w b = (cyclicSegmentAt w b).take L ++
        (cyclicSegmentAt w b).drop L := hsplit
    _ = d.suffixWord r ++
          (cyclicSegmentAt w ((b + L) % w.length)).take
            (w.length - L) := by
        rw [hdrop hwpos]
        rw [htake]

/-- The rotated-word cycle closure at a block's C3-tail boundary is
the `wordA` of `suffixWord r` followed by the rotated remainder.  This
instantiates `cycleQb8Input_rotated_wordA` on the block decomposition. -/
theorem cycleRiseBlockRotatedWordA_eq_suffix_append
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m * (2 ^ S - 5 ^ P) =
      StringFlow.Word.wordA
        (d.suffixWord r ++
          (cyclicSegmentAt w
            ((cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % w.length)).take
              (w.length - (d.suffixWord r).length)) := by
  have hwpos : 0 < w.length := by
    have hP : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    rw [d.hperiod]
    omega
  have hb : cycleRiseBlockTailDepth d r ≤ w.length := by
    have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
      cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  rw [← cyclicSegmentAt_tail_eq_suffix_append d r hr hLle hwpos]
  exact cycleQb8Input_rotated_wordA h (cycleRiseBlockTailDepth d r) hb

/-- Exact suffix-side expansion of the same rotated-word identity:
the boundary-state term equals the shifted `wordA` of the rise suffix
plus the local power-of-two suffix terms. -/
theorem cycleRiseBlockRotatedWordA_suffix_expansion
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hLle : (d.suffixWord r).length ≤ w.length) :
    StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m * (2 ^ S - 5 ^ P) =
      5 ^ (w.length - (d.suffixWord r).length) *
          StringFlow.Word.wordA (d.suffixWord r) +
        ((List.range (w.length - (d.suffixWord r).length)).map
          (fun j => 5 ^ (w.length - (d.suffixWord r).length - 1 - j) *
          2 ^ (StringFlow.wordWeight (d.suffixWord r) +
               StringFlow.wordWeight
                   ((cyclicSegmentAt w
                     ((cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % w.length)).take j)))).sum := by
  have hwpos : 0 < w.length := by
    have hP : 2 ≤ P := CycleBridge.cycleQb8Input_P_ge_two h
    rw [d.hperiod]
    omega
  let mid := (cycleRiseBlockTailDepth d r + (d.suffixWord r).length) % w.length
  have hb_mid : mid ≤ w.length := by
    dsimp [mid]
    exact le_of_lt (Nat.mod_lt _ hwpos)
  have hlen_mid : (cyclicSegmentAt w mid).length = w.length :=
    cyclicSegmentAt_length w mid hb_mid
  have hrest_len : ((cyclicSegmentAt w mid).take
      (w.length - (d.suffixWord r).length)).length =
      w.length - (d.suffixWord r).length := by
    rw [List.length_take_of_le]
    rw [hlen_mid]
    exact Nat.sub_le _ _
  rw [cycleRiseBlockRotatedWordA_eq_suffix_append h d r hr hLle]
  rw [wordA_append]
  rw [hrest_len]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjlt : j < w.length - (d.suffixWord r).length := List.mem_range.mp hj
  have htake : (cyclicSegmentAt w mid).take j =
      ((cyclicSegmentAt w mid).take (w.length - (d.suffixWord r).length)).take j := by
    rw [List.take_take]
    rw [Nat.min_eq_left (le_of_lt hjlt)]
  dsimp [mid] at htake ⊢
  rw [← htake]

/-- The rise suffix `wordA` splits at its last step:
`wordA(suffix) = 5·wordA(dropLast) + 2^{weight dropLast}`.  This is the
`u = u' ++ [t]` decomposition needed to substitute the predecessor
identity `cycleRiseBlockHpred_of_real_terminal`. -/
theorem cycleRiseBlockSuffixWordA_last_step
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hne : d.suffixWord r ≠ []) :
    StringFlow.Word.wordA (d.suffixWord r) =
      5 * StringFlow.Word.wordA ((d.suffixWord r).dropLast) +
        2 ^ StringFlow.wordWeight ((d.suffixWord r).dropLast) := by
  have hsplit : d.suffixWord r =
      (d.suffixWord r).dropLast ++ [StringFlow.Word.wordLast (d.suffixWord r)] :=
    S6Audit.word_eq_dropLast_append_last (d.suffixWord r) hne
  conv_lhs => rw [hsplit]
  exact StringFlow.Word.wordA_append_singleton ((d.suffixWord r).dropLast)
    (StringFlow.Word.wordLast (d.suffixWord r))

/-- The rise suffix splits as `dropLast ++ [last]`, so the dropLast
prefix has length `L-1`.  This is the `u'` length needed by
`cycleRiseBlockHpred_of_real_terminal`. -/
theorem cycleRiseBlockSuffixDropLast_length
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hne : d.suffixWord r ≠ []) :
    (d.suffixWord r).dropLast.length = (d.suffixWord r).length - 1 := by
  have hsplit := S6Audit.word_eq_dropLast_append_last (d.suffixWord r) hne
  have hlen : (d.suffixWord r).length =
      (d.suffixWord r).dropLast.length + 1 := by
    have h := congrArg List.length hsplit
    simpa [List.length_append] using h
  omega

/-- The rise suffix's `dropLast` equals the cyclic rotation's
`take (L-1)`: the two `u'` forms in `cycleRiseBlockSuffixWordA_last_step`
and `cycleRiseBlockWordA_prefix_add` are the same list. -/
theorem cycleRiseBlockSuffixDropLast_eq_cyclic_take
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length) :
    (d.suffixWord r).dropLast =
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        ((d.suffixWord r).length - 1) := by
  have htake := cycleRiseBlockSuffixWord_eq_cyclic_take d r hr hLle
  rw [htake]
  have h1 := List.dropLast_take_eq_take_dropLast
    (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)) ((d.suffixWord r).length)
  rw [h1]
  have hLpos : 0 < (d.suffixWord r).length := List.length_pos_iff.mpr hne
  have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
    cycleRiseBlockTailDepth_lt_succ d r hr
  have hble : cycleRiseBlockTailDepth d r ≤ w.length := by
    rw [d.hperiod]
    omega
  have hseg_len : (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).length =
      w.length :=
    cyclicSegmentAt_length w (cycleRiseBlockTailDepth d r) hble
  have htake_len : (List.take ((d.suffixWord r).length)
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r))).length =
      (d.suffixWord r).length := by
    rw [List.length_take_of_le]
    rw [hseg_len]
    exact hLle
  have hLle' : (d.suffixWord r).length - 1 ≤
      (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).length - 1 := by
    rw [hseg_len]
    omega
  rw [htake_len]
  rw [List.dropLast_eq_take]
  rw [List.take_take]
  rw [Nat.min_eq_left hLle']

/-- The last entry of `u ++ [t]` is `t`. -/
lemma wordLast_append_singleton (u : List Nat) (t : Nat) :
    StringFlow.Word.wordLast (u ++ [t]) = t := by
  induction u with
  | nil => simp [StringFlow.Word.wordLast]
  | cons a as ih =>
      cases as with
      | nil => simp [StringFlow.Word.wordLast]
      | cons b bs =>
          change StringFlow.Word.wordLast ((b :: bs) ++ [t]) = t
          exact ih

/-- The suffix weight splits as `weight dropLast + last`, matching the
`u = u' ++ [t]` decomposition of the predecessor identity. -/
theorem cycleRiseBlockSuffixWeight_last_step
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hne : d.suffixWord r ≠ []) :
    StringFlow.wordWeight (d.suffixWord r) =
      StringFlow.wordWeight ((d.suffixWord r).dropLast) +
        StringFlow.Word.wordLast (d.suffixWord r) := by
  have hsplit := S6Audit.word_eq_dropLast_append_last (d.suffixWord r) hne
  rw [hsplit]
  rw [StringFlow.Word.wordWeight_append]
  simp [StringFlow.wordWeight, wordLast_append_singleton]

/-- Direct construction of the block-head predecessor identity
(`hpred`) from the real boundary terminal and its genuine local reset
(`hterm`).  The proof instantiates the real terminal, the cyclic prefix
occurrence with its exact incoming edge, the exact word identity for
the rise prefix, the exact boundary-terminal identity
`rt.r = 2^(w[b-1]-1) * q`, and the reset alignment that turns
`IsLocalResetTerminal` into the real predecessor identity.  After this
algebraic reduction, `hpred` is exactly the word equation

`wordA u' + 5^(L-1)*q = 2^(weight u' + c - 1)*q + delta*2^(weight u')*5^(L-1)`

for the rise prefix `u'` of length `L-1`; the equation is obtained
from `hterm`, not from the cycle closure alone.  The block length must
be at least three: for `L <= 2` the conclusion would force
`rt.r + delta*5^(L-1) = o_local` with `rt.r >= 4*q` while zero or one
rise step keeps `o_local < 4*q`, so those cases are exactly the
pseudo-candidates excluded by `cyclic_local_reset_length_ge_three`.  No
size estimate and no C3-rank input is used. -/
theorem cycleRiseBlockHpred_of_real_terminal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hLge3 : 3 ≤ (d.suffixWord r).length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2) :
    5 ^ rt.k * rt.s + delta * 5 ^ ((d.suffixWord r).length - 1) - 1 =
      StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          ((d.suffixWord r).length - 1))
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m) := by
  have hLpos : 1 ≤ (d.suffixWord r).length := List.length_pos_iff.mpr hne
  have hb := cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  have hlast := cycleRiseBlockSuffixLastStep d r hr hLpos hLle
  have ht_last' : t = (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
      ((d.suffixWord r).length - 1) := by
    rw [← hlast]
    exact ht_last
  let b : Nat := cycleRiseBlockTailDepth d r
  let L : Nat := (d.suffixWord r).length
  let u' : List Nat := (cyclicSegmentAt w b).take (L - 1)
  let q : Nat := StringFlow.Word.wordOrbit (w.take b) m
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  rcases RealOrbitLocalLemma.cycleQb8Input_cyclic_prefix_occurrence_with_incoming
      h b L hble hLpos hLle with ⟨n, hn, hiter, hprev, hwWord⟩
  dsimp [b, L, u', q] at hprev ⊢
  rw [← hprev]
  have hprod : 5 ^ rt.k * rt.s = rt.r + 1 := by
    simpa [Nat.mul_comm] using rt.hprod
  have hterminal := RealOrbitLocalLemma.cycleQb8Input_boundary_terminal_eq h b hb rt hrt
  have hvalid_rot : StringFlow.Word.wordValid (cyclicSegmentAt w b) q := by
    dsimp [q]
    exact cyclicSegmentAt_valid h b
  have hsplit : cyclicSegmentAt w b = u' ++ (cyclicSegmentAt w b).drop (L - 1) := by
    dsimp [u']
    exact (List.take_append_drop (L - 1) (cyclicSegmentAt w b)).symm
  have hvalid_u' : StringFlow.Word.wordValid u' q := by
    rw [hsplit] at hvalid_rot
    exact (S6Audit.wordValid_append u' ((cyclicSegmentAt w b).drop (L - 1)) q).mp
      hvalid_rot |>.1
  -- The rise-prefix word equation is exactly
  -- `cycleQb8Input_cyclic_local_block_data` instantiated at length
  -- `L-1` (the cyclic block equation of the rise prefix `u'`).
  have hid : 2 ^ StringFlow.wordWeight u' * StringFlow.Word.wordOrbit u' q =
      5 ^ (L - 1) * q + StringFlow.Word.wordA u' := by
    by_cases hL1 : L = 1
    · subst L
      dsimp [u', q]
      simp [hL1, StringFlow.Word.wordOrbit, StringFlow.Word.wordA, StringFlow.wordWeight]
    · have hLpos' : 1 ≤ L - 1 := by omega
      have hLle' : L - 1 ≤ w.length := le_trans (Nat.sub_le L 1) hLle
      rcases cycleQb8Input_cyclic_local_block_data h b (L - 1) hb hLpos' hLle' with
        ⟨Aj', Wp', Wj', t', hAj', hWj', hWp', ht0', hW', hid', hdiv', hrjform'⟩
      change 2 ^ Wj' * StringFlow.Word.wordOrbit u' q =
          Aj' + 5 ^ (L - 1) * q at hid'
      rw [hAj', hWj'] at hid'
      simpa [u', q, Nat.add_comm] using hid'
  have hu'_len : u'.length = L - 1 := by
    dsimp [u']
    rw [List.length_take_of_le]
    · rw [cyclicSegmentAt_length w b hble]
      exact le_trans (Nat.sub_le L 1) hLle
  -- E5 is the word-equation form of the real predecessor identity.  It
  -- is derived from `hterm` through `isLocalResetTerminal_iff_resetHeadEq`
  -- and the depth-aligned predecessor lemma; the cycle closure does not
  -- force the delta-zero block property, so that real reset remains the
  -- open upstream input.
  have hE5 : StringFlow.Word.wordA u' + 5 ^ (L - 1) * q =
      2 ^ ((StringFlow.wordWeight u' + w.getI (b - 1)) - 1) * q +
        delta * 2 ^ StringFlow.wordWeight u' * 5 ^ (L - 1) := by
    have hterm' : IsLocalResetTerminal t L
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q) delta rt := by
      simpa [b, L, q] using hterm
    have hw : S6Audit.orbitStepWeight (n - 1) = t := by
      rw [hwWord, ← ht_last']
    have hreset : S6Audit.ResetHeadEq rt.s L rt.k t delta
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q) :=
      (isLocalResetTerminal_iff_resetHeadEq t L
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
        delta rt ht hdelta).mp hterm'
    have hpred := RealOrbitLocalLemma.reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
      n L rt.k t delta rt.s 0
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
        hLpos hreset hn hiter hw
    have hxprev : S6Audit.fullOrbitIter (n - 1) =
        rt.r + delta * 5 ^ (L - 1) := by
      omega
    have ho_prev : StringFlow.Word.wordOrbit u' q =
        rt.r + delta * 5 ^ (L - 1) := by
      rw [← hprev]
      exact hxprev
    rw [ho_prev] at hid
    rw [hterminal] at hid
    have hleft : 2 ^ StringFlow.wordWeight u' *
        (2 ^ (w.getI (b - 1) - 1) * q + delta * 5 ^ (L - 1)) =
        2 ^ ((StringFlow.wordWeight u' + w.getI (b - 1)) - 1) * q +
          delta * 2 ^ StringFlow.wordWeight u' * 5 ^ (L - 1) := by
      rw [Nat.mul_add]
      rw [← Nat.mul_assoc]
      rw [← Nat.pow_add]
      have hc : 1 ≤ w.getI (b - 1) := by
        have h3 : 3 ≤ w.getI (b - 1) := hb.2.2.1
        omega
      have hsub : (StringFlow.wordWeight u' + w.getI (b - 1)) - 1 =
          StringFlow.wordWeight u' + (w.getI (b - 1) - 1) := by omega
      rw [hsub]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (2 ^ StringFlow.wordWeight u') delta]
    rw [hleft] at hid
    simpa [Nat.add_comm] using hid.symm
  have heq' : 2 ^ StringFlow.wordWeight u' * StringFlow.Word.wordOrbit u' q =
      2 ^ StringFlow.wordWeight u' * (rt.r + delta * 5 ^ (L - 1)) := by
    rw [hterminal]
    rw [hid]
    have hleft : 2 ^ StringFlow.wordWeight u' *
        (2 ^ (w.getI (b - 1) - 1) * q + delta * 5 ^ (L - 1)) =
        2 ^ ((StringFlow.wordWeight u' + w.getI (b - 1)) - 1) * q +
          delta * 2 ^ StringFlow.wordWeight u' * 5 ^ (L - 1) := by
      rw [Nat.mul_add]
      rw [← Nat.mul_assoc]
      rw [← Nat.pow_add]
      have hc : 1 ≤ w.getI (b - 1) := by
        have h3 : 3 ≤ w.getI (b - 1) := hb.2.2.1
        omega
      have hsub : (StringFlow.wordWeight u' + w.getI (b - 1)) - 1 =
          StringFlow.wordWeight u' + (w.getI (b - 1) - 1) := by omega
      rw [hsub]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (2 ^ StringFlow.wordWeight u') delta]
    rw [hleft]
    simpa [Nat.add_comm] using hE5
  have heq'' : StringFlow.Word.wordOrbit u' q =
      rt.r + delta * 5 ^ (L - 1) := by
    have hpos : 0 < 2 ^ StringFlow.wordWeight u' :=
      Nat.pow_pos (by decide : 0 < 2)
    exact Nat.eq_of_mul_eq_mul_left hpos heq'
  have heq''' : 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1 =
      StringFlow.Word.wordOrbit u' q := by
    rw [heq'']
    omega
  dsimp [u', q, b, L] at heq'''
  rw [← hprev] at heq'''
  exact heq'''

/-- Combining `cycleRiseBlockHpred_of_real_terminal` with the cyclic
local block equation exposes the rise-prefix numerator as an exact
`q`-polynomial.  Addition form avoids Nat subtraction. -/
theorem cycleRiseBlockWordA_prefix_add
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hLge3 : 3 ≤ (d.suffixWord r).length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2) :
    let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        ((d.suffixWord r).length - 1)
    let q := StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m
    StringFlow.Word.wordA u' +
        5 ^ ((d.suffixWord r).length - 1) * q =
      2 ^ StringFlow.wordWeight u' *
        (5 ^ rt.k * rt.s +
          delta * 5 ^ ((d.suffixWord r).length - 1) - 1) := by
  let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
      ((d.suffixWord r).length - 1)
  let q := StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r)) m
  have hpred := cycleRiseBlockHpred_of_real_terminal h d r hr hne hLle hLge3
    t delta ht_last ht hdelta rt hterm hrt
  have hLpos' : 1 ≤ (d.suffixWord r).length - 1 := by omega
  have hLle' : (d.suffixWord r).length - 1 ≤ w.length := by omega
  have hb : IsCyclicC3RiseBoundaryAt w (cycleRiseBlockTailDepth d r) :=
    cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  rcases cycleQb8Input_cyclic_local_block_data h (cycleRiseBlockTailDepth d r)
      ((d.suffixWord r).length - 1) hb hLpos' hLle' with
    ⟨Aj, Wp, Wj, t0, hAj, hWj, hWp, ht0, hW, hid', hdiv, hrjform⟩
  have hAj' : Aj = StringFlow.Word.wordA u' := by
    simpa [u'] using hAj
  have hWj' : Wj = StringFlow.wordWeight u' := by
    simpa [u'] using hWj
  have hid'' : 2 ^ StringFlow.wordWeight u' *
        (5 ^ rt.k * rt.s +
          delta * 5 ^ ((d.suffixWord r).length - 1) - 1) =
      StringFlow.Word.wordA u' +
        5 ^ ((d.suffixWord r).length - 1) * q := by
    rw [hWj', hAj', ← hpred] at hid'
    exact hid'
  exact hid''.symm

/-- The suffix numerator plus the shifted boundary term collapses to
the exact `q`-polynomial `2^{W'}·(5X+1)`.  This is the block-level
form in which the boundary rank `R_r = v2(q+1)` can be extracted after
substituting `rt.r = 2^{c-1}·q`. -/
theorem cycleRiseBlockSuffixWordA_q_polynomial
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hLge3 : 3 ≤ (d.suffixWord r).length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2) :
    let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        ((d.suffixWord r).length - 1)
    let q := StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m
    let L := (d.suffixWord r).length
    let X := 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1
    StringFlow.Word.wordA (d.suffixWord r) + 5 ^ L * q =
      2 ^ StringFlow.wordWeight u' * (5 * X + 1) := by
  let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
      ((d.suffixWord r).length - 1)
  let q := StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r)) m
  let L := (d.suffixWord r).length
  let X := 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1
  have hdrop := cycleRiseBlockSuffixDropLast_eq_cyclic_take d r hr hne hLle
  have hlast := cycleRiseBlockSuffixWordA_last_step d r hne
  have hlast' : StringFlow.Word.wordA (d.suffixWord r) =
      5 * StringFlow.Word.wordA u' + 2 ^ StringFlow.wordWeight u' := by
    rw [hdrop] at hlast
    simpa [u'] using hlast
  have hpref := cycleRiseBlockWordA_prefix_add h d r hr hne hLle hLge3 t delta
    ht_last ht hdelta rt hterm hrt
  have hmain : StringFlow.Word.wordA (d.suffixWord r) + 5 ^ L * q =
      5 * (StringFlow.Word.wordA u' + 5 ^ (L - 1) * q) +
        2 ^ StringFlow.wordWeight u' := by
    rw [hlast']
    have hpow : 5 ^ L = 5 * 5 ^ (L - 1) := by
      have hLpos : 0 < L := by
        dsimp [L]
        exact List.length_pos_iff.mpr hne
      have hL_eq : L = (L - 1) + 1 := by omega
      rw [hL_eq, Nat.pow_succ]
      have hsub : L - 1 + 1 - 1 = L - 1 := by omega
      rw [hsub]
      rw [Nat.mul_comm]
    rw [hpow]
    ring
  calc
    StringFlow.Word.wordA (d.suffixWord r) + 5 ^ L * q
        = 5 * (StringFlow.Word.wordA u' + 5 ^ (L - 1) * q) +
            2 ^ StringFlow.wordWeight u' := hmain
    _ = 5 * (2 ^ StringFlow.wordWeight u' * X) +
          2 ^ StringFlow.wordWeight u' := by
        have hpref' : StringFlow.Word.wordA u' + 5 ^ (L - 1) * q =
            2 ^ StringFlow.wordWeight u' * X := by
          simpa [u', q, L, X] using hpref
        rw [hpref']
    _ = 2 ^ StringFlow.wordWeight u' * (5 * X + 1) := by ring

/-- Boundary substitution: `rt.r = 2^{c-1}·q` and
`5^rt.k·rt.s = rt.r+1` rewrite the `q`-polynomial into the explicit
`2^{c-1}` form.  This is the block-level shape used for the whole-cycle
rank sum. -/
theorem cycleRiseBlockSuffixWordA_q_polynomial_boundary
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (hLge3 : 3 ≤ (d.suffixWord r).length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hterm : IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2) :
    let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
        ((d.suffixWord r).length - 1)
    let q := StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m
    let L := (d.suffixWord r).length
    StringFlow.Word.wordA (d.suffixWord r) + 5 ^ L * q =
      2 ^ StringFlow.wordWeight u' *
        (5 * 2 ^ (w.getI (cycleRiseBlockTailDepth d r - 1) - 1) * q +
          5 * delta * 5 ^ (L - 1) + 1) := by
  let u' := (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
      ((d.suffixWord r).length - 1)
  let q := StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r)) m
  let L := (d.suffixWord r).length
  let X := 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1
  have hq0 := cycleRiseBlockSuffixWordA_q_polynomial h d r hr hne hLle hLge3 t delta
    ht_last ht hdelta rt hterm hrt
  have hb : IsCyclicC3RiseBoundaryAt w (cycleRiseBlockTailDepth d r) :=
    cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  have hbound := RealOrbitLocalLemma.cycleQb8Input_boundary_terminal_eq
    h (cycleRiseBlockTailDepth d r) hb rt hrt
  have hX0 : 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1 =
      rt.r + delta * 5 ^ (L - 1) := by
    have hprod' : 5 ^ rt.k * rt.s = rt.r + 1 := by
      simpa [Nat.mul_comm] using rt.hprod
    rw [hprod']
    omega
  have hX : 5 * (5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1) + 1 =
      5 * 2 ^ (w.getI (cycleRiseBlockTailDepth d r - 1) - 1) * q +
        5 * delta * 5 ^ (L - 1) + 1 := by
    rw [hX0, hbound]
    ring
  have hq1 : StringFlow.Word.wordA (d.suffixWord r) + 5 ^ L * q =
      2 ^ StringFlow.wordWeight u' * (5 * X + 1) := by
    simpa [u', q, L] using hq0
  rw [hX] at hq1
  simpa [u', q, L] using hq1

/-- The real-orbit half of `hterm`: the genuine predecessor identity
`5^rt.k * rt.s + delta * 5^(L-1) - 1 = wordOrbit u' q` constructs the
reset equation.  The remaining open input is exactly that predecessor
identity, supplied by real orbit data; cycle closure does not replace
it.  The `L ≥ 3` premise is structural: for `L ≤ 2` the identity is the
pseudo-candidate excluded by `cyclic_local_reset_length_ge_three`, whose
proof currently depends on `hterm` itself. -/
theorem cycleRiseBlockHterm_of_real_predecessor
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (_hLge3 : 3 ≤ (d.suffixWord r).length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hpred : 5 ^ rt.k * rt.s + delta * 5 ^ ((d.suffixWord r).length - 1) - 1 =
      StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          ((d.suffixWord r).length - 1))
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) :
    IsLocalResetTerminal t (d.suffixWord r).length
      (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
          (d.suffixWord r).length)
        (StringFlow.Word.wordOrbit
          (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt := by
  have hLpos : 1 ≤ (d.suffixWord r).length := List.length_pos_iff.mpr hne
  have hb := cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  have hlast := cycleRiseBlockSuffixLastStep d r hr hLpos hLle
  have ht_last' : t = (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).getI
      ((d.suffixWord r).length - 1) := by
    rw [← hlast]
    exact ht_last
  let b : Nat := cycleRiseBlockTailDepth d r
  let L : Nat := (d.suffixWord r).length
  let u' : List Nat := (cyclicSegmentAt w b).take (L - 1)
  let q : Nat := StringFlow.Word.wordOrbit (w.take b) m
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  rcases RealOrbitLocalLemma.cycleQb8Input_cyclic_prefix_occurrence_with_incoming
      h b L hble hLpos hLle with ⟨n, hn, hiter, hprev, hwWord⟩
  dsimp [b, L, u', q] at hprev ⊢
  have hw : S6Audit.orbitStepWeight (n - 1) = t := by
    rw [hwWord, ← ht_last']
  have hpred' : 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1 =
      S6Audit.fullOrbitIter (n - 1) := by
    rw [hprev]
    simpa [b, L, u', q] using hpred
  have hreset := RealOrbitLocalLemma.ResetHeadEq_of_fullOrbit_predecessor_eq
    n L rt.k t delta rt.s
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
    hLpos hn hiter hw ht hdelta hpred'
  have hterm' : IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q) delta rt :=
    (isLocalResetTerminal_iff_resetHeadEq t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
      delta rt ht hdelta).mpr hreset
  simpa [b, L, q] using hterm'

/-- Pure boundary form of the real predecessor identity: it no longer
mentions a `CycleRiseBlockDecomposition`.  All structure is carried by
the concrete C3-to-rise boundary `b`, the rise length `L`, the exact
rise-prefix membership `hseg`, and the single real terminal `rt`.  The
`L ≥ 3` premise is structural: without it the identity is the `L ≤ 2`
pseudo-candidate excluded by `cyclic_local_reset_length_ge_three`, whose
proof currently depends on `hterm` itself. -/
def cyclic_real_predecessor_identity
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (L : Nat) (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (hseg : ∀ k : Nat, k < L →
      (cyclicSegmentAt w b).getI k = 1 ∨
      (cyclicSegmentAt w b).getI k = 2)
    (t delta : Nat)
    (ht_last : t = (cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
      (w.take (b - 1)) m + 1) / 2) :
    Prop :=
  5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1 =
    StringFlow.Word.wordOrbit
      ((cyclicSegmentAt w b).take (L - 1))
      (StringFlow.Word.wordOrbit (w.take b) m)

/-- The congruence step behind the real predecessor identity:
`wordOrbit u' q ≡ 2^(c-1) q (mod 5^(L-1))`.  Once this congruence is
proved, the quotient `delta` is an integer and the remaining work is
only to pin its parity and size to `{1,3}` (or `1` for `t=1`). -/
def cyclic_real_predecessor_congruence : Prop :=
  ∀ (m S P : Nat) (w rise c3 : List Nat),
    ∀ (h : CycleQb8Input m S P w rise c3),
      ∀ (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b),
        ∀ (hLpos : 1 ≤ L) (hLle : L ≤ w.length),
          StringFlow.Word.wordOrbit
              ((cyclicSegmentAt w b).take (L - 1))
              (StringFlow.Word.wordOrbit (w.take b) m) %
                5 ^ (L - 1) =
            (2 ^ (w.getI (b - 1) - 1) *
              StringFlow.Word.wordOrbit (w.take b) m) %
              5 ^ (L - 1)

/-- The selected-block congruence target: the same mod `5^(L-1)`
congruence, but only for blocks whose penultimate rise step is `1`.
This is the quantifier-shrunk form forced by the mod-5 discriminator. -/
def cyclic_real_predecessor_congruence_selected : Prop :=
  ∀ (m S P : Nat) (w rise c3 : List Nat),
    ∀ (h : CycleQb8Input m S P w rise c3),
      ∀ (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b),
        ∀ (hLpos : 1 ≤ L) (hLle : L ≤ w.length),
          ∀ (hseg : ∀ k : Nat, k < L →
            (cyclicSegmentAt w b).getI k = 1 ∨
            (cyclicSegmentAt w b).getI k = 2),
            (cyclicSegmentAt w b).getI (L - 2) = 1 →
            StringFlow.Word.wordOrbit
                ((cyclicSegmentAt w b).take (L - 1))
                (StringFlow.Word.wordOrbit (w.take b) m) %
                  5 ^ (L - 1) =
              (2 ^ (w.getI (b - 1) - 1) *
                StringFlow.Word.wordOrbit (w.take b) m) %
                5 ^ (L - 1)

/-- The mod-25 base of the selected congruence.  This is the first
non-trivial layer of the 5-adic telescope; C4C8Tail supplies the exact
`wordA mod 25` and start-residue identities used at this level. -/
def cyclic_real_predecessor_congruence_mod25_selected : Prop :=
  ∀ (m S P : Nat) (w rise c3 : List Nat),
    ∀ (h : CycleQb8Input m S P w rise c3),
      ∀ (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b),
        ∀ (hLpos : 1 ≤ L) (hLle : L ≤ w.length),
          ∀ (hseg : ∀ k : Nat, k < L →
            (cyclicSegmentAt w b).getI k = 1 ∨
            (cyclicSegmentAt w b).getI k = 2),
            (cyclicSegmentAt w b).getI (L - 2) = 1 →
            StringFlow.Word.wordOrbit
                ((cyclicSegmentAt w b).take (L - 1))
                (StringFlow.Word.wordOrbit (w.take b) m) %
                  25 =
              (2 ^ (w.getI (b - 1) - 1) *
                StringFlow.Word.wordOrbit (w.take b) m) %
                25

/-- The unique candidate for `delta` in the real predecessor identity,
read directly from the actual orbit: the quotient of
`wordOrbit u' q - 2^(c-1) q` by `5^(L-1)`.  The congruence step makes
this quotient exact; the parity/size step then forces it into `{1,3}`. -/
def realPredecessorDelta (p q c m : Nat) : Nat :=
  (p - 2 ^ (c - 1) * q) / 5 ^ m

/-- A prefix of the cyclic rotation at a C3-to-rise boundary is a valid
word from the boundary state.  This is the non-`d` validity input used
by the mod-5 endpoint lemmas. -/
theorem cyclicSegmentAt_prefix_wordValid
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hble : b ≤ w.length) (hLle : L ≤ w.length) :
    StringFlow.Word.wordValid
      ((cyclicSegmentAt w b).take L)
      (StringFlow.Word.wordOrbit (w.take b) m) := by
  have hvalid_rot := cyclicSegmentAt_valid h b
  have hsplit : cyclicSegmentAt w b =
      (cyclicSegmentAt w b).take L ++ (cyclicSegmentAt w b).drop L :=
    (List.take_append_drop L (cyclicSegmentAt w b)).symm
  have hvalid_rot' : StringFlow.Word.wordValid
      ((cyclicSegmentAt w b).take L ++ (cyclicSegmentAt w b).drop L)
      (StringFlow.Word.wordOrbit (w.take b) m) := by
    rw [← hsplit]
    exact hvalid_rot
  exact (S6Audit.wordValid_append ((cyclicSegmentAt w b).take L)
    ((cyclicSegmentAt w b).drop L)
    (StringFlow.Word.wordOrbit (w.take b) m)).mp hvalid_rot' |>.1

/-- The exact forward recurrence on a cyclic rise prefix: appending
the `j`-th step multiplies the old orbit equation by the step weight. -/
theorem cyclicSegmentAt_prefix_orbit_succ
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b j : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hj : j < (cyclicSegmentAt w b).length) :
    2 ^ (cyclicSegmentAt w b).getI j *
      StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (j + 1))
        (StringFlow.Word.wordOrbit (w.take b) m) =
      5 * StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m) + 1 := by
  let u := cyclicSegmentAt w b
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hlen : u.length = w.length := by
    dsimp [u]
    exact cyclicSegmentAt_length w b hble
  have hj' : j < u.length := by
    simpa [u] using hj
  have hjlen : j + 1 ≤ w.length := by
    have hjw : j < w.length := by
      rw [← hlen]
      exact hj'
    omega
  have hvalid : StringFlow.Word.wordValid (u.take (j + 1)) q := by
    simpa [u, q] using cyclicSegmentAt_prefix_wordValid h b (j + 1) hble hjlen
  have htake0 := List.take_concat_get (l := u) (i := j) (by
    exact hj')
  have hget : u.getI j = u[j] :=
    List.getI_eq_getElem (l := u) (n := j) (by
      exact hj')
  rw [← hget] at htake0
  rw [List.concat_eq_append] at htake0
  have htake : u.take (j + 1) = u.take j ++ [u.getI j] := htake0.symm
  have hvalid_append : StringFlow.Word.wordValid
      (u.take j ++ [u.getI j]) q := by
    simpa [htake] using hvalid
  have hsplit := (S6Audit.wordValid_append_singleton
    (u.take j) q (u.getI j)).mp hvalid_append
  have hdvd : 2 ^ u.getI j ∣ 5 * StringFlow.Word.wordOrbit (u.take j) q + 1 :=
    Nat.dvd_iff_mod_eq_zero.mpr hsplit.2
  have hquot : StringFlow.Word.wordOrbit (u.take (j + 1)) q =
      (5 * StringFlow.Word.wordOrbit (u.take j) q + 1) / 2 ^ u.getI j := by
    simpa [htake] using
      (S6Audit.wordOrbit_append_singleton (u.take j) q (u.getI j))
  rw [hquot]
  exact Nat.mul_div_cancel' hdvd

/-- With `hcycle`, a `w.take k` orbit is exactly the corresponding
accelerated orbit state `fiveXPlusOneOrbit 7 (c + k)`. -/
theorem cycleQb8Input_wordOrbit_take_eq_orbit
    {w : List Nat} {c p : Nat}
    (hw : w = cycleWord c p)
    (k : Nat) (hk : k ≤ p) :
    StringFlow.Word.wordOrbit (w.take k)
        (fiveXPlusOneOrbit 7 c) = fiveXPlusOneOrbit 7 (c + k) := by
  rw [hw]
  exact cycleWord_prefix_orbit_eq c p k hk

/-- With `hcycle`, every in-range rotated entry is the exact step
weight at the corresponding accelerated orbit state. -/
theorem cycleQb8Input_cyclicSegmentAt_getI_eq_orbit
    {w : List Nat} {c p : Nat}
    (hw : w = cycleWord c p) (hp : 1 ≤ p)
    (b j : Nat) (hb : b ≤ p) (hj : j < p) :
    (cyclicSegmentAt w b).getI j =
      twoValuation
        (5 * fiveXPlusOneOrbit 7 (c + ((b + j) % p)) + 1) := by
  have hlen : w.length = p := by
    rw [hw, cycleWord_length]
  have hbw : b ≤ w.length := by simpa [hlen] using hb
  have hjw : j < w.length := by simpa [hlen] using hj
  have hmod := cyclicSegmentAt_getI_mod w b j hbw hjw
  rw [hw] at hmod
  have hlt : (b + j) % p < p := Nat.mod_lt _ (by omega)
  have hget := cycleWord_getI_eq c p ((b + j) % p) hlt
  rw [hw, hmod, cycleWord_length, hget]

/-- The last entry of a nonempty word is its final `getI`. -/
lemma wordLast_eq_getLast (u : List Nat) (hne : u ≠ []) :
    StringFlow.Word.wordLast u = List.getLast u hne := by
  induction u with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.Word.wordLast]
      | cons b l =>
          have htsne : b :: l ≠ [] := by simp
          have ih' := ih htsne
          have hcons := List.getLast_cons_cons (a := t) (b := b) (l := l)
          have hmain : List.getLast (b :: l) htsne =
              List.getLast (t :: b :: l) hne := by
            simpa [hne, htsne] using hcons.symm
          exact ih'.trans hmain

/-- The last entry of a nonempty word is its final `getI`. -/
lemma wordLast_eq_getI (u : List Nat) (hpos : 1 ≤ u.length) :
    StringFlow.Word.wordLast u = u.getI (u.length - 1) := by
  have hne : u ≠ [] := by
    intro h
    subst h
    simp at hpos
  rw [wordLast_eq_getLast u hne]
  have hlen : u.length - 1 < u.length := by omega
  rw [List.getLast_eq_getElem (l := u) hne]
  rw [List.getI_eq_getElem (l := u) (n := u.length - 1) hlen]

/-- The penultimate rotated entry is the last entry of the rise prefix
`(cyclicSegmentAt w b).take (L-1)`. -/
lemma wordLast_take_penultimate
    {w : List Nat} (b L : Nat)
    (hble : b ≤ w.length) (hLle : L ≤ w.length) (hLge3 : 3 ≤ L) :
    StringFlow.Word.wordLast ((cyclicSegmentAt w b).take (L - 1)) =
      (cyclicSegmentAt w b).getI (L - 2) := by
  let u := (cyclicSegmentAt w b).take (L - 1)
  have hulen : u.length = L - 1 := by
    dsimp [u]
    rw [List.length_take_of_le]
    rw [cyclicSegmentAt_length w b hble]
    omega
  have hpos : 1 ≤ u.length := by
    rw [hulen]
    omega
  rw [wordLast_eq_getI u hpos]
  have hklt : L - 2 < u.length := by
    rw [hulen]
    omega
  have hulen' : u.length - 1 = L - 2 := by
    rw [hulen]
    omega
  rw [hulen']
  have hget := List.getI_eq_getElem (l := u) (n := L - 2) hklt
  have hrot_lt : L - 2 < (cyclicSegmentAt w b).length := by
    rw [cyclicSegmentAt_length w b hble]
    omega
  have hrot := List.getI_eq_getElem
    (l := cyclicSegmentAt w b) (n := L - 2) hrot_lt
  have htake : u[L - 2] = (cyclicSegmentAt w b)[L - 2] :=
    List.getElem_take (j := L - 1) (i := L - 2) (h := hklt)
  rw [hget]
  rw [htake]
  exact hrot.symm

/-- Modulo 5, the real predecessor congruence holds exactly when the
penultimate rise step is `1`.  If the penultimate step is `2`, the
endpoint residue is `4 mod 5`, while the boundary terminal forces the
right-hand side to be `3 mod 5`.  This is the quantifier discriminator
used to shrink the universal congruence to selected blocks. -/
theorem cyclic_real_predecessor_congruence_mod_five_iff_penultimate_one
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (hseg : ∀ k : Nat, k < L →
      (cyclicSegmentAt w b).getI k = 1 ∨
      (cyclicSegmentAt w b).getI k = 2) :
    (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 5) ↔
      (cyclicSegmentAt w b).getI (L - 2) = 1 := by
  let q : Nat := StringFlow.Word.wordOrbit (w.take b) m
  let u : List Nat := (cyclicSegmentAt w b).take (L - 1)
  let c : Nat := w.getI (b - 1)
  have hLpos : 1 ≤ L := by omega
  have hLm : L - 1 ≤ w.length := le_trans (Nat.sub_le L 1) hLle
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hvalid : StringFlow.Word.wordValid u q := by
    dsimp [u, q]
    exact cyclicSegmentAt_prefix_wordValid h b (L - 1) hble hLm
  have hlast : StringFlow.Word.wordLast u =
      (cyclicSegmentAt w b).getI (L - 2) := by
    dsimp [u]
    exact wordLast_take_penultimate b L hble hLle hLge3
  have hbprev : b - 1 < w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hbpos : 1 ≤ b := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hsucc := wordOrbit_take_succ w m (b - 1) hbprev
  have hbadd : b - 1 + 1 = b := Nat.sub_add_cancel hbpos
  rw [hbadd] at hsucc
  have hcpos : 1 ≤ c := by
    dsimp [c]
    have hge : 3 ≤ w.getI (b - 1) := hb.2.2.1
    omega
  have hdvd : 2 ^ c ∣ 5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 := by
    dsimp [c]
    have hval := h.hexact (b - 1) hbprev
    have hle : c ≤ twoValuation
        (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) := by
      dsimp [c]
      omega
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) c
      (by positivity)).mp hle
  have hstep : 2 ^ c * q =
      5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 := by
    dsimp [q]
    rw [hsucc]
    exact Nat.mul_div_cancel' hdvd
  have hmodc : (2 ^ c * q) % 5 = 1 := by
    rw [hstep]
    rw [Nat.add_mod, Nat.mul_mod]
    simp
  have hpow : 2 * 2 ^ (c - 1) = 2 ^ c := by
    have hsub : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
    calc
      2 * 2 ^ (c - 1) = 2 ^ (c - 1) * 2 := by ring
      _ = 2 ^ ((c - 1) + 1) := by rw [Nat.pow_succ]
      _ = 2 ^ c := by rw [hsub]
  have hbound : (2 ^ (c - 1) * q) % 5 = 3 := by
    have hmod2 : (2 * (2 ^ (c - 1) * q)) % 5 = 1 := by
      rw [← Nat.mul_assoc, hpow]
      exact hmodc
    exact StringFlow.Word.two_mul_mod_five_eq_one_imp
      (2 ^ (c - 1) * q) hmod2
  have hq : q = StringFlow.Word.wordOrbit (w.take b) m := rfl
  have hc : c = w.getI (b - 1) := rfl
  rw [hq, hc] at hbound
  constructor
  · intro hcong
    have hp3 : StringFlow.Word.wordOrbit u q % 5 = 3 := by
      rwa [hbound] at hcong
    by_contra hnot
    have ht2 : (cyclicSegmentAt w b).getI (L - 2) = 2 := by
      have hcase := hseg (L - 2) (by omega)
      rcases hcase with h1 | h2
      · omega
      · exact h2
    have hlast2 : StringFlow.Word.wordLast u = 2 := by
      rw [hlast]
      exact ht2
    have hp4 := StringFlow.Word.wordOrbit_mod_five_of_last_two u q hvalid hlast2
    omega
  · intro ht1
    have hlast1 : StringFlow.Word.wordLast u = 1 := by
      rw [hlast]
      exact ht1
    have hp3 := StringFlow.Word.wordOrbit_mod_five_of_last_one u q hvalid hlast1
    rw [hp3, hbound]

/-- If the penultimate rise step is `2`, the mod-5 layer of the real
predecessor congruence fails: the endpoint residue is `4`, while the
boundary terminal forces the target residue `3`.  This is the formal
reason the universal congruence must be shrunk to selected blocks with
penultimate step `1`. -/
theorem cyclic_real_predecessor_congruence_mod_five_false_of_penultimate_two
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (hseg : ∀ k : Nat, k < L →
      (cyclicSegmentAt w b).getI k = 1 ∨
      (cyclicSegmentAt w b).getI k = 2)
    (ht2 : (cyclicSegmentAt w b).getI (L - 2) = 2) :
    ¬ (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 5) := by
  have hiff := cyclic_real_predecessor_congruence_mod_five_iff_penultimate_one
    h b L hb hLge3 hLle hseg
  intro hcong
  have h1 : (cyclicSegmentAt w b).getI (L - 2) = 1 := hiff.mp hcong
  omega

/-- `2^W mod 5` depends only on `W mod 4`. -/
lemma two_pow_mod5_of_mod4 (W : Nat) : (2 ^ W) % 5 = (2 ^ (W % 4)) % 5 := by
  have hdiv : W = 4 * (W / 4) + W % 4 := (Nat.div_add_mod W 4).symm
  have h4 : (2 ^ 4) % 5 = 1 := by norm_num
  have hmul : ((2 ^ 4) ^ (W / 4)) % 5 = 1 := by
    rw [Nat.pow_mod, h4]
    norm_num
  rw [hdiv, Nat.pow_add, Nat.mul_mod, Nat.pow_mul, hmul]
  norm_num

/-- `2^a == 2^b (mod 5)` iff `a == b (mod 4)`. -/
lemma two_pow_mod5_eq_iff_mod4_eq (a b : Nat) :
    (2 ^ a) % 5 = (2 ^ b) % 5 ↔ a % 4 = b % 4 := by
  constructor
  · intro h
    have ha := two_pow_mod5_of_mod4 a
    have hb := two_pow_mod5_of_mod4 b
    rw [ha, hb] at h
    have hlt₁ : a % 4 < 4 := Nat.mod_lt a (by decide)
    have hlt₂ : b % 4 < 4 := Nat.mod_lt b (by decide)
    interval_cases h₁ : a % 4 <;> interval_cases h₂ : b % 4 <;>
      norm_num at h <;> all_goals omega
  · intro h
    rw [two_pow_mod5_of_mod4 a, two_pow_mod5_of_mod4 b, h]

/-- Given `x * 2^a == 1 (mod 5)`, the identity `x * 2^b == 1 (mod 5)`
holds iff `a == b (mod 4)`. -/
lemma mul_pow_mod5_eq_one_iff (x a b : Nat) (h1 : (x * 2 ^ a) % 5 = 1) :
    (x * 2 ^ b) % 5 = 1 ↔ a % 4 = b % 4 := by
  constructor
  · intro h2
    have ha := two_pow_mod5_of_mod4 a
    have hb := two_pow_mod5_of_mod4 b
    rw [Nat.mul_mod] at h1
    rw [Nat.mul_mod] at h2
    rw [ha] at h1
    rw [hb] at h2
    have hxlt : x % 5 < 5 := Nat.mod_lt x (by decide)
    have hyalt : a % 4 < 4 := Nat.mod_lt a (by decide)
    have hyblt : b % 4 < 4 := Nat.mod_lt b (by decide)
    interval_cases hx : x % 5 <;> interval_cases hya : a % 4 <;>
      interval_cases hyb : b % 4 <;> (try norm_num at h1) <;> (try norm_num at h2)
    all_goals omega
  · intro hres
    rw [Nat.mul_mod] at h1 ⊢
    rw [two_pow_mod5_of_mod4 b, ← hres, ← two_pow_mod5_of_mod4 a]
    exact h1

/-- Adding the same summand does not change equality modulo `n`. -/
lemma add_mod_eq_add_mod_iff (a b c n : Nat) :
    (a + b) % n = (c + b) % n ↔ a % n = c % n := by
  constructor
  · intro h
    apply Nat.modEq_iff_dvd.mpr
    rcases (Nat.modEq_iff_dvd.mp (show a + b ≡ c + b [MOD n] from h)) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  · intro h
    exact Nat.ModEq.add (show a ≡ c [MOD n] from h) (Nat.ModEq.refl b)

/-- `5 == 5a (mod 25)` iff `a == 1 (mod 5)`. -/
lemma five_mod25_eq_mul_mod25_iff (a : Nat) :
    5 % 25 = (5 * a) % 25 ↔ a % 5 = 1 := by
  constructor
  · intro h
    have h' : (5 * a) % 25 = 5 := h.symm
    have ha : a = 5 * (a / 5) + a % 5 := by
      have hdiv := Nat.div_add_mod a 5
      omega
    rw [ha] at h'
    have hmul : 5 * (5 * (a / 5) + a % 5) = 25 * (a / 5) + 5 * (a % 5) := by ring
    rw [hmul, Nat.add_mod, Nat.mul_mod] at h'
    have hlt : a % 5 < 5 := Nat.mod_lt a (by decide)
    interval_cases ha5 : a % 5 <;> (try norm_num at h')
    all_goals omega
  · intro h
    have ha : a = 5 * (a / 5) + 1 := by
      have hdiv := Nat.div_add_mod a 5
      omega
    rw [ha]
    have hmul : 5 * (5 * (a / 5) + 1) = 25 * (a / 5) + 5 := by ring
    rw [hmul, Nat.add_mod, Nat.mul_mod]
    norm_num

/-- `(5 + 2^t) == (5x + 1) * 2^t (mod 25)` iff `x * 2^t == 1 (mod 5)`. -/
lemma mod25_cong_five_iff_mod5_one (x t : Nat) :
    (5 + 2 ^ t) % 25 = ((5 * x + 1) * 2 ^ t) % 25 ↔ (x * 2 ^ t) % 5 = 1 := by
  have hring : (5 * x + 1) * 2 ^ t = 5 * x * 2 ^ t + 2 ^ t := by ring
  rw [hring]
  rw [add_mod_eq_add_mod_iff 5 (2 ^ t) (5 * x * 2 ^ t) 25]
  rw [Nat.mul_assoc]
  exact five_mod25_eq_mul_mod25_iff (x * 2 ^ t)

/-- Multiplying by a unit preserves equality modulo 25. -/
lemma mod25_eq_iff_mul_unit (a b u v : Nat) (huv : (u * v) % 25 = 1) :
    a % 25 = b % 25 ↔ (a * u) % 25 = (b * u) % 25 := by
  constructor
  · intro h
    exact Nat.ModEq.mul_right u (show a ≡ b [MOD 25] from h)
  · intro h
    have h2 : a * u * v ≡ b * u * v [MOD 25] :=
      Nat.ModEq.mul_right v (show a * u ≡ b * u [MOD 25] from h)
    have hleft : a * u * v ≡ a [MOD 25] := by
      have heq : a * u * v = a * (u * v) := by ring
      rw [heq]
      exact (Nat.ModEq.mul_left a (show u * v ≡ 1 [MOD 25] from huv)).trans
        (by simpa [Nat.mul_one] using (Nat.ModEq.refl a : a ≡ a [MOD 25]))
    have hright : b * u * v ≡ b [MOD 25] := by
      have heq : b * u * v = b * (u * v) := by ring
      rw [heq]
      exact (Nat.ModEq.mul_left b (show u * v ≡ 1 [MOD 25] from huv)).trans
        (by simpa [Nat.mul_one] using (Nat.ModEq.refl b : b ≡ b [MOD 25]))
    have hba : b ≡ a [MOD 25] :=
      (Nat.ModEq.symm hright).trans ((Nat.ModEq.symm h2).trans hleft)
    exact hba.symm

/-- Multiplying by a unit preserves equality modulo `n`. -/
lemma modEq_eq_iff_mul_unit (a b u v n : Nat) (hn : 1 < n) (huv : (u * v) % n = 1) :
    a % n = b % n ↔ (a * u) % n = (b * u) % n := by
  constructor
  · intro h
    exact Nat.ModEq.mul_right u (show a ≡ b [MOD n] from h)
  · intro h
    have h2 : a * u * v ≡ b * u * v [MOD n] :=
      Nat.ModEq.mul_right v (show a * u ≡ b * u [MOD n] from h)
    have hleft : a * u * v ≡ a [MOD n] := by
      have heq : a * u * v = a * (u * v) := by ring
      rw [heq]
      exact (Nat.ModEq.mul_left a (by
        unfold Nat.ModEq
        rw [Nat.mod_eq_of_lt hn]
        exact huv)).trans
        (by simpa [Nat.mul_one] using (Nat.ModEq.refl a : a ≡ a [MOD n]))
    have hright : b * u * v ≡ b [MOD n] := by
      have heq : b * u * v = b * (u * v) := by ring
      rw [heq]
      exact (Nat.ModEq.mul_left b (by
        unfold Nat.ModEq
        rw [Nat.mod_eq_of_lt hn]
        exact huv)).trans
        (by simpa [Nat.mul_one] using (Nat.ModEq.refl b : b ≡ b [MOD n]))
    have hba : b ≡ a [MOD n] :=
      (Nat.ModEq.symm hright).trans ((Nat.ModEq.symm h2).trans hleft)
    exact hba.symm

/-- The inverse of `2` modulo `5^k`, explicit as `(5^k + 1) / 2`. -/
def pow2Inv5 (k : Nat) : Nat :=
  (5 ^ k + 1) / 2

/-- `2 * pow2Inv5 k == 1 (mod 5^k)` for `1 <= k`. -/
lemma pow2Inv5_spec (k : Nat) (hk : 1 ≤ k) :
    (2 * pow2Inv5 k) % 5 ^ k = 1 := by
  have hodd : (5 ^ k) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hdvd : 2 ∣ 5 ^ k + 1 := by
    have hmod : (5 ^ k + 1) % 2 = 0 := by
      rw [Nat.add_mod, hodd]
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hdiv : (5 ^ k + 1) / 2 * 2 = 5 ^ k + 1 := by
    have hmul := Nat.mul_div_cancel' hdvd
    rw [Nat.mul_comm] at hmul
    exact hmul
  dsimp [pow2Inv5]
  rw [Nat.mul_comm, hdiv]
  rw [Nat.add_mod, Nat.mod_self]
  have hlt : 1 < 5 ^ k := by
    have hpow : 5 ^ 1 ≤ 5 ^ k := Nat.pow_le_pow_right (by decide : 0 < 5) hk
    norm_num at hpow ⊢
    omega
  simp [Nat.mod_eq_of_lt hlt]

/-- `2^m * (pow2Inv5 k)^m == 1 (mod 5^k)`. -/
lemma pow2Inv5_pow_spec (k m : Nat) (hk : 1 ≤ k) :
    (2 ^ m * (pow2Inv5 k) ^ m) % 5 ^ k = 1 := by
  rw [← Nat.mul_pow, Nat.pow_mod, pow2Inv5_spec k hk]
  have hlt : 1 < 5 ^ k := by
    have hpow : 5 ^ 1 ≤ 5 ^ k := Nat.pow_le_pow_right (by decide : 0 < 5) hk
    norm_num at hpow ⊢
    omega
  simp
  rw [Nat.mod_eq_of_lt hlt]

/-- If `a == b (mod 5^k)` then `5a == 5b (mod 5^(k+1))`. -/
lemma mul_five_lift_mod (a b k : Nat) (h : a % 5 ^ k = b % 5 ^ k) :
    (5 * a) % 5 ^ (k + 1) = (5 * b) % 5 ^ (k + 1) := by
  apply Nat.modEq_iff_dvd.mpr
  rcases (Nat.modEq_iff_dvd.mp (show a ≡ b [MOD 5 ^ k] from h)) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hpow : ((5 ^ (k + 1) : Nat) : ℤ) = (5 : ℤ) * ((5 ^ k : Nat) : ℤ) := by
    rw [Nat.pow_succ, Nat.cast_mul]
    ring
  have hcastpow : ((5 ^ k : Nat) : ℤ) = (5 : ℤ) ^ k := by
    rw [Nat.cast_pow]
    norm_num
  have hcast : (↑(5 * b) : ℤ) - ↑(5 * a) = (5 : ℤ) * (↑b - ↑a) := by
    simp [Nat.cast_mul]
    ring
  rw [hcast, hpow, hc, hcastpow]
  ring

/-- The exact `k`-th layer lift of the 5-adic telescope: from the
previous-layer congruence `p ≡ r` and the real-orbit residue
`25x + 7 ≡ 2^(u+1)x`, one step of weight `u` reaches `p' ≡ x`. -/
lemma real_predecessor_congruence_prefix_lift
    (p p' r x u k : Nat)
    (hstep : 2 ^ u * p' = 5 * p + 1)
    (hr : 2 * r = 5 * x + 1)
    (hp : p ≡ r [MOD 5 ^ k])
    (hx : 25 * x + 7 ≡ 2 ^ (u + 1) * x [MOD 5 ^ k]) :
    p' ≡ x [MOD 5 ^ k] := by
  have hp5 : 5 * p + 1 ≡ 5 * r + 1 [MOD 5 ^ k] :=
    (Nat.ModEq.mul_left 5 hp).add_right 1
  have h2step : 2 ^ (u + 1) * p' = 2 * (5 * p + 1) := by
    calc
      2 ^ (u + 1) * p' = (2 * 2 ^ u) * p' := by
        rw [Nat.pow_succ]
        ring
      _ = 2 * (2 ^ u * p') := by ring
      _ = 2 * (5 * p + 1) := by rw [hstep]
  have h2r : 2 * (5 * r + 1) = 25 * x + 7 := by
    nlinarith
  have hcong : 2 ^ (u + 1) * p' ≡ 2 ^ (u + 1) * x [MOD 5 ^ k] := by
    calc
      2 ^ (u + 1) * p' = 2 * (5 * p + 1) := h2step
      _ ≡ 2 * (5 * r + 1) [MOD 5 ^ k] := Nat.ModEq.mul_left 2 hp5
      _ = 25 * x + 7 := h2r
      _ ≡ 2 ^ (u + 1) * x [MOD 5 ^ k] := hx
  have hdvd_int : (5 ^ k : ℤ) ∣
      ↑(2 ^ (u + 1) * x) - ↑(2 ^ (u + 1) * p') :=
    (Nat.modEq_iff_dvd.mp hcong)
  have hdvd_nat : 5 ^ k ∣ 2 ^ (u + 1) * (↑x - ↑p' : ℤ).natAbs := by
    have hdvd_int' : (5 ^ k : ℤ) ∣
        (2 ^ (u + 1) : ℤ) * (↑x - ↑p' : ℤ) := by
      simpa [Nat.cast_mul, Nat.cast_pow, mul_sub] using hdvd_int
    have hdvd_int'' : 5 ^ k ∣
        ((2 ^ (u + 1) : ℤ) * (↑x - ↑p' : ℤ)).natAbs :=
      Int.natCast_dvd.mp hdvd_int'
    have hdvd_int''' : 5 ^ k ∣
        (2 ^ (u + 1) : ℤ).natAbs * (↑x - ↑p' : ℤ).natAbs := by
      rw [Int.natAbs_mul] at hdvd_int''
      exact hdvd_int''
    norm_num at hdvd_int'''
    exact hdvd_int'''
  have hcop : (2 ^ (u + 1)).Coprime (5 ^ k) := by
    have hcop2 : (2 : Nat).Coprime 5 := by norm_num
    exact (Nat.Coprime.pow_left (u + 1) hcop2).pow_right k
  have hdvd_x : 5 ^ k ∣ (↑x - ↑p' : ℤ).natAbs :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd_nat
  have hdvd_int' : (5 ^ k : ℤ) ∣ (↑x - ↑p' : ℤ) :=
    Int.natCast_dvd.mpr hdvd_x
  exact Nat.modEq_iff_dvd.mpr hdvd_int'

/-- Left cancellation in `Nat.ModEq` when the multiplier is coprime to
the modulus. -/
lemma modEq_mul_left_cancel_of_coprime (a b c n : Nat) (hc : c.Coprime n)
    (h : c * a ≡ c * b [MOD n]) : a ≡ b [MOD n] := by
  have hdvd_int : (n : ℤ) ∣ ↑(c * b) - ↑(c * a) :=
    (Nat.modEq_iff_dvd.mp h)
  have hdvd_nat : n ∣ c * (↑b - ↑a : ℤ).natAbs := by
    have hdvd_int' : (n : ℤ) ∣ (c : ℤ) * (↑b - ↑a : ℤ) := by
      simpa [Nat.cast_mul, mul_sub] using hdvd_int
    have hdvd_int'' : n ∣ ((c : ℤ) * (↑b - ↑a : ℤ)).natAbs :=
      Int.natCast_dvd.mp hdvd_int'
    have hdvd_int''' : n ∣ (c : ℤ).natAbs * (↑b - ↑a : ℤ).natAbs := by
      rw [Int.natAbs_mul] at hdvd_int''
      exact hdvd_int''
    norm_num at hdvd_int'''
    exact hdvd_int'''
  have hdvd_x : n ∣ (↑b - ↑a : ℤ).natAbs :=
    Nat.Coprime.dvd_of_dvd_mul_left hc.symm hdvd_nat
  have hdvd_int' : (n : ℤ) ∣ (↑b - ↑a : ℤ) :=
    Int.natCast_dvd.mpr hdvd_x
  exact Nat.modEq_iff_dvd.mpr hdvd_int'

/-- The forward telescope step: from `p ≡ x (mod 5^k)` and the
real-orbit residue `5x+1 ≡ 2^u x (mod 5^(k+1))`, one step of weight
`u` reaches `p' ≡ x (mod 5^(k+1))`. -/
lemma prefix_congruence_step (p p' x u k : Nat)
    (hstep : 2 ^ u * p' = 5 * p + 1)
    (hp : p ≡ x [MOD 5 ^ k])
    (hx : 5 * x + 1 ≡ 2 ^ u * x [MOD 5 ^ (k + 1)]) :
    p' ≡ x [MOD 5 ^ (k + 1)] := by
  have hp5 : 5 * p + 1 ≡ 5 * x + 1 [MOD 5 ^ (k + 1)] := by
    have h' : 5 * p + 1 ≡ 5 * x + 1 [MOD 5 * 5 ^ k] :=
      (Nat.ModEq.mul_left' 5 hp).add_right 1
    simpa [Nat.pow_succ, Nat.mul_comm] using h'
  have hcong : 2 ^ u * p' ≡ 2 ^ u * x [MOD 5 ^ (k + 1)] := by
    calc
      2 ^ u * p' = 5 * p + 1 := hstep
      _ ≡ 5 * x + 1 [MOD 5 ^ (k + 1)] := hp5
      _ ≡ 2 ^ u * x [MOD 5 ^ (k + 1)] := hx
  have hcop : (2 ^ u).Coprime (5 ^ (k + 1)) := by
    have hcop2 : (2 : Nat).Coprime 5 := by norm_num
    exact (Nat.Coprime.pow_left u hcop2).pow_right (k + 1)
  exact modEq_mul_left_cancel_of_coprime p' x (2 ^ u) (5 ^ (k + 1)) hcop hcong

/-- The formal 5-adic telescope on a cyclic rise prefix: once the
real-orbit residue chain `5x+1 ≡ 2^(u_j)x` is supplied at every layer,
the full prefix congruence `p_n ≡ x (mod 5^n)` follows by induction. -/
theorem cyclic_real_predecessor_prefix_orbit_congruence_chain
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b n : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hnle : n ≤ w.length)
    (hres : ∀ j : Nat, j < n →
      5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 ≡
        2 ^ (cyclicSegmentAt w b).getI j *
          StringFlow.Word.wordOrbit (w.take (b - 1)) m
          [MOD 5 ^ (j + 1)]) :
    StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take n)
        (StringFlow.Word.wordOrbit (w.take b) m) ≡
      StringFlow.Word.wordOrbit (w.take (b - 1)) m [MOD 5 ^ n] := by
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let x := StringFlow.Word.wordOrbit (w.take (b - 1)) m
  let u := cyclicSegmentAt w b
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hulen : u.length = w.length := by
    dsimp [u]
    exact cyclicSegmentAt_length w b hble
  induction n with
  | zero =>
      change q % 1 = x % 1
      simp [q, x, Nat.mod_one]
  | succ n ih =>
      have ihn : n ≤ w.length := by omega
      have ih' : StringFlow.Word.wordOrbit (u.take n) q ≡ x [MOD 5 ^ n] := by
        have h := ih ihn (fun j hj => by simpa [u, x] using hres j (by omega))
        simpa [u, q, x] using h
      have hstep : 2 ^ u.getI n *
          StringFlow.Word.wordOrbit (u.take (n + 1)) q =
        5 * StringFlow.Word.wordOrbit (u.take n) q + 1 := by
        simpa [u, q] using cyclicSegmentAt_prefix_orbit_succ h b n hb (by
          have hnlt : n < u.length := by
            rw [hulen]
            omega
          simpa [u] using hnlt)
      have hx : 5 * x + 1 ≡ 2 ^ u.getI n * x [MOD 5 ^ (n + 1)] := by
        simpa [u, x] using hres n (by omega)
      simpa [q, x, u, Nat.add_comm] using
        (prefix_congruence_step (StringFlow.Word.wordOrbit (u.take n) q)
          (StringFlow.Word.wordOrbit (u.take (n + 1)) q)
          x (u.getI n) n hstep ih' hx)

/-- The mod-25 real-predecessor congruence, written with the inverse
of `2^(t+1)`, holds iff `x * 2^t == 1 (mod 5)`, where `2r = 5x + 1`. -/
lemma mod25_cong_iff_mod5_one
    (x t inv : Nat) (hinv : (2 ^ (t + 1) * inv) % 25 = 1)
    (r : Nat) (h2 : 2 * r = 5 * x + 1) :
    (((5 + 2 ^ t) * inv) % 25 = r % 25) ↔ (x * 2 ^ t) % 5 = 1 := by
  have hiff1 := mod25_eq_iff_mul_unit ((5 + 2 ^ t) * inv) r (2 ^ (t + 1)) inv hinv
  rw [hiff1]
  have hL : ((5 + 2 ^ t) * inv * 2 ^ (t + 1)) % 25 = (5 + 2 ^ t) % 25 := by
    have hmod : (5 + 2 ^ t) * inv * 2 ^ (t + 1) ≡ 5 + 2 ^ t [MOD 25] := by
      calc
        (5 + 2 ^ t) * inv * 2 ^ (t + 1) = (5 + 2 ^ t) * (inv * 2 ^ (t + 1)) := by ring
        _ ≡ (5 + 2 ^ t) * 1 [MOD 25] := by
            exact Nat.ModEq.mul_left (5 + 2 ^ t)
              (show inv * 2 ^ (t + 1) ≡ 1 [MOD 25] from by
                rw [Nat.mul_comm]
                exact hinv)
        _ ≡ 5 + 2 ^ t [MOD 25] := by
          simpa [Nat.mul_one] using
            (Nat.ModEq.refl (5 + 2 ^ t) : 5 + 2 ^ t ≡ 5 + 2 ^ t [MOD 25])
    exact hmod
  have hR : (r * 2 ^ (t + 1)) % 25 = ((5 * x + 1) * 2 ^ t) % 25 := by
    have hpow : 2 ^ (t + 1) = 2 ^ t * 2 := by rw [Nat.pow_succ]
    have heq : r * 2 ^ (t + 1) = (5 * x + 1) * 2 ^ t := by
      calc
        r * 2 ^ (t + 1) = r * (2 ^ t * 2) := by rw [hpow]
        _ = (2 * r) * 2 ^ t := by ring
        _ = (5 * x + 1) * 2 ^ t := by rw [h2]
    rw [heq]
  rw [hL, hR]
  exact mod25_cong_five_iff_mod5_one x t

/-- The forward congruence step: if the prefix orbit at `L-2` is
congruent to the pre-C3 state modulo `5^(L-2)`, then the real
predecessor congruence holds modulo `5^(L-1)` at a selected block
whose penultimate rise step is `1`.  This is the algebraic core of the
5-adic telescope; the orbit congruence itself is the remaining
real-orbit content. -/
theorem cyclic_real_predecessor_congruence_mod_pow_of_prefix_orbit_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (ht1 : (cyclicSegmentAt w b).getI (L - 2) = 1)
    (hcond : StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 2))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 2) =
      StringFlow.Word.wordOrbit (w.take (b - 1)) m % 5 ^ (L - 2)) :
    StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) := by
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let x := StringFlow.Word.wordOrbit (w.take (b - 1)) m
  let c := w.getI (b - 1)
  let u' := (cyclicSegmentAt w b).take (L - 1)
  let u'' := (cyclicSegmentAt w b).take (L - 2)
  let A := StringFlow.Word.wordA u'
  let A'' := StringFlow.Word.wordA u''
  let W'' := StringFlow.wordWeight u''
  let y'' := StringFlow.Word.wordOrbit u'' q
  let p := StringFlow.Word.wordOrbit u' q
  let r := 2 ^ (c - 1) * q
  have hbpos1 : 1 ≤ b := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hbprev : b - 1 < w.length := by omega
  have hlt : L - 2 < (cyclicSegmentAt w b).length := by
    rw [cyclicSegmentAt_length w b hble]
    omega
  have htake := List.take_concat_get (l := cyclicSegmentAt w b) (i := L - 2) hlt
  have hget : (cyclicSegmentAt w b).getI (L - 2) = (cyclicSegmentAt w b)[L - 2] :=
    List.getI_eq_getElem (l := cyclicSegmentAt w b) (n := L - 2) hlt
  rw [← hget] at htake
  rw [ht1] at htake
  rw [List.concat_eq_append] at htake
  have hu' : u' = u'' ++ [1] := by
    have hLadd : L - 2 + 1 = L - 1 := by omega
    rw [hLadd] at htake
    dsimp [u', u'']
    exact htake.symm
  have hW : StringFlow.wordWeight u' = W'' + 1 := by
    dsimp [W'', u', u''] at hu' ⊢
    rw [hu']
    rw [StringFlow.Word.wordWeight_append ((cyclicSegmentAt w b).take (L - 2)) [1]]
    simp [StringFlow.wordWeight]
  have hA : A = 5 * A'' + 2 ^ W'' := by
    have hA' := StringFlow.Word.wordA_append_singleton u'' 1
    rw [← hu'] at hA'
    simpa [A, A'', W'', u', u''] using hA'
  have hvalid_u' : StringFlow.Word.wordValid u' q := by
    dsimp [u', q]
    have hvalid_rot := cyclicSegmentAt_valid h b
    have hsplit : cyclicSegmentAt w b =
        (cyclicSegmentAt w b).take (L - 1) ++ (cyclicSegmentAt w b).drop (L - 1) :=
      (List.take_append_drop (L - 1) (cyclicSegmentAt w b)).symm
    have hvalid_rot' : StringFlow.Word.wordValid
        ((cyclicSegmentAt w b).take (L - 1) ++ (cyclicSegmentAt w b).drop (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) := by
      rw [← hsplit]
      exact hvalid_rot
    exact (S6Audit.wordValid_append ((cyclicSegmentAt w b).take (L - 1))
      ((cyclicSegmentAt w b).drop (L - 1))
      (StringFlow.Word.wordOrbit (w.take b) m)).mp hvalid_rot' |>.1
  have hvalid_u'' : StringFlow.Word.wordValid u'' q := by
    dsimp [u'', q]
    have hvalid_rot := cyclicSegmentAt_valid h b
    have hsplit : cyclicSegmentAt w b =
        (cyclicSegmentAt w b).take (L - 2) ++ (cyclicSegmentAt w b).drop (L - 2) :=
      (List.take_append_drop (L - 2) (cyclicSegmentAt w b)).symm
    have hvalid_rot' : StringFlow.Word.wordValid
        ((cyclicSegmentAt w b).take (L - 2) ++ (cyclicSegmentAt w b).drop (L - 2))
        (StringFlow.Word.wordOrbit (w.take b) m) := by
      rw [← hsplit]
      exact hvalid_rot
    exact (S6Audit.wordValid_append ((cyclicSegmentAt w b).take (L - 2))
      ((cyclicSegmentAt w b).drop (L - 2))
      (StringFlow.Word.wordOrbit (w.take b) m)).mp hvalid_rot' |>.1
  have hid' : 2 ^ (W'' + 1) * p = 5 ^ (L - 1) * q + A := by
    have hid := StringFlow.Word.word_orbit_identity u' q hvalid_u'
    have hlen : u'.length = L - 1 := by
      dsimp [u']
      rw [List.length_take_of_le]
      rw [cyclicSegmentAt_length w b hble]
      omega
    rw [hW, hlen] at hid
    simpa [p, A, u'] using hid
  have hid'' : 2 ^ W'' * y'' = 5 ^ (L - 2) * q + A'' := by
    have hid := StringFlow.Word.word_orbit_identity u'' q hvalid_u''
    have hlen : u''.length = L - 2 := by
      dsimp [u'']
      rw [List.length_take_of_le]
      rw [cyclicSegmentAt_length w b hble]
      omega
    rw [hlen] at hid
    simpa [y'', A'', u''] using hid
  have hstep : 2 ^ c * q = 5 * x + 1 := by
    have hsucc := wordOrbit_take_succ w m (b - 1) hbprev
    have hbadd : (b - 1) + 1 = b := Nat.sub_add_cancel hbpos1
    rw [hbadd] at hsucc
    have hval : twoValuation (5 * x + 1) = c := by
      dsimp [c, x]
      exact h.hexact (b - 1) hbprev
    have hdvd : 2 ^ c ∣ 5 * x + 1 := by
      have hge : c ≤ twoValuation (5 * x + 1) := by
        rw [hval]
      exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
        (5 * x + 1) c (by positivity)).mp hge
    dsimp [q, x, c]
    rw [hsucc]
    exact Nat.mul_div_cancel' hdvd
  have hr2 : 2 * r = 5 * x + 1 := by
    have hc3 : 3 ≤ c := by
      dsimp [c]
      exact hb.2.2.1
    have hcpos : 1 ≤ c := by omega
    have hc : c = (c - 1) + 1 := by omega
    have hpow : 2 ^ c = 2 * 2 ^ (c - 1) := by
      conv_lhs => rw [hc]
      rw [Nat.pow_succ]
      ring
    have h2r : 2 * r = 2 ^ c * q := by
      dsimp [r]
      rw [hpow]
      ring
    rw [h2r, hstep]
  have hrdiv : r = (5 * x + 1) / 2 := by
    have hdvd : 2 ∣ 5 * x + 1 := ⟨r, hr2.symm⟩
    have hdiv := Nat.mul_div_cancel' hdvd
    have hEq : 2 * r = 2 * ((5 * x + 1) / 2) := by
      rw [hr2]
      exact hdiv.symm
    exact Nat.mul_left_cancel (by decide : 0 < 2) hEq
  have hmodA'' : A'' % 5 ^ (L - 2) = (2 ^ W'' * x) % 5 ^ (L - 2) := by
    have hLm2 : 1 ≤ L - 2 := by omega
    have hpowpos : 0 < 5 ^ (L - 2) := by positivity
    have h25q : (5 ^ (L - 2) * q) % 5 ^ (L - 2) = 0 := by
      exact Nat.mul_mod_right (5 ^ (L - 2)) q
    have hleft : (2 ^ W'' * y'') % 5 ^ (L - 2) = A'' % 5 ^ (L - 2) := by
      have hid''_mod := congrArg (fun t : Nat => t % 5 ^ (L - 2)) hid''
      rw [Nat.add_mod, h25q] at hid''_mod
      simpa [Nat.add_comm] using hid''_mod
    have hright : (2 ^ W'' * y'') % 5 ^ (L - 2) = (2 ^ W'' * x) % 5 ^ (L - 2) := by
      have hx : y'' % 5 ^ (L - 2) = x % 5 ^ (L - 2) := by
        simpa [x, y'', q, u''] using hcond
      exact Nat.ModEq.mul_left (2 ^ W'')
        (show y'' ≡ x [MOD 5 ^ (L - 2)] from hx)
    exact hleft.symm.trans hright
  have hmodA : A % 5 ^ (L - 1) = (2 ^ W'' * (5 * x + 1)) % 5 ^ (L - 1) := by
    have hLm1 : 1 ≤ L - 1 := by omega
    have hpowpos : 0 < 5 ^ (L - 1) := by positivity
    have hmul5 : (5 * A'') % 5 ^ (L - 1) = (5 * (2 ^ W'' * x)) % 5 ^ (L - 1) := by
      have hlift := mul_five_lift_mod A'' (2 ^ W'' * x) (L - 2) hmodA''
      have hL : L - 1 = (L - 2) + 1 := by omega
      simpa [hL] using hlift
    have hring : A = 5 * A'' + 2 ^ W'' := hA
    have hring' : 2 ^ W'' * (5 * x + 1) = 5 * (2 ^ W'' * x) + 2 ^ W'' := by ring
    rw [hring, hring']
    rw [add_mod_eq_add_mod_iff (5 * A'') (2 ^ W'')
      (5 * (2 ^ W'' * x)) (5 ^ (L - 1))]
    exact hmul5
  have hmodp : (2 ^ (W'' + 1) * p) % 5 ^ (L - 1) =
      (2 ^ (W'' + 1) * r) % 5 ^ (L - 1) := by
    have h25q : (5 ^ (L - 1) * q) % 5 ^ (L - 1) = 0 := by
      exact Nat.mul_mod_right (5 ^ (L - 1)) q
    have hleft : (2 ^ (W'' + 1) * p) % 5 ^ (L - 1) = A % 5 ^ (L - 1) := by
      have hmod := congrArg (fun t : Nat => t % 5 ^ (L - 1)) hid'
      rw [Nat.add_mod, h25q] at hmod
      simpa [Nat.add_comm] using hmod
    have hright : (2 ^ (W'' + 1) * r) % 5 ^ (L - 1) =
        (2 ^ W'' * (5 * x + 1)) % 5 ^ (L - 1) := by
      have hr : 2 ^ (W'' + 1) * r = 2 ^ W'' * (5 * x + 1) := by
        calc
          2 ^ (W'' + 1) * r = (2 * 2 ^ W'') * r := by
            rw [Nat.pow_succ]
            ring
          _ = 2 ^ W'' * (2 * r) := by ring
          _ = 2 ^ W'' * (5 * x + 1) := by rw [hr2]
      rw [hr]
    rw [hleft, hright]
    exact hmodA
  have hinv : (2 ^ (W'' + 1) * (pow2Inv5 (L - 1)) ^ (W'' + 1)) % 5 ^ (L - 1) = 1 := by
    exact pow2Inv5_pow_spec (L - 1) (W'' + 1) (by omega)
  have hcong := (modEq_eq_iff_mul_unit p r (2 ^ (W'' + 1))
    ((pow2Inv5 (L - 1)) ^ (W'' + 1)) (5 ^ (L - 1)) (by omega) hinv).mpr (by
      simpa [Nat.mul_comm] using hmodp)
  simpa [p, r, q, u', u'', W'', c, x] using hcong

/-- The selected congruence closes from the real-orbit prefix
congruence at `L-2`: this is the exact forward step of the 5-adic
telescope, stated with the orbit input made explicit. -/
theorem cyclic_real_predecessor_congruence_selected_of_prefix_orbit_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (ht1 : (cyclicSegmentAt w b).getI (L - 2) = 1)
    (hcond : StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 2))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 2) =
      StringFlow.Word.wordOrbit (w.take (b - 1)) m % 5 ^ (L - 2)) :
    StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) :=
  cyclic_real_predecessor_congruence_mod_pow_of_prefix_orbit_eq h b L hb hLge3 hLle ht1 hcond

/-- The selected congruence is closed once the real orbit supplies the
5-adic residue chain at every prefix step.  This is the full algebraic
content of Step 4; the remaining real-orbit input is exactly `hres`. -/
theorem cyclic_real_predecessor_congruence_selected_of_residue_chain
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (ht1 : (cyclicSegmentAt w b).getI (L - 2) = 1)
    (hres : ∀ j : Nat, j < L - 2 →
      5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 ≡
        2 ^ (cyclicSegmentAt w b).getI j *
          StringFlow.Word.wordOrbit (w.take (b - 1)) m
          [MOD 5 ^ (j + 1)]) :
    StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 5 ^ (L - 1) := by
  have hchain := cyclic_real_predecessor_prefix_orbit_congruence_chain
    h b (L - 2) hb (by omega) (by
      intro j hj
      exact hres j hj)
  exact cyclic_real_predecessor_congruence_selected_of_prefix_orbit_eq
    h b L hb hLge3 hLle ht1 (by simpa [Nat.ModEq] using hchain)

/-- The first two entries of a list of length at least two. -/
lemma take_two_eq (l : List Nat) (h : 2 ≤ l.length) :
    l.take 2 = [l.getI 0, l.getI 1] := by
  cases l with
  | nil => norm_num at h
  | cons a as =>
      cases as with
      | nil => norm_num at h
      | cons b bs =>
          have htake : (a :: b :: bs).take 2 = [a, b] := by
            simp
          rw [htake]
          have h0 : (a :: b :: bs).getI 0 = a := by simp [List.getI]
          have h1 : (a :: b :: bs).getI 1 = b := by simp [List.getI]
          rw [h0, h1]

/-- The mod-25 layer of the real predecessor congruence at `L = 3`
holds iff the preceding step weight is congruent to the first rise
step weight modulo 4.  This is the first non-free layer of the
5-adic telescope: it is decided by the real orbit content at the
previous step, not by the boundary structure alone.  Consequently the
universal congruence is not a free consequence of `CycleQb8Input`; the
selected-block interface is the correct scope. -/
theorem cyclic_real_predecessor_congruence_mod25_iff_prev_residue
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLle : 3 ≤ w.length)
    (ht1 : (cyclicSegmentAt w b).getI 1 = 1) :
    (StringFlow.Word.wordOrbit
        ((cyclicSegmentAt w b).take 2)
        (StringFlow.Word.wordOrbit (w.take b) m) % 25 =
      (2 ^ (w.getI (b - 1) - 1) *
        StringFlow.Word.wordOrbit (w.take b) m) % 25) ↔
      w.getI (b - 2) % 4 = (cyclicSegmentAt w b).getI 0 % 4 := by
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let x := StringFlow.Word.wordOrbit (w.take (b - 1)) m
  let y := StringFlow.Word.wordOrbit (w.take (b - 2)) m
  let c := w.getI (b - 1)
  let tp := w.getI (b - 2)
  let t0 := (cyclicSegmentAt w b).getI 0
  let u := (cyclicSegmentAt w b).take 2
  let p := StringFlow.Word.wordOrbit u q
  let r := 2 ^ (c - 1) * q
  let inv := StringFlow.Word.pow2Inv25 (t0 + 1)
  have hbpos1 : 1 ≤ b := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hbpos : 2 ≤ b := by
    by_cases hb1 : b = 1
    · subst b
      have hc3 : 3 ≤ w.getI 0 := hb.2.2.1
      rcases h.hrise_start with h1 | h2
      · rw [h1] at hc3
        omega
      · rw [h2] at hc3
        omega
    · omega
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hbprev : b - 1 < w.length := by omega
  have hbprev2 : b - 2 < w.length := by omega
  have hrot_len2 : 2 ≤ (cyclicSegmentAt w b).length := by
    rw [cyclicSegmentAt_length w b hble]
    omega
  have hu : u = [t0, 1] := by
    dsimp [u, t0]
    rw [take_two_eq (cyclicSegmentAt w b) hrot_len2]
    rw [ht1]
  have hvalid_u : StringFlow.Word.wordValid u q := by
    dsimp [u, q]
    have hvalid_rot := cyclicSegmentAt_valid h b
    have hsplit : cyclicSegmentAt w b =
        (cyclicSegmentAt w b).take 2 ++ (cyclicSegmentAt w b).drop 2 :=
      (List.take_append_drop 2 (cyclicSegmentAt w b)).symm
    have hvalid_rot' : StringFlow.Word.wordValid
        ((cyclicSegmentAt w b).take 2 ++ (cyclicSegmentAt w b).drop 2)
        (StringFlow.Word.wordOrbit (w.take b) m) := by
      rw [← hsplit]
      exact hvalid_rot
    exact (S6Audit.wordValid_append ((cyclicSegmentAt w b).take 2)
      ((cyclicSegmentAt w b).drop 2)
      (StringFlow.Word.wordOrbit (w.take b) m)).mp hvalid_rot' |>.1
  have hid : 2 ^ (t0 + 1) * p = 25 * q + (5 + 2 ^ t0) := by
    have hid' := StringFlow.Word.word_orbit_identity u q hvalid_u
    rw [hu] at hid'
    have hw : StringFlow.wordWeight [t0, 1] = t0 + 1 := by
      simp [StringFlow.wordWeight]
    have hA : StringFlow.Word.wordA [t0, 1] = 5 + 2 ^ t0 := by
      simp [StringFlow.Word.wordA]
    rw [hw, hA] at hid'
    dsimp [p]
    rw [hu, hid']
    simp
  have hpmod : p % 25 = ((5 + 2 ^ t0) * inv) % 25 := by
    have hA : StringFlow.Word.wordA [t0, 1] = 5 + 2 ^ t0 := by
      simp [StringFlow.Word.wordA]
    have hx : 2 ^ (t0 + 1) * p =
        StringFlow.Word.wordA ([] ++ [t0, 1]) + 5 ^ (0 + 2) * q := by
      rw [hid]
      simp [hA]
      ring
    have hstart := StringFlow.Word.start_mod25_of_tail_two
      [] t0 1 p q (t0 + 1) (by simp [StringFlow.wordWeight]) hx
    simpa [inv, StringFlow.wordWeight] using hstart
  have hstep : 2 ^ c * q = 5 * x + 1 := by
    have hsucc := wordOrbit_take_succ w m (b - 1) hbprev
    have hbadd : (b - 1) + 1 = b := Nat.sub_add_cancel hbpos1
    rw [hbadd] at hsucc
    have hval : twoValuation (5 * x + 1) = c := by
      dsimp [c, x]
      exact h.hexact (b - 1) hbprev
    have hdvd : 2 ^ c ∣ 5 * x + 1 := by
      have hge : c ≤ twoValuation (5 * x + 1) := by
        rw [hval]
      exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
        (5 * x + 1) c (by positivity)).mp hge
    dsimp [q, x, c]
    rw [hsucc]
    exact Nat.mul_div_cancel' hdvd
  have hr2 : 2 * r = 5 * x + 1 := by
    have hc3 : 3 ≤ c := by
      dsimp [c]
      exact hb.2.2.1
    have hcpos : 1 ≤ c := by omega
    have hc : c = (c - 1) + 1 := by omega
    have hpow : 2 ^ c = 2 * 2 ^ (c - 1) := by
      conv_lhs => rw [hc]
      rw [Nat.pow_succ]
      ring
    have h2r : 2 * r = 2 ^ c * q := by
      dsimp [r]
      rw [hpow]
      ring
    rw [h2r, hstep]
  have hprevstep : 2 ^ tp * x = 5 * y + 1 := by
    have hsucc := wordOrbit_take_succ w m (b - 2) hbprev2
    have hbadd : (b - 2) + 1 = b - 1 := by omega
    rw [hbadd] at hsucc
    have hval : twoValuation (5 * y + 1) = tp := by
      dsimp [tp, y]
      exact h.hexact (b - 2) hbprev2
    have hdvd : 2 ^ tp ∣ 5 * y + 1 := by
      have hge : tp ≤ twoValuation (5 * y + 1) := by
        rw [hval]
      exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
        (5 * y + 1) tp (by positivity)).mp hge
    dsimp [tp, x, y]
    rw [hsucc]
    exact Nat.mul_div_cancel' hdvd
  have hprevmod : (2 ^ tp * x) % 5 = 1 := by
    rw [hprevstep, Nat.add_mod, Nat.mul_mod]
    norm_num
  have hinv : (2 ^ (t0 + 1) * inv) % 25 = 1 := by
    dsimp [inv]
    exact StringFlow.Word.pow2Inv25_spec (t0 + 1)
  have hgoal : (p % 25 = r % 25) ↔ (x * 2 ^ t0) % 5 = 1 := by
    rw [hpmod]
    exact mod25_cong_iff_mod5_one x t0 inv hinv r hr2
  have hprevmod' : (x * 2 ^ tp) % 5 = 1 := by
    rw [Nat.mul_comm]
    exact hprevmod
  have hfinal : (x * 2 ^ t0) % 5 = 1 ↔ tp % 4 = t0 % 4 := by
    exact mul_pow_mod5_eq_one_iff x tp t0 hprevmod'
  simpa [p, r, tp, t0, u, q] using hgoal.trans hfinal

/-- The pure-boundary predecessor identity constructs `hterm` directly
at the same C3-to-rise boundary and length.  This is the non-`d`
version of `cycleRiseBlockHterm_of_real_predecessor`: once the identity
is supplied at `(b, L)`, the exact incoming step and real terminal give
`IsLocalResetTerminal` with no block decomposition input. -/
theorem cyclic_real_predecessor_identity_to_hterm
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L t delta : Nat)
    (hb : IsCyclicC3RiseBoundaryAt w b)
    (hLge3 : 3 ≤ L) (hLle : L ≤ w.length)
    (hseg : ∀ k : Nat, k < L →
      (cyclicSegmentAt w b).getI k = 1 ∨
      (cyclicSegmentAt w b).getI k = 2)
    (ht_last : t = (cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2)
    (hpred : cyclic_real_predecessor_identity h b hb L hLge3 hLle hseg
      t delta ht_last ht hdelta rt hrt) :
    IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) delta rt := by
  let q : Nat := StringFlow.Word.wordOrbit (w.take b) m
  have hLpos : 1 ≤ L := by omega
  have hble : b ≤ w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  rcases RealOrbitLocalLemma.cycleQb8Input_cyclic_prefix_occurrence_with_incoming
      h b L hble hLpos hLle with ⟨n, hn, hiter, hprev, hwWord⟩
  have hw : S6Audit.orbitStepWeight (n - 1) = t := by
    rw [hwWord, ← ht_last]
  have hpred' : 5 ^ rt.k * rt.s + delta * 5 ^ (L - 1) - 1 =
      S6Audit.fullOrbitIter (n - 1) := by
    rw [hprev]
    unfold cyclic_real_predecessor_identity at hpred
    simpa [q] using hpred
  have hreset := RealOrbitLocalLemma.ResetHeadEq_of_fullOrbit_predecessor_eq
    n L rt.k t delta rt.s
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
    hLpos hn hiter hw ht hdelta hpred'
  have hterm' : IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q) delta rt :=
    (isLocalResetTerminal_iff_resetHeadEq t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L) q)
      delta rt ht hdelta).mpr hreset
  simpa [q] using hterm'

/-- The block-level predecessor identity is the trivial instance of the
pure boundary proposition at the block's C3-tail boundary and rise
suffix.  No decomposition induction or structural case analysis is
allowed inside its proof: the boundary, length, membership, and last
step are supplied directly by the cyclic rise block. -/
def cycleQb8InputRealPredecessorIdentity : Prop :=
  ∀ (m S P : Nat) (w rise c3 : List Nat),
    ∀ (h : CycleQb8Input m S P w rise c3),
      ∀ (d : CycleRiseBlockDecomposition m S P w) (r : Nat),
        ∀ (hr : r < d.blockCount) (hne : d.suffixWord r ≠ []),
          ∀ (hLle : (d.suffixWord r).length ≤ w.length)
            (hLge3 : 3 ≤ (d.suffixWord r).length),
            ∀ (t delta : Nat),
              ∀ (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
                (ht : t = 1 ∨ t = 2)
                (hdelta : (t = 1 → delta = 1) ∧
                  (t = 2 → delta = 1 ∨ delta = 3)),
                ∀ (rt : S6Audit.AngelinaGilbertaRealTerminal)
                  (hrt : rt.r = (5 * StringFlow.Word.wordOrbit
                    (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2),
                  cyclic_real_predecessor_identity h
                    (cycleRiseBlockTailDepth d r)
                    (cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne)
                    (d.suffixWord r).length hLge3 hLle
                    (fun k hk => cycleRiseBlockSuffixHall d r hr hLle k hk)
                    t delta
                    (by
                      have hLpos : 1 ≤ (d.suffixWord r).length := by omega
                      exact ht_last.trans
                        (cycleRiseBlockSuffixLastStep d r hr hLpos hLle))
                    ht hdelta rt hrt

/-- The real predecessor identity closes the real-orbit half of
`hterm` at every cyclic rise block. -/
theorem cycleQb8InputHtermOfRealPredecessorIdentity
    (hpre : cycleQb8InputRealPredecessorIdentity) :
    ∀ m S P : Nat, ∀ w rise c3 : List Nat,
      CycleQb8Input m S P w rise c3 →
      ∀ (d : CycleRiseBlockDecomposition m S P w) (r : Nat),
        r < d.blockCount → d.suffixWord r ≠ [] →
        (d.suffixWord r).length ≤ w.length →
        3 ≤ (d.suffixWord r).length →
        ∀ t delta : Nat,
          t = (d.suffixWord r).getI ((d.suffixWord r).length - 1) →
          (t = 1 ∨ t = 2) →
          ((t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3)) →
          ∀ rt : S6Audit.AngelinaGilbertaRealTerminal,
            rt.r = (5 * StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) / 2 →
            IsLocalResetTerminal t (d.suffixWord r).length
              (StringFlow.Word.wordOrbit
                ((cyclicSegmentAt w (cycleRiseBlockTailDepth d r)).take
                  (d.suffixWord r).length)
                (StringFlow.Word.wordOrbit
                  (w.take (cycleRiseBlockTailDepth d r)) m)) delta rt := by
  intro m S P w rise c3 h d r hr hne hLle hLge3
    t delta ht_last ht hdelta rt hrt
  exact cycleRiseBlockHterm_of_real_predecessor h d r hr hne hLle hLge3
    t delta ht_last ht hdelta rt
    (hpre m S P w rise c3 h d r hr hne hLle hLge3
      t delta ht_last ht hdelta rt hrt)

/-- Selected-block form of the real predecessor identity: hterm only
needs one genuine cyclic rise block, not every block in the
decomposition.  The caller (for example the bad-prefix hfail side)
supplies the concrete `b, L, t, delta, rt`; this target is exactly the
pure boundary identity at that selection. -/
def cycleQb8InputSelectedRealPredecessorIdentity : Prop :=
  ∀ (m S P : Nat) (w rise c3 : List Nat),
    ∀ (h : CycleQb8Input m S P w rise c3),
      ∃ b L t delta : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        ∃ hb : IsCyclicC3RiseBoundaryAt w b,
        ∃ hLge3 : 3 ≤ L, ∃ hLle : L ≤ w.length,
        ∃ hpen : (cyclicSegmentAt w b).getI (L - 2) = 1,
        ∃ hseg : ∀ k : Nat, k < L →
          (cyclicSegmentAt w b).getI k = 1 ∨
          (cyclicSegmentAt w b).getI k = 2,
        ∃ hres : ∀ j : Nat, j < L - 2 →
          5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 ≡
            2 ^ (cyclicSegmentAt w b).getI j *
              StringFlow.Word.wordOrbit (w.take (b - 1)) m
              [MOD 5 ^ (j + 1)],
        ∃ ht_last : t = (cyclicSegmentAt w b).getI (L - 1),
        ∃ ht : t = 1 ∨ t = 2,
        ∃ hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3),
        ∃ hrt : rt.r = (5 * StringFlow.Word.wordOrbit
          (w.take (b - 1)) m + 1) / 2,
          cyclic_real_predecessor_identity h b hb L hLge3 hLle hseg
            t delta ht_last ht hdelta rt hrt

/-- A selected predecessor identity directly supplies an `hterm` at
that selected block; no universal `∀ d r` block quantification is
needed. -/
theorem cycleQb8InputSelectedHtermOfRealPredecessorIdentity
    (hpre : cycleQb8InputSelectedRealPredecessorIdentity) :
    ∀ m S P : Nat, ∀ w rise c3 : List Nat,
      CycleQb8Input m S P w rise c3 →
      ∃ b L t delta : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        IsLocalResetTerminal t L
          (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
            (StringFlow.Word.wordOrbit (w.take b) m)) delta rt := by
  intro m S P w rise c3 h
  rcases hpre m S P w rise c3 h with
    ⟨b, L, t, delta, rt, hb, hLge3, hLle, hpen, hseg, _hres,
      ht_last, ht, hdelta, hrt, hpred⟩
  exact ⟨b, L, t, delta, rt,
    cyclic_real_predecessor_identity_to_hterm h b L t delta
      hb hLge3 hLle hseg ht_last ht hdelta rt hrt hpred⟩

/-- The complete real-block premises instantiation for a cyclic rise
block (wrap-invariant): the word structure, the `q0` interval, the head
bound and the prefix-orbit identities are all derived from the
decomposition; only the real reset-window size (`hhead`), the tail size
(`hrs_lt`) and the failure-branch data (`r_s % 8`, `L`, `H_s`) remain
as inputs. -/
theorem premises_of_cycleRiseBlock
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (j s t rj r_s L H_s : Nat)
    (hj_pos : 1 ≤ j) (hj_le_s : j ≤ s) (hs_le : s ≤ (d.suffixWord r).length)
    (ht : UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) j =
      UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1) + t)
    (hrj : rj = StringFlow.Word.wordOrbit
      (w.take ((cycleRiseBlockTailDepth d r + j) % P)) m)
    (hhead : 5 ^ j ≤ 2 ^ t * rj ∧ rj < 5 ^ j)
    (hrs_eq : r_s = StringFlow.Word.wordOrbit
      (w.take ((cycleRiseBlockTailDepth d r + s) % P)) m)
    (hrs_lt : r_s < 5 ^ s)
    (hrs_mod8 : r_s % 8 = 5)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hH : H_s = 2 * s + 13 - 2 *
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) s -
        UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1))) :
    UnifiedCoreAudit.All36_20PremisesNoHge j
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1))
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) j)
      (cycleRiseBlockC3TailState d r)
      (S6Audit.wordMolecule (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) j)
      (S6Audit.wordMolecule (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) s) s
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) s) r_s L H_s
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) := by
  have hvs := suffixWord_valid_of_cycleRiseBlock d r hr
  have hprej := suffixWord_prefix_eq_word_prefix_mod d r hr j (by omega)
  have hpres := suffixWord_prefix_eq_word_prefix_mod d r hr s hs_le
  have hrj_local : rj = StringFlow.Word.wordOrbit ((d.suffixWord r).take j)
      (cycleRiseBlockC3TailState d r) := by
    rw [hrj]
    exact hprej.symm
  have hrs_local : r_s = StringFlow.Word.wordOrbit ((d.suffixWord r).take s)
      (cycleRiseBlockC3TailState d r) := by
    rw [hrs_eq]
    exact hpres.symm
  exact UnifiedCoreAudit.premises_of_real_orbit_head (d.suffixWord r)
    (cycleRiseBlockC3TailState d r)
    j s r_s L H_s t rj hvs.1 hvs.2 hj_pos hj_le_s hs_le ht hrj_local hhead
    hrs_local hrs_lt hrs_mod8 hL hH

/-- The real reset-window version of the cyclic rise-block premises:
the head-size interval is supplied by the genuine reset reachability
`ResetHeadEq` / `ResetWindowReachability` (the output of
`local_hident_to_reset_reachability` on the real block), so only the
tail-size and failure-branch inputs remain. -/
theorem premises_of_cycleRiseBlock_of_reset_window
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (j s t rj r_s L H_s k0 delta s0 : Nat)
    (hj_pos : 1 ≤ j) (hj_le_s : j ≤ s) (hs_le : s ≤ (d.suffixWord r).length)
    (ht : UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) j =
      UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1) + t)
    (hrj : rj = StringFlow.Word.wordOrbit
      (w.take ((cycleRiseBlockTailDepth d r + j) % P)) m)
    (hreset : S6Audit.ResetHeadEq s0 j k0 t delta rj)
    (hreach : S6Audit.ResetWindowReachability j k0 t delta s0)
    (hrs_eq : r_s = StringFlow.Word.wordOrbit
      (w.take ((cycleRiseBlockTailDepth d r + s) % P)) m)
    (hrs_lt : r_s < 5 ^ s)
    (hrs_mod8 : r_s % 8 = 5)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hH : H_s = 2 * s + 13 - 2 *
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) s -
        UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1))) :
    UnifiedCoreAudit.All36_20PremisesNoHge j
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) (j - 1))
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) j)
      (cycleRiseBlockC3TailState d r)
      (S6Audit.wordMolecule (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) j)
      (S6Audit.wordMolecule (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) s) s
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r) s) r_s L H_s
      (UnifiedCoreAudit.prefixWeightOf (d.suffixWord r)) := by
  have hhead := StringFlow.RealOrbitLocalLemma.reset_head_size_bounds_of_reachability
    j k0 t delta s0 rj hreset hreach
  exact premises_of_cycleRiseBlock d r hr j s t rj r_s L H_s
    hj_pos hj_le_s hs_le ht hrj hhead hrs_eq hrs_lt hrs_mod8 hL hH

/-! ## Uniform whole-cycle block summation

The lemmas in this section are the uniform block-layer mechanism for
the whole-cycle sum.  They instantiate
`cycleQb8Input_cyclic_local_block_data` at every C3-tail boundary
`b = cycleRiseBlockTailDepth d r` with `u = suffixWord r`, so no
selected-block `hterm`/`rt` enters the summation.  The selected-block
`q`-polynomial lemmas above remain available only after a block has
been chosen. -/

/-- Uniform cyclic local block data at every C3-tail boundary: the
rise suffix `u = suffixWord r`, its boundary state
`q = wordOrbit (w.take b) m`, and its exact local word equation,
instantiated from `cycleQb8Input_cyclic_local_block_data` without any
selected-block `hterm`/`rt`. -/
theorem cycleRiseBlockUniformLocalBlockData
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length) :
    ∃ Aj Wp Wj t : Nat,
      Aj = StringFlow.Word.wordA (d.suffixWord r) ∧
      Wj = StringFlow.wordWeight (d.suffixWord r) ∧
      Wp = StringFlow.wordWeight ((d.suffixWord r).take
        ((d.suffixWord r).length - 1)) ∧
      t = (d.suffixWord r).getI ((d.suffixWord r).length - 1) ∧
      Wj = Wp + t ∧
      2 ^ Wj * StringFlow.Word.wordOrbit (d.suffixWord r)
            (StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m) =
        StringFlow.Word.wordA (d.suffixWord r) +
          5 ^ (d.suffixWord r).length *
            StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m ∧
      (StringFlow.Word.wordA (d.suffixWord r) +
          5 ^ (d.suffixWord r).length *
            StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m) %
            2 ^ Wj = 0 ∧
      StringFlow.Word.wordOrbit (d.suffixWord r)
            (StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m) =
        (StringFlow.Word.wordA (d.suffixWord r) +
          5 ^ (d.suffixWord r).length *
            StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m) /
            2 ^ Wj := by
  let u := d.suffixWord r
  let b := cycleRiseBlockTailDepth d r
  let L := u.length
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hb : IsCyclicC3RiseBoundaryAt w b := by
    dsimp [b]
    exact cycleRiseBlockTailDepth_is_cyclic_c3_rise_boundary d r hr hne
  have hLpos : 1 ≤ L := by
    dsimp [L, u]
    exact List.length_pos_iff.mpr hne
  have hLle' : L ≤ w.length := by
    dsimp [L, u]
    exact hLle
  have hsuff : (cyclicSegmentAt w b).take L = u := by
    dsimp [u, L, b]
    exact (cycleRiseBlockSuffixWord_eq_cyclic_take d r hr hLle).symm
  rcases cycleQb8Input_cyclic_local_block_data h b L hb hLpos hLle' with
    ⟨Aj, Wp, Wj, t, hAj, hWj, hWp, ht, hW, hid, hdiv, hrjform⟩
  refine ⟨Aj, Wp, Wj, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [u, hsuff] using hAj
  · simpa [u, hsuff] using hWj
  · simpa [u, L, hsuff] using hWp
  · simpa [u, L, hsuff] using ht
  · exact hW
  · simpa [u, q, b, L, hsuff, hAj] using hid
  · simpa [u, q, b, L, hsuff, hAj] using hdiv
  · simpa [u, q, b, L, hsuff, hAj] using hrjform

/-- Sum of the uniform local block equations over the whole cyclic
decomposition:
`Σ (wordA suffix_r + 5^{L_r}·q_r) = Σ (2^{W_r}·y_r)`. -/
theorem cycleRiseBlockUniformSuffixEquationSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w)
    (hsuff_pos : ∀ r : Nat, r < d.blockCount → d.suffixWord r ≠ [])
    (hLle : ∀ r : Nat, r < d.blockCount →
      (d.suffixWord r).length ≤ w.length) :
    ((List.range d.blockCount).map
      (fun r => StringFlow.Word.wordA (d.suffixWord r) +
        5 ^ (d.suffixWord r).length *
          StringFlow.Word.wordOrbit
            (w.take (cycleRiseBlockTailDepth d r)) m)).sum =
    ((List.range d.blockCount).map
      (fun r => 2 ^ StringFlow.wordWeight (d.suffixWord r) *
          StringFlow.Word.wordOrbit (d.suffixWord r)
            (cycleRiseBlockC3TailState d r))).sum := by
  have hmap : (List.range d.blockCount).map
      (fun r => StringFlow.Word.wordA (d.suffixWord r) +
        5 ^ (d.suffixWord r).length *
          StringFlow.Word.wordOrbit
            (w.take (cycleRiseBlockTailDepth d r)) m) =
    (List.range d.blockCount).map
      (fun r => 2 ^ StringFlow.wordWeight (d.suffixWord r) *
          StringFlow.Word.wordOrbit (d.suffixWord r)
            (cycleRiseBlockC3TailState d r)) := by
    apply List.map_congr_left
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    rcases cycleRiseBlockUniformLocalBlockData h d r hrlt
      (hsuff_pos r hrlt) (hLle r hrlt) with
      ⟨Aj, Wp, Wj, t, hAj, hWj, hWp, ht, hW, hid, hdiv, hrjform⟩
    have hhid : 2 ^ Wj * StringFlow.Word.wordOrbit (d.suffixWord r)
          (cycleRiseBlockC3TailState d r) =
        StringFlow.Word.wordA (d.suffixWord r) +
          5 ^ (d.suffixWord r).length *
            StringFlow.Word.wordOrbit
              (w.take (cycleRiseBlockTailDepth d r)) m := by
      simpa [cycleRiseBlockC3TailState, cycleRiseBlockTailDepth] using hid
    simpa [hWj] using hhid.symm
  rw [hmap]

/-- Sum of the rotated-word equations at every C3-tail boundary:
`Σ q_r·(2^S−5^P)` is the sum of the block-rotated `wordA` values. -/
theorem cycleRiseBlockRotatedWordAEquationSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w)
    (hLle : ∀ r : Nat, r < d.blockCount →
      (d.suffixWord r).length ≤ w.length) :
    ((List.range d.blockCount).map
      (fun r => StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m * (2 ^ S - 5 ^ P))).sum =
      ((List.range d.blockCount).map
        (fun r => StringFlow.Word.wordA
          (d.suffixWord r ++
            (cyclicSegmentAt w
              ((cycleRiseBlockTailDepth d r + (d.suffixWord r).length) %
                w.length)).take
                (w.length - (d.suffixWord r).length)))).sum := by
  have hmap : (List.range d.blockCount).map
      (fun r => StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r)) m * (2 ^ S - 5 ^ P)) =
    (List.range d.blockCount).map
      (fun r => StringFlow.Word.wordA
        (d.suffixWord r ++
          (cyclicSegmentAt w
            ((cycleRiseBlockTailDepth d r + (d.suffixWord r).length) %
              w.length)).take
              (w.length - (d.suffixWord r).length))) := by
    apply List.map_congr_left
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    exact cycleRiseBlockRotatedWordA_eq_suffix_append h d r hrlt (hLle r hrlt)
  rw [hmap]

/-- The exact per-block residual rearrangement of
`cycleRiseBlockC3ChainRankGain`:
`Σresidual_r = R_r + Σ(c3Word r) − 2`. -/
theorem cycleRiseBlockC3ResidualSum_eq_tailRank_add_c3Weight_sub_two
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    cycleRiseBlockC3ResidualSum d r =
      cycleRiseBlockTailRank d r + (d.c3Word r).sum - 2 := by
  have h := cycleRiseBlockC3ChainRankGain d r hr
  simp [cycleRiseBlockC3ResidualSum] at h ⊢
  omega

/-- The boundary rank is the 2-adic valuation of the rotated-word
numerator plus the cycle slack:
`R_r = v2(wordA (rotation at b_r) + (2^S − 5^P))`.
This follows from `q_r·(2^S−5^P) = wordA (rotation at b_r)` and the
oddness of `2^S−5^P`; it is the exact bridge that lets the whole-cycle
`A_P` expansion speak about the boundary ranks. -/
theorem cycleRiseBlockTailRank_eq_v2_rotated_plus_delta
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    cycleRiseBlockTailRank d r =
      twoValuation (StringFlow.Word.wordA
        (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)) + (2 ^ S - 5 ^ P)) := by
  let b := cycleRiseBlockTailDepth d r
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hb : b ≤ w.length := by
    dsimp [b]
    have hblt : cycleRiseBlockTailDepth d r - 1 < P :=
      cycleRiseBlockTailDepth_lt_succ d r hr
    rw [d.hperiod]
    omega
  have hrot := cycleQb8Input_rotated_wordA h b hb
  have hlt := cycleQb8Input_weak_comparison h
  have hSpos : 1 ≤ S := by
    by_contra hnot
    have hS0 : S = 0 := by omega
    rw [hS0] at hlt
    norm_num at hlt
  have hdelta_pos : 0 < 2 ^ S - 5 ^ P := by omega
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
  have hdelta_odd : (2 ^ S - 5 ^ P) % 2 = 1 :=
    Nat.odd_iff.mp hdelta_odd'
  have hv2 : twoValuation
      ((2 ^ S - 5 ^ P) * (q + 1)) = twoValuation (q + 1) :=
    StringFlow.Lte.twoValuation_mul_odd (2 ^ S - 5 ^ P) (q + 1)
      hdelta_odd (by positivity)
  have hval : twoValuation
      (StringFlow.Word.wordA (cyclicSegmentAt w b) + (2 ^ S - 5 ^ P)) =
      twoValuation (q + 1) := by
    calc
      twoValuation (StringFlow.Word.wordA (cyclicSegmentAt w b) + (2 ^ S - 5 ^ P))
          = twoValuation (q * (2 ^ S - 5 ^ P) + (2 ^ S - 5 ^ P)) := by
              rw [← hrot]
      _ = twoValuation ((2 ^ S - 5 ^ P) * (q + 1)) := by
              congr 1
              ring
      _ = twoValuation (q + 1) := hv2
  simp [cycleRiseBlockTailRank, cycleRiseBlockC3TailState, cycleRiseBlockTailDepth, b, q] at hval ⊢
  exact hval.symm

/-- Summed form of the boundary-rank valuation bridge:
`Σ R_r = Σ v2(wordA (rotation at b_r) + Δ)`.  This is the exact shape
in which the whole-cycle `A_P` expansion and `2^S > 5^P` can speak to
the summed boundary ranks. -/
theorem cycleRiseBlockTailRankSum_eq_v2_rotated_plus_delta_sum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
      (fun r => cycleRiseBlockTailRank d r)).sum =
      ((List.range d.blockCount).map
        (fun r => twoValuation
          (StringFlow.Word.wordA
            (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)) +
            (2 ^ S - 5 ^ P)))).sum := by
  have hmap : (List.range d.blockCount).map
      (fun r => cycleRiseBlockTailRank d r) =
    (List.range d.blockCount).map
      (fun r => twoValuation
        (StringFlow.Word.wordA
          (cyclicSegmentAt w (cycleRiseBlockTailDepth d r)) +
          (2 ^ S - 5 ^ P))) := by
    apply List.map_congr_left
    intro r hr
    exact cycleRiseBlockTailRank_eq_v2_rotated_plus_delta
      h d r (List.mem_range.mp hr)
  rw [hmap]

end StringFlow.CycleBridge
