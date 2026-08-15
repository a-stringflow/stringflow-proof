import RunDecomposition
import C4C8Tail

set_option maxHeartbeats 800000

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
  · intro r hr
    intro t ht
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
  · intro r hr
    intro k hk
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
  · intro r hr
    intro k hk
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
  · intro r hr
    intro t ht
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
  · intro r hr
    intro k hk
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
  · intro r hr
    intro k hk
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

/-- The real cyclic rise decomposition plus the tail-charged PMI
comparison yield a C3-tail failure.  Structural existence is now
closed; only the PMI comparison remains an input. -/
theorem cycleRiseBlockFailure_of_real_input_and_global_comparison
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (hglobal : cycleRiseBlockPMIGlobalComparisonHolds) :
    ∃ d : CycleRiseBlockDecomposition m S P w,
      ∃ r : Nat, r < d.blockCount ∧
        2 * (cycleRiseBlockTailDepth d r -
            cycleRiseBlockTailResetWeight d r) + 13 ≤
          cycleRiseBlockTailRank d r := by
  rcases cycleRiseBlockDecompositionExists_of_input h with ⟨d, _hdpos⟩
  exact ⟨d, cycleRiseBlockTailFailure_of_global_comparison d
    (hglobal m S P w rise c3 h d)⟩

/-- The real cyclic rise decomposition plus the tail-charged PMI
comparison supply the C3-tail failure window. -/
theorem cycleRiseBlockTailFailureWindowExistence_of_pmi
    (hglobal : cycleRiseBlockPMIGlobalComparisonHolds) :
    cycleRiseBlockTailFailureWindowExistence := by
  intro m S P w rise c3 h
  rcases cycleRiseBlockDecompositionExists_of_input h with ⟨d, _hdpos⟩
  refine ⟨d, ?_⟩
  exact cycleRiseBlockTailFailureWindow_of_global_comparison h d
    (hglobal m S P w rise c3 h d)

end StringFlow.CycleBridge
