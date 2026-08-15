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

/-- Direct construction of the block-head predecessor identity
(`hpred`) from the real boundary terminal.  The proof instantiates the
real terminal, the cyclic prefix occurrence with its exact incoming
edge, the exact word identity for the rise prefix, and the exact
boundary-terminal identity `rt.r = 2^(w[b-1]-1) * q`.  After this
algebraic reduction, `hpred` is exactly the word equation

`wordA u' + 5^(L-1)*q = 2^(weight u' + c - 1)*q + delta*2^(weight u')*5^(L-1)`

for the rise prefix `u'` of length `L-1`; that word equation is the
single remaining step, to be supplied by the cyclic block equations of
`CycleQb8Input` (delta-zero block structure, real orbit occurrence,
boundary-terminal identity).  No size estimate and no C3-rank input is
used. -/
theorem cycleRiseBlockHpred_of_real_terminal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hne : d.suffixWord r ≠ [])
    (hLle : (d.suffixWord r).length ≤ w.length)
    (t delta : Nat)
    (ht_last : t = (d.suffixWord r).getI ((d.suffixWord r).length - 1))
    (ht : t = 1 ∨ t = 2)
    (hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3))
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
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
  -- E5 is not a new consequence of the block equation: the block
  -- equation only rewrites the left-hand side to the word-equation
  -- side.  E5 is equivalent to the predecessor identity itself,
  -- `o_local(L-1) = rt.r + delta*5^(L-1)`, hence to `hterm`.  Its
  -- source is therefore the delta-zero block property of this
  -- specific block (the reset equation holds), which is exactly
  -- `hterm`; whether the cycle closure/PMI forces this property is
  -- exactly what remains to be derived.
  have hE5 : StringFlow.Word.wordA u' + 5 ^ (L - 1) * q =
      2 ^ ((StringFlow.wordWeight u' + w.getI (b - 1)) - 1) * q +
        delta * 2 ^ StringFlow.wordWeight u' * 5 ^ (L - 1) := by
    have hDpos : 0 < 2 ^ S - 5 ^ P := by
      rcases h.hcycle with ⟨hcp⟩
      rcases hcp with ⟨cp, hprops⟩
      rcases hprops with ⟨hw, hm⟩
      rcases hm with ⟨hm, hS⟩
      rcases hS with ⟨hS, _hr, _hc⟩
      have hclosed' : StringFlow.Word.wordOrbit
          (cycleWord cp.1 cp.2) (fiveXPlusOneOrbit 7 cp.1) =
          fiveXPlusOneOrbit 7 cp.1 := by
        simpa [hw, hm] using h.hclosed
      have hP : P = cp.2 := by
        rw [← h.hlength, hw, cycleWord_length cp.1 cp.2]
      have hp : 1 ≤ cp.2 := by
        have hPge2 : 2 ≤ P := cycleQb8Input_P_ge_two h
        omega
      have hD := cycleWord_D_pos cp.1 cp.2 hclosed' hp
      have hS' : S = cycleWordTotalWeight cp.1 cp.2 := by
        dsimp [cycleWordTotalWeight]
        exact hS
      simpa [hS', hP] using hD
    have hqD : q * (2 ^ S - 5 ^ P) =
        StringFlow.Word.wordA (cyclicSegmentAt w b) := by
      exact cycleQb8Input_rotated_wordA h b hble
    apply Nat.eq_of_mul_eq_mul_left hDpos
    rw [Nat.mul_add, Nat.mul_add]
    ring_nf
    rw [Nat.mul_comm (2 ^ S - 5 ^ P) q]
    rw [hqD]
    have hrot_split : cyclicSegmentAt w b =
        u' ++ [t] ++ (cyclicSegmentAt w b).drop L := by
      have hLlt : L - 1 < (cyclicSegmentAt w b).length := by
        rw [cyclicSegmentAt_length w b hble]
        omega
      have htc := List.take_concat_get (l := cyclicSegmentAt w b) (i := L - 1) hLlt
      have hget : (cyclicSegmentAt w b)[L - 1] = t := by
        have hg := List.getI_eq_getElem (l := cyclicSegmentAt w b) (n := L - 1) hLlt
        rw [← hg]
        exact ht_last'.symm
      have htake : (cyclicSegmentAt w b).take L = u' ++ [t] := by
        have htc' : (cyclicSegmentAt w b).take (L - 1) ++
            [(cyclicSegmentAt w b)[L - 1]] = (cyclicSegmentAt w b).take L := by
          have hsub : L - 1 + 1 = L := Nat.sub_add_cancel hLpos
          rw [List.concat_eq_append] at htc
          simpa [hsub] using htc
        rw [hget] at htc'
        change (cyclicSegmentAt w b).take L = u' ++ [t]
        exact htc'.symm
      have hsplit : cyclicSegmentAt w b =
          (cyclicSegmentAt w b).take L ++ (cyclicSegmentAt w b).drop L :=
        (List.take_append_drop L (cyclicSegmentAt w b)).symm
      rw [htake] at hsplit
      simpa [List.append_assoc] using hsplit
    sorry
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

end StringFlow.CycleBridge
