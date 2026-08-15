import RealOrbitCharge

namespace StringFlow.CycleBridge

open S6Audit

/-- Length of the rise run starting at cyclic boundary `b`. -/
def blockRiseLen (w : List Nat) (b : Nat) : Nat :=
  risePrefixLength (cyclicSegmentAt w b)

/-- Length of the C3 run ending just before cyclic boundary `b`. -/
def blockC3Len (w : List Nat) (b : Nat) : Nat :=
  c3SuffixLengthAt w b

/-- The next rise-run start after the rise run at `b` and the C3 run
that follows it. -/
def nextRiseStart (w : List Nat) (P : Nat) (b : Nat) : Nat :=
  ((b + blockRiseLen w b) % P + c3PrefixLength
    (cyclicSegmentAt w ((b + blockRiseLen w b) % P))) % P

/-- The C3 run ending before `b` and the rise run starting at `b` are
disjoint: their lengths together never exceed the period. -/
theorem blockCover_le
    {w : List Nat} {P b : Nat}
    (hw : w.length = P)
    (hb : b ≤ w.length)
    (hb1 : 1 ≤ b)
    (hprev : 3 ≤ w.getI (b - 1)) :
    blockC3Len w b + blockRiseLen w b ≤ P := by
  by_contra hnot
  have hgt : P < blockC3Len w b + blockRiseLen w b := Nat.lt_of_not_ge hnot
  have hc3le : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
  have hc3pos : 0 < blockC3Len w b :=
    c3SuffixLengthAt_pos_of_head w b hb1 hprev
  let i := P - blockC3Len w b
  have hi_lt : i < blockRiseLen w b := by
    dsimp [i]
    have hc3leP : blockC3Len w b ≤ P := by omega
    omega
  have hrise_mem := risePrefixLength_mem (cyclicSegmentAt w b) i hi_lt
  have hlenSeg : (cyclicSegmentAt w b).length = w.length :=
    cyclicSegmentAt_length w b hb
  have hrise_le : blockRiseLen w b ≤ w.length := by
    calc
      risePrefixLength (cyclicSegmentAt w b) ≤
          (cyclicSegmentAt w b).length := risePrefixLength_le _
      _ = w.length := hlenSeg
  have hilt : i < w.length := by omega
  have hmod := cyclicSegmentAt_getI_mod w b i hb hilt
  have hidx : (b + i) % w.length = b - blockC3Len w b := by
    dsimp [i]
    rw [hw]
    have hbge : blockC3Len w b ≤ b := hc3le
    have hlt : b - blockC3Len w b < w.length := by
      rw [hw]
      omega
    have hsum : (b + (w.length - blockC3Len w b)) % w.length =
        (b - blockC3Len w b) % w.length := by
      have hadd : b + (w.length - blockC3Len w b) =
          (b - blockC3Len w b) + w.length := by omega
      rw [hadd, Nat.add_mod_right]
    rw [hw] at hsum
    rw [hsum]
    rw [← hw]
    exact Nat.mod_eq_of_lt hlt
  rw [hidx] at hmod
  rcases hrise_mem with hr1 | hr2
  · rw [hr1] at hmod
    have hwget : w.getI (b - blockC3Len w b) = 1 :=
      hmod.symm
    have hc3at : 3 ≤ w.getI (b - blockC3Len w b) := by
      have hk : blockC3Len w b - 1 < blockC3Len w b := by omega
      have hmem := c3SuffixLengthAt_mem w b hb (blockC3Len w b - 1) hk
      have hindex : b - 1 - (blockC3Len w b - 1) = b - blockC3Len w b := by omega
      simpa [hindex] using hmem
    rw [hwget] at hc3at
    omega
  · rw [hr2] at hmod
    have hwget : w.getI (b - blockC3Len w b) = 2 :=
      hmod.symm
    have hc3at : 3 ≤ w.getI (b - blockC3Len w b) := by
      have hk : blockC3Len w b - 1 < blockC3Len w b := by omega
      have hmem := c3SuffixLengthAt_mem w b hb (blockC3Len w b - 1) hk
      have hindex : b - 1 - (blockC3Len w b - 1) = b - blockC3Len w b := by omega
      simpa [hindex] using hmem
    rw [hwget] at hc3at
    omega

/-- The C3 segment of the block ending at boundary `b`: the maximal C3
run immediately before `b`. -/
def blockC3Word (w : List Nat) (b : Nat) : List Nat :=
  (w.take b).drop (b - blockC3Len w b)

/-- The rise segment of the block starting at boundary `b`. -/
def blockSuffixWord (w : List Nat) (b : Nat) : List Nat :=
  (cyclicSegmentAt w b).take (blockRiseLen w b)

/-- Depth of the block head: the start of the C3 segment. -/
def blockHeadDepth (w : List Nat) (b : Nat) : Nat :=
  b - blockC3Len w b

/-- The C3 segment has exactly the C3-run length. -/
theorem blockC3Word_length
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    (blockC3Word w b).length = blockC3Len w b := by
  unfold blockC3Word
  have hle : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
  have htake : (w.take b).length = b := List.length_take_of_le hb
  rw [List.length_drop, htake]
  omega

/-- The `k`-th entry of the C3 segment is the word entry at the
corresponding position. -/
theorem blockC3Word_getI
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (k : Nat)
    (hk : k < blockC3Len w b) :
    (blockC3Word w b).getI k = w.getI (b - blockC3Len w b + k) := by
  unfold blockC3Word
  have hk' : k < ((w.take b).drop (b - blockC3Len w b)).length := by
    rw [List.length_drop]
    have htake : (w.take b).length = b := List.length_take_of_le hb
    rw [htake]
    have hc3le : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
    omega
  rw [List.getI_eq_getElem (l := (w.take b).drop (b - blockC3Len w b)) (n := k) hk']
  have hdrop := List.getElem_drop
    (xs := w.take b) (i := b - blockC3Len w b) (j := k) (h := hk')
  rw [hdrop]
  have hlt : b - blockC3Len w b + k < (w.take b).length := by
    rw [List.length_take_of_le hb]
    have hc3le : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
    omega
  have htake := List.getElem_take
    (xs := w) (j := b) (i := b - blockC3Len w b + k) (h := hlt)
  rw [htake]
  have hltw : b - blockC3Len w b + k < w.length := by
    rw [List.length_take_of_le hb] at hlt
    omega
  rw [List.getI_eq_getElem (l := w) (n := b - blockC3Len w b + k) hltw]

/-- The rise segment has exactly the rise-run length. -/
theorem blockSuffixWord_length (w : List Nat) (b : Nat) :
    (blockSuffixWord w b).length = blockRiseLen w b := by
  unfold blockSuffixWord
  exact List.length_take_of_le (risePrefixLength_le (cyclicSegmentAt w b))

/-- The `k`-th entry of the rise segment is the cyclic word entry. -/
theorem blockSuffixWord_getI
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (k : Nat)
    (hk : k < blockRiseLen w b) :
    (blockSuffixWord w b).getI k = w.getI ((b + k) % w.length) := by
  unfold blockSuffixWord
  have hk' : k < ((cyclicSegmentAt w b).take (blockRiseLen w b)).length := by
    dsimp [blockRiseLen]
    rw [List.length_take_of_le (risePrefixLength_le (cyclicSegmentAt w b))]
    exact hk
  rw [List.getI_eq_getElem
    (l := (cyclicSegmentAt w b).take (blockRiseLen w b)) (n := k) hk']
  have htake := List.getElem_take
    (xs := cyclicSegmentAt w b) (j := blockRiseLen w b) (i := k) (h := hk')
  rw [htake]
  have hilt : k < w.length := by
    have hle := risePrefixLength_le (cyclicSegmentAt w b)
    have hseg := cyclicSegmentAt_length w b hb
    have hklt : k < risePrefixLength (cyclicSegmentAt w b) := by
      simpa [blockRiseLen] using hk
    omega
  have hmod := cyclicSegmentAt_getI_mod w b k hb hilt
  have hiltSeg : k < (cyclicSegmentAt w b).length := by
    rwa [cyclicSegmentAt_length w b hb]
  rw [← List.getI_eq_getElem (l := cyclicSegmentAt w b) (n := k) hiltSeg]
  rw [hmod]

/-- The block head is a valid non-wrapping word depth. -/
theorem blockHeadDepth_lt_P
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hb : b ≤ w.length)
    (hb1 : 1 ≤ b) (hprev : 3 ≤ w.getI (b - 1)) :
    blockHeadDepth w b < P := by
  unfold blockHeadDepth
  have hc3pos : 0 < blockC3Len w b := c3SuffixLengthAt_pos_of_head w b hb1 hprev
  have hc3le : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
  rw [← hw]
  omega

/-- Because the cycle starts with a rise step, the block head is at
least one. -/
theorem blockHeadDepth_pos_of_rise_start
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (hb1 : 1 ≤ b)
    (hprev : 3 ≤ w.getI (b - 1))
    (hrise0 : w.getI 0 = 1 ∨ w.getI 0 = 2) :
    1 ≤ blockHeadDepth w b := by
  unfold blockHeadDepth
  have hc3le : blockC3Len w b ≤ b := c3SuffixLengthAt_le w b hb
  by_contra hnot
  have hle0 : b - blockC3Len w b = 0 := by omega
  have hb_eq : b = blockC3Len w b := by omega
  have hpos : 0 < blockC3Len w b := c3SuffixLengthAt_pos_of_head w b hb1 hprev
  have hk : blockC3Len w b - 1 < blockC3Len w b := by omega
  have hmem := c3SuffixLengthAt_mem w b hb (blockC3Len w b - 1) hk
  have hindex : b - 1 - (blockC3Len w b - 1) = 0 := by omega
  rw [hindex] at hmem
  rcases hrise0 with h1 | h2
  · rw [h1] at hmem
    omega
  · rw [h2] at hmem
    omega

/-- The sequence of rise-run starts obtained by iterating the next
boundary map. -/
def riseBoundaryIter (w : List Nat) (P : Nat) (b : Nat) : Nat → Nat
  | 0 => b
  | n + 1 => nextRiseStart w P (riseBoundaryIter w P b n)

/-- Number of rise-run starts in one full cyclic tour: `1` plus the
number of further steps needed to return to the starting boundary. -/
def riseRunCycleLenAux (w : List Nat) (P fuel b0 b : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
      if b = b0 then 0
      else 1 + riseRunCycleLenAux w P fuel b0 (nextRiseStart w P b)

/-- Number of cyclic blocks starting at boundary `b0`. -/
def riseRunCycleLen (w : List Nat) (P b0 : Nat) : Nat :=
  1 + riseRunCycleLenAux w P P b0 (nextRiseStart w P b0)

/-- `blockCountOf` is the number of rise runs in the cyclic
decomposition starting at `b0`. -/
def blockCountOf (w : List Nat) (P b0 : Nat) : Nat :=
  riseRunCycleLen w P b0

/-- The next boundary is a valid modular position. -/
theorem nextRiseStart_lt {P : Nat} (hP : 0 < P) (w : List Nat) (b : Nat) :
    nextRiseStart w P b < P := by
  unfold nextRiseStart
  exact Nat.mod_lt _ hP

/-- The successor boundary of the iteration is the next rise start. -/
theorem riseBoundaryIter_succ (w : List Nat) (P b : Nat) (n : Nat) :
    riseBoundaryIter w P b (n + 1) =
      nextRiseStart w P (riseBoundaryIter w P b n) :=
  rfl

/-- A cyclic rise decomposition always has at least one block. -/
theorem blockCountOf_pos (w : List Nat) (P b0 : Nat) :
    1 ≤ blockCountOf w P b0 := by
  unfold blockCountOf riseRunCycleLen
  omega

/-- The forward advance from one rise-run start to the next: the rise
run plus the C3 run that follows it. -/
def blockAdvance (w : List Nat) (P : Nat) (b : Nat) : Nat :=
  blockRiseLen w b + c3PrefixLength
    (cyclicSegmentAt w ((b + blockRiseLen w b) % P))

/-- A rise-run start with a rise entry gives a nonempty rise run. -/
theorem blockRiseLen_pos_of_boundary
    (w : List Nat) (b : Nat) (hb : b ≤ w.length)
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2) :
    1 ≤ blockRiseLen w b := by
  unfold blockRiseLen
  have h0 : isRiseStep ((cyclicSegmentAt w b).getI 0) := by
    rw [cyclicSegmentAt_head w b hb]
    exact hnext
  exact risePrefixLength_pos_of_head (cyclicSegmentAt w b) h0

/-- The last entry of the cyclic segment is the entry before its start,
which is a C3 step at a C3-rise boundary. -/
lemma cyclicSegmentAt_last_getI
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (hb1 : 1 ≤ b)
    (hltw : b - 1 < w.length) :
    (cyclicSegmentAt w b).getI (w.length - 1) = w.getI (b - 1) := by
  have hilt : w.length - 1 < w.length := by omega
  have hmod := cyclicSegmentAt_getI_mod w b (w.length - 1) hb hilt
  have hsum : b + (w.length - 1) = (b - 1) + w.length := by omega
  have hidx : (b + (w.length - 1)) % w.length = b - 1 := by
    rw [hsum, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hltw
  rwa [hidx] at hmod

/-- After a maximal rise run, the next cyclic entry is a C3 step, so
the following C3 run is nonempty. -/
theorem c3AfterRise_pos
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (hb1 : 1 ≤ b)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev : 3 ≤ w.getI (b - 1)) :
    1 ≤ c3PrefixLength
      (cyclicSegmentAt w ((b + blockRiseLen w b) % w.length)) := by
  have hltw : b - 1 < w.length := by
    by_contra hnot
    have hge : w.length ≤ b - 1 := Nat.le_of_not_gt hnot
    have hzero : w.getI (b - 1) = 0 := by
      simpa using (List.getI_eq_default (l := w) (n := b - 1) hge)
    omega
  have hlenpos : 0 < w.length := by omega
  have hseg : (cyclicSegmentAt w b).length = w.length :=
    cyclicSegmentAt_length w b hb
  have hrise_le : blockRiseLen w b ≤ w.length := by
    unfold blockRiseLen
    calc
      risePrefixLength (cyclicSegmentAt w b) ≤
          (cyclicSegmentAt w b).length := risePrefixLength_le _
      _ = w.length := hseg
  have hne : blockRiseLen w b ≠ w.length := by
    intro heq
    have hlast := cyclicSegmentAt_last_getI w b hb hb1 hltw
    have hposR : 0 < blockRiseLen w b := by omega
    have heq' : risePrefixLength (cyclicSegmentAt w b) = w.length := by
      simpa [blockRiseLen] using heq
    have hmemArg : w.length - 1 < risePrefixLength (cyclicSegmentAt w b) := by
      have hlt : w.length - 1 < w.length := by omega
      rwa [heq']
    have hmem := risePrefixLength_mem (cyclicSegmentAt w b) (w.length - 1) hmemArg
    rw [hlast] at hmem
    rcases hmem with h1 | h2
    · rw [h1] at hprev
      omega
    · rw [h2] at hprev
      omega
  have hstoplt : blockRiseLen w b < (cyclicSegmentAt w b).length := by
    rw [hseg]
    exact lt_of_le_of_ne hrise_le hne
  have hposSeg : ∀ x, x ∈ cyclicSegmentAt w b → 1 ≤ x := by
    intro x hx
    exact hpos x (cyclicSegmentAt_mem (w := w) (b := b) hx)
  have hstop := risePrefixLength_stop (cyclicSegmentAt w b) hposSeg hstoplt
  let mid := (b + blockRiseLen w b) % w.length
  have hmidle : mid ≤ w.length := le_of_lt (Nat.mod_lt _ hlenpos)
  have hhead := cyclicSegmentAt_head w mid hmidle
  have hmidmod : mid % w.length = mid := Nat.mod_eq_of_lt (Nat.mod_lt _ hlenpos)
  have hilt : blockRiseLen w b < w.length := by
    rw [hseg] at hstoplt
    exact hstoplt
  have hmod := cyclicSegmentAt_getI_mod w b (blockRiseLen w b) hb hilt
  have hsegget : (cyclicSegmentAt w b).getI (blockRiseLen w b) =
      (cyclicSegmentAt w mid).getI 0 := by
    rw [hmod, hhead, hmidmod]
  have h3 : 3 ≤ (cyclicSegmentAt w mid).getI 0 := by
    rwa [← hsegget]
  apply c3PrefixLength_pos_of_head (cyclicSegmentAt w mid)
  exact h3

/-- Each cyclic block advances by at least two word positions. -/
theorem blockAdvance_pos
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P)
    (hb : b ≤ w.length) (hb1 : 1 ≤ b)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev : 3 ≤ w.getI (b - 1))
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2) :
    2 ≤ blockAdvance w P b := by
  unfold blockAdvance
  have hr : 1 ≤ blockRiseLen w b :=
    blockRiseLen_pos_of_boundary w b hb hnext
  have hc0 := c3AfterRise_pos w b hb hb1 hpos hprev
  have hc : 1 ≤ c3PrefixLength
      (cyclicSegmentAt w ((b + blockRiseLen w b) % P)) := by
    rw [hw] at hc0
    exact hc0
  omega

/-- The next boundary is exactly the current boundary advanced by the
block advance, reduced modulo the period. -/
theorem nextRiseStart_eq_add_blockAdvance
    (w : List Nat) (P b : Nat) :
    nextRiseStart w P b = (b + blockAdvance w P b) % P := by
  unfold nextRiseStart blockAdvance
  let r := blockRiseLen w b
  let c := c3PrefixLength (cyclicSegmentAt w ((b + blockRiseLen w b) % P))
  change ((b + r) % P + c) % P = (b + (r + c)) % P
  have h : (b + (r + c)) % P = ((b + r) % P + c) % P := by
    calc
      (b + (r + c)) % P = ((b + r) + c) % P := by rw [Nat.add_assoc]
      _ = ((b + r) % P + c) % P := by rw [Nat.mod_add_mod]
  exact h.symm

/-- The cycle-length counter never exceeds its fuel. -/
theorem riseRunCycleLenAux_le_fuel
    (w : List Nat) (P fuel b0 b : Nat) :
    riseRunCycleLenAux w P fuel b0 b ≤ fuel := by
  induction fuel generalizing b with
  | zero =>
      simp [riseRunCycleLenAux]
  | succ fuel ih =>
      by_cases hb : b = b0
      · simp [riseRunCycleLenAux, hb]
      · simp [riseRunCycleLenAux, hb]
        have h := ih (nextRiseStart w P b)
        omega

/-- A first upper bound on the block count: at most one plus the period. -/
theorem blockCountOf_le_succ_P (w : List Nat) (P b0 : Nat) :
    blockCountOf w P b0 ≤ P + 1 := by
  unfold blockCountOf riseRunCycleLen
  have h := riseRunCycleLenAux_le_fuel w P P b0 (nextRiseStart w P b0)
  omega

/-- Total forward advance accumulated over the first `n` blocks. -/
def blockTotalAdvance (w : List Nat) (P b0 : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      blockTotalAdvance w P b0 n +
        blockAdvance w P (riseBoundaryIter w P b0 n)

/-- The `n`-th boundary is the starting boundary advanced by the total
block advance, reduced modulo the period. -/
theorem riseBoundaryIter_eq_add_totalAdvance
    (w : List Nat) (P b0 : Nat) (hb0 : b0 < P) (n : Nat) :
    riseBoundaryIter w P b0 n =
      (b0 + blockTotalAdvance w P b0 n) % P := by
  induction n with
  | zero =>
      simp [riseBoundaryIter, blockTotalAdvance, Nat.mod_eq_of_lt hb0]
  | succ n ih =>
      rw [riseBoundaryIter_succ]
      rw [nextRiseStart_eq_add_blockAdvance]
      dsimp [blockTotalAdvance]
      rw [ih]
      let T := blockTotalAdvance w P b0 n
      let A := blockAdvance w P ((b0 + T) % P)
      change ((b0 + T) % P + A) % P = (b0 + (T + A)) % P
      have hmod : ((b0 + T) % P + A) % P = (b0 + (T + A)) % P := by
        calc
          ((b0 + T) % P + A) % P = ((b0 + T) + A) % P :=
            Nat.mod_add_mod (b0 + T) P A
          _ = (b0 + (T + A)) % P := by rw [Nat.add_assoc]
      exact hmod

/-- With every block advancing at least two, the total advance after
`n` blocks is at least `2*n`. -/
theorem blockTotalAdvance_ge_two_mul
    (w : List Nat) (P b0 : Nat) (n : Nat)
    (hall : ∀ k < n, 2 ≤ blockAdvance w P (riseBoundaryIter w P b0 k)) :
    2 * n ≤ blockTotalAdvance w P b0 n := by
  induction n with
  | zero =>
      simp [blockTotalAdvance]
  | succ n ih =>
      simp [blockTotalAdvance]
      have h := hall n (by omega)
      have ih' := ih (fun k hk => hall k (by omega))
      omega

/-- A single rise run never exceeds the period. -/
theorem blockRiseLen_le_P
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hb : b ≤ w.length) :
    blockRiseLen w b ≤ P := by
  unfold blockRiseLen
  have hlen := cyclicSegmentAt_length w b hb
  calc
    risePrefixLength (cyclicSegmentAt w b) ≤
        (cyclicSegmentAt w b).length := risePrefixLength_le _
    _ = w.length := hlen
    _ = P := hw

/-- A single C3 run never exceeds the period. -/
theorem c3PrefixLength_le_P
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hb : b ≤ w.length) :
    c3PrefixLength (cyclicSegmentAt w b) ≤ P := by
  have hlen := cyclicSegmentAt_length w b hb
  calc
    c3PrefixLength (cyclicSegmentAt w b) ≤
        (cyclicSegmentAt w b).length := c3PrefixLength_le _
    _ = w.length := hlen
    _ = P := hw

end StringFlow.CycleBridge
