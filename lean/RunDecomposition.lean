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

/-- Dropping `n` entries from a cyclic segment gives the next cyclic
segment restricted to the remaining positions. -/
lemma cyclicSegmentAt_drop_take
    (w : List Nat) (b n : Nat) (hb : b ≤ w.length) (hn : n ≤ w.length)
    (hlenpos : 0 < w.length) :
    (cyclicSegmentAt w b).drop n =
      (cyclicSegmentAt w ((b + n) % w.length)).take (w.length - n) := by
  have hseg : (cyclicSegmentAt w b).length = w.length :=
    cyclicSegmentAt_length w b hb
  have hmidle : (b + n) % w.length ≤ w.length :=
    le_of_lt (Nat.mod_lt _ hlenpos)
  have hseg' : (cyclicSegmentAt w ((b + n) % w.length)).length = w.length :=
    cyclicSegmentAt_length w ((b + n) % w.length) hmidle
  refine List.ext_getElem ?hlen ?hget
  · rw [List.length_drop, hseg]
    have htl : ((cyclicSegmentAt w ((b + n) % w.length)).take
        (w.length - n)).length = w.length - n :=
      List.length_take_of_le (le_trans (Nat.sub_le w.length n)
        (le_of_eq hseg'.symm))
    rw [htl]
  · intro i hi1 hi2
    have hilt : n + i < w.length := by
      rw [List.length_drop, hseg] at hi1
      omega
    have hilt2 : i < w.length := by
      have htakeLen : ((cyclicSegmentAt w ((b + n) % w.length)).take
          (w.length - n)).length = w.length - n :=
        List.length_take_of_le (le_trans (Nat.sub_le w.length n)
          (le_of_eq hseg'.symm))
      rw [htakeLen] at hi2
      omega
    have hmod := cyclicSegmentAt_getI_mod w b (n + i) hb hilt
    have hmod' := cyclicSegmentAt_getI_mod w ((b + n) % w.length) i hmidle hilt2
    have hmodEq : (b + (n + i)) % w.length =
        ((b + n) % w.length + i) % w.length := by
      calc
        (b + (n + i)) % w.length = ((b + n) + i) % w.length := by rw [Nat.add_assoc]
        _ = ((b + n) % w.length + i) % w.length :=
          (Nat.mod_add_mod (b + n) w.length i).symm
    have h1 : (cyclicSegmentAt w b).getI (n + i) =
        (cyclicSegmentAt w ((b + n) % w.length)).getI i := by
      rw [hmod, hmod', hmodEq]
    have hd := List.getElem_drop
      (xs := cyclicSegmentAt w b) (i := n) (j := i) (h := hi1)
    have ht := List.getElem_take
      (xs := cyclicSegmentAt w ((b + n) % w.length))
      (j := w.length - n) (i := i) (h := hi2)
    rw [hd, ht]
    have hgetL := List.getI_eq_getElem
      (l := cyclicSegmentAt w b) (n := n + i) (by rwa [hseg])
    have hgetR := List.getI_eq_getElem
      (l := cyclicSegmentAt w ((b + n) % w.length)) (n := i) (by rwa [hseg'])
    rw [hgetL, hgetR] at h1
    exact h1

/-- The forward advance of one block never exceeds the period. -/
theorem blockAdvance_le_P
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P)
    (hb : b ≤ w.length) (_hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2) :
    blockAdvance w P b ≤ P := by
  unfold blockAdvance
  have hlenpos : 0 < w.length := by
    by_contra hnot
    have hw0 : w.length = 0 := Nat.eq_zero_of_not_pos hnot
    have hb0 : b = 0 := by omega
    subst b
    have hz : w.getI 0 = 0 := by
      have hge : w.length ≤ 0 := by omega
      simpa using (List.getI_eq_default (l := w) (n := 0) hge)
    have hnext' : w.getI 0 = 1 ∨ w.getI 0 = 2 := by
      simpa [hw0] using hnext
    rcases hnext' with h1 | h2
    · rw [h1] at hz
      omega
    · rw [h2] at hz
      omega
  let mid := (b + blockRiseLen w b) % w.length
  have hmidle : mid ≤ w.length := le_of_lt (Nat.mod_lt _ hlenpos)
  have hc3le : c3PrefixLength (cyclicSegmentAt w mid) ≤
      w.length - blockRiseLen w b := by
    by_contra hnot
    have hlt : w.length - blockRiseLen w b <
        c3PrefixLength (cyclicSegmentAt w mid) := Nat.lt_of_not_ge hnot
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w mid)
      (w.length - blockRiseLen w b) hlt
    have hilt : w.length - blockRiseLen w b < w.length := by
      have hr : blockRiseLen w b ≤ w.length := by
        simpa [hw] using blockRiseLen_le_P w P b hw hb
      have hposR : 0 < blockRiseLen w b :=
        blockRiseLen_pos_of_boundary w b hb hnext
      exact Nat.sub_lt hlenpos hposR
    have hmod := cyclicSegmentAt_getI_mod w mid
      (w.length - blockRiseLen w b) hmidle hilt
    have hidx : (mid + (w.length - blockRiseLen w b)) % w.length =
        b % w.length := by
      dsimp [mid]
      have hr : blockRiseLen w b ≤ w.length := by
        simpa [hw] using blockRiseLen_le_P w P b hw hb
      have hsum : b + blockRiseLen w b + (w.length - blockRiseLen w b) =
          b + w.length := by omega
      calc
        ((b + blockRiseLen w b) % w.length +
            (w.length - blockRiseLen w b)) % w.length
            = (b + blockRiseLen w b + (w.length - blockRiseLen w b)) % w.length :=
              Nat.mod_add_mod (b + blockRiseLen w b)
                w.length (w.length - blockRiseLen w b)
        _ = (b + w.length) % w.length := by rw [hsum]
        _ = b % w.length := by rw [Nat.add_mod_right]
    rw [hmod, hidx] at hmem
    rcases hnext with h1 | h2
    · rw [h1] at hmem
      omega
    · rw [h2] at hmem
      omega
  have hc3le' : c3PrefixLength
      (cyclicSegmentAt w ((b + blockRiseLen w b) % P)) ≤
        P - blockRiseLen w b := by
    simpa [mid, hw] using hc3le
  have hr : blockRiseLen w b ≤ P := blockRiseLen_le_P w P b hw hb
  omega

/-- From the first step on, every boundary of the iteration is a valid
modular position. -/
theorem riseBoundaryIter_mod
    {P : Nat} (hP : 0 < P) (w : List Nat) (b : Nat) (n : Nat) :
    riseBoundaryIter w P b (n + 1) < P := by
  induction n with
  | zero =>
      simp [riseBoundaryIter]
      exact nextRiseStart_lt hP w b
  | succ n ih =>
      simp [riseBoundaryIter]
      exact nextRiseStart_lt hP w (riseBoundaryIter w P b (n + 1))

/-- Every block advance lies in the interval `[2, P]`. -/
theorem blockAdvance_two_le_le_P
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P)
    (hb : b ≤ w.length) (hb1 : 1 ≤ b)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev : 3 ≤ w.getI (b - 1))
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2) :
    2 ≤ blockAdvance w P b ∧ blockAdvance w P b ≤ P := by
  constructor
  · exact blockAdvance_pos w P b hw hb hb1 hpos hprev hnext
  · exact blockAdvance_le_P w P b hw hb hpos hnext

/-- The total advance strictly increases at every block. -/
theorem blockTotalAdvance_lt_succ
    (w : List Nat) (P b0 : Nat) (n : Nat)
    (hpos : 2 ≤ blockAdvance w P (riseBoundaryIter w P b0 n)) :
    blockTotalAdvance w P b0 n < blockTotalAdvance w P b0 (n + 1) := by
  simp [blockTotalAdvance]
  omega

/-- `(x % P + P - 1)` is congruent to `x + P - 1` modulo `P`. -/
lemma mod_add_sub_one {P : Nat} (hP : 0 < P) (x : Nat) :
    (x % P + (P - 1)) % P = (x + (P - 1)) % P := by
  have hsub : (P - 1) % P = P - 1 := Nat.mod_eq_of_lt (by omega)
  simpa [hsub] using (Nat.mod_add_mod x P (P - 1))

/-- A cyclic rise-run start: `b` is a position modulo the period whose
entry is a rise step and whose previous cyclic entry is a C3 step. -/
def IsCyclicBoundary (w : List Nat) (P : Nat) (b : Nat) : Prop :=
  b < P ∧
  3 ≤ w.getI ((b + P - 1) % P) ∧
  (w.getI (b % P) = 1 ∨ w.getI (b % P) = 2)

/-- The last entry of the cyclic segment starting at zero is the last
entry of the word. -/
lemma cyclicSegmentAt_last_getI_wrap
    (w : List Nat) (P : Nat) (hw : w.length = P) (hP : 0 < P) :
    (cyclicSegmentAt w 0).getI (w.length - 1) = w.getI (w.length - 1) := by
  have hilt : w.length - 1 < w.length := by omega
  have hmod := cyclicSegmentAt_getI_mod w 0 (w.length - 1) (by simp) hilt
  have hidx : (0 + (w.length - 1)) % w.length = w.length - 1 := by
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt hilt
  simpa [hidx] using hmod

/-- After a maximal rise run starting at zero, the next cyclic entry
is a C3 step. -/
theorem c3AfterRise_pos_wrap
    (w : List Nat) (P : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    1 ≤ c3PrefixLength
      (cyclicSegmentAt w (blockRiseLen w 0 % w.length)) := by
  have hlenpos : 0 < w.length := by rw [hw]; exact hP
  have hseg : (cyclicSegmentAt w 0).length = w.length :=
    cyclicSegmentAt_length w 0 (by simp)
  have hrise_le : blockRiseLen w 0 ≤ w.length := by
    unfold blockRiseLen
    calc
      risePrefixLength (cyclicSegmentAt w 0) ≤
          (cyclicSegmentAt w 0).length := risePrefixLength_le _
      _ = w.length := hseg
  have hne : blockRiseLen w 0 ≠ w.length := by
    intro heq
    have hlast := cyclicSegmentAt_last_getI_wrap w P hw hP
    have hposR : 0 < blockRiseLen w 0 := by omega
    have heq' : risePrefixLength (cyclicSegmentAt w 0) = w.length := by
      simpa [blockRiseLen] using heq
    have hmemArg : w.length - 1 < risePrefixLength (cyclicSegmentAt w 0) := by
      have hlt : w.length - 1 < w.length := by omega
      rwa [heq']
    have hmem := risePrefixLength_mem (cyclicSegmentAt w 0) (w.length - 1) hmemArg
    rw [hlast] at hmem
    have hprev0' : 3 ≤ w.getI (w.length - 1) := by
      rw [← hw] at hprev0
      simpa using hprev0
    rcases hmem with h1 | h2
    · rw [h1] at hprev0'
      omega
    · rw [h2] at hprev0'
      omega
  have hstoplt : blockRiseLen w 0 < (cyclicSegmentAt w 0).length := by
    rw [hseg]
    exact lt_of_le_of_ne hrise_le hne
  have hposSeg : ∀ x, x ∈ cyclicSegmentAt w 0 → 1 ≤ x := by
    intro x hx
    exact hpos x (cyclicSegmentAt_mem (w := w) (b := 0) hx)
  have hstop := risePrefixLength_stop (cyclicSegmentAt w 0) hposSeg hstoplt
  let mid := blockRiseLen w 0 % w.length
  have hmidle : mid ≤ w.length := le_of_lt (Nat.mod_lt _ hlenpos)
  have hhead := cyclicSegmentAt_head w mid hmidle
  have hmidmod : mid % w.length = mid := Nat.mod_eq_of_lt (Nat.mod_lt _ hlenpos)
  have hilt : blockRiseLen w 0 < w.length := by
    rw [hseg] at hstoplt
    exact hstoplt
  have hmod := cyclicSegmentAt_getI_mod w 0 (blockRiseLen w 0) (by simp) hilt
  have hsegget : (cyclicSegmentAt w 0).getI (blockRiseLen w 0) =
      (cyclicSegmentAt w mid).getI 0 := by
    rw [hmod, hhead, hmidmod]
    congr 1
    rw [Nat.zero_add]
  have h3 : 3 ≤ (cyclicSegmentAt w mid).getI 0 := by
    rwa [← hsegget]
  apply c3PrefixLength_pos_of_head (cyclicSegmentAt w mid)
  exact h3

/-- The cyclic block starting at zero advances by at least two
positions. -/
theorem blockAdvance_pos_wrap
    (w : List Nat) (P : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev0 : 3 ≤ w.getI (P - 1))
    (hnext : w.getI (0 % w.length) = 1 ∨ w.getI (0 % w.length) = 2) :
    2 ≤ blockAdvance w P 0 := by
  unfold blockAdvance
  have hr : 1 ≤ blockRiseLen w 0 :=
    blockRiseLen_pos_of_boundary w 0 (by simp) hnext
  have hc0 := c3AfterRise_pos_wrap w P hw hP hpos hprev0
  have hc : 1 ≤ c3PrefixLength
      (cyclicSegmentAt w ((0 + blockRiseLen w 0) % P)) := by
    rw [hw] at hc0
    simpa [Nat.zero_add] using hc0
  omega

/-- Every block starting at a cyclic boundary advances at least two
positions. -/
theorem blockAdvance_two_le_of_cyclic_boundary
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b) :
    2 ≤ blockAdvance w P b := by
  rcases hbnd with ⟨hbP, hprev, hnext⟩
  by_cases hb0 : b = 0
  · subst b
    have hprev0 : 3 ≤ w.getI (P - 1) := by
      have hm : (0 + P - 1) % P = P - 1 := by
        have hlt : P - 1 < P := by omega
        rw [Nat.zero_add]
        exact Nat.mod_eq_of_lt hlt
      simpa [hm] using hprev
    exact blockAdvance_pos_wrap w P hw hP hpos hprev0 hnext
  · have hb1 : 1 ≤ b := by omega
    have hb : b ≤ w.length := by rw [hw]; omega
    have hprev' : 3 ≤ w.getI (b - 1) := by
      have hm : (b + P - 1) % P = b - 1 := by
        have hsub : b + P - 1 = (b - 1) + P := by omega
        rw [hsub, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      simpa [hm] using hprev
    have hnext' : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2 := by
      simpa [← hw] using hnext
    exact (blockAdvance_two_le_le_P w P b hw hb hb1 hpos hprev' hnext').1

/-- Every block starting at a cyclic boundary advances at most the
period. -/
theorem blockAdvance_le_P_of_cyclic_boundary
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b) :
    blockAdvance w P b ≤ P := by
  rcases hbnd with ⟨hbP, _hprev, hnext⟩
  have hb : b ≤ w.length := by rw [hw]; omega
  have hnext' : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2 := by
    simpa [← hw] using hnext
  exact blockAdvance_le_P w P b hw hb hpos hnext'

/-- No position strictly inside a block can itself be a cyclic
boundary: inside the rise run the predecessor is still a rise step,
and inside the C3 run the entry is a C3 step. -/
theorem blockInterior_not_cyclic_boundary
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hb : b ≤ w.length) (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b) (hj1 : 1 ≤ j) (hj2 : j < blockAdvance w P b) :
    ¬ IsCyclicBoundary w P ((b + j) % P) := by
  intro hbad
  rcases hbad with ⟨_hbadlt, hbadprev, hbadnext⟩
  have hlenpos : 0 < w.length := by rw [hw]; exact hP
  have hbndle : blockAdvance w P b ≤ P :=
    blockAdvance_le_P_of_cyclic_boundary w P b hw hP hpos hbnd
  have hjl : j < w.length := by
    rw [hw]
    omega
  have hjl1 : j - 1 < w.length := by omega
  by_cases hrise : j < blockRiseLen w b
  · have hmemj := risePrefixLength_mem (cyclicSegmentAt w b) j
      (by simpa [blockRiseLen] using hrise)
    have hmemj1 : (cyclicSegmentAt w b).getI (j - 1) = 1 ∨
        (cyclicSegmentAt w b).getI (j - 1) = 2 := by
      have hjl' : j - 1 < blockRiseLen w b := by omega
      exact risePrefixLength_mem (cyclicSegmentAt w b) (j - 1)
        (by simpa [blockRiseLen] using hjl')
    have hgetj := cyclicSegmentAt_getI_mod w b j hb hjl
    have hgetj1 := cyclicSegmentAt_getI_mod w b (j - 1) hb hjl1
    have hmod : ((b + j) % w.length + (w.length - 1)) % w.length =
        (b + (j - 1)) % w.length := by
      have hx := mod_add_sub_one hlenpos (b + j)
      rw [hx]
      have hsum : b + j + (w.length - 1) = (b + (j - 1)) + w.length := by omega
      rw [hsum, Nat.add_mod_right]
    have hprevbad : 3 ≤ w.getI ((b + (j - 1)) % w.length) := by
      have hbadprev' : 3 ≤ w.getI (((b + j) % w.length + (w.length - 1)) % w.length) := by
        have hre : ((b + j) % P + P - 1) % P =
            ((b + j) % P + (P - 1)) % P := by
          congr 1
          omega
        rw [hre] at hbadprev
        simpa [← hw] using hbadprev
      rwa [hmod] at hbadprev'
    have hprev12 : w.getI ((b + (j - 1)) % w.length) = 1 ∨
        w.getI ((b + (j - 1)) % w.length) = 2 := by
      simpa [← hgetj1] using hmemj1
    rcases hprev12 with h1 | h2
    · rw [h1] at hprevbad
      omega
    · rw [h2] at hprevbad
      omega
  · have hrle : blockRiseLen w b ≤ j := Nat.le_of_not_gt hrise
    let seg := cyclicSegmentAt w ((b + blockRiseLen w b) % P)
    have hc3lt : j - blockRiseLen w b < c3PrefixLength seg := by
      dsimp [seg]
      have hj2' : j < blockRiseLen w b +
          c3PrefixLength (cyclicSegmentAt w ((b + blockRiseLen w b) % P)) := by
        simpa [blockAdvance] using hj2
      omega
    have hsegle : (b + blockRiseLen w b) % P ≤ w.length := by
      rw [hw]
      exact le_of_lt (Nat.mod_lt _ hP)
    have hilt : j - blockRiseLen w b < w.length := by
      have hcle : c3PrefixLength seg ≤ w.length := by
        have hseg' := cyclicSegmentAt_length w ((b + blockRiseLen w b) % P) hsegle
        calc
          c3PrefixLength seg ≤ seg.length := c3PrefixLength_le _
          _ = w.length := hseg'
      omega
    have hmem := c3PrefixLength_mem seg (j - blockRiseLen w b) hc3lt
    have hget := cyclicSegmentAt_getI_mod w ((b + blockRiseLen w b) % P)
      (j - blockRiseLen w b) hsegle hilt
    have hge3' : 3 ≤ w.getI (((b + blockRiseLen w b) % P +
        (j - blockRiseLen w b)) % w.length) := by
      dsimp [seg] at hmem hget
      rwa [hget] at hmem
    have hge3 : 3 ≤ w.getI (((b + blockRiseLen w b) % P +
        (j - blockRiseLen w b)) % P) := by
      simpa [hw] using hge3'
    have hmod : ((b + blockRiseLen w b) % P + (j - blockRiseLen w b)) % P =
        (b + j) % P := by
      have hsum : (b + blockRiseLen w b) + (j - blockRiseLen w b) = b + j := by omega
      calc
        ((b + blockRiseLen w b) % P + (j - blockRiseLen w b)) % P
            = (b + blockRiseLen w b + (j - blockRiseLen w b)) % P :=
              Nat.mod_add_mod (b + blockRiseLen w b) P (j - blockRiseLen w b)
        _ = (b + j) % P := by rw [hsum]
    have hge3'' : 3 ≤ w.getI ((b + j) % P) := by
      rwa [hmod] at hge3
    have hbadnext' : w.getI ((b + j) % P) = 1 ∨ w.getI ((b + j) % P) = 2 := by
      simpa using hbadnext
    rcases hbadnext' with h1 | h2
    · rw [h1] at hge3''
      omega
    · rw [h2] at hge3''
      omega

/-- The successor of a cyclic boundary is again a cyclic boundary. -/
theorem nextRiseStart_is_cyclic_boundary
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b) :
    IsCyclicBoundary w P (nextRiseStart w P b) := by
  rcases hbnd with ⟨hbP, hprev, hnext⟩
  have hb : b ≤ w.length := by rw [hw]; omega
  have hlenpos : 0 < w.length := by rw [hw]; exact hP
  let mid := (b + blockRiseLen w b) % w.length
  have hmidle : mid ≤ w.length := le_of_lt (Nat.mod_lt _ hlenpos)
  have hc3pos : 1 ≤ c3PrefixLength (cyclicSegmentAt w mid) := by
    dsimp [mid]
    by_cases hb0 : b = 0
    · subst b
      have hprev0 : 3 ≤ w.getI (P - 1) := by
        have hm : (0 + P - 1) % P = P - 1 := by
          have hlt : P - 1 < P := by omega
          rw [Nat.zero_add]
          exact Nat.mod_eq_of_lt hlt
        simpa [hm] using hprev
      have hc := c3AfterRise_pos_wrap w P hw hP hpos hprev0
      simpa [Nat.zero_add] using hc
    · have hb1 : 1 ≤ b := by omega
      have hprev' : 3 ≤ w.getI (b - 1) := by
        have hm : (b + P - 1) % P = b - 1 := by
          have hsub : b + P - 1 = (b - 1) + P := by omega
          rw [hsub, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        simpa [hm] using hprev
      have hc := c3AfterRise_pos w b hb hb1 hpos hprev'
      simpa using hc
  let c := c3PrefixLength (cyclicSegmentAt w mid)
  have hc3ge1 : 1 ≤ c := by simpa [c] using hc3pos
  have hc3lt : c < w.length := by
    have hcle : c ≤ (cyclicSegmentAt w mid).length := c3PrefixLength_le _
    have hseg : (cyclicSegmentAt w mid).length = w.length :=
      cyclicSegmentAt_length w mid hmidle
    have hcle' : c ≤ w.length := by omega
    by_contra hnot
    have hceq : c = w.length := le_antisymm hcle' (Nat.le_of_not_gt hnot)
    let idx := (b + w.length - mid) % w.length
    have hidxlt : idx < w.length := Nat.mod_lt _ hlenpos
    have hidxltc : idx < c := by
      dsimp [idx]
      rw [hceq]
      exact Nat.mod_lt _ hlenpos
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w mid) idx hidxltc
    have hget := cyclicSegmentAt_getI_mod w mid idx hmidle hidxlt
    have hmidlt : mid < w.length := Nat.mod_lt _ hlenpos
    have hmod : (mid + idx) % w.length = b % w.length := by
      dsimp [idx]
      have hsum : mid + (b + w.length - mid) = b + w.length := by omega
      calc
        (mid + ((b + w.length - mid) % w.length)) % w.length
            = (mid + (b + w.length - mid)) % w.length := by
              simpa [Nat.mod_eq_of_lt hmidlt] using
                (Nat.mod_add_mod mid w.length (b + w.length - mid))
        _ = (b + w.length) % w.length := by
          rw [hsum]
        _ = b % w.length := by rw [Nat.add_mod_right]
    have hge : 3 ≤ w.getI (b % w.length) := by
      have hwget : w.getI ((mid + idx) % w.length) = w.getI (b % w.length) := by
        rw [hmod]
      have hge' : 3 ≤ w.getI ((mid + idx) % w.length) := by
        rwa [hget] at hmem
      rwa [← hwget]
    have hgeP : 3 ≤ w.getI (b % P) := by
      simpa [hw] using hge
    rcases hnext with h1 | h2
    · rw [h1] at hgeP
      omega
    · rw [h2] at hgeP
      omega
  have hposSeg : ∀ x, x ∈ cyclicSegmentAt w mid → 1 ≤ x := by
    intro x hx
    exact hpos x (cyclicSegmentAt_mem (w := w) (b := mid) hx)
  have hc3ltSeg : c < (cyclicSegmentAt w mid).length := by
    rw [cyclicSegmentAt_length w mid hmidle]
    exact hc3lt
  have hstop := c3PrefixLength_stop (cyclicSegmentAt w mid) hposSeg hc3ltSeg
  let q := (mid + c) % w.length
  have hqlt : q < w.length := Nat.mod_lt _ hlenpos
  have hqnext : w.getI (q % w.length) = 1 ∨ w.getI (q % w.length) = 2 := by
    have hget := cyclicSegmentAt_getI_mod w mid c hmidle hc3lt
    have hwget : w.getI (q % w.length) = (cyclicSegmentAt w mid).getI c := by
      simpa [q] using hget.symm
    rwa [← hwget] at hstop
  have hqprev : 3 ≤ w.getI ((q + w.length - 1) % w.length) := by
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w mid) (c - 1) (by omega)
    have hiltc1 : c - 1 < w.length := by omega
    have hget := cyclicSegmentAt_getI_mod w mid (c - 1) hmidle hiltc1
    have hge : 3 ≤ w.getI ((mid + (c - 1)) % w.length) := by
      rwa [hget] at hmem
    have hmod : (mid + (c - 1)) % w.length = (q + w.length - 1) % w.length := by
      dsimp [q]
      have hre : ((mid + c) % w.length + w.length - 1) % w.length =
          ((mid + c) % w.length + (w.length - 1)) % w.length := by
        congr 1
        omega
      have hx := mod_add_sub_one hlenpos (mid + c)
      rw [hre, hx]
      have hsum' : mid + c + (w.length - 1) = (mid + (c - 1)) + w.length := by omega
      rw [hsum', Nat.add_mod_right]
    rwa [hmod] at hge
  have hqltP : q < P := by rwa [hw] at hqlt
  have hqprevP : 3 ≤ w.getI ((q + P - 1) % P) := by
    rwa [hw] at hqprev
  have hqnextP : w.getI (q % P) = 1 ∨ w.getI (q % P) = 2 := by
    rwa [hw] at hqnext
  have hqeq : q = nextRiseStart w P b := by
    dsimp [q, mid, c]
    unfold nextRiseStart
    rw [hw]
  rw [← hqeq]
  exact ⟨hqltP, hqprevP, hqnextP⟩

/-- Every iterate of the boundary map from a cyclic boundary is again
a cyclic boundary. -/
theorem riseBoundaryIter_is_cyclic_boundary
    (w : List Nat) (P b0 : Nat) (k : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b0) (hk : k < P) :
    IsCyclicBoundary w P (riseBoundaryIter w P b0 k) := by
  induction k with
  | zero =>
      simpa [riseBoundaryIter] using hbnd
  | succ k ih =>
      have hk' : k < P := by omega
      simpa [riseBoundaryIter] using
        nextRiseStart_is_cyclic_boundary w P (riseBoundaryIter w P b0 k)
          hw hP hpos (ih hk')

/-- Iterating from the successor is the same as iterating one more
step from the starting boundary. -/
theorem riseBoundaryIter_succ_compose (w : List Nat) (P b : Nat) (n : Nat) :
    riseBoundaryIter w P (nextRiseStart w P b) n =
      riseBoundaryIter w P b (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [riseBoundaryIter, ih]

/-- If the boundary iteration reaches the starting boundary within
`n` steps, the cycle-length counter stops no later than step `n`. -/
theorem riseRunCycleLenAux_le_of_hit
    (w : List Nat) (P fuel b0 b : Nat) (n : Nat)
    (hn : n ≤ fuel) (hit : riseBoundaryIter w P b n = b0) :
    riseRunCycleLenAux w P fuel b0 b ≤ n := by
  induction n generalizing fuel b with
  | zero =>
      have hb : b = b0 := by
        simpa [riseBoundaryIter] using hit
      induction fuel with
      | zero => simp [riseRunCycleLenAux]
      | succ fuel ihf => simp [riseRunCycleLenAux, hb]
  | succ n ih =>
      by_cases hb : b = b0
      · induction fuel with
        | zero => simp [riseRunCycleLenAux]
        | succ fuel ihf => simp [riseRunCycleLenAux, hb]
      · cases fuel with
        | zero => omega
        | succ fuel =>
            have hstep : riseBoundaryIter w P (nextRiseStart w P b) n = b0 := by
              rw [riseBoundaryIter_succ_compose w P b n]
              exact hit
            have hle : n ≤ fuel := by omega
            have hih := ih fuel (nextRiseStart w P b) hle hstep
            have haux : riseRunCycleLenAux w P (fuel + 1) b0 b =
                1 + riseRunCycleLenAux w P fuel b0 (nextRiseStart w P b) := by
              simp [riseRunCycleLenAux, hb]
            rw [haux]
            omega

/-- The cyclic boundary tour returns to its starting boundary within
`P` steps, so the number of rise blocks is at most the period. -/
theorem blockCountOf_le_P
    (w : List Nat) (P b0 : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b0) :
    blockCountOf w P b0 ≤ P := by
  have hb0P : b0 < P := hbnd.1
  have hbndAt : ∀ k : Nat, k < P →
      IsCyclicBoundary w P (riseBoundaryIter w P b0 k) := by
    intro k hk
    exact riseBoundaryIter_is_cyclic_boundary w P b0 k hw hP hpos hbnd hk
  have hT_P : P ≤ blockTotalAdvance w P b0 P := by
    have h := blockTotalAdvance_ge_two_mul w P b0 P
      (fun k hk => blockAdvance_two_le_of_cyclic_boundary w P
        (riseBoundaryIter w P b0 k) hw hP hpos (hbndAt k (by omega)))
    omega
  let S : Nat → Prop := fun n => P ≤ blockTotalAdvance w P b0 n
  have hnon : ∃ n : Nat, S n := ⟨P, hT_P⟩
  let n0 := Nat.find hnon
  have hn0 : P ≤ blockTotalAdvance w P b0 n0 := by
    dsimp [n0]
    exact Nat.find_spec hnon
  have hn0min : ∀ n : Nat, P ≤ blockTotalAdvance w P b0 n → n0 ≤ n := by
    intro n hn
    dsimp [n0]
    exact Nat.find_min' hnon hn
  have hn0pos : 0 < n0 := by
    by_contra hz
    have hn0z : n0 = 0 := Nat.eq_zero_of_not_pos hz
    rw [hn0z] at hn0
    simp [blockTotalAdvance] at hn0
    omega
  have hn0le : n0 ≤ P := hn0min P hT_P
  have hprevlt : blockTotalAdvance w P b0 (n0 - 1) < P := by
    by_contra hnot
    have hge : P ≤ blockTotalAdvance w P b0 (n0 - 1) := Nat.le_of_not_gt hnot
    have hle := hn0min (n0 - 1) hge
    omega
  let b := riseBoundaryIter w P b0 (n0 - 1)
  let A := blockAdvance w P b
  have hbndb : IsCyclicBoundary w P b := by
    dsimp [b]
    exact hbndAt (n0 - 1) (by omega)
  have hTlast : blockTotalAdvance w P b0 n0 =
      blockTotalAdvance w P b0 (n0 - 1) + A := by
    have hsub : n0 = (n0 - 1) + 1 := by omega
    rw [hsub]
    simp [blockTotalAdvance, b, A]
  have hT_n0_eq : blockTotalAdvance w P b0 n0 = P := by
    by_contra hnot
    have hgt : P < blockTotalAdvance w P b0 n0 :=
      lt_of_le_of_ne hn0 (fun h => hnot h.symm)
    let j := P - blockTotalAdvance w P b0 (n0 - 1)
    have hj1 : 1 ≤ j := by
      dsimp [j]
      omega
    have hj2 : j < A := by
      dsimp [j]
      rw [hTlast] at hgt
      omega
    have hb : b ≤ w.length := by
      have hbP : b < w.length := by simpa [← hw] using hbndb.1
      omega
    have hnotb := blockInterior_not_cyclic_boundary w P b hw hP hb
      hpos hbndb hj1 hj2
    have hpos_eq : (b + j) % P = b0 := by
      have hbmod := riseBoundaryIter_eq_add_totalAdvance w P b0 hb0P (n0 - 1)
      have hb' : riseBoundaryIter w P b0 (n0 - 1) =
          (b0 + blockTotalAdvance w P b0 (n0 - 1)) % P := hbmod
      dsimp [b, j]
      rw [hb']
      have haP : blockTotalAdvance w P b0 (n0 - 1) ≤ P := by omega
      have hadd : blockTotalAdvance w P b0 (n0 - 1) +
          (P - blockTotalAdvance w P b0 (n0 - 1)) = P := Nat.add_sub_of_le haP
      calc
        ((b0 + blockTotalAdvance w P b0 (n0 - 1)) % P +
            (P - blockTotalAdvance w P b0 (n0 - 1))) % P
            = (b0 + blockTotalAdvance w P b0 (n0 - 1) +
                (P - blockTotalAdvance w P b0 (n0 - 1))) % P :=
              Nat.mod_add_mod (b0 + blockTotalAdvance w P b0 (n0 - 1)) P
                (P - blockTotalAdvance w P b0 (n0 - 1))
        _ = (b0 + P) % P := by
            rw [Nat.add_assoc, hadd]
        _ = b0 := by
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt hb0P
    have hbad0 : IsCyclicBoundary w P ((b + j) % P) := by
      simpa [← hpos_eq] using hbnd
    exact hnotb hbad0
  have hreturn : riseBoundaryIter w P (nextRiseStart w P b0) (n0 - 1) = b0 := by
    rw [riseBoundaryIter_succ_compose w P b0 (n0 - 1)]
    have hsub : n0 - 1 + 1 = n0 := by omega
    rw [hsub]
    rw [riseBoundaryIter_eq_add_totalAdvance w P b0 hb0P n0]
    rw [hT_n0_eq]
    have hsum : (b0 + P) % P = b0 := by
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hb0P
    simpa using hsum
  have haux : riseRunCycleLenAux w P P b0 (nextRiseStart w P b0) ≤ n0 - 1 :=
    riseRunCycleLenAux_le_of_hit w P P b0 (nextRiseStart w P b0) (n0 - 1)
      (by omega) hreturn
  unfold blockCountOf riseRunCycleLen
  omega

/-- If the cycle-length counter stops at `k` steps below its fuel,
the boundary iteration really reached the starting boundary. -/
theorem riseRunCycleLenAux_eq_imp_hit
    (w : List Nat) (P fuel b0 b : Nat) (k : Nat)
    (hk : k < fuel) (haux : riseRunCycleLenAux w P fuel b0 b = k) :
    riseBoundaryIter w P b k = b0 := by
  induction fuel generalizing b k with
  | zero => omega
  | succ fuel ih =>
      by_cases hb : b = b0
      · have hk0 : k = 0 := by
          have hs : riseRunCycleLenAux w P (fuel + 1) b0 b = 0 := by
            simp [riseRunCycleLenAux, hb]
          rw [hs] at haux
          exact haux.symm
        rw [hk0]
        simpa [riseBoundaryIter, hb]
      · have hkpos : 1 ≤ k := by
          by_contra hz
          have hk0 : k = 0 := Nat.eq_zero_of_not_pos hz
          rw [hk0] at haux
          unfold riseRunCycleLenAux at haux
          rw [if_neg hb] at haux
          omega
        have haux' : riseRunCycleLenAux w P fuel b0 (nextRiseStart w P b) = k - 1 := by
          have hsimp : riseRunCycleLenAux w P (fuel + 1) b0 b =
              1 + riseRunCycleLenAux w P fuel b0 (nextRiseStart w P b) := by
            simp [riseRunCycleLenAux, hb]
          rw [hsimp] at haux
          omega
        have hk' : k - 1 < fuel := by omega
        have hhit := ih (nextRiseStart w P b) (k - 1) hk' haux'
        have hcomp : riseBoundaryIter w P b k =
            riseBoundaryIter w P (nextRiseStart w P b) (k - 1) := by
          have hsub : k = (k - 1) + 1 := by omega
          rw [hsub]
          exact (riseBoundaryIter_succ_compose w P b (k - 1)).symm
        rwa [← hcomp] at hhit

/-- The boundary tour returns to the starting boundary exactly after
`blockCountOf` steps. -/
theorem riseBoundaryIter_blockCount_eq
    (w : List Nat) (P b0 : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hbnd : IsCyclicBoundary w P b0) :
    riseBoundaryIter w P b0 (blockCountOf w P b0) = b0 := by
  have hcomp' : riseBoundaryIter w P (nextRiseStart w P b0)
        (blockCountOf w P b0 - 1) =
      riseBoundaryIter w P b0 (blockCountOf w P b0) := by
    have hsub : blockCountOf w P b0 - 1 + 1 = blockCountOf w P b0 := by
      have hpos1 : 1 ≤ blockCountOf w P b0 := blockCountOf_pos w P b0
      omega
    rw [← hsub]
    exact riseBoundaryIter_succ_compose w P b0 (blockCountOf w P b0 - 1)
  rw [← hcomp']
  apply riseRunCycleLenAux_eq_imp_hit w P P b0 (nextRiseStart w P b0)
    (blockCountOf w P b0 - 1)
  · have hle := blockCountOf_le_P w P b0 hw hP hpos hbnd
    have hpos1 : 1 ≤ blockCountOf w P b0 := blockCountOf_pos w P b0
    omega
  · unfold blockCountOf riseRunCycleLen
    omega

/-- The boundary index `P` represents the cyclic position `0`, so a
word position `0` boundary is kept inside `1..P`. -/
def cyclicBoundaryIndex (P : Nat) (b : Nat) : Nat :=
  if b = 0 then P else b

theorem cyclicBoundaryIndex_zero (P : Nat) :
    cyclicBoundaryIndex P 0 = P := by
  simp [cyclicBoundaryIndex]

theorem cyclicBoundaryIndex_of_pos (P : Nat) (b : Nat) (hb : b ≠ 0) :
    cyclicBoundaryIndex P b = b := by
  simp [cyclicBoundaryIndex, hb]

theorem cyclicBoundaryIndex_pos {P : Nat} (hP : 0 < P) (b : Nat) :
    1 ≤ cyclicBoundaryIndex P b := by
  by_cases hb : b = 0
  · simp [cyclicBoundaryIndex, hb]
    omega
  · simp [cyclicBoundaryIndex, hb]
    omega

theorem cyclicBoundaryIndex_le {P : Nat} (b : Nat) (hb : b < P) :
    cyclicBoundaryIndex P b ≤ P := by
  by_cases hb0 : b = 0
  · simp [cyclicBoundaryIndex, hb0]
  · simp [cyclicBoundaryIndex, hb0]
    omega

/-- A rise run starting at a boundary `b < P` cannot wrap around the
end of the word: its last entry would be the C3 entry before zero. -/
theorem blockRiseLen_boundary_add_lt
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hb1 : 1 ≤ b) (hbP : b < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    b + blockRiseLen w b < P := by
  by_contra hnot
  have hge : P ≤ b + blockRiseLen w b := Nat.le_of_not_gt hnot
  let j := P - 1 - b
  have hbw : b ≤ w.length := by rw [hw]; omega
  have hjl : j < blockRiseLen w b := by
    dsimp [j]
    omega
  have hjlw : j < w.length := by
    have hle := risePrefixLength_le (cyclicSegmentAt w b)
    have hseg := cyclicSegmentAt_length w b hbw
    have hjl' : j < blockRiseLen w b := hjl
    unfold blockRiseLen at hjl'
    omega
  have hmem := risePrefixLength_mem (cyclicSegmentAt w b) j
    (by simpa [blockRiseLen] using hjl)
  have hget := cyclicSegmentAt_getI_mod w b j hbw hjlw
  have hposP1 : (b + j) % w.length = P - 1 := by
    dsimp [j]
    have hsum : b + (P - 1 - b) = P - 1 := by omega
    rw [hsum]
    exact Nat.mod_eq_of_lt (by rw [hw]; omega)
  have hw12 : w.getI (P - 1) = 1 ∨ w.getI (P - 1) = 2 := by
    rw [hposP1] at hget
    rwa [hget] at hmem
  rcases hw12 with h1 | h2
  · rw [h1] at hprev0
    omega
  · rw [h2] at hprev0
    omega

/-- The C3 run ending before `b` stops at the first non-C3 entry. -/
theorem c3SuffixLengthAt_stop
    (w : List Nat) (b : Nat) (hb : b ≤ w.length)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hstop : c3SuffixLengthAt w b < b) :
    w.getI (b - 1 - c3SuffixLengthAt w b) = 1 ∨
      w.getI (b - 1 - c3SuffixLengthAt w b) = 2 := by
  unfold c3SuffixLengthAt
  have hlenRev : ((w.take b).reverse).length = b := by
    rw [List.length_reverse, List.length_take_of_le hb]
  have hlt : c3PrefixLength ((w.take b).reverse) <
      ((w.take b).reverse).length := by
    rwa [hlenRev]
  have hposRev : ∀ x, x ∈ (w.take b).reverse → 1 ≤ x := by
    intro x hx
    exact hpos x (List.mem_of_mem_take (List.mem_reverse.mp hx))
  have hstop' := c3PrefixLength_stop ((w.take b).reverse) hposRev hlt
  have hlenTake : (w.take b).length = b := List.length_take_of_le hb
  have hlen : c3PrefixLength ((w.take b).reverse) < (w.take b).length := by
    rwa [hlenTake]
  rw [reverse_getI_of_lt (w.take b)
    (c3PrefixLength ((w.take b).reverse)) hlen] at hstop'
  have hsub : (w.take b).length - 1 - c3PrefixLength ((w.take b).reverse) =
      b - 1 - c3PrefixLength ((w.take b).reverse) := by
    simpa [hlenTake]
  rw [hsub] at hstop'
  have hlt2 : b - 1 - c3PrefixLength ((w.take b).reverse) < w.length := by
    have hle' : c3PrefixLength ((w.take b).reverse) < b := by
      have hlt3 : c3PrefixLength ((w.take b).reverse) < b := by
        simpa [hlenRev] using hlt
      exact hlt3
    omega
  have htake : (w.take b).getI (b - 1 - c3PrefixLength ((w.take b).reverse)) =
      w.getI (b - 1 - c3PrefixLength ((w.take b).reverse)) := by
    have hlt3 : b - 1 - c3PrefixLength ((w.take b).reverse) <
        (w.take b).length := by
      rw [hlenTake]
      omega
    rw [List.getI_eq_getElem (l := w.take b)
      (n := b - 1 - c3PrefixLength ((w.take b).reverse)) hlt3]
    rw [List.getI_eq_getElem (l := w)
      (n := b - 1 - c3PrefixLength ((w.take b).reverse)) hlt2]
    exact List.getElem_take (xs := w) (j := b)
      (i := b - 1 - c3PrefixLength ((w.take b).reverse))
  rwa [htake] at hstop'

/-- The C3 run ending before a boundary whose entries are exactly the
linear segment `s .. q-1`, with a rise step before `s`, has length
`q - s`. -/
theorem c3SuffixLengthAt_eq_sub_of_c3_run
    (w : List Nat) (q s : Nat) (hb : q ≤ w.length) (hss : s ≤ q)
    (hs1 : 1 ≤ s)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hC3 : ∀ k, k < q - s → 3 ≤ w.getI (s + k))
    (hprev12 : w.getI (s - 1) = 1 ∨ w.getI (s - 1) = 2) :
    c3SuffixLengthAt w q = q - s := by
  unfold c3SuffixLengthAt
  let u := (w.take q).reverse
  have hlenU : u.length = q := by
    dsimp [u]
    rw [List.length_reverse, List.length_take_of_le hb]
  apply le_antisymm
  · by_contra hnot
    have hlt : q - s < c3PrefixLength u := Nat.lt_of_not_ge hnot
    have hmem := c3PrefixLength_mem u (q - s) hlt
    have hk : q - s < u.length := by
      have hle' := c3PrefixLength_le u
      exact lt_of_lt_of_le hlt hle'
    have hlenT : (w.take q).length = q := List.length_take_of_le hb
    rw [reverse_getI_of_lt (w.take q) (q - s)
      (by rw [hlenT]; omega)] at hmem
    have hsub : (w.take q).length - 1 - (q - s) = s - 1 := by
      rw [hlenT]
      omega
    rw [hsub] at hmem
    have hlt2 : s - 1 < (w.take q).length := by
      rw [hlenT]
      omega
    have htake : (w.take q).getI (s - 1) = w.getI (s - 1) := by
      rw [List.getI_eq_getElem (l := w.take q) (n := s - 1) hlt2]
      rw [List.getI_eq_getElem (l := w) (n := s - 1) (by omega)]
      exact List.getElem_take (xs := w) (j := q) (i := s - 1)
    rw [htake] at hmem
    rcases hprev12 with h1 | h2
    · rw [h1] at hmem
      omega
    · rw [h2] at hmem
      omega
  · by_contra hnot
    have hlt : c3PrefixLength u < q - s := Nat.lt_of_not_ge hnot
    have hltU : c3PrefixLength u < u.length := by
      have hqle : q - s ≤ u.length := by omega
      omega
    have hposU : ∀ x, x ∈ u → 1 ≤ x := by
      intro x hx
      dsimp [u] at hx
      exact hpos x (List.mem_of_mem_take (List.mem_reverse.mp hx))
    have hstop' := c3PrefixLength_stop u hposU hltU
    let k := c3PrefixLength u
    have hkU : k < u.length := by
      have hle' := c3PrefixLength_le u
      dsimp [k]
      omega
    have hlenT : (w.take q).length = q := List.length_take_of_le hb
    rw [reverse_getI_of_lt (w.take q) k
      (by rw [hlenT, ← hlenU]; exact hkU)] at hstop'
    have hsub : (w.take q).length - 1 - k = q - 1 - k := by
      rw [hlenT]
    rw [hsub] at hstop'
    have hj : q - 1 - k - s < q - s := by
      dsimp [k]
      omega
    have hposIdx : q - 1 - k = s + (q - 1 - k - s) := by omega
    have hge' : 3 ≤ w.getI (q - 1 - k) := by
      have hh := hC3 (q - 1 - k - s) hj
      rw [← hposIdx] at hh
      exact hh
    have hltW : q - 1 - k < w.length := by
      have hk' : k < q := by
        have hle' := c3PrefixLength_le u
        dsimp [k]
        have hlenU' : u.length = q := hlenU
        omega
      omega
    have htake : (w.take q).getI (q - 1 - k) = w.getI (q - 1 - k) := by
      rw [List.getI_eq_getElem (l := w.take q) (n := q - 1 - k)
        (by rw [hlenT]; omega)]
      rw [List.getI_eq_getElem (l := w) (n := q - 1 - k) hltW]
      exact List.getElem_take (xs := w) (j := q) (i := q - 1 - k)
    rw [htake] at hstop'
    rcases hstop' with h1 | h2
    · rw [h1] at hge'
      omega
    · rw [h2] at hge'
      omega

/-- The C3 run after the rise at a boundary `b` is exactly the C3 run
ending before the next boundary (represented in `1..P`).  Position
`0` is a rise boundary, so neither run wraps across it. -/
theorem blockC3Len_next_eq_of_cyclic
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hb1 : 1 ≤ b) (hbP : b < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev : 3 ≤ w.getI (b - 1))
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2)
    (hzero0 : w.getI 0 = 1 ∨ w.getI 0 = 2)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    c3SuffixLengthAt w (cyclicBoundaryIndex P (nextRiseStart w P b)) =
      c3PrefixLength (cyclicSegmentAt w (b + blockRiseLen w b)) := by
  let L := blockRiseLen w b
  let s := b + L
  have hsP : s < P := by
    dsimp [s, L]
    exact blockRiseLen_boundary_add_lt w P b hw hP hb1 hbP hpos hnext hprev0
  have hs1 : 1 ≤ s := by omega
  let C := c3PrefixLength (cyclicSegmentAt w s)
  have hsC_le : s + C ≤ P := by
    by_contra hnot
    have hgt : P < s + C := Nat.lt_of_not_ge hnot
    let j := P - s
    have hjlt : j < C := by
      dsimp [j]
      omega
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w s) j hjlt
    have hklt : j < w.length := by
      have hle' := c3PrefixLength_le (cyclicSegmentAt w s)
      have hle'' : C ≤ w.length := by
        dsimp [C]
        have hseg := cyclicSegmentAt_length w s (by dsimp [s]; rw [hw]; omega)
        simpa [hseg] using hle'
      rw [hw]
      omega
    have hget := cyclicSegmentAt_getI_mod w s j (by dsimp [s]; rw [hw]; omega) hklt
    have hpos0 : (s + j) % w.length = 0 := by
      dsimp [j]
      have hsum : s + (P - s) = P := Nat.add_sub_of_le (by omega)
      rw [hsum]
      simp [hw]
    have h0ge : 3 ≤ w.getI 0 := by
      have hwget : w.getI ((s + j) % w.length) = w.getI 0 := by rw [hpos0]
      have hge' : 3 ≤ w.getI ((s + j) % w.length) := by rwa [hget] at hmem
      rwa [← hwget]
    rcases hzero0 with h1 | h2
    · rw [h1] at h0ge
      omega
    · rw [h2] at h0ge
      omega
  have hC3 : ∀ k, k < C → 3 ≤ w.getI (s + k) := by
    intro k hk
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w s) k hk
    have hklt : k < w.length := by
      rw [hw]
      have hle' : C ≤ P := by
        have hseg := cyclicSegmentAt_length w s (by dsimp [s]; rw [hw]; omega)
        calc
          C ≤ (cyclicSegmentAt w s).length := by dsimp [C]; exact c3PrefixLength_le _
          _ = w.length := hseg
          _ = P := hw
      omega
    have hget := cyclicSegmentAt_getI_mod w s k (by dsimp [s]; rw [hw]; omega) hklt
    have hmod : (s + k) % w.length = s + k := by
      have hlt : s + k < P := by omega
      rw [hw]
      exact Nat.mod_eq_of_lt (by omega)
    have hge : 3 ≤ w.getI (s + k) := by
      rw [hget] at hmem
      rwa [hmod] at hmem
    exact hge
  have hprev12 : w.getI (s - 1) = 1 ∨ w.getI (s - 1) = 2 := by
    have hbw : b ≤ w.length := by rw [hw]; omega
    have hLpos : 1 ≤ L := by
      dsimp [L]
      exact blockRiseLen_pos_of_boundary w b hbw hnext
    have hmem := risePrefixLength_mem (cyclicSegmentAt w b) (L - 1)
      (by
        dsimp [L]
        simpa [blockRiseLen] using
          (Nat.sub_lt (blockRiseLen_pos_of_boundary w b hbw hnext) (by decide : 0 < 1)))
    have hklt : L - 1 < w.length := by
      have hle' : L ≤ w.length := by
        dsimp [L]
        have hseg := cyclicSegmentAt_length w b hbw
        calc
          risePrefixLength (cyclicSegmentAt w b) ≤
              (cyclicSegmentAt w b).length := risePrefixLength_le _
          _ = w.length := hseg
      rw [hw]
      omega
    have hget := cyclicSegmentAt_getI_mod w b (L - 1) hbw hklt
    have hmod : (b + (L - 1)) % w.length = s - 1 := by
      have hsum : b + (L - 1) = s - 1 := by
        dsimp [s]
        omega
      rw [hsum]
      exact Nat.mod_eq_of_lt (by dsimp [s] at hsP; dsimp [s]; rw [hw]; omega)
    rw [hget] at hmem
    rwa [hmod] at hmem
  let q := nextRiseStart w P b
  have hq : q = (s + C) % P := by
    dsimp [q, s, C, L]
    rw [nextRiseStart_eq_add_blockAdvance]
    unfold blockAdvance
    have hmod : (b + blockRiseLen w b) % P = s := by
      dsimp [s]
      exact Nat.mod_eq_of_lt (by simpa [s] using hsP)
    rw [hmod]
    have hadd : b + (blockRiseLen w b + c3PrefixLength (cyclicSegmentAt w s)) =
        s + C := by
      dsimp [s, C]
      omega
    rw [hadd]
  let bndq := cyclicBoundaryIndex P q
  have hCq : c3SuffixLengthAt w bndq = C := by
    by_cases hlt : s + C < P
    · have hq' : q = s + C := by
        rw [hq]
        exact Nat.mod_eq_of_lt hlt
      have hbnd : bndq = s + C := by
        dsimp [bndq]
        rw [hq']
        unfold cyclicBoundaryIndex
        rw [if_neg (by dsimp [s]; omega : s + C ≠ 0)]
      have hC3' : ∀ k, k < (s + C) - s → 3 ≤ w.getI (s + k) := by
        intro k hk
        have hk' : k < C := by omega
        exact hC3 k hk'
      have hsle : s ≤ s + C := by omega
      have hlen : s + C ≤ w.length := by
        rw [hw]
        omega
      have hsub0 : c3SuffixLengthAt w (s + C) = (s + C) - s :=
        c3SuffixLengthAt_eq_sub_of_c3_run w (s + C) s hlen hsle hs1 hpos hC3' hprev12
      have hsub' : c3SuffixLengthAt w (s + C) = C := by
        rw [hsub0]
        omega
      rwa [← hbnd] at hsub'
    · have heq : s + C = P := by omega
      have hq' : q = 0 := by
        rw [hq, heq]
        simp
      have hbnd : bndq = P := by
        dsimp [bndq]
        rw [hq']
        simp [cyclicBoundaryIndex]
      have hC3' : ∀ k, k < P - s → 3 ≤ w.getI (s + k) := by
        intro k hk
        have hk' : k < C := by
          rw [← heq] at hk
          omega
        exact hC3 k hk'
      have hsle : s ≤ P := by omega
      have hlen : P ≤ w.length := by rw [hw]
      have hsub' : c3SuffixLengthAt w P = P - s :=
        c3SuffixLengthAt_eq_sub_of_c3_run w P s hlen hsle hs1 hpos hC3' hprev12
      have hPs : P - s = C := by omega
      rw [hbnd]
      rw [hsub', hPs]
  exact hCq

/-- For a cyclic rise boundary `b < P` whose block does not wrap, the
head depth of the next block is the current head depth plus the C3 and
rise lengths of the current block. -/
theorem blockHeadDepth_next_of_boundary
    (w : List Nat) (P b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hb1 : 1 ≤ b) (hbP : b < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev : 3 ≤ w.getI (b - 1))
    (hnext : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2)
    (hzero0 : w.getI 0 = 1 ∨ w.getI 0 = 2)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    blockHeadDepth w (cyclicBoundaryIndex P (nextRiseStart w P b)) =
      blockHeadDepth w b + blockC3Len w b + blockRiseLen w b := by
  let L := blockRiseLen w b
  let C := blockC3Len w b
  let q := nextRiseStart w P b
  let bndq := cyclicBoundaryIndex P q
  have hbw : b ≤ w.length := by rw [hw]; omega
  have hCle : C ≤ b := by
    dsimp [C]
    exact c3SuffixLengthAt_le w b hbw
  have hCq : c3SuffixLengthAt w bndq = c3PrefixLength (cyclicSegmentAt w (b + L)) := by
    dsimp [bndq, q, L]
    exact blockC3Len_next_eq_of_cyclic w P b hw hP hb1 hbP hpos hprev hnext hzero0 hprev0
  have hbndC : c3SuffixLengthAt w bndq ≤ bndq := by
    have hqlt : q < P := nextRiseStart_lt hP w b
    have hle' : bndq ≤ P := cyclicBoundaryIndex_le q hqlt
    exact c3SuffixLengthAt_le w bndq (by rw [hw]; exact hle')
  have hbd : blockHeadDepth w bndq = bndq - c3SuffixLengthAt w bndq := rfl
  have hbd0 : blockHeadDepth w b = b - C := by
    dsimp [C]
    rfl
  let s := b + L
  let C' := c3PrefixLength (cyclicSegmentAt w s)
  have hCq' : c3SuffixLengthAt w bndq = C' := by
    dsimp [C', s]
    exact hCq
  have hsP : s < P := by
    dsimp [s, L]
    exact blockRiseLen_boundary_add_lt w P b hw hP hb1 hbP hpos hnext hprev0
  have hsC_le : s + C' ≤ P := by
    by_contra hnot
    have hgt : P < s + C' := Nat.lt_of_not_ge hnot
    let j := P - s
    have hjlt : j < C' := by
      dsimp [j]
      omega
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w s) j hjlt
    have hklt : j < w.length := by
      have hle' : C' ≤ w.length := by
        dsimp [C']
        have hseg := cyclicSegmentAt_length w s (by dsimp [s]; rw [hw]; omega)
        calc
          c3PrefixLength (cyclicSegmentAt w s) ≤
              (cyclicSegmentAt w s).length := c3PrefixLength_le _
          _ = w.length := hseg
      rw [hw]
      omega
    have hget := cyclicSegmentAt_getI_mod w s j (by dsimp [s]; rw [hw]; omega) hklt
    have hpos0 : (s + j) % w.length = 0 := by
      dsimp [j]
      have hsum : s + (P - s) = P := Nat.add_sub_of_le (by omega)
      rw [hsum]
      simp [hw]
    have h0ge : 3 ≤ w.getI 0 := by
      have hwget : w.getI ((s + j) % w.length) = w.getI 0 := by rw [hpos0]
      have hge' : 3 ≤ w.getI ((s + j) % w.length) := by rwa [hget] at hmem
      rwa [← hwget]
    rcases hzero0 with h1 | h2
    · rw [h1] at h0ge
      omega
    · rw [h2] at h0ge
      omega
  by_cases hlt : s + C' < P
  · have hbnd : bndq = s + C' := by
      dsimp [bndq, q]
      rw [nextRiseStart_eq_add_blockAdvance]
      unfold blockAdvance
      have hmod : (b + blockRiseLen w b) % P = s := by
        dsimp [s]
        exact Nat.mod_eq_of_lt (by simpa [s] using hsP)
      rw [hmod]
      have hadd : b + (blockRiseLen w b + c3PrefixLength (cyclicSegmentAt w s)) =
          s + C' := by
        dsimp [s, C']
        omega
      rw [hadd]
      rw [Nat.mod_eq_of_lt hlt]
      unfold cyclicBoundaryIndex
      rw [if_neg (by dsimp [s]; omega : s + C' ≠ 0)]
    have hmain : bndq - c3SuffixLengthAt w bndq = s := by
      rw [hCq', hbnd]
      omega
    rw [hbd, hmain, hbd0]
    dsimp [s, L, C]
    dsimp [C] at hCle
    omega
  · have heq : s + C' = P := by omega
    have hbnd : bndq = P := by
      dsimp [bndq, q]
      rw [nextRiseStart_eq_add_blockAdvance]
      unfold blockAdvance
      have hmod : (b + blockRiseLen w b) % P = s := by
        dsimp [s]
        exact Nat.mod_eq_of_lt (by simpa [s] using hsP)
      rw [hmod]
      have hadd : b + (blockRiseLen w b + c3PrefixLength (cyclicSegmentAt w s)) =
          s + C' := by
        dsimp [s, C']
        omega
      rw [hadd, heq]
      simp [cyclicBoundaryIndex]
    have hmain : bndq - c3SuffixLengthAt w bndq = s := by
      rw [hCq', hbnd]
      omega
    rw [hbd, hmain, hbd0]
    dsimp [s, L, C]
    dsimp [C] at hCle
    omega

/-- A closed QB-8 input is anchored at position `0` as a cyclic rise
boundary: entry `0` is a rise step and the previous cyclic entry is a
C3 step. -/
theorem cycleQb8Input_isCyclicBoundary_zero
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    IsCyclicBoundary w P 0 := by
  have hP2 : 2 ≤ P := cycleQb8Input_P_ge_two h
  have hprev : 3 ≤ w.getI ((0 + P - 1) % P) := by
    have hm : (0 + P - 1) % P = P - 1 := by
      have hlt : P - 1 < P := by omega
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt hlt
    rw [hm]
    exact cycleQb8Input_last_step_c3 h
  have hnext : w.getI (0 % P) = 1 ∨ w.getI (0 % P) = 2 := by
    simp
    exact h.hrise_start
  exact ⟨by omega, hprev, hnext⟩

/-- The normalized boundary index `cyclicBoundaryIndex P b` still has
the boundary properties: it is in `1..P`, its previous cyclic entry is
a C3 step, and its own entry is a rise step. -/
lemma cyclicBoundaryIndex_isBoundary
    (w : List Nat) (P : Nat) (b : Nat) (hw : w.length = P) (hP : 0 < P)
    (hbnd : IsCyclicBoundary w P b) (hprev0 : 3 ≤ w.getI (P - 1)) :
    1 ≤ cyclicBoundaryIndex P b ∧ cyclicBoundaryIndex P b ≤ P ∧
    3 ≤ w.getI (cyclicBoundaryIndex P b - 1) ∧
    (w.getI (cyclicBoundaryIndex P b % w.length) = 1 ∨
     w.getI (cyclicBoundaryIndex P b % w.length) = 2) := by
  rcases hbnd with ⟨hbP, hprev, hnext⟩
  by_cases hb0 : b = 0
  · subst b
    have hbndP : cyclicBoundaryIndex P 0 = P := cyclicBoundaryIndex_zero P
    constructor
    · rw [hbndP]
      omega
    · constructor
      · simp [hbndP]
      · constructor
        · have hm : (0 + P - 1) % P = P - 1 := by
            have hlt : P - 1 < P := by omega
            rw [Nat.zero_add]
            exact Nat.mod_eq_of_lt hlt
          rw [hbndP, ← hm]
          exact hprev
        · have hmod : P % w.length = 0 := by
            rw [hw]
            simp
          rw [hbndP, hmod]
          simpa using hnext
  · have hbndb : cyclicBoundaryIndex P b = b :=
      cyclicBoundaryIndex_of_pos P b hb0
    have hbpos : 1 ≤ b := by omega
    have hprev' : 3 ≤ w.getI (b - 1) := by
      have hm : (b + P - 1) % P = b - 1 := by
        have hsub : b + P - 1 = (b - 1) + P := by omega
        rw [hsub, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hm]
      exact hprev
    have hnext' : w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2 := by
      simpa [← hw] using hnext
    constructor
    · rw [hbndb]
      omega
    · constructor
      · rw [hbndb]
        omega
      · constructor
        · simpa [hbndb] using hprev'
        · simpa [hbndb] using hnext'

/-- The rise run starting at position `0` cannot reach the C3 entry
before zero, so its length is below the period. -/
theorem blockRiseLen_zero_lt
    (w : List Nat) (P : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    blockRiseLen w 0 < P := by
  by_contra hnot
  have hge : P ≤ blockRiseLen w 0 := Nat.le_of_not_gt hnot
  have hle : blockRiseLen w 0 ≤ P := by
    unfold blockRiseLen
    have hseg := cyclicSegmentAt_length w 0 (by simp)
    calc
      risePrefixLength (cyclicSegmentAt w 0) ≤
          (cyclicSegmentAt w 0).length := risePrefixLength_le _
      _ = w.length := hseg
      _ = P := hw
  have heq : blockRiseLen w 0 = P := le_antisymm hle hge
  have hmem := risePrefixLength_mem (cyclicSegmentAt w 0) (P - 1)
    (by
      have heq' : risePrefixLength (cyclicSegmentAt w 0) = P := by
        simpa [blockRiseLen] using heq
      have hlt : P - 1 < P := by omega
      simpa [heq'])
  have hget := cyclicSegmentAt_getI_mod w 0 (P - 1) (by simp)
    (by rw [hw]; omega)
  have hmod : (0 + (P - 1)) % w.length = P - 1 := by
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by rw [hw]; omega)
  have hw12 : w.getI (P - 1) = 1 ∨ w.getI (P - 1) = 2 := by
    rw [hmod] at hget
    rwa [hget] at hmem
  rcases hw12 with h1 | h2
  · rw [h1] at hprev0
    omega
  · rw [h2] at hprev0
    omega

/-- If the boundary iteration returns to the starting boundary at a
positive step, the counted cycle length is no larger. -/
theorem blockCountOf_le_of_return
    (w : List Nat) (P b0 : Nat) (k : Nat) (hkpos : 0 < k)
    (hit : riseBoundaryIter w P b0 k = b0) :
    blockCountOf w P b0 ≤ k := by
  by_cases hkP : k ≤ P + 1
  · have hcomp := riseBoundaryIter_succ_compose w P b0 (k - 1)
    have hsub : k - 1 + 1 = k := by omega
    have hcomp' : riseBoundaryIter w P (nextRiseStart w P b0) (k - 1) =
        riseBoundaryIter w P b0 k := by
      rw [← hsub]
      exact hcomp
    have haux : riseRunCycleLenAux w P P b0 (nextRiseStart w P b0) ≤ k - 1 :=
      riseRunCycleLenAux_le_of_hit w P P b0 (nextRiseStart w P b0) (k - 1)
        (by omega) (by rwa [hcomp'])
    unfold blockCountOf riseRunCycleLen
    omega
  · have hle : blockCountOf w P b0 ≤ P + 1 :=
      blockCountOf_le_succ_P w P b0
    omega

/-- No intermediate boundary of the tour is position `0`: the tour
returns to zero only at its counted end. -/
theorem riseBoundaryIter_ne_zero_of_lt_blockCount
    (w : List Nat) (P : Nat) (k : Nat) (hkpos : 0 < k)
    (hk : k < blockCountOf w P 0) :
    riseBoundaryIter w P 0 k ≠ 0 := by
  intro hz
  have hle := blockCountOf_le_of_return w P 0 k hkpos hz
  omega

/-- The C3 run after the rise starting at position `0` is exactly the
C3 run ending before the next boundary (represented in `1..P`). -/
theorem blockC3Len_next_eq_of_cyclic_zero
    (w : List Nat) (P : Nat) (hw : w.length = P) (hP : 0 < P)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hnext0 : w.getI 0 = 1 ∨ w.getI 0 = 2)
    (hprev0 : 3 ≤ w.getI (P - 1)) :
    c3SuffixLengthAt w (cyclicBoundaryIndex P (nextRiseStart w P 0)) =
      c3PrefixLength (cyclicSegmentAt w (blockRiseLen w 0)) := by
  let L := blockRiseLen w 0
  let s := L
  have hsP : s < P := by
    dsimp [s, L]
    exact blockRiseLen_zero_lt w P hw hP hpos hprev0
  have hs1 : 1 ≤ s := by
    dsimp [s, L]
    exact blockRiseLen_pos_of_boundary w 0 (by simp) (by simpa using hnext0)
  let C := c3PrefixLength (cyclicSegmentAt w s)
  have hsC_le : s + C ≤ P := by
    by_contra hnot
    have hgt : P < s + C := Nat.lt_of_not_ge hnot
    let j := P - s
    have hjlt : j < C := by
      dsimp [j]
      omega
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w s) j hjlt
    have hklt : j < w.length := by
      have hle' := c3PrefixLength_le (cyclicSegmentAt w s)
      have hle'' : C ≤ w.length := by
        dsimp [C]
        have hseg := cyclicSegmentAt_length w s (by dsimp [s]; rw [hw]; omega)
        simpa [hseg] using hle'
      rw [hw]
      omega
    have hget := cyclicSegmentAt_getI_mod w s j (by dsimp [s]; rw [hw]; omega) hklt
    have hpos0 : (s + j) % w.length = 0 := by
      dsimp [j]
      have hsum : s + (P - s) = P := Nat.add_sub_of_le (by omega)
      rw [hsum]
      simp [hw]
    have h0ge : 3 ≤ w.getI 0 := by
      have hwget : w.getI ((s + j) % w.length) = w.getI 0 := by rw [hpos0]
      have hge' : 3 ≤ w.getI ((s + j) % w.length) := by rwa [hget] at hmem
      rwa [← hwget]
    rcases hnext0 with h1 | h2
    · rw [h1] at h0ge
      omega
    · rw [h2] at h0ge
      omega
  have hC3 : ∀ k, k < C → 3 ≤ w.getI (s + k) := by
    intro k hk
    have hmem := c3PrefixLength_mem (cyclicSegmentAt w s) k hk
    have hklt : k < w.length := by
      rw [hw]
      have hle' : C ≤ P := by
        have hseg := cyclicSegmentAt_length w s (by dsimp [s]; rw [hw]; omega)
        calc
          C ≤ (cyclicSegmentAt w s).length := by dsimp [C]; exact c3PrefixLength_le _
          _ = w.length := hseg
          _ = P := hw
      omega
    have hget := cyclicSegmentAt_getI_mod w s k (by dsimp [s]; rw [hw]; omega) hklt
    have hmod : (s + k) % w.length = s + k := by
      have hlt : s + k < P := by omega
      rw [hw]
      exact Nat.mod_eq_of_lt (by omega)
    have hge : 3 ≤ w.getI (s + k) := by
      rw [hget] at hmem
      rwa [hmod] at hmem
    exact hge
  have hprev12 : w.getI (s - 1) = 1 ∨ w.getI (s - 1) = 2 := by
    have hmem := risePrefixLength_mem (cyclicSegmentAt w 0) (L - 1)
      (by
        dsimp [L]
        simpa [blockRiseLen] using
          (Nat.sub_lt (blockRiseLen_pos_of_boundary w 0 (by simp)
            (by simpa using hnext0)) (by decide : 0 < 1)))
    have hklt : L - 1 < w.length := by
      have hle' : L ≤ w.length := by
        dsimp [L]
        have hseg := cyclicSegmentAt_length w 0 (by simp)
        calc
          risePrefixLength (cyclicSegmentAt w 0) ≤
              (cyclicSegmentAt w 0).length := risePrefixLength_le _
          _ = w.length := hseg
      rw [hw]
      omega
    have hget := cyclicSegmentAt_getI_mod w 0 (L - 1) (by simp) hklt
    have hmod : (0 + (L - 1)) % w.length = s - 1 := by
      have hsum : 0 + (L - 1) = s - 1 := by
        dsimp [s]
        omega
      rw [hsum]
      exact Nat.mod_eq_of_lt (by dsimp [s] at hsP; dsimp [s]; rw [hw]; omega)
    rw [hget] at hmem
    rwa [hmod] at hmem
  let q := nextRiseStart w P 0
  have hq : q = (s + C) % P := by
    dsimp [q, s, C, L]
    rw [nextRiseStart_eq_add_blockAdvance]
    unfold blockAdvance
    have hmod : (0 + blockRiseLen w 0) % P = s := by
      dsimp [s]
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by simpa [s] using hsP)
    rw [hmod]
    have hadd : 0 + (blockRiseLen w 0 + c3PrefixLength (cyclicSegmentAt w s)) =
        s + C := by
      dsimp [s, C]
      omega
    rw [hadd]
  let bndq := cyclicBoundaryIndex P q
  have hCq : c3SuffixLengthAt w bndq = C := by
    by_cases hlt : s + C < P
    · have hq' : q = s + C := by
        rw [hq]
        exact Nat.mod_eq_of_lt hlt
      have hbnd : bndq = s + C := by
        dsimp [bndq]
        rw [hq']
        unfold cyclicBoundaryIndex
        rw [if_neg (by dsimp [s]; omega : s + C ≠ 0)]
      have hC3' : ∀ k, k < (s + C) - s → 3 ≤ w.getI (s + k) := by
        intro k hk
        have hk' : k < C := by omega
        exact hC3 k hk'
      have hsle : s ≤ s + C := by omega
      have hlen : s + C ≤ w.length := by
        rw [hw]
        omega
      have hsub0 : c3SuffixLengthAt w (s + C) = (s + C) - s :=
        c3SuffixLengthAt_eq_sub_of_c3_run w (s + C) s hlen hsle hs1 hpos hC3' hprev12
      have hsub' : c3SuffixLengthAt w (s + C) = C := by
        rw [hsub0]
        omega
      rwa [← hbnd] at hsub'
    · have heq : s + C = P := by omega
      have hq' : q = 0 := by
        rw [hq, heq]
        simp
      have hbnd : bndq = P := by
        dsimp [bndq]
        rw [hq']
        simp [cyclicBoundaryIndex]
      have hC3' : ∀ k, k < P - s → 3 ≤ w.getI (s + k) := by
        intro k hk
        have hk' : k < C := by
          rw [← heq] at hk
          omega
        exact hC3 k hk'
      have hsle : s ≤ P := by omega
      have hlen : P ≤ w.length := by rw [hw]
      have hsub' : c3SuffixLengthAt w P = P - s :=
        c3SuffixLengthAt_eq_sub_of_c3_run w P s hlen hsle hs1 hpos hC3' hprev12
      have hPs : P - s = C := by omega
      rw [hbnd]
      rw [hsub', hPs]
  exact hCq

end StringFlow.CycleBridge
