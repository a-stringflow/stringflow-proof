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

end StringFlow.CycleBridge
