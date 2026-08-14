import CycleBridge

namespace StringFlow

namespace CycleBridge

/-- The cyclic rotation of `w` starting after position `b`.
    For `b = w.length` this is the original word; for `b < w.length`
    it is `w.drop b ++ w.take b`, so rise runs may wrap around the end. -/
def cyclicSegmentAt (w : List Nat) (b : Nat) : List Nat :=
  w.drop b ++ w.take b

/-- The segment has the same length as the original word when the
rotation point is in range. -/
theorem cyclicSegmentAt_length (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    (cyclicSegmentAt w b).length = w.length := by
  unfold cyclicSegmentAt
  rw [List.length_append, List.length_drop, List.length_take_of_le hb]
  omega

/-- A cyclic rotation of a closed cycle word remains valid from the
prefix state at the rotation point. -/
theorem cyclicSegmentAt_valid
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) :
    StringFlow.Word.wordValid (cyclicSegmentAt w b)
      (StringFlow.Word.wordOrbit (w.take b) m) := by
  let pre : List Nat := w.take b
  let suf : List Nat := w.drop b
  let q : Nat := StringFlow.Word.wordOrbit pre m
  have hsplit : pre ++ suf = w := by
    dsimp [pre, suf]
    exact List.take_append_drop b w
  have hv0 : StringFlow.Word.wordValid (pre ++ suf) m := by
    simpa [hsplit] using h.hvalid
  have hparts := (S6Audit.wordValid_append pre suf m).mp hv0
  have hvalid_suf : StringFlow.Word.wordValid suf q := by
    change StringFlow.Word.wordValid suf
      (StringFlow.Word.wordOrbit pre m)
    exact hparts.2
  have hvalid_pre : StringFlow.Word.wordValid pre m := hparts.1
  have hclosed0 : StringFlow.Word.wordOrbit (pre ++ suf) m = m := by
    simpa [hsplit] using h.hclosed
  have hclosed_suf : StringFlow.Word.wordOrbit suf q = m := by
    change StringFlow.Word.wordOrbit suf
      (StringFlow.Word.wordOrbit pre m) = m
    simpa [S6Audit.wordOrbit_append] using hclosed0
  have hvalid_pre_at_end : StringFlow.Word.wordValid pre
      (StringFlow.Word.wordOrbit suf q) := by
    simpa [hclosed_suf] using hvalid_pre
  have hvalid_rot : StringFlow.Word.wordValid (suf ++ pre) q := by
    rw [S6Audit.wordValid_append]
    exact ⟨hvalid_suf, hvalid_pre_at_end⟩
  change StringFlow.Word.wordValid (suf ++ pre) q
  exact hvalid_rot

/-- A cyclic rotation of a closed cycle word remains closed from the
prefix state at the rotation point. -/
theorem cyclicSegmentAt_closed
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) :
    StringFlow.Word.wordOrbit (cyclicSegmentAt w b)
      (StringFlow.Word.wordOrbit (w.take b) m) =
      StringFlow.Word.wordOrbit (w.take b) m := by
  let pre : List Nat := w.take b
  let suf : List Nat := w.drop b
  let q : Nat := StringFlow.Word.wordOrbit pre m
  have hsplit : pre ++ suf = w := by
    dsimp [pre, suf]
    exact List.take_append_drop b w
  have hclosed0 : StringFlow.Word.wordOrbit (pre ++ suf) m = m := by
    simpa [hsplit] using h.hclosed
  have hclosed_suf : StringFlow.Word.wordOrbit suf q = m := by
    change StringFlow.Word.wordOrbit suf
      (StringFlow.Word.wordOrbit pre m) = m
    simpa [S6Audit.wordOrbit_append] using hclosed0
  have hclosed_rot : StringFlow.Word.wordOrbit (suf ++ pre) q = q := by
    rw [S6Audit.wordOrbit_append]
    rw [hclosed_suf]
  change StringFlow.Word.wordOrbit (suf ++ pre) q = q
  exact hclosed_rot

/-- A cyclic rotation of a closed cycle word remains valid and closed. -/
theorem cyclicSegmentAt_valid_closed
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) (_hb : b ≤ w.length) :
    StringFlow.Word.wordValid (cyclicSegmentAt w b)
      (StringFlow.Word.wordOrbit (w.take b) m) ∧
    StringFlow.Word.wordOrbit (cyclicSegmentAt w b)
      (StringFlow.Word.wordOrbit (w.take b) m) =
      StringFlow.Word.wordOrbit (w.take b) m := by
  exact ⟨cyclicSegmentAt_valid h b, cyclicSegmentAt_closed h b⟩

/-- A C3-to-rise boundary in the cyclic word.  The wrap boundary is
`b = w.length`, where the previous index is `w.length - 1` and the
next index is `0`. -/
def IsCyclicC3RiseBoundaryAt (w : List Nat) (b : Nat) : Prop :=
  0 < w.length ∧
    (b = w.length ∨ (1 ≤ b ∧ b < w.length)) ∧
    3 ≤ w.getI (b - 1) ∧
    (w.getI (b % w.length) = 1 ∨ w.getI (b % w.length) = 2)

def HasC3RiseBoundary (w : List Nat) : Prop :=
  ∃ b : Nat, IsCyclicC3RiseBoundaryAt w b

/-- The cyclic version of the block-boundary interface.  This is the
block-selection precondition; it deliberately allows `b = w.length`. -/
def cycleQb8Input_exists_c3_rise_run : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ b L t : Nat,
        IsCyclicC3RiseBoundaryAt w b ∧
        1 ≤ L ∧ L ≤ w.length ∧
        t = (cyclicSegmentAt w b).getI (L - 1) ∧
        (t = 1 ∨ t = 2) ∧
        (∀ k : Nat, k < L →
          (cyclicSegmentAt w b).getI k = 1 ∨
            (cyclicSegmentAt w b).getI k = 2) ∧
        (L = w.length ∨ 3 ≤ (cyclicSegmentAt w b).getI L)

/-- The local `hident` block using the cyclic suffix equation.  The
local depth remains `j = L`; the head is obtained from the rotated
segment `cyclicSegmentAt w b`, not from the non-wrapping expression
`w.take (b + L)`. -/
def cycleQb8InputExistsLocalHidentBlock : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ b L t delta : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        ∃ q Aj Wp Wj : Nat,
          IsCyclicC3RiseBoundaryAt w b ∧
          1 ≤ L ∧ L ≤ w.length ∧
          LocalHidentBlock L Wp Wj q Aj
            (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
              (StringFlow.Word.wordOrbit (w.take b) m)) t delta rt

end CycleBridge

end StringFlow
