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

/-- The first entry of the cyclic rotation is the next entry after the
rotation point. -/
theorem cyclicSegmentAt_head (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    (cyclicSegmentAt w b).getI 0 = w.getI (b % w.length) := by
  by_cases hlt : b < w.length
  · have hdrop_pos : 0 < (w.drop b).length := by
      rw [List.length_drop]
      omega
    unfold cyclicSegmentAt
    rw [List.getI_append (w.drop b) (w.take b) 0 hdrop_pos]
    have hdrop : (w.drop b).getI 0 = w.getI b := by
      rw [List.getI_eq_getElem (l := w.drop b) (n := 0) hdrop_pos]
      rw [List.getI_eq_getElem (l := w) (n := b) hlt]
      exact List.getElem_drop (i := b) (j := 0)
        (h := by simpa [List.length_drop] using hdrop_pos)
    have hmod : b % w.length = b := Nat.mod_eq_of_lt hlt
    simpa [hdrop, hmod]
  · have hb_eq : b = w.length := by omega
    subst b
    simp [cyclicSegmentAt]

/-- Before the rotation reaches the end of the original word, its
`k`-th entry is exactly the global entry at `b+k`. -/
theorem cyclicSegmentAt_getI_nonwrap
    (w : List Nat) (b k : Nat) (hbk : b + k < w.length) :
    (cyclicSegmentAt w b).getI k = w.getI (b + k) := by
  have hkdrop : k < (w.drop b).length := by
    rw [List.length_drop]
    omega
  unfold cyclicSegmentAt
  rw [List.getI_append (w.drop b) (w.take b) k hkdrop]
  rw [List.getI_eq_getElem (l := w.drop b) (n := k) hkdrop]
  rw [List.getI_eq_getElem (l := w) (n := b + k) hbk]
  exact List.getElem_drop (i := b) (j := k)
    (h := by simpa [List.length_drop] using hkdrop)

/-- Every in-range entry of the cyclic segment is the original word
entry at the corresponding modular index.  This is the wrap-aware
counterpart of `cyclicSegmentAt_getI_nonwrap`. -/
theorem cyclicSegmentAt_getI_mod
    (w : List Nat) (b k : Nat)
    (hb : b <= w.length) (hk : k < w.length) :
    (cyclicSegmentAt w b).getI k =
      w.getI ((b + k) % w.length) := by
  have hlenpos : 0 < w.length := by omega
  by_cases hnon : b + k < w.length
  · rw [cyclicSegmentAt_getI_nonwrap w b k hnon]
    rw [Nat.mod_eq_of_lt hnon]
  · have hdrop_le : (w.drop b).length <= k := by
      rw [List.length_drop]
      omega
    unfold cyclicSegmentAt
    rw [List.getI_append_right (w.drop b) (w.take b) k hdrop_le]
    let r := b + k - w.length
    have hrb : r < b := by
      dsimp [r]
      omega
    have hrlen : r < w.length := lt_of_lt_of_le hrb hb
    have hr_take : r < (w.take b).length := by
      rw [List.length_take_of_le hb]
      exact hrb
    have htake : (w.take b).getI r = w.getI r := by
      rw [List.getI_eq_getElem (l := w.take b) (n := r) hr_take]
      rw [List.getI_eq_getElem (l := w) (n := r) hrlen]
      exact List.getElem_take (j := b) (i := r) (h := hr_take)
    have hsub : k - (w.drop b).length = r := by
      rw [List.length_drop]
      dsimp [r]
      omega
    rw [hsub, htake]
    have hsum : b + k = w.length + r := by
      dsimp [r]
      omega
    have hmod : (b + k) % w.length = r := by
      simp [hsum, Nat.add_mod, Nat.mod_eq_of_lt hrlen]
    rw [hmod]

/-- Every entry of a cyclic rotation is an entry of the original word. -/
theorem cyclicSegmentAt_mem {w : List Nat} {b x : Nat}
    (h : x ∈ cyclicSegmentAt w b) : x ∈ w := by
  unfold cyclicSegmentAt at h
  rcases List.mem_append.mp h with hdrop | htake
  · exact List.mem_of_mem_drop hdrop
  · exact List.mem_of_mem_take htake

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

/-- A nonempty cyclic word that contains both a C3 entry and a rise entry
has a C3-to-rise boundary.  This is the pure list-colouring argument behind
the cyclic block-selection layer. -/
theorem cyclicC3RiseBoundary_of_lists
    (w : List Nat)
    (hne : w ≠ [])
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hc3 : ∃ i, i < w.length ∧ 3 ≤ w.getI i)
    (hrise : ∃ j, j < w.length ∧ (w.getI j = 1 ∨ w.getI j = 2)) :
    HasC3RiseBoundary w := by
  rcases hc3 with ⟨i0, hi0, hi0ge⟩
  rcases hrise with ⟨j, hj, hjr⟩
  have hlenpos : 0 < w.length := List.length_pos_iff.mpr hne
  by_contra hno
  have hsucc : ∀ k, k < w.length → 3 ≤ w.getI k →
      3 ≤ w.getI ((k + 1) % w.length) := by
    intro k hk hkge
    by_contra hnot
    have hmodlt : (k + 1) % w.length < w.length := Nat.mod_lt _ hlenpos
    have hpos_next : 1 ≤ w.getI ((k + 1) % w.length) := by
      rw [List.getI_eq_getElem (l := w) (n := (k + 1) % w.length) hmodlt]
      exact hpos _ (List.getElem_mem hmodlt)
    have hnext12 : w.getI ((k + 1) % w.length) = 1 ∨
        w.getI ((k + 1) % w.length) = 2 := by omega
    have hb : IsCyclicC3RiseBoundaryAt w (k + 1) := by
      unfold IsCyclicC3RiseBoundaryAt
      constructor
      · exact hlenpos
      · constructor
        · by_cases hlast : k + 1 = w.length
          · left
            exact hlast
          · right
            constructor <;> omega
        · constructor
          · have hprev : k + 1 - 1 = k := by omega
            simpa [hprev] using hkge
          · exact hnext12
    exact hno ⟨k + 1, hb⟩
  have hcycle : ∀ k, k < w.length →
      3 ≤ w.getI ((i0 + k) % w.length) := by
    intro k hk
    induction k with
    | zero =>
        simpa [Nat.mod_eq_of_lt hi0] using hi0ge
    | succ k ih =>
        have hprev : 3 ≤ w.getI ((i0 + k) % w.length) := ih (by omega)
        have hmod : (i0 + k) % w.length < w.length := Nat.mod_lt _ hlenpos
        have hnext := hsucc ((i0 + k) % w.length) hmod hprev
        have hidx : ((i0 + k) % w.length + 1) % w.length =
            (i0 + (k + 1)) % w.length := by
          rw [show i0 + (k + 1) = i0 + k + 1 by omega]
          exact Nat.mod_add_mod (i0 + k) w.length 1
        simpa [hidx] using hnext
  let k := (j + w.length - i0) % w.length
  have hklt : k < w.length := by
    dsimp [k]
    exact Nat.mod_lt _ hlenpos
  have htarget : (i0 + k) % w.length = j := by
    dsimp [k]
    rw [Nat.add_mod_mod]
    have hi0lt : i0 < w.length := hi0
    have hposdiff : 0 < j + w.length - i0 := by omega
    have h1 : i0 + (j + w.length - i0) = j + w.length := by omega
    rw [h1]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hj
  have hc3j : 3 ≤ w.getI j := by
    have hh := hcycle k hklt
    simpa [htarget] using hh
  rcases hjr with h1 | h2
  · rw [h1] at hc3j
    omega
  · rw [h2] at hc3j
    omega

/-- Every real closed QB-8 word has a cyclic C3-to-rise boundary.  This
closes the first half of the cyclic block-selection layer: the boundary
itself exists without any scanning or extra range hypothesis. -/
theorem cycleQb8Input_has_c3_rise_boundary
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    HasC3RiseBoundary w := by
  rcases cycleQb8Input_exists_c3_index h with ⟨i, hi, hi3⟩
  rcases cycleQb8Input_exists_rise_index h with ⟨j, hj, hj12⟩
  have hne : w ≠ [] := by
    intro hnil
    have hlen : 2 ≤ ([] : List Nat).length := by
      simpa [hnil] using cycleQb8Input_length_ge_two h
    norm_num at hlen
  rcases cycleQb8Input_cycle_params h with ⟨c, p, hw, hm, hS, hr, hc⟩
  have hpos : ∀ x, x ∈ w → 1 ≤ x := by
    intro x hx
    rw [hw] at hx
    exact cycleWord_mem_ge_one c p hx
  exact cyclicC3RiseBoundary_of_lists w hne hpos
    ⟨i, hi, hi3⟩ ⟨j, hj, hj12⟩

/-- The rise predicate used to isolate a maximal rise run. -/
abbrev isRiseStep (t : Nat) : Prop :=
  t = 1 ∨ t = 2

/-- Boolean form of `isRiseStep`, for `List.takeWhile`. -/
def risePred (t : Nat) : Bool :=
  decide (isRiseStep t)

/-- Length of the initial rise run of a word. -/
def risePrefixLength (w : List Nat) : Nat :=
  (w.takeWhile risePred).length

/-- If a word starts with a rise step, its initial rise run is nonempty. -/
theorem risePrefixLength_pos_of_head
    (w : List Nat) (h : isRiseStep (w.getI 0)) :
    1 ≤ risePrefixLength w := by
  cases w with
  | nil =>
      rcases h with h1 | h2
      · norm_num at h1
      · norm_num at h2
  | cons t ts =>
      have ht : isRiseStep t := by simpa using h
      have hb : risePred t = true := by
        unfold risePred
        exact decide_eq_true ht
      dsimp [risePrefixLength]
      rw [List.takeWhile_cons_of_pos hb]
      simp

/-- Every entry before the initial rise-run length is a rise step. -/
theorem risePrefixLength_mem
    (w : List Nat) (k : Nat)
    (hk : k < risePrefixLength w) :
    isRiseStep (w.getI k) := by
  induction w generalizing k with
  | nil =>
      have hk0 : k < 0 := by simpa [risePrefixLength] using hk
      exact False.elim (Nat.not_lt_zero k hk0)
  | cons t ts ih =>
      by_cases ht : isRiseStep t
      · have hb : risePred t = true := by
          unfold risePred
          exact decide_eq_true ht
        cases k with
        | zero =>
            simpa using ht
        | succ k =>
            have hik : k < (ts.takeWhile risePred).length := by
              dsimp [risePrefixLength] at hk
              rw [List.takeWhile_cons_of_pos hb] at hk
              simpa using hk
            have hih := ih k (by simpa [risePrefixLength] using hik)
            simpa [List.getI_cons_succ] using hih
      · have hb : risePred t = false := by
          unfold risePred
          exact decide_eq_false ht
        have hb' : ¬ risePred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        have hlen : risePrefixLength (t :: ts) = 0 := by
          dsimp [risePrefixLength]
          rw [List.takeWhile_cons_of_neg hb']
          rfl
        rw [hlen] at hk
        omega

/-- The initial rise run is not longer than the word. -/
theorem risePrefixLength_le (w : List Nat) :
    risePrefixLength w ≤ w.length := by
  dsimp [risePrefixLength]
  exact (List.takeWhile_prefix risePred).length_le

/-- If the initial rise run stops before the end of a word whose entries are
all positive, the stopping entry is a C3 step. -/
theorem risePrefixLength_stop
    (w : List Nat)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hstop : risePrefixLength w < w.length) :
    3 ≤ w.getI (risePrefixLength w) := by
  induction w with
  | nil =>
      simp [risePrefixLength] at hstop
  | cons t ts ih =>
      by_cases ht : isRiseStep t
      · have hb : risePred t = true := by
          unfold risePred
          exact decide_eq_true ht
        have hstopRaw : (ts.takeWhile risePred).length < ts.length := by
          dsimp [risePrefixLength] at hstop
          rw [List.takeWhile_cons_of_pos hb] at hstop
          simpa using hstop
        have hpos' : ∀ x, x ∈ ts → 1 ≤ x := by
          intro x hx
          exact hpos x (List.mem_cons.mpr (Or.inr hx))
        have hih := ih hpos' (by simpa [risePrefixLength] using hstopRaw)
        have hidx : (t :: ts).getI (risePrefixLength (t :: ts)) =
            ts.getI (risePrefixLength ts) := by
          dsimp [risePrefixLength]
          rw [List.takeWhile_cons_of_pos hb]
          rw [show (t :: ts.takeWhile risePred).length =
              (ts.takeWhile risePred).length + 1 by simp]
          rw [List.getI_cons_succ]
        simpa [hidx] using hih
      · have hb : risePred t = false := by
          unfold risePred
          exact decide_eq_false ht
        have hb' : ¬ risePred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        have hlen : risePrefixLength (t :: ts) = 0 := by
          dsimp [risePrefixLength]
          rw [List.takeWhile_cons_of_neg hb']
          rfl
        rw [hlen]
        have htp : 1 ≤ t := hpos t (by simp)
        have htge : 3 ≤ t := by omega
        simpa using htge

/-- Boolean form of the C3 predicate. -/
def c3Pred (t : Nat) : Bool :=
  decide (3 ≤ t)

/-- Length of the initial C3 run of a word. -/
def c3PrefixLength (w : List Nat) : Nat :=
  (w.takeWhile c3Pred).length

/-- If a word starts with a C3 step, its initial C3 run is nonempty. -/
theorem c3PrefixLength_pos_of_head
    (w : List Nat) (h : 3 ≤ w.getI 0) :
    1 ≤ c3PrefixLength w := by
  cases w with
  | nil =>
      have h0 : 3 ≤ ([] : List Nat).getI 0 := by simpa using h
      norm_num at h0
  | cons t ts =>
      have ht : 3 ≤ t := by simpa using h
      have hb : c3Pred t = true := by
        unfold c3Pred
        exact decide_eq_true ht
      dsimp [c3PrefixLength]
      rw [List.takeWhile_cons_of_pos hb]
      simp

/-- Every entry before the initial C3-run length is a C3 step. -/
theorem c3PrefixLength_mem
    (w : List Nat) (k : Nat)
    (hk : k < c3PrefixLength w) :
    3 ≤ w.getI k := by
  induction w generalizing k with
  | nil =>
      have hk0 : k < 0 := by simpa [c3PrefixLength] using hk
      exact False.elim (Nat.not_lt_zero k hk0)
  | cons t ts ih =>
      by_cases ht : 3 ≤ t
      · have hb : c3Pred t = true := by
          unfold c3Pred
          exact decide_eq_true ht
        cases k with
        | zero =>
            simpa using ht
        | succ k =>
            have hik : k < (ts.takeWhile c3Pred).length := by
              dsimp [c3PrefixLength] at hk
              rw [List.takeWhile_cons_of_pos hb] at hk
              simpa using hk
            have hih := ih k (by simpa [c3PrefixLength] using hik)
            simpa [List.getI_cons_succ] using hih
      · have hb : c3Pred t = false := by
          unfold c3Pred
          exact decide_eq_false ht
        have hb' : ¬ c3Pred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        have hlen : c3PrefixLength (t :: ts) = 0 := by
          dsimp [c3PrefixLength]
          rw [List.takeWhile_cons_of_neg hb']
          rfl
        rw [hlen] at hk
        omega

/-- The initial C3 run is not longer than the word. -/
theorem c3PrefixLength_le (w : List Nat) :
    c3PrefixLength w ≤ w.length := by
  dsimp [c3PrefixLength]
  exact (List.takeWhile_prefix c3Pred).length_le

/-- If the initial C3 run stops before the end of a word whose entries
are all positive, the stopping entry is a rise step. -/
theorem c3PrefixLength_stop
    (w : List Nat)
    (hpos : ∀ x, x ∈ w → 1 ≤ x)
    (hstop : c3PrefixLength w < w.length) :
    w.getI (c3PrefixLength w) = 1 ∨ w.getI (c3PrefixLength w) = 2 := by
  induction w with
  | nil =>
      simp [c3PrefixLength] at hstop
  | cons t ts ih =>
      by_cases ht : 3 ≤ t
      · have hb : c3Pred t = true := by
          unfold c3Pred
          exact decide_eq_true ht
        have hstopRaw : (ts.takeWhile c3Pred).length < ts.length := by
          dsimp [c3PrefixLength] at hstop
          rw [List.takeWhile_cons_of_pos hb] at hstop
          simpa using hstop
        have hpos' : ∀ x, x ∈ ts → 1 ≤ x := by
          intro x hx
          exact hpos x (List.mem_cons.mpr (Or.inr hx))
        have hih := ih hpos' (by simpa [c3PrefixLength] using hstopRaw)
        have hidx : (t :: ts).getI (c3PrefixLength (t :: ts)) =
            ts.getI (c3PrefixLength ts) := by
          dsimp [c3PrefixLength]
          rw [List.takeWhile_cons_of_pos hb]
          rw [show (t :: ts.takeWhile c3Pred).length =
              (ts.takeWhile c3Pred).length + 1 by simp]
          rw [List.getI_cons_succ]
        simpa [hidx] using hih
      · have hb : c3Pred t = false := by
          unfold c3Pred
          exact decide_eq_false ht
        have hb' : ¬ c3Pred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        have hlen : c3PrefixLength (t :: ts) = 0 := by
          dsimp [c3PrefixLength]
          rw [List.takeWhile_cons_of_neg hb']
          rfl
        rw [hlen]
        have htp : 1 ≤ t := hpos t (by simp)
        have hnot : ¬ 3 ≤ t := by
          intro hge
          exact ht hge
        have hlt : t < 3 := Nat.lt_of_not_ge hnot
        interval_cases t <;> simp at htp ⊢

/-- The `k`-th entry of a reversed list is the entry mirrored from the
end of the original list. -/
lemma reverse_getI_of_lt (l : List Nat) (k : Nat) (hk : k < l.length) :
    l.reverse.getI k = l.getI (l.length - 1 - k) := by
  have hk' : k < l.reverse.length := by simpa using hk
  rw [List.getI_eq_getElem (l := l.reverse) (n := k) hk']
  rw [List.getI_eq_getElem (l := l) (n := l.length - 1 - k) (by omega)]
  exact List.getElem_reverse hk'

/-- Length of the maximal C3 run ending immediately before position
`b` in the cyclic word.  This is the C3 chain of the cyclic block whose
rise run starts at `b`. -/
def c3SuffixLengthAt (w : List Nat) (b : Nat) : Nat :=
  c3PrefixLength ((w.take b).reverse)

/-- A C3 entry immediately before `b` makes the C3 run ending there
nonempty. -/
theorem c3SuffixLengthAt_pos_of_head
    (w : List Nat) (b : Nat) (hb : 1 ≤ b)
    (hprev : 3 ≤ w.getI (b - 1)) :
    0 < c3SuffixLengthAt w b := by
  unfold c3SuffixLengthAt
  apply c3PrefixLength_pos_of_head
  have hlt : b - 1 < w.length := by
    by_contra hnot
    have hge : w.length ≤ b - 1 := Nat.le_of_not_gt hnot
    have hzero : w.getI (b - 1) = 0 := by
      simpa using (List.getI_eq_default (l := w) (n := b - 1) hge)
    omega
  have hbw : b ≤ w.length := by omega
  have hlen : 1 ≤ (w.take b).length := by
    rw [List.length_take_of_le hbw]
    exact hb
  rw [reverse_getI_of_lt (w.take b) 0 hlen]
  have hsub : (w.take b).length - 1 - 0 = b - 1 := by
    rw [List.length_take_of_le hbw]
    omega
  rw [hsub]
  have hlt2 : b - 1 < (w.take b).length := by
    rw [List.length_take_of_le hbw]
    omega
  have htake : (w.take b).getI (b - 1) = w.getI (b - 1) := by
    rw [List.getI_eq_getElem (l := w.take b) (n := b - 1) hlt2]
    rw [List.getI_eq_getElem (l := w) (n := b - 1) hlt]
    exact List.getElem_take (xs := w) (j := b) (i := b - 1)
  rw [htake]
  exact hprev

/-- The C3 run ending before `b` is not longer than `b`. -/
theorem c3SuffixLengthAt_le
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) :
    c3SuffixLengthAt w b ≤ b := by
  unfold c3SuffixLengthAt
  have hlen : ((w.take b).reverse).length = b := by
    rw [List.length_reverse, List.length_take_of_le hb]
  calc
    c3PrefixLength ((w.take b).reverse) ≤
        ((w.take b).reverse).length := c3PrefixLength_le _
    _ = b := hlen

/-- Every entry of the C3 run ending before `b` is a C3 step. -/
theorem c3SuffixLengthAt_mem
    (w : List Nat) (b : Nat) (hb : b ≤ w.length) (k : Nat)
    (hk : k < c3SuffixLengthAt w b) :
    3 ≤ w.getI (b - 1 - k) := by
  unfold c3SuffixLengthAt at hk
  have hmem := c3PrefixLength_mem ((w.take b).reverse) k hk
  have hlenRev : ((w.take b).reverse).length = b := by
    rw [List.length_reverse, List.length_take_of_le hb]
  have hlenTake : (w.take b).length = b := List.length_take_of_le hb
  have hlen : k < (w.take b).length := by
    have hle' : k < b := lt_of_lt_of_le hk (by
      calc
        c3PrefixLength ((w.take b).reverse) ≤
            ((w.take b).reverse).length := c3PrefixLength_le _
        _ = b := hlenRev)
    rwa [hlenTake]
  rw [reverse_getI_of_lt (w.take b) k hlen] at hmem
  have hsub : (w.take b).length - 1 - k = b - 1 - k := by
    simpa [hlenTake]
  rw [hsub] at hmem
  have hkltb : k < b := by simpa [hlenTake] using hlen
  have hlt : b - 1 - k < w.length := by omega
  have hlt2 : b - 1 - k < (w.take b).length := by
    rw [hlenTake]
    omega
  have htake : (w.take b).getI (b - 1 - k) = w.getI (b - 1 - k) := by
    rw [List.getI_eq_getElem (l := w.take b) (n := b - 1 - k) hlt2]
    rw [List.getI_eq_getElem (l := w) (n := b - 1 - k) hlt]
    exact List.getElem_take (xs := w) (j := b) (i := b - 1 - k)
  rw [htake] at hmem
  exact hmem

/-- The cyclic version of the block-boundary interface.  This is the
block-selection precondition; it deliberately allows `b = w.length`. -/
theorem cycleQb8Input_exists_c3_rise_run :
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
          (L = w.length ∨ 3 ≤ (cyclicSegmentAt w b).getI L) := by
  intro m S P w rise c3 h
  rcases cycleQb8Input_has_c3_rise_boundary h with ⟨b, hb⟩
  rcases hb with ⟨hlenpos, hbcase, _hprev3, hnextrise⟩
  have hble : b ≤ w.length := by
    rcases hbcase with hlast | hrange
    · omega
    · exact le_of_lt hrange.2
  let u := cyclicSegmentAt w b
  have hu0 : isRiseStep (u.getI 0) := by
    dsimp [u]
    rw [cyclicSegmentAt_head w b hble]
    rcases hnextrise with h1 | h2
    · left
      exact h1
    · right
      exact h2
  let L := risePrefixLength u
  let t := u.getI (L - 1)
  have hLpos : 1 ≤ L := by
    dsimp [L]
    exact risePrefixLength_pos_of_head u hu0
  have hLle : L ≤ w.length := by
    dsimp [L]
    have hu_len : u.length = w.length := cyclicSegmentAt_length w b hble
    calc
      risePrefixLength u ≤ u.length := risePrefixLength_le u
      _ = w.length := hu_len
  have ht_rise : t = 1 ∨ t = 2 := by
    dsimp [t, L]
    exact risePrefixLength_mem u (risePrefixLength u - 1) (by omega)
  have hall : ∀ k : Nat, k < L →
      (cyclicSegmentAt w b).getI k = 1 ∨
        (cyclicSegmentAt w b).getI k = 2 := by
    intro k hk
    have hk' : k < risePrefixLength u := by
      dsimp [L] at hk
      exact hk
    have hrise := risePrefixLength_mem u k hk'
    dsimp [u] at hrise
    exact hrise
  have hstop : L = w.length ∨
      3 ≤ (cyclicSegmentAt w b).getI L := by
    by_cases hend : L = w.length
    · left
      exact hend
    · right
      have hu_len : u.length = w.length := cyclicSegmentAt_length w b hble
      have hlt : risePrefixLength u < u.length := by
        dsimp [L] at hend ⊢
        rw [hu_len]
        have hle := risePrefixLength_le u
        omega
      have hpos : ∀ x, x ∈ u → 1 ≤ x := by
        rcases cycleQb8Input_cycle_params h with ⟨c, p, hw, _hm, _hS,
          _hr, _hc⟩
        intro x hx
        have hxw : x ∈ w := cyclicSegmentAt_mem (w := w) (b := b) hx
        rw [hw] at hxw
        exact cycleWord_mem_ge_one c p hxw
      have hge := risePrefixLength_stop u hpos hlt
      dsimp [L]
      exact hge
  have hboundary : IsCyclicC3RiseBoundaryAt w b :=
    ⟨hlenpos, hbcase, _hprev3, hnextrise⟩
  refine ⟨b, L, t, hboundary, hLpos, hLle, rfl, ht_rise, hall, hstop⟩

/-- For a non-wrapping maximal rise run, the stop entry is the actual
global word entry immediately after its endpoint. -/
theorem maximal_cyclic_rise_run_outgoing_c3_nonwrap
    {P : Nat} {w : List Nat} {b L : Nat}
    (hlength : w.length = P) (hbL : b + L < P)
    (hstop : L = w.length \/ 3 <= (cyclicSegmentAt w b).getI L) :
    3 <= w.getI (b + L) := by
  have hglobal : b + L < w.length := by
    rw [hlength]
    exact hbL
  rcases hstop with hfull | hc3
  · rw [hfull] at hglobal
    omega
  · rw [cyclicSegmentAt_getI_nonwrap w b L hglobal] at hc3
    exact hc3

/-- Every closed QB-8 word has a real terminal at its chosen cyclic
C3-to-rise boundary.  This is the starting point for the global hident:
the boundary and rise-run witness are structural, and the terminal is
constructed by `cycleQb8Input_angelina_real_terminal`. -/
theorem cycleQb8Input_exists_real_boundary_terminal :
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
        ∃ b L : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
          IsCyclicC3RiseBoundaryAt w b ∧
          1 ≤ L ∧ L ≤ w.length ∧
          rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 := by
  intro m S P w rise c3 h
  rcases cycleQb8Input_exists_c3_rise_run m S P w rise c3 h with
    ⟨b, L, _t, hb, hL, hLle, _ht, _hrise, _hstop⟩
  rcases hb with ⟨hlenpos, hbcase, hprev3, _hnextrise⟩
  have hb1 : 1 ≤ b := by
    rcases hbcase with hlast | hrange
    · omega
    · omega
  have hble : b ≤ w.length := by
    rcases hbcase with hlast | hrange
    · omega
    · exact le_of_lt hrange.2
  rcases cycleQb8Input_angelina_real_terminal h b hb1 hble hprev3 with
    ⟨rt, hrt⟩
  have hboundary : IsCyclicC3RiseBoundaryAt w b :=
    ⟨hlenpos, hbcase, hprev3, _hnextrise⟩
  exact ⟨b, L, rt, hboundary, hL, hLle, hrt⟩

/-- The cyclic local block equation for the rotated segment
`(cyclicSegmentAt w b).take L`.  This is the wrapping form of
`cycleQb8Input_local_block_equation`: it starts at the cyclic C3-to-rise
boundary and remains correct when the rise run crosses the end of `w`. -/
theorem cycleQb8Input_cyclic_local_block_data
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat)
    (hb : IsCyclicC3RiseBoundaryAt w b)
    (hL : 1 ≤ L) (hLle : L ≤ w.length) :
    let u := (cyclicSegmentAt w b).take L
    let q := StringFlow.Word.wordOrbit (w.take b) m
    let rj := StringFlow.Word.wordOrbit u q
    ∃ Aj Wp Wj t : Nat,
      Aj = StringFlow.Word.wordA u ∧
      Wj = StringFlow.wordWeight u ∧
      Wp = StringFlow.wordWeight (u.take (L - 1)) ∧
      t = u.getI (L - 1) ∧
      Wj = Wp + t ∧
      2 ^ Wj * rj = Aj + 5 ^ L * q ∧
      (Aj + 5 ^ L * q) % 2 ^ Wj = 0 ∧
      rj = (Aj + 5 ^ L * q) / 2 ^ Wj := by
  let u := (cyclicSegmentAt w b).take L
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let rj := StringFlow.Word.wordOrbit u q
  rcases hb with ⟨_hlenpos, hbcase, _hprev3, _hnextrise⟩
  have hble : b ≤ w.length := by
    rcases hbcase with hlast | hrange
    · omega
    · exact le_of_lt hrange.2
  have hrot_len : (cyclicSegmentAt w b).length = w.length :=
    cyclicSegmentAt_length w b hble
  have hu_len : u.length = L := by
    dsimp [u]
    rw [List.length_take_of_le]
    rw [hrot_len]
    exact hLle
  have hvalid_rot : StringFlow.Word.wordValid (cyclicSegmentAt w b) q := by
    dsimp [q]
    exact cyclicSegmentAt_valid h b
  have hvalid_u : StringFlow.Word.wordValid u q := by
    have hsplit_rot : cyclicSegmentAt w b =
        u ++ (cyclicSegmentAt w b).drop L := by
      dsimp [u]
      exact (List.take_append_drop L (cyclicSegmentAt w b)).symm
    have hvalid_rot' : StringFlow.Word.wordValid
        (u ++ ((cyclicSegmentAt w b).drop L)) q := by
      rw [← hsplit_rot]
      exact hvalid_rot
    exact (S6Audit.wordValid_append u ((cyclicSegmentAt w b).drop L) q).mp
      hvalid_rot' |>.1
  have hid := StringFlow.Word.word_orbit_identity u q hvalid_u
  let Aj := StringFlow.Word.wordA u
  let Wj := StringFlow.wordWeight u
  let Wp := StringFlow.wordWeight (u.take (L - 1))
  let t := u.getI (L - 1)
  have hlast_lt : L - 1 < u.length := by
    rw [hu_len]
    omega
  have htake := List.take_concat_get (l := u) (i := L - 1) hlast_lt
  have htake' : (u.take (L - 1)).concat u[L - 1] =
      List.take (L - 1 + 1) u := htake
  have htake_append : u.take (L - 1) ++ [u[L - 1]] = u.take L := by
    rw [← List.concat_eq_append]
    simpa [Nat.sub_add_cancel hL] using htake'
  have htake_all : u.take L = u := by
    rw [List.take_of_length_le (le_of_eq hu_len)]
  have hsplit_raw : u = u.take (L - 1) ++ [u[L - 1]] := by
    calc
      u = u.take L := htake_all.symm
      _ = u.take (L - 1) ++ [u[L - 1]] := htake_append.symm
  have hget : u[L - 1] = u.getI (L - 1) := by
    have hd := List.getElem_eq_getD (l := u) (i := L - 1)
      (h := hlast_lt) 0
    unfold List.getI
    exact hd
  have hsplit : u = u.take (L - 1) ++ [u.getI (L - 1)] := by
    conv_lhs => rw [hsplit_raw]
    rw [hget]
  have hWleft : StringFlow.wordWeight u =
      StringFlow.wordWeight (u.take (L - 1)) + u.getI (L - 1) := by
    conv_lhs => rw [hsplit]
    exact UnifiedCoreAudit.wordWeight_append_singleton
      (u.take (L - 1)) (u.getI (L - 1))
  have hW : Wj = Wp + t := by
    simpa [Wj, Wp, t] using hWleft
  have hid' : 2 ^ Wj * rj = Aj + 5 ^ L * q := by
    dsimp [Wj, Aj, rj]
    have h := hid
    rw [hu_len] at h
    simpa [Nat.add_comm] using h
  have hEq : Aj + 5 ^ L * q = 2 ^ Wj * rj := by
    exact hid'.symm
  have hdiv : (Aj + 5 ^ L * q) % 2 ^ Wj = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨rj, hEq⟩
  have hrjform : rj = (Aj + 5 ^ L * q) / 2 ^ Wj := by
    rw [hEq]
    exact (Nat.mul_div_right rj (Nat.pow_pos (by decide : 0 < 2) :
      0 < 2 ^ Wj)).symm
  exact ⟨Aj, Wp, Wj, t, rfl, rfl, rfl, rfl, hW, hid', hdiv, hrjform⟩

/-- When the selected rise run does not wrap, the cyclic local head is
the ordinary global prefix head at depth `b + L`. -/
theorem cyclic_local_head_eq_global_nonwrap
    {m : Nat} {w : List Nat}
    (b L : Nat) (hbL : b + L ≤ w.length) :
    StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m) =
      StringFlow.Word.wordOrbit (w.take (b + L)) m := by
  have hdrop_len : L ≤ (w.drop b).length := by
    rw [List.length_drop]
    omega
  have hseg1 : (cyclicSegmentAt w b).take L = (w.drop b).take L := by
    unfold cyclicSegmentAt
    rw [List.take_append_of_le_length hdrop_len]
  have hseg2 : (w.drop b).take L = (w.take (b + L)).drop b := by
    rw [List.take_drop]
  calc
    StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m) =
      StringFlow.Word.wordOrbit ((w.drop b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m) := by rw [hseg1]
    _ = StringFlow.Word.wordOrbit ((w.take (b + L)).drop b)
        (StringFlow.Word.wordOrbit (w.take b) m) := by rw [hseg2]
    _ = StringFlow.Word.wordOrbit (w.take (b + L)) m :=
      (wordOrbit_take_drop w m b L hbL).symm

/-- Given the cyclic local block equation and one genuine reset terminal,
this assembles the `LocalHidentBlock` without assuming that the rise run is
non-wrapping.  The terminal equation `hterm` remains the exact arithmetic
input to the next layer; the remaining fields are constructed from
`CycleQb8Input`. -/
theorem cycleQb8Input_cyclic_local_hident_block
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L t δ : Nat)
    (hb : IsCyclicC3RiseBoundaryAt w b)
    (hL : 1 ≤ L) (hLle : L ≤ w.length)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (ht_last : t = (cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3))
    (hterm : IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) δ rt)
    (hk : rt.k + 1 ≤ L)
    (hslt : rt.s < 5 ^ (L - rt.k - 1))
    (hrj_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)))
    (hrj_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m))) :
    ∃ q Aj Wp Wj : Nat,
      LocalHidentBlock L Wp Wj q Aj
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
          (StringFlow.Word.wordOrbit (w.take b) m)) t δ rt := by
  let u := (cyclicSegmentAt w b).take L
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let rj := StringFlow.Word.wordOrbit u q
  rcases cycleQb8Input_cyclic_local_block_data h b L hb hL hLle with
    ⟨Aj, Wp, Wj, t0, hAj, hWj, hWp, ht0, hW, hid, hdiv, hrjform⟩
  rcases hb with ⟨_hlenpos, hbcase, _hprev3, _hnextrise⟩
  have hble : b ≤ w.length := by
    rcases hbcase with hlast | hrange
    · omega
    · exact le_of_lt hrange.2
  have hrot_len : (cyclicSegmentAt w b).length = w.length :=
    cyclicSegmentAt_length w b hble
  have ht_take :
      ((cyclicSegmentAt w b).take L).getI (L - 1) =
        (cyclicSegmentAt w b).getI (L - 1) := by
    unfold List.getI
    have h1 : L - 1 < ((cyclicSegmentAt w b).take L).length := by
      rw [List.length_take_of_le (by rw [hrot_len]; exact hLle)]
      omega
    have h2 : L - 1 < (cyclicSegmentAt w b).length := by
      rw [hrot_len]
      omega
    have hget : ((cyclicSegmentAt w b).take L)[L - 1] =
        (cyclicSegmentAt w b)[L - 1] :=
      List.getElem_take (j := L) (i := L - 1) (h := h1)
    have hd1 := List.getElem_eq_getD
      (l := (cyclicSegmentAt w b).take L) (i := L - 1) (h := h1) 0
    have hd2 := List.getElem_eq_getD
      (l := cyclicSegmentAt w b) (i := L - 1) (h := h2) 0
    calc
      ((cyclicSegmentAt w b).take L).getD (L - 1) 0 =
          ((cyclicSegmentAt w b).take L)[L - 1] := hd1.symm
      _ = (cyclicSegmentAt w b)[L - 1] := hget
      _ = (cyclicSegmentAt w b).getD (L - 1) 0 := hd2
  have ht_eq : t0 = t := by
    exact ht0.trans (ht_take.trans ht_last.symm)
  rw [ht_eq] at hW
  have hrjform' :
      rj = (Aj + 5 ^ L * q) / 2 ^ Wj := by
    exact hrjform
  refine ⟨q, Aj, Wp, Wj, ?_⟩
  exact {
    hW := hW
    ht := ht
    hδ := hδ
    hrj := hrjform'
    hdiv := hdiv
    hterm := hterm
    hk := hk
    hs_lt := hslt
    hrj_odd := hrj_odd
    hrj_reach := hrj_reach
  }

/-- Reset-equation form of the cyclic local hident constructor.  The
new terminal/reset equivalence removes `hterm` as a separately supplied
algebraic premise: once the same real terminal's `s,k` satisfy the
local `ResetHeadEq`, the exact hident block follows. -/
theorem cycleQb8Input_cyclic_local_hident_block_of_reset
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L t δ : Nat)
    (hb : IsCyclicC3RiseBoundaryAt w b)
    (hL : 1 ≤ L) (hLle : L ≤ w.length)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (ht_last : t = (cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3))
    (hreset : S6Audit.ResetHeadEq rt.s L rt.k t δ
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)))
    (hk : rt.k + 1 ≤ L)
    (hslt : rt.s < 5 ^ (L - rt.k - 1))
    (hrj_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)))
    (hrj_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m))) :
    ∃ q Aj Wp Wj : Nat,
      LocalHidentBlock L Wp Wj q Aj
        (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
          (StringFlow.Word.wordOrbit (w.take b) m)) t δ rt := by
  have hterm : IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) δ rt :=
    (isLocalResetTerminal_iff_resetHeadEq t L
      (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) δ rt ht hδ).mpr hreset
  exact cycleQb8Input_cyclic_local_hident_block
    h b L t δ hb hL hLle rt ht_last ht hδ hterm hk hslt
      hrj_odd hrj_reach

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
          rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 ∧
          LocalHidentBlock L Wp Wj q Aj
            (StringFlow.Word.wordOrbit ((cyclicSegmentAt w b).take L)
              (StringFlow.Word.wordOrbit (w.take b) m)) t delta rt

/-- Global-depth version of `cycleQb8Input_local_hident_block`: the
block starts at word index zero, has length `b + L`, and its head is
`wordOrbit (w.take (b + L)) m`.  All parameters except the genuine
global `hterm` are supplied by the cycle word. -/
theorem cycleQb8Input_global_hident_block_of_reset
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L t δ : Nat)
    (hL : 1 ≤ L) (hbL : b + L ≤ w.length)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2)
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3))
    (ht_last : w.getI (b + L - 1) = t)
    (hterm : IsLocalResetTerminal t (b + L)
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) δ rt)
    (hk : rt.k + 1 ≤ b + L)
    (hslt : rt.s < 5 ^ (b + L - rt.k - 1))
    (hrj_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (b + L)) m))
    (hrj_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit (w.take (b + L)) m)) :
    ∃ q Aj Wp Wj : Nat,
      LocalHidentBlock (b + L) Wp Wj q Aj
        (StringFlow.Word.wordOrbit (w.take (b + L)) m) t δ rt ∧
      rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 := by
  have hbL_pos : 1 ≤ b + L := Nat.le_trans hL (Nat.le_add_left L b)
  rcases (cycleQb8Input_local_hident_block h 0 (b + L) t δ hbL_pos
      (by simpa using hbL) rt
      ht hδ (by simpa using ht_last) (by simpa using hterm)
      (by simpa using hk) (by simpa using hslt)
      (by simpa using hrj_odd) (by simpa using hrj_reach)) with
    ⟨q, Aj, Wp, Wj, d⟩
  exact ⟨q, Aj, Wp, Wj, by simpa using d, hrt⟩

/-- The operative remaining input for `failureWindowExistence`: at a
non-wrapping cyclic C3-to-rise block, the global depth is `b + L`, and
the real terminal from `b - 1` satisfies the global hident and both
failure lower bounds.  The terminal equation is part of the statement,
so an arbitrary locally compatible `rt` cannot instantiate this input. -/
def cycleQb8InputExistsGlobalHidentBlock : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ b L t δ : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        ∃ q Aj Wp Wj : Nat,
          IsCyclicC3RiseBoundaryAt w b ∧
          1 ≤ L ∧ L ≤ w.length ∧
          b + L < P ∧
          rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 ∧
          w.getI (b + L - 1) = t ∧
          LocalHidentBlock (b + L) Wp Wj q Aj
            (StringFlow.Word.wordOrbit (w.take (b + L)) m) t δ rt ∧
          (t = 1 → 2 * (b + L) + 12 ≤
            twoValuation
              (5 ^ (rt.k + 1) * rt.s + 5 ^ (b + L) - 2)) ∧
          (t = 2 → 2 * (b + L) + 11 ≤
            twoValuation
              (5 ^ (rt.k + 1) * rt.s + δ * 5 ^ (b + L)))

/-- Once the global-depth hident and failure bounds exist,
`local_hident_to_global_failure_window` closes the entire
`failureWindowExistence` statement. -/
theorem failureWindowExistence_of_global_hident
    (hglobal : cycleQb8InputExistsGlobalHidentBlock) :
    failureWindowExistence := by
  intro m S P w rise c3 h
  rcases hglobal m S P w rise c3 h with
    ⟨b, L, t, δ, rt, q, Aj, Wp, Wj, _hb, _hL, _hLle, hj_lt, _hrt,
      hincoming, d, hfail_t1, hfail_t2⟩
  exact ⟨b + L, rt.k, t, δ, rt.s,
    local_hident_to_global_failure_window h hj_lt rfl hincoming d
      hfail_t1 hfail_t2⟩

/-- The remaining analytic input has two distinct sources:

1. real-orbit reset data at a non-wrapping cyclic C3-to-rise block:
   the terminal equation, global hident, and 5-adic size bounds;
2. the PMI block-sum result: `hfail_t1` / `hfail_t2`.

The PMI half is not implied by the real-orbit half, so both are kept in
the same statement only as a combined open input. -/
def cycleQb8InputExistsGlobalHidentAndPMIFailure : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ b L t δ : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        IsCyclicC3RiseBoundaryAt w b ∧
        1 ≤ L ∧ L ≤ w.length ∧
        b + L < P ∧
        rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 ∧
        t = w.getI (b + L - 1) ∧
        (t = 1 ∨ t = 2) ∧
        ((t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3)) ∧
        IsLocalResetTerminal t (b + L)
          (StringFlow.Word.wordOrbit (w.take (b + L)) m) δ rt ∧
        rt.k + 1 ≤ b + L ∧
        rt.s < 5 ^ (b + L - rt.k - 1) ∧
        (t = 1 → 2 * (b + L) + 12 ≤
          twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ (b + L) - 2)) ∧
        (t = 2 → 2 * (b + L) + 11 ≤
          twoValuation (5 ^ (rt.k + 1) * rt.s + δ * 5 ^ (b + L)))

/-- The combined real-orbit + PMI input assembles the full global
hident block. -/
theorem cycleQb8InputExistsGlobalHidentBlock_of_global_hident_and_pmi
    (hglobalTerm : cycleQb8InputExistsGlobalHidentAndPMIFailure) :
    cycleQb8InputExistsGlobalHidentBlock := by
  intro m S P w rise c3 h
  rcases hglobalTerm m S P w rise c3 h with
    ⟨b, L, t, δ, rt, hb, hL, hLle, hj_lt, hrt, ht_last, ht, hδ,
      hterm_eq, hk, hslt, hfail_t1, hfail_t2⟩
  have hbL : b + L ≤ w.length := by
    rw [h.hlength]
    exact le_of_lt hj_lt
  have hreach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) :=
    cycleQb8Input_prefix_full_reachable h (b + L) hbL
  have hodd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) :=
    S6Audit.FullOrbitFrom7_odd _ hreach
  rcases cycleQb8Input_global_hident_block_of_reset
      h b L t δ hL hbL rt hrt ht hδ
      ht_last.symm (by simpa using hterm_eq)
      (by simpa using hk) (by simpa using hslt)
      (by simpa using hodd) (by simpa using hreach) with
    ⟨q, Aj, Wp, Wj, d, hrt'⟩
  exact ⟨b, L, t, δ, rt, q, Aj, Wp, Wj, hb, hL, hLle, hj_lt, hrt',
    ht_last.symm, d, hfail_t1, hfail_t2⟩

/-- The combined real-orbit + PMI input closes
`failureWindowExistence`. -/
theorem failureWindowExistence_of_global_hident_and_pmi
    (hglobalTerm : cycleQb8InputExistsGlobalHidentAndPMIFailure) :
    failureWindowExistence :=
  failureWindowExistence_of_global_hident
    (cycleQb8InputExistsGlobalHidentBlock_of_global_hident_and_pmi
      hglobalTerm)

end CycleBridge

end StringFlow
