import Td0CertBridge

namespace StringFlow

/-- Positions of the `2` entries, largest index first (matching the
order produced by `combinations`). -/
def twosPositions : List Nat -> List Nat
  | [] => []
  | t :: ts =>
      (twosPositions ts).map (fun i => i + 1) ++
        (if t = 2 then [0] else [])

example : twosPositions [2,1,2] = [2,0] := by
  native_decide

example : twosPositions [1,2,2] = [2,1] := by
  native_decide

example : [2,0] ∈ combinations 3 2 := by
  native_decide

/-- Strictly decreasing list. -/
def DecList : List Nat -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b < a ∧ DecList (b :: rest)

theorem decList_head_gt_all (a : Nat) (l : List Nat) (h : DecList (a :: l)) :
    ∀ x ∈ l, x < a := by
  induction l generalizing a with
  | nil =>
      intro x hx
      cases hx
  | cons b rest ih =>
      intro x hx
      have hb : b < a := by
        simp [DecList] at h
        exact h.1
      have hrest : DecList (b :: rest) := by
        simp [DecList] at h
        exact h.2
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hb
      · have hxlt : x < b := ih b hrest x hx
        omega

theorem decList_map_add (l : List Nat) (h : DecList l) :
    DecList (l.map (fun i => i + 1)) := by
  induction l with
  | nil => simp [DecList]
  | cons a rest ih =>
      cases rest with
      | nil => simp [DecList]
      | cons b rest2 =>
          have hb : b < a := by
            simp [DecList] at h
            exact h.1
          have hrest : DecList (b :: rest2) := by
            simp [DecList] at h
            exact h.2
          have ih' := ih hrest
          simp [DecList, hb]
          exact ih'

theorem decList_append_zero (l : List Nat) (h : DecList l)
    (hpos : ∀ x ∈ l, 0 < x) : DecList (l ++ [0]) := by
  cases l with
  | nil => simp [DecList]
  | cons a rest =>
      cases rest with
      | nil =>
          simp [DecList, hpos a (by simp)]
      | cons b rest2 =>
          have hb : b < a := by
            simp [DecList] at h
            exact h.1
          have hrest : DecList (b :: rest2) := by
            simp [DecList] at h
            exact h.2
          have hposrest : ∀ x ∈ (b :: rest2), 0 < x := by
            intro x hx
            exact hpos x (by simp [hx])
          have ih' := decList_append_zero (b :: rest2) hrest hposrest
          simp [DecList, hb]
          exact ih'

theorem twosPositions_decList (w : List Nat) : DecList (twosPositions w) := by
  induction w with
  | nil =>
      simp [twosPositions, DecList]
  | cons t ts ih =>
      by_cases ht : t = 2
      · simp [twosPositions, ht]
        have hmap : DecList ((twosPositions ts).map (fun i => i + 1)) :=
          decList_map_add (twosPositions ts) ih
        have hpos : ∀ x ∈ (twosPositions ts).map (fun i => i + 1), 0 < x := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
          omega
        exact decList_append_zero
          ((twosPositions ts).map (fun i => i + 1)) hmap hpos
      · simp [twosPositions, ht]
        exact decList_map_add (twosPositions ts) ih

theorem twosPositions_length (w : List Nat) :
    (twosPositions w).length = (w.filter (fun t => t = 2)).length := by
  induction w with
  | nil => simp [twosPositions]
  | cons t ts ih =>
      by_cases ht : t = 2
      · simp [twosPositions, ht, ih]
      · simp [twosPositions, ht, ih]

theorem twosPositions_lt_length (w : List Nat) :
    ∀ x ∈ twosPositions w, x < w.length := by
  induction w with
  | nil => simp [twosPositions]
  | cons t ts ih =>
      intro x hx
      simp [twosPositions] at hx
      rcases hx with hmap | hzero
      · rcases hmap with ⟨i, hi, rfl⟩
        have hi' := ih i hi
        simp
        omega
      · by_cases ht : t = 2
        · simp [ht] at hzero
          subst x
          simp
        · simp [ht] at hzero

theorem mem_combinations_iff (pos : List Nat) (n k : Nat) :
    pos ∈ combinations n k ↔ pos.length = k ∧ DecList pos ∧ ∀ x ∈ pos, x < n := by
  induction n generalizing k pos with
  | zero =>
      cases k with
      | zero =>
          constructor
          · intro h
            simp [combinations] at h
            subst pos
            simp [DecList]
          · intro h
            rcases h with ⟨hlen, hdec, hlt⟩
            cases pos with
            | nil => simp [combinations]
            | cons a rest => simp at hlen
      | succ k =>
          constructor
          · intro h
            simp [combinations] at h
          · intro h
            rcases h with ⟨hlen, hdec, hlt⟩
            cases pos with
            | nil => simp at hlen
            | cons a rest =>
                have ha : a < 0 := hlt a (by simp)
                omega
  | succ n ih =>
      cases k with
      | zero =>
          constructor
          · intro h
            simp [combinations] at h
            subst pos
            simp [DecList]
          · intro h
            rcases h with ⟨hlen, hdec, hlt⟩
            cases pos with
            | nil => simp [combinations]
            | cons a rest => simp at hlen
      | succ k =>
          constructor
          · intro h
            simp [combinations] at h
            rcases h with h1 | h2
            · have hmem := (ih pos (k + 1)).1 h1
              rcases hmem with ⟨hlen, hdec, hlt⟩
              refine ⟨hlen, hdec, ?_⟩
              intro x hx
              have hxlt := hlt x hx
              omega
            · rcases h2 with ⟨c, hc, hpos⟩
              subst pos
              have hmem := (ih c k).1 hc
              rcases hmem with ⟨hlen, hdec, hlt⟩
              refine ⟨?_, ?_, ?_⟩
              · simp [hlen]
              · cases c with
                | nil => simp [DecList]
                | cons d rest =>
                    have hd : d < n := hlt d (by simp)
                    have hdec' : DecList (d :: rest) := hdec
                    simp [DecList, hd, hdec']
              · intro x hx
                rw [List.mem_cons] at hx
                rcases hx with rfl | hx
                · omega
                · have hxlt := hlt x hx
                  omega
          · intro h
            rcases h with ⟨hlen, hdec, hlt⟩
            cases pos with
            | nil => simp at hlen
            | cons a c =>
                have hclen : c.length = k := by
                  simp at hlen
                  exact hlen
                by_cases ha : a = n
                · subst a
                  change n :: c ∈ combinations n (k + 1) ++
                    (combinations n k).map (fun c => n :: c)
                  rw [List.mem_append]
                  right
                  rw [List.mem_map]
                  refine ⟨c, ?_, rfl⟩
                  apply (ih c k).2
                  refine ⟨hclen, ?_, ?_⟩
                  · cases c with
                    | nil => simp [DecList]
                    | cons d rest =>
                        simp [DecList] at hdec
                        exact hdec.2
                  · exact decList_head_gt_all n c hdec
                · change a :: c ∈ combinations n (k + 1) ++
                    (combinations n k).map (fun c => n :: c)
                  rw [List.mem_append]
                  left
                  apply (ih (a :: c) (k + 1)).2
                  refine ⟨hlen, hdec, ?_⟩
                  intro x hx
                  have ha_lt : a < n := by
                    have hlt_a := hlt a (by simp)
                    omega
                  rw [List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · omega
                  · have hxlt' := decList_head_gt_all a c hdec x hx
                    omega

theorem twosPositions_mem_combinations (w : List Nat) :
    twosPositions w ∈ combinations w.length (w.filter (fun t => t = 2)).length := by
  rw [mem_combinations_iff]
  exact ⟨twosPositions_length w, twosPositions_decList w, twosPositions_lt_length w⟩

theorem dropLast_filter_count_last_one (w : List Nat)
    (h : StringFlow.Word.wordLast w = 1) :
    (w.dropLast.filter (fun t => t = 2)).length =
      (w.filter (fun t => t = 2)).length := by
  induction w with
  | nil => simp [StringFlow.Word.wordLast] at h
  | cons t ts ih =>
      cases ts with
      | nil =>
          have ht : t = 1 := by
            simp [StringFlow.Word.wordLast] at h
            exact h
          simp [List.dropLast, ht]
      | cons u us =>
          have htail : StringFlow.Word.wordLast (u :: us) = 1 := by
            simp [StringFlow.Word.wordLast] at h
            exact h
          have ih' := ih htail
          by_cases ht : t = 2
          · simp [ht, ih']
          · simp [ht, ih']

theorem filter_count_of_last_two (w : List Nat)
    (h : StringFlow.Word.wordLast w = 2) :
    (w.filter (fun t => t = 2)).length =
      (w.dropLast.filter (fun t => t = 2)).length + 1 := by
  induction w with
  | nil => simp [StringFlow.Word.wordLast] at h
  | cons t ts ih =>
      cases ts with
      | nil =>
          have ht : t = 2 := by
            simp [StringFlow.Word.wordLast] at h
            exact h
          simp [List.dropLast, ht]
      | cons u us =>
          have htail : StringFlow.Word.wordLast (u :: us) = 2 := by
            simp [StringFlow.Word.wordLast] at h
            exact h
          have ih' := ih htail
          by_cases ht : t = 2
          · simp [ht, ih']
          · simp [ht, ih']

theorem dropLast_filter_count_last_two (w : List Nat)
    (h : StringFlow.Word.wordLast w = 2) :
    (w.dropLast.filter (fun t => t = 2)).length =
      (w.filter (fun t => t = 2)).length - 1 := by
  have hcount := filter_count_of_last_two w h
  omega

theorem dropLast_length (w : List Nat) : w.dropLast.length = w.length - 1 := by
  cases w with
  | nil => simp
  | cons t ts =>
      induction ts with
      | nil => simp
      | cons u us ih =>
          simp [List.dropLast]

theorem mem_twosPositions_of_last_one (w : List Nat)
    (hw : StringFlow.Word.wordLast w = 1) :
    w.length - 1 ∉ twosPositions w := by
  induction w with
  | nil => simp [StringFlow.Word.wordLast] at hw
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        have ht : t = 1 := by
          simp [StringFlow.Word.wordLast] at hw
          exact hw
        simp [twosPositions, ht]
      · have htail : StringFlow.Word.wordLast ts = 1 := by
          simp [StringFlow.Word.wordLast] at hw
          exact hw
        have ih' := ih htail
        have hlen : (t :: ts).length - 1 = ts.length := by
          cases ts with
          | nil => contradiction
          | cons u us => simp
        intro hx
        rw [hlen] at hx
        simp [twosPositions] at hx
        rcases hx with hmap | hzero
        · rcases hmap with ⟨i, hi, hix⟩
          have hix' : i + 1 = ts.length := by simpa [hlen] using hix
          have hi' : ts.length - 1 ∈ twosPositions ts := by
            have : i = ts.length - 1 := by omega
            simpa [this] using hi
          exact ih' hi'
        · by_cases ht2 : t = 2
          · have hz : ts.length = 0 := by simpa [ht2] using hzero
            cases ts with
            | nil => contradiction
            | cons u us => simp at hz
          · simp [ht2] at hzero

theorem twosPositions_mem_combinations_of_last_one (w : List Nat)
    (hw : StringFlow.Word.wordLast w = 1) :
    twosPositions w ∈ combinations (w.length - 1)
      (w.filter (fun t => t = 2)).length := by
  have hmem := twosPositions_mem_combinations w
  rw [mem_combinations_iff] at hmem
  rcases hmem with ⟨hlen, hdec, hlt⟩
  rw [mem_combinations_iff]
  refine ⟨hlen, hdec, ?_⟩
  intro x hx
  have hxlt := hlt x hx
  have hxne : x ≠ w.length - 1 := by
    intro hxeq
    have hmemlast : w.length - 1 ∈ twosPositions w := by
      simpa [hxeq] using hx
    exact mem_twosPositions_of_last_one w hw hmemlast
  have hlenpos : 0 < w.length := by
    by_contra hzero
    have h0 : w.length = 0 := by omega
    have hnil : w = [] := List.eq_nil_of_length_eq_zero h0
    subst w
    simp [StringFlow.Word.wordLast] at hw
  omega

theorem twosPositions_mem_combinations_of_last_two (w : List Nat)
    (_hw : StringFlow.Word.wordLast w = 2) :
    twosPositions w.dropLast ∈ combinations (w.length - 1)
      ((w.dropLast.filter (fun t => t = 2)).length) := by
  have hlen : w.dropLast.length = w.length - 1 := dropLast_length w
  simpa [hlen] using twosPositions_mem_combinations w.dropLast

/-- The word of length `L` whose `i`-th entry is `2` iff `i ∈ pos`. -/
def wordOfPos (L : Nat) (pos : List Nat) : List Nat :=
  (List.range L).map (fun i => if pos.contains i then 2 else 1)

/-- `auOfAux` of an appended singleton splits into the prefix and the
last contribution. -/
theorem auOfAux_append_singleton (A W : Nat) (word : List Nat) (t : Nat) :
    auOfAux A W (word ++ [t]) =
      5 * auOfAux A W word + 2 ^ (W + StringFlow.wordWeight word) := by
  induction word generalizing A W with
  | nil => simp [auOfAux, StringFlow.wordWeight]
  | cons u us ih =>
      simp [auOfAux]
      have h := ih (5 * A + 2 ^ W) (W + u)
      simpa [StringFlow.wordWeight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Weight of an appended singleton. -/
theorem wordWeight_append_singleton (word : List Nat) (t : Nat) :
    StringFlow.wordWeight (word ++ [t]) = StringFlow.wordWeight word + t := by
  induction word with
  | nil => simp [StringFlow.wordWeight]
  | cons u us ih =>
      simp [StringFlow.wordWeight, ih]
      omega

/-- The `auOfPos` fold is exactly `auOfAux` on `wordOfPos`. -/
theorem foldl_auOfPos_pair (A W L : Nat) (pos : List Nat) :
    (List.range L).foldl (fun st i =>
      let A := st.1
      let W := st.2
      let t := if pos.contains i then 2 else 1
      (5 * A + 2^W, W + t)) (A, W) =
    (auOfAux A W (wordOfPos L pos), W + StringFlow.wordWeight (wordOfPos L pos)) := by
  induction L generalizing A W with
  | zero => simp [wordOfPos, auOfAux, StringFlow.wordWeight]
  | succ L ih =>
      rw [List.range_succ]
      rw [List.foldl_append]
      have hpair := ih A W
      rw [hpair]
      let t := if pos.contains L then 2 else 1
      have hdef : wordOfPos (L + 1) pos = wordOfPos L pos ++ [t] := by
        dsimp [wordOfPos, t]
        rw [List.range_succ]
        simp [List.map_append]
      rw [hdef]
      by_cases hmem : L ∈ pos
      · have hc : pos.contains L = true := List.contains_iff_mem.mpr hmem
        simp [t, hc, auOfAux_append_singleton, wordWeight_append_singleton,
          StringFlow.wordWeight]
        omega
      · have hc : pos.contains L = false := by
          cases hc0 : pos.contains L with
          | false => rfl
          | true => exact False.elim (hmem (List.contains_iff_mem.mp hc0))
        simp [t, hc, auOfAux_append_singleton, wordWeight_append_singleton,
          StringFlow.wordWeight]
        omega

/-- `auOfPos` is `auOf` of the word built from the same positions. -/
theorem auOfPos_eq_auOf_wordOfPos (L : Nat) (pos : List Nat) :
    auOfPos L pos = auOf (wordOfPos L pos) := by
  unfold auOfPos auOf
  have h := foldl_auOfPos_pair 0 0 L pos
  simpa using congrArg Prod.fst h

/-- Membership in the shifted position list. -/
theorem mem_shift_iff (pos : List Nat) (i : Nat) (hi : 0 < i) :
    i ∈ (pos.map (fun x => x + 1)) ↔ i - 1 ∈ pos := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨x, hx, hxeq⟩
    have hx' : x = i - 1 := by omega
    simpa [hx'] using hx
  · intro h
    apply List.mem_map.mpr
    exact ⟨i - 1, h, by omega⟩

/-- The existential form of the shifted membership. -/
theorem exists_add_one_iff (pos : List Nat) (i : Nat) (hi : 0 < i) :
    (∃ a ∈ pos, a + 1 = i) ↔ i - 1 ∈ pos := by
  rw [← List.mem_map]
  exact mem_shift_iff pos i hi

/-- Prepending one step shifts all `2` positions by one. -/
theorem wordOfPos_cons_shift (t L : Nat) (pos : List Nat)
    (ht : t = 1 ∨ t = 2) (hlt : ∀ x ∈ pos, x < L) :
    wordOfPos (L + 1) ((pos.map (fun i => i + 1)) ++ (if t = 2 then [0] else [])) =
      t :: wordOfPos L pos := by
  apply List.ext_getElem?
  intro i
  by_cases hi0 : i = 0
  · subst i
    rcases ht with ht1 | ht2
    · simp [wordOfPos, ht1]
    · simp [wordOfPos, ht2]
  · have hi : 0 < i := by omega
    by_cases hiL : i < L + 1
    · have hmem : (((pos.map (fun x => x + 1)) ++ (if t = 2 then [0] else [])).contains i) =
          pos.contains (i - 1) := by
        simp only [List.contains_eq_mem]
        by_cases ht2 : t = 2
        · rw [ht2]
          simp [List.mem_append, List.mem_singleton, exists_add_one_iff pos i hi, hi]
          intro hi0'
          omega
        · have ht1 : t = 1 := by omega
          rw [ht1]
          simp [List.mem_append, exists_add_one_iff pos i hi, hi]
      unfold wordOfPos
      have hiL' : i - 1 < L := by omega
      rw [List.getElem?_map, List.getElem?_range hiL]
      rw [List.getElem?_cons, List.getElem?_map, List.getElem?_range hiL']
      simp [hi0, exists_add_one_iff pos i hi]
    · have hiLge : L + 1 ≤ i := by omega
      unfold wordOfPos
      have hnone1 : ((List.range (L + 1)).map (fun j =>
          if (((pos.map (fun x => x + 1)) ++ (if t = 2 then [0] else [])).contains j) then 2 else 1))[i]? = none := by
        rw [List.getElem?_map]
        have hnone1' : ((List.range (L + 1))[i]?) = none := by
          exact List.getElem?_eq_none_iff.mpr (by
            rw [List.length_range]
            omega)
        simp [hnone1']
      have hnone2 : (t :: (List.range L).map (fun j => if pos.contains j then 2 else 1))[i]? = none := by
        rw [List.getElem?_cons, List.getElem?_map]
        have hnone3 : ((List.range L)[i - 1]?) = none := by
          exact List.getElem?_eq_none_iff.mpr (by
            rw [List.length_range]
            omega)
        simp [hi0, hnone3]
      rw [hnone1, hnone2]

/-- `wordOfPos` has the requested length. -/
theorem wordOfPos_length (L : Nat) (pos : List Nat) :
    (wordOfPos L pos).length = L := by
  unfold wordOfPos
  simp

/-- Prepending one rising step gives the shifted `auOfPos`. -/
theorem auOfPos_cons_pos (t L : Nat) (pos : List Nat)
    (ht : t = 1 ∨ t = 2) (hlt : ∀ x ∈ pos, x < L) :
    auOfPos (L + 1) ((pos.map (fun i => i + 1)) ++ (if t = 2 then [0] else [])) =
      5 ^ L + 2 ^ t * auOfPos L pos := by
  rw [auOfPos_eq_auOf_wordOfPos, auOfPos_eq_auOf_wordOfPos]
  rw [wordOfPos_cons_shift t L pos ht hlt]
  have hlen : (wordOfPos L pos).length = L := wordOfPos_length L pos
  unfold auOf
  rw [auOfAux_eq]
  simp [hlen, StringFlow.GC.chainA]
  rw [← auOf_eq_chainA]
  rfl

/-- The chain numerator of a real `{1,2}` word is exactly
`auOfPos` at its `2` positions. -/
theorem wordA_eq_auOfPos_of_twosPositions (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    StringFlow.Word.wordA w = auOfPos w.length (twosPositions w) := by
  induction w with
  | nil => simp [StringFlow.Word.wordA, twosPositions, auOfPos]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      have hok' : ∀ x ∈ ts, x = 1 ∨ x = 2 := by
        intro x hx
        exact hok x (by simp [hx])
      have ih' := ih hok'
      have hpos : ∀ x ∈ twosPositions ts, x < ts.length :=
        twosPositions_lt_length ts
      have hcons : auOfPos (ts.length + 1) (twosPositions (t :: ts)) =
          5 ^ ts.length + 2 ^ t * auOfPos ts.length (twosPositions ts) := by
        rcases ht with ht1 | ht2
        · simpa [twosPositions, ht1] using
            (auOfPos_cons_pos t ts.length (twosPositions ts) (Or.inl ht1) hpos)
        · simpa [twosPositions, ht2] using
            (auOfPos_cons_pos t ts.length (twosPositions ts) (Or.inr ht2) hpos)
      simp [StringFlow.Word.wordA, ih']
      rw [hcons]

/-- A word with entries at least `1` has weight at least length. -/
theorem wordWeight_ge_length (w : List Nat) (hok : ∀ t ∈ w, 1 ≤ t) :
    w.length ≤ StringFlow.wordWeight w := by
  induction w with
  | nil => simp
  | cons t ts ih =>
      have ht1 : 1 ≤ t := hok t (by simp)
      have hok' : ∀ x ∈ ts, 1 ≤ x := by
        intro x hx
        exact hok x (by simp [hx])
      have ih' := ih hok'
      simp [StringFlow.wordWeight]
      omega

/-- The number of `2` entries in a `{1,2}` word is the weight minus
the length. -/
theorem filter_count_eq_wordWeight_sub_length (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    (w.filter (fun t => t = 2)).length = StringFlow.wordWeight w - w.length := by
  induction w with
  | nil => simp [StringFlow.wordWeight]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      have hok' : ∀ x ∈ ts, x = 1 ∨ x = 2 := by
        intro x hx
        exact hok x (by simp [hx])
      have ih' := ih hok'
      have hge : ts.length ≤ StringFlow.wordWeight ts :=
        wordWeight_ge_length ts (fun x hx => by
          rcases hok x (by simp [hx]) with h1 | h2 <;> omega)
      rcases ht with ht1 | ht2
      · simp [ht1, StringFlow.wordWeight]
        rw [ih']
        omega
      · simp [ht2, StringFlow.wordWeight]
        rw [ih']
        omega

/-- A `{1,2}` word with `U` twos and length `L` has weight `L + U`. -/
theorem wordWeight_of_count (w : List Nat) (L U : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hwlen : w.length = L) :
    StringFlow.wordWeight w = L + U := by
  have hfs := filter_count_eq_wordWeight_sub_length w hok
  rw [hUcount, hwlen] at hfs
  have hge := wordWeight_ge_length w (fun t ht => by
    rcases hok t ht with h1 | h2 <;> omega)
  omega

/-- A nonempty word is its prefix followed by its last entry. -/
theorem word_eq_dropLast_append_last (w : List Nat) (hne : w ≠ []) :
    w = w.dropLast ++ [StringFlow.Word.wordLast w] := by
  induction w with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.Word.wordLast]
      | cons u us =>
          have ih' := ih (by simp)
          simp [List.dropLast, StringFlow.Word.wordLast]
          rw [← ih']

/-- Appending `1` does not change the positions of `2`s. -/
theorem twosPositions_append_one (pre : List Nat) :
    twosPositions (pre ++ [1]) = twosPositions pre := by
  induction pre with
  | nil => simp [twosPositions]
  | cons t ts ih =>
      simp [twosPositions, ih]

/-- The last step value does not affect the prefix numerator. -/
theorem auOf_append_last_irrelevant (pre : List Nat) :
    auOf (pre ++ [1]) = auOf (pre ++ [2]) := by
  unfold auOf
  rw [auOfAux_append_singleton, auOfAux_append_singleton]

/-- The chain numerator of a real `{1,2}` word ending in `2` is
`auOfPos` at the `2` positions of its prefix. -/
theorem wordA_eq_auOfPos_of_twosPositions_dropLast (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) (hlast : StringFlow.Word.wordLast w = 2) :
    StringFlow.Word.wordA w = auOfPos w.length (twosPositions w.dropLast) := by
  have hne : w ≠ [] := by
    intro h
    subst w
    simp [StringFlow.Word.wordLast] at hlast
  have hw : w = w.dropLast ++ [2] := by
    simpa [hlast] using word_eq_dropLast_append_last w hne
  have hok1 : ∀ t ∈ (w.dropLast ++ [1]), t = 1 ∨ t = 2 := by
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · have ht' : t ∈ w := by
        rw [hw]
        simp [List.mem_append, ht]
      exact hok t ht'
    · simp at ht
      subst t
      exact Or.inl rfl
  have hA1 : StringFlow.Word.wordA (w.dropLast ++ [1]) =
      auOfPos (w.dropLast ++ [1]).length (twosPositions (w.dropLast ++ [1])) :=
    wordA_eq_auOfPos_of_twosPositions (w.dropLast ++ [1]) hok1
  have hlen1 : (w.dropLast ++ [1]).length = w.length := by
    rw [hw]
    simp [List.length_append]
  have htwos : twosPositions (w.dropLast ++ [1]) = twosPositions w.dropLast :=
    twosPositions_append_one w.dropLast
  have hlastEq : StringFlow.Word.wordA w =
      StringFlow.Word.wordA (w.dropLast ++ [1]) := by
    rw [← StringFlow.auOf_eq_wordA, ← StringFlow.auOf_eq_wordA]
    have hw' : auOf w = auOf (w.dropLast ++ [2]) := by
      conv =>
        lhs
        rw [hw]
    rw [hw']
    exact (auOf_append_last_irrelevant w.dropLast).symm
  calc
    StringFlow.Word.wordA w = StringFlow.Word.wordA (w.dropLast ++ [1]) := hlastEq
    _ = auOfPos (w.dropLast ++ [1]).length (twosPositions (w.dropLast ++ [1])) := hA1
    _ = auOfPos w.length (twosPositions w.dropLast) := by
        rw [hlen1, htwos]

end StringFlow
