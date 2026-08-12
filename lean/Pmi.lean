import Std

/-!
# PMI and PMI-B: prefix margin identity and ballot bound

This module formalizes the algebraic content of the PMI identity from
`general_analytic_constraints.md` section 17.  The Lean core used here
has no `Real`/`Mathlib`, so the identity is stated after clearing
denominators and exponentials:

    sum_{j=0}^{P-1} 5^(P-j) * 2^(W_j) = 5 * n0 * (2^T - 5^P)

where `W_j` is the prefix weight after `j` steps and
`T = W_P`.  This is exactly the identity obtained from

    sum_j 2^(-M_j) = 5*m*(2^delta - 1)

by substituting `M_j = j*log2 5 - W_j`, `delta = T - P*log2 5`
and multiplying by `5^P`.

PMI-B is formalized as the counting bound for "bad" prefixes
`5^j <= 2^(W_j)` (the algebraic form of `M_j <= 0`).
-/

namespace StringFlow.PMI

/-- Prefix weight after `j` steps: `W_0 = 0`, `W_(j+1) = W_j + t_j`. -/
def prefixWeight (t : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => prefixWeight t j + t j

/-- `A_total = sum_{j=0}^{P-1} 5^(P-1-j) * 2^(W_j)`. -/
def aTotal (P : Nat) (t : Nat → Nat) : Nat :=
  ((List.range P).map (fun j => 5 ^ (P - 1 - j) * 2 ^ prefixWeight t j)).sum

/-- PMI numerator: `sum_{j=0}^{P-1} 5^(P-j) * 2^(W_j)`. -/
def aTotal5 (P : Nat) (t : Nat → Nat) : Nat :=
  ((List.range P).map (fun j => 5 ^ (P - j) * 2 ^ prefixWeight t j)).sum

/-- A prefix is "bad" for PMI-B when `1 <= j < P` and `5^j <= 2^(W_j)`. -/
def isBad (P : Nat) (t : Nat → Nat) (j : Nat) : Bool :=
  decide (1 ≤ j) && decide (j < P) && decide (5 ^ j ≤ 2 ^ prefixWeight t j)

/-- The list of bad prefixes. -/
def badList (P : Nat) (t : Nat → Nat) : List Nat :=
  (List.range P).filter (isBad P t)

/-- The number of bad prefixes. -/
def badCount (P : Nat) (t : Nat → Nat) : Nat :=
  (badList P t).length

theorem mem_badList_iff (P : Nat) (t : Nat → Nat) (j : Nat) :
    j ∈ badList P t ↔ j < P ∧ 1 ≤ j ∧ 5 ^ j ≤ 2 ^ prefixWeight t j := by
  unfold badList
  rw [List.mem_filter, List.mem_range]
  constructor
  · intro h
    rcases h with ⟨hjlt, hbad⟩
    have hb : (1 ≤ j ∧ j < P) ∧ 5 ^ j ≤ 2 ^ prefixWeight t j := by
      simpa [isBad] using hbad
    rcases hb with ⟨hj1lt, hle⟩
    rcases hj1lt with ⟨hj1, hjlt2⟩
    exact ⟨hjlt, hj1, hle⟩
  · intro h
    rcases h with ⟨hjlt, hj1, hle⟩
    exact ⟨hjlt, by simp [isBad, hj1, hjlt, hle]⟩

theorem range_succ_cons (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun j => j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by
          rw [List.range_succ]
        _ = (0 :: (List.range n).map (fun j => j + 1)) ++ [n + 1] := by
          rw [ih]
        _ = 0 :: ((List.range n).map (fun j => j + 1) ++ [n + 1]) := by
          simp
        _ = 0 :: (List.range (n + 1)).map (fun j => j + 1) := by
          rw [List.range_succ, List.map_append]
          simp

theorem sum_map_mul_left (l : List Nat) (c : Nat) (f : Nat → Nat) :
    (l.map (fun j => c * f j)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp [List.sum_cons, Nat.mul_add, ih]

theorem aTotal5_succ (n : Nat) (t : Nat → Nat) :
    aTotal5 (n + 1) t = 5 * aTotal5 n t + 5 * 2 ^ prefixWeight t n := by
  unfold aTotal5
  rw [List.range_succ, List.map_append, List.sum_append]
  have hrange :
      ((List.range n).map (fun j => 5 ^ (n + 1 - j) * 2 ^ prefixWeight t j)).sum
        = 5 * ((List.range n).map
            (fun j => 5 ^ (n - j) * 2 ^ prefixWeight t j)).sum := by
    rw [← sum_map_mul_left (List.range n) 5
        (fun j => 5 ^ (n - j) * 2 ^ prefixWeight t j)]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hjlt : j < n := (List.mem_range.mp hj)
    have hsub : n + 1 - j = (n - j) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    rw [← Nat.mul_assoc 5 (5 ^ (n - j)) (2 ^ prefixWeight t j)]
    rw [Nat.mul_comm (5 ^ (n - j)) 5]
  rw [hrange]
  simp

theorem aTotal_succ (n : Nat) (t : Nat → Nat) :
    aTotal (n + 1) t = 5 * aTotal n t + 2 ^ prefixWeight t n := by
  unfold aTotal
  rw [List.range_succ, List.map_append, List.sum_append]
  have hrange :
      ((List.range n).map (fun j => 5 ^ (n + 1 - 1 - j) * 2 ^ prefixWeight t j)).sum
        = 5 * ((List.range n).map
            (fun j => 5 ^ (n - 1 - j) * 2 ^ prefixWeight t j)).sum := by
    rw [← sum_map_mul_left (List.range n) 5
        (fun j => 5 ^ (n - 1 - j) * 2 ^ prefixWeight t j)]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hjlt : j < n := (List.mem_range.mp hj)
    have hsub : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    rw [← Nat.mul_assoc 5 (5 ^ (n - 1 - j)) (2 ^ prefixWeight t j)]
    rw [Nat.mul_comm (5 ^ (n - 1 - j)) 5]
  rw [hrange]
  simp

theorem aTotal5_eq_five_mul_aTotal (P : Nat) (t : Nat → Nat) :
    aTotal5 P t = 5 * aTotal P t := by
  induction P with
  | zero => simp [aTotal5, aTotal]
  | succ P ih =>
      rw [aTotal5_succ, aTotal_succ, ih]
      simp [Nat.mul_add]

theorem pmi_algebraic (P : Nat) (t : Nat → Nat) (n0 T : Nat)
    (hcycle : 2 ^ T * n0 = 5 ^ P * n0 + aTotal P t) :
    aTotal5 P t = 5 * n0 * (2 ^ T - 5 ^ P) := by
  rw [aTotal5_eq_five_mul_aTotal]
  have hA : aTotal P t = n0 * (2 ^ T - 5 ^ P) := by
    rw [Nat.mul_sub]
    rw [Nat.mul_comm n0 (2 ^ T), Nat.mul_comm n0 (5 ^ P)]
    rw [hcycle]
    omega
  rw [hA]
  rw [Nat.mul_assoc]

theorem sum_ge_of_mem_ge (l : List Nat) (c : Nat) (f : Nat → Nat)
    (hf : ∀ j, j ∈ l → c ≤ f j) :
    c * l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp [List.sum_cons]
      have h1 : c ≤ f a := hf a (by simp)
      have h2 : c * as.length ≤ (as.map f).sum :=
        ih (fun j hj => hf j (by simp [hj]))
      rw [Nat.mul_succ]
      omega

theorem sum_filter_le_sum (l : List Nat) (p : Nat → Bool) (f : Nat → Nat) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a = true
      · rw [List.filter_cons]
        simp [h]
        omega
      · rw [List.filter_cons]
        simp [h]
        omega

theorem bad_term_ge (P : Nat) (t : Nat → Nat) {j : Nat}
    (hj : j < P) (hbad : 5 ^ j ≤ 2 ^ prefixWeight t j) :
    5 ^ P ≤ 5 ^ (P - j) * 2 ^ prefixWeight t j := by
  have hpow : 5 ^ P = 5 ^ (P - j) * 5 ^ j := by
    rw [← Nat.pow_add]
    congr
    omega
  rw [hpow]
  exact Nat.mul_le_mul_left (5 ^ (P - j)) hbad

theorem badCount_eq_filter_length (P : Nat) (t : Nat → Nat) :
    badCount P t =
      ((List.range (P - 1)).filter (fun k => isBad P t (k + 1))).length := by
  unfold badCount badList
  by_cases hP : P = 0
  · subst P
    simp
  · have hsplit : List.range P = 0 :: (List.range (P - 1)).map (fun k => k + 1) := by
      have : P = (P - 1) + 1 := by omega
      rw [this]
      exact range_succ_cons (P - 1)
    rw [hsplit]
    rw [List.filter_cons]
    have h0 : isBad P t 0 = false := by simp [isBad]
    simp [h0]
    rw [List.filter_map]
    rw [List.length_map]
    rfl

theorem aTotal5_ge_bad (P : Nat) (t : Nat → Nat) (hP : 1 ≤ P) :
    5 ^ P + badCount P t * 5 ^ P ≤ aTotal5 P t := by
  have hsplit : List.range P = 0 :: (List.range (P - 1)).map (fun k => k + 1) := by
    have : P = (P - 1) + 1 := by omega
    rw [this]
    exact range_succ_cons (P - 1)
  unfold aTotal5
  rw [hsplit]
  simp [prefixWeight]
  let bl : List Nat := (List.range (P - 1)).filter (fun k => isBad P t (k + 1))
  let g : Nat → Nat := fun k => 5 ^ (P - (k + 1)) * 2 ^ prefixWeight t (k + 1)
  have hbadSum : 5 ^ P * bl.length ≤ (bl.map g).sum := by
    apply sum_ge_of_mem_ge
    intro j hj
    rw [List.mem_filter] at hj
    rcases hj with ⟨hjmem, hjb⟩
    have hjlt : j + 1 < P := by
      rw [List.mem_range] at hjmem
      omega
    have hle : 5 ^ (j + 1) ≤ 2 ^ prefixWeight t (j + 1) := by
      have hb := hjb
      simp [isBad] at hb
      omega
    exact bad_term_ge P t hjlt hle
  have hfull : (bl.map g).sum ≤ ((List.range (P - 1)).map g).sum := by
    unfold bl
    exact sum_filter_le_sum (List.range (P - 1)) (fun k => isBad P t (k + 1)) g
  have hbadSum' : bl.length * 5 ^ P ≤ (bl.map g).sum := by
    simpa [Nat.mul_comm] using hbadSum
  have hbc : badCount P t = bl.length := by
    rw [badCount_eq_filter_length]
  rw [hbc]
  change bl.length * 5 ^ P ≤ ((List.range (P - 1)).map g).sum
  omega

/--
PMI-B counting bound: the number of bad proper prefixes is bounded by
the PMI budget.  Algebraically:

    (badCount + 1) * 5^P <= 5 * n0 * (2^T - 5^P).
-/
theorem pmi_b_count (P : Nat) (t : Nat → Nat) (n0 T : Nat) (hP : 1 ≤ P)
    (hcycle : 2 ^ T * n0 = 5 ^ P * n0 + aTotal P t) :
    5 ^ P + badCount P t * 5 ^ P ≤ 5 * n0 * (2 ^ T - 5 ^ P) := by
  rw [← pmi_algebraic P t n0 T hcycle]
  exact aTotal5_ge_bad P t hP

/-- PMI-B corollary: if the frame-A budget is below `2 * 5^P`, then no
proper prefix is bad; algebraically `2^(W_j) < 5^j` for `1 <= j < P`. -/
theorem pmi_b_no_bad_prefix (P : Nat) (t : Nat → Nat) (n0 T : Nat)
    (hP : 1 ≤ P)
    (hcycle : 2 ^ T * n0 = 5 ^ P * n0 + aTotal P t)
    (hbudget : 5 * n0 * (2 ^ T - 5 ^ P) < 2 * 5 ^ P) :
    ∀ j, 1 ≤ j → j < P → 2 ^ prefixWeight t j < 5 ^ j := by
  intro j hj1 hjP
  by_cases hlt : 2 ^ prefixWeight t j < 5 ^ j
  · exact hlt
  · have hbadge : 5 ^ j ≤ 2 ^ prefixWeight t j := by omega
    have hcount : 5 ^ P + badCount P t * 5 ^ P ≤ 5 * n0 * (2 ^ T - 5 ^ P) :=
      pmi_b_count P t n0 T hP hcycle
    have hbadcount : 1 ≤ badCount P t := by
      unfold badCount
      have hmem : j ∈ badList P t := (mem_badList_iff P t j).mpr
        ⟨hjP, hj1, hbadge⟩
      have hpos : 0 < (badList P t).length := List.length_pos_of_mem hmem
      omega
    have h1 : 5 ^ P ≤ badCount P t * 5 ^ P := by
      have h := Nat.mul_le_mul_right (5 ^ P) hbadcount
      simpa [Nat.mul_comm] using h
    exfalso
    omega

end StringFlow.PMI
