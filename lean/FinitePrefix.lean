import S6AuditStage1

/-!
# Finite prefix of the full accelerated 7-orbit

Explicit expansion of the first 17 states of `S6Audit.fullOrbitIter`,
with step weights, proved by `norm_num`/`simp` only.  No `native_decide`
and no unbounded search is used.
-/

namespace S6Audit

/-- First 17 states of the full accelerated 7-orbit. -/
theorem fullOrbitIter_prefix_expand :
    fullOrbitIter 0 = 7 ∧
    fullOrbitIter 1 = 9 ∧
    fullOrbitIter 2 = 23 ∧
    fullOrbitIter 3 = 29 ∧
    fullOrbitIter 4 = 73 ∧
    fullOrbitIter 5 = 183 ∧
    fullOrbitIter 6 = 229 ∧
    fullOrbitIter 7 = 573 ∧
    fullOrbitIter 8 = 1433 ∧
    fullOrbitIter 9 = 3583 ∧
    fullOrbitIter 10 = 4479 ∧
    fullOrbitIter 11 = 5599 ∧
    fullOrbitIter 12 = 6999 ∧
    fullOrbitIter 13 = 8749 ∧
    fullOrbitIter 14 = 21873 ∧
    fullOrbitIter 15 = 54683 ∧
    fullOrbitIter 16 = 34177 := by
  simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- Depths 17 and 18 of the full accelerated 7-orbit. -/
theorem fullOrbitIter_prefix_expand_18 :
    fullOrbitIter 17 = 85443 ∧
    fullOrbitIter 18 = 26701 := by
  simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- Step weights at depths 16 and 17: the depth-16 step is small, the
depth-17 step is already `t=4`. -/
theorem fullOrbit_prefix_step_weights_17 :
    twoValuation (5 * fullOrbitIter 16 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 17 + 1) = 4 := by
  simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- Step weights of the first 16 steps.  The first 15 steps have
weight `1` or `2`; the step from depth 15 to depth 16 has weight `3`. -/
theorem fullOrbit_prefix_step_weights :
    twoValuation (5 * fullOrbitIter 0 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 1 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 2 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 3 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 4 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 5 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 6 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 7 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 8 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 9 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 10 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 11 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 12 + 1) = 2 ∧
    twoValuation (5 * fullOrbitIter 13 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 14 + 1) = 1 ∧
    twoValuation (5 * fullOrbitIter 15 + 1) = 3 := by
  simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- The first `t ≥ 3` step of the full 7-orbit is the depth-15 step,
and its weight is exactly `3`. -/
theorem fullOrbit_first_t_ge3_is_exactly_3 :
    (∀ n : Nat, n < 15 → twoValuation (5 * fullOrbitIter n + 1) ≤ 2) ∧
    twoValuation (5 * fullOrbitIter 15 + 1) = 3 := by
  constructor
  · intro n hn
    interval_cases n <;>
      simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  · simp [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- If `n` is the first index with `t_n >= 3`, then it is exactly the
depth-15 step and its weight is `3`. -/
theorem first_big_step_unique
    (n : Nat)
    (hsmall : ∀ m : Nat, m < n → twoValuation (5 * fullOrbitIter m + 1) ≤ 2)
    (hbig : 3 ≤ twoValuation (5 * fullOrbitIter n + 1)) :
    n = 15 ∧ twoValuation (5 * fullOrbitIter n + 1) = 3 := by
  have hbase := fullOrbit_first_t_ge3_is_exactly_3
  have hn_le : n ≤ 15 := by
    by_contra hnle
    have h15lt : 15 < n := Nat.lt_of_not_ge hnle
    have h15small := hsmall 15 h15lt
    have h15eq : twoValuation (5 * fullOrbitIter 15 + 1) = 3 := hbase.2
    omega
  have hn_ge : 15 ≤ n := by
    by_contra hnge
    have hnlt : n < 15 := Nat.lt_of_not_ge hnge
    have hnsmall := hbase.1 n hnlt
    omega
  have hn15 : n = 15 := by omega
  constructor
  · exact hn15
  · subst n
    exact hbase.2

/-- A candidate whose first `t >= 3` step has weight `5` or `6`
contradicts the finite base. -/
theorem candidate_first_big_step_weight_ne_three
    (n k : Nat) (hk : k = 5 ∨ k = 6)
    (hsmall : ∀ m : Nat, m < n → twoValuation (5 * fullOrbitIter m + 1) ≤ 2)
    (hbig : twoValuation (5 * fullOrbitIter n + 1) = k) :
    False := by
  have hkge : 3 ≤ twoValuation (5 * fullOrbitIter n + 1) := by
    rcases hk with rfl | rfl <;> omega
  have huniq := first_big_step_unique n hsmall hkge
  rcases huniq with ⟨hn15, hw⟩
  rcases hk with rfl | rfl <;> omega

/-- A candidate whose first `t >= 3` step has weight at least `5`
contradicts the finite base.  Covers the `e=2, a>=1` branch. -/
theorem candidate_first_big_step_weight_ge_five
    (n k : Nat) (hk : 5 ≤ k)
    (hsmall : ∀ m : Nat, m < n → twoValuation (5 * fullOrbitIter m + 1) ≤ 2)
    (hbig : twoValuation (5 * fullOrbitIter n + 1) = k) :
    False := by
  have hkge : 3 ≤ twoValuation (5 * fullOrbitIter n + 1) := by omega
  have huniq := first_big_step_unique n hsmall hkge
  rcases huniq with ⟨hn15, hw⟩
  omega

/-- The `d=3` unique family requires its first `t >= 3` step at depth
`j+4 >= 928`, contradicting the depth-15 base. -/
theorem d3_unique_family_contradicts_base
    (j n : Nat) (hj : 924 ≤ j) (hn : n = j + 4)
    (hsmall : ∀ m : Nat, m < n → twoValuation (5 * fullOrbitIter m + 1) ≤ 2)
    (hbig : twoValuation (5 * fullOrbitIter n + 1) = 6) :
    False := by
  have hkge : 3 ≤ twoValuation (5 * fullOrbitIter n + 1) := by omega
  have huniq := first_big_step_unique n hsmall hkge
  rcases huniq with ⟨hn15, hw⟩
  have hnge : 928 ≤ n := by omega
  omega

/-- `j-1 ≡ 923 (mod 1728)` is encoded as `j % 1728 = 924`; this gives
`924 ≤ j`. -/
theorem j_ge_924_of_mod
    (j : Nat) (hj : j % 1728 = 924) : 924 ≤ j := by
  have hmodle : j % 1728 ≤ j := Nat.mod_le j 1728
  omega

/-- The `d=3` unique family, together with its congruence class
`j-1 ≡ 923 (mod 1728)`, contradicts the depth-15 base. -/
theorem d3_family_mod_contradicts_base
    (j n : Nat) (hjmod : j % 1728 = 924) (hn : n = j + 4)
    (hsmall : ∀ m : Nat, m < n → twoValuation (5 * fullOrbitIter m + 1) ≤ 2)
    (hbig : twoValuation (5 * fullOrbitIter n + 1) = 6) :
    False := by
  exact d3_unique_family_contradicts_base j n (j_ge_924_of_mod j hjmod) hn hsmall hbig

/-- `e=3, j=17`, `t_j=1`, `δ=1`: the candidate `x` fails the corrected
residue `x ≡ 53 (mod 160)` (the actual value is `x ≡ 133 (mod 160)`).
The old modulus `640`/residue `13` belonged to the invalidated
`36.30.6` class and is not used here. -/
theorem e3_j17_t1_corrected_excluded
    (x : Nat) (hx : x = 4 * 34177 + 5 ^ 16)
    (hmod : x % 160 = 53) : False := by
  rw [hx] at hmod
  norm_num at hmod

/-- `e=3, j=17`, `t_j=2`, `δ=3`: the candidate `x` fails the corrected
residue `x ≡ 183 (mod 320)` (the actual value is `x ≡ 263 (mod 320)`).
The old modulus `1280`/residue `743` belonged to the invalidated
`36.30.6` class and is not used here. -/
theorem e3_j17_t2_delta3_corrected_excluded
    (x : Nat) (hx : x = 4 * 34177 + 3 * 5 ^ 16)
    (hmod : x % 320 = 183) : False := by
  rw [hx] at hmod
  norm_num at hmod

/-- Local check that explicit recursive rewriting computes `v2 36`. -/
example : StringFlow.twoValuation 36 = 2 := by
  rw [StringFlow.twoValuation_succ 35]
  norm_num
  rw [StringFlow.twoValuation_succ 17]
  norm_num
  rw [StringFlow.twoValuation_succ 8]
  norm_num

/-- The word of the first 15 full-orbit step weights: `t_0,...,t_14`.
The depth-15 step `t_15=3` is intentionally excluded. -/
def fullOrbitPrefixWord : List Nat :=
  [2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1]

/-- For `n ≤ 15`, the first `n` full-orbit steps form a legal `{1,2}`
word from `7`. -/
theorem fullOrbitPrefix_wordValid (n : Nat) (hn : n ≤ 15) :
    StringFlow.Word.wordValid (fullOrbitPrefixWord.take n) 7 := by
  interval_cases n <;>
    simp [fullOrbitPrefixWord, StringFlow.Word.wordValid]

/-- For `n ≤ 15`, applying the first `n` full-orbit step weights from
`7` reproduces `fullOrbitIter n`. -/
theorem fullOrbitPrefix_wordOrbit (n : Nat) (hn : n ≤ 15) :
    StringFlow.Word.wordOrbit (fullOrbitPrefixWord.take n) 7 = fullOrbitIter n := by
  interval_cases n <;>
    simp [fullOrbitPrefixWord, StringFlow.Word.wordOrbit,
      fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- Bridge: a full-orbit state at depth `n ≤ 15` is also reachable by a
legal `{1,2}` word, i.e. `OrbitFrom7`. -/
theorem fullOrbitPrefix_imp_OrbitFrom7 (n : Nat) (hn : n ≤ 15) :
    OrbitFrom7 (fullOrbitIter n) := by
  refine ⟨fullOrbitPrefixWord.take n, ?_, ?_, ?_⟩
  · interval_cases n <;> simp [fullOrbitPrefixWord]
  · exact fullOrbitPrefix_wordValid n hn
  · exact fullOrbitPrefix_wordOrbit n hn

end S6Audit
