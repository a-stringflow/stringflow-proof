import UnifiedCoreAudit

/-!
# Pure block-local route for the unified core

This module separates the 36.20 block-local proof from the full-orbit
candidate-exclusion route.  The theorems here use only
`All36_20PremisesNoHge`, `OrbitFrom7 r`, `H_s >= 2`, and the standard
capacity/valuation identities.  No `FullOrbitFrom7` is used.
-/

namespace UnifiedCoreAudit

/-- Pure-block version of the 36.30.23.1 mod-5 congruence. -/
theorem block_head_mod_five_congruence_of_premises_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj) :
    r ≡ StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5 [MOD 5] := by
  have hdvd : 2 ^ Wj ∣ Aj + 5 ^ j * q := Nat.dvd_iff_mod_eq_zero.mpr hPrem.r_j_int
  have hmul : 2 ^ Wj * r = Aj + 5 ^ j * q := by
    rw [hrj]
    exact Nat.mul_div_cancel' hdvd
  have h5dvd : 5 ∣ 5 ^ j := by
    refine ⟨5 ^ (j - 1), ?_⟩
    calc
      5 ^ j = 5 ^ ((j - 1) + 1) := by
        congr 1
        exact (Nat.sub_add_cancel hPrem.j_pos).symm
      _ = 5 * 5 ^ (j - 1) := by
        rw [Nat.pow_succ]
        ring
  have h5mod : 5 ^ j ≡ 0 [MOD 5] := by
    rw [Nat.ModEq]
    exact Nat.dvd_iff_mod_eq_zero.mp h5dvd
  have hmodsum : Aj + 5 ^ j * q ≡ Aj [MOD 5] := by
    have h0 : 5 ^ j * q ≡ 0 [MOD 5] := by simpa using h5mod.mul_right q
    have hadd : Aj + 5 ^ j * q ≡ Aj + 0 [MOD 5] := h0.add_left Aj
    simpa using hadd
  have hmodA : 2 ^ Wj * r ≡ Aj [MOD 5] := by
    rw [Nat.ModEq]
    rw [hmul]
    have h := hmodsum
    rwa [Nat.ModEq] at h
  have hword : S6Audit.wordMolecule weight j ≡ 2 ^ Wp [MOD 5] := by
    have hjsub : j = (j - 1) + 1 := (Nat.sub_add_cancel hPrem.j_pos).symm
    rw [hjsub]
    simpa [hPrem.Wp_def] using wordMolecule_mod_five weight (j - 1)
  have hAj : Aj ≡ 2 ^ Wp [MOD 5] := by
    rw [hPrem.Aj_mol]
    exact hword
  have hmodW : 2 ^ Wj * r ≡ 2 ^ Wp [MOD 5] := hmodA.trans hAj
  have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hpow : 2 ^ Wj = 2 ^ Wp * 2 ^ (Wj - Wp) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmodW' : 2 ^ Wp * (2 ^ (Wj - Wp) * r) ≡ 2 ^ Wp * 1 [MOD 5] := by
    have hcalc : 2 ^ Wp * (2 ^ (Wj - Wp) * r) = 2 ^ Wj * r := by
      rw [hpow]
      ring
    rw [hcalc]
    simpa using hmodW
  let invWp := StringFlow.Lte.invMod5 (2 ^ Wp)
  have hinvWp : 2 ^ Wp * invWp ≡ 1 [MOD 5] := by
    rw [Nat.ModEq]
    exact StringFlow.Lte.invMod5_spec (2 ^ Wp) (S6Audit.pow_two_mod_five_ne_zero Wp)
  have hcancel := hmodW'.mul_right invWp
  have hleft : (2 ^ Wp * (2 ^ (Wj - Wp) * r)) * invWp ≡
      2 ^ (Wj - Wp) * r [MOD 5] := by
    have h' := hinvWp.mul_left (2 ^ (Wj - Wp) * r)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
  have hright : (2 ^ Wp * 1) * invWp ≡ 1 [MOD 5] := by
    have htmp : (2 ^ Wp * 1) * invWp = 2 ^ Wp * invWp := by ring
    rw [htmp]
    exact hinvWp
  have hunit : 2 ^ (Wj - Wp) * r ≡ 1 [MOD 5] :=
    hleft.symm.trans (hcancel.trans hright)
  let invT := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp))
  have hinvT : 2 ^ (Wj - Wp) * invT ≡ 1 [MOD 5] := by
    rw [Nat.ModEq]
    exact StringFlow.Lte.invMod5_spec (2 ^ (Wj - Wp))
      (S6Audit.pow_two_mod_five_ne_zero (Wj - Wp))
  have hmulT := hunit.mul_right invT
  have hleftT : (2 ^ (Wj - Wp) * r) * invT ≡ r [MOD 5] := by
    have h' := hinvT.mul_left r
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
  have hrightT : 1 * invT ≡ invT [MOD 5] := by
    rw [Nat.ModEq]
    simp
  have hmain : r ≡ invT [MOD 5] := hleftT.symm.trans (hmulT.trans hrightT)
  simpa [invT] using hmain.trans (Nat.mod_modEq invT 5).symm

/-- Pure-block disjunction form of the mod-5 block-head residue. -/
theorem block_head_mod_five_of_premises_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj) :
    r % 5 = 3 ∨ r % 5 = 4 := by
  have hcong := block_head_mod_five_congruence_of_premises_pure j Wp Wj q Aj A_s s W_s
    r_s L H_s weight r hPrem hrj
  rcases hPrem.tj_mem with h1 | h2
  · left
    have ht : Wj - Wp = 1 := by omega
    have hinv : StringFlow.Lte.invMod5 2 % 5 = 3 := by
      norm_num [StringFlow.Lte.invMod5]
    have hc : r ≡ 3 [MOD 5] := by
      rw [ht] at hcong
      simpa [hinv] using hcong
    rw [Nat.ModEq] at hc
    norm_num at hc
    exact hc
  · right
    have ht : Wj - Wp = 2 := by omega
    have hinv : StringFlow.Lte.invMod5 4 % 5 = 4 := by
      norm_num [StringFlow.Lte.invMod5]
    have hc : r ≡ 4 [MOD 5] := by
      rw [ht] at hcong
      simpa [hinv] using hcong
    rw [Nat.ModEq] at hc
    norm_num at hc
    exact hc

/-- Pure-block version of `rj0_le_of_failure_no_hge`. -/
theorem rj0_le_of_failure_no_hge_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = StringFlow.twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    S6Audit.rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≤ r := by
  have hrmod := block_head_mod_five_congruence_of_premises_pure j Wp Wj q Aj A_s s W_s r_s
    L H_s weight r hPrem hrj
  rcases failure_rj_satisfies_exact_equation j Wp Wj q Aj A_s s W_s r_s L H_s weight r
    hPrem hrj hH hL hfail with ⟨k, heq⟩
  exact rj0_le_of_exact_equation j Wp Wj q Aj A_s s W_s r_s L H_s weight r k
    (by omega) hrmod heq

/-- Pure-block version of `rj0_lt_five_pow_of_failure_no_hge`. -/
theorem rj0_lt_five_pow_of_failure_no_hge_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = StringFlow.twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    S6Audit.rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight < 5 ^ j := by
  have hle := rj0_le_of_failure_no_hge_pure j Wp Wj q Aj A_s s W_s r_s L H_s weight r
    hPrem hrj hH hL hfail
  have hrlt : r < 5 ^ j := by
    simpa [hrj] using hPrem.r_j_lt
  exact lt_of_le_of_lt hle hrlt

/-- Pure-block version of `terminal_bound_of_rj0_lower`. -/
theorem terminal_bound_of_rj0_lower_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = StringFlow.twoValuation (3 * r_s + 1))
    (hrj0 : 5 ^ j ≤ S6Audit.rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    StringFlow.twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  by_contra hnot
  have hpos : 0 < 5 ^ (L + 3) * wTerminal L r_s + 1 := by positivity
  have hlt : H_s - 2 < StringFlow.twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) :=
    not_le.mp hnot
  have hge : H_s - 1 ≤ StringFlow.twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) := by
    omega
  have hdvd : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 ^ (L + 3) * wTerminal L r_s + 1) (H_s - 1) hpos).mp hge
  have hlt0 := rj0_lt_five_pow_of_failure_no_hge_pure j Wp Wj q Aj A_s s W_s r_s L H_s
    weight r hPrem hrj hH hL hdvd
  omega

/-- The pure block-local unified core theorem: it needs `OrbitFrom7 r`,
not `FullOrbitFrom7 r`. -/
theorem unified_core_final_no_hge_pure
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.OrbitFrom7 r)
    (hH : 2 ≤ H_s) :
    StringFlow.twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  have hrj0 : 5 ^ j ≤ S6Audit.rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight :=
    local_lemma_final_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hH hReach
  exact terminal_bound_of_rj0_lower_pure j Wp Wj q Aj A_s s W_s r_s L H_s weight r
    hPrem hrj hH hPrem.L_val hrj0

end UnifiedCoreAudit
