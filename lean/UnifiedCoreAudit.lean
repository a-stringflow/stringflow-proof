import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import S6Audit
import S6AuditStage1
import FinitePrefix
import LteMacro

/-!
# Unified core audit (2026-08-12)

This file formalizes the derivation chain around the unified core

    X_i + 2*D_i <= 2*i + 13

without assuming the `H_ge : 3 <= H_s` premise of `S6Audit.All36_20Premises`.
It is an audit file: every non-final step is proved or explicitly reported
as missing, and exactly one theorem carries `by sorry`, namely the final
valuation inequality of document 36.20.

Status convention:
- "proved" means the theorem compiles without `sorry` or `axiom`;
- "missing premise" means the theorem is true only after adding the named
  definitional link that is not present in the statement as written;
- "open" means the theorem is the single final open core and is marked
  with `by sorry`.
-/

namespace UnifiedCoreAudit

open S6Audit

/-- The `t=2` window form of the unified core (document
`pmi_block_projection.md`, section 3):
`v2(5^(k0+1)*s + delta*5^j) <= 2j+10`. -/
def unified_core_t2 (j k0 delta s : Nat) : Prop :=
  twoValuation (5 ^ (k0 + 1) * s + delta * 5 ^ j) ≤ 2 * j + 10

/-- The local form `X_i + 2*D <= 2*i + 13`; `X_i` is the external
valuation `v2(5*r_i + 3)` of the block state.  The original document
writes `X_i` as an ambient quantity; Lean needs it as an explicit
parameter, so this definition is the parameterized transcription. -/
def unified_core_local (X_i i D : Nat) : Prop :=
  X_i + 2 * D ≤ 2 * i + 13

/-- Document 36.20 premises with `H_ge` removed.  All fields of
`S6Audit.All36_20Premises` except `H_ge` are kept explicit. -/
structure All36_20PremisesNoHge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) : Prop where
  Wp_def : Wp = weight (j - 1)
  Wj_def : Wj = weight j
  Ws_def : W_s = weight s
  tj_mem : Wj = Wp + 1 ∨ Wj = Wp + 2
  Aj_mol : Aj = wordMolecule weight j
  Aj_lt : Aj < 5 ^ j
  q_ge : 2 ^ Wp ≤ q
  q_lt : q < 2 ^ Wj
  q0_def : q = negResidue (A_s * pow5Inv s W_s) (2 ^ W_s)
  r_s_eq : r_s = (A_s + 5 ^ s * q) / 2 ^ W_s
  r_s_int : (A_s + 5 ^ s * q) % 2 ^ W_s = 0
  r_s_lt : r_s < 5 ^ s
  r_s_mod8 : r_s % 8 = 5
  L_val : L + 4 = twoValuation (3 * r_s + 1)
  H_def : H_s = 2 * s + 13 - 2 * (W_s - Wp)
  A_s_mol : A_s = wordMolecule weight s
  A_s_lt : A_s < 5 ^ s
  r_j_int : (Aj + 5 ^ j * q) % 2 ^ Wj = 0
  r_j_lt : (Aj + 5 ^ j * q) / 2 ^ Wj < 5 ^ j
  Wj_le_Ws : Wj ≤ W_s
  j_le_s : j ≤ s
  W0_def : weight 0 = 0
  j_pos : 1 ≤ j
  weight_step : ∀ k : Nat, k < s → weight (k + 1) = weight k + 1 ∨
    weight (k + 1) = weight k + 2
  valid_prefix : ∀ k : Nat, k ≤ s →
    (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0

/-- Explicit block-head state bound `0 <= r < 5^j`; the `0 <=` half is
automatic for `Nat`, and `r_j_lt` in the premises is the strict half. -/
theorem block_head_bound_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    0 ≤ (Aj + 5 ^ j * q) / 2 ^ Wj ∧ (Aj + 5 ^ j * q) / 2 ^ Wj < 5 ^ j := by
  exact ⟨Nat.zero_le _, hPrem.r_j_lt⟩

/-- Adding the `H_ge` premise recovers the original 36.20 structure. -/
theorem premises_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (h : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hge : 3 ≤ H_s) :
    All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight :=
  { Wp_def := h.Wp_def
    Wj_def := h.Wj_def
    Ws_def := h.Ws_def
    tj_mem := h.tj_mem
    Aj_mol := h.Aj_mol
    Aj_lt := h.Aj_lt
    q_ge := h.q_ge
    q_lt := h.q_lt
    q0_def := h.q0_def
    r_s_eq := h.r_s_eq
    r_s_int := h.r_s_int
    r_s_lt := h.r_s_lt
    r_s_mod8 := h.r_s_mod8
    L_val := h.L_val
    H_def := h.H_def
    H_ge := hge
    A_s_mol := h.A_s_mol
    A_s_lt := h.A_s_lt
    r_j_int := h.r_j_int
    r_j_lt := h.r_j_lt
    Wj_le_Ws := h.Wj_le_Ws
    j_le_s := h.j_le_s
    W0_def := h.W0_def
    j_pos := h.j_pos
    weight_step := h.weight_step
    valid_prefix := h.valid_prefix }

/-- Dropping `H_ge` from the original structure. -/
theorem no_hge_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (h : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight :=
  { Wp_def := h.Wp_def
    Wj_def := h.Wj_def
    Ws_def := h.Ws_def
    tj_mem := h.tj_mem
    Aj_mol := h.Aj_mol
    Aj_lt := h.Aj_lt
    q_ge := h.q_ge
    q_lt := h.q_lt
    q0_def := h.q0_def
    r_s_eq := h.r_s_eq
    r_s_int := h.r_s_int
    r_s_lt := h.r_s_lt
    r_s_mod8 := h.r_s_mod8
    L_val := h.L_val
    H_def := h.H_def
    A_s_mol := h.A_s_mol
    A_s_lt := h.A_s_lt
    r_j_int := h.r_j_int
    r_j_lt := h.r_j_lt
    Wj_le_Ws := h.Wj_le_Ws
    j_le_s := h.j_le_s
    W0_def := h.W0_def
    j_pos := h.j_pos
    weight_step := h.weight_step
    valid_prefix := h.valid_prefix }

/-- The block tail `r_s` is in the 25-state orbit, with `H_ge` dropped. -/
theorem r_s_mem_orbit25_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.OrbitFrom7 r) :
    S6Audit.InOrbit25 r_s := by
  have hmem_j : S6Audit.InOrbit25 (S6Audit.blockState weight q j) := by
    have hbsj : S6Audit.blockState weight q j = (Aj + 5 ^ j * q) / 2 ^ Wj := by
      dsimp [S6Audit.blockState]
      rw [← hPrem.Aj_mol, ← hPrem.Wj_def]
    rw [hbsj, ← hrj]
    exact S6Audit.OrbitFrom7_mem_orbit25 r hReach
  have hmem_s := S6Audit.blockState_mem_orbit25 j s weight q hPrem.j_le_s
    hPrem.weight_step hPrem.valid_prefix hmem_j
  have hbss : S6Audit.blockState weight q s = r_s := by
    dsimp [S6Audit.blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def]
    exact hPrem.r_s_eq.symm
  simpa [hbss] using hmem_s

/-- The no-`H_ge` premises force the block tail `r_s = 229`. -/
theorem r_s_eq_229_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.OrbitFrom7 r) :
    r_s = 229 := by
  exact S6Audit.r_s_eq_229_of_orbit25 r_s L
    (r_s_mem_orbit25_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach)
    hPrem.r_s_mod8 hPrem.L_val

/-- The no-`H_ge` premises bound the block length: `s ≤ 9`. -/
theorem s_le_9_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.OrbitFrom7 r)
    (hH : 2 ≤ H_s) :
    s ≤ 9 := by
  have hrs : r_s = 229 :=
    r_s_eq_229_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ s * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ s * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ s * q = 2 ^ W_s * ((A_s + 5 ^ s * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ s * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hqge : 2 ^ Wp ≤ q := hPrem.q_ge
  have hq : 5 ^ s * 2 ^ Wp ≤ 229 * 2 ^ W_s := by
    have hle : 5 ^ s * 2 ^ Wp ≤ A_s + 5 ^ s * q := by
      have h1 : 5 ^ s * 2 ^ Wp ≤ 5 ^ s * q := Nat.mul_le_mul_left (5 ^ s) hqge
      omega
    rw [← h229] at hle
    exact hle
  have hWp_le_Wj : Wp ≤ Wj := by
    rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hWj_le_Ws : Wj ≤ W_s := hPrem.Wj_le_Ws
  have hWp_le_Ws : Wp ≤ W_s := le_trans hWp_le_Wj hWj_le_Ws
  have hWs : W_s = Wp + (W_s - Wp) := by omega
  have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
    conv_lhs => rw [hWs]
    rw [Nat.pow_add]
  have hq' : 5 ^ s * 2 ^ Wp ≤ 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) := by
    rwa [hpowWs] at hq
  have hcancel : 5 ^ s ≤ 229 * 2 ^ (W_s - Wp) := by
    have hle : 5 ^ s * 2 ^ Wp ≤ (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq'
    exact Nat.le_of_mul_le_mul_right hle (Nat.pow_pos (by decide : 0 < 2))
  have hD : W_s - Wp = (W_s - Wj) + (Wj - Wp) := by omega
  have h5le : 5 ^ s ≤ 229 * 2 ^ ((W_s - Wj) + (Wj - Wp)) := by
    rw [← hD]
    exact hcancel
  let X := (W_s - Wj) + (Wj - Wp)
  have h229le : 229 * 2 ^ X ≤ 2 ^ (X + 8) := by
    have h229 : 229 ≤ 2 ^ 8 := by norm_num
    have hmul : 229 * 2 ^ X ≤ 2 ^ 8 * 2 ^ X := Nat.mul_le_mul_right (2 ^ X) h229
    have hpow : 2 ^ 8 * 2 ^ X = 2 ^ (X + 8) := by
      rw [Nat.add_comm, ← Nat.pow_add]
    rwa [hpow] at hmul
  have h5le2 : 5 ^ s ≤ 2 ^ (X + 8) := le_trans h5le h229le
  have hHs : H_s = 2 * s + 13 - 2 * (W_s - Wp) := hPrem.H_def
  have h2le : 2 * (W_s - Wp) ≤ 2 * s + 10 := by
    have hBle : 2 * (W_s - Wp) ≤ 2 * s + 13 := by
      by_contra h
      have hgt : 2 * s + 13 < 2 * (W_s - Wp) := by omega
      have hsub0 : 2 * s + 13 - 2 * (W_s - Wp) = 0 :=
        Nat.sub_eq_zero_of_le (by omega)
      have hge : 2 ≤ H_s := hH
      rw [hHs, hsub0] at hge
      norm_num at hge
    have hsum : H_s + 2 * (W_s - Wp) = 2 * s + 13 := by
      rw [hHs]
      exact Nat.sub_add_cancel hBle
    have hge3 : 3 ≤ H_s := by
      by_contra hnot
      have hle2 : H_s ≤ 2 := by omega
      have hHseq : H_s = 2 := by omega
      have hmod : (2 * s + 13) % 2 = (H_s + 2 * (W_s - Wp)) % 2 := by
        rw [hsum]
      have hleft : (2 * s + 13) % 2 = 1 := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
        norm_num
      have hright : (H_s + 2 * (W_s - Wp)) % 2 = H_s % 2 := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
        simp
      rw [hright, hHseq] at hmod
      norm_num at hmod
    omega
  have h2le' : W_s - Wp ≤ s + 5 := by
    have hle' : 2 * (W_s - Wp) ≤ 2 * (s + 5) := by nlinarith [h2le]
    exact Nat.le_of_mul_le_mul_left hle' (by norm_num : 0 < 2)
  have hXle : X ≤ s + 5 := by
    dsimp [X]
    rw [← hD]
    exact h2le'
  have hpowle : 2 ^ (X + 8) ≤ 2 ^ (s + 13) := by
    have hle : X + 8 ≤ s + 13 := by omega
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have h5le3 : 5 ^ s ≤ 2 ^ (s + 13) := le_trans h5le2 hpowle
  by_contra h
  have hs : 10 ≤ s := by omega
  have hgt := S6Audit.five_pow_gt_two_pow_add s hs
  omega

/-- Correctness of the Hensel inverse `5^s * pow5Inv s m ≡ 1 (mod 2^m)`. -/
theorem pow5Inv_correct (s m : Nat) (hm : 1 ≤ m) :
    5 ^ s * pow5Inv s m ≡ 1 [MOD 2 ^ m] := by
  unfold pow5Inv
  have hodd : (5 ^ s) % 2 = 1 := StringFlow.Lte.five_pow_odd s
  have hspec := invOdd_mod_pow_spec (5 ^ s) m hodd hm
  have hmod1 : 1 % 2 ^ m = 1 := by
    exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : m ≠ 0))
  rw [Nat.ModEq]
  simpa [hmod1] using hspec

/-- `negResidue a m = 0` iff `m ∣ a`. -/
theorem negResidue_eq_zero_iff_dvd (a m : Nat) (hm : 0 < m) :
    negResidue a m = 0 ↔ m ∣ a := by
  unfold negResidue
  rw [Nat.dvd_iff_mod_eq_zero]
  have hr : a % m < m := Nat.mod_lt a hm
  constructor
  · intro h
    have h' : (m - a % m) % m = 0 := h
    by_contra hne
    have hr0 : 0 < a % m := Nat.pos_of_ne_zero hne
    have hsub : m - a % m < m := Nat.sub_lt (by omega) hr0
    have hmod : (m - a % m) % m = m - a % m := Nat.mod_eq_of_lt hsub
    rw [hmod] at h'
    omega
  · intro hdvd
    rw [hdvd]
    simp

/-- Divisibility by `m` is invariant under congruence modulo `m`. -/
theorem dvd_modEq_iff (m x y : Nat) (h : x ≡ y [MOD m]) : m ∣ x ↔ m ∣ y := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  rw [Nat.ModEq] at h
  rw [h]

/-- Multiplication by a unit preserves divisibility by `m`. -/
theorem dvd_mul_unit_iff (m u i b : Nat) (hunit : i * b ≡ 1 [MOD m]) :
    m ∣ u * i ↔ m ∣ u := by
  constructor
  · intro hd
    have hd' : m ∣ (u * i) * b := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using (dvd_mul_of_dvd_right hd b)
    have h3 : u * (i * b) ≡ u [MOD m] := by
      simpa using hunit.mul_left u
    have hcong : (u * i) * b ≡ u [MOD m] := by
      calc
        (u * i) * b = u * (i * b) := by ring
        _ ≡ u [MOD m] := h3
    exact (dvd_modEq_iff m ((u * i) * b) u hcong).mp hd'
  · intro hd
    simpa [Nat.mul_comm] using (dvd_mul_of_dvd_right hd i)

/-- The `q0` residue is the unique representative below `2^W_s` of the
block-tail integrality congruence `A_s + 5^s*q ≡ 0 (mod 2^W_s)`. -/
theorem q0_unique_of_congruence
    (A_s s W_s q : Nat) (hWs : 1 ≤ W_s) (hq : q < 2 ^ W_s)
    (hint : (A_s + 5 ^ s * q) % 2 ^ W_s = 0) :
    q = negResidue (A_s * pow5Inv s W_s) (2 ^ W_s) := by
  let m := 2 ^ W_s
  let inv := pow5Inv s W_s
  let N := negResidue (A_s * inv) m
  have hm : 0 < m := by dsimp [m]; positivity
  have hinv : 5 ^ s * inv ≡ 1 [MOD m] := by
    dsimp [inv, m]
    exact pow5Inv_correct s W_s hWs
  have hzero : A_s + 5 ^ s * q ≡ 0 [MOD m] := by
    rw [Nat.ModEq]
    simpa [m] using hint
  have hmul : (A_s + 5 ^ s * q) * inv ≡ 0 [MOD m] := by
    simpa using hzero.mul_right inv
  have hqinv : q * (5 ^ s * inv) ≡ q [MOD m] := by
    have h := hinv.mul_left q
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hdist : (A_s + 5 ^ s * q) * inv ≡ A_s * inv + q [MOD m] := by
    have hcalc : (A_s + 5 ^ s * q) * inv = A_s * inv + q * (5 ^ s * inv) := by
      dsimp [inv]
      ring
    rw [hcalc]
    exact hqinv.add_left (A_s * inv)
  have hsum : A_s * inv + q ≡ 0 [MOD m] := hdist.symm.trans hmul
  have hqmod : q + A_s * inv ≡ 0 [MOD m] := by
    simpa [Nat.add_comm] using hsum
  have hN : N + A_s * inv ≡ 0 [MOD m] := by
    have hspec : (N + (A_s * inv) % m) % m = 0 := by
      dsimp [N]
      exact negResidue_spec (A_s * inv) m hm
    have hmod : (A_s * inv) % m ≡ A_s * inv [MOD m] :=
      Nat.mod_modEq (A_s * inv) m
    have hNmod : N + (A_s * inv) % m ≡ N + A_s * inv [MOD m] :=
      hmod.add_left N
    have hN0 : N + (A_s * inv) % m ≡ 0 [MOD m] := by
      rw [Nat.ModEq]
      exact hspec
    exact hNmod.symm.trans hN0
  have hqeq : q ≡ N [MOD m] :=
    Nat.ModEq.add_right_cancel' (A_s * inv) (hqmod.trans hN.symm)
  have hNlt : N < m := by
    dsimp [N, negResidue]
    exact Nat.mod_lt _ hm
  have hqlt : q < m := by simpa [m] using hq
  exact Nat.ModEq.eq_of_lt_of_lt hqeq hqlt hNlt

/-- Document lemma 7.1 (block-head scope): the `q0` interval
`[2^Wp, 2^Wj)` is equivalent to the block-head size bound
`5^j <= 2^t * r_j` and `r_j < 5^j`, where `t = Wj - Wp`. -/
theorem q0_interval_iff_rj_bound
    (j Wp Wj q Aj r_j t : Nat)
    (ht : Wj = Wp + t)
    (hAj : Aj < 5 ^ j)
    (hint : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hrj : r_j = (Aj + 5 ^ j * q) / 2 ^ Wj) :
    (2 ^ Wp ≤ q ∧ q < 2 ^ Wj) ↔ (5 ^ j ≤ 2 ^ t * r_j ∧ r_j < 5 ^ j) := by
  have hpow : 2 ^ Wj = 2 ^ Wp * 2 ^ t := by
    rw [ht, Nat.pow_add]
  have hpos5 : 0 < 5 ^ j := by positivity
  have hpos2j : 0 < 2 ^ Wj := by positivity
  have hpos2p : 0 < 2 ^ Wp := by positivity
  have hdvd : 2 ^ Wj ∣ Aj + 5 ^ j * q := Nat.dvd_iff_mod_eq_zero.mpr hint
  have heq : 2 ^ Wj * r_j = Aj + 5 ^ j * q := by
    have hmul : 2 ^ Wj * ((Aj + 5 ^ j * q) / 2 ^ Wj) = Aj + 5 ^ j * q :=
      Nat.mul_div_cancel' hdvd
    rw [← hrj] at hmul
    exact hmul
  constructor
  · intro h
    rcases h with ⟨hqge, hqlt⟩
    constructor
    · have hge : 5 ^ j * 2 ^ Wp ≤ 2 ^ Wj * r_j := by
        nlinarith [heq, hqge]
      have hge' : 5 ^ j * 2 ^ Wp ≤ (2 ^ t * r_j) * 2 ^ Wp := by
        nlinarith [hge, hpow]
      exact Nat.le_of_mul_le_mul_right hge' hpos2p
    · by_contra hnot
      have hrge : 5 ^ j ≤ r_j := by omega
      have hgt : 5 ^ j * 2 ^ Wj ≤ 2 ^ Wj * r_j := by
        nlinarith [hrge, hpos2j]
      have hlt : Aj + 5 ^ j * q < 5 ^ j * 2 ^ Wj := by
        nlinarith [hqlt, hAj, hpos5]
      nlinarith [heq, hgt, hlt]
  · intro h
    rcases h with ⟨hrge, hrlt⟩
    constructor
    · by_contra hnot
      have hqlt2 : q < 2 ^ Wp := by omega
      have hlt : 5 ^ j * q < 5 ^ j * 2 ^ Wp := by
        nlinarith [hqlt2, hpos5]
      have hge : 5 ^ j * 2 ^ Wp ≤ 2 ^ Wj * r_j := by
        have hmul : 5 ^ j * 2 ^ Wp ≤ (2 ^ t * r_j) * 2 ^ Wp := by
          nlinarith [hrge, hpos2p]
        nlinarith [hmul, hpow]
      have hgt : 2 ^ Wj * r_j < 5 ^ j * 2 ^ Wp + 5 ^ j := by
        nlinarith [heq, hlt, hAj]
      nlinarith [hge, hgt]
    · by_contra hnot
      have hqge : 2 ^ Wj ≤ q := by omega
      have hlt : 2 ^ Wj * r_j < 5 ^ j * 2 ^ Wj := by
        nlinarith [hrlt, hpos2j]
      have hge : 5 ^ j * 2 ^ Wj ≤ 2 ^ Wj * r_j := by
        nlinarith [heq, hqge, hAj]
      nlinarith [hlt, hge]

/-- Integer dyadic bounds for the block tail forced by the `q0`
interval: `5^s*2^Wp ≤ 2^W_s*r_s < 5^s*(2^Wj+1)`. -/
theorem r_s_dyadic_bounds_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    5 ^ s * 2 ^ Wp ≤ 2 ^ W_s * r_s ∧
      2 ^ W_s * r_s < 5 ^ s * (2 ^ Wj + 1) := by
  have hdvd : 2 ^ W_s ∣ A_s + 5 ^ s * q :=
    Nat.dvd_iff_mod_eq_zero.mpr hPrem.r_s_int
  have heq : 2 ^ W_s * r_s = A_s + 5 ^ s * q := by
    have hmul : 2 ^ W_s * ((A_s + 5 ^ s * q) / 2 ^ W_s) = A_s + 5 ^ s * q :=
      Nat.mul_div_cancel' hdvd
    rw [← hPrem.r_s_eq] at hmul
    exact hmul
  constructor
  · have hqge' : 5 ^ s * 2 ^ Wp ≤ 5 ^ s * q :=
      Nat.mul_le_mul_left (5 ^ s) hPrem.q_ge
    have hle : 5 ^ s * 2 ^ Wp ≤ A_s + 5 ^ s * q := by
      nlinarith [hqge']
    nlinarith [heq, hle]
  · have h1 : 5 ^ s * q < 5 ^ s * 2 ^ Wj :=
      (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < 5))).2 hPrem.q_lt
    have hlt : A_s + 5 ^ s * q < 5 ^ s * (2 ^ Wj + 1) := by
      nlinarith [h1, hPrem.A_s_lt]
    nlinarith [heq, hlt]

/-- The CRT representative of `S6Audit.crtRep` is below `n*m`. -/
theorem crtRep_lt (a b n m : Nat) (h : a ≡ b [MOD Nat.gcd n m])
    (hn : n ≠ 0) (hm : m ≠ 0) :
    crtRep a b n m h < n * m := by
  have hlt := Nat.chineseRemainder'_lt_lcm (n := n) (m := m) h hn hm
  have hle : Nat.lcm n m ≤ n * m :=
    Nat.lcm_le_mul (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm)
  exact lt_of_lt_of_le hlt hle

/-- CRT uniqueness: below `n*m`, the two residue classes have exactly one
representative, so any such `r` equals `crtRep`. -/
theorem crtRep_unique (a b n m r : Nat) (hcop : Nat.Coprime n m)
    (h : a ≡ b [MOD Nat.gcd n m])
    (hr1 : r ≡ a [MOD n]) (hr2 : r ≡ b [MOD m])
    (hrlt : r < n * m) :
    r = crtRep a b n m h := by
  have hc1 : crtRep a b n m h ≡ a [MOD n] := crtRep_left a b n m h
  have hc2 : crtRep a b n m h ≡ b [MOD m] := crtRep_right a b n m h
  have hmod_lcm : r ≡ crtRep a b n m h [MOD Nat.lcm n m] :=
    Nat.mod_lcm (hr1.trans hc1.symm) (hr2.trans hc2.symm)
  have hlcm : Nat.lcm n m = n * m := hcop.lcm_eq_mul
  have hmod : r ≡ crtRep a b n m h [MOD n * m] := by
    simpa [hlcm] using hmod_lcm
  have hn : n ≠ 0 := by
    intro h0
    have : r < 0 := by simp [h0] at hrlt ⊢
    omega
  have hm : m ≠ 0 := by
    intro h0
    have : r < 0 := by simp [h0] at hrlt ⊢
    omega
  have hcrlt : crtRep a b n m h < n * m := crtRep_lt a b n m h hn hm
  exact Nat.ModEq.eq_of_lt_of_lt hmod hrlt hcrlt

/-- Instantiation for the `rj0` CRT: modulo `2^K` and `5` the candidate
below `2^K * 5` is unique. -/
theorem rj0_crt_candidate_unique (K res2 res5 r : Nat)
    (hr1 : r ≡ res2 [MOD 2 ^ K]) (hr2 : r ≡ res5 [MOD 5])
    (hrlt : r < 2 ^ K * 5) :
    r = crtRep res2 res5 (2 ^ K) 5 (crt_coprime_2_5 K res2 res5) := by
  exact crtRep_unique res2 res5 (2 ^ K) 5 r
    (Nat.Coprime.pow_left K (by decide : Nat.Coprime 2 5))
    (crt_coprime_2_5 K res2 res5) hr1 hr2 hrlt

/-- `wordA` appending a step multiplies the old word by `5` and adds
the old total weight power. -/
lemma wordA_append_singleton (w : List Nat) (t : Nat) :
    StringFlow.Word.wordA (w ++ [t]) =
      5 * StringFlow.Word.wordA w + 2 ^ StringFlow.wordWeight w := by
  induction w with
  | nil => simp [StringFlow.Word.wordA, StringFlow.wordWeight]
  | cons a as ih =>
      simp [StringFlow.Word.wordA, StringFlow.wordWeight, ih]
      rw [Nat.pow_add]
      ring

/-- `wordWeight` is additive along appending a singleton step. -/
lemma wordWeight_append_singleton (w : List Nat) (t : Nat) :
    StringFlow.wordWeight (w ++ [t]) = StringFlow.wordWeight w + t := by
  induction w with
  | nil => simp [StringFlow.wordWeight]
  | cons a as ih =>
      simp [StringFlow.wordWeight, ih]
      omega

/-- The total weight of a block suffix telescopes to the weight
difference from `j` to `j+n`. -/
lemma blockWord_wordWeight (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    StringFlow.wordWeight (blockWord weight j n) = weight (j + n) - weight j := by
  induction n with
  | zero => simp [blockWord, StringFlow.wordWeight]
  | succ n ih =>
      rw [blockWord]
      rw [wordWeight_append_singleton]
      have hstep_small : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hmono : weight j ≤ weight (j + n) :=
        weight_mono_le weight j n (fun k hk => by
          rcases hstep_small k hk with h1 | h2 <;> omega)
      rw [ih hstep_small]
      have h : j + n + 1 = j + (n + 1) := by omega
      rw [h]
      rcases hstep (j + n) (by omega) with h1 | h2
      · have h1' : weight (j + (n + 1)) = weight (j + n) + 1 := by
          rw [← h]
          exact h1
        rw [h1']
        omega
      · have h2' : weight (j + (n + 1)) = weight (j + n) + 2 := by
          rw [← h]
          exact h2
        rw [h2']
        omega

/-- The block suffix molecule equals the `blockB` tail. -/
lemma blockWord_wordA (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    StringFlow.Word.wordA (blockWord weight j n) = blockB weight j n := by
  induction n with
  | zero => simp [blockWord, StringFlow.Word.wordA, blockB]
  | succ n ih =>
      rw [blockWord]
      rw [wordA_append_singleton]
      have hstep_small : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      rw [ih hstep_small, blockWord_wordWeight weight j n hstep_small]
      rw [blockB]
      ring

/-- The exact block-tail relation:
`2^(W_s-W_j)*r_s = 5^(s-j)*r_j + B`, where `B` is the block suffix
molecule. -/
lemma block_tail_equation
    (weight : Nat → Nat) (q j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2)
    (hvalid : ∀ k, k ≤ j + n → (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0) :
    2 ^ (weight (j + n) - weight j) * blockState weight q (j + n) =
      5 ^ n * blockState weight q j + blockB weight j n := by
  have hbw := blockWord_valid weight q j n hstep hvalid
  have hid := StringFlow.Word.word_orbit_identity (blockWord weight j n)
    (blockState weight q j) hbw.1
  rw [hbw.2] at hid
  rw [blockWord_wordA weight j n hstep] at hid
  rw [blockWord_wordWeight weight j n hstep] at hid
  rw [blockWord_length] at hid
  exact hid

/-- Block-tail relation in the no-`H_ge` premises:
`2^(W_s-W_j)*r_s = 5^(s-j)*r + B`. -/
lemma block_tail_equation_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj) :
    2 ^ (W_s - Wj) * r_s = 5 ^ (s - j) * r + blockB weight j (s - j) := by
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hks : k < s := by
      have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
      omega
    exact hPrem.weight_step k hks
  have hvalid : ∀ k, k ≤ j + (s - j) →
      (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
    intro k hk
    have hks : k ≤ s := by
      have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
      omega
    exact hPrem.valid_prefix k hks
  have hb := block_tail_equation weight q j (s - j) hstep hvalid
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  rw [hsum] at hb
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, hrj]
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def]
    exact hPrem.r_s_eq.symm
  rw [hbsj, hbss] at hb
  rw [← hPrem.Wj_def, ← hPrem.Ws_def] at hb
  exact hb

/-- A run of consecutive `t=1` block steps advances `blockState` by the
`t=1` step equation, with the integrality witness. -/
lemma block_trailing_ones_step (weight : Nat → Nat) (q k m : Nat)
    (hsteps : ∀ i < m, weight (k + i + 1) = weight (k + i) + 1)
    (hvalid : ∀ i ≤ m,
      (wordMolecule weight (k + i) + 5 ^ (k + i) * q) % 2 ^ weight (k + i) = 0) :
    ∀ i < m, blockState weight q (k + i + 1) = (5 * blockState weight q (k + i) + 1) / 2 ∧
      (5 * blockState weight q (k + i) + 1) % 2 = 0 := by
  intro i hi
  have hstep := blockState_step weight q (k + i) 1 (hsteps i hi)
    (hvalid i (by omega)) (hvalid (i + 1) (by omega))
  have hstep' : (5 * blockState weight q (k + i) + 1) % 2 = 0 ∧
      (5 * blockState weight q (k + i) + 1) / 2 = blockState weight q (k + i + 1) := by
    simpa using hstep
  exact ⟨hstep'.2.symm, hstep'.1⟩

/-- A run of consecutive `t=2` block steps advances `blockState` by the
`t=2` step equation, with the integrality witness. -/
lemma block_trailing_twos_step (weight : Nat → Nat) (q k m : Nat)
    (hsteps : ∀ i < m, weight (k + i + 1) = weight (k + i) + 2)
    (hvalid : ∀ i ≤ m,
      (wordMolecule weight (k + i) + 5 ^ (k + i) * q) % 2 ^ weight (k + i) = 0) :
    ∀ i < m, blockState weight q (k + i + 1) = (5 * blockState weight q (k + i) + 1) / 4 ∧
      (5 * blockState weight q (k + i) + 1) % 4 = 0 := by
  intro i hi
  have hstep := blockState_step weight q (k + i) 2 (hsteps i hi)
    (hvalid i (by omega)) (hvalid (i + 1) (by omega))
  have hstep' : (5 * blockState weight q (k + i) + 1) % 4 = 0 ∧
      (5 * blockState weight q (k + i) + 1) / 4 = blockState weight q (k + i + 1) := by
    simpa using hstep
  exact ⟨hstep'.2.symm, hstep'.1⟩

/-- Length of the leading run of `1`s in a word (used after reversal for
the trailing `t=1` run). -/
def leadingOnes : List Nat → Nat
  | 1 :: t => leadingOnes t + 1
  | _ => 0

/-- Length of the leading run of `2`s in a word. -/
def leadingTwos : List Nat → Nat
  | 2 :: t => leadingTwos t + 1
  | _ => 0

/-- Split a word into `(m1, m2)`: `m1` trailing `1`s and `m2` preceding
`2`s (computed on the reversed word). -/
def tailSplit (w : List Nat) : Nat × Nat :=
  let rw := w.reverse
  let m1 := leadingOnes rw
  (m1, leadingTwos (rw.drop m1))

lemma leadingOnes_replicate (n : Nat) : leadingOnes (List.replicate n 1) = n := by
  induction n with
  | zero => simp [leadingOnes]
  | succ n ih => simp [leadingOnes, List.replicate, ih]

lemma leadingTwos_replicate (n : Nat) : leadingTwos (List.replicate n 2) = n := by
  induction n with
  | zero => simp [leadingTwos]
  | succ n ih => simp [leadingTwos, List.replicate, ih]

lemma leadingOnes_le_length (w : List Nat) : leadingOnes w ≤ w.length := by
  cases w with
  | nil => simp [leadingOnes]
  | cons a t =>
      by_cases ha : a = 1
      · subst a
        simp [leadingOnes]
        exact leadingOnes_le_length t
      · simp [leadingOnes, ha]

lemma leadingTwos_le_length (w : List Nat) : leadingTwos w ≤ w.length := by
  cases w with
  | nil => simp [leadingTwos]
  | cons a t =>
      by_cases ha : a = 2
      · subst a
        simp [leadingTwos]
        exact leadingTwos_le_length t
      · simp [leadingTwos, ha]

lemma tailSplit_sum_le_length (w : List Nat) :
    (tailSplit w).1 + (tailSplit w).2 ≤ w.length := by
  unfold tailSplit
  let rw := w.reverse
  let m1 := leadingOnes rw
  have hm1 : m1 ≤ rw.length := by
    dsimp [m1]
    exact leadingOnes_le_length rw
  have hdrop : (rw.drop m1).length = rw.length - m1 := by simp
  have hm2 : leadingTwos (rw.drop m1) ≤ (rw.drop m1).length :=
    leadingTwos_le_length (rw.drop m1)
  have hle : leadingOnes rw + leadingTwos (rw.drop m1) ≤ rw.length := by
    rw [hdrop] at hm2
    omega
  have hrev : rw.length = w.length := by
    dsimp [rw]
    simp
  have hle' : leadingOnes rw + leadingTwos (rw.drop m1) ≤ w.length := by
    rw [hrev] at hle
    exact hle
  dsimp [tailSplit, rw, m1]
  exact hle'

lemma leadingOnes_spec (w : List Nat) :
    (∀ i, i < leadingOnes w → w.getD i 0 = 1) ∧
    (∀ i, i = leadingOnes w → i < w.length → w.getD i 0 ≠ 1) := by
  induction w with
  | nil => simp [leadingOnes]
  | cons a t ih =>
      by_cases ha : a = 1
      · subst a
        have hred : leadingOnes (1 :: t) = leadingOnes t + 1 := by rfl
        constructor
        · intro i hi
          rw [hred] at hi
          cases i with
          | zero => simp [List.getD]
          | succ i =>
              have hi' : i < leadingOnes t := by omega
              have h := ih.1 i hi'
              simpa [List.getD] using h
        · intro i hi hlen
          rw [hred] at hi
          cases i with
          | zero => omega
          | succ i =>
              have hi' : i = leadingOnes t := by omega
              have hlen' : i < t.length := by
                simp at hlen
                omega
              have h := ih.2 i hi' hlen'
              simpa [List.getD] using h
      · constructor
        · intro i hi
          have hred : leadingOnes (a :: t) = 0 := by simp [leadingOnes, ha]
          rw [hred] at hi
          omega
        · intro i hi hlen
          have hred : leadingOnes (a :: t) = 0 := by simp [leadingOnes, ha]
          rw [hred] at hi
          cases i with
          | zero => simpa [List.getD] using ha
          | succ i => omega

lemma leadingTwos_spec (w : List Nat) :
    (∀ i, i < leadingTwos w → w.getD i 0 = 2) ∧
    (∀ i, i = leadingTwos w → i < w.length → w.getD i 0 ≠ 2) := by
  induction w with
  | nil => simp [leadingTwos]
  | cons a t ih =>
      by_cases ha : a = 2
      · subst a
        have hred : leadingTwos (2 :: t) = leadingTwos t + 1 := by rfl
        constructor
        · intro i hi
          rw [hred] at hi
          cases i with
          | zero => simp [List.getD]
          | succ i =>
              have hi' : i < leadingTwos t := by omega
              have h := ih.1 i hi'
              simpa [List.getD] using h
        · intro i hi hlen
          rw [hred] at hi
          cases i with
          | zero => omega
          | succ i =>
              have hi' : i = leadingTwos t := by omega
              have hlen' : i < t.length := by
                simp at hlen
                omega
              have h := ih.2 i hi' hlen'
              simpa [List.getD] using h
      · constructor
        · intro i hi
          have hred : leadingTwos (a :: t) = 0 := by simp [leadingTwos, ha]
          rw [hred] at hi
          omega
        · intro i hi hlen
          have hred : leadingTwos (a :: t) = 0 := by simp [leadingTwos, ha]
          rw [hred] at hi
          cases i with
          | zero => simpa [List.getD] using ha
          | succ i => omega

lemma tailSplit_spec (w : List Nat) :
    let rw := w.reverse
    let m1 := leadingOnes rw
    let m2 := leadingTwos (rw.drop m1)
    (∀ i, i < m1 → rw.getD i 0 = 1) ∧
    (∀ i, i < m2 → (rw.drop m1).getD i 0 = 2) := by
  dsimp
  constructor
  · intro i hi
    exact (leadingOnes_spec w.reverse).1 i hi
  · intro i hi
    exact (leadingTwos_spec (w.reverse.drop (leadingOnes w.reverse))).1 i hi

lemma getD_append_left (l₁ l₂ : List Nat) (n d : Nat) (hn : n < l₁.length) :
    (l₁ ++ l₂).getD n d = l₁.getD n d := by
  induction l₁ generalizing n with
  | nil =>
      simp at hn
  | cons a t ih =>
      cases n with
      | zero => simp [List.getD]
      | succ n =>
          have hn' : n < t.length := by
            simp at hn
            omega
          have h := ih n hn'
          simpa [List.getD] using h

lemma getD_append_last (l : List Nat) (x d : Nat) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => simp [List.getD]
  | cons a t ih => simp [List.getD]

lemma blockWord_getD (weight : Nat → Nat) (j n i : Nat) (hi : i < n) :
    (blockWord weight j n).getD i 0 = weight (j + i + 1) - weight (j + i) := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hdef : blockWord weight j (n + 1) =
          blockWord weight j n ++ [weight (j + n + 1) - weight (j + n)] := rfl
      rw [hdef]
      by_cases hin : i < n
      · have h := ih hin
        have hlen : i < (blockWord weight j n).length := by
          rw [blockWord_length]
          exact hin
        rw [getD_append_left (blockWord weight j n)
          [weight (j + n + 1) - weight (j + n)] i 0 hlen]
        exact h
      · have hin' : i = n := by omega
        subst i
        have hlen : n = (blockWord weight j n).length :=
          (blockWord_length weight j n).symm
        conv_lhs =>
          arg 2
          rw [hlen]
        rw [getD_append_last (blockWord weight j n)
          (weight (j + n + 1) - weight (j + n)) 0]

lemma getD_drop_add (l : List Nat) (i n d : Nat) :
    (l.drop n).getD i d = l.getD (n + i) d := by
  rw [List.getD, List.getD]
  rw [List.getElem?_drop]

lemma getD_reverse (w : List Nat) (i d : Nat) (hi : i < w.length) :
    w.reverse.getD i d = w.getD (w.length - 1 - i) d := by
  rw [List.getD, List.getD]
  rw [List.getElem?_reverse hi]

lemma blockWord_tailSplit_twos_weight
    (weight : Nat → Nat) (j n m1 m2 : Nat)
    (hw : ∀ k < n, weight (j + k + 1) = weight (j + k) + 1 ∨
                   weight (j + k + 1) = weight (j + k) + 2)
    (hm : (m1, m2) = tailSplit (blockWord weight j n)) :
    ∀ k < m2,
      weight (j + (n - m1 - m2) + k + 1) =
        weight (j + (n - m1 - m2) + k) + 2 := by
  intro k hk
  let w := blockWord weight j n
  have hm1 : m1 = (tailSplit w).1 := by
    simpa [w] using congrArg Prod.fst hm
  have hm2 : m2 = (tailSplit w).2 := by
    simpa [w] using congrArg Prod.snd hm
  have hs : (∀ i, i < m1 → w.reverse.getD i 0 = 1) ∧
      (∀ i, i < m2 → (w.reverse.drop m1).getD i 0 = 2) := by
    have hs0 := tailSplit_spec w
    have hs0' : (∀ i, i < (tailSplit w).1 → w.reverse.getD i 0 = 1) ∧
        (∀ i, i < (tailSplit w).2 →
          (w.reverse.drop (tailSplit w).1).getD i 0 = 2) := by
      simpa [tailSplit] using hs0
    rwa [← hm1, ← hm2] at hs0'
  let i := m2 - 1 - k
  have hi : i < m2 := by omega
  have htw : (w.reverse.drop m1).getD i 0 = 2 := hs.2 i hi
  have hdrop : (w.reverse.drop m1).getD i 0 =
      w.reverse.getD (m1 + i) 0 := getD_drop_add w.reverse i m1 0
  have hlen : m1 + i < w.length := by
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ w.length := by
      rwa [← hm1, ← hm2] at hsum
    omega
  have hrev : w.reverse.getD (m1 + i) 0 =
      w.getD (w.length - 1 - (m1 + i)) 0 := getD_reverse w (m1 + i) 0 hlen
  have hspec' : w.getD (w.length - 1 - (m1 + i)) 0 = 2 := by
    rw [hdrop] at htw
    rw [hrev] at htw
    exact htw
  have hindex : w.length - 1 - (m1 + i) = n - m1 - m2 + k := by
    have hlen : w.length = n := blockWord_length weight j n
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ w.length := by
      rwa [← hm1, ← hm2] at hsum
    omega
  have hget : w.getD (n - m1 - m2 + k) 0 = 2 := by
    rwa [hindex] at hspec'
  have hbd : n - m1 - m2 + k < n := by
    have hlen : w.length = n := blockWord_length weight j n
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ n := by
      rwa [hlen, ← hm1, ← hm2] at hsum
    have hpos : 0 < m2 - k := by omega
    have hA : 0 < n - m1 := by omega
    have hsub : n - m1 - m2 + k = (n - m1) - (m2 - k) := by omega
    rw [hsub]
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hA hpos) (Nat.sub_le n m1)
  have hwd := blockWord_getD weight j n (n - m1 - m2 + k) hbd
  have hcase := hw (n - m1 - m2 + k) hbd
  rcases hcase with h1 | h2
  · have hwd' : weight (j + (n - m1 - m2 + k) + 1) -
        weight (j + (n - m1 - m2 + k)) = 1 := by
      simp [h1]
    have htwo : weight (j + (n - m1 - m2 + k) + 1) -
        weight (j + (n - m1 - m2 + k)) = 2 := by
      have hwd' : w.getD (n - m1 - m2 + k) 0 =
          weight (j + (n - m1 - m2 + k) + 1) -
            weight (j + (n - m1 - m2 + k)) := by
        simpa [w] using hwd
      rw [← hwd']
      simpa [hindex] using hget
    omega
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2

lemma blockWord_tailSplit_ones_weight
    (weight : Nat → Nat) (j n m1 m2 : Nat)
    (hw : ∀ k < n, weight (j + k + 1) = weight (j + k) + 1 ∨
                   weight (j + k + 1) = weight (j + k) + 2)
    (hm : (m1, m2) = tailSplit (blockWord weight j n)) :
    ∀ k < m1,
      weight (j + (n - m1) + k + 1) =
        weight (j + (n - m1) + k) + 1 := by
  intro k hk
  let w := blockWord weight j n
  have hm1 : m1 = (tailSplit w).1 := by
    simpa [w] using congrArg Prod.fst hm
  have hm2 : m2 = (tailSplit w).2 := by
    simpa [w] using congrArg Prod.snd hm
  have hs : (∀ i, i < m1 → w.reverse.getD i 0 = 1) ∧
      (∀ i, i < m2 → (w.reverse.drop m1).getD i 0 = 2) := by
    have hs0 := tailSplit_spec w
    have hs0' : (∀ i, i < (tailSplit w).1 → w.reverse.getD i 0 = 1) ∧
        (∀ i, i < (tailSplit w).2 →
          (w.reverse.drop (tailSplit w).1).getD i 0 = 2) := by
      simpa [tailSplit] using hs0
    rwa [← hm1, ← hm2] at hs0'
  let i := m1 - 1 - k
  have hi : i < m1 := by omega
  have hone : w.reverse.getD i 0 = 1 := hs.1 i hi
  have hlen : i < w.length := by
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ w.length := by
      rwa [← hm1, ← hm2] at hsum
    omega
  have hrev : w.reverse.getD i 0 = w.getD (w.length - 1 - i) 0 :=
    getD_reverse w i 0 hlen
  have hspec' : w.getD (w.length - 1 - i) 0 = 1 := by
    rw [hrev] at hone
    exact hone
  have hlen : w.length = n := blockWord_length weight j n
  have hindex : w.length - 1 - i = n - m1 + k := by
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ w.length := by
      rwa [← hm1, ← hm2] at hsum
    omega
  have hget : w.getD (n - m1 + k) 0 = 1 := by
    rwa [hindex] at hspec'
  have hbd : n - m1 + k < n := by
    have hklt : k < m1 := hk
    have hsum := tailSplit_sum_le_length w
    have hsum' : m1 + m2 ≤ w.length := by
      rwa [← hm1, ← hm2] at hsum
    omega
  have hwd := blockWord_getD weight j n (n - m1 + k) hbd
  have hcase := hw (n - m1 + k) hbd
  rcases hcase with h1 | h2
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  · have hwd' : weight (j + (n - m1 + k) + 1) -
        weight (j + (n - m1 + k)) = 2 := by
      simp [h2]
    have hone : weight (j + (n - m1 + k) + 1) -
        weight (j + (n - m1 + k)) = 1 := by
      have hwd' : w.getD (n - m1 + k) 0 =
          weight (j + (n - m1 + k) + 1) -
            weight (j + (n - m1 + k)) := by
        simpa [w] using hwd
      rw [← hwd']
      simpa [hindex] using hget
    omega

lemma getD_mem_of_lt (l : List Nat) (i d : Nat) (hi : i < l.length) :
    l.getD i d ∈ l := by
  have hget := List.getElem_eq_getD (l := l) (i := i) (h := hi) d
  have hmem : l[i]'hi ∈ l := List.get_mem l ⟨i, hi⟩
  simpa [hget] using hmem

lemma tailSplit_m2_zero_m1_eq_length (w : List Nat)
    (hmem : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hm : (tailSplit w).2 = 0) :
    (tailSplit w).1 = w.length := by
  let rw := w.reverse
  let m1 := leadingOnes rw
  let m2 := leadingTwos (rw.drop m1)
  have hm1 : m1 = (tailSplit w).1 := by simp [tailSplit, m1, rw]
  have hm2 : m2 = (tailSplit w).2 := by simp [tailSplit, m2, m1, rw]
  have hm0 : m2 = 0 := by simpa [hm2] using hm
  by_contra hne
  have hlt : m1 < w.length := by
    have hle := leadingOnes_le_length rw
    have hlen : rw.length = w.length := by simp [rw]
    have hne' : m1 ≠ w.length := by
      intro h
      apply hne
      simpa [hm1, h] using h
    omega
  have hdrop_pos : 0 < (rw.drop m1).length := by
    have hlen_drop : (rw.drop m1).length = w.length - m1 := by simp [rw]
    omega
  let x := (rw.drop m1).getD 0 0
  have hdrop_eq : (rw.drop m1).getD 0 0 = rw.getD m1 0 := by
    simp
  have hxmem : x ∈ rw.drop m1 := by
    dsimp [x]
    exact getD_mem_of_lt (rw.drop m1) 0 0 hdrop_pos
  have hxmem_rw : x ∈ rw := List.mem_of_mem_drop hxmem
  have hxmem_w : x ∈ w := by
    have hrev : x ∈ w.reverse := by simpa [rw] using hxmem_rw
    exact List.mem_reverse.mp hrev
  rcases hmem x hxmem_w with hx1 | hx2
  · have hones := (leadingOnes_spec rw).2 m1 rfl (by simpa [rw] using hlt)
    have htarget : rw.getD m1 0 = 1 := by
      rw [← hdrop_eq]
      simpa [x] using hx1
    exact hones htarget
  · have hzero : 0 = leadingTwos (rw.drop m1) := by
      change 0 = m2
      exact hm0.symm
    have htwos := (leadingTwos_spec (rw.drop m1)).2 0 hzero hdrop_pos
    have htwos' : rw.getD m1 0 ≠ 2 := by
      simpa [← hdrop_eq] using htwos
    exact htwos' (by
      rw [← hdrop_eq]
      simpa [x] using hx2)

lemma tailSplit_m2_zero_all_ones (w : List Nat)
    (hmem : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hm : (tailSplit w).2 = 0) :
    ∀ i < w.length, w.getD i 0 = 1 := by
  have hm1 : (tailSplit w).1 = w.length := tailSplit_m2_zero_m1_eq_length w hmem hm
  intro i hi
  have hs := tailSplit_spec w
  let k := w.length - 1 - i
  have hk : k < (tailSplit w).1 := by
    have hlen : (tailSplit w).1 = w.length := hm1
    omega
  have hrev := hs.1 k hk
  have hrev' : w.reverse.getD k 0 = w.getD (w.length - 1 - k) 0 :=
    getD_reverse w k 0 (by
      have hlen : (tailSplit w).1 = w.length := hm1
      omega)
  have hw : w.getD (w.length - 1 - k) 0 = 1 := by
    rw [← hrev']
    exact hrev
  have hidx : w.length - 1 - k = i := by
    dsimp [k]
    omega
  simpa [hidx] using hw

lemma tail_start_eq_block_head_of_m2_zero
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n))
    (hm2 : m2 = 0) :
    blockState weight q (j + (n - m1 - m2)) = blockState weight q j := by
  have hmem : ∀ t ∈ blockWord weight j n, t = 1 ∨ t = 2 := by
    apply S6Audit.blockWord_mem weight j n
    intro k hk
    have hks : k < s := by
      have hn' : n = s - j := hn
      have hjle : j ≤ s := hPrem.j_le_s
      omega
    exact hPrem.weight_step k hks
  have hm1 : m1 = n := by
    have hzero : (tailSplit (blockWord weight j n)).2 = 0 := by
      rw [← hm]
      exact hm2
    have h := tailSplit_m2_zero_m1_eq_length (blockWord weight j n) hmem hzero
    rw [blockWord_length] at h
    rw [← hm] at h
    simpa using h
  have ha : j + (n - m1 - m2) = j := by
    rw [hm2, hm1]
    omega
  rw [ha]

lemma t1_step_mod8_five (r r' : Nat)
    (hstep : r' = (5 * r + 1) / 2)
    (hdiv : (5 * r + 1) % 2 = 0)
    (hmod : r' % 8 = 5) :
    r % 8 = 5 := by
  have hmul : 2 * r' = 5 * r + 1 := by
    rw [hstep]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hmod5r : (5 * r + 1) % 8 = 2 := by
    rw [← hmul]
    rw [Nat.mul_mod]
    rw [hmod]
  have h5rmod : (5 * r) % 8 = 1 := by
    have hsum := Nat.add_mod (5 * r) 1 8
    rw [hmod5r] at hsum
    norm_num at hsum ⊢
    have hlt : (5 * r) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  have h5 : (5 * (r % 8)) % 8 = 1 := by
    simpa [Nat.mul_mod] using h5rmod
  have hlt : r % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases r % 8
  all_goals norm_num at h5
  all_goals omega

lemma twoValuation_eq_one_of_mod8_five (n : Nat) (h : n % 8 = 5) :
    twoValuation (n + 1) = 1 := by
  have hpos : 0 < n + 1 := by positivity
  have h8 : (n + 1) % 8 = 6 := by
    rw [Nat.add_mod]
    rw [h]
  have hmod4 : (n + 1) % 4 = 2 := by
    have hmm : (n + 1) % 8 % 4 = (n + 1) % 4 :=
      Nat.mod_mod_of_dvd (n + 1) (c := 4) (b := 8) (by norm_num)
    rw [← hmm, h8]
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (n + 1) hpos
  by_cases hv0 : twoValuation (n + 1) = 0
  · have hodd' : (n + 1) % 2 = 1 :=
      StringFlow.twoValuation_eq_zero_odd (n + 1) hpos hv0
    have heven' : (n + 1) % 2 = 0 := by
      have hmm : (n + 1) % 4 % 2 = (n + 1) % 2 :=
        Nat.mod_mod_of_dvd (n + 1) (c := 2) (b := 4) (by norm_num)
      rw [← hmm, hmod4]
    omega
  · by_cases hvge2 : 2 ≤ twoValuation (n + 1)
    · have hpow : 2 ^ twoValuation (n + 1) =
        4 * 2 ^ (twoValuation (n + 1) - 2) := by
        have h : twoValuation (n + 1) = (twoValuation (n + 1) - 2) + 2 := by omega
        rw [h, Nat.pow_add]
        norm_num
        ring
      have hdvd4 : 4 ∣ n + 1 := by
        refine ⟨2 ^ (twoValuation (n + 1) - 2) * StringFlow.oddPart (n + 1), ?_⟩
        calc
          n + 1 = 2 ^ twoValuation (n + 1) * StringFlow.oddPart (n + 1) := hdec
          _ = 4 * (2 ^ (twoValuation (n + 1) - 2) *
              StringFlow.oddPart (n + 1)) := by
                rw [hpow]
                ring_nf
      have hmod4zero : (n + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd4
      omega
    · have hv1 : twoValuation (n + 1) = 1 := by omega
      exact hv1

lemma t1_run_mod8_five (r : Nat → Nat) (m : Nat)
    (hsteps : ∀ i < m, r (i + 1) = (5 * r i + 1) / 2 ∧ (5 * r i + 1) % 2 = 0)
    (hfinal : r m % 8 = 5) :
    ∀ i ≤ m, r i % 8 = 5 := by
  have hmain : ∀ n, n ≤ m → r (m - n) % 8 = 5 := by
    intro n hn
    induction n using Nat.strongRecOn with
    | ind n ih =>
        by_cases hn0 : n = 0
        · subst n
          simpa using hfinal
        · have hstep := hsteps (m - n) (by omega)
          have hk1 : m - (n - 1) = (m - n) + 1 := by omega
          have hmod_next : r ((m - n) + 1) % 8 = 5 := by
            have hih := ih (n - 1) (by omega) (by omega)
            simpa [hk1] using hih
          exact t1_step_mod8_five (r (m - n)) (r ((m - n) + 1))
            (by simpa [hk1] using hstep.1) (by simpa [hk1] using hstep.2) hmod_next
  intro i hi
  have := hmain (m - i) (Nat.sub_le m i)
  simpa [Nat.sub_sub_self hi] using this

lemma t1_step_r_plus_one_valuation_one (r r' : Nat)
    (hstep : r' = (5 * r + 1) / 2)
    (hdiv : (5 * r + 1) % 2 = 0)
    (hmod : r' % 8 = 5) :
    twoValuation (r + 1) = 1 :=
  twoValuation_eq_one_of_mod8_five r (t1_step_mod8_five r r' hstep hdiv hmod)

/-- `liftToNonneg` returns the least `t` satisfying the predicate. -/
lemma liftToNonneg_minimal (B0 R C t : Nat) (hC : 0 < C)
    (h : R ≤ B0 + C * t) :
    liftToNonneg B0 R C hC ≤ t := by
  unfold liftToNonneg
  have hex : ∃ t, R ≤ B0 + C * t :=
    ⟨R, by have hCR : R ≤ C * R := Nat.le_mul_of_pos_left R hC; omega⟩
  exact Nat.find_min' (p := fun t => R ≤ B0 + C * t) hex h

/-- `wordMolecule weight (n+1) ≡ 2^(weight n) (mod 5)`: the only
5-adic low digit of a weighted word molecule is the final weight. -/
lemma wordMolecule_mod_five (weight : Nat → Nat) (n : Nat) :
    wordMolecule weight (n + 1) ≡ 2 ^ weight n [MOD 5] := by
  rw [Nat.ModEq]
  simp [wordMolecule, Nat.add_mod]

/-- Multiplication by an odd natural is cancellative modulo `2^k`. -/
lemma mul_cancel_modEq (k c a b : Nat) (hcodd : c % 2 = 1)
    (h : c * a ≡ c * b [MOD 2 ^ k]) :
    a ≡ b [MOD 2 ^ k] := by
  by_cases hk : 1 ≤ k
  · let M := 2 ^ k
    let inv := StringFlow.Word.invOdd c (k - 1) % M
    have hspec := invOdd_mod_pow_spec c k hcodd hk
    have hmod1 : 1 % 2 ^ k = 1 := by
      exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : k ≠ 0))
    have hinv : c * inv ≡ 1 [MOD M] := by
      dsimp [inv, M]
      rw [Nat.ModEq]
      simpa [hmod1] using hspec
    have hmul := h.mul_right inv
    have hleft : (c * a) * inv ≡ a [MOD M] := by
      have h' := hinv.mul_left a
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
    have hright : (c * b) * inv ≡ b [MOD M] := by
      have h' := hinv.mul_left b
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
    exact (hleft.symm.trans (hmul.trans hright))
  · have hk0 : k = 0 := by omega
    subst k
    rw [Nat.ModEq]
    simp [Nat.mod_one]

/-- 36.30.23.1 on the real-orbit block head, congruence form: under the
no-`H_ge` premises and `FullOrbitFrom7 r`, `r ≡ 2^(-t_j) (mod 5)`. -/
theorem block_head_mod_five_congruence_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : S6Audit.FullOrbitFrom7 r) :
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
  have hword : wordMolecule weight j ≡ 2 ^ Wp [MOD 5] := by
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
    exact StringFlow.Lte.invMod5_spec (2 ^ Wp) (pow_two_mod_five_ne_zero Wp)
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
      (pow_two_mod_five_ne_zero (Wj - Wp))
  have hmulT := hunit.mul_right invT
  have hleftT : (2 ^ (Wj - Wp) * r) * invT ≡ r [MOD 5] := by
    have h' := hinvT.mul_left r
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
  have hrightT : 1 * invT ≡ invT [MOD 5] := by
    rw [Nat.ModEq]
    simp
  have hmain : r ≡ invT [MOD 5] := hleftT.symm.trans (hmulT.trans hrightT)
  simpa [invT] using hmain.trans (Nat.mod_modEq invT 5).symm

/-- 36.30.23.1 on the real-orbit block head, disjunction form: the block
head is `3 mod 5` for a `t=1` reset and `4 mod 5` for a `t=2` reset. -/
theorem block_head_mod_five_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : S6Audit.FullOrbitFrom7 r) :
    r % 5 = 3 ∨ r % 5 = 4 := by
  have hcong := block_head_mod_five_congruence_of_premises j Wp Wj q Aj A_s s W_s r_s
    L H_s weight r hPrem hrj _hReach
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

/-- The least nonnegative solution `rj0` of the document-36.26 exact
equation is no larger than any other solution `r` satisfying the same
mod-5 block-head residue. -/
theorem rj0_le_of_exact_equation
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r m : Nat)
    (hH : 1 ≤ H_s)
    (hrmod : r ≡ StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5 [MOD 5])
    (heq : 3 * 5 ^ (s - j) * r + 3 * blockB weight j (s - j) + 2 ^ (W_s - Wj)
        = 2 ^ (W_s - Wj + L + 4) *
            (uResidue L (H_s - 1) + m * 2 ^ (H_s - 1))) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≤ r := by
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let u := uResidue L (H_s - 1)
  let inv35 := StringFlow.Word.invOdd (3 * 5 ^ n) (K2 - 1) % 2 ^ K2
  let num := (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) % 2 ^ K2
  let res2 := (num * inv35) % 2 ^ K2
  let res5 := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5
  let r0 := crtRep res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  let M := 2 ^ K2 * 5
  let C := 3 * 5 ^ n * M
  let B0 := 3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ
  let R := 2 ^ (Δ + L + 4) * u
  let t := liftToNonneg B0 R C (three_five_pow_mul_pos n K2)
  have hK2 : 1 ≤ K2 := by dsimp [K2]; omega
  have hMpos : 0 < M := by dsimp [M]; positivity
  have heq0 : 3 * 5 ^ n * r + 3 * B + 2 ^ Δ =
      2 ^ (Δ + L + 4) * (u + m * 2 ^ (H_s - 1)) := by
    simpa [n, Δ, B, u] using heq
  have hpow : 2 ^ (Δ + L + 4) * (m * 2 ^ (H_s - 1)) = m * 2 ^ K2 := by
    dsimp [K2]
    have hsum : (Δ + L + 4) + (H_s - 1) = Δ + L + H_s + 3 := by omega
    calc
      2 ^ (Δ + L + 4) * (m * 2 ^ (H_s - 1))
          = m * (2 ^ (Δ + L + 4) * 2 ^ (H_s - 1)) := by ring
      _ = m * 2 ^ ((Δ + L + 4) + (H_s - 1)) := by rw [← Nat.pow_add]
      _ = m * 2 ^ (Δ + L + H_s + 3) := by rw [hsum]
  have hdist : 2 ^ (Δ + L + 4) * (u + m * 2 ^ (H_s - 1)) =
      2 ^ (Δ + L + 4) * u + 2 ^ (Δ + L + 4) * (m * 2 ^ (H_s - 1)) := by
    rw [Nat.mul_add]
  have heq' : 3 * 5 ^ n * r + (3 * B + 2 ^ Δ) = R + m * 2 ^ K2 := by
    calc
      3 * 5 ^ n * r + (3 * B + 2 ^ Δ)
          = 3 * 5 ^ n * r + 3 * B + 2 ^ Δ := by ring
      _ = 2 ^ (Δ + L + 4) * (u + m * 2 ^ (H_s - 1)) := heq0
      _ = 2 ^ (Δ + L + 4) * u + 2 ^ (Δ + L + 4) * (m * 2 ^ (H_s - 1)) := hdist
      _ = R + m * 2 ^ K2 := by
        dsimp [R]
        rw [hpow]
  have hRmod2r : 3 * 5 ^ n * r + (3 * B + 2 ^ Δ) ≡ R [MOD 2 ^ K2] := by
    rw [Nat.ModEq]
    rw [heq']
    rw [Nat.mul_comm m (2 ^ K2)]
    exact Nat.add_mul_mod_self_left R (2 ^ K2) m
  have hRjmod2 : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
      (3 * B + 2 ^ Δ) ≡ R [MOD 2 ^ K2] := by
    have h := rj0_spec_2 j Wp Wj q Aj A_s s W_s r_s L H_s weight
    simpa [n, Δ, K2, B, u, R, Nat.add_assoc] using h
  have hcongFull : 3 * 5 ^ n * r + (3 * B + 2 ^ Δ) ≡
      3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
        (3 * B + 2 ^ Δ) [MOD 2 ^ K2] := hRmod2r.trans hRjmod2.symm
  have hcong2 : 3 * 5 ^ n * r ≡
      3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight
      [MOD 2 ^ K2] := Nat.ModEq.add_right_cancel' (3 * B + 2 ^ Δ) hcongFull
  have h35odd : (3 * 5 ^ n) % 2 = 1 := by
    rw [Nat.mul_mod]
    have h5 : (5 ^ n) % 2 = 1 := StringFlow.Lte.five_pow_odd n
    simp [h5]
  have hcongR : r ≡ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight [MOD 2 ^ K2] :=
    mul_cancel_modEq K2 (3 * 5 ^ n) r
      (rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight) h35odd hcong2
  have hcong5 : r ≡ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight [MOD 5] := by
    have h1 := hrmod
    have h2 := rj0_spec_5 j Wp Wj q Aj A_s s W_s r_s L H_s weight
    exact h1.trans h2.symm
  have hmodR0 : rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≡ r0 [MOD M] := by
    unfold rj0
    dsimp [n, Δ, K2, B, u, inv35, num, res2, res5, r0, M, C, B0, R, t]
    change (r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M) % M = r0 % M
    conv_lhs => rw [Nat.mul_comm (liftToNonneg B0 R C (three_five_pow_mul_pos n K2)) M]
    rw [Nat.add_mul_mod_self_left r0 M (liftToNonneg B0 R C (three_five_pow_mul_pos n K2))]
  have hcop : Nat.Coprime (2 ^ K2) 5 :=
    Nat.Coprime.pow_left K2 (by decide : Nat.Coprime 2 5)
  have hlcm : Nat.lcm (2 ^ K2) 5 = M := by
    dsimp [M]
    exact hcop.lcm_eq_mul
  have hmodL : r ≡ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight
      [MOD Nat.lcm (2 ^ K2) 5] := Nat.mod_lcm hcongR hcong5
  have hmodM : r ≡ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight [MOD M] := by
    simpa [hlcm] using hmodL
  have hr0 : r ≡ r0 [MOD M] := hmodM.trans hmodR0
  have hr0lt : r0 < M := by
    dsimp [r0, M]
    exact crtRep_lt res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
      (ne_of_gt (by positivity : 0 < 2 ^ K2)) (by decide : 5 ≠ 0)
  have hr0mod : r % M = r0 := by
    have h := hr0
    rw [Nat.ModEq] at h
    have hmod : r0 % M = r0 := Nat.mod_eq_of_lt hr0lt
    rwa [hmod] at h
  have hdiv := Nat.div_add_mod r M
  have hdecomp : r = r0 + (r / M) * M := by
    calc
      r = M * (r / M) + r % M := hdiv.symm
      _ = r0 + (r / M) * M := by
        rw [hr0mod]
        ring
  have hleR : R ≤ 3 * 5 ^ n * r + 3 * B + 2 ^ Δ := by
    have hle : R ≤ R + m * 2 ^ K2 := by omega
    nlinarith [heq', hle]
  have hleR' : R ≤ B0 + C * (r / M) := by
    have hleR'' : R ≤ 3 * 5 ^ n * (r0 + (r / M) * M) + 3 * B + 2 ^ Δ := by
      rwa [hdecomp] at hleR
    dsimp [B0, C]
    have hring : 3 * 5 ^ n * (r0 + (r / M) * M) + 3 * B + 2 ^ Δ =
        (3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ) +
          (3 * 5 ^ n * M) * (r / M) := by ring
    rw [hring] at hleR''
    simpa [Nat.add_assoc] using hleR''
  have ht : liftToNonneg B0 R C (three_five_pow_mul_pos n K2) ≤ r / M :=
    liftToNonneg_minimal B0 R C (r / M) (three_five_pow_mul_pos n K2) hleR'
  unfold rj0
  dsimp [n, Δ, K2, B, u, inv35, num, res2, res5, M, C, B0, R, t]
  have hsum : r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M ≤
      r0 + (r / M) * M := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_right M ht) r0
  change r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M ≤ r
  calc
    r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M ≤
        r0 + (r / M) * M := hsum
    _ = r := hdecomp.symm

/--
`H_ge` is equivalent to the capacity bound `H2 <= j+4`, provided the
definitional link `W_s - Wp = (s - j + 1) + H2` holds.  The link is the
count of `t=2` steps from `j` to `s`; without it the stated equivalence
is not derivable from the raw arithmetic.
-/
theorem H_ge_iff_capacity (j s Ws Wp H2 : Nat)
    (hj : j ≤ s)
    (hW : Ws - Wp = (s - j + 1) + H2) :
    (3 ≤ 2 * s + 13 - 2 * (Ws - Wp)) ↔ H2 ≤ j + 4 := by
  constructor
  · intro h
    have hcalc : 2 * s + 13 - 2 * (Ws - Wp) = 2 * j + 11 - 2 * H2 := by
      omega
    omega
  · intro h
    have hcalc : 2 * s + 13 - 2 * (Ws - Wp) = 2 * j + 11 - 2 * H2 := by
      omega
    omega

/-- Count of `t=2` steps among the first `m` block steps starting at
index `j` (transitions `j -> j+1`, ..., `j+m-1 -> j+m`). -/
def countTwosFrom (weight : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      countTwosFrom weight j n +
        if weight (j + n + 1) - weight (j + n) = 2 then 1 else 0

/-- A `{1,2}` word is nondecreasing in total weight. -/
theorem weight_mono (weight : Nat → Nat) (j k : Nat)
    (hstep : ∀ i : Nat, i < j + k →
      weight (i + 1) = weight i + 1 ∨ weight (i + 1) = weight i + 2) :
    weight j ≤ weight (j + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep' : ∀ i : Nat, i < j + k →
          weight (i + 1) = weight i + 1 ∨ weight (i + 1) = weight i + 2 := by
        intro i hi
        exact hstep i (by omega)
      have hprev : weight j ≤ weight (j + k) := ih hstep'
      have hlast : weight (j + k) ≤ weight (j + k + 1) := by
        have := hstep (j + k) (by omega)
        rcases this with h1 | h2 <;> omega
      simpa [Nat.add_assoc] using le_trans hprev hlast

/-- For a `{1,2}` word, the total weight gain over `m` steps equals
`m` plus the number of `t=2` steps. -/
theorem weight_diff_step_count (weight : Nat → Nat) (j m : Nat)
    (hstep : ∀ k : Nat, k < j + m →
      weight (k + 1) = weight k + 1 ∨ weight (k + 1) = weight k + 2) :
    weight (j + m) - weight j = m + countTwosFrom weight j m := by
  induction m with
  | zero => simp [countTwosFrom]
  | succ m ih =>
      have hstep' : ∀ k : Nat, k < j + m →
          weight (k + 1) = weight k + 1 ∨ weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hih := ih hstep'
      have hlast : weight (j + m + 1) = weight (j + m) + 1 ∨
          weight (j + m + 1) = weight (j + m) + 2 := by
        have := hstep (j + m) (by omega)
        simpa [Nat.add_assoc] using this
      have hmono : weight j ≤ weight (j + m) := by
        exact weight_mono weight j m (by intro i hi; exact hstep i (by omega))
      rcases hlast with h1 | h2
      · have hcnt : countTwosFrom weight j (m + 1) = countTwosFrom weight j m := by
          simp [countTwosFrom, h1]
        have hL : j + (m + 1) = j + m + 1 := by omega
        have hgoal : weight (j + (m + 1)) - weight j = (m + 1) + countTwosFrom weight j m := by
          rw [hL]
          have hdiff : weight (j + m + 1) - weight j = (weight (j + m) - weight j) + 1 := by
            omega
          rw [hdiff, hih]
          omega
        rwa [← hcnt] at hgoal
      · have hcnt : countTwosFrom weight j (m + 1) = countTwosFrom weight j m + 1 := by
          simp [countTwosFrom, h2]
        have hL : j + (m + 1) = j + m + 1 := by omega
        have hgoal : weight (j + (m + 1)) - weight j = (m + 1) + (countTwosFrom weight j m + 1) := by
          rw [hL]
          have hdiff : weight (j + m + 1) - weight j = (weight (j + m) - weight j) + 2 := by
            omega
          rw [hdiff, hih]
          omega
        rwa [← hcnt] at hgoal

/-- The definitional link needed by `H_ge_iff_capacity` is derivable from
the no-`H_ge` premises: `W_s - Wp = (s-j+1) + countTwosFrom weight (j-1) (s-j+1)`. -/
theorem weight_link_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    W_s - Wp = (s - j + 1) + countTwosFrom weight (j - 1) (s - j + 1) := by
  have hsum' : (j - 1) + (s - j + 1) = s := by
    have hj1 : j - 1 + 1 = j := Nat.sub_add_cancel hPrem.j_pos
    have hsj : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    calc
      (j - 1) + (s - j + 1) = (j - 1) + 1 + (s - j) := by omega
      _ = j + (s - j) := by rw [hj1]
      _ = s := hsj
  have hsum : weight ((j - 1) + (s - j + 1)) - weight (j - 1) =
      (s - j + 1) + countTwosFrom weight (j - 1) (s - j + 1) := by
    apply weight_diff_step_count weight (j - 1) (s - j + 1)
    intro k hk
    have hks : k < s := by
      rw [hsum'] at hk
      exact hk
    exact hPrem.weight_step k hks
  rw [hsum'] at hsum
  rw [hPrem.Wp_def, hPrem.Ws_def]
  exact hsum

/-- With `H2 := countTwosFrom weight (j-1) (s-j+1)`, the capacity
equivalence follows from the no-`H_ge` premises alone. -/
theorem H_ge_iff_capacity_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    (3 ≤ H_s) ↔ countTwosFrom weight (j - 1) (s - j + 1) ≤ j + 4 := by
  rw [hPrem.H_def]
  exact H_ge_iff_capacity j s W_s Wp
    (countTwosFrom weight (j - 1) (s - j + 1))
    hPrem.j_le_s (weight_link_of_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem)

/-- The odd part `w = (3*r_s + 1) / 2^(L+4)` of the terminal state. -/
def wTerminal (L r_s : Nat) : Nat :=
  (3 * r_s + 1) / 2 ^ (L + 4)

/-- Under the exact valuation condition, `wTerminal` is the odd part:
`3*r_s+1 = 2^(L+4) * w`. -/
lemma wTerminal_mul_eq (L r_s : Nat)
    (hL : L + 4 = twoValuation (3 * r_s + 1)) :
    3 * r_s + 1 = 2 ^ (L + 4) * wTerminal L r_s := by
  have hpos : 0 < 3 * r_s + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (3 * r_s + 1) hpos
  have hdec' : 3 * r_s + 1 = 2 ^ (L + 4) * StringFlow.oddPart (3 * r_s + 1) := by
    simpa [← hL] using hdec
  have hq : wTerminal L r_s = StringFlow.oddPart (3 * r_s + 1) := by
    unfold wTerminal
    calc
      (3 * r_s + 1) / 2 ^ (L + 4)
          = (2 ^ (L + 4) * StringFlow.oddPart (3 * r_s + 1)) / 2 ^ (L + 4) := by
            conv_lhs => rw [hdec']
      _ = StringFlow.oddPart (3 * r_s + 1) :=
        Nat.mul_div_cancel_left (StringFlow.oddPart (3 * r_s + 1))
          (by positivity : 0 < 2 ^ (L + 4))
  rw [hq]
  exact hdec'

/-- 36.29.1 valuation shift: one `t=1` strip raises `v2(3r+1)` by one. -/
lemma t1_strip_twoValuation (r r' L : Nat)
    (hstep : r' = (5 * r + 1) / 2)
    (hdiv : (5 * r + 1) % 2 = 0)
    (hL : L + 4 = twoValuation (3 * r' + 1)) :
    (L + 1) + 4 = twoValuation (3 * r + 1) := by
  have hmul : 2 * r' = 5 * r + 1 := by
    rw [hstep]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have h2z : 2 * (3 * r' + 1) = 5 * (3 * r + 1) := by
    calc
      2 * (3 * r' + 1) = 6 * r' + 2 := by ring
      _ = 3 * (2 * r') + 2 := by ring
      _ = 3 * (5 * r + 1) + 2 := by rw [hmul]
      _ = 5 * (3 * r + 1) := by ring
  have hpos : 0 < 3 * r + 1 := by positivity
  have hleftv : twoValuation (2 * (3 * r' + 1)) = twoValuation (3 * r' + 1) + 1 := by
    exact StringFlow.twoValuation_mul_two (3 * r' + 1) (by positivity)
  have hrightv : twoValuation (5 * (3 * r + 1)) = twoValuation (3 * r + 1) := by
    exact StringFlow.Lte.twoValuation_mul_odd 5 (3 * r + 1) (by norm_num) hpos
  have heqv : twoValuation (2 * (3 * r' + 1)) = twoValuation (5 * (3 * r + 1)) := by
    rw [h2z]
  rw [hleftv, hrightv] at heqv
  rw [← hL] at heqv
  omega

/-- 36.29.1: stripping one trailing `t=1` step multiplies the odd part
`wTerminal` by `5` and increments `L`. -/
lemma t1_strip_wTerminal_mul (r r' L : Nat)
    (hstep : r' = (5 * r + 1) / 2)
    (hdiv : (5 * r + 1) % 2 = 0)
    (hL : L + 4 = twoValuation (3 * r' + 1)) :
    wTerminal L r' = 5 * wTerminal (L + 1) r := by
  have hmul : 2 * r' = 5 * r + 1 := by
    rw [hstep]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have h2z : 2 * (3 * r' + 1) = 5 * (3 * r + 1) := by
    calc
      2 * (3 * r' + 1) = 6 * r' + 2 := by ring
      _ = 3 * (2 * r') + 2 := by ring
      _ = 3 * (5 * r + 1) + 2 := by rw [hmul]
      _ = 5 * (3 * r + 1) := by ring
  have hpos : 0 < 3 * r + 1 := by positivity
  have hval : L + 5 = twoValuation (3 * r + 1) := by
    have hleftv : twoValuation (2 * (3 * r' + 1)) = twoValuation (3 * r' + 1) + 1 := by
      exact StringFlow.twoValuation_mul_two (3 * r' + 1) (by positivity)
    have hrightv : twoValuation (5 * (3 * r + 1)) = twoValuation (3 * r + 1) := by
      exact StringFlow.Lte.twoValuation_mul_odd 5 (3 * r + 1) (by norm_num) hpos
    have heqv : twoValuation (2 * (3 * r' + 1)) = twoValuation (5 * (3 * r + 1)) := by
      rw [h2z]
    rw [hleftv, hrightv] at heqv
    rw [← hL] at heqv
    omega
  have hw' : 3 * r' + 1 = 2 ^ (L + 4) * wTerminal L r' := wTerminal_mul_eq L r' hL
  have hw : 3 * r + 1 = 2 ^ (L + 5) * wTerminal (L + 1) r := wTerminal_mul_eq (L + 1) r hval
  have hmain : 2 * (2 ^ (L + 4) * wTerminal L r') =
      5 * (2 ^ (L + 5) * wTerminal (L + 1) r) := by
    rw [← hw', ← hw, h2z]
  have hpow : 2 * 2 ^ (L + 4) = 2 ^ (L + 5) := by
    rw [show L + 5 = (L + 4) + 1 by omega]
    rw [Nat.pow_add]
    ring_nf
  have hmain' : 2 ^ (L + 5) * wTerminal L r' =
      5 * (2 ^ (L + 5) * wTerminal (L + 1) r) := by
    calc
      2 ^ (L + 5) * wTerminal L r' = 2 * (2 ^ (L + 4) * wTerminal L r') := by
        rw [← hpow]
        ring
      _ = 5 * (2 ^ (L + 5) * wTerminal (L + 1) r) := hmain
  have hcancel : wTerminal L r' = 5 * wTerminal (L + 1) r := by
    have hpos2 : 0 < 2 ^ (L + 5) := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpos2
    rw [hmain']
    ring
  exact hcancel

/-- 36.29.1 iterated: `m` consecutive trailing `t=1` strips multiply
`wTerminal` by `5^m` and increment `L` by `m`. -/
lemma t1_strip_iter_wTerminal (r : Nat → Nat) (m L : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 2 ∧ (5 * r i + 1) % 2 = 0)
    (hL : L + 4 = twoValuation (3 * r m + 1)) :
    wTerminal L (r m) = 5 ^ m * wTerminal (L + m) (r 0) := by
  induction m generalizing L with
  | zero =>
      simp
  | succ m ih =>
      have hstep_m : r (m + 1) = (5 * r m + 1) / 2 := (hsteps m (by omega)).1
      have hdiv_m : (5 * r m + 1) % 2 = 0 := (hsteps m (by omega)).2
      have hval_m : (L + 1) + 4 = twoValuation (3 * r m + 1) :=
        t1_strip_twoValuation (r m) (r (m + 1)) L hstep_m hdiv_m hL
      have hstrip : wTerminal L (r (m + 1)) = 5 * wTerminal (L + 1) (r m) :=
        t1_strip_wTerminal_mul (r m) (r (m + 1)) L hstep_m hdiv_m hL
      have hih := ih (L + 1) (fun i hi => hsteps i (by omega)) hval_m
      rw [hstrip, hih]
      have hsum1 : (L + 1) + m = L + (m + 1) := by omega
      have hsum2 : m + 1 = Nat.succ m := by omega
      rw [hsum1, hsum2, Nat.pow_succ]
      ring

lemma t1_strip_iter_twoValuation (r : Nat → Nat) (m L : Nat)
    (hsteps : ∀ i < m, r (i + 1) = (5 * r i + 1) / 2 ∧ (5 * r i + 1) % 2 = 0)
    (hL : L + 4 = twoValuation (3 * (r m) + 1)) :
    (L + m) + 4 = twoValuation (3 * (r 0) + 1) := by
  induction m generalizing L with
  | zero => simp [hL]
  | succ m ih =>
      have hstep_m : r (m + 1) = (5 * r m + 1) / 2 := (hsteps m (by omega)).1
      have hdiv_m : (5 * r m + 1) % 2 = 0 := (hsteps m (by omega)).2
      have hval_m : (L + 1) + 4 = twoValuation (3 * (r m) + 1) :=
        t1_strip_twoValuation (r m) (r (m + 1)) L hstep_m hdiv_m hL
      have hih := ih (L + 1) (fun i hi => hsteps i (by omega)) hval_m
      have hgoal : (L + (m + 1)) + 4 = twoValuation (3 * (r 0) + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hih
      exact hgoal

/-- 36.29.2 step: one exact `t=2` step satisfies `4*(r'+1)=5*(r+1)`. -/
lemma t2_step_plus_one_mul (r r' : Nat)
    (hstep : r' = (5 * r + 1) / 4)
    (hdiv : (5 * r + 1) % 4 = 0) :
    4 * (r' + 1) = 5 * (r + 1) := by
  have hmul : 4 * r' = 5 * r + 1 := by
    rw [hstep]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  calc
    4 * (r' + 1) = 4 * r' + 4 := by ring
    _ = 5 * r + 1 + 4 := by rw [hmul]
    _ = 5 * (r + 1) := by ring

/-- 36.29.2 iterated: `m` consecutive `t=2` steps multiply `r+1` by
`5^m/4^m`. -/
lemma t2_run_mul (r : Nat → Nat) (m : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 4 ∧ (5 * r i + 1) % 4 = 0) :
    4 ^ m * (r m + 1) = 5 ^ m * (r 0 + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep_m : r (m + 1) = (5 * r m + 1) / 4 := (hsteps m (by omega)).1
      have hdiv_m : (5 * r m + 1) % 4 = 0 := (hsteps m (by omega)).2
      have hmul_step : 4 * (r (m + 1) + 1) = 5 * (r m + 1) :=
        t2_step_plus_one_mul (r m) (r (m + 1)) hstep_m hdiv_m
      have hih := ih (fun i hi => hsteps i (by omega))
      calc
        4 ^ (m + 1) * (r (m + 1) + 1)
            = 4 ^ m * (4 * (r (m + 1) + 1)) := by
                rw [Nat.pow_succ]
                ring
          _ = 4 ^ m * (5 * (r m + 1)) := by rw [hmul_step]
          _ = 5 * (4 ^ m * (r m + 1)) := by ring
          _ = 5 * (5 ^ m * (r 0 + 1)) := by rw [hih]
          _ = 5 ^ (m + 1) * (r 0 + 1) := by
                rw [Nat.pow_succ]
                ring

/-- 36.29.2 closed form: with `r_0+1=2^(2m+1)·u`, the `t=2` run end is
`r_m+1=2·5^m·u`. -/
lemma t2_run_closed_form (r : Nat → Nat) (m u : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 4 ∧ (5 * r i + 1) % 4 = 0)
    (hstart : r 0 + 1 = 2 ^ (2 * m + 1) * u) :
    r m + 1 = 2 * 5 ^ m * u := by
  have hmul := t2_run_mul r m hsteps
  have hpow4 : 4 ^ m = 2 ^ (2 * m) := by
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← Nat.pow_mul]
  have hpow1 : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by
    have hsucc : 2 * m + 1 = (2 * m) + 1 := by omega
    rw [hsucc, Nat.pow_add, Nat.pow_one]
    ring
  have hmain : 2 ^ (2 * m) * (r m + 1) = 2 * 5 ^ m * (2 ^ (2 * m) * u) := by
    calc
      2 ^ (2 * m) * (r m + 1) = 4 ^ m * (r m + 1) := by rw [hpow4]
      _ = 5 ^ m * (r 0 + 1) := hmul
      _ = 5 ^ m * (2 ^ (2 * m + 1) * u) := by rw [hstart]
      _ = 2 * 5 ^ m * (2 ^ (2 * m) * u) := by
            rw [hpow1]
            ring
  have hpos : 0 < 2 ^ (2 * m) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmain]
  ring

/-- 36.29.2 cleared form: under the `t=2` run decomposition,
`2^(L+3)·wTerminal L (r_m) = 3·5^m·u − 1`. -/
lemma t2_run_wTerminal_mul (r : Nat → Nat) (m L u : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 4 ∧ (5 * r i + 1) % 4 = 0)
    (hstart : r 0 + 1 = 2 ^ (2 * m + 1) * u)
    (hL : L + 4 = twoValuation (3 * (r m) + 1)) :
    2 ^ (L + 3) * wTerminal L (r m) = 3 * 5 ^ m * u - 1 := by
  have hclose := t2_run_closed_form r m u hsteps hstart
  have hpos : 0 < r m + 1 := by positivity
  have hge : 1 ≤ 2 * 5 ^ m * u := by
    nlinarith [hpos, hclose]
  have hr : r m = 2 * 5 ^ m * u - 1 := by omega
  let Y := 5 ^ m * u
  have hY : 1 ≤ 2 * Y := by
    dsimp [Y]
    have hrew : 2 * 5 ^ m * u = 2 * (5 ^ m * u) := by ring
    rw [← hrew]
    exact hge
  have hrY : r m = 2 * Y - 1 := by
    dsimp [Y]
    have hrew : 2 * 5 ^ m * u = 2 * (5 ^ m * u) := by ring
    rw [hrew] at hr
    exact hr
  have hzY : 3 * (2 * Y - 1) + 1 = 2 * (3 * Y - 1) := by
    have hY3 : 1 ≤ 3 * Y := by nlinarith [hY]
    omega
  have hz : 3 * (r m) + 1 = 2 * (3 * 5 ^ m * u - 1) := by
    rw [hrY]
    have h3Y : 3 * 5 ^ m * u = 3 * Y := by
      dsimp [Y]
      ring
    rw [h3Y]
    exact hzY
  have hw := wTerminal_mul_eq L (r m) hL
  have hpow : 2 ^ (L + 4) = 2 * 2 ^ (L + 3) := by
    rw [show L + 4 = (L + 3) + 1 by omega]
    rw [Nat.pow_add]
    ring_nf
  have hw2 : 2 * (3 * 5 ^ m * u - 1) = 2 ^ (L + 4) * wTerminal L (r m) := by
    rw [← hz, hw]
  have hw3 : 3 * 5 ^ m * u - 1 = 2 ^ (L + 3) * wTerminal L (r m) := by
    have hw2' : 2 * (3 * 5 ^ m * u - 1) = 2 * (2 ^ (L + 3) * wTerminal L (r m)) := by
      rw [hpow] at hw2
      simpa [Nat.mul_assoc] using hw2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hw2'
  exact hw3.symm

/-- 36.29.2 conclusion: under the `t=2` run decomposition, the odd part is
`wTerminal L (r_m) = (3·5^m·u − 1)/2^(L+3)`. -/
lemma t2_run_wTerminal (r : Nat → Nat) (m L u : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 4 ∧ (5 * r i + 1) % 4 = 0)
    (hstart : r 0 + 1 = 2 ^ (2 * m + 1) * u)
    (hL : L + 4 = twoValuation (3 * (r m) + 1)) :
    wTerminal L (r m) = (3 * 5 ^ m * u - 1) / 2 ^ (L + 3) := by
  have hz := t2_run_wTerminal_mul r m L u hsteps hstart hL
  have hw3 : 3 * 5 ^ m * u - 1 = 2 ^ (L + 3) * wTerminal L (r m) := hz.symm
  have hdvd : 2 ^ (L + 3) ∣ 3 * 5 ^ m * u - 1 := ⟨wTerminal L (r m), hw3⟩
  have hcancel : (3 * 5 ^ m * u - 1) / 2 ^ (L + 3) = wTerminal L (r m) := by
    rw [hw3]
    exact Nat.mul_div_right (wTerminal L (r m)) (by positivity : 0 < 2 ^ (L + 3))
  exact hcancel.symm

/-- 36.29.3 clearing: if `w = z/2^(L+3)`, the failure
`2^(H_s-1) | 5^(L+3)w+1` lifts to
`2^(L+H_s+2) | 5^(L+3)z+2^(L+3)`. -/
lemma failure_congruence_lift_w
    (L H_s z w : Nat) (_hH : 2 ≤ H_s)
    (hz : 2 ^ (L + 3) * w = z)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * w + 1) :
    2 ^ (L + H_s + 2) ∣ 5 ^ (L + 3) * z + 2 ^ (L + 3) := by
  rcases hfail with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hpow : 2 ^ (L + 3) * 2 ^ (H_s - 1) = 2 ^ (L + H_s + 2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    5 ^ (L + 3) * z + 2 ^ (L + 3)
        = 5 ^ (L + 3) * (2 ^ (L + 3) * w) + 2 ^ (L + 3) := by rw [hz]
      _ = 2 ^ (L + 3) * (5 ^ (L + 3) * w + 1) := by ring
      _ = 2 ^ (L + 3) * (2 ^ (H_s - 1) * k) := by rw [hk]
      _ = 2 ^ (L + H_s + 2) * k := by
            rw [← Nat.mul_assoc, hpow]

/-- 36.29.3: the failure congruence for the `t=2` run end, written as a
single 2-adic congruence on `u`. -/
lemma t2_run_failure_congruence
    (r : Nat → Nat) (m L H_s u : Nat)
    (hsteps : ∀ i, i < m → r (i + 1) = (5 * r i + 1) / 4 ∧ (5 * r i + 1) % 4 = 0)
    (hstart : r 0 + 1 = 2 ^ (2 * m + 1) * u)
    (hL : L + 4 = twoValuation (3 * (r m) + 1))
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L (r m) + 1) :
    2 ^ (L + H_s + 2) ∣ 5 ^ (L + 3) * (3 * 5 ^ m * u - 1) + 2 ^ (L + 3) := by
  have hz := t2_run_wTerminal_mul r m L u hsteps hstart hL
  exact failure_congruence_lift_w L H_s (3 * 5 ^ m * u - 1) (wTerminal L (r m)) hH hz hfail

/-- 36.29.3 full tail: `m1` trailing `t=1` strips followed by `m2` `t=2`
steps give `wTerminal L r_s = 5^m1·(3·5^m2·u−1)/2^(L+m1+3)`. -/
lemma tail_wTerminal_full
    (r1 r2 : Nat → Nat) (m1 m2 L u : Nat)
    (ht1 : ∀ i, i < m1 → r1 (i + 1) = (5 * r1 i + 1) / 2 ∧ (5 * r1 i + 1) % 2 = 0)
    (ht2 : ∀ i, i < m2 → r2 (i + 1) = (5 * r2 i + 1) / 4 ∧ (5 * r2 i + 1) % 4 = 0)
    (hstart2 : r2 0 + 1 = 2 ^ (2 * m2 + 1) * u)
    (hmid : r1 0 = r2 m2)
    (hL1 : L + 4 = twoValuation (3 * (r1 m1) + 1))
    (hL2 : (L + m1) + 4 = twoValuation (3 * (r2 m2) + 1)) :
    wTerminal L (r1 m1) =
      5 ^ m1 * ((3 * 5 ^ m2 * u - 1) / 2 ^ ((L + m1) + 3)) := by
  have hw1 := t1_strip_iter_wTerminal r1 m1 L ht1 hL1
  have hw2 := t2_run_wTerminal r2 m2 (L + m1) u ht2 hstart2 hL2
  rw [hw1, hmid, hw2]

lemma block_tail_wTerminal_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n)) :
    ∃ r1 r2 : Nat → Nat, ∃ u : Nat,
      (∀ i < m1, r1 (i + 1) = (5 * r1 i + 1) / 2 ∧ (5 * r1 i + 1) % 2 = 0) ∧
      (∀ i < m2, r2 (i + 1) = (5 * r2 i + 1) / 4 ∧ (5 * r2 i + 1) % 4 = 0) ∧
      r1 0 = r2 m2 ∧
      r1 m1 = r_s ∧
      r2 0 = blockState weight q (j + (n - m1 - m2)) ∧
      (L + m1) + 4 = twoValuation (3 * (r2 m2) + 1) ∧
      r2 0 + 1 = 2 ^ (2 * m2 + 1) * u ∧
      wTerminal L r_s =
        5 ^ m1 * ((3 * 5 ^ m2 * u - 1) / 2 ^ ((L + m1) + 3)) := by
  let a := j + (n - m1 - m2)
  let r2 : Nat → Nat := fun i => blockState weight q (a + i)
  let r1 : Nat → Nat := fun i => blockState weight q (a + m2 + i)
  let u : Nat := StringFlow.oddPart (r2 0 + 1)
  have hsum0 : m1 + m2 ≤ n := by
    have hsum := tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum
    rw [hlen] at hsum
    simpa using hsum
  have ha_end : a + m2 + m1 = s := by
    dsimp [a]
    have hn' : n = s - j := hn
    have hjle : j ≤ s := hPrem.j_le_s
    have hsum0' : m1 + m2 ≤ s - j := by
      rwa [hn'] at hsum0
    omega
  have hwstep : ∀ k < n, weight (j + k + 1) = weight (j + k) + 1 ∨
      weight (j + k + 1) = weight (j + k) + 2 := by
    intro k hk
    have hk' : j + k < s := by
      have hn' : n = s - j := hn
      omega
    exact hPrem.weight_step (j + k) hk'
  have ht1_weights := blockWord_tailSplit_ones_weight weight j n m1 m2 hwstep hm
  have ht2_weights := blockWord_tailSplit_twos_weight weight j n m1 m2 hwstep hm
  have hvalid2 : ∀ i ≤ m2, (wordMolecule weight (a + i) + 5 ^ (a + i) * q) %
      2 ^ weight (a + i) = 0 := by
    intro i hi
    have hle : a + i ≤ s := by
      dsimp [a]
      have hn' : n = s - j := hn
      omega
    exact hPrem.valid_prefix (a + i) hle
  have hvalid1 : ∀ i ≤ m1, (wordMolecule weight (a + m2 + i) + 5 ^ (a + m2 + i) * q) %
      2 ^ weight (a + m2 + i) = 0 := by
    intro i hi
    have hle : a + m2 + i ≤ s := by
      dsimp [a]
      omega
    exact hPrem.valid_prefix (a + m2 + i) hle
  have ht2_steps : ∀ i < m2, weight (a + i + 1) = weight (a + i) + 2 := by
    intro i hi
    have h := ht2_weights i hi
    simpa [a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have ht1_steps : ∀ i < m1, weight (a + m2 + i + 1) = weight (a + m2 + i) + 1 := by
    intro i hi
    have h := ht1_weights i hi
    have h' : j + (n - m1) = a + m2 := by
      dsimp [a]
      omega
    rw [h'] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hres2 := block_trailing_twos_step weight q a m2 ht2_steps hvalid2
  have hres1 := block_trailing_ones_step weight q (a + m2) m1 ht1_steps hvalid1
  have ht1 : ∀ i < m1, r1 (i + 1) = (5 * r1 i + 1) / 2 ∧ (5 * r1 i + 1) % 2 = 0 := by
    intro i hi
    have h := hres1 i hi
    simpa [r1, Nat.add_assoc] using h
  have ht2 : ∀ i < m2, r2 (i + 1) = (5 * r2 i + 1) / 4 ∧ (5 * r2 i + 1) % 4 = 0 := by
    intro i hi
    have h := hres2 i hi
    simpa [r2, Nat.add_assoc] using h
  have hmid : r1 0 = r2 m2 := by
    simp [r1, r2]
  have hend : r1 m1 = r_s := by
    dsimp [r1]
    have hsum : a + m2 + m1 = s := ha_end
    rw [hsum]
    have hbs : blockState weight q s = r_s := by
      dsimp [blockState]
      rw [← hPrem.A_s_mol, ← hPrem.Ws_def]
      exact hPrem.r_s_eq.symm
    exact hbs
  have hL2 : (L + m1) + 4 = twoValuation (3 * (r2 m2) + 1) := by
    have hval_s : L + 4 = twoValuation (3 * (r1 m1) + 1) := by
      simpa [hend] using hPrem.L_val
    have hval0 := t1_strip_iter_twoValuation r1 m1 L ht1 hval_s
    simpa [hmid] using hval0
  have hval_end : twoValuation (r2 m2 + 1) = 1 := by
    have hmod : r2 m2 % 8 = 5 := by
      have hmods : r_s % 8 = 5 := hPrem.r_s_mod8
      have hmod_all := t1_run_mod8_five r1 m1 ht1 (by simpa [hend] using hmods)
      have hr10 : r1 0 % 8 = 5 := hmod_all 0 (Nat.zero_le m1)
      simpa [hmid] using hr10
    exact twoValuation_eq_one_of_mod8_five (r2 m2) hmod
  have hpos_end : 0 < r2 m2 + 1 := by positivity
  have hdec_end := StringFlow.n_eq_two_pow_mul_oddPart (r2 m2 + 1) hpos_end
  have hmul := t2_run_mul r2 m2 ht2
  have hpow4 : 4 ^ m2 = 2 ^ (2 * m2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← Nat.pow_mul]
  have hleft : twoValuation (4 ^ m2 * (r2 m2 + 1)) = 2 * m2 + 1 := by
    rw [hpow4]
    have hdec' : r2 m2 + 1 = 2 * StringFlow.oddPart (r2 m2 + 1) := by
      simp [hval_end] at hdec_end
      simpa using hdec_end
    have hpow : 2 ^ (2 * m2) * 2 = 2 ^ (2 * m2 + 1) := by
      rw [show 2 * m2 + 1 = (2 * m2) + 1 by omega, Nat.pow_add, Nat.pow_one]
    have hprod : 2 ^ (2 * m2) * (r2 m2 + 1) =
        2 ^ (2 * m2 + 1) * StringFlow.oddPart (r2 m2 + 1) := by
      conv_lhs =>
        arg 2
        rw [hdec']
      calc
        2 ^ (2 * m2) * (2 * StringFlow.oddPart (r2 m2 + 1))
            = (2 ^ (2 * m2) * 2) * StringFlow.oddPart (r2 m2 + 1) := by ring
        _ = 2 ^ (2 * m2 + 1) * StringFlow.oddPart (r2 m2 + 1) := by rw [hpow]
    rw [hprod]
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq (2 * m2 + 1)
      (StringFlow.oddPart (r2 m2 + 1))
      (StringFlow.oddPart_odd_of_pos (r2 m2 + 1) hpos_end)
  have hright : twoValuation (5 ^ m2 * (r2 0 + 1)) = twoValuation (r2 0 + 1) :=
    StringFlow.Lte.twoValuation_mul_odd (5 ^ m2) (r2 0 + 1)
      (StringFlow.Lte.five_pow_odd m2) (by positivity)
  have hv : twoValuation (r2 0 + 1) = 2 * m2 + 1 := by
    have hcong := congrArg twoValuation hmul
    rw [hleft, hright] at hcong
    exact hcong.symm
  have hpos0 : 0 < r2 0 + 1 := by positivity
  have hdec0 := StringFlow.n_eq_two_pow_mul_oddPart (r2 0 + 1) hpos0
  have hstart : r2 0 + 1 = 2 ^ (2 * m2 + 1) * u := by
    dsimp [u]
    simp [hv] at hdec0
    exact hdec0
  have hw := tail_wTerminal_full r1 r2 m1 m2 L u ht1 ht2 hstart hmid
    (by simpa [hend] using hPrem.L_val) hL2
  refine ⟨r1, r2, u, ht1, ht2, hmid, hend, ?_, hL2, hstart, ?_⟩
  · dsimp [r2]
  · simpa [hend] using hw

lemma tail_failure_congruence_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n))
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ∃ r2 : Nat → Nat, ∃ u : Nat,
      (∀ i < m2, r2 (i + 1) = (5 * r2 i + 1) / 4 ∧ (5 * r2 i + 1) % 4 = 0) ∧
      r2 0 + 1 = 2 ^ (2 * m2 + 1) * u ∧
      r2 0 = blockState weight q (j + (n - m1 - m2)) ∧
      (L + m1) + 4 = twoValuation (3 * (r2 m2) + 1) ∧
      2 ^ ((L + m1) + H_s + 2) ∣
        5 ^ ((L + m1) + 3) * (3 * 5 ^ m2 * u - 1) + 2 ^ ((L + m1) + 3) := by
  rcases block_tail_wTerminal_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2
    weight hPrem hn hm with ⟨r1, r2, u, ht1, ht2, hmid, hend, hstart_block, hL2, hstart, hwterm⟩
  have hval_s : L + 4 = twoValuation (3 * (r1 m1) + 1) := by
    simpa [hend] using hPrem.L_val
  have hw1 := t1_strip_iter_wTerminal r1 m1 L ht1 hval_s
  have hw2 : wTerminal L r_s = 5 ^ m1 * wTerminal (L + m1) (r2 m2) := by
    simpa [hend, hmid] using hw1
  have hpow : 5 ^ (L + m1 + 3) = 5 ^ (L + 3) * 5 ^ m1 := by
    rw [show L + m1 + 3 = (L + 3) + m1 by omega, Nat.pow_add]
  have hfail' : 2 ^ (H_s - 1) ∣
      5 ^ (L + m1 + 3) * wTerminal (L + m1) (r2 m2) + 1 := by
    rcases hfail with ⟨k, hk⟩
    rw [hw2] at hk
    refine ⟨k, ?_⟩
    rw [hpow]
    ring_nf at hk ⊢
    exact hk
  have hcong := t2_run_failure_congruence r2 m2 (L + m1) H_s u
    ht2 hstart hL2 hH hfail'
  refine ⟨r2, u, ht2, hstart, hstart_block, hL2, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcong

lemma tail_failure_odd_part_congruence
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n))
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ∃ r2 : Nat → Nat, ∃ u w : Nat,
      (∀ i < m2, r2 (i + 1) = (5 * r2 i + 1) / 4 ∧ (5 * r2 i + 1) % 4 = 0) ∧
      r2 0 + 1 = 2 ^ (2 * m2 + 1) * u ∧
      r2 0 = blockState weight q (j + (n - m1 - m2)) ∧
      (L + m1) + 4 = twoValuation (3 * (r2 m2) + 1) ∧
      3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w ∧
      w % 2 = 1 ∧
      2 ^ (H_s - 1) ∣ 5 ^ ((L + m1) + 3) * w + 1 := by
  rcases tail_failure_congruence_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2
    weight hPrem hn hm hH hfail with ⟨r2, u, ht2, hstart, hstart_block, hL2, hcong⟩
  have hclosed := t2_run_closed_form r2 m2 u ht2 hstart
  have hpos : 0 < 3 * 5 ^ m2 * u - 1 := by
    have hupos : 0 < u := by
      by_contra hu0
      have hu : u = 0 := by omega
      rw [hu] at hstart
      simp at hstart
    have hpowpos : 0 < 5 ^ m2 := by positivity
    have hApos : 0 < 5 ^ m2 * u := Nat.mul_pos hpowpos hupos
    have hA1 : 1 ≤ 5 ^ m2 * u := by omega
    have hA3 : 3 ≤ 3 * (5 ^ m2 * u) := by nlinarith
    have hpos' : 0 < 3 * (5 ^ m2 * u) - 1 := by omega
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpos'
  have hrel : 3 * (r2 m2) + 1 = 2 * (3 * 5 ^ m2 * u - 1) := by
    have hrel' : 3 * (r2 m2 + 1) - 2 = 2 * (3 * 5 ^ m2 * u - 1) := by
      rw [hclosed]
      ring_nf
      have hA3 : 1 ≤ 3 * 5 ^ m2 * u := by nlinarith
      omega
    have hrew : 3 * (r2 m2 + 1) - 2 = 3 * (r2 m2) + 1 := by omega
    rw [← hrew]
    exact hrel'
  have hv : twoValuation (3 * 5 ^ m2 * u - 1) = (L + m1) + 3 := by
    have hleft : twoValuation (3 * (r2 m2) + 1) =
        twoValuation (2 * (3 * 5 ^ m2 * u - 1)) := by rw [hrel]
    have hv2 : twoValuation (2 * (3 * 5 ^ m2 * u - 1)) =
        twoValuation (3 * 5 ^ m2 * u - 1) + 1 :=
      StringFlow.twoValuation_mul_two (3 * 5 ^ m2 * u - 1) hpos
    rw [← hL2, hv2] at hleft
    omega
  let w := StringFlow.oddPart (3 * 5 ^ m2 * u - 1)
  have hwodd : w % 2 = 1 :=
    StringFlow.oddPart_odd_of_pos (3 * 5 ^ m2 * u - 1) hpos
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (3 * 5 ^ m2 * u - 1) hpos
  have heq : 3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w := by
    dsimp [w]
    simp [hv] at hdec
    exact hdec
  have hdiv : 2 ^ (H_s - 1) ∣ 5 ^ ((L + m1) + 3) * w + 1 := by
    rcases hcong with ⟨k, hk⟩
    have hpow : 2 ^ ((L + m1) + H_s + 2) =
        2 ^ ((L + m1) + 3) * 2 ^ (H_s - 1) := by
      rw [show (L + m1) + H_s + 2 = ((L + m1) + 3) + (H_s - 1) by omega,
        Nat.pow_add]
    have hfact : 5 ^ ((L + m1) + 3) * (3 * 5 ^ m2 * u - 1) +
        2 ^ ((L + m1) + 3) = 2 ^ ((L + m1) + 3) *
          (5 ^ ((L + m1) + 3) * w + 1) := by
      rw [heq]
      ring
    have hk' : 2 ^ ((L + m1) + 3) * (5 ^ ((L + m1) + 3) * w + 1) =
        2 ^ ((L + m1) + 3) * 2 ^ (H_s - 1) * k := by
      rw [hfact] at hk
      rw [hpow] at hk
      exact hk
    have hk'' : 2 ^ ((L + m1) + 3) * (5 ^ ((L + m1) + 3) * w + 1) =
        2 ^ ((L + m1) + 3) * (2 ^ (H_s - 1) * k) := by
      simpa [Nat.mul_assoc] using hk'
    have hcancel := Nat.eq_of_mul_eq_mul_left
      (by positivity : 0 < 2 ^ ((L + m1) + 3)) hk''
    exact ⟨k, hcancel⟩
  exact ⟨r2, u, w, ht2, hstart, hstart_block, hL2, heq, hwodd, hdiv⟩

/-- Exact `m2=0` content of the tail failure: the block head has
`r + 1 = 2*u` with `u ≡ 3 (mod 8)`, hence `r ≡ 5 (mod 16)`.
This is the true residue forced by the single tail congruence; it is
incompatible with the document-36.30.6 residue `r ≡ 33 (mod 64)`. -/
lemma tail_failure_m2_zero_block_head_mod16
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n))
    (hm2 : m2 = 0)
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    r % 16 = 5 := by
  rcases tail_failure_odd_part_congruence j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2
    weight hPrem hn hm hH hfail with
    ⟨r2, u, w, ht2, hstart, hstart_block, hL2, hcong, hwodd, hdiv⟩
  have hstart' : blockState weight q (j + (n - m1 - m2)) + 1 = 2 * u := by
    rw [← hstart_block]
    simpa [hm2] using hstart
  have hstart_j : blockState weight q j + 1 = 2 * u := by
    rw [tail_start_eq_block_head_of_m2_zero j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2
      weight hPrem hn hm hm2] at hstart'
    exact hstart'
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def]
    exact hrj.symm
  have hr : r + 1 = 2 * u := by
    rw [← hbsj]
    exact hstart_j
  have hpow5 : 5 ^ m2 = 1 := by
    rw [hm2]
    simp
  have hcongu : 3 * u = 2 ^ ((L + m1) + 3) * w + 1 := by
    have h3 : 3 * 5 ^ m2 * u = 3 * u := by
      simp [hpow5]
    rw [h3] at hcong
    omega
  have hk : 3 ≤ (L + m1) + 3 := by omega
  have hdvd8 : 8 ∣ 2 ^ ((L + m1) + 3) := by
    have h := pow_dvd_pow 2 hk
    simpa using h
  have hdvd8w : 8 ∣ 2 ^ ((L + m1) + 3) * w := dvd_mul_of_dvd_left hdvd8 w
  have hmod3u : (3 * u) % 8 = 1 := by
    have hmodpow : (2 ^ ((L + m1) + 3) * w) % 8 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdvd8w
    rw [hcongu]
    rw [Nat.add_mod, hmodpow]
    try norm_num
  have hu8 : u % 8 = 3 := by
    have hmod : (3 * u) % 8 = (3 * (u % 8)) % 8 := by
      rw [Nat.mul_mod]
      try norm_num
    rw [hmod] at hmod3u
    have hlt8 : u % 8 < 8 := Nat.mod_lt u (by norm_num)
    interval_cases u % 8
    all_goals norm_num at hmod3u
    all_goals norm_num
  have h2u : (2 * u) % 16 = 6 := by
    have hmod : (2 * u) % 16 = (2 * (u % 16)) % 16 := by
      rw [Nat.mul_mod]
      try norm_num
    have hu16 : u % 16 = 3 ∨ u % 16 = 11 := by
      have hmm : u % 16 % 8 = u % 8 :=
        Nat.mod_mod_of_dvd u (c := 8) (b := 16) (by norm_num)
      rw [hu8] at hmm
      have hlt16 : u % 16 < 16 := Nat.mod_lt u (by norm_num)
      interval_cases u % 16
      all_goals norm_num at hmm
      all_goals norm_num
    rcases hu16 with h3 | h11
    · rw [hmod, h3]
      try norm_num
    · rw [hmod, h11]
      try norm_num
  have h16 : (r + 1) % 16 = 6 := by
    rw [hr, h2u]
  have hmod16 : r % 16 = 5 := by
    have hmod : (r + 1) % 16 = (r % 16 + 1) % 16 := by
      rw [Nat.add_mod]
      try norm_num
    rw [hmod] at h16
    have hlt16 : r % 16 < 16 := Nat.mod_lt r (by norm_num)
    interval_cases r % 16
    all_goals norm_num at h16
    all_goals norm_num
  exact hmod16

/-- The `m2=0` tail failure excludes the document-36.30.6 candidate
residue `r ≡ 33 (mod 64)`: the true tail congruence fixes `r ≡ 5 (mod 16)`. -/
lemma tail_failure_m2_zero_not_rj_mod64
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hn : n = s - j)
    (hm : (m1, m2) = tailSplit (blockWord weight j n))
    (hm2 : m2 = 0)
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ¬ r % 64 = 33 := by
  intro h33
  have h16 := tail_failure_m2_zero_block_head_mod16 j Wp Wj q Aj A_s s W_s r_s L H_s
    n m1 m2 weight r hPrem hrj hn hm hm2 hH hfail
  have hmm : r % 64 % 16 = r % 16 :=
    Nat.mod_mod_of_dvd r (c := 16) (b := 64) (by norm_num)
  rw [h33] at hmm
  norm_num at hmm
  omega

/-- Corrected predecessor residue, `t=1`: from `r % 16 = 5` and
`r = (5*x+1)/2`, the real-orbit predecessor is `x ≡ 21 (mod 32)`. -/
lemma predecessor_mod32_of_block_head_mod16_t1 (x r : Nat)
    (hr : r = (5 * x + 1) / 2)
    (hdiv : (5 * x + 1) % 2 = 0)
    (hr16 : r % 16 = 5) :
    x % 32 = 21 := by
  have hmul : 2 * r = 5 * x + 1 := by
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hrdec : r = 16 * (r / 16) + 5 := by
    have h := (Nat.div_add_mod r 16).symm
    rw [hr16] at h
    exact h
  have hmod : (5 * x + 1) % 32 = 10 := by
    rw [← hmul]
    rw [hrdec]
    ring_nf
    rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  have h5x : (5 * x) % 32 = 9 := by
    have hsum := Nat.add_mod (5 * x) 1 32
    rw [hmod] at hsum
    norm_num at hsum
    have hlt : (5 * x) % 32 < 32 := Nat.mod_lt (5 * x) (by norm_num)
    omega
  have hx : (5 * (x % 32)) % 32 = 9 := by
    simpa [Nat.mul_mod] using h5x
  have hlt : x % 32 < 32 := Nat.mod_lt x (by norm_num)
  interval_cases x % 32
  all_goals norm_num at hx
  all_goals norm_num

/-- Corrected predecessor residue, `t=2`: from `r % 16 = 5` and
`r = (5*x+1)/4`, the real-orbit predecessor is `x ≡ 55 (mod 64)`. -/
lemma predecessor_mod64_of_block_head_mod16_t2 (x r : Nat)
    (hr : r = (5 * x + 1) / 4)
    (hdiv : (5 * x + 1) % 4 = 0)
    (hr16 : r % 16 = 5) :
    x % 64 = 55 := by
  have hmul : 4 * r = 5 * x + 1 := by
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hrdec : r = 16 * (r / 16) + 5 := by
    have h := (Nat.div_add_mod r 16).symm
    rw [hr16] at h
    exact h
  have hmod : (5 * x + 1) % 64 = 20 := by
    rw [← hmul]
    rw [hrdec]
    ring_nf
    rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  have h5x : (5 * x) % 64 = 19 := by
    have hsum := Nat.add_mod (5 * x) 1 64
    rw [hmod] at hsum
    norm_num at hsum
    have hlt : (5 * x) % 64 < 64 := Nat.mod_lt (5 * x) (by norm_num)
    omega
  have hx : (5 * (x % 64)) % 64 = 19 := by
    simpa [Nat.mul_mod] using h5x
  have hlt : x % 64 < 64 := Nat.mod_lt x (by norm_num)
  interval_cases x % 64
  all_goals norm_num at hx
  all_goals norm_num

/-- The terminal failure congruence, cleared of the odd-part denominator:
`2^(H_s-1) | 5^(L+3)*w+1` iff
`2^(L+H_s+3) | 5^(L+3)*(3*r_s+1)+2^(L+4)`. -/
theorem failure_cleared_iff (L H_s r_s : Nat) (_hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1)) :
    2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 ↔
      2 ^ (L + H_s + 3) ∣ 5 ^ (L + 3) * (3 * r_s + 1) + 2 ^ (L + 4) := by
  let a := 5 ^ (L + 3)
  let w := wTerminal L r_s
  let v := L + 4
  let h := H_s - 1
  have hvw : 3 * r_s + 1 = 2 ^ v * w := by
    dsimp [v, w]
    exact wTerminal_mul_eq L r_s hL
  have hsum : v + h = L + H_s + 3 := by dsimp [v, h]; omega
  have hpow : 2 ^ (v + h) = 2 ^ v * 2 ^ h := by rw [Nat.pow_add]
  constructor
  · intro hd
    rcases hd with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hleft : 2 ^ (v + h) * m = 2 ^ v * (2 ^ h * m) := by
      rw [hpow]
      ring
    have hmain : a * (3 * r_s + 1) + 2 ^ v = 2 ^ (v + h) * m := by
      rw [hvw]
      dsimp [a]
      rw [hleft, ← hm]
      ring
    rw [hsum] at hmain
    exact hmain
  · intro hd
    rcases hd with ⟨m, hm⟩
    have hright : a * (3 * r_s + 1) + 2 ^ v = 2 ^ v * (a * w + 1) := by
      rw [hvw]
      dsimp [a]
      ring
    rw [hright] at hm
    rw [← hsum] at hm
    rw [hpow] at hm
    have hcancel : 2 ^ h * m = a * w + 1 := by
      apply Nat.eq_of_mul_eq_mul_left
        (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ v)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm.symm
    exact ⟨m, hcancel.symm⟩

/-- The terminal failure fixes the odd part modulo `2^(H_s-1)` to the
explicit representative `uResidue L (H_s-1)`. -/
lemma failure_w_congruence (L H_s r_s : Nat) (hH : 2 ≤ H_s)
    (_hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    wTerminal L r_s ≡ uResidue L (H_s - 1) [MOD 2 ^ (H_s - 1)] := by
  let a := 5 ^ (L + 3)
  let N := 2 ^ (H_s - 1)
  let w := wTerminal L r_s
  let w0 := uResidue L (H_s - 1)
  let raw := StringFlow.Word.invOdd a (H_s - 2)
  let inv := raw % N
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hodd : a % 2 = 1 := by
    dsimp [a]
    exact StringFlow.Lte.five_pow_odd (L + 3)
  have hspec := invOdd_mod_pow_spec a (H_s - 1) hodd (by omega)
  have hm1 : 1 % 2 ^ (H_s - 1) = 1 := by
    exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : H_s - 1 ≠ 0))
  have hinv : a * inv ≡ 1 [MOD N] := by
    dsimp [inv, N]
    rw [Nat.ModEq]
    have hsub : H_s - 1 - 1 = H_s - 2 := by omega
    simpa [hsub, hm1] using hspec
  have hfail' : a * w + 1 ≡ 0 [MOD N] := by
    rw [Nat.ModEq]
    dsimp [a, w, N]
    simpa using (Nat.dvd_iff_mod_eq_zero.mp hfail)
  have hsum : (a * w + 1) * inv ≡ 0 [MOD N] := by
    simpa using hfail'.mul_right inv
  have hcalc : (a * w + 1) * inv = a * (w * inv) + inv := by ring
  have hdist : (a * w + 1) * inv ≡ w + inv [MOD N] := by
    rw [hcalc]
    have hw : a * (w * inv) ≡ w [MOD N] := by
      have h := hinv.mul_left w
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    exact hw.add_right inv
  have hwinv : w + inv ≡ 0 [MOD N] := hdist.symm.trans hsum
  have hspec0 := negResidue_spec raw N hNpos
  have hw0inv : w0 + inv ≡ 0 [MOD N] := by
    rw [Nat.ModEq]
    dsimp [w0, uResidue, raw, inv, N, a]
    have hsub : H_s - 1 - 1 = H_s - 2 := by omega
    rw [hsub]
    have hmod : raw % N % N = raw % N := Nat.mod_eq_of_lt (Nat.mod_lt raw hNpos)
    simpa [hmod, a, N, raw, inv] using hspec0
  have hw : w ≡ w0 [MOD N] := by
    have h1 : w + inv ≡ w0 + inv [MOD N] := hwinv.trans hw0inv.symm
    exact Nat.ModEq.add_right_cancel' inv h1
  simpa [w, w0] using hw

/-- The terminal failure writes the odd part as
`w = uResidue L (H_s-1) + k*2^(H_s-1)`. -/
lemma failure_w_progression (L H_s r_s : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ∃ k : Nat,
      wTerminal L r_s = uResidue L (H_s - 1) + k * 2 ^ (H_s - 1) := by
  let N := 2 ^ (H_s - 1)
  let w := wTerminal L r_s
  let w0 := uResidue L (H_s - 1)
  have hw := failure_w_congruence L H_s r_s hH hL hfail
  have hw0lt : w0 < N := by
    dsimp [w0, N]
    exact uResidue_lt_pow L (H_s - 1)
  have hwmod : w % N = w0 := by
    have hmod := hw
    change w % N = w0 % N at hmod
    have hw0mod : w0 % N = w0 := Nat.mod_eq_of_lt hw0lt
    rw [hw0mod] at hmod
    exact hmod
  have hdiv := Nat.div_add_mod w N
  have hk : w = w0 + (w / N) * N := by
    calc
      w = N * (w / N) + w % N := hdiv.symm
      _ = w0 + (w / N) * N := by
        rw [hwmod]
        ring
  refine ⟨w / N, ?_⟩
  dsimp [w, w0, N]
  exact hk

/-- The terminal failure puts `r_s` in the document-36.23 arithmetic
progression: `3*r_s+1 = 2^(L+4)*(uResidue + k*2^(H_s-1))`. -/
lemma failure_rs_progression
    (L H_s r_s : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ∃ k : Nat,
      3 * r_s + 1 =
        2 ^ (L + 4) * (uResidue L (H_s - 1) + k * 2 ^ (H_s - 1)) := by
  rcases failure_w_progression L H_s r_s hH hL hfail with ⟨k, hk⟩
  have hmul := wTerminal_mul_eq L r_s hL
  refine ⟨k, ?_⟩
  rw [hmul, hk]

/-- Under terminal failure, the actual block head `r` satisfies the
document-36.26 exact equation (with the same `k` from the progression). -/
lemma failure_rj_satisfies_exact_equation
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hH : 2 ≤ H_s) (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    ∃ k : Nat,
      3 * 5 ^ (s - j) * r + 3 * blockB weight j (s - j) + 2 ^ (W_s - Wj) =
        2 ^ (W_s - Wj + L + 4) *
          (uResidue L (H_s - 1) + k * 2 ^ (H_s - 1)) := by
  rcases failure_rs_progression L H_s r_s hH hL hfail with ⟨k, hprog⟩
  have htail := block_tail_equation_of_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj
  let n := s - j
  let Δ := W_s - Wj
  let u := uResidue L (H_s - 1)
  let N := 2 ^ (H_s - 1)
  have hprog' : 3 * r_s + 1 = 2 ^ (L + 4) * (u + k * N) := by
    dsimp [u, N]
    exact hprog
  have h3r : 3 * r_s = 2 ^ (L + 4) * (u + k * N) - 1 := by
    have hXpos : 1 ≤ 2 ^ (L + 4) * (u + k * N) := by omega
    omega
  have htail3 : 2 ^ Δ * (3 * r_s) =
      3 * 5 ^ n * r + 3 * blockB weight j n := by
    dsimp [n, Δ]
    have hdist3 : 2 ^ Δ * (3 * r_s) = 3 * (2 ^ Δ * r_s) := by ring
    rw [hdist3]
    nlinarith [htail]
  have hsub : 2 ^ Δ * (2 ^ (L + 4) * (u + k * N) - 1) =
      2 ^ Δ * (2 ^ (L + 4) * (u + k * N)) - 2 ^ Δ := by
    rw [Nat.mul_sub_left_distrib]
    simp
  rw [h3r] at htail3
  rw [hsub] at htail3
  have hle : 2 ^ Δ ≤ 2 ^ Δ * (2 ^ (L + 4) * (u + k * N)) := by
    have hpos : 0 < 2 ^ (L + 4) * (u + k * N) := by omega
    have h := Nat.le_mul_of_pos_left (2 ^ Δ) hpos
    simpa [Nat.mul_comm] using h
  have htarget : 2 ^ Δ * (2 ^ (L + 4) * (u + k * N)) =
      3 * 5 ^ n * r + 3 * blockB weight j n + 2 ^ Δ := by
    omega
  have hpow : 2 ^ Δ * 2 ^ (L + 4) = 2 ^ (Δ + L + 4) := by
    rw [← Nat.pow_add]
    rw [show Δ + (L + 4) = Δ + L + 4 by omega]
  have hA : 2 ^ Δ * (2 ^ (L + 4) * (u + k * N)) =
      2 ^ (Δ + L + 4) * (u + k * N) := by
    rw [← Nat.mul_assoc, hpow]
  rw [hA] at htarget
  refine ⟨k, ?_⟩
  simpa [n, Δ, u, N] using htarget.symm

/-- Failure of the terminal inequality bounds the true block head by the
least nonnegative solution: `rj0 ≤ r`. -/
theorem rj0_le_of_failure_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≤ r := by
  have hrmod := block_head_mod_five_congruence_of_premises j Wp Wj q Aj A_s s W_s r_s
    L H_s weight r hPrem hrj hReach
  rcases failure_rj_satisfies_exact_equation j Wp Wj q Aj A_s s W_s r_s L H_s weight r
    hPrem hrj hH hL hfail with ⟨k, heq⟩
  exact rj0_le_of_exact_equation j Wp Wj q Aj A_s s W_s r_s L H_s weight r k
    (by omega) hrmod heq

/-- Under failure, the least solution stays below the block-head bound. -/
theorem rj0_lt_five_pow_of_failure_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight < 5 ^ j := by
  have hle := rj0_le_of_failure_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
    hPrem hrj hReach hH hL hfail
  have hrlt : r < 5 ^ j := by
    simpa [hrj] using hPrem.r_j_lt
  exact lt_of_le_of_lt hle hrlt

/-- The final valuation inequality follows once `5^j ≤ rj0` is available. -/
theorem terminal_bound_of_rj0_lower
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hrj0 : 5 ^ j ≤ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  by_contra hnot
  have hpos : 0 < 5 ^ (L + 3) * wTerminal L r_s + 1 := by positivity
  have hlt : H_s - 2 < twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) :=
    not_le.mp hnot
  have hge : H_s - 1 ≤ twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) := by
    omega
  have hdvd : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 ^ (L + 3) * wTerminal L r_s + 1) (H_s - 1) hpos).mp hge
  have hlt0 := rj0_lt_five_pow_of_failure_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s
    weight r hPrem hrj hReach hH hL hdvd
  omega

/-- The terminal failure pins the cleared numerator
`3*r_s+1` modulo `2^(L+H_s+3)`. -/
lemma failure_rs_cleared_congruence
    (L H_s r_s : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1) :
    3 * r_s + 1 ≡ 2 ^ (L + 4) * uResidue L (H_s - 1)
      [MOD 2 ^ (L + H_s + 3)] := by
  let v := L + 4
  let N := 2 ^ (H_s - 1)
  have hw := failure_w_congruence L H_s r_s hH hL hfail
  have hwmod : wTerminal L r_s % N = uResidue L (H_s - 1) % N := hw
  have hmulw : (2 ^ v * wTerminal L r_s) % (2 ^ v * N) =
      2 ^ v * (wTerminal L r_s % N) :=
    Nat.mul_mod_mul_left (2 ^ v) (wTerminal L r_s) N
  have hmulw0 : (2 ^ v * uResidue L (H_s - 1)) % (2 ^ v * N) =
      2 ^ v * (uResidue L (H_s - 1) % N) :=
    Nat.mul_mod_mul_left (2 ^ v) (uResidue L (H_s - 1)) N
  have hcong : 2 ^ v * wTerminal L r_s ≡ 2 ^ v * uResidue L (H_s - 1)
      [MOD 2 ^ v * N] := by
    rw [Nat.ModEq]
    rw [hmulw, hmulw0, hwmod]
  have hmul := wTerminal_mul_eq L r_s hL
  have hmain : 3 * r_s + 1 ≡ 2 ^ v * uResidue L (H_s - 1)
      [MOD 2 ^ v * N] := by
    simpa [v, hmul.symm] using hcong
  have hmodulus : 2 ^ v * N = 2 ^ (L + H_s + 3) := by
    dsimp [v, N]
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hmodulus] at hmain
  simpa [v] using hmain

/-- Since `3` is a unit modulo `2^k`, the `+1` can be cancelled from
`3*a+1 ≡ 3*b+1`. -/
lemma three_cancel_modEq (k a b : Nat)
    (h : 3 * a + 1 ≡ 3 * b + 1 [MOD 2 ^ k]) :
    a ≡ b [MOD 2 ^ k] := by
  by_cases hk : 1 ≤ k
  · let M := 2 ^ k
    have hodd : (3 : Nat) % 2 = 1 := by norm_num
    have hspec := invOdd_mod_pow_spec 3 k hodd hk
    have hmod1 : 1 % 2 ^ k = 1 := by
      exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : k ≠ 0))
    let inv := StringFlow.Word.invOdd 3 (k - 1) % M
    have hinv : 3 * inv ≡ 1 [MOD M] := by
      dsimp [inv, M]
      rw [Nat.ModEq]
      simpa [hmod1] using hspec
    have hcancel1 : 3 * a ≡ 3 * b [MOD M] := Nat.ModEq.add_right_cancel' 1 h
    have hmul : (3 * a) * inv ≡ (3 * b) * inv [MOD M] := hcancel1.mul_right inv
    have hleft : (3 * a) * inv ≡ a [MOD M] := by
      have h' := hinv.mul_left a
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
    have hright : (3 * b) * inv ≡ b [MOD M] := by
      have h' := hinv.mul_left b
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h'
    simpa [M] using (hleft.symm.trans (hmul.trans hright))
  · have hmod : a ≡ b [MOD 1] := by
      rw [Nat.ModEq]
      simp [Nat.mod_one]
    have hk0 : k = 0 := by omega
    subst k
    exact hmod

/-- Any two terminal failures give the same `r_s` class modulo
`2^(L+H_s+3)`: the candidate family is a single residue class. -/
lemma failure_rs_unique
    (L H_s r_s r_s' : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hL' : L + 4 = twoValuation (3 * r_s' + 1))
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1)
    (hfail' : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s' + 1) :
    r_s ≡ r_s' [MOD 2 ^ (L + H_s + 3)] := by
  have h1 := failure_rs_cleared_congruence L H_s r_s hH hL hfail
  have h2 := failure_rs_cleared_congruence L H_s r_s' hH hL' hfail'
  have h3 : 3 * r_s + 1 ≡ 3 * r_s' + 1 [MOD 2 ^ (L + H_s + 3)] :=
    h1.trans h2.symm
  exact three_cancel_modEq (L + H_s + 3) r_s r_s' h3

/-- The `y*` residue of document 36.18, written as the least nonnegative
representative of `-(w + 5^(-(L+3))) * (3*5^s)^(-1)` modulo `2^(H_s-1)`. -/
def yStar (L H_s s r_s : Nat) : Nat :=
  negResidue
    ((wTerminal L r_s +
        StringFlow.Word.invOdd (5 ^ (L + 3)) (H_s - 2) % 2 ^ (H_s - 1)) *
      (StringFlow.Word.invOdd (3 * 5 ^ s) (H_s - 2) % 2 ^ (H_s - 1)))
    (2 ^ (H_s - 1))

/-- `y* = 0` iff the failure congruence `5^(L+3)*w ≡ -1` holds modulo
`2^(H_s-1)`.  This is the exact equivalence used in document 36.20. -/
theorem yStar_eq_zero_iff_congruence (L H_s s r_s : Nat) (hH : 2 ≤ H_s) :
    yStar L H_s s r_s = 0 ↔
      2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 := by
  let m := 2 ^ (H_s - 1)
  let a := 5 ^ (L + 3)
  let b := 3 * 5 ^ s
  let w := wTerminal L r_s
  let i5 := StringFlow.Word.invOdd a (H_s - 2) % m
  let i35 := StringFlow.Word.invOdd b (H_s - 2) % m
  have hm : 0 < m := by dsimp [m]; positivity
  have hi5 : a * i5 ≡ 1 [MOD m] := by
    have hodd : a % 2 = 1 := by
      dsimp [a]
      exact StringFlow.Lte.five_pow_odd (L + 3)
    have hspec := invOdd_mod_pow_spec a (H_s - 1) hodd (by omega)
    have hm1 : 1 % 2 ^ (H_s - 1) = 1 := by
      exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : H_s - 1 ≠ 0))
    have hsub : H_s - 1 - 1 = H_s - 2 := by omega
    rw [Nat.ModEq]
    dsimp [i5, m]
    simpa [hm1, hsub] using hspec
  have hi35 : b * i35 ≡ 1 [MOD m] := by
    have hodd : b % 2 = 1 := by
      dsimp [b]
      rw [Nat.mul_mod]
      have h5 : (5 ^ s) % 2 = 1 := StringFlow.Lte.five_pow_odd s
      simp [h5]
    have hspec := invOdd_mod_pow_spec b (H_s - 1) hodd (by omega)
    have hm1 : 1 % 2 ^ (H_s - 1) = 1 := by
      exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : H_s - 1 ≠ 0))
    have hsub : H_s - 1 - 1 = H_s - 2 := by omega
    rw [Nat.ModEq]
    dsimp [i35, m]
    simpa [hm1, hsub] using hspec
  rw [yStar]
  rw [negResidue_eq_zero_iff_dvd _ m hm]
  calc
    m ∣ (w + i5) * i35 ↔ m ∣ w + i5 :=
      dvd_mul_unit_iff m (w + i5) i35 b (by simpa [Nat.mul_comm] using hi35)
    _ ↔ m ∣ (w + i5) * a :=
      (dvd_mul_unit_iff m (w + i5) a i5 (by simpa [Nat.mul_comm] using hi5)).symm
    _ ↔ m ∣ a * w + a * i5 := by
      have hcalc : (w + i5) * a = a * w + a * i5 := by ring
      have hcong : (w + i5) * a ≡ a * w + a * i5 [MOD m] := by
        rw [hcalc]
      exact dvd_modEq_iff m ((w + i5) * a) (a * w + a * i5) hcong
    _ ↔ m ∣ a * w + 1 := by
      have hcong : a * w + a * i5 ≡ a * w + 1 [MOD m] :=
        hi5.add_left (a * w)
      exact dvd_modEq_iff m (a * w + a * i5) (a * w + 1) hcong

/-- The document-36.20 terminal inequality is equivalent to the failure
congruence not holding, i.e. to `y* != 0`.  This step uses the standard
valuation lemma `twoValuation_le_iff_not_dvd_pow`; it needs no `H_ge`. -/
theorem terminal_bound_iff_not_dvd (L H_s r_s : Nat) (hH : 2 ≤ H_s) :
    twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 ↔
      ¬ 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 := by
  have hpos : 0 < 5 ^ (L + 3) * wTerminal L r_s + 1 := by positivity
  have h := StringFlow.Lte.twoValuation_le_iff_not_dvd_pow
    (5 ^ (L + 3) * wTerminal L r_s + 1) (H_s - 2) hpos
  have hsucc : (H_s - 2) + 1 = H_s - 1 := by omega
  rwa [hsucc] at h

/-- Document 36.20: the terminal inequality holds iff `y* != 0`.  This
is the exact composition of `terminal_bound_iff_not_dvd` and
`yStar_eq_zero_iff_congruence`. -/
theorem terminal_bound_iff_yStar_ne_zero (L H_s s r_s : Nat) (hH : 2 ≤ H_s) :
    (twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2) ↔
      yStar L H_s s r_s ≠ 0 := by
  rw [terminal_bound_iff_not_dvd L H_s r_s hH]
  rw [← yStar_eq_zero_iff_congruence L H_s s r_s hH]

/-- `y*=0` puts `3*r_s+1` in the candidate class modulo
`2^(L+H_s+3)`. -/
lemma yStar_zero_implies_rs_candidate_class
    (L H_s s r_s : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hy : yStar L H_s s r_s = 0) :
    3 * r_s + 1 ≡ 2 ^ (L + 4) * uResidue L (H_s - 1)
      [MOD 2 ^ (L + H_s + 3)] := by
  have hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 :=
    (yStar_eq_zero_iff_congruence L H_s s r_s hH).mp hy
  exact failure_rs_cleared_congruence L H_s r_s hH hL hfail

/-- Failure of the terminal inequality puts `3*r_s+1` in the same
candidate class. -/
lemma terminal_failure_implies_candidate_class
    (L H_s _s r_s : Nat) (hH : 2 ≤ H_s)
    (hL : L + 4 = twoValuation (3 * r_s + 1))
    (hfail : ¬ twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2) :
    3 * r_s + 1 ≡ 2 ^ (L + 4) * uResidue L (H_s - 1)
      [MOD 2 ^ (L + H_s + 3)] := by
  have hpos : 0 < 5 ^ (L + 3) * wTerminal L r_s + 1 := by positivity
  have hlt : H_s - 2 < twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) :=
    not_le.mp hfail
  have hge : H_s - 1 ≤ twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) := by
    omega
  have hdvd : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * wTerminal L r_s + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 ^ (L + 3) * wTerminal L r_s + 1) (H_s - 1) hpos).mp hge
  exact failure_rs_cleared_congruence L H_s r_s hH hL hdvd

/-- (B1) without `H_ge`: the block tail bound
`3B + 2^Delta <= 3*5^n - 2*4^n`. -/
theorem blockB_bound_of_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    3 * blockB weight j (s - j) + 2 ^ (W_s - Wj) ≤
      3 * 5 ^ (s - j) - 2 * 4 ^ (s - j) := by
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hdiff : W_s - Wj ≤ 2 * (s - j) := by
    have hd := weight_diff_le_two_mul weight j (s - j) hstep
    simpa [hsum, hPrem.Ws_def, hPrem.Wj_def] using hd
  exact three_blockB_add_two_pow_le weight j (s - j) (W_s - Wj) hstep hdiff

/-- The sufficient size direction of item 7: under `All36_20PremisesNoHge`,
the two inverse-size conditions (B2)/(B3) together with (B1) imply
`rj0 >= 5^j`.  This wraps `S6Audit.rj0_ge_of_size_bounds`; the converse
and the full iff remain part of the open core. -/
theorem rj0_ge_of_size_conditions_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hH : 1 ≤ H_s)
    (hBase2 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1))
    (hPow3 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + H_s + 3)) :
    5 ^ j ≤ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
  exact rj0_ge_of_size_bounds j Wp Wj q Aj A_s s W_s r_s L H_s weight
    hPrem.j_le_s hH
    (blockB_bound_of_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem)
    hBase2 hPow3

lemma concat_word_eq_path_of_rs229_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r)
    (hrs : r_s = 229) :
    ∃ w : List Nat,
      (∀ t ∈ w, t = 1 ∨ t = 2) ∧
      w ++ blockWord weight j (s - j) = [2, 1, 2, 1, 1, 2] := by
  rcases hReach with ⟨w, hokw, hvalidw, horbitw⟩
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hvalid : ∀ k, k ≤ j + (s - j) →
      (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
    intro k hk
    have hks : k ≤ s := by omega
    exact hPrem.valid_prefix k hks
  have hbw := blockWord_valid weight q j (s - j) hstep hvalid
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def, hPrem.r_s_eq]
  have hwv : StringFlow.Word.wordValid (blockWord weight j (s - j)) r := by
    rw [← hbsj]
    exact hbw.1
  have hwo : StringFlow.Word.wordOrbit (blockWord weight j (s - j)) r = r_s := by
    rw [← hbsj, ← hbss]
    have hbw2 : StringFlow.Word.wordOrbit (blockWord weight j (s - j))
        (blockState weight q j) = blockState weight q (j + (s - j)) := hbw.2
    simpa [hsum] using hbw2
  have hok_block : ∀ t ∈ blockWord weight j (s - j), t = 1 ∨ t = 2 :=
    blockWord_mem weight j (s - j) hstep
  have hok_all : ∀ t ∈ w ++ blockWord weight j (s - j), t = 1 ∨ t = 2 := by
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact hokw t ht
    · exact hok_block t ht
  have hvalid_all : StringFlow.Word.wordValid
      (w ++ blockWord weight j (s - j)) 7 := by
    rw [wordValid_append]
    rw [horbitw]
    exact ⟨hvalidw, hwv⟩
  have horbit_all : StringFlow.Word.wordOrbit
      (w ++ blockWord weight j (s - j)) 7 = 229 := by
    rw [wordOrbit_append, horbitw, hwo, hrs]
  have hunique := path229_unique (w ++ blockWord weight j (s - j))
    hok_all hvalid_all horbit_all
  exact ⟨w, hokw, hunique⟩

lemma bad_2112_false_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [2, 1, 1, 2])
    (hs : s = 6) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 4 := by
    rw [hblock]; simp
  have hsj : s - j = 4 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_2112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6⟩
  have hmono : ∀ k, k < 6 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 4 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 6 := by omega
  have hW6 : weight 6 = Wp + 8 := by omega
  have hnot := bad_suffix_2112_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 6 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 6 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 6 * q = 2 ^ W_s * ((A_s + 5 ^ 6 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 6 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 6 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 6 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 8 := by
    rw [hPrem.Ws_def]
    exact hW6
  have hA : A_s = wordMolecule weight 6 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

lemma bad_12112_false_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [1, 2, 1, 1, 2])
    (hs : s = 7) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 5 := by
    rw [hblock]; simp
  have hsj : s - j = 5 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_12112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6, h7⟩
  have hmono : ∀ k, k < 7 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 3 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 6 := by omega
  have hW6 : weight 6 = Wp + 7 := by omega
  have hW7 : weight 7 = Wp + 9 := by omega
  have hnot := bad_suffix_12112_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hW6 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 7 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 7 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 7 * q = 2 ^ W_s * ((A_s + 5 ^ 7 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 7 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 7 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 7 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 9 := by
    rw [hPrem.Ws_def]
    exact hW7
  have hA : A_s = wordMolecule weight 7 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

/-- The pseudo-candidate `[2,1,2,1,1,2]` (`s=8`, `Wj-Wp=2`) cannot
satisfy the integrality equation for `r_s=229`. -/
lemma bad_suffix_full_no_div (weight : Nat → Nat) (Wp : Nat)
    (hW0 : weight 0 = 0) (hW1 : weight 1 = Wp)
    (hW2 : weight 2 = Wp + 2) (hW3 : weight 3 = Wp + 4)
    (hW4 : weight 4 = Wp + 5) (hW5 : weight 5 = Wp + 7)
    (hW6 : weight 6 = Wp + 8) (hW7 : weight 7 = Wp + 9)
    (hWp : Wp = 1 ∨ Wp = 2) :
    ¬ 5 ^ 8 ∣ 229 * 2 ^ (Wp + 11) - wordMolecule weight 8 := by
  rcases hWp with rfl | rfl
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6, hW7]
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6, hW7]

lemma bad_full_false_of_premises_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [2, 1, 2, 1, 1, 2])
    (hs : s = 8) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 6 := by
    rw [hblock]; simp
  have hsj : s - j = 6 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_212112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6, h7, h8⟩
  have hmono : ∀ k, k < 8 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 4 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 7 := by omega
  have hW6 : weight 6 = Wp + 8 := by omega
  have hW7 : weight 7 = Wp + 9 := by omega
  have hW8 : weight 8 = Wp + 11 := by omega
  have hnot := bad_suffix_full_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hW6 hW7 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 8 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 8 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 8 * q = 2 ^ W_s * ((A_s + 5 ^ 8 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 8 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 8 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 8 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 11 := by
    rw [hPrem.Ws_def]
    exact hW8
  have hA : A_s = wordMolecule weight 8 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

theorem local_lemma_final_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hH : 2 ≤ H_s)
    (hReach : OrbitFrom7 r) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≥ 5 ^ j := by
  let sfx := blockWord weight j (s - j)
  let e := Wj - Wp
  have hj_le_s : j ≤ s := hPrem.j_le_s
  have hrs : r_s = 229 :=
    r_s_eq_229_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  have hs9 : s ≤ 9 :=
    s_le_9_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach hH
  have hL0 : L = 0 := by
    have h := hPrem.L_val
    rw [hrs] at h
    simp [StringFlow.twoValuation_succ] at h
    omega
  rcases concat_word_eq_path_of_rs229_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs with ⟨w, hokw, hconcat⟩
  have hsfx : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                     [1,2,1,1,2], [2,1,2,1,1,2]] := by
    dsimp [sfx]
    exact suffix_of_path229 w (blockWord weight j (s - j)) hconcat hokw
      (blockWord_mem weight j (s - j) (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks))
  have hs_len : sfx.length + 1 ≤ s := by
    dsimp [sfx]
    rw [blockWord_length]
    have hpos : 1 ≤ j := hPrem.j_pos
    omega
  have he : e = 1 ∨ e = 2 := by
    have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
    dsimp [e]
    rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hD : W_s - Wj = sumSuffix sfx := by
    dsimp [sfx]
    have h := blockWord_sum weight j (s - j) (by
      intro k hk
      have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
      have hks : k < s := by omega
      rcases hPrem.weight_step k hks with h1 | h2 <;> omega)
    have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    rw [hsum, ← hPrem.Ws_def, ← hPrem.Wj_def] at h
    exact h.symm
  have hn : s - j = sfx.length := by
    dsimp [sfx]
    exact (blockWord_length weight j (s - j)).symm
  have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hWsWp : W_s - Wp = e + sumSuffix sfx := by
    dsimp [e]
    have hWj_le_Ws : Wj ≤ W_s := hPrem.Wj_le_Ws
    omega
  have hHdef : H_s = 2 * s + 13 - 2 * (sumSuffix sfx + e) := by
    rw [hPrem.H_def]
    rw [hWsWp]
    simp [Nat.add_comm]
  have hj_eq : s - sfx.length = j := by
    dsimp [sfx]
    rw [blockWord_length]
    omega
  have hWpB : let jj := s - sfx.length; jj - 1 ≤ Wp ∧ Wp ≤ 2 * (jj - 1) := by
    dsimp
    rw [hj_eq]
    constructor
    · rw [hPrem.Wp_def]
      have hge := weight_ge weight (j - 1) hPrem.W0_def (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks)
      exact hge
    · rw [hPrem.Wp_def]
      have hle := weight_diff_le_two_mul weight 0 (j - 1) (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks)
      simpa [hPrem.W0_def] using hle
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ s * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ s * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ s * q = 2 ^ W_s * ((A_s + 5 ^ s * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ s * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hq1 : 5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) := by
    have hqge : 2 ^ Wp ≤ q := hPrem.q_ge
    have hle : 5 ^ s * 2 ^ Wp ≤ 229 * 2 ^ W_s := by
      have h2 : 5 ^ s * 2 ^ Wp ≤ A_s + 5 ^ s * q := by
        have h1 : 5 ^ s * 2 ^ Wp ≤ 5 ^ s * q := Nat.mul_le_mul_left (5 ^ s) hqge
        omega
      rw [← h229] at h2
      exact h2
    have hWp_le_Ws : Wp ≤ W_s := by
      have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
      exact le_trans hWp_le_Wj hPrem.Wj_le_Ws
    have hWs : W_s = Wp + (W_s - Wp) := by omega
    have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
      conv_lhs => rw [hWs]
      rw [Nat.pow_add]
    have hle' : 5 ^ s * 2 ^ Wp ≤ 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) := by
      rwa [hpowWs] at hle
    have hcancel : 5 ^ s ≤ 229 * 2 ^ (W_s - Wp) := by
      have hle2 : 5 ^ s * 2 ^ Wp ≤ (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle'
      exact Nat.le_of_mul_le_mul_right hle2 (Nat.pow_pos (by decide : 0 < 2))
    rwa [hWsWp] at hcancel
  have hq2 : 229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) := by
    have hqlt : q < 2 ^ Wj := hPrem.q_lt
    have hlt : 229 * 2 ^ W_s < A_s + 5 ^ s * 2 ^ Wj := by
      have h1 : 5 ^ s * q < 5 ^ s * 2 ^ Wj :=
        (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < 5))).2 hqlt
      rw [h229]
      exact Nat.add_lt_add_left h1 A_s
    have hlt2 : A_s + 5 ^ s * 2 ^ Wj < 5 ^ s * (1 + 2 ^ Wj) := by
      have hA : A_s < 5 ^ s := hPrem.A_s_lt
      have hlt' : A_s + 5 ^ s * 2 ^ Wj < 5 ^ s + 5 ^ s * 2 ^ Wj :=
        Nat.add_lt_add_right hA (5 ^ s * 2 ^ Wj)
      simpa [Nat.mul_add, Nat.mul_one] using hlt'
    have hlt3 : 229 * 2 ^ W_s < 5 ^ s * (1 + 2 ^ Wj) := lt_trans hlt hlt2
    have hWj_eq : Wj = Wp + e := by
      dsimp [e]
      rcases hPrem.tj_mem with h1 | h2 <;> omega
    have hle : 1 + 2 ^ Wj ≤ (2 ^ e + 1) * 2 ^ Wp := by
      have hpowWj : 2 ^ Wj = 2 ^ e * 2 ^ Wp := by
        rw [hWj_eq, Nat.pow_add, Nat.mul_comm]
      rw [hpowWj]
      have hWp_ge1 : 1 ≤ 2 ^ Wp := Nat.one_le_pow Wp 2 (by omega)
      nlinarith
    have hlt4 : 229 * 2 ^ W_s < 5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) :=
      lt_of_lt_of_le hlt3 (Nat.mul_le_mul_left (5 ^ s) hle)
    have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
      have hWs : W_s = Wp + (W_s - Wp) := by
        have hWp_le_Ws : Wp ≤ W_s := by
          have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
          exact le_trans hWp_le_Wj hPrem.Wj_le_Ws
        omega
      conv_lhs => rw [hWs]
      rw [Nat.pow_add]
    have hlt5 : 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) <
        5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) := by
      simpa [hpowWs] using hlt4
    have hleft : 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) =
        (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by ring
    have hright : 5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) =
        (5 ^ s * (2 ^ e + 1)) * 2 ^ Wp := by ring
    rw [hleft, hright] at hlt5
    have hlt6 : 229 * 2 ^ (W_s - Wp) < 5 ^ s * (2 ^ e + 1) := by
      exact Nat.lt_of_mul_lt_mul_right hlt5
    rwa [hWsWp] at hlt6
  have hbad1 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs6, he2, hWp1⟩
    exact bad_2112_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs6 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad2 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs6, he2, hWp2⟩
    exact bad_2112_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs6 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hbad3 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs7, he2, hWp1⟩
    exact bad_12112_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs7 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad4 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs7, he2, hWp2⟩
    exact bad_12112_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs7 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hbad5 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs8, he2, hWp1⟩
    exact bad_full_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs8 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad6 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs8, he2, hWp2⟩
    exact bad_full_false_of_premises_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs8 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hB2 : 3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (sumSuffix sfx + 4) *
        uResidue 0 (2 * s + 13 - 2 * (sumSuffix sfx + e) - 1) := by
    exact b2_of_suffix_qbound_nonbad sfx s e Wp hsfx hs_len hs9 he hWpB hq1 hq2
      hbad1 hbad2 hbad3 hbad4 hbad5 hbad6
  have hH1 : 1 ≤ H_s := by
    have h := hH
    omega
  have hB3 : 3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (sumSuffix sfx + H_s + 3) :=
    b2_imp_b3 s sfx.length (sumSuffix sfx) H_s hH1 (by
      rw [hHdef]
      exact hB2)
  have hBase2 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1) := by
    rw [hL0, hn, hD, hHdef]
    simpa [Nat.add_assoc] using hB2
  have hPow3 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + H_s + 3) := by
    rw [hL0, hn, hD]
    simpa [Nat.add_assoc] using hB3
  exact rj0_ge_of_size_conditions_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem (by omega) hBase2 hPow3

/-- The finite-prefix branch of the final core: depth `≤15` is closed by
the orbit25 base. -/
theorem unified_core_final_no_hge_le15
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (hH : 2 ≤ H_s)
    (hshort : ∃ n : Nat, S6Audit.fullOrbitIter n = r ∧ n ≤ 15) :
    twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  rcases hshort with ⟨n, hn, hnle⟩
  have hOrbit : S6Audit.OrbitFrom7 r := by
    rw [← hn]
    exact S6Audit.fullOrbitPrefix_imp_OrbitFrom7 n hnle
  have hge0 : 5 ^ j ≤ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight :=
    local_lemma_final_no_hge j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hH hOrbit
  exact terminal_bound_of_rj0_lower j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach hH hPrem.L_val hge0

/--
The final open core: document 36.20 terminal inequality

    v2(5^(L+3) * ((3*r_s+1)/2^(L+4)) + 1) <= H_s - 2

under `All36_20PremisesNoHge` (no `H_ge` input) and with the explicit
block-head reachability `FullOrbitFrom7 r`, where
`r = (Aj + 5^j*q)/2^Wj`.  `FullOrbitFrom7` is the real accelerated 7
orbit, not `GeneralOrbitFrom7` and not mere legal-word membership.
The premise `2 <= H_s` is a domain condition needed for `H_s - 1` to be a
valid modulus; it is not the forbidden `H_ge` input.  This is the unique
`sorry` in this audit file.

The stated bridge `failure_implies_rj_mod_64` is invalid: the tail
congruence (with `m2=0`) gives `r % 16 = 5`, hence `r % 64 = 33` is
impossible (`tail_failure_m2_zero_block_head_mod16` and
`tail_failure_m2_zero_not_rj_mod64` above).  The document-36.30.6
residue is therefore not a consequence of the terminal failure; the
`d=1/2/3/≥4` candidate exclusions do not attach to this tail branch as
stated.  The unique `sorry` remains the depth-`≥16` branch of
`unified_core_final_no_hge`; closing it needs a different orbit
constraint, not the candidate-residue bridge.

PMI audit (2026-08-13): the prefix identity
`sum 2^(-m_k) = 5*A_N/5^N` is covered for arbitrary words by
`StringFlow.PMI.aTotal5_eq_five_mul_aTotal`,
`StringFlow.PH.localLambda_eq_pmi_aTotal` and
`StringFlow.SurvEx.wordA_eq_localLambda`; the `cycleWord_*` theorems are
closed-cycle specializations and require `hclosed`.  The remaining open
steps are L1 (an absolute bound on the excess depth `n_j - j`) and L2 (an
independent upper bound on `2^(W_(N-1))*(125*x+39)` or `*(125*x+53)`);
neither is encoded as a Lean theorem here.
-/
theorem unified_core_final_no_hge
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : S6Audit.FullOrbitFrom7 r)
    (hH : 2 ≤ H_s) :
    twoValuation (5 ^ (L + 3) * wTerminal L r_s + 1) ≤ H_s - 2 := by
  rcases hReach with ⟨n, hn⟩
  by_cases hn15 : n ≤ 15
  · exact unified_core_final_no_hge_le15 j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj ⟨n, hn⟩ hH ⟨n, hn, hn15⟩
  · sorry

/-!
# Status table

| Step | Status | Note |
|---|---|---|
| `unified_core_t2` / `unified_core_local` | defined | two stated forms; the document's `X_i` is explicit here |
| `All36_20PremisesNoHge` | encoded | `H_ge` removed, all other 36.20 fields explicit |
| `premises_of_no_hge` / `no_hge_of_premises` | proved | conversion between no-`H_ge` and full premises |
| `block_head_bound_of_no_hge` | proved | `0 <= (Aj+5^j q)/2^Wj < 5^j`; the `0 <=` half is automatic |
| `H_ge_iff_capacity` | proved | with missing definitional link `W_s - Wp = (s-j+1)+H2`; without it the statement is under-specified |
| `weight_link_of_no_hge` / `H_ge_iff_capacity_of_no_hge` | proved | the missing link is derivable from the no-`H_ge` premises via `countTwosFrom` |
| `unified_core_forms_equivalent` | missing | the bridge between `unified_core_t2` and `unified_core_local` is the unified core itself, not a separately derivable step |
| `yStar` / `yStar_eq_zero_iff_congruence` / `terminal_bound_iff_yStar_ne_zero` | proved | terminal inequality iff `y* != 0`, i.e. failure congruence absent |
| `terminal_bound_iff_not_dvd` | proved | valuation bound iff `2^(H_s-1)` does not divide the failure numerator |
| `wTerminal_mul_eq` / `failure_cleared_iff` | proved | `3*r_s+1=2^(L+4)*w` and the cleared failure congruence modulo `2^(L+H_s+3)` |
| `failure_w_congruence` / `failure_rs_cleared_congruence` | proved | failure fixes `w` to `uResidue L (H_s-1)` and pins `3*r_s+1` modulo `2^(L+H_s+3)` |
| `three_cancel_modEq` / `failure_rs_unique` | proved | `3` is a unit modulo `2^k`; any two failures give the same `r_s` candidate class |
| `r_s_dyadic_bounds_of_no_hge` | proved | integer dyadic bounds `5^s*2^Wp ≤ 2^W_s*r_s < 5^s*(2^Wj+1)` |
| `failure_w_progression` / `failure_rs_progression` | proved | failure writes `w = uResidue + k*2^(H_s-1)` and `3*r_s+1 = 2^(L+4)*(uResidue + k*2^(H_s-1))` |
| `yStar_zero_implies_rs_candidate_class` / `terminal_failure_implies_candidate_class` | proved | `y*=0` or terminal failure puts `3*r_s+1` in the candidate class modulo `2^(L+H_s+3)` |
| `q0_unique_of_congruence` / `q0_interval_iff_rj_bound` | proved | congruence uniqueness of `q0` below `2^W_s`, and `[2^Wp,2^Wj)` iff `5^j <= 2^t*r_j` with `r_j < 5^j` |
| `blockB_bound_of_no_hge` | proved | (B1) does not need `H_ge`; B2 itself is the finite suffix closure already proved in `S6Audit` and is not restated here |
| `rj0_ge_of_size_conditions_no_hge` | proved | (B1)+(B2)+(B3) imply `rj0 >= 5^j`; this is the sufficient half of item 7 |
| `rj0_le_of_exact_equation` | proved | the least nonnegative 36.26 solution is no larger than any other solution with the same mod-5 block-head residue; wires `failure_rj_satisfies_exact_equation` into `rj0_le_of_failure_no_hge` |
| `t1_strip_twoValuation` / `t1_strip_wTerminal_mul` / `t1_strip_iter_wTerminal` | proved | 36.29.1: one `t=1` strip raises `v2(3r+1)` by one and multiplies `wTerminal` by `5`; `m` strips give `wTerminal L r_m = 5^m · wTerminal (L+m) r_0` |
| `t1_strip_iter_twoValuation` | proved | iterated `t=1` stripping: `(L+m)+4 = v2(3·(r 0)+1)` |
| `t1_step_mod8_five` / `t1_run_mod8_five` / `twoValuation_eq_one_of_mod8_five` | proved | trailing `t=1` run preserves `mod 8 = 5` backwards and gives `v2(r+1)=1` |
| `t2_step_plus_one_mul` / `t2_run_mul` / `t2_run_closed_form` | proved | 36.29.2: `4(r'+1)=5(r+1)`, `4^m(r_m+1)=5^m(r_0+1)`, and `r_0+1=2^(2m+1)u ⇒ r_m+1=2·5^m·u` |
| `t2_run_wTerminal` | proved | 36.29.2 conclusion: under the `t=2` run decomposition, `wTerminal L (r_m) = (3·5^m·u−1)/2^(L+3)` |
| `failure_congruence_lift_w` | proved | 36.29.3 clearing: `2^(H_s-1) | 5^(L+3)w+1` with `w=z/2^(L+3)` lifts to `2^(L+H_s+2) | 5^(L+3)z+2^(L+3)` |
| `t2_run_wTerminal_mul` / `t2_run_failure_congruence` | proved | 36.29.3: `2^(L+3)wTerminal = 3·5^m·u−1`, and the failure becomes `2^(L+H_s+2) | 5^(L+3)(3·5^m·u−1)+2^(L+3)` |
| `tail_wTerminal_full` | proved | 36.29.3 full tail: `m1` t=1 strips + `m2` t=2 run give `wTerminal L r_s = 5^m1·(3·5^m2·u−1)/2^(L+m1+3)` |
| `block_tail_wTerminal_of_premises` | proved | from `All36_20PremisesNoHge` builds `r1/r2/u`, exact `t=1`/`t=2` run steps, `r2 0+1=2^(2m2+1)u`, and the full `wTerminal` closed form |
| `tail_failure_congruence_of_premises` | proved | the terminal failure lifts through the tail to the single `2^((L+m1)+H_s+2)` congruence on `u` |
| `tail_failure_odd_part_congruence` | proved | clears the odd part: `3·5^m2·u−1 = 2^((L+m1)+3)·w` with `w` odd and `2^(H_s-1) | 5^((L+m1)+3)·w+1` |
| `block_trailing_ones_step` / `block_trailing_twos_step` | proved | a `t=1`/`t=2` run in `weight_step` advances `blockState` by the exact step equation with the divisibility witness |
| `leadingOnes` / `leadingTwos` / `tailSplit` | proved | list primitives for `(m1,m2)` tail splitting: trailing `1`s and preceding `2`s, with `replicate` specs |
| `leadingOnes_le_length` / `leadingTwos_le_length` / `tailSplit_sum_le_length` | proved | run lengths are bounded by the word length and `m1+m2 ≤ w.length` |
| `leadingOnes_spec` / `leadingTwos_spec` / `tailSplit_spec` | proved | the split is exact: reversed word begins with `m1` ones then `m2` twos, with the next entry excluded from the run |
| `tailSplit_m2_zero_m1_eq_length` / `tailSplit_m2_zero_all_ones` / `tail_start_eq_block_head_of_m2_zero` | proved | `m2=0` forces the block word to be all `t=1` and makes the `t=2` run start equal the block head |
| `r_s_mem_orbit25_of_premises_no_hge` / `r_s_eq_229_of_premises_no_hge` | proved | no-`H_ge` premises + `OrbitFrom7 r` force `r_s∈orbit25` and `r_s=229` |
| `s_le_9_of_premises_no_hge` | proved | no-`H_ge` premises + `OrbitFrom7 r` + `2<=H_s` force `s<=9` |
| `concat_word_eq_path_of_rs229_no_hge` / `bad_*_no_hge` | proved | no-`H_ge` path uniqueness and pseudo-candidate exclusions, used by the finite base |
| `local_lemma_final_no_hge` | proved | no-`H_ge` premises + `OrbitFrom7 r` + `2<=H_s` imply `rj0 >= 5^j`; axioms are only `propext / Classical.choice / Quot.sound` |
| `unified_core_final_no_hge_le15` | proved | the depth-`≤15` full-orbit branch of the final core closes via `fullOrbitPrefix_imp_OrbitFrom7` + `local_lemma_final_no_hge` |
| `pow5Inv_correct` | proved | `5^s * pow5Inv s m ≡ 1 (mod 2^m)` |
| `crtRep_lt` / `crtRep_unique` / `rj0_crt_candidate_unique` | proved | CRT representative is `< n*m` and unique below the product |
| `rj0_ge_iff_terminal_bound` | missing | the full iff through B2/B3 and the CRT lift; not yet formalized |
| `tail_failure_m2_zero_block_head_mod16` | proved | exact `m2=0` tail residue: failure forces `r % 16 = 5` (i.e. `u % 8 = 3`); this is the true content of the single tail congruence |
| `tail_failure_m2_zero_not_rj_mod64` | proved | the stated `failure_implies_rj_mod_64` bridge is false: `r % 16 = 5` excludes `r % 64 = 33` |
| `predecessor_mod32_of_block_head_mod16_t1` / `predecessor_mod64_of_block_head_mod16_t2` | proved | corrected predecessor residues: `t=1` gives `x ≡ 21 (mod 32)`, `t=2` gives `x ≡ 55 (mod 64)`; zero `sorry`, only `propext / Classical.choice / Quot.sound` |
| `UnifiedCoreBridge.d2_survivor_terminal_even` | proved | corrected `d=2` family: `x+1 ≡ 4 (mod 5)` and even for all `j ≡ 4 (mod 16)`; violates `ResetHeadEq` `s0` odd, so the `d=2` survivor is a pseudo-candidate, not a counterexample |
| `UnifiedCoreBridge.d3_survivor_terminal_even` | proved | corrected `d=3` survivor family (`t=2,δ=1,e=2,u1=u2=1`, `j≡168 mod 432`): `x+1 ≡ 4 (mod 5)` and even; violates `ResetHeadEq` `s0` odd, so the only `d=3` congruence survivor is a pseudo-candidate |
| `UnifiedCoreBridge.d3_*_no_pow_mod32/64` (10 branches) | proved | 10 of the 21 no-solution `d=3` branches are excluded by the mod-`2^k` power-period set (`C mod 2^k` is not a power of `5`); zero `sorry`, only `propext / Classical.choice / Quot.sound` |
| `UnifiedCoreBridge.d3_*_no_pow` (11 branches) | proved | the remaining 11 `d=3` branches are excluded by CRT: mod-`2^k` fixes `j % 2^(k-2)`, then the mod-`m` period table (`m∈{31,61,93,109}`) has no `s`; zero `sorry`, only `propext / Classical.choice / Quot.sound` |
| `UnifiedCoreBridge.dge4_e3_j17_t1_corrected_excluded` / `dge4_e3_j17_t2_delta3_corrected_excluded` | proved | d≥4 `e=3,j=17` branches still excluded under corrected residues: `x≡133 (mod 160)` vs required `53`, and `x≡263 (mod 320)` vs required `183` |
| `unified_core_final_no_hge` | **open** | no-`H_ge` premises + `r=(Aj+5^j q)/2^Wj` + `FullOrbitFrom7 r` + `2 <= H_s`; depth-`≤15` branch closed via `unified_core_final_no_hge_le15`, the single `sorry` is the depth-`≥16` branch; d=1/2/3/≥4 corrected exclusions are formalized, but the remaining open statements are (a) the `m2>0` tail branch (not covered by the `m2=0` candidate residue) and (b) the premises-to-candidate parameterization bridge |
| `failure_implies_rj_mod_64` | **invalid as stated** | 36.29/36.30.5 core: the tail congruence contradicts the claimed `r % 64 = 33`; the true `m2=0` residue is `r % 16 = 5` |
| `FinitePrefix.fullOrbit_first_t_ge3_is_exactly_3` | proved | `lean/FinitePrefix.lean`: explicit 17-state expansion by `simp [StringFlow.twoValuation_succ]`, zero `native_decide`; closes 36.30.23 at math level |
| `UnifiedCoreBridge` | encoded | `lean/UnifiedCoreBridge.lean`: `candidateX`, `candidateRj`, `orbitState`, `orbitStepWeight`; step 1 of the assembly plan |
| `UnifiedCoreBridge.fullOrbitStep_mul_eq` | proved | exact `2^t * fullOrbitStep x = 5*x+1`; used by the full-orbit rigidity lemmas |
| `UnifiedCoreBridge.fullOrbitStep_not_dvd_five` / `fullOrbitIter_not_dvd_five` | proved | 36.30.23.0: all full-orbit states are prime to `5` |
| `UnifiedCoreBridge.candidateRj_mod_five` | proved | 36.30.23.1: reset block head is `3 mod 5` for `t=1`, `4 mod 5` for `t=2` |
| `UnifiedCoreBridge.d1_exclusion` | proved | 36.30.23.5 `d=1`: `y=g` with the candidate parameterization is impossible |
| `UnifiedCoreBridge.d2_size_exclusion` | proved | 36.30.23.5 `d=2`: non-surviving branches excluded by `g < 5^(j-1)/2^(e-1)` |
| `UnifiedCoreBridge.five_pow_mod17_eq` / `five_pow_mod256_eq` | proved | period-16 and period-64 discrete-log lemmas used by the `d=2` survivor |
| `UnifiedCoreBridge.d2_survivor_mod_contradicts` | proved | `5^m ≡ 6 (mod 17)` and `5^m ≡ 45 (mod 256)` are incompatible |
| `UnifiedCoreBridge.d2_survivor_congruences` | proved | `d=2` survivor equations force the two power congruences |
| `UnifiedCoreBridge.d2_exclusion` | proved | full `d=2` segment exclusion: size branches plus survivor congruence contradiction |
| `UnifiedCoreBridge.orbitStepWeight_of_mul` | proved | `fullOrbitIter n = y`, `5y+1=2^k*x`, `x` odd ⇒ `orbitStepWeight n = k`; the reusable first-big-step input for `d=3`/`d≥4` |
| `UnifiedCoreBridge.d3_family_big_weight_excluded` | proved | `d=3` unique family: `z→w` has weight `6` at depth `j+4`, contradicting `FinitePrefix` |
| `UnifiedCoreBridge.dge4_e2_a_ge1_excluded` | proved | `d≥4`, `e=2,a≥1`: `y→x` has weight `1+4a≥5`, contradicting `FinitePrefix` |
| `UnifiedCoreBridge.dge4_e3_j17_t1_excluded` / `dge4_e3_j17_t2_delta3_excluded` | proved | `d≥4`, `e=3,j=17` branches fail the `mod 640/1280` candidate residue |
| `UnifiedCoreBridge.d3_exclusion_of_orbit` | proved | orbit-data wrapper for the `d=3` unique family: `z→w` weight `6` at depth `j+4` |
| `UnifiedCoreBridge.dge4_e2_exclusion_of_orbit` | proved | orbit-data wrapper for `d≥4`, `e=2,a≥1`: first big step weight `1+4a≥5` |
| `UnifiedCoreBridge.reset_head_predecessor` | proved | 36.30.9.1: `ResetHeadEq` + `rj=(5x+1)/2^t` force `x=5^k·s0+δ·5^(j-1)-1` |
| `UnifiedCoreBridge.candidateX_of_reset_and_terminal` | proved | 36.30.23.3+23.4: with `k=0` and `s0-1=2^(e-1)g`, the reset predecessor is `candidateX j e g δ` |
| `UnifiedCoreBridge.first_block_terminal_eq` | proved | 36.30.23.3: `5·g_prev+1=2^e·g` and `r=(5·g_prev+1)/2` force `r=2^(e-1)·g` |
| `UnifiedCoreBridge.reset_q0_form` | proved | 36.30.8.2: exact identity `A_j+5^j·q=2^L·(B+δ·5^j)` gives `q=m+δ·2^L` with `m<2^L` |
| `UnifiedCoreBridge.block_head_identity_of_reset` | proved | block-head representation + `ResetHeadEq` give `A_j+5^j·q=2^Wp·(5^(k+1)·s0-4+δ·5^j)` |
| `UnifiedCoreBridge.reset_head_eq_of_block_head_identity` | proved | converse: the 36.30.8.2 exact identity plus the block-head representation recover `ResetHeadEq` |
| `UnifiedCoreBridge.candidateRj_of_mod_five` | proved | mod-5 class `3/4` supplies `x` with `r = candidateRj x t` and the exact divisibility `2^t | 5x+1` |
| `UnifiedCoreBridge.reset_predecessor_of_block_head_premises` | proved | no-`H_ge` premises + `FullOrbitFrom7 r` give `t∈{1,2}` and `r = candidateRj x t` |
| `UnifiedCoreBridge.reset_predecessor_bound_of_block_head_premises` | proved | the same reset predecessor satisfies `x < 2^t·5^(j-1)` |
| `UnifiedCoreBridge.fullOrbitStep_eq_of_candidateRj` | proved | an odd reset successor `r` makes `x` a full-orbit preimage: `fullOrbitStep x = r` |
| `UnifiedCoreBridge.candidateRj_predecessor_odd` | proved | a `t∈{1,2}` reset predecessor of an odd state is odd |
| `UnifiedCoreBridge.candidateRj_eq_fullOrbitIter_of_weight` | proved | exact-predecessor bridge: if the full-orbit step into `r` at depth `n0` has weight `t`, then the `t`-reset predecessor `x` equals `fullOrbitIter (n0-1)`; no injectivity needed, only quotient equality by `2^t` |
| `UnifiedCoreBridge.candidate_parameterization_of_reset_full_orbit` | proved | packaged candidate bridge: `ResetHeadEq s0 (n0-1) 0 t δ r` + `s0=2^(e-1)*g+1` + exact full-orbit weights give `x = candidateX (n0-1) e g δ`, `x=fullOrbitIter (n0-1)`, `g=fullOrbitIter (n0-2)`, `e=orbitStepWeight (n0-2)` |
| `FinitePrefix.fullOrbitPrefix_wordValid/wordOrbit/imp_OrbitFrom7` | proved | depth `n≤15` full-orbit states are `OrbitFrom7`-reachable via `[2,1,2,1,1,2,1,1,1,2,2,2,2,1,1]` prefixes |
| `UnifiedCoreBridge.fullOrbitFrom7_le15_imp_OrbitFrom7` | proved | `FullOrbitFrom7` with depth `≤15` reduces to `OrbitFrom7` |
| `UnifiedCoreBridge.candidateX_mod4_of_e2/e_ge3` | proved | 36.30.23.4 branch table: `e=2⇒x≡2+δ (mod 4)`, `e≥3⇒x≡δ (mod 4)` |
| `UnifiedCoreBridge.orbitSegmentWord_*` | proved | exact segment word `2^W·x=5^d·g+A` for consecutive full-orbit steps |
| `UnifiedCoreBridge.d1_segment_equation/d2_segment_equation` | proved | exact `d=1`/`d=2` candidate segment equations from the actual orbit |
| `UnifiedCoreBridge.candidate_d1_input` | proved | converse of `d1_segment_equation`: a single `1+4a` orbit step from `g` to `x` makes `fullOrbitIter j = candidateX` |
| `UnifiedCoreBridge.d1_exclusion_of_orbit/d2_exclusion_of_orbit` | proved | orbit-data wrappers that invoke `d1_exclusion`/`d2_exclusion` |
| `UnifiedCoreBridge.blockWord_eq_orbitSegment_of_fullOrbit` | proved | word-segment continuity: a legal block from a full-orbit head is the exact continuous full-orbit suffix `orbitSegmentWord (n0+1) n`, and every block state is `fullOrbitIter (n0+n)` |
| `UnifiedCoreBridge.blockWord_full_suffix_of_fullOrbit(_reach)` | proved | the full block word equals the full-orbit suffix and `r_s=fullOrbitIter (n0+(s-j))`; existential form from `FullOrbitFrom7 r` |
| `UnifiedCoreBridge.blockState_fullOrbit_of_premises_fullOrbit` | proved | every block state from a full-orbit block head is itself a full-orbit state |
| `UnifiedCoreBridge.tail_failure_m2_even_u_mod8` / `tail_failure_m2_odd_u_mod8` | proved | exact `m2>0` tail residue on `u`: `m2` even gives `u≡3 (mod 8)`, `m2` odd gives `u≡7 (mod 8)`; pure arithmetic, no scan |
| `UnifiedCoreBridge.tail_failure_m2_pos_audit` | proved | packaged `m2>0` audit: `r_a` is full-orbit, `r_a+1=2^(2*m2+1)*u`, `u mod 8` fixed by parity of `m2`, and the cleared odd part `w` satisfies the same high 2-adic window as the `m2=0` branch |
| directed legal-word check (length <= 20) | evidence, not proof | 130,322 legal fixed-`q` blocks satisfy the no-`H_ge` premises with `2 <= H_s`; 0 violate the final inequality; 3 have real-orbit heads |

Minimum failing premises found so far:
1. `H_ge_iff_capacity` needs the definitional link `W_s - Wp = (s-j+1)+H2`;
   the raw statement in the task is not a theorem for arbitrary naturals.
   The link itself is now derived from the no-`H_ge` premises
   (`weight_link_of_no_hge`, `H_ge_iff_capacity_of_no_hge`).
2. `unified_core_forms_equivalent` and `rj0_ge_iff_terminal_bound` are not
   separately derivable non-core steps: both reduce to the same final
   valuation inequality `v2(5^(L+3)*w+1) <= H_s-2`.
3. `unified_core_final_no_hge` now carries the explicit real-orbit
   reachability `FullOrbitFrom7 r` (`r=(Aj+5^j q)/2^Wj`) and the domain
   premise `2 <= H_s`; it is the single open valuation inequality and the
   unique `sorry` in this file.  Document 36.29 (2026-08-12) has now
   rewritten the tail as an exact full-orbit decomposition: trailing
   `t=1` steps strip to `L_eff=L+m1`, and a final `t=2` run of length
   `m2` gives `r_a+1=2^(2*m2+1)*u` with
   `w_eff=(3*5^m2*u-1)/2^(L_eff+3)` and a single 2-adic congruence on
   `u`.  The word-segment continuity lemma now supplies the exact prefix
   position of `r_a` and the word shape from `r_j` to `r_a`; the `m2>0`
   tail residue on `u` is fixed by `tail_failure_m2_even_u_mod8` and
   `tail_failure_m2_odd_u_mod8`.  The reset equation (`ResetHeadEq` from
   the previous even terminal) is still not encoded in
   `All36_20PremisesNoHge`, so the premises-to-candidate bridge and the
   `m2>0` exclusion remain open.  Until those enter the proof, no true-card
   or candidate-true-card verdict is allowed; the audit remains open.

Math-level closure (2026-08-13): with `FinitePrefix` formalized, the
`d=1`, `d=2`, `d=3` and `d≥4` exclusions in document 36.30.23.5 close
the candidate family, hence the block-head candidate exclusion and the
downstream chain.  Lean assembly of that chain into
`unified_core_final_no_hge` is in progress: `FinitePrefix`, the
`d=1` and full `d=2` exclusions, and the 36.30.23.0/1 rigidity lemmas
now compile; the remaining assembly is the premises-to-parameterization
bridge and the `d=3`, `d≥4` exclusions.  The theorem above remains
`by sorry` and no Lean closure is claimed.
-/

end UnifiedCoreAudit
