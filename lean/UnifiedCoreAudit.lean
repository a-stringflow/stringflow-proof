import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import S6Audit
import S6AuditStage1
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
  sorry

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
| `q0_unique_of_congruence` / `q0_interval_iff_rj_bound` | proved | congruence uniqueness of `q0` below `2^W_s`, and `[2^Wp,2^Wj)` iff `5^j <= 2^t*r_j` with `r_j < 5^j` |
| `blockB_bound_of_no_hge` | proved | (B1) does not need `H_ge`; B2 itself is the finite suffix closure already proved in `S6Audit` and is not restated here |
| `rj0_ge_of_size_conditions_no_hge` | proved | (B1)+(B2)+(B3) imply `rj0 >= 5^j`; this is the sufficient half of item 7 |
| `pow5Inv_correct` | proved | `5^s * pow5Inv s m ≡ 1 (mod 2^m)` |
| `crtRep_lt` / `crtRep_unique` / `rj0_crt_candidate_unique` | proved | CRT representative is `< n*m` and unique below the product |
| `rj0_ge_iff_terminal_bound` | missing | the full iff through B2/B3 and the CRT lift; not yet formalized |
| `unified_core_final_no_hge` | **open** | the unique final core: no-`H_ge` premises + `r=(Aj+5^j q)/2^Wj` + `FullOrbitFrom7 r` + `2 <= H_s`; marked with `by sorry` |
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
| `UnifiedCoreBridge.reset_head_predecessor` | proved | 36.30.9.1: `ResetHeadEq` + `rj=(5x+1)/2^t` force `x=5^k·s0+δ·5^(j-1)-1` |
| `UnifiedCoreBridge.candidateX_of_reset_and_terminal` | proved | 36.30.23.3+23.4: with `k=0` and `s0-1=2^(e-1)g`, the reset predecessor is `candidateX j e g δ` |
| `UnifiedCoreBridge.first_block_terminal_eq` | proved | 36.30.23.3: `5·g_prev+1=2^e·g` and `r=(5·g_prev+1)/2` force `r=2^(e-1)·g` |
| `UnifiedCoreBridge.reset_q0_form` | proved | 36.30.8.2: exact identity `A_j+5^j·q=2^L·(B+δ·5^j)` gives `q=m+δ·2^L` with `m<2^L` |
| `UnifiedCoreBridge.block_head_identity_of_reset` | proved | block-head representation + `ResetHeadEq` give `A_j+5^j·q=2^Wp·(5^(k+1)·s0-4+δ·5^j)` |
| `FinitePrefix.fullOrbitPrefix_wordValid/wordOrbit/imp_OrbitFrom7` | proved | depth `n≤15` full-orbit states are `OrbitFrom7`-reachable via `[2,1,2,1,1,2,1,1,1,2,2,2,2,1,1]` prefixes |
| `UnifiedCoreBridge.fullOrbitFrom7_le15_imp_OrbitFrom7` | proved | `FullOrbitFrom7` with depth `≤15` reduces to `OrbitFrom7` |
| `UnifiedCoreBridge.candidateX_mod4_of_e2/e_ge3` | proved | 36.30.23.4 branch table: `e=2⇒x≡2+δ (mod 4)`, `e≥3⇒x≡δ (mod 4)` |
| `UnifiedCoreBridge.orbitSegmentWord_*` | proved | exact segment word `2^W·x=5^d·g+A` for consecutive full-orbit steps |
| `UnifiedCoreBridge.d1_segment_equation/d2_segment_equation` | proved | exact `d=1`/`d=2` candidate segment equations from the actual orbit |
| `UnifiedCoreBridge.d1_exclusion_of_orbit/d2_exclusion_of_orbit` | proved | orbit-data wrappers that invoke `d1_exclusion`/`d2_exclusion` |
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
   `u`.  The remaining `FullOrbitFrom7` facts not yet used are the exact
   prefix position of `r_a`, the word shape from `r_j` to `r_a`, and the
   reset equation.  Until those enter the proof, no true-card or
   candidate-true-card verdict is allowed; the audit remains open.

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
