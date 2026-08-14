import QWindow
import S6Audit

/-!
# Pure-block PMI layer for the general local lemma

This module fixes the block word as the PMI skeleton

    2^(W_i) * r_i = 5^i * q + A_i,
    A_i = sum_{k<i} 5^(i-1-k) * 2^(W_k).

The integers `A_i`, the prefix representative `q_i`, the bad residue
`q_V`, the carry balance `B_i`, and the carry bit `c_i` are defined from
this skeleton. The two joint-potential transitions below are identities.
-/

namespace StringFlow.PmiLocalLemma

open S6Audit

/-- `A_i`, the PMI word numerator at depth `i`. -/
def numerator (weight : Nat → Nat) (i : Nat) : Nat :=
  wordMolecule weight i

/-- `W_i`, the cumulative weight at depth `i`. -/
def weightAt (weight : Nat → Nat) (i : Nat) : Nat :=
  weight i

/-- The prefix representative
`q_i = ⟨-A_i·5^{-i}⟩_{2^(W_i)}`. -/
def prefixQ (weight : Nat → Nat) (i : Nat) : Nat :=
  negResidue
    (numerator weight i * pow5Inv i (weightAt weight i))
    (2 ^ weightAt weight i)

/-- Local version of the Hensel inverse specification. -/
theorem pow5Inv_correct_local (s m : Nat) (hm : 1 ≤ m) :
    5 ^ s * pow5Inv s m ≡ 1 [MOD 2 ^ m] := by
  unfold pow5Inv
  have hodd : (5 ^ s) % 2 = 1 := StringFlow.Lte.five_pow_odd s
  have hspec := invOdd_mod_pow_spec (5 ^ s) m hodd hm
  have hmod1 : 1 % 2 ^ m = 1 := by
    exact Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : m ≠ 0))
  rw [Nat.ModEq]
  simpa [hmod1] using hspec

/-- `q_i` is the exact least residue solving
`A_i + 5^i*q_i ≡ 0 (mod 2^(W_i))`. -/
theorem prefixQ_spec (weight : Nat → Nat) (i : Nat)
    (hW : 1 ≤ weightAt weight i) :
    (numerator weight i + 5 ^ i * prefixQ weight i) %
        2 ^ weightAt weight i = 0 := by
  let A := numerator weight i
  let W := weightAt weight i
  let M := 2 ^ W
  let inv := pow5Inv i W
  let R := prefixQ weight i
  have hM : 0 < M := by positivity
  have hinv : 5 ^ i * inv ≡ 1 [MOD M] := by
    dsimp [inv, M, W]
    exact pow5Inv_correct_local i (weightAt weight i) hW
  have hNmod : R + A * inv ≡ 0 [MOD M] := by
    have hspec : (R + (A * inv) % M) % M = 0 := by
      dsimp [R, prefixQ, A, W, inv, M]
      exact negResidue_spec (numerator weight i * pow5Inv i (weightAt weight i))
        (2 ^ weightAt weight i) hM
    have hmod : (A * inv) % M ≡ A * inv [MOD M] :=
      Nat.mod_modEq (A * inv) M
    have hNmod' : R + (A * inv) % M ≡ R + A * inv [MOD M] :=
      hmod.add_left R
    have hzero : R + (A * inv) % M ≡ 0 [MOD M] := by
      rw [Nat.ModEq]
      exact hspec
    exact hNmod'.symm.trans hzero
  have hAinv : A * (5 ^ i * inv) ≡ A [MOD M] := by
    have h := hinv.mul_left A
    simpa using h
  have hdist : 5 ^ i * R + A * (5 ^ i * inv) ≡ 0 [MOD M] := by
    have h := hNmod.mul_left (5 ^ i)
    have hcalc : 5 ^ i * (R + A * inv) =
        5 ^ i * R + A * (5 ^ i * inv) := by ring
    simpa [hcalc] using h
  have hsum : 5 ^ i * R + A ≡ 0 [MOD M] := by
    exact (hAinv.add_left (5 ^ i * R)).symm.trans hdist
  have hzero : (5 ^ i * R + A) % M = 0 := by
    rw [Nat.ModEq] at hsum
    simpa [Nat.add_comm] using hsum
  simpa [Nat.add_comm] using hzero

/-- For a legal word prefix starting at weight zero, every nonempty
word numerator `A_i` is odd. -/
theorem numerator_odd_of_valid_start
    (weight : Nat → Nat) : ∀ i : Nat, 1 ≤ i → weight 0 = 0 →
      (∀ k : Nat, k < i → weight (k + 1) = weight k + 1 ∨
        weight (k + 1) = weight k + 2) →
      numerator weight i % 2 = 1
  | 0, hi, _, _ => by omega
  | 1, _, hW0, _ => by
      change (2 ^ weight 0 + 5 * wordMolecule weight 0) % 2 = 1
      rw [hW0]
      rw [wordMolecule]
      norm_num
  | n + 2, _, hW0, hstep => by
      have hstep_small : ∀ k : Nat, k < n + 1 →
          weight (k + 1) = weight k + 1 ∨
            weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hA := numerator_odd_of_valid_start weight (n + 1)
        (by omega) hW0 hstep_small
      have hwi : 1 ≤ weight (n + 1) := by
        have h := S6Audit.weight_ge weight (n + 1) hW0 hstep_small
        omega
      unfold numerator
      rw [wordMolecule]
      have hpow : (2 ^ weight (n + 1)) % 2 = 0 :=
        StringFlow.Lte.pow_two_even_mod (weight (n + 1)) hwi
      have h5A : (5 * numerator weight (n + 1)) % 2 = 1 :=
        StringFlow.Lte.odd_mul_odd_mod_two 5
          (numerator weight (n + 1)) (by norm_num) hA
      exact StringFlow.Lte.even_add_odd_mod_two
        (2 ^ weight (n + 1)) (5 * numerator weight (n + 1))
        hpow h5A

/-- If the word numerator is odd and the weight is positive, then
`N_i = 5A_i + 3路2^(W_i)` is odd. -/
theorem windowNumerator_odd
    (A W : Nat) (hW : 1 ≤ W) (hA : A % 2 = 1) :
    (5 * A + 3 * 2 ^ W) % 2 = 1 := by
  have h5A : (5 * A) % 2 = 1 :=
    StringFlow.Lte.odd_mul_odd_mod_two 5 A (by norm_num) hA
  have htail : (3 * 2 ^ W) % 2 = 0 := by
    have hpow : (2 ^ W) % 2 = 0 :=
      StringFlow.Lte.pow_two_even_mod W hW
    have h := StringFlow.Lte.even_mul_mod_two (2 ^ W) 3 hpow
    simpa [Nat.mul_comm] using h
  have hsum := StringFlow.Lte.even_add_odd_mod_two
    (3 * 2 ^ W) (5 * A) htail h5A
  simpa [Nat.add_comm] using hsum

/-- The bad residue `q_V` has the same least bit as `N_i`; hence an
odd window numerator forces `q_V` to be odd. -/
theorem badResidue_odd_of_windowNumerator_odd
    (A W i E : Nat) (hW : 1 ≤ W) (hA : A % 2 = 1) (hE : 1 ≤ E) :
    QWindow.badResidue A W i E % 2 = 1 := by
  let N := 5 * A + 3 * 2 ^ W
  let b := QWindow.badResidue A W i E
  let M := 2 ^ E
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hNodd : N % 2 = 1 := by
    dsimp [N]
    exact windowNumerator_odd A W hW hA
  have hspec := QWindow.badResidue_spec A W i E hE
  have hbmod : (5 ^ (i + 1) * b) % M = (M - N % M) % M := by
    simpa [N, b, M] using hspec
  have hsumM : (5 ^ (i + 1) * b + N) % M = 0 := by
    have h := QWindow.mod_add_eq_zero_of_b_eq_neg
      N (5 ^ (i + 1) * b) M hM hbmod
    simpa [Nat.add_comm] using h
  have htwo_dvd_M : 2 ∣ M := by
    refine ⟨2 ^ (E - 1), ?_⟩
    dsimp [M]
    rw [show E = (E - 1) + 1 by omega]
    rw [Nat.pow_succ]
    rw [show E - 1 + 1 - 1 = E - 1 by omega]
    rw [Nat.mul_comm]
  have hsum2 : (5 ^ (i + 1) * b + N) % 2 = 0 :=
    QWindow.mod_zero_of_dvd_mod
      (5 ^ (i + 1) * b + N) M 2 htwo_dvd_M hsumM
  have h5odd : (5 ^ (i + 1)) % 2 = 1 :=
    StringFlow.Lte.five_pow_odd (i + 1)
  have hbcase : b % 2 = 0 ∨ b % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one b
  rcases hbcase with hb0 | hb1
  · have hmul : (5 ^ (i + 1) * b) % 2 = 0 := by
      rw [Nat.mul_mod]
      rw [h5odd, hb0]
    have hsumodd : (5 ^ (i + 1) * b + N) % 2 = 1 :=
      StringFlow.Lte.even_add_odd_mod_two
        (5 ^ (i + 1) * b) N hmul hNodd
    rw [hsumodd] at hsum2
    norm_num at hsum2
  · exact hb1

/-- The bad residue `q_V` in the window `2^(W_i+H_i+1)`. -/
def qV (weight : Nat → Nat) (i H : Nat) : Nat :=
  QWindow.badResidue
    (numerator weight i) (weightAt weight i) i
    (weightAt weight i + H + 1)

/-- For a legal prefix, the bad residue `q_V` is odd. -/
theorem qV_odd_of_valid_prefix
    (weight : Nat → Nat) (i H : Nat) (hi : 1 ≤ i)
    (hW0 : weight 0 = 0) (hW : 1 ≤ weightAt weight i)
    (hstep : ∀ k : Nat, k < i → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    qV weight i H % 2 = 1 := by
  unfold qV
  exact badResidue_odd_of_windowNumerator_odd
    (numerator weight i) (weightAt weight i) i
    (weightAt weight i + H + 1) hW
    (numerator_odd_of_valid_start weight i hi hW0 hstep)
    (by omega)

/-- The carry balance
`B_i = ((q_V-q_i)/2^(W_i)) mod 2^(H_i+1)`. -/
def carryBalanceP (weight : Nat → Nat) (i q H : Nat) : Nat :=
  QWindow.carryBalance
    (numerator weight i) (weightAt weight i) i q H

/-- The carry bit `c_i`, the bit of `q_V` at position
`W_i+H_i+1`. -/
def carryBitP (weight : Nat → Nat) (i H : Nat) : Nat :=
  QWindow.carryBit (numerator weight i) (weightAt weight i) i H

/-- The `p_i = 5^(-(i+2))` inverse used in the lifted `t=1` carry
recurrence. -/
def pTermT1 (i H : Nat) : Nat :=
  pow5Inv (i + 2) (H + 1)

/-- The same inverse at the `t=2` recurrence precision. -/
def pTermT2 (i H : Nat) : Nat :=
  pow5Inv (i + 2) H

/-- Exact lifted `t=1` carry recurrence:
`B_{i+1} ≡ (B_i+4p_i+c_i·2^(H_i+1))/2 (mod 2^(H_i+1))`. -/
def carryBalanceStepOneStatement
    (weight : Nat → Nat) (q i H : Nat) : Prop :=
  carryBalanceP weight (i + 1) q H ≡
    (carryBalanceP weight i q H + 4 * pTermT1 i H +
      carryBitP weight i H * 2 ^ (H + 1)) / 2
    [MOD 2 ^ (H + 1)]

/-- Exact `t=2` carry recurrence:
`B_{i+1} ≡ (B_i-2p_i)/4 (mod 2^(H_i-1))`. -/
def carryBalanceStepTwoStatement
    (weight : Nat → Nat) (q i H : Nat) : Prop :=
  carryBalanceP weight (i + 1) q (H - 2) ≡
    (carryBalanceP weight i q H - 2 * pTermT2 i H) / 4
    [MOD 2 ^ (H - 1)]

/-- A finite representative of the full 2-adic window quotient
`y_i = (q_V - q_i)/2^(W_i)`, modulo `2^(H+2)`. -/
def windowQuot (weight : Nat → Nat) (i q H : Nat) : Nat :=
  let W := weightAt weight i
  let M := 2 ^ (W + H + 2)
  let b := QWindow.badResidue (numerator weight i) W i (W + H + 2)
  ((b + M - q % 2 ^ W) % M) / 2 ^ W

/-- The actual block state determined by the PMI equation. -/
def blockStateP (weight : Nat → Nat) (q i : Nat) : Nat :=
  blockState weight q i

/-- The cleared PMI identity:
`2^(W_i) * r_i = 5^i * q + A_i`. -/
theorem pmi_identity_of_valid
    (weight : Nat → Nat) (q i : Nat)
    (hdiv : (numerator weight i + 5 ^ i * q) % 2 ^ weight i = 0) :
    2 ^ weight i * blockStateP weight q i =
      5 ^ i * q + numerator weight i := by
  unfold blockStateP blockState numerator
  have h := (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
  unfold numerator at h
  simpa [Nat.add_comm] using h.symm

/-- The joint 2-adic/5-adic potential
`P_i = 2^(W_i-W_j) * (5*r_i+3)`.
Its 2-adic valuation is exactly `(W_i-W_j)+v_2(5r_i+3)`. -/
def potential (weight : Nat → Nat) (q i j : Nat) : Nat :=
  2 ^ (weightAt weight i - weightAt weight j) *
    (5 * blockStateP weight q i + 3)

/-- One exact `t=1` block step advances the joint potential by
`5 P_i - 4 * 2^(W_i-W_j)`. -/
theorem potential_step_one
    (weight : Nat → Nat) (q i j : Nat)
    (_hij : j ≤ i)
    (_hmono : weight j ≤ weight i)
    (hW : weight (i + 1) = weight i + 1)
    (hprev : (numerator weight i + 5 ^ i * q) % 2 ^ weight i = 0)
    (hnext : (numerator weight (i + 1) + 5 ^ (i + 1) * q) %
        2 ^ weight (i + 1) = 0) :
    potential weight q (i + 1) j =
      5 * potential weight q i j -
        4 * 2 ^ (weight i - weight j) := by
  let r := blockState weight q i
  let r' := blockState weight q (i + 1)
  have hstep := blockState_step weight q i 1 hW hprev hnext
  have hexact : 2 * r' = 5 * r + 1 := by
    have hdiv : 2 ∣ 5 * r + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr hstep.1
    have hstepEq : (5 * r + 1) / 2 = r' := by
      simpa [r, r'] using hstep.2
    have hmul := Nat.mul_div_cancel' hdiv
    rw [hstepEq] at hmul
    exact hmul
  have hd : weight (i + 1) - weight j =
      (weight i - weight j) + 1 := by
    rw [hW]
    omega
  have hpow : 2 ^ (weight (i + 1) - weight j) =
      2 * 2 ^ (weight i - weight j) := by
    rw [hd, Nat.pow_succ]
    ring_nf
  have hleft : 2 * potential weight q (i + 1) j =
      2 ^ ((weight i - weight j) + 1) * (25 * r + 11) := by
    unfold potential
    dsimp [r, r', blockStateP, weightAt]
    rw [hpow]
    have hnum : 2 * (5 * r' + 3) = 25 * r + 11 := by
      nlinarith [hexact]
    have hr' : blockState weight q (i + 1) = r' := rfl
    rw [hr']
    calc
      2 * (2 * 2 ^ (weight i - weight j) * (5 * r' + 3))
          = 2 * 2 ^ (weight i - weight j) * (2 * (5 * r' + 3)) := by ring
      _ = 2 * 2 ^ (weight i - weight j) * (25 * r + 11) := by rw [hnum]
      _ = 2 ^ ((weight i - weight j) + 1) * (25 * r + 11) := by
          rw [Nat.pow_succ]
          ring
  have hright : 2 * (5 * potential weight q i j -
      4 * 2 ^ (weight i - weight j)) =
      2 ^ ((weight i - weight j) + 1) * (25 * r + 11) := by
    unfold potential
    dsimp [r, blockStateP, weightAt]
    rw [show (weight i - weight j) + 1 = Nat.succ (weight i - weight j) by omega]
    rw [Nat.pow_succ]
    ring_nf
    omega
  have hEq : 2 * potential weight q (i + 1) j =
      2 * (5 * potential weight q i j -
        4 * 2 ^ (weight i - weight j)) := by
    calc
      2 * potential weight q (i + 1) j
          = 2 ^ ((weight i - weight j) + 1) * (25 * r + 11) := hleft
      _ = 2 * (5 * potential weight q i j -
            4 * 2 ^ (weight i - weight j)) := hright.symm
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) hEq

/-- One exact `t=2` block step advances the joint potential by
`5 P_i + 2 * 2^(W_i-W_j)`. -/
theorem potential_step_two
    (weight : Nat → Nat) (q i j : Nat)
    (_hij : j ≤ i)
    (_hmono : weight j ≤ weight i)
    (hW : weight (i + 1) = weight i + 2)
    (hprev : (numerator weight i + 5 ^ i * q) % 2 ^ weight i = 0)
    (hnext : (numerator weight (i + 1) + 5 ^ (i + 1) * q) %
        2 ^ weight (i + 1) = 0) :
    potential weight q (i + 1) j =
      5 * potential weight q i j +
        2 * 2 ^ (weight i - weight j) := by
  let r := blockState weight q i
  let r' := blockState weight q (i + 1)
  have hstep := blockState_step weight q i 2 hW hprev hnext
  have hexact : 4 * r' = 5 * r + 1 := by
    have hdiv : 4 ∣ 5 * r + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr hstep.1
    have hstepEq : (5 * r + 1) / 4 = r' := by
      simpa [r, r'] using hstep.2
    have hmul := Nat.mul_div_cancel' hdiv
    rw [hstepEq] at hmul
    exact hmul
  have hd : weight (i + 1) - weight j =
      (weight i - weight j) + 2 := by
    rw [hW]
    omega
  have hpow : 2 ^ (weight (i + 1) - weight j) =
      4 * 2 ^ (weight i - weight j) := by
    rw [hd]
    rw [show (weight i - weight j) + 2 = 2 + (weight i - weight j) by omega]
    rw [Nat.pow_add]
  have hleft : 4 * potential weight q (i + 1) j =
      2 ^ ((weight i - weight j) + 2) * (25 * r + 17) := by
    unfold potential
    dsimp [r, r', blockStateP, weightAt]
    rw [hpow]
    have hnum : 4 * (5 * r' + 3) = 25 * r + 17 := by
      nlinarith [hexact]
    have hr' : blockState weight q (i + 1) = r' := rfl
    rw [hr']
    calc
      4 * (4 * 2 ^ (weight i - weight j) * (5 * r' + 3))
          = 4 * 2 ^ (weight i - weight j) * (4 * (5 * r' + 3)) := by ring
      _ = 4 * 2 ^ (weight i - weight j) * (25 * r + 17) := by rw [hnum]
      _ = 2 ^ ((weight i - weight j) + 2) * (25 * r + 17) := by
          rw [show 4 = 2 ^ 2 by norm_num]
          rw [show (weight i - weight j) + 2 =
            2 + (weight i - weight j) by omega]
          rw [Nat.pow_add]
  have hright : 4 * (5 * potential weight q i j +
      2 * 2 ^ (weight i - weight j)) =
      2 ^ ((weight i - weight j) + 2) * (25 * r + 17) := by
    unfold potential
    dsimp [r, blockStateP, weightAt]
    rw [show (weight i - weight j) + 2 = 2 + (weight i - weight j) by omega]
    rw [Nat.pow_add]
    ring_nf
  have hEq : 4 * potential weight q (i + 1) j =
      4 * (5 * potential weight q i j +
        2 * 2 ^ (weight i - weight j)) := by
    calc
      4 * potential weight q (i + 1) j
          = 2 ^ ((weight i - weight j) + 2) * (25 * r + 17) := hleft
      _ = 4 * (5 * potential weight q i j +
            2 * 2 ^ (weight i - weight j)) := hright.symm
  exact Nat.mul_left_cancel (by norm_num : 0 < 4) hEq

/-- The valuation of the joint potential is exactly the shifted valuation
of the block state. -/
theorem valuation_of_potential
    (weight : Nat → Nat) (q i j : Nat) (_hij : j ≤ i) :
    twoValuation (potential weight q i j) =
      weight i - weight j +
        twoValuation (5 * blockStateP weight q i + 3) := by
  have hpos : 0 < 5 * blockStateP weight q i + 3 := by positivity
  unfold potential
  exact StringFlow.Lte.twoValuation_mul_two_pow
    (weight i - weight j) (5 * blockStateP weight q i + 3) hpos

/-- `u_i = v2(r_i+1)`. -/
def uAt (weight : Nat → Nat) (q i : Nat) : Nat :=
  twoValuation (blockStateP weight q i + 1)

/-- `X_i = v2(5*r_i+3)`. -/
def XAt (weight : Nat → Nat) (q i : Nat) : Nat :=
  twoValuation (5 * blockStateP weight q i + 3)

/-- Exact `t=1` valuation transfer: if `5*r_i+3 = 4*C`, then
`X_{i+1} = 1 + v2(5*C-1)`. -/
theorem XAt_step_one_exact
    (weight : Nat → Nat) (q i C : Nat)
    (hW : weightAt weight (i + 1) = weightAt weight i + 1)
    (hprev : (numerator weight i + 5 ^ i * q) % 2 ^ weightAt weight i = 0)
    (hnext : (numerator weight (i + 1) + 5 ^ (i + 1) * q) %
        2 ^ weightAt weight (i + 1) = 0)
    (hC : 5 * blockStateP weight q i + 3 = 4 * C) :
    XAt weight q (i + 1) = 1 + twoValuation (5 * C - 1) := by
  let r := blockStateP weight q i
  let r' := blockStateP weight q (i + 1)
  have hstep := blockState_step weight q i 1
    (by simpa [weightAt] using hW) hprev hnext
  have hdiv : 2 ∣ 5 * r + 1 := by
    have hm := hstep.1
    have hmod : (5 * r + 1) % 2 = 0 := by
      simpa [r, blockStateP] using hm
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  have htwo_r' : 2 * r' = 5 * r + 1 := by
    have hm := Nat.mul_div_cancel' hdiv
    have hstep' : (5 * r + 1) / 2 = r' := by
      simpa [r, r', blockStateP] using hstep.2
    rw [hstep'] at hm
    exact hm
  have hCpos : 0 < C := by
    have hposN : 0 < 5 * r + 3 := by positivity
    have hpos4 : 0 < 4 * C := by
      rw [← hC]
      exact hposN
    omega
  have hnext_eq : 5 * r' + 3 = 2 * (5 * C - 1) := by
    have htwice : 2 * (5 * r' + 3) = 2 * (2 * (5 * C - 1)) := by
      calc
        2 * (5 * r' + 3) = 25 * r + 11 := by nlinarith [htwo_r']
        _ = 5 * (5 * r + 3) - 4 := by omega
        _ = 5 * (4 * C) - 4 := by rw [hC]
        _ = 2 * (2 * (5 * C - 1)) := by omega
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) htwice
  have hpos : 0 < 5 * C - 1 := by
    nlinarith [hCpos]
  have hval' := StringFlow.twoValuation_mul_two (5 * C - 1) hpos
  have hval : twoValuation (2 * (5 * C - 1)) =
      1 + twoValuation (5 * C - 1) := by
    simpa [Nat.add_comm] using hval'
  calc
    XAt weight q (i + 1) = twoValuation (5 * r' + 3) := rfl
    _ = twoValuation (2 * (5 * C - 1)) := by rw [hnext_eq]
    _ = 1 + twoValuation (5 * C - 1) := hval

/-- Exact `t=2` valuation transfer: if `5*r_i+3 = 2*C`, then
`X_{i+1} = v2(5*C+1)-1`. -/
theorem XAt_step_two_exact
    (weight : Nat → Nat) (q i C : Nat)
    (hW : weightAt weight (i + 1) = weightAt weight i + 2)
    (hprev : (numerator weight i + 5 ^ i * q) % 2 ^ weightAt weight i = 0)
    (hnext : (numerator weight (i + 1) + 5 ^ (i + 1) * q) %
        2 ^ weightAt weight (i + 1) = 0)
    (hC : 5 * blockStateP weight q i + 3 = 2 * C) :
    XAt weight q (i + 1) = twoValuation (5 * C + 1) - 1 := by
  let r := blockStateP weight q i
  let r' := blockStateP weight q (i + 1)
  have hstep := blockState_step weight q i 2
    (by simpa [weightAt] using hW) hprev hnext
  have hdiv : 4 ∣ 5 * r + 1 := by
    have hm := hstep.1
    have hmod : (5 * r + 1) % 4 = 0 := by
      simpa [r, blockStateP] using hm
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hfour_r' : 4 * r' = 5 * r + 1 := by
    have hm := Nat.mul_div_cancel' hdiv
    have hstep' : (5 * r + 1) / 4 = r' := by
      simpa [r, r', blockStateP] using hstep.2
    rw [hstep'] at hm
    exact hm
  have hnext_eq : 2 * (5 * r' + 3) = 5 * C + 1 := by
    have hfour : 4 * (5 * r' + 3) = 2 * (5 * C + 1) := by
      calc
        4 * (5 * r' + 3) = 25 * r + 17 := by nlinarith [hfour_r']
        _ = 5 * (5 * r + 3) + 2 := by ring_nf
        _ = 5 * (2 * C) + 2 := by rw [hC]
        _ = 2 * (5 * C + 1) := by ring_nf
    have hhalf : 2 * (5 * r' + 3) = 5 * C + 1 := by
      have hmul : 2 * (2 * (5 * r' + 3)) = 2 * (5 * C + 1) := by
        calc
          2 * (2 * (5 * r' + 3)) = 4 * (5 * r' + 3) := by ring
          _ = 2 * (5 * C + 1) := hfour
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul
    exact hhalf
  have hpos : 0 < 5 * r' + 3 := by positivity
  have hval' := StringFlow.twoValuation_mul_two (5 * r' + 3) hpos
  have hval : twoValuation (2 * (5 * r' + 3)) =
      1 + twoValuation (5 * r' + 3) := by
    simpa [Nat.add_comm] using hval'
  have hv : 1 + XAt weight q (i + 1) =
      twoValuation (5 * C + 1) := by
    calc
      1 + XAt weight q (i + 1)
          = twoValuation (2 * (5 * r' + 3)) := by
              rw [XAt, hval]
      _ = twoValuation (5 * C + 1) := by rw [hnext_eq]
  omega

private lemma dvd_two_pow_add_two_left (H a : Nat) :
    2 ^ H ∣ a ↔ 2 ^ (H + 2) ∣ 4 * a := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    have hpow : 2 ^ (H + 2) = 2 ^ 2 * 2 ^ H := by
      rw [Nat.pow_add]
      rw [Nat.mul_comm]
    rw [hpow]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hpow : 2 ^ (H + 2) = 2 ^ 2 * 2 ^ H := by
      rw [Nat.pow_add]
      rw [Nat.mul_comm]
    rw [hpow] at ht
    have hfac : 2 ^ 2 * (2 ^ H * t) = 2 ^ 2 * a := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht.symm
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2)) hfac.symm

private lemma dvd_two_pow_shift_left (W H a : Nat) :
    2 ^ (H + 2) ∣ a ↔ 2 ^ (W + H + 2) ∣ 2 ^ W * a := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    rw [Nat.pow_add]
    ring
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hpow : 2 ^ (W + H + 2) = 2 ^ W * 2 ^ (H + 2) := by
      calc
        2 ^ (W + H + 2) = 2 ^ (W + H) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = (2 ^ W * 2 ^ H) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = 2 ^ W * (2 ^ H * 2 ^ 2) := by ring
        _ = 2 ^ W * 2 ^ (H + 2) := by rw [Nat.pow_add]
    rw [hpow] at ht
    have hfac : 2 ^ W * (2 ^ (H + 2) * t) = 2 ^ W * a := by
      simpa [Nat.mul_assoc] using ht.symm
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2)) hfac.symm

private lemma dvd_two_pow_add_one_left (H a : Nat) :
    2 ^ H ∣ a ↔ 2 ^ (H + 1) ∣ 2 * a := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    rw [Nat.pow_add]
    ring
  · rintro ⟨t, ht⟩
    have hpow : 2 ^ (H + 1) = 2 * 2 ^ H := by
      rw [Nat.pow_add]
      ring
    rw [hpow] at ht
    have hfac : 2 * (2 ^ H * t) = 2 * a := by
      simpa [Nat.mul_assoc] using ht.symm
    exact ⟨t, Nat.mul_left_cancel (by decide : 0 < 2) hfac.symm⟩

private lemma dvd_two_pow_shift_left_one (W H a : Nat) :
    2 ^ (H + 1) ∣ a ↔ 2 ^ (W + H + 1) ∣ 2 ^ W * a := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    rw [Nat.pow_add]
    ring
  · rintro ⟨t, ht⟩
    have hpow : 2 ^ (W + H + 1) = 2 ^ W * 2 ^ (H + 1) := by
      calc
        2 ^ (W + H + 1) = 2 ^ (W + H) * 2 ^ 1 := by rw [Nat.pow_add]
        _ = (2 ^ W * 2 ^ H) * 2 := by rw [Nat.pow_add]; norm_num
        _ = 2 ^ W * (2 ^ H * 2) := by ring
        _ = 2 ^ W * 2 ^ (H + 1) := by rw [Nat.pow_add]
    rw [hpow] at ht
    have hfac : 2 ^ W * (2 ^ (H + 1) * t) = 2 ^ W * a := by
      simpa [Nat.mul_assoc] using ht.symm
    exact ⟨t, Nat.mul_left_cancel
      (Nat.pow_pos (by decide : 0 < 2)) hfac.symm⟩

private lemma twoValuation_ge_iff_dvd_pow (n H : Nat)
    (hn : 0 < n) (hH : 1 ≤ H) :
    H ≤ twoValuation n ↔ 2 ^ H ∣ n := by
  have hle := StringFlow.Lte.twoValuation_le_iff_not_dvd_pow n (H - 1) hn
  rw [show H - 1 + 1 = H by omega] at hle
  constructor
  · intro hv
    have hdec := n_eq_two_pow_mul_oddPart n hn
    have hpow : 2 ^ twoValuation n =
        2 ^ H * 2 ^ (twoValuation n - H) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hdec, hpow]
    refine ⟨2 ^ (twoValuation n - H) * oddPart n, ?_⟩
    ring
  · intro hdvd
    by_contra hvle
    have hvle' : twoValuation n ≤ H - 1 := by omega
    exact (hle.mp hvle') hdvd

/-- The single `t=1` failure is exactly one divisibility of the word
numerator and the block parameter `q`. -/
theorem t1FailureDivisibility
    (weight : Nat → Nat) (q k H C r : Nat)
    (hrep : numerator weight k + 5 ^ k * q =
      2 ^ weightAt weight k * r)
    (hC : 5 * r + 3 = 4 * C) :
    2 ^ H ∣ 5 * C - 1 ↔
      2 ^ (weightAt weight k + H + 2) ∣
        25 * numerator weight k + 11 * 2 ^ weightAt weight k +
          5 ^ (k + 2) * q := by
  let W := weightAt weight k
  have hCpos : 0 < C := by
    have hpos : 0 < 5 * r + 3 := by positivity
    have hpos4 : 0 < 4 * C := by rw [← hC]; exact hpos
    omega
  have h1 : 4 * (5 * C - 1) = 25 * r + 11 := by
    calc
      4 * (5 * C - 1) = 5 * (4 * C) - 4 := by omega
      _ = 5 * (5 * r + 3) - 4 := by rw [hC]
      _ = 25 * r + 11 := by omega
  have hdivC := dvd_two_pow_add_two_left H (5 * C - 1)
  have hdivR := dvd_two_pow_shift_left (weightAt weight k) H (25 * r + 11)
  have hpow5 : 25 * 5 ^ k = 5 ^ (k + 2) := by
    calc
      25 * 5 ^ k = 5 ^ 2 * 5 ^ k := by norm_num
      _ = 5 ^ (k + 2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
  have hEq : 2 ^ W * (25 * r + 11) =
      25 * numerator weight k + 11 * 2 ^ W + 5 ^ (k + 2) * q := by
    calc
      2 ^ W * (25 * r + 11) = 25 * (2 ^ W * r) + 11 * 2 ^ W := by ring
      _ = 25 * (numerator weight k + 5 ^ k * q) + 11 * 2 ^ W := by
          rw [← hrep]
      _ = 25 * numerator weight k + 25 * 5 ^ k * q + 11 * 2 ^ W := by
          ring
      _ = 25 * numerator weight k + 5 ^ (k + 2) * q + 11 * 2 ^ W := by
          rw [hpow5]
      _ = 25 * numerator weight k + 11 * 2 ^ W + 5 ^ (k + 2) * q := by
          ring
  calc
    2 ^ H ∣ 5 * C - 1 ↔ 2 ^ (H + 2) ∣ 4 * (5 * C - 1) := hdivC
    _ ↔ 2 ^ (H + 2) ∣ 25 * r + 11 := by rw [h1]
    _ ↔ 2 ^ (W + H + 2) ∣ 2 ^ W * (25 * r + 11) := hdivR
    _ ↔ 2 ^ (W + H + 2) ∣
        25 * numerator weight k + 11 * 2 ^ W + 5 ^ (k + 2) * q := by
          rw [hEq]

/-- The single `t=2` failure is exactly the corresponding divisibility
of the word numerator and `q`. -/
theorem t2FailureDivisibility
    (weight : Nat → Nat) (q k H C r : Nat)
    (hrep : numerator weight k + 5 ^ k * q =
      2 ^ weightAt weight k * r)
    (hC : 5 * r + 3 = 2 * C) :
    2 ^ H ∣ 5 * C + 1 ↔
      2 ^ (weightAt weight k + H + 1) ∣
        25 * numerator weight k + 17 * 2 ^ weightAt weight k +
          5 ^ (k + 2) * q := by
  let W := weightAt weight k
  have hCpos : 0 < C := by
    have hpos : 0 < 5 * r + 3 := by positivity
    have hpos2 : 0 < 2 * C := by rw [← hC]; exact hpos
    omega
  have h1 : 2 * (5 * C + 1) = 25 * r + 17 := by
    calc
      2 * (5 * C + 1) = 5 * (2 * C) + 2 := by omega
      _ = 5 * (5 * r + 3) + 2 := by rw [hC]
      _ = 25 * r + 17 := by omega
  have hdivC := dvd_two_pow_add_one_left H (5 * C + 1)
  have hdivR := dvd_two_pow_shift_left_one (weightAt weight k) H (25 * r + 17)
  have hpow5 : 25 * 5 ^ k = 5 ^ (k + 2) := by
    calc
      25 * 5 ^ k = 5 ^ 2 * 5 ^ k := by norm_num
      _ = 5 ^ (k + 2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
  have hEq : 2 ^ W * (25 * r + 17) =
      25 * numerator weight k + 17 * 2 ^ W + 5 ^ (k + 2) * q := by
    calc
      2 ^ W * (25 * r + 17) = 25 * (2 ^ W * r) + 17 * 2 ^ W := by ring
      _ = 25 * (numerator weight k + 5 ^ k * q) + 17 * 2 ^ W := by
          rw [← hrep]
      _ = 25 * numerator weight k + 25 * 5 ^ k * q + 17 * 2 ^ W := by
          ring
      _ = 25 * numerator weight k + 5 ^ (k + 2) * q + 17 * 2 ^ W := by
          rw [hpow5]
      _ = 25 * numerator weight k + 17 * 2 ^ W + 5 ^ (k + 2) * q := by
          ring
  calc
    2 ^ H ∣ 5 * C + 1 ↔ 2 ^ (H + 1) ∣ 2 * (5 * C + 1) := hdivC
    _ ↔ 2 ^ (H + 1) ∣ 25 * r + 17 := by rw [h1]
    _ ↔ 2 ^ (W + H + 1) ∣ 2 ^ W * (25 * r + 17) := hdivR
    _ ↔ 2 ^ (W + H + 1) ∣
        25 * numerator weight k + 17 * 2 ^ W + 5 ^ (k + 2) * q := by
          rw [hEq]

/-- The `t=1` successor fails exactly when the single-step word
divisibility above holds. -/
theorem XAt_step_one_failure_iff_divisibility
    (weight : Nat → Nat) (q k H C : Nat)
    (hW : weightAt weight (k + 1) = weightAt weight k + 1)
    (hprev : (numerator weight k + 5 ^ k * q) % 2 ^ weightAt weight k = 0)
    (hnext : (numerator weight (k + 1) + 5 ^ (k + 1) * q) %
        2 ^ weightAt weight (k + 1) = 0)
    (hC : 5 * blockStateP weight q k + 3 = 4 * C)
    (hH : 1 ≤ H) :
    H < XAt weight q (k + 1) ↔
      2 ^ (weightAt weight k + H + 2) ∣
        25 * numerator weight k + 11 * 2 ^ weightAt weight k +
          5 ^ (k + 2) * q := by
  have hx := XAt_step_one_exact weight q k C hW hprev hnext hC
  rw [hx]
  have hCpos : 0 < C := by
    have hpos : 0 < 5 * blockStateP weight q k + 3 := by positivity
    have hpos4 : 0 < 4 * C := by rw [← hC]; exact hpos
    omega
  have hC1 : 1 ≤ C := by omega
  have hpos : 0 < 5 * C - 1 := by omega
  have hge : H < 1 + twoValuation (5 * C - 1) ↔
      H ≤ twoValuation (5 * C - 1) := by omega
  have hvd := twoValuation_ge_iff_dvd_pow (5 * C - 1) H hpos hH
  have hrep : numerator weight k + 5 ^ k * q =
      2 ^ weightAt weight k * blockStateP weight q k := by
    simpa [Nat.add_comm, weightAt] using
      (pmi_identity_of_valid weight q k hprev).symm
  have hdiv := t1FailureDivisibility weight q k H C
    (blockStateP weight q k) hrep hC
  exact hge.trans (hvd.trans hdiv)

/-- The `t=2` successor fails exactly when the corresponding
single-step word divisibility holds. -/
theorem XAt_step_two_failure_iff_divisibility
    (weight : Nat → Nat) (q k H C : Nat)
    (hW : weightAt weight (k + 1) = weightAt weight k + 2)
    (hprev : (numerator weight k + 5 ^ k * q) % 2 ^ weightAt weight k = 0)
    (hnext : (numerator weight (k + 1) + 5 ^ (k + 1) * q) %
        2 ^ weightAt weight (k + 1) = 0)
    (hC : 5 * blockStateP weight q k + 3 = 2 * C)
    (hH : 2 ≤ H) :
    H - 2 < XAt weight q (k + 1) ↔
      2 ^ (weightAt weight k + H + 1) ∣
        25 * numerator weight k + 17 * 2 ^ weightAt weight k +
          5 ^ (k + 2) * q := by
  have hx := XAt_step_two_exact weight q k C hW hprev hnext hC
  rw [hx]
  have hCpos : 0 < C := by
    have hpos : 0 < 5 * blockStateP weight q k + 3 := by positivity
    have hpos2 : 0 < 2 * C := by rw [← hC]; exact hpos
    omega
  have hpos : 0 < 5 * C + 1 := by positivity
  have hge : H - 2 < twoValuation (5 * C + 1) - 1 ↔
      H ≤ twoValuation (5 * C + 1) := by omega
  have hvd := twoValuation_ge_iff_dvd_pow (5 * C + 1) H hpos
    (by omega : 1 ≤ H)
  have hrep : numerator weight k + 5 ^ k * q =
      2 ^ weightAt weight k * blockStateP weight q k := by
    simpa [Nat.add_comm, weightAt] using
      (pmi_identity_of_valid weight q k hprev).symm
  have hdiv := t2FailureDivisibility weight q k H C
    (blockStateP weight q k) hrep hC
  exact hge.trans (hvd.trans hdiv)

/-- `H_i = 2i+13-2(W_i-W_{j-1})`. -/
@[irreducible] def HAt (weight : Nat → Nat) (i j : Nat) : Nat :=
  2 * i + 13 - 2 * (weightAt weight i - weightAt weight (j - 1))

/-- The candidate odd-rank invariant `I_i : H_i >= u_i+4`. -/
def oddRankAt (weight : Nat → Nat) (q i j : Nat) : Prop :=
  HAt weight i j ≥ uAt weight q i + 4

/-- The even-valuation statement used by the capacity induction:
at a `u=1` state with even `X_i`, the valuation is not in the top
three window positions. -/
def evenValuationAt (weight : Nat → Nat) (q i j : Nat) : Prop :=
  uAt weight q i = 1 →
  XAt weight q i % 2 = 0 →
  XAt weight q i + 3 ≤ HAt weight i j

/-- The full local lemma at a `u=1` state, in the block-local form. -/
def localLemmaAt (weight : Nat → Nat) (q i j : Nat) : Prop :=
  twoValuation (5 * blockStateP weight q i + 3) ≤
    2 * i + 13 - 2 * (weightAt weight i - weightAt weight (j - 1))

/-- The capacity half: `H_i ≥ 3`. -/
def capacityAt (weight : Nat → Nat) (i j : Nat) : Prop :=
  3 ≤ 2 * i + 13 - 2 * (weightAt weight i - weightAt weight (j - 1))

/-- The odd-rank invariant is strictly stronger than the capacity
condition at a `u=1` state. -/
theorem capacity_of_oddRank
    (weight : Nat → Nat) (q i j : Nat)
    (hu : uAt weight q i = 1) (hI : oddRankAt weight q i j) :
    capacityAt weight i j := by
  unfold capacityAt oddRankAt HAt weightAt at *
  nlinarith

/-- The valuation half, written as nonzero carry balance. -/
def valuationAt (weight : Nat → Nat) (q i _j H : Nat) : Prop :=
  carryBalanceP weight i q H ≠ 0

/-- The high window is exactly the carry part of `q_V`:
`q_V = q + 2^W * B`. -/
theorem badResidue_eq_q_add_two_pow_mul_carryBalance
    (A W i q H r : Nat) (hW : 1 ≤ W) (hq : q < 2 ^ W)
    (hrep : A + 5 ^ i * q = 2 ^ W * r) :
    QWindow.badResidue A W i (W + H + 1) =
      q + 2 ^ W * QWindow.carryBalance A W i q H := by
  let T := 2 ^ W
  let M := 2 ^ (W + H + 1)
  let b := QWindow.badResidue A W i (W + H + 1)
  have hbT := QWindow.badResidue_mod_two_pow_eq_q A W i q H r hW hq hrep
  have hbM : b < M := by
    dsimp [b, M]
    unfold QWindow.badResidue
    exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have hTpos : 0 < T := by
    dsimp [T]
    exact Nat.pow_pos (by decide : 0 < 2)
  have hqT : q % T = q := Nat.mod_eq_of_lt (by simpa [T] using hq)
  have hbT' : b % T = q := by
    simpa [T, hqT] using hbT
  let k := b / T
  have hbdec : b = T * k + q := by
    have hdec : b = T * (b / T) + b % T := (Nat.div_add_mod b T).symm
    rw [hbT'] at hdec
    simpa [k] using hdec
  have hqle : q ≤ b := by
    rw [hbdec]
    omega
  have hd : (b + M - q) % M = b - q := by
    have hval : b + M - q = M + (b - q) := by omega
    rw [hval]
    rw [Nat.add_comm]
    rw [StringFlow.Word.add_mod_mul_one (b - q) M]
    exact Nat.mod_eq_of_lt (by omega)
  have hsub : b - q = T * k := by
    rw [hbdec]
    omega
  have hklt : k < 2 ^ (H + 1) := by
    have hmul : T * k ≤ b := by
      rw [hbdec]
      omega
    have hlt : T * k < M := Nat.lt_of_le_of_lt hmul hbM
    have hM' : M = T * 2 ^ (H + 1) := by
      dsimp [T, M]
      rw [← Nat.pow_add]
      congr 1
    rw [hM'] at hlt
    exact (Nat.mul_lt_mul_left hTpos).1 hlt
  have hB : QWindow.carryBalance A W i q H = k := by
    unfold QWindow.carryBalance
    dsimp [T, M, b, k]
    rw [hqT, hd, hsub]
    rw [Nat.mul_div_right k hTpos]
    exact Nat.mod_eq_of_lt hklt
  rw [hB]
  change b = q + T * k
  simpa [Nat.add_comm] using hbdec

/-- `B_i ≠ 0` is exactly the statement that `2^(H+1)` does not divide
`5*r_i+3`. -/
theorem valuationAt_iff_not_two_pow_dvd
    (weight : Nat → Nat) (q i H : Nat)
    (hW : 1 ≤ weightAt weight i) (hq : q < 2 ^ weightAt weight i)
    (hrep : numerator weight i + 5 ^ i * q =
      2 ^ weightAt weight i * blockStateP weight q i) :
    valuationAt weight q i 0 H ↔
      ¬ 2 ^ (H + 1) ∣ 5 * blockStateP weight q i + 3 := by
  have h1 : QWindow.carryBalance
      (numerator weight i) (weightAt weight i) i q H ≠ 0 ↔
      ¬ StringFlow.Automaton.failureCongruence
        (numerator weight i) (weightAt weight i) i q H :=
    QWindow.carryBalance_ne_zero_iff_not_failure
      (numerator weight i) (weightAt weight i) i q H
      (blockStateP weight q i) hW hq hrep
  have h2 : (¬ StringFlow.Automaton.failureCongruence
      (numerator weight i) (weightAt weight i) i q H) ↔
      2 ^ weightAt weight i ≤ QWindow.badResidue
        (numerator weight i) (weightAt weight i) i
        (weightAt weight i + H + 1) :=
    QWindow.localLemma_iff_qV_ge
      (numerator weight i) (weightAt weight i) i q H hW hq
      ⟨blockStateP weight q i, hrep⟩
  have h3 : (2 ^ weightAt weight i ≤ QWindow.badResidue
      (numerator weight i) (weightAt weight i) i
        (weightAt weight i + H + 1)) ↔
      ¬ 2 ^ (H + 1) ∣ 5 * blockStateP weight q i + 3 :=
    QWindow.qV_ge_iff_not_two_pow_dvd
      (numerator weight i) (weightAt weight i) i q H
      (blockStateP weight q i) hW hq hrep
  unfold valuationAt carryBalanceP
  exact h1.trans (h2.trans h3)

/-- Therefore `B_i ≠ 0` is exactly the valuation statement
`X_i = v2(5*r_i+3) ≤ H`. -/
theorem valuationAt_iff_XAt_le
    (weight : Nat → Nat) (q i H : Nat)
    (hW : 1 ≤ weightAt weight i) (hq : q < 2 ^ weightAt weight i)
    (hrep : numerator weight i + 5 ^ i * q =
      2 ^ weightAt weight i * blockStateP weight q i) :
    valuationAt weight q i 0 H ↔ XAt weight q i ≤ H := by
  have hnotdvd := valuationAt_iff_not_two_pow_dvd
    weight q i H hW hq hrep
  have hpos : 0 < 5 * blockStateP weight q i + 3 := by positivity
  have hv : twoValuation (5 * blockStateP weight q i + 3) ≤ H ↔
      ¬ 2 ^ (H + 1) ∣ 5 * blockStateP weight q i + 3 :=
    StringFlow.Lte.twoValuation_le_iff_not_dvd_pow
      (5 * blockStateP weight q i + 3) H hpos
  simpa [XAt] using hnotdvd.trans hv.symm

/-- The general pure-block local lemma, without any orbit predicate. -/
def localLemmaGeneral (weight : Nat → Nat) (q : Nat) : Prop :=
  ∀ (i j Wp Wj : Nat),
    1 ≤ j →
    j ≤ i →
    Wp = weight (j - 1) →
    Wj = weight j →
    (Wj = Wp + 1 ∨ Wj = Wp + 2) →
    2 ^ Wp ≤ q →
    q < 2 ^ Wj →
    numerator weight j < 5 ^ j →
    (∀ k : Nat, k ≤ i →
      (numerator weight k + 5 ^ k * q) % 2 ^ weight k = 0) →
    (∀ k : Nat, k ≤ i → blockStateP weight q k < 5 ^ k) →
    localLemmaAt weight q i j

end StringFlow.PmiLocalLemma
