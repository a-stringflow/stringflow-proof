import Mathlib
import StageOneScan
import Td1Phase2
import RisingBound

/-!
# Phase-2 TD-0 bridge

This module connects the phase-2 Rat bound `m * t(P) >= 8/3` to the
`upperAt` window used by `Td1Window`, so that the phase-2 branch can
eventually be fed into the same final interval exclusion as stage one.
-/

namespace StringFlow.TD0

/-- The phase-2 prefix ratio `B = 5^L / 2^S`, written as
`2^(b-1) * a * x`. -/
def phase2B (b Q L : Nat) : Rat :=
  let P := L + Q
  let T := StringFlow.tCeil P
  let a : Rat := (8 / 5 : Rat) ^ Q
  let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
  (if b = 1 then a else 2 * a) * x

/-- Phase-2 upper branch with the correct `hmax` term `1/(3B)`.
This is the analytic form of `Rmax < U_bullet` from 52.16. -/
def upperBranch (b Q L m : Nat) : Bool :=
  let P := L + Q
  let T := StringFlow.tCeil P
  let U := StringFlow.uReq b Q L
  let a : Rat := (8 / 5 : Rat) ^ Q
  let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
  let B : Rat := phase2B b Q L
  let rho : Rat := (4 / 5 : Rat) ^ U
  let hmax : Rat := 1 - (2 / 3 : Rat) * rho - (1 : Rat) / (3 * B)
  let Ubr : Rat := if b = 1 then
      2 * a - (2 * a - (89 / 25 : Rat)) / (3 * (m : Rat))
    else
      4 * a - (4 * a - (29 / 5 : Rat)) / (3 * (m : Rat))
  let Rmax : Rat := B * (1 + hmax / (m : Rat))
  decide (Rmax < Ubr)

/-- `G_up` for the correct A-family `hmax` is still below `8/3`. -/
theorem gupA_correct_lt_eight_thirds (a x rho : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (89 / 75) / a - (1 / 3) / a < (8 / 3 : Rat) := by
  have hxle : x ≤ 2 := le_of_lt hx2
  have hcoef : 1 - (2 / 3 : Rat) * rho ≤ 1 := by nlinarith
  have hcoef0 : 0 ≤ 1 - (2 / 3 : Rat) * rho := by nlinarith
  have hmul : x * (1 - (2 / 3 : Rat) * rho) < 2 := by nlinarith
  have hapos : 0 < a := by nlinarith
  have hneg : 0 ≤ ((89 / 75 : Rat) + 1 / 3) / a := by
    positivity
  ring_nf at hmul hneg ⊢
  nlinarith

/-- `G_up` for the correct B-family `hmax` is still below `8/3`. -/
theorem gupB_correct_lt_eight_thirds (a x rho : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (17 / 15) / a < (8 / 3 : Rat) := by
  have hxle : x ≤ 2 := le_of_lt hx2
  have hcoef : 1 - (2 / 3 : Rat) * rho ≤ 1 := by nlinarith
  have hcoef0 : 0 ≤ 1 - (2 / 3 : Rat) * rho := by nlinarith
  have hmul : x * (1 - (2 / 3 : Rat) * rho) < 2 := by nlinarith
  have hapos : 0 < a := by nlinarith
  have hneg : 0 ≤ ((17 / 15 : Rat)) / a := by positivity
  ring_nf at hmul hneg ⊢
  nlinarith

/-- Correct A-family lower bound for `m*t` above `G_up`. -/
theorem mt_gt_gupA_correct_of_ge (a x rho mt : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hmt : mt ≥ (8 / 3 : Rat)) :
    mt > x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (89 / 75) / a - (1 / 3) / a := by
  have hg := gupA_correct_lt_eight_thirds a x rho ha1 hx0 hx2 hrho0 hrho1
  nlinarith

/-- Correct B-family lower bound for `m*t` above `G_up`. -/
theorem mt_gt_gupB_correct_of_ge (a x rho mt : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hmt : mt ≥ (8 / 3 : Rat)) :
    mt > x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (17 / 15) / a := by
  have hg := gupB_correct_lt_eight_thirds a x rho ha1 hx0 hx2 hrho0 hrho1
  nlinarith

/-- `G_up < 8/3` under the phase-2 monotonicity bounds
`0 <= x < 2`, `0 <= rho`, `0 < a`, `0 <= C`. -/
theorem gup_lt_eight_thirds (a x rho C : Rat)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hC0 : 0 ≤ C) :
    x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) - C / a <
      (8 / 3 : Rat) := by
  have hcoef : 1 - (2 / 3 : Rat) * rho ≤ 1 := by nlinarith
  have hcoef0 : 0 ≤ 1 - (2 / 3 : Rat) * rho := by nlinarith
  have hxle : x ≤ 2 := le_of_lt hx2
  have hmul : x * (1 - (2 / 3 : Rat) * rho) < 2 := by nlinarith
  have hCdiv : 0 ≤ C / a := div_nonneg hC0 (le_of_lt ha)
  nlinarith

/-- `mt >= 8/3` is strictly above `G_up` under the same bounds. -/
theorem mt_gt_gup_of_ge (a x rho C mt : Rat)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hC0 : 0 ≤ C)
    (hmt : mt ≥ (8 / 3 : Rat)) :
    mt > x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) - C / a := by
  have hg := gup_lt_eight_thirds a x rho C ha hx0 hx2 hrho0 hrho1 hC0
  nlinarith

/-- Exact A-family `G_up < 8/3`, matching `upperAt`. -/
theorem gupA_exact_lt_eight_thirds (a x rho : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    x * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) + (2 / 3 : Rat) -
        (89 / 75) / a < (8 / 3 : Rat) := by
  have hxle : x ≤ 2 := le_of_lt hx2
  have hinv : (1 / a : Rat) ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ ha1
  have hy0 : 0 ≤ (1 / a : Rat) := by
    have hapos : 0 < a := by nlinarith
    rw [one_div]
    exact inv_nonneg.mpr (le_of_lt hapos)
  have hdiv : (1 / (3 * a) : Rat) = (1 / 3) * (1 / a) := by ring
  have hthird : (1 / (3 * a) : Rat) ≤ 1 / 3 := by
    rw [hdiv]
    nlinarith
  have hcoef0 : 0 ≤ 1 - (2 / 3 : Rat) * rho - 1 / (3 * a) := by nlinarith
  have hmul : x * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) ≤
      2 * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) := by
    nlinarith
  have hc : (89 / 75 : Rat) / a = (89 / 75) * (1 / a) := by ring
  rw [hdiv] at hmul hcoef0 ⊢
  rw [hc]
  nlinarith

/-- Exact B-family `G_up < 8/3`, matching `upperAt`. -/
theorem gupB_exact_lt_eight_thirds (a x rho : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    x * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) + (2 / 3 : Rat) -
        (29 / 30) / a < (8 / 3 : Rat) := by
  have hxle : x ≤ 2 := le_of_lt hx2
  have hinv : (1 / a : Rat) ≤ 1 := by
    rw [one_div]
    exact inv_le_one_of_one_le₀ ha1
  have hy0 : 0 ≤ (1 / a : Rat) := by
    have hapos : 0 < a := by nlinarith
    rw [one_div]
    exact inv_nonneg.mpr (le_of_lt hapos)
  have hdiv : (1 / (6 * a) : Rat) = (1 / 6) * (1 / a) := by ring
  have hsixth : (1 / (6 * a) : Rat) ≤ 1 / 6 := by
    rw [hdiv]
    nlinarith
  have hcoef0 : 0 ≤ 1 - (2 / 3 : Rat) * rho - 1 / (6 * a) := by nlinarith
  have hmul : x * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) ≤
      2 * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) := by
    nlinarith
  have hc : (29 / 30 : Rat) / a = (29 / 30) * (1 / a) := by ring
  rw [hdiv] at hmul hcoef0 ⊢
  rw [hc]
  nlinarith

/-- Exact A-family: `mt >= 8/3` is above the exact `G_up`. -/
theorem mt_gt_gupA_of_ge (a x rho mt : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hmt : mt ≥ (8 / 3 : Rat)) :
    mt > x * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) + (2 / 3 : Rat) -
        (89 / 75) / a := by
  have hg := gupA_exact_lt_eight_thirds a x rho ha1 hx0 hx2 hrho0 hrho1
  nlinarith

/-- Exact B-family: `mt >= 8/3` is above the exact `G_up`. -/
theorem mt_gt_gupB_of_ge (a x rho mt : Rat)
    (ha1 : 1 ≤ a) (hx0 : 0 ≤ x) (hx2 : x < 2)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hmt : mt ≥ (8 / 3 : Rat)) :
    mt > x * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) + (2 / 3 : Rat) -
        (29 / 30) / a := by
  have hg := gupB_exact_lt_eight_thirds a x rho ha1 hx0 hx2 hrho0 hrho1
  nlinarith

/-- A-family `Rmax < U_A` is exactly `m * t > G_up`. -/
theorem aUpper_iff (a x rho m t : Rat)
    (ha : 0 < a) (hm : 0 < m) (ht : t = 2 - x) :
    (a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) / m) <
      2 * a - (2 * a - 89 / 25) / (3 * m)) ↔
      m * t > x * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) +
        (2 / 3 : Rat) - (89 / 75) / a := by
  rw [ht]
  constructor
  · intro h
    have hmul : (3 * a * m) * (a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) / m)) <
        (3 * a * m) * (2 * a - (2 * a - 89 / 25) / (3 * m)) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha] at ⊢
    ring_nf at ⊢
    nlinarith
  · intro h
    have hmul : (3 * a * m) * (m * (2 - x)) >
        (3 * a * m) * (x * (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) +
          (2 / 3 : Rat) - (89 / 75) / a) := by
      exact mul_lt_mul_of_pos_left h (by positivity)
    field_simp [ne_of_gt ha, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hm] at ⊢
    ring_nf at ⊢
    nlinarith

/-- B-family `Rmax < U_B` is exactly `m * t > G_up`. -/
theorem bUpper_iff (a x rho m t : Rat)
    (ha : 0 < a) (hm : 0 < m) (ht : t = 2 - x) :
    (2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) / m) <
      4 * a - (4 * a - 29 / 5) / (3 * m)) ↔
      m * t > x * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) +
        (2 / 3 : Rat) - (29 / 30) / a := by
  rw [ht]
  constructor
  · intro h
    have hmul : (3 * a * m) * (2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) / m)) <
        (3 * a * m) * (4 * a - (4 * a - 29 / 5) / (3 * m)) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha] at ⊢
    ring_nf at ⊢
    nlinarith
  · intro h
    have hmul : (3 * a * m) * (m * (2 - x)) >
        (3 * a * m) * (x * (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) +
          (2 / 3 : Rat) - (29 / 30) / a) := by
      exact mul_lt_mul_of_pos_left h (by positivity)
    field_simp [ne_of_gt ha, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hm] at ⊢
    ring_nf at ⊢
    nlinarith

/-- The phase-2 Rat bound `m * t(P) >= 8/3` makes `upperAt` true. -/
theorem upperAt_of_mt_ge (b Q L m : Nat)
    (hb : b = 1 ∨ b = 2) (hm : 0 < m)
    (hltpow : 5 ^ (L + Q) < 2 ^ StringFlow.tCeil (L + Q))
    (hmt : (m : Rat) * StringFlow.TD1.tRat (L + Q) ≥ (8 / 3 : Rat)) :
    StringFlow.upperAt b Q L m = true := by
  unfold StringFlow.upperAt
  apply decide_eq_true
  rcases hb with rfl | rfl
  · let P := L + Q
    let T := StringFlow.tCeil P
    let U := StringFlow.uReq 1 Q L
    let a : Rat := (8 / 5 : Rat) ^ Q
    let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
    let rho : Rat := (4 / 5 : Rat) ^ U
    have ht : StringFlow.TD1.tRat P = 2 - x := by
      dsimp [StringFlow.TD1.tRat, x, T]
      norm_num
      have hpow : (2 ^ T : Nat) ≠ 0 := by positivity
      have hpow0 : (2 ^ StringFlow.tCeil P : Nat) ≠ 0 := by positivity
      field_simp [hpow, hpow0]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hmRat : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
    have ha1 : 1 ≤ a := by
      dsimp [a]
      have h85 : (1 : Rat) ≤ 8 / 5 := by norm_num
      exact one_le_pow₀ h85
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hx2 : x < 2 := by
      dsimp [x]
      have h2cast : (2 ^ T : Rat) = ((2 ^ T : Nat) : Rat) := by norm_num
      rw [h2cast]
      have hpowpos : 0 < ((2 ^ T : Nat) : Rat) := by positivity
      rw [div_lt_iff₀ hpowpos]
      have hlt : ((5 ^ P : Nat) : Rat) < ((2 ^ T : Nat) : Rat) := by
        exact_mod_cast (by simpa [P, T] using hltpow)
      nlinarith
    have hrho0 : 0 ≤ rho := by
      dsimp [rho]
      positivity
    have hrho1 : rho ≤ 1 := by
      dsimp [rho]
      have h45 : (0 : Rat) ≤ 4 / 5 := by norm_num
      have h45le : (4 / 5 : Rat) ≤ 1 := by norm_num
      exact pow_le_one₀ h45 h45le
    have hgoal : a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (3 * a)) / (m : Rat)) <
        2 * a - (2 * a - 89 / 25) / (3 * (m : Rat)) :=
      (aUpper_iff a x rho (m : Rat) (StringFlow.TD1.tRat P) ha hmRat ht).2
        (mt_gt_gupA_of_ge a x rho (m * StringFlow.TD1.tRat P) ha1 hx0 hx2
          hrho0 hrho1 hmt)
    simpa [P, T, U, a, x, rho] using hgoal
  · let P := L + Q
    let T := StringFlow.tCeil P
    let U := StringFlow.uReq 2 Q L
    let a : Rat := (8 / 5 : Rat) ^ Q
    let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
    let rho : Rat := (4 / 5 : Rat) ^ U
    have ht : StringFlow.TD1.tRat P = 2 - x := by
      dsimp [StringFlow.TD1.tRat, x, T]
      norm_num
      have hpow : (2 ^ T : Nat) ≠ 0 := by positivity
      have hpow0 : (2 ^ StringFlow.tCeil P : Nat) ≠ 0 := by positivity
      field_simp [hpow, hpow0]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hmRat : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
    have ha1 : 1 ≤ a := by
      dsimp [a]
      have h85 : (1 : Rat) ≤ 8 / 5 := by norm_num
      exact one_le_pow₀ h85
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hx2 : x < 2 := by
      dsimp [x]
      have h2cast : (2 ^ T : Rat) = ((2 ^ T : Nat) : Rat) := by norm_num
      rw [h2cast]
      have hpowpos : 0 < ((2 ^ T : Nat) : Rat) := by positivity
      rw [div_lt_iff₀ hpowpos]
      have hlt : ((5 ^ P : Nat) : Rat) < ((2 ^ T : Nat) : Rat) := by
        exact_mod_cast (by simpa [P, T] using hltpow)
      nlinarith
    have hrho0 : 0 ≤ rho := by
      dsimp [rho]
      positivity
    have hrho1 : rho ≤ 1 := by
      dsimp [rho]
      have h45 : (0 : Rat) ≤ 4 / 5 := by norm_num
      have h45le : (4 / 5 : Rat) ≤ 1 := by norm_num
      exact pow_le_one₀ h45 h45le
    have hgoal : 2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (6 * a)) / (m : Rat)) <
        4 * a - (4 * a - 29 / 5) / (3 * (m : Rat)) :=
      (bUpper_iff a x rho (m : Rat) (StringFlow.TD1.tRat P) ha hmRat ht).2
        (mt_gt_gupB_of_ge a x rho (m * StringFlow.TD1.tRat P) ha1 hx0 hx2
          hrho0 hrho1 hmt)
    have hgoal' := hgoal
    ring_nf at hgoal'
    convert hgoal' using 1 <;> (dsimp [a, x, rho, U, P, T]; ring_nf)

/-- Correct A-family `Rmax < U_A` is exactly `m*t > G_up`. -/
theorem aUpperCorrect_iff (a x rho m t : Rat)
    (ha : 0 < a) (hx : 0 < x) (hm : 0 < m) (ht : t = 2 - x) :
    (a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (3 * a * x)) / m) <
      2 * a - (2 * a - 89 / 25) / (3 * m)) ↔
      m * t > x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (89 / 75) / a - (1 / 3) / a := by
  rw [ht]
  constructor
  · intro h
    have hmul : (3 * a * m) *
        (a * x * (1 + (1 - (2 / 3 : Rat) * rho - 1 / (3 * a * x)) / m)) <
        (3 * a * m) * (2 * a - (2 * a - 89 / 25) / (3 * m)) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hx] at ⊢
    ring_nf at ⊢
    nlinarith
  · intro h
    have hmul : (3 * a * m) * (m * (2 - x)) >
        (3 * a * m) * (x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
          (89 / 75) / a - (1 / 3) / a) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at ⊢
    ring_nf at ⊢
    nlinarith

/-- Correct B-family `Rmax < U_B` is exactly `m*t > G_up`. -/
theorem bUpperCorrect_iff (a x rho m t : Rat)
    (ha : 0 < a) (hx : 0 < x) (hm : 0 < m) (ht : t = 2 - x) :
    (2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho -
        1 / (3 * (2 * a * x))) / m) <
      4 * a - (4 * a - 29 / 5) / (3 * m)) ↔
      m * t > x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
        (17 / 15) / a := by
  rw [ht]
  constructor
  · intro h
    have hmul : (3 * a * m) *
        (2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho -
          1 / (3 * (2 * a * x))) / m)) <
        (3 * a * m) * (4 * a - (4 * a - 29 / 5) / (3 * m)) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hx] at ⊢
    ring_nf at ⊢
    nlinarith
  · intro h
    have hmul : (3 * a * m) * (m * (2 - x)) >
        (3 * a * m) * (x * (1 - (2 / 3 : Rat) * rho) + (2 / 3 : Rat) -
          (17 / 15) / a) := by
      have hpos : 0 < (3 * a * m : Rat) := by positivity
      exact mul_lt_mul_of_pos_left h hpos
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at hmul
    ring_nf at hmul
    field_simp [ne_of_gt ha, ne_of_gt hx, ne_of_gt hm] at ⊢
    ring_nf at ⊢
    nlinarith

/-- The phase-2 Rat bound `m*t(P) >= 8/3` makes the corrected
`upperBranch` true. -/
theorem upperBranch_of_mt_ge (b Q L m : Nat)
    (hb : b = 1 ∨ b = 2) (hm : 0 < m)
    (hltpow : 5 ^ (L + Q) < 2 ^ StringFlow.tCeil (L + Q))
    (hmt : (m : Rat) * StringFlow.TD1.tRat (L + Q) ≥ (8 / 3 : Rat)) :
    upperBranch b Q L m = true := by
  unfold upperBranch
  apply decide_eq_true
  rcases hb with rfl | rfl
  · let P := L + Q
    let T := StringFlow.tCeil P
    let U := StringFlow.uReq 1 Q L
    let a : Rat := (8 / 5 : Rat) ^ Q
    let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
    let rho : Rat := (4 / 5 : Rat) ^ U
    have ht : StringFlow.TD1.tRat P = 2 - x := by
      dsimp [StringFlow.TD1.tRat, x, T]
      norm_num
      have hpow : (2 ^ T : Nat) ≠ 0 := by positivity
      have hpow0 : (2 ^ StringFlow.tCeil P : Nat) ≠ 0 := by positivity
      field_simp [hpow, hpow0]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hmRat : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
    have ha1 : 1 ≤ a := by
      dsimp [a]
      have h85 : (1 : Rat) ≤ 8 / 5 := by norm_num
      exact one_le_pow₀ h85
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hx2 : x < 2 := by
      dsimp [x]
      have h2cast : (2 ^ T : Rat) = ((2 ^ T : Nat) : Rat) := by norm_num
      rw [h2cast]
      have hpowpos : 0 < ((2 ^ T : Nat) : Rat) := by positivity
      rw [div_lt_iff₀ hpowpos]
      have hlt : ((5 ^ P : Nat) : Rat) < ((2 ^ T : Nat) : Rat) := by
        exact_mod_cast (by simpa [P, T] using hltpow)
      nlinarith
    have hrho0 : 0 ≤ rho := by
      dsimp [rho]
      positivity
    have hrho1 : rho ≤ 1 := by
      dsimp [rho]
      have h45 : (0 : Rat) ≤ 4 / 5 := by norm_num
      have h45le : (4 / 5 : Rat) ≤ 1 := by norm_num
      exact pow_le_one₀ h45 h45le
    have hgoal : a * x * (1 + (1 - (2 / 3 : Rat) * rho -
        1 / (3 * a * x)) / (m : Rat)) <
        2 * a - (2 * a - 89 / 25) / (3 * (m : Rat)) :=
      (aUpperCorrect_iff a x rho (m : Rat) (StringFlow.TD1.tRat P)
        ha hxpos hmRat ht).2
        (mt_gt_gupA_correct_of_ge a x rho (m * StringFlow.TD1.tRat P)
          ha1 hx0 hx2 hrho0 hrho1 hmt)
    have hgoal' := hgoal
    ring_nf at hgoal'
    convert hgoal' using 1 <;> (dsimp [a, x, rho, U, P, T, phase2B]; ring_nf)
  · let P := L + Q
    let T := StringFlow.tCeil P
    let U := StringFlow.uReq 2 Q L
    let a : Rat := (8 / 5 : Rat) ^ Q
    let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
    let rho : Rat := (4 / 5 : Rat) ^ U
    have ht : StringFlow.TD1.tRat P = 2 - x := by
      dsimp [StringFlow.TD1.tRat, x, T]
      norm_num
      have hpow : (2 ^ T : Nat) ≠ 0 := by positivity
      have hpow0 : (2 ^ StringFlow.tCeil P : Nat) ≠ 0 := by positivity
      field_simp [hpow, hpow0]
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hmRat : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
    have ha1 : 1 ≤ a := by
      dsimp [a]
      have h85 : (1 : Rat) ≤ 8 / 5 := by norm_num
      exact one_le_pow₀ h85
    have hx0 : 0 ≤ x := by
      dsimp [x]
      positivity
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hx2 : x < 2 := by
      dsimp [x]
      have h2cast : (2 ^ T : Rat) = ((2 ^ T : Nat) : Rat) := by norm_num
      rw [h2cast]
      have hpowpos : 0 < ((2 ^ T : Nat) : Rat) := by positivity
      rw [div_lt_iff₀ hpowpos]
      have hlt : ((5 ^ P : Nat) : Rat) < ((2 ^ T : Nat) : Rat) := by
        exact_mod_cast (by simpa [P, T] using hltpow)
      nlinarith
    have hrho0 : 0 ≤ rho := by
      dsimp [rho]
      positivity
    have hrho1 : rho ≤ 1 := by
      dsimp [rho]
      have h45 : (0 : Rat) ≤ 4 / 5 := by norm_num
      have h45le : (4 / 5 : Rat) ≤ 1 := by norm_num
      exact pow_le_one₀ h45 h45le
    have hgoal : 2 * a * x * (1 + (1 - (2 / 3 : Rat) * rho -
        1 / (3 * (2 * a * x))) / (m : Rat)) <
        4 * a - (4 * a - 29 / 5) / (3 * (m : Rat)) :=
      (bUpperCorrect_iff a x rho (m : Rat) (StringFlow.TD1.tRat P)
        ha hxpos hmRat ht).2
        (mt_gt_gupB_correct_of_ge a x rho (m * StringFlow.TD1.tRat P)
          ha1 hx0 hx2 hrho0 hrho1 hmt)
    have hgoal' := hgoal
    ring_nf at hgoal'
    convert hgoal' using 1 <;> (dsimp [a, x, rho, U, P, T, phase2B]; ring_nf)

/-- Under the feasibility identity `T = L + 3Q + b + U`, the phase-2
ratio `B = 2^(b-1) a x` is `5^L / 2^(L+U)`. -/
theorem phase2B_eq (b Q L U : Nat)
    (hb : b = 1 ∨ b = 2)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U) :
    phase2B b Q L = (5 ^ L : Rat) / (2 ^ (L + U) : Rat) := by
  unfold phase2B
  rcases hb with rfl | rfl
  · simp [phase2B]
    have h85 : (8 / 5 : Rat) ^ Q =
        ((8 ^ Q : Nat) : Rat) / ((5 ^ Q : Nat) : Rat) := by
      rw [div_pow]
      norm_num
    have h8 : ((8 ^ Q : Nat) : Rat) = ((2 ^ (3 * Q) : Nat) : Rat) := by
      rw [show 8 = 2 ^ 3 by decide]
      rw [← Nat.pow_mul]
    have hcancel :
        ((2 ^ (3 * Q) : Nat) : Rat) * 2 * ((5 ^ (L + Q) : Nat) : Rat) *
            ((2 ^ (L + U) : Nat) : Rat) =
          ((5 ^ Q : Nat) : Rat) * ((2 ^ (L + 3 * Q + 1 + U) : Nat) : Rat) *
            ((5 ^ L : Nat) : Rat) := by
      have h5 : 5 ^ (L + Q) = 5 ^ L * 5 ^ Q := by rw [Nat.pow_add]
      have h2sum : L + 3 * Q + 1 + U = (L + U) + (3 * Q + 1) := by omega
      have h2 : 2 ^ (L + 3 * Q + 1 + U) = 2 ^ (L + U) * 2 ^ (3 * Q + 1) := by
        rw [h2sum, Nat.pow_add]
      have h2succ : 2 ^ (3 * Q + 1) = 2 ^ (3 * Q) * 2 := by rw [Nat.pow_succ]
      rw [h5, h2, h2succ]
      simp [Nat.cast_mul, Nat.cast_pow]
      ring
    rw [hT, h85, h8]
    field_simp
    simpa [Nat.cast_pow] using hcancel
  · simp [phase2B]
    have h85 : (8 / 5 : Rat) ^ Q =
        ((8 ^ Q : Nat) : Rat) / ((5 ^ Q : Nat) : Rat) := by
      rw [div_pow]
      norm_num
    have h8 : ((8 ^ Q : Nat) : Rat) = ((2 ^ (3 * Q) : Nat) : Rat) := by
      rw [show 8 = 2 ^ 3 by decide]
      rw [← Nat.pow_mul]
    have hcancel :
        (2 ^ 2 : Rat) * ((2 ^ (3 * Q) : Nat) : Rat) *
            ((5 ^ (L + Q) : Nat) : Rat) * ((2 ^ (L + U) : Nat) : Rat) =
          ((5 ^ Q : Nat) : Rat) * ((2 ^ (L + 3 * Q + 2 + U) : Nat) : Rat) *
            ((5 ^ L : Nat) : Rat) := by
      have h5 : 5 ^ (L + Q) = 5 ^ L * 5 ^ Q := by rw [Nat.pow_add]
      have h2sum : L + 3 * Q + 2 + U = (L + U) + (3 * Q + 2) := by omega
      have h2 : 2 ^ (L + 3 * Q + 2 + U) = 2 ^ (L + U) * 2 ^ (3 * Q + 2) := by
        rw [h2sum, Nat.pow_add]
      have h2succ : 2 ^ (3 * Q + 2) = 2 ^ (3 * Q) * 4 := by
        have h1 : 3 * Q + 2 = (3 * Q) + 2 := by omega
        rw [h1, Nat.pow_add]
      rw [h5, h2, h2succ]
      simp [Nat.cast_mul, Nat.cast_pow]
      ring
    rw [hT, h85, h8]
    field_simp
    simpa [Nat.cast_pow] using hcancel

/-- Propositional form of the A-family corrected upper branch. -/
theorem upperBranchA_prop (Q L m : Nat)
    (hUp : upperBranch 1 Q L m = true) :
    (let P := L + Q
     let T := StringFlow.tCeil P
     let U := StringFlow.uReq 1 Q L
     let a : Rat := (8 / 5 : Rat) ^ Q
     let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
     let B : Rat := phase2B 1 Q L
     let rho : Rat := (4 / 5 : Rat) ^ U
     B * (1 + (1 - (2 / 3 : Rat) * rho - (1 : Rat) / (3 * B)) / (m : Rat)) <
       2 * a - (2 * a - (89 / 25 : Rat)) / (3 * (m : Rat))) := by
  simpa [upperBranch] using (of_decide_eq_true hUp)

/-- Propositional form of the B-family corrected upper branch. -/
theorem upperBranchB_prop (Q L m : Nat)
    (hUp : upperBranch 2 Q L m = true) :
    (let P := L + Q
     let T := StringFlow.tCeil P
     let U := StringFlow.uReq 2 Q L
     let a : Rat := (8 / 5 : Rat) ^ Q
     let x : Rat := (2 * (5 ^ P : Nat) : Rat) / (2 ^ T : Rat)
     let B : Rat := phase2B 2 Q L
     let rho : Rat := (4 / 5 : Rat) ^ U
     B * (1 + (1 - (2 / 3 : Rat) * rho - (1 : Rat) / (3 * B)) / (m : Rat)) <
       4 * a - (4 * a - (29 / 5 : Rat)) / (3 * (m : Rat))) := by
  simpa [upperBranch] using (of_decide_eq_true hUp)

end StringFlow.TD0
