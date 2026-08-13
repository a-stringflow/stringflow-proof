import FinitePrefix
import UnifiedCoreAudit

/-!
# Bridge definitions from document 36.30.23 to the unified core

Definitions only; proofs are added in later assembly steps.
-/

namespace S6Audit

/-- 36.30.23.4: candidate predecessor `x` in terms of the orbit state
`g`, incoming weight `e`, and reset parameter `δ`. -/
def candidateX (j e g δ : Nat) : Nat :=
  2 ^ (e - 1) * g + δ * 5 ^ (j - 1)

/-- Candidate block head reached from `x` by the reset step of weight `t`. -/
def candidateRj (x t : Nat) : Nat :=
  (5 * x + 1) / 2 ^ t

/-- `g` is the actual full-orbit state at depth `j-1`. -/
def orbitState (j g : Nat) : Prop :=
  fullOrbitIter (j - 1) = g

/-- The full-orbit step weight at depth `n`. -/
def orbitStepWeight (n : Nat) : Nat :=
  twoValuation (5 * fullOrbitIter n + 1)

/-- If `fullOrbitIter n = y` and `5*y+1 = 2^k*x` with `x` odd, then the
step weight at depth `n` is exactly `k`. -/
lemma orbitStepWeight_of_mul (n k y x : Nat)
    (hy : fullOrbitIter n = y)
    (hxodd : x % 2 = 1)
    (hstep : 5 * y + 1 = 2 ^ k * x) :
    orbitStepWeight n = k := by
  unfold orbitStepWeight
  rw [hy, hstep]
  exact StringFlow.Lte.twoValuation_mul_two_pow_eq k x hxodd

/-- `5x+1` is even for odd `x`, so its exact step weight is at least 1. -/
lemma twoValuation_five_mul_add_one_ge_one (x : Nat) (hodd : IsOdd x) :
    1 ≤ twoValuation (5 * x + 1) := by
  have hpos : 0 < 5 * x + 1 := by positivity
  have heven : (5 * x + 1) % 2 = 0 := by
    have hx : x % 2 = 1 := hodd
    have h5x : (5 * x) % 2 = 1 := by
      rw [Nat.mul_mod]
      rw [show 5 % 2 = 1 by norm_num, hx]
    rw [Nat.add_mod, h5x]
  have hdiv : 2 ^ 1 ∣ 5 * x + 1 := by
    have h2 : 2 ∣ 5 * x + 1 := Nat.dvd_of_mod_eq_zero heven
    simpa using h2
  exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * x + 1) 1 hpos).mpr hdiv

/-- From an odd state, the exact accelerated step divides by at least
`2`, so its output is no larger than the `t=1` quotient. -/
lemma fullOrbitStep_le_div_two (x : Nat) (hodd : IsOdd x) :
    fullOrbitStep x ≤ (5 * x + 1) / 2 := by
  unfold fullOrbitStep
  have hge1 : 1 ≤ twoValuation (5 * x + 1) :=
    twoValuation_five_mul_add_one_ge_one x hodd
  have hpow : 2 ≤ 2 ^ twoValuation (5 * x + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hge1
  have hq2 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) * 2 ≤
      5 * x + 1 := by
    have h1 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) * 2 ≤
        (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) *
          2 ^ twoValuation (5 * x + 1) :=
      Nat.mul_le_mul_left
        ((5 * x + 1) / 2 ^ twoValuation (5 * x + 1)) hpow
    have h2 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) *
        2 ^ twoValuation (5 * x + 1) ≤ 5 * x + 1 :=
      Nat.div_mul_le_self (5 * x + 1) (2 ^ twoValuation (5 * x + 1))
    exact le_trans h1 h2
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 hq2

/-- `2^n ≤ 5^n` for every `n`. -/
lemma pow_two_le_pow_five (n : Nat) : 2 ^ n ≤ 5 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        _ ≤ 2 * 5 ^ n := Nat.mul_le_mul_left 2 ih
        _ ≤ 5 * 5 ^ n := Nat.mul_le_mul_right (5 ^ n) (by norm_num)
        _ = 5 ^ (n + 1) := by rw [pow_succ]; ring

/-- Every full-orbit state satisfies the all-`t=1` upper bound
`3 * 2^n * r_n ≤ 22 * 5^n - 2^n`. -/
theorem fullOrbitIter_upper_bound (n : Nat) :
    3 * 2 ^ n * fullOrbitIter n ≤ 22 * 5 ^ n - 2 ^ n := by
  induction n with
  | zero => norm_num [fullOrbitIter]
  | succ n ih =>
      have hodd : IsOdd (fullOrbitIter n) := fullOrbitIter_odd n
      have hle := fullOrbitStep_le_div_two (fullOrbitIter n) hodd
      have heven : (5 * fullOrbitIter n + 1) % 2 = 0 := by
        have hx : fullOrbitIter n % 2 = 1 := hodd
        have h5x : (5 * fullOrbitIter n) % 2 = 1 := by
          rw [Nat.mul_mod]
          rw [show 5 % 2 = 1 by norm_num, hx]
        rw [Nat.add_mod, h5x]
      have hdiv2 : 2 ∣ 5 * fullOrbitIter n + 1 := Nat.dvd_of_mod_eq_zero heven
      let z := (5 * fullOrbitIter n + 1) / 2
      have hz : 2 * z = 5 * fullOrbitIter n + 1 := by
        dsimp [z]
        exact Nat.mul_div_cancel' hdiv2
      have hstep : fullOrbitIter (n + 1) = fullOrbitStep (fullOrbitIter n) := rfl
      rw [hstep]
      have hmul1 : 3 * 2 ^ (n + 1) * fullOrbitStep (fullOrbitIter n) ≤
          3 * 2 ^ (n + 1) * z :=
        Nat.mul_le_mul_left (3 * 2 ^ (n + 1)) (by simpa [z] using hle)
      have hcal : 3 * 2 ^ (n + 1) * z =
          3 * 2 ^ n * (5 * fullOrbitIter n + 1) := by
        have hpow2 : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [pow_succ]
          ring
        calc
          3 * 2 ^ (n + 1) * z = 3 * (2 * 2 ^ n) * z := by rw [hpow2]
          _ = 3 * 2 ^ n * (2 * z) := by ring
          _ = 3 * 2 ^ n * (5 * fullOrbitIter n + 1) := by rw [hz]
      have h5 : 3 * 2 ^ n * (5 * fullOrbitIter n + 1) =
          5 * (3 * 2 ^ n * fullOrbitIter n) + 3 * 2 ^ n := by ring
      have hih5 : 5 * (3 * 2 ^ n * fullOrbitIter n) + 3 * 2 ^ n ≤
          5 * (22 * 5 ^ n - 2 ^ n) + 3 * 2 ^ n := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 ih) (3 * 2 ^ n)
      have hge : 2 ^ n ≤ 22 * 5 ^ n := by
        have h1 : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by norm_num)
        have hQle : 2 ^ n ≤ 5 ^ n := pow_two_le_pow_five n
        nlinarith
      have hrhs : 5 * (22 * 5 ^ n - 2 ^ n) + 3 * 2 ^ n =
          22 * 5 ^ (n + 1) - 2 ^ (n + 1) := by
        rw [pow_succ]
        have hsub : 5 * (22 * 5 ^ n - 2 ^ n) = 110 * 5 ^ n - 5 * 2 ^ n := by
          rw [Nat.mul_sub_left_distrib]
          ring_nf
        rw [hsub]
        have hpow2 : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [pow_succ]
          ring
        rw [hpow2]
        omega
      have hgoal1 : 3 * 2 ^ (n + 1) * fullOrbitStep (fullOrbitIter n) ≤
          5 * (3 * 2 ^ n * fullOrbitIter n) + 3 * 2 ^ n := by
        exact le_trans hmul1 (by rw [hcal, h5])
      have hgoal2 : 5 * (3 * 2 ^ n * fullOrbitIter n) + 3 * 2 ^ n ≤
          22 * 5 ^ (n + 1) - 2 ^ (n + 1) := by
        exact le_trans hih5 (by rw [hrhs])
      exact le_trans hgoal1 hgoal2

/-- The corrected `d=2` survivor is too large to be a full-orbit state
once `n ≥ 5`: `g=(4*5^n-7)/17` exceeds the all-`t=1` upper bound. -/
theorem d2_survivor_size_contradiction (n : Nat) (hn : 5 ≤ n)
    (hg : 17 * fullOrbitIter n = 4 * 5 ^ n - 7) : False := by
  have hbound := fullOrbitIter_upper_bound n
  have hle17 : 17 * (3 * 2 ^ n * fullOrbitIter n) ≤
      17 * (22 * 5 ^ n - 2 ^ n) :=
    Nat.mul_le_mul_left 17 hbound
  have hleft : 17 * (3 * 2 ^ n * fullOrbitIter n) =
      3 * 2 ^ n * (17 * fullOrbitIter n) := by ring
  rw [hleft, hg] at hle17
  have hP : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by norm_num)
  have hQle : 2 ^ n ≤ 5 ^ n := pow_two_le_pow_five n
  have hQge : 32 ≤ 2 ^ n := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    norm_num at h ⊢
    exact h
  have hge7 : 7 ≤ 4 * 5 ^ n := by nlinarith [hP]
  have hge2 : 2 ^ n ≤ 22 * 5 ^ n := by nlinarith [hP, hQle]
  have h10 : 10 ^ n = 2 ^ n * 5 ^ n := by
    rw [show 10 = 2 * 5 by norm_num, Nat.mul_pow]
  have hL : 3 * 2 ^ n * (4 * 5 ^ n - 7) = 12 * 2 ^ n * 5 ^ n - 21 * 2 ^ n := by
    rw [Nat.mul_sub_left_distrib]
    ring_nf
  have hR : 17 * (22 * 5 ^ n - 2 ^ n) = 374 * 5 ^ n - 17 * 2 ^ n := by
    rw [Nat.mul_sub_left_distrib]
    ring_nf
  have hineq : 17 * (22 * 5 ^ n - 2 ^ n) < 3 * 2 ^ n * (4 * 5 ^ n - 7) := by
    rw [hR, hL]
    have hmain : 374 * 5 ^ n + 4 * 2 ^ n < 12 * (2 ^ n * 5 ^ n) := by
      have hA : 374 * 5 ^ n + 4 * 2 ^ n ≤ 378 * 5 ^ n := by
        have h4 : 4 * 2 ^ n ≤ 4 * 5 ^ n := Nat.mul_le_mul_left 4 hQle
        nlinarith
      have hB : 378 * 5 ^ n < 384 * 5 ^ n := by nlinarith [hP]
      have hC : 384 * 5 ^ n ≤ 12 * (2 ^ n * 5 ^ n) := by
        have h32 : 32 * 5 ^ n ≤ 2 ^ n * 5 ^ n :=
          Nat.mul_le_mul_right (5 ^ n) hQge
        nlinarith
      nlinarith
    have hA : 21 * 2 ^ n ≤ 12 * 2 ^ n * 5 ^ n := by nlinarith [hQle, hP]
    have hB : 17 * 2 ^ n ≤ 374 * 5 ^ n := by nlinarith [hQle, hP]
    have hmain' : 374 * 5 ^ n + 4 * 2 ^ n < 12 * 2 ^ n * 5 ^ n := by
      nlinarith [hmain]
    omega
  exact (not_lt_of_ge hle17) hineq

/-- The corrected `d=2` survivor family is excluded for `j ≥ 6` by the
full-orbit size bound; the only small case is `j=4`, which is already in
the finite base. -/
theorem d2_exclusion_of_corrected_residue (j g : Nat)
    (hj : 6 ≤ j)
    (hseg : 8 * g + 4 * 5 ^ (j - 1) = 7 + 25 * g)
    (_hxmod : candidateX j 2 g 1 % 320 = 183)
    (hiter : fullOrbitIter (j - 1) = g) : False := by
  let n := j - 1
  let P := 5 ^ n
  have hn : 5 ≤ n := by dsimp [n]; omega
  have h17g : 4 * P = 7 + 17 * g := by
    dsimp [P, n]
    nlinarith [hseg]
  have hge7 : 7 ≤ 4 * P := by
    have h1 : 1 ≤ P := by
      dsimp [P]
      exact Nat.one_le_pow n 5 (by norm_num)
    nlinarith
  have hg17 : 17 * g = 4 * P - 7 := by
    omega
  have hgh : 17 * fullOrbitIter n = 4 * P - 7 := by
    dsimp [n]
    rw [hiter]
    exact hg17
  exact d2_survivor_size_contradiction n hn (by simpa [P] using hgh)

/-- The depth-16 full-orbit step is small: `t_16 = 1`. -/
lemma orbitStepWeight_16_eq_one : orbitStepWeight 16 = 1 := by
  unfold orbitStepWeight
  exact fullOrbit_prefix_step_weights_17.1

/-- The depth-17 full-orbit step is already big: `t_17 = 4`. -/
lemma orbitStepWeight_17_ge_three : 3 ≤ orbitStepWeight 17 := by
  unfold orbitStepWeight
  rw [fullOrbit_prefix_step_weights_17.2]
  norm_num

/-- A `t=2` exact step cannot occur at full-orbit depths 16 or 17: the
depth-16 step is `t=1`, and the depth-17 step is `t=4`. -/
lemma no_t2_step_at_depth_16_17 (n_a : Nat)
    (hweight : orbitStepWeight n_a = 2) :
    n_a ≠ 16 ∧ n_a ≠ 17 := by
  constructor
  · intro h16
    rw [h16] at hweight
    have h16w : orbitStepWeight 16 = 1 := orbitStepWeight_16_eq_one
    omega
  · intro h17
    rw [h17] at hweight
    have h17w : 3 ≤ orbitStepWeight 17 := orbitStepWeight_17_ge_three
    omega

/-- From `2*q ≡ 1 (mod 5)`, the inverse `2^{-1} ≡ 3 (mod 5)` forces
`q ≡ 3 (mod 5)`. -/
lemma mod5_cancel_two (q : Nat) (h : (2 * q) % 5 = 1) : q % 5 = 3 := by
  have hmod : 2 * q ≡ 1 [MOD 5] := by rw [Nat.ModEq]; exact h
  have h6 : 6 ≡ 1 [MOD 5] := by norm_num [Nat.ModEq]
  have hq3 : q ≡ 3 [MOD 5] := by
    have h1 := hmod.mul_right 3
    have hleft : (2 * q) * 3 ≡ q [MOD 5] := by
      rw [show (2 * q) * 3 = q * 6 by ring]
      simpa using h6.mul_left q
    exact hleft.symm.trans h1
  rw [Nat.ModEq] at hq3
  norm_num at hq3
  exact hq3

/-- From `4*q ≡ 1 (mod 5)`, the inverse `4^{-1} ≡ 4 (mod 5)` forces
`q ≡ 4 (mod 5)`. -/
lemma mod5_cancel_four (q : Nat) (h : (4 * q) % 5 = 1) : q % 5 = 4 := by
  have hmod : 4 * q ≡ 1 [MOD 5] := by rw [Nat.ModEq]; exact h
  have h16 : 16 ≡ 1 [MOD 5] := by norm_num [Nat.ModEq]
  have hq4 : q ≡ 4 [MOD 5] := by
    have h1 := hmod.mul_right 4
    have hleft : (4 * q) * 4 ≡ q [MOD 5] := by
      rw [show (4 * q) * 4 = q * 16 by ring]
      simpa using h16.mul_left q
    exact hleft.symm.trans h1
  rw [Nat.ModEq] at hq4
  norm_num at hq4
  exact hq4

/-- A legal `t=1` or `t=2` step always lands in `3` or `4` modulo `5`,
since `2^-1 ≡ 3` and `2^-2 ≡ 4` modulo `5`. -/
lemma legal_step_next_mod5 (x t : Nat) (ht : t = 1 ∨ t = 2)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    ((5 * x + 1) / 2 ^ t) % 5 = 3 ∨ ((5 * x + 1) / 2 ^ t) % 5 = 4 := by
  have hmod1 : (5 * x + 1) % 5 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  rcases ht with rfl | rfl
  · have hdvd : 2 ∣ 5 * x + 1 := by
      simpa [Nat.pow_one] using Nat.dvd_iff_mod_eq_zero.mpr hdiv
    have hmul : 2 * ((5 * x + 1) / 2) = 5 * x + 1 := Nat.mul_div_cancel' hdvd
    have hq2 : (2 * ((5 * x + 1) / 2)) % 5 = 1 := by
      rw [hmul]
      exact hmod1
    have hq : ((5 * x + 1) / 2) % 5 = 3 := mod5_cancel_two ((5 * x + 1) / 2) hq2
    left
    exact hq
  · have hdvd : 2 ^ 2 ∣ 5 * x + 1 := by
      simpa [Nat.pow_two] using Nat.dvd_iff_mod_eq_zero.mpr hdiv
    have hmul : 4 * ((5 * x + 1) / 4) = 5 * x + 1 := Nat.mul_div_cancel' hdvd
    have hq4 : (4 * ((5 * x + 1) / 4)) % 5 = 1 := by
      rw [hmul]
      exact hmod1
    have hq : ((5 * x + 1) / 4) % 5 = 4 := mod5_cancel_four ((5 * x + 1) / 4) hq4
    right
    exact hq

/-- 36.30.9.1: from the reset equation and `rj=(5x+1)/2^t`, the full
predecessor is `x = 5^k*s0 + δ*5^(j-1) - 1`. -/
theorem reset_head_predecessor (s0 j k t δ rj x : Nat)
    (hj : 1 ≤ j)
    (hres : ResetHeadEq s0 j k t δ rj)
    (hrj : rj = (5 * x + 1) / 2 ^ t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x = 5 ^ k * s0 + δ * 5 ^ (j - 1) - 1 := by
  have hmul : 2 ^ t * rj = 5 * x + 1 := by
    rw [hrj]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  rcases hres with h1 | h2
  · rcases h1 with ⟨ht, hδ, heq⟩
    subst t
    subst δ
    have hplus : 2 * (rj + 1) + 2 = 5 ^ (k + 1) * s0 + 5 ^ j := by omega
    have hleft : 2 * (rj + 1) + 2 = 5 * x + 5 := by
      nlinarith [hmul]
    have hpow : 5 ^ (k + 1) = 5 * 5 ^ k := by rw [Nat.pow_succ]; ring
    have hpowj : 5 ^ j = 5 * 5 ^ (j - 1) := by
      have h : j = (j - 1) + 1 := by omega
      calc
        5 ^ j = 5 ^ ((j - 1) + 1) := by conv_lhs => rw [h]
        _ = 5 ^ (j - 1) * 5 := by rw [Nat.pow_add, Nat.pow_one]
        _ = 5 * 5 ^ (j - 1) := by ring
    have h5 : 5 * (x + 1) = 5 * (5 ^ k * s0 + 5 ^ (j - 1)) := by
      nlinarith [hplus, hleft, hpow, hpowj]
    have hx : x + 1 = 5 ^ k * s0 + 5 ^ (j - 1) := by
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h5
    omega
  · rcases h2 with ⟨ht, hδ, heq⟩
    subst t
    have hleft : 4 * (rj + 1) = 5 * x + 5 := by
      nlinarith [hmul]
    have hpow : 5 ^ (k + 1) = 5 * 5 ^ k := by rw [Nat.pow_succ]; ring
    have hpowj : 5 ^ j = 5 * 5 ^ (j - 1) := by
      have h : j = (j - 1) + 1 := by omega
      calc
        5 ^ j = 5 ^ ((j - 1) + 1) := by conv_lhs => rw [h]
        _ = 5 ^ (j - 1) * 5 := by rw [Nat.pow_add, Nat.pow_one]
        _ = 5 * 5 ^ (j - 1) := by ring
    have h5 : 5 * (x + 1) = 5 * (5 ^ k * s0 + δ * 5 ^ (j - 1)) := by
      nlinarith [heq, hleft, hpow, hpowj]
    have hx : x + 1 = 5 ^ k * s0 + δ * 5 ^ (j - 1) := by
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h5
    omega

/-- The reset exponent is `k=0` exactly when the predecessor satisfies
`5 ∤ x+1`: for `j ≥ 2`, `k ≥ 1` forces `5 | x+1`.  This is the precise
premise the `d≥2` bridge needs; the residue classes `x ≡ 21 (mod 32)` /
`x ≡ 55 (mod 64)` alone do NOT imply `5 ∤ x+1`. -/
theorem reset_k_eq_zero_of_not_five_dvd_x1
    (s0 j k t δ rj x : Nat) (hj : 2 ≤ j)
    (hres : ResetHeadEq s0 j k t δ rj)
    (hrj : rj = (5 * x + 1) / 2 ^ t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0)
    (h5 : ¬ 5 ∣ x + 1) :
    k = 0 := by
  have hx1 := reset_head_predecessor s0 j k t δ rj x (by omega) hres hrj hdiv
  have hdpos : 0 < δ * 5 ^ (j - 1) := by
    rcases hres with h1 | h2
    · rcases h1 with ⟨ht, hδ, _⟩
      subst δ
      positivity
    · rcases h2 with ⟨ht, hδ, _⟩
      rcases hδ with hδ1 | hδ3
      · subst δ
        positivity
      · subst δ
        positivity
  have hge1 : 1 ≤ 5 ^ k * s0 + δ * 5 ^ (j - 1) := by omega
  have hx1' : x + 1 = 5 ^ k * s0 + δ * 5 ^ (j - 1) := by
    rw [hx1]
    omega
  by_contra hk
  have hk1 : 1 ≤ k := by omega
  have hdivA : 5 ∣ 5 ^ k * s0 := by
    refine ⟨5 ^ (k - 1) * s0, ?_⟩
    have hpow : 5 ^ k = 5 * 5 ^ (k - 1) := by
      have hk : k = (k - 1) + 1 := by omega
      calc
        5 ^ k = 5 ^ ((k - 1) + 1) := by conv_lhs => rw [hk]
        _ = 5 * 5 ^ (k - 1) := by rw [Nat.pow_add, Nat.pow_one]; ring
    rw [hpow]
    ring
  have hdivB : 5 ∣ δ * 5 ^ (j - 1) := by
    refine ⟨δ * 5 ^ (j - 2), ?_⟩
    have hpow : 5 ^ (j - 1) = 5 * 5 ^ (j - 2) := by
      have hj' : j - 1 = (j - 2) + 1 := by omega
      calc
        5 ^ (j - 1) = 5 ^ ((j - 2) + 1) := by conv_lhs => rw [hj']
        _ = 5 * 5 ^ (j - 2) := by rw [Nat.pow_add, Nat.pow_one]; ring
    rw [hpow]
    ring
  have hdiv5 : 5 ∣ x + 1 := by
    rw [hx1']
    exact dvd_add hdivA hdivB
  exact h5 hdiv5

/-- Generalized 36.30.23.3+23.4: the terminal-chain identity
`5^k*s0 = 2^(e-1)*g+1` (valid for every `k`) makes the reset
predecessor exactly `candidateX`. -/
theorem candidateX_of_reset_and_terminal_general
    (s0 j k t δ rj x e g : Nat) (hj : 1 ≤ j)
    (hres : ResetHeadEq s0 j k t δ rj)
    (hrj : rj = (5 * x + 1) / 2 ^ t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0)
    (hterm : 5 ^ k * s0 = 2 ^ (e - 1) * g + 1) :
    x = candidateX j e g δ := by
  have hx := reset_head_predecessor s0 j k t δ rj x hj hres hrj hdiv
  have hdpos : 0 < δ * 5 ^ (j - 1) := by
    rcases hres with h1 | h2
    · rcases h1 with ⟨ht, hδ, _⟩
      subst δ
      positivity
    · rcases h2 with ⟨ht, hδ, _⟩
      rcases hδ with hδ1 | hδ3
      · subst δ
        positivity
      · subst δ
        positivity
  have hge1 : 1 ≤ 5 ^ k * s0 + δ * 5 ^ (j - 1) := by omega
  have hx1 : x + 1 = 5 ^ k * s0 + δ * 5 ^ (j - 1) := by
    rw [hx]
    omega
  have hx2 : x + 1 = 2 ^ (e - 1) * g + 1 + δ * 5 ^ (j - 1) := by
    rw [hx1, hterm]
  have hx3 : x = 2 ^ (e - 1) * g + δ * 5 ^ (j - 1) := by omega
  unfold candidateX
  exact hx3

/-- 36.30.23.3+23.4: with `k=0` and the first-block terminal
`s0-1 = 2^(e-1)*g`, the reset predecessor is exactly `candidateX`. -/
theorem candidateX_of_reset_and_terminal
    (s0 j t δ rj x e g : Nat)
    (hj : 1 ≤ j)
    (hres : ResetHeadEq s0 j 0 t δ rj)
    (hrj : rj = (5 * x + 1) / 2 ^ t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0)
    (hterm : s0 = 2 ^ (e - 1) * g + 1) :
    x = candidateX j e g δ := by
  have hx := reset_head_predecessor s0 j 0 t δ rj x hj hres hrj hdiv
  have hx' : x = s0 + δ * 5 ^ (j - 1) - 1 := by simpa using hx
  unfold candidateX
  omega

/-- 36.30.23.3: if `5*g_prev+1=2^e*g` and `r=(5*g_prev+1)/2`, then
`r=2^(e-1)*g`. -/
theorem first_block_terminal_eq (e g_prev g r : Nat)
    (hg : 5 * g_prev + 1 = 2 ^ e * g)
    (hr : r = (5 * g_prev + 1) / 2)
    (he : 1 ≤ e) :
    r = 2 ^ (e - 1) * g := by
  have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
    have h : e = (e - 1) + 1 := by omega
    calc
      2 ^ e = 2 ^ ((e - 1) + 1) := by conv_lhs => rw [h]
      _ = 2 ^ (e - 1) * 2 := by rw [Nat.pow_add, Nat.pow_one]
      _ = 2 * 2 ^ (e - 1) := by ring
  have hdiv : (5 * g_prev + 1) % 2 = 0 := by
    rw [hg, hpow]
    rw [Nat.mul_mod]
    have h2 : (2 * 2 ^ (e - 1)) % 2 = 0 := by
      rw [Nat.mul_mod, Nat.mod_self]
      simp
    simp [h2]
  have hmul : 2 * r = 5 * g_prev + 1 := by
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have h2r : 2 * r = 2 ^ e * g := by rw [hmul, hg]
  have h2r' : 2 * r = 2 * (2 ^ (e - 1) * g) := by
    rw [h2r, hpow]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2r'

/-- The terminal-chain identity: `5^k0*s = r+1` and `r = 2^(e-1)*g`
imply `5^k0*s = 2^(e-1)*g+1`.  This is the exact bridge input for every
`k0`, not only `k0=0`. -/
theorem terminal_chain_identity (k0 s r g e g_prev : Nat)
    (hprod : s * 5 ^ k0 = r + 1)
    (hstep : 5 * g_prev + 1 = 2 ^ e * g)
    (hr : r = (5 * g_prev + 1) / 2)
    (he : 1 ≤ e) :
    5 ^ k0 * s = 2 ^ (e - 1) * g + 1 := by
  have hterm0 := first_block_terminal_eq e g_prev g r hstep hr he
  calc
    5 ^ k0 * s = r + 1 := by rw [Nat.mul_comm]; exact hprod
    _ = 2 ^ (e - 1) * g + 1 := by rw [hterm0]

/-- 36.30.8.2: from the exact identity `A_j + 5^j*q = 2^L*(B+δ*5^j)`
with `0 < B < 5^j` and `A_j < 5^j`, the `q` is `m + δ*2^L` with
`m < 2^L`. -/
theorem reset_q0_form (j L δ A_j q B : Nat)
    (hA : A_j < 5 ^ j)
    (hB : 0 < B) (hBlt : B < 5 ^ j)
    (_hδ : δ = 1 ∨ δ = 3)
    (hrep : A_j + 5 ^ j * q = 2 ^ L * (B + δ * 5 ^ j)) :
    ∃ m : Nat, q = m + δ * 2 ^ L ∧ m < 2 ^ L := by
  have hpos5 : 0 < 5 ^ j := by positivity
  have hrep' : A_j + 5 ^ j * q = 2 ^ L * B + δ * 2 ^ L * 5 ^ j := by
    rw [hrep]
    ring
  have hA1 : A_j + 1 ≤ 5 ^ j := Nat.succ_le_of_lt hA
  have hqge : δ * 2 ^ L ≤ q := by
    by_contra hnot
    have hq1 : q + 1 ≤ δ * 2 ^ L := by omega
    have hleLHS' : A_j + 5 ^ j * q + 1 ≤ 5 ^ j * (δ * 2 ^ L) := by
      nlinarith [hA1, hq1, hpos5]
    have hB1 : 1 ≤ B := hB
    have hleRHS : 5 ^ j * (δ * 2 ^ L) + 1 ≤ 2 ^ L * B + δ * 2 ^ L * 5 ^ j := by
      nlinarith [hB1, hpos5]
    nlinarith [hrep', hleLHS', hleRHS]
  let m := q - δ * 2 ^ L
  refine ⟨m, ?_, ?_⟩
  · omega
  · have hq : q = m + δ * 2 ^ L := by omega
    have hcancel : A_j + 5 ^ j * m = 2 ^ L * B := by
      nlinarith [hrep', hq]
    have hle1 : 5 ^ j * m ≤ 2 ^ L * B := by nlinarith [hcancel]
    have hlt2 : 2 ^ L * B < 2 ^ L * 5 ^ j :=
      Nat.mul_lt_mul_of_pos_left hBlt (by positivity : 0 < 2 ^ L)
    have hlt : 5 ^ j * m < 2 ^ L * 5 ^ j := lt_of_le_of_lt hle1 hlt2
    have hlt' : m * 5 ^ j < 2 ^ L * 5 ^ j := by
      simpa [Nat.mul_comm] using hlt
    exact Nat.lt_of_mul_lt_mul_right hlt'

/-- 36.30.8.2: the block-head representation plus the reset equation give
the exact identity `A_j + 5^j*q = 2^Wp*(5^(k+1)*s0 - 4 + δ*5^j)`. -/
theorem block_head_identity_of_reset
    (j Wp Wj q Aj rj s0 k t δ : Nat)
    (hj : 1 ≤ j)
    (hs0 : 0 < s0)
    (hW : Wj = Wp + t)
    (hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hres : ResetHeadEq s0 j k t δ rj) :
    Aj + 5 ^ j * q = 2 ^ Wp * (5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j) := by
  have hmul : 2 ^ Wj * rj = Aj + 5 ^ j * q := by
    rw [hrj]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have h5j : 5 ≤ 5 ^ j := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 1 ≤ j))
  have hres2 : 2 ^ t * rj = 5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j := by
    have h5k5 : 5 ≤ 5 ^ (k + 1) := by
      have hle : 1 ≤ k + 1 := by omega
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hle)
    rcases hres with h1 | h2
    · rcases h1 with ⟨ht, hδ, heq⟩
      subst t
      subst δ
      have hpos : 0 ≤ 5 ^ (k + 1) * s0 := by positivity
      have ha : 4 ≤ 5 ^ (k + 1) * s0 := by
        have hmul := Nat.mul_le_mul h5k5 hs0
        norm_num at hmul
        omega
      have hge : 4 ≤ 5 ^ (k + 1) * s0 + 5 ^ j := by nlinarith [h5j, hpos]
      have heq' : 2 * rj + 4 = 5 ^ (k + 1) * s0 + 5 ^ j := by omega
      have hcore : 2 * rj = 5 ^ (k + 1) * s0 + 5 ^ j - 4 := by omega
      omega
    · rcases h2 with ⟨ht, hδ, heq⟩
      subst t
      have hpos : 0 ≤ 5 ^ (k + 1) * s0 := by positivity
      have ha : 4 ≤ 5 ^ (k + 1) * s0 := by
        have hmul := Nat.mul_le_mul h5k5 hs0
        norm_num at hmul
        omega
      have hge : 4 ≤ 5 ^ (k + 1) * s0 + δ * 5 ^ j := by
        rcases hδ with rfl | rfl <;> nlinarith [h5j, hpos]
      have heq' : 4 * rj + 4 = 5 ^ (k + 1) * s0 + δ * 5 ^ j := by omega
      have hcore : 4 * rj = 5 ^ (k + 1) * s0 + δ * 5 ^ j - 4 := by omega
      omega
  have hpow : 2 ^ Wj = 2 ^ Wp * 2 ^ t := by
    rw [hW, Nat.pow_add]
  have hcomb : 2 ^ Wp * (2 ^ t * rj) = Aj + 5 ^ j * q := by
    rw [hpow] at hmul
    simpa [Nat.mul_assoc] using hmul
  have htarget : 2 ^ Wp * (2 ^ t * rj) = 2 ^ Wp * (5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j) := by
    rw [hres2]
  exact hcomb.symm.trans htarget

/-- Converse of `block_head_identity_of_reset`: the exact 36.30.8.2
identity `A_j + 5^j*q = 2^Wp*(5^(k+1)*s0 - 4 + δ*5^j)` is equivalent to
the reset equation for a block head with reset weight `t`. -/
theorem reset_head_eq_of_block_head_identity
    (j Wp Wj q Aj rj s0 k t δ : Nat)
    (hs0 : 0 < s0)
    (hW : Wj = Wp + t)
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3))
    (hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hident : Aj + 5 ^ j * q = 2 ^ Wp * (5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j)) :
    ResetHeadEq s0 j k t δ rj := by
  have hmul : 2 ^ Wj * rj = Aj + 5 ^ j * q := by
    rw [hrj]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hpow : 2 ^ Wj = 2 ^ Wp * 2 ^ t := by
    rw [hW, Nat.pow_add]
  have hmain : 2 ^ Wp * (2 ^ t * rj) = 2 ^ Wp * (5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j) := by
    calc
      2 ^ Wp * (2 ^ t * rj) = 2 ^ Wj * rj := by
        rw [hpow]
        ring
      _ = Aj + 5 ^ j * q := hmul
      _ = 2 ^ Wp * (5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j) := hident
  have hcore : 2 ^ t * rj = 5 ^ (k + 1) * s0 - 4 + δ * 5 ^ j := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ Wp) hmain
  rcases ht with ht1 | ht2
  · subst t
    have hδ1 : δ = 1 := hδ.1 rfl
    subst δ
    left
    refine ⟨rfl, rfl, ?_⟩
    have hXge : 4 ≤ 5 ^ (k + 1) * s0 := by
      have h5 : 5 ≤ 5 ^ (k + 1) := by
        have hk : 1 ≤ k + 1 := by omega
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hk)
      nlinarith
    have hcore' : 2 * rj = 5 ^ (k + 1) * s0 + 5 ^ j - 4 := by
      norm_num at hcore ⊢
      rw [← Nat.sub_add_comm hXge] at hcore
      omega
    have hge : 4 ≤ 5 ^ (k + 1) * s0 + 5 ^ j := by
      omega
    omega
  · subst t
    right
    refine ⟨rfl, hδ.2 rfl, ?_⟩
    have hXge : 4 ≤ 5 ^ (k + 1) * s0 := by
      have h5 : 5 ≤ 5 ^ (k + 1) := by
        have hk : 1 ≤ k + 1 := by omega
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hk)
      nlinarith
    have hcore' : 4 * rj = 5 ^ (k + 1) * s0 + δ * 5 ^ j - 4 := by
      norm_num at hcore ⊢
      rw [← Nat.sub_add_comm hXge] at hcore
      omega
    have hge : 4 ≤ 5 ^ (k + 1) * s0 + δ * 5 ^ j := by
      omega
    omega

/-- The exact full-orbit step rewrites as `2^t * fullOrbitStep x = 5*x+1`. -/
lemma fullOrbitStep_mul_eq (x : Nat) :
    2 ^ twoValuation (5 * x + 1) * fullOrbitStep x = 5 * x + 1 := by
  unfold fullOrbitStep
  have hpos : 0 < 5 * x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos
  have hdvd : 2 ^ twoValuation (5 * x + 1) ∣ 5 * x + 1 := by
    exact ⟨StringFlow.oddPart (5 * x + 1), hdec⟩
  exact Nat.mul_div_cancel' hdvd

/-- The terminal-chain identity instantiated from the exact full-orbit
segment: `g` at depth `n0-(1+d)`, `g_prev` one step before it, and `e`
the weight of the step into `g`. -/
theorem terminal_chain_identity_of_full_orbit_d
    (n0 d k0 s r g e g_prev : Nat)
    (_hd : 1 ≤ d)
    (hn0 : 2 + d ≤ n0)
    (hprod : s * 5 ^ k0 = r + 1)
    (hiter_g : fullOrbitIter (n0 - (1 + d)) = g)
    (hiter_gp : fullOrbitIter (n0 - (2 + d)) = g_prev)
    (hstep_e : orbitStepWeight (n0 - (2 + d)) = e)
    (he : 1 ≤ e)
    (hr : r = (5 * g_prev + 1) / 2) :
    5 ^ k0 * s = 2 ^ (e - 1) * g + 1 := by
  have hstep : 5 * g_prev + 1 = 2 ^ e * g := by
    let m := n0 - (2 + d)
    have hm : m + 1 = n0 - (1 + d) := by dsimp [m]; omega
    have hstep0 := fullOrbitStep_mul_eq (fullOrbitIter m)
    have hval : twoValuation (5 * fullOrbitIter m + 1) = e := by
      dsimp [m] at hstep_e ⊢
      unfold orbitStepWeight at hstep_e
      exact hstep_e
    have hstep' : 2 ^ e * fullOrbitStep (fullOrbitIter m) = 5 * fullOrbitIter m + 1 := by
      rw [hval] at hstep0
      exact hstep0
    have hsucc : fullOrbitStep (fullOrbitIter m) = fullOrbitIter (m + 1) := by rfl
    rw [hsucc, hm] at hstep'
    dsimp [m] at hstep'
    rw [hiter_g, hiter_gp] at hstep'
    exact hstep'.symm
  exact terminal_chain_identity k0 s r g e g_prev hprod hstep hr he

/-- 36.30.23.0: every full-orbit step output is prime to `5`. -/
lemma fullOrbitStep_not_dvd_five (x : Nat) : ¬ 5 ∣ fullOrbitStep x := by
  intro h5
  have hmul := fullOrbitStep_mul_eq x
  have h5prod : 5 ∣ 2 ^ twoValuation (5 * x + 1) * fullOrbitStep x := by
    exact dvd_mul_of_dvd_right h5 _
  rw [hmul] at h5prod
  have hmod : (5 * x + 1) % 5 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
    simp
  have hzero : (5 * x + 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5prod
  omega

/-- 36.30.23.0: all states of the full accelerated 7-orbit are prime to `5`. -/
theorem fullOrbitIter_not_dvd_five (n : Nat) : ¬ 5 ∣ fullOrbitIter n := by
  induction n with
  | zero => norm_num [fullOrbitIter]
  | succ n ih => exact fullOrbitStep_not_dvd_five (fullOrbitIter n)

/-- 36.30.23.1: the reset block head is `3 mod 5` for `t=1` and
`4 mod 5` for `t=2`. -/
theorem candidateRj_mod_five (x t : Nat) (ht : t = 1 ∨ t = 2)
    (hdiv : 2 ^ t ∣ 5 * x + 1) :
    (t = 1 → candidateRj x t % 5 = 3) ∧
    (t = 2 → candidateRj x t % 5 = 4) := by
  constructor
  · intro ht1
    subst t
    have hmul : 2 * candidateRj x 1 = 5 * x + 1 := by
      unfold candidateRj
      simpa using (Nat.mul_div_cancel' hdiv : 2 ^ 1 * ((5 * x + 1) / 2 ^ 1) = 5 * x + 1)
    have hmod5 : (5 * x + 1) % 5 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
      simp
    have hmod : (2 * candidateRj x 1) % 5 = 1 := by
      rw [hmul]
      exact hmod5
    have hmod' : (2 * (candidateRj x 1 % 5)) % 5 = 1 := by
      simpa [Nat.mul_mod] using hmod
    have hcases : candidateRj x 1 % 5 = 0 ∨ candidateRj x 1 % 5 = 1 ∨
        candidateRj x 1 % 5 = 2 ∨ candidateRj x 1 % 5 = 3 ∨
        candidateRj x 1 % 5 = 4 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · rw [h0] at hmod'
      norm_num at hmod'
    · rw [h1] at hmod'
      norm_num at hmod'
    · rw [h2] at hmod'
      norm_num at hmod'
    · rw [h3] at hmod'
      norm_num at hmod'
      exact h3
    · rw [h4] at hmod'
      norm_num at hmod'
  · intro ht2
    subst t
    have hmul : 4 * candidateRj x 2 = 5 * x + 1 := by
      unfold candidateRj
      simpa using (Nat.mul_div_cancel' hdiv : 2 ^ 2 * ((5 * x + 1) / 2 ^ 2) = 5 * x + 1)
    have hmod5 : (5 * x + 1) % 5 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
      simp
    have hmod : (4 * candidateRj x 2) % 5 = 1 := by
      rw [hmul]
      exact hmod5
    have hmod' : (4 * (candidateRj x 2 % 5)) % 5 = 1 := by
      simpa [Nat.mul_mod] using hmod
    have hcases : candidateRj x 2 % 5 = 0 ∨ candidateRj x 2 % 5 = 1 ∨
        candidateRj x 2 % 5 = 2 ∨ candidateRj x 2 % 5 = 3 ∨
        candidateRj x 2 % 5 = 4 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · rw [h0] at hmod'
      norm_num at hmod'
    · rw [h1] at hmod'
      norm_num at hmod'
    · rw [h2] at hmod'
      norm_num at hmod'
    · rw [h3] at hmod'
      norm_num at hmod'
    · rw [h4] at hmod'
      norm_num at hmod'
      exact h4

/-- Converse of `candidateRj_mod_five`: a state with the correct mod-5
class is the `t`-reset successor of an integer `x`. -/
lemma candidateRj_of_mod_five (r t : Nat)
    (ht : t = 1 ∨ t = 2)
    (hmod : (t = 1 → r % 5 = 3) ∧ (t = 2 → r % 5 = 4)) :
    ∃ x : Nat, r = candidateRj x t ∧ (5 * x + 1) % 2 ^ t = 0 := by
  rcases ht with ht1 | ht2
  · subst t
    have hr5 : r % 5 = 3 := hmod.1 rfl
    let q := r / 5
    have hrq : r = 5 * q + 3 := by
      have hdivmod := (Nat.div_add_mod r 5).symm
      simpa [q, hr5] using hdivmod
    have hbase : 2 * r = 10 * q + 6 := by
      rw [hrq]
      ring
    have hdvd : 5 ∣ 2 * r - 1 := by
      refine ⟨2 * q + 1, ?_⟩
      have hge : 1 ≤ 2 * r := by
        rw [hbase]
        omega
      rw [hbase]
      have hsub : 10 * q + 6 - 1 = 10 * q + 5 := by omega
      rw [hsub]
      ring
    let x := (2 * r - 1) / 5
    have hmul : 2 * r = 5 * x + 1 := by
      have hx : x = (2 * r - 1) / 5 := rfl
      have h' : 2 * r - 1 = 5 * x := by
        rw [hx]
        exact (Nat.mul_div_cancel' hdvd).symm
      have hge : 1 ≤ 2 * r := by
        rw [hbase]
        omega
      omega
    have hdiv2 : (5 * x + 1) % 2 = 0 := by
      rw [← hmul]
      rw [Nat.mul_mod, Nat.mod_self]
      simp
    refine ⟨x, ?_, hdiv2⟩
    unfold candidateRj
    have hdiv2' : 2 ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr hdiv2
    have hmul2 : 2 * ((5 * x + 1) / 2) = 5 * x + 1 :=
      Nat.mul_div_cancel' hdiv2'
    have hleft : 2 * r = 2 * ((5 * x + 1) / 2) := by rw [hmul, hmul2]
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hleft
  · subst t
    have hr5 : r % 5 = 4 := hmod.2 rfl
    let q := r / 5
    have hrq : r = 5 * q + 4 := by
      have hdivmod := (Nat.div_add_mod r 5).symm
      simpa [q, hr5] using hdivmod
    have hbase : 4 * r = 20 * q + 16 := by
      rw [hrq]
      ring
    have hdvd : 5 ∣ 4 * r - 1 := by
      refine ⟨4 * q + 3, ?_⟩
      have hge : 1 ≤ 4 * r := by
        rw [hbase]
        omega
      rw [hbase]
      have hsub : 20 * q + 16 - 1 = 20 * q + 15 := by omega
      rw [hsub]
      ring
    let x := (4 * r - 1) / 5
    have hmul : 4 * r = 5 * x + 1 := by
      have hx : x = (4 * r - 1) / 5 := rfl
      have h' : 4 * r - 1 = 5 * x := by
        rw [hx]
        exact (Nat.mul_div_cancel' hdvd).symm
      have hge : 1 ≤ 4 * r := by
        rw [hbase]
        omega
      omega
    have hdiv2 : (5 * x + 1) % 4 = 0 := by
      rw [← hmul]
      rw [Nat.mul_mod, Nat.mod_self]
      simp
    refine ⟨x, ?_, hdiv2⟩
    unfold candidateRj
    have hdiv4 : 4 ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr hdiv2
    have hmul4 : 4 * ((5 * x + 1) / 4) = 5 * x + 1 :=
      Nat.mul_div_cancel' hdiv4
    have hleft : 4 * r = 4 * ((5 * x + 1) / 4) := by rw [hmul, hmul4]
    have heq : r = (5 * x + 1) / 4 :=
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) hleft
    simpa using heq

/-- The no-`H_ge` block-head rigidity plus `FullOrbitFrom7 r` supplies the
reset weight `t∈{1,2}` and an integer predecessor `x` with
`r = candidateRj x t`. -/
theorem reset_predecessor_of_block_head_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r) :
    ∃ t x : Nat, (t = 1 ∨ t = 2) ∧ r = candidateRj x t ∧
      (5 * x + 1) % 2 ^ t = 0 := by
  have hcong := UnifiedCoreAudit.block_head_mod_five_congruence_of_premises
    j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  rcases hPrem.tj_mem with htj1 | htj2
  · have ht : Wj - Wp = 1 := by omega
    have hinv : StringFlow.Lte.invMod5 2 % 5 = 3 := by
      norm_num [StringFlow.Lte.invMod5]
    have hc : r ≡ 3 [MOD 5] := by
      rw [ht] at hcong
      simpa [hinv] using hcong
    rw [Nat.ModEq] at hc
    norm_num at hc
    rcases candidateRj_of_mod_five r 1 (Or.inl rfl)
      ⟨fun _ => hc, fun h => by norm_num at h⟩ with ⟨x, hx, hdiv⟩
    exact ⟨1, x, Or.inl rfl, hx, hdiv⟩
  · have ht : Wj - Wp = 2 := by omega
    have hinv : StringFlow.Lte.invMod5 4 % 5 = 4 := by
      norm_num [StringFlow.Lte.invMod5]
    have hc : r ≡ 4 [MOD 5] := by
      rw [ht] at hcong
      simpa [hinv] using hcong
    rw [Nat.ModEq] at hc
    norm_num at hc
    rcases candidateRj_of_mod_five r 2 (Or.inr rfl)
      ⟨fun h => by norm_num at h, fun _ => hc⟩ with ⟨x, hx, hdiv⟩
    exact ⟨2, x, Or.inr rfl, hx, hdiv⟩

/-- The reset predecessor of a block head is bounded by `2^t*5^(j-1)`. -/
theorem reset_predecessor_bound_of_block_head_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r) :
    ∃ t x : Nat, (t = 1 ∨ t = 2) ∧ r = candidateRj x t ∧
      x < 2 ^ t * 5 ^ (j - 1) := by
  rcases reset_predecessor_of_block_head_premises j Wp Wj q Aj A_s s W_s r_s L H_s
    weight r hPrem hrj hReach with ⟨t, x, ht, hr, hdiv⟩
  refine ⟨t, x, ht, hr, ?_⟩
  have hrlt : r < 5 ^ j := by simpa [hrj] using hPrem.r_j_lt
  have hmul : 2 ^ t * r = 5 * x + 1 := by
    unfold candidateRj at hr
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hlt : 5 * x + 1 < 2 ^ t * 5 ^ j := by
    rw [← hmul]
    exact Nat.mul_lt_mul_of_pos_left hrlt (by positivity : 0 < 2 ^ t)
  have hle : 5 * x < 2 ^ t * 5 ^ j := by omega
  have hj1 : 1 ≤ j := hPrem.j_pos
  have hsum' : (j - 1) + 1 = j := by omega
  have hpow : 2 ^ t * 5 ^ j = 5 * (2 ^ t * 5 ^ (j - 1)) := by
    conv_lhs =>
      rw [← hsum']
      rw [Nat.pow_add, Nat.pow_one]
    ring
  rw [hpow] at hle
  exact Nat.lt_of_mul_lt_mul_left hle

/-- If an odd state `r` is the `t`-reset successor of `x`, then `x` is a
full-orbit preimage of `r`: `fullOrbitStep x = r`. -/
lemma fullOrbitStep_eq_of_candidateRj (r x t : Nat)
    (hr : r = candidateRj x t)
    (hodd : r % 2 = 1)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    fullOrbitStep x = r := by
  have hmul : 2 ^ t * r = 5 * x + 1 := by
    unfold candidateRj at hr
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hv : twoValuation (5 * x + 1) = t := by
    rw [← hmul]
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq t r (by simpa [IsOdd] using hodd)
  unfold fullOrbitStep
  rw [hv]
  rw [hr]
  rfl

/-- The reset predecessor of an odd `t∈{1,2}` successor is odd. -/
lemma candidateRj_predecessor_odd (r x t : Nat)
    (ht : t = 1 ∨ t = 2)
    (hr : r = candidateRj x t)
    (_hodd : r % 2 = 1)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x % 2 = 1 := by
  have hmul : 2 ^ t * r = 5 * x + 1 := by
    unfold candidateRj at hr
    rw [hr]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have h2t_even : (2 ^ t) % 2 = 0 := by
    rcases ht with rfl | rfl <;> norm_num
  have heven : (5 * x + 1) % 2 = 0 := by
    rw [← hmul]
    rw [Nat.mul_mod, h2t_even]
    simp
  have h5xodd : (5 * x) % 2 = 1 := by
    have hsplit : (5 * x + 1) % 2 = ((5 * x) % 2 + 1 % 2) % 2 := by
      rw [Nat.add_mod]
    rw [heven] at hsplit
    norm_num at hsplit
    have hlt : (5 * x) % 2 < 2 := Nat.mod_lt (5 * x) (by decide)
    omega
  have hxmod : (5 * x) % 2 = x % 2 := by
    rw [Nat.mul_mod]
    norm_num
  rw [hxmod] at h5xodd
  exact h5xodd

/-- If the full-orbit step into `r` at depth `n0` has weight `t`, then the
`t`-reset predecessor `x` of `r` is exactly the preceding full-orbit state.
This is the exact-predecessor half of the premises-to-candidate bridge:
no injectivity of `fullOrbitStep` is needed, only equality of quotients by
the same power of two. -/
lemma candidateRj_eq_fullOrbitIter_of_weight
    (n0 x t r : Nat)
    (hn0 : 1 ≤ n0)
    (hiter : fullOrbitIter n0 = r)
    (hstep : orbitStepWeight (n0 - 1) = t)
    (hr : r = candidateRj x t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x = fullOrbitIter (n0 - 1) := by
  let x0 := fullOrbitIter (n0 - 1)
  have htv : twoValuation (5 * x0 + 1) = t := by
    unfold orbitStepWeight at hstep
    change twoValuation (5 * x0 + 1) = t at hstep
    exact hstep
  have hx0_step : (5 * x0 + 1) / 2 ^ t = r := by
    have hsucc : n0 = (n0 - 1) + 1 := by omega
    rw [hsucc, fullOrbitIter] at hiter
    unfold fullOrbitStep at hiter
    rw [htv] at hiter
    exact hiter
  have hdiv0 : 2 ^ t ∣ 5 * x0 + 1 := by
    have hpos : 0 < 5 * x0 + 1 := by positivity
    have hge : t ≤ twoValuation (5 * x0 + 1) := by omega
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * x0 + 1) t hpos).mp hge
  have hnum0 : 2 ^ t * ((5 * x0 + 1) / 2 ^ t) = 5 * x0 + 1 := Nat.mul_div_cancel' hdiv0
  have hnumx : 2 ^ t * ((5 * x + 1) / 2 ^ t) = 5 * x + 1 :=
    Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hq : (5 * x0 + 1) / 2 ^ t = (5 * x + 1) / 2 ^ t := by
    rw [hx0_step]
    unfold candidateRj at hr
    exact hr
  have hnum : 5 * x0 + 1 = 5 * x + 1 := by
    rw [← hnum0, ← hnumx]
    congr 1
  have hx0x : x0 = x := by
    have h5 : 5 * x0 = 5 * x := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h5
  dsimp [x0] at hx0x
  exact hx0x.symm

/-- Packaged candidate parameterization: if the full-orbit step into the
block head `r` has weight `t`, and the reset terminal satisfies
`s0 = 2^(e-1)*g + 1` with `g` two full-orbit steps before `r`, then the
reset predecessor `x` is simultaneously the full-orbit predecessor and
the candidate `candidateX (n0-1) e g δ`. -/
theorem candidate_parameterization_of_reset_full_orbit
    (n0 k t δ e g s0 x r : Nat)
    (hn0 : 3 ≤ n0)
    (hiter : fullOrbitIter n0 = r)
    (hiter_g : fullOrbitIter (n0 - 2) = g)
    (hstep_e : orbitStepWeight (n0 - 3) = e)
    (hstep_t : orbitStepWeight (n0 - 1) = t)
    (hres : ResetHeadEq s0 (n0 - 1) k t δ r)
    (hterm : 5 ^ k * s0 = 2 ^ (e - 1) * g + 1)
    (hr : r = candidateRj x t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x = candidateX (n0 - 1) e g δ ∧ x = fullOrbitIter (n0 - 1) ∧
      g = fullOrbitIter (n0 - 2) ∧ e = orbitStepWeight (n0 - 3) := by
  have hx_iter := candidateRj_eq_fullOrbitIter_of_weight n0 x t r (by omega) hiter hstep_t hr hdiv
  have hx_cand := candidateX_of_reset_and_terminal_general s0 (n0 - 1) k t δ r x e g
    (by omega) hres hr hdiv hterm
  exact ⟨hx_cand, hx_iter, hiter_g.symm, hstep_e.symm⟩

/-- Same bridge for a general segment length `d`: `g` is `d` full-orbit
steps before `x`, `e` is the weight of the step into `g`, and the reset
head depth is `n0-d`.  This is the input shape used by the `d=2`, `d=3`
and `d≥4` exclusions. -/
theorem candidate_parameterization_of_reset_full_orbit_d
    (n0 d k t δ e g s0 x r : Nat)
    (_hd : 1 ≤ d)
    (hn0 : d + 3 ≤ n0)
    (hiter : fullOrbitIter n0 = r)
    (hiter_g : fullOrbitIter (n0 - (1 + d)) = g)
    (hstep_e : orbitStepWeight (n0 - (2 + d)) = e)
    (hstep_t : orbitStepWeight (n0 - 1) = t)
    (hres : ResetHeadEq s0 (n0 - d) k t δ r)
    (hterm : 5 ^ k * s0 = 2 ^ (e - 1) * g + 1)
    (hr : r = candidateRj x t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x = candidateX (n0 - d) e g δ ∧ x = fullOrbitIter (n0 - 1) ∧
      g = fullOrbitIter (n0 - (1 + d)) ∧ e = orbitStepWeight (n0 - (2 + d)) := by
  have hx_iter := candidateRj_eq_fullOrbitIter_of_weight n0 x t r (by omega) hiter hstep_t hr hdiv
  have hx_cand := candidateX_of_reset_and_terminal_general s0 (n0 - d) k t δ r x e g
    (by omega) hres hr hdiv hterm
  exact ⟨hx_cand, hx_iter, hiter_g.symm, hstep_e.symm⟩

/-- 36.30.23.4 branch table, `e=2`: `candidateX ≡ 2+δ (mod 4)`
when the full-orbit state `g` is odd. -/
lemma two_mul_odd_mod4 (g : Nat) (hgodd : g % 2 = 1) : (2 * g) % 4 = 2 := by
  have hg : g = 2 * (g / 2) + 1 := by
    have h := (Nat.div_add_mod g 2).symm
    rw [hgodd] at h
    exact h
  rw [hg]
  ring_nf
  rw [Nat.add_mod, Nat.mul_mod]
  norm_num

lemma candidateX_mod4_of_e2 (j g δ : Nat) (hgodd : g % 2 = 1)
    (hδ : δ = 1 ∨ δ = 3) :
    candidateX j 2 g δ % 4 = (2 + δ) % 4 := by
  rcases hδ with rfl | rfl
  · have h5 : 5 ^ (j - 1) % 4 = 1 := five_pow_mod_four (j - 1)
    have hx : candidateX j 2 g 1 = 2 * g + 5 ^ (j - 1) := by
      simp [candidateX]
    rw [hx]
    have h2 : (2 * g) % 4 = 2 := two_mul_odd_mod4 g hgodd
    rw [Nat.add_mod, h2, h5]
  · have h5 : 5 ^ (j - 1) % 4 = 1 := five_pow_mod_four (j - 1)
    have hx : candidateX j 2 g 3 = 2 * g + 3 * 5 ^ (j - 1) := by
      simp [candidateX]
    rw [hx]
    have h2 : (2 * g) % 4 = 2 := two_mul_odd_mod4 g hgodd
    have h3 : (3 * 5 ^ (j - 1)) % 4 = 3 := by
      rw [Nat.mul_mod, h5]
    rw [Nat.add_mod, h2, h3]

/-- 36.30.23.4 branch table, `e≥3`: `candidateX ≡ δ (mod 4)`. -/
lemma candidateX_mod4_of_e_ge3 (j e g δ : Nat) (he : 3 ≤ e) :
    candidateX j e g δ % 4 = δ % 4 := by
  have hdvd : 4 ∣ 2 ^ (e - 1) := by
    have hle : 2 ≤ e - 1 := by omega
    have hpow := pow_dvd_pow 2 hle
    simpa using hpow
  have hmod : 2 ^ (e - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have h5 : 5 ^ (j - 1) % 4 = 1 := five_pow_mod_four (j - 1)
  have hx : candidateX j e g δ = 2 ^ (e - 1) * g + δ * 5 ^ (j - 1) := rfl
  rw [hx]
  have h2 : (2 ^ (e - 1) * g) % 4 = 0 := by
    rw [Nat.mul_mod, hmod]
    norm_num
  have h5' : (δ * 5 ^ (j - 1)) % 4 = δ % 4 := by
    rw [Nat.mul_mod, h5]
    rw [Nat.mul_one]
    have hlt : δ % 4 < 4 := Nat.mod_lt δ (by norm_num)
    exact Nat.mod_eq_of_lt hlt
  rw [Nat.add_mod, h2, h5']
  rw [Nat.zero_add]
  have hlt : δ % 4 < 4 := Nat.mod_lt δ (by norm_num)
  exact Nat.mod_eq_of_lt hlt

/-- 36.30.23.5, `d=1`: with `y=g`, the candidate parameterization is
impossible.  This is the first segment-length exclusion. -/
theorem d1_exclusion
    (j e g δ a : Nat)
    (hj : 3 ≤ j)
    (hgpos : 0 < g)
    (hg : g < 5 ^ (j - 1) / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hy : 5 * g + 1 = 2 ^ (1 + 4 * a) * candidateX j e g δ) :
    False := by
  have hx : candidateX j e g δ = 2 ^ (e - 1) * g + δ * 5 ^ (j - 1) := rfl
  have hpow : 2 ^ (1 + 4 * a) * 2 ^ (e - 1) = 2 ^ (e + 4 * a) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hmain : 5 * g + 1 = 2 ^ (e + 4 * a) * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
    rw [hy, hx]
    rw [Nat.mul_add]
    have hleft : 2 ^ (1 + 4 * a) * (2 ^ (e - 1) * g) = 2 ^ (e + 4 * a) * g := by
      rw [← Nat.mul_assoc, hpow]
    have hright : 2 ^ (1 + 4 * a) * (δ * 5 ^ (j - 1)) =
        δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
      ring
    rw [hleft, hright]
  have hδge : 1 ≤ δ := by
    rcases hδ with rfl | rfl <;> norm_num
  have hpos5 : 0 < 5 ^ (j - 1) := by positivity
  have hpos2 : 0 < 2 ^ (1 + 4 * a) := by positivity
  have htermpos : 0 < δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
    positivity
  by_cases he3 : 3 ≤ e
  · have hcoef : 8 ≤ 2 ^ (e + 4 * a) := by
      have hle : 3 ≤ e + 4 * a := by omega
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have hRHS : 8 * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) ≤
        2 ^ (e + 4 * a) * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
      nlinarith [hcoef, hgpos]
    have hLHS : 5 * g + 1 < 8 * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
      have hlt : 5 * g + 1 < 8 * g := by nlinarith [hgpos]
      nlinarith [hlt, htermpos]
    nlinarith [hmain, hRHS, hLHS]
  · have he2 : e = 2 := by omega
    subst e
    by_cases ha0 : a = 0
    · subst a
      norm_num at hmain
      have hg_eq : g + 1 = δ * 2 * 5 ^ (j - 1) := by
        nlinarith [hmain]
      have hgge : 2 * 5 ^ (j - 1) - 1 ≤ g := by
        have hδ2 : 2 ≤ δ * 2 := by nlinarith [hδge]
        have hd : 2 * 5 ^ (j - 1) ≤ δ * 2 * 5 ^ (j - 1) := by
          nlinarith [hδ2, hpos5]
        have hg1 : 2 * 5 ^ (j - 1) ≤ g + 1 := by nlinarith [hg_eq, hd]
        omega
      have h5 : 25 ≤ 5 ^ (j - 1) := by
        have hle : 2 ≤ j - 1 := by omega
        simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hle)
      have hsmall : 5 ^ (j - 1) / 4 < 2 * 5 ^ (j - 1) - 1 := by
        have hdiv : 5 ^ (j - 1) / 4 < 5 ^ (j - 1) := by
          exact Nat.div_lt_self (by positivity) (by decide : 1 < 4)
        nlinarith [hdiv, h5]
      have hnot : g < 5 ^ (j - 1) / 4 := hg
      nlinarith [hgge, hsmall, hnot]
    · have hcoef : 64 ≤ 2 ^ (2 + 4 * a) := by
        have hle : 6 ≤ 2 + 4 * a := by omega
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hle
        norm_num at hpow ⊢
        exact hpow
      have hRHS : 64 * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) ≤
          2 ^ (2 + 4 * a) * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
        nlinarith [hcoef, hgpos]
      have hLHS : 5 * g + 1 < 64 * g + δ * 2 ^ (1 + 4 * a) * 5 ^ (j - 1) := by
        have hlt : 5 * g + 1 < 64 * g := by nlinarith [hgpos]
        nlinarith [hlt, htermpos]
      nlinarith [hmain, hRHS, hLHS]

/-- 36.30.23.5, `d=2`: all branches except the surviving
`(未=1, e=2, u1=1)` family are excluded by the size bound
`g < 5^(j-1)/2^(e-1)`. -/
theorem d2_size_exclusion
    (j e g δ u1 : Nat)
    (hj : 3 ≤ j)
    (_hgpos : 0 < g)
    (hg : g < 5 ^ (j - 1) / 2 ^ (e - 1))
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hu1 : u1 = 1 ∨ u1 = 2)
    (hseg : 2 ^ (u1 + e) * g + 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) =
      5 + 2 ^ u1 + 25 * g)
    (hnot : ¬ (δ = 1 ∧ e = 2 ∧ u1 = 1)) :
    False := by
  have hδge : 1 ≤ δ := by
    rcases hδ with rfl | rfl <;> norm_num
  have h5 : 25 ≤ 5 ^ (j - 1) := by
    have hle : 2 ≤ j - 1 := by omega
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hle)
  have hsmall : 2 ^ (u1 + e) < 25 := by
    by_contra hnotsmall
    have hge : 25 ≤ 2 ^ (u1 + e) := by omega
    have hgeg : 25 * g ≤ 2 ^ (u1 + e) * g := Nat.mul_le_mul_right g hge
    have hu1le : 2 ^ u1 ≤ 4 := by
      rcases hu1 with rfl | rfl <;> norm_num
    have hcoef : 4 ≤ 2 ^ (u1 + 1) := by
      rcases hu1 with rfl | rfl <;> norm_num
    have hT : 5 + 2 ^ u1 < 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) := by
      have hA : 4 * 25 ≤ 2 ^ (u1 + 1) * 5 ^ (j - 1) := Nat.mul_le_mul hcoef h5
      have hleδ : 2 ^ (u1 + 1) * 5 ^ (j - 1) ≤ 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) := by
        have h := Nat.mul_le_mul_right (2 ^ (u1 + 1) * 5 ^ (j - 1)) hδge
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
      have hAδ : 100 ≤ 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) := by
        nlinarith [hA, hleδ]
      have hsmall5 : 5 + 2 ^ u1 ≤ 9 := by nlinarith [hu1le]
      have h9 : 9 < 100 := by norm_num
      nlinarith
    nlinarith [hseg, hgeg, hT]
  have hsum : u1 + e ≤ 4 := by
    by_contra hnotsum
    have hge5 : 5 ≤ u1 + e := by omega
    have h32 : 32 ≤ 2 ^ (u1 + e) := by
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hge5
      norm_num at hpow ⊢
      exact hpow
    omega
  rcases hu1 with rfl | rfl
  · have he_le3 : e ≤ 3 := by omega
    interval_cases e
    · -- u1=1, e=2
      norm_num at hseg
      have hg2 : 2 * g < 5 ^ (j - 1) := by
        have hlt := Nat.mul_lt_mul_of_pos_left hg (by norm_num : 0 < 2)
        have hle : 2 * (5 ^ (j - 1) / 2) ≤ 5 ^ (j - 1) := by
          simpa [Nat.mul_comm] using (Nat.mul_div_le (5 ^ (j - 1)) 2)
        exact lt_of_lt_of_le hlt hle
      rcases hδ with rfl | rfl
      · norm_num at hnot
      · norm_num at hseg
        nlinarith [hseg, hg2, h5]
    · -- u1=1, e=3
      norm_num at hseg
      have hg4 : 4 * g < 5 ^ (j - 1) := by
        have hlt := Nat.mul_lt_mul_of_pos_left hg (by norm_num : 0 < 4)
        have hle : 4 * (5 ^ (j - 1) / 4) ≤ 5 ^ (j - 1) := by
          simpa [Nat.mul_comm] using (Nat.mul_div_le (5 ^ (j - 1)) 4)
        exact lt_of_lt_of_le hlt hle
      rcases hδ with rfl | rfl <;> norm_num at hseg <;> nlinarith [hseg, hg4, h5]
  · have he_le2 : e ≤ 2 := by omega
    have he2 : e = 2 := by omega
    subst e
    norm_num at hseg
    have hg2 : 2 * g < 5 ^ (j - 1) := by
      have hlt := Nat.mul_lt_mul_of_pos_left hg (by norm_num : 0 < 2)
      have hle : 2 * (5 ^ (j - 1) / 2) ≤ 5 ^ (j - 1) := by
        simpa [Nat.mul_comm] using (Nat.mul_div_le (5 ^ (j - 1)) 2)
      exact lt_of_lt_of_le hlt hle
    rcases hδ with rfl | rfl <;> norm_num at hseg <;> nlinarith [hseg, hg2, h5]

/-- `5^16 ≡ 1 (mod 17)`: the period-16 lemma for powers of five. -/
lemma five_pow_mod17_period (m : Nat) :
    5 ^ (m + 16) % 17 = 5 ^ m % 17 := by
  rw [Nat.pow_add]
  have h : 5 ^ 16 % 17 = 1 := by norm_num
  rw [Nat.mul_mod, h]
  simp

/-- Reduce `5^(q*16+r)` modulo 17 to `5^r`. -/
lemma five_pow_mod17_reduce (q r : Nat) :
    5 ^ (q * 16 + r) % 17 = 5 ^ r % 17 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hrewrite : (q + 1) * 16 + r = (q * 16 + r) + 16 := by omega
      rw [hrewrite, five_pow_mod17_period]
      exact ih

/-- `5^8 ≡ 1 (mod 32)`: the period-8 lemma for powers of five. -/
lemma five_pow_mod32_period (m : Nat) :
    5 ^ (m + 8) % 32 = 5 ^ m % 32 := by
  rw [Nat.pow_add]
  have h : 5 ^ 8 % 32 = 1 := by norm_num
  rw [Nat.mul_mod, h]
  simp

/-- Reduce `5^(q*8+r)` modulo 32 to `5^r`. -/
lemma five_pow_mod32_reduce (q r : Nat) :
    5 ^ (q * 8 + r) % 32 = 5 ^ r % 32 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hrewrite : (q + 1) * 8 + r = (q * 8 + r) + 8 := by omega
      rw [hrewrite, five_pow_mod32_period]
      exact ih

/-- `5^16 ≡ 1 (mod 64)`: the period-16 lemma for powers of five. -/
lemma five_pow_mod64_period (m : Nat) :
    5 ^ (m + 16) % 64 = 5 ^ m % 64 := by
  rw [Nat.pow_add]
  have h : 5 ^ 16 % 64 = 1 := by norm_num
  rw [Nat.mul_mod, h]
  simp

/-- Reduce `5^(q*16+r)` modulo 64 to `5^r`. -/
lemma five_pow_mod64_reduce (q r : Nat) :
    5 ^ (q * 16 + r) % 64 = 5 ^ r % 64 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hrewrite : (q + 1) * 16 + r = (q * 16 + r) + 16 := by omega
      rw [hrewrite, five_pow_mod64_period]
      exact ih

/-- Discrete logarithm of `61` base `5` modulo `64`: the exponent is
`3` modulo `16`. -/
lemma five_pow_mod64_eq_61 (m : Nat) :
    5 ^ m % 64 = 61 → m % 16 = 3 := by
  intro h
  have hq := Nat.div_add_mod m 16
  have hred := five_pow_mod64_reduce (m / 16) (m % 16)
  have hred' : 5 ^ (16 * (m / 16) + m % 16) % 64 = 5 ^ (m % 16) % 64 := by
    simpa [Nat.mul_comm] using hred
  rw [← hq] at h
  rw [hred'] at h
  have hlt : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
  interval_cases m % 16
  all_goals (norm_num at h; try norm_num)

/-- If `C mod 32` is not in the period-8 power set of `5`, then
`5^m ≢ C (mod 32)` for every `m`. -/
lemma pow_five_mod32_not_of_not_period (C : Nat)
    (hnot : ∀ r : Nat, r < 8 → 5 ^ r % 32 ≠ C % 32) :
    ¬ ∃ m : Nat, 5 ^ m % 32 = C % 32 := by
  rintro ⟨m, hm⟩
  have hq := Nat.div_add_mod m 8
  have hred := five_pow_mod32_reduce (m / 8) (m % 8)
  have hred' : 5 ^ (8 * (m / 8) + m % 8) % 32 = 5 ^ (m % 8) % 32 := by
    simpa [Nat.mul_comm] using hred
  rw [← hq, hred'] at hm
  exact hnot (m % 8) (Nat.mod_lt m (by norm_num)) hm

/-- If `C mod 64` is not in the period-16 power set of `5`, then
`5^m ≢ C (mod 64)` for every `m`. -/
lemma pow_five_mod64_not_of_not_period (C : Nat)
    (hnot : ∀ r : Nat, r < 16 → 5 ^ r % 64 ≠ C % 64) :
    ¬ ∃ m : Nat, 5 ^ m % 64 = C % 64 := by
  rintro ⟨m, hm⟩
  have hq := Nat.div_add_mod m 16
  have hred := five_pow_mod64_reduce (m / 16) (m % 16)
  have hred' : 5 ^ (16 * (m / 16) + m % 16) % 64 = 5 ^ (m % 16) % 64 := by
    simpa [Nat.mul_comm] using hred
  rw [← hq, hred'] at hm
  exact hnot (m % 16) (Nat.mod_lt m (by norm_num)) hm

/-- d=3 branch `(t=1,δ=1,e=2,u1=1,u2=1)`: `C≡11 (mod 32)` is not a
power of `5` modulo 32. -/
lemma d3_t1_e2_u11_no_pow_mod32 : ¬ ∃ m, 5 ^ m % 32 = 11 := by
  change ¬ ∃ m, 5 ^ m % 32 = (11 % 32)
  apply pow_five_mod32_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=1,δ=1,e=2,u1=1,u2=2)`: `C≡3 (mod 32)` is not a
power of `5` modulo 32. -/
lemma d3_t1_e2_u12_no_pow_mod32 : ¬ ∃ m, 5 ^ m % 32 = 3 := by
  change ¬ ∃ m, 5 ^ m % 32 = (3 % 32)
  apply pow_five_mod32_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=1,δ=1,e=2,u1=2,u2=1)`: `C≡7 (mod 32)` is not a
power of `5` modulo 32. -/
lemma d3_t1_e2_u21_no_pow_mod32 : ¬ ∃ m, 5 ^ m % 32 = 7 := by
  change ¬ ∃ m, 5 ^ m % 32 = (7 % 32)
  apply pow_five_mod32_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=1,δ=1,e=2,u1=2,u2=2)`: `C≡23 (mod 32)` is not a
power of `5` modulo 32. -/
lemma d3_t1_e2_u22_no_pow_mod32 : ¬ ∃ m, 5 ^ m % 32 = 23 := by
  change ¬ ∃ m, 5 ^ m % 32 = (23 % 32)
  apply pow_five_mod32_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=1,e=3,u1=1,u2=1)`: `C≡35 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d1_e3_u11_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 35 := by
  change ¬ ∃ m, 5 ^ m % 64 = (35 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=1,e=3,u1=1,u2=2)`: `C≡19 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d1_e3_u12_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 19 := by
  change ¬ ∃ m, 5 ^ m % 64 = (19 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=1,e=3,u1=2,u2=1)`: `C≡27 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d1_e3_u21_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 27 := by
  change ¬ ∃ m, 5 ^ m % 64 = (27 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=1,e=4,u1=1,u2=1)`: `C≡15 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d1_e4_u11_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 15 := by
  change ¬ ∃ m, 5 ^ m % 64 = (15 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=3,e=2,u1=1,u2=1)`: `C≡15 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d3_e2_u11_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 15 := by
  change ¬ ∃ m, 5 ^ m % 64 = (15 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- d=3 branch `(t=2,δ=3,e=2,u1=2,u2=2)`: `C≡19 (mod 64)` is not a
power of `5` modulo 64. -/
lemma d3_t2_d3_e2_u22_no_pow_mod64 : ¬ ∃ m, 5 ^ m % 64 = 19 := by
  change ¬ ∃ m, 5 ^ m % 64 = (19 % 64)
  apply pow_five_mod64_not_of_not_period
  intro r hr
  interval_cases r <;> norm_num

/-- One-step periodicity of the `m`-component: if
`5^(P2*ord) ≡ 1 (mod m)`, then `5^(r0+P2*(s+ord)) ≡ 5^(r0+P2*s) (mod m)`. -/
lemma d3_period_pow (P2 m ord r0 s : Nat)
    (hperpow : 5 ^ (P2 * ord) % m = 1) :
    5 ^ (r0 + P2 * (s + ord)) % m = 5 ^ (r0 + P2 * s) % m := by
  have harg : r0 + P2 * (s + ord) = (r0 + P2 * s) + P2 * ord := by ring
  rw [harg, Nat.pow_add, Nat.mul_mod, hperpow]
  simp

/-- Period reduction of the `m`-component: the exponent `s` can be
replaced by `s % ord`. -/
lemma d3_period_reduce (P2 m ord r0 s : Nat)
    (hper : ∀ s, 5 ^ (r0 + P2 * (s + ord)) % m = 5 ^ (r0 + P2 * s) % m) :
    5 ^ (r0 + P2 * s) % m = 5 ^ (r0 + P2 * (s % ord)) % m := by
  have hq := Nat.div_add_mod s ord
  have hs : s = ord * (s / ord) + s % ord := by
    exact hq.symm
  have hred_q : ∀ q, 5 ^ (r0 + P2 * (ord * q + s % ord)) % m =
      5 ^ (r0 + P2 * (s % ord)) % m := by
    intro q
    induction q with
    | zero =>
        have hz : r0 + P2 * (ord * 0 + s % ord) = r0 + P2 * (s % ord) := by ring
        rw [hz]
    | succ q ih =>
        have harg : r0 + P2 * (ord * (q + 1) + s % ord) =
            (r0 + P2 * (ord * q + s % ord)) + P2 * ord := by ring
        have harg' : (r0 + P2 * (ord * q + s % ord)) + P2 * ord =
            r0 + P2 * ((ord * q + s % ord) + ord) := by ring
        rw [harg, harg', hper, ih]
  conv_lhs => rw [hs]
  exact hred_q (s / ord)

/-- CRT exclusion for `L = 32*m`: after the mod-32 part fixes
`j % 8 = r0`, the mod-`m` part contradicts the period-`ord` table. -/
lemma d3_no_pow_mod32_m (m C r0 ord : Nat)
    (hr0lt : r0 < 8) (_hmpos : 0 < m) (hordpos : 0 < ord)
    (hr0 : 5 ^ r0 % 32 = C % 32)
    (hnot : ∀ s, s < ord → 5 ^ (r0 + 8 * s) % m ≠ C % m)
    (hper : ∀ s, 5 ^ (r0 + 8 * (s + ord)) % m = 5 ^ (r0 + 8 * s) % m) :
    ¬ ∃ j, 5 ^ j % (32 * m) = C % (32 * m) := by
  rintro ⟨j, hj⟩
  have h32 : 5 ^ j % 32 = C % 32 := by
    have h1 : (5 ^ j % (32 * m)) % 32 = 5 ^ j % 32 :=
      Nat.mod_mod_of_dvd (5 ^ j) (c := 32) (b := 32 * m)
        (by simp [Nat.mul_comm])
    have h2 : (C % (32 * m)) % 32 = C % 32 :=
      Nat.mod_mod_of_dvd C (c := 32) (b := 32 * m)
        (by simp [Nat.mul_comm])
    have hjmod := congrArg (fun x => x % 32) hj
    rw [h1, h2] at hjmod
    exact hjmod
  have hred_j : 5 ^ j % 32 = 5 ^ (j % 8) % 32 := by
    have hq := Nat.div_add_mod j 8
    have hred := five_pow_mod32_reduce (j / 8) (j % 8)
    have hred' : 5 ^ (8 * (j / 8) + j % 8) % 32 = 5 ^ (j % 8) % 32 := by
      simpa [Nat.mul_comm] using hred
    conv_lhs => rw [← hq]
    exact hred'
  have hjr : j % 8 = r0 := by
    rw [hred_j] at h32
    rw [← hr0] at h32
    have hltj : j % 8 < 8 := Nat.mod_lt j (by norm_num)
    interval_cases j % 8
    all_goals interval_cases r0
    all_goals norm_num at h32
    all_goals norm_num
  have hj8 : j = 8 * (j / 8) + r0 := by
    have hdiv := Nat.div_add_mod j 8
    rw [hjr] at hdiv
    exact hdiv.symm
  have hm : 5 ^ j % m = C % m := by
    have h1 : (5 ^ j % (32 * m)) % m = 5 ^ j % m :=
      Nat.mod_mod_of_dvd (5 ^ j) (c := m) (b := 32 * m)
        (by simp [Nat.mul_comm])
    have h2 : (C % (32 * m)) % m = C % m :=
      Nat.mod_mod_of_dvd C (c := m) (b := 32 * m)
        (by simp [Nat.mul_comm])
    have hjmod := congrArg (fun x => x % m) hj
    rw [h1, h2] at hjmod
    exact hjmod
  have hm' : 5 ^ (r0 + 8 * (j / 8)) % m = C % m := by
    rw [hj8] at hm
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  have hred_per := d3_period_reduce 8 m ord r0 (j / 8) hper
  rw [hred_per] at hm'
  exact hnot ((j / 8) % ord) (Nat.mod_lt (j / 8) hordpos) hm'

/-- CRT exclusion for `L = 64*m`: after the mod-64 part fixes
`j % 16 = r0`, the mod-`m` part contradicts the period-`ord` table. -/
lemma d3_no_pow_mod64_m (m C r0 ord : Nat)
    (hr0lt : r0 < 16) (_hmpos : 0 < m) (hordpos : 0 < ord)
    (hr0 : 5 ^ r0 % 64 = C % 64)
    (hnot : ∀ s, s < ord → 5 ^ (r0 + 16 * s) % m ≠ C % m)
    (hper : ∀ s, 5 ^ (r0 + 16 * (s + ord)) % m = 5 ^ (r0 + 16 * s) % m) :
    ¬ ∃ j, 5 ^ j % (64 * m) = C % (64 * m) := by
  rintro ⟨j, hj⟩
  have h64 : 5 ^ j % 64 = C % 64 := by
    have h1 : (5 ^ j % (64 * m)) % 64 = 5 ^ j % 64 :=
      Nat.mod_mod_of_dvd (5 ^ j) (c := 64) (b := 64 * m)
        (by simp [Nat.mul_comm])
    have h2 : (C % (64 * m)) % 64 = C % 64 :=
      Nat.mod_mod_of_dvd C (c := 64) (b := 64 * m)
        (by simp [Nat.mul_comm])
    have hjmod := congrArg (fun x => x % 64) hj
    rw [h1, h2] at hjmod
    exact hjmod
  have hred_j : 5 ^ j % 64 = 5 ^ (j % 16) % 64 := by
    have hq := Nat.div_add_mod j 16
    have hred := five_pow_mod64_reduce (j / 16) (j % 16)
    have hred' : 5 ^ (16 * (j / 16) + j % 16) % 64 = 5 ^ (j % 16) % 64 := by
      simpa [Nat.mul_comm] using hred
    conv_lhs => rw [← hq]
    exact hred'
  have hjr : j % 16 = r0 := by
    rw [hred_j] at h64
    rw [← hr0] at h64
    have hltj : j % 16 < 16 := Nat.mod_lt j (by norm_num)
    interval_cases j % 16
    all_goals interval_cases r0
    all_goals norm_num at h64
    all_goals norm_num
  have hj16 : j = 16 * (j / 16) + r0 := by
    have hdiv := Nat.div_add_mod j 16
    rw [hjr] at hdiv
    exact hdiv.symm
  have hm : 5 ^ j % m = C % m := by
    have h1 : (5 ^ j % (64 * m)) % m = 5 ^ j % m :=
      Nat.mod_mod_of_dvd (5 ^ j) (c := m) (b := 64 * m)
        (by simp [Nat.mul_comm])
    have h2 : (C % (64 * m)) % m = C % m :=
      Nat.mod_mod_of_dvd C (c := m) (b := 64 * m)
        (by simp [Nat.mul_comm])
    have hjmod := congrArg (fun x => x % m) hj
    rw [h1, h2] at hjmod
    exact hjmod
  have hm' : 5 ^ (r0 + 16 * (j / 16)) % m = C % m := by
    rw [hj16] at hm
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  have hred_per := d3_period_reduce 16 m ord r0 (j / 16) hper
  rw [hred_per] at hm'
  exact hnot ((j / 16) % ord) (Nat.mod_lt (j / 16) hordpos) hm'

/-- d=3 branch `(t=1,δ=1,e=3,u1=1,u2=1)`: no `5^(j-1)` solves
`X ≡ 993 (mod 2976)`. -/
lemma d3_t1_e3_u11_no_pow : ¬ ∃ j, 5 ^ j % (32 * 93) = 993 % (32 * 93) := by
  apply d3_no_pow_mod32_m 93 993 0 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 8 93 3 0 s (by norm_num)

/-- d=3 branch `(t=1,δ=1,e=3,u1=1,u2=2)`: no `5^(j-1)` solves
`X ≡ 1745 (mod 1952)`. -/
lemma d3_t1_e3_u12_no_pow : ¬ ∃ j, 5 ^ j % (32 * 61) = 1745 % (32 * 61) := by
  apply d3_no_pow_mod32_m 61 1745 4 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 8 61 15 4 s (by norm_num)

/-- d=3 branch `(t=1,δ=1,e=3,u1=2,u2=1)`: no `5^(j-1)` solves
`X ≡ 1433 (mod 1952)`. -/
lemma d3_t1_e3_u21_no_pow : ¬ ∃ j, 5 ^ j % (32 * 61) = 1433 % (32 * 61) := by
  apply d3_no_pow_mod32_m 61 1433 2 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 8 61 15 2 s (by norm_num)

/-- d=3 branch `(t=1,δ=1,e=4,u1=1,u2=1)`: no `5^(j-1)` solves
`X ≡ 653 (mod 1952)`. -/
lemma d3_t1_e4_u11_no_pow : ¬ ∃ j, 5 ^ j % (32 * 61) = 653 % (32 * 61) := by
  apply d3_no_pow_mod32_m 61 653 7 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 8 61 15 7 s (by norm_num)

/-- d=3 branch `(t=2,δ=1,e=2,u1=1,u2=2)`: no `5^(j-1)` solves
`X ≡ 613 (mod 5952)`. -/
lemma d3_t2_d1_e2_u12_no_pow : ¬ ∃ j, 5 ^ j % (64 * 93) = 613 % (64 * 93) := by
  apply d3_no_pow_mod64_m 93 613 9 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 93 3 9 s (by norm_num)

/-- d=3 branch `(t=2,δ=1,e=2,u1=2,u2=1)`: no `5^(j-1)` solves
`X ≡ 137 (mod 5952)`. -/
lemma d3_t2_d1_e2_u21_no_pow : ¬ ∃ j, 5 ^ j % (64 * 93) = 137 % (64 * 93) := by
  apply d3_no_pow_mod64_m 93 137 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 93 3 6 s (by norm_num)

/-- d=3 branch `(t=2,δ=1,e=2,u1=2,u2=2)`: no `5^(j-1)` solves
`X ≡ 2745 (mod 3904)`. -/
lemma d3_t2_d1_e2_u22_no_pow : ¬ ∃ j, 5 ^ j % (64 * 61) = 2745 % (64 * 61) := by
  apply d3_no_pow_mod64_m 61 2745 10 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 61 15 10 s (by norm_num)

/-- d=3 branch `(t=2,δ=3,e=3,u1=1,u2=1)`: no `5^(j-1)` solves
`X ≡ 1633 (mod 1984)`. -/
lemma d3_t2_d3_e3_u11_no_pow : ¬ ∃ j, 5 ^ j % (64 * 31) = 1633 % (64 * 31) := by
  apply d3_no_pow_mod64_m 31 1633 8 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 31 3 8 s (by norm_num)

/-- d=3 branch `(t=2,δ=3,e=3,u1=1,u2=2)`: no `5^(j-1)` solves
`X ≡ 2737 (mod 3904)`. -/
lemma d3_t2_d3_e3_u12_no_pow : ¬ ∃ j, 5 ^ j % (64 * 61) = 2737 % (64 * 61) := by
  apply d3_no_pow_mod64_m 61 2737 4 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 61 15 4 s (by norm_num)

/-- d=3 branch `(t=2,δ=3,e=3,u1=2,u2=1)`: no `5^(j-1)` solves
`X ≡ 2633 (mod 3904)`. -/
lemma d3_t2_d3_e3_u21_no_pow : ¬ ∃ j, 5 ^ j % (64 * 61) = 2633 % (64 * 61) := by
  apply d3_no_pow_mod64_m 61 2633 6 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 61 15 6 s (by norm_num)

/-- d=3 branch `(t=2,δ=3,e=4,u1=1,u2=1)`: no `5^(j-1)` solves
`X ≡ 2373 (mod 3904)`. -/
lemma d3_t2_d3_e4_u11_no_pow : ¬ ∃ j, 5 ^ j % (64 * 61) = 2373 % (64 * 61) := by
  apply d3_no_pow_mod64_m 61 2373 1 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro s hs
    interval_cases s <;> norm_num
  · intro s
    exact d3_period_pow 16 61 15 1 s (by norm_num)

/-- d≥4, `e=3, j=17`, `t_j=1, δ=1`: the corrected residue `x ≡ 53
(mod 160)` fails (`x ≡ 133 (mod 160)`), so the branch is excluded. -/
lemma dge4_e3_j17_t1_corrected_excluded
    (x : Nat) (hx : x = 4 * 34177 + 5 ^ 16)
    (hmod : x % 160 = 53) : False := by
  rw [hx] at hmod
  norm_num at hmod

/-- d≥4, `e=3, j=17`, `t_j=2, δ=3`: the corrected residue `x ≡ 183
(mod 320)` fails (`x ≡ 263 (mod 320)`), so the branch is excluded. -/
lemma dge4_e3_j17_t2_delta3_corrected_excluded
    (x : Nat) (hx : x = 4 * 34177 + 3 * 5 ^ 16)
    (hmod : x % 320 = 183) : False := by
  rw [hx] at hmod
  norm_num at hmod

/-- Discrete logarithm of `6` base `5` modulo `17`. -/
lemma five_pow_mod17_eq (m : Nat) :
    5 ^ m % 17 = 6 ↔ m % 16 = 3 := by
  constructor
  · intro h
    have hq := Nat.div_add_mod m 16
    have hred := five_pow_mod17_reduce (m / 16) (m % 16)
    have hred' : 5 ^ (16 * (m / 16) + m % 16) % 17 = 5 ^ (m % 16) % 17 := by
      simpa [Nat.mul_comm] using hred
    rw [← hq] at h
    rw [hred'] at h
    have hlt : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
    interval_cases m % 16
    all_goals (norm_num at h; try norm_num)
  · intro h
    have hq := Nat.div_add_mod m 16
    have hred := five_pow_mod17_reduce (m / 16) (m % 16)
    have hred' : 5 ^ (16 * (m / 16) + m % 16) % 17 = 5 ^ (m % 16) % 17 := by
      simpa [Nat.mul_comm] using hred
    rw [← hq, hred']
    rw [h]
    norm_num

/-- `5^64 ≡ 1 (mod 256)`: the period-64 lemma for powers of five. -/
lemma five_pow_mod256_period (m : Nat) :
    5 ^ (m + 64) % 256 = 5 ^ m % 256 := by
  rw [Nat.pow_add]
  have h : 5 ^ 64 % 256 = 1 := by norm_num
  rw [Nat.mul_mod, h]
  simp

/-- Reduce `5^(q*64+r)` modulo 256 to `5^r`. -/
lemma five_pow_mod256_reduce (q r : Nat) :
    5 ^ (q * 64 + r) % 256 = 5 ^ r % 256 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hrewrite : (q + 1) * 64 + r = (q * 64 + r) + 64 := by omega
      rw [hrewrite, five_pow_mod256_period]
      exact ih

/-- Discrete logarithm of `45` base `5` modulo `256`. -/
lemma five_pow_mod256_eq (m : Nat) :
    5 ^ m % 256 = 45 ↔ m % 64 = 7 := by
  constructor
  · intro h
    have hq := Nat.div_add_mod m 64
    have hred := five_pow_mod256_reduce (m / 64) (m % 64)
    have hred' : 5 ^ (64 * (m / 64) + m % 64) % 256 = 5 ^ (m % 64) % 256 := by
      simpa [Nat.mul_comm] using hred
    rw [← hq] at h
    rw [hred'] at h
    have hlt : m % 64 < 64 := Nat.mod_lt _ (by norm_num)
    interval_cases m % 64
    all_goals (norm_num at h; try norm_num)
  · intro h
    have hq := Nat.div_add_mod m 64
    have hred := five_pow_mod256_reduce (m / 64) (m % 64)
    have hred' : 5 ^ (64 * (m / 64) + m % 64) % 256 = 5 ^ (m % 64) % 256 := by
      simpa [Nat.mul_comm] using hred
    rw [← hq, hred']
    rw [h]
    norm_num

/-- The `d=2` survivor `(未=1, e=2, u1=1)` fails the two power congruences
`5^m ≡ 6 (mod 17)` and `5^m ≡ 45 (mod 256)`. -/
theorem d2_survivor_mod_contradicts (m : Nat)
    (h17 : 5 ^ m % 17 = 6) (h256 : 5 ^ m % 256 = 45) : False := by
  have hm16 : m % 16 = 3 := (five_pow_mod17_eq m).mp h17
  have hm64 : m % 64 = 7 := (five_pow_mod256_eq m).mp h256
  have hmod64 : (m % 64) % 16 = m % 16 := by
    exact Nat.mod_mod_of_dvd (a := m) (c := 16) (b := 64) (by norm_num)
  have hm16' : m % 16 = 7 := by
    rw [← hmod64, hm64]
  omega

/-- Corrected `d=2` survivor family: for `j ≡ 4 (mod 16)`, the reset
predecessor `x = (25·5^(j-1)-14)/17` has `x+1 ≡ 4 (mod 5)` and is even.
This does NOT violate `ResetHeadEq`: with `k=0` the terminal odd part is
`s0 = x+1-5^(j-1)`, which is odd (`d2_survivor_candidate_s0_odd`). -/
lemma d2_survivor_terminal_even (j x : Nat)
    (hj : j % 16 = 4)
    (hint : 17 ∣ 25 * 5 ^ (j - 1) - 14)
    (hx : x = (25 * 5 ^ (j - 1) - 14) / 17) :
    (x + 1) % 2 = 0 ∧ (x + 1) % 5 = 4 := by
  have hjpos : 1 ≤ j := by
    have hle : j % 16 ≤ j := Nat.mod_le j 16
    omega
  have hdiv := Nat.div_add_mod j 16
  rw [hj] at hdiv
  have hjsub : j - 1 = 16 * (j / 16) + 3 := by omega
  have h5_17 : 5 ^ (j - 1) % 17 = 6 := by
    rw [hjsub]
    have hred := five_pow_mod17_reduce (j / 16) 3
    simpa [Nat.mul_comm, Nat.add_comm] using hred
  have hge : 14 ≤ 25 * 5 ^ (j - 1) := by
    have h1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by norm_num)
    nlinarith
  have h17x : 17 * x = 25 * 5 ^ (j - 1) - 14 := by
    have hcancel := Nat.mul_div_cancel' hint
    rw [← hx] at hcancel
    exact hcancel
  have hnum3 : 17 ∣ 25 * 5 ^ (j - 1) + 3 := by
    rcases hint with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega
  have hx1 : x + 1 = (25 * 5 ^ (j - 1) + 3) / 17 := by
    have hmul : 17 * (x + 1) = 25 * 5 ^ (j - 1) + 3 := by
      omega
    rw [← hmul]
    exact (Nat.mul_div_right (x + 1) (by decide : 0 < 17)).symm
  have h5_34 : 5 ^ (j - 1) % 34 = 23 := by
    rw [hjsub]
    have hred : 5 ^ ((j / 16) * 16 + 3) % 34 = 5 ^ 3 % 34 := by
      have hperiod : ∀ q, 5 ^ (q * 16 + 3) % 34 = 5 ^ 3 % 34 := by
        intro q
        calc
          5 ^ (q * 16 + 3) % 34 = ((5 ^ 16) ^ q * 5 ^ 3) % 34 := by
            rw [show q * 16 + 3 = 16 * q + 3 by omega]
            rw [← Nat.pow_mul, ← Nat.pow_add]
          _ = ((5 ^ 16) ^ q % 34 * (5 ^ 3 % 34)) % 34 := by
            rw [Nat.mul_mod]
          _ = (1 * (5 ^ 3 % 34)) % 34 := by
            have hpow : (5 ^ 16) ^ q % 34 = 1 := by
              induction q with
              | zero => norm_num
              | succ q ih =>
                  rw [pow_succ]
                  rw [Nat.mul_mod, ih]
                  norm_num
            rw [hpow]
          _ = 5 ^ 3 % 34 := by
            norm_num
      exact hperiod (j / 16)
    simpa [Nat.mul_comm, Nat.add_comm] using hred
  have h34 : (25 * 5 ^ (j - 1) + 3) % 34 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod, h5_34]
    try norm_num
  have hx1_even : (x + 1) % 2 = 0 := by
    have hdvd : 34 ∣ 25 * 5 ^ (j - 1) + 3 := Nat.dvd_iff_mod_eq_zero.mpr h34
    rcases hdvd with ⟨k, hk⟩
    have hquot : (25 * 5 ^ (j - 1) + 3) / 17 = 2 * k := by
      have hk' : 25 * 5 ^ (j - 1) + 3 = 17 * (2 * k) := by
        rw [hk]
        ring
      rw [hk']
      exact Nat.mul_div_right (2 * k) (by decide : 0 < 17)
    rw [hx1, hquot]
    try norm_num
  have hx1_mod5 : (x + 1) % 5 = 4 := by
    have hmul : 17 * (x + 1) = 25 * 5 ^ (j - 1) + 3 := by
      rw [hx1]
      exact Nat.mul_div_cancel' hnum3
    have hN5 : (25 * 5 ^ (j - 1) + 3) % 5 = 3 := by
      rw [Nat.add_mod, Nat.mul_mod]
      norm_num
    have h17x5 : (17 * (x + 1)) % 5 = 3 := by
      rw [hmul, hN5]
    have hmod : (17 * (x + 1)) % 5 = (2 * ((x + 1) % 5)) % 5 := by
      rw [Nat.mul_mod]
      try norm_num
    rw [hmod] at h17x5
    have hlt : (x + 1) % 5 < 5 := Nat.mod_lt (x + 1) (by norm_num)
    interval_cases (x + 1) % 5
    all_goals norm_num at h17x5
    all_goals norm_num
  exact ⟨hx1_even, hx1_mod5⟩

/-- Corrected `d=2` survivor parameterization: under the corrected
residue `x ≡ 183 (mod 320)`, the `d=2` segment equation forces
`j ≡ 4 (mod 16)` and the survivor formulas for `g` and `x`. -/
theorem d2_survivor_parameterization_corrected
    (j g : Nat) (hj : 3 ≤ j)
    (hseg : 8 * g + 4 * 5 ^ (j - 1) = 7 + 25 * g)
    (hxmod : candidateX j 2 g 1 % 320 = 183) :
    j % 16 = 4 ∧
      17 ∣ 25 * 5 ^ (j - 1) - 14 ∧
      candidateX j 2 g 1 = (25 * 5 ^ (j - 1) - 14) / 17 := by
  let P := 5 ^ (j - 1)
  have h17g : 4 * P = 7 + 17 * g := by
    dsimp [P]
    nlinarith [hseg]
  have hx : candidateX j 2 g 1 = 2 * g + P := by
    simp [candidateX, P]
  have hge : 7 ≤ 4 * P := by
    have h1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by norm_num)
    nlinarith
  have hge14 : 14 ≤ 25 * P := by nlinarith
  have h17x : 17 * candidateX j 2 g 1 = 25 * P - 14 := by
    rw [hx]
    have h17x' : 17 * (2 * g + P) + 14 = 25 * P := by
      nlinarith [h17g]
    omega
  have hdiv : 17 ∣ 25 * P - 14 := by
    refine ⟨2 * g + P, ?_⟩
    rw [← h17x, hx]
  have hxeq : candidateX j 2 g 1 = (25 * P - 14) / 17 := by
    rw [← h17x]
    exact (Nat.mul_div_right (candidateX j 2 g 1) (by decide : 0 < 17)).symm
  have hxmodEq : candidateX j 2 g 1 ≡ 183 [MOD 320] := by
    rw [Nat.ModEq]
    exact hxmod
  have hmul := hxmodEq.mul_right 17
  have h17mod : (17 * candidateX j 2 g 1) % 320 = 231 := by
    rw [Nat.ModEq] at hmul
    norm_num at hmul
    simpa [Nat.mul_comm] using hmul
  have hsub : (25 * P - 14) % 320 = 231 := by
    rw [h17x] at h17mod
    exact h17mod
  have h25mod320 : (25 * P) % 320 = 245 := by
    have hsubEq : 25 * P - 14 ≡ 231 [MOD 320] := by
      rw [Nat.ModEq]
      exact hsub
    have hplus := hsubEq.add_right 14
    have hmod' : (25 * P - 14 + 14) % 320 = (231 + 14) % 320 := by
      rw [Nat.ModEq] at hplus
      exact hplus
    have hcancel : (25 * P - 14) + 14 = 25 * P := Nat.sub_add_cancel hge14
    rw [hcancel] at hmod'
    norm_num at hmod'
    exact hmod'
  have hmod64 : (25 * P) % 64 = 53 := by
    have hred : (25 * P) % 320 % 64 = (25 * P) % 64 :=
      Nat.mod_mod_of_dvd (25 * P) (c := 64) (b := 320) (by norm_num)
    rw [h25mod320] at hred
    norm_num at hred
    exact hred.symm
  have h25inv : 25 * 41 ≡ 1 [MOD 64] := by norm_num [Nat.ModEq]
  have hP64 : P % 64 = 61 := by
    have hmodEq : 25 * P ≡ 53 [MOD 64] := by
      rw [Nat.ModEq]
      exact hmod64
    have hmul' := hmodEq.mul_right 41
    have hleft : (25 * P) * 41 ≡ P [MOD 64] := by
      have h1 := h25inv.mul_left P
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1
    have hright : (25 * P) * 41 ≡ 53 * 41 [MOD 64] := hmul'
    have htarget : P ≡ 61 [MOD 64] := by
      have htrans := hleft.symm.trans hright
      norm_num at htrans ⊢
      exact htrans
    rw [Nat.ModEq] at htarget
    exact htarget
  have hP16 : (j - 1) % 16 = 3 := by
    have h := hP64
    dsimp [P] at h
    exact five_pow_mod64_eq_61 (j - 1) h
  have hj16 : j % 16 = 4 := by
    have hmod : j % 16 = ((j - 1) % 16 + 1) % 16 := by
      have hsubj : j = (j - 1) + 1 := by omega
      rw [hsubj, Nat.add_mod]
      simp
    rw [hmod, hP16]
  exact ⟨hj16, hdiv, hxeq⟩

/-- For the corrected `d=2` survivor, the reset odd part is
`s0 = x + 1 - 5^(j-1)` and is odd.  In particular `s0` is not `x + 1`,
so the "even `s0`" exclusion in the document is not valid. -/
theorem d2_survivor_candidate_s0_odd (j x : Nat)
    (hj4 : j % 16 = 4)
    (hint : 17 ∣ 25 * 5 ^ (j - 1) - 14)
    (hx : x = (25 * 5 ^ (j - 1) - 14) / 17) :
    (x + 1 - 5 ^ (j - 1)) % 2 = 1 := by
  have hpar := d2_survivor_terminal_even j x hj4 hint hx
  let P := 5 ^ (j - 1)
  have hPodd : P % 2 = 1 := by
    dsimp [P]
    exact StringFlow.Lte.five_pow_odd (j - 1)
  have hge : 14 ≤ 25 * P := by
    have h1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by norm_num)
    dsimp [P]
    nlinarith
  have h17x : 17 * x = 25 * P - 14 := by
    have hc := Nat.mul_div_cancel' hint
    rw [← hx] at hc
    exact hc
  have h17x1 : 17 * (x + 1) = 25 * P + 3 := by
    have hmul : 17 * x + 17 = 25 * P + 3 := by omega
    nlinarith
  have hgeP : P ≤ x + 1 := by
    have hle17 : 17 * P ≤ 25 * P + 3 := by nlinarith
    have hle17' : 17 * P ≤ 17 * (x + 1) := by
      rw [h17x1]
      exact hle17
    exact Nat.le_of_mul_le_mul_left hle17' (by decide : 0 < 17)
  have hA : (((x + 1 - P) % 2) + 1) % 2 = 0 := by
    have hsub : (x + 1 - P) + P = x + 1 := Nat.sub_add_cancel hgeP
    have hmod : ((x + 1 - P) + P) % 2 = 0 := by
      rw [hsub]
      exact hpar.1
    rw [Nat.add_mod, hPodd] at hmod
    exact hmod
  have hlt : (x + 1 - P) % 2 < 2 := Nat.mod_lt (x + 1 - P) (by norm_num)
  rcases Nat.mod_two_eq_zero_or_one (x + 1 - P) with h0 | h1
  · have hbad : (0 + 1) % 2 = 0 := by
      rw [h0] at hA
      exact hA
    norm_num at hbad
  · exact h1

/-- Corrected `d=3` survivor family (`t=2, δ=1, e=2, u1=u2=1`): with
`X = 5^(j-1) ≡ 73 (mod 109)` and `x = (125X-78)/109`, the reset
predecessor has `x+1 ≡ 4 (mod 5)` and is even.  As in `d=2`, this does
not violate `ResetHeadEq`; the `d=3` exclusion is closed by the weight-6
full-orbit step, not by this parity. -/
lemma d3_survivor_terminal_even (j x : Nat)
    (hX : 5 ^ (j - 1) % 109 = 73)
    (hint : 109 ∣ 125 * 5 ^ (j - 1) - 78)
    (hx : x = (125 * 5 ^ (j - 1) - 78) / 109) :
    (x + 1) % 2 = 0 ∧ (x + 1) % 5 = 4 := by
  have h109x : 109 * x = 125 * 5 ^ (j - 1) - 78 := by
    have hc := Nat.mul_div_cancel' hint
    rw [← hx] at hc
    exact hc
  have hge : 78 ≤ 125 * 5 ^ (j - 1) := by
    have h1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by norm_num)
    nlinarith [Nat.mul_le_mul_left 125 h1]
  have hnum3 : 109 ∣ 125 * 5 ^ (j - 1) + 31 := by
    refine ⟨x + 1, ?_⟩
    omega
  have hx1 : x + 1 = (125 * 5 ^ (j - 1) + 31) / 109 := by
    have hmul : 109 * (x + 1) = 125 * 5 ^ (j - 1) + 31 := by
      omega
    rw [← hmul]
    exact (Nat.mul_div_right (x + 1) (by decide : 0 < 109)).symm
  have hN2 : (125 * 5 ^ (j - 1) + 31) % 2 = 0 := by
    have hodd : (125 * 5 ^ (j - 1)) % 2 = 1 := by
      rw [Nat.mul_mod]
      have h5 : 5 ^ (j - 1) % 2 = 1 := StringFlow.Lte.five_pow_odd (j - 1)
      norm_num [h5]
    rw [Nat.add_mod, hodd]
    try norm_num
  have h218 : 218 ∣ 125 * 5 ^ (j - 1) + 31 := by
    rcases hnum3 with ⟨a, ha⟩
    have ha2 : a % 2 = 0 := by
      have hmod : (109 * a) % 2 = a % 2 := by
        rw [Nat.mul_mod]
        norm_num
      have hN2' : (109 * a) % 2 = 0 := by
        rw [← ha]
        exact hN2
      rw [← hmod]
      exact hN2'
    have ha_eq : a = 2 * (a / 2) := by
      have hdiv := (Nat.div_add_mod a 2).symm
      rw [ha2] at hdiv
      simpa using hdiv
    refine ⟨a / 2, ?_⟩
    calc
      125 * 5 ^ (j - 1) + 31 = 109 * a := ha
      _ = 218 * (a / 2) := by
        conv_lhs => rw [ha_eq]
        ring
  have hx1_even : (x + 1) % 2 = 0 := by
    rcases h218 with ⟨k, hk⟩
    have hquot : (125 * 5 ^ (j - 1) + 31) / 109 = 2 * k := by
      have hk' : 125 * 5 ^ (j - 1) + 31 = 109 * (2 * k) := by
        rw [hk]
        ring_nf
      rw [hk']
      exact Nat.mul_div_right (2 * k) (by decide : 0 < 109)
    rw [hx1, hquot]
    try norm_num
  have hx1_mod5 : (x + 1) % 5 = 4 := by
    have hmul : 109 * (x + 1) = 125 * 5 ^ (j - 1) + 31 := by
      rw [hx1]
      exact Nat.mul_div_cancel' hnum3
    have hN5 : (125 * 5 ^ (j - 1) + 31) % 5 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod]
      norm_num
    have h109x5 : (109 * (x + 1)) % 5 = 1 := by
      rw [hmul, hN5]
    have hmod : (109 * (x + 1)) % 5 = (4 * ((x + 1) % 5)) % 5 := by
      rw [Nat.mul_mod]
      try norm_num
    rw [hmod] at h109x5
    have hlt : (x + 1) % 5 < 5 := Nat.mod_lt (x + 1) (by norm_num)
    interval_cases (x + 1) % 5
    all_goals norm_num at h109x5
    all_goals norm_num
  exact ⟨hx1_even, hx1_mod5⟩

/-- If `25*p ≡ 101 (mod 256)`, then `p ≡ 45 (mod 256)`. -/
lemma mod_inv_25_256 (p : Nat) (h : (25 * p) % 256 = 101) :
    p % 256 = 45 := by
  have hmodEq : 25 * p ≡ 101 [MOD 256] := by
    rw [Nat.ModEq]
    exact h
  have h25 : 25 * 41 ≡ 1 [MOD 256] := by
    norm_num [Nat.ModEq]
  have hmul := hmodEq.mul_right 41
  have hleft : (25 * p) * 41 = 25 * 41 * p := by ring
  have h25p : 25 * 41 * p ≡ p [MOD 256] := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (h25.mul_left p)
  have hcombine : (25 * p) * 41 ≡ p [MOD 256] := by
    rw [hleft]
    exact h25p
  have htarget : (25 * p) * 41 ≡ 101 * 41 [MOD 256] := hmul
  have h101 : 101 * 41 = 4141 := by norm_num
  have h45 : 4141 % 256 = 45 := by norm_num
  have hp : p ≡ 45 [MOD 256] := by
    have htrans := hcombine.symm.trans htarget
    rw [h101] at htrans
    have hmod45 : 4141 ≡ 45 [MOD 256] := by
      norm_num [Nat.ModEq]
    exact htrans.trans hmod45
  rw [Nat.ModEq] at hp
  exact hp

/-- The `d=2` survivor equations force the two power congruences. -/
theorem d2_survivor_congruences (j g : Nat) (hj : 3 ≤ j)
    (hseg : 8 * g + 4 * 5 ^ (j - 1) = 7 + 25 * g)
    (hxmod : candidateX j 2 g 1 % 1280 = 743) :
    5 ^ (j - 1) % 17 = 6 ∧ 5 ^ (j - 1) % 256 = 45 := by
  let P := 5 ^ (j - 1)
  have hPdef : P = 5 ^ (j - 1) := rfl
  have h17g : 4 * P = 7 + 17 * g := by
    dsimp [P]
    nlinarith [hseg]
  have h4mod : (4 * P) % 17 = 7 := by
    rw [h17g]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self]
    simp
  have hmod17' : (4 * (P % 17)) % 17 = 7 := by
    simpa [Nat.mul_mod] using h4mod
  have hP17 : P % 17 = 6 := by
    have hlt : P % 17 < 17 := Nat.mod_lt _ (by norm_num)
    interval_cases P % 17
    all_goals (norm_num at hmod17'; try norm_num)
  have hx : candidateX j 2 g 1 = 2 * g + P := by
    simp [candidateX, P]
  have h17x : 17 * candidateX j 2 g 1 = 25 * P - 14 := by
    rw [hx]
    have h17x' : 17 * (2 * g + P) + 14 = 25 * P := by
      nlinarith [h17g]
    omega
  have hxmodEq : candidateX j 2 g 1 ≡ 743 [MOD 1280] := by
    rw [Nat.ModEq]
    exact hxmod
  have h17modEq : 17 * candidateX j 2 g 1 ≡ 17 * 743 [MOD 1280] :=
    by
      have hmul := hxmodEq.mul_right 17
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have h17xmod : (17 * candidateX j 2 g 1) % 1280 = 1111 := by
    rw [Nat.ModEq] at h17modEq
    norm_num at h17modEq ⊢
    exact h17modEq
  have h25sub : (25 * P - 14) % 1280 = 1111 := by
    rw [h17x] at h17xmod
    exact h17xmod
  have h5 : 25 ≤ P := by
    dsimp [P]
    have hle : 2 ≤ j - 1 := by omega
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hle)
  have h14 : 14 ≤ 25 * P := by nlinarith [h5]
  have h25modEq : 25 * P ≡ 1125 [MOD 1280] := by
    have hsub := Nat.sub_add_cancel h14
    have hmodEqsub : 25 * P - 14 ≡ 1111 [MOD 1280] := by
      rw [Nat.ModEq]
      exact h25sub
    have hadd := hmodEqsub.add_right 14
    rw [hsub] at hadd
    norm_num at hadd ⊢
    exact hadd
  have h25mod1280 : (25 * P) % 1280 = 1125 := by
    rw [Nat.ModEq] at h25modEq
    exact h25modEq
  have hmod256 : (25 * P) % 256 = 101 := by
    have hmod : (25 * P) % 1280 % 256 = (25 * P) % 256 :=
      Nat.mod_mod_of_dvd (25 * P) (c := 256) (b := 1280) (by norm_num)
    rw [h25mod1280] at hmod
    norm_num at hmod
    exact hmod.symm
  have hP256 : P % 256 = 45 := mod_inv_25_256 P hmod256
  constructor
  · simpa [P] using hP17
  · simpa [P] using hP256

/-- 36.30.23.5, `d=2`: the full segment exclusion, combining the size
branches with the survivor congruence contradiction. -/
theorem d2_exclusion
    (j e g δ u1 : Nat)
    (hj : 3 ≤ j)
    (_hgpos : 0 < g)
    (hg : g < 5 ^ (j - 1) / 2 ^ (e - 1))
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hu1 : u1 = 1 ∨ u1 = 2)
    (hseg : 2 ^ (u1 + e) * g + 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) =
      5 + 2 ^ u1 + 25 * g)
    (hxmod : candidateX j e g δ % 1280 = 743) :
    False := by
  by_cases hsurv : δ = 1 ∧ e = 2 ∧ u1 = 1
  · rcases hsurv with ⟨rfl, rfl, rfl⟩
    norm_num at hseg
    have hcong := d2_survivor_congruences j g hj hseg hxmod
    exact d2_survivor_mod_contradicts (j - 1) hcong.1 hcong.2
  · exact d2_size_exclusion j e g δ u1 hj _hgpos hg hδ he hu1 hseg hsurv

/-- Bridge: the `d=3` unique family contradiction, expressed with
`orbitStepWeight`. -/
theorem d3_family_bridge_contradicts
    (j n : Nat)
    (hjmod : j % 1728 = 924)
    (hn : n = j + 4)
    (hsmall : ∀ m : Nat, m < n → orbitStepWeight m ≤ 2)
    (hbig : orbitStepWeight n = 6) :
    False := by
  exact d3_family_mod_contradicts_base j n hjmod hn hsmall hbig

/-- Bridge: a candidate first `t >= 3` step of weight at least `5`
contradicts the finite base, expressed with `orbitStepWeight`. -/
theorem candidate_first_big_weight_ge_five_bridge
    (n k : Nat) (hk : 5 ≤ k)
    (hsmall : ∀ m : Nat, m < n → orbitStepWeight m ≤ 2)
    (hbig : orbitStepWeight n = k) :
    False := by
  exact candidate_first_big_step_weight_ge_five n k hk hsmall hbig

/-- 36.30.23.5, `d=3` unique family: the `z→w` step has weight `6` at
depth `j+4`, contradicting the finite base. -/
theorem d3_family_big_weight_excluded
    (j z w : Nat)
    (hjmod : j % 1728 = 924)
    (hz : fullOrbitIter (j + 4) = z)
    (h5z : 5 * z + 1 = 2 ^ 6 * w)
    (hwodd : w % 2 = 1)
    (hsmall : ∀ m : Nat, m < j + 4 → orbitStepWeight m ≤ 2) :
    False := by
  have hbig : orbitStepWeight (j + 4) = 6 :=
    orbitStepWeight_of_mul (j + 4) 6 z w hz hwodd h5z
  exact d3_family_bridge_contradicts j (j + 4) hjmod rfl hsmall hbig

/-- 36.30.23.5, `d≥4` branch `e=2, a≥1`: the `y→x` step has weight
`1+4a ≥ 5`, contradicting the finite base. -/
theorem dge4_e2_a_ge1_excluded
    (n a y x : Nat)
    (ha : 1 ≤ a)
    (hy : fullOrbitIter n = y)
    (hxodd : x % 2 = 1)
    (hstep : 5 * y + 1 = 2 ^ (1 + 4 * a) * x)
    (hsmall : ∀ m : Nat, m < n → orbitStepWeight m ≤ 2) :
    False := by
  have hbig : orbitStepWeight n = 1 + 4 * a :=
    orbitStepWeight_of_mul n (1 + 4 * a) y x hy hxodd hstep
  have hk : 5 ≤ 1 + 4 * a := by omega
  exact candidate_first_big_weight_ge_five_bridge n (1 + 4 * a) hk hsmall hbig

/-- A full-orbit state at depth at most 15 is also `OrbitFrom7`
reachable.  This is the finite-prefix half of the `FullOrbitFrom7`
to `OrbitFrom7` bridge. -/
theorem fullOrbitFrom7_le15_imp_OrbitFrom7 (r : Nat)
    (_hReach : FullOrbitFrom7 r)
    (hshort : ∃ n : Nat, fullOrbitIter n = r ∧ n ≤ 15) :
    OrbitFrom7 r := by
  rcases hshort with ⟨n, hn, hnle⟩
  rw [← hn]
  exact fullOrbitPrefix_imp_OrbitFrom7 n hnle

/-- The segment word of `d` consecutive full-orbit step weights starting
at depth `j-1`. -/
def orbitSegmentWord : Nat → Nat → List Nat
  | _, 0 => []
  | j, d + 1 => orbitSegmentWord j d ++ [orbitStepWeight (j - 1 + d)]

/-- The segment word has length `d`. -/
lemma orbitSegmentWord_length (j d : Nat) :
    (orbitSegmentWord j d).length = d := by
  induction d with
  | zero => simp [orbitSegmentWord]
  | succ d ih => simp [orbitSegmentWord, ih]

/-- The segment word maps `g = fullOrbitIter (j-1)` to
`x = fullOrbitIter (j-1+d)`. -/
lemma orbitSegmentWord_orbit (j d : Nat) :
    StringFlow.Word.wordOrbit (orbitSegmentWord j d) (fullOrbitIter (j - 1)) =
      fullOrbitIter (j - 1 + d) := by
  induction d with
  | zero => simp [orbitSegmentWord, StringFlow.Word.wordOrbit]
  | succ d ih =>
      have hprev : StringFlow.Word.wordOrbit (orbitSegmentWord j d)
          (fullOrbitIter (j - 1)) = fullOrbitIter (j - 1 + d) := ih
      have hlast : fullOrbitIter (j - 1 + (d + 1)) =
          (5 * fullOrbitIter (j - 1 + d) + 1) /
            2 ^ orbitStepWeight (j - 1 + d) := by
        have h : j - 1 + (d + 1) = (j - 1 + d) + 1 := by omega
        rw [h]
        simp [fullOrbitIter, fullOrbitStep, orbitStepWeight]
      rw [orbitSegmentWord]
      rw [wordOrbit_append_singleton]
      rw [hprev]
      exact hlast

/-- The segment word is legal from `fullOrbitIter (j-1)`. -/
lemma orbitSegmentWord_valid (j d : Nat) :
    StringFlow.Word.wordValid (orbitSegmentWord j d) (fullOrbitIter (j - 1)) := by
  induction d with
  | zero => simp [orbitSegmentWord, StringFlow.Word.wordValid]
  | succ d ih =>
      have hprev : StringFlow.Word.wordValid (orbitSegmentWord j d)
          (fullOrbitIter (j - 1)) := ih
      have htail : (5 * fullOrbitIter (j - 1 + d) + 1) %
          2 ^ orbitStepWeight (j - 1 + d) = 0 := by
        have hmul := fullOrbitStep_mul_eq (fullOrbitIter (j - 1 + d))
        have hdvd : 2 ^ orbitStepWeight (j - 1 + d) ∣
            5 * fullOrbitIter (j - 1 + d) + 1 := by
          unfold orbitStepWeight
          exact ⟨fullOrbitStep (fullOrbitIter (j - 1 + d)), hmul.symm⟩
        exact Nat.dvd_iff_mod_eq_zero.mp hdvd
      rw [orbitSegmentWord]
      rw [wordValid_append_singleton]
      constructor
      · exact hprev
      · rw [orbitSegmentWord_orbit]
        exact htail

/-- Exact segment word equation from the full orbit:
`2^W * x = 5^d * g + A`, where `W` is the total segment weight and
`A = wordA (orbitSegmentWord j d)`. -/
lemma orbitSegmentWord_equation (j d : Nat) :
    2 ^ StringFlow.wordWeight (orbitSegmentWord j d) * fullOrbitIter (j - 1 + d) =
      5 ^ d * fullOrbitIter (j - 1) +
        StringFlow.Word.wordA (orbitSegmentWord j d) := by
  have hvalid := orbitSegmentWord_valid j d
  have hid := StringFlow.Word.word_orbit_identity (orbitSegmentWord j d)
    (fullOrbitIter (j - 1)) hvalid
  rw [orbitSegmentWord_orbit] at hid
  rw [orbitSegmentWord_length] at hid
  exact hid

/-- Candidate form of the segment equation: with
`x = candidateX j e g δ` at depth `j-1+d`, the exact word equation holds
for the actual orbit segment. -/
lemma orbitSegmentWord_candidate_equation
    (j d e g δ : Nat)
    (hg : fullOrbitIter (j - 1) = g)
    (hx : fullOrbitIter (j - 1 + d) = candidateX j e g δ) :
    2 ^ StringFlow.wordWeight (orbitSegmentWord j d) * candidateX j e g δ =
      5 ^ d * g + StringFlow.Word.wordA (orbitSegmentWord j d) := by
  have h := orbitSegmentWord_equation j d
  rw [hg] at h
  rw [hx] at h
  exact h

/-- `d=1` bridge: the single-step segment equation
`5*g+1 = 2^(1+4a)*x` is the actual full-orbit step from `g` to `x`. -/
lemma d1_segment_equation
    (j e g δ a : Nat)
    (hj : 1 ≤ j)
    (hg : fullOrbitIter (j - 1) = g)
    (hx : fullOrbitIter j = candidateX j e g δ)
    (hstep : orbitStepWeight (j - 1) = 1 + 4 * a) :
    5 * g + 1 = 2 ^ (1 + 4 * a) * candidateX j e g δ := by
  have hji : j - 1 + 1 = j := by omega
  have hx' : fullOrbitIter (j - 1 + 1) = candidateX j e g δ := by
    rw [hji]
    exact hx
  have hgen := orbitSegmentWord_candidate_equation j 1 e g δ hg hx'
  have hw : StringFlow.wordWeight (orbitSegmentWord j 1) = 1 + 4 * a := by
    simp [orbitSegmentWord, StringFlow.wordWeight, hstep]
  have hA : StringFlow.Word.wordA (orbitSegmentWord j 1) = 1 := by
    simp [orbitSegmentWord, StringFlow.Word.wordA]
  rw [hw, hA] at hgen
  exact hgen.symm

/-- Converse of `d1_segment_equation`: a single full-orbit step of weight
`1+4a` from `g` to `x` makes `x` the depth-`j` candidate state. -/
theorem candidate_d1_input
    (j e g δ a x : Nat)
    (hj : 1 ≤ j)
    (hg : fullOrbitIter (j - 1) = g)
    (hxeq : x = candidateX j e g δ)
    (hstep : orbitStepWeight (j - 1) = 1 + 4 * a)
    (hseg : 5 * g + 1 = 2 ^ (1 + 4 * a) * x) :
    fullOrbitIter j = candidateX j e g δ := by
  have hji : j - 1 + 1 = j := by omega
  have hfj0 : fullOrbitIter (j - 1 + 1) = fullOrbitStep (fullOrbitIter (j - 1)) := by
    rw [show j - 1 + 1 = Nat.succ (j - 1) by omega]
    simp [fullOrbitIter]
  have hfj1 : fullOrbitStep (fullOrbitIter (j - 1)) =
      (5 * g + 1) / 2 ^ orbitStepWeight (j - 1) := by
    rw [hg]
    simp [fullOrbitStep]
    simp [orbitStepWeight, hg]
  have hstep_idx : fullOrbitIter j = fullOrbitStep (fullOrbitIter (j - 1)) := by
    rw [← hji]
    exact hfj0
  have hfj : fullOrbitIter j = (5 * g + 1) / 2 ^ orbitStepWeight (j - 1) := by
    rw [hstep_idx, hfj1]
  rw [hstep, hseg] at hfj
  have hcancel : (2 ^ (1 + 4 * a) * x) / 2 ^ (1 + 4 * a) = x :=
    Nat.mul_div_right x (Nat.pow_pos (by decide : 0 < 2))
  rw [hcancel] at hfj
  rw [hxeq] at hfj
  exact hfj

/-- `d=2` bridge: with `a=0` (so the second segment step has weight
`1`), the exact segment equation is the `hseg` input of
`d2_exclusion`. -/
lemma d2_segment_equation
    (j e g δ u1 : Nat)
    (hj : 1 ≤ j)
    (he : 2 ≤ e)
    (hg : fullOrbitIter (j - 1) = g)
    (hx : fullOrbitIter (j + 1) = candidateX j e g δ)
    (hu1 : orbitStepWeight (j - 1) = u1)
    (hu2 : orbitStepWeight j = 1) :
    2 ^ (u1 + e) * g + 2 ^ (u1 + 1) * δ * 5 ^ (j - 1) =
      5 + 2 ^ u1 + 25 * g := by
  have hji : j - 1 + 2 = j + 1 := by omega
  have hx' : fullOrbitIter (j - 1 + 2) = candidateX j e g δ := by
    rw [hji]
    exact hx
  have he1 : 1 ≤ e := by omega
  have hgen := orbitSegmentWord_candidate_equation j 2 e g δ hg hx'
  have hji' : j - 1 + 1 = j := by omega
  have hw : StringFlow.wordWeight (orbitSegmentWord j 2) = u1 + 1 := by
    rw [show orbitSegmentWord j 2 =
        orbitSegmentWord j 1 ++ [orbitStepWeight (j - 1 + 1)] by rfl]
    rw [hji']
    simp [orbitSegmentWord, StringFlow.wordWeight, hu1, hu2]
  have hA : StringFlow.Word.wordA (orbitSegmentWord j 2) = 5 + 2 ^ u1 := by
    rw [show orbitSegmentWord j 2 =
        orbitSegmentWord j 1 ++ [orbitStepWeight (j - 1 + 1)] by rfl]
    rw [hji']
    simp [orbitSegmentWord, StringFlow.Word.wordA, hu1, hu2]
  rw [hw, hA] at hgen
  have hcan : candidateX j e g δ = 2 ^ (e - 1) * g + δ * 5 ^ (j - 1) := rfl
  rw [hcan] at hgen
  have hpow : 2 ^ (u1 + 1) * 2 ^ (e - 1) = 2 ^ (u1 + e) := by
    have hsum : (u1 + 1) + (e - 1) = u1 + e := by omega
    rw [← Nat.pow_add, hsum]
  nlinarith [hgen, hpow]

/-- `d=1` exclusion from the actual orbit: the segment equation is
derived, then `d1_exclusion` applies. -/
theorem d1_exclusion_of_orbit
    (j e g δ a : Nat)
    (hj : 3 ≤ j)
    (hgpos : 0 < g)
    (hg : g < 5 ^ (j - 1) / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hiter : fullOrbitIter (j - 1) = g)
    (hx : fullOrbitIter j = candidateX j e g δ)
    (hstep : orbitStepWeight (j - 1) = 1 + 4 * a) :
    False := by
  have hseg := d1_segment_equation j e g δ a (by omega) hiter hx hstep
  exact d1_exclusion j e g δ a hj hgpos hg hδ he hseg

/-- `d=1` exclusion assembled from the reset-to-candidate bridge: the
reset terminal data plus the actual full-orbit weights satisfy every
input of `d1_exclusion_of_orbit`. -/
theorem d1_exclusion_of_reset_candidate
    (n0 k t δ e g a s0 x r : Nat)
    (hn0 : 4 ≤ n0)
    (hiter : fullOrbitIter n0 = r)
    (hiter_g : fullOrbitIter (n0 - 2) = g)
    (hstep_e : orbitStepWeight (n0 - 3) = e)
    (hstep_t : orbitStepWeight (n0 - 1) = t)
    (hstep_a : orbitStepWeight (n0 - 2) = 1 + 4 * a)
    (hres : ResetHeadEq s0 (n0 - 1) k t δ r)
    (hterm : 5 ^ k * s0 = 2 ^ (e - 1) * g + 1)
    (hr : r = candidateRj x t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0)
    (hgpos : 0 < g)
    (hg : g < 5 ^ (n0 - 2) / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e) :
    False := by
  have hbridge := candidate_parameterization_of_reset_full_orbit n0 k t δ e g s0 x r
    (by omega) hiter hiter_g hstep_e hstep_t hres hterm hr hdiv
  have hx : fullOrbitIter (n0 - 1) = candidateX (n0 - 1) e g δ := by
    rw [← hbridge.2.1, hbridge.1]
  exact d1_exclusion_of_orbit (n0 - 1) e g δ a (by omega) hgpos hg hδ he hiter_g hx hstep_a

/-- `d=2` exclusion from the actual orbit: derive the segment equation
and the survivor modulus, then `d2_exclusion` applies. -/
theorem d2_exclusion_of_orbit
    (j e g δ u1 : Nat)
    (hj : 3 ≤ j)
    (hgpos : 0 < g)
    (hg : g < 5 ^ (j - 1) / 2 ^ (e - 1))
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hu1 : u1 = 1 ∨ u1 = 2)
    (hiter : fullOrbitIter (j - 1) = g)
    (hx : fullOrbitIter (j + 1) = candidateX j e g δ)
    (hstep1 : orbitStepWeight (j - 1) = u1)
    (hstep2 : orbitStepWeight j = 1)
    (hxmod : candidateX j e g δ % 1280 = 743) :
    False := by
  have hseg := d2_segment_equation j e g δ u1 (by omega) he hiter hx hstep1 hstep2
  exact d2_exclusion j e g δ u1 hj hgpos hg hδ he hu1 hseg hxmod

/-- `d=2` exclusion assembled from the segment-length-`d` reset bridge:
`g` is two full-orbit steps before the reset predecessor `x`, and the
candidate depth is `n0-2`. -/
theorem d2_exclusion_of_reset_candidate
    (n0 k t δ e g u1 s0 x r : Nat)
    (hn0 : 6 ≤ n0)
    (hiter : fullOrbitIter n0 = r)
    (hiter_g : fullOrbitIter (n0 - 3) = g)
    (hstep_e : orbitStepWeight (n0 - 4) = e)
    (hstep_t : orbitStepWeight (n0 - 1) = t)
    (hstep1 : orbitStepWeight (n0 - 3) = u1)
    (hstep2 : orbitStepWeight (n0 - 2) = 1)
    (hres : ResetHeadEq s0 (n0 - 2) k t δ r)
    (hterm : 5 ^ k * s0 = 2 ^ (e - 1) * g + 1)
    (hr : r = candidateRj x t)
    (hdiv : (5 * x + 1) % 2 ^ t = 0)
    (hgpos : 0 < g)
    (hg : g < 5 ^ (n0 - 3) / 2 ^ (e - 1))
    (hδ : δ = 1 ∨ δ = 3)
    (he : 2 ≤ e)
    (hu1 : u1 = 1 ∨ u1 = 2)
    (hxmod : candidateX (n0 - 2) e g δ % 1280 = 743) :
    False := by
  have hbridge := candidate_parameterization_of_reset_full_orbit_d n0 2 k t δ e g s0 x r
    (by norm_num) (by omega) hiter hiter_g hstep_e hstep_t hres hterm hr hdiv
  have hx : fullOrbitIter (n0 - 1) = candidateX (n0 - 2) e g δ := by
    rw [← hbridge.2.1, hbridge.1]
  have hx' : fullOrbitIter (n0 - 2 + 1) = candidateX (n0 - 2) e g δ := by
    have hidx : n0 - 2 + 1 = n0 - 1 := by omega
    rw [hidx]
    exact hx
  exact d2_exclusion_of_orbit (n0 - 2) e g δ u1 (by omega) hgpos hg hδ he hu1
    hiter_g hx' hstep1 hstep2 hxmod

/-- `d=3` unique family exclusion, expressed directly on the actual
full-orbit segment `z→w`. -/
theorem d3_exclusion_of_orbit (j z w : Nat)
    (hjmod : j % 1728 = 924)
    (hz : fullOrbitIter (j + 4) = z)
    (h5z : 5 * z + 1 = 2 ^ 6 * w)
    (hwodd : w % 2 = 1)
    (hsmall : ∀ m : Nat, m < j + 4 → orbitStepWeight m ≤ 2) :
    False :=
  d3_family_big_weight_excluded j z w hjmod hz h5z hwodd hsmall

/-- `d≥4`, `e=2,a≥1` branch exclusion, expressed directly on the actual
full-orbit step `y→x`. -/
theorem dge4_e2_exclusion_of_orbit (n a y x : Nat)
    (ha : 1 ≤ a)
    (hy : fullOrbitIter n = y)
    (hxodd : x % 2 = 1)
    (hstep : 5 * y + 1 = 2 ^ (1 + 4 * a) * x)
    (hsmall : ∀ m : Nat, m < n → orbitStepWeight m ≤ 2) :
    False :=
  dge4_e2_a_ge1_excluded n a y x ha hy hxodd hstep hsmall

/-- An even block state cannot take a legal `t=1` or `t=2` step, because
`5*y+1` is then odd. -/
lemma no_legal_step_of_even (y : Nat) (hy : y % 2 = 0) :
    ∀ t : Nat, t = 1 ∨ t = 2 → (5 * y + 1) % 2 ^ t ≠ 0 := by
  intro t ht
  have hmod : (5 * y + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, hy]
  rcases ht with rfl | rfl
  · intro hzero
    have hzero2 : (5 * y + 1) % 2 = 0 := by simpa [Nat.pow_one] using hzero
    omega
  · intro hzero
    have hdiv4 : 2 ^ 2 ∣ 5 * y + 1 := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have hdiv2 : 2 ∣ 5 * y + 1 := dvd_trans (by norm_num : 2 ∣ 2 ^ 2) hdiv4
    have hzero2 : (5 * y + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv2
    omega

/-- The terminal block state is exactly `r_s`. -/
lemma blockState_eq_r_s_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    blockState weight q s = r_s := by
  dsimp [blockState]
  rw [← hPrem.A_s_mol, ← hPrem.Ws_def, hPrem.r_s_eq]

/-- Every interior block state before the tail is odd: an even state has no
legal successor, and the tail itself is `5 mod 8`. -/
lemma blockState_next_odd_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s k : Nat) (weight : Nat → Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hk : k < s) :
    (blockState weight q (k + 1)) % 2 = 1 := by
  by_contra hnot
  have heven : (blockState weight q (k + 1)) % 2 = 0 := by
    have hlt : (blockState weight q (k + 1)) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  by_cases hks : k + 1 < s
  · rcases hPrem.weight_step (k + 1) hks with ht1 | ht2
    · have hstep := blockState_step weight q (k + 1) 1 ht1
        (hPrem.valid_prefix (k + 1) (by omega))
        (hPrem.valid_prefix (k + 2) (by omega))
      exact no_legal_step_of_even (blockState weight q (k + 1)) heven 1 (Or.inl rfl) hstep.1
    · have hstep := blockState_step weight q (k + 1) 2 ht2
        (hPrem.valid_prefix (k + 1) (by omega))
        (hPrem.valid_prefix (k + 2) (by omega))
      exact no_legal_step_of_even (blockState weight q (k + 1)) heven 2 (Or.inr rfl) hstep.1
  · have hk1 : k + 1 = s := by omega
    have hrs : blockState weight q s = r_s :=
      blockState_eq_r_s_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem
    have heven' : r_s % 2 = 0 := by
      rw [← hrs, ← hk1]
      exact heven
    have hmod2 : r_s % 2 = (r_s % 8) % 2 := by
      exact (Nat.mod_mod_of_dvd r_s (c := 2) (b := 8) (by norm_num : 2 ∣ 8)).symm
    have hodd : r_s % 2 = 1 := by
      rw [hmod2, hPrem.r_s_mod8]
    omega

/-- All block states from the full-orbit block head to the tail are odd. -/
lemma blockState_odd_of_premises_fullOrbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (k : Nat) (hjk : j ≤ k) (hks : k ≤ s) :
    (blockState weight q k) % 2 = 1 := by
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hodd0 : r % 2 = 1 := by
    simpa [IsOdd] using FullOrbitFrom7_odd r hReach
  induction k with
  | zero =>
      have hjpos : 1 ≤ j := hPrem.j_pos
      exfalso
      omega
  | succ k ih =>
      by_cases hklt : k < j
      · have hkj : k + 1 = j := by omega
        have h' : blockState weight q (k + 1) = r := by
          rw [hkj]
          exact hbsj
        rw [h']
        exact hodd0
      · have hprev := ih (by omega) (by omega)
        exact blockState_next_odd_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s k
          weight hPrem (by omega)

/-- In a legal block, the block step weight is the exact full-orbit step
weight: `t = v2(5*x+1)`. -/
lemma blockState_step_exact_of_premises_fullOrbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s k : Nat) (weight : Nat → Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hk : k < s) :
    weight (k + 1) - weight k = twoValuation (5 * blockState weight q k + 1) := by
  rcases hPrem.weight_step k hk with ht1 | ht2
  · have hstep := blockState_step weight q k 1 ht1
      (hPrem.valid_prefix k (by omega))
      (hPrem.valid_prefix (k + 1) (by omega))
    have hodd : (blockState weight q (k + 1)) % 2 = 1 :=
      blockState_next_odd_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s k weight hPrem hk
    have hdvd : 2 ^ 1 ∣ 5 * blockState weight q k + 1 := Nat.dvd_iff_mod_eq_zero.mpr hstep.1
    have hmul : 2 ^ 1 * blockState weight q (k + 1) = 5 * blockState weight q k + 1 := by
      rw [← hstep.2]
      exact Nat.mul_div_cancel' hdvd
    have hv : twoValuation (5 * blockState weight q k + 1) = 1 := by
      have hv' := StringFlow.Lte.twoValuation_mul_two_pow_eq 1
        (blockState weight q (k + 1)) hodd
      rw [hmul] at hv'
      exact hv'
    rw [hv]
    omega
  · have hstep := blockState_step weight q k 2 ht2
      (hPrem.valid_prefix k (by omega))
      (hPrem.valid_prefix (k + 1) (by omega))
    have hodd : (blockState weight q (k + 1)) % 2 = 1 :=
      blockState_next_odd_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s k weight hPrem hk
    have hdvd : 2 ^ 2 ∣ 5 * blockState weight q k + 1 := Nat.dvd_iff_mod_eq_zero.mpr hstep.1
    have hmul : 2 ^ 2 * blockState weight q (k + 1) = 5 * blockState weight q k + 1 := by
      rw [← hstep.2]
      exact Nat.mul_div_cancel' hdvd
    have hv : twoValuation (5 * blockState weight q k + 1) = 2 := by
      have hv' := StringFlow.Lte.twoValuation_mul_two_pow_eq 2
        (blockState weight q (k + 1)) hodd
      rw [hmul] at hv'
      exact hv'
    rw [hv]
    omega

/-- Every block state after a legal step is `3` or `4` modulo `5`. -/
lemma blockState_next_mod5_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s k : Nat) (weight : Nat → Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hk : k < s) :
    (blockState weight q (k + 1)) % 5 = 3 ∨ (blockState weight q (k + 1)) % 5 = 4 := by
  rcases hPrem.weight_step k hk with ht1 | ht2
  · have hstep := blockState_step weight q k 1 ht1
      (hPrem.valid_prefix k (by omega))
      (hPrem.valid_prefix (k + 1) (by omega))
    have hmod := legal_step_next_mod5 (blockState weight q k) 1 (Or.inl rfl) hstep.1
    rw [hstep.2] at hmod
    exact hmod
  · have hstep := blockState_step weight q k 2 ht2
      (hPrem.valid_prefix k (by omega))
      (hPrem.valid_prefix (k + 1) (by omega))
    have hmod := legal_step_next_mod5 (blockState weight q k) 2 (Or.inr rfl) hstep.1
    rw [hstep.2] at hmod
    exact hmod

/-- Every block state from a full-orbit block head to the tail is `3` or
`4` modulo `5`: the head is a reset head, and each legal `t∈{1,2}` step
preserves membership in `{3,4}` modulo `5`. -/
lemma blockState_mod5_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (k : Nat) (hjk : j ≤ k) (hks : k ≤ s) :
    (blockState weight q k) % 5 = 3 ∨ (blockState weight q k) % 5 = 4 := by
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hhead : r % 5 = 3 ∨ r % 5 = 4 := by
    have hcong := UnifiedCoreAudit.block_head_mod_five_congruence_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s
      weight r hPrem hrj hReach
    rcases hPrem.tj_mem with ht1 | ht2
    · have ht : Wj - Wp = 1 := by omega
      have hc : r % 5 = 3 := by
        rw [ht] at hcong
        rw [Nat.ModEq] at hcong
        norm_num [StringFlow.Lte.invMod5] at hcong
        exact hcong
      exact Or.inl hc
    · have ht : Wj - Wp = 2 := by omega
      have hc : r % 5 = 4 := by
        rw [ht] at hcong
        rw [Nat.ModEq] at hcong
        norm_num [StringFlow.Lte.invMod5] at hcong
        exact hcong
      exact Or.inr hc
  induction k with
  | zero =>
      have hjpos : 1 ≤ j := hPrem.j_pos
      exfalso
      omega
  | succ k ih =>
      by_cases hklt : k < j
      · have hkj : k + 1 = j := by omega
        have h' : blockState weight q (k + 1) = r := by
          rw [hkj]
          exact hbsj
        rw [h']
        exact hhead
      · have hprev := ih (by omega) (by omega)
        exact blockState_next_mod5_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s k
          weight hPrem (by omega)

/-- Word-segment continuity: if the block head `r` is a full-orbit state at
depth `n0`, then every block prefix of length `n` equals the corresponding
full-orbit suffix word, and its endpoint is the full-orbit iterate. -/
theorem blockWord_eq_orbitSegment_of_fullOrbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s n0 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hiter : fullOrbitIter n0 = r)
    (n : Nat) (hn : n ≤ s - j) :
    blockWord weight j n = orbitSegmentWord (n0 + 1) n ∧
      blockState weight q (j + n) = fullOrbitIter (n0 + n) := by
  let hReach : FullOrbitFrom7 r := ⟨n0, hiter⟩
  induction n with
  | zero =>
      constructor
      · simp [blockWord, orbitSegmentWord]
      · have hbsj : blockState weight q j = r := by
          dsimp [blockState]
          rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
        simp [hbsj, hiter]
  | succ n ih =>
      have hnle : n ≤ s - j := by omega
      rcases ih hnle with ⟨hw, hbs⟩
      have hk : j + n < s := by omega
      have hexact := blockState_step_exact_of_premises_fullOrbit
        j Wp Wj q Aj A_s s W_s r_s L H_s (j + n) weight hPrem hk
      have hval : twoValuation (5 * blockState weight q (j + n) + 1) =
          weight (j + n + 1) - weight (j + n) := hexact.symm
      have hweight : orbitStepWeight (n0 + n) = weight (j + n + 1) - weight (j + n) := by
        unfold orbitStepWeight
        rw [← hbs]
        exact hval
      have hw' : blockWord weight j (n + 1) = orbitSegmentWord (n0 + 1) (n + 1) := by
        simp [blockWord, orbitSegmentWord, hw, hweight]
      have hnext : blockState weight q (j + (n + 1)) = fullOrbitIter (n0 + (n + 1)) := by
        have hk1 : j + n + 1 = j + (n + 1) := by omega
        have hk2 : n0 + n + 1 = n0 + (n + 1) := by omega
        rw [← hk1, ← hk2]
        have hbs' : blockState weight q ((j + n) + 1) = fullOrbitStep (blockState weight q (j + n)) := by
          rcases hPrem.weight_step (j + n) hk with ht1 | ht2
          · have hstep := blockState_step weight q (j + n) 1 ht1
              (hPrem.valid_prefix (j + n) (by omega))
              (hPrem.valid_prefix (j + n + 1) (by omega))
            have hv1 : twoValuation (5 * blockState weight q (j + n) + 1) = 1 := by
              have hex' : twoValuation (5 * blockState weight q (j + n) + 1) =
                  weight (j + n + 1) - weight (j + n) := hexact.symm
              rw [hex', ht1]
              norm_num
            unfold fullOrbitStep
            rw [hv1]
            exact hstep.2.symm
          · have hstep := blockState_step weight q (j + n) 2 ht2
              (hPrem.valid_prefix (j + n) (by omega))
              (hPrem.valid_prefix (j + n + 1) (by omega))
            have hv2 : twoValuation (5 * blockState weight q (j + n) + 1) = 2 := by
              have hex' : twoValuation (5 * blockState weight q (j + n) + 1) =
                  weight (j + n + 1) - weight (j + n) := hexact.symm
              rw [hex', ht2]
              norm_num
            unfold fullOrbitStep
            rw [hv2]
            exact hstep.2.symm
        rw [hbs']
        rw [hbs]
        rfl
      constructor
      · exact hw'
      · exact hnext

/-- The full block word is the corresponding full-orbit suffix, and the
block tail is its full-orbit endpoint. -/
theorem blockWord_full_suffix_of_fullOrbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s n0 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hiter : fullOrbitIter n0 = r) :
    blockWord weight j (s - j) = orbitSegmentWord (n0 + 1) (s - j) ∧
      r_s = fullOrbitIter (n0 + (s - j)) := by
  have h := blockWord_eq_orbitSegment_of_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s n0
    weight r hPrem hrj hiter (s - j) (by omega)
  constructor
  · exact h.1
  · have hk : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    have h2 : blockState weight q (j + (s - j)) = fullOrbitIter (n0 + (s - j)) := h.2
    have hrs : blockState weight q s = r_s :=
      blockState_eq_r_s_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem
    rw [hk] at h2
    rw [hrs] at h2
    exact h2

/-- A full-orbit block head makes the whole block word a full-orbit suffix:
the existential form of `FullOrbitFrom7 r`. -/
theorem blockWord_full_suffix_of_fullOrbit_reach
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r) :
    ∃ n0 : Nat, fullOrbitIter n0 = r ∧
      blockWord weight j (s - j) = orbitSegmentWord (n0 + 1) (s - j) ∧
        r_s = fullOrbitIter (n0 + (s - j)) := by
  rcases hReach with ⟨n0, hiter⟩
  have h := blockWord_full_suffix_of_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s n0
    weight r hPrem hrj hiter
  exact ⟨n0, hiter, h.1, h.2⟩

/-- Every block state between a full-orbit block head and the block tail is
itself a full-orbit state. -/
theorem blockState_fullOrbit_of_premises_fullOrbit
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (k : Nat) (hjk : j ≤ k) (hks : k ≤ s) :
    FullOrbitFrom7 (blockState weight q k) := by
  rcases hReach with ⟨n0, hiter⟩
  have h := blockWord_eq_orbitSegment_of_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s n0
    weight r hPrem hrj hiter (k - j) (by omega)
  have hk' : j + (k - j) = k := Nat.add_sub_of_le hjk
  have h2 : blockState weight q (j + (k - j)) = fullOrbitIter (n0 + (k - j)) := h.2
  rw [hk'] at h2
  exact ⟨n0 + (k - j), h2.symm⟩

/-- `m2>0`, even run length: the cleared tail congruence fixes
`u ≡ 3 (mod 8)`. -/
lemma tail_failure_m2_even_u_mod8
    (m1 m2 L _H_s u w : Nat)
    (hm2even : m2 % 2 = 0)
    (hupos : 0 < u)
    (hcong : 3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w) :
    u % 8 = 3 := by
  have hA : 1 ≤ 3 * 5 ^ m2 * u := by
    have h5 : 0 < 5 ^ m2 := by positivity
    have h3u : 0 < 3 * u := by positivity
    nlinarith
  have hcong' : 3 * 5 ^ m2 * u = 2 ^ ((L + m1) + 3) * w + 1 := by omega
  have hdvd8 : 8 ∣ 2 ^ ((L + m1) + 3) := by
    have hk : 3 ≤ (L + m1) + 3 := by omega
    have h := pow_dvd_pow 2 hk
    simpa using h
  have hdvd8w : 8 ∣ 2 ^ ((L + m1) + 3) * w := dvd_mul_of_dvd_left hdvd8 w
  have hmodpow : (2 ^ ((L + m1) + 3) * w) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd8w
  have hmod3u : (3 * 5 ^ m2 * u) % 8 = 1 := by
    rw [hcong']
    rw [Nat.add_mod, hmodpow]
  have hm2e : m2 = 2 * (m2 / 2) := by
    have h := Nat.div_add_mod m2 2
    rw [hm2even] at h
    omega
  have h25 : (25 : Nat) % 8 = 1 := by norm_num
  have hpow25 : (25 ^ (m2 / 2)) % 8 = 1 := by
    induction m2 / 2 with
    | zero => norm_num
    | succ n ih =>
        rw [Nat.pow_succ, Nat.mul_mod, ih, h25]
  have hpow5 : (5 ^ m2) % 8 = 1 := by
    rw [hm2e]
    rw [Nat.pow_mul]
    exact hpow25
  have h3u1 : (3 * u) % 8 = 1 := by
    have h35 : (3 * 5 ^ m2) % 8 = 3 := by
      rw [Nat.mul_mod, hpow5]
    have hmod : (3 * 5 ^ m2 * u) % 8 = (3 * u) % 8 := by
      rw [show 3 * 5 ^ m2 * u = (3 * 5 ^ m2) * u by ring]
      rw [Nat.mul_mod, h35]
      rw [Nat.mul_mod]
      norm_num
    rw [← hmod]
    exact hmod3u
  have hmod3 : (3 * (u % 8)) % 8 = 1 := by
    have hmm : (3 * u) % 8 = (3 * (u % 8)) % 8 := by
      rw [Nat.mul_mod]
    rw [hmm] at h3u1
    exact h3u1
  have hlt8 : u % 8 < 8 := Nat.mod_lt u (by norm_num)
  interval_cases u % 8
  all_goals norm_num at hmod3
  all_goals norm_num

/-- `m2>0`, odd run length: the cleared tail congruence fixes
`u ≡ 7 (mod 8)`. -/
lemma tail_failure_m2_odd_u_mod8
    (m1 m2 L _H_s u w : Nat)
    (hm2odd : m2 % 2 = 1)
    (hupos : 0 < u)
    (hcong : 3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w) :
    u % 8 = 7 := by
  have hA : 1 ≤ 3 * 5 ^ m2 * u := by
    have h5 : 0 < 5 ^ m2 := by positivity
    have h3u : 0 < 3 * u := by positivity
    nlinarith
  have hcong' : 3 * 5 ^ m2 * u = 2 ^ ((L + m1) + 3) * w + 1 := by omega
  have hdvd8 : 8 ∣ 2 ^ ((L + m1) + 3) := by
    have hk : 3 ≤ (L + m1) + 3 := by omega
    have h := pow_dvd_pow 2 hk
    simpa using h
  have hdvd8w : 8 ∣ 2 ^ ((L + m1) + 3) * w := dvd_mul_of_dvd_left hdvd8 w
  have hmodpow : (2 ^ ((L + m1) + 3) * w) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd8w
  have hmod3u : (3 * 5 ^ m2 * u) % 8 = 1 := by
    rw [hcong']
    rw [Nat.add_mod, hmodpow]
  have hm2o : m2 = 2 * (m2 / 2) + 1 := by
    have h := Nat.div_add_mod m2 2
    rw [hm2odd] at h
    omega
  have h25 : (25 : Nat) % 8 = 1 := by norm_num
  have hpow25 : (25 ^ (m2 / 2)) % 8 = 1 := by
    induction m2 / 2 with
    | zero => norm_num
    | succ n ih =>
        rw [Nat.pow_succ, Nat.mul_mod, ih, h25]
  have hpow5 : (5 ^ m2) % 8 = 5 := by
    rw [hm2o]
    rw [Nat.pow_add, Nat.pow_one]
    rw [Nat.pow_mul]
    norm_num
    rw [Nat.mul_mod]
    rw [hpow25]
  have h7u1 : (7 * u) % 8 = 1 := by
    have h35 : (3 * 5 ^ m2) % 8 = 7 := by
      rw [Nat.mul_mod, hpow5]
    have hmod : (3 * 5 ^ m2 * u) % 8 = (7 * u) % 8 := by
      rw [show 3 * 5 ^ m2 * u = (3 * 5 ^ m2) * u by ring]
      rw [Nat.mul_mod, h35]
      rw [Nat.mul_mod]
      norm_num
    rw [← hmod]
    exact hmod3u
  have hmod7 : (7 * (u % 8)) % 8 = 1 := by
    have hmm : (7 * u) % 8 = (7 * (u % 8)) % 8 := by
      rw [Nat.mul_mod]
    rw [hmm] at h7u1
    exact h7u1
  have hlt8 : u % 8 < 8 := Nat.mod_lt u (by norm_num)
  interval_cases u % 8
  all_goals norm_num at hmod7
  all_goals norm_num

/-- Complete `m2>0` audit: the trailing `t=2` run start `r_a` is a
full-orbit state, `r_a+1 = 2^(2*m2+1)*u`, the tail congruence fixes
`u` modulo `8` by the parity of `m2`, and the cleared odd part `w`
satisfies the same high 2-adic window as in the `m2=0` case. -/
lemma tail_failure_m2_pos_audit
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (hn : n = s - j)
    (hm : (m1, m2) = UnifiedCoreAudit.tailSplit (blockWord weight j n))
    (hm2 : 1 ≤ m2)
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * UnifiedCoreAudit.wTerminal L r_s + 1) :
    ∃ r2 u w n0 : Nat,
      r2 + 1 = 2 ^ (2 * m2 + 1) * u ∧
      fullOrbitIter n0 = r2 ∧
      r2 = blockState weight q (j + (n - m1 - m2)) ∧
      ((m2 % 2 = 0 ∧ u % 8 = 3) ∨ (m2 % 2 = 1 ∧ u % 8 = 7)) ∧
      3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w ∧
      w % 2 = 1 ∧
      2 ^ (H_s - 1) ∣ 5 ^ ((L + m1) + 3) * w + 1 := by
  rcases UnifiedCoreAudit.tail_failure_odd_part_congruence j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2
    weight hPrem hn hm hH hfail with
    ⟨_r2f, u, w, _ht2, hstart, hstart_block, _hL2, hcong, hwodd, hdiv⟩
  let a := j + (n - m1 - m2)
  have hja : j ≤ a := by dsimp [a]; omega
  have has : a ≤ s := by
    dsimp [a]
    have hsum := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum
    rw [hlen] at hsum
    have hn' : n = s - j := hn
    omega
  have hreach_r2 : FullOrbitFrom7 (blockState weight q a) :=
    blockState_fullOrbit_of_premises_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach a hja has
  rcases hreach_r2 with ⟨n0, hiter⟩
  have hstart' : blockState weight q a + 1 = 2 ^ (2 * m2 + 1) * u := by
    rw [← hstart_block]
    exact hstart
  have hupos : 0 < u := by
    by_contra hu
    have hu' : u = 0 := by omega
    rw [hu'] at hstart'
    have hpos : 0 < blockState weight q a + 1 := by positivity
    omega
  have hres : (m2 % 2 = 0 ∧ u % 8 = 3) ∨ (m2 % 2 = 1 ∧ u % 8 = 7) := by
    by_cases hpar : m2 % 2 = 0
    · left
      exact ⟨hpar, tail_failure_m2_even_u_mod8 m1 m2 L H_s u w hpar hupos hcong⟩
    · right
      have hpar1 : m2 % 2 = 1 := by omega
      exact ⟨hpar1, tail_failure_m2_odd_u_mod8 m1 m2 L H_s u w hpar1 hupos hcong⟩
  exact ⟨blockState weight q a, u, w, n0, hstart', hiter, rfl, hres, hcong, hwodd, hdiv⟩

/-- Full `m2>0` audit with the modulo-5 word rigidity: the run start
`r_a` is also `3` or `4` modulo `5`. -/
lemma tail_failure_m2_pos_audit_mod5
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (hn : n = s - j)
    (hm : (m1, m2) = UnifiedCoreAudit.tailSplit (blockWord weight j n))
    (hm2 : 1 ≤ m2)
    (hH : 2 ≤ H_s)
    (hfail : 2 ^ (H_s - 1) ∣ 5 ^ (L + 3) * UnifiedCoreAudit.wTerminal L r_s + 1) :
    ∃ r2 u w n0 : Nat,
      r2 + 1 = 2 ^ (2 * m2 + 1) * u ∧
      fullOrbitIter n0 = r2 ∧
      (r2 % 5 = 3 ∨ r2 % 5 = 4) ∧
      ((m2 % 2 = 0 ∧ u % 8 = 3) ∨ (m2 % 2 = 1 ∧ u % 8 = 7)) ∧
      3 * 5 ^ m2 * u - 1 = 2 ^ ((L + m1) + 3) * w ∧
      w % 2 = 1 ∧
      2 ^ (H_s - 1) ∣ 5 ^ ((L + m1) + 3) * w + 1 := by
  rcases tail_failure_m2_pos_audit j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 weight r
    hPrem hrj hReach hn hm hm2 hH hfail with
    ⟨r2, u, w, n0, hstart, hiter, hr2, hres, hcong, hwodd, hdiv⟩
  let a := j + (n - m1 - m2)
  have hja : j ≤ a := by dsimp [a]; omega
  have has : a ≤ s := by
    dsimp [a]
    have hsum := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum
    rw [hlen] at hsum
    have hn' : n = s - j := hn
    omega
  have hmod5 : (blockState weight q a) % 5 = 3 ∨ (blockState weight q a) % 5 = 4 :=
    blockState_mod5_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach a hja has
  have hmod5' : r2 % 5 = 3 ∨ r2 % 5 = 4 := by
    rw [hr2]
    exact hmod5
  exact ⟨r2, u, w, n0, hstart, hiter, hmod5', hres, hcong, hwodd, hdiv⟩

/-- In the `m2>0` tail, the first `t=2` step is an exact full-orbit step:
the run start `r_a` has full-orbit depth `n_a` with `orbitStepWeight n_a = 2`. -/
lemma m2_pos_first_step_weight_two
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : FullOrbitFrom7 r)
    (hn : n = s - j)
    (hm : (m1, m2) = UnifiedCoreAudit.tailSplit (blockWord weight j n))
    (hm2 : 1 ≤ m2) :
    ∃ n_a : Nat,
      fullOrbitIter n_a = blockState weight q (j + (n - m1 - m2)) ∧
      orbitStepWeight n_a = 2 := by
  let a := j + (n - m1 - m2)
  have hja : j ≤ a := by dsimp [a]; omega
  have has : a ≤ s := by
    dsimp [a]
    have hsum := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum
    rw [hlen] at hsum
    have hn' : n = s - j := hn
    omega
  have haslt : a < s := by
    dsimp [a]
    have hsum := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum
    rw [hlen] at hsum
    have hn' : n = s - j := hn
    omega
  have hreach_a : FullOrbitFrom7 (blockState weight q a) :=
    blockState_fullOrbit_of_premises_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach a hja has
  rcases hreach_a with ⟨n_a, hiter⟩
  have hstep := blockState_step_exact_of_premises_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s a
    weight hPrem haslt
  have hwstep : ∀ k < n, weight (j + k + 1) = weight (j + k) + 1 ∨
      weight (j + k + 1) = weight (j + k) + 2 := by
    intro k hk
    have hk' : j + k < s := by
      have hn' : n = s - j := hn
      omega
    exact hPrem.weight_step (j + k) hk'
  have htwos := UnifiedCoreAudit.blockWord_tailSplit_twos_weight weight j n m1 m2 hwstep hm
  have htwo := htwos 0 (by omega)
  have hw : weight (a + 1) - weight a = 2 := by
    have htwo' : weight (a + 1) = weight a + 2 := by
      simpa [a, Nat.add_assoc] using htwo
    omega
  have hval : twoValuation (5 * blockState weight q a + 1) = 2 := by
    rw [← hstep, hw]
  have hw2 : orbitStepWeight n_a = 2 := by
    unfold orbitStepWeight
    rw [hiter]
    exact hval
  exact ⟨n_a, hiter, hw2⟩

/-- In the `n≥16` branch, the `m2>0` run start is pushed to full-orbit
depth at least `18`: the exact suffix gives `n_a = n0+(a-j) ≥ 16`, and the
finite base excludes exact `t=2` steps at depths 16 and 17. -/
lemma m2_pos_tail_start_ge_18
    (j Wp Wj q Aj A_s s W_s r_s L H_s n m1 m2 n0 : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : UnifiedCoreAudit.All36_20PremisesNoHge j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hiter0 : fullOrbitIter n0 = r)
    (hhead : 16 ≤ n0)
    (hn : n = s - j)
    (hm : (m1, m2) = UnifiedCoreAudit.tailSplit (blockWord weight j n))
    (hm2 : 1 ≤ m2) :
    ∃ n_a : Nat, fullOrbitIter n_a = blockState weight q (j + (n - m1 - m2)) ∧ 18 ≤ n_a := by
  let a := j + (n - m1 - m2)
  let n_a := n0 + (a - j)
  have hja : j ≤ a := by dsimp [a]; omega
  have hsum : j + (a - j) = a := Nat.add_sub_of_le hja
  rcases blockWord_eq_orbitSegment_of_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s n0
    weight r hPrem hrj hiter0 (a - j) (by omega) with ⟨_hw, hcont2⟩
  have hbs : blockState weight q a = fullOrbitIter n_a := by
    dsimp [n_a]
    rw [hsum] at hcont2
    exact hcont2
  have has : a ≤ s := by
    dsimp [a]
    have hsum' := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum'
    rw [hlen] at hsum'
    have hn' : n = s - j := hn
    omega
  have haslt : a < s := by
    dsimp [a]
    have hsum' := UnifiedCoreAudit.tailSplit_sum_le_length (blockWord weight j n)
    have hlen : (blockWord weight j n).length = n := blockWord_length weight j n
    rw [← hm] at hsum'
    rw [hlen] at hsum'
    have hn' : n = s - j := hn
    omega
  have hstep := blockState_step_exact_of_premises_fullOrbit j Wp Wj q Aj A_s s W_s r_s L H_s a
    weight hPrem haslt
  have hwstep : ∀ k < n, weight (j + k + 1) = weight (j + k) + 1 ∨
      weight (j + k + 1) = weight (j + k) + 2 := by
    intro k hk
    have hk' : j + k < s := by
      have hn' : n = s - j := hn
      omega
    exact hPrem.weight_step (j + k) hk'
  have htwos := UnifiedCoreAudit.blockWord_tailSplit_twos_weight weight j n m1 m2 hwstep hm
  have htwo := htwos 0 (by omega)
  have hw : weight (a + 1) - weight a = 2 := by
    have htwo' : weight (a + 1) = weight a + 2 := by
      simpa [a, Nat.add_assoc] using htwo
    omega
  have hval : twoValuation (5 * blockState weight q a + 1) = 2 := by
    rw [← hstep, hw]
  have hweight : orbitStepWeight n_a = 2 := by
    unfold orbitStepWeight
    rw [← hbs]
    exact hval
  have hne := no_t2_step_at_depth_16_17 n_a hweight
  have hge : 18 ≤ n_a := by
    have h16 : 16 ≤ n_a := by
      dsimp [n_a]
      omega
    omega
  exact ⟨n_a, hbs.symm, hge⟩

end S6Audit
