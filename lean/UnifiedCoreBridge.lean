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

/-- 36.30.23.5, `d≥4`, `e=3, j=17`, `t_j=1`, `未=1`: the candidate
`x` fails the required residue modulo `640`. -/
theorem dge4_e3_j17_t1_excluded (x : Nat)
    (hx : x = 4 * 34177 + 5 ^ 16)
    (hmod : x % 640 = 13) : False :=
  e3_j17_t1_excluded x hx hmod

/-- 36.30.23.5, `d≥4`, `e=3, j=17`, `t_j=2`, `未=3`: the candidate
`x` fails the required residue modulo `1280`. -/
theorem dge4_e3_j17_t2_delta3_excluded (x : Nat)
    (hx : x = 4 * 34177 + 3 * 5 ^ 16)
    (hmod : x % 1280 = 743) : False :=
  e3_j17_t2_delta3_excluded x hx hmod

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

end S6Audit
