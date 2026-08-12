import DigitBalance

set_option linter.unnecessarySimpa false

/-!
# One-dimensional 2-regular ranks for Collatz

Theorem 2.25 in the notes (3x+1 part): no function of the form
`r(n) = A^(zeros) B^(ones)` with positive `A, B` can be a strictly
descending rank along the Collatz map.  The proof uses the exact
digit-profile family
`n_j = 3*2^(j+2)+1`, `V_j = 9*2^j+1`, whose binary profiles coincide.
-/

namespace StringFlow

/-- Rank function `r(n) = A^(number of zero bits) * B^(number of one bits)`. -/
def profileRank (A B : Nat) (n : Nat) : Nat :=
  A ^ binaryZeros n * B ^ binaryWeight n

/-- Collatz map `T(n) = n/2` for even `n`, `3n+1` for odd `n`. -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- First member of the exact profile family: `n_j = 3*2^(j+2)+1`. -/
def collatzProfileN (j : Nat) : Nat := 3 * 2 ^ (j + 2) + 1

/-- Second member of the exact profile family: `V_j = 9*2^j+1`. -/
def collatzProfileV (j : Nat) : Nat := 9 * 2 ^ j + 1

theorem binaryWeight_one : binaryWeight 1 = 1 := by
  simpa using binaryWeight_two_pow 0

theorem binaryWeight_three : binaryWeight 3 = 2 := by
  rw [show 3 = 2 * 1 + 1 by omega]
  rw [binaryWeight_two_mul_add_one]
  rw [binaryWeight_one]

theorem binaryWeight_nine : binaryWeight 9 = 2 := by
  rw [show 9 = 2 * 4 + 1 by omega]
  rw [binaryWeight_two_mul_add_one]
  rw [show binaryWeight 4 = 1 by simpa using binaryWeight_two_pow 2]

theorem mul_assoc_swap (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b, Nat.mul_assoc]

theorem one_lt_two_pow_succ (k : Nat) : 1 < 2 ^ (k + 1) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  have hge : 2 <= 2 * 2 ^ k := by
    simpa using (Nat.mul_le_mul_left 2 (Nat.one_le_pow k 2 (by omega)))
  omega

theorem one_lt_two_pow_of_pos (j : Nat) (hj : 1 <= j) : 1 < 2 ^ j := by
  have h : j = (j - 1) + 1 := by omega
  rw [h]
  exact one_lt_two_pow_succ (j - 1)

theorem binaryWeight_collatzProfileN (j : Nat) :
    binaryWeight (collatzProfileN j) = 3 := by
  unfold collatzProfileN
  have hq : 1 < 2 ^ (j + 2) := one_lt_two_pow_succ (j + 1)
  rw [binaryWeight_add_mul_two_pow 3 1 (j + 2) hq]
  rw [binaryWeight_three, binaryWeight_one]

theorem binaryWeight_collatzProfileV (j : Nat) (hj : 1 <= j) :
    binaryWeight (collatzProfileV j) = 3 := by
  unfold collatzProfileV
  have hq : 1 < 2 ^ j := one_lt_two_pow_of_pos j hj
  rw [binaryWeight_add_mul_two_pow 9 1 j hq]
  rw [binaryWeight_nine, binaryWeight_one]

theorem binaryLength_three : binaryLength 3 = 2 := by
  rw [show 3 = 2 * 1 + 1 by omega]
  rw [binaryLength_two_mul_add_one]
  rw [show binaryLength 1 = 1 by simpa using binaryLength_two_pow 0]

theorem binaryLength_nine : binaryLength 9 = 4 := by
  rw [show 9 = 2 * 4 + 1 by omega]
  rw [binaryLength_two_mul_add_one]
  rw [show binaryLength 4 = 3 by simpa using binaryLength_two_pow 2]

theorem binaryLength_three_pow (M : Nat) : binaryLength (3 * 2 ^ M) = M + 2 := by
  induction M with
  | zero =>
      rw [show 3 * 1 = 3 by omega]
      rw [binaryLength_three]
  | succ M ih =>
      have hpow : 3 * 2 ^ (M + 1) = 2 * (3 * 2 ^ M) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ M) 2]
        rw [mul_assoc_swap 3 2 (2 ^ M)]
      rw [hpow]
      have hn : 0 < 3 * 2 ^ M := by
        exact Nat.mul_pos (by omega) (Nat.pow_pos (show 0 < 2 by omega))
      rw [binaryLength_two_mul (3 * 2 ^ M) hn]
      rw [ih]

theorem binaryLength_nine_pow (M : Nat) : binaryLength (9 * 2 ^ M) = M + 4 := by
  induction M with
  | zero =>
      rw [show 9 * 1 = 9 by omega]
      rw [binaryLength_nine]
  | succ M ih =>
      have hpow : 9 * 2 ^ (M + 1) = 2 * (9 * 2 ^ M) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_comm (2 ^ M) 2]
        rw [mul_assoc_swap 9 2 (2 ^ M)]
      rw [hpow]
      have hn : 0 < 9 * 2 ^ M := by
        exact Nat.mul_pos (by omega) (Nat.pow_pos (show 0 < 2 by omega))
      rw [binaryLength_two_mul (9 * 2 ^ M) hn]
      rw [ih]

theorem binaryLength_collatzProfileN (j : Nat) :
    binaryLength (collatzProfileN j) = j + 4 := by
  unfold collatzProfileN
  have hstep : 3 * 2 ^ (j + 2) + 1 = 2 * (3 * 2 ^ (j + 1)) + 1 := by
    have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    rw [mul_assoc_swap 3 2 (2 ^ (j + 1))]
  rw [hstep, binaryLength_two_mul_add_one]
  rw [binaryLength_three_pow (j + 1)]

theorem binaryLength_collatzProfileV (j : Nat) (hj : 1 <= j) :
    binaryLength (collatzProfileV j) = j + 4 := by
  unfold collatzProfileV
  have hstep : 9 * 2 ^ j + 1 = 2 * (9 * 2 ^ (j - 1)) + 1 := by
    have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
      calc
        2 ^ j = 2 ^ ((j - 1) + 1) := by
          congr 1
          omega
        _ = 2 * 2 ^ (j - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    rw [mul_assoc_swap 9 2 (2 ^ (j - 1))]
  rw [hstep, binaryLength_two_mul_add_one]
  rw [binaryLength_nine_pow (j - 1)]
  omega

theorem binaryZeros_collatzProfileN (j : Nat) :
    binaryZeros (collatzProfileN j) = j + 1 := by
  unfold binaryZeros
  rw [binaryLength_collatzProfileN, binaryWeight_collatzProfileN]
  omega

theorem binaryZeros_collatzProfileV (j : Nat) (hj : 1 <= j) :
    binaryZeros (collatzProfileV j) = j + 1 := by
  unfold binaryZeros
  rw [binaryLength_collatzProfileV j hj, binaryWeight_collatzProfileV j hj]
  omega

/-- Shifting by two bits multiplies the rank by `A^2`. -/
theorem profileRank_four_mul (A B n : Nat) (hn : 0 < n) :
    profileRank A B (4 * n) = A ^ 2 * profileRank A B n := by
  unfold profileRank
  rw [binaryZeros_four_mul n hn, binaryWeight_four_mul]
  rw [show binaryZeros n + 2 = 2 + binaryZeros n by omega]
  rw [Nat.pow_add]
  rw [Nat.mul_assoc]

/-- The exact family has identical binary profiles on both sides. -/
theorem profileRank_collatzProfileN_eq_V (A B j : Nat) (hj : 1 <= j) :
    profileRank A B (collatzProfileN j) = profileRank A B (collatzProfileV j) := by
  unfold profileRank
  rw [binaryZeros_collatzProfileN, binaryZeros_collatzProfileV j hj]
  rw [binaryWeight_collatzProfileN, binaryWeight_collatzProfileV j hj]

/-- `T(n_j) = 4 V_j` for the exact profile family. -/
theorem collatzStep_collatzProfileN (j : Nat) :
    collatzStep (collatzProfileN j) = 4 * collatzProfileV j := by
  unfold collatzStep collatzProfileN collatzProfileV
  have hodd : (3 * 2 ^ (j + 2) + 1) % 2 = 1 := by
    have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have hrew : 3 * (2 * 2 ^ (j + 1)) = 2 * (3 * 2 ^ (j + 1)) := by
      rw [mul_assoc_swap 3 2 (2 ^ (j + 1))]
    rw [hrew]
    omega
  have hodd0 : ¬ (3 * 2 ^ (j + 2) + 1) % 2 = 0 := by omega
  rw [if_neg hodd0]
  have hpow4 : 2 ^ (j + 2) = 4 * 2 ^ j := by
    rw [Nat.pow_succ]
    rw [Nat.pow_succ]
    rw [Nat.mul_assoc]
    rw [show 2 * 2 = 4 by omega]
    rw [Nat.mul_comm]
  have hmain : 3 * (3 * 2 ^ (j + 2) + 1) + 1 = 4 * (9 * 2 ^ j + 1) := by
    rw [hpow4]
    omega
  exact hmain

/-- Ranks of the exact family are positive. -/
theorem profileRank_pos (A B n : Nat) (hA : 0 < A) (hB : 0 < B) :
    0 < profileRank A B n := by
  unfold profileRank
  exact Nat.mul_pos (Nat.pow_pos hA) (Nat.pow_pos hB)

/-- Theorem 2.25, 3x+1 case: no `A^z B^o` rank can descend along Collatz. -/
theorem collatz_no_descent_profile_rank :
    ¬ ∃ A B : Nat, 0 < A ∧ 0 < B ∧
      ∀ n : Nat, profileRank A B (collatzStep n) < profileRank A B n := by
  intro h
  rcases h with ⟨A, B, hA0, hB, hdesc⟩
  have hA : 1 < A := by
    have h2 := hdesc 2
    have hstep : collatzStep 2 = 1 := by
      unfold collatzStep
      rw [if_pos (by omega)]
    rw [hstep] at h2
    unfold profileRank at h2
    have hz1 : binaryZeros 1 = 0 := by
      unfold binaryZeros
      rw [show binaryLength 1 = 1 by simpa using binaryLength_two_pow 0]
      rw [show binaryWeight 1 = 1 by simpa using binaryWeight_two_pow 0]
    have hz2 : binaryZeros 2 = 1 := by
      unfold binaryZeros
      rw [show binaryLength 2 = 2 by simpa using binaryLength_two_pow 1]
      rw [show binaryWeight 2 = 1 by simpa using binaryWeight_two_pow 1]
    have ho1 : binaryWeight 1 = 1 := by simpa using binaryWeight_two_pow 0
    have ho2 : binaryWeight 2 = 1 := by simpa using binaryWeight_two_pow 1
    rw [hz1, ho1, hz2, ho2] at h2
    have hBlt : 1 * B < A * B := by
      simpa [Nat.pow_zero, Nat.pow_one, Nat.mul_one, Nat.one_mul] using h2
    have hApos : 0 < A := by
      have h01 : A = 0 ∨ 0 < A := Nat.eq_zero_or_pos A
      rcases h01 with hA0 | hApos
      · subst hA0
        omega
      · exact hApos
    have hAne1 : A ≠ 1 := by
      intro hA1
      subst hA1
      omega
    exact Nat.lt_of_le_of_ne (by omega) hAne1.symm
  let j : Nat := 1
  have hj : 1 <= j := by omega
  let n := collatzProfileN j
  let v := collatzProfileV j
  have hT : collatzStep n = 4 * v := by
    dsimp [n, v]
    exact collatzStep_collatzProfileN j
  have hrankV : profileRank A B v = profileRank A B n := by
    dsimp [n, v]
    exact (profileRank_collatzProfileN_eq_V A B j hj).symm
  have hv : 0 < v := by
    dsimp [v, collatzProfileV]
    have h2pos : 0 < 2 ^ 1 := Nat.pow_pos (show 0 < 2 by omega)
    have hmul : 0 < 9 * 2 ^ 1 := Nat.mul_pos (by omega) h2pos
    omega
  have hTrank : profileRank A B (collatzStep n) = A ^ 2 * profileRank A B n := by
    rw [hT]
    rw [profileRank_four_mul A B v hv]
    rw [hrankV]
  have hdesc2 := hdesc n
  rw [hTrank] at hdesc2
  have hp : 0 < profileRank A B n := profileRank_pos A B n (by omega) hB
  have hA1 : 1 <= A := by omega
  have hA2 : 2 <= A := by omega
  have hp_lt_Ap : profileRank A B n < A * profileRank A B n := by
    have h2p : profileRank A B n < 2 * profileRank A B n := by omega
    have h2leA : 2 * profileRank A B n <= A * profileRank A B n :=
      Nat.mul_le_mul_right (profileRank A B n) (by omega)
    exact Nat.lt_of_lt_of_le h2p h2leA
  have hAp_le : A * profileRank A B n <= A ^ 2 * profileRank A B n := by
    have h' : 1 * (A * profileRank A B n) <= A * (A * profileRank A B n) :=
      Nat.mul_le_mul_right (A * profileRank A B n) hA1
    have h'' : A * profileRank A B n <= A * (A * profileRank A B n) := by
      simpa [Nat.one_mul] using h'
    have hsq : A * (A * profileRank A B n) = A ^ 2 * profileRank A B n := by
      rw [Nat.pow_two]
      rw [Nat.mul_assoc]
    calc
      A * profileRank A B n <= A * (A * profileRank A B n) := h''
      _ = A ^ 2 * profileRank A B n := hsq
  have hchain : profileRank A B n < A ^ 2 * profileRank A B n :=
    Nat.lt_of_lt_of_le hp_lt_Ap hAp_le
  exact Nat.lt_asymm hchain hdesc2

end StringFlow
