import DigitBalance

/-!
# The `a = 2^m + 1` family of the digit-balance lemma

Lemma 2.28 special case: for `a = 2^m + 1` and `b = 1`, the witness
`d = 2^(2m) - a`, `e = 2^(2m-1) - 1` satisfies
`a*d+1 = 2^(m+1)*e` and `s2(e) = s2(d)`.
-/

namespace StringFlow

/-- `(a+1)^2 = a^2 + 2a + 1` in `Nat`. -/
private theorem square_add_one (a : Nat) :
    (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  rw [Nat.add_mul, Nat.mul_add]
  omega

/-- `2^(m*2) = (2^m)^2`. -/
private theorem two_pow_mul_two (m : Nat) : 2 ^ (m * 2) = (2 ^ m) ^ 2 := by
  rw [Nat.pow_mul]

/-- For `0 < m`, `2^(2m) = 2 * 2^(2m-1)`. -/
private theorem two_pow_two_mul_eq_double (m : Nat) (hm : 0 < m) :
    2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
  have h : 2 * m = (2 * m - 1) + 1 := by omega
  calc
    2 ^ (2 * m) = 2 ^ ((2 * m - 1) + 1) := by
      congr 1
    _ = 2 * 2 ^ (2 * m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- For `0 < m`, `2^m = 2 * 2^(m-1)`. -/
private theorem two_pow_eq_double_pred (m : Nat) (hm : 0 < m) :
    2 ^ m = 2 * 2 ^ (m - 1) := by
  have h : m = (m - 1) + 1 := by omega
  calc
    2 ^ m = 2 ^ ((m - 1) + 1) := by
      congr 1
    _ = 2 * 2 ^ (m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- `2^(2m-1) = 2^(m-1) * 2^m` for `0 < m`. -/
private theorem two_pow_pred_two_mul (m : Nat) (hm : 0 < m) :
    2 ^ (2 * m - 1) = 2 ^ (m - 1) * 2 ^ m := by
  have h : 2 * m - 1 = (m - 1) + m := by omega
  rw [h, Nat.pow_add]

/-- `2^(2m-1) = 2 * 2^(2m-2)` for `0 < m`. -/
private theorem two_pow_pred_two_mul_double (m : Nat) (hm : 0 < m) :
    2 ^ (2 * m - 1) = 2 * 2 ^ (2 * m - 2) := by
  have h : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  calc
    2 ^ (2 * m - 1) = 2 ^ ((2 * m - 2) + 1) := by rw [h]
    _ = 2 * 2 ^ (2 * m - 2) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- `d = 2^(2m) - (2^m+1)` is odd. -/
private theorem odd_two_pow_add_one_d (m : Nat) (hm : 0 < m) :
    IsOdd (2 ^ (2 * m) - (2 ^ m + 1)) := by
  unfold IsOdd
  have hA : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := two_pow_two_mul_eq_double m hm
  have hB : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_eq_double_pred m hm
  have hle : 2 ^ (m - 1) + 1 <= 2 ^ (2 * m - 1) := by
    have hp : 2 ^ (2 * m - 1) = 2 ^ (m - 1) * 2 ^ m := two_pow_pred_two_mul m hm
    rw [hp]
    have hge2 : 2 <= 2 ^ m := by
      have hp' : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_eq_double_pred m hm
      rw [hp']
      have h1 : 1 <= 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
      omega
    have h1 : 1 <= 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
    have hA : 2 ^ (m - 1) + 1 <= 2 * 2 ^ (m - 1) := by omega
    have hA' : 2 ^ (m - 1) + 1 <= 2 ^ (m - 1) * 2 := by
      simpa [Nat.mul_comm] using hA
    have hB : 2 ^ (m - 1) * 2 <= 2 ^ (m - 1) * 2 ^ m :=
      Nat.mul_le_mul_left (2 ^ (m - 1)) hge2
    exact Nat.le_trans hA' hB
  rw [hA, hB]
  omega

/-- `e = 2^(2m-1) - 1` is odd. -/
private theorem odd_two_pow_add_one_e (m : Nat) (hm : 0 < m) :
    IsOdd (2 ^ (2 * m - 1) - 1) := by
  unfold IsOdd
  have hp : 2 ^ (2 * m - 1) = 2 * 2 ^ (2 * m - 2) := two_pow_pred_two_mul_double m hm
  rw [hp]
  have h1 : 1 <= 2 ^ (2 * m - 2) := Nat.one_le_pow (2 * m - 2) 2 (by omega)
  omega

/-- `2*P + 1 <= P^3` once `2 <= P`. -/
private theorem two_mul_add_one_le_cube (P : Nat) (hP : 2 <= P) :
    2 * P + 1 <= P * (P * P) := by
  have hPP : 4 <= P * P := by
    have h1 : 2 * P <= P * P := Nat.mul_le_mul_right P hP
    have h2 : 4 <= 2 * P := by omega
    omega
  have hPc : 4 * P <= P * (P * P) := by
    have h := Nat.mul_le_mul_right P hPP
    simpa [Nat.mul_assoc] using h
  omega

/-- The defining identity for the `a = 2^m + 1` family. -/
private theorem two_pow_add_one_main (m : Nat) (hm : 0 < m) :
    (2 ^ m + 1) * (2 ^ (2 * m) - (2 ^ m + 1)) + 1 =
      2 ^ (m + 1) * (2 ^ (2 * m - 1) - 1) := by
  have hQ : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by
    have h : 2 * m = m + m := by omega
    rw [h, Nat.pow_add]
  have hsucc : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hR : 2 ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by
    have h : 2 * m = (2 * m - 1) + 1 := by omega
    calc
      2 ^ (2 * m - 1) * 2 = 2 ^ ((2 * m - 1) + 1) := by rw [← Nat.pow_succ]
      _ = 2 ^ (2 * m) := by rw [← h]
  have hcube : (2 * 2 ^ m) * 2 ^ (2 * m - 1) = 2 ^ m * (2 ^ m * 2 ^ m) := by
    calc
      (2 * 2 ^ m) * 2 ^ (2 * m - 1) = 2 * (2 ^ m * 2 ^ (2 * m - 1)) := by
        rw [Nat.mul_assoc]
      _ = 2 ^ m * (2 * 2 ^ (2 * m - 1)) := by
        rw [← Nat.mul_assoc]
        rw [Nat.mul_comm 2 (2 ^ m)]
        rw [Nat.mul_assoc]
      _ = 2 ^ m * (2 ^ (2 * m - 1) * 2) := by
        rw [Nat.mul_comm 2 (2 ^ (2 * m - 1))]
      _ = 2 ^ m * (2 ^ m * 2 ^ m) := by rw [hR, hQ]
  have hPge2 : 2 <= 2 ^ m := by
    have hp' : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_eq_double_pred m hm
    rw [hp']
    have h1 : 1 <= 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
    omega
  have hle := two_mul_add_one_le_cube (2 ^ m) hPge2
  calc
    (2 ^ m + 1) * (2 ^ (2 * m) - (2 ^ m + 1)) + 1
        = (2 ^ m + 1) * (2 ^ m * 2 ^ m - (2 ^ m + 1)) + 1 := by rw [hQ]
    _ = ((2 ^ m + 1) * (2 ^ m * 2 ^ m) - (2 ^ m + 1) * (2 ^ m + 1)) + 1 := by
          rw [Nat.mul_sub_left_distrib]
    _ = ((2 ^ m * (2 ^ m * 2 ^ m) + 2 ^ m * 2 ^ m) -
          (2 ^ m * 2 ^ m + 2 * 2 ^ m + 1)) + 1 := by
          rw [Nat.add_mul, Nat.one_mul]
          rw [square_add_one (2 ^ m)]
    _ = 2 ^ m * (2 ^ m * 2 ^ m) - 2 * 2 ^ m := by omega
    _ = 2 ^ (m + 1) * (2 ^ (2 * m - 1) - 1) := by
          rw [hsucc]
          rw [Nat.mul_sub_left_distrib]
          rw [Nat.mul_one]
          rw [hcube]

/-- `s2(d) = 2m - 1` for `d = 2^(2m) - (2^m+1)`. -/
private theorem two_pow_add_one_weight_d (m : Nat) (hm : 0 < m) :
    binaryWeight (2 ^ (2 * m) - (2 ^ m + 1)) = 2 * m - 1 := by
  have x_lt_square : ∀ x : Nat, 1 < x -> x < x * x := by
    intro x hx
    rcases x with _ | _ | k
    · omega
    · omega
    · have hsq : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by
        rw [show k + 2 = (k + 1) + 1 by omega, square_add_one (k + 1)]
        rw [square_add_one k]
        omega
      rw [hsq]
      have hk0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
      rcases hk0 with hk0 | hkpos
      · subst hk0
        omega
      · have h : k <= k * k := Nat.le_mul_of_pos_right k hkpos
        omega
  have hlt : 2 ^ m < 2 ^ (2 * m) := by
    have h : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by
      have hh : 2 * m = m + m := by omega
      rw [hh, Nat.pow_add]
    rw [h]
    have h1 : 1 < 2 ^ m := by
      have hp : 2 ^ m = 2 * 2 ^ (m - 1) := two_pow_eq_double_pred m hm
      rw [hp]
      have h2 : 1 <= 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
      omega
    exact x_lt_square (2 ^ m) h1
  have hsub : 2 ^ (2 * m) - (2 ^ m + 1) = 2 ^ (2 * m) - 1 - 2 ^ m := by
    omega
  rw [hsub]
  rw [binaryWeight_complement (2 ^ m) (2 * m) hlt]
  rw [binaryWeight_two_pow]

/-- `s2(e) = 2m - 1` for `e = 2^(2m-1) - 1`. -/
private theorem two_pow_add_one_weight_e (m : Nat) :
    binaryWeight (2 ^ (2 * m - 1) - 1) = 2 * m - 1 := by
  rw [binaryWeight_two_pow_sub_one (2 * m - 1)]

/-- Lemma 2.28, second special class: `a = 2^m + 1`, `b = 1`. -/
theorem balance_two_pow_add_one (m : Nat) (hm : 0 < m) :
    ∃ d e : Nat, BalanceWitness (2 ^ m + 1) 1 d e := by
  let d := 2 ^ (2 * m) - (2 ^ m + 1)
  let e := 2 ^ (2 * m - 1) - 1
  refine ⟨d, e, ?oddD, ?oddE, ?main, ?wt⟩
  · dsimp [d]
    exact odd_two_pow_add_one_d m hm
  · dsimp [e]
    exact odd_two_pow_add_one_e m hm
  · have hlen : binaryLength (2 ^ m + 1) = m + 1 := by
      have hlen' := binaryLength_two_pow_add_one (m - 1)
      have h1 : (m - 1) + 1 = m := by omega
      have h2 : (m - 1) + 2 = m + 1 := by omega
      rw [h1, h2] at hlen'
      exact hlen'
    dsimp [d, e]
    rw [hlen]
    exact two_pow_add_one_main m hm
  · dsimp [d, e]
    rw [two_pow_add_one_weight_d m hm, two_pow_add_one_weight_e m]

end StringFlow
