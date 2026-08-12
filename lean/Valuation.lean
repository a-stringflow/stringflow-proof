import BinaryDigits

/-!
# 2-adic valuation and odd part

Basic structural facts about `twoValuation` (`v_2`) and `oddPart`
used by the `F_b` cycle theory (Problem 1) and the 2-adic
equidistribution results (Problem 2).
-/

namespace StringFlow

/-- `v2(2n) = v2(n)+1` for positive `n`. -/
theorem twoValuation_mul_two (n : Nat) (hn : 0 < n) :
    twoValuation (2 * n) = twoValuation n + 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [twoValuation_succ (2 * k + 1)]
      have hmod : (2 * k + 2) % 2 = 0 := by omega
      have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
      rw [hmod, hdiv]
      simp
      omega

/-- Odd numbers have `v2 = 0`. -/
theorem twoValuation_odd (n : Nat) (h : n % 2 = 1) : twoValuation n = 0 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [twoValuation_succ k]
      have hnot : ¬ (k + 1) % 2 = 0 := by omega
      rw [if_neg hnot]

/-- Removing one factor of two from the odd part does not change it. -/
theorem oddPart_mul_two (n : Nat) : oddPart (2 * n) = oddPart n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hpos : 0 < n := by omega
    unfold oddPart
    have hv : twoValuation (2 * n) = twoValuation n + 1 := twoValuation_mul_two n hpos
    rw [hv]
    have hpow : 2 ^ (twoValuation n + 1) = 2 * 2 ^ twoValuation n := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    rw [Nat.mul_comm 2 n]
    rw [Nat.mul_comm 2 (2 ^ twoValuation n)]
    exact Nat.mul_div_mul_right (m := 2) n (2 ^ twoValuation n) (by omega)

/-- Odd numbers are their own odd part. -/
theorem oddPart_odd (n : Nat) (h : n % 2 = 1) : oddPart n = n := by
  unfold oddPart
  have hv : twoValuation n = 0 := twoValuation_odd n h
  rw [hv, Nat.pow_zero, Nat.div_one]

/-- The odd part of a positive number is odd. -/
theorem oddPart_odd_of_pos (n : Nat) (hn : 0 < n) : oddPart n % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hn0 : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      rcases hn0 with hn0 | hnpos
      · subst hn0
        omega
      · have h01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
        rcases h01 with h0 | h1
        · have hsplit : n = 2 * (n / 2) := by
            have hd := Nat.div_add_mod n 2
            rw [h0] at hd
            omega
          have hhalf : 0 < n / 2 := by omega
          have hih : oddPart (n / 2) % 2 = 1 := ih (n / 2) (by omega) (by omega)
          rw [hsplit]
          rw [oddPart_mul_two]
          exact hih
        · rw [oddPart_odd n h1]
          exact h1

/-- Decomposition `n = 2^v2(n) * oddPart(n)` for positive `n`. -/
theorem n_eq_two_pow_mul_oddPart (n : Nat) (hn : 0 < n) :
    n = 2 ^ twoValuation n * oddPart n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hn0 : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      rcases hn0 with hn0 | hnpos
      · subst hn0
        omega
      · have h01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
        rcases h01 with h0 | h1
        · have hsplit : n = 2 * (n / 2) := by
            have hd := Nat.div_add_mod n 2
            rw [h0] at hd
            omega
          have hhalf : 0 < n / 2 := by omega
          have hih' : n / 2 = 2 ^ twoValuation (n / 2) * oddPart (n / 2) :=
            ih (n / 2) (by omega) (by omega)
          have hpow : 2 ^ (twoValuation (n / 2) + 1) = 2 * 2 ^ twoValuation (n / 2) := by
            rw [Nat.pow_succ, Nat.mul_comm]
          rw [hsplit]
          rw [twoValuation_mul_two (n / 2) hhalf]
          rw [oddPart_mul_two]
          calc
            2 * (n / 2) = 2 * (2 ^ twoValuation (n / 2) * oddPart (n / 2)) := by
              congr 1
            _ = 2 ^ (twoValuation (n / 2) + 1) * oddPart (n / 2) := by
              rw [hpow]
              rw [Nat.mul_assoc]
        · have hv : twoValuation n = 0 := twoValuation_odd n h1
          rw [hv, Nat.pow_zero, Nat.one_mul]
          rw [oddPart_odd n h1]

/-- Positive numbers with `v2 = 0` are odd. -/
theorem twoValuation_eq_zero_odd (n : Nat) (hn : 0 < n) (hv : twoValuation n = 0) :
    n % 2 = 1 := by
  have hdec := n_eq_two_pow_mul_oddPart n hn
  rw [hv, Nat.pow_zero, Nat.one_mul] at hdec
  have hodd := oddPart_odd_of_pos n hn
  rw [hdec]
  exact hodd

/-- The odd part of an even number is at most half of it. -/
theorem oddPart_le_half_of_even (m : Nat) (h : m % 2 = 0) : oddPart m ≤ m / 2 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have hpos : 0 < m := by omega
    have hdec := n_eq_two_pow_mul_oddPart m hpos
    have hvpos : 0 < twoValuation m := by
      have h0 : twoValuation m = 0 ∨ 0 < twoValuation m :=
        Nat.eq_zero_or_pos (twoValuation m)
      rcases h0 with hz | hp
      · have hmodd : m % 2 = 1 := twoValuation_eq_zero_odd m hpos hz
        omega
      · exact hp
    have hpow : 2 ^ twoValuation m = 2 * 2 ^ (twoValuation m - 1) := by
      have h : twoValuation m = (twoValuation m - 1) + 1 := by omega
      calc
        2 ^ twoValuation m = 2 ^ ((twoValuation m - 1) + 1) := by congr 1
        _ = 2 * 2 ^ (twoValuation m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hm2 : m = 2 * (2 ^ (twoValuation m - 1) * oddPart m) := by
      calc
        m = 2 ^ twoValuation m * oddPart m := hdec
        _ = (2 * 2 ^ (twoValuation m - 1)) * oddPart m := by rw [hpow]
        _ = 2 * (2 ^ (twoValuation m - 1) * oddPart m) := by rw [Nat.mul_assoc]
    have hdiv : m / 2 = 2 ^ (twoValuation m - 1) * oddPart m := by
      calc
        m / 2 = (2 * (2 ^ (twoValuation m - 1) * oddPart m)) / 2 := by
          congr 1
        _ = 2 ^ (twoValuation m - 1) * oddPart m := by
          have h := Nat.mul_div_left (2 ^ (twoValuation m - 1) * oddPart m) (n := 2) (by omega)
          rw [Nat.mul_comm]
          exact h
    rw [hdiv]
    have h1 : 0 < 2 ^ (twoValuation m - 1) :=
      Nat.pow_pos (show 0 < 2 by omega)
    exact Nat.le_mul_of_pos_left (oddPart m) h1

end StringFlow
