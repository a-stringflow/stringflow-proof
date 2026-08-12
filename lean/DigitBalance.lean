import BinaryDigits

/-!
# Digit-balance machinery for Problem 2

This module formalizes the digit-sum difference
`f(q) = s_2(a q) - s_2(q)` (Observation 2.30), its additivity over
disjoint binary blocks, and the Mersenne special case of the
digit-balance lemma (Lemma 2.28).
-/

namespace StringFlow

/-- Oddness for natural numbers, expressed through the lowest bit. -/
def IsOdd (n : Nat) : Prop := n % 2 = 1

/-- An integer-valued digit-sum difference `s_2(a q) - s_2(q)`. -/
def digitDelta (a q : Nat) : Int :=
  (binaryWeight (a * q) : Int) - (binaryWeight q : Int)

/-- Observation 2.30: digit-sum differences add over disjoint binary blocks. -/
theorem digitDelta_add (a q1 q2 M : Nat)
    (hq : q2 < 2 ^ M) (ha : a * q2 < 2 ^ M) :
    digitDelta a (q1 * 2 ^ M + q2) = digitDelta a q1 + digitDelta a q2 := by
  have h1 : binaryWeight (a * (q1 * 2 ^ M + q2)) =
      binaryWeight (a * q1) + binaryWeight (a * q2) := by
    rw [Nat.mul_add]
    rw [← Nat.mul_assoc]
    exact binaryWeight_add_mul_two_pow (a * q1) (a * q2) M ha
  have h2 : binaryWeight (q1 * 2 ^ M + q2) =
      binaryWeight q1 + binaryWeight q2 :=
    binaryWeight_add_mul_two_pow q1 q2 M hq
  unfold digitDelta
  rw [h1, h2]
  omega

/-- A witness for the digit-balance lemma (Lemma 2.28): odd `d, e` with
  `a*d+b = 2^(L(a))*e` and `s2 e = s2 d`. -/
def BalanceWitness (a b d e : Nat) : Prop :=
  IsOdd d ∧ IsOdd e ∧ a * d + b = 2 ^ binaryLength a * e ∧
    binaryWeight e = binaryWeight d

/-- Mersenne family `a = 2^m - 1`: `d = b`, `e = b` works for every odd `b`. -/
theorem balance_mersenne (a b m : Nat) (ha : a = 2 ^ m - 1) (hb : IsOdd b) :
    ∃ d e : Nat, BalanceWitness a b d e := by
  refine ⟨b, b, hb, hb, ?_, rfl⟩
  rw [ha]
  rw [binaryLength_two_pow_sub_one m]
  rw [Nat.mul_sub_right_distrib]
  rw [Nat.one_mul]
  have hle : b ≤ 2 ^ m * b := by
    calc
      b = b * 1 := by rw [Nat.mul_one]
      _ ≤ b * 2 ^ m := by
        exact Nat.mul_le_mul_left b (Nat.one_le_pow m 2 (by omega))
      _ = 2 ^ m * b := by rw [Nat.mul_comm]
  exact Nat.sub_add_cancel hle

end StringFlow
