import FBeta

/-!
# The `×2` cycle modulo `b` (Problem 1, Theorems 1.8 and 1.13)

For an odd `b`, the `U_b` cycles of `F_b` correspond to cycles of the map
`x -> 2x mod b`.  For a positive `r < b` with `T = ord_b(2)` and
`M = (2^T - 1) / b`, the number of odd terms in the first `T` steps of
that orbit is `s2(rM)`: the weight of the binary period word of `r/b`.

The module is self-contained: instead of developing a full theory of
`ord_b(2)`, the statements take the hypotheses `0 < T`, `2^T % b = 1`
and `M = (2^T - 1) / b` (plus minimality of `T` where the period is
claimed).
-/

namespace StringFlow

/-- One step of the `×2` map modulo `b`. -/
def mulTwoStep (b x : Nat) : Nat := (2 * x) % b

/-- The `i`-th bit of `n` (least significant first). -/
def binaryBit (n i : Nat) : Nat := (n / 2 ^ i) % 2

/-- Reducing the right factor before multiplication does not change the
residue. -/
theorem mul_mod_comm (c x n : Nat) : (c * (x % n)) % n = (c * x) % n := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [Nat.mod_zero]
  · have hn : 0 < n := by omega
    calc
      (c * (x % n)) % n = (c % n) * ((x % n) % n) % n := by rw [Nat.mul_mod]
      _ = (c % n) * (x % n) % n := by
        rw [Nat.mod_eq_of_lt (Nat.mod_lt x hn)]
      _ = (c * x) % n := by rw [← Nat.mul_mod]

/-- The `F_b`/`U_b` iterate function is reused; the orbit of `mulTwoStep`
after `i` steps from `r < b` is `(2^i * r) % b`. -/
theorem iterate_mulTwoStep (b r i : Nat) (hr : r % b = r) :
    iterate (mulTwoStep b) i r = (2 ^ i * r) % b := by
  induction i generalizing r hr with
  | zero =>
      simp [iterate, hr]
  | succ i ih =>
      have hx : (mulTwoStep b r) % b = mulTwoStep b r := by
        unfold mulTwoStep
        by_cases hb0 : b = 0
        · subst hb0
          simp [Nat.mod_zero]
        · have hb : 0 < b := by omega
          rw [Nat.mod_eq_of_lt (Nat.mod_lt (2 * r) hb)]
      have hpow2 : 2 ^ i * (2 * r) = 2 ^ (i + 1) * r := by
        rw [Nat.pow_succ]
        rw [Nat.mul_assoc]
      calc
        iterate (mulTwoStep b) (i + 1) r = iterate (mulTwoStep b) i (mulTwoStep b r) := by
          rw [iterate]
        _ = (2 ^ i * mulTwoStep b r) % b := ih (mulTwoStep b r) hx
        _ = (2 ^ i * ((2 * r) % b)) % b := rfl
        _ = (2 ^ i * (2 * r)) % b := by rw [mul_mod_comm (2 ^ i) (2 * r) b]
        _ = (2 ^ (i + 1) * r) % b := by rw [hpow2]

/-- `2^T % b = 1` makes the orbit periodic with period `T`. -/
theorem mulTwoStep_period (b r T : Nat) (hr : r % b = r) (hpow : 2 ^ T % b = 1) :
    iterate (mulTwoStep b) T r = r := by
  rw [iterate_mulTwoStep b r T hr]
  calc
    (2 ^ T * r) % b = ((2 ^ T % b) * (r % b)) % b := by
      rw [Nat.mul_mod]
    _ = (1 * r) % b := by rw [hpow, hr]
    _ = r % b := by rw [Nat.one_mul]
    _ = r := hr

end StringFlow
