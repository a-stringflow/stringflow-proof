import BinaryDigits
import Valuation

/-!
# LTE decomposition for the macro-step window inequality

This module states the exact LTE/K4 interface used in
`lte_macro_k4_reduction.md`.  It does not assert the local lemma or K4.
The definitions are natural-number versions of the macro positive odd
part `C = (5*r+3)/2^(2a)` and of the failure threshold
`v2(5^a*C-1) <= m+1`.

The three-way decomposition is a pure identity once the standard LTE
valuation `v2(5^a-1) = 2+v2(a)` is supplied; it is stated here as an
open statement, exactly like the other interfaces in this repository.
-/

namespace StringFlow.Lte

/-- `v2(2^n * x) = n` when `x` is odd. -/
theorem twoValuation_mul_two_pow_eq (n x : Nat) (hx : x % 2 = 1) :
    twoValuation (2 ^ n * x) = n := by
  induction n with
  | zero => simp [twoValuation_odd x hx]
  | succ n ih =>
      have hpos : 0 < 2 ^ n * x := by
        exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
      have hpow : 2 ^ (n + 1) * x = 2 * (2 ^ n * x) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_assoc]
        rw [Nat.mul_left_comm]
      rw [hpow]
      rw [twoValuation_mul_two (2 ^ n * x) hpos]
      rw [ih]

/-- `v2(2^n * x) = n + v2(x)` for positive `x`. -/
theorem twoValuation_mul_two_pow (n x : Nat) (hx : 0 < x) :
    twoValuation (2 ^ n * x) = n + twoValuation x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < 2 ^ n * x := Nat.mul_pos (Nat.pow_pos (by omega)) hx
      have hpow : 2 ^ (n + 1) * x = 2 * (2 ^ n * x) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_assoc]
        rw [Nat.mul_left_comm]
      rw [hpow]
      rw [twoValuation_mul_two (2 ^ n * x) hpos]
      rw [ih]
      omega

/-- `v2(n) <= k` is equivalent to `2^(k+1)` not dividing positive `n`. -/
theorem twoValuation_le_iff_not_dvd_pow (n k : Nat) (hn : 0 < n) :
    twoValuation n ≤ k ↔ ¬ (2 ^ (k + 1) ∣ n) := by
  constructor
  · intro hv hdvd
    rcases hdvd with ⟨t, ht⟩
    have hpos_t : 0 < t := by
      by_cases ht0 : t = 0
      · rw [ht0, Nat.mul_zero] at ht
        omega
      · exact Nat.pos_of_ne_zero ht0
    have hvt : twoValuation (2 ^ (k + 1) * t) = k + 1 + twoValuation t :=
      twoValuation_mul_two_pow (k + 1) t hpos_t
    have hv2 : twoValuation n = k + 1 + twoValuation t := by
      rw [ht, hvt]
    omega
  · intro hndvd
    by_cases h : twoValuation n ≤ k
    · exact h
    · exfalso
      have hgt : k + 1 ≤ twoValuation n := by omega
      have hdec := n_eq_two_pow_mul_oddPart n hn
      have hpow : 2 ^ twoValuation n = 2 ^ (k + 1) * 2 ^ (twoValuation n - (k + 1)) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hdiv : 2 ^ (k + 1) ∣ n := by
        rw [hdec, hpow]
        exact ⟨2 ^ (twoValuation n - (k + 1)) * oddPart n, by rw [Nat.mul_assoc]⟩
      exact hndvd hdiv

/-- `2^k` is even for `k >= 1`. -/
theorem pow_two_even_mod (k : Nat) (hk : 1 ≤ k) : (2 ^ k) % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
      rw [Nat.pow_succ]
      rw [Nat.mul_mod]
      simp

/-- Multiplying by an even number keeps the product even. -/
theorem even_mul_mod_two (a b : Nat) (ha : a % 2 = 0) : (a * b) % 2 = 0 := by
  rw [Nat.mul_mod]
  simp [ha]

/-- An even number plus an odd number is odd. -/
theorem even_add_odd_mod_two (a b : Nat) (ha : a % 2 = 0) (hb : b % 2 = 1) :
    (a + b) % 2 = 1 := by
  rw [Nat.add_mod]
  simp [ha, hb]

/-- If `v2(x) < v2(y)`, then `v2(x+y) = v2(x)`.  Strict 2-adic
triangle identity for natural numbers. -/
theorem twoValuation_add_eq_of_lt (x y : Nat) (hx : 0 < x) (hy : 0 < y)
    (h : twoValuation x < twoValuation y) :
    twoValuation (x + y) = twoValuation x := by
  let vx := twoValuation x
  let vy := twoValuation y
  let ox := oddPart x
  let oy := oddPart y
  have hxdec : x = 2 ^ vx * ox := by
    dsimp [vx, ox]
    exact n_eq_two_pow_mul_oddPart x hx
  have hydec : y = 2 ^ vy * oy := by
    dsimp [vy, oy]
    exact n_eq_two_pow_mul_oddPart y hy
  have hxodd : ox % 2 = 1 := by
    dsimp [ox]
    exact oddPart_odd_of_pos x hx
  have hyodd : oy % 2 = 1 := by
    dsimp [oy]
    exact oddPart_odd_of_pos y hy
  have hd : 0 < vy - vx := by omega
  have hpow : 2 ^ vy = 2 ^ vx * 2 ^ (vy - vx) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hsum : x + y = 2 ^ vx * (ox + 2 ^ (vy - vx) * oy) := by
    rw [hxdec, hydec, hpow]
    rw [Nat.mul_assoc]
    rw [← Nat.mul_add]
  have h1 : (2 ^ (vy - vx) * oy) % 2 = 0 := by
    have hp : (2 ^ (vy - vx)) % 2 = 0 := pow_two_even_mod (vy - vx) hd
    exact even_mul_mod_two (2 ^ (vy - vx)) oy hp
  have hodd : (ox + 2 ^ (vy - vx) * oy) % 2 = 1 := by
    rw [Nat.add_comm]
    exact even_add_odd_mod_two (2 ^ (vy - vx) * oy) ox h1 hxodd
  have hv : twoValuation (ox + 2 ^ (vy - vx) * oy) = 0 := twoValuation_odd _ hodd
  have hpos : 0 < ox + 2 ^ (vy - vx) * oy := by
    have hox : 0 < ox := by
      by_cases hz : ox = 0
      · rw [hz] at hxodd
        omega
      · exact Nat.pos_of_ne_zero hz
    omega
  calc
    twoValuation (x + y) = twoValuation (2 ^ vx * (ox + 2 ^ (vy - vx) * oy)) := by rw [hsum]
    _ = vx + twoValuation (ox + 2 ^ (vy - vx) * oy) :=
      twoValuation_mul_two_pow vx (ox + 2 ^ (vy - vx) * oy) hpos
    _ = vx := by rw [hv]; omega

/-- Symmetric form: if `v2(y) < v2(x)`, then `v2(x+y) = v2(y)`. -/
theorem twoValuation_add_eq_of_gt (x y : Nat) (hx : 0 < x) (hy : 0 < y)
    (h : twoValuation y < twoValuation x) :
    twoValuation (x + y) = twoValuation y := by
  rw [Nat.add_comm]
  exact twoValuation_add_eq_of_lt y x hy hx h

/-- If `v2(x)=v2(y)`, then `v2(x+y) >= v2(x)+1`. -/
theorem twoValuation_add_ge_succ_of_eq (x y : Nat) (hx : 0 < x) (hy : 0 < y)
    (h : twoValuation x = twoValuation y) :
    twoValuation x + 1 ≤ twoValuation (x + y) := by
  have hxdec := n_eq_two_pow_mul_oddPart x hx
  have hydec := n_eq_two_pow_mul_oddPart y hy
  have hxodd : oddPart x % 2 = 1 := oddPart_odd_of_pos x hx
  have hyodd : oddPart y % 2 = 1 := oddPart_odd_of_pos y hy
  have hsum : x + y = 2 ^ twoValuation x * (oddPart x + oddPart y) := by
    conv =>
      lhs
      rw [hxdec, hydec, h]
    rw [← Nat.mul_add]
    rw [h]
  have hpar : (oddPart x + oddPart y) % 2 = 0 := by
    rw [Nat.add_mod, hxodd, hyodd]
  have hxopos : 0 < oddPart x := by
    by_cases hz : oddPart x = 0
    · rw [hz] at hxodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hyopos : 0 < oddPart y := by
    by_cases hz : oddPart y = 0
    · rw [hz] at hyodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hpos : 0 < oddPart x + oddPart y := by omega
  have hge : 1 ≤ twoValuation (oddPart x + oddPart y) := by
    by_cases hge' : 1 ≤ twoValuation (oddPart x + oddPart y)
    · exact hge'
    · exfalso
      have hz : twoValuation (oddPart x + oddPart y) = 0 := by omega
      have hodd := twoValuation_eq_zero_odd (oddPart x + oddPart y) hpos hz
      rw [hpar] at hodd
      omega
  calc
    twoValuation (x + y) = twoValuation (2 ^ twoValuation x * (oddPart x + oddPart y)) := by rw [hsum]
    _ = twoValuation x + twoValuation (oddPart x + oddPart y) :=
        twoValuation_mul_two_pow (twoValuation x) (oddPart x + oddPart y) hpos
    _ ≥ twoValuation x + 1 := by omega

/-- If `2^k | n`, then `k <= v2(n)`. -/
theorem twoValuation_le_of_dvd (n k : Nat) (hn : 0 < n) (h : 2 ^ k ∣ n) :
    k ≤ twoValuation n := by
  rcases h with ⟨t, ht⟩
  have htpos : 0 < t := by
    by_cases ht0 : t = 0
    · rw [ht0, Nat.mul_zero] at ht
      omega
    · exact Nat.pos_of_ne_zero ht0
  have hv : twoValuation n = k + twoValuation t := by
    rw [ht]
    exact twoValuation_mul_two_pow k t htpos
  omega

/-- `k <= v2(n)` iff `2^k | n` for positive `n`. -/
theorem twoValuation_ge_iff_dvd_pow (n k : Nat) (hn : 0 < n) :
    k ≤ twoValuation n ↔ 2 ^ k ∣ n := by
  constructor
  · intro hk
    have hdec := n_eq_two_pow_mul_oddPart n hn
    have hpow : 2 ^ twoValuation n = 2 ^ k * 2 ^ (twoValuation n - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hdec, hpow]
    exact ⟨2 ^ (twoValuation n - k) * oddPart n, by rw [Nat.mul_assoc]⟩
  · intro h
    exact twoValuation_le_of_dvd n k hn h

/-- Multiplying by an odd number does not change `v2`. -/
theorem twoValuation_mul_odd (x n : Nat) (hx : x % 2 = 1) (hn : 0 < n) :
    twoValuation (x * n) = twoValuation n := by
  have hdec := n_eq_two_pow_mul_oddPart n hn
  have ho : oddPart n % 2 = 1 := oddPart_odd_of_pos n hn
  have hxo : (x * oddPart n) % 2 = 1 := by
    rw [Nat.mul_mod, hx, ho]
  have hxpos : 0 < x := by
    by_cases hz : x = 0
    · rw [hz] at hx
      omega
    · exact Nat.pos_of_ne_zero hz
  have hopos : 0 < oddPart n := by
    by_cases hz : oddPart n = 0
    · rw [hz] at ho
      omega
    · exact Nat.pos_of_ne_zero hz
  have hpos : 0 < x * oddPart n := Nat.mul_pos hxpos hopos
  have hv : twoValuation (x * oddPart n) = 0 := twoValuation_odd (x * oddPart n) hxo
  have hxn : x * n = x * (2 ^ twoValuation n * oddPart n) := by
    conv =>
      lhs
      rw [hdec]
  calc
    twoValuation (x * n) = twoValuation (x * (2 ^ twoValuation n * oddPart n)) := by rw [hxn]
    _ = twoValuation ((x * 2 ^ twoValuation n) * oddPart n) := by rw [Nat.mul_assoc]
    _ = twoValuation ((2 ^ twoValuation n * x) * oddPart n) := by
        congr 1
        rw [Nat.mul_comm x (2 ^ twoValuation n)]
    _ = twoValuation (2 ^ twoValuation n * (x * oddPart n)) := by rw [Nat.mul_assoc]
    _ = twoValuation n + twoValuation (x * oddPart n) :=
        twoValuation_mul_two_pow (twoValuation n) (x * oddPart n) hpos
    _ = twoValuation n := by rw [hv]; omega

/-- `5^n` is odd. -/
theorem five_pow_odd (n : Nat) : (5 ^ n) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- `v2(5^n) = 0`. -/
theorem twoValuation_five_pow (n : Nat) : twoValuation (5 ^ n) = 0 :=
  twoValuation_odd (5 ^ n) (five_pow_odd n)

/-- Multiplying by `5^n` does not change `v2`. -/
theorem twoValuation_five_pow_mul (n x : Nat) (hx : 0 < x) :
    twoValuation (5 ^ n * x) = twoValuation x :=
  twoValuation_mul_odd (5 ^ n) x (five_pow_odd n) hx

/-- Since `5` is odd, `2^k | 5*n` implies `2^k | n`. -/
theorem dvd_two_pow_of_odd_mul (k n : Nat) (h : 2 ^ k ∣ 5 * n) : 2 ^ k ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hv : twoValuation (5 * n) = twoValuation n :=
      twoValuation_mul_odd 5 n (by decide) hnpos
    have hk : k ≤ twoValuation n := by
      have hk' : k ≤ twoValuation (5 * n) :=
        twoValuation_le_of_dvd (5 * n) k (by omega) h
      rw [hv] at hk'
      exact hk'
    have hdec := n_eq_two_pow_mul_oddPart n hnpos
    have hpow : 2 ^ twoValuation n = 2 ^ k * 2 ^ (twoValuation n - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hdec, hpow]
    exact ⟨2 ^ (twoValuation n - k) * oddPart n, by rw [Nat.mul_assoc]⟩

/-- If `a % m = 1`, then `m | a - 1`. -/
theorem dvd_sub_one_of_mod_eq_one (a m : Nat) (_hm : 0 < m) (h : a % m = 1) :
    m ∣ a - 1 := by
  have hd := Nat.div_add_mod a m
  rw [h] at hd
  have hsub : a - 1 = (a / m) * m := by
    conv =>
      lhs
      lhs
      rw [← hd]
    rw [Nat.add_comm, Nat.mul_comm]
    exact Nat.add_sub_cancel_left 1 (a / m * m)
  rw [hsub]
  exact ⟨a / m, by rw [Nat.mul_comm]⟩

/-- The inverse of `5` modulo `2^H` is unique among representatives
below `2^H`, ordered case. -/
theorem five_inv_unique_le (H m1 m2 : Nat)
    (hle : m1 ≤ m2) (h1 : m1 < 2 ^ H) (h2 : m2 < 2 ^ H)
    (h1' : (5 * m1) % 2 ^ H = 1) (h2' : (5 * m2) % 2 ^ H = 1) :
    m1 = m2 := by
  have hm1pos : 0 < m1 := by
    by_cases hm1z : m1 = 0
    · subst hm1z
      simp at h1'
    · exact Nat.pos_of_ne_zero hm1z
  have hm2pos : 0 < m2 := by
    by_cases hm2z : m2 = 0
    · subst hm2z
      simp at h2'
    · exact Nat.pos_of_ne_zero hm2z
  have hdvd1 : 2 ^ H ∣ 5 * m2 - 1 :=
    dvd_sub_one_of_mod_eq_one (5 * m2) (2 ^ H) (by omega) h2'
  have hdvd0 : 2 ^ H ∣ 5 * m1 - 1 :=
    dvd_sub_one_of_mod_eq_one (5 * m1) (2 ^ H) (by omega) h1'
  have hsub : 5 * (m2 - m1) = (5 * m2 - 1) - (5 * m1 - 1) := by
    rw [Nat.mul_sub_left_distrib]
    omega
  have hdvd : 2 ^ H ∣ 5 * (m2 - m1) := by
    rw [hsub]
    exact Nat.dvd_sub hdvd1 hdvd0
  have hdiv : 2 ^ H ∣ m2 - m1 := dvd_two_pow_of_odd_mul H (m2 - m1) hdvd
  have hlt : m2 - m1 < 2 ^ H := by
    by_cases hm1 : m1 = 0
    · subst hm1
      simpa using h2
    · have hlt' : m2 - m1 < m2 := Nat.sub_lt hm2pos (Nat.pos_of_ne_zero hm1)
      have hlt2 : m2 - m1 < 2 ^ H := by omega
      exact hlt2
  have hz : m2 - m1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
  omega

/-- The inverse of `5` modulo `2^H` is unique among representatives
below `2^H`. -/
theorem five_inv_unique (H m1 m2 : Nat)
    (h1 : m1 < 2 ^ H) (h2 : m2 < 2 ^ H)
    (h1' : (5 * m1) % 2 ^ H = 1) (h2' : (5 * m2) % 2 ^ H = 1) :
    m1 = m2 := by
  by_cases hle : m1 ≤ m2
  · exact five_inv_unique_le H m1 m2 hle h1 h2 h1' h2'
  · have hle' : m2 ≤ m1 := by omega
    exact (five_inv_unique_le H m2 m1 hle' h2 h1 h2' h1').symm

/-- Exact numerator split `5^a*C-1 = (5^a-1)*C + (C-1)`. -/
theorem macroNumerator_split (a C : Nat) :
    5 ^ a * C - 1 = (5 ^ a - 1) * C + (C - 1) := by
  cases C with
  | zero => simp
  | succ C =>
      rw [Nat.mul_sub_right_distrib]
      rw [Nat.one_mul]
      have hle : C + 1 ≤ 5 ^ a * (C + 1) := by
        exact Nat.le_mul_of_pos_left (C + 1) (Nat.pow_pos (by omega))
      have hsub : (5 ^ a * (C + 1) - (C + 1)) + (C + 1) = 5 ^ a * (C + 1) :=
        Nat.sub_add_cancel hle
      omega

/-- `a * b * c = b * (a * c)`, a small semiring normal-form lemma. -/
theorem mul_assoc_left_comm (a b c : Nat) : a * b * c = b * (a * c) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm]

/-- The `s < n` LTE factorisation of `(2^n*w)*C + 2^s*u`. -/
theorem lteFactor_lt (n s w C u : Nat) (hsn : s < n) :
    (2 ^ n * w) * C + 2 ^ s * u = 2 ^ s * (2 ^ (n - s) * w * C + u) := by
  have hns : n = (n - s) + s := by omega
  have hpow : 2 ^ n = 2 ^ (n - s) * 2 ^ s := by
    conv =>
      lhs
      rw [hns]
      rw [Nat.pow_add]
  rw [hpow]
  have hmain : w * (C * (2 ^ s * 2 ^ (n - s))) = (w * (C * 2 ^ (n - s))) * 2 ^ s := by
    calc
      w * (C * (2 ^ s * 2 ^ (n - s)))
          = (w * C) * (2 ^ s * 2 ^ (n - s)) := by rw [← Nat.mul_assoc]
      _ = (w * C) * (2 ^ (n - s) * 2 ^ s) := by
          conv =>
            lhs
            rhs
            rw [Nat.mul_comm]
      _ = ((w * C) * 2 ^ (n - s)) * 2 ^ s := by rw [← Nat.mul_assoc]
      _ = (w * (C * 2 ^ (n - s))) * 2 ^ s := by
          congr 1
          rw [← Nat.mul_assoc]
  have hswap : (2 ^ (n - s) * 2 ^ s) * (w * C) = 2 ^ s * (2 ^ (n - s) * w * C) := by
    calc
      (2 ^ (n - s) * 2 ^ s) * (w * C)
          = 2 ^ (n - s) * (2 ^ s * (w * C)) := by rw [Nat.mul_assoc]
      _ = 2 ^ (n - s) * ((2 ^ s * w) * C) := by
          congr 1
          rw [← Nat.mul_assoc]
      _ = (2 ^ (n - s) * (2 ^ s * w)) * C := by rw [← Nat.mul_assoc]
      _ = (2 ^ s * (2 ^ (n - s) * w)) * C := by rw [Nat.mul_left_comm]
      _ = 2 ^ s * ((2 ^ (n - s) * w) * C) := by rw [Nat.mul_assoc]
  conv =>
    lhs
    rw [Nat.mul_assoc]
  rw [hswap]
  rw [Nat.mul_add]

/-- The `n < s` LTE factorisation of `(2^n*w)*C + 2^s*u`. -/
theorem lteFactor_gt (n s w C u : Nat) (hsn : n < s) :
    (2 ^ n * w) * C + 2 ^ s * u = 2 ^ n * (w * C + 2 ^ (s - n) * u) := by
  have hsn' : s = (s - n) + n := by omega
  have hpow : 2 ^ s = 2 ^ (s - n) * 2 ^ n := by
    conv =>
      lhs
      rw [hsn']
      rw [Nat.pow_add]
  rw [hpow]
  rw [Nat.mul_add]
  conv =>
    lhs
    lhs
    rw [Nat.mul_assoc]
  rw [show 2 ^ (s - n) * 2 ^ n * u = 2 ^ n * (2 ^ (s - n) * u) from
        mul_assoc_left_comm (2 ^ (s - n)) (2 ^ n) u]

/-- Product of two odd numbers is odd. -/
theorem odd_mul_odd_mod_two (a b : Nat) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  rw [Nat.mul_mod]
  simp [ha, hb]

/-- Odd plus even is odd. -/
theorem odd_add_even_mod_two (a b : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) :
    (a + b) % 2 = 1 := by
  rw [Nat.add_mod]
  simp [ha, hb]

/-- `n = 2 + v2(a)`, the LTE exponent for `5^a - 1`. -/
def lteN (a : Nat) : Nat :=
  2 + twoValuation a

/-- Odd part of `5^a - 1` at the LTE exponent: `w = (5^a-1)/2^n`. -/
def lteW (a : Nat) : Nat :=
  (5 ^ a - 1) / 2 ^ lteN a

/-- Odd part of `C - 1` at valuation `s`: `u = (C-1)/2^s`. -/
def lteU (C s : Nat) : Nat :=
  (C - 1) / 2 ^ s

/-- Macro endpoint valuation `v2(5^a*C - 1)`. -/
def macroValue (a C : Nat) : Nat :=
  twoValuation (5 ^ a * C - 1)

/-- Extra cancellation when `s = n`:
`v2(w + u + 2^n*w*u) = v2((5^a*C-1)/2^n)`. -/
def lteExtra (a C : Nat) : Nat :=
  let n := lteN a
  let w := lteW a
  let u := lteU C n
  twoValuation (w + u + 2 ^ n * w * u)

/-- Exact LTE three-way valuation.  The hypotheses include the standard
LTE valuation `5^a-1 = 2^n*w` and oddness of `w,u`; these are the only
facts needed for the three-way identity. -/
def lteThreeWayStatement : Prop :=
  ∀ (a C s : Nat),
    1 ≤ a → 1 ≤ C → C % 2 = 1 →
    lteW a % 2 = 1 → lteU C s % 2 = 1 →
    C - 1 = 2 ^ s * lteU C s →
    5 ^ a - 1 = 2 ^ lteN a * lteW a →
    (s < lteN a → macroValue a C = s) ∧
    (lteN a < s → macroValue a C = lteN a) ∧
    (s = lteN a → macroValue a C = lteN a + lteExtra a C)

/-- Exact LTE three-way valuation with the correct hypotheses. -/
theorem lteThreeWayTheorem (a C s : Nat)
    (_ha : 1 ≤ a) (hC : 1 ≤ C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (huodd : lteU C s % 2 = 1)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a) :
    (s < lteN a → macroValue a C = s) ∧
    (lteN a < s → macroValue a C = lteN a) ∧
    (s = lteN a → macroValue a C = lteN a + lteExtra a C) := by
  constructor
  · intro hsn
    unfold macroValue
    have hsplit := macroNumerator_split a C
    rw [hsplit, hlte, hCu]
    have hfac := lteFactor_lt (lteN a) s (lteW a) C (lteU C s) hsn
    rw [hfac]
    have hnsub : 1 ≤ lteN a - s := by omega
    have hpow_even : (2 ^ (lteN a - s)) % 2 = 0 :=
      pow_two_even_mod (lteN a - s) hnsub
    have hwpow_even : ((2 ^ (lteN a - s)) * lteW a) % 2 = 0 :=
      even_mul_mod_two (2 ^ (lteN a - s)) (lteW a) hpow_even
    have hfirst_even : ((2 ^ (lteN a - s) * lteW a) * C) % 2 = 0 :=
      even_mul_mod_two (2 ^ (lteN a - s) * lteW a) C hwpow_even
    have hbodd : (2 ^ (lteN a - s) * lteW a * C + lteU C s) % 2 = 1 :=
      even_add_odd_mod_two (2 ^ (lteN a - s) * lteW a * C) (lteU C s) hfirst_even huodd
    have hv : twoValuation (2 ^ (lteN a - s) * lteW a * C + lteU C s) = 0 :=
      twoValuation_odd _ hbodd
    have hu_pos : 0 < lteU C s := by
      by_cases hz : lteU C s = 0
      · rw [hz] at huodd
        omega
      · exact Nat.pos_of_ne_zero hz
    have hpos : 0 < 2 ^ (lteN a - s) * lteW a * C + lteU C s := by omega
    calc
      twoValuation (2 ^ s * (2 ^ (lteN a - s) * lteW a * C + lteU C s))
          = s + twoValuation (2 ^ (lteN a - s) * lteW a * C + lteU C s) :=
            twoValuation_mul_two_pow s (2 ^ (lteN a - s) * lteW a * C + lteU C s) hpos
      _ = s + 0 := by rw [hv]
      _ = s := by omega
  · constructor
    · intro hsn
      unfold macroValue
      have hsplit := macroNumerator_split a C
      rw [hsplit, hlte, hCu]
      have hfac := lteFactor_gt (lteN a) s (lteW a) C (lteU C s) hsn
      rw [hfac]
      have hfirst_odd : (lteW a * C) % 2 = 1 :=
        odd_mul_odd_mod_two (lteW a) C hwodd hCodd
      have hns : 1 ≤ s - lteN a := by omega
      have hpow_even : (2 ^ (s - lteN a)) % 2 = 0 :=
        pow_two_even_mod (s - lteN a) hns
      have hsecond_even : ((2 ^ (s - lteN a)) * lteU C s) % 2 = 0 :=
        even_mul_mod_two (2 ^ (s - lteN a)) (lteU C s) hpow_even
      have hbodd : (lteW a * C + 2 ^ (s - lteN a) * lteU C s) % 2 = 1 :=
        odd_add_even_mod_two (lteW a * C) (2 ^ (s - lteN a) * lteU C s) hfirst_odd hsecond_even
      have hv : twoValuation (lteW a * C + 2 ^ (s - lteN a) * lteU C s) = 0 :=
        twoValuation_odd _ hbodd
      have hu_pos : 0 < lteU C s := by
        by_cases hz : lteU C s = 0
        · rw [hz] at huodd
          omega
        · exact Nat.pos_of_ne_zero hz
      have hpos : 0 < lteW a * C + 2 ^ (s - lteN a) * lteU C s := by omega
      calc
        twoValuation (2 ^ lteN a * (lteW a * C + 2 ^ (s - lteN a) * lteU C s))
            = lteN a + twoValuation (lteW a * C + 2 ^ (s - lteN a) * lteU C s) :=
              twoValuation_mul_two_pow (lteN a) (lteW a * C + 2 ^ (s - lteN a) * lteU C s) hpos
        _ = lteN a + 0 := by rw [hv]
        _ = lteN a := by omega
    · intro hsn
      have hs : s = lteN a := hsn
      have hCu' : C - 1 = 2 ^ lteN a * lteU C (lteN a) := by
        simpa [hs] using hCu
      have hCeq : C = 1 + 2 ^ lteN a * lteU C (lteN a) := by
        have h := Nat.sub_add_cancel hC
        rw [hCu'] at h
        omega
      unfold macroValue lteExtra
      have hsplit := macroNumerator_split a C
      rw [hsplit, hlte, hCu']
      have hprod : (2 ^ lteN a * lteW a) * C =
          (2 ^ lteN a * lteW a) * (1 + 2 ^ lteN a * lteU C (lteN a)) := by
        exact congrArg (fun x => (2 ^ lteN a * lteW a) * x) hCeq
      have hmain : (2 ^ lteN a * lteW a) * C + 2 ^ lteN a * lteU C (lteN a) =
          2 ^ lteN a * (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a)) := by
        rw [hprod]
        have hswap : (2 ^ lteN a * lteW a) * (2 ^ lteN a * lteU C (lteN a)) =
            2 ^ lteN a * (2 ^ lteN a * lteW a * lteU C (lteN a)) := by
          calc
            (2 ^ lteN a * lteW a) * (2 ^ lteN a * lteU C (lteN a))
                = ((2 ^ lteN a * lteW a) * 2 ^ lteN a) * lteU C (lteN a) := by
                  rw [← Nat.mul_assoc]
            _ = (2 ^ lteN a * (2 ^ lteN a * lteW a)) * lteU C (lteN a) := by
                  rw [Nat.mul_comm (2 ^ lteN a * lteW a) (2 ^ lteN a)]
            _ = 2 ^ lteN a * ((2 ^ lteN a * lteW a) * lteU C (lteN a)) := by
                  rw [Nat.mul_assoc]
            _ = 2 ^ lteN a * (2 ^ lteN a * (lteW a * lteU C (lteN a))) := by
                  congr 1
                  rw [Nat.mul_assoc]
            _ = 2 ^ lteN a * (2 ^ lteN a * lteW a * lteU C (lteN a)) := by
                  congr 1
                  rw [Nat.mul_assoc]
        rw [Nat.mul_add, Nat.mul_one]
        rw [hswap]
        rw [Nat.mul_add]
        rw [Nat.mul_add]
        omega
      rw [hmain]
      have hw_pos : 0 < lteW a := by
        by_cases hz : lteW a = 0
        · rw [hz] at hwodd
          omega
        · exact Nat.pos_of_ne_zero hz
      have hu_pos : 0 < lteU C (lteN a) := by
        by_cases hz : lteU C (lteN a) = 0
        · have hz' : lteU C s = 0 := by simpa [hs] using hz
          rw [hz'] at huodd
          omega
        · exact Nat.pos_of_ne_zero hz
      have hpos : 0 < lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a) := by
        omega
      calc
        twoValuation (2 ^ lteN a * (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a)))
            = lteN a + twoValuation (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a)) :=
              twoValuation_mul_two_pow (lteN a) (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a)) hpos
        _ = lteN a + twoValuation (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a)) := rfl

theorem lteThreeWayStatement_proof : lteThreeWayStatement := by
  intro a C s ha hC hCodd hwodd huodd hCu hlte
  exact lteThreeWayTheorem a C s ha hC hCodd hwodd huodd hCu hlte

/-- Natural-number form of macro success:
`v2(5^a*C-1) <= m+1`, equivalently `2^(m+2)` does not divide it. -/
def macroSuccessNat (a m C : Nat) : Prop :=
  ¬ (2 ^ (m + 2) ∣ (5 ^ a * C - 1))

/-- Macro success is exactly `v2(5^a*C-1) <= m+1`. -/
theorem macroSuccess_iff_val_le (a m C : Nat) (hC : 1 < C) :
    macroSuccessNat a m C ↔ macroValue a C ≤ m + 1 := by
  unfold macroSuccessNat macroValue
  have hpos : 0 < 5 ^ a * C - 1 := by
    have hC2 : 2 ≤ C := by omega
    have h5 : 1 ≤ 5 ^ a := by
      exact Nat.succ_le_of_lt (Nat.pow_pos (show 0 < 5 by omega))
    have hprod : 2 ≤ 5 ^ a * C := Nat.mul_le_mul h5 hC2
    omega
  rw [twoValuation_le_iff_not_dvd_pow (5 ^ a * C - 1) (m + 1) hpos]

/-- `lteU C s` is the odd part of `C-1` when `s = v2(C-1)`. -/
theorem lteU_eq_oddPart (C s : Nat) (hs : s = twoValuation (C - 1)) :
    lteU C s = oddPart (C - 1) := by
  unfold lteU oddPart
  rw [hs]

/-- K4 family A: `m <= v2(a)` iff macro success is `s <= m+1`. -/
theorem k4_familyA_iff (a m C : Nat)
    (ha : 1 ≤ a) (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hfam : m ≤ twoValuation a) :
    macroValue a C ≤ m + 1 ↔ twoValuation (C - 1) ≤ m + 1 := by
  let s := twoValuation (C - 1)
  have hn : lteN a = 2 + twoValuation a := rfl
  have hn_ge : m + 2 ≤ lteN a := by
    rw [hn]
    omega
  have hC1 : 1 ≤ C := by omega
  have hCpos : 0 < C - 1 := by omega
  have hdec := n_eq_two_pow_mul_oddPart (C - 1) hCpos
  have hCu : C - 1 = 2 ^ s * lteU C s := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact hdec
  have huodd : lteU C s % 2 = 1 := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hthree := lteThreeWayTheorem a C s ha hC1 hCodd hwodd huodd hCu hlte
  constructor
  · intro hval
    by_cases hs : s ≤ m + 1
    · exact hs
    · exfalso
      have hs_ge : m + 2 ≤ s := by omega
      dsimp [s] at hs_ge
      by_cases hsn : s < lteN a
      · have hV : macroValue a C = s := hthree.1 hsn
        rw [hV] at hval
        omega
      · have hns : lteN a ≤ s := by omega
        rcases Nat.eq_or_lt_of_le hns with heq | hlt
        · have hV : macroValue a C = lteN a + lteExtra a C := hthree.2.2 heq.symm
          rw [hV] at hval
          omega
        · have hV : macroValue a C = lteN a := hthree.2.1 hlt
          rw [hV] at hval
          omega
  · intro hs
    by_cases hsn : s < lteN a
    · have hV : macroValue a C = s := hthree.1 hsn
      rw [hV]
      exact hs
    · have hns : lteN a ≤ s := by omega
      exfalso
      omega

/-- K4 family B: `v2(a) < m` iff macro success is `s ≠ n` or
`(s = n and extra <= m+1-n)`. -/
theorem k4_familyB_iff (a m C : Nat)
    (ha : 1 ≤ a) (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hfam : ¬ m ≤ twoValuation a) :
    macroValue a C ≤ m + 1 ↔
      (twoValuation (C - 1) ≠ lteN a ∨
       (twoValuation (C - 1) = lteN a ∧ lteExtra a C ≤ m + 1 - lteN a)) := by
  let s := twoValuation (C - 1)
  have hn : lteN a = 2 + twoValuation a := rfl
  have hn_le : lteN a ≤ m + 1 := by
    rw [hn]
    omega
  have hC1 : 1 ≤ C := by omega
  have hCpos : 0 < C - 1 := by omega
  have hdec := n_eq_two_pow_mul_oddPart (C - 1) hCpos
  have hCu : C - 1 = 2 ^ s * lteU C s := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact hdec
  have huodd : lteU C s % 2 = 1 := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hthree := lteThreeWayTheorem a C s ha hC1 hCodd hwodd huodd hCu hlte
  constructor
  · intro hval
    by_cases hsn : s = lteN a
    · right
      constructor
      · exact hsn
      · have hV : macroValue a C = lteN a + lteExtra a C := hthree.2.2 hsn
        rw [hV] at hval
        omega
    · left
      exact hsn
  · intro hdisj
    rcases hdisj with hsne | hseq
    · by_cases hlt : s < lteN a
      · have hV : macroValue a C = s := hthree.1 hlt
        rw [hV]
        omega
      · have hns : lteN a ≤ s := by omega
        rcases Nat.eq_or_lt_of_le hns with heq | hgt
        · exfalso
          exact hsne heq.symm
        · have hV : macroValue a C = lteN a := hthree.2.1 hgt
          rw [hV]
          exact hn_le
    · rcases hseq with ⟨hsn, hextra⟩
      have hV : macroValue a C = lteN a + lteExtra a C := hthree.2.2 hsn
      rw [hV]
      omega

/-- K4 in the two families.  Family A (`m ≤ v2 a`) requires
`s ≤ m+1`; family B (`v2 a < m`) requires `s ≠ n` or
`extra ≤ m+1-n`. -/
def k4Statement (a m C : Nat) : Prop :=
  let n := lteN a
  let s := twoValuation (C - 1)
  if m ≤ twoValuation a then
    s ≤ m + 1
  else
    s ≠ n ∨ (s = n ∧ lteExtra a C ≤ m + 1 - n)

/-- K4 is equivalent to the macro endpoint inequality.  Proved by
`k4EquivalentStatement_proof` using `k4_familyA_iff` and
`k4_familyB_iff`. -/
def k4EquivalentStatement : Prop :=
  ∀ (a m C : Nat),
    1 ≤ a → 1 < C → C % 2 = 1 →
    lteW a % 2 = 1 →
    5 ^ a - 1 = 2 ^ lteN a * lteW a →
    (macroSuccessNat a m C ↔ k4Statement a m C)

theorem k4EquivalentStatement_proof : k4EquivalentStatement := by
  change ∀ (a m C : Nat),
    1 ≤ a → 1 < C → C % 2 = 1 →
    lteW a % 2 = 1 →
    5 ^ a - 1 = 2 ^ lteN a * lteW a →
    (macroSuccessNat a m C ↔ k4Statement a m C)
  intro a
  intro m
  intro C
  intro ha
  intro hC
  intro hCodd
  intro hwodd
  intro hlte
  rw [macroSuccess_iff_val_le a m C hC]
  unfold k4Statement
  by_cases hfam : m ≤ twoValuation a
  · rw [if_pos hfam]
    exact k4_familyA_iff a m C ha hC hCodd hwodd hlte hfam
  · rw [if_neg hfam]
    exact k4_familyB_iff a m C ha hC hCodd hwodd hlte hfam

/-- Sufficient K4 reduction: L1 + L2 + K4B imply macro success.
  L1: `m >= v2(a)+1`; L2: `s <= m+2`; K4B: at `s=n` the extra
  cancellation is bounded.  The three statements are open targets. -/
def k4SufficientStatement : Prop :=
  ∀ (a C m : Nat),
    1 ≤ a → 1 < C → C % 2 = 1 →
    lteW a % 2 = 1 →
    5 ^ a - 1 = 2 ^ lteN a * lteW a →
    twoValuation a + 1 ≤ m →
    twoValuation (C - 1) ≤ m + 2 →
    (twoValuation (C - 1) = lteN a → lteExtra a C ≤ m + 1 - lteN a) →
    macroSuccessNat a m C

theorem k4SufficientStatement_proof : k4SufficientStatement := by
  intro a C m ha hC hCodd hwodd hlte hL1 hL2 hK4B
  rw [macroSuccess_iff_val_le a m C hC]
  let s := twoValuation (C - 1)
  have hCpos : 0 < C - 1 := by omega
  have hdec := n_eq_two_pow_mul_oddPart (C - 1) hCpos
  have hCu : C - 1 = 2 ^ s * lteU C s := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact hdec
  have huodd : lteU C s % 2 = 1 := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hthree := lteThreeWayTheorem a C s ha (show 1 ≤ C by omega) hCodd hwodd huodd hCu hlte
  by_cases hsn : s < lteN a
  · have hV : macroValue a C = s := hthree.1 hsn
    rw [hV]
    have hs_le : s ≤ twoValuation a + 1 := by
      have hn : lteN a = 2 + twoValuation a := rfl
      rw [hn] at hsn
      omega
    omega
  · have hns : lteN a ≤ s := by omega
    rcases Nat.eq_or_lt_of_le hns with heq | hlt
    · have hV : macroValue a C = lteN a + lteExtra a C := hthree.2.2 heq.symm
      rw [hV]
      have hextra : lteExtra a C ≤ m + 1 - lteN a := hK4B heq.symm
      have hn_le : lteN a ≤ m + 1 := by
        have hn : lteN a = 2 + twoValuation a := rfl
        rw [hn]
        omega
      omega
    · have hV : macroValue a C = lteN a := hthree.2.1 hlt
      rw [hV]
      have hn_le : lteN a ≤ m + 1 := by
        have hn : lteN a = 2 + twoValuation a := rfl
        rw [hn]
        omega
      exact hn_le

/-- `C = 1` is impossible: `5*r+3 = 4^a` has no solution modulo 5,
so `v2(C-1)` is well-defined. -/
def macroOddPartNotOneStatement : Prop :=
  ∀ (a r : Nat),
    (5 * r + 3) % 2 ^ (2 * a) = 0 →
    ¬ ((5 * r + 3) / 2 ^ (2 * a) = 1)

/-- `4^a` is congruent to 1 or 4 modulo 5. -/
theorem four_pow_mod_five (a : Nat) : 4 ^ a % 5 = 1 ∨ 4 ^ a % 5 = 4 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.pow_succ]
      rw [Nat.mul_mod]
      cases ih with
      | inl h => rw [h]; simp
      | inr h => rw [h]; simp

theorem macroOddPartNotOneStatement_proof : macroOddPartNotOneStatement := by
  intro a r hdiv hquot
  have hdiv' : 2 ^ (2 * a) ∣ 5 * r + 3 := Nat.dvd_iff_mod_eq_zero.mpr hdiv
  have h : 5 * r + 3 = 2 ^ (2 * a) := by
    calc
      5 * r + 3 = (5 * r + 3) / 2 ^ (2 * a) * 2 ^ (2 * a) :=
        (Nat.div_mul_cancel hdiv').symm
      _ = 1 * 2 ^ (2 * a) := by rw [hquot]
      _ = 2 ^ (2 * a) := by simp
  have hpow : 2 ^ (2 * a) = 4 ^ a := by
    calc
      2 ^ (2 * a) = (2 ^ 2) ^ a := by
        rw [← Nat.pow_mul]
      _ = 4 ^ a := by simp
  have h45 : 4 ^ a % 5 = 1 ∨ 4 ^ a % 5 = 4 := four_pow_mod_five a
  have h3 : (5 * r + 3) % 5 = 3 := by omega
  have hc : 3 = (2 ^ (2 * a)) % 5 := by
    rw [← h3]
    rw [h]
  rw [hpow] at hc
  cases h45 with
  | inl h1 => rw [h1] at hc; omega
  | inr h4 => rw [h4] at hc; omega

/-- Exact macro-chain recurrence between consecutive macro starts:
`C' = (5^a*C-1)/2^(2a'-1)`. -/
def macroChainRecurrenceStatement : Prop :=
  ∀ (a a' C : Nat),
    1 ≤ a → 1 ≤ a' → 1 < C → C % 2 = 1 →
    let V := macroValue a C
    V = 2 * a' - 1 →
    ((5 ^ a * C - 1) / 2 ^ V) % 2 = 1

theorem macroChainRecurrenceStatement_proof : macroChainRecurrenceStatement := by
  intro a a' C ha ha' hC hCodd
  dsimp
  intro hV
  change ((5 ^ a * C - 1) / 2 ^ macroValue a C) % 2 = 1
  unfold macroValue
  have hpos : 0 < 5 ^ a * C - 1 := by
    have hC2 : 2 ≤ C := by omega
    have h5 : 5 ≤ 5 ^ a := by
      have h := Nat.pow_le_pow_right (show 0 < 5 by omega) ha
      simpa using h
    have hprod : 5 * 2 ≤ 5 ^ a * C := Nat.mul_le_mul h5 hC2
    omega
  exact oddPart_odd_of_pos (5 ^ a * C - 1) hpos

/-- Next macro positive odd part after dividing out `V`. -/
def macroNextC (a C V : Nat) : Nat :=
  (5 ^ a * C - 1) / 2 ^ V

/-- Exact three-case carry recurrence for `s' = v2(C'-1)` along the
macro chain.  This is the analytic replacement of the old per-step
carry bit.  It is a pure identity conditional on the standard LTE
oddness hypothesis `lteW a % 2 = 1`. -/
def macroChainSCasesStatement : Prop :=
  ∀ (a a' C : Nat),
    1 ≤ a → 1 ≤ a' → 1 < C → C % 2 = 1 →
    lteW a % 2 = 1 →
    let n := lteN a
    let w := lteW a
    let s := twoValuation (C - 1)
    let u := lteU C s
    let V := macroValue a C
    5 ^ a - 1 = 2 ^ n * w →
    V = 2 * a' - 1 →
    (s < n →
      s = V ∧
      twoValuation (macroNextC a C V - 1) =
        twoValuation ((u - 1) + 2 ^ (n - s) * w * (1 + 2 ^ s * u))) ∧
    (n < s →
      n = V ∧
      twoValuation (macroNextC a C V - 1) =
        twoValuation ((w - 1) + 2 ^ (s - n) * u * (1 + 2 ^ n * w))) ∧
    (s = n →
      macroValue a C = n + lteExtra a C ∧
      (macroNextC a C V) % 2 = 1)

/-- When `s < n`, the next odd part is `2^(n-s)*w*C + u`. -/
theorem macroNextC_lt (a C s : Nat)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hsn : s < lteN a) :
    macroNextC a C s = 2 ^ (lteN a - s) * lteW a * C + lteU C s := by
  unfold macroNextC
  have hsplit := macroNumerator_split a C
  rw [hsplit, hlte, hCu]
  have hfac := lteFactor_lt (lteN a) s (lteW a) C (lteU C s) hsn
  rw [hfac]
  have hpos : 0 < 2 ^ s := Nat.pow_pos (show 0 < 2 by omega)
  exact Nat.mul_div_right (2 ^ (lteN a - s) * lteW a * C + lteU C s) (m := 2 ^ s) hpos

/-- When `n < s`, the next odd part is `w*C + 2^(s-n)*u`. -/
theorem macroNextC_gt (a C s : Nat)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hsn : lteN a < s) :
    macroNextC a C (lteN a) = lteW a * C + 2 ^ (s - lteN a) * lteU C s := by
  unfold macroNextC
  have hsplit := macroNumerator_split a C
  rw [hsplit, hlte, hCu]
  have hfac := lteFactor_gt (lteN a) s (lteW a) C (lteU C s) hsn
  rw [hfac]
  have hpos : 0 < 2 ^ lteN a := Nat.pow_pos (show 0 < 2 by omega)
  exact Nat.mul_div_right (lteW a * C + 2 ^ (s - lteN a) * lteU C s) (m := 2 ^ lteN a) hpos

/-- `s < n`: exact subtraction identity for `C' - 1`. -/
theorem macroNextC_lt_sub (n s w C u : Nat)
    (hC : C = 1 + 2 ^ s * u)
    (hu : 0 < u) :
    (2 ^ (n - s) * w * C + u) - 1 =
      (u - 1) + 2 ^ (n - s) * w * (1 + 2 ^ s * u) := by
  calc
    (2 ^ (n - s) * w * C + u) - 1 = (u - 1) + 2 ^ (n - s) * w * C := by
      rw [hC, Nat.mul_add, Nat.mul_one]
      have hsum : 0 < 2 ^ (n - s) * w * (1 + 2 ^ s * u) + u := by omega
      omega
    _ = (u - 1) + 2 ^ (n - s) * w * (1 + 2 ^ s * u) := by
      rw [hC, Nat.mul_add, Nat.mul_one]

/-- `n < s`: exact subtraction identity for `C' - 1`. -/
theorem macroNextC_gt_sub (n s w C u : Nat)
    (hns : n < s)
    (hC : C = 1 + 2 ^ s * u)
    (hw : 0 < w) :
    (w * C + 2 ^ (s - n) * u) - 1 =
      (w - 1) + 2 ^ (s - n) * u * (1 + 2 ^ n * w) := by
  have hpow : 2 ^ (s - n) * 2 ^ n = 2 ^ s := by
    rw [← Nat.pow_add]
    rw [show (s - n) + n = s by omega]
  have hcross : 2 ^ (s - n) * u * (2 ^ n * w) = w * (2 ^ s * u) := by
    calc
      2 ^ (s - n) * u * (2 ^ n * w)
          = 2 ^ (s - n) * (u * (2 ^ n * w)) := by rw [Nat.mul_assoc]
      _ = 2 ^ (s - n) * ((u * 2 ^ n) * w) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = 2 ^ (s - n) * ((2 ^ n * u) * w) := by
          congr 1
          rw [Nat.mul_comm u (2 ^ n)]
      _ = 2 ^ (s - n) * (2 ^ n * (u * w)) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = (2 ^ (s - n) * 2 ^ n) * (u * w) := by rw [← Nat.mul_assoc]
      _ = 2 ^ s * (u * w) := by rw [hpow]
      _ = w * (2 ^ s * u) := by
          rw [← Nat.mul_assoc]
          rw [Nat.mul_comm]
  have hrhs : 2 ^ (s - n) * u * (1 + 2 ^ n * w) =
      w * (2 ^ s * u) + 2 ^ (s - n) * u := by
    rw [Nat.mul_add, Nat.mul_one]
    rw [← hcross]
    rw [Nat.add_comm]
  rw [hC, Nat.mul_add, Nat.mul_one]
  rw [Nat.add_assoc]
  have hsplit : (w + (w * (2 ^ s * u) + 2 ^ (s - n) * u)) - 1 =
      (w - 1) + (w * (2 ^ s * u) + 2 ^ (s - n) * u) := by
    have hw1 : 1 ≤ w := by omega
    exact Nat.sub_add_comm hw1
  rw [hsplit, hrhs]

/-- Explicit terminal odd part in the `s < n` case:
`C' = 2^(n-s)*w + 2^n*w*u + u`. -/
theorem macroNextC_lt_expand (a C s : Nat)
    (hC : 1 < C)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hsn : s < lteN a) :
    macroNextC a C s =
      2 ^ (lteN a - s) * lteW a + 2 ^ lteN a * lteW a * lteU C s + lteU C s := by
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hC' : macroNextC a C s = 2 ^ (lteN a - s) * lteW a * C + lteU C s :=
    macroNextC_lt a C s hlte hCu hsn
  rw [hC']
  conv =>
    lhs
    lhs
    rw [hCeq]
  rw [Nat.mul_add, Nat.mul_one]
  have hpow : 2 ^ (lteN a - s) * 2 ^ s = 2 ^ lteN a := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hprod : 2 ^ (lteN a - s) * lteW a * (2 ^ s * lteU C s) =
      2 ^ lteN a * lteW a * lteU C s := by
    calc
      (2 ^ (lteN a - s) * lteW a) * (2 ^ s * lteU C s)
          = 2 ^ (lteN a - s) * (lteW a * (2 ^ s * lteU C s)) := by rw [Nat.mul_assoc]
      _ = 2 ^ (lteN a - s) * ((lteW a * 2 ^ s) * lteU C s) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = 2 ^ (lteN a - s) * ((2 ^ s * lteW a) * lteU C s) := by
          congr 1
          rw [Nat.mul_comm (lteW a) (2 ^ s)]
      _ = 2 ^ (lteN a - s) * (2 ^ s * (lteW a * lteU C s)) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = (2 ^ (lteN a - s) * 2 ^ s) * (lteW a * lteU C s) := by rw [← Nat.mul_assoc]
      _ = 2 ^ lteN a * (lteW a * lteU C s) := by rw [hpow]
      _ = 2 ^ lteN a * lteW a * lteU C s := by rw [Nat.mul_assoc]
  rw [hprod]

/-- Explicit terminal odd part in the `n < s` case:
`C' = w + 2^(s-n)*u*(1+2^n*w)`. -/
theorem macroNextC_gt_expand (a C s : Nat)
    (hC : 1 < C)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hns : lteN a < s) :
    macroNextC a C (lteN a) =
      lteW a + 2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a) := by
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hC' : macroNextC a C (lteN a) = lteW a * C + 2 ^ (s - lteN a) * lteU C s :=
    macroNextC_gt a C s hlte hCu hns
  rw [hC']
  conv =>
    lhs
    lhs
    rw [hCeq]
  rw [Nat.mul_add, Nat.mul_one]
  have hpow : 2 ^ (s - lteN a) * 2 ^ lteN a = 2 ^ s := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hcross : 2 ^ (s - lteN a) * lteU C s * (2 ^ lteN a * lteW a) =
      lteW a * (2 ^ s * lteU C s) := by
    calc
      2 ^ (s - lteN a) * lteU C s * (2 ^ lteN a * lteW a)
          = 2 ^ (s - lteN a) * (lteU C s * (2 ^ lteN a * lteW a)) := by rw [Nat.mul_assoc]
      _ = 2 ^ (s - lteN a) * ((lteU C s * 2 ^ lteN a) * lteW a) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = 2 ^ (s - lteN a) * ((2 ^ lteN a * lteU C s) * lteW a) := by
          congr 1
          rw [Nat.mul_comm (lteU C s) (2 ^ lteN a)]
      _ = 2 ^ (s - lteN a) * (2 ^ lteN a * (lteU C s * lteW a)) := by
          congr 1
          rw [Nat.mul_assoc]
      _ = (2 ^ (s - lteN a) * 2 ^ lteN a) * (lteU C s * lteW a) := by rw [← Nat.mul_assoc]
      _ = 2 ^ s * (lteU C s * lteW a) := by rw [hpow]
      _ = lteW a * (2 ^ s * lteU C s) := by
          rw [← Nat.mul_assoc]
          rw [Nat.mul_comm]
  have hrhs : 2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a) =
      lteW a * (2 ^ s * lteU C s) + 2 ^ (s - lteN a) * lteU C s := by
    rw [Nat.mul_add, Nat.mul_one]
    rw [← hcross]
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
  rw [hrhs]

theorem macroChainSCasesStatement_proof : macroChainSCasesStatement := by
  intro a a' C ha ha' hC hCodd hwodd
  dsimp
  intro hltel hV
  let s := twoValuation (C - 1)
  have hCpos : 0 < C - 1 := by omega
  have hdec := n_eq_two_pow_mul_oddPart (C - 1) hCpos
  have hCu : C - 1 = 2 ^ s * lteU C s := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact hdec
  have huodd : lteU C s % 2 = 1 := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hu : 0 < lteU C s := by
    by_cases hz : lteU C s = 0
    · rw [hz] at huodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hw : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hltel
      have hp : 0 < 5 ^ a - 1 := by
        have h5 : 5 ≤ 5 ^ a := by
          exact Nat.pow_le_pow_right (show 0 < 5 by omega) ha
        omega
      omega
    · exact Nat.pos_of_ne_zero hz
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hthree := lteThreeWayTheorem a C s ha (show 1 ≤ C by omega) hCodd hwodd huodd hCu hltel
  constructor
  · intro hsn
    constructor
    · have hVs := hthree.1 hsn
      symm
      exact hVs
    · have hC' : macroNextC a C (macroValue a C) = 2 ^ (lteN a - s) * lteW a * C + lteU C s := by
        rw [hthree.1 hsn]
        exact macroNextC_lt a C s hltel hCu hsn
      have hsub := macroNextC_lt_sub (lteN a) s (lteW a) C (lteU C s) hCeq hu
      calc
        twoValuation (macroNextC a C (macroValue a C) - 1)
            = twoValuation ((2 ^ (lteN a - s) * lteW a * C + lteU C s) - 1) := by
              rw [hC']
        _ = twoValuation ((lteU C s - 1) + 2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s)) := by
              rw [hsub]
  · constructor
    · intro hns
      constructor
      · have hVn := hthree.2.1 hns
        exact hVn.symm
      · have hC' : macroNextC a C (macroValue a C) = lteW a * C + 2 ^ (s - lteN a) * lteU C s := by
          rw [hthree.2.1 hns]
          exact macroNextC_gt a C s hltel hCu hns
        have hsub := macroNextC_gt_sub (lteN a) s (lteW a) C (lteU C s) hns hCeq hw
        calc
          twoValuation (macroNextC a C (macroValue a C) - 1)
              = twoValuation ((lteW a * C + 2 ^ (s - lteN a) * lteU C s) - 1) := by
                rw [hC']
          _ = twoValuation ((lteW a - 1) + 2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a)) := by
                rw [hsub]
    · intro hsn
      constructor
      · exact hthree.2.2 hsn
      · have hodd := macroChainRecurrenceStatement_proof a a' C ha ha' hC hCodd hV
        simpa [macroNextC] using hodd

/-- In the `s < n` case, if `v2(u-1) < n-s`, the next valuation is
`v2(u-1)`: the carry term cannot cancel at a higher level. -/
theorem macroNextC_lt_val_of_u_min (a C s : Nat)
    (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (huodd : lteU C s % 2 = 1)
    (hsn : s < lteN a)
    (hs : 1 ≤ s)
    (hu : 1 < lteU C s)
    (h : twoValuation (lteU C s - 1) < lteN a - s) :
    twoValuation (macroNextC a C s - 1) = twoValuation (lteU C s - 1) := by
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hC' : macroNextC a C s = 2 ^ (lteN a - s) * lteW a * C + lteU C s :=
    macroNextC_lt a C s hlte hCu hsn
  have hsub1 := macroNextC_lt_sub (lteN a) s (lteW a) C (lteU C s) hCeq (by omega)
  rw [hC']
  rw [hsub1]
  have hodd1 : (1 + 2 ^ s * lteU C s) % 2 = 1 := by
    have heven : (2 ^ s * lteU C s) % 2 = 0 := by
      have hp : (2 ^ s) % 2 = 0 := pow_two_even_mod s hs
      exact even_mul_mod_two (2 ^ s) (lteU C s) hp
    rw [Nat.add_comm]
    exact even_add_odd_mod_two (2 ^ s * lteU C s) 1 heven (by decide)
  have hw1odd : (lteW a * (1 + 2 ^ s * lteU C s)) % 2 = 1 :=
    odd_mul_odd_mod_two (lteW a) (1 + 2 ^ s * lteU C s) hwodd hodd1
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hBpos : 0 < 2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s) := by
    have hp1 : 0 < 2 ^ (lteN a - s) * lteW a :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hwpos
    exact Nat.mul_pos hp1 (by omega)
  have hBval : twoValuation (2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s)) = lteN a - s := by
    have hB : 2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s) =
        2 ^ (lteN a - s) * (lteW a * (1 + 2 ^ s * lteU C s)) := by
      rw [Nat.mul_assoc]
    rw [hB]
    exact twoValuation_mul_two_pow_eq (lteN a - s) (lteW a * (1 + 2 ^ s * lteU C s)) hw1odd
  have hx : 0 < lteU C s - 1 := by omega
  have h' : twoValuation (lteU C s - 1) <
      twoValuation (2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s)) := by
    rw [hBval]
    exact h
  have hres := twoValuation_add_eq_of_lt (lteU C s - 1)
      (2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s * lteU C s)) hx hBpos h'
  exact hres

/-- In the `s < n` case with `u = 1`, the next valuation is exactly
`n-s`: there is no odd part of `u-1` to carry. -/
theorem macroNextC_lt_val_of_u_eq_one (a C s : Nat)
    (hC : 1 < C)
    (hwodd : lteW a % 2 = 1)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (hsn : s < lteN a)
    (hs : 1 ≤ s)
    (hu1 : lteU C s = 1) :
    twoValuation (macroNextC a C s - 1) = lteN a - s := by
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hC' : macroNextC a C s = 2 ^ (lteN a - s) * lteW a * C + lteU C s :=
    macroNextC_lt a C s hlte hCu hsn
  have hsub1 := macroNextC_lt_sub (lteN a) s (lteW a) C (lteU C s) hCeq (by omega)
  rw [hC', hsub1, hu1]
  simp
  have hodd1 : (1 + 2 ^ s) % 2 = 1 := by
    have heven : (2 ^ s) % 2 = 0 := pow_two_even_mod s hs
    rw [Nat.add_comm]
    exact even_add_odd_mod_two (2 ^ s) 1 heven (by decide)
  have hw1odd : (lteW a * (1 + 2 ^ s)) % 2 = 1 :=
    odd_mul_odd_mod_two (lteW a) (1 + 2 ^ s) hwodd hodd1
  have hB : 2 ^ (lteN a - s) * lteW a * (1 + 2 ^ s) =
      2 ^ (lteN a - s) * (lteW a * (1 + 2 ^ s)) := by
    rw [Nat.mul_assoc]
  rw [hB]
  exact twoValuation_mul_two_pow_eq (lteN a - s) (lteW a * (1 + 2 ^ s)) hw1odd

/-- In the `n < s` case, if `v2(w-1) < s-n`, the next valuation is
`v2(w-1)`. -/
theorem macroNextC_gt_val_of_w_min (a C s : Nat)
    (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hCu : C - 1 = 2 ^ s * lteU C s)
    (huodd : lteU C s % 2 = 1)
    (hns : lteN a < s)
    (hw : 1 < lteW a)
    (h : twoValuation (lteW a - 1) < s - lteN a) :
    twoValuation (macroNextC a C (lteN a) - 1) = twoValuation (lteW a - 1) := by
  have hCeq : C = 1 + 2 ^ s * lteU C s := by
    have hsub := Nat.sub_add_cancel (show 1 ≤ C by omega)
    rw [hCu] at hsub
    omega
  have hC' : macroNextC a C (lteN a) = lteW a * C + 2 ^ (s - lteN a) * lteU C s :=
    macroNextC_gt a C s hlte hCu hns
  have hsub1 := macroNextC_gt_sub (lteN a) s (lteW a) C (lteU C s) hns hCeq (by omega)
  rw [hC']
  rw [hsub1]
  have hnpos : 1 ≤ lteN a := by
    have hn : lteN a = 2 + twoValuation a := rfl
    rw [hn]
    omega
  have hodd1 : (1 + 2 ^ lteN a * lteW a) % 2 = 1 := by
    have heven : (2 ^ lteN a * lteW a) % 2 = 0 := by
      have hp : (2 ^ lteN a) % 2 = 0 := pow_two_even_mod (lteN a) hnpos
      exact even_mul_mod_two (2 ^ lteN a) (lteW a) hp
    rw [Nat.add_comm]
    exact even_add_odd_mod_two (2 ^ lteN a * lteW a) 1 heven (by decide)
  have hu1odd : (lteU C s * (1 + 2 ^ lteN a * lteW a)) % 2 = 1 :=
    odd_mul_odd_mod_two (lteU C s) (1 + 2 ^ lteN a * lteW a) huodd hodd1
  have hu1pos : 0 < lteU C s := by
    by_cases hz : lteU C s = 0
    · rw [hz] at huodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hBpos : 0 < 2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a) := by
    have hp1 : 0 < 2 ^ (s - lteN a) * lteU C s :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hu1pos
    exact Nat.mul_pos hp1 (by omega)
  have hBval : twoValuation (2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a)) = s - lteN a := by
    have hB : 2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a) =
        2 ^ (s - lteN a) * (lteU C s * (1 + 2 ^ lteN a * lteW a)) := by
      rw [Nat.mul_assoc]
    rw [hB]
    exact twoValuation_mul_two_pow_eq (s - lteN a) (lteU C s * (1 + 2 ^ lteN a * lteW a)) hu1odd
  have hx : 0 < lteW a - 1 := by omega
  have h' : twoValuation (lteW a - 1) <
      twoValuation (2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a)) := by
    rw [hBval]
    exact h
  have hres := twoValuation_add_eq_of_lt (lteW a - 1)
      (2 ^ (s - lteN a) * lteU C s * (1 + 2 ^ lteN a * lteW a)) hx hBpos h'
  exact hres

/-- In the `s = n` case, when `v2(w+u) < n`, the extra cancellation
is exactly `v2(w+u)`: `lteExtra = v2(w+u+2^n*w*u)`. -/
theorem lteExtra_eq_val_of_lt (a C s : Nat)
    (hwodd : lteW a % 2 = 1)
    (huodd : lteU C s % 2 = 1)
    (hsn : s = lteN a)
    (h : twoValuation (lteW a + lteU C s) < lteN a) :
    lteExtra a C = twoValuation (lteW a + lteU C s) := by
  unfold lteExtra
  dsimp
  have huodd' : lteU C (lteN a) % 2 = 1 := by
    simpa [hsn] using huodd
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hupos : 0 < lteU C (lteN a) := by
    by_cases hz : lteU C (lteN a) = 0
    · rw [hz] at huodd'
      omega
    · exact Nat.pos_of_ne_zero hz
  have hx : 0 < lteW a + lteU C (lteN a) := by omega
  have hy : 0 < 2 ^ lteN a * lteW a * lteU C (lteN a) := by
    have hp1 : 0 < 2 ^ lteN a * lteW a :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hwpos
    exact Nat.mul_pos hp1 hupos
  have hwuo : (lteW a * lteU C (lteN a)) % 2 = 1 :=
    odd_mul_odd_mod_two (lteW a) (lteU C (lteN a)) hwodd huodd'
  have hyval : twoValuation (2 ^ lteN a * lteW a * lteU C (lteN a)) = lteN a := by
    have hB : 2 ^ lteN a * lteW a * lteU C (lteN a) =
        2 ^ lteN a * (lteW a * lteU C (lteN a)) := by
      rw [Nat.mul_assoc]
    rw [hB]
    exact twoValuation_mul_two_pow_eq (lteN a) (lteW a * lteU C (lteN a)) hwuo
  have h' : twoValuation (lteW a + lteU C (lteN a)) <
      twoValuation (2 ^ lteN a * lteW a * lteU C (lteN a)) := by
    rw [hyval]
    simpa [hsn] using h
  have hres := twoValuation_add_eq_of_lt (lteW a + lteU C (lteN a))
      (2 ^ lteN a * lteW a * lteU C (lteN a)) hx hy h'
  simpa [hsn] using hres

/-- In the `s = n` case, when `n < v2(w+u)`, the extra cancellation is
exactly `n`. -/
theorem lteExtra_eq_n_of_gt (a C s : Nat)
    (hwodd : lteW a % 2 = 1)
    (huodd : lteU C s % 2 = 1)
    (hsn : s = lteN a)
    (h : lteN a < twoValuation (lteW a + lteU C s)) :
    lteExtra a C = lteN a := by
  unfold lteExtra
  dsimp
  have huodd' : lteU C (lteN a) % 2 = 1 := by
    simpa [hsn] using huodd
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hupos : 0 < lteU C (lteN a) := by
    by_cases hz : lteU C (lteN a) = 0
    · rw [hz] at huodd'
      omega
    · exact Nat.pos_of_ne_zero hz
  have hx : 0 < lteW a + lteU C (lteN a) := by omega
  have hy : 0 < 2 ^ lteN a * lteW a * lteU C (lteN a) := by
    have hp1 : 0 < 2 ^ lteN a * lteW a :=
      Nat.mul_pos (Nat.pow_pos (by decide)) hwpos
    exact Nat.mul_pos hp1 hupos
  have hwuo : (lteW a * lteU C (lteN a)) % 2 = 1 :=
    odd_mul_odd_mod_two (lteW a) (lteU C (lteN a)) hwodd huodd'
  have hyval : twoValuation (2 ^ lteN a * lteW a * lteU C (lteN a)) = lteN a := by
    have hB : 2 ^ lteN a * lteW a * lteU C (lteN a) =
        2 ^ lteN a * (lteW a * lteU C (lteN a)) := by
      rw [Nat.mul_assoc]
    rw [hB]
    exact twoValuation_mul_two_pow_eq (lteN a) (lteW a * lteU C (lteN a)) hwuo
  have h' : twoValuation (2 ^ lteN a * lteW a * lteU C (lteN a)) <
      twoValuation (lteW a + lteU C (lteN a)) := by
    rw [hyval]
    simpa [hsn] using h
  have hres := twoValuation_add_eq_of_gt (lteW a + lteU C (lteN a))
      (2 ^ lteN a * lteW a * lteU C (lteN a)) hx hy h'
  rw [hres]
  exact hyval

/-- In the `s = n` case with `v2(w+u) = n`, the extra cancellation has
the exact form `n + v2(oddPart(w+u) + w*u)`.  This is the only case
where the carry can grow beyond `n`. -/
theorem lteExtra_eq_add_of_eq (a C s : Nat)
    (hwodd : lteW a % 2 = 1)
    (huodd : lteU C s % 2 = 1)
    (hsn : s = lteN a)
    (h : twoValuation (lteW a + lteU C s) = lteN a) :
    lteExtra a C =
      lteN a + twoValuation (oddPart (lteW a + lteU C s) + lteW a * lteU C s) := by
  unfold lteExtra
  dsimp
  have huodd' : lteU C (lteN a) % 2 = 1 := by
    simpa [hsn] using huodd
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hupos : 0 < lteU C (lteN a) := by
    by_cases hz : lteU C (lteN a) = 0
    · rw [hz] at huodd'
      omega
    · exact Nat.pos_of_ne_zero hz
  have hxpos : 0 < lteW a + lteU C (lteN a) := by omega
  have hxdec := n_eq_two_pow_mul_oddPart (lteW a + lteU C (lteN a)) hxpos
  have hx : twoValuation (lteW a + lteU C (lteN a)) = lteN a := by
    simpa [← hsn] using h
  have hxpow : lteW a + lteU C (lteN a) =
      2 ^ lteN a * oddPart (lteW a + lteU C (lteN a)) := by
    simpa [hx] using hxdec
  have h2 : 2 ^ lteN a * lteW a * lteU C (lteN a) =
      2 ^ lteN a * (lteW a * lteU C (lteN a)) := by
    rw [Nat.mul_assoc]
  have hsum : lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a) =
      2 ^ lteN a * (oddPart (lteW a + lteU C (lteN a)) + lteW a * lteU C (lteN a)) := by
    conv =>
      lhs
      rw [hxpow, h2]
    rw [← Nat.mul_add]
  have hoddpos : 0 < oddPart (lteW a + lteU C (lteN a)) := by
    by_cases hz : oddPart (lteW a + lteU C (lteN a)) = 0
    · have hxodd := oddPart_odd_of_pos (lteW a + lteU C (lteN a)) hxpos
      rw [hz] at hxodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hwupos : 0 < lteW a * lteU C (lteN a) := Nat.mul_pos hwpos hupos
  have hpos : 0 < oddPart (lteW a + lteU C (lteN a)) + lteW a * lteU C (lteN a) := by omega
  calc
    twoValuation (lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a))
        = twoValuation (2 ^ lteN a * (oddPart (lteW a + lteU C (lteN a)) + lteW a * lteU C (lteN a))) := by
          rw [hsum]
    _ = lteN a + twoValuation (oddPart (lteW a + lteU C (lteN a)) + lteW a * lteU C (lteN a)) :=
          twoValuation_mul_two_pow (lteN a) (oddPart (lteW a + lteU C (lteN a)) + lteW a * lteU C (lteN a)) hpos
    _ = lteN a + twoValuation (oddPart (lteW a + lteU C s) + lteW a * lteU C s) := by
          simp [← hsn]

/-- In `s=n` with `v2(w+u)=n`, the extra cancellation is at least
`n+1`. -/
theorem lteExtra_ge_succ_of_eq_val (a C s : Nat)
    (hwodd : lteW a % 2 = 1) (huodd : lteU C s % 2 = 1)
    (hsn : s = lteN a)
    (h : twoValuation (lteW a + lteU C s) = lteN a) :
    lteN a + 1 ≤ lteExtra a C := by
  have hE := lteExtra_eq_add_of_eq a C s hwodd huodd hsn h
  rw [hE]
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hupos : 0 < lteU C s := by
    by_cases hz : lteU C s = 0
    · rw [hz] at huodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hxpos : 0 < lteW a + lteU C s := by omega
  have hxodd : oddPart (lteW a + lteU C s) % 2 = 1 :=
    oddPart_odd_of_pos (lteW a + lteU C s) hxpos
  have hwupos : 0 < lteW a * lteU C s := Nat.mul_pos hwpos hupos
  have hwuodd : (lteW a * lteU C s) % 2 = 1 :=
    odd_mul_odd_mod_two (lteW a) (lteU C s) hwodd huodd
  have hxvu : twoValuation (oddPart (lteW a + lteU C s)) = 0 :=
    twoValuation_odd (oddPart (lteW a + lteU C s)) hxodd
  have hwuvu : twoValuation (lteW a * lteU C s) = 0 :=
    twoValuation_odd (lteW a * lteU C s) hwuodd
  have hxpos' : 0 < oddPart (lteW a + lteU C s) := by
    by_cases hz : oddPart (lteW a + lteU C s) = 0
    · rw [hz] at hxodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hge := twoValuation_add_ge_succ_of_eq
      (oddPart (lteW a + lteU C s)) (lteW a * lteU C s)
      hxpos' hwupos (by rw [hxvu, hwuvu])
  omega

/-- Since `5^a = 1+2^n*w`, the extra cancellation is exactly
`v2(w+5^a*u)`. -/
theorem lteExtra_eq_v2_w_add_five_pow_u (a C : Nat)
    (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a) :
    lteExtra a C = twoValuation (lteW a + 5 ^ a * lteU C (lteN a)) := by
  unfold lteExtra
  dsimp
  have h5 : 5 ^ a = 1 + 2 ^ lteN a * lteW a := by
    have hle : 1 ≤ 5 ^ a := by
      exact Nat.succ_le_of_lt (Nat.pow_pos (show 0 < 5 by omega))
    have hsub := Nat.sub_add_cancel hle
    rw [hlte] at hsub
    omega
  have hsum : lteW a + lteU C (lteN a) + 2 ^ lteN a * lteW a * lteU C (lteN a) =
      lteW a + 5 ^ a * lteU C (lteN a) := by
    rw [h5, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_assoc]
  rw [hsum]

/-- In the `s = n` case, `macroValue = n + v2(w + 5^a*u)`. -/
theorem macroValue_eq_n_add_v2_w_add_five_pow_u (a C : Nat)
    (ha : 1 ≤ a) (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hs : twoValuation (C - 1) = lteN a) :
    macroValue a C = lteN a + twoValuation (lteW a + 5 ^ a * lteU C (lteN a)) := by
  let s := twoValuation (C - 1)
  have hCpos : 0 < C - 1 := by omega
  have hdec := n_eq_two_pow_mul_oddPart (C - 1) hCpos
  have hCu : C - 1 = 2 ^ s * lteU C s := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact hdec
  have huodd : lteU C s % 2 = 1 := by
    dsimp [s]
    rw [lteU_eq_oddPart C (twoValuation (C - 1)) rfl]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hthree := lteThreeWayTheorem a C s ha (show 1 ≤ C by omega) hCodd hwodd huodd hCu hlte
  have hsn : s = lteN a := hs
  have hV : macroValue a C = lteN a + lteExtra a C := hthree.2.2 hsn
  have hE := lteExtra_eq_v2_w_add_five_pow_u a C hlte
  rw [hV, hE]

/-- In `s=n` with `v2(w+u)=n`, the macro valuation is at least
`2n+1`. -/
theorem macroValue_ge_two_n_add_one_of_eq_val (a C s : Nat)
    (ha : 1 ≤ a) (hC : 1 < C) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hs : twoValuation (C - 1) = lteN a) (hsn : s = lteN a)
    (huodd : lteU C s % 2 = 1)
    (h : twoValuation (lteW a + lteU C s) = lteN a) :
    2 * lteN a + 1 ≤ macroValue a C := by
  have hE : lteN a + 1 ≤ lteExtra a C :=
    lteExtra_ge_succ_of_eq_val a C s hwodd huodd hsn h
  have hV := macroValue_eq_n_add_v2_w_add_five_pow_u a C ha hC hCodd hwodd hlte hs
  have hE' : lteN a + 1 ≤ twoValuation (lteW a + 5 ^ a * lteU C (lteN a)) := by
    rw [← lteExtra_eq_v2_w_add_five_pow_u a C hlte]
    exact hE
  rw [hV]
  omega

/-- K4B in `s = n` is exactly the linear valuation bound
`v2(w+5^a*u) <= m+1-n`. -/
theorem macroSuccessNat_iff_v2_w_add_five_pow_u_le (a C m : Nat)
    (hC : 1 < C) (ha : 1 ≤ a) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hs : twoValuation (C - 1) = lteN a) (hle : lteN a ≤ m + 1) :
    macroSuccessNat a m C ↔
      twoValuation (lteW a + 5 ^ a * lteU C (lteN a)) ≤ m + 1 - lteN a := by
  rw [macroSuccess_iff_val_le a m C hC]
  have hV := macroValue_eq_n_add_v2_w_add_five_pow_u a C ha hC hCodd hwodd hlte hs
  rw [hV]
  constructor <;> omega

/-- K4B failure in `s = n` is the exact mod-zero congruence
`w + 5^a*u ≡ 0 (mod 2^(m+2-n))`. -/
theorem macroFailureNat_iff_mod_eq_zero (a C m : Nat)
    (hC : 1 < C) (ha : 1 ≤ a) (hCodd : C % 2 = 1)
    (hwodd : lteW a % 2 = 1) (hlte : 5 ^ a - 1 = 2 ^ lteN a * lteW a)
    (hs : twoValuation (C - 1) = lteN a) (hle : lteN a ≤ m + 1) :
    ¬ macroSuccessNat a m C ↔
      (lteW a + 5 ^ a * lteU C (lteN a)) % 2 ^ (m + 2 - lteN a) = 0 := by
  rw [macroSuccessNat_iff_v2_w_add_five_pow_u_le a C m hC ha hCodd hwodd hlte hs hle]
  let X := lteW a + 5 ^ a * lteU C (lteN a)
  change (¬ twoValuation X ≤ m + 1 - lteN a) ↔ X % 2 ^ (m + 2 - lteN a) = 0
  have hwpos : 0 < lteW a := by
    by_cases hz : lteW a = 0
    · rw [hz] at hwodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have huodd : lteU C (lteN a) % 2 = 1 := by
    have hCpos : 0 < C - 1 := by omega
    rw [lteU_eq_oddPart C (lteN a) hs.symm]
    exact oddPart_odd_of_pos (C - 1) hCpos
  have hupos : 0 < lteU C (lteN a) := by
    by_cases hz : lteU C (lteN a) = 0
    · rw [hz] at huodd
      omega
    · exact Nat.pos_of_ne_zero hz
  have hXpos : 0 < X := by
    have h5pos : 0 < 5 ^ a * lteU C (lteN a) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) hupos
    omega
  have hlin : (¬ twoValuation X ≤ m + 1 - lteN a) ↔
      m + 2 - lteN a ≤ twoValuation X := by omega
  rw [hlin]
  rw [twoValuation_ge_iff_dvd_pow X (m + 2 - lteN a) hXpos]
  rw [Nat.dvd_iff_mod_eq_zero]

end StringFlow.Lte
