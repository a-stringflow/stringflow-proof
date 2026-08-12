import Std

/-!
# Binary digit machinery for the string-flow algebra project

The notes use `s_2(n)` (binary digit sum), `L(n)` (binary length),
and `v_2(n)` (2-adic valuation).  This module formalizes those
functions for natural numbers and proves the basic identities used in
Problem 2: shifting, all-ones blocks, complements, and disjoint block
concatenation.
-/

namespace StringFlow

/-- Number of 1-bits in the binary expansion of `n`. -/
def binaryWeight : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + binaryWeight ((n + 1) / 2)
termination_by n => n
decreasing_by
  simp_wf
  omega

/-- Number of bits in the binary expansion of `n` (0 for `n = 0`). -/
def binaryLength : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + binaryLength ((n + 1) / 2)
termination_by n => n
decreasing_by
  simp_wf
  omega

/-- Exponent of the largest power of two dividing `n`, with `v2 0 = 0`. -/
def twoValuation : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + twoValuation ((n + 1) / 2) else 0
termination_by n => n
decreasing_by
  simp_wf
  omega

/-- The odd part of `n`: remove all factors of two. -/
def oddPart (n : Nat) : Nat := n / 2 ^ twoValuation n

@[simp] theorem binaryWeight_zero : binaryWeight 0 = 0 := by
  simp [binaryWeight]

@[simp] theorem binaryWeight_succ (n : Nat) :
    binaryWeight (n + 1) = (n + 1) % 2 + binaryWeight ((n + 1) / 2) := by
  simp [binaryWeight]

@[simp] theorem binaryLength_zero : binaryLength 0 = 0 := by
  simp [binaryLength]

theorem binaryLength_succ (n : Nat) :
    binaryLength (n + 1) = 1 + binaryLength ((n + 1) / 2) := by
  simp [binaryLength]

@[simp] theorem twoValuation_zero : twoValuation 0 = 0 := by
  simp [twoValuation]

theorem twoValuation_succ (n : Nat) :
    twoValuation (n + 1) =
      if (n + 1) % 2 = 0 then 1 + twoValuation ((n + 1) / 2) else 0 := by
  simp [twoValuation]

@[simp] theorem oddPart_zero : oddPart 0 = 0 := by
  simp [oddPart]

/-- Shifting by one bit does not change the number of ones. -/
theorem binaryWeight_two_mul (n : Nat) : binaryWeight (2 * n) = binaryWeight n := by
  cases n with
  | zero => simp
  | succ k =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [binaryWeight_succ (2 * k + 1)]
      have hmod : (2 * k + 2) % 2 = 0 := by omega
      have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
      rw [hmod, hdiv]
      simp

/-- An odd number has one more one-bit than its half. -/
theorem binaryWeight_two_mul_add_one (n : Nat) :
    binaryWeight (2 * n + 1) = binaryWeight n + 1 := by
  rw [binaryWeight_succ (2 * n)]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hmod, hdiv]
  omega

/-- Powers of two have exactly one 1-bit. -/
theorem binaryWeight_two_pow (k : Nat) : binaryWeight (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
      rw [binaryWeight_two_mul]
      exact ih

private theorem two_mul_two_pow_sub_one_add_one (k : Nat) :
    2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.mul_one]
  rw [Nat.pow_succ]
  rw [← Nat.mul_comm 2 (2 ^ k)]
  have hge : 2 ≤ 2 * 2 ^ k := by
    exact Nat.mul_le_mul_left 2 (Nat.one_le_pow k 2 (by omega))
  omega

/-- The all-ones block of length `k` has digit sum `k`. -/
theorem binaryWeight_two_pow_sub_one (k : Nat) : binaryWeight (2 ^ k - 1) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← two_mul_two_pow_sub_one_add_one k]
      rw [binaryWeight_two_mul_add_one]
      rw [ih]

/-- Concatenating two disjoint binary blocks adds their digit sums.
  `q1` occupies bits `M` and above, `q2` occupies the low `M` bits. -/
theorem binaryWeight_add_mul_two_pow (q1 q2 M : Nat) (h : q2 < 2 ^ M) :
    binaryWeight (q1 * 2 ^ M + q2) = binaryWeight q1 + binaryWeight q2 := by
  induction M generalizing q2 with
  | zero =>
      have hz : q2 = 0 := by omega
      subst hz
      simp
  | succ M ih =>
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm]
      have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hq : q2 < 2 * 2 ^ M := by
        rw [hpow] at h
        exact h
      have hlt : q2 / 2 < 2 ^ M := by
        omega
      have hsplit : q2 = 2 * (q2 / 2) + q2 % 2 := by
        exact (Nat.div_add_mod q2 2).symm
      have hdist : 2 * (q1 * 2 ^ M + q2 / 2) + q2 % 2 =
          2 * (q1 * 2 ^ M) + 2 * (q2 / 2) + q2 % 2 := by
        rw [Nat.mul_add]
      rw [hsplit]
      rw [← Nat.add_assoc]
      rw [← hdist]
      have h01 : q2 % 2 = 0 ∨ q2 % 2 = 1 := Nat.mod_two_eq_zero_or_one q2
      rcases h01 with hpar | hpar
      · rw [hpar]
        simp
        rw [binaryWeight_two_mul]
        rw [binaryWeight_two_mul]
        rw [ih (q2 / 2) hlt]
      · rw [hpar]
        change binaryWeight (2 * (q1 * 2 ^ M + q2 / 2) + 1) =
          binaryWeight q1 + binaryWeight (2 * (q2 / 2) + 1)
        rw [binaryWeight_two_mul_add_one]
        rw [binaryWeight_two_mul_add_one]
        rw [ih (q2 / 2) hlt]
        omega

/-- `binaryWeight` of a number is the weight of its half plus its lowest bit. -/
theorem binaryWeight_eq_half_add_mod (n : Nat) :
    binaryWeight n = binaryWeight (n / 2) + n % 2 := by
  induction n with
  | zero => simp
  | succ k =>
      rw [binaryWeight_succ]
      rw [Nat.add_comm]

/-- Digit sums of a block are bounded by the block length. -/
theorem binaryWeight_le_of_lt_pow_two (n r : Nat) (h : n < 2 ^ r) :
    binaryWeight n ≤ r := by
  induction r generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      simp
  | succ r ih =>
      have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow] at h
      have hlt : n / 2 < 2 ^ r := by omega
      rw [binaryWeight_eq_half_add_mod]
      have hw : binaryWeight (n / 2) ≤ r := ih (n / 2) hlt
      have hmod : n % 2 ≤ 1 := by
        have h01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
        omega
      omega

/-- Complement identity inside a block of `r` bits. -/
theorem binaryWeight_complement (m r : Nat) (h : m < 2 ^ r) :
    binaryWeight (2 ^ r - 1 - m) = r - binaryWeight m := by
  induction r generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst hm
      simp
  | succ r ih =>
      have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow] at h
      rw [hpow]
      have hp : m / 2 < 2 ^ r := by omega
      have hsplit : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
      rw [hsplit]
      have h01 : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
      rcases h01 with h0 | h1
      · rw [h0]
        simp
        have heven : 2 * 2 ^ r - 1 - 2 * (m / 2) = 2 * (2 ^ r - 1 - m / 2) + 1 := by
          omega
        rw [heven]
        rw [binaryWeight_two_mul_add_one]
        rw [binaryWeight_two_mul]
        rw [ih (m / 2) hp]
        have hb : binaryWeight (m / 2) ≤ r := binaryWeight_le_of_lt_pow_two (m / 2) r hp
        omega
      · rw [h1]
        have hodd : 2 * 2 ^ r - 1 - (2 * (m / 2) + 1) = 2 * (2 ^ r - 1 - m / 2) := by
          omega
        rw [hodd]
        rw [binaryWeight_two_mul]
        rw [binaryWeight_two_mul_add_one]
        rw [ih (m / 2) hp]
        have hb : binaryWeight (m / 2) ≤ r := binaryWeight_le_of_lt_pow_two (m / 2) r hp
        omega

/-- Every number is below `2^(binaryLength n)`. -/
theorem binaryLength_pow_upper (n : Nat) : n < 2 ^ binaryLength n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simp
      | succ k =>
          have hih : (k + 1) / 2 < 2 ^ binaryLength ((k + 1) / 2) :=
            ih ((k + 1) / 2) (by omega)
          rw [binaryLength_succ]
          have hpow : 2 ^ (1 + binaryLength ((k + 1) / 2)) =
              2 * 2 ^ binaryLength ((k + 1) / 2) := by
            rw [show 1 + binaryLength ((k + 1) / 2) =
              binaryLength ((k + 1) / 2) + 1 by omega]
            rw [Nat.pow_succ, Nat.mul_comm]
          have hsplit : k + 1 = 2 * ((k + 1) / 2) + (k + 1) % 2 :=
            (Nat.div_add_mod (k + 1) 2).symm
          have hmod : (k + 1) % 2 ≤ 1 := by
            have h01 : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := Nat.mod_two_eq_zero_or_one (k + 1)
            omega
          calc
            k + 1 = 2 * ((k + 1) / 2) + (k + 1) % 2 := hsplit
            _ < 2 * 2 ^ binaryLength ((k + 1) / 2) := by omega
            _ = 2 ^ (1 + binaryLength ((k + 1) / 2)) := hpow.symm

/-- The number of ones never exceeds the binary length. -/
theorem binaryWeight_le_binaryLength (n : Nat) : binaryWeight n ≤ binaryLength n := by
  have hlt := binaryLength_pow_upper n
  exact binaryWeight_le_of_lt_pow_two n (binaryLength n) hlt

/-- `binaryLength` of `2*n` for positive `n` is one more than that of `n`. -/
theorem binaryLength_two_mul_succ (k : Nat) :
    binaryLength (2 * (k + 1)) = binaryLength (k + 1) + 1 := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
  rw [binaryLength_succ (2 * k + 1)]
  have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
  rw [hdiv]
  omega

/-- `binaryLength` of `2*n` for positive `n` is one more than that of `n`. -/
theorem binaryLength_two_mul (n : Nat) (hn : 0 < n) :
    binaryLength (2 * n) = binaryLength n + 1 := by
  cases n with
  | zero => omega
  | succ k => exact binaryLength_two_mul_succ k

/-- `binaryLength` of `2*n+1` is one more than that of `n`. -/
theorem binaryLength_two_mul_add_one (n : Nat) :
    binaryLength (2 * n + 1) = binaryLength n + 1 := by
  rw [binaryLength_succ (2 * n)]
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hdiv]
  omega

/-- Powers of two have binary length one more than the exponent. -/
theorem binaryLength_two_pow (k : Nat) : binaryLength (2 ^ k) = k + 1 := by
  induction k with
  | zero =>
      change binaryLength 1 = 1
      rw [binaryLength_succ 0]
      simp
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have hn : 0 < 2 ^ k := by
        exact Nat.pow_pos (show 0 < 2 by omega)
      rw [binaryLength_two_mul (2 ^ k) hn]
      rw [ih]

/-- The all-ones block of length `k` has binary length `k`. -/
theorem binaryLength_two_pow_sub_one (k : Nat) : binaryLength (2 ^ k - 1) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← two_mul_two_pow_sub_one_add_one k]
      rw [binaryLength_two_mul_add_one]
      rw [ih]

/-- `2^(m+1) + 1` has binary length `m + 2`. -/
theorem binaryLength_two_pow_add_one (m : Nat) :
    binaryLength (2 ^ (m + 1) + 1) = m + 2 := by
  induction m with
  | zero =>
      change binaryLength 3 = 2
      rw [binaryLength_succ 2]
      have hd : 3 / 2 = 1 := by omega
      rw [hd]
      rw [binaryLength_succ 0]
      simp
  | succ m ih =>
      have hpow : 2 ^ ((m + 1) + 1) = 2 * 2 ^ (m + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      rw [binaryLength_two_mul_add_one]
      rw [binaryLength_two_pow (m + 1)]

/-- `binaryLength` doubles the length budget by one when shifting left. -/
theorem binaryLength_four_mul (n : Nat) (hn : 0 < n) :
    binaryLength (4 * n) = binaryLength n + 2 := by
  have hn2 : 0 < 2 * n := by omega
  have h4 : 4 * n = 2 * (2 * n) := by
    rw [show 4 = 2 * 2 by omega]
    rw [Nat.mul_assoc]
  calc
    binaryLength (4 * n) = binaryLength (2 * (2 * n)) := by rw [h4]
    _ = binaryLength (2 * n) + 1 := binaryLength_two_mul (2 * n) hn2
    _ = (binaryLength n + 1) + 1 := by rw [binaryLength_two_mul n hn]
    _ = binaryLength n + 2 := by omega

/-- Shifting left by two bits preserves the number of ones. -/
theorem binaryWeight_four_mul (n : Nat) : binaryWeight (4 * n) = binaryWeight n := by
  rw [show 4 * n = 2 * (2 * n) by omega]
  rw [binaryWeight_two_mul, binaryWeight_two_mul]

/-- Number of zero bits in the binary expansion. -/
def binaryZeros (n : Nat) : Nat := binaryLength n - binaryWeight n

/-- Shifting left by two bits adds two zeros to the profile. -/
theorem binaryZeros_four_mul (n : Nat) (hn : 0 < n) :
    binaryZeros (4 * n) = binaryZeros n + 2 := by
  unfold binaryZeros
  rw [binaryLength_four_mul n hn, binaryWeight_four_mul]
  have hb : binaryWeight n ≤ binaryLength n := binaryWeight_le_binaryLength n
  omega

/-- Binary length of a positive number is the length of its half plus one. -/
theorem binaryLength_eq_half_add_one (n : Nat) (hn : 0 < n) :
    binaryLength n = binaryLength (n / 2) + 1 := by
  cases n with
  | zero => omega
  | succ k =>
      rw [binaryLength_succ]
      omega

/-- Numbers below `2^r` have binary length at most `r`. -/
theorem binaryLength_le_of_lt_pow_two (n r : Nat) (h : n < 2 ^ r) :
    binaryLength n ≤ r := by
  induction r generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      simp
  | succ r ih =>
      have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow] at h
      have hlt : n / 2 < 2 ^ r := by omega
      have hn0 : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      rcases hn0 with hn0 | hnpos
      · subst hn0
        simp
      · have hhalf : binaryLength n = binaryLength (n / 2) + 1 :=
          binaryLength_eq_half_add_one n hnpos
        rw [hhalf]
        have hle := ih (n / 2) hlt
        omega

/-- A number between `2^(r-1)` and `2^r` has binary length exactly `r`. -/
theorem binaryLength_eq_of_bounds (n r : Nat) (hr : 0 < r)
    (h1 : 2 ^ (r - 1) ≤ n) (h2 : n < 2 ^ r) : binaryLength n = r := by
  have hle : binaryLength n ≤ r := binaryLength_le_of_lt_pow_two n r h2
  have hge : r ≤ binaryLength n := by
    have hnot : ¬ binaryLength n < r := by
      intro hlt
      have hle2 : binaryLength n ≤ r - 1 := by omega
      have hpowle : 2 ^ binaryLength n ≤ 2 ^ (r - 1) :=
        Nat.pow_le_pow_right (show 0 < 2 by omega) hle2
      have hpow : n < 2 ^ binaryLength n := binaryLength_pow_upper n
      omega
    have hlg := Nat.lt_or_ge (binaryLength n) r
    rcases hlg with hlt | hge
    · exact (hnot hlt).elim
    · exact hge
  omega

/-- Concatenating blocks adds their binary lengths. -/
theorem binaryLength_add_mul_two_pow (q1 q2 M : Nat) (hq2 : q2 < 2 ^ M) (hq1 : 0 < q1) :
    binaryLength (q1 * 2 ^ M + q2) = binaryLength q1 + M := by
  induction M generalizing q2 with
  | zero =>
      have hz : q2 = 0 := by omega
      subst hz
      simp
  | succ M ih =>
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (q1 * 2 ^ M) 2]
      have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hq : q2 < 2 * 2 ^ M := by
        rw [hpow] at hq2
        exact hq2
      have hlt : q2 / 2 < 2 ^ M := by omega
      have hsplit : q2 = 2 * (q2 / 2) + q2 % 2 := (Nat.div_add_mod q2 2).symm
      have h01 : q2 % 2 = 0 ∨ q2 % 2 = 1 := Nat.mod_two_eq_zero_or_one q2
      rcases h01 with h0 | h1m
      · have hn : q2 = 2 * (q2 / 2) := by
          rw [hsplit, h0]
          omega
        rw [hn]
        rw [← Nat.mul_add]
        have hq1pow : 0 < q1 * 2 ^ M :=
          Nat.mul_pos hq1 (Nat.pow_pos (show 0 < 2 by omega))
        have hpos : 0 < q1 * 2 ^ M + q2 / 2 := by omega
        rw [binaryLength_two_mul (q1 * 2 ^ M + q2 / 2) hpos]
        rw [ih (q2 / 2) hlt]
        omega
      · have hn : q2 = 2 * (q2 / 2) + 1 := by
          rw [hsplit, h1m]
          omega
        rw [hn]
        rw [← Nat.add_assoc]
        rw [← Nat.mul_add]
        rw [binaryLength_two_mul_add_one]
        rw [ih (q2 / 2) hlt]
        omega

/-- A number with binary length `r > 0` is at least `2^(r-1)`. -/
theorem two_pow_pred_le_of_binaryLength (n r : Nat) (hr : 0 < r)
    (hL : binaryLength n = r) : 2 ^ (r - 1) ≤ n := by
  have hlg := Nat.lt_or_ge n (2 ^ (r - 1))
  rcases hlg with hlt | hge
  · have hlen : binaryLength n ≤ r - 1 :=
      binaryLength_le_of_lt_pow_two n (r - 1) hlt
    omega
  · exact hge

/-- An odd number with binary length `r > 1` has predecessor of the same length. -/
theorem binaryLength_pred_of_odd (a r : Nat) (ha : 1 < a) (hr : 0 < r)
    (hodd : a % 2 = 1) (hL : binaryLength a = r) :
    binaryLength (a - 1) = r := by
  have h1 : 2 ^ (r - 1) ≤ a - 1 := by
    have hleA : 2 ^ (r - 1) ≤ a := two_pow_pred_le_of_binaryLength a r hr hL
    have hne : 2 ^ (r - 1) ≠ a := by
      intro heq
      have hr2 : 2 ≤ r := by
        have hrne1 : r ≠ 1 := by
          intro hr1
          subst hr1
          have ha_lt : a < 2 := by
            have h1a := binaryLength_pow_upper a
            rw [hL] at h1a
            simpa using h1a
          omega
        have hrne0 : r ≠ 0 := by omega
        omega
      have hpow : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
        have h : r - 1 = (r - 2) + 1 := by omega
        rw [h, Nat.pow_succ, Nat.mul_comm]
      have heven : (2 ^ (r - 1)) % 2 = 0 := by
        rw [hpow]
        omega
      rw [← heq] at hodd
      omega
    have hltA : 2 ^ (r - 1) + 1 ≤ a := by omega
    omega
  have h2 : a - 1 < 2 ^ r := by
    have hlt : a < 2 ^ r := by
      have h1a := binaryLength_pow_upper a
      have hmono : 2 ^ binaryLength a ≤ 2 ^ r :=
        Nat.pow_le_pow_right (show 0 < 2 by omega) (by omega)
      omega
    omega
  exact binaryLength_eq_of_bounds (a - 1) r hr h1 h2

/-- Multiplying an odd number by the all-ones block doubles its length. -/
theorem binaryLength_mul_all_ones (a r : Nat) (ha : 1 < a) (hr : 0 < r)
    (hodd : a % 2 = 1) (hL : binaryLength a = r) :
    binaryLength (a * (2 ^ r - 1)) = 2 * r := by
  have hlt : a < 2 ^ r := by
    have h1a := binaryLength_pow_upper a
    have hmono : 2 ^ binaryLength a ≤ 2 ^ r :=
      Nat.pow_le_pow_right (show 0 < 2 by omega) (by omega)
    omega
  have hsplit : a * (2 ^ r - 1) = (a - 1) * 2 ^ r + (2 ^ r - a) := by
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_sub_right_distrib]
    rw [Nat.mul_one]
    have hX : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    have hA : 1 ≤ a := by omega
    have hleA : a ≤ 2 ^ r := by omega
    have hleP : 2 ^ r ≤ a * 2 ^ r :=
      Nat.le_mul_of_pos_left (2 ^ r) (by omega)
    omega
  have hq2 : 2 ^ r - a < 2 ^ r := by omega
  have hq1 : 0 < a - 1 := by omega
  have hlen := binaryLength_add_mul_two_pow (a - 1) (2 ^ r - a) r hq2 hq1
  rw [hsplit]
  rw [hlen]
  have hLpred := binaryLength_pred_of_odd a r ha hr hodd hL
  rw [hLpred]
  omega

/-- Shifting left by one bit adds one zero to the profile. -/
theorem binaryZeros_two_mul (n : Nat) (hn : 0 < n) :
    binaryZeros (2 * n) = binaryZeros n + 1 := by
  unfold binaryZeros
  rw [binaryLength_two_mul n hn, binaryWeight_two_mul]
  have hb : binaryWeight n ≤ binaryLength n := binaryWeight_le_binaryLength n
  omega

/-- The all-ones complement identity: `s2(a(2^r-1)) = r` for `r ≥ L(a)`. -/
theorem binaryWeight_mul_all_ones (a r : Nat) (ha : 0 < a) (hle : binaryLength a ≤ r) :
    binaryWeight (a * (2 ^ r - 1)) = r := by
  have hlt : a < 2 ^ r := by
    have h1 : a < 2 ^ binaryLength a := binaryLength_pow_upper a
    have hmono : 2 ^ binaryLength a ≤ 2 ^ r :=
      Nat.pow_le_pow_right (show 0 < 2 by omega) hle
    omega
  have hsplit : a * (2 ^ r - 1) = (a - 1) * 2 ^ r + (2 ^ r - a) := by
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_sub_right_distrib]
    rw [Nat.mul_one]
    have hX : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    have hA : 1 ≤ a := by omega
    have hleA : a ≤ 2 ^ r := by omega
    have hleP : 2 ^ r ≤ a * 2 ^ r :=
      Nat.le_mul_of_pos_left (2 ^ r) (by omega)
    omega
  have hq2 : 2 ^ r - a < 2 ^ r := by omega
  have hw := binaryWeight_add_mul_two_pow (a - 1) (2 ^ r - a) r hq2
  rw [hsplit]
  rw [hw]
  have hsub : 2 ^ r - a = 2 ^ r - 1 - (a - 1) := by omega
  rw [hsub]
  have hlt1 : a - 1 < 2 ^ r := by omega
  rw [binaryWeight_complement (a - 1) r hlt1]
  have hb : binaryWeight (a - 1) ≤ r := by
    apply binaryWeight_le_of_lt_pow_two (a - 1) r
    omega
  omega

end StringFlow
