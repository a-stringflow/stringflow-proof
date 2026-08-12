import WordWindow
import Mathlib.Tactic.Ring

namespace StringFlow.Word

/-- Penultimate entry of a word (0 for words of length < 2). -/
def wordPenultimate (w : List Nat) : Nat :=
  wordLast (w.dropLast)

/-- Word weight is additive over concatenation. -/
theorem wordWeight_append (w1 w2 : List Nat) :
    StringFlow.wordWeight (w1 ++ w2) =
      StringFlow.wordWeight w1 + StringFlow.wordWeight w2 := by
  induction w1 with
  | nil => simp [StringFlow.wordWeight]
  | cons a as ih =>
      simp [StringFlow.wordWeight, ih, Nat.add_assoc]

/-- Appending one step appends one `5^L` term to the prefix numerator. -/
theorem wordA_append_singleton (w : List Nat) (t : Nat) :
    wordA (w ++ [t]) = 5 * wordA w + 2 ^ StringFlow.wordWeight w := by
  induction w with
  | nil =>
      simp [wordA, StringFlow.wordWeight]
  | cons a as ih =>
      have hlen : (as ++ [t]).length = as.length + 1 := by simp
      have hA : wordA (as ++ [t]) =
          5 * wordA as + 2 ^ StringFlow.wordWeight as := ih
      simp [wordA, StringFlow.wordWeight, hlen, hA]
      rw [Nat.pow_add, Nat.mul_add, Nat.mul_add]
      norm_num
      ring_nf

/-- Mod 25, `A_L` is determined by the last two steps. -/
theorem wordA_mod25_of_tail_two (pre : List Nat) (t1 t2 : Nat) :
    wordA (pre ++ [t1, t2]) % 25 =
      ((2 ^ StringFlow.wordWeight pre *
          (5 + 2 ^ t1)) % 25) := by
  have h1 := wordA_append_singleton pre t1
  have h2 := wordA_append_singleton (pre ++ [t1]) t2
  have hw : StringFlow.wordWeight (pre ++ [t1]) =
      StringFlow.wordWeight pre + t1 := by
    rw [wordWeight_append pre [t1]]
    simp [StringFlow.wordWeight]
  have h3 : pre ++ [t1, t2] = (pre ++ [t1]) ++ [t2] := by
    rw [List.append_assoc]
    rfl
  rw [h3, h2, h1, hw]
  rw [Nat.mul_add, Nat.mul_add, Nat.pow_add]
  have h25 : (25 * wordA pre) % 25 = 0 := by
    exact Nat.mul_mod_right 25 (wordA pre)
  have h25mul : 5 * (5 * wordA pre) = 25 * wordA pre := by ring_nf
  rw [h25mul]
  simp [Nat.add_mod, Nat.mul_mod, h25]
  ring_nf

/-- `13^n mod 25`, the inverse of `2^n` modulo 25. -/
def pow2Inv25 : Nat → Nat
  | 0 => 1
  | n + 1 => (pow2Inv25 n * 13) % 25

/-- Multiplication by a reduced residue modulo `m`. -/
theorem mul_mod_right' (a b m : Nat) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_mod, Nat.mul_mod]
  simp

/-- `pow2Inv25 n` is the inverse of `2^n` modulo 25. -/
theorem pow2Inv25_spec (n : Nat) : (2 ^ n * pow2Inv25 n) % 25 = 1 := by
  induction n with
  | zero => simp [pow2Inv25]
  | succ n ih =>
      rw [pow2Inv25, Nat.pow_succ]
      rw [mul_mod_right']
      have h26 : (26 * (2 ^ n * pow2Inv25 n)) % 25 =
          (2 ^ n * pow2Inv25 n) % 25 := by
        rw [Nat.mul_mod]
        have h26m : 26 % 25 = 1 := by norm_num
        rw [h26m]
        simp
      rw [show 2 ^ n * 2 * (pow2Inv25 n * 13) =
          26 * (2 ^ n * pow2Inv25 n) by ring_nf]
      rw [h26]
      exact ih

/-- Residue class of a start is determined by the last two steps. -/
theorem start_mod25_of_tail_two (pre : List Nat) (t1 t2 : Nat)
    (x q S : Nat) (_hS : S = StringFlow.wordWeight pre + t1 + t2)
    (hx : 2 ^ S * x = wordA (pre ++ [t1, t2]) + 5 ^ (pre.length + 2) * q) :
    x % 25 =
      ((2 ^ StringFlow.wordWeight pre * (5 + 2 ^ t1) *
          pow2Inv25 S) % 25) := by
  have hA := wordA_mod25_of_tail_two pre t1 t2
  have h25q : (5 ^ (pre.length + 2) * q) % 25 = 0 := by
    have hpow : 5 ^ (pre.length + 2) = 25 * 5 ^ pre.length := by
      rw [show pre.length + 2 = pre.length + 1 + 1 by omega]
      rw [Nat.pow_add, Nat.pow_add]
      norm_num
      ring_nf
    rw [hpow, Nat.mul_assoc, Nat.mul_mod]
    simp
  have hxmod : (2 ^ S * x) % 25 = wordA (pre ++ [t1, t2]) % 25 := by
    rw [hx, Nat.add_mod, h25q]
    simp
  have hinv := pow2Inv25_spec S
  have hx' : x % 25 = (wordA (pre ++ [t1, t2]) * pow2Inv25 S) % 25 := by
    have hmul : (2 ^ S * x * pow2Inv25 S) % 25 =
        (wordA (pre ++ [t1, t2]) * pow2Inv25 S) % 25 := by
      rw [Nat.mul_mod, Nat.mul_mod]
      rw [hxmod]
      simp
    have hcancel : (2 ^ S * x * pow2Inv25 S) % 25 = x % 25 := by
      rw [show 2 ^ S * x * pow2Inv25 S = x * (2 ^ S * pow2Inv25 S) by ring_nf]
      rw [Nat.mul_mod, Nat.mul_mod]
      rw [hinv]
      simp
    exact hcancel.symm.trans hmul
  rw [hx']
  have hAinv : (wordA (pre ++ [t1, t2]) % 25 * pow2Inv25 S) % 25 =
      (wordA (pre ++ [t1, t2]) * pow2Inv25 S) % 25 := by
    rw [Nat.mul_mod, Nat.mul_mod]
    simp [Nat.mul_comm]
  rw [← hAinv]
  rw [hA]
  have hAinv2 : ((2 ^ StringFlow.wordWeight pre * (5 + 2 ^ t1)) % 25 *
      pow2Inv25 S) % 25 =
      (2 ^ StringFlow.wordWeight pre * (5 + 2 ^ t1) * pow2Inv25 S) % 25 := by
    rw [Nat.mul_mod, Nat.mul_mod]
    simp [Nat.mul_comm]
  rw [← hAinv2]

set_option maxHeartbeats 1000000 in
/-- For a t=1 run start with prefix weight `W ≥ 2`, the quotient
`q` satisfies `q ≡ -A (mod 4)`. -/
theorem runStartQuotient_mod4 (W m A q r : Nat)
    (hW : 2 ≤ W)
    (h : 2 ^ W * (5 * r + 3) =
        5 * A + 5 ^ (m + 1) * q + 3 * 2 ^ W) :
    q % 4 = (4 - A % 4) % 4 := by
  have hmod := congrArg (fun x => x % 4) h
  have hL : (2 ^ W * (5 * r + 3)) % 4 = 0 := by
    have h2 : (2 ^ W) % 4 = 0 := by
      rw [show W = 2 + (W - 2) by omega]
      rw [Nat.pow_add, Nat.mul_mod]
      norm_num
    rw [Nat.mul_mod, h2]
    simp
  rw [hL] at hmod
  have h5A : (5 * A) % 4 = A % 4 := by
    simp [Nat.mul_mod]
  have h5pow_aux : ∀ n, (5 ^ (n + 1)) % 4 = 1 := by
    intro n
    rw [Nat.pow_mod]
    norm_num
  have h5q : (5 ^ (m + 1) * q) % 4 = q % 4 := by
    rw [Nat.mul_mod, h5pow_aux m]
    simp
  have h3 : (3 * 2 ^ W) % 4 = 0 := by
    rw [Nat.mul_mod]
    rw [show W = 2 + (W - 2) by omega]
    rw [Nat.pow_add, Nat.mul_mod]
    norm_num
  have hmain : (5 * A + 5 ^ (m + 1) * q) % 4 = (A + q) % 4 := by
    simp [Nat.add_mod, h5A, h5q]
  have hR : (5 * A + 5 ^ (m + 1) * q + 3 * 2 ^ W) % 4 =
      (A + q) % 4 := by
    rw [Nat.add_mod, hmain, h3]
    simp
  rw [hR] at hmod
  have hAq : (A % 4 + q % 4) % 4 = 0 := by
    simpa [Nat.add_mod] using hmod.symm
  let a := A % 4
  let qq := q % 4
  have ha : a < 4 := by
    dsimp [a]
    exact Nat.mod_lt A (by decide)
  have hqq : qq < 4 := by
    dsimp [qq]
    exact Nat.mod_lt q (by decide)
  have hAq' : (a + qq) % 4 = 0 := by
    simpa [a, qq] using hAq
  have hdvd : 4 ∣ a + qq := Nat.dvd_iff_mod_eq_zero.mpr hAq'
  rcases hdvd with ⟨k, hk⟩
  have hk01 : k = 0 ∨ k = 1 := by
    have hsum : a + qq < 8 := by omega
    omega
  rcases hk01 with hk0 | hk1
  · have ha0 : a = 0 := by omega
    have hq0 : qq = 0 := by omega
    dsimp [a, qq] at ha0 hq0
    simp [hq0, ha0]
  · have hqqeq : qq = 4 - a := by omega
    have hpos : 0 < a := by omega
    dsimp [qq] at hqqeq ⊢
    rw [hqqeq]
    dsimp [a]
    have hApos : 0 < A % 4 := by
      dsimp [a] at hpos
      exact hpos
    have hltA : 4 - A % 4 < 4 := by
      have hAm : A % 4 < 4 := Nat.mod_lt A (by decide)
      omega
    exact (Nat.mod_eq_of_lt hltA).symm

end StringFlow.Word
