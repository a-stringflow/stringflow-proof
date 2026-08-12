import CollatzRank
import TwoPowPlusOne

/-!
# Theorem 2.29: balance witnesses forbid one-dimensional regular ranks

If the digit-balance lemma (Lemma 2.28) supplies an odd witness
`d, e` for `(a,b)`, then `T_{a,b}` has no strictly descending rank of
the form `r(n) = A^(zeros) B^(ones)`.
-/

namespace StringFlow

/-- `T_{a,b}(n) = n/2` for even `n` and `a n + b` for odd `n`. -/
def tStep (a b n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else a * n + b

/-- The odd family point `n = c*2^k + d` with `c = 2^L-1`. -/
def reductionN (a d k : Nat) : Nat := (2 ^ binaryLength a - 1) * 2 ^ k + d

/-- The transformed family point `v = a*c*2^(k-L)+e`. -/
def reductionV (a c e k L : Nat) : Nat := a * c * 2 ^ (k - L) + e

private theorem reductionN_odd (L k d : Nat) (hk : 1 ≤ k) (hd : d % 2 = 1) :
    ((2 ^ L - 1) * 2 ^ k + d) % 2 = 1 := by
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have h : k = (k - 1) + 1 := by omega
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by
        congr 1
      _ = 2 * 2 ^ (k - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  have hrew : (2 ^ L - 1) * (2 * 2 ^ (k - 1)) = 2 * ((2 ^ L - 1) * 2 ^ (k - 1)) := by
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm (2 ^ L - 1) 2]
    rw [Nat.mul_assoc]
  rw [hrew]
  omega

private theorem tStep_reduction (a b d e : Nat) (L : Nat)
    (ha : 1 < a) (hL : binaryLength a = L)
    (hbal : a * d + b = 2 ^ L * e)
    (k : Nat) (hk : L ≤ k) (hdodd : d % 2 = 1) :
    tStep a b ((2 ^ L - 1) * 2 ^ k + d) =
      2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L) + e) := by
  unfold tStep
  have hLpos : 0 < L := by
    have h0 : L = 0 ∨ 0 < L := Nat.eq_zero_or_pos L
    rcases h0 with hL0 | hLpos
    · rw [hL0]
      have hz : a = 0 := by
        have h := binaryLength_pow_upper a
        rw [hL] at h
        rw [hL0] at h
        have h1 : a < 1 := by simpa using h
        omega
      omega
    · exact hLpos
  have hk1 : 1 ≤ k := by omega
  have hodd := reductionN_odd L k d hk1 hdodd
  have hnot : ¬ ((2 ^ L - 1) * 2 ^ k + d) % 2 = 0 := by omega
  rw [if_neg hnot]
  have h1 : a * ((2 ^ L - 1) * 2 ^ k + d) + b =
      a * (2 ^ L - 1) * 2 ^ k + (a * d + b) := by
    calc
      a * ((2 ^ L - 1) * 2 ^ k + d) + b
          = a * ((2 ^ L - 1) * 2 ^ k) + a * d + b := by rw [Nat.mul_add]
      _ = a * (2 ^ L - 1) * 2 ^ k + a * d + b := by rw [← Nat.mul_assoc]
      _ = a * (2 ^ L - 1) * 2 ^ k + (a * d + b) := by omega
  have h2 : a * (2 ^ L - 1) * 2 ^ k + (a * d + b) =
      a * (2 ^ L - 1) * 2 ^ k + 2 ^ L * e := by
    rw [hbal]
  have hpow : 2 ^ k = 2 ^ L * 2 ^ (k - L) := by
    calc
      2 ^ k = 2 ^ (L + (k - L)) := by
        congr 1
        omega
      _ = 2 ^ L * 2 ^ (k - L) := by rw [Nat.pow_add]
  have hrew : a * (2 ^ L - 1) * (2 ^ L * 2 ^ (k - L)) =
      2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L)) := by
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm (a * (2 ^ L - 1)) (2 ^ L)]
    rw [Nat.mul_assoc]
  have h3 : a * (2 ^ L - 1) * 2 ^ k + 2 ^ L * e =
      2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L) + e) := by
    calc
      a * (2 ^ L - 1) * 2 ^ k + 2 ^ L * e
          = a * (2 ^ L - 1) * (2 ^ L * 2 ^ (k - L)) + 2 ^ L * e := by rw [hpow]
      _ = 2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L)) + 2 ^ L * e := by rw [hrew]
      _ = 2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L) + e) := by rw [← Nat.mul_add]
  calc
    a * ((2 ^ L - 1) * 2 ^ k + d) + b
        = a * (2 ^ L - 1) * 2 ^ k + (a * d + b) := h1
    _ = a * (2 ^ L - 1) * 2 ^ k + 2 ^ L * e := h2
    _ = 2 ^ L * (a * (2 ^ L - 1) * 2 ^ (k - L) + e) := h3

private theorem reductionN_profile (d : Nat) (L k : Nat)
    (hd : d < 2 ^ k) (hc : 0 < 2 ^ L - 1) :
    binaryWeight ((2 ^ L - 1) * 2 ^ k + d) = L + binaryWeight d ∧
    binaryZeros ((2 ^ L - 1) * 2 ^ k + d) = k - binaryWeight d := by
  have hw : binaryWeight ((2 ^ L - 1) * 2 ^ k + d) =
      binaryWeight (2 ^ L - 1) + binaryWeight d :=
    binaryWeight_add_mul_two_pow (2 ^ L - 1) d k hd
  have hwL : binaryWeight (2 ^ L - 1) = L := binaryWeight_two_pow_sub_one L
  have hlen : binaryLength ((2 ^ L - 1) * 2 ^ k + d) =
      binaryLength (2 ^ L - 1) + k :=
    binaryLength_add_mul_two_pow (2 ^ L - 1) d k hd hc
  have hlenL : binaryLength (2 ^ L - 1) = L := binaryLength_two_pow_sub_one L
  constructor
  · rw [hw, hwL]
  · unfold binaryZeros
    rw [hlen, hlenL, hw, hwL]
    have hb : binaryWeight d ≤ k := binaryWeight_le_of_lt_pow_two d k hd
    omega

private theorem reductionV_profile (a e : Nat) (L k : Nat)
    (ha : 1 < a) (hodd : a % 2 = 1)
    (hL : binaryLength a = L) (hLpos : 0 < L)
    (he : e < 2 ^ (k - L)) (hkc : L ≤ k) :
    binaryWeight (a * (2 ^ L - 1) * 2 ^ (k - L) + e) = L + binaryWeight e ∧
    binaryZeros (a * (2 ^ L - 1) * 2 ^ (k - L) + e) = k - binaryWeight e := by
  have hw1 : binaryWeight (a * (2 ^ L - 1) * 2 ^ (k - L) + e) =
      binaryWeight (a * (2 ^ L - 1)) + binaryWeight e :=
    binaryWeight_add_mul_two_pow (a * (2 ^ L - 1)) e (k - L) he
  have hw2 : binaryWeight (a * (2 ^ L - 1)) = L :=
    binaryWeight_mul_all_ones a L (by omega) (by omega)
  have hcpos : 0 < 2 ^ L - 1 := by
    have h1 : 1 < 2 ^ L := by
      have h := one_lt_two_pow_succ (L - 1)
      have hL' : L = (L - 1) + 1 := by omega
      rw [hL']
      exact h
    omega
  have hac : 0 < a * (2 ^ L - 1) := Nat.mul_pos (by omega) hcpos
  have hlen1 : binaryLength (a * (2 ^ L - 1) * 2 ^ (k - L) + e) =
      binaryLength (a * (2 ^ L - 1)) + (k - L) :=
    binaryLength_add_mul_two_pow (a * (2 ^ L - 1)) e (k - L) he hac
  have hlen2 : binaryLength (a * (2 ^ L - 1)) = 2 * L :=
    binaryLength_mul_all_ones a L ha hLpos hodd hL
  constructor
  · rw [hw1, hw2]
  · unfold binaryZeros
    rw [hlen1, hlen2, hw1, hw2]
    have hb : binaryWeight e ≤ k - L := binaryWeight_le_of_lt_pow_two e (k - L) he
    omega

private theorem profileRank_two_mul (A B n : Nat) (hn : 0 < n) :
    profileRank A B (2 * n) = A * profileRank A B n := by
  unfold profileRank
  rw [binaryZeros_two_mul n hn, binaryWeight_two_mul]
  rw [show binaryZeros n + 1 = 1 + binaryZeros n by omega]
  rw [Nat.pow_add]
  simp
  rw [Nat.mul_assoc]

private theorem profileRank_shift (A B n L : Nat) (hn : 0 < n) :
    profileRank A B (2 ^ L * n) = A ^ L * profileRank A B n := by
  induction L with
  | zero => simp [profileRank]
  | succ L ih =>
      have hpow : 2 ^ (L + 1) * n = 2 * (2 ^ L * n) := by
        calc
          2 ^ (L + 1) * n = (2 ^ L * 2) * n := by rw [Nat.pow_succ]
          _ = 2 ^ L * (2 * n) := by rw [Nat.mul_assoc]
          _ = 2 * (2 ^ L * n) := by
            rw [← Nat.mul_assoc]
            rw [Nat.mul_comm (2 ^ L) 2]
            rw [Nat.mul_assoc]
      rw [hpow]
      have hn2 : 0 < 2 ^ L * n :=
        Nat.mul_pos (Nat.pow_pos (show 0 < 2 by omega)) hn
      rw [profileRank_two_mul A B (2 ^ L * n) hn2]
      rw [ih]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm A (A ^ L)]
      rw [Nat.pow_succ]

private theorem tStep_two (a b : Nat) : tStep a b 2 = 1 := by
  unfold tStep
  rw [if_pos (by omega)]

private theorem profileRank_A_gt_one_of_descent (a b A B : Nat) (_hB : 0 < B)
    (hdesc : ∀ n : Nat, profileRank A B (tStep a b n) < profileRank A B n) :
    1 < A := by
  have h2 := hdesc 2
  have hstep : tStep a b 2 = 1 := tStep_two a b
  rw [hstep] at h2
  unfold profileRank at h2
  have hz1 : binaryZeros 1 = 0 := by
    unfold binaryZeros
    have hlen : binaryLength 1 = 1 := by
      rw [show 1 = 2 ^ 0 by rfl]
      exact binaryLength_two_pow 0
    have hwt : binaryWeight 1 = 1 := by
      rw [show 1 = 2 ^ 0 by rfl]
      exact binaryWeight_two_pow 0
    rw [hlen, hwt]
  have hz2 : binaryZeros 2 = 1 := by
    unfold binaryZeros
    have hlen : binaryLength 2 = 2 := by
      rw [show 2 = 2 ^ 1 by rfl]
      exact binaryLength_two_pow 1
    have hwt : binaryWeight 2 = 1 := by
      rw [show 2 = 2 ^ 1 by rfl]
      exact binaryWeight_two_pow 1
    rw [hlen, hwt]
  have ho1 : binaryWeight 1 = 1 := by
    rw [show 1 = 2 ^ 0 by rfl]
    exact binaryWeight_two_pow 0
  have ho2 : binaryWeight 2 = 1 := by
    rw [show 2 = 2 ^ 1 by rfl]
    exact binaryWeight_two_pow 1
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

/-- Theorem 2.29, conditional on the balance lemma. -/
theorem no_regular_rank_of_balance (a b : Nat) (ha : 1 < a) (hoddA : a % 2 = 1)
    (hbal : ∃ d e : Nat, BalanceWitness a b d e) :
    ¬ ∃ A B : Nat, 0 < A ∧ 0 < B ∧
      ∀ n : Nat, profileRank A B (tStep a b n) < profileRank A B n := by
  intro h
  rcases h with ⟨A, B, hA0, hB, hdesc⟩
  have hA : 1 < A := profileRank_A_gt_one_of_descent a b A B hB hdesc
  rcases hbal with ⟨d, e, hw⟩
  rcases hw with ⟨hdOdd, heOdd, hbalEq, hbalWt⟩
  let L := binaryLength a
  have hL : binaryLength a = L := rfl
  let c := 2 ^ L - 1
  let k := L + binaryLength d + binaryLength e
  let n := c * 2 ^ k + d
  let v := a * c * 2 ^ (k - L) + e
  have hkL : L ≤ k := by dsimp [k]; omega
  have hdlt : d < 2 ^ k := by
    have h1 := binaryLength_pow_upper d
    have hmono : 2 ^ binaryLength d ≤ 2 ^ k :=
      Nat.pow_le_pow_right (show 0 < 2 by omega) (by dsimp [k]; omega)
    omega
  have helt : e < 2 ^ (k - L) := by
    have h1 := binaryLength_pow_upper e
    have hmono : 2 ^ binaryLength e ≤ 2 ^ (k - L) :=
      Nat.pow_le_pow_right (show 0 < 2 by omega) (by dsimp [k]; omega)
    omega
  have hLpos : 0 < L := by
    have h0 : L = 0 ∨ 0 < L := Nat.eq_zero_or_pos L
    rcases h0 with hL0 | hLpos
    · rw [hL0]
      have hz : a = 0 := by
        have h := binaryLength_pow_upper a
        rw [hL] at h
        rw [hL0] at h
        have h1 : a < 1 := by simpa using h
        omega
      omega
    · exact hLpos
  have hcpos : 0 < c := by
    dsimp [c]
    have h1 : 1 < 2 ^ L := by
      have h := one_lt_two_pow_succ (L - 1)
      have hL' : L = (L - 1) + 1 := by omega
      rw [hL']
      exact h
    omega
  have hstep : tStep a b n = 2 ^ L * v := by
    dsimp [n, v, c]
    exact tStep_reduction a b d e L ha hL hbalEq k hkL hdOdd
  have hnprof := reductionN_profile d L k hdlt hcpos
  have hvprof := reductionV_profile a e L k ha hoddA hL hLpos helt hkL
  have hrank : profileRank A B n = profileRank A B v := by
    unfold profileRank
    rcases hnprof with ⟨hnw, hnz⟩
    rcases hvprof with ⟨hvw, hvz⟩
    rw [hnw, hvw, hbalWt]
    rw [hnz, hvz, hbalWt]
  have hac : 0 < a * c := Nat.mul_pos (by omega) hcpos
  have hvpos : 0 < v := by
    dsimp [v]
    have h1 : 0 < a * c * 2 ^ (k - L) :=
      Nat.mul_pos hac (Nat.pow_pos (show 0 < 2 by omega))
    omega
  have hshift : profileRank A B (tStep a b n) = A ^ L * profileRank A B n := by
    rw [hstep]
    rw [profileRank_shift A B v L hvpos]
    rw [hrank]
  have hdesc2 := hdesc n
  rw [hshift] at hdesc2
  have hp : 0 < profileRank A B n := profileRank_pos A B n (by omega) hB
  have hAge2 : 2 ≤ A := by omega
  have hA1leL : 1 ≤ L := by omega
  have hAL : 2 ≤ A ^ L := by
    have hAeq : A = A ^ 1 := by simp
    have hpowle : A ^ 1 ≤ A ^ L :=
      Nat.pow_le_pow_right (by omega) hA1leL
    omega
  have hle : profileRank A B n ≤ A ^ L * profileRank A B n := by
    have h2p : profileRank A B n < 2 * profileRank A B n := by omega
    have h2le : 2 * profileRank A B n ≤ A ^ L * profileRank A B n :=
      Nat.mul_le_mul_right (profileRank A B n) hAL
    omega
  have hcontra : profileRank A B n < profileRank A B n :=
    Nat.lt_of_le_of_lt hle hdesc2
  exact (Nat.lt_irrefl _ hcontra)

/-- `2^m - 1` is odd for `0 < m`. -/
theorem odd_two_pow_sub_one (m : Nat) (hm : 0 < m) : (2 ^ m - 1) % 2 = 1 := by
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have h : m = (m - 1) + 1 := by omega
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1
      _ = 2 * 2 ^ (m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp]
  have h1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow (m - 1) 2 (by omega)
  omega

/-- `2^m + 1` is odd for `0 < m`. -/
theorem odd_two_pow_add_one (m : Nat) (hm : 0 < m) : (2 ^ m + 1) % 2 = 1 := by
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have h : m = (m - 1) + 1 := by omega
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1
      _ = 2 * 2 ^ (m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hp]
  omega

private theorem tStep_even (a b n q : Nat) (h : n % 2 = 0) (hd : n / 2 = q) :
    tStep a b n = q := by
  unfold tStep
  rw [if_pos h, hd]

private theorem tStep_odd (a b n q : Nat) (h : n % 2 = 1) (hm : a * n + b = q) :
    tStep a b n = q := by
  unfold tStep
  rw [if_neg (by omega)]
  exact hm

theorem tStep_five_one_one : tStep 5 1 1 = 6 := by
  exact tStep_odd 5 1 1 6 (by omega) (by omega)

theorem tStep_five_one_six : tStep 5 1 6 = 3 := by
  exact tStep_even 5 1 6 3 (by omega) (by omega)

theorem tStep_five_one_three : tStep 5 1 3 = 16 := by
  exact tStep_odd 5 1 3 16 (by omega) (by omega)

theorem tStep_five_one_sixteen : tStep 5 1 16 = 8 := by
  exact tStep_even 5 1 16 8 (by omega) (by omega)

theorem tStep_five_one_eight : tStep 5 1 8 = 4 := by
  exact tStep_even 5 1 8 4 (by omega) (by omega)

theorem tStep_five_one_four : tStep 5 1 4 = 2 := by
  exact tStep_even 5 1 4 2 (by omega) (by omega)

theorem tStep_five_one_two : tStep 5 1 2 = 1 := by
  exact tStep_even 5 1 2 1 (by omega) (by omega)

/-- Theorem 2.25, 5x+1 case: the trivial cycle excludes any descending rank. -/
theorem five_x_one_no_descent_profile_rank :
    ¬ ∃ A B : Nat, 0 < A ∧ 0 < B ∧
      ∀ n : Nat, profileRank A B (tStep 5 1 n) < profileRank A B n := by
  rintro ⟨A, B, _hA0, _hB, hdesc⟩
  have h1 := hdesc 1
  rw [tStep_five_one_one] at h1
  have h6 := hdesc 6
  rw [tStep_five_one_six] at h6
  have h3 := hdesc 3
  rw [tStep_five_one_three] at h3
  have h16 := hdesc 16
  rw [tStep_five_one_sixteen] at h16
  have h8 := hdesc 8
  rw [tStep_five_one_eight] at h8
  have h4 := hdesc 4
  rw [tStep_five_one_four] at h4
  have h2 := hdesc 2
  rw [tStep_five_one_two] at h2
  have hchain : profileRank A B 1 < profileRank A B 1 := by omega
  exact (Nat.lt_irrefl _ hchain)

/-- Mersenne family: no `A^z B^o` descent rank for `T_{2^m-1,b}`. -/
theorem mersenne_no_regular_rank (m b : Nat) (hm : 1 < m) (hb : IsOdd b) :
    ¬ ∃ A B : Nat, 0 < A ∧ 0 < B ∧
      ∀ n : Nat, profileRank A B (tStep (2 ^ m - 1) b n) < profileRank A B n := by
  have hbal := balance_mersenne (2 ^ m - 1) b m rfl hb
  have ha : 1 < 2 ^ m - 1 := by
    have hpow : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have h1 : m = (m - 1) + 1 := by omega
      have h2 : m - 1 = (m - 2) + 1 := by omega
      have hp1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
        calc
          2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1
          _ = 2 * 2 ^ (m - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hp2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
        calc
          2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by congr 1
          _ = 2 * 2 ^ (m - 2) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hp1, hp2]
      omega
    rw [hpow]
    have h1 : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow (m - 2) 2 (by omega)
    omega
  have hodd : (2 ^ m - 1) % 2 = 1 := odd_two_pow_sub_one m (by omega)
  exact no_regular_rank_of_balance (2 ^ m - 1) b ha hodd hbal

/-- `a = 2^m + 1`, `b = 1`: no `A^z B^o` descent rank. -/
theorem two_pow_add_one_no_regular_rank (m : Nat) (hm : 0 < m) :
    ¬ ∃ A B : Nat, 0 < A ∧ 0 < B ∧
      ∀ n : Nat, profileRank A B (tStep (2 ^ m + 1) 1 n) < profileRank A B n := by
  have hbal := balance_two_pow_add_one m hm
  have ha : 1 < 2 ^ m + 1 := by
    have h1 : 0 < 2 ^ m := Nat.pow_pos (show 0 < 2 by omega)
    omega
  have hodd : (2 ^ m + 1) % 2 = 1 := odd_two_pow_add_one m hm
  exact no_regular_rank_of_balance (2 ^ m + 1) 1 ha hodd hbal

end StringFlow
