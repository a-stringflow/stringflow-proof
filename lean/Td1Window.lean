import Gc

/-!
# TD-1 ratio-window equivalences in cleared integer form

This module formalizes the algebraic core of `ph_qb_gc_chain.md`
section 52.16 without `Real`/`Rat` divisions.  For the A family
(`t_last = 1`, `t_1 = 3`) and the B family (`t_last = 2`,
`t_1 = 5`), the ratio-window comparisons `R < U` and `R < L` are
rewritten as integer inequalities between powers of 5 and 8.

The endpoint `A_0 = (8^Q - 5^Q)/3` is represented by the all-three
chain numerator `a0 Q`, whose `3 * a0 Q = 8^Q - 5^Q` identity is
already proved in `Gc.lean`.
-/

namespace StringFlow.TD1

/-- The all-three chain used for `A_0 = (8^Q - 5^Q)/3`. -/
def rep3 : Nat → List Nat
  | 0 => []
  | n + 1 => 3 :: rep3 n

theorem rep3_length (n : Nat) : (rep3 n).length = n := by
  induction n with
  | zero => simp [rep3]
  | succ n ih => simp [rep3, ih]

theorem allThree_rep3 (n : Nat) :
    StringFlow.GC.allThree (rep3 n) := by
  induction n with
  | zero => simp [rep3, StringFlow.GC.allThree]
  | succ n ih => simp [rep3, StringFlow.GC.allThree, ih]

/-- `A_0 = (8^Q - 5^Q)/3`, represented as the all-three chain
numerator. -/
def a0 (Q : Nat) : Nat :=
  StringFlow.GC.chainA (rep3 Q)

theorem a0_three_mul (Q : Nat) : 3 * a0 Q = 8 ^ Q - 5 ^ Q := by
  unfold a0
  have h := StringFlow.GC.three_mul_chainA (rep3 Q) (allThree_rep3 Q)
  have hlen := rep3_length Q
  rwa [hlen] at h

/-- `Z < 2` for the A family, cleared of the denominator 3. -/
theorem td1A_Z_lt_two_iff (Q m M0 : Nat) :
    (5 ^ Q * M0 + a0 Q) < 2 * 8 ^ Q * m ↔
      3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) < 6 * 8 ^ Q * m := by
  have hA := a0_three_mul Q
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_left (show 0 < 3 by decide)).2 h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (2 * 8 ^ Q * m) = 6 * 8 ^ Q * m := by
      rw [← show 3 * 2 = 6 by decide]
      ac_rfl
    rwa [hleft, hright] at hmul
  · intro h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (2 * 8 ^ Q * m) = 6 * 8 ^ Q * m := by
      rw [← show 3 * 2 = 6 by decide]
      ac_rfl
    have hmul : 3 * (5 ^ Q * M0 + a0 Q) < 3 * (2 * 8 ^ Q * m) := by
      rwa [← hleft, ← hright] at h
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- `Z < 4` for the B family, cleared of the denominator 3. -/
theorem td1B_Z_lt_four_iff (Q m M0 : Nat) :
    (5 ^ Q * M0 + a0 Q) < 4 * 8 ^ Q * m ↔
      3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) < 12 * 8 ^ Q * m := by
  have hA := a0_three_mul Q
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_left (show 0 < 3 by decide)).2 h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (4 * 8 ^ Q * m) = 12 * 8 ^ Q * m := by
      rw [← show 3 * 4 = 12 by decide]
      ac_rfl
    rwa [hleft, hright] at hmul
  · intro h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (4 * 8 ^ Q * m) = 12 * 8 ^ Q * m := by
      rw [← show 3 * 4 = 12 by decide]
      ac_rfl
    have hmul : 3 * (5 ^ Q * M0 + a0 Q) < 3 * (4 * 8 ^ Q * m) := by
      rwa [← hleft, ← hright] at h
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- `Z > 4` for the B family, cleared of the denominator 3. -/
theorem td1B_Z_gt_four_iff (Q m M0 : Nat) :
    4 * 8 ^ Q * m < 5 ^ Q * M0 + a0 Q ↔
      12 * 8 ^ Q * m < 3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
  have hA := a0_three_mul Q
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_left (show 0 < 3 by decide)).2 h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (4 * 8 ^ Q * m) = 12 * 8 ^ Q * m := by
      rw [← show 3 * 4 = 12 by decide]
      ac_rfl
    rwa [hright, hleft] at hmul
  · intro h
    have hleft : 3 * (5 ^ Q * M0 + a0 Q) =
        3 * 5 ^ Q * M0 + (8 ^ Q - 5 ^ Q) := by
      rw [Nat.mul_add, hA]
      ac_rfl
    have hright : 3 * (4 * 8 ^ Q * m) = 12 * 8 ^ Q * m := by
      rw [← show 3 * 4 = 12 by decide]
      ac_rfl
    have hmul : 3 * (4 * 8 ^ Q * m) < 3 * (5 ^ Q * M0 + a0 Q) := by
      rwa [← hright, ← hleft] at h
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- `a + (c-d) < b` iff `a+c < b+d` when `d <= c`. -/
theorem lt_add_sub_iff (a b c d : Nat) (hle : d ≤ c) :
    (a + (c - d) < b) ↔ (a + c < b + d) := by
  have hsum : (c - d) + d = c := Nat.sub_add_cancel hle
  constructor
  · intro h
    have hadd : a + (c - d) + d < b + d := Nat.add_lt_add_right h d
    have hrew : a + (c - d) + d = a + c := by
      rw [Nat.add_assoc, hsum]
    rwa [hrew] at hadd
  · intro h
    have hrew : a + (c - d) + d = a + c := by
      rw [Nat.add_assoc, hsum]
    have hadd : a + (c - d) + d < b + d := by
      rwa [← hrew] at h
    exact Nat.lt_of_add_lt_add_right hadd

/-- A-family lower window: `Z < 2` is the cleared form of
`R < L_A`. -/
theorem td1A_Z_lt_two_iff_R_lt_LA (Q m M0 : Nat) :
    (5 ^ Q * M0 + a0 Q < 2 * 8 ^ Q * m) ↔
      (3 * 5 ^ Q * M0 + 8 ^ Q < 6 * 8 ^ Q * m + 5 ^ Q) := by
  rw [td1A_Z_lt_two_iff Q m M0]
  have hge : 5 ^ Q ≤ 8 ^ Q := StringFlow.GC.five_pow_le_eight_pow Q
  exact lt_add_sub_iff (3 * 5 ^ Q * M0) (6 * 8 ^ Q * m) (8 ^ Q) (5 ^ Q) hge

/-- B-family lower window: `Z < 4` is the cleared form of
`R < L_B`. -/
theorem td1B_Z_lt_four_iff_R_lt_LB (Q m M0 : Nat) :
    (5 ^ Q * M0 + a0 Q < 4 * 8 ^ Q * m) ↔
      (3 * 5 ^ Q * M0 + 8 ^ Q < 12 * 8 ^ Q * m + 5 ^ Q) := by
  rw [td1B_Z_lt_four_iff Q m M0]
  have hge : 5 ^ Q ≤ 8 ^ Q := StringFlow.GC.five_pow_le_eight_pow Q
  exact lt_add_sub_iff (3 * 5 ^ Q * M0) (12 * 8 ^ Q * m) (8 ^ Q) (5 ^ Q) hge

/-- `R < L_A` for the A family, cleared of the denominators
`3*m` and `5^Q`. -/
theorem td1A_R_lt_LA_iff (Q m M0 : Nat) (hm : 0 < m) :
    3 * 5 ^ Q * M0 < (6 * m - 1) * 8 ^ Q + 5 ^ Q ↔
      M0 * (5 ^ Q * 3 * m) < ((6 * m - 1) * 8 ^ Q + 5 ^ Q) * m := by
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_right hm).2 h
    have hrewrite : (3 * 5 ^ Q * M0) * m = M0 * (5 ^ Q * 3 * m) := by
      ac_rfl
    rwa [hrewrite] at hmul
  · intro h
    have hrewrite : (3 * 5 ^ Q * M0) * m = M0 * (5 ^ Q * 3 * m) := by
      ac_rfl
    have h' : (3 * 5 ^ Q * M0) * m < ((6 * m - 1) * 8 ^ Q + 5 ^ Q) * m := by
      rwa [← hrewrite] at h
    have hleft' : m * (3 * 5 ^ Q * M0) <
        m * ((6 * m - 1) * 8 ^ Q + 5 ^ Q) := by
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h'
    exact (Nat.mul_lt_mul_left hm).1 hleft'

/-- `R < U_A` for the A family, cleared of the denominators
`25`, `3*m` and `5^Q`. -/
theorem td1A_R_lt_UA_iff (Q m M0 : Nat) (hm : 0 < m) :
    75 * 5 ^ Q * M0 < 25 * (6 * m - 2) * 8 ^ Q + 89 * 5 ^ Q ↔
      M0 * (25 * 5 ^ Q * 3 * m) <
        (25 * (6 * m - 2) * 8 ^ Q + 89 * 5 ^ Q) * m := by
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_right hm).2 h
    have hrewrite : (75 * 5 ^ Q * M0) * m = M0 * (25 * 5 ^ Q * 3 * m) := by
      rw [show 75 = 3 * 25 by decide]
      ac_rfl
    rwa [hrewrite] at hmul
  · intro h
    have hrewrite : (75 * 5 ^ Q * M0) * m = M0 * (25 * 5 ^ Q * 3 * m) := by
      rw [show 75 = 3 * 25 by decide]
      ac_rfl
    have h' : (75 * 5 ^ Q * M0) * m <
        (25 * (6 * m - 2) * 8 ^ Q + 89 * 5 ^ Q) * m := by
      rwa [← hrewrite] at h
    have hleft' : m * (75 * 5 ^ Q * M0) <
        m * (25 * (6 * m - 2) * 8 ^ Q + 89 * 5 ^ Q) := by
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h'
    exact (Nat.mul_lt_mul_left hm).1 hleft'

/-- `R < L_B` for the B family, cleared of the denominators
`3*m` and `5^Q`. -/
theorem td1B_R_lt_LB_iff (Q m M0 : Nat) (hm : 0 < m) :
    3 * 5 ^ Q * M0 < (12 * m - 1) * 8 ^ Q + 5 ^ Q ↔
      M0 * (5 ^ Q * 3 * m) < ((12 * m - 1) * 8 ^ Q + 5 ^ Q) * m := by
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_right hm).2 h
    have hrewrite : (3 * 5 ^ Q * M0) * m = M0 * (5 ^ Q * 3 * m) := by
      ac_rfl
    rwa [hrewrite] at hmul
  · intro h
    have hrewrite : (3 * 5 ^ Q * M0) * m = M0 * (5 ^ Q * 3 * m) := by
      ac_rfl
    have h' : (3 * 5 ^ Q * M0) * m < ((12 * m - 1) * 8 ^ Q + 5 ^ Q) * m := by
      rwa [← hrewrite] at h
    have hleft' : m * (3 * 5 ^ Q * M0) <
        m * ((12 * m - 1) * 8 ^ Q + 5 ^ Q) := by
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h'
    exact (Nat.mul_lt_mul_left hm).1 hleft'

/-- `R < U_B` for the B family, cleared of the denominators
`15`, `m` and `5^Q`. -/
theorem td1B_R_lt_UB_iff (Q m M0 : Nat) (hm : 0 < m) :
    15 * 5 ^ Q * M0 < 5 * (12 * m - 4) * 8 ^ Q + 29 * 5 ^ Q ↔
      M0 * (15 * 5 ^ Q * m) <
        (5 * (12 * m - 4) * 8 ^ Q + 29 * 5 ^ Q) * m := by
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_right hm).2 h
    have hrewrite : (15 * 5 ^ Q * M0) * m = M0 * (15 * 5 ^ Q * m) := by
      ac_rfl
    rwa [hrewrite] at hmul
  · intro h
    have hrewrite : (15 * 5 ^ Q * M0) * m = M0 * (15 * 5 ^ Q * m) := by
      ac_rfl
    have h' : (15 * 5 ^ Q * M0) * m <
        (5 * (12 * m - 4) * 8 ^ Q + 29 * 5 ^ Q) * m := by
      rwa [← hrewrite] at h
    have hleft' : m * (15 * 5 ^ Q * M0) <
        m * (5 * (12 * m - 4) * 8 ^ Q + 29 * 5 ^ Q) := by
      simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h'
    exact (Nat.mul_lt_mul_left hm).1 hleft'

end StringFlow.TD1
