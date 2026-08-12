import Mathlib
import Td1Interval

/-!
# TD-1 chain interpolation bounds

This module formalizes the 52.10 interval

    A0 <= A_chain <= A_max

for the A and B chain families used by TD-1.  The lower bound is a
general statement for every C3 chain (all weights at least 3); the
upper bounds use the family budgets `b = 1` and `b = 2`.
-/

namespace StringFlow.TD1

/-- `a0 (n+1) = 5^n + 8 * a0 n`. -/
theorem a0_succ (n : Nat) :
    a0 (n + 1) = 5 ^ n + 8 * a0 n := by
  unfold a0
  simp [rep3, StringFlow.GC.chainA, rep3_length]

/-- `3*(A0 + S3) = 2*8^Q - 89*5^(Q-2)` for `Q >= 2`. -/
theorem three_mul_a0_add_s3 (Q : Nat) (hQ : 2 ≤ Q) :
    3 * (a0 Q + s3 Q) = 2 * 8 ^ Q - 89 * 5 ^ (Q - 2) := by
  rw [Nat.mul_add, a0_three_mul Q, three_mul_s3 Q hQ]
  have h5 : 5 ^ Q = 25 * 5 ^ (Q - 2) := five_pow_eq_25_mul Q hQ
  have hle1 : 5 ^ Q ≤ 8 ^ Q := StringFlow.GC.five_pow_le_eight_pow Q
  have hle2 : 64 * 5 ^ (Q - 2) ≤ 8 ^ Q := s3_le_eight Q hQ
  rw [h5]
  omega

/-- Lower chain bound: a C3 chain is never below the all-three chain
`A0`. -/
theorem chainA_ge_a0 (ts : List Nat)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    a0 ts.length ≤ StringFlow.GC.chainA ts := by
  induction ts with
  | nil =>
      unfold a0
      simp [rep3, StringFlow.GC.chainA]
  | cons t ts ih =>
      have ht : 3 ≤ t := hge t (by simp)
      have htail : ∀ x ∈ ts, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      have ih' := ih htail
      have h8 : 8 ≤ 2 ^ t := by
        exact Nat.pow_le_pow_right (by decide : 0 < 2) ht
      change a0 (ts.length + 1) ≤
        5 ^ ts.length + 2 ^ t * StringFlow.GC.chainA ts
      rw [a0_succ ts.length]
      have hmul : 8 * a0 ts.length ≤ 2 ^ t * StringFlow.GC.chainA ts := by
        exact Nat.mul_le_mul h8 ih'
      omega

/-- Auxiliary upper bound for a chain of length `n` with budget
`3n + 1`: the maximum is achieved by putting the single excess at the
first weight. -/
def boundA (n : Nat) : Nat :=
  if n = 0 then 0 else 5 ^ (n - 1) + 16 * a0 (n - 1)

/-- `boundA (n+1) = 5^n + 16 * a0 n`. -/
theorem boundA_succ (n : Nat) :
    boundA (n + 1) = 5 ^ n + 16 * a0 n := by
  unfold boundA
  simp

/-- `boundA n <= 2 * a0 n`. -/
theorem boundA_le_two_a0 (n : Nat) : boundA n ≤ 2 * a0 n := by
  by_cases hn : n = 0
  · subst n
    simp [boundA]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hpred : n - 1 + 1 = n := by omega
    have ha := a0_succ (n - 1)
    rw [hpred] at ha
    unfold boundA
    simp [hn]
    rw [ha]
    have hle : 5 ^ (n - 1) ≤ 2 * 5 ^ (n - 1) := by omega
    omega

/-- The A-family upper endpoint satisfies
`A0(Q+1) + S3(Q+1) = 5^Q + 8 * boundA Q`. -/
theorem amaxA_succ_eq_bound (n : Nat) (hn : 1 ≤ n) :
    a0 (n + 1) + s3 (n + 1) = 5 ^ n + 8 * boundA n := by
  have hL := three_mul_a0_add_s3 (n + 1) (by omega : 2 ≤ n + 1)
  have hA : 3 * a0 (n - 1) = 8 ^ (n - 1) - 5 ^ (n - 1) :=
    a0_three_mul (n - 1)
  have h5 : 5 ^ n = 5 * 5 ^ (n - 1) := by
    have hsub : n = (n - 1) + 1 := by omega
    rw [hsub, Nat.pow_add]
    have hsub2 : n - 1 + 1 - 1 = n - 1 := by omega
    rw [hsub2]
    rw [show 5 ^ 1 = 5 by decide]
    rw [Nat.mul_comm]
  have h8 : 8 ^ (n + 1) = 64 * 8 ^ (n - 1) := by
    have hsub : n + 1 = (n - 1) + 2 := by omega
    rw [hsub, Nat.pow_add]
    rw [show 8 ^ 2 = 64 by decide]
    rw [Nat.mul_comm]
  have hL' : 3 * (a0 (n + 1) + s3 (n + 1)) =
      2 * 8 ^ (n + 1) - 89 * 5 ^ (n - 1) := by
    rw [show n + 1 - 2 = n - 1 by omega] at hL
    exact hL
  have hA' : 384 * a0 (n - 1) =
      128 * (8 ^ (n - 1) - 5 ^ (n - 1)) := by
    have h384 : 384 * a0 (n - 1) = 128 * (3 * a0 (n - 1)) := by omega
    rw [h384, hA]
  have hA'' : a0 (n - 1) * 384 =
      128 * (8 ^ (n - 1) - 5 ^ (n - 1)) := by
    rw [Nat.mul_comm]
    exact hA'
  have h3eq : 3 * (a0 (n + 1) + s3 (n + 1)) =
      3 * (5 ^ n + 8 * boundA n) := by
    rw [hL']
    unfold boundA
    have hn0 : n ≠ 0 := by omega
    simp [hn0]
    rw [h5]
    rw [h8]
    ring_nf
    rw [hA'']
    ring_nf
    have hle : 5 ^ (n - 1) ≤ 8 ^ (n - 1) :=
      StringFlow.GC.five_pow_le_eight_pow (n - 1)
    omega
  exact Nat.mul_left_cancel (by decide : 0 < 3) h3eq

/-- The sum of a C3 chain is at least `3 * length`. -/
theorem chain_sum_ge_three_mul (ts : List Nat)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    3 * ts.length ≤ ts.sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      have ht : 3 ≤ t := hge t (by simp)
      have htail : ∀ x ∈ ts, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      have ih' := ih htail
      simp [List.sum_cons]
      omega

/-- A chain with no excess budget satisfies `A_chain <= A0`. -/
theorem chainA_le_a0_no_excess (ts : List Nat)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum ≤ 3 * ts.length) :
    StringFlow.GC.chainA ts ≤ a0 ts.length := by
  induction ts with
  | nil =>
      unfold a0
      simp [rep3, StringFlow.GC.chainA]
  | cons t ts ih =>
      have ht : 3 ≤ t := hge t (by simp)
      have htail : ∀ x ∈ ts, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      simp [List.sum_cons] at hsum
      have hsumge : 3 * ts.length ≤ ts.sum := chain_sum_ge_three_mul ts htail
      have htle : t ≤ 3 := by omega
      have ht3 : t = 3 := by omega
      have htailsum : ts.sum ≤ 3 * ts.length := by omega
      have ih' := ih htail htailsum
      change StringFlow.GC.chainA (t :: ts) ≤ a0 (ts.length + 1)
      rw [ht3]
      simp [StringFlow.GC.chainA]
      rw [a0_succ ts.length]
      have hmul : 8 * StringFlow.GC.chainA ts ≤ 8 * a0 ts.length :=
        Nat.mul_le_mul_left 8 ih'
      omega

/-- A chain with budget `3n + 1` satisfies
`A_chain <= boundA n`. -/
theorem chainA_le_boundA (ts : List Nat)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum ≤ 3 * ts.length + 1) :
    StringFlow.GC.chainA ts ≤ boundA ts.length := by
  induction ts with
  | nil => simp [boundA, StringFlow.GC.chainA]
  | cons t ts ih =>
      have ht : 3 ≤ t := hge t (by simp)
      have htail : ∀ x ∈ ts, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      simp [List.sum_cons] at hsum
      have hsumge : 3 * ts.length ≤ ts.sum := chain_sum_ge_three_mul ts htail
      have htle4 : t ≤ 4 := by omega
      have htailsum1 : ts.sum ≤ 3 * ts.length + 1 := by omega
      have ih' := ih htail htailsum1
      by_cases ht3 : t = 3
      · have hchain : StringFlow.GC.chainA (t :: ts) =
            5 ^ ts.length + 8 * StringFlow.GC.chainA ts := by
          rw [ht3]
          simp [StringFlow.GC.chainA]
        change StringFlow.GC.chainA (t :: ts) ≤ boundA (ts.length + 1)
        rw [hchain, boundA_succ ts.length]
        have hb : 8 * StringFlow.GC.chainA ts ≤ 16 * a0 ts.length := by
          have h1 : 8 * StringFlow.GC.chainA ts ≤ 8 * boundA ts.length :=
            Nat.mul_le_mul_left 8 ih'
          have h2 : 8 * boundA ts.length ≤ 16 * a0 ts.length := by
            have hb2 := boundA_le_two_a0 ts.length
            nlinarith
          exact Nat.le_trans h1 h2
        nlinarith [hb]
      · have ht4 : t = 4 := by omega
        have htailsum0 : ts.sum ≤ 3 * ts.length := by omega
        have htaila0 := chainA_le_a0_no_excess ts htail htailsum0
        have hchain : StringFlow.GC.chainA (t :: ts) =
            5 ^ ts.length + 16 * StringFlow.GC.chainA ts := by
          rw [ht4]
          simp [StringFlow.GC.chainA]
        change StringFlow.GC.chainA (t :: ts) ≤ boundA (ts.length + 1)
        rw [hchain, boundA_succ ts.length]
        have hb : 16 * StringFlow.GC.chainA ts ≤ 16 * a0 ts.length :=
          Nat.mul_le_mul_left 16 htaila0
        nlinarith [hb]

/-- A-family upper interpolation bound:
`A_chain <= A0 + S3` for a chain with `t_1 = 3` and budget `b = 1`. -/
theorem chainA_le_amaxA (ts : List Nat)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum ≤ 3 * ts.length + 1) :
    StringFlow.GC.chainA ts ≤ amaxA ts.length := by
  cases ts with
  | nil =>
      simp at hQ
  | cons t rest =>
      have ht3 : t = 3 := hhead t rest rfl
      simp at hQ
      have htail : ∀ x ∈ rest, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      simp [List.sum_cons] at hsum
      have htailsum : rest.sum ≤ 3 * rest.length + 1 := by omega
      have htailb := chainA_le_boundA rest htail htailsum
      have hchain : StringFlow.GC.chainA (t :: rest) =
          5 ^ rest.length + 8 * StringFlow.GC.chainA rest := by
        rw [ht3]
        simp [StringFlow.GC.chainA]
      have hn : 1 ≤ rest.length := by omega
      have heq := amaxA_succ_eq_bound rest.length hn
      change StringFlow.GC.chainA (t :: rest) ≤
        amaxA (rest.length + 1)
      unfold amaxA
      rw [hchain, heq]
      nlinarith [htailb]

/-- `3 * A_max,5(Q+1) = 3 * (5^Q + 32*A0(Q))`. -/
theorem three_mul_amaxB_succ (n : Nat) (hn : 1 ≤ n) :
    3 * amaxB (n + 1) = 3 * (5 ^ n + 32 * a0 n) := by
  have hA : 3 * a0 n = 8 ^ n - 5 ^ n := a0_three_mul n
  have hS : 3 * s3 (n + 1) = 8 ^ (n + 1) - 64 * 5 ^ (n - 1) :=
    three_mul_s3 (n + 1) (by omega : 2 ≤ n + 1)
  have h5 : 5 ^ n = 5 * 5 ^ (n - 1) := by
    have hsub : n = (n - 1) + 1 := by omega
    rw [hsub, Nat.pow_add]
    have hsub2 : n - 1 + 1 - 1 = n - 1 := by omega
    rw [hsub2]
    rw [show 5 ^ 1 = 5 by decide]
    rw [Nat.mul_comm]
  have h8 : 8 ^ (n + 1) = 8 * 8 ^ n := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hSle : 64 * 5 ^ (n - 1) ≤ 8 ^ (n + 1) := by
    have h := s3_le_eight (n + 1) (by omega : 2 ≤ n + 1)
    simpa using h
  have hAle : 5 ^ n ≤ 8 ^ n := StringFlow.GC.five_pow_le_eight_pow n
  have hSadd : 3 * s3 (n + 1) + 64 * 5 ^ (n - 1) = 8 ^ (n + 1) := by
    omega
  have hAadd : 3 * a0 n + 5 ^ n = 8 ^ n := by
    omega
  have h12add : 12 * s3 (n + 1) + 256 * 5 ^ (n - 1) =
      4 * 8 ^ (n + 1) := by
    nlinarith [hSadd]
  have h96add : 96 * a0 n + 32 * 5 ^ n = 32 * 8 ^ n := by
    nlinarith [hAadd]
  have hcore : 12 * s3 (n + 1) + 96 * 5 ^ (n - 1) = 96 * a0 n := by
    rw [h8] at h12add
    rw [h5] at h96add
    ring_nf at h12add h96add
    nlinarith
  unfold amaxB
  rw [show n + 1 - 1 = n by omega, show n + 1 - 2 = n - 1 by omega]
  ring_nf
  have hs3 : s3 (1 + n) * 12 = 12 * s3 (n + 1) := by
    rw [show 1 + n = n + 1 by omega, Nat.mul_comm]
  have ha0 : a0 n * 96 = 96 * a0 n := by rw [Nat.mul_comm]
  rw [hs3, ha0]
  rw [← hcore]
  ring

/-- The B-family upper endpoint satisfies
`A_max,5(Q+1) = 5^Q + 32 * A0(Q)`. -/
theorem amaxB_succ_eq (n : Nat) (hn : 1 ≤ n) :
    amaxB (n + 1) = 5 ^ n + 32 * a0 n := by
  exact Nat.mul_left_cancel (by decide : 0 < 3)
    (three_mul_amaxB_succ n hn)

/-- B-family upper interpolation bound:
`A_chain <= A_max,5` for a chain with `t_1 = 5` and budget `b = 2`. -/
theorem chainA_le_amaxB (ts : List Nat)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum ≤ 3 * ts.length + 2) :
    StringFlow.GC.chainA ts ≤ amaxB ts.length := by
  cases ts with
  | nil =>
      simp at hQ
  | cons t rest =>
      have ht5 : t = 5 := hhead t rest rfl
      simp at hQ
      have htail : ∀ x ∈ rest, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      simp [List.sum_cons] at hsum
      have htailsum0 : rest.sum ≤ 3 * rest.length := by omega
      have htaila0 := chainA_le_a0_no_excess rest htail htailsum0
      have hchain : StringFlow.GC.chainA (t :: rest) =
          5 ^ rest.length + 32 * StringFlow.GC.chainA rest := by
        rw [ht5]
        simp [StringFlow.GC.chainA]
      have hn : 1 ≤ rest.length := by omega
      have heq := amaxB_succ_eq rest.length hn
      change StringFlow.GC.chainA (t :: rest) ≤
        amaxB (rest.length + 1)
      rw [hchain, heq]
      have hmul : 32 * StringFlow.GC.chainA rest ≤
          32 * a0 rest.length :=
        Nat.mul_le_mul_left 32 htaila0
      exact Nat.add_le_add_left hmul (5 ^ rest.length)

/-- In the B family the budget is tight: `t_1 = 5` and
`sum = 3*len + 2` force every remaining weight to be `3`, so
`A_chain = A_max,5` exactly. -/
theorem chainA_eq_amaxB (ts : List Nat)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum = 3 * ts.length + 2) :
    StringFlow.GC.chainA ts = amaxB ts.length := by
  cases ts with
  | nil => simp at hQ
  | cons t rest =>
      have ht5 : t = 5 := hhead t rest rfl
      have htail : ∀ x ∈ rest, 3 ≤ x := by
        intro x hx
        exact hge x (by simp [hx])
      have hrestsum : rest.sum = 3 * rest.length := by
        rw [ht5] at hsum
        simp [List.sum_cons] at hsum
        omega
      have htail_le : StringFlow.GC.chainA rest ≤ a0 rest.length :=
        chainA_le_a0_no_excess rest htail (by omega)
      have htail_ge : a0 rest.length ≤ StringFlow.GC.chainA rest :=
        chainA_ge_a0 rest htail
      have htail_eq : StringFlow.GC.chainA rest = a0 rest.length :=
        le_antisymm htail_le htail_ge
      have hchain : StringFlow.GC.chainA (t :: rest) =
          5 ^ rest.length + 32 * a0 rest.length := by
        rw [ht5]
        simp [StringFlow.GC.chainA, htail_eq]
      have hn : 1 ≤ rest.length := by
        simp at hQ
        omega
      have heq := amaxB_succ_eq rest.length hn
      change StringFlow.GC.chainA (t :: rest) = amaxB (rest.length + 1)
      rw [hchain, heq]

/-- The A-family endpoint is below `8^Q`. -/
theorem amaxA_lt_eight_pow (Q : Nat) (hQ : 2 ≤ Q) :
    amaxA Q < 8 ^ Q := by
  have h := three_mul_a0_add_s3 Q hQ
  have hlt : 2 * 8 ^ Q - 89 * 5 ^ (Q - 2) < 3 * 8 ^ Q := by
    have hpos : 0 < 89 * 5 ^ (Q - 2) := by positivity
    have hlt2 : 2 * 8 ^ Q - 89 * 5 ^ (Q - 2) < 2 * 8 ^ Q :=
      Nat.sub_lt (by positivity : 0 < 2 * 8 ^ Q) hpos
    have h2 : 2 * 8 ^ Q ≤ 3 * 8 ^ Q := by omega
    omega
  have h3 : 3 * amaxA Q < 3 * 8 ^ Q := by
    change 3 * (a0 Q + s3 Q) < 3 * 8 ^ Q
    calc
      3 * (a0 Q + s3 Q) = 2 * 8 ^ Q - 89 * 5 ^ (Q - 2) := h
      _ < 3 * 8 ^ Q := hlt
  exact Nat.lt_of_mul_lt_mul_left h3

/-- The B-family endpoint is below `2 * 8^Q`. -/
theorem amaxB_lt_two_eight_pow (Q : Nat) (hQ : 2 ≤ Q) :
    amaxB Q < 2 * 8 ^ Q := by
  have hQ1 : 1 ≤ Q - 1 := by omega
  have heq := amaxB_succ_eq (Q - 1) hQ1
  have hsub : (Q - 1) + 1 = Q := by omega
  rw [hsub] at heq
  have ha0 : 3 * a0 (Q - 1) = 8 ^ (Q - 1) - 5 ^ (Q - 1) :=
    a0_three_mul (Q - 1)
  have h5 : 5 ^ (Q - 1) < 8 ^ (Q - 1) := by
    exact StringFlow.GC.five_pow_lt_eight_pow (Q - 1) (by omega : 1 ≤ Q - 1)
  have h3lt : 3 * amaxB Q < 6 * 8 ^ Q := by
    rw [heq]
    have h3a : 3 * (5 ^ (Q - 1) + 32 * a0 (Q - 1)) =
        3 * 5 ^ (Q - 1) + 96 * a0 (Q - 1) := by ring
    rw [h3a]
    have h3a0 : 3 * a0 (Q - 1) < 8 ^ (Q - 1) := by
      rw [ha0]
      have h5pos : 0 < 5 ^ (Q - 1) := by positivity
      omega
    have h96 : 96 * a0 (Q - 1) < 32 * 8 ^ (Q - 1) := by
      have h' : 32 * (3 * a0 (Q - 1)) < 32 * 8 ^ (Q - 1) :=
        Nat.mul_lt_mul_of_pos_left h3a0 (by decide : 0 < 32)
      nlinarith
    have h3b : 3 * 5 ^ (Q - 1) < 3 * 8 ^ (Q - 1) :=
      Nat.mul_lt_mul_of_pos_left h5 (by decide : 0 < 3)
    have h48 : 6 * 8 ^ Q = 48 * 8 ^ (Q - 1) := by
      rw [show Q = (Q - 1) + 1 by omega, Nat.pow_add]
      simp
      omega
    rw [h48]
    omega
  have h6 : 3 * (2 * 8 ^ Q) = 6 * 8 ^ Q := by ring
  rw [← h6] at h3lt
  exact Nat.lt_of_mul_lt_mul_left h3lt

/-- Every C3 chain in either family satisfies `A_chain < 2*8^Q`. -/
theorem chainA_le_two_eight_pow (b Q : Nat) (ts : List Nat)
    (hb : b = 1 ∨ b = 2)
    (hQ : 2 ≤ Q) (hQlen : ts.length = Q)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum ≤ 3 * Q + b) :
    StringFlow.GC.chainA ts < 2 * 8 ^ Q := by
  rcases hb with rfl | rfl
  · have hle := chainA_le_amaxA ts (by omega)
      (by intro a as hts; simpa using hhead a as hts) hge (by omega)
    have hle' : StringFlow.GC.chainA ts ≤ amaxA Q := by
      simpa [hQlen] using hle
    have hmax := amaxA_lt_eight_pow Q hQ
    omega
  · have hle := chainA_le_amaxB ts (by omega)
      (by intro a as hts; simpa using hhead a as hts) hge (by omega)
    have hle' : StringFlow.GC.chainA ts ≤ amaxB Q := by
      simpa [hQlen] using hle
    have hmax := amaxB_lt_two_eight_pow Q hQ
    omega

end StringFlow.TD1
