import Td1Window

/-!
# S3 closed form and `A0 - S3`

This module formalizes the geometric tail

    S3(Q) = sum_{k=2}^{Q-1} 5^{Q-1-k} * 8^k

through its closed form

    S3(Q) = (8^Q - 64 * 5^(Q-2)) / 3

and proves the endpoint identity

    A0(Q) - S3(Q) = 13 * 5^(Q-2),

used by sections 52.13 and 52.15 of `ph_qb_gc_chain.md`.
-/

namespace StringFlow.TD1

/-- The closed form of `S3(Q) = sum_{k=2}^{Q-1} 5^{Q-1-k} 8^k`. -/
def s3 (Q : Nat) : Nat := (8 ^ Q - 64 * 5 ^ (Q - 2)) / 3

theorem five_pow_mod3 (n : Nat) : (5 ^ n) % 3 = (2 ^ n) % 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [Nat.pow_succ, Nat.mul_mod, ih,
        show 5 % 3 = 2 by decide]

theorem sixty_four_mul_five_pow_mod3 (n : Nat) :
    (64 * 5 ^ n) % 3 = (2 ^ n) % 3 := by
  rw [Nat.mul_mod, five_pow_mod3 n]
  rw [show 64 % 3 = 1 by decide]
  simp

theorem eight_pow_mod3 (Q : Nat) : (8 ^ Q) % 3 = (2 ^ (3 * Q)) % 3 := by
  rw [← StringFlow.GC.two_pow_three_mul_eq_eight_pow Q]

theorem sub_two_mod2 (Q : Nat) (hQ : 2 ≤ Q) : (Q - 2) % 2 = Q % 2 := by
  have hsum : (Q - 2) + 2 = Q := Nat.sub_add_cancel hQ
  calc
    (Q - 2) % 2 = ((Q - 2) + 2) % 2 := by
      rw [Nat.add_mod]
      simp
    _ = Q % 2 := by rw [hsum]

theorem three_mul_mod2 (Q : Nat) : (3 * Q) % 2 = Q % 2 := by
  rw [Nat.mul_mod]
  simp

theorem s3_residue_eq (Q : Nat) (hQ : 2 ≤ Q) :
    (64 * 5 ^ (Q - 2)) % 3 = (8 ^ Q) % 3 := by
  calc
    (64 * 5 ^ (Q - 2)) % 3 = (2 ^ (Q - 2)) % 3 :=
      sixty_four_mul_five_pow_mod3 (Q - 2)
    _ = (2 ^ (3 * Q)) % 3 := by
      rw [StringFlow.GC.two_pow_mod3 (Q - 2),
        StringFlow.GC.two_pow_mod3 (3 * Q)]
      rw [three_mul_mod2 Q, sub_two_mod2 Q hQ]
    _ = (8 ^ Q) % 3 := (eight_pow_mod3 Q).symm

theorem s3_le_eight (Q : Nat) (hQ : 2 ≤ Q) :
    64 * 5 ^ (Q - 2) ≤ 8 ^ Q := by
  have hpow : 8 ^ Q = 64 * 8 ^ (Q - 2) := by
    have hQ2 : Q = (Q - 2) + 2 := by omega
    calc
      8 ^ Q = 8 ^ ((Q - 2) + 2) := by rw [← hQ2]
      _ = 8 ^ (Q - 2) * 8 ^ 2 := by rw [Nat.pow_add]
      _ = 8 ^ (Q - 2) * 64 := by rw [show 8 ^ 2 = 64 by decide]
      _ = 64 * 8 ^ (Q - 2) := by rw [Nat.mul_comm]
  have hfive : 5 ^ (Q - 2) ≤ 8 ^ (Q - 2) :=
    StringFlow.GC.five_pow_le_eight_pow (Q - 2)
  have hmul := Nat.mul_le_mul_left 64 hfive
  rwa [← hpow] at hmul

theorem three_mul_s3 (Q : Nat) (hQ : 2 ≤ Q) :
    3 * s3 Q = 8 ^ Q - 64 * 5 ^ (Q - 2) := by
  unfold s3
  have hdiv : 3 ∣ 8 ^ Q - 64 * 5 ^ (Q - 2) :=
    StringFlow.Word.dvd_sub_of_mod_eq (64 * 5 ^ (Q - 2)) (8 ^ Q) 3
      (by decide) (s3_le_eight Q hQ) (s3_residue_eq Q hQ)
  have hmod : (8 ^ Q - 64 * 5 ^ (Q - 2)) % 3 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hdiv
  have h := Nat.div_add_mod (8 ^ Q - 64 * 5 ^ (Q - 2)) 3
  rw [hmod] at h
  omega

theorem five_pow_eq_25_mul (Q : Nat) (hQ : 2 ≤ Q) :
    5 ^ Q = 25 * 5 ^ (Q - 2) := by
  have hQ2 : Q = (Q - 2) + 2 := by omega
  calc
    5 ^ Q = 5 ^ ((Q - 2) + 2) := by rw [← hQ2]
    _ = 5 ^ (Q - 2) * 5 ^ 2 := by rw [Nat.pow_add]
    _ = 5 ^ (Q - 2) * 25 := by rw [show 5 ^ 2 = 25 by decide]
    _ = 25 * 5 ^ (Q - 2) := by rw [Nat.mul_comm]

/-- The endpoint identity `A0(Q) - S3(Q) = 13 * 5^(Q-2)`. -/
theorem a0_sub_s3 (Q : Nat) (hQ : 2 ≤ Q) :
    a0 Q - s3 Q = 13 * 5 ^ (Q - 2) := by
  have hA := a0_three_mul Q
  have hS := three_mul_s3 Q hQ
  have h5 := five_pow_eq_25_mul Q hQ
  have h64le : 64 * 5 ^ (Q - 2) ≤ 8 ^ Q := s3_le_eight Q hQ
  have h25le64 : 25 * 5 ^ (Q - 2) ≤ 64 * 5 ^ (Q - 2) := by omega
  have h25le8 : 25 * 5 ^ (Q - 2) ≤ 8 ^ Q := by omega
  have hge3 : 3 * s3 Q ≤ 3 * a0 Q := by
    rw [hS, hA, h5]
    omega
  have hge : s3 Q ≤ a0 Q := Nat.le_of_mul_le_mul_left hge3 (by decide : 0 < 3)
  have h3 : 3 * (a0 Q - s3 Q) = 39 * 5 ^ (Q - 2) := by
    rw [Nat.mul_sub_left_distrib, hA, hS, h5]
    omega
  have h3' : 3 * (a0 Q - s3 Q) = 3 * (13 * 5 ^ (Q - 2)) := by
    rw [h3]
    omega
  exact Nat.mul_left_cancel (by decide : 0 < 3) h3'

end StringFlow.TD1
