import LteMacro

namespace StringFlow.Lte

/-- Inverse of a nonzero residue modulo 5. -/
def invMod5 (a : Nat) : Nat :=
  match a % 5 with
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 4
  | _ => 0

theorem mod5_decompose (x y u v t : Nat) :
    (5 * x + u + (5 * y + v) * t) % 5 = (u + v * t) % 5 := by
  rw [Nat.add_mul]
  have hfive : ∀ z : Nat, (5 * z) % 5 = 0 := by
    intro z
    rw [Nat.mul_mod]
    simp
  simp [Nat.add_mod, Nat.mul_mod, hfive, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem lift_residue_case (k a t r s : Nat) (hk : k % 5 = r) (ha : a % 5 = s)
    (h : (r + s * t) % 5 = 0) : (k + a * t) % 5 = 0 := by
  have hkdec : k = 5 * (k / 5) + r := by
    simpa [hk] using (Nat.div_add_mod k 5).symm
  have hadec : a = 5 * (a / 5) + s := by
    simpa [ha] using (Nat.div_add_mod a 5).symm
  rw [hkdec, hadec]
  rw [mod5_decompose (k / 5) (a / 5) r s t]
  exact h

theorem invMod5_lift_residue (a k : Nat) (ha : a % 5 ≠ 0) :
    (k + a * ((5 - (k % 5) * invMod5 a % 5) % 5)) % 5 = 0 := by
  have hk : k % 5 < 5 := Nat.mod_lt k (by decide)
  have ha5 : a % 5 < 5 := Nat.mod_lt a (by decide)
  have ha1 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have hk1 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases ha1 with ha1 | ha2 | ha3 | ha4 <;> rcases hk1 with hk0 | hk1 | hk2 | hk3 | hk4
  · simp [invMod5, ha1, hk0]
  · simp [invMod5, ha1, hk1]
    simpa using lift_residue_case k a 4 1 1 hk1 ha1 (by decide)
  · simp [invMod5, ha1, hk2]
    simpa using lift_residue_case k a 3 2 1 hk2 ha1 (by decide)
  · simp [invMod5, ha1, hk3]
    simpa using lift_residue_case k a 2 3 1 hk3 ha1 (by decide)
  · simp [invMod5, ha1, hk4]
    simpa using lift_residue_case k a 1 4 1 hk4 ha1 (by decide)
  · simp [invMod5, ha2, hk0]
  · simp [invMod5, ha2, hk1]
    simpa using lift_residue_case k a 2 1 2 hk1 ha2 (by decide)
  · simp [invMod5, ha2, hk2]
    simpa using lift_residue_case k a 4 2 2 hk2 ha2 (by decide)
  · simp [invMod5, ha2, hk3]
    simpa using lift_residue_case k a 1 3 2 hk3 ha2 (by decide)
  · simp [invMod5, ha2, hk4]
    simpa using lift_residue_case k a 3 4 2 hk4 ha2 (by decide)
  · simp [invMod5, ha3, hk0]
  · simp [invMod5, ha3, hk1]
    simpa using lift_residue_case k a 3 1 3 hk1 ha3 (by decide)
  · simp [invMod5, ha3, hk2]
    simpa using lift_residue_case k a 1 2 3 hk2 ha3 (by decide)
  · simp [invMod5, ha3, hk3]
    simpa using lift_residue_case k a 4 3 3 hk3 ha3 (by decide)
  · simp [invMod5, ha3, hk4]
    simpa using lift_residue_case k a 2 4 3 hk4 ha3 (by decide)
  · simp [invMod5, ha4, hk0]
  · simp [invMod5, ha4, hk1]
    simpa using lift_residue_case k a 1 1 4 hk1 ha4 (by decide)
  · simp [invMod5, ha4, hk2]
    simpa using lift_residue_case k a 2 2 4 hk2 ha4 (by decide)
  · simp [invMod5, ha4, hk3]
    simpa using lift_residue_case k a 3 3 4 hk3 ha4 (by decide)
  · simp [invMod5, ha4, hk4]
    simpa using lift_residue_case k a 4 4 4 hk4 ha4 (by decide)

theorem invMod5_spec (a : Nat) (ha : a % 5 ≠ 0) :
    (a * invMod5 a) % 5 = 1 := by
  have hlt : a % 5 < 5 := Nat.mod_lt a (by decide)
  have hcases : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · simp [invMod5, h1]
  · have hdec : a = 5 * (a / 5) + 2 := by
      have h := Nat.div_add_mod a 5
      rw [h2] at h
      omega
    simp [invMod5, h2]
    rw [hdec]
    rw [Nat.add_mul]
    rw [show (5 * (a / 5) * 3 + 2 * 3) % 5 = (2 * 3) % 5 by
      rw [Nat.add_mod, Nat.mul_mod]
      simp]
  · have hdec : a = 5 * (a / 5) + 3 := by
      have h := Nat.div_add_mod a 5
      rw [h3] at h
      omega
    simp [invMod5, h3]
    rw [hdec]
    rw [Nat.add_mul]
    rw [show (5 * (a / 5) * 2 + 3 * 2) % 5 = (3 * 2) % 5 by
      rw [Nat.add_mod, Nat.mul_mod]
      simp]
  · have hdec : a = 5 * (a / 5) + 4 := by
      have h := Nat.div_add_mod a 5
      rw [h4] at h
      omega
    simp [invMod5, h4]
    rw [hdec]
    rw [Nat.add_mul]
    rw [show (5 * (a / 5) * 4 + 4 * 4) % 5 = (4 * 4) % 5 by
      rw [Nat.add_mod, Nat.mul_mod]
      simp]

/-- Hensel lift coefficient for the inverse modulo a power of 5. -/
def invMod5Lift (a b N : Nat) : Nat :=
  let k := (a * b - 1) / 5 ^ N
  ((5 - (k % 5) * invMod5 a % 5) % 5)

theorem invMod5_lift_spec (a b N : Nat) (ha : a % 5 ≠ 0) (_hN : 1 ≤ N)
    (hmod : (a * b) % 5 ^ N = 1) :
    (a * (b + invMod5Lift a b N * 5 ^ N)) % 5 ^ (N + 1) = 1 := by
  have hge1 : 1 ≤ a * b := by
    cases h : a * b with
    | zero =>
        rw [h] at hmod
        have hm : (0 : Nat) % 5 ^ N = 0 := by simp
        rw [hm] at hmod
        omega
    | succ k =>
        omega
  have hdvd : 5 ^ N ∣ a * b - 1 :=
    StringFlow.Lte.dvd_sub_one_of_mod_eq_one (a * b) (5 ^ N) (by omega) hmod
  rcases hdvd with ⟨k, hk⟩
  let t := invMod5Lift a b N
  have hk' : a * b = 1 + k * 5 ^ N := by
    have hsub := Nat.sub_add_cancel hge1
    rw [hk] at hsub
    rw [Nat.mul_comm] at hsub
    omega
  have hkdiv : k = (a * b - 1) / 5 ^ N := by
    rw [hk]
    rw [Nat.mul_div_right k (Nat.pow_pos (show 0 < 5 by decide))]
  have ht_res : (k + a * t) % 5 = 0 := by
    dsimp [t, invMod5Lift]
    rw [← hkdiv]
    exact invMod5_lift_residue a k ha
  have h5dvd : 5 ∣ k + a * t := Nat.dvd_iff_mod_eq_zero.mpr ht_res
  rcases h5dvd with ⟨q, hq⟩
  have hprod : a * (b + t * 5 ^ N) = 1 + (k + a * t) * 5 ^ N := by
    rw [Nat.mul_add, hk']
    rw [← Nat.mul_assoc]
    rw [Nat.add_mul]
    omega
  have hpow5 : 5 ^ (N + 1) = 5 * 5 ^ N := by
    rw [show N + 1 = Nat.succ N by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have hqeq : (k + a * t) * 5 ^ N = 5 ^ (N + 1) * q := by
    rw [hq]
    rw [hpow5]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hmain : a * (b + t * 5 ^ N) = 1 + 5 ^ (N + 1) * q := by
    rw [hprod, hqeq]
  rw [hmain]
  rw [Nat.add_mul_mod_self_left 1 (5 ^ (N + 1)) q]
  have h1lt : 1 < 5 ^ (N + 1) :=
    Nat.pow_lt_pow_right (a := 5) (by decide : 1 < 5)
      (m := 0) (n := N + 1) (by omega)
  exact Nat.mod_eq_of_lt h1lt

/-- Inverse of a number coprime to 5 modulo `5^L`, by Hensel lifting. -/
def invFive : Nat → Nat → Nat
  | _, 0 => 1
  | a, 1 => invMod5 a
  | a, n + 2 =>
      let b := invFive a (n + 1)
      b + invMod5Lift a b (n + 1) * 5 ^ (n + 1)

theorem invFive_spec (a : Nat) (ha : a % 5 ≠ 0) :
    ∀ n, (a * invFive a (n + 1)) % 5 ^ (n + 1) = 1 := by
  intro n
  induction n with
  | zero =>
      simp [invFive]
      exact invMod5_spec a ha
  | succ n ih =>
      have hb : (a * invFive a (n + 1)) % 5 ^ (n + 1) = 1 := ih
      have hlift := invMod5_lift_spec a (invFive a (n + 1)) (n + 1) ha
        (by omega) hb
      have hdef : invFive a (n + 2) =
          invFive a (n + 1) +
            invMod5Lift a (invFive a (n + 1)) (n + 1) * 5 ^ (n + 1) := by
        simp [invFive]
      rw [hdef]
      have hpow : 5 ^ (n + 2) = 5 ^ ((n + 1) + 1) := by
        congr
      rw [hpow]
      exact hlift

end StringFlow.Lte
