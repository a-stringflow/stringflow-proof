import Gc

/-!
# GC-13: first-run length bound for the small-`P` frame-A branches

The analytic statement in `ph_qb_gc_chain.md` section 19 uses
`r1 <= floor(log2(3*m_max+1))` and the `t=2` variant.  Without
`Real`/`log`, this module formalizes the cleared integer core: with
`D = 2^T - 5^P` and `m_max = (4*5^P + D)/(3D)`, the bounds are
certified by exact power inequalities, and the small-`P` table is
checked by `native_decide`.
-/

namespace StringFlow.GC

/-- `T = ceil(P * log2 5)` for the six frame-A small `P`. -/
def gc13T : Nat → Nat
  | 31 => 72
  | 59 => 137
  | 205 => 476
  | 351 => 815
  | 497 => 1154
  | 643 => 1493
  | _ => 0

/-- The certified `r1` cap from section 19.2. -/
def gc13R1Max : Nat → Nat
  | 31 => 8
  | 59 => 10
  | 205 => 10
  | 351 => 11
  | 497 => 12
  | 643 => 14
  | _ => 0

/-- Exact power certificate for the two GC-13 inequalities. -/
def gc13Cert (P : Nat) : Bool :=
  let T := gc13T P
  let D := 2 ^ T - 5 ^ P
  let R := gc13R1Max P
  decide (0 < D &&
    D * 2 ^ (R + 1) > 4 * 5 ^ P + 2 * D &&
    D * 2 ^ (R + 1) > 5 * 5 ^ P + 3 * D)

/-- All six small-`P` certificates. -/
def gc13AllOK : Bool :=
  gc13Cert 31 && gc13Cert 59 && gc13Cert 205 &&
  gc13Cert 351 && gc13Cert 497 && gc13Cert 643

theorem gc13_allOK_check : gc13AllOK = true := by
  native_decide

/-- `2^r < 2^(R+1)` implies `r <= R`. -/
theorem pow_two_lt_imp_le (r R : Nat) (h : 2 ^ r < 2 ^ (R + 1)) :
    r ≤ R := by
  by_cases hR : r ≤ R
  · exact hR
  · exfalso
    have hRlt : R < r := by omega
    have hle : 2 ^ (R + 1) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (show 0 < 2 by decide) (by omega)
    exact (Nat.lt_irrefl (2 ^ (R + 1))) (Nat.lt_of_le_of_lt hle h)

/-- GC-13 for `t(m)=1`: cleared m window plus the power certificate
give `r1 <= R`. -/
theorem gc13_t1_bound (m r P T R D : Nat)
    (_hD : D = 2 ^ T - 5 ^ P)
    (_hPos : 0 < D)
    (hWindow : D * (3 * m + 1) ≤ 4 * 5 ^ P + 2 * D)
    (hPow : D * 2 ^ (R + 1) > 4 * 5 ^ P + 2 * D)
    (hRun : 2 ^ r ≤ 3 * m + 1) :
    r ≤ R := by
  have hlt : 3 * m + 1 < 2 ^ (R + 1) := by
    have hmul : D * (3 * m + 1) < D * 2 ^ (R + 1) :=
      Nat.lt_of_le_of_lt hWindow hPow
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hlt2 : 2 ^ r < 2 ^ (R + 1) := Nat.lt_of_le_of_lt hRun hlt
  exact pow_two_lt_imp_le r R hlt2

/-- GC-13 for `t(m)=2`: `X0 = (5m+1)/4` and the same certificate. -/
theorem gc13_t2_bound (m r P T R D : Nat)
    (_hD : D = 2 ^ T - 5 ^ P)
    (_hPos : 0 < D)
    (hdiv : (5 * m + 1) % 4 = 0)
    (hWindow : D * (15 * m + 7) ≤ 20 * 5 ^ P + 12 * D)
    (hPow : D * 2 ^ (R + 1) > 5 * 5 ^ P + 3 * D)
    (hRun : 2 ^ r ≤ 3 * ((5 * m + 1) / 4) + 1) :
    r ≤ R := by
  have hlt4 : 15 * m + 7 < 4 * 2 ^ (R + 1) := by
    have hPow4 : 20 * 5 ^ P + 12 * D < 4 * (D * 2 ^ (R + 1)) := by
      have h4 : 4 * (5 * 5 ^ P + 3 * D) <
          4 * (D * 2 ^ (R + 1)) :=
        (Nat.mul_lt_mul_left (show 0 < 4 by decide)).2 hPow
      have h4eq : 4 * (5 * 5 ^ P + 3 * D) =
          20 * 5 ^ P + 12 * D := by omega
      rwa [h4eq] at h4
    have hDmul0 : D * (15 * m + 7) < 4 * (D * 2 ^ (R + 1)) :=
      Nat.lt_of_le_of_lt hWindow hPow4
    have hEq : 4 * (D * 2 ^ (R + 1)) =
        D * (4 * 2 ^ (R + 1)) := by ac_rfl
    have hDmul : D * (15 * m + 7) < D * (4 * 2 ^ (R + 1)) := by
      rwa [hEq] at hDmul0
    exact Nat.lt_of_mul_lt_mul_left hDmul
  have hX : 4 * ((5 * m + 1) / 4) = 5 * m + 1 := by
    have h := Nat.div_add_mod (5 * m + 1) 4
    rw [hdiv] at h
    omega
  have hxbound : 3 * ((5 * m + 1) / 4) + 1 < 2 ^ (R + 1) := by
    have h4x : 4 * (3 * ((5 * m + 1) / 4) + 1) =
        15 * m + 7 := by
      calc
        4 * (3 * ((5 * m + 1) / 4) + 1)
            = 12 * ((5 * m + 1) / 4) + 4 := by omega
        _ = 3 * (4 * ((5 * m + 1) / 4)) + 4 := by omega
        _ = 3 * (5 * m + 1) + 4 := by rw [hX]
        _ = 15 * m + 7 := by omega
    have hmul : 4 * (3 * ((5 * m + 1) / 4) + 1) <
        4 * 2 ^ (R + 1) := by
      rw [h4x]
      exact hlt4
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hlt2 : 2 ^ r < 2 ^ (R + 1) := Nat.lt_of_le_of_lt hRun hxbound
  exact pow_two_lt_imp_le r R hlt2

/-- The six long-rising `(P,L)` pairs from section 19.4. -/
def gc13LongRise (P L : Nat) : Prop :=
  (P = 31 ∧ L = 11) ∨ (P = 59 ∧ L = 20) ∨ (P = 205 ∧ L = 70) ∨
  (P = 351 ∧ L = 119) ∨ (P = 497 ∧ L = 169) ∨ (P = 643 ∧ L = 218)

/-- U=0 closure for `P = 31`. -/
theorem gc13_u0_31 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ20 : Q ≤ 20)
    (hL : L = 31 - Q) : gc13R1Max 31 < L := by
  change 8 < L
  omega

/-- U=0 closure for `P = 59`. -/
theorem gc13_u0_59 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ39 : Q ≤ 39)
    (hL : L = 59 - Q) : gc13R1Max 59 < L := by
  change 10 < L
  omega

/-- U=0 closure for `P = 205`. -/
theorem gc13_u0_205 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ135 : Q ≤ 135)
    (hL : L = 205 - Q) : gc13R1Max 205 < L := by
  change 10 < L
  omega

/-- U=0 closure for `P = 351`. -/
theorem gc13_u0_351 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ232 : Q ≤ 232)
    (hL : L = 351 - Q) : gc13R1Max 351 < L := by
  change 11 < L
  omega

/-- U=0 closure for `P = 497`. -/
theorem gc13_u0_497 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ328 : Q ≤ 328)
    (hL : L = 497 - Q) : gc13R1Max 497 < L := by
  change 12 < L
  omega

/-- U=0 closure for `P = 643`. -/
theorem gc13_u0_643 (Q L : Nat) (hQ8 : 8 ≤ Q) (hQ425 : Q ≤ 425)
    (hL : L = 643 - Q) : gc13R1Max 643 < L := by
  change 14 < L
  omega

/-- The long-rising pairs contradict any GC-13 first-run cap. -/
theorem gc13_long_rise_contradicts (P L : Nat)
    (h : gc13LongRise P L) (hRun : L ≤ gc13R1Max P) : False := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6
  · rcases h1 with ⟨rfl, rfl⟩
    change 11 ≤ 8 at hRun
    omega
  · rcases h2 with ⟨rfl, rfl⟩
    change 20 ≤ 10 at hRun
    omega
  · rcases h3 with ⟨rfl, rfl⟩
    change 70 ≤ 10 at hRun
    omega
  · rcases h4 with ⟨rfl, rfl⟩
    change 119 ≤ 11 at hRun
    omega
  · rcases h5 with ⟨rfl, rfl⟩
    change 169 ≤ 12 at hRun
    omega
  · rcases h6 with ⟨rfl, rfl⟩
    change 218 ≤ 14 at hRun
    omega

/-- GC-7 m window in the cleared form used by GC-13:
`D*(3m+1) <= 4*5^P + 2*D`. -/
theorem gc7_window_for_gc13 (rise c3 : List Nat) (m : Nat)
    (hpm : pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hle : 5 ^ (rise.length + c3.length) ≤ 2 ^ (rise.sum + c3.sum))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) *
        (3 * m + 1) ≤
      4 * 5 ^ (rise.length + c3.length) +
        2 * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) := by
  let P : Nat := rise.length + c3.length
  let T : Nat := rise.sum + c3.sum
  have hgc : (2 ^ T - 5 ^ P) * (3 * m) ≤ 3 * 5 ^ P + 2 ^ T := by
    have h := gc7_m_cleared_bound rise c3 m hpm hrise hc3
    simpa [P, T, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hDle : 5 ^ P ≤ 2 ^ T := by simpa [P, T] using hle
  have hsum : 5 ^ P + (2 ^ T - 5 ^ P) = 2 ^ T := Nat.add_sub_of_le hDle
  calc
    (2 ^ T - 5 ^ P) * (3 * m + 1)
        = (2 ^ T - 5 ^ P) * (3 * m) + (2 ^ T - 5 ^ P) := by
          rw [Nat.mul_add]
          rw [show (2 ^ T - 5 ^ P) * 1 = 2 ^ T - 5 ^ P by simp]
    _ ≤ (3 * 5 ^ P + 2 ^ T) + (2 ^ T - 5 ^ P) := by
          exact Nat.add_le_add_right hgc (2 ^ T - 5 ^ P)
    _ = 4 * 5 ^ P + 2 * (2 ^ T - 5 ^ P) := by
          rw [← hsum]
          omega

end StringFlow.GC
