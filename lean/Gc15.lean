import Gc

namespace StringFlow.GC

/-- One `t=1` step preserves the GC-15 cleared rise bound. -/
theorem gc15_rise_cons_one (ts c3 : List Nat)
    (ih : 3 * 5 ^ countTwo ts * risePart ts c3 ≤
      15 * 5 ^ (ts.length + c3.length + countTwo ts) -
        10 * 5 ^ (ts.length + c3.length) * 4 ^ countTwo ts) :
    3 * 5 ^ countTwo ts * risePart (1 :: ts) c3 ≤
      15 * 5 ^ ((1 :: ts).length + c3.length + countTwo ts) -
        10 * 5 ^ ((1 :: ts).length + c3.length) * 4 ^ countTwo ts := by
  let U : Nat := countTwo ts
  let L : Nat := ts.length
  let Q : Nat := c3.length
  let A : Nat := 5 ^ (L + Q + U)
  let B : Nat := 5 ^ (L + Q) * 4 ^ U
  have hih' : 3 * 5 ^ U * risePart ts c3 ≤ 15 * A - 10 * B := by
    simpa [U, L, Q, A, B, Nat.mul_assoc] using ih
  have hBleA : B ≤ A := by
    have h4 : 4 ^ U ≤ 5 ^ U := four_pow_le_five_pow U
    have hmul := Nat.mul_le_mul_right (5 ^ (L + Q)) h4
    have hpow : 5 ^ U * 5 ^ (L + Q) = 5 ^ (L + Q + U) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow] at hmul
    simpa [A, B, Nat.mul_comm] using hmul
  have hterm : 3 * 5 ^ U * (5 ^ (Q + L) * 2) ≤ 6 * A := by
    have hpowA : 5 ^ U * 5 ^ (Q + L) = A := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hswap : 3 * 5 ^ U * (5 ^ (Q + L) * 2) =
        (3 * (5 ^ U * 5 ^ (Q + L))) * 2 := by ac_rfl
    rw [hswap, hpowA]
    omega
  have htail : 3 * 5 ^ U * (2 * risePart ts c3) ≤
      2 * (15 * A - 10 * B) := by
    have hswap : 3 * 5 ^ U * (2 * risePart ts c3) =
        2 * (3 * 5 ^ U * risePart ts c3) := by ac_rfl
    rw [hswap]
    exact Nat.mul_le_mul_left 2 hih'
  have hsum' : 3 * 5 ^ U * (5 ^ (Q + L) * 2 + 2 * risePart ts c3) ≤
      6 * A + 2 * (15 * A - 10 * B) := by
    have hdist : 3 * 5 ^ U * (5 ^ (Q + L) * 2 + 2 * risePart ts c3) =
        3 * 5 ^ U * (5 ^ (Q + L) * 2) +
          3 * 5 ^ U * (2 * risePart ts c3) := by rw [Nat.mul_add]
    rw [hdist]
    exact Nat.add_le_add hterm htail
  have hAeq : 6 * A + 2 * (15 * A - 10 * B) = 36 * A - 20 * B := by
    omega
  have htarget : 36 * A - 20 * B ≤
      15 * 5 ^ (L + 1 + Q + U) - 10 * 5 ^ (L + 1 + Q) * 4 ^ U := by
    have hA5 : 5 ^ (L + 1 + Q + U) = 5 * A := by
      rw [show L + 1 + Q + U = (L + Q + U) + 1 by omega]
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
    have hB5 : 10 * 5 ^ (L + 1 + Q) * 4 ^ U = 50 * B := by
      rw [show L + 1 + Q = (L + Q) + 1 by omega]
      rw [Nat.pow_succ]
      have hprod : 10 * (5 ^ (L + Q) * 5) * 4 ^ U =
          (10 * 5) * (5 ^ (L + Q) * 4 ^ U) := by ac_rfl
      rw [hprod]
    rw [hA5, hB5]
    omega
  have hgoal : 3 * 5 ^ U * risePart (1 :: ts) c3 ≤
      15 * 5 ^ ((1 :: ts).length + c3.length + U) -
        10 * 5 ^ ((1 :: ts).length + c3.length) * 4 ^ U := by
    change 3 * 5 ^ U * (5 ^ (Q + L) * 2 + 2 * risePart ts c3) ≤
      15 * 5 ^ (L + 1 + Q + U) - 10 * 5 ^ (L + 1 + Q) * 4 ^ U
    calc
      _ ≤ 6 * A + 2 * (15 * A - 10 * B) := hsum'
      _ = 36 * A - 20 * B := hAeq
      _ ≤ 15 * 5 ^ (L + 1 + Q + U) - 10 * 5 ^ (L + 1 + Q) * 4 ^ U := htarget
  exact hgoal

/-- One `t=2` step preserves the GC-15 cleared rise bound. -/
theorem gc15_rise_cons_two (ts c3 : List Nat)
    (ih : 3 * 5 ^ countTwo ts * risePart ts c3 ≤
      15 * 5 ^ (ts.length + c3.length + countTwo ts) -
        10 * 5 ^ (ts.length + c3.length) * 4 ^ countTwo ts) :
    3 * 5 ^ (countTwo ts + 1) * risePart (2 :: ts) c3 ≤
      15 * 5 ^ ((2 :: ts).length + c3.length + (countTwo ts + 1)) -
        10 * 5 ^ ((2 :: ts).length + c3.length) * 4 ^ (countTwo ts + 1) := by
  let U : Nat := countTwo ts
  let L : Nat := ts.length
  let Q : Nat := c3.length
  let A : Nat := 5 ^ (L + Q + U)
  let B : Nat := 5 ^ (L + Q) * 4 ^ U
  have hih' : 3 * 5 ^ U * risePart ts c3 ≤ 15 * A - 10 * B := by
    simpa [U, L, Q, A, B, Nat.mul_assoc] using ih
  have hBleA : B ≤ A := by
    have h4 : 4 ^ U ≤ 5 ^ U := four_pow_le_five_pow U
    have hmul := Nat.mul_le_mul_right (5 ^ (L + Q)) h4
    have hpow : 5 ^ U * 5 ^ (L + Q) = 5 ^ (L + Q + U) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow] at hmul
    simpa [A, B, Nat.mul_comm] using hmul
  have hpowA : 5 ^ (U + 1) * 5 ^ (Q + L) = 5 * A := by
    rw [← Nat.pow_add]
    rw [show U + 1 + (Q + L) = (L + Q + U) + 1 by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have hterm : 3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4) ≤ 60 * A := by
    have hswap : 3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4) =
        (3 * (5 ^ (U + 1) * 5 ^ (Q + L))) * 4 := by ac_rfl
    rw [hswap, hpowA]
    omega
  have htail : 3 * 5 ^ (U + 1) * (4 * risePart ts c3) ≤
      20 * (15 * A - 10 * B) := by
    have hscalar : 3 * 5 ^ (U + 1) * 4 = 20 * (3 * 5 ^ U) := by
      rw [Nat.pow_succ, Nat.mul_comm]
      omega
    have hswap : 3 * 5 ^ (U + 1) * (4 * risePart ts c3) =
        20 * (3 * 5 ^ U * risePart ts c3) := by
      calc
        3 * 5 ^ (U + 1) * (4 * risePart ts c3)
            = (3 * 5 ^ (U + 1) * 4) * risePart ts c3 := by ac_rfl
        _ = (20 * (3 * 5 ^ U)) * risePart ts c3 := by rw [hscalar]
        _ = 20 * (3 * 5 ^ U * risePart ts c3) := by ac_rfl
    rw [hswap]
    exact Nat.mul_le_mul_left 20 hih'
  have hsum' : 3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4 + 4 * risePart ts c3) ≤
      60 * A + 20 * (15 * A - 10 * B) := by
    have hdist : 3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4 + 4 * risePart ts c3) =
        3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4) +
          3 * 5 ^ (U + 1) * (4 * risePart ts c3) := by rw [Nat.mul_add]
    rw [hdist]
    exact Nat.add_le_add hterm htail
  have hAeq : 60 * A + 20 * (15 * A - 10 * B) = 360 * A - 200 * B := by
    omega
  have htarget : 360 * A - 200 * B ≤
      15 * 5 ^ (L + 1 + Q + (U + 1)) -
        10 * 5 ^ (L + 1 + Q) * 4 ^ (U + 1) := by
    have hA25 : 5 ^ (L + 1 + Q + (U + 1)) = 25 * A := by
      rw [show L + 1 + Q + (U + 1) = (L + Q + U) + 2 by omega]
      rw [Nat.pow_add]
      rw [show 5 ^ 2 = 25 by decide]
      rw [Nat.mul_comm]
    have hB20 : 10 * 5 ^ (L + 1 + Q) * 4 ^ (U + 1) = 200 * B := by
      rw [show L + 1 + Q = (L + Q) + 1 by omega]
      rw [Nat.pow_succ]
      rw [show 4 ^ (U + 1) = 4 * 4 ^ U by
        rw [Nat.pow_succ, Nat.mul_comm]]
      have hprod : 10 * (5 ^ (L + Q) * 5) * (4 * 4 ^ U) =
          (10 * 5 * 4) * (5 ^ (L + Q) * 4 ^ U) := by ac_rfl
      rw [hprod]
    rw [hA25, hB20]
    omega
  have hgoal : 3 * 5 ^ (U + 1) * risePart (2 :: ts) c3 ≤
      15 * 5 ^ ((2 :: ts).length + c3.length + (U + 1)) -
        10 * 5 ^ ((2 :: ts).length + c3.length) * 4 ^ (U + 1) := by
    change 3 * 5 ^ (U + 1) * (5 ^ (Q + L) * 4 + 4 * risePart ts c3) ≤
      15 * 5 ^ (L + 1 + Q + (U + 1)) -
        10 * 5 ^ (L + 1 + Q) * 4 ^ (U + 1)
    calc
      _ ≤ 60 * A + 20 * (15 * A - 10 * B) := hsum'
      _ = 360 * A - 200 * B := hAeq
      _ ≤ 15 * 5 ^ (L + 1 + Q + (U + 1)) -
          10 * 5 ^ (L + 1 + Q) * 4 ^ (U + 1) := htarget
  exact hgoal

/-- GC-15 general `U`: a rising segment with `U` steps of weight `2`
contributes at most `F(U) * 5^P` to the PMI numerator, cleared as
`3*5^U*risePart <= 15*5^(P+U)-10*5^P*4^U`. -/
theorem gc15_risePart_bound (rise c3 : List Nat)
    (hrise : ∀ t ∈ rise, t = 1 ∨ t = 2) :
    3 * 5 ^ countTwo rise * risePart rise c3 ≤
      15 * 5 ^ (rise.length + c3.length + countTwo rise) -
        10 * 5 ^ (rise.length + c3.length) * 4 ^ countTwo rise := by
  induction rise generalizing c3 with
  | nil => simp [risePart, countTwo]
  | cons t ts ih =>
      rcases hrise t (by simp) with rfl | rfl
      · have hU : countTwo (1 :: ts) = countTwo ts := by simp [countTwo]
        rw [hU]
        exact gc15_rise_cons_one ts c3
          (ih c3 (fun x hx => hrise x (by simp [hx])))
      · have hU : countTwo (2 :: ts) = countTwo ts + 1 := by
          simp [countTwo]
          omega
        rw [hU]
        exact gc15_rise_cons_two ts c3
          (ih c3 (fun x hx => hrise x (by simp [hx])))

end StringFlow.GC
