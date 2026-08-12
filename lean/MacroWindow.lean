import AutomatonInterface

namespace StringFlow.Automaton

/-- One `t=1` step followed by `a-1` steps of `t=2`. -/
def macroEnd (r0 a : Nat) : Nat :=
  twoRun ((5 * r0 + 1) / 2) (a - 1)

/-- Exact macro closed form:
`(r_a+1)*2^(2a-1) = 5^(a-1)*(5*r_0+3)`. -/
theorem macroEnd_plus_one_mul (r0 a : Nat) (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0) :
    (macroEnd r0 a + 1) * 2 ^ (2 * a - 1) = 5 ^ (a - 1) * (5 * r0 + 3) := by
  have hclosed := twoRun_plus_one_mul (a - 1) ((5 * r0 + 1) / 2) h2
  have hr1 : ((5 * r0 + 1) / 2 + 1) * 2 = 5 * r0 + 3 := by
    have hdiv := Nat.div_add_mod (5 * r0 + 1) 2
    rw [h1] at hdiv
    omega
  have h4 : 2 ^ (2 * a - 1) = 2 * 4 ^ (a - 1) := by
    calc
      2 ^ (2 * a - 1) = 2 ^ ((2 * (a - 1)) + 1) := by
          congr 1
          omega
      _ = 2 * 2 ^ (2 * (a - 1)) := by
          rw [Nat.pow_succ]
          rw [Nat.mul_comm]
      _ = 2 * 4 ^ (a - 1) := by
          have hpow : 4 ^ (a - 1) = 2 ^ (2 * (a - 1)) := by
            rw [show 4 = 2 ^ 2 by rfl]
            rw [Nat.pow_mul]
          rw [hpow]
  calc
    (macroEnd r0 a + 1) * 2 ^ (2 * a - 1)
        = ((macroEnd r0 a + 1) * 4 ^ (a - 1)) * 2 := by
            rw [h4]
            rw [Nat.mul_comm 2 (4 ^ (a - 1))]
            rw [← Nat.mul_assoc]
    _ = (5 ^ (a - 1) * (((5 * r0 + 1) / 2) + 1)) * 2 := by
            unfold macroEnd
            rw [hclosed]
    _ = 5 ^ (a - 1) * ((((5 * r0 + 1) / 2) + 1) * 2) := by
            rw [Nat.mul_assoc]
    _ = 5 ^ (a - 1) * (5 * r0 + 3) := by rw [hr1]

/-- Exact valuation of the macro endpoint:
`v2(r_a+1) = v2(5*r_0+3) - (2*a-1)`. -/
theorem macroEnd_valuation (r0 a : Nat) (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hv : 2 * a - 1 ≤ twoValuation (5 * r0 + 3)) :
    twoValuation (macroEnd r0 a + 1) = twoValuation (5 * r0 + 3) - (2 * a - 1) := by
  have hclosed := macroEnd_plus_one_mul r0 a ha h1 h2
  have hleft : twoValuation ((macroEnd r0 a + 1) * 2 ^ (2 * a - 1)) =
      twoValuation (macroEnd r0 a + 1) + (2 * a - 1) := by
    rw [Nat.mul_comm]
    have h := StringFlow.Lte.twoValuation_mul_two_pow (2 * a - 1)
      (macroEnd r0 a + 1) (by omega)
    simpa [Nat.add_comm] using h
  have hright : twoValuation (5 ^ (a - 1) * (5 * r0 + 3)) =
      twoValuation (5 * r0 + 3) := by
    exact StringFlow.Lte.twoValuation_five_pow_mul (a - 1) (5 * r0 + 3) (by omega)
  have heq : twoValuation (macroEnd r0 a + 1) + (2 * a - 1) =
      twoValuation (5 * r0 + 3) := by
    have hh := congrArg twoValuation hclosed
    rw [hleft, hright] at hh
    omega
  omega

/-- An even macro-step endpoint is again in the `u=1` state. -/
theorem macroEnd_plus_one_val_eq_one (r0 a : Nat) (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hv : twoValuation (5 * r0 + 3) = 2 * a) :
    twoValuation (macroEnd r0 a + 1) = 1 := by
  have hv' : 2 * a - 1 ≤ twoValuation (5 * r0 + 3) := by omega
  have hval := macroEnd_valuation r0 a ha h1 h2 hv'
  omega

/-- An odd macro endpoint (after `a+1` steps) is the terminal `u=0` state. -/
def macroTerminal (r0 a : Nat) : Nat :=
  twoRun ((5 * r0 + 1) / 2) a

theorem macroTerminal_valuation (r0 s a : Nat) (ha : 1 ≤ a)
    (hr1 : r0 + 1 = 2 * s) (hodd : s % 2 = 1)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hv : 2 * a + 1 ≤ twoValuation (5 * r0 + 3)) :
    twoValuation (macroTerminal r0 a + 1) = twoValuation (5 * r0 + 3) - (2 * a + 1) := by
  unfold macroTerminal
  have hclosed := twoRun_plus_one_mul a ((5 * r0 + 1) / 2) h2
  have h4a : 4 ^ a = 2 ^ (2 * a) := by
    rw [show 4 = 2 ^ 2 by rfl]
    rw [Nat.pow_mul]
  have hleft : twoValuation ((twoRun ((5 * r0 + 1) / 2) a + 1) * 2 ^ (2 * a)) =
      twoValuation (twoRun ((5 * r0 + 1) / 2) a + 1) + 2 * a := by
    rw [Nat.mul_comm]
    have h := StringFlow.Lte.twoValuation_mul_two_pow (2 * a)
      (twoRun ((5 * r0 + 1) / 2) a + 1) (by omega)
    simpa [Nat.add_comm] using h
  have hright : twoValuation (5 ^ a * (((5 * r0 + 1) / 2) + 1)) =
      twoValuation (((5 * r0 + 1) / 2) + 1) := by
    exact StringFlow.Lte.twoValuation_five_pow_mul a (((5 * r0 + 1) / 2) + 1) (by omega)
  have hval0 : twoValuation (((5 * r0 + 1) / 2) + 1) = twoValuation (5 * r0 + 3) - 1 := by
    exact t1_next_valuation r0 s hr1 hodd
  have hval : twoValuation (twoRun ((5 * r0 + 1) / 2) a + 1) + 2 * a =
      twoValuation (((5 * r0 + 1) / 2) + 1) := by
    have hh := congrArg twoValuation hclosed
    rw [h4a] at hh
    rw [hleft, hright] at hh
    omega
  rw [hval0] at hval
  omega

/-- The macro endpoint has odd part `2*C*5^(a-1)`. -/
theorem macroEnd_plus_one_eq (r0 a C : Nat) (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hC : 5 * r0 + 3 = C * 2 ^ (2 * a)) :
    macroEnd r0 a + 1 = 2 * C * 5 ^ (a - 1) := by
  have hclosed := macroEnd_plus_one_mul r0 a ha h1 h2
  have hpow : 2 ^ (2 * a) = 2 ^ (2 * a - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hrhs : 5 ^ (a - 1) * (5 * r0 + 3) =
      (2 * C * 5 ^ (a - 1)) * 2 ^ (2 * a - 1) := by
    rw [hC, hpow]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hpos : 0 < 2 ^ (2 * a - 1) := Nat.pow_pos (by decide)
  apply Nat.mul_right_cancel hpos
  rw [hclosed, hrhs]

/-- Macro endpoint identity `5*r_a+3 = 2*(5^a*C-1)`. -/
theorem macroEnd_five_r_plus_three (r0 a C : Nat) (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hC : 5 * r0 + 3 = C * 2 ^ (2 * a)) :
    5 * macroEnd r0 a + 3 = 2 * (5 ^ a * C - 1) := by
  have hpe := macroEnd_plus_one_eq r0 a C ha h1 h2 hC
  have hpow5 : 5 ^ a = 5 * 5 ^ (a - 1) := by
    calc
      5 ^ a = 5 ^ ((a - 1) + 1) := by
          congr 1
          omega
      _ = 5 ^ (a - 1) * 5 := by rw [Nat.pow_succ]
      _ = 5 * 5 ^ (a - 1) := by rw [Nat.mul_comm]
  have hfive : 5 * (2 * C * 5 ^ (a - 1)) = 2 * (5 ^ a * C) := by
    rw [hpow5]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hCpos : 0 < C := by
    by_cases hz : C = 0
    · simp [hz] at hC
    · exact Nat.pos_of_ne_zero hz
  have hsub : 2 * (5 ^ a * C) - 2 = 2 * (5 ^ a * C - 1) := by
    have hpowpos : 0 < 5 ^ a := Nat.pow_pos (by decide)
    have hge : 2 ≤ 2 * (5 ^ a * C) := by omega
    omega
  have hstep : 5 * macroEnd r0 a + 3 = 5 * (macroEnd r0 a + 1) - 2 := by omega
  rw [hstep, hpe, hfive, hsub]

/-- Macro endpoint failure is exactly the divisibility
`2^(m+2) | 5^a*C-1`, where `m = H-2a` is the remaining budget. -/
theorem macro_endpoint_failure_iff (r0 a C m : Nat)
    (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hC : 5 * r0 + 3 = C * 2 ^ (2 * a)) :
    (2 ^ (m + 3) ∣ 5 * macroEnd r0 a + 3) ↔
      (2 ^ (m + 2) ∣ 5 ^ a * C - 1) := by
  have hend := macroEnd_five_r_plus_three r0 a C ha h1 h2 hC
  have hpow : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by
    rw [show m + 3 = Nat.succ (m + 2) by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  constructor
  · intro hdvd
    rcases hdvd with ⟨k, hk⟩
    rw [hend] at hk
    rw [hpow] at hk
    have hk' : 2 * (5 ^ a * C - 1) = 2 * (k * 2 ^ (m + 2)) := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hk
    have hcancel : 5 ^ a * C - 1 = k * 2 ^ (m + 2) :=
      Nat.mul_left_cancel (by decide : 0 < 2) hk'
    exact ⟨k, by simpa [Nat.mul_comm] using hcancel⟩
  · intro hdvd
    rcases hdvd with ⟨k, hk⟩
    rw [hend, hpow]
    refine ⟨k, ?_⟩
    rw [hk]
    simp [Nat.mul_comm, Nat.mul_left_comm]

/-- Macro endpoint success is exactly the negation of
`2^(m+2) | 5^a*C-1`. -/
theorem macro_endpoint_success_iff (r0 a C m : Nat)
    (ha : 1 ≤ a)
    (h1 : (5 * r0 + 1) % 2 = 0)
    (h2 : ∀ k, k < a - 1 →
      (5 * twoRun ((5 * r0 + 1) / 2) k + 1) % 4 = 0)
    (hC : 5 * r0 + 3 = C * 2 ^ (2 * a)) :
    (¬ 2 ^ (m + 3) ∣ 5 * macroEnd r0 a + 3) ↔
      (¬ 2 ^ (m + 2) ∣ 5 ^ a * C - 1) := by
  constructor
  · intro hnot hdvd
    exact hnot ((macro_endpoint_failure_iff r0 a C m ha h1 h2 hC).mpr hdvd)
  · intro hnot hdvd
    exact hnot ((macro_endpoint_failure_iff r0 a C m ha h1 h2 hC).mp hdvd)

/-- Non-final macro parity: from `V<=m+1` with both `m` and `V` odd,
we get `V <= m`. -/
theorem macroNext_V_le_m (m V : Nat)
    (hm : m % 2 = 1) (hV : V % 2 = 1) (hle : V ≤ m + 1) :
    V ≤ m := by
  have hneq : V ≠ m + 1 := by
    intro heq
    rw [heq] at hV
    have hm1 : (m + 1) % 2 = 0 := by
      rw [Nat.add_mod]
      simp [hm]
    omega
  by_cases h : V ≤ m
  · exact h
  · have hgt : m < V := by omega
    have hle' : m + 1 ≤ V := by omega
    have heq : V = m + 1 := by omega
    exact (hneq heq).elim

/-- Non-final macro parity: the next margin is positive. -/
theorem macroNext_margin_ge_one (m V : Nat)
    (hm : m % 2 = 1) (hV : V % 2 = 1) (hle : V ≤ m + 1) :
    1 ≤ m + 1 - V := by
  have hle' := macroNext_V_le_m m V hm hV hle
  omega

/-- Non-final macro parity: the next margin is odd. -/
theorem macroNext_margin_odd (m V : Nat)
    (hm : m % 2 = 1) (hV : V % 2 = 1) (hle : V ≤ m + 1) :
    (m + 1 - V) % 2 = 1 := by
  have hle' := macroNext_V_le_m m V hm hV hle
  have hmdec : m = 2 * (m / 2) + 1 := by
    have h := Nat.div_add_mod m 2
    rw [hm] at h
    omega
  have hvdec : V = 2 * (V / 2) + 1 := by
    have h := Nat.div_add_mod V 2
    rw [hV] at h
    omega
  have hdiff : m - V = 2 * (m / 2 - V / 2) := by
    omega
  have hsub_mod : (m - V) % 2 = 0 := by
    rw [hdiff, Nat.mul_mod]
    simp
  have hsum : m + 1 - V = (m - V) + 1 := by omega
  rw [hsum, Nat.add_mod, hsub_mod]

/-- If additionally `V != m`, the next margin is at least `3`. -/
theorem macroNext_margin_ge_three_of_not_eq (m V : Nat)
    (hm : m % 2 = 1) (hV : V % 2 = 1) (hle : V ≤ m + 1)
    (hne : V ≠ m) :
    3 ≤ m + 1 - V := by
  have hodd := macroNext_margin_odd m V hm hV hle
  have hle' := macroNext_V_le_m m V hm hV hle
  have hlt : V < m := by
    by_cases h : V < m
    · exact h
    · have heq : V = m := by omega
      exact (hne heq).elim
  have h2 : 2 ≤ m + 1 - V := by omega
  by_cases h3 : 3 ≤ m + 1 - V
  · exact h3
  · have hx : m + 1 - V = 2 := by omega
    have hodd' : 2 % 2 = 1 := by
      rw [hx] at hodd
      exact hodd
    have hz : 2 % 2 = 0 := by decide
    rw [hz] at hodd'
    omega

/-- L1 is automatic for `a=1,2,4` once the next margin is at least `3`. -/
theorem l1_small_a (a m : Nat) (ha : a = 1 ∨ a = 2 ∨ a = 4) (hm : 3 ≤ m) :
    twoValuation a + 1 ≤ m := by
  rcases ha with rfl | rfl | rfl
  · have h : twoValuation 1 + 1 = 1 := by native_decide
    omega
  · have h : twoValuation 2 + 1 = 2 := by native_decide
    omega
  · have h : twoValuation 4 + 1 = 3 := by native_decide
    omega

/-- In the `V=m` exceptional family, `m%4=3` makes the next `a'` even,
so L1 cannot hold at the next macro start. -/
theorem v_eq_m_l1_fails_when_m_mod_four_three (m : Nat)
    (hm4 : m % 4 = 3) :
    1 < twoValuation ((m + 1) / 2) + 1 := by
  have hdiv4 := Nat.div_add_mod m 4
  rw [hm4] at hdiv4
  have hquad : m + 1 = 2 * (2 * (m / 4) + 2) := by
    rw [← hdiv4]
    omega
  have hhalf : (m + 1) / 2 = 2 * (m / 4) + 2 := by
    rw [hquad]
    exact Nat.mul_div_right (n := 2 * (m / 4) + 2) (m := 2) (by decide)
  have haeven : ((m + 1) / 2) % 2 = 0 := by
    rw [hhalf]
    simp
  have hpos : 0 < (m + 1) / 2 := by
    have hmge : 3 ≤ m := by
      rw [← hdiv4]
      omega
    omega
  have hdvd : 2 ^ 1 ∣ (m + 1) / 2 := Nat.dvd_iff_mod_eq_zero.mpr haeven
  have hge : 1 ≤ twoValuation ((m + 1) / 2) := by
    rw [StringFlow.Lte.twoValuation_ge_iff_dvd_pow ((m + 1) / 2) 1 hpos]
    exact hdvd
  omega

/-- In the `V=m` family, `m%4=3` is incompatible with L1 at the next
macro start. -/
theorem v_eq_m_l1_fails (m : Nat) (hm4 : m % 4 = 3) :
    ¬ (twoValuation ((m + 1) / 2) + 1 ≤ 1) := by
  intro h
  have hgt := v_eq_m_l1_fails_when_m_mod_four_three m hm4
  omega

/-- If the modulus reaches past the `q` interval, a residue class contains
at most one `q` in the interval. -/
theorem q_interval_unique_mod (W M q1 q2 : Nat) (hM : W ≤ M)
    (h1 : q1 < 2 ^ W) (h2 : q2 < 2 ^ W)
    (hmod : q1 % 2 ^ M = q2 % 2 ^ M) : q1 = q2 := by
  have hpow : 2 ^ W ≤ 2 ^ M :=
    Nat.pow_le_pow_right (show 0 < 2 by decide) hM
  have h1' : q1 < 2 ^ M := Nat.lt_of_lt_of_le h1 hpow
  have h2' : q2 < 2 ^ M := Nat.lt_of_lt_of_le h2 hpow
  have hq1 : q1 % 2 ^ M = q1 := Nat.mod_eq_of_lt h1'
  have hq2 : q2 % 2 ^ M = q2 := Nat.mod_eq_of_lt h2'
  rw [hq1, hq2] at hmod
  exact hmod

end StringFlow.Automaton
