/-
Lean interface for the local-lemma weighted automaton and its finite
abstraction.  The file states the exact definitions and the open theorem
statements; it deliberately does not assert the local lemma.  The concrete
K=32 example at the end is a verified blocker: the fixed abstraction is not
transition-functional.
-/

import LteMacro

namespace StringFlow.Automaton

/-- A prefix step is 1 or 2. -/
def StepOK (t : Nat) : Prop := t = 1 ∨ t = 2

/-- Exact prefix state used by the delta=0 automaton. -/
structure PrefixState where
  i : Nat
  W : Nat
  A : Nat
  q : Nat
  r : Nat
  j : Nat
  Wp : Nat
  Wj : Nat
  h : Nat

/-- `H_i = 2i + 13 - 2D_i` with `D_i = W_i - W_{j-1}`. -/
def Hval (s : PrefixState) : Nat :=
  2 * s.i + 13 - 2 * (s.W - s.Wp)

/-- The fixed finite abstraction used in the blocked automaton search. -/
def abstractK (K : Nat) (s : PrefixState) : Nat × Nat × Nat × Nat × Nat :=
  (s.q % 2 ^ K, s.A % 2 ^ K, s.W % K, s.h, Hval s)

/-- Exact failure congruence: local lemma fails iff this divisibility holds. -/
def failureCongruence (A W i q H : Nat) : Prop :=
  ∃ z : Nat, 5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q = z * 2 ^ (W + H + 1)

/-- `u_i = 1`, i.e. `r_i` is odd and `(r_i + 1)/2` is odd. -/
def uOne (s : PrefixState) : Prop :=
  ∃ u : Nat, s.r + 1 = 2 * u ∧ u % 2 = 1

/-- Open local-lemma statement, expressed as absence of the failure congruence. -/
def localLemmaStatement : Prop :=
  ∀ s : PrefixState, uOne s → ¬ failureCongruence s.A s.W s.i s.q (Hval s)

/-- A delta=0 transition with step t. -/
def DeltaZeroTransition (s1 s2 : PrefixState) (t : Nat) : Prop :=
  StepOK t ∧
  s2.i = s1.i + 1 ∧
  s2.W = s1.W + t ∧
  s2.A = 5 * s1.A + 2 ^ s1.W ∧
  s2.q = s1.q ∧
  s2.r = (5 * s1.r + 1) / 2 ^ t ∧
  s2.j = s1.j ∧
  s2.Wp = s1.Wp ∧
  s2.Wj = s1.Wj ∧
  s2.h = if t = 2 then s1.h + 1 else s1.h

/-- The `q`-interval membership is invariant under every delta=0 step. -/
theorem q_interval_preserved (s1 s2 : PrefixState) (t : Nat)
    (ht : DeltaZeroTransition s1 s2 t)
    (hmin : 2 ^ s1.Wp ≤ s1.q)
    (hmax : s1.q < 2 ^ s1.Wj) :
    2 ^ s2.Wp ≤ s2.q ∧ s2.q < 2 ^ s2.Wj := by
  rcases ht with ⟨htok, hi, hW, hA, hq, hr, hj, hWp, hWj, hh⟩
  rw [hq, hWp, hWj]
  exact ⟨hmin, hmax⟩

/-- Minimal-representative membership is preserved by every delta=0 step. -/
theorem minimal_representative_preserved (s1 s2 : PrefixState) (t : Nat)
    (ht : DeltaZeroTransition s1 s2 t)
    (hmin : s1.r < 5 ^ s1.i) :
    s2.r < 5 ^ s2.i := by
  rcases ht with ⟨htok, hi, hW, hA, hq, hr, hj, hWp, hWj, hh⟩
  rw [hi, hr]
  have ht1 : 1 ≤ t := by
    rcases htok with h1 | h2 <;> omega
  have hnum : 5 * s1.r + 1 < 5 ^ (s1.i + 1) := by
    have hpow : 5 * 5 ^ s1.i = 5 ^ (s1.i + 1) := by
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
    have hle1 : s1.r ≤ 5 ^ s1.i - 1 := by omega
    have hbound : 5 * s1.r + 1 ≤ 5 * (5 ^ s1.i - 1) + 1 := by omega
    have hsmall : 5 * (5 ^ s1.i - 1) + 1 < 5 * 5 ^ s1.i := by
      have hpos : 0 < 5 ^ s1.i := Nat.pow_pos (by decide)
      omega
    rw [← hpow]
    omega
  have hle : (5 * s1.r + 1) / 2 ^ t ≤ 5 * s1.r + 1 :=
    Nat.div_le_self (5 * s1.r + 1) (2 ^ t)
  have hlt : (5 * s1.r + 1) / 2 ^ t < 5 ^ (s1.i + 1) := by omega
  exact hlt

/-- Exact `t=2` run map: `r_{n+1} = (5*r_n+1)/4`. -/
def twoRun (r0 : Nat) : Nat → Nat
  | 0 => r0
  | n + 1 => (5 * twoRun r0 n + 1) / 4

/-- Closed form for a pure `t=2` run, modulo the divisibility required by
each step: `(r_n+1)*4^n = 5^n*(r_0+1)`. -/
theorem twoRun_plus_one_mul (n r0 : Nat)
    (hint : ∀ k, k < n → (5 * twoRun r0 k + 1) % 4 = 0) :
    (twoRun r0 n + 1) * 4 ^ n = 5 ^ n * (r0 + 1) := by
  induction n with
  | zero =>
      simp [twoRun]
  | succ n ih =>
      have hintn : (5 * twoRun r0 n + 1) % 4 = 0 := hint n (by omega)
      have hdiv : 4 ∣ 5 * twoRun r0 n + 1 := by
        rwa [Nat.dvd_iff_mod_eq_zero]
      rcases hdiv with ⟨q, hq⟩
      have hq1 : (q + 1) * 4 = 5 * twoRun r0 n + 5 := by
        omega
      have hstep : (twoRun r0 (n + 1) + 1) * 4 ^ (n + 1) =
          5 ^ (n + 1) * (r0 + 1) := by
        unfold twoRun
        rw [Nat.pow_succ, Nat.pow_succ]
        have htwo : (5 * twoRun r0 n + 1) / 4 = q := by
          have htwo0 : (4 * q) / 4 = q :=
            Nat.mul_div_right (n := q) (m := 4) (by decide)
          rw [← hq] at htwo0
          exact htwo0
        rw [htwo]
        rw [Nat.mul_comm (4 ^ n) 4]
        rw [← Nat.mul_assoc]
        rw [hq1]
        have hfactor : (5 * twoRun r0 n + 5) * 4 ^ n =
            5 * ((twoRun r0 n + 1) * 4 ^ n) := by
          have h5x : 5 * twoRun r0 n + 5 = 5 * (twoRun r0 n + 1) := by omega
          rw [h5x]
          rw [Nat.mul_assoc]
        rw [hfactor]
        have hih := ih (fun k hk => hint k (by omega))
        rw [hih]
        rw [← Nat.mul_assoc]
        rw [Nat.mul_comm 5 (5 ^ n)]
      exact hstep

/-- Valuation of a pure `t=2` run: `v2(r_n+1) = u - 2*n` when the
start has `v2(r_0+1) = u`. -/
theorem twoRun_valuation (n r0 u s : Nat)
    (hint : ∀ k, k < n → (5 * twoRun r0 k + 1) % 4 = 0)
    (hr0 : r0 + 1 = 2 ^ u * s)
    (hodd : s % 2 = 1)
    (_hu : 2 * n ≤ u) :
    twoValuation (twoRun r0 n + 1) = u - 2 * n := by
  have hclosed := twoRun_plus_one_mul n r0 hint
  have h4 : 4 ^ n = 2 ^ (2 * n) := by
    rw [show 4 = 2 ^ 2 by rfl]
    rw [Nat.pow_mul]
  have hx4 : (twoRun r0 n + 1) * 2 ^ (2 * n) = 5 ^ n * (2 ^ u * s) := by
    rw [← h4, hclosed, hr0]
  have hodd' : (5 ^ n * s) % 2 = 1 :=
    StringFlow.Lte.odd_mul_odd_mod_two (5 ^ n) s
      (StringFlow.Lte.five_pow_odd n) hodd
  have hvleft : twoValuation ((twoRun r0 n + 1) * 2 ^ (2 * n)) =
      twoValuation (twoRun r0 n + 1) + 2 * n := by
    rw [Nat.mul_comm]
    have h := StringFlow.Lte.twoValuation_mul_two_pow (2 * n) (twoRun r0 n + 1)
      (by omega)
    simpa [Nat.add_comm] using h
  have hvright : twoValuation (2 ^ u * (5 ^ n * s)) = u :=
    StringFlow.Lte.twoValuation_mul_two_pow_eq u (5 ^ n * s) hodd'
  have heq : twoValuation ((twoRun r0 n + 1) * 2 ^ (2 * n)) =
      twoValuation (2 ^ u * (5 ^ n * s)) := by
    have hswap : 5 ^ n * (2 ^ u * s) = 2 ^ u * (5 ^ n * s) := by
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (5 ^ n) (2 ^ u)]
      rw [Nat.mul_assoc]
    rw [hx4, hswap]
  rw [hvleft, hvright] at heq
  omega

/-- Exact `t=1` run map: `r_{n+1} = (5*r_n+1)/2`. -/
def t1Run (r0 : Nat) : Nat → Nat
  | 0 => r0
  | n + 1 => (5 * t1Run r0 n + 1) / 2

/-- Closed form for a pure `t=1` run, modulo the divisibility required by
each step: `(3*r_n+1)*2^n = 5^n*(3*r_0+1)`. -/
theorem t1Run_three_plus_one_mul (n r0 : Nat)
    (hint : ∀ k, k < n → (5 * t1Run r0 k + 1) % 2 = 0) :
    (3 * t1Run r0 n + 1) * 2 ^ n = 5 ^ n * (3 * r0 + 1) := by
  induction n with
  | zero =>
      simp [t1Run]
  | succ n ih =>
      have hintn : (5 * t1Run r0 n + 1) % 2 = 0 := hint n (by omega)
      have hdiv : 2 ∣ 5 * t1Run r0 n + 1 := by
        rwa [Nat.dvd_iff_mod_eq_zero]
      rcases hdiv with ⟨q, hq⟩
      have hqval : (5 * t1Run r0 n + 1) / 2 = q := by
        have hq0 : (2 * q) / 2 = q :=
          Nat.mul_div_right (n := q) (m := 2) (by decide)
        rw [← hq] at hq0
        exact hq0
      have hstep : (3 * ((5 * t1Run r0 n + 1) / 2) + 1) * 2 ^ (n + 1) =
          5 ^ (n + 1) * (3 * r0 + 1) := by
        rw [hqval]
        have h3 : (3 * q + 1) * 2 = 5 * (3 * t1Run r0 n + 1) := by
          omega
        have hsuff : (3 * q + 1) * 2 ^ (n + 1) = 5 ^ (n + 1) * (3 * r0 + 1) := by
          rw [Nat.pow_succ]
          rw [Nat.mul_comm (2 ^ n) 2]
          rw [← Nat.mul_assoc (3 * q + 1) 2 (2 ^ n)]
          rw [h3]
          rw [Nat.mul_assoc]
          rw [ih (fun k hk => hint k (by omega))]
          rw [Nat.pow_succ]
          rw [← Nat.mul_assoc]
          rw [Nat.mul_comm 5 (5 ^ n)]
        exact hsuff
      unfold t1Run
      exact hstep

/-- Valuation of a pure `t=1` run: the 2-adic valuation of `3*r_n+1`
decreases by exactly `n` along the run. -/
theorem t1Run_three_plus_one_valuation (n r0 v s : Nat)
    (hint : ∀ k, k < n → (5 * t1Run r0 k + 1) % 2 = 0)
    (hr0 : 3 * r0 + 1 = 2 ^ v * s)
    (hodd : s % 2 = 1)
    (hv : n ≤ v) :
    twoValuation (3 * t1Run r0 n + 1) = v - n := by
  have hclosed := t1Run_three_plus_one_mul n r0 hint
  have hx2 : (3 * t1Run r0 n + 1) * 2 ^ n = 5 ^ n * (2 ^ v * s) := by
    rw [hclosed, hr0]
  have hodd' : (5 ^ n * s) % 2 = 1 :=
    StringFlow.Lte.odd_mul_odd_mod_two (5 ^ n) s
      (StringFlow.Lte.five_pow_odd n) hodd
  have hvleft : twoValuation ((3 * t1Run r0 n + 1) * 2 ^ n) =
      twoValuation (3 * t1Run r0 n + 1) + n := by
    rw [Nat.mul_comm]
    have h := StringFlow.Lte.twoValuation_mul_two_pow n (3 * t1Run r0 n + 1)
      (by omega)
    simpa [Nat.add_comm] using h
  have hvright : twoValuation (2 ^ v * (5 ^ n * s)) = v :=
    StringFlow.Lte.twoValuation_mul_two_pow_eq v (5 ^ n * s) hodd'
  have heq : twoValuation ((3 * t1Run r0 n + 1) * 2 ^ n) =
      twoValuation (2 ^ v * (5 ^ n * s)) := by
    have hswap : 5 ^ n * (2 ^ v * s) = 2 ^ v * (5 ^ n * s) := by
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (5 ^ n) (2 ^ v)]
      rw [Nat.mul_assoc]
    rw [hx2, hswap]
  rw [hvleft, hvright] at heq
  omega

/-- Valuation of one `t=1` step from a `u=1` state:
`v2(r'+1) = v2(5r+3)-1`. -/
theorem t1_next_valuation (r s : Nat)
    (hr1 : r + 1 = 2 * s) (hodd : s % 2 = 1) :
    twoValuation ((5 * r + 1) / 2 + 1) = twoValuation (5 * r + 3) - 1 := by
  have hmod1 : (5 * r + 1) % 2 = 0 := by
    have hrodd : r % 2 = 1 := by omega
    omega
  have hdiv := Nat.div_add_mod (5 * r + 1) 2
  have hsplit : 5 * r + 3 = 2 * ((5 * r + 1) / 2 + 1) := by
    rw [hmod1] at hdiv
    omega
  let y := (5 * r + 1) / 2 + 1
  have hypos : 0 < y := by
    dsimp [y]
    omega
  have hv : twoValuation (5 * r + 3) = 1 + twoValuation y := by
    rw [hsplit]
    have h := StringFlow.Lte.twoValuation_mul_two_pow 1 y hypos
    simpa [y, Nat.add_comm] using h
  change twoValuation y = twoValuation (5 * r + 3) - 1
  omega

/-- `2x-1` is odd for positive `x`. -/
theorem two_mul_sub_one_mod_two (x : Nat) (hx : 0 < x) :
    (2 * x - 1) % 2 = 1 := by
  have hform : 2 * x - 1 = 1 + (x - 1) * 2 := by
    have hsub : 2 * (x - 1) = 2 * x - 2 := by
      simpa using (Nat.mul_sub_left_distrib 2 x 1)
    rw [Nat.mul_comm (x - 1) 2]
    rw [hsub]
    omega
  rw [hform, Nat.add_mul_mod_self_right]

/-- `r+1=P` implies `r=P-1`. -/
theorem add_one_eq_sub_one (r P : Nat) (hr : r + 1 = P) : r = P - 1 := by
  omega

/-- Exact valuation window for `u=1`: `5r+3 = 2*(5s-1)`. -/
theorem five_r_plus_three_val_succ_of_u_one (r s : Nat)
    (hr : r + 1 = 2 * s) (hodd : s % 2 = 1) :
    twoValuation (5 * r + 3) = 1 + twoValuation (5 * s - 1) := by
  have hs1 : 1 ≤ s := by
    by_cases h : s = 0
    · rw [h] at hodd
      simp at hodd
    · omega
  have hr' : r = 2 * s - 1 := by omega
  have hsplit : 5 * r + 3 = 2 * (5 * s - 1) := by
    rw [hr']
    omega
  have hpos : 0 < 5 * s - 1 := by omega
  rw [hsplit]
  exact StringFlow.Lte.twoValuation_mul_two_pow 1 (5 * s - 1) hpos

/-- Exact valuation window for `u=0`: `5r+3` is odd. -/
theorem five_r_plus_three_val_zero_of_u_zero (r s : Nat)
    (hr : r + 1 = s) (hodd : s % 2 = 1) :
    twoValuation (5 * r + 3) = 0 := by
  have hs1 : 1 ≤ s := by
    by_cases h : s = 0
    · rw [h] at hodd
      simp at hodd
    · omega
  have hr' : r = s - 1 := by omega
  have hval : (5 * r + 3) % 2 = 1 := by
    rw [hr']
    omega
  exact StringFlow.twoValuation_odd (5 * r + 3) hval

/-- The abstraction would be usable for a deterministic automaton only if
this functional transition property held. -/
def transitionFunctionalStatement (K : Nat) : Prop :=
  ∀ (s1 s1' s2 s2' : PrefixState) (t : Nat),
    DeltaZeroTransition s1 s1' t →
    DeltaZeroTransition s2 s2' t →
    abstractK K s1 = abstractK K s2 →
    abstractK K s1' = abstractK K s2'

/-- Prefix numerator of a block suffix, with relative weight starting at 0. -/
def suffixAux (W : Nat) : List Nat → Nat
  | [] => 0
  | t :: ts => 5 * suffixAux (W + t) ts + 2 ^ W

/-- `S_i` for a block suffix word `s`. -/
def suffixA (s : List Nat) : Nat :=
  suffixAux 0 s

/-- `N_i = 5^(L+1) r_j + 5 S_i + 3*2^d` in a delta=0 block. -/
def blockN (L d S rj : Nat) : Nat :=
  5 ^ (L + 1) * rj + 5 * S + 3 * 2 ^ d

/-- Failure congruence at the end of a delta=0 block. -/
def blockFailureCongruence (L d H S rj : Nat) : Prop :=
  ∃ k : Nat, blockN L d S rj = k * 2 ^ (d + H + 1)

/-- Open p-adic route statement: no block end satisfies the congruence
together with the minimal-representative and q interval constraints. -/
def pAdicWindowStatement : Prop :=
  ∀ (L d H S rj A j Wj Wp : Nat),
    rj < 5 ^ j →
    Wp < Wj →
    (∃ q : Nat,
      2 ^ Wj * rj = A + 5 ^ j * q ∧
      2 ^ Wp ≤ q ∧
      q < 2 ^ Wj) →
    ¬ blockFailureCongruence L d H S rj

/-- The unique residue `m^* = 5^{-1} mod 2^H`. -/
def candidateMClass (H m : Nat) : Prop :=
  m < 2 ^ H ∧ (5 * m) % 2 ^ H = 1

/-- `candidateMClass` is unique: there is at most one representative
of `5^{-1}` below `2^H`. -/
theorem candidateMClass_unique (H m1 m2 : Nat)
    (h1 : candidateMClass H m1) (h2 : candidateMClass H m2) :
    m1 = m2 := by
  rcases h1 with ⟨h1lt, h1m⟩
  rcases h2 with ⟨h2lt, h2m⟩
  exact StringFlow.Lte.five_inv_unique H m1 m2 h1lt h2lt h1m h2m

/-- `m = (r_i+1)/2` expressed through `A_i, W_i, q_i`. -/
def mValue (A W i q : Nat) : Nat :=
  (A + 5 ^ i * q + 2 ^ W) / 2 ^ (W + 1)

/-- Failure congruence `5m-1 ≡ 0 mod 2^H` in the `m` formulation. -/
def mFailureCongruence (A W i q H : Nat) : Prop :=
  (5 * mValue A W i q) % 2 ^ H = 1

/-- If the m-congruence holds and `m` is below `2^H`, then `m` is the
unique candidate residue. -/
theorem mFailureCongruence_implies_candidate (A W i q H : Nat)
    (h : mFailureCongruence A W i q H) (hlt : mValue A W i q < 2 ^ H) :
    candidateMClass H (mValue A W i q) := by
  exact ⟨hlt, h⟩

/-- Under the same size bound, the m-congruence is equivalent to being
the unique candidate residue. -/
theorem mFailureCongruence_iff_candidate (A W i q H : Nat)
    (hlt : mValue A W i q < 2 ^ H) :
    mFailureCongruence A W i q H ↔ candidateMClass H (mValue A W i q) := by
  constructor
  · intro h
    exact ⟨hlt, h⟩
  · intro hc
    exact hc.2

/-- `a ≡ 1 mod b` is the same as `b | a-1` for `b >= 2`. -/
theorem modEqOne_iff_dvd_sub (a b : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    a % b = 1 ↔ b ∣ a - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hbpos : 0 < b := by omega
  have hb1 : 1 < b := by omega
  have hmod1 : 1 % b = 1 := Nat.mod_eq_of_lt hb1
  have hsum : a = (a - 1) + 1 := by omega
  constructor
  · intro h
    have h0 := Nat.add_mod (a - 1) 1 b
    rw [← hsum] at h0
    rw [h] at h0
    have h0' : ((a - 1) % b + 1) % b = 1 := by
      simpa [hmod1] using h0.symm
    let r := (a - 1) % b
    have hrlt : r < b := by
      dsimp [r]
      exact Nat.mod_lt (a - 1) hbpos
    have hmod : (r + 1) % b = 1 := by
      simpa [r] using h0'
    by_cases hrb : r + 1 < b
    · have hres : (r + 1) % b = r + 1 := Nat.mod_eq_of_lt hrb
      rw [hres] at hmod
      change r = 0
      omega
    · have hrb' : r + 1 = b := by omega
      rw [hrb'] at hmod
      rw [Nat.mod_self b] at hmod
      omega
  · intro h
    have hdvd : b ∣ a - 1 := Nat.dvd_iff_mod_eq_zero.mpr h
    rcases hdvd with ⟨k, hk⟩
    have hk0 : a = k * b + 1 := by
      rw [Nat.mul_comm k b]
      rw [← hk]
      omega
    rw [hk0]
    rw [Nat.add_mod]
    rw [Nat.mul_comm]
    rw [Nat.mul_mod_right]
    rw [hmod1]
    exact hmod1

/-- Exact `m`-numerator identity used to bridge the two failure forms. -/
theorem five_N_eq_M_add (A W i q : Nat) :
    5 * (A + 5 ^ i * q + 2 ^ W) =
      (5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q) + 2 ^ (W + 1) := by
  have hpow : 5 * 5 ^ i = 5 ^ (i + 1) := by
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have htwo : 5 * 2 ^ W = 3 * 2 ^ W + 2 ^ (W + 1) := by
    rw [Nat.pow_succ]
    omega
  have hpq : 5 * (5 ^ i * q) = 5 ^ (i + 1) * q := by
    rw [← Nat.mul_assoc, hpow]
  rw [Nat.mul_add]
  rw [Nat.mul_add]
  rw [hpq]
  omega

/-- When the numerator is divisible by `2^(W+1)`, `mValue` is exact. -/
theorem mValue_eq_of_dvd (A W i q m : Nat)
    (hN : A + 5 ^ i * q + 2 ^ W = m * 2 ^ (W + 1)) :
    mValue A W i q = m := by
  unfold mValue
  rw [hN]
  rw [Nat.mul_comm]
  simpa using Nat.mul_div_right (n := m) (m := 2 ^ (W + 1))
    (Nat.pow_pos (by decide))

/-- The `m`-congruence and the affine failure congruence are equivalent
whenever `m` is an integer and the window height is at least `2`. -/
theorem mFailureCongruence_iff_failureCongruence (A W i q H : Nat)
    (hH : 2 ≤ H) (hN : ∃ m : Nat, A + 5 ^ i * q + 2 ^ W = m * 2 ^ (W + 1)) :
    mFailureCongruence A W i q H ↔ failureCongruence A W i q H := by
  rcases hN with ⟨m, hm⟩
  have hmval : mValue A W i q = m := mValue_eq_of_dvd A W i q m hm
  unfold mFailureCongruence
  rw [hmval]
  let N := A + 5 ^ i * q + 2 ^ W
  let M := 5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q
  show (5 * m) % 2 ^ H = 1 ↔ ∃ z : Nat, M = z * 2 ^ (W + H + 1)
  have hN' : N = m * 2 ^ (W + 1) := by
    simpa [N] using hm
  have hrel : 5 * N = M + 2 ^ (W + 1) := by
    simpa [N, M] using five_N_eq_M_add A W i q
  have hmp : 1 ≤ m := by
    have hNpos : 0 < N := by
      dsimp [N]
      have h2 : 0 < 2 ^ W := Nat.pow_pos (by decide)
      omega
    have hNpos' : 0 < m * 2 ^ (W + 1) := by
      simpa [hN'] using hNpos
    by_cases hmz : m = 0
    · rw [hmz] at hNpos'
      simp at hNpos'
    · omega
  have hM : M = (5 * m - 1) * 2 ^ (W + 1) := by
    have h5N : 5 * N = (5 * m) * 2 ^ (W + 1) := by
      rw [hN']
      rw [Nat.mul_assoc]
    have hM' : M = 5 * N - 2 ^ (W + 1) := by omega
    rw [hM', h5N]
    have hmul : (5 * m - 1) * 2 ^ (W + 1) =
        (5 * m) * 2 ^ (W + 1) - 2 ^ (W + 1) := by
      rw [Nat.mul_sub_right_distrib]
      simp
    rw [hmul]
  have hpowH : 2 ^ (W + H + 1) = 2 ^ (W + 1) * 2 ^ H := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hpow2 : 2 ≤ 2 ^ H := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ H by omega)
    simpa using h
  constructor
  · intro hmod
    have hdvd : 2 ^ H ∣ 5 * m - 1 := by
      exact modEqOne_iff_dvd_sub (5 * m) (2 ^ H) (by omega) hpow2
        |>.mp hmod
    rcases hdvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hM]
    rw [hk]
    rw [hpowH]
    rw [Nat.mul_assoc]
    rw [Nat.mul_comm k (2 ^ (W + 1))]
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm (2 ^ H) (2 ^ (W + 1))]
    rw [Nat.mul_comm]
  · intro hdvd
    rcases hdvd with ⟨z, hz⟩
    have h5m : 2 ^ H ∣ 5 * m - 1 := by
      refine ⟨z, ?_⟩
      rw [hM] at hz
      rw [hpowH] at hz
      rw [Nat.mul_comm (2 ^ (W + 1)) (2 ^ H)] at hz
      rw [← Nat.mul_assoc] at hz
      have hcancel : 5 * m - 1 = z * 2 ^ H :=
        Nat.mul_right_cancel (Nat.pow_pos (by decide)) hz
      rw [Nat.mul_comm] at hcancel
      simpa [Nat.mul_comm] using hcancel
    exact modEqOne_iff_dvd_sub (5 * m) (2 ^ H) (by omega) hpow2
      |>.mpr h5m

/-- Affine numerator identity: `2^W*(5*r+3)` in terms of `A, q`. -/
theorem five_r_plus_three_affine (A W i q r : Nat)
    (hr : A + 5 ^ i * q = 2 ^ W * r) :
    5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q = 2 ^ W * (5 * r + 3) := by
  have h5q : 5 * (5 ^ i * q) = 5 ^ (i + 1) * q := by
    have hpow : 5 * 5 ^ i = 5 ^ (i + 1) := by
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
    rw [← Nat.mul_assoc, hpow]
  calc
    5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q
        = 5 * A + 5 ^ (i + 1) * q + 3 * 2 ^ W := by omega
    _ = 5 * (A + 5 ^ i * q) + 3 * 2 ^ W := by
        rw [Nat.mul_add]
        rw [← h5q]
    _ = 5 * (2 ^ W * r) + 3 * 2 ^ W := by rw [hr]
    _ = 2 ^ W * (5 * r + 3) := by
        rw [Nat.mul_add]
        rw [Nat.mul_comm (2 ^ W) (5 * r)]
        rw [Nat.mul_comm (2 ^ W) 3]
        have hswap : 5 * (2 ^ W * r) = (5 * r) * 2 ^ W := by
          rw [Nat.mul_assoc]
          rw [Nat.mul_comm (2 ^ W) r]
        rw [hswap]

/-- Necessary size bound for a failure: the failure window height
`H+1` cannot exceed the size of the minimal representative. -/
theorem failureCongruence_height_bound (A W i q H r : Nat)
    (hr : A + 5 ^ i * q = 2 ^ W * r)
    (hmin : r < 5 ^ i)
    (hf : failureCongruence A W i q H) :
    2 ^ (H + 1) ≤ 5 ^ (i + 1) + 3 := by
  unfold failureCongruence at hf
  rcases hf with ⟨z, hz⟩
  have hM : 5 * A + 3 * 2 ^ W + 5 ^ (i + 1) * q =
      2 ^ W * (5 * r + 3) := five_r_plus_three_affine A W i q r hr
  have hpow2 : 2 ^ (W + H + 1) = 2 ^ W * 2 ^ (H + 1) := by
    rw [← Nat.pow_add]
    congr 1
  have hcancel : 5 * r + 3 = z * 2 ^ (H + 1) := by
    rw [hM] at hz
    rw [Nat.mul_comm (2 ^ W) (5 * r + 3)] at hz
    rw [hpow2] at hz
    rw [Nat.mul_comm (2 ^ W) (2 ^ (H + 1))] at hz
    rw [← Nat.mul_assoc] at hz
    exact Nat.mul_right_cancel
      (show 0 < 2 ^ W by exact Nat.pow_pos (show 0 < 2 by decide)) hz
  have hz1 : 1 ≤ z := by
    have hpos : 0 < 5 * r + 3 := by omega
    by_cases hz0 : z = 0
    · rw [hz0] at hcancel
      simp at hcancel
    · omega
  have hle : 2 ^ (H + 1) ≤ 5 * r + 3 := by
    rw [hcancel]
    have hmul : 1 * 2 ^ (H + 1) ≤ z * 2 ^ (H + 1) :=
      Nat.mul_le_mul_right (2 ^ (H + 1)) hz1
    simpa using hmul
  have h5r : 5 * r < 5 ^ (i + 1) := by
    have hpow : 5 * 5 ^ i = 5 ^ (i + 1) := by
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
    rw [← hpow]
    exact (Nat.mul_lt_mul_left (show 0 < 5 by decide)).2 hmin
  have hlt : 5 * r + 3 < 5 ^ (i + 1) + 3 := by omega
  omega

/-- Necessary `m`-size inequality from the q-interval lower endpoint:
`m * 2^(W-Wp+1) >= 5^i + 2^(W-Wp)`. -/
theorem mValue_lower_bound (A W i q Wp : Nat)
    (hWp : Wp ≤ W)
    (hq : 2 ^ Wp ≤ q)
    (hN : ∃ m : Nat, A + 5 ^ i * q + 2 ^ W = m * 2 ^ (W + 1)) :
    mValue A W i q * 2 ^ (W - Wp + 1) ≥ 5 ^ i + 2 ^ (W - Wp) := by
  rcases hN with ⟨m, hm⟩
  have hmval : mValue A W i q = m := mValue_eq_of_dvd A W i q m hm
  rw [hmval]
  have hqmul' : 2 ^ Wp * 5 ^ i ≤ q * 5 ^ i := Nat.mul_le_mul_right (5 ^ i) hq
  have hqmul : 5 ^ i * 2 ^ Wp ≤ 5 ^ i * q := by
    simpa [Nat.mul_comm] using hqmul'
  have hNge : m * 2 ^ (W + 1) ≥ 5 ^ i * q + 2 ^ W := by
    rw [← hm]
    omega
  have htarget0 : m * 2 ^ (W + 1) ≥ 5 ^ i * 2 ^ Wp + 2 ^ W := by omega
  have hpow : 2 ^ (W + 1) = 2 ^ Wp * 2 ^ (W - Wp + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hpow2 : 2 ^ W = 2 ^ Wp * 2 ^ (W - Wp) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow] at htarget0
  rw [hpow2] at htarget0
  rw [Nat.mul_comm (5 ^ i) (2 ^ Wp)] at htarget0
  rw [← Nat.mul_add] at htarget0
  rw [← Nat.mul_assoc] at htarget0
  rw [Nat.mul_comm m (2 ^ Wp)] at htarget0
  rw [Nat.mul_assoc] at htarget0
  exact Nat.le_of_mul_le_mul_left htarget0 (Nat.pow_pos (by decide))

/-- The minimal representative condition bounds the prefix numerator:
`A < 5^i * (2^W - q)`. -/
theorem A_bound_of_minimal (A W i q r : Nat)
    (hr : A + 5 ^ i * q = 2 ^ W * r)
    (hmin : r < 5 ^ i) :
    A < 5 ^ i * (2 ^ W - q) := by
  have h1 : 2 ^ W * r < 2 ^ W * 5 ^ i :=
    (Nat.mul_lt_mul_left (show 0 < 2 ^ W by exact Nat.pow_pos (show 0 < 2 by decide))).2 hmin
  have h2 : A + 5 ^ i * q < 2 ^ W * 5 ^ i := by
    rw [← hr] at h1
    exact h1
  have h2' : A + 5 ^ i * q < 5 ^ i * 2 ^ W := by
    simpa [Nat.mul_comm] using h2
  have hqle : q ≤ 2 ^ W := by
    by_cases hqle : q ≤ 2 ^ W
    · exact hqle
    · have hq' : 2 ^ W < q := by omega
      have hbig : 2 ^ W * 5 ^ i ≤ 5 ^ i * q := by
        have hmul : 2 ^ W * 5 ^ i ≤ q * 5 ^ i :=
          Nat.mul_le_mul_right (5 ^ i) (Nat.le_of_lt hq')
        simpa [Nat.mul_comm] using hmul
      omega
  have hsub : 5 ^ i * (2 ^ W - q) = 5 ^ i * 2 ^ W - 5 ^ i * q := by
    rw [Nat.mul_sub_left_distrib]
  rw [hsub]
  omega

/-- For odd `m`, `5m ≡ 1 mod 2`. -/
theorem odd_five_mul_mod_two (m : Nat) (hm : m % 2 = 1) :
    (5 * m) % 2 = 1 := by
  rw [Nat.mul_mod]
  have h5 : 5 % 2 = 1 := by native_decide
  simp [h5, hm]

/-- `u_i = 1` makes the `m` numerator divisible by `2^(W+1)`. -/
theorem uOne_implies_numerator_divisible (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s) :
    ∃ m : Nat, s.A + 5 ^ s.i * s.q + 2 ^ s.W = m * 2 ^ (s.W + 1) := by
  rcases hu with ⟨u, hsu, huodd⟩
  refine ⟨u, ?_⟩
  rw [hrep]
  have hsum : 2 ^ s.W * s.r + 2 ^ s.W = 2 ^ s.W * (s.r + 1) := by
    rw [Nat.mul_add]
    simp
  rw [hsum, hsu]
  have hpow : 2 ^ s.W * (2 * u) = u * 2 ^ (s.W + 1) := by
    rw [Nat.pow_succ]
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm (2 ^ s.W * 2) u]
  exact hpow

/-- `u_i = 1` forces `m = (r_i+1)/2` to be odd. -/
theorem uOne_implies_mValue_odd (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s) :
    mValue s.A s.W s.i s.q % 2 = 1 := by
  rcases hu with ⟨u, hsu, huodd⟩
  have hN : s.A + 5 ^ s.i * s.q + 2 ^ s.W = u * 2 ^ (s.W + 1) := by
    rw [hrep]
    have hsum : 2 ^ s.W * s.r + 2 ^ s.W = 2 ^ s.W * (s.r + 1) := by
      rw [Nat.mul_add]
      simp
    rw [hsum, hsu]
    have hpow : 2 ^ s.W * (2 * u) = u * 2 ^ (s.W + 1) := by
      rw [Nat.pow_succ]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (2 ^ s.W * 2) u]
    exact hpow
  have hm : mValue s.A s.W s.i s.q = u := mValue_eq_of_dvd s.A s.W s.i s.q u hN
  rw [hm]
  exact huodd

/-- Height-one failure in the `m` form is automatic for `u_i = 1`. -/
theorem uOne_implies_height_one_failure (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s) :
    mFailureCongruence s.A s.W s.i s.q 1 := by
  unfold mFailureCongruence
  have hodd := uOne_implies_mValue_odd s hrep hu
  exact odd_five_mul_mod_two (mValue s.A s.W s.i s.q) hodd

/-- Height-one failure in the affine congruence form is automatic
for `u_i = 1`. -/
theorem uOne_implies_height_one_failureCongruence (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s) :
    failureCongruence s.A s.W s.i s.q 1 := by
  rcases hu with ⟨u, hsu, huodd⟩
  have h4 : 4 ∣ 5 * s.r + 3 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  rcases h4 with ⟨t, ht⟩
  unfold failureCongruence
  refine ⟨t, ?_⟩
  have hM : 5 * s.A + 3 * 2 ^ s.W + 5 ^ (s.i + 1) * s.q =
      2 ^ s.W * (5 * s.r + 3) := five_r_plus_three_affine s.A s.W s.i s.q s.r hrep
  rw [hM, ht]
  have hpow : 2 ^ (s.W + 2) = 4 * 2 ^ s.W := by
    rw [Nat.pow_succ]
    rw [Nat.pow_succ]
    omega
  rw [show 2 ^ (s.W + 1 + 1) = 2 ^ (s.W + 2) by rfl]
  rw [hpow]
  rw [Nat.mul_comm t (4 * 2 ^ s.W)]
  rw [← Nat.mul_assoc]
  rw [Nat.mul_comm (2 ^ s.W) 4]

/-- Capacity condition is necessary: if the local lemma holds at a
`u_i = 1` state, then `H_i != 1`. -/
theorem capacityCondition_necessary (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s)
    (hll : ¬ failureCongruence s.A s.W s.i s.q (Hval s)) :
    Hval s ≠ 1 := by
  intro h
  have hf := uOne_implies_height_one_failureCongruence s hrep hu
  rw [← h] at hf
  exact hll hf

/-- Failure congruence is monotone in the window height. -/
theorem failureCongruence_mono (A W i q H1 H2 : Nat)
    (hle : H1 ≤ H2) (hf : failureCongruence A W i q H2) :
    failureCongruence A W i q H1 := by
  rcases hf with ⟨z, hz⟩
  refine ⟨z * 2 ^ (H2 - H1), ?_⟩
  have hpow : 2 ^ (W + H2 + 1) = 2 ^ (W + H1 + 1) * 2 ^ (H2 - H1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow] at hz
  rw [Nat.mul_comm (2 ^ (W + H1 + 1)) (2 ^ (H2 - H1))] at hz
  rw [← Nat.mul_assoc] at hz
  exact hz

/-- Height-zero failure is automatic for `u_i = 1`. -/
theorem uOne_implies_height_zero_failureCongruence (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s) :
    failureCongruence s.A s.W s.i s.q 0 := by
  exact failureCongruence_mono s.A s.W s.i s.q 0 1 (by omega)
    (uOne_implies_height_one_failureCongruence s hrep hu)

/-- `H_i` is either zero or odd; there is no other small positive value. -/
theorem Hval_zero_or_odd (s : PrefixState) :
    Hval s = 0 ∨ Hval s % 2 = 1 := by
  unfold Hval
  by_cases h : 2 * (s.W - s.Wp) ≤ 2 * s.i + 13
  · right
    omega
  · left
    omega

/-- Local lemma implies the capacity condition `3 <= H_i`. -/
theorem capacityCondition_from_localLemma (s : PrefixState)
    (hrep : s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r)
    (hu : uOne s)
    (hll : ¬ failureCongruence s.A s.W s.i s.q (Hval s)) :
    3 ≤ Hval s := by
  have h0 := uOne_implies_height_zero_failureCongruence s hrep hu
  have h1 := uOne_implies_height_one_failureCongruence s hrep hu
  have hne0 : Hval s ≠ 0 := by
    intro h
    rw [← h] at h0
    exact hll h0
  have hne1 : Hval s ≠ 1 := by
    intro h
    rw [← h] at h1
    exact hll h1
  rcases Hval_zero_or_odd s with hz | hodd
  · exact False.elim (hne0 hz)
  · by_cases hsmall : Hval s ≤ 2
    · have hcases : Hval s = 0 ∨ Hval s = 1 ∨ Hval s = 2 := by omega
      rcases hcases with h | h | h
      · exact False.elim (hne0 h)
      · exact False.elim (hne1 h)
      · have hz0 : Hval s = 0 := by omega
        exact False.elim (hne0 hz0)
    · omega

/-- Refined one-dimensional target with all `u=1`, minimal-representative,
and numerator hypotheses made explicit. -/
def mIntervalLocalLemmaStatementFull : Prop :=
  ∀ (s : PrefixState),
    uOne s →
    s.A + 5 ^ s.i * s.q = 2 ^ s.W * s.r →
    s.r < 5 ^ s.i →
    ¬ mFailureCongruence s.A s.W s.i s.q (Hval s)

/-- The affine local-lemma statement implies the refined one-dimensional
`m`-interval no-candidate statement. -/
theorem localLemmaStatement_implies_mIntervalFull :
    localLemmaStatement → mIntervalLocalLemmaStatementFull := by
  intro hll s hu hrep _hrmin hm
  have hnot : ¬ failureCongruence s.A s.W s.i s.q (Hval s) := hll s hu
  have hH : 2 ≤ Hval s := by
    have hcap : 3 ≤ Hval s := capacityCondition_from_localLemma s hrep hu hnot
    omega
  have hN := uOne_implies_numerator_divisible s hrep hu
  have heq := mFailureCongruence_iff_failureCongruence s.A s.W s.i s.q
    (Hval s) hH hN
  have hf : failureCongruence s.A s.W s.i s.q (Hval s) := heq.mp hm
  exact hnot hf

/-- Open one-dimensional target: no delta=0 u=1 state has `m` in the
unique candidate residue class. -/
def mIntervalLocalLemmaStatement : Prop :=
  ∀ (i W Wp Wj A q : Nat),
    Wp < Wj →
    Wj ≤ W →
    q < 2 ^ Wj →
    2 ^ Wp ≤ q →
    ¬ mFailureCongruence A W i q (2 * i + 13 - 2 * (W - Wp))

/-- Finite state for the weighted automaton computing `G_i mod 2^m`. -/
structure WeightedState (m : Nat) where
  kMod : Nat
  wMod : Nat
  gMod : Nat

/-- A certified inverse of 5 modulo `2^m`. -/
structure FiveInv (m : Nat) where
  inv : Nat
  spec : (5 * inv) % 2 ^ m = 1

/-- Period of `5^{-k}` modulo `2^m` for `m >= 3`. -/
def period (m : Nat) : Nat := 2 ^ (m - 2)

/-- One weighted-automaton transition. -/
def weightedStep (m : Nat) (fi : FiveInv m) (s : WeightedState m)
    (t : Nat) : WeightedState m :=
  let mod := 2 ^ m
  let coeff :=
    ((2 ^ s.wMod) % mod) * ((fi.inv ^ (s.kMod + 1)) % mod)
  { kMod := (s.kMod + 1) % period m,
    wMod := (s.wMod + t) % m,
    gMod := (s.gMod + coeff % mod) % mod }

/-- Concrete K=32 blocker, current states. -/
def old32 : PrefixState :=
  { i := 20, W := 37, A := 91856933410353, q := 130895839231,
    r := 90827234089349, j := 20, Wp := 35, Wj := 37, h := 0 }

def new32 : PrefixState :=
  { i := 20, W := 37, A := 92007257265713, q := 49291460607,
    r := 34202821552729, j := 20, Wp := 35, Wj := 37, h := 0 }

def old32t1 : PrefixState :=
  { i := 21, W := 38, A := 459422106005237, q := 130895839231,
    r := 227068085223373, j := 20, Wp := 35, Wj := 37, h := 0 }

def new32t1 : PrefixState :=
  { i := 21, W := 38, A := 460173725282037, q := 49291460607,
    r := 85507053881823, j := 20, Wp := 35, Wj := 37, h := 0 }

example : abstractK 32 old32 = abstractK 32 new32 := by
  native_decide

example : abstractK 32 old32 = abstractK 32 new32 := by
  native_decide

example : old32.r ≠ new32.r := by
  native_decide

example : Hval old32 = Hval new32 := by
  native_decide

/-- The fixed abstraction identifies two reachable states with different
exact representatives; it does not carry enough information to determine
`v = v_2(5(r+1)/2 - 1)`. -/
def abstractionValuationBlocker : Prop :=
  abstractK 32 old32 = abstractK 32 new32 ∧ old32.r ≠ new32.r

example : abstractionValuationBlocker := by
  unfold abstractionValuationBlocker
  constructor
  · native_decide
  · native_decide

example : blockN 1 1 (suffixA ([1] : List Nat)) old32.r =
    2 * (5 * old32t1.r + 3) := by
  native_decide

example : blockN 1 1 (suffixA ([1] : List Nat)) new32.r =
    2 * (5 * new32t1.r + 3) := by
  native_decide

example : mValue old32.A old32.W old32.i old32.q =
    (old32.r + 1) / 2 := by
  native_decide

example : mValue new32.A new32.W new32.i new32.q =
    (new32.r + 1) / 2 := by
  native_decide

example : ¬ mFailureCongruence old32.A old32.W old32.i old32.q
    (Hval old32) := by
  unfold mFailureCongruence mValue
  native_decide

example : ¬ mFailureCongruence new32.A new32.W new32.i new32.q
    (Hval new32) := by
  unfold mFailureCongruence mValue
  native_decide

end StringFlow.Automaton
