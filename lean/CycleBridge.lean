import BlockAutomaton
import FinalStatement
import S6AuditStage1
import SurvExAudit
import Td0Real
import Angelina_Gilberta_Bridge

/-!
# Cycle bridge: corrected decisive window valuation -> no positive cycle of 7

This module is the downstream interface for the open window theorem.
It does **not** prove the window bound; it packages the implication

    decisiveWindowValuationBoundCorrected -> ¬ OrbitCycle 7

The old unconstrained `decisiveWindowValuationBound` is disproved and
is never consumed by this bridge.

as the target `windowBoundToNoCycle`, and proves the low-level orbit
bridges that do not depend on the window: the full accelerated orbit
coincides with the top-level orbit, and every state of a 7-cycle is
therefore reachable in the corrected full-orbit predicate.

The remaining open lemmas (cycle -> reset head, cycle -> QB-8, QB-8 ->
failure window, failure window -> contradiction) are documented in
`docs/cycle_bridge_window_to_no_cycle.md`; they are deliberately not
declared as theorems here, so this file has no `sorry`.
-/

namespace StringFlow

namespace CycleBridge

/-- Exponent of the largest power of `5` dividing `n`. -/
def fiveValuation (n : Nat) : Nat :=
  n.factorization 5

/-- The five-adic odd part of `n`. -/
def fiveOddPart (n : Nat) : Nat :=
  n / 5 ^ fiveValuation n

/-- The five-adic decomposition `n = 5^k * s`. -/
theorem fiveOddPart_spec {n : Nat} (hn : n ≠ 0) :
    n = 5 ^ fiveValuation n * fiveOddPart n := by
  have hp : Nat.Prime 5 := by norm_num
  have hdvd : 5 ^ fiveValuation n ∣ n := by
    exact (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl
  unfold fiveOddPart
  exact (Nat.mul_div_cancel' hdvd).symm

/-- The five-adic odd part is not divisible by `5`. -/
theorem fiveOddPart_not_dvd_five {n : Nat} (hn : n ≠ 0) :
    ¬ 5 ∣ fiveOddPart n := by
  have hp : Nat.Prime 5 := by norm_num
  have hnot : ¬ 5 ^ (n.factorization 5 + 1) ∣ n :=
    Nat.pow_succ_factorization_not_dvd hn hp
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  have hspec := fiveOddPart_spec hn
  rw [hq] at hspec
  dsimp [fiveValuation] at hspec
  have hspec' : n = 5 ^ (fiveValuation n + 1) * q := by
    calc
      n = 5 ^ fiveValuation n * (5 * q) := hspec
      _ = (5 ^ fiveValuation n * 5) * q := by ring
      _ = (5 * 5 ^ fiveValuation n) * q := by ring
      _ = 5 ^ (fiveValuation n + 1) * q := by
          rw [Nat.pow_succ]
          ring
  exact hnot ⟨q, hspec'⟩

/-- Oddness is preserved by removing factors of `5`. -/
theorem fiveOddPart_odd_of_odd {n : Nat} (hn : n % 2 = 1) :
    fiveOddPart n % 2 = 1 := by
  by_cases hz : n = 0
  · subst n
    norm_num at hn
  · have hspec := fiveOddPart_spec hz
    have hoddn : Odd n := Nat.odd_iff.mpr hn
    have hoddprod : Odd (5 ^ fiveValuation n * fiveOddPart n) := by
      rwa [← hspec]
    exact Nat.odd_iff.mp (Nat.odd_mul.mp hoddprod).2

/-- The terminal data used to construct a reset-window witness.
`s` and `k0` are forced to be the five-adic odd part and valuation of
the single previous terminal `r_prev`. -/
structure RealTerminal where
  r_prev : Nat
  s : Nat
  k0 : Nat
  hprod : s * 5 ^ k0 = r_prev + 1
  hs_odd : S6Audit.IsOdd s
  hs_not_five : ¬ 5 ∣ s
  hreach : S6Audit.GeneralOrbitFrom7 r_prev

/-- Target: the corrected decisive window valuation bound rules out
every positive cycle of the accelerated 5x+1 orbit of 7.  The old
`BlockAutomaton.decisiveWindowValuationBound` is invalid and is not
used here. -/
def windowBoundToNoCycle : Prop :=
  BlockAutomaton.decisiveWindowValuationBoundCorrected → ¬ OrbitCycle 7

/-- The full accelerated step is definitionally the top-level step. -/
theorem fullOrbitStep_eq_fiveXPlusOneStep (x : Nat) :
    S6Audit.fullOrbitStep x = fiveXPlusOneStep x := by
  rfl

/-- The full accelerated orbit of `7` is exactly the top-level orbit. -/
theorem fullOrbitIter_eq_fiveXPlusOneOrbit (n : Nat) :
    S6Audit.fullOrbitIter n = fiveXPlusOneOrbit 7 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [S6Audit.fullOrbitIter, fiveXPlusOneOrbit,
        fullOrbitStep_eq_fiveXPlusOneStep, ih]

/-- Every top-level orbit state of `7` is full-orbit reachable. -/
theorem fiveXPlusOneOrbit_full_reachable (n : Nat) :
    S6Audit.FullOrbitFrom7 (fiveXPlusOneOrbit 7 n) := by
  refine ⟨n, ?_⟩
  exact fullOrbitIter_eq_fiveXPlusOneOrbit n

/-- Every state of a 7-cycle is full-orbit reachable. -/
theorem orbit_cycle_states_full_reachable (_h : OrbitCycle 7) :
    ∀ n : Nat, S6Audit.FullOrbitFrom7 (fiveXPlusOneOrbit 7 n) :=
  fiveXPlusOneOrbit_full_reachable

/-- Every state of a 7-cycle is general-orbit reachable (from
`FinalStatement`). -/
theorem orbit_cycle_states_general_reachable (_h : OrbitCycle 7) :
    ∀ n : Nat, S6Audit.GeneralOrbitFrom7 (fiveXPlusOneOrbit 7 n) :=
  fiveXPlusOneOrbit_general_orbit 7 S6Audit.general_orbit_seven

/-- Every state of the top-level orbit of `7` is odd. -/
theorem fiveXPlusOneOrbit_odd_7 (n : Nat) :
    S6Audit.IsOdd (fiveXPlusOneOrbit 7 n) := by
  rw [← fullOrbitIter_eq_fiveXPlusOneOrbit n]
  exact S6Audit.fullOrbitIter_odd n

/-- Every state of the top-level orbit of `7` is positive. -/
theorem fiveXPlusOneOrbit_pos_7 (n : Nat) :
    0 < fiveXPlusOneOrbit 7 n := by
  have hodd := fiveXPlusOneOrbit_odd_7 n
  exact Nat.pos_of_ne_zero (by
    intro hz
    rw [hz] at hodd
    unfold S6Audit.IsOdd at hodd
    norm_num at hodd)

/-- The full accelerated step is the odd part of `5x+1`. -/
theorem fiveXPlusOneStep_eq_oddPart (x : Nat) :
    fiveXPlusOneStep x = StringFlow.oddPart (5 * x + 1) := by
  unfold fiveXPlusOneStep
  have hpos : 0 < 5 * x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos
  have hodd : StringFlow.oddPart (5 * x + 1) % 2 = 1 :=
    StringFlow.oddPart_odd_of_pos (5 * x + 1) hpos
  have hdec' : 5 * x + 1 =
      2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1) := by
    have hdef : twoValuation (5 * x + 1) = twoValuation (5 * x + 1) := rfl
    rwa [hdef] at hdec
  have hv : twoValuation
      (2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1)) =
      twoValuation (5 * x + 1) := by
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq
      (twoValuation (5 * x + 1)) (StringFlow.oddPart (5 * x + 1)) hodd
  conv_lhs => rw [hdec', hv]
  exact Nat.mul_div_cancel_left (StringFlow.oddPart (5 * x + 1))
    (by positivity : 0 < 2 ^ twoValuation (5 * x + 1))

/-- The exact accelerated-step equation `2^t * x' = 5x+1`. -/
theorem fiveXPlusOneStep_mul_eq (x : Nat) :
    2 ^ twoValuation (5 * x + 1) * fiveXPlusOneStep x = 5 * x + 1 := by
  have hpos : 0 < 5 * x + 1 := by positivity
  rw [fiveXPlusOneStep_eq_oddPart x]
  exact (StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos).symm

/-- A rise step's output is `3 mod 5` for `t=1` and `4 mod 5` for
`t=2`. -/
theorem rise_step_next_mod_five (x t : Nat)
    (ht : t = 1 ∨ t = 2)
    (hvalid : twoValuation (5 * x + 1) = t) :
    ((5 * x + 1) / 2 ^ t) % 5 = (if t = 1 then 3 else 4) := by
  set q : Nat := (5 * x + 1) / 2 ^ t
  have hmul := fiveXPlusOneStep_mul_eq x
  have hq : q = fiveXPlusOneStep x := by
    dsimp [q]
    rw [← hvalid]
    rfl
  have h2 : 2 ^ t * q = 5 * x + 1 := by
    rw [hq]
    simpa [hvalid] using hmul
  have hmod : (5 * x + 1) % 5 = 1 := by omega
  have hmodmul : (2 ^ t * q) % 5 = 1 := by
    rw [h2]
    exact hmod
  have hmod2 : ((2 ^ t % 5) * (q % 5)) % 5 = 1 := by
    rw [← Nat.mul_mod]
    exact hmodmul
  have hqlt : q % 5 < 5 := Nat.mod_lt _ (by decide)
  rcases ht with rfl | rfl
  · change q % 5 = 3
    interval_cases q % 5 <;> norm_num at hmod2 <;> omega
  · change q % 5 = 4
    interval_cases q % 5 <;> norm_num at hmod2 <;> omega

/-- The full accelerated step never introduces a factor of `5`. -/
theorem fiveXPlusOneStep_not_dvd_five (x : Nat) (_hx : ¬ 5 ∣ x) :
    ¬ 5 ∣ fiveXPlusOneStep x := by
  intro hdiv
  have hpos : 0 < 5 * x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos
  have hstep := fiveXPlusOneStep_eq_oddPart x
  rw [hstep] at hdiv
  have hprod : 2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1) =
      5 * x + 1 := hdec.symm
  rcases hdiv with ⟨k, hk⟩
  have h5div : 5 ∣ 5 * x + 1 := by
    refine ⟨2 ^ twoValuation (5 * x + 1) * k, ?_⟩
    calc
      5 * x + 1
          = 2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1) :=
            hprod.symm
      _ = 2 ^ twoValuation (5 * x + 1) * (5 * k) := by
            rw [hk]
      _ = 5 * (2 ^ twoValuation (5 * x + 1) * k) := by
            ac_rfl
  have hmod : (5 * x + 1) % 5 = 1 := by omega
  have hmod0 : (5 * x + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5div
  omega

/-- No state of the orbit of `7` is divisible by `5`. -/
theorem fiveXPlusOneOrbit_not_dvd_five (n : Nat) :
    ¬ 5 ∣ fiveXPlusOneOrbit 7 n := by
  induction n with
  | zero => norm_num [fiveXPlusOneOrbit]
  | succ n ih =>
      have hstep := fiveXPlusOneStep_not_dvd_five (fiveXPlusOneOrbit 7 n) ih
      simpa [fiveXPlusOneOrbit] using hstep

/-- If the exact step weight is at most two, the accelerated step
strictly increases the state. -/
theorem fiveXPlusOneStep_gt_of_weight_le_two (x : Nat)
    (hx : 0 < x) (ht : twoValuation (5 * x + 1) ≤ 2) :
    x < fiveXPlusOneStep x := by
  unfold fiveXPlusOneStep
  let t := twoValuation (5 * x + 1)
  have ht' : t ≤ 2 := by simpa [t] using ht
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  have hpow_pos : 0 < 2 ^ t := Nat.pow_pos (by decide : 0 < 2)
  have hpos5 : 0 < 5 * x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos5
  have hdec' : 5 * x + 1 =
      2 ^ t * StringFlow.oddPart (5 * x + 1) := by
    have ht_def : twoValuation (5 * x + 1) = t := rfl
    rw [ht_def] at hdec
    exact hdec
  have hxmul_lt : x * 2 ^ t < 5 * x + 1 := by
    rcases hcases with h0 | h1 | h2
    · rw [h0]
      omega
    · rw [h1]
      omega
    · rw [h2]
      omega
  have hodd_gt : x < StringFlow.oddPart (5 * x + 1) := by
    rw [hdec'] at hxmul_lt
    have hxmul : x * 2 ^ t <
        StringFlow.oddPart (5 * x + 1) * 2 ^ t := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hxmul_lt
    exact Nat.lt_of_mul_lt_mul_right hxmul
  have hdiv : (5 * x + 1) / 2 ^ t =
      StringFlow.oddPart (5 * x + 1) := by
    conv_lhs => rw [hdec']
    exact Nat.mul_div_cancel_left (StringFlow.oddPart (5 * x + 1)) hpow_pos
  rwa [hdiv]

/-- A positive cycle of the accelerated 5x+1 orbit contains a C3
start: at least one step weight is at least three. -/
theorem orbit_cycle_imp_exists_c3_start (h : OrbitCycle 7) :
    ∃ n : Nat, 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 n + 1) := by
  by_contra hnone
  push Not at hnone
  rcases h with ⟨n, m, hmn, heq⟩
  have hmle : m ≤ n := by omega
  have hmono : ∀ i, fiveXPlusOneOrbit 7 i < fiveXPlusOneOrbit 7 (i + 1) := by
    intro i
    have hle2 : twoValuation (5 * fiveXPlusOneOrbit 7 i + 1) ≤ 2 := by
      have hlt := hnone i
      omega
    have hstep := fiveXPlusOneStep_gt_of_weight_le_two
      (fiveXPlusOneOrbit 7 i) (fiveXPlusOneOrbit_pos_7 i) hle2
    simpa [fiveXPlusOneOrbit] using hstep
  have hchain : ∀ k, 1 ≤ k → k ≤ n - m →
      fiveXPlusOneOrbit 7 m < fiveXPlusOneOrbit 7 (m + k) := by
    intro k hk1 hk
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          simpa using hmono m
        · have hk1' : 1 ≤ k := by omega
          have hlt := ih hk1' (by omega)
          have hstep : fiveXPlusOneOrbit 7 (m + k) <
              fiveXPlusOneOrbit 7 (m + k + 1) := hmono (m + k)
          have hlt2 : fiveXPlusOneOrbit 7 m <
              fiveXPlusOneOrbit 7 (m + k + 1) := lt_trans hlt hstep
          simpa [Nat.add_assoc] using hlt2
  have hltn : fiveXPlusOneOrbit 7 m < fiveXPlusOneOrbit 7 n := by
    have hnm : 1 ≤ n - m := by omega
    have hk := hchain (n - m) hnm (by omega)
    have hn : m + (n - m) = n := Nat.add_sub_of_le hmle
    simpa [hn] using hk
  exact (ne_of_lt hltn) heq

/-- A cycle repeat gives a period `p` and a deterministic
periodicity identity from the repeat index onward. -/
theorem orbit_repeat_period (h : OrbitCycle 7) :
    ∃ m p : Nat, 1 ≤ p ∧
      fiveXPlusOneOrbit 7 (m + p) = fiveXPlusOneOrbit 7 m ∧
      (∀ d : Nat,
        fiveXPlusOneOrbit 7 (m + d + p) = fiveXPlusOneOrbit 7 (m + d)) := by
  rcases h with ⟨n, m, hmn, heq⟩
  let p := n - m
  have hp : 1 ≤ p := by omega
  have hn : m + p = n := by
    dsimp [p]
    exact Nat.add_sub_of_le (by omega)
  have heq' : fiveXPlusOneOrbit 7 (m + p) = fiveXPlusOneOrbit 7 m := by
    rw [← hn] at heq
    exact heq.symm
  refine ⟨m, p, hp, heq', ?_⟩
  intro d
  induction d with
  | zero => simpa using heq'
  | succ d ih =>
      have h1 : fiveXPlusOneOrbit 7 (m + (d + 1) + p) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 (m + d + p)) := by
        rw [show m + (d + 1) + p = (m + d + p) + 1 by omega]
        simp [fiveXPlusOneOrbit]
      have h2 : fiveXPlusOneOrbit 7 (m + (d + 1)) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 (m + d)) := by
        rw [show m + (d + 1) = (m + d) + 1 by omega]
        simp [fiveXPlusOneOrbit]
      rw [h1, h2, ih]

/-- Periodicity at one point extends to all later indices. -/
theorem periodic_shift (c p : Nat)
    (hper : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c) :
    ∀ d : Nat, fiveXPlusOneOrbit 7 (c + d + p) = fiveXPlusOneOrbit 7 (c + d) := by
  intro d
  induction d with
  | zero => simpa using hper
  | succ d ih =>
      have h1 : fiveXPlusOneOrbit 7 (c + (d + 1) + p) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 (c + d + p)) := by
        rw [show c + (d + 1) + p = (c + d + p) + 1 by omega]
        simp [fiveXPlusOneOrbit]
      have h2 : fiveXPlusOneOrbit 7 (c + (d + 1)) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 (c + d)) := by
        rw [show c + (d + 1) = (c + d) + 1 by omega]
        simp [fiveXPlusOneOrbit]
      rw [h1, h2, ih]

/-- Periodicity extends to shifts by multiples of `p`. -/
theorem periodic_shift_mul (c p : Nat)
    (hper : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c)
    (k n : Nat) :
    fiveXPlusOneOrbit 7 (c + n + k * p) = fiveXPlusOneOrbit 7 (c + n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := periodic_shift c p hper (n + k * p)
      have hidx : c + n + (k + 1) * p = c + (n + k * p) + p := by ring
      calc
        fiveXPlusOneOrbit 7 (c + n + (k + 1) * p)
            = fiveXPlusOneOrbit 7 (c + (n + k * p) + p) := by
                rw [hidx]
        _ = fiveXPlusOneOrbit 7 (c + (n + k * p)) := hstep
        _ = fiveXPlusOneOrbit 7 (c + n) := by
            simpa [Nat.add_assoc] using ih

/-- A positive cycle contains a periodic C3-start segment: there is
`c` and a period `p` with `t(c) >= 3` and `orbit(c+p) = orbit c`. -/
theorem orbit_cycle_imp_periodic_c3_segment (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ∧
      fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c := by
  rcases orbit_repeat_period h with ⟨m, p, hp, heq', hper⟩
  have hc3 : ∃ c : Nat, m ≤ c ∧ c < m + p ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
    by_contra hnone
    push Not at hnone
    have hmono_in : ∀ i : Nat, m ≤ i → i < m + p →
        fiveXPlusOneOrbit 7 i < fiveXPlusOneOrbit 7 (i + 1) := by
      intro i hi1 hi2
      have hle2 : twoValuation (5 * fiveXPlusOneOrbit 7 i + 1) ≤ 2 := by
        have hbad := hnone i hi1 hi2
        omega
      have hstep := fiveXPlusOneStep_gt_of_weight_le_two
        (fiveXPlusOneOrbit 7 i) (fiveXPlusOneOrbit_pos_7 i) hle2
      simpa [fiveXPlusOneOrbit] using hstep
    have hchain : ∀ k : Nat, 1 ≤ k → k ≤ p →
        fiveXPlusOneOrbit 7 m < fiveXPlusOneOrbit 7 (m + k) := by
      intro k hk1 hkp
      induction k with
      | zero => omega
      | succ k ih =>
          by_cases hk0 : k = 0
          · subst k
            simpa using hmono_in m (by omega) (by omega)
          · have hk1' : 1 ≤ k := by omega
            have hlt := ih hk1' (by omega)
            have hmid : m ≤ m + k := by omega
            have hlt2 : m + k < m + p := by omega
            have hstep := hmono_in (m + k) hmid hlt2
            have hlt2' : fiveXPlusOneOrbit 7 m <
                fiveXPlusOneOrbit 7 (m + k + 1) := lt_trans hlt hstep
            simpa [Nat.add_assoc] using hlt2'
    have hltp : fiveXPlusOneOrbit 7 m < fiveXPlusOneOrbit 7 (m + p) :=
      hchain p hp (by omega)
    exact (ne_of_lt hltp) heq'.symm
  rcases hc3 with ⟨c, hcm, hclt, hc3'⟩
  refine ⟨c, p, hp, hc3', ?_⟩
  have hc_eq : c = m + (c - m) := by omega
  have hper_c := hper (c - m)
  rw [← hc_eq] at hper_c
  exact hper_c

/-- The period word of a cycle segment: exact step weights along `p`
steps starting at orbit state `c`. -/
def cycleWord : Nat → Nat → List Nat
  | _, 0 => []
  | c, p + 1 =>
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :: cycleWord (c + 1) p

/-- The `j`-th step weight of the cycle word (`0` past the end). -/
def cycleWordStepAt (c p j : Nat) : Nat :=
  (cycleWord c p).getI j

/-- Total weight of the cycle word. -/
def cycleWordTotalWeight (c p : Nat) : Nat :=
  StringFlow.wordWeight (cycleWord c p)

/-- The cycle states in one period. -/
def cycleStateList (c p : Nat) : List Nat :=
  (List.range p).map (fun i => fiveXPlusOneOrbit 7 (c + i))

/-- Membership in the period-state list. -/
theorem mem_cycleStateList_iff (c p x : Nat) :
    x ∈ cycleStateList c p ↔
      ∃ i, i < p ∧ fiveXPlusOneOrbit 7 (c + i) = x := by
  simp [cycleStateList, List.mem_map, List.mem_range]

/-- A nonempty period contains a global minimum state. -/
theorem cycle_min_exists (c p : Nat) (hp : 1 ≤ p) :
    ∃ i, i < p ∧ ∀ j, j < p →
      fiveXPlusOneOrbit 7 (c + i) ≤ fiveXPlusOneOrbit 7 (c + j) := by
  let l := cycleStateList c p
  have hlen : 0 < l.length := by
    dsimp [l, cycleStateList]
    simp
    omega
  let m := l.minimum_of_length_pos hlen
  have hmem : m ∈ l := l.minimum_of_length_pos_mem hlen
  rcases (mem_cycleStateList_iff c p m).mp hmem with ⟨i, hi, heq⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hmemj : fiveXPlusOneOrbit 7 (c + j) ∈ l :=
    (mem_cycleStateList_iff c p (fiveXPlusOneOrbit 7 (c + j))).mpr
      ⟨j, hj, rfl⟩
  have hle := l.minimum_of_length_pos_le_of_mem hmemj hlen
  simpa [m, heq] using hle

/-- Membership in a `take` implies membership in the whole list. -/
theorem mem_take_imp_mem {a n : Nat} (l : List Nat) (h : a ∈ l.take n) :
    a ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons b bs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          simp [List.take] at h
          cases h with
          | inl hb => simp [hb]
          | inr htail =>
              rw [List.mem_cons]
              exact Or.inr (ih htail)

/-- PMI prefix weight equals the word weight of the `take`. -/
theorem cycleWord_prefixWeight_eq_wordWeight_take (c p j : Nat) :
    StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j =
      StringFlow.wordWeight ((cycleWord c p).take j) := by
  unfold cycleWordStepAt
  rw [StringFlow.TD0.wordWeight_eq_sum]
  exact StringFlow.TD0.prefixWeight_getI_eq_take_sum (cycleWord c p) j

/-- Word weight splits as the prefix weight before the last step plus
the last step weight. -/
theorem cycleWord_weight_split_last (c p : Nat) (hp : 1 ≤ p) :
    StringFlow.wordWeight (cycleWord c p) =
      StringFlow.PMI.prefixWeight (cycleWordStepAt c p) (p - 1) +
        twoValuation (5 * fiveXPlusOneOrbit 7 (c + (p - 1)) + 1) := by
  induction p generalizing c with
  | zero => omega
  | succ p ih =>
      cases p with
      | zero =>
          simp [cycleWord, StringFlow.wordWeight, StringFlow.PMI.prefixWeight,
            cycleWordStepAt]
      | succ n =>
          have hih := ih (c + 1)
          have hih' : StringFlow.wordWeight (cycleWord (c + 1) (n + 1)) =
              StringFlow.PMI.prefixWeight (cycleWordStepAt (c + 1) (n + 1)) n +
                twoValuation (5 * fiveXPlusOneOrbit 7 (c + 1 + n) + 1) := by
            have h := hih (by omega : 1 ≤ n + 1)
            simpa [Nat.add_sub_cancel] using h
          have h1 : StringFlow.wordWeight (cycleWord c (n + 2)) =
              twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) +
                StringFlow.wordWeight (cycleWord (c + 1) (n + 1)) := by
            simp [cycleWord, StringFlow.wordWeight]
          have h2 : StringFlow.PMI.prefixWeight (cycleWordStepAt c (n + 2)) (n + 1) =
              twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) +
                StringFlow.PMI.prefixWeight (cycleWordStepAt (c + 1) (n + 1)) n := by
            change StringFlow.PMI.prefixWeight (fun j =>
                (twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ::
                  cycleWord (c + 1) (n + 1)).getI j) (n + 1) =
              twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) +
                StringFlow.PMI.prefixWeight (fun j =>
                  (cycleWord (c + 1) (n + 1)).getI j) n
            rw [StringFlow.PH.prefixWeight_cons_getI]
          have hlast : twoValuation (5 * fiveXPlusOneOrbit 7 (c + (n + 1)) + 1) =
              twoValuation (5 * fiveXPlusOneOrbit 7 ((c + 1) + n) + 1) := by
            have hidx : c + (n + 1) = (c + 1) + n := by omega
            rw [hidx]
          change StringFlow.wordWeight (cycleWord c (n + 2)) =
            StringFlow.PMI.prefixWeight (cycleWordStepAt c (n + 2)) (n + 1) +
              twoValuation (5 * fiveXPlusOneOrbit 7 (c + (n + 1)) + 1)
          rw [h1, h2, hih', hlast]
          omega

/-- Following `cycleWord c p` from `orbit c` reaches `orbit (c+p)`. -/
theorem cycleWord_orbit_eq (c p : Nat) :
    StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 (c + p) := by
  induction p generalizing c with
  | zero =>
      simp [cycleWord, StringFlow.Word.wordOrbit]
  | succ p ih =>
      unfold cycleWord
      rw [StringFlow.Word.wordOrbit]
      have hstep : (5 * fiveXPlusOneOrbit 7 c + 1) /
          2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := rfl
      rw [hstep]
      have horb : fiveXPlusOneOrbit 7 (c + 1) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := by
        rw [show c + 1 = Nat.succ c by omega]
        simp [fiveXPlusOneOrbit]
      rw [← horb]
      have hih := ih (c + 1)
      rw [hih]
      congr 1
      omega

/-- The cycle word is a valid word for its start state. -/
theorem cycleWord_wordValid (c p : Nat) :
    StringFlow.Word.wordValid (cycleWord c p) (fiveXPlusOneOrbit 7 c) := by
  induction p generalizing c with
  | zero => simp [cycleWord, StringFlow.Word.wordValid]
  | succ p ih =>
      unfold cycleWord
      rw [StringFlow.Word.wordValid]
      constructor
      · rcases (fiveXPlusOneStep_wordValid (fiveXPlusOneOrbit 7 c)).1 with
          ⟨hdiv, _⟩
        exact hdiv
      · have hstep : (5 * fiveXPlusOneOrbit 7 c + 1) /
          2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := rfl
        rw [hstep]
        have horb : fiveXPlusOneOrbit 7 (c + 1) =
            fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := by
          rw [show c + 1 = Nat.succ c by omega]
          simp [fiveXPlusOneOrbit]
        rw [← horb]
        exact ih (c + 1)

/-- Length of the cycle word is `p`. -/
theorem cycleWord_length (c p : Nat) :
    (cycleWord c p).length = p := by
  induction p generalizing c with
  | zero => simp [cycleWord]
  | succ p ih => simp [cycleWord, ih]

/-- Taking a prefix of a cycle word cuts the period. -/
theorem cycleWord_take_eq (c p k : Nat) (hk : k ≤ p) :
    (cycleWord c p).take k = cycleWord c k := by
  induction k generalizing c p with
  | zero => simp [cycleWord]
  | succ k ih =>
      cases p with
      | zero => omega
      | succ p =>
          have hk' : k ≤ p := by omega
          have h := ih (c + 1) p hk'
          simp [cycleWord, h]

/-- The `k`-th entry of the cycle word is the exact step weight at
the `k`-th orbit state. -/
theorem cycleWord_getI_eq (c p k : Nat) (hk : k < p) :
    (cycleWord c p).getI k =
      twoValuation (5 * fiveXPlusOneOrbit 7 (c + k) + 1) := by
  induction k generalizing c p with
  | zero =>
      cases p with
      | zero => omega
      | succ p => simp [cycleWord]
  | succ k ih =>
      cases p with
      | zero => omega
      | succ p =>
          have hk' : k < p := by omega
          have h := ih (c + 1) p hk'
          change (twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ::
              cycleWord (c + 1) p).getI (k + 1) =
            twoValuation (5 * fiveXPlusOneOrbit 7 (c + (k + 1)) + 1)
          rw [List.getI_cons_succ]
          have h' : twoValuation (5 * fiveXPlusOneOrbit 7 (c + 1 + k) + 1) =
              twoValuation (5 * fiveXPlusOneOrbit 7 (c + (k + 1)) + 1) := by
            have hidx : c + 1 + k = c + (k + 1) := by omega
            rw [hidx]
          rw [← h']
          exact h

/-- A prefix of the cycle word reaches the corresponding orbit state. -/
theorem cycleWord_prefix_orbit_eq (c p k : Nat) (hk : k ≤ p) :
    StringFlow.Word.wordOrbit ((cycleWord c p).take k)
        (fiveXPlusOneOrbit 7 c) = fiveXPlusOneOrbit 7 (c + k) := by
  rw [cycleWord_take_eq c p k hk]
  exact cycleWord_orbit_eq c k

/-- Each cycle-word step is exact: the word weight equals the exact
2-adic valuation along the orbit. -/
theorem cycleWord_step_exact (c p k : Nat) (hk : k < p) :
    twoValuation (5 * StringFlow.Word.wordOrbit
        ((cycleWord c p).take k) (fiveXPlusOneOrbit 7 c) + 1) =
      (cycleWord c p).getI k := by
  have hk_le : k ≤ p := by omega
  rw [cycleWord_prefix_orbit_eq c p k hk_le]
  exact (cycleWord_getI_eq c p k hk).symm

/-- The first step of a nonempty cycle word is the exact weight at the
start state. -/
theorem cycleWord_head_eq (c p : Nat) (hp : 1 ≤ p) :
    cycleWord c p =
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :: cycleWord (c + 1) (p - 1) := by
  cases p with
  | zero => omega
  | succ p =>
      simp [cycleWord]

/-- `5x+1` is even for odd `x`, so its exact step weight is at least 1. -/
theorem twoValuation_five_mul_add_one_ge_one (x : Nat)
    (hodd : S6Audit.IsOdd x) :
    1 ≤ twoValuation (5 * x + 1) := by
  have hpos : 0 < 5 * x + 1 := by positivity
  have heven : (5 * x + 1) % 2 = 0 := by
    have hx : x % 2 = 1 := hodd
    have h5x : (5 * x) % 2 = 1 := by
      rw [Nat.mul_mod]
      rw [show 5 % 2 = 1 by norm_num, hx]
    rw [Nat.add_mod, h5x]
  have hdiv : 2 ^ 1 ∣ 5 * x + 1 := by
    have h2 : 2 ∣ 5 * x + 1 := Nat.dvd_of_mod_eq_zero heven
    simpa using h2
  exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * x + 1) 1 hpos).mpr hdiv

/-- From an odd state, the exact accelerated step divides by at least
`2`, so its output is no larger than the `t=1` quotient. -/
theorem fiveXPlusOneStep_le_div_two (x : Nat) (hodd : S6Audit.IsOdd x) :
    fiveXPlusOneStep x ≤ (5 * x + 1) / 2 := by
  unfold fiveXPlusOneStep
  have hge1 : 1 ≤ twoValuation (5 * x + 1) :=
    twoValuation_five_mul_add_one_ge_one x hodd
  have hpow : 2 ≤ 2 ^ twoValuation (5 * x + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hge1
  have hq2 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) * 2 ≤
      5 * x + 1 := by
    have h1 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) * 2 ≤
        (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) *
          2 ^ twoValuation (5 * x + 1) :=
      Nat.mul_le_mul_left
        ((5 * x + 1) / 2 ^ twoValuation (5 * x + 1)) hpow
    have h2 : (5 * x + 1) / 2 ^ twoValuation (5 * x + 1) *
        2 ^ twoValuation (5 * x + 1) ≤ 5 * x + 1 :=
      Nat.div_mul_le_self (5 * x + 1) (2 ^ twoValuation (5 * x + 1))
    exact le_trans h1 h2
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 hq2

/-- The exact orbit states of `7` satisfy the state bound
`r_n < 5^n` for every `n ≥ 2`. -/
theorem fiveXPlusOneOrbit_lt_five_pow (n : Nat) (hn : 2 ≤ n) :
    fiveXPlusOneOrbit 7 n < 5 ^ n := by
  refine Nat.le_induction ?base ?step n hn
  · norm_num [fiveXPlusOneOrbit, fiveXPlusOneStep, StringFlow.twoValuation]
  · intro k _hk hlt
    have horb : fiveXPlusOneOrbit 7 (k + 1) =
        fiveXPlusOneStep (fiveXPlusOneOrbit 7 k) := by
      rw [show k + 1 = Nat.succ k by omega]
      simp [fiveXPlusOneOrbit]
    rw [horb]
    have hle := fiveXPlusOneStep_le_div_two (fiveXPlusOneOrbit 7 k)
      (fiveXPlusOneOrbit_odd_7 k)
    have hdiv : (5 * fiveXPlusOneOrbit 7 k + 1) / 2 < 5 ^ (k + 1) := by
      have hlt' : 5 * fiveXPlusOneOrbit 7 k + 1 < 5 ^ (k + 1) * 2 := by
        have h1 : 5 * fiveXPlusOneOrbit 7 k + 1 < 5 * 5 ^ k + 1 := by omega
        have h2 : 5 * 5 ^ k + 1 = 5 ^ (k + 1) + 1 := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have h3 : 5 ^ (k + 1) + 1 < 5 ^ (k + 1) * 2 := by
          have hpos : 0 < 5 ^ (k + 1) := Nat.pow_pos (by decide)
          omega
        omega
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2 hlt'
    exact lt_of_le_of_lt hle hdiv

/-- Every entry of the cycle word is a valid step weight `t >= 1`. -/
theorem cycleWord_mem_ge_one (c p : Nat) {t : Nat} (ht : t ∈ cycleWord c p) :
    1 ≤ t := by
  induction p generalizing c with
  | zero => simp [cycleWord] at ht
  | succ p ih =>
      have ht' : t = twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ∨
          t ∈ cycleWord (c + 1) p := by
        simpa [cycleWord] using ht
      rcases ht' with ht0 | htail
      · rw [ht0]
        exact twoValuation_five_mul_add_one_ge_one (fiveXPlusOneOrbit 7 c)
          (fiveXPlusOneOrbit_odd_7 c)
      · exact ih (c + 1) htail

/-- Every non-C3 entry of the cycle word is a rise step `t = 1` or
`t = 2`. -/
theorem cycleWord_non_c3_rise (c p : Nat) {t : Nat} (ht : t ∈ cycleWord c p)
    (hnot : ¬ 3 ≤ t) : t = 1 ∨ t = 2 := by
  have hge : 1 ≤ t := cycleWord_mem_ge_one c p ht
  omega

/-- A `t >= 3` step from a positive state strictly decreases. -/
theorem c3Step_lt_of_pos (x t : Nat) (hx : 1 ≤ x) (ht : 3 ≤ t) :
    (5 * x + 1) / 2 ^ t < x := by
  have hpow : 8 ≤ 2 ^ t := Nat.pow_le_pow_right (show 0 < 2 by decide) ht
  have hlt : 5 * x + 1 < 2 ^ t * x := by
    have hle : 5 * x + 1 ≤ 6 * x := by omega
    have h6 : 6 * x < 8 * x := by omega
    have h8 : 8 * x ≤ 2 ^ t * x := Nat.mul_le_mul_right x hpow
    omega
  have hpos : 0 < 2 ^ t := Nat.pow_pos (by decide)
  rw [Nat.div_lt_iff_lt_mul hpos]
  have hcomm : x * 2 ^ t = 2 ^ t * x := Nat.mul_comm x (2 ^ t)
  rwa [hcomm]

/-- A C3 orbit step strictly decreases. -/
theorem orbit_step_lt_of_c3 (i : Nat)
    (ht : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 i + 1)) :
    fiveXPlusOneOrbit 7 (i + 1) < fiveXPlusOneOrbit 7 i := by
  have hpos : 1 ≤ fiveXPlusOneOrbit 7 i := fiveXPlusOneOrbit_pos_7 i
  have hstep := c3Step_lt_of_pos (fiveXPlusOneOrbit 7 i)
    (twoValuation (5 * fiveXPlusOneOrbit 7 i + 1)) hpos ht
  simpa [fiveXPlusOneOrbit, fiveXPlusOneStep] using hstep

/-- Every positive cycle has a closed period word starting at a
global-minimum state, whose first step is a rise step (`t <= 2`). -/
theorem orbit_cycle_imp_min_rise_start (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ≤ 2 := by
  rcases orbit_cycle_imp_periodic_c3_segment h with ⟨c0, p, hp, hc3, hper⟩
  have hper' := periodic_shift c0 p hper
  rcases cycle_min_exists c0 p hp with ⟨i, hi, hmin⟩
  let c := c0 + i
  have hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c := by
    rw [cycleWord_orbit_eq c p]
    have hperAt : fiveXPlusOneOrbit 7 (c0 + i + p) =
        fiveXPlusOneOrbit 7 (c0 + i) := hper' i
    simpa [c] using hperAt
  have hrise : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ≤ 2 := by
    by_contra hnot
    have ht3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by omega
    have hdec := orbit_step_lt_of_c3 c ht3
    by_cases hi' : i + 1 < p
    · have hle := hmin (i + 1) hi'
      have hle' : fiveXPlusOneOrbit 7 c ≤
          fiveXPlusOneOrbit 7 (c + 1) := by
        simpa [c, Nat.add_assoc] using hle
      exact (not_lt_of_ge hle') hdec
    · have hip : i + 1 = p := by omega
      have hc1 : fiveXPlusOneOrbit 7 (c + 1) = fiveXPlusOneOrbit 7 c0 := by
        have hidx : c + 1 = c0 + p := by
          dsimp [c]
          omega
        rw [hidx, hper]
      have hle0 := hmin 0 (by omega)
      have hle0' : fiveXPlusOneOrbit 7 c ≤ fiveXPlusOneOrbit 7 c0 := by
        simpa [c] using hle0
      omega
  exact ⟨c, p, hp, hclosed, hrise⟩

/-- The same global-minimum rise-start construction, additionally
carrying the period-minimality property for every shifted index. -/
theorem orbit_cycle_imp_min_rise_start_min (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ≤ 2 ∧
      ∀ j : Nat, j < p →
        fiveXPlusOneOrbit 7 c ≤ fiveXPlusOneOrbit 7 (c + j) := by
  rcases orbit_cycle_imp_periodic_c3_segment h with ⟨c0, p, hp, hc3, hper⟩
  have hper' := periodic_shift c0 p hper
  rcases cycle_min_exists c0 p hp with ⟨i, hi, hmin⟩
  let c := c0 + i
  have hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c := by
    rw [cycleWord_orbit_eq c p]
    have hperAt : fiveXPlusOneOrbit 7 (c0 + i + p) =
        fiveXPlusOneOrbit 7 (c0 + i) := hper' i
    simpa [c] using hperAt
  have hrise : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ≤ 2 := by
    by_contra hnot
    have ht3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by omega
    have hdec := orbit_step_lt_of_c3 c ht3
    by_cases hi' : i + 1 < p
    · have hle := hmin (i + 1) hi'
      have hle' : fiveXPlusOneOrbit 7 c ≤
          fiveXPlusOneOrbit 7 (c + 1) := by
        simpa [c, Nat.add_assoc] using hle
      exact (not_lt_of_ge hle') hdec
    · have hip : i + 1 = p := by omega
      have hc1 : fiveXPlusOneOrbit 7 (c + 1) = fiveXPlusOneOrbit 7 c0 := by
        have hidx : c + 1 = c0 + p := by
          dsimp [c]
          omega
        rw [hidx, hper]
      have hle0 := hmin 0 (by omega)
      have hle0' : fiveXPlusOneOrbit 7 c ≤ fiveXPlusOneOrbit 7 c0 := by
        simpa [c] using hle0
      omega
  have hglobal : ∀ j : Nat, j < p →
      fiveXPlusOneOrbit 7 c ≤ fiveXPlusOneOrbit 7 (c + j) := by
    intro j hj
    let r := (i + j) % p
    let k := (i + j) / p
    have hr : r < p := Nat.mod_lt (i + j) hp
    have hminr := hmin r hr
    have hdecomp : i + j = k * p + r := by
      simpa [k, r, Nat.mul_comm] using
        (Nat.div_add_mod (i + j) p).symm
    have hper_mul := periodic_shift_mul c0 p hper k r
    have hstate : fiveXPlusOneOrbit 7 (c + j) =
        fiveXPlusOneOrbit 7 (c0 + r) := by
      dsimp [c]
      have hidx : c0 + i + j = c0 + r + k * p := by
        nlinarith [hdecomp]
      rw [hidx, hper_mul]
    rw [hstate]
    exact hminr
  exact ⟨c, p, hp, hclosed, hrise, hglobal⟩

/-- A rise start in the exact orbit satisfies the `j=1`, `k=0`,
`δ=1` reset-head equation for the next accelerated state. -/
theorem orbit_reset_head_eq_of_rise_start (c : Nat)
    (hrise : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ≤ 2) :
    S6Audit.ResetHeadEq (fiveXPlusOneOrbit 7 c) 1 0
      (twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)) 1
      (fiveXPlusOneOrbit 7 (c + 1)) := by
  have hge1 : 1 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :=
    twoValuation_five_mul_add_one_ge_one (fiveXPlusOneOrbit 7 c)
      (fiveXPlusOneOrbit_odd_7 c)
  have ht : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) = 1 ∨
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) = 2 := by omega
  have hmul := fiveXPlusOneStep_mul_eq (fiveXPlusOneOrbit 7 c)
  have hy : fiveXPlusOneOrbit 7 (c + 1) =
      fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := by
    rw [show c + 1 = Nat.succ c by omega]
    simp [fiveXPlusOneOrbit]
  have hmul' : 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) *
      fiveXPlusOneOrbit 7 (c + 1) = 5 * fiveXPlusOneOrbit 7 c + 1 := by
    rw [hy]
    exact hmul
  unfold S6Audit.ResetHeadEq
  rcases ht with ht1 | ht2
  · rw [ht1] at hmul' ⊢
    left
    refine ⟨rfl, rfl, ?_⟩
    norm_num at hmul' ⊢
    omega
  · rw [ht2] at hmul' ⊢
    right
    refine ⟨rfl, Or.inl rfl, ?_⟩
    norm_num at hmul' ⊢
    omega

/-- Every exact one-step rise equation `2^t*rj = 5*q+1` gives the
local reset-head equation with depth `j=1`, `k=0`, `δ=1`, and previous
terminal odd part `s=q`.  The block suffix is handled separately. -/
theorem reset_head_eq_of_rise_step (q t rj : Nat)
    (ht : t = 1 ∨ t = 2)
    (hstep : 2 ^ t * rj = 5 * q + 1) :
    S6Audit.ResetHeadEq q 1 0 t 1 rj := by
  unfold S6Audit.ResetHeadEq
  rcases ht with rfl | rfl
  · left
    refine ⟨rfl, rfl, ?_⟩
    norm_num at hstep ⊢
    omega
  · right
    refine ⟨rfl, Or.inl rfl, ?_⟩
    norm_num at hstep ⊢
    omega

/-- A positive cycle supplies a rise start whose state is odd,
not divisible by `5`, and satisfies the `j=1` reset-head equation. -/
theorem orbit_cycle_imp_min_rise_witness (h : OrbitCycle 7) :
    ∃ c, S6Audit.IsOdd (fiveXPlusOneOrbit 7 c) ∧
      ¬ 5 ∣ fiveXPlusOneOrbit 7 c ∧
      S6Audit.ResetHeadEq (fiveXPlusOneOrbit 7 c) 1 0
        (twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)) 1
        (fiveXPlusOneOrbit 7 (c + 1)) := by
  rcases orbit_cycle_imp_min_rise_start h with ⟨c, _p, _hp, _hclosed, hrise⟩
  exact ⟨c, fiveXPlusOneOrbit_odd_7 c, fiveXPlusOneOrbit_not_dvd_five c,
    orbit_reset_head_eq_of_rise_start c hrise⟩

/-- The `i`-th step weight of the cycle word is in the word. -/
theorem cycleWord_mem_at (c p i : Nat) (hi : i < p) :
    twoValuation (5 * fiveXPlusOneOrbit 7 (c + i) + 1) ∈ cycleWord c p := by
  induction i generalizing c p with
  | zero =>
      cases p with
      | zero => omega
      | succ p =>
          simp [cycleWord]
  | succ i ih =>
      cases p with
      | zero => omega
      | succ p =>
          have hi' : i < p := by omega
          have h := ih (c + 1) p hi'
          have h' : twoValuation (5 * fiveXPlusOneOrbit 7 (c + (i + 1)) + 1) ∈
              cycleWord (c + 1) p := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          right
          exact h'

/-- Consecutive `t=2` run: `t2Run r n` is the state after `n` exact
`t=2` steps from `r`. -/
def t2Run : Nat → Nat → Nat
  | r, 0 => r
  | r, n + 1 => t2Run ((5 * r + 1) / 4) n

/-- A single exact `t=2` step is possible only from `v2(r+1) >= 2`,
and it drops `v2(r+1)` by exactly two. -/
theorem t2Step_valuation_drop (r : Nat)
    (hvalid : twoValuation (5 * r + 1) = 2) :
    2 ≤ twoValuation (r + 1) ∧
    twoValuation (((5 * r + 1) / 4) + 1) = twoValuation (r + 1) - 2 := by
  have hpos5 : 0 < 5 * r + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * r + 1) hpos5
  rw [hvalid] at hdec
  have hodd : StringFlow.oddPart (5 * r + 1) % 2 = 1 :=
    StringFlow.oddPart_odd_of_pos (5 * r + 1) hpos5
  have hq : (5 * r + 1) / 4 = StringFlow.oddPart (5 * r + 1) := by
    conv_lhs => rw [hdec]
    rw [show (2 ^ 2 : Nat) = 4 by norm_num]
    exact Nat.mul_div_cancel_left (StringFlow.oddPart (5 * r + 1))
      (by decide : 0 < 4)
  have hrel : 5 * (r + 1) =
      4 * (((5 * r + 1) / 4) + 1) := by
    have hdec' : 5 * r + 1 = 4 * StringFlow.oddPart (5 * r + 1) := by
      simpa [show (2 ^ 2 : Nat) = 4 by norm_num] using hdec
    calc
      5 * (r + 1) = 5 * r + 5 := by ring
      _ = (5 * r + 1) + 4 := by omega
      _ = 4 * StringFlow.oddPart (5 * r + 1) + 4 := by
        conv_lhs => rw [hdec']
      _ = 4 * (StringFlow.oddPart (5 * r + 1) + 1) := by ring
      _ = 4 * (((5 * r + 1) / 4) + 1) := by rw [hq]
  have hposx : 0 < ((5 * r + 1) / 4) + 1 := by positivity
  have hv := StringFlow.Lte.twoValuation_mul_two_pow 2
    (((5 * r + 1) / 4) + 1) hposx
  have hleft : twoValuation (5 * (r + 1)) =
      twoValuation (((5 * r + 1) / 4) + 1) + 2 := by
    rw [hrel]
    simpa [show (4 : Nat) = 2 ^ 2 by norm_num, Nat.add_comm] using hv
  have hposr1 : 0 < r + 1 := by positivity
  have h5mul := StringFlow.Lte.twoValuation_mul_odd 5 (r + 1)
    (by decide : 5 % 2 = 1) hposr1
  have hmain : twoValuation (((5 * r + 1) / 4) + 1) + 2 =
      twoValuation (r + 1) := by
    rw [← h5mul]
    exact hleft.symm
  constructor <;> omega

/-- A run of `n` exact `t=2` steps consumes `2n` of the initial
valuation: `2*n <= v2(r+1)`. -/
theorem pure_t2_balance (r n : Nat)
    (hsteps : ∀ i, i < n → twoValuation (5 * t2Run r i + 1) = 2) :
    2 * n ≤ twoValuation (r + 1) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
      have hfirst : twoValuation (5 * r + 1) = 2 := by
        have := hsteps 0 (by omega)
        simpa [t2Run] using this
      have hdrop := t2Step_valuation_drop r hfirst
      have hge2 : 2 ≤ twoValuation (r + 1) := hdrop.1
      have htail : 2 * n ≤ twoValuation (((5 * r + 1) / 4) + 1) := by
        apply ih
        intro i hi
        have h := hsteps (i + 1) (by omega)
        simpa [t2Run] using h
      have hle : 2 * n + 2 ≤ twoValuation (r + 1) := by
        have h := htail
        rw [hdrop.2] at h
        omega
      omega

/-- If a pure `t=2` block head avoids the failure window, its length
is capped by `j + 4`. -/
theorem pure_t2_block_capacity (r j L : Nat)
    (hsteps : ∀ i, i < L → twoValuation (5 * t2Run r i + 1) = 2)
    (hwin : twoValuation (r + 1) ≤ 2 * j + 8) :
    L ≤ j + 4 := by
  have hbal := pure_t2_balance r L hsteps
  omega

/-- One exact rise step (`t=1` or `t=2`) of the accelerated map. -/
def riseStep (r t : Nat) : Nat :=
  (5 * r + 1) / 2 ^ t

/-- Run a rise word from a block head. -/
def riseRun : Nat → List Nat → Nat
  | r, [] => r
  | r, t :: ts => riseRun (riseStep r t) ts

/-- `riseRun` is the same recurrence as `Word.wordOrbit`. -/
theorem riseRun_eq_wordOrbit (r : Nat) (ts : List Nat) :
    riseRun r ts = StringFlow.Word.wordOrbit ts r := by
  induction ts generalizing r with
  | nil => rfl
  | cons t ts ih =>
      simp [riseRun, StringFlow.Word.wordOrbit, riseStep]
      exact ih (riseStep r t)

/-- Number of `t=2` steps in a rise word. -/
def riseCountTwo : List Nat → Nat
  | [] => 0
  | t :: ts => (if t = 2 then 1 else 0) + riseCountTwo ts

/-- Recharge contributed by one rise step: the positive part of the
change in `v2(r+1)`; a `t=2` step contributes zero. -/
def riseCharge (r t : Nat) : Nat :=
  if t = 2 then 0 else
    Nat.max (twoValuation (riseStep r t + 1) - twoValuation (r + 1)) 0

/-- Total recharge along a rise word. -/
def riseChargeSum (r : Nat) : List Nat → Nat
  | [] => 0
  | t :: ts => riseCharge r t + riseChargeSum (riseStep r t) ts

/-- Rise-block balance: `t=2` steps consume `2` units of `v2(r+1)`
each, and `t=1` steps can only recharge by their positive valuation
increase. -/
theorem rise_block_balance (r0 : Nat) (ts : List Nat)
    (hok : ∀ t ∈ ts, t = 1 ∨ t = 2)
    (hexact : ∀ k, k < ts.length →
      twoValuation (5 * riseRun r0 (ts.take k) + 1) = ts.getI k) :
    2 * riseCountTwo ts ≤
      twoValuation (r0 + 1) + riseChargeSum r0 ts := by
  induction ts generalizing r0 with
  | nil => simp [riseCountTwo, riseChargeSum]
  | cons t ts ih =>
      rcases hok t (by simp) with ht1 | ht2
      · subst t
        let r1 := riseStep r0 1
        have htail := ih r1 (fun t ht => hok t (by simp [ht]))
        have htailExact : ∀ k, k < ts.length →
            twoValuation (5 * riseRun r1 (ts.take k) + 1) = ts.getI k := by
          intro k hk
          have hk' : k + 1 < (1 :: ts).length := by
            simp [hk]
          have h := hexact (k + 1) hk'
          have hrun : riseRun r0 ((1 :: ts).take (k + 1)) =
              riseRun r1 (ts.take k) := by
            have htake : (1 :: ts).take (k + 1) = 1 :: ts.take k :=
              List.take_cons (by omega)
            rw [htake]
            rfl
          have hidx : (1 :: ts).getI (k + 1) = ts.getI k := by
            rw [List.getI_cons_succ]
          rwa [hrun, hidx] at h
        have hbal := htail htailExact
        have hcharge_ge : twoValuation (r1 + 1) - twoValuation (r0 + 1) ≤
            riseCharge r0 1 := by
          unfold riseCharge
          simp [r1]
        have hle1 : twoValuation (r1 + 1) ≤
            twoValuation (r0 + 1) + riseCharge r0 1 := by
          omega
        have hsum : riseChargeSum r0 (1 :: ts) =
            riseCharge r0 1 + riseChargeSum r1 ts := rfl
        change 2 * (0 + riseCountTwo ts) ≤
          twoValuation (r0 + 1) + riseChargeSum r0 (1 :: ts)
        calc
          2 * (0 + riseCountTwo ts) = 2 * riseCountTwo ts := by simp
          _ ≤ twoValuation (r1 + 1) + riseChargeSum r1 ts := hbal
          _ ≤ twoValuation (r0 + 1) + riseCharge r0 1 +
                riseChargeSum r1 ts := by omega
          _ = twoValuation (r0 + 1) + riseChargeSum r0 (1 :: ts) := by
              rw [hsum]
              omega
      · subst t
        let r1 := riseStep r0 2
        have htail := ih r1 (fun t ht => hok t (by simp [ht]))
        have htailExact : ∀ k, k < ts.length →
            twoValuation (5 * riseRun r1 (ts.take k) + 1) = ts.getI k := by
          intro k hk
          have hk' : k + 1 < (2 :: ts).length := by
            simp [hk]
          have h := hexact (k + 1) hk'
          have hrun : riseRun r0 ((2 :: ts).take (k + 1)) =
              riseRun r1 (ts.take k) := by
            have htake : (2 :: ts).take (k + 1) = 2 :: ts.take k :=
              List.take_cons (by omega)
            rw [htake]
            rfl
          have hidx : (2 :: ts).getI (k + 1) = ts.getI k := by
            rw [List.getI_cons_succ]
          rwa [hrun, hidx] at h
        have hbal := htail htailExact
        have hfirst : twoValuation (5 * r0 + 1) = 2 := by
          have h0 : twoValuation (5 * riseRun r0 ([] : List Nat) + 1) =
              (2 :: ts).getI 0 := hexact 0 (by simp)
          simpa [riseRun, riseStep] using h0
        have hdrop := t2Step_valuation_drop r0 hfirst
        have hdrop' : twoValuation (r1 + 1) + 2 =
            twoValuation (r0 + 1) := by
          have h := hdrop.2
          dsimp [r1, riseStep] at h ⊢
          omega
        have hcharge : riseCharge r0 2 = 0 := by
          unfold riseCharge
          simp
        have hsum : riseChargeSum r0 (2 :: ts) =
            riseChargeSum r1 ts := by
          dsimp [r1]
          rw [riseChargeSum, hcharge]
          simp
        change 2 * (1 + riseCountTwo ts) ≤
          twoValuation (r0 + 1) + riseChargeSum r0 (2 :: ts)
        calc
          2 * (1 + riseCountTwo ts) = 2 + 2 * riseCountTwo ts := by ring
          _ ≤ 2 + (twoValuation (r1 + 1) + riseChargeSum r1 ts) := by omega
          _ = twoValuation (r0 + 1) + riseChargeSum r1 ts := by omega
          _ = twoValuation (r0 + 1) + riseChargeSum r0 (2 :: ts) := by
            rw [hsum]

/-- Endpoint rank upper bound along a rise word.  Every `t=2` step
consumes exactly two units, while the recorded charge covers every
positive `t=1` rank increase.  Negative `t=1` changes are discarded, so
the endpoint side is bounded above by `v2(r0+1)+F`. -/
theorem rise_endpoint_rank_le (r0 : Nat) (ts : List Nat)
    (hok : ∀ t ∈ ts, t = 1 ∨ t = 2)
    (hexact : ∀ k, k < ts.length →
      twoValuation (5 * riseRun r0 (ts.take k) + 1) = ts.getI k) :
    twoValuation (riseRun r0 ts + 1) + 2 * riseCountTwo ts ≤
      twoValuation (r0 + 1) + riseChargeSum r0 ts := by
  induction ts generalizing r0 with
  | nil => simp [riseRun, riseCountTwo, riseChargeSum]
  | cons t ts ih =>
      rcases hok t (by simp) with ht1 | ht2
      · subst t
        let r1 := riseStep r0 1
        have htail := ih r1 (fun t ht => hok t (by simp [ht]))
        have htailExact : ∀ k, k < ts.length →
            twoValuation (5 * riseRun r1 (ts.take k) + 1) = ts.getI k := by
          intro k hk
          have hk' : k + 1 < (1 :: ts).length := by simp [hk]
          have h := hexact (k + 1) hk'
          have hrun : riseRun r0 ((1 :: ts).take (k + 1)) =
              riseRun r1 (ts.take k) := by
            rw [List.take_cons (by omega)]
            rfl
          have hidx : (1 :: ts).getI (k + 1) = ts.getI k := by
            rw [List.getI_cons_succ]
          rwa [hrun, hidx] at h
        have hcharge_ge : twoValuation (r1 + 1) ≤
            twoValuation (r0 + 1) + riseCharge r0 1 := by
          unfold riseCharge
          simp [r1]
          omega
        have hsum : riseChargeSum r0 (1 :: ts) =
            riseCharge r0 1 + riseChargeSum r1 ts := rfl
        change twoValuation (riseRun r0 (1 :: ts) + 1) +
            2 * (0 + riseCountTwo ts) ≤
          twoValuation (r0 + 1) + riseChargeSum r0 (1 :: ts)
        calc
          twoValuation (riseRun r0 (1 :: ts) + 1) +
              2 * (0 + riseCountTwo ts) =
              twoValuation (riseRun r1 ts + 1) + 2 * riseCountTwo ts := by
            simp [r1, riseRun, riseStep]
          _ ≤ twoValuation (r1 + 1) + riseChargeSum r1 ts := htail htailExact
          _ ≤ twoValuation (r0 + 1) + riseCharge r0 1 +
                riseChargeSum r1 ts := by omega
          _ = twoValuation (r0 + 1) + riseChargeSum r0 (1 :: ts) := by
            rw [hsum]
            omega
      · subst t
        let r1 := riseStep r0 2
        have htail := ih r1 (fun t ht => hok t (by simp [ht]))
        have htailExact : ∀ k, k < ts.length →
            twoValuation (5 * riseRun r1 (ts.take k) + 1) = ts.getI k := by
          intro k hk
          have hk' : k + 1 < (2 :: ts).length := by simp [hk]
          have h := hexact (k + 1) hk'
          have hrun : riseRun r0 ((2 :: ts).take (k + 1)) =
              riseRun r1 (ts.take k) := by
            rw [List.take_cons (by omega)]
            rfl
          have hidx : (2 :: ts).getI (k + 1) = ts.getI k := by
            rw [List.getI_cons_succ]
          rwa [hrun, hidx] at h
        have hfirst : twoValuation (5 * r0 + 1) = 2 := by
          have h0 := hexact 0 (by simp)
          simpa [riseRun] using h0
        have hdrop := t2Step_valuation_drop r0 hfirst
        have hdrop' : twoValuation (r1 + 1) + 2 =
            twoValuation (r0 + 1) := by
          dsimp [r1, riseStep] at hdrop ⊢
          omega
        have hcharge : riseCharge r0 2 = 0 := by
          unfold riseCharge
          simp
        have hsum : riseChargeSum r0 (2 :: ts) =
            riseChargeSum r1 ts := by
          dsimp [r1]
          rw [riseChargeSum, hcharge]
          simp
        have hbal2 := htail htailExact
        change twoValuation (riseRun r0 (2 :: ts) + 1) +
            2 * (1 + riseCountTwo ts) ≤
          twoValuation (r0 + 1) + riseChargeSum r0 (2 :: ts)
        calc
          twoValuation (riseRun r0 (2 :: ts) + 1) +
              2 * (1 + riseCountTwo ts) =
              (twoValuation (riseRun r1 ts + 1) + 2 * riseCountTwo ts) + 2 := by
            simp [r1, riseRun, riseStep]
            ring
          _ ≤ (twoValuation (r1 + 1) + riseChargeSum r1 ts) + 2 := by
            omega
          _ = twoValuation (r0 + 1) + riseChargeSum r1 ts := by omega
          _ = twoValuation (r0 + 1) + riseChargeSum r0 (2 :: ts) := by
            rw [hsum]

/-- If a block's local balance, window-avoidance bound, and explicit
charge budget all hold, then its `t=2` count satisfies the capacity
bound `H2 ≤ j-t+6`. -/
theorem block_capacity_of_charge_bound
    (j t u F H2 : Nat)
    (hbal : 2 * H2 ≤ u + F)
    (hwindow : u ≤ 2 * (j - t) + 12)
    (hcharge : F ≤ 2 * (j - t) + 12 - u) :
    H2 ≤ j - t + 6 := by
  have hsum : u + F ≤ 2 * (j - t) + 12 := by omega
  have htwo : 2 * H2 ≤ 2 * (j - t) + 12 := le_trans hbal hsum
  omega

/-- Number of C3 steps (`t >= 3`) in the cycle word. -/
def cycleWordC3Count (c p : Nat) : Nat :=
  ((cycleWord c p).filter (fun t => decide (3 ≤ t))).length

/-- A nonempty cycle word with a C3 head has at least one C3 step. -/
theorem cycleWordC3Count_pos (c p : Nat) (hp : 1 ≤ p)
    (hc3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)) :
    1 ≤ cycleWordC3Count c p := by
  unfold cycleWordC3Count
  have hhead := cycleWord_head_eq c p hp
  have hmem : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ∈
      cycleWord c p := by
    rw [hhead]
    simp
  have hfilter : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ∈
      (cycleWord c p).filter (fun t => decide (3 ≤ t)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hc3]⟩
  exact List.length_pos_of_mem hfilter

/-- A closed period word cannot consist only of rise steps: otherwise
every step strictly increases and the period could not return to its
starting state. -/
theorem cycleWordC3Count_pos_of_rise_closed (c p : Nat) (hp : 1 ≤ p)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p)
        (fiveXPlusOneOrbit 7 c) = fiveXPlusOneOrbit 7 c) :
    1 ≤ cycleWordC3Count c p := by
  by_contra hnot
  have hcount0 : cycleWordC3Count c p = 0 := by omega
  unfold cycleWordC3Count at hcount0
  have hfilter_empty :
      (cycleWord c p).filter (fun t => decide (3 ≤ t)) = [] := by
    exact List.eq_nil_of_length_eq_zero hcount0
  have hnone : ∀ t ∈ cycleWord c p, ¬ 3 ≤ t := by
    intro t ht h3
    have hmem : t ∈ (cycleWord c p).filter (fun t => decide (3 ≤ t)) := by
      rw [List.mem_filter]
      exact ⟨ht, by simp [h3]⟩
    rw [hfilter_empty] at hmem
    simpa using hmem
  have hstep_le : ∀ k, k < p →
      twoValuation (5 * fiveXPlusOneOrbit 7 (c + k) + 1) ≤ 2 := by
    intro k hk
    have htmem : twoValuation (5 * fiveXPlusOneOrbit 7 (c + k) + 1) ∈
        cycleWord c p := cycleWord_mem_at c p k hk
    have hge : 1 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 (c + k) + 1) :=
      twoValuation_five_mul_add_one_ge_one (fiveXPlusOneOrbit 7 (c + k))
        (fiveXPlusOneOrbit_odd_7 (c + k))
    have hnot3 := hnone
      (twoValuation (5 * fiveXPlusOneOrbit 7 (c + k) + 1)) htmem
    omega
  have hstep_gt : ∀ k, k < p →
      fiveXPlusOneOrbit 7 (c + k) < fiveXPlusOneOrbit 7 (c + (k + 1)) := by
    intro k hk
    have ht := hstep_le k hk
    have hgt := fiveXPlusOneStep_gt_of_weight_le_two
      (fiveXPlusOneOrbit 7 (c + k)) (fiveXPlusOneOrbit_pos_7 (c + k)) ht
    have hsucc : fiveXPlusOneOrbit 7 (c + (k + 1)) =
        fiveXPlusOneStep (fiveXPlusOneOrbit 7 (c + k)) := by
      rw [show c + (k + 1) = (c + k) + 1 by omega]
      simp [fiveXPlusOneOrbit]
    rwa [hsucc]
  have hchain : ∀ k, 1 ≤ k → k ≤ p →
      fiveXPlusOneOrbit 7 c < fiveXPlusOneOrbit 7 (c + k) := by
    intro k hk1 hkp
    induction k with
    | zero => omega
    | succ k ih =>
        cases k with
        | zero =>
            have h := hstep_gt 0 (by omega)
            simpa using h
        | succ k =>
            have hltprev : fiveXPlusOneOrbit 7 c <
                fiveXPlusOneOrbit 7 (c + (k + 1)) :=
              ih (by omega) (by omega)
            have hstep : fiveXPlusOneOrbit 7 (c + (k + 1)) <
                fiveXPlusOneOrbit 7 (c + ((k + 1) + 1)) := by
              exact hstep_gt (k + 1) (by omega)
            have hidx : c + (k + 2) = c + ((k + 1) + 1) := by omega
            simpa [hidx] using lt_trans hltprev hstep
  have hltcycle : fiveXPlusOneOrbit 7 c < fiveXPlusOneOrbit 7 (c + p) :=
    hchain p hp (by omega)
  have hclosed' : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c := by
    rw [← cycleWord_orbit_eq c p]
    exact hclosed
  exact (ne_of_lt hltcycle) hclosed'.symm

/-- Total word weight splits into rise weight (`t < 3`) plus C3 weight
(`t >= 3`). -/
theorem wordWeight_filter_lt_ge_split (w : List Nat) :
    StringFlow.wordWeight w =
      StringFlow.wordWeight (w.filter (fun t => decide (t < 3))) +
      StringFlow.wordWeight (w.filter (fun t => decide (3 ≤ t))) := by
  induction w with
  | nil => simp [StringFlow.wordWeight]
  | cons a as ih =>
      by_cases h : a < 3
      · have h3 : ¬ 3 ≤ a := by omega
        simp [StringFlow.wordWeight, h, h3, ih]
        omega
      · have h3 : 3 ≤ a := by omega
        simp [StringFlow.wordWeight, h, h3, ih]
        omega

/-- Rise part of the cycle word: total weight of entries `t < 3`. -/
def cycleWordRiseWeight (c p : Nat) : Nat :=
  StringFlow.wordWeight ((cycleWord c p).filter (fun t => decide (t < 3)))

/-- C3 part of the cycle word: total weight of entries `t >= 3`. -/
def cycleWordC3Weight (c p : Nat) : Nat :=
  StringFlow.wordWeight ((cycleWord c p).filter (fun t => decide (3 ≤ t)))

/-- The cycle word total weight equals rise weight plus C3 weight. -/
theorem cycleWord_weight_decomp (c p : Nat) :
    StringFlow.wordWeight (cycleWord c p) =
      cycleWordRiseWeight c p + cycleWordC3Weight c p := by
  unfold cycleWordRiseWeight cycleWordC3Weight
  exact wordWeight_filter_lt_ge_split (cycleWord c p)

/-- Rise part of the cycle word: entries with `t < 3`. -/
def cycleWordRiseSteps (c p : Nat) : List Nat :=
  (cycleWord c p).filter (fun t => decide (t < 3))

/-- A closed cycle word has at least one rise step (`t < 3`). -/
theorem cycleWordRiseSteps_nonempty_of_closed (c p : Nat) (hp : 1 ≤ p)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) :
    cycleWordRiseSteps c p ≠ [] := by
  intro hnil
  have hall : ∀ t, t ∈ cycleWord c p → 3 ≤ t := by
    intro t ht
    by_contra hnot
    have h12 := cycleWord_non_c3_rise c p ht hnot
    have hmem : t ∈ cycleWordRiseSteps c p := by
      unfold cycleWordRiseSteps
      rw [List.mem_filter]
      exact ⟨ht, by
        rcases h12 with rfl | rfl <;> norm_num⟩
    rw [hnil] at hmem
    simp at hmem
  have hdecr : ∀ i, i < p →
      fiveXPlusOneOrbit 7 (c + i + 1) < fiveXPlusOneOrbit 7 (c + i) := by
    intro i hi
    have hmem := cycleWord_mem_at c p i hi
    have hge : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 (c + i) + 1) := hall _ hmem
    have hstep := orbit_step_lt_of_c3 (c + i) hge
    simpa [Nat.add_assoc] using hstep
  have hchain : ∀ k, 1 ≤ k → k ≤ p →
      fiveXPlusOneOrbit 7 (c + k) < fiveXPlusOneOrbit 7 c := by
    intro k hk1 hkp
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          have h0 := hdecr 0 (by omega)
          simpa using h0
        · have hk1' : 1 ≤ k := by omega
          have hlt := ih hk1' (by omega)
          have hstep := hdecr k (by omega)
          exact lt_trans hstep hlt
  have hltp : fiveXPlusOneOrbit 7 (c + p) < fiveXPlusOneOrbit 7 c :=
    hchain p hp (by omega)
  have horb_eq : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c := by
    rw [cycleWord_orbit_eq c p] at hclosed
    exact hclosed
  exact (ne_of_lt hltp) horb_eq

/-- C3 part of the cycle word: entries with `t >= 3`. -/
def cycleWordC3Steps (c p : Nat) : List Nat :=
  (cycleWord c p).filter (fun t => decide (3 ≤ t))

/-- Every C3 step extracted from the cycle word has weight at least
three. -/
theorem cycleWordC3Steps_mem_ge_three (c p : Nat) {t : Nat}
    (ht : t ∈ cycleWordC3Steps c p) :
    3 ≤ t := by
  unfold cycleWordC3Steps at ht
  rw [List.mem_filter] at ht
  exact of_decide_eq_true ht.2

/-- Every rise step extracted from the cycle word is `t = 1` or
`t = 2`. -/
theorem cycleWordRiseSteps_mem_one_two (c p : Nat) {t : Nat}
    (ht : t ∈ cycleWordRiseSteps c p) :
    t = 1 ∨ t = 2 := by
  unfold cycleWordRiseSteps at ht
  rw [List.mem_filter] at ht
  have hmem : t ∈ cycleWord c p := ht.1
  have htlt : t < 3 := of_decide_eq_true ht.2
  exact cycleWord_non_c3_rise c p hmem (by omega)

/-- Filtering a list by a complement pair splits its length. -/
theorem filter_length_add_filter_length (w : List Nat) :
    (w.filter (fun t => decide (t < 3))).length +
      (w.filter (fun t => decide (3 ≤ t))).length = w.length := by
  induction w with
  | nil => simp
  | cons a as ih =>
      by_cases h : a < 3
      · have h3 : ¬ 3 ≤ a := by omega
        simp [h, h3]
        omega
      · have h3 : 3 ≤ a := by omega
        simp [h, h3]
        omega

/-- Cycle word length splits into rise length plus C3 length. -/
theorem cycleWord_length_split (c p : Nat) :
    (cycleWordRiseSteps c p).length + (cycleWordC3Steps c p).length = p := by
  conv =>
    rhs
    rw [← cycleWord_length c p]
  unfold cycleWordRiseSteps cycleWordC3Steps
  exact filter_length_add_filter_length (cycleWord c p)

/-- The number of extracted C3 steps is the C3 count. -/
theorem cycleWordC3Steps_length (c p : Nat) :
    (cycleWordC3Steps c p).length = cycleWordC3Count c p := by
  unfold cycleWordC3Steps cycleWordC3Count
  rfl

/-- The number of C3 steps is at most the cycle length. -/
theorem cycleWordC3Count_le_length (c p : Nat) :
    cycleWordC3Count c p ≤ p := by
  unfold cycleWordC3Count
  conv =>
    rhs
    rw [← cycleWord_length c p]
  exact List.length_filter_le (fun t => decide (3 ≤ t)) (cycleWord c p)

/-- If every entry of a list is at least `c`, the total word weight is
at least `c * length`. -/
theorem wordWeight_ge_mul_length_of_ge (w : List Nat) (c : Nat)
    (hc : ∀ t ∈ w, c ≤ t) :
    c * w.length ≤ StringFlow.wordWeight w := by
  induction w with
  | nil => simp [StringFlow.wordWeight]
  | cons a as ih =>
      simp [StringFlow.wordWeight, Nat.mul_succ]
      have hca : c ≤ a := hc a (by simp)
      have htail : c * as.length ≤ StringFlow.wordWeight as :=
        ih (fun t ht => hc t (by simp [ht]))
      omega

/-- The C3 part of the cycle word has weight at least `3 * Q`. -/
theorem cycleWordC3Weight_ge_three_mul_count (c p : Nat) :
    3 * (cycleWordC3Steps c p).length ≤ cycleWordC3Weight c p := by
  unfold cycleWordC3Weight cycleWordC3Steps
  exact wordWeight_ge_mul_length_of_ge
    ((cycleWord c p).filter (fun t => decide (3 ≤ t))) 3
    (fun t ht => by
      rw [List.mem_filter] at ht
      exact of_decide_eq_true ht.2)

/-- The rising equation for the cycle word:
`2^S * orbit(c+p) = 5^p * orbit c + A`, where `S` is the word weight
and `A` is the word numerator. -/
theorem cycleWord_rising_equation (c p : Nat) :
    2 ^ StringFlow.wordWeight (cycleWord c p) * fiveXPlusOneOrbit 7 (c + p) =
      5 ^ p * fiveXPlusOneOrbit 7 c + StringFlow.Word.wordA (cycleWord c p) := by
  induction p generalizing c with
  | zero =>
      simp [cycleWord, StringFlow.wordWeight, StringFlow.Word.wordA]
  | succ p ih =>
      unfold cycleWord
      let t := twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)
      let tail := cycleWord (c + 1) p
      have hstep : (5 * fiveXPlusOneOrbit 7 c + 1) / 2 ^ t =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := by
        dsimp [t]
        rfl
      have horb : fiveXPlusOneOrbit 7 (c + 1) =
          fiveXPlusOneStep (fiveXPlusOneOrbit 7 c) := by
        rw [show c + 1 = Nat.succ c by omega]
        simp [fiveXPlusOneOrbit]
      have hpow_pos : 0 < 2 ^ t := Nat.pow_pos (by decide : 0 < 2)
      have hpos5 : 0 < 5 * fiveXPlusOneOrbit 7 c + 1 := by positivity
      have hdec0 := StringFlow.n_eq_two_pow_mul_oddPart
        (5 * fiveXPlusOneOrbit 7 c + 1) hpos5
      have hdec : 5 * fiveXPlusOneOrbit 7 c + 1 =
          2 ^ t * StringFlow.oddPart (5 * fiveXPlusOneOrbit 7 c + 1) := by
        have ht_def : twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) = t := rfl
        rw [ht_def] at hdec0
        exact hdec0
      have hq : (5 * fiveXPlusOneOrbit 7 c + 1) / 2 ^ t =
          StringFlow.oddPart (5 * fiveXPlusOneOrbit 7 c + 1) := by
        conv_lhs => rw [hdec]
        exact Nat.mul_div_cancel_left
          (StringFlow.oddPart (5 * fiveXPlusOneOrbit 7 c + 1)) hpow_pos
      have horb_odd : fiveXPlusOneOrbit 7 (c + 1) =
          StringFlow.oddPart (5 * fiveXPlusOneOrbit 7 c + 1) := by
        rw [horb, ← hstep, hq]
      have ht_mul : 2 ^ t * fiveXPlusOneOrbit 7 (c + 1) =
          5 * fiveXPlusOneOrbit 7 c + 1 := by
        rw [horb_odd]
        exact hdec.symm
      have hih := ih (c + 1)
      have hindex : c + (p + 1) = (c + 1) + p := by omega
      rw [hindex]
      simp [StringFlow.wordWeight, StringFlow.Word.wordA, cycleWord_length]
      calc
        2 ^ (t + StringFlow.wordWeight (cycleWord (c + 1) p)) *
            fiveXPlusOneOrbit 7 (c + 1 + p)
            = 2 ^ t * (2 ^ StringFlow.wordWeight (cycleWord (c + 1) p) *
                fiveXPlusOneOrbit 7 (c + 1 + p)) := by
              rw [Nat.pow_add]
              ring
        _ = 2 ^ t * (5 ^ p * fiveXPlusOneOrbit 7 (c + 1) +
              StringFlow.Word.wordA (cycleWord (c + 1) p)) := by
              rw [hih]
        _ = 5 ^ (p + 1) * fiveXPlusOneOrbit 7 c +
              (5 ^ p + 2 ^ t * StringFlow.Word.wordA (cycleWord (c + 1) p)) := by
              rw [Nat.mul_add]
              have hterm : 2 ^ t * (5 ^ p * fiveXPlusOneOrbit 7 (c + 1)) =
                  5 ^ p * (2 ^ t * fiveXPlusOneOrbit 7 (c + 1)) := by ring
              rw [hterm, ht_mul]
              ring_nf

/-- A closed cycle word satisfies the exact Diophantine cycle
equation `2^S * m = 5^p * m + A`. -/
theorem cycleWord_cycle_equation (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) :
    2 ^ StringFlow.wordWeight (cycleWord c p) * fiveXPlusOneOrbit 7 c =
      5 ^ p * fiveXPlusOneOrbit 7 c + StringFlow.Word.wordA (cycleWord c p) := by
  have h := cycleWord_rising_equation c p
  have hstep : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c := by
    rw [← cycleWord_orbit_eq c p]
    exact hclosed
  rwa [hstep] at h

/-- The word numerator is the list-form PMI numerator. -/
theorem cycleWord_wordA_eq_pmi_aTotal (c p : Nat) :
    StringFlow.Word.wordA (cycleWord c p) =
      StringFlow.PMI.aTotal p (cycleWordStepAt c p) := by
  rw [StringFlow.SurvEx.wordA_eq_localLambda]
  have h := StringFlow.PH.localLambda_eq_pmi_aTotal (cycleWord c p)
  change StringFlow.PH.localLambda (cycleWord c p) =
      StringFlow.PMI.aTotal p (fun j => (cycleWord c p).getI j)
  simpa [cycleWord_length c p] using h

/-- The exact cycle equation in PMI `aTotal` form. -/
theorem cycleWord_pmi_cycle_equation (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) :
    2 ^ cycleWordTotalWeight c p * fiveXPlusOneOrbit 7 c =
      5 ^ p * fiveXPlusOneOrbit 7 c +
        StringFlow.PMI.aTotal p (cycleWordStepAt c p) := by
  have hcycle := cycleWord_cycle_equation c p hclosed
  have hA := cycleWord_wordA_eq_pmi_aTotal c p
  rw [hA] at hcycle
  simpa [cycleWordTotalWeight] using hcycle

/-- PMI for the closed cycle word:
`aTotal5 = 5 * m * (2^S - 5^P)`. -/
theorem cycleWord_pmi_algebraic (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) :
    StringFlow.PMI.aTotal5 p (cycleWordStepAt c p) =
      5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) := by
  have hcycle := cycleWord_pmi_cycle_equation c p hclosed
  have hpm := StringFlow.PMI.pmi_algebraic p (cycleWordStepAt c p)
    (fiveXPlusOneOrbit 7 c) (cycleWordTotalWeight c p) hcycle
  simpa [cycleWordStepAt, cycleWordTotalWeight] using hpm

/-- PMI-B counting bound for the closed cycle word. -/
theorem cycleWord_pmi_b_count (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) :
    5 ^ p + StringFlow.PMI.badCount p (cycleWordStepAt c p) * 5 ^ p ≤
      5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) := by
  have hcycle := cycleWord_pmi_cycle_equation c p hclosed
  exact StringFlow.PMI.pmi_b_count p (cycleWordStepAt c p)
    (fiveXPlusOneOrbit 7 c) (cycleWordTotalWeight c p) hp hcycle

/-- PMI-B corollary for the closed cycle word: under the small-budget
hypothesis every proper prefix has `2^(W_j) < 5^j`. -/
theorem cycleWord_pmi_b_no_bad_prefix (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    ∀ j, 1 ≤ j → j < p →
      2 ^ StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j < 5 ^ j := by
  have hcycle := cycleWord_pmi_cycle_equation c p hclosed
  exact StringFlow.PMI.pmi_b_no_bad_prefix p (cycleWordStepAt c p)
    (fiveXPlusOneOrbit 7 c) (cycleWordTotalWeight c p) hp hcycle hbudget

/-- A small-budget closed cycle word satisfies the margin-balance
necessary condition on every proper prefix. -/
theorem cycleWord_margin_balance (c p j : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    (3 - StringFlow.TD0.log2Real 5) *
        (StringFlow.TD0.countAtLeastThree ((cycleWord c p).take j) : Real) ≤
      (StringFlow.TD0.log2Real 5 - 1) *
        (StringFlow.TD0.countOne ((cycleWord c p).take j) : Real) +
        (StringFlow.TD0.log2Real 5 - 2) *
          (StringFlow.TD0.countTwo ((cycleWord c p).take j) : Real) := by
  let w := (cycleWord c p).take j
  have hpref := cycleWord_pmi_b_no_bad_prefix c p hclosed hp hbudget j hj1 hjp
  have hW := StringFlow.TD0.log2_of_pow_lt_pow
      (StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j) j hpref
  have hpos_w : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    have ht' : t ∈ cycleWord c p := mem_take_imp_mem (cycleWord c p) ht
    exact cycleWord_mem_ge_one c p ht'
  have hcounts : (StringFlow.TD0.countOne w +
        2 * StringFlow.TD0.countTwo w +
        3 * StringFlow.TD0.countAtLeastThree w : Real) ≤
      (StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j : Real) := by
    have hc := StringFlow.TD0.counts_weight_le w
    rw [← cycleWord_prefixWeight_eq_wordWeight_take] at hc
    exact_mod_cast hc
  have hW' : (StringFlow.TD0.countOne w +
        2 * StringFlow.TD0.countTwo w +
        3 * StringFlow.TD0.countAtLeastThree w : Real) ≤
      (j : Real) * StringFlow.TD0.log2Real 5 := by
    nlinarith [hW, hcounts]
  have hsum : StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w = j := by
    have hsum' := StringFlow.TD0.count_sum_length w hpos_w
    have hlen : w.length = j := by
      unfold w
      rw [List.length_take]
      have hjp_le : j ≤ p := by omega
      have hlen' : (cycleWord c p).length = p := cycleWord_length c p
      rw [hlen']
      exact Nat.min_eq_left hjp_le
    rw [hlen] at hsum'
    exact hsum'
  have hsumR : (StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w : Real) = (j : Real) := by
    exact_mod_cast hsum
  have hh : (StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w : Real) *
      StringFlow.TD0.log2Real 5 ≥
    StringFlow.TD0.countOne w + 2 * StringFlow.TD0.countTwo w +
      3 * StringFlow.TD0.countAtLeastThree w := by
    rw [hsumR]
    exact hW'
  have hmb := StringFlow.TD0.margin_balance_necessary
    (StringFlow.TD0.countOne w) (StringFlow.TD0.countTwo w)
    (StringFlow.TD0.countAtLeastThree w) hh
  simpa [w] using hmb

/-- Strict version of the prefix margin balance under a small PMI-B
budget. -/
theorem cycleWord_margin_balance_strict (c p j : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    (3 - StringFlow.TD0.log2Real 5) *
        (StringFlow.TD0.countAtLeastThree ((cycleWord c p).take j) : Real) <
      (StringFlow.TD0.log2Real 5 - 1) *
        (StringFlow.TD0.countOne ((cycleWord c p).take j) : Real) +
        (StringFlow.TD0.log2Real 5 - 2) *
          (StringFlow.TD0.countTwo ((cycleWord c p).take j) : Real) := by
  let w := (cycleWord c p).take j
  have hpref := cycleWord_pmi_b_no_bad_prefix c p hclosed hp hbudget j hj1 hjp
  have hW := StringFlow.TD0.log2_of_pow_lt_pow
      (StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j) j hpref
  have hpos_w : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    have ht' : t ∈ cycleWord c p := mem_take_imp_mem (cycleWord c p) ht
    exact cycleWord_mem_ge_one c p ht'
  have hcounts : (StringFlow.TD0.countOne w +
        2 * StringFlow.TD0.countTwo w +
        3 * StringFlow.TD0.countAtLeastThree w : Real) ≤
      (StringFlow.PMI.prefixWeight (cycleWordStepAt c p) j : Real) := by
    have hc := StringFlow.TD0.counts_weight_le w
    rw [← cycleWord_prefixWeight_eq_wordWeight_take] at hc
    exact_mod_cast hc
  have hW' : (StringFlow.TD0.countOne w +
        2 * StringFlow.TD0.countTwo w +
        3 * StringFlow.TD0.countAtLeastThree w : Real) <
      (j : Real) * StringFlow.TD0.log2Real 5 := by
    nlinarith [hW, hcounts]
  have hsum : StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w = j := by
    have hsum' := StringFlow.TD0.count_sum_length w hpos_w
    have hlen : w.length = j := by
      unfold w
      rw [List.length_take]
      have hjp_le : j ≤ p := by omega
      have hlen' : (cycleWord c p).length = p := cycleWord_length c p
      rw [hlen']
      exact Nat.min_eq_left hjp_le
    rw [hlen] at hsum'
    exact hsum'
  have hsumR : (StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w : Real) = (j : Real) := by
    exact_mod_cast hsum
  have hh : (StringFlow.TD0.countOne w + StringFlow.TD0.countTwo w +
      StringFlow.TD0.countAtLeastThree w : Real) *
      StringFlow.TD0.log2Real 5 >
    StringFlow.TD0.countOne w + 2 * StringFlow.TD0.countTwo w +
      3 * StringFlow.TD0.countAtLeastThree w := by
    rw [hsumR]
    exact hW'
  have hmb := StringFlow.TD0.margin_balance_necessary_strict
    (StringFlow.TD0.countOne w) (StringFlow.TD0.countTwo w)
    (StringFlow.TD0.countAtLeastThree w) hh
  simpa [w] using hmb

/-- The number of bad prefixes is bounded by the PMI budget quotient. -/
theorem cycleWord_badCount_le (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) :
    StringFlow.PMI.badCount p (cycleWordStepAt c p) ≤
      (5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p)) / 5 ^ p - 1 := by
  have hb := cycleWord_pmi_b_count c p hclosed hp
  have hsum : 5 ^ p + StringFlow.PMI.badCount p (cycleWordStepAt c p) * 5 ^ p =
      (StringFlow.PMI.badCount p (cycleWordStepAt c p) + 1) * 5 ^ p := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [hsum] at hb
  have hpow : 0 < 5 ^ p := Nat.pow_pos (by decide)
  have h2 : StringFlow.PMI.badCount p (cycleWordStepAt c p) + 1 ≤
      (5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p)) / 5 ^ p := by
    rw [Nat.le_div_iff_mul_le hpow]
    exact hb
  omega

/-- The word numerator of a nonempty cycle word is positive. -/
theorem cycleWord_wordA_pos (c p : Nat) (hp : 1 ≤ p) :
    0 < StringFlow.Word.wordA (cycleWord c p) := by
  have hhead := cycleWord_head_eq c p hp
  rw [hhead]
  simp [StringFlow.Word.wordA]

/-- A closed cycle word satisfies `5^P < 2^S`, i.e. the period is a
genuine positive cycle with total weight above `P log2 5`. -/
theorem cycleWord_weight_gt_five_pow (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) :
    5 ^ p < 2 ^ StringFlow.wordWeight (cycleWord c p) := by
  have hposm : 0 < fiveXPlusOneOrbit 7 c := fiveXPlusOneOrbit_pos_7 c
  have hposA : 0 < StringFlow.Word.wordA (cycleWord c p) :=
    cycleWord_wordA_pos c p hp
  have heq := cycleWord_cycle_equation c p hclosed
  have hlt : 5 ^ p * fiveXPlusOneOrbit 7 c <
      5 ^ p * fiveXPlusOneOrbit 7 c + StringFlow.Word.wordA (cycleWord c p) :=
    Nat.lt_add_of_pos_right hposA
  have hgt : 5 ^ p * fiveXPlusOneOrbit 7 c <
      2 ^ StringFlow.wordWeight (cycleWord c p) * fiveXPlusOneOrbit 7 c := by
    rwa [← heq] at hlt
  exact Nat.lt_of_mul_lt_mul_right hgt

/-- The closed cycle word has positive `2^S - 5^P`. -/
theorem cycleWord_D_pos (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p) :
    0 < 2 ^ cycleWordTotalWeight c p - 5 ^ p := by
  have hlt := cycleWord_weight_gt_five_pow c p hclosed hp
  unfold cycleWordTotalWeight at hlt ⊢
  omega

/-- Under the small PMI-B budget, `2^S < 2 * 5^P`. -/
theorem cycleWord_small_budget_two_pow_lt (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p)
    (hm7 : 7 ≤ fiveXPlusOneOrbit 7 c)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    2 ^ cycleWordTotalWeight c p < 2 * 5 ^ p := by
  let D := 2 ^ cycleWordTotalWeight c p - 5 ^ p
  have hD : 0 < D := by
    dsimp [D]
    exact cycleWord_D_pos c p hclosed hp
  have hm1 : 1 ≤ fiveXPlusOneOrbit 7 c := by omega
  have hmul : D ≤ fiveXPlusOneOrbit 7 c * D := by
    exact Nat.le_mul_of_pos_left D (by omega : 0 < fiveXPlusOneOrbit 7 c)
  have h5 : 5 * D ≤ 5 * fiveXPlusOneOrbit 7 c * D := by
    have h' : 5 * D ≤ 5 * (fiveXPlusOneOrbit 7 c * D) :=
      Nat.mul_le_mul_left 5 hmul
    simpa [Nat.mul_assoc] using h'
  have h5lt : 5 * D < 2 * 5 ^ p := by
    exact lt_of_le_of_lt h5 (by simpa [D] using hbudget)
  have hP : 0 < 5 ^ p := Nat.pow_pos (by decide)
  have h2P : 2 * 5 ^ p < 5 * 5 ^ p := by omega
  have h5P : 5 * D < 5 * 5 ^ p := Nat.lt_trans h5lt h2P
  have hDlt : D < 5 ^ p :=
    Nat.lt_of_mul_lt_mul_left h5P
  have hsum : 2 ^ cycleWordTotalWeight c p = 5 ^ p + D := by
    dsimp [D]
    omega
  rw [hsum]
  omega

/-- Under the small PMI-B budget, the total weight is within one of
the average line: `S < P*log_2 5 + 1`. -/
theorem cycleWord_small_budget_weight_lt (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp : 1 ≤ p)
    (hm7 : 7 ≤ fiveXPlusOneOrbit 7 c)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    (cycleWordTotalWeight c p : Real) <
      (p : Real) * StringFlow.TD0.log2Real 5 + 1 := by
  have h2 := cycleWord_small_budget_two_pow_lt c p hclosed hp hm7 hbudget
  exact StringFlow.TD0.log2_of_pow_lt_two_mul (cycleWordTotalWeight c p) p h2

/-- Under the small PMI-B budget, the last accelerated step must be a
C3 step (`t >= 3`). -/
theorem cycleWord_last_step_c3_of_small_budget (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp2 : 2 ≤ p)
    (hm7 : 7 ≤ fiveXPlusOneOrbit 7 c)
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) :
    3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 (c + (p - 1)) + 1) := by
  let S := cycleWordTotalWeight c p
  let W := StringFlow.PMI.prefixWeight (cycleWordStepAt c p) (p - 1)
  let t := twoValuation (5 * fiveXPlusOneOrbit 7 (c + (p - 1)) + 1)
  have hp : 1 ≤ p := by omega
  have hsplit := cycleWord_weight_split_last c p hp
  have hpref := cycleWord_pmi_b_no_bad_prefix c p hclosed hp hbudget
    (p - 1) (by omega) (by omega)
  have hW := StringFlow.TD0.log2_of_pow_lt_pow W (p - 1) hpref
  have hSgt := StringFlow.TD0.log2_of_pow_gt_pow S p
    (cycleWord_weight_gt_five_pow c p hclosed hp)
  have hSlt := cycleWord_small_budget_weight_lt c p hclosed hp hm7 hbudget
  have hsplitR : (S : Real) = (W : Real) + (t : Real) := by
    dsimp [S, t]
    exact_mod_cast hsplit
  have hRpos : 0 < (S : Real) - (p : Real) * StringFlow.TD0.log2Real 5 := by
    nlinarith [hSgt]
  have hp1 : ((p - 1 : Nat) : Real) + 1 = (p : Real) := by
    exact_mod_cast (Nat.sub_add_cancel hp)
  have hRlt : (S : Real) - (p : Real) * StringFlow.TD0.log2Real 5 <
      (t : Real) - StringFlow.TD0.log2Real 5 := by
    calc
      (S : Real) - (p : Real) * StringFlow.TD0.log2Real 5
          = (W : Real) + (t : Real) - (p : Real) * StringFlow.TD0.log2Real 5 := by
              rw [hsplitR]
      _ < ((p - 1 : Nat) : Real) * StringFlow.TD0.log2Real 5 +
            (t : Real) - (p : Real) * StringFlow.TD0.log2Real 5 := by
              nlinarith [hW]
      _ = (t : Real) - StringFlow.TD0.log2Real 5 := by
              nlinarith [hp1]
  have htgt : StringFlow.TD0.log2Real 5 < (t : Real) := by
    nlinarith [hRpos, hRlt]
  have hgt2 : (2 : Real) < StringFlow.TD0.log2Real 5 :=
    StringFlow.TD0.log2_five_gt_two
  have ht2 : (2 : Real) < (t : Real) := by nlinarith
  have ht2nat : 2 < t := by exact_mod_cast ht2
  have ht3 : 3 ≤ t := by omega
  simpa [t] using ht3

/-- The small-budget hypothesis contradicts a C3 first step: the
first proper prefix would be bad. -/
theorem small_budget_contradicts_c3_start (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp2 : 2 ≤ p)
    (hc3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1))
    (hbudget : 5 * fiveXPlusOneOrbit 7 c *
        (2 ^ cycleWordTotalWeight c p - 5 ^ p) < 2 * 5 ^ p) : False := by
  have hp : 1 ≤ p := by omega
  have hpref := cycleWord_pmi_b_no_bad_prefix c p hclosed hp hbudget 1 (by omega) (by omega)
  have hW1 : StringFlow.PMI.prefixWeight (cycleWordStepAt c p) 1 =
      cycleWordStepAt c p 0 := by
    simp [StringFlow.PMI.prefixWeight]
  have ht0 : cycleWordStepAt c p 0 =
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
    unfold cycleWordStepAt
    rw [cycleWord_head_eq c p hp]
    simp
  have hlt : 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) < 5 := by
    simpa [hW1, ht0] using hpref
  have hgt : 5 < 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
    have hpow : 2 ^ 3 ≤ 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hc3
    have h58 : 5 < 2 ^ 3 := by norm_num
    exact lt_of_lt_of_le h58 hpow
  omega

/-- A C3 first step makes the first proper prefix bad. -/
theorem cycleWord_badCount_ge_one_of_c3_start (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp2 : 2 ≤ p)
    (hc3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)) :
    1 ≤ StringFlow.PMI.badCount p (cycleWordStepAt c p) := by
  have hp : 1 ≤ p := by omega
  have hW1 : StringFlow.PMI.prefixWeight (cycleWordStepAt c p) 1 =
      cycleWordStepAt c p 0 := by
    simp [StringFlow.PMI.prefixWeight]
  have ht0 : cycleWordStepAt c p 0 =
      twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
    unfold cycleWordStepAt
    rw [cycleWord_head_eq c p hp]
    simp
  have hbad : 5 ≤ 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
    have hpow : 2 ^ 3 ≤ 2 ^ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hc3
    have h58 : 5 < 2 ^ 3 := by norm_num
    exact le_of_lt (lt_of_lt_of_le h58 hpow)
  have hmem : 1 ∈ StringFlow.PMI.badList p (cycleWordStepAt c p) :=
    (StringFlow.PMI.mem_badList_iff p (cycleWordStepAt c p) 1).mpr
      ⟨by omega, by omega, by simpa [hW1, ht0] using hbad⟩
  have hlen : 0 < (StringFlow.PMI.badList p (cycleWordStepAt c p)).length :=
    List.length_pos_of_mem hmem
  unfold StringFlow.PMI.badCount
  omega

/-- The PMI-B budget is at least `2 * 5^P` for a C3-start cycle word. -/
theorem cycleWord_pmi_budget_ge_two_pow (c p : Nat)
    (hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c) (hp2 : 2 ≤ p)
    (hc3 : 3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1)) :
    2 * 5 ^ p ≤ 5 * fiveXPlusOneOrbit 7 c *
      (2 ^ cycleWordTotalWeight c p - 5 ^ p) := by
  have hb := cycleWord_pmi_b_count c p hclosed (by omega)
  have hbc := cycleWord_badCount_ge_one_of_c3_start c p hclosed hp2 hc3
  have hle1 : 5 ^ p ≤ StringFlow.PMI.badCount p (cycleWordStepAt c p) * 5 ^ p := by
    exact Nat.le_mul_of_pos_left (5 ^ p) hbc
  have hle2 : 2 * 5 ^ p ≤ 5 ^ p +
      StringFlow.PMI.badCount p (cycleWordStepAt c p) * 5 ^ p := by
    rw [Nat.two_mul]
    exact Nat.add_le_add_left hle1 (5 ^ p)
  exact le_trans hle2 hb

/-- A positive cycle gives a closed period word whose first step is a
C3 start. -/
theorem orbit_cycle_imp_cycle_word_closed (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
  rcases orbit_cycle_imp_periodic_c3_segment h with ⟨c, p, hp, hc3, hper⟩
  refine ⟨c, p, hp, ?_, hc3⟩
  rw [cycleWord_orbit_eq c p]
  exact hper

/-- A positive cycle gives a closed, valid period word whose first
step is a C3 start. -/
theorem orbit_cycle_imp_cycle_word_valid_closed (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      StringFlow.Word.wordValid (cycleWord c p) (fiveXPlusOneOrbit 7 c) ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
  rcases orbit_cycle_imp_cycle_word_closed h with ⟨c, p, hp, hclosed, hc3⟩
  exact ⟨c, p, hp, cycleWord_wordValid c p, hclosed, hc3⟩

/-- The full cycle-word input for the QB-8 translation: the word is
valid, closed, starts with a C3 step, and has the explicit head
decomposition. -/
theorem orbit_cycle_imp_cycle_word_qb8_input (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      StringFlow.Word.wordValid (cycleWord c p) (fiveXPlusOneOrbit 7 c) ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      cycleWord c p = twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) ::
        cycleWord (c + 1) (p - 1) ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
  rcases orbit_cycle_imp_cycle_word_valid_closed h with
    ⟨c, p, hp, hvalid, hclosed, hc3⟩
  exact ⟨c, p, hp, hvalid, hclosed, cycleWord_head_eq c p hp, hc3⟩

/-- A positive cycle gives the full Diophantine cycle equation
`2^S * m = 5^p * m + A` for a closed, valid word with a C3 head. -/
theorem orbit_cycle_imp_diophantine_cycle_equation (h : OrbitCycle 7) :
    ∃ c p : Nat, 1 ≤ p ∧
      (cycleWord c p).length = p ∧
      StringFlow.Word.wordValid (cycleWord c p) (fiveXPlusOneOrbit 7 c) ∧
      StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
        fiveXPlusOneOrbit 7 c ∧
      2 ^ StringFlow.wordWeight (cycleWord c p) * fiveXPlusOneOrbit 7 c =
        5 ^ p * fiveXPlusOneOrbit 7 c + StringFlow.Word.wordA (cycleWord c p) ∧
      3 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) := by
  rcases orbit_cycle_imp_cycle_word_valid_closed h with
    ⟨c, p, hp, hvalid, hclosed, hc3⟩
  exact ⟨c, p, hp, cycleWord_length c p, hvalid, hclosed,
    cycleWord_cycle_equation c p hclosed, hc3⟩

/-- Range-free QB-8 word input extracted from a positive cycle.

The existing `FirstC3Orbit`/`Qb8Orbit` structures carry
`m ≤ 10^6`, `8 ≤ Q`, `feasible64`, and `S ≥ 26` assumptions, which
are not allowed by the cycle-bridge discipline.  This structure keeps
only what follows from the cycle itself: a valid closed word, its
rise/C3 split, and the C3-count positivity. -/
structure CycleQb8Input (m S P : Nat) (w rise c3 : List Nat) : Prop where
  hvalid : StringFlow.Word.wordValid w m
  hclosed : StringFlow.Word.wordOrbit w m = m
  hlength : w.length = P
  hweight : StringFlow.wordWeight w = S
  hrise_ok : ∀ t ∈ rise, t = 1 ∨ t = 2
  hc3_ok : ∀ t ∈ c3, 3 ≤ t
  hlen_split : rise.length + c3.length = P
  hweight_split : S = StringFlow.wordWeight rise + StringFlow.wordWeight c3
  hc3_pos : 1 ≤ c3.length
  hrise_start : w.getI 0 = 1 ∨ w.getI 0 = 2
  hglobal_min : ∀ i : Nat, i < P →
    m ≤ StringFlow.Word.wordOrbit (w.take i) m
  hrise_filter : rise = (w.filter (fun t => decide (t < 3)))
  hc3_filter : c3 = (w.filter (fun t => decide (3 ≤ t)))
  hexact : ∀ k, k < w.length →
    twoValuation (5 * StringFlow.Word.wordOrbit (w.take k) m + 1) = w.getI k
  hm_pos : 0 < m
  hstart : S6Audit.FullOrbitFrom7 m
  hcycle : Nonempty { cp : Nat × Nat //
    And (w = cycleWord cp.1 cp.2)
      (And (m = fiveXPlusOneOrbit 7 cp.1)
        (And (S = StringFlow.wordWeight (cycleWord cp.1 cp.2))
          (And (rise = cycleWordRiseSteps cp.1 cp.2)
            (c3 = cycleWordC3Steps cp.1 cp.2)))) }
  hm_odd : S6Audit.IsOdd m
  hm_not_five : ¬ 5 ∣ m
  hrise_pos : 1 ≤ rise.length

/-- Every positive cycle supplies a range-free QB-8 word input. -/
theorem orbit_cycle_imp_cycle_qb8_input (h : OrbitCycle 7) :
    ∃ c p m S : Nat, ∃ w rise c3 : List Nat,
      CycleQb8Input m S p w rise c3 ∧
      w = cycleWord c p ∧ rise = cycleWordRiseSteps c p ∧
      c3 = cycleWordC3Steps c p ∧ S = StringFlow.wordWeight w ∧
      m = fiveXPlusOneOrbit 7 c := by
  rcases orbit_cycle_imp_min_rise_start_min h with
    ⟨c, p, hp, hclosed, hrise, hglobal⟩
  have hvalid : StringFlow.Word.wordValid (cycleWord c p)
      (fiveXPlusOneOrbit 7 c) := cycleWord_wordValid c p
  refine ⟨c, p, fiveXPlusOneOrbit 7 c,
    StringFlow.wordWeight (cycleWord c p), cycleWord c p,
    cycleWordRiseSteps c p, cycleWordC3Steps c p, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact {
    hvalid := hvalid
    hclosed := hclosed
    hlength := cycleWord_length c p
    hweight := rfl
    hrise_ok := fun t ht => cycleWordRiseSteps_mem_one_two c p ht
    hc3_ok := fun t ht => cycleWordC3Steps_mem_ge_three c p ht
    hlen_split := cycleWord_length_split c p
    hweight_split := by
      unfold cycleWordRiseSteps cycleWordC3Steps
      exact cycleWord_weight_decomp c p
    hc3_pos := by
      have hpos : 1 ≤ cycleWordC3Count c p :=
        cycleWordC3Count_pos_of_rise_closed c p hp hclosed
      rw [← cycleWordC3Steps_length c p] at hpos
      exact hpos
    hrise_start := by
      rw [cycleWord_head_eq c p hp]
      have hge : 1 ≤ twoValuation (5 * fiveXPlusOneOrbit 7 c + 1) :=
        twoValuation_five_mul_add_one_ge_one (fiveXPlusOneOrbit 7 c)
          (fiveXPlusOneOrbit_odd_7 c)
      simp
      omega
    hglobal_min := by
      intro i hi
      have hprefix := cycleWord_prefix_orbit_eq c p i (by omega)
      have hmin := hglobal i (by omega)
      simpa [hprefix] using hmin
    hrise_filter := by
      unfold cycleWordRiseSteps
      rfl
    hc3_filter := by
      unfold cycleWordC3Steps
      rfl
    hexact := by
      intro k hk
      have hk' : k < p := by
        rw [← cycleWord_length c p]
        exact hk
      exact cycleWord_step_exact c p k hk'
    hm_pos := fiveXPlusOneOrbit_pos_7 c
    hstart := Exists.intro c (by rw [fullOrbitIter_eq_fiveXPlusOneOrbit])
    hcycle := Nonempty.intro (Subtype.mk (c, p)
      (And.intro rfl (And.intro rfl (And.intro rfl (And.intro rfl rfl)))))
    hm_odd := fiveXPlusOneOrbit_odd_7 c
    hm_not_five := fiveXPlusOneOrbit_not_dvd_five c
    hrise_pos := by
      have hne : cycleWordRiseSteps c p ≠ [] :=
        cycleWordRiseSteps_nonempty_of_closed c p hp hclosed
      cases h : cycleWordRiseSteps c p with
      | nil => exact False.elim (hne h)
      | cons a as => simp }

/-- A closed QB-8 cycle word has at least one rise step and one C3
step, so its period length is at least two. -/
theorem cycleQb8Input_P_ge_two {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) : 2 ≤ P := by
  have hr : 1 ≤ rise.length := h.hrise_pos
  have hc : 1 ≤ c3.length := h.hc3_pos
  have hsum : rise.length + c3.length = P := h.hlen_split
  omega

/-- The same lower bound on the word length. -/
theorem cycleQb8Input_length_ge_two {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) : 2 ≤ w.length := by
  rw [h.hlength]
  exact cycleQb8Input_P_ge_two h

/-- The rise and C3 lists of a QB-8 input are disjoint. -/
theorem cycleQb8Input_rise_disjoint_c3 {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∀ t : Nat, t ∈ rise → t ∉ c3 := by
  intro t ht htc3
  rcases h.hrise_ok t ht with ht1 | ht2
  · subst t
    have hge : 3 ≤ 1 := h.hc3_ok 1 htc3
    norm_num at hge
  · subst t
    have hge : 3 ≤ 2 := h.hc3_ok 2 htc3
    norm_num at hge

/-- A nonempty C3 filter of a word locates an actual C3 index. -/
theorem exists_c3_index_of_filter_nonempty (w : List Nat)
    (hne : (w.filter (fun t => decide (3 ≤ t))) ≠ []) :
    ∃ j : Nat, j < w.length ∧ 3 ≤ w.getI j := by
  induction w with
  | nil => simp at hne
  | cons t ts ih =>
      by_cases ht : 3 ≤ t
      · refine ⟨0, by simp, ht⟩
      · have hne' : (ts.filter (fun t => decide (3 ≤ t))) ≠ [] := by
          intro hnil
          apply hne
          simp [ht, hnil]
        rcases ih hne' with ⟨j, hjlt, hjge⟩
        refine ⟨j + 1, by simp [hjlt], ?_⟩
        rw [List.getI_cons_succ]
        exact hjge

/-- A nonempty rise filter with `t ∈ {1,2}` members locates an
actual rise index. -/
theorem exists_rise_index_of_filter (w : List Nat)
    (hne : (w.filter (fun t => decide (t < 3))) ≠ [])
    (hok : ∀ t, t ∈ (w.filter (fun t => decide (t < 3))) → t = 1 ∨ t = 2) :
    ∃ j : Nat, j < w.length ∧ (w.getI j = 1 ∨ w.getI j = 2) := by
  induction w with
  | nil => simp at hne
  | cons t ts ih =>
      by_cases ht : t < 3
      · have hmem : t ∈ (t :: ts).filter (fun t => decide (t < 3)) := by
          simp [ht]
        have h12 := hok t hmem
        refine ⟨0, by simp, h12⟩
      · have hne' : (ts.filter (fun t => decide (t < 3))) ≠ [] := by
          intro hnil
          apply hne
          simp [ht, hnil]
        have hok' : ∀ x, x ∈ (ts.filter (fun t => decide (t < 3))) →
            x = 1 ∨ x = 2 := by
          intro x hx
          have hx' : x ∈ (t :: ts).filter (fun t => decide (t < 3)) := by
            rcases (List.mem_filter.mp hx) with ⟨hxmem, hxlt⟩
            rw [List.mem_filter]
            exact ⟨List.mem_cons.mpr (Or.inr hxmem), hxlt⟩
          exact hok x hx'
        rcases ih hne' hok' with ⟨j, hjlt, hj12⟩
        refine ⟨j + 1, by simp [hjlt], ?_⟩
        rw [List.getI_cons_succ]
        exact hj12

/-- Every closed QB-8 input has an actual rise index in its word. -/
theorem cycleQb8Input_exists_rise_index {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∃ j : Nat, j < w.length ∧ (w.getI j = 1 ∨ w.getI j = 2) := by
  have hne : (w.filter (fun t => decide (t < 3))) ≠ [] := by
    rw [← h.hrise_filter]
    cases hrise_eq : rise with
    | nil =>
        have hpos : 1 ≤ 0 := by simpa [hrise_eq] using h.hrise_pos
        omega
    | cons a as =>
        intro hnil
        simp at hnil
  have hok : ∀ t, t ∈ (w.filter (fun t => decide (t < 3))) → t = 1 ∨ t = 2 := by
    intro t ht
    have ht' : t ∈ rise := by
      rw [h.hrise_filter]
      exact ht
    exact h.hrise_ok t ht'
  exact exists_rise_index_of_filter w hne hok

/-- Every closed QB-8 input has an actual C3 index in its word. -/
theorem cycleQb8Input_exists_c3_index {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∃ j : Nat, j < w.length ∧ 3 ≤ w.getI j := by
  have hne : (w.filter (fun t => decide (3 ≤ t))) ≠ [] := by
    rw [← h.hc3_filter]
    cases hc3_eq : c3 with
    | nil =>
        have hpos : 1 ≤ 0 := by simpa [hc3_eq] using h.hc3_pos
        omega
    | cons a as =>
        intro hnil
        simp at hnil
  exact exists_c3_index_of_filter_nonempty w hne

/-- Every closed QB-8 input contains both a C3 index and a rise
index. -/
theorem cycleQb8Input_exists_c3_and_rise_index
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    (∃ j : Nat, j < w.length ∧ 3 ≤ w.getI j) ∧
      (∃ j : Nat, j < w.length ∧ (w.getI j = 1 ∨ w.getI j = 2)) := by
  constructor
  · exact cycleQb8Input_exists_c3_index h
  · exact cycleQb8Input_exists_rise_index h

/-- A PMI-B bad proper prefix of a closed QB-8 cycle word returns to
the global minimum: `wordOrbit (w.take j) m = m`.  Here "bad" is the
PMI-B condition `5^j <= 2^(W_j)` in the word-weight form of
`StringFlow.PMI.isBad`, and the numerator bound
`wordA (w.take j) < 5^j` is supplied by `wordA_lt_five_pow` on the
pure `{1,2}` prefix. -/
theorem cycleQb8Input_bad_prefix_returns_to_min
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) {j : Nat}
    (hjp : j < P)
    (hbad : 5 ^ j ≤ 2 ^ StringFlow.wordWeight (w.take j))
    (hok : StringFlow.Word.wordOK (w.take j)) :
    StringFlow.Word.wordOrbit (w.take j) m = m := by
  let u := w.take j
  have hu_len : u.length = j := by
    dsimp [u]
    rw [List.length_take_of_le]
    rw [h.hlength]
    omega
  have hv : StringFlow.Word.wordValid (u ++ w.drop j) m := by
    dsimp [u]
    simpa [List.take_append_drop] using h.hvalid
  have hvalid_u : StringFlow.Word.wordValid u m := by
    exact (S6Audit.wordValid_append u (w.drop j) m).mp hv |>.1
  have hA_lt : StringFlow.Word.wordA u < 5 ^ j := by
    have hlt := StringFlow.Word.wordA_lt_five_pow u hok
    rwa [hu_len] at hlt
  have hid : 2 ^ StringFlow.wordWeight u * StringFlow.Word.wordOrbit u m =
      5 ^ j * m + StringFlow.Word.wordA u := by
    have hid' := StringFlow.Word.word_orbit_identity u m hvalid_u
    rwa [hu_len] at hid'
  have hmul_lt : StringFlow.Word.wordOrbit u m *
        2 ^ StringFlow.wordWeight u <
      (m + 1) * 2 ^ StringFlow.wordWeight u := by
    calc
      StringFlow.Word.wordOrbit u m * 2 ^ StringFlow.wordWeight u
          = 5 ^ j * m + StringFlow.Word.wordA u := by
              rw [Nat.mul_comm, hid]
      _ < 5 ^ j * m + 5 ^ j := Nat.add_lt_add_left hA_lt (5 ^ j * m)
      _ = 5 ^ j * (m + 1) := by ring
      _ ≤ (m + 1) * 2 ^ StringFlow.wordWeight u := by
          have h' : 5 ^ j * (m + 1) ≤
              2 ^ StringFlow.wordWeight u * (m + 1) :=
            Nat.mul_le_mul_right (m + 1) hbad
          rw [Nat.mul_comm (m + 1) (2 ^ StringFlow.wordWeight u)]
          exact h'
  have ho_le_m : StringFlow.Word.wordOrbit u m ≤ m := by
    have hlt := Nat.lt_of_mul_lt_mul_right hmul_lt
    omega
  have hm_le_o : m ≤ StringFlow.Word.wordOrbit u m := by
    simpa [u] using h.hglobal_min j hjp
  simpa [u] using le_antisymm ho_le_m hm_le_o

/-- One more step of `wordOrbit` is the exact quotient by the next
step weight. -/
theorem wordOrbit_take_succ (w : List Nat) (m j : Nat) (hj : j < w.length) :
    StringFlow.Word.wordOrbit (w.take (j + 1)) m =
      (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) / 2 ^ w.getI j := by
  induction j generalizing w m with
  | zero =>
      cases w with
      | nil => simp at hj
      | cons a as =>
          simp [StringFlow.Word.wordOrbit]
  | succ j ih =>
      cases w with
      | nil => simp at hj
      | cons a as =>
          have hj' : j < as.length := by
            simp at hj
            omega
          have hih := ih as ((5 * m + 1) / 2 ^ a) hj'
          have htake : (a :: as).take (j + 2) = a :: as.take (j + 1) :=
            List.take_cons (by omega)
          simpa [htake, StringFlow.Word.wordOrbit, List.getI_cons_succ] using hih

/-- The prefix orbit at `b+L` is the orbit of the suffix after `b`
starting from the prefix orbit at `b`. -/
theorem wordOrbit_take_drop (w : List Nat) (m b L : Nat)
    (hbL : b + L <= w.length) :
    StringFlow.Word.wordOrbit (w.take (b + L)) m =
      StringFlow.Word.wordOrbit ((w.take (b + L)).drop b)
        (StringFlow.Word.wordOrbit (w.take b) m) := by
  have hsplit : w.take (b + L) =
      (w.take (b + L)).take b ++ (w.take (b + L)).drop b := by
    rw [List.take_append_drop b (w.take (b + L))]
  have htake : (w.take (b + L)).take b = w.take b := by
    rw [List.take_take]
    rw [Nat.min_eq_left]
    omega
  conv_lhs => rw [hsplit]
  rw [S6Audit.wordOrbit_append]
  rw [htake]

/-- A nonempty dropped segment of the first `b+L` entries is obtained
by appending the last entry to the dropped segment of the first
`b+L-1` entries. -/
lemma cycleWord_drop_take_concat_last
    (w : List Nat) (b L : Nat)
    (hL : 1 ≤ L) (hbL : b + L ≤ w.length) :
    (w.take (b + L)).drop b =
      (w.take (b + L - 1)).drop b ++ [w.getI (b + L - 1)] := by
  let i := b + L - 1
  have hi : i < w.length := by omega
  have htake : (w.take i).concat w[i] = w.take (i + 1) :=
    List.take_concat_get hi
  have happ : (w.take i) ++ [w[i]] = w.take (i + 1) := by
    simpa [List.concat_eq_append] using htake
  have hlen_take : b ≤ (w.take i).length := by
    have hle : i ≤ w.length := le_of_lt hi
    rw [List.length_take_of_le hle]
    omega
  have hdrop := List.drop_append_of_le_length
    (l₁ := w.take i) (l₂ := [w[i]]) hlen_take
  have hget : w[i] = w.getI i := by
    have hd := List.getElem_eq_getD (l := w) (i := i) (h := hi) 0
    unfold List.getI
    exact hd
  have hidx : i + 1 = b + L := by omega
  calc
    (w.take (b + L)).drop b = (w.take (i + 1)).drop b := by rw [← hidx]
    _ = ((w.take i) ++ [w[i]]).drop b := by rw [← happ]
    _ = (w.take i).drop b ++ [w[i]] := hdrop
    _ = (w.take (b + L - 1)).drop b ++ [w.getI (b + L - 1)] := by
        dsimp [i]
        rw [hget]

/-- The actual local block equation obtained by writing a `CycleQb8Input`
segment as a suffix of the full cycle word.  This supplies the genuine
`q`, `A_j`, `Wj`, and `rj` required by 36.30.8.2; `q` is the local orbit
start state, not the previous terminal odd part `s`. -/
theorem cycleQb8Input_local_block_equation
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hbL : b + L ≤ w.length) :
    let u := (w.take (b + L)).drop b
    let q := StringFlow.Word.wordOrbit (w.take b) m
    let rj := StringFlow.Word.wordOrbit u q
    u.length = L ∧ StringFlow.Word.wordValid u q ∧
      StringFlow.Word.wordOrbit (w.take (b + L)) m = rj ∧
      2 ^ StringFlow.wordWeight u * rj =
        5 ^ L * q + StringFlow.Word.wordA u := by
  let u := (w.take (b + L)).drop b
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let rj := StringFlow.Word.wordOrbit u q
  have hu_take : u = (w.drop b).take L := by
    dsimp [u]
    rw [List.take_drop]
  have hvalid_rest : StringFlow.Word.wordValid (w.drop b) q := by
    have hv : StringFlow.Word.wordValid (w.take b ++ w.drop b) m := by
      simpa using h.hvalid
    have hparts := (S6Audit.wordValid_append (w.take b) (w.drop b) m).mp hv
    dsimp [q]
    exact hparts.2
  have hrest_split : w.drop b = u ++ (w.drop b).drop L := by
    calc
      w.drop b = (w.drop b).take L ++ (w.drop b).drop L :=
        (List.take_append_drop L (w.drop b)).symm
      _ = u ++ (w.drop b).drop L :=
        congrArg (fun v => v ++ (w.drop b).drop L) hu_take.symm
  have hvalid_u : StringFlow.Word.wordValid u q := by
    have hvalid_rest' : StringFlow.Word.wordValid
        (u ++ (w.drop b).drop L) q := by
      rw [← hrest_split]
      exact hvalid_rest
    exact (S6Audit.wordValid_append u ((w.drop b).drop L) q).mp
      hvalid_rest' |>.1
  have hlen : u.length = L := by
    dsimp [u]
    rw [List.length_drop, List.length_take_of_le hbL]
    omega
  have hend : StringFlow.Word.wordOrbit (w.take (b + L)) m = rj := by
    dsimp [rj, q, u]
    exact wordOrbit_take_drop w m b L hbL
  have hid := StringFlow.Word.word_orbit_identity u q hvalid_u
  have hid' : 2 ^ StringFlow.wordWeight u * rj =
      5 ^ L * q + StringFlow.Word.wordA u := by
    simpa [rj, hlen] using hid
  exact ⟨hlen, hvalid_u, hend, hid'⟩

/-- The full local block data used in 36.30.8.2: the block quotient
`q`, numerator `A_j`, prefix weights `Wp,Wj`, last step `t`, and block
head `rj`.  The endpoint equation and divisibility are returned as
proofs, so this is not a bare parameter bundle. -/
theorem cycleQb8Input_local_block_data
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L : Nat) (hL : 1 ≤ L) (hbL : b + L ≤ w.length) :
    ∃ q Aj Wp Wj t rj : Nat,
      q = StringFlow.Word.wordOrbit (w.take b) m ∧
      rj = StringFlow.Word.wordOrbit (w.take (b + L)) m ∧
      Aj = StringFlow.Word.wordA ((w.take (b + L)).drop b) ∧
      Wj = StringFlow.wordWeight ((w.take (b + L)).drop b) ∧
      Wp = StringFlow.wordWeight ((w.take (b + L - 1)).drop b) ∧
      t = w.getI (b + L - 1) ∧
      Wj = Wp + t ∧
      2 ^ Wj * rj = Aj + 5 ^ L * q ∧
      (Aj + 5 ^ L * q) % 2 ^ Wj = 0 ∧
      rj = (Aj + 5 ^ L * q) / 2 ^ Wj := by
  let u := (w.take (b + L)).drop b
  let q := StringFlow.Word.wordOrbit (w.take b) m
  let rj := StringFlow.Word.wordOrbit u q
  have hblock := cycleQb8Input_local_block_equation h b L hbL
  have hlen : u.length = L := hblock.1
  have hvalid : StringFlow.Word.wordValid u q := hblock.2.1
  have hend : StringFlow.Word.wordOrbit (w.take (b + L)) m = rj := hblock.2.2.1
  have hid : 2 ^ StringFlow.wordWeight u * rj = 5 ^ L * q + StringFlow.Word.wordA u :=
    hblock.2.2.2
  let Aj := StringFlow.Word.wordA u
  let Wj := StringFlow.wordWeight u
  let Wp := StringFlow.wordWeight ((w.take (b + L - 1)).drop b)
  let t := w.getI (b + L - 1)
  have hsplitList : u = (w.take (b + L - 1)).drop b ++ [t] := by
    dsimp [u, t]
    exact cycleWord_drop_take_concat_last w b L hL hbL
  have hW : Wj = Wp + t := by
    dsimp [Wj, Wp, t]
    rw [hsplitList]
    exact UnifiedCoreAudit.wordWeight_append_singleton
      ((w.take (b + L - 1)).drop b) (w.getI (b + L - 1))
  have hEq : Aj + 5 ^ L * q = 2 ^ Wj * rj := by
    have h := hid
    dsimp [Aj, Wj] at h ⊢
    rw [Nat.add_comm] at h
    exact h.symm
  have hdiv : (Aj + 5 ^ L * q) % 2 ^ Wj = 0 := by
    exact Nat.mod_eq_zero_of_dvd ⟨rj, hEq⟩
  have hrjform : rj = (Aj + 5 ^ L * q) / 2 ^ Wj := by
    rw [hEq]
    exact (Nat.mul_div_right rj (Nat.pow_pos (by decide : 0 < 2) :
      0 < 2 ^ Wj)).symm
  exact ⟨q, Aj, Wp, Wj, t, rj, rfl, by
    dsimp [rj]
    exact hend.symm, rfl, rfl, rfl, rfl, hW, by
      dsimp [Aj, Wj]
      simpa [Nat.add_comm] using hid, hdiv, hrjform⟩

/-- Every prefix of a closed cycle word from the full-orbit start
state is itself a full-orbit state. -/
theorem cycleQb8Input_prefix_full_reachable
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j <= w.length) :
    S6Audit.FullOrbitFrom7 (StringFlow.Word.wordOrbit (w.take j) m) := by
  induction j with
  | zero =>
      simpa [StringFlow.Word.wordOrbit] using h.hstart
  | succ j ih =>
      have hjw : j < w.length := by omega
      have hprev : S6Audit.FullOrbitFrom7
          (StringFlow.Word.wordOrbit (w.take j) m) := ih (by omega)
      rcases hprev with ⟨n, hn⟩
      have hstep := wordOrbit_take_succ w m j hjw
      have hex : twoValuation
          (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) =
          w.getI j := h.hexact j hjw
      have hexS : S6Audit.twoValuation
          (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) =
          w.getI j := by simpa using hex
      have hnext : StringFlow.Word.wordOrbit (w.take (j + 1)) m =
          S6Audit.fullOrbitStep (StringFlow.Word.wordOrbit (w.take j) m) := by
        rw [hstep]
        unfold S6Audit.fullOrbitStep
        rw [hexS]
      have hiter : S6Audit.fullOrbitIter (n + 1) =
          S6Audit.fullOrbitStep (S6Audit.fullOrbitIter n) := rfl
      refine Exists.intro (n + 1) ?_
      rw [hnext, ← hn, hiter]

/-- The even intermediate immediately before a prefix state is
reachable in the general orbit, with the same concrete cycle word. -/
theorem cycleQb8Input_predecessor_general_reachable
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : 1 <= j) (hjl : j <= w.length) :
    S6Audit.GeneralOrbitFrom7
      ((5 * StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) / 2) := by
  let x := StringFlow.Word.wordOrbit (w.take (j - 1)) m
  have hfull : S6Audit.FullOrbitFrom7 x :=
    cycleQb8Input_prefix_full_reachable h (j - 1) (by omega)
  have hgen : S6Audit.GeneralOrbitFrom7 x :=
    S6Audit.FullOrbitFrom7_imp_general x hfull
  have hodd : S6Audit.IsOdd x := S6Audit.FullOrbitFrom7_odd x hfull
  have hmod : (5 * x + 1) % 2 = 0 := by
    have hx : x % 2 = 1 := hodd
    rw [Nat.add_mod, Nat.mul_mod]
    simp [hx]
  exact S6Audit.general_orbit_step x 1 hmod hgen

/-- Construct the real terminal data from the exact C3 step preceding
a rise block.  This keeps `q` and `s` separate: `q` never enters this
structure. -/
theorem cycleQb8Input_real_terminal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) (hb1 : 1 ≤ b) (hb_le : b ≤ w.length)
    (hprev3 : 3 ≤ w.getI (b - 1)) :
    ∃ rt : RealTerminal,
      rt.r_prev = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 := by
  let x := StringFlow.Word.wordOrbit (w.take (b - 1)) m
  let rprev := (5 * x + 1) / 2
  have hbprev_lt : b - 1 < w.length := by omega
  have htprev : twoValuation (5 * x + 1) = w.getI (b - 1) := by
    dsimp [x]
    exact h.hexact (b - 1) hbprev_lt
  have hge3 : 3 ≤ twoValuation (5 * x + 1) := by
    rw [htprev]
    exact hprev3
  have hge2 : 2 ≤ twoValuation (5 * x + 1) := by omega
  have h4dvd : 4 ∣ 5 * x + 1 := by
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 * x + 1) 2 (by positivity)).mp hge2
  rcases h4dvd with ⟨y, hy⟩
  have hrprev_even : rprev % 2 = 0 := by
    dsimp [rprev]
    have hdiv : (4 * y) / 2 = 2 * y := by omega
    rw [hy, hdiv]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  have hr_odd : (rprev + 1) % 2 = 1 := by
    rw [Nat.add_mod, hrprev_even]
  have hrpos : rprev + 1 ≠ 0 := by positivity
  let k0 := fiveValuation (rprev + 1)
  let s := fiveOddPart (rprev + 1)
  have hreach : S6Audit.GeneralOrbitFrom7 rprev := by
    dsimp [rprev, x]
    exact cycleQb8Input_predecessor_general_reachable h b hb1 hb_le
  refine ⟨{ r_prev := rprev
            s := s
            k0 := k0
            hprod := by
              dsimp [s, k0]
              have h := (fiveOddPart_spec hrpos).symm
              rw [Nat.mul_comm] at h
              exact h
            hs_odd := by
              dsimp [s]
              exact fiveOddPart_odd_of_odd hr_odd
            hs_not_five := by
              dsimp [s]
              exact fiveOddPart_not_dvd_five hrpos
            hreach := hreach }, ?_⟩
  dsimp [rprev, x]

/-- The same real terminal packaged in the
`AngelinaGilbertaRealTerminal` structure.  This is the terminal
component used by the local `hident` assembly below; it does not
introduce the block quotient `q` as `s`. -/
theorem cycleQb8Input_angelina_real_terminal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b : Nat) (hb1 : 1 ≤ b) (hb_le : b ≤ w.length)
    (hprev3 : 3 ≤ w.getI (b - 1)) :
    ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
      rt.r = (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 := by
  rcases cycleQb8Input_real_terminal h b hb1 hb_le hprev3 with
    ⟨rt, hrt⟩
  refine ⟨{ r := rt.r_prev
            s := rt.s
            k := rt.k0
            hprod := rt.hprod
            hs_odd := rt.hs_odd
            hs_not_five := rt.hs_not_five
            hreach := rt.hreach }, ?_⟩
  exact hrt

/-- Recover the concrete cycle parameters from the `Nonempty` field
of a `CycleQb8Input`. -/
theorem cycleQb8Input_cycle_params
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∃ c p : Nat, w = cycleWord c p ∧
      m = fiveXPlusOneOrbit 7 c ∧
      S = StringFlow.wordWeight (cycleWord c p) ∧
      rise = cycleWordRiseSteps c p ∧
      c3 = cycleWordC3Steps c p := by
  rcases h.hcycle with ⟨hcp⟩
  rcases hcp with ⟨cp, hprops⟩
  rcases hprops with ⟨hw, hm⟩
  rcases hm with ⟨hm, hS⟩
  rcases hS with ⟨hS, hr⟩
  rcases hr with ⟨hrise, hc3⟩
  exact ⟨cp.1, cp.2, hw, hm, hS, hrise, hc3⟩

/-- Conversely, every `CycleQb8Input` really does determine a positive
repeat of the accelerated orbit of `7`.  The `hcycle` field supplies
the concrete cycle-word parameters, while `hclosed` supplies the
endpoint equality. -/
theorem cycleQb8Input_imp_orbit_cycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    OrbitCycle 7 := by
  rcases cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  have hp : 1 ≤ p := by
    have hlen : w.length = p := by
      rw [hw, cycleWord_length]
    have hP : 2 ≤ w.length := cycleQb8Input_length_ge_two h
    omega
  have hclosed : StringFlow.Word.wordOrbit (cycleWord c p)
      (fiveXPlusOneOrbit 7 c) = fiveXPlusOneOrbit 7 c := by
    simpa [hw, hm] using h.hclosed
  have horbit : fiveXPlusOneOrbit 7 (c + p) = fiveXPlusOneOrbit 7 c := by
    rw [← cycleWord_orbit_eq c p]
    exact hclosed
  exact ⟨c + p, c, by omega, horbit.symm⟩

/-- Absence of a positive orbit repeat is equivalent to absence of all
`CycleQb8Input` packages.  Both directions use concrete bridges, so a
universal proposition over `CycleQb8Input` may be vacuous precisely
when the desired no-cycle conclusion is already true. -/
theorem no_orbit_cycle_iff_no_cycleQb8Input :
    (¬ OrbitCycle 7) ↔
      (∀ m S P : Nat, ∀ w rise c3 : List Nat,
        ¬ CycleQb8Input m S P w rise c3) := by
  constructor
  · intro hno m S P w rise c3 hinput
    exact hno (cycleQb8Input_imp_orbit_cycle hinput)
  · intro hno hcycle
    rcases orbit_cycle_imp_cycle_qb8_input hcycle with
      ⟨_c, P, m, S, w, rise, c3, hinput, _hw, _hrise, _hc3, _hS, _hm⟩
    exact hno m S P w rise c3 hinput

/-- A `CycleQb8Input` is anchored at a rise start, so its first
step weight is `1` or `2`. -/
theorem cycleQb8Input_rise_start
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    w.getI 0 = 1 ∨ w.getI 0 = 2 :=
  h.hrise_start

/-- Weak comparison `5^P < 2^S` follows from the positive PMI cycle
equation via `cycleWord_weight_gt_five_pow`.  It is the weak budget
input used by the hfail rank target; it is not the rejected strict
global comparison (6). -/
theorem cycleQb8Input_weak_comparison
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    5 ^ P < 2 ^ S := by
  rcases cycleQb8Input_cycle_params h with ⟨c, p, hw, hm, hS, _hrise, _hc3⟩
  have hclosed : StringFlow.Word.wordOrbit (cycleWord c p) (fiveXPlusOneOrbit 7 c) =
      fiveXPlusOneOrbit 7 c := by
    simpa [hw, hm] using h.hclosed
  have hp : 1 ≤ p := by
    have hlen : w.length = p := by rw [hw, cycleWord_length]
    have hP : 2 ≤ w.length := cycleQb8Input_length_ge_two h
    omega
  have hlt := cycleWord_weight_gt_five_pow c p hclosed hp
  have hP : P = p := by
    rw [← h.hlength, hw, cycleWord_length]
  calc
    5 ^ P = 5 ^ p := by rw [hP]
    _ < 2 ^ wordWeight (cycleWord c p) := hlt
    _ = 2 ^ S := by rw [hS]

/-- A valid word step from a positive state stays positive. -/
theorem wordOrbit_pos_of_wordValid (w : List Nat) (x : Nat) (hx : 0 < x) :
    StringFlow.Word.wordValid w x → 0 < StringFlow.Word.wordOrbit w x := by
  induction w generalizing x with
  | nil => simpa [StringFlow.Word.wordValid, StringFlow.Word.wordOrbit]
  | cons t ts ih =>
      intro hv
      have hqpos : 0 < (5 * x + 1) / 2 ^ t := by
        have hmod : (5 * x + 1) % 2 ^ t = 0 := hv.1
        have hdvd : 2 ^ t ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
        have hpos1 : 0 < 5 * x + 1 := by positivity
        have hle : 2 ^ t ≤ 5 * x + 1 := Nat.le_of_dvd hpos1 hdvd
        exact Nat.div_pos hle (Nat.pow_pos (by decide))
      simpa [StringFlow.Word.wordOrbit] using
        ih ((5 * x + 1) / 2 ^ t) hqpos hv.2

/-- A closed QB-8 input is anchored at a cyclic rise boundary: the
last cyclic entry before position `0` is a C3 step.  This follows
because the start state is the global minimum of the cycle, so the
last step back to it cannot be a rise step. -/
theorem cycleQb8Input_last_step_c3
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) : 3 ≤ w.getI (P - 1) := by
  have hP2 : 2 ≤ P := cycleQb8Input_P_ge_two h
  by_contra hnot
  have hle2 : w.getI (P - 1) ≤ 2 := by omega
  let r := StringFlow.Word.wordOrbit (w.take (P - 1)) m
  have hlast_lt : P - 1 < w.length := by
    rw [h.hlength]
    omega
  have hr_pos : 0 < r := by
    dsimp [r]
    have hvalid_prefix : StringFlow.Word.wordValid (w.take (P - 1)) m := by
      have hsplit : w.take (P - 1) ++ w.drop (P - 1) = w :=
        List.take_append_drop (P - 1) w
      have hv : StringFlow.Word.wordValid
          (w.take (P - 1) ++ w.drop (P - 1)) m := by
        rw [hsplit]
        exact h.hvalid
      exact ((S6Audit.wordValid_append (w.take (P - 1)) (w.drop (P - 1)) m).mp hv).1
    exact wordOrbit_pos_of_wordValid (w.take (P - 1)) m h.hm_pos hvalid_prefix
  have ht : twoValuation (5 * r + 1) = w.getI (P - 1) := by
    dsimp [r]
    exact h.hexact (P - 1) hlast_lt
  have ht_le : twoValuation (5 * r + 1) ≤ 2 := by
    rwa [ht]
  have hgt : r < StringFlow.fiveXPlusOneStep r :=
    fiveXPlusOneStep_gt_of_weight_le_two r hr_pos ht_le
  have hmin : m ≤ r := by
    dsimp [r]
    have hP : P - 1 < P := by omega
    exact h.hglobal_min (P - 1) hP
  have hstep : StringFlow.fiveXPlusOneStep r = m := by
    dsimp [r]
    have htake : w.take P = w := by
      exact List.take_of_length_le (by rw [h.hlength])
    have hsucc := wordOrbit_take_succ w m (P - 1) hlast_lt
    have hsub : P - 1 + 1 = P := by omega
    rw [hsub] at hsucc
    rw [← ht] at hsucc
    rw [htake] at hsucc
    rw [h.hclosed] at hsucc
    exact hsucc.symm
  have hlt : r < m := by
    calc
      r < StringFlow.fiveXPlusOneStep r := hgt
      _ = m := hstep
  omega

/-- Every closed QB-8 input has a rise index whose next state is
`3 mod 5` or `4 mod 5`. -/
theorem cycleQb8Input_exists_block_head_mod_five
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3) :
    ∃ j : Nat, j < w.length ∧
      ((StringFlow.Word.wordOrbit (w.take (j + 1)) m) % 5 = 3 ∨
       (StringFlow.Word.wordOrbit (w.take (j + 1)) m) % 5 = 4) := by
  rcases cycleQb8Input_exists_rise_index h with ⟨j, hjlt, hj12⟩
  let r := StringFlow.Word.wordOrbit (w.take j) m
  let rj := StringFlow.Word.wordOrbit (w.take (j + 1)) m
  have hstep := wordOrbit_take_succ w m j hjlt
  have hex : twoValuation (5 * r + 1) = w.getI j := by
    dsimp [r]
    exact h.hexact j hjlt
  have hmod := rise_step_next_mod_five r (w.getI j) hj12 hex
  refine ⟨j, hjlt, ?_⟩
  rcases hj12 with hj1 | hj2
  · left
    have hmod' : rj % 5 = 3 := by
      dsimp [rj]
      rw [hstep, hj1]
      dsimp [r] at hmod
      rw [hj1] at hmod
      exact hmod
    exact hmod'
  · right
    have hmod' : rj % 5 = 4 := by
      dsimp [rj]
      rw [hstep, hj2]
      dsimp [r] at hmod
      rw [hj2] at hmod
      exact hmod
    exact hmod'

/-- The five-power numerator determined by a local block head and the
reset parameters.  For the `t=1,δ=1` case this is
`2*rj - 5^j + 4`; the leading addition avoids a second Nat
subtraction in the definition. -/
def localResetNumerator (t j rj δ : Nat) : Nat :=
  2 ^ t * rj + 4 - δ * 5 ^ j

/-- A real terminal is locally compatible with a block head when its
`s*5^(k+1)` exactly equals the numerator
`2^t*rj - δ*5^j + 4`.  The extra factor of `5` is the one appearing
as `5^(k+1)*s - 4` in the document's definition of `B`. -/
def IsLocalResetTerminal (t j rj δ : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal) : Prop :=
  rt.s * 5 ^ (rt.k + 1) = localResetNumerator t j rj δ

/-- The local construction of the document 36.30.8.2 identity from the
block-head representation and the single reset-step scalar equation.
The scalar equation is the undivided local relation between the real
previous terminal and the block head. -/
theorem local_hident_of_reset_scalar
    (j Wp Wj q Aj rj s k t δ : Nat)
    (hW : Wj = Wp + t)
    (hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hscalar : 2 ^ t * rj = 5 ^ (k + 1) * s - 4 + δ * 5 ^ j) :
    Aj + 5 ^ j * q =
      2 ^ Wp * (5 ^ (k + 1) * s - 4 + δ * 5 ^ j) := by
  have hmul : 2 ^ Wj * rj = Aj + 5 ^ j * q := by
    rw [hrj]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)
  have hpow : 2 ^ Wj = 2 ^ Wp * 2 ^ t := by
    rw [hW, Nat.pow_add]
  calc
    Aj + 5 ^ j * q = 2 ^ Wj * rj := hmul.symm
    _ = (2 ^ Wp * 2 ^ t) * rj := by rw [hpow]
    _ = 2 ^ Wp * (2 ^ t * rj) := by ring
    _ = 2 ^ Wp * (5 ^ (k + 1) * s - 4 + δ * 5 ^ j) := by rw [hscalar]

/-- The local terminal equation recovers the undivided scalar equation
`2^t*rj = 5^(k+1)*s - 4 + δ*5^j` from
`rt.s * 5^(rt.k+1) = 2^t*rj - δ*5^j + 4`. -/
theorem local_reset_scalar_of_angelina_terminal
    (t j rj δ : Nat) (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hterm : IsLocalResetTerminal t j rj δ rt) :
    2 ^ t * rj = 5 ^ (rt.k + 1) * rt.s - 4 + δ * 5 ^ j := by
  unfold IsLocalResetTerminal localResetNumerator at hterm
  have hspos : 0 < rt.s := by
    have hodd : rt.s % 2 = 1 := rt.hs_odd
    by_contra hnot
    have hz : rt.s = 0 := by omega
    rw [hz] at hodd
    norm_num at hodd
  let N := rt.s * 5 ^ (rt.k + 1)
  let A := 2 ^ t * rj
  let C := δ * 5 ^ j
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.mul_pos hspos
      (Nat.pow_pos (by decide : 0 < 5) : 0 < 5 ^ (rt.k + 1))
  have hs1 : 1 ≤ rt.s := Nat.succ_le_of_lt hspos
  have hpow5 : 5 ≤ 5 ^ (rt.k + 1) := by
    have hle : 1 ≤ rt.k + 1 := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 5) hle
    simpa using hpow
  have hNge4 : 4 ≤ N := by
    dsimp [N]
    nlinarith [hs1, hpow5]
  have hterm' : N = A + 4 - C := by
    simpa [N, A, C] using hterm
  have hC_le : C ≤ A + 4 := by
    by_contra hnot
    have hlt : A + 4 < C := by omega
    have hsub : A + 4 - C = 0 := by omega
    rw [hsub] at hterm'
    omega
  have hsum : A + 4 = N + C := by omega
  have hgoal : A = N - 4 + C := by
    have hA_eq : A = N + C - 4 :=
      (Nat.sub_eq_of_eq_add (a := N + C) (b := 4) (c := A) hsum.symm).symm
    have hshift' : C + N - 4 = C + (N - 4) :=
      Nat.add_sub_assoc hNge4 C
    have hshift : N + C - 4 = N - 4 + C := by
      simpa [Nat.add_comm] using hshift'
    rw [hA_eq, hshift]
  simpa [N, A, C, Nat.mul_comm] using hgoal

/-- For an admissible reset branch, the local terminal equation is
exactly the reset-head equation for the same real terminal.  Thus
`hterm` is not an additional valuation hypothesis: its remaining
content is precisely that the boundary terminal's own `s,k` reset to
the chosen block head. -/
theorem isLocalResetTerminal_iff_resetHeadEq
    (t j rj δ : Nat) (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3)) :
    IsLocalResetTerminal t j rj δ rt ↔
      S6Audit.ResetHeadEq rt.s j rt.k t δ rj := by
  have hspos : 0 < rt.s := by
    have hodd : rt.s % 2 = 1 := rt.hs_odd
    omega
  have hpow5 : 5 ≤ 5 ^ (rt.k + 1) := by
    have hle : 1 ≤ rt.k + 1 := by omega
    simpa using Nat.pow_le_pow_right (by decide : 0 < 5) hle
  have hprod4 : 4 ≤ 5 ^ (rt.k + 1) * rt.s := by
    have hs1 : 1 ≤ rt.s := by omega
    nlinarith
  constructor
  · intro hterm
    have hscalar := local_reset_scalar_of_angelina_terminal
      t j rj δ rt hterm
    rcases ht with ht1 | ht2
    · have hδ1 : δ = 1 := hδ.1 ht1
      left
      refine ⟨ht1, hδ1, ?_⟩
      subst t
      subst δ
      norm_num at hscalar ⊢
      omega
    · have hδ13 : δ = 1 ∨ δ = 3 := hδ.2 ht2
      right
      refine ⟨ht2, hδ13, ?_⟩
      subst t
      norm_num at hscalar ⊢
      omega
  · intro hreset
    unfold IsLocalResetTerminal localResetNumerator
    rcases hreset with h1 | h2
    · rcases h1 with ⟨ht1, hδ1, heq⟩
      subst t
      subst δ
      norm_num at heq ⊢
      rw [Nat.mul_comm]
      omega
    · rcases h2 with ⟨ht2, _hδ13, heq⟩
      subst t
      norm_num at heq ⊢
      rw [Nat.mul_comm]
      omega

/-- Given the local block-head representation and a locally compatible
real terminal, construct the exact 36.30.8.2 identity.  The terminal
`rt.s` and `rt.k` are determined by the local numerator
`2^t*rj - δ*5^j + 4`, not by an unrelated global previous terminal. -/
theorem local_hident_of_angelina_terminal
    (j Wp Wj q Aj rj t δ : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hW : Wj = Wp + t)
    (hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hterm : IsLocalResetTerminal t j rj δ rt) :
    Aj + 5 ^ j * q =
      2 ^ Wp * (5 ^ (rt.k + 1) * rt.s - 4 + δ * 5 ^ j) := by
  have hscalar := local_reset_scalar_of_angelina_terminal t j rj δ rt hterm
  exact local_hident_of_reset_scalar
    j Wp Wj q Aj rj rt.s rt.k t δ hW hrj hdiv hscalar

/-- The explicit 36.30.8.2 quotient form
`q = m + δ*2^Wp`, `m < 2^Wp`.  This is the document's integrality
reduction; it is obtained from the local `hident` by the already proved
`S6Audit.reset_q0_form`. -/
theorem local_hident_q_form
    (j Wp Wj q Aj rj t δ : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hW : Wj = Wp + t)
    (hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0)
    (hterm : IsLocalResetTerminal t j rj δ rt)
    (hA : Aj < 5 ^ j)
    (hB : 0 < 5 ^ (rt.k + 1) * rt.s - 4)
    (hBlt : 5 ^ (rt.k + 1) * rt.s - 4 < 5 ^ j)
    (hδ : δ = 1 ∨ δ = 3) :
    ∃ m : Nat, q = m + δ * 2 ^ Wp ∧ m < 2 ^ Wp := by
  have hident := local_hident_of_angelina_terminal
    j Wp Wj q Aj rj t δ rt hW hrj hdiv hterm
  exact S6Audit.reset_q0_form j Wp δ Aj q
    (5 ^ (rt.k + 1) * rt.s - 4) hA hB hBlt hδ hident

/-- Local block data that has already been written in document 36.30.8.2.
The `hterm` field says that the real terminal is locally compatible:
`rt.s * 5^(rt.k+1)` is the local numerator
`2^t*rj - δ*5^j + 4`.  This is the undivided input used to construct the
exact identity `A_j + 5^j*q = 2^Wp*(B + δ*5^j)`. -/
structure LocalHidentBlock
    (j Wp Wj q Aj rj t δ : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal) : Prop where
  hW : Wj = Wp + t
  ht : t = 1 ∨ t = 2
  hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3)
  hrj : rj = (Aj + 5 ^ j * q) / 2 ^ Wj
  hdiv : (Aj + 5 ^ j * q) % 2 ^ Wj = 0
  hterm : IsLocalResetTerminal t j rj δ rt
  hk : rt.k + 1 ≤ j
  hs_lt : rt.s < 5 ^ (j - rt.k - 1)
  hrj_odd : S6Audit.IsOdd rj
  hrj_reach : S6Audit.FullOrbitFrom7 rj

/-- Once the local 36.30.8.2 identity is available, it generates both
the reset-head equation and the corrected reset-window reachability
witness.  This is the exact wiring requested for
`cycleQb8Input_exists_block_reset_head`: no parameter is filled by
hand; `s`, `j`, `k`, `t`, and `δ` are all taken from `LocalHidentBlock`
and the single real terminal `rt`. -/
theorem local_hident_to_reset_reachability
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : LocalHidentBlock j Wp Wj q Aj rj t δ rt) :
    S6Audit.ResetHeadEq rt.s j rt.k t δ rj ∧
      S6Audit.ResetWindowReachability j rt.k t δ rt.s := by
  have hpos_s : 0 < rt.s := by
    have hodd : rt.s % 2 = 1 := rt.hs_odd
    by_contra hnot
    have hz : rt.s = 0 := by omega
    rw [hz] at hodd
    norm_num at hodd
  have hreset : S6Audit.ResetHeadEq rt.s j rt.k t δ rj :=
    have hident := local_hident_of_angelina_terminal
      j Wp Wj q Aj rj t δ rt d.hW d.hrj d.hdiv d.hterm
    S6Audit.reset_head_eq_of_block_head_identity
      j Wp Wj q Aj rj rt.s rt.k t δ hpos_s d.hW d.ht d.hδ d.hrj d.hdiv hident
  have hs_lt' : rt.s < 5 ^ (j - 1 - rt.k) := by
    have hsub : j - rt.k - 1 = j - 1 - rt.k := by omega
    simpa [hsub] using d.hs_lt
  refine ⟨hreset, ?_⟩
  refine ⟨rt.r, rj, d.hk, ?_, rt.hs_odd, rt.hs_not_five, hs_lt',
    rt.hreach, hreset, d.hrj_odd, d.hrj_reach⟩
  exact rt.hprod

/-- The local `hident` also gives the explicit quotient form
`q = m + δ*2^Wp` with `m < 2^Wp`.  The extra size bound
`A_j < 5^j` is the only input not already in `LocalHidentBlock`; it is
the usual word-numerator bound from the local `{1,2}` suffix. -/
theorem local_hident_block_q_form
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (hA : Aj < 5 ^ j) :
    ∃ m : Nat, q = m + δ * 2 ^ Wp ∧ m < 2 ^ Wp := by
  have hspos : 0 < rt.s := by
    have hodd : rt.s % 2 = 1 := rt.hs_odd
    by_contra hnot
    have hz : rt.s = 0 := by omega
    rw [hz] at hodd
    norm_num at hodd
  have hs1 : 1 ≤ rt.s := Nat.succ_le_of_lt hspos
  have hpow5 : 5 ≤ 5 ^ (rt.k + 1) := by
    have hle : 1 ≤ rt.k + 1 := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 5) hle
    simpa using hpow
  have hprod_ge5 : 5 ≤ 5 ^ (rt.k + 1) * rt.s := by
    have hmul := Nat.mul_le_mul hpow5 hs1
    simpa using hmul
  have hBpos : 0 < 5 ^ (rt.k + 1) * rt.s - 4 := by
    omega
  have hBlt : 5 ^ (rt.k + 1) * rt.s - 4 < 5 ^ j := by
    have hsub : j - rt.k - 1 = j - (rt.k + 1) := by omega
    have hlt := d.hs_lt
    have hlt' : rt.s < 5 ^ (j - (rt.k + 1)) := by
      simpa [hsub] using hlt
    have hmul : 5 ^ (rt.k + 1) * rt.s <
        5 ^ (rt.k + 1) * 5 ^ (j - (rt.k + 1)) :=
      Nat.mul_lt_mul_of_pos_left hlt'
        (Nat.pow_pos (by decide : 0 < 5) : 0 < 5 ^ (rt.k + 1))
    have hpowadd : 5 ^ (rt.k + 1) * 5 ^ (j - (rt.k + 1)) = 5 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      exact Nat.add_sub_of_le d.hk
    have hmul' : 5 ^ (rt.k + 1) * rt.s < 5 ^ j := by
      simpa [hpowadd] using hmul
    exact Nat.sub_lt_of_lt hmul'
  have hδall : δ = 1 ∨ δ = 3 := by
    rcases d.ht with h1 | h2
    · left
      exact d.hδ.1 h1
    · exact d.hδ.2 h2
  have hident := local_hident_of_angelina_terminal
    j Wp Wj q Aj rj t δ rt d.hW d.hrj d.hdiv d.hterm
  exact S6Audit.reset_q0_form j Wp δ Aj q
    (5 ^ (rt.k + 1) * rt.s - 4) hA hBpos hBlt hδall hident

/-- Assemble a `LocalHidentBlock` from a concrete cycle-word segment,
its last step, and a locally compatible real terminal.  The local
`A_j,q,Wp,Wj,rj` are taken from
`cycleQb8Input_local_block_data`; no local coordinate is guessed. -/
theorem cycleQb8Input_local_hident_block
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (b L t δ : Nat) (hL : 1 ≤ L) (hbL : b + L ≤ w.length)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (ht : t = 1 ∨ t = 2)
    (hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3))
    (hlast : w.getI (b + L - 1) = t)
    (hterm : IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) δ rt)
    (hk : rt.k + 1 ≤ L)
    (hslt : rt.s < 5 ^ (L - rt.k - 1))
    (hrj_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (b + L)) m))
    (hrj_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit (w.take (b + L)) m)) :
    ∃ q Aj Wp Wj : Nat,
      LocalHidentBlock L Wp Wj q Aj
        (StringFlow.Word.wordOrbit (w.take (b + L)) m) t δ rt := by
  rcases cycleQb8Input_local_block_data h b L hL hbL with
    ⟨q, Aj, Wp, Wj, t0, rj, hq, hrj, hAj, hWj, hWp, ht0, hW, hEq,
      hdiv, hrjform⟩
  have ht_eq : t0 = t := by omega
  rw [ht_eq] at hW
  have hrjform' :
      StringFlow.Word.wordOrbit (w.take (b + L)) m =
        (Aj + 5 ^ L * q) / 2 ^ Wj := by
    exact hrj.symm.trans hrjform
  refine ⟨q, Aj, Wp, Wj, ?_⟩
  exact {
    hW := hW
    ht := ht
    hδ := hδ
    hrj := hrjform'
    hdiv := hdiv
    hterm := hterm
    hk := hk
    hs_lt := hslt
    hrj_odd := hrj_odd
    hrj_reach := hrj_reach
  }

/-- A reset-head failure window: parameters matching
`BlockAutomaton.decisiveWindowValuationBoundCorrected`, with the
block-head valuation one above the decisive upper bound.  The window is
tied to the concrete QB-8 word input: it must occur at a proper depth of
that word, and it must carry real orbit reachability
(`hreach : S6Audit.FullIsGloballyReachableCorrected`), so a global
arithmetic witness cannot satisfy the step-3 statement. -/
structure FailureWindow (m S P : Nat) (w rise c3 : List Nat)
    (j k0 t δ s : Nat) : Prop where
  hinput : CycleQb8Input m S P w rise c3
  hj_lt : j < P
  ht : t = 1 ∨ t = 2
  hincoming : w.getI (j - 1) = t
  hδ : (t = 1 → δ = 1) ∧ (t = 2 → δ = 1 ∨ δ = 3)
  hreset : S6Audit.ResetHeadEq s j k0 t δ
    (StringFlow.Word.wordOrbit (w.take j) m)
  hreach : S6Audit.ResetWindowReachability j k0 t δ s
  hs_odd : s % 2 = 1
  hs_not_five : ¬ 5 ∣ s
  hk : k0 + 1 ≤ j
  hs_lt : s < 5 ^ (j - k0 - 1)
  hfail_t1 : t = 1 → 2 * j + 12 ≤
    twoValuation (5 ^ (k0 + 1) * s + 5 ^ j - 2)
  hfail_t2 : t = 2 → 2 * j + 11 ≤
    twoValuation (5 ^ (k0 + 1) * s + δ * 5 ^ j)

/-- Once a `LocalHidentBlock` is written at the same global depth `j`
as `wordOrbit (w.take j) m`, the reset reachability theorem supplies the
two reachability fields of `FailureWindow`.  The failure lower bounds
remain the separate block-budget input. -/
theorem local_hident_to_global_failure_window
    {m S P : Nat} {w rise c3 : List Nat}
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (h : CycleQb8Input m S P w rise c3)
    (hj_lt : j < P)
    (hrj_eq : rj = StringFlow.Word.wordOrbit (w.take j) m)
    (hincoming : w.getI (j - 1) = t)
    (d : LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (hfail_t1 : t = 1 → 2 * j + 12 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ j - 2))
    (hfail_t2 : t = 2 → 2 * j + 11 ≤
      twoValuation (5 ^ (rt.k + 1) * rt.s + δ * 5 ^ j)) :
    FailureWindow m S P w rise c3 j rt.k t δ rt.s := by
  rcases local_hident_to_reset_reachability d with ⟨hreset, hreach⟩
  exact {
    hinput := h
    hj_lt := hj_lt
    ht := d.ht
    hincoming := hincoming
    hδ := d.hδ
    hreset := by
      rw [← hrj_eq]
      exact hreset
    hreach := hreach
    hs_odd := rt.hs_odd
    hs_not_five := rt.hs_not_five
    hk := d.hk
    hs_lt := d.hs_lt
    hfail_t1 := hfail_t1
    hfail_t2 := hfail_t2
  }

/-- Open step-3 statement: every closed QB-8 word has a failure
window block. This is the remaining analytic core; it is
intentionally not proved here. -/
def failureWindowExistence : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ j k0 t δ s : Nat, FailureWindow m S P w rise c3 j k0 t δ s

/-- Step-4 `t=2` algebra: the failure lower bound and the window
upper bound contradict. -/
theorem failure_window_contradicts_t2 (j _k0 _δ _s v : Nat)
    (hfail : 2 * j + 11 ≤ v)
    (hwin : v ≤ 2 * j + 10) : False := by omega

/-- Step-4 `t=1` algebra: the failure lower bound and the window
upper bound contradict. -/
theorem failure_window_contradicts_t1 (j _k0 _s v : Nat)
    (hfail : 2 * j + 12 ≤ v)
    (hwin : v ≤ 2 * j + 11) : False := by omega

/-- INVALID: this theorem consumes the disproved unconstrained
`decisiveWindowValuationBound`.  It is kept only for the audit trail;
downstream bridge code must use
`failure_window_contradicts_window_corrected` instead. -/
theorem failure_window_contradicts_window_invalid
    (hwin : BlockAutomaton.decisiveWindowValuationBound)
    {m S P : Nat} {w rise c3 : List Nat} {j k0 t δ s : Nat}
    (fw : FailureWindow m S P w rise c3 j k0 t δ s) : False := by
  rcases fw.ht with ht1 | ht2
  · have hδ1 : δ = 1 := fw.hδ.1 ht1
    subst δ
    subst t
    have hb := hwin.2 j k0 (j - k0 - 1) s rfl fw.hs_odd fw.hs_not_five
    have hf := fw.hfail_t1 rfl
    exact failure_window_contradicts_t1 j k0 s
      (BlockAutomaton.t1WindowValue j k0 s) hf hb
  · have hδ := fw.hδ.2 ht2
    rcases hδ with hd1 | hd3
    · subst t
      subst δ
      have hb := hwin.1 j k0 (j - k0 - 1) 1 s rfl (Or.inl rfl)
        fw.hs_odd fw.hs_not_five
      have hf := fw.hfail_t2 rfl
      exact failure_window_contradicts_t2 j k0 1 s
        (BlockAutomaton.t2WindowValue j k0 1 s) hf hb
    · subst t
      subst δ
      have hb := hwin.1 j k0 (j - k0 - 1) 3 s rfl (Or.inr rfl)
        fw.hs_odd fw.hs_not_five
      have hf := fw.hfail_t2 rfl
      exact failure_window_contradicts_t2 j k0 3 s
        (BlockAutomaton.t2WindowValue j k0 3 s) hf hb

/-- A failure window contradicts the corrected decisive window
valuation bound.  The reachability field `fw.hreach` supplies exactly
the block-head/previous-terminal constraints that the corrected bound
requires. -/
theorem failure_window_contradicts_window_corrected
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    {m S P : Nat} {w rise c3 : List Nat} {j k0 t δ s : Nat}
    (fw : FailureWindow m S P w rise c3 j k0 t δ s) : False := by
  rcases fw.ht with ht1 | ht2
  · have hδ1 : δ = 1 := fw.hδ.1 ht1
    subst δ
    have hb : BlockAutomaton.t1WindowValue j k0 s ≤ 2 * j + 11 :=
      hwin.2 j k0 (j - k0 - 1) t s rfl ht1 fw.hreach
    have hf := fw.hfail_t1 ht1
    exact failure_window_contradicts_t1 j k0 s
      (BlockAutomaton.t1WindowValue j k0 s) hf hb
  · have hδ := fw.hδ.2 ht2
    rcases hδ with hd1 | hd3
    · have hδ1 : δ = 1 := hd1
      subst δ
      have hb : BlockAutomaton.t2WindowValue j k0 1 s ≤ 2 * j + 10 :=
        hwin.1 j k0 (j - k0 - 1) t 1 s rfl ht2 (Or.inl rfl) fw.hreach
      have hf := fw.hfail_t2 ht2
      exact failure_window_contradicts_t2 j k0 1 s
        (BlockAutomaton.t2WindowValue j k0 1 s) hf hb
    · have hδ3 : δ = 3 := hd3
      subst δ
      have hb : BlockAutomaton.t2WindowValue j k0 3 s ≤ 2 * j + 10 :=
        hwin.1 j k0 (j - k0 - 1) t 3 s rfl ht2 (Or.inr rfl) fw.hreach
      have hf := fw.hfail_t2 ht2
      exact failure_window_contradicts_t2 j k0 3 s
        (BlockAutomaton.t2WindowValue j k0 3 s) hf hb

/-- Audit: the old unconstrained failure-window parameters already
have a global arithmetic witness, which is why `FailureWindow` must
carry the concrete QB-8 word input and a proper depth `j < P`. -/
theorem arithmetic_failure_window_witness :
    ∃ j k0 t δ s : Nat,
      t = 2 ∧ δ = 3 ∧ k0 + 1 ≤ j ∧ s % 2 = 1 ∧ ¬ 5 ∣ s ∧
      s < 5 ^ (j - k0 - 1) ∧
      2 * j + 11 ≤ twoValuation (5 ^ (k0 + 1) * s + δ * 5 ^ j) := by
  let s : Nat := 940257419896922313665033
  refine ⟨36, 0, 2, 3, s, rfl, rfl, by norm_num, ?_, ?_, ?_, ?_⟩
  · norm_num [s]
  · norm_num [s]
  · norm_num [s]
  · have hN : 5 * s + 3 * 5 ^ 36 = 5 * 2 ^ 83 := by norm_num [s]
    have hodd5 : (5 : Nat) % 2 = 1 := by norm_num
    have hv : twoValuation (5 * 2 ^ 83) = 83 := by
      rw [Nat.mul_comm]
      exact StringFlow.Lte.twoValuation_mul_two_pow_eq 83 5 hodd5
    have hval : twoValuation (5 * s + 3 * 5 ^ 36) = 83 := by
      rw [hN]
      simpa using hv
    have hgoal : 83 ≤ twoValuation (5 * s + 3 * 5 ^ 36) := by
      rw [hval]
    simpa using hgoal

/-- Audit: the unconstrained `decisiveWindowValuationBound` is false;
the real window theorem must carry a block-head reachability input. -/
theorem decisiveWindowValuationBound_contradiction :
    ¬ BlockAutomaton.decisiveWindowValuationBound := by
  rcases arithmetic_failure_window_witness with
    ⟨j, k0, t, δ, s, ht, hδ, hk, hodd, hfive, hlt, hfail⟩
  subst t
  subst δ
  intro hwin
  have hb := hwin.1 j k0 (j - k0 - 1) 3 s rfl (Or.inr rfl) hodd hfive
  unfold BlockAutomaton.t2WindowValue at hb
  omega

/-- OPEN: the arithmetic failure witness should not satisfy the
corrected reachability input.  This is the missing formal target for
Task 2.2; it is deliberately not declared as a theorem because no proof
is available yet. -/
def arithmeticFailureWitnessNotCorrected : Prop :=
  ¬ S6Audit.ResetWindowReachability 36 0 2 3 (2^83 - 3 * 5^35)

/-- Once the bridge `windowBoundToNoCycle` is closed, the window bound
alone gives no positive cycle. -/
theorem no_cycle_of_window_bound
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hbridge : windowBoundToNoCycle) :
    ¬ OrbitCycle 7 :=
  hbridge hwin

/-- The final bridge is closed once step 3 supplies a failure window:
every closed QB-8 word admits a `FailureWindow`, and any such window
contradicts the decisive window bound. -/
theorem windowBoundToNoCycle_of_failureWindowExistence
    (hfw : failureWindowExistence) : windowBoundToNoCycle := by
  intro hwin hcycle
  rcases orbit_cycle_imp_cycle_qb8_input hcycle with
    ⟨c, p, m, S, w, rise, c3, hinput, _hw, _hrise, _hc3, _hS, _hm⟩
  have hex := hfw m S p w rise c3 hinput
  rcases hex with ⟨j, k0, t, δ, s, hfw'⟩
  exact failure_window_contradicts_window_corrected hwin hfw'

/-- Conditional final assembly: the window bound plus
`failureWindowExistence` rule out a positive cycle of `7`. -/
theorem no_cycle_of_window_bound_of_failureWindowExistence
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : failureWindowExistence) :
    ¬ OrbitCycle 7 :=
  windowBoundToNoCycle_of_failureWindowExistence hfw hwin

/-- Conditional unboundedness: the window bound plus
`failureWindowExistence` give the final divergence statement. -/
theorem five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hfw : failureWindowExistence) :
    IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7
    (no_cycle_of_window_bound_of_failureWindowExistence hwin hfw)

/-- Once the bridge is closed, the orbit of `7` is unbounded. -/
theorem five_x_plus_one_diverges_at_7_of_window_bound
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected)
    (hbridge : windowBoundToNoCycle) :
    IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 (no_cycle_of_window_bound hwin hbridge)

end CycleBridge

#print axioms StringFlow.CycleBridge.no_cycle_of_window_bound
#print axioms StringFlow.CycleBridge.orbit_cycle_imp_exists_c3_start
#print axioms StringFlow.CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound
#print axioms StringFlow.CycleBridge.cycleWord_wordA_eq_pmi_aTotal
#print axioms StringFlow.CycleBridge.cycleWord_pmi_b_count
#print axioms StringFlow.CycleBridge.cycleWord_pmi_b_no_bad_prefix
#print axioms StringFlow.CycleBridge.failure_window_contradicts_window_invalid
#print axioms StringFlow.CycleBridge.failure_window_contradicts_window_corrected
#print axioms StringFlow.CycleBridge.cycleWord_margin_balance
#print axioms StringFlow.CycleBridge.rise_block_balance
#print axioms StringFlow.CycleBridge.fiveXPlusOneOrbit_not_dvd_five
#print axioms StringFlow.CycleBridge.fiveXPlusOneOrbit_lt_five_pow
#print axioms StringFlow.CycleBridge.orbit_cycle_imp_min_rise_witness
#print axioms StringFlow.CycleBridge.arithmetic_failure_window_witness
#print axioms StringFlow.CycleBridge.decisiveWindowValuationBound_contradiction
#print axioms StringFlow.CycleBridge.windowBoundToNoCycle_of_failureWindowExistence
#print axioms StringFlow.CycleBridge.no_cycle_of_window_bound_of_failureWindowExistence
#print axioms StringFlow.CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window

end StringFlow
