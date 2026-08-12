import Std

/-!
# QB: quantitative Ballot (current spike-structure route)

This module formalizes the algebraic contradiction inside QB-7 and the
monotonicity facts used by QB-8 from `ph_qb_gc_chain.md` sections 8
and 10.  QB-7 is reduced to a cleared rational inequality: with
`q = 2^delta = 2^T / 5^P`, the condition

    (5/4 - q) * m > 1/5

and the exact cycle identity

    2^Delta * (m + theta') = m + theta + 2^(-M) / 5

cannot both hold when the word has an internal step, because then
`2^Delta >= 5/4`.  The theorem `qb7_core` states that contradiction
using only ordered-field facts about `Rat`.

QB-8 then uses the monotonicity of a C3 step (`c3_step_lt`) and of a
rising `t=1/2` step (`rise_step_gt`) to turn the QB-7 rigidity into
the spike structure: C3 starts strictly decrease and the rising
segment strictly increases.
-/

namespace StringFlow.QB

/-- QB-7 condition in terms of `q = 2^delta`: `(5/4 - q)m > 1/5`. -/
def qb7Condition (m q : Rat) : Prop :=
  0 < m ∧ m * q + 1 / 5 < (5 / 4) * m

/-- The contradiction core of QB-7.  Here `f = 2^Delta`,
`x = theta`, `y = theta'`, `e = 2^(-M)/5`, and `heq` is the exact
identity from the cycle. -/
def qb7CoreStatement (m q f x y e : Rat) : Prop :=
  qb7Condition m q ∧ 5 / 4 ≤ f ∧ 0 ≤ f ∧ 0 ≤ y ∧
    m + x ≤ m * q ∧ e ≤ 1 / 5 ∧ f * (m + y) = m + x + e

/-- QB-7: if the condition holds and the word really has an internal
step, the exact identity forces a contradiction. -/
theorem qb7_core (m q f x y e : Rat) (h : qb7CoreStatement m q f x y e) :
    False := by
  rcases h with ⟨hcond0, hf, hf0, hy, hx, he, heq⟩
  rcases hcond0 with ⟨hm, hcond⟩
  have h1 : m + x + e ≤ m * q + 1 / 5 := by
    have hx' : m + x + e ≤ m * q + e := by
      rwa [Rat.add_le_add_right]
    have he' : m * q + e ≤ m * q + 1 / 5 := by
      rwa [Rat.add_le_add_left]
    exact Rat.le_trans hx' he'
  have h2 : m + x + e < (5 / 4) * m := by
    by_cases h : m + x + e < (5 / 4) * m
    · exact h
    · have hCA : (5 / 4) * m ≤ m + x + e := (Rat.not_lt.mp h)
      have hCB : (5 / 4) * m ≤ m * q + 1 / 5 := Rat.le_trans hCA h1
      exact False.elim ((Rat.not_lt.mpr hCB) hcond)
  have h3 : (5 / 4) * m ≤ f * (m + y) := by
    have hmle : 0 ≤ m := Rat.le_of_lt hm
    have h0 : (5 / 4) * m ≤ f * m := by
      exact Rat.mul_le_mul_of_nonneg_right hf hmle
    have hfnon : 0 ≤ f := hf0
    have hmy0 : m + 0 ≤ m + y := (Rat.add_le_add_left).2 hy
    have hmy : m ≤ m + y := by simpa [Rat.add_zero] using hmy0
    have hfm : f * m ≤ f * (m + y) :=
      Rat.mul_le_mul_of_nonneg_left hmy hfnon
    exact Rat.le_trans h0 hfm
  rw [← heq] at h2
  exact (Rat.not_lt.mpr h3) h2

/-- QB-7, in the form used by the structural route: no internal-step
datum can coexist with the exact cycle identity under the QB-7
condition. -/
theorem qb7_no_internal_data (m q : Rat) :
    ∀ f x y e : Rat, qb7CoreStatement m q f x y e → False := by
  intro f x y e h
  exact qb7_core m q f x y e h

/-- One accelerated C3 step: `(5n+1)/2^t`. -/
def c3Step (n t : Nat) : Nat :=
  (5 * n + 1) / 2 ^ t

/-- One rising step: `(5m+1)/2^t` for `t = 1,2`. -/
def riseStep (m t : Nat) : Nat :=
  (5 * m + 1) / 2 ^ t

/-- A C3 step with `n >= 7` and `t >= 3` strictly decreases. -/
theorem c3_step_lt (n t : Nat) (hn : 7 ≤ n) (ht : 3 ≤ t) :
    c3Step n t < n := by
  unfold c3Step
  have hnpos : 0 < n := by omega
  have h8 : 8 ≤ 2 ^ t := by
    have hpow := Nat.pow_le_pow_right (show 0 < 2 by decide) ht
    simpa using hpow
  have h5 : 5 * n + 1 ≤ 6 * n := by omega
  have h6 : 6 * n < 8 * n := by omega
  have h8n : 8 * n ≤ 2 ^ t * n := by
    exact Nat.mul_le_mul_right n h8
  have hlt : 5 * n + 1 < 2 ^ t * n := by omega
  have hpos : 0 < 2 ^ t := Nat.pow_pos (by decide)
  rw [Nat.div_lt_iff_lt_mul hpos]
  have hcomm : n * 2 ^ t = 2 ^ t * n := Nat.mul_comm n (2 ^ t)
  rwa [hcomm]

/-- A rising `t=1/2` step from `m >= 7` strictly increases. -/
theorem rise_step_gt (m t : Nat) (hm : 7 ≤ m) (ht : t = 1 ∨ t = 2) :
    m < riseStep m t := by
  unfold riseStep
  rcases ht with rfl | rfl
  · change m < (5 * m + 1) / 2
    let q := (5 * m + 1) / 2
    change m < q
    by_cases hqle : q ≤ m
    · have hdiv : 2 * q + (5 * m + 1) % 2 = 5 * m + 1 := by
        have h := Nat.div_add_mod (5 * m + 1) 2
        simpa [q, Nat.mul_comm] using h
      have hmod : (5 * m + 1) % 2 < 2 := Nat.mod_lt _ (by decide)
      have hbound : 2 * q + (5 * m + 1) % 2 ≤ 2 * m + 1 := by omega
      have hcontra : 5 * m + 1 ≤ 2 * m + 1 := by
        rw [← hdiv]
        exact hbound
      omega
    · exact Nat.lt_of_not_ge hqle
  · change m < (5 * m + 1) / 4
    let q := (5 * m + 1) / 4
    change m < q
    by_cases hqle : q ≤ m
    · have hdiv : 4 * q + (5 * m + 1) % 4 = 5 * m + 1 := by
        have h := Nat.div_add_mod (5 * m + 1) 4
        simpa [q, Nat.mul_comm] using h
      have hmod : (5 * m + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
      have hbound : 4 * q + (5 * m + 1) % 4 ≤ 4 * m + 3 := by omega
      have hcontra : 5 * m + 1 ≤ 4 * m + 3 := by
        rw [← hdiv]
        exact hbound
      omega
    · exact Nat.lt_of_not_ge hqle

/-- A list is strictly decreasing. -/
def strictlyDecreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => y < x ∧ strictlyDecreasing (y :: xs)

/-- A chain of C3 starts: each next value is the C3 output of the
previous one, and every C3 step has `n >= 7`, `t >= 3`. -/
def c3Chain : List Nat → List Nat → Prop
  | [], _ => True
  | [_], [] => True
  | n :: n' :: ns, t :: ts =>
      n' = c3Step n t ∧ 7 ≤ n ∧ 3 ≤ t ∧ c3Chain (n' :: ns) ts
  | _, _ => False

/-- QB-8: a C3 chain is strictly decreasing. -/
theorem c3_chain_strictlyDecreasing (ns ts : List Nat) (h : c3Chain ns ts) :
    strictlyDecreasing ns := by
  cases ns with
  | nil => simp [strictlyDecreasing]
  | cons n rest =>
      cases rest with
      | nil => simp [strictlyDecreasing]
      | cons n' rest2 =>
          cases ts with
          | nil => simp [c3Chain] at h
          | cons t ts2 =>
              rcases h with ⟨hstep, hn, ht, htail⟩
              simp [strictlyDecreasing]
              constructor
              · rw [hstep]
                exact c3_step_lt n t hn ht
              · exact c3_chain_strictlyDecreasing (n' :: rest2) ts2 htail

/-- All word lengths in a list are `1`. -/
def allOne : List Nat → Prop
  | [] => True
  | l :: ls => l = 1 ∧ allOne ls

/-- The C3 start indices generated from a list of word lengths. -/
def startsFrom (base : Nat) : List Nat → List Nat
  | [] => [base]
  | l :: ls => base :: startsFrom (base + l) ls

/-- A consecutive list of indices starting at `base`. -/
def consecutiveFrom (base : Nat) : Nat → List Nat
  | 0 => [base]
  | n + 1 => base :: consecutiveFrom (base + 1) n

/-- QB-8: if every word after the initial segment has length `1`,
the C3 starts are consecutive. -/
theorem startsFrom_consecutive_of_allOne (base : Nat) (ls : List Nat)
    (h : allOne ls) :
    startsFrom base ls = consecutiveFrom base ls.length := by
  induction ls generalizing base with
  | nil => simp [startsFrom, consecutiveFrom]
  | cons l ls ih =>
      rcases h with ⟨hl, hls⟩
      simp [startsFrom, consecutiveFrom, hl]
      exact ih (base + 1) hls

/-- QB-8, assembled: singleton word lengths give consecutive C3
starts, and the C3 chain is strictly decreasing. -/
theorem qb8_structure (lens ns ts : List Nat)
    (hone : allOne lens) (hchain : c3Chain ns ts) :
    startsFrom 0 lens = consecutiveFrom 0 lens.length ∧
      strictlyDecreasing ns := by
  constructor
  · exact startsFrom_consecutive_of_allOne 0 lens hone
  · exact c3_chain_strictlyDecreasing ns ts hchain

end StringFlow.QB
