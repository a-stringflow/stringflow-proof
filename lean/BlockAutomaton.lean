import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import LteMacro
import S6AuditStage1

/-!
# Block-level carry automaton for the decisive window valuation

This module formalizes the exact digit-by-digit carry automaton used in
`docs/pmi_block_projection.md` section 18.  It does **not** assert the
window valuation; the spectral-radius proposition is still open and is
recorded as a `Prop` definition, not as a theorem.

State `(e,u)` represents a partial value `n = 2^e * u` with `u` odd.
For a base-5 digit `d`, the exact transition is
`n' = 5*n + d`, `e' = v2(n')`, `u' = oddPart(n')`.
-/

namespace StringFlow.BlockAutomaton

/-- One high-to-low base-5 digit step: `n' = 5*n + d`. -/
def digitStep (n d : Nat) : Nat := 5 * n + d

/-- Exact valuation/carry transition: `(v2(5n+d), oddPart(5n+d))`. -/
def valuationStep (e u d : Nat) : Nat × Nat :=
  (twoValuation (digitStep (2 ^ e * u) d),
   oddPart (digitStep (2 ^ e * u) d))

/-- Exactness of `valuationStep`: it preserves the decomposition
`n' = 2^(e') * u'` with `u'` odd. -/
theorem valuationStep_correct (e u d : Nat) (hu : u % 2 = 1) :
    digitStep (2 ^ e * u) d =
      2 ^ (valuationStep e u d).1 * (valuationStep e u d).2 ∧
      (valuationStep e u d).2 % 2 = 1 := by
  unfold valuationStep digitStep
  have hu_ne0 : u ≠ 0 := by
    intro hu0
    subst u
    norm_num at hu
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero hu_ne0
  have htwo : 0 < 2 ^ e := Nat.pow_pos (by decide : (0 : Nat) < 2)
  have hfive : 0 < 5 * (2 ^ e * u) := by
    exact Nat.mul_pos (by decide : 0 < 5) (Nat.mul_pos htwo hu1)
  have hpos : 0 < 5 * (2 ^ e * u) + d := Nat.add_pos_left hfive d
  constructor
  · simpa using StringFlow.n_eq_two_pow_mul_oddPart (5 * (2 ^ e * u) + d) hpos
  · exact StringFlow.oddPart_odd_of_pos (5 * (2 ^ e * u) + d) hpos

/-- Reading the digit `0` multiplies the value by `5`; the valuation is
unchanged and the odd part is multiplied by `5`. -/
theorem valuationStep_zero (e u : Nat) (hu : u % 2 = 1) :
    valuationStep e u 0 = (e, 5 * u) := by
  unfold valuationStep digitStep
  have hodd5u : (5 * u) % 2 = 1 := by
    exact StringFlow.Lte.odd_mul_odd_mod_two 5 u (by decide) hu
  have hfac : 5 * (2 ^ e * u) = 2 ^ e * (5 * u) := by ring
  have hv : twoValuation (5 * (2 ^ e * u)) = e := by
    rw [hfac]
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq e (5 * u) hodd5u
  have hu_ne0 : u ≠ 0 := by
    intro hu0
    subst u
    norm_num at hu
  have hu1 : 1 ≤ u := Nat.pos_of_ne_zero hu_ne0
  have htwo : 0 < 2 ^ e := Nat.pow_pos (by decide : (0 : Nat) < 2)
  have hpos : 0 < 5 * (2 ^ e * u) := by
    exact Nat.mul_pos (by decide : 0 < 5) (Nat.mul_pos htwo hu1)
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * (2 ^ e * u)) hpos
  have hodd : oddPart (5 * (2 ^ e * u)) = 5 * u := by
    rw [hv] at hdec
    have h' : 2 ^ e * (5 * u) = 2 ^ e * oddPart (5 * (2 ^ e * u)) := by
      exact hfac.symm.trans hdec
    have h2pos : 0 < 2 ^ e := Nat.pow_pos (by decide : (0 : Nat) < 2)
    exact Nat.mul_left_cancel h2pos h'.symm
  apply Prod.ext
  · simp [hv]
  · simp [hodd]

/-- Lift event `(e=0,d=1)`: `e' = v2(5u+1)`. -/
theorem valuationStep_lift_e0_d1 (u : Nat) :
    (valuationStep 0 u 1).1 = twoValuation (5 * u + 1) := by
  unfold valuationStep digitStep
  simp

/-- Lift event `(e=0,d=3)`: `e' = v2(5u+3)`. -/
theorem valuationStep_lift_e0_d3 (u : Nat) :
    (valuationStep 0 u 3).1 = twoValuation (5 * u + 3) := by
  unfold valuationStep digitStep
  simp

/-- Lift event `(e=1,d=2)`: `e' = 1+v2(5u+1)`. -/
theorem valuationStep_lift_e1_d2 (u : Nat) :
    (valuationStep 1 u 2).1 = 1 + twoValuation (5 * u + 1) := by
  unfold valuationStep digitStep
  norm_num
  have hfac : 5 * (2 * u) + 2 = 2 * (5 * u + 1) := by ring
  have hpos : 0 < 5 * u + 1 := by positivity
  rw [hfac]
  have hv : twoValuation (2 * (5 * u + 1)) =
      twoValuation (5 * u + 1) + 1 :=
    StringFlow.twoValuation_mul_two (5 * u + 1) hpos
  rw [hv]
  ring

/-- Lift event `(e=2,d=4)`: `e' = 2+v2(5u+1)`. -/
theorem valuationStep_lift_e2_d4 (u : Nat) :
    (valuationStep 2 u 4).1 = 2 + twoValuation (5 * u + 1) := by
  unfold valuationStep digitStep
  norm_num
  have hfac : 5 * (4 * u) + 4 = 4 * (5 * u + 1) := by ring
  have hpos : 0 < 5 * u + 1 := by positivity
  rw [hfac]
  have hv : twoValuation (4 * (5 * u + 1)) =
      2 + twoValuation (5 * u + 1) := by
    rw [show 4 = 2 ^ 2 by norm_num]
    exact StringFlow.Lte.twoValuation_mul_two_pow 2 (5 * u + 1) hpos
  rw [hv]

/-- Run the exact carry automaton over a list of digits (high-to-low). -/
def valuationRun (e u : Nat) (ds : List Nat) : Nat × Nat :=
  ds.foldl (fun st d => valuationStep st.1 st.2 d) (e, u)

/-- The value built by applying `digitStep` to the list. -/
def digitRun (e u : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun n d => digitStep n d) (2 ^ e * u)

/-- The carry automaton is exact on any digit list: the final state still
decomposes the final value as `2^e * u` with `u` odd. -/
theorem valuationRun_correct (e u : Nat) (hu : u % 2 = 1) (ds : List Nat) :
    digitRun e u ds =
      2 ^ (valuationRun e u ds).1 * (valuationRun e u ds).2 ∧
      (valuationRun e u ds).2 % 2 = 1 := by
  induction ds generalizing e u with
  | nil =>
      simp [valuationRun, digitRun, hu]
  | cons d ds ih =>
      have hstep := valuationStep_correct e u d hu
      let n1 := digitStep (2 ^ e * u) d
      let e1 := (valuationStep e u d).1
      let u1 := (valuationStep e u d).2
      have hn1 : n1 = 2 ^ e1 * u1 := by
        dsimp [n1, e1, u1]
        exact hstep.1
      have hu1 : u1 % 2 = 1 := by
        dsimp [u1]
        exact hstep.2
      have hrun : valuationRun e u (d :: ds) = valuationRun e1 u1 ds := by
        simp [valuationRun, e1, u1]
      have hdig : digitRun e u (d :: ds) = digitRun e1 u1 ds := by
        change List.foldl (fun n d => digitStep n d) (digitStep (2 ^ e * u) d) ds =
          List.foldl (fun n d => digitStep n d) (2 ^ e1 * u1) ds
        have hn1' : digitStep (2 ^ e * u) d = 2 ^ e1 * u1 := by
          simpa [n1] using hn1
        rw [hn1']
      rw [hrun, hdig]
      exact ih e1 u1 hu1

/-- Value whose valuation is controlled by the t=2 decisive window. -/
def t2WindowValue (j k0 δ s : Nat) : Nat :=
  twoValuation (5 ^ (k0 + 1) * s + δ * 5 ^ j)

/-- Value whose valuation is controlled by the t=1 decisive window. -/
def t1WindowValue (j k0 s : Nat) : Nat :=
  twoValuation (5 ^ (k0 + 1) * s + 5 ^ j - 2)

/-- Open t=2 window bound. -/
def t2WindowBound (j k0 a δ s : Nat) : Prop :=
  a = j - k0 - 1 → δ = 1 ∨ δ = 3 → s % 2 = 1 → ¬ 5 ∣ s →
  t2WindowValue j k0 δ s ≤ 2 * j + 10

/-- Open t=1 window bound. -/
def t1WindowBound (j k0 a s : Nat) : Prop :=
  a = j - k0 - 1 → s % 2 = 1 → ¬ 5 ∣ s →
  t1WindowValue j k0 s ≤ 2 * j + 11

/-- The decisive window valuation bound, stated as the conjunction of the
two open bounds. This is a definition (statement), not a theorem; the
spectral-radius proof is still open. -/
def decisiveWindowValuationBound : Prop :=
  (∀ j k0 a δ s, t2WindowBound j k0 a δ s) ∧
  (∀ j k0 a s, t1WindowBound j k0 a s)

/-!
INVALID: `decisiveWindowValuationBound` above is the old unconstrained
statement.  It is disproved by
`StringFlow.CycleBridge.decisiveWindowValuationBound_contradiction`
(j=36, k0=0, t=2, δ=3, s=2^83-3*5^35), so it must not be used as a
window-bridge input.  The reachability-carrying statement is
`decisiveWindowValuationBoundCorrected` below.
-/

/-- Corrected t=2 window bound: the same valuation inequality, but only
for reset parameters whose exact `j,k0,t` block has a previous terminal
in the general orbit and a reset head on the full orbit (see
`S6Audit.ResetWindowReachability`). -/
def t2WindowBoundCorrected (j k0 a t delta s : Nat) : Prop :=
  a = j - k0 - 1 ->
  t = 2 ->
  delta = 1 \/ delta = 3 ->
  S6Audit.ResetWindowReachability j k0 t delta s ->
  t2WindowValue j k0 delta s <= 2 * j + 10

/-- Corrected t=1 window bound.  The reachability input carries the
`δ=1` reset-head equation and the previous-terminal/full-orbit
constraints, with the same `j,k0,t` fixed. -/
def t1WindowBoundCorrected (j k0 a t s : Nat) : Prop :=
  a = j - k0 - 1 ->
  t = 1 ->
  S6Audit.ResetWindowReachability j k0 t 1 s ->
  t1WindowValue j k0 s <= 2 * j + 11

/-- The corrected decisive window valuation bound.  This is the only
window-bound statement that downstream bridge theorems may consume. -/
def decisiveWindowValuationBoundCorrected : Prop :=
  ((j k0 a t delta s : Nat) -> t2WindowBoundCorrected j k0 a t delta s) /\
  ((j k0 a t s : Nat) -> t1WindowBoundCorrected j k0 a t s)

end StringFlow.BlockAutomaton
