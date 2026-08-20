import S6Audit
import FBeta

/-!
# Final statement and orbit foundations

This module defines the top-level orbit objects and the already proved
no-cycle-to-unbounded bridge:

- `fiveXPlusOneStep`
- `fiveXPlusOneOrbit`
- `IsUnboundedOrbit`
- `OrbitCycle`
- `unbounded_of_no_cycle`

It contains no `sorry`. The top-level assembly theorem
`five_x_plus_one_diverges_at_7` is deliberately isolated in
`FinalTheorem.lean`; modules such as `CycleBridge` can import this file
without importing that final assembly target.

The step is the full accelerated 5x+1 map:

    fiveXPlusOneStep x = (5x + 1) / 2^(v_2(5x + 1)).

Divergence means that the orbit of `x` is unbounded.
-/

namespace StringFlow

/-- The full accelerated 5x+1 step. -/
def fiveXPlusOneStep (x : Nat) : Nat :=
  (5 * x + 1) / 2 ^ twoValuation (5 * x + 1)

/-- The orbit of `x` under the full accelerated 5x+1 map. -/
def fiveXPlusOneOrbit (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => fiveXPlusOneStep (fiveXPlusOneOrbit x n)

/-- The orbit of `x` is unbounded. -/
def IsUnboundedOrbit (x : Nat) : Prop :=
  ∀ B : Nat, ∃ n : Nat, B ≤ fiveXPlusOneOrbit x n

/-- The orbit of `x` repeats: two distinct times land on the same
state.  A bounded deterministic orbit must eventually repeat. -/
def OrbitCycle (x : Nat) : Prop :=
  ∃ n m : Nat, m < n ∧ fiveXPlusOneOrbit x m = fiveXPlusOneOrbit x n

/-- If the orbit of `x` never repeats, it is unbounded. -/
theorem unbounded_of_no_cycle (x : Nat) (h : ¬ OrbitCycle x) :
    IsUnboundedOrbit x := by
  by_contra hbounded
  have hbounded' : ∃ B : Nat, ∀ n : Nat, fiveXPlusOneOrbit x n < B := by
    rw [IsUnboundedOrbit] at hbounded
    push Not at hbounded
    rcases hbounded with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    exact hB n
  rcases hbounded' with ⟨B, hlt⟩
  obtain ⟨i, j, hij, hjle, heq⟩ :=
    exists_repeat_lt B (fun n => fiveXPlusOneOrbit x n) (fun i _ => hlt i)
  exact h ⟨j, i, hij, heq⟩



/-- The exact accelerated step is a legal word step with the exact
2-adic weight.  This is the bridge between the top-level orbit and the
`wordValid` block framework used by the S6 audit. -/
lemma fiveXPlusOneStep_wordValid (x : Nat) :
    StringFlow.Word.wordValid [twoValuation (5 * x + 1)] x ∧
    StringFlow.Word.wordOrbit [twoValuation (5 * x + 1)] x = fiveXPlusOneStep x := by
  constructor
  · dsimp [StringFlow.Word.wordValid]
    have hx : 0 < 5 * x + 1 := by positivity
    have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hx
    have hodd : StringFlow.oddPart (5 * x + 1) % 2 = 1 :=
      StringFlow.oddPart_odd_of_pos (5 * x + 1) hx
    have hv : twoValuation
        (2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1)) =
        twoValuation (5 * x + 1) := by
      exact StringFlow.Lte.twoValuation_mul_two_pow_eq
        (twoValuation (5 * x + 1)) (StringFlow.oddPart (5 * x + 1)) hodd
    rw [hdec]
    rw [hv]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  · rfl

/-- The exact accelerated step preserves `GeneralOrbitFrom7` reachability. -/
lemma fiveXPlusOneStep_general_orbit (x : Nat) (h : S6Audit.GeneralOrbitFrom7 x) :
    S6Audit.GeneralOrbitFrom7 (fiveXPlusOneStep x) := by
  rcases fiveXPlusOneStep_wordValid x with ⟨hvalid, _⟩
  have hvalid' : (5 * x + 1) % 2 ^ twoValuation (5 * x + 1) = 0 := hvalid.1
  have hstep := S6Audit.general_orbit_step x (twoValuation (5 * x + 1)) hvalid' h
  simpa [fiveXPlusOneStep] using hstep

/-- Every state of the exact accelerated orbit is `GeneralOrbitFrom7`
reachable. -/
lemma fiveXPlusOneOrbit_general_orbit (x : Nat) (h : S6Audit.GeneralOrbitFrom7 x) :
    ∀ n : Nat, S6Audit.GeneralOrbitFrom7 (fiveXPlusOneOrbit x n) := by
  intro n
  induction n with
  | zero => simpa [fiveXPlusOneOrbit] using h
  | succ n ih =>
      have hstep := fiveXPlusOneStep_general_orbit (fiveXPlusOneOrbit x n) ih
      simpa [fiveXPlusOneOrbit] using hstep
end StringFlow
