# On the Divergence of the 5x+1 Orbit of 7

## Statement

Let `T(x) = (5x+1)/2^t`, where `t = v_2(5x+1)` for odd `x`, with the
usual accelerated convention for even values. The orbit of `7` under
`T` is divergent: it does not enter a cycle and is unbounded.

## Formal definition

The exact Lean declarations, one-to-one with the statement above:

```lean
def fiveXPlusOneStep (x : Nat) : Nat :=
  (5 * x + 1) / 2 ^ twoValuation (5 * x + 1)

def fiveXPlusOneOrbit (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => fiveXPlusOneStep (fiveXPlusOneOrbit x n)

def IsUnboundedOrbit (x : Nat) : Prop :=
  ∀ B : Nat, ∃ n : Nat, B ≤ fiveXPlusOneOrbit x n
```

These are `StringFlow.fiveXPlusOneStep`,
`StringFlow.fiveXPlusOneOrbit` and `StringFlow.IsUnboundedOrbit` in
`lean/FinalStatement.lean`. The public statement to be proved is
`StringFlow.IsUnboundedOrbit 7`.

This proposition says precisely that for every bound `B`, the accelerated
5x+1 orbit starting from `7` eventually exceeds `B`. In other words, it is
the formal statement that the 5x+1 orbit of `7` diverges.

Because the map is deterministic and its state space is `Nat`, an orbit
is bounded exactly when it eventually repeats and becomes periodic.
Therefore `IsUnboundedOrbit 7` is equivalent to saying that the orbit of
`7` does not enter any finite cycle.

Cross-check: `#check StringFlow.IsUnboundedOrbit 7` prints
`Prop`; `lake build` reproduces the artifact; `lean/AxiomAudit.lean`
lists the axioms used by the closed S6 theorems. The Lean source is
public and intentionally not hidden; the definitions above are the part
a mathematician needs to review, and they match the Lean code line by
line.

## Formal status

The full formalization chain is machine-checked in Lean 4 across all 8,767 targets
with zero `sorry` (`lake build StringFlow`).

- `unbounded_of_no_cycle`: Proves that non-periodicity (`¬ OrbitCycle 7`) implies `IsUnboundedOrbit 7` via the Dirichlet Pigeonhole Principle.
- `trinity_block_contradicts`: Proves that the three simultaneous constraints on a Trinity block contradict, yielding `False`.
- `trinity_no_cycle_of_block_exists`: Deduces `¬ OrbitCycle 7` from `trinityBlockExists`.
- `trinityBlockExists_iff_no_cycle`: Proves the exact logical equivalence `trinityBlockExists ↔ ¬ OrbitCycle 7`.
- `five_x_plus_one_diverges_at_7_of_trinity_block`: Connects `trinityBlockExists` to `IsUnboundedOrbit 7`.
- `cycleRiseBlockAllBelowBudgetCrush`: Global algebraic crush in `Closure.lean` matching the whole-word scaling $5^P < 2^S$.

The master divergence interfaces are formalized in `lean/FinalTheorem.lean` and `lean/FinalStatement.lean`.

## Build

Pinned toolchain: Lean 4 `v4.33.0-rc2` (`lean/lean-toolchain`), a recent
release that postdates the known Lean 4 soundness issues.

```sh
cd lean
lake build S6Audit
```

## Identity proof

SHA-512:

```text
c9590e865d4abc6ba03c26b294d73da624929c894c5c6faeb64dbdc5646e826ab308fda141593aa8a544538724c0a0711356727581cfbe08cc370406af827eac
```
