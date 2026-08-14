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

The S6 / local-lemma audit chain is machine-checked in
`lean/S6Audit.lean` with zero `sorry`:

- `pure_t2_m1_no_odd_hit` - pure `t=2` `M=1` base-case exclusion;
- `local_lemma_final` - the local lemma under the corrected 36.20
  premises, full word legality, `wordValid`, and `OrbitFrom7 r`.

The public statement `IsUnboundedOrbit 7` is not yet assembled.
Remaining work:

- post-exit block coverage (block-layer induction for new blocks after
  the word-model exits);
- the X=1 chain (symmetric formalization);
- the downstream `L/C/G_i/c_k/m_d/D0` chain;
- TD0/TD1 final wiring and the top-level theorem.

The public statement is defined in `lean/FinalStatement.lean` as
`StringFlow.IsUnboundedOrbit 7`; its proof is the assembly target and is
not yet complete.

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
