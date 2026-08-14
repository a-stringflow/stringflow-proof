# String Flow: 5x+1 7-Divergence Research

Lean 4 formalization and analytic notes for the string-flow approach to
the 5x+1 7-divergence problem.

![Lean CI](https://github.com/a-stringflow/stringflow-proof/actions/workflows/lean.yml/badge.svg?branch=proof)

## Core definition

The full accelerated 5x+1 step is

```lean
def fiveXPlusOneStep (x : Nat) : Nat :=
  (5 * x + 1) / 2 ^ twoValuation (5 * x + 1)
```

The orbit of `x` is the infinite sequence

```lean
def fiveXPlusOneOrbit (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => fiveXPlusOneStep (fiveXPlusOneOrbit x n)
```

That is, `fiveXPlusOneOrbit x n` is the `n`-th term of

```text
x, T(x), T(T(x)), ...
```

where `T = fiveXPlusOneStep`. From the odd starting point `7` every term
is odd, so this is exactly the standard accelerated 5x+1 orbit.

Divergence means the orbit is unbounded:

```lean
def IsUnboundedOrbit (x : Nat) : Prop :=
  ∀ B : Nat, ∃ n : Nat, B ≤ fiveXPlusOneOrbit x n
```

The public mathematical target is:

```lean
IsUnboundedOrbit 7
```

In words, this is exactly the proposition that the accelerated 5x+1 orbit
starting from `7` is unbounded. This is the standard formal statement of
the claim that the orbit of `7` diverges.

For this deterministic total map on `Nat`, boundedness is equivalent to
eventual periodicity: if the orbit is bounded, two iterates must repeat,
and the orbit is periodic from then on. Conversely, if the orbit never
enters a finite cycle, it is unbounded. The Lean theorem
`unbounded_of_no_cycle` supplies the no-cycle-to-unbounded direction used
in the final assembly.

## Status

The S6 / local-lemma audit chain is machine-checked in
`lean/S6Audit.lean` with zero `sorry`. This includes the pure `t=2`
`M=1` base-case exclusion (`pure_t2_m1_no_odd_hit`) and the local lemma
(`local_lemma_final`). The public statement `IsUnboundedOrbit 7` is not
yet assembled; the remaining open items are the post-exit block coverage,
the X=1 chain, the downstream `L/C/G/c_k/m_d/D0` chain, and the TD0/TD1
wiring.

## Layout

- `lean/` - Lean 4 formalization (ASCII-only comments)
- `docs/` - Chinese working notes, kept private, not part of public verification
- `.github/workflows/lean.yml` - Lean CI
- `STATEMENT.md` - English theorem statement and verification status

## Build

Pinned toolchain: Lean 4 `v4.33.0-rc2` (`lean/lean-toolchain`), a recent
release that postdates the known Lean 4 soundness issues.

```sh
cd lean
lake build S6Audit
```

## Verification boundary

`lake build` verifies that every formal statement is proved by the
Lean 4 kernel, but type-checking success does not by itself certify
that a statement matches an intended mathematical formulation. The
correspondence between the formal statements and the mathematical
target is controlled by the simple top-level definition
(`IsUnboundedOrbit 7`), the exact translation of the accelerated
5x+1 step, and the audit records in this repository.

Finite base cases are proved by explicit rewriting (`simp`,
`norm_num`) and do not rely on `native_decide`. The verification
boundary described here does not affect the definition of the final
theorem.

## AI assistance

AI-assisted tools (DeepSeek V4 Flash (0731), Codex, and OpenCode Go)
were used during development for drafting Lean code, organizing
documentation, and assisting proof development. The final proofs are
fully verified by the Lean 4 kernel; no AI-generated correctness claim
is used as evidence. All formal statements, proof obligations, and
verification results are reproducible from the pinned toolchain and
dependencies in this repository.

## Identity proof

SHA-512:

```text
c9590e865d4abc6ba03c26b294d73da624929c894c5c6faeb64dbdc5646e826ab308fda141593aa8a544538724c0a0711356727581cfbe08cc370406af827eac
```
