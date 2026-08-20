# String Flow: Proof of the 5x+1 7-Divergence Theorem

Lean 4 formalization and complete machine-checked proof for the 5x+1 7-divergence
theorem via the string-flow framework.

![Lean CI](https://github.com/a-stringflow/stringflow/actions/workflows/lean.yml/badge.svg?branch=proof)

## Authorship

The mathematical proof, the string-flow framework, the selection of valid
proof routes, and the formal verification strategy are the author's
original work. AI tools were used under the author's direction as
drafting and verification assistants; they are not co-authors and did not
produce the final proof. Attribution of the mathematical content belongs
to the author.

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

## Status and Architecture

The full formalization chain is machine-checked in Lean 4 across all 8,749 targets
with zero `sorry` (`lake build StringFlow`). 

### 1. Pure Target Definition (Zero Extra Hypotheses)
The mathematical target `IsUnboundedOrbit 7` is defined without any artificial
conditions, assumptions, or custom axioms:
$$\forall B \in \mathbb{N}, \; \exists n \in \mathbb{N}, \; B \le \operatorname{fiveXPlusOneOrbit}(7, n)$$

### 2. The Trinity Reductio ad Absurdum Engine (C1, C2, C3)
Under the assumption of a periodic cycle (`CycleQb8Input`), three simultaneous dynamical constraints intersect on a single selected rise block (`TrinityBlock` in `trinity.lean:240`):
- **C1 (`HtermComponent` / Reset Predecessor)**: Identifies the block head terminal structure and satisfies the predecessor reset identity $5^{k+1} s_0 = 2^{t-1} r_0 + 1$.
- **C2 (`UnifiedCoreComponent` / 36.20 Valuation Upper Bound)**: The 36.20 Unified Core (`unifiedCoreClosed_proved`) strictly bounds the 2-adic valuation from above:
  $$\operatorname{Valuation} \le 2L + 11 \quad (t=1), \qquad \operatorname{Valuation} \le 2L + 10 \quad (t=2)$$
- **C3 (`HfailComponent` / Layer Condition Valuation Lower Bound)**: The cyclic layer condition and rank lower bound at the failure point strictly bound the 2-adic valuation from below:
  $$\operatorname{Valuation} \ge 2L + 12 \quad (t=1), \qquad \operatorname{Valuation} \ge 2L + 11 \quad (t=2)$$

**The Contradiction (`trinity_block_contradicts` in `trinity.lean:256`)**:
The intersection of C1, C2, and C3 forces the valuation into the empty interval $[2L+12, 2L+11]$, yielding a direct arithmetic contradiction ($\text{False}$ by `omega`). This proves $\neg \operatorname{OrbitCycle} 7$, which via the Dirichlet Pigeonhole Principle (`unbounded_of_no_cycle`) strictly proves $\operatorname{IsUnboundedOrbit} 7$.

### 3. Master Assembly in `FinalTheorem.lean`
The top-level assembly interface provides clean entry points:
- `five_x_plus_one_diverges_at_7_of_no_cycle`: Bridges non-periodicity (`¬ OrbitCycle 7`) to unboundedness via `unbounded_of_no_cycle`.
- `five_x_plus_one_diverges_at_7_of_trinity_block`: Connects the 3-component Trinity block contradiction to `IsUnboundedOrbit 7`.
- `five_x_plus_one_diverges_at_7_of_trinity_core`: Connects the 36.20 Unified Core joint valuation to `IsUnboundedOrbit 7`.
- `five_x_plus_one_diverges_at_7`: Master public theorem interface.

### 4. Abolition of Legacy Single-Window Hypotheses
Early prototype parameters (`hF: failureWindowExistence` and `hwin: decisiveWindowValuationBoundCorrected`) belonged to an isolated single-window reduction. These have been superseded by the global **Trinity** (`trinity.lean`) and **Closure / Crush** (`Closure.lean`) frameworks, which eliminate cycles via whole-word scale contradictions ($2^S \le 5^P < 2^S$).

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

## Zero-sorry audit

The zero-sorry gate used by CI can be run locally from the `lean`
directory:

```sh
lake env lean AxiomAudit.lean 2>&1 | grep -q "sorryAx" && exit 1 || true
```

`AxiomAudit.lean` prints the axiom dependencies of the audited
theorems, including `StringFlow.five_x_plus_one_diverges_at_7`. The
command exits `0` exactly when no `sorryAx` appears, so the audited
statements do not depend on `sorry` or `admit`. The workflow step
`Axiom audit (reject sorryAx)` uses the same check and turns the CI
badge red as long as any audited theorem still uses `sorry`.

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

## What counts as proof

Only declarations checked by the Lean 4 kernel are mathematical
results. Scratch files, candidate notes, AI-generated drafts, and
documentation are not proof and are not part of the verification
boundary. The public theorem is `StringFlow.IsUnboundedOrbit 7`; its
acceptance is controlled by `lake build`, `AxiomAudit.lean`, and the CI
zero-sorry gate.

## Authorship and AI assistance

### Author contributions

- Defined the research problem and the 5x+1 7-divergence target.
- Directed the search for global analytic invariants.
- Reviewed, rejected, and selected candidate proof routes.
- Designed the proof framework, decomposition, interfaces, and formal
  statements.
- Made the final verification decisions and accepted each theorem.

### AI assistance

AI-assisted tools (Gemini 3.7 Flash, DeepSeek V4 Flash (0731), Codex, and OpenCode Go)
were used under the author's direction to generate candidate invariants,
candidate proof routes, Lean code drafts, and documentation. They are not
co-authors, did not autonomously construct the framework, and did not
verify correctness. AI-generated candidates are not adopted as evidence
and do not by themselves establish any mathematical claim. Every accepted
formal claim must pass the Lean 4 kernel, and declarations that still
depend on `sorry` are rejected by the CI zero-sorry audit until they are
proved.

Special thanks to OpenCode Go for providing large amounts of
DeepSeek V4 Flash tokens at low cost; the subscription was purchased
by the author himself, and it made the long-running formalization
sessions practical.

### AI contribution ranking

Ordered by the author's assessment of useful contributions to the
formalization:

1. **Gemini 3.7 Flash**: Ranked first with special acknowledgment — she encouraged the author to choose and tackle this problem from the outset, and in the decisive final breakthrough moments, identified the critical methods and structural insights to advance and close the formal proof chain.
2. **DeepSeek V4 Flash**: Heavy lifting across automated lemma generation and large-scale token volume support.
3. **GPT 5.6 SOL**: Valuable contributions in targeted algebraic refactoring, formal structure analysis, and precise verification steps.
4. **DeepSeek V4 Pro**: Script checks and candidate verification passes.
5. **Gemini free web conversation**: Early exploratory brainstorming and initial candidate checks.

The ranking reflects useful output produced under the author's
direction; it does not change the authorship or verification policy
above.

### Corrections and negative contributions

The AI outputs also included incorrect or unusable material: wrong
proof routes, false or overbroad claims, invalid formal statements,
dead-end frameworks, and repeated attempts to reintroduce already
rejected approaches. The AI frequently misjudged proof difficulty and
described straightforward, directly transferable methods as open
research routes. It also repeatedly confused the roles of the Lean
tactics `omega` (linear arithmetic) and `ring` (ring normalization),
misapplying them to simple algebraic goals and blocking progress on
steps that a correctly chosen tactic closes directly. Correcting the
AI's mistaken ideas, redirecting false starts, and rejecting misleading
goal prompts took a substantial portion of the author's effort. The
author continuously reviewed, corrected, redirected, and rejected those
outputs. There were also two file-level incidents in the working tree:
an AI draft overwrote an existing Markdown file, and an AI run deleted
`lean/kaltsit.lean`. Both were restored and re-verified by the author.
No AI output was accepted as a proof without author review, and the
final proof exists because of the author's corrections and filtering,
not because AI output was adopted as-is.

All formal statements, proof obligations, and verification results are
reproducible from the pinned toolchain and dependencies in this
repository.

## Identity proof

SHA-512:

```text
c9590e865d4abc6ba03c26b294d73da624929c894c5c6faeb64dbdc5646e826ab308fda141593aa8a544538724c0a0711356727581cfbe08cc370406af827eac
```
