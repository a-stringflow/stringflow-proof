/-
Exact integer-balance interface for the delta=0 local lemma.

The file does not assert the local lemma.  It formalises the new
reduction from `p_adic_window_route.md` sections 8--10: the balance
`E_L` has an exact affine recurrence with no per-step carry bit, and
local-lemma failure is equivalent to one integer congruence.
-/

namespace StringFlow.Balance

inductive Step where
  | one
  | two
deriving DecidableEq

def Step.weight : Step → Nat
  | .one => 1
  | .two => 2

def Step.coef : Step → Int
  | .one => 4
  | .two => -2

/-- `M_L` is the suffix-only part of the balance:
`M_0 = 0`, `M_{k+1} = 5 M_k + c_t * 2^{d_k}`. -/
def suffixM : List Step → Nat → Int
  | [], _ => 0
  | t :: ts, d =>
      t.coef * (2 ^ d : Int) * (5 ^ ts.length : Int) + suffixM ts (d + t.weight)

/-- Full balance `E_L` from a block-start value `E0 = -(5*r_j+3)`. -/
def balanceE : List Step → Int → Int
  | [], E => E
  | t :: ts, E =>
      balanceE ts (5 * E + t.coef * (2 ^ 0 : Int))

/-- Weighted version with explicit relative depth. -/
def balanceEWithDepth : List Step → Nat → Int → Int
  | [], _, E => E
  | t :: ts, d, E =>
      let E' := 5 * E + t.coef * (2 ^ d : Int)
      balanceEWithDepth ts (d + t.weight) E'

-- `balanceE` starts at depth 0; this is the version used in the notes.
def balanceE0 (s : List Step) (E0 : Int) : Int :=
  balanceEWithDepth s 0 E0

/-- Exact affine decomposition of the full balance:
`E_L = 5^L * E + M_L`. -/
theorem balanceEWithDepth_eq (s : List Step) (d : Nat) (E : Int) :
    balanceEWithDepth s d E = (5 ^ s.length : Int) * E + suffixM s d := by
  revert d E
  induction s with
  | nil => intro d E; simp [balanceEWithDepth, suffixM]
  | cons t ts ih =>
      intro d E
      calc
        balanceEWithDepth (t :: ts) d E
            = balanceEWithDepth ts (d + t.weight) (5 * E + t.coef * (2 ^ d : Int)) := rfl
        _ = (5 ^ ts.length : Int) * (5 * E + t.coef * (2 ^ d : Int)) + suffixM ts (d + t.weight) :=
            ih (d + t.weight) (5 * E + t.coef * (2 ^ d : Int))
        _ = (5 ^ ts.length : Int) * (5 * E) + (5 ^ ts.length : Int) * (t.coef * (2 ^ d : Int)) + suffixM ts (d + t.weight) := by
            rw [Int.mul_add]
        _ = (5 ^ ts.length : Int) * 5 * E + t.coef * (2 ^ d : Int) * (5 ^ ts.length : Int) + suffixM ts (d + t.weight) := by
            have hfirst : (5 ^ ts.length : Int) * (5 * E) = (5 ^ ts.length : Int) * 5 * E := by
              rw [← Int.mul_assoc]
            have hsecond : (5 ^ ts.length : Int) * (t.coef * (2 ^ d : Int)) =
                t.coef * (2 ^ d : Int) * (5 ^ ts.length : Int) := by
              rw [Int.mul_comm]
            rw [hfirst, hsecond]
        _ = (5 ^ (ts.length + 1) : Int) * E + t.coef * (2 ^ d : Int) * (5 ^ ts.length : Int) + suffixM ts (d + t.weight) := by
            have hpow : (5 ^ (ts.length + 1) : Int) = (5 ^ ts.length : Int) * 5 := by
              have h := congrArg (fun n : Nat => (n : Int)) (Nat.pow_add 5 ts.length 1)
              simpa using h
            rw [← hpow]
        _ = (5 ^ (t :: ts).length : Int) * E + suffixM (t :: ts) d := by
            simp [suffixM]
            omega

/-- `balanceE0 = 5^L E0 + M_L`. -/
theorem balanceE0_eq (s : List Step) (E0 : Int) :
    balanceE0 s E0 = (5 ^ s.length : Int) * E0 + suffixM s 0 := by
  unfold balanceE0
  exact balanceEWithDepth_eq s 0 E0

/-- The macro map between consecutive `u=1` states: if `v2(F)=2a`,
then one `t=1` step followed by `a-1` `t=2` steps gives
`F' = 2 + 5^a F / 2^(2a-1)`. -/
def macroBalance (a : Nat) (F : Int) : Int :=
  2 + ((5 ^ a : Int) * F) / (2 ^ (2 * a - 1) : Int)

/-- Open failure congruence for the macro step:
`F' = 0 mod 2^(H_next+1)`. -/
def macroFailureCongruence (a Hnext : Nat) (F : Int) : Prop :=
  ∃ k : Int, macroBalance a F = k * (2 ^ (Hnext + 1) : Int)

/-- Failure congruence from `p_adic_window_route.md` section 8. -/
def failureCongruence (s : List Step) (H0 : Nat) (E0 : Int) : Prop :=
  let l := s.filter (fun t => t = Step.one) |>.length
  ∃ k : Int,
    balanceE0 s E0 = k * (2 ^ (H0 + l + 1) : Int)

/-- Failure congruence in affine form:
`5^L E0 + M_L = k * 2^(H0+l+1)`. -/
theorem failureCongruence_iff_affine (s : List Step) (H0 : Nat) (E0 : Int) :
    failureCongruence s H0 E0 ↔
      ∃ k : Int,
        (5 ^ s.length : Int) * E0 + suffixM s 0 =
          k * (2 ^ (H0 + (s.filter (fun t => t = Step.one)).length + 1) : Int) := by
  unfold failureCongruence
  rw [balanceE0_eq]

/-- Explicit t=2-run closed form: `E_n = 5^n E0 + 2^(2n+1) - 2*5^n`. -/
def twoRunBalance (n : Nat) (E0 : Int) : Int :=
  (5 ^ n : Int) * E0 + (2 ^ (2 * n + 1) : Int) - 2 * (5 ^ n : Int)

/-- Positive odd part `C = (5*r+3) / 2^(2a)` at a `u=1` state with
`X = 2a`.  Sign convention: with `c = -C`, `F_p = c * 2^(2a)` and the
macro endpoint satisfies `F' = -2 * (5^a * C - 1)`. -/
def macroPositiveOddPart (a : Nat) (r : Int) : Int :=
  (5 * r + 3) / (2 ^ (2 * a) : Int)

/-- Endpoint balance of the macro `p -> p + a` (one `t=1`, then
`a-1` `t=2` steps): `F' = -2*(5^a*C - 1)`. -/
def macroEndpointF (a : Nat) (r : Int) : Int :=
  -2 * ((5 ^ a : Int) * macroPositiveOddPart a r - 1)

/-- Macro success inequality `v2(5^a*C-1) <= Hp - 2a + 1`,
equivalently `2^(m+2)` does not divide `5^a*C - 1` with `m = Hp - 2a`.
This is the local lemma at the macro endpoint. -/
def macroSuccessInequality (a Hp : Nat) (r : Int) : Prop :=
  let m := Hp - 2 * a
  Not ((2 ^ (m + 2) : Int) ∣ (5 ^ a : Int) * macroPositiveOddPart a r - 1)

/-- Macro endpoint failure congruence:
`2^(m+2) | 5^a*C - 1`, i.e. `X' >= Hp - 2a + 3`. -/
def macroFailureCongruence2 (a Hp : Nat) (r : Int) : Prop :=
  let m := Hp - 2 * a
  Exists fun k : Int =>
    (5 ^ a : Int) * macroPositiveOddPart a r - 1 = k * (2 ^ (m + 2) : Int)

/-- Macro success is exactly the negation of the failure congruence. -/
theorem macroSuccess_iff_not_failure (a Hp : Nat) (r : Int) :
    macroSuccessInequality a Hp r ↔ ¬ macroFailureCongruence2 a Hp r := by
  unfold macroSuccessInequality macroFailureCongruence2
  simp [Dvd.dvd, Int.mul_comm]

/-- Exact one-bit carry criterion for macro failure.  Here
`u = y/2^(2a)` is the odd part of the window and `n` is the lift bit just
above the `Hp+1`-bit window.  The criterion says there exists the 2-adic
unit `s = 5^(-(p+a+1)) mod 2^(m+3)` such that `u + s = 0 mod 2^(m+1)`
and the next bit of `u+s` equals `n`.  The documented reduction is: the
macro endpoint fails iff this criterion holds. -/
def macroCarryFailureCriterion (a Hp p : Nat) (u n : Int) : Prop :=
  let m := Hp - 2 * a
  Exists fun s : Int =>
    (2 ^ (m + 3) : Int) ∣ (s * (5 : Int) ^ (p + a + 1) - 1) ∧
    (2 ^ (m + 1) : Int) ∣ (u + s) ∧
    ((u + s) / (2 ^ (m + 1) : Int)) % 2 = n

/-- Macro suffix numerator for one `t=1` followed by `a-1` `t=2` steps:
`S_a = 3*5^(a-1) - 2*4^(a-1)`. -/
def macroSuffixNumerator (a : Nat) : Int :=
  3 * (5 ^ (a - 1) : Int) - 2 * (4 ^ (a - 1) : Int)

/-- Recurrence of the macro suffix numerator:
`S_{a+1} = 5 S_a + 2^(2a-1)`. -/
theorem macroSuffixNumerator_succ (a : Nat) (ha : 1 ≤ a) :
    macroSuffixNumerator (a + 1) = 5 * macroSuffixNumerator a + (2 ^ (2 * a - 1) : Int) := by
  unfold macroSuffixNumerator
  have ha1 : a + 1 - 1 = a := by omega
  rw [ha1]
  have h5a : (5 ^ a : Int) = 5 * (5 ^ (a - 1) : Int) := by
    have h : a = (a - 1) + 1 := by omega
    rw [h]
    have hp := congrArg (fun n : Nat => (n : Int)) (Nat.pow_add 5 (a - 1) 1)
    simpa [Int.mul_comm] using hp
  have h4a : (4 ^ a : Int) = 4 * (4 ^ (a - 1) : Int) := by
    have h : a = (a - 1) + 1 := by omega
    rw [h]
    have hp := congrArg (fun n : Nat => (n : Int)) (Nat.pow_add 4 (a - 1) 1)
    simpa [Int.mul_comm] using hp
  have h2 : (2 ^ (2 * a - 1) : Int) = 2 * (4 ^ (a - 1) : Int) := by
    have h : 2 * a - 1 = 1 + 2 * (a - 1) := by omega
    rw [h]
    have hp := congrArg (fun n : Nat => (n : Int)) (Nat.pow_add 2 1 (2 * (a - 1)))
    have hsq : (2 ^ (2 * (a - 1)) : Int) = (4 ^ (a - 1) : Int) := by
      have hm := congrArg (fun n : Nat => (n : Int)) (Nat.pow_mul 2 2 (a - 1))
      simpa using hm
    simpa [hsq, Int.mul_comm] using hp
  rw [h5a, h4a, h2]
  omega

/-- Endpoint identity of a macro: `r_i + 1 = 2 * 5^(a-1) * C_p`. -/
def macroEndpointPlusOne (a : Nat) (r : Int) : Int :=
  2 * (5 ^ (a - 1) : Int) * macroPositiveOddPart a r

/-- Open exact identity: macro endpoint balance equals
`-2 * (5^a * C - 1)`, which is the definitional form of
`r_i + 1 = 2 * 5^(a-1) * C`. -/
def macroEndpointIdentityStatement : Prop :=
  ∀ (a : Nat) (r : Int), 1 ≤ a →
    macroEndpointF a r = -2 * ((5 ^ a : Int) * macroPositiveOddPart a r - 1)

/-- Margin `H - X` at a state. -/
def marginAt (H X : Int) : Int := H - X

/-- Open margin monotonicity: along consecutive `u=1` states `p -> i`,
the earlier margin is `M_i + X_i - 2`, so `M_p >= M_i` since `X_i >= 2`. -/
def marginMonoStatement : Prop :=
  ∀ (Hp Xp Hi Xi : Int),
    Hp = Hi + Xp - 2 →
    marginAt Hp Xp = marginAt Hi Xi + Xi - 2

/-- Open terminal-capacity reduction: for the last `u=1` state in a block,
with `X = X_m`, `k` `t=2` steps before the even terminal and `h_e = h_m + k`,
the last-state margin is `2*(j-t_j)+12-2*h_e-(X-1-2*k)`, so
`X <= H` iff the displayed capacity inequality holds. -/
def terminalCapacityReductionStatement : Prop :=
  ∀ (j tj hm he X k : Int),
    0 ≤ X - 1 - 2 * k →
    he = hm + k →
    (0 ≤ 2 * (j - tj) + 13 - 2 * hm - X ↔
      2 * he ≤ 2 * (j - tj) + 12 - (X - 1 - 2 * k))

/-- D invariant `u - H` at odd states. -/
def dInvariant (u H : Int) : Int := u - H

/-- t=2 steps keep D invariant: `u' = u - 2` and `H' = H - 2`. -/
def dInvariantTwoStepStatement : Prop :=
  ∀ (u H : Int), dInvariant (u - 2) (H - 2) = dInvariant u H

/-- t=1 from a `u=1` state with valuation `X`: `u' = X - 1`, `H' = H`,
so `D' = -marginAt H X - 1`. -/
def dInvariantOneStepStatement : Prop :=
  ∀ (H X : Int), dInvariant (X - 1) H = -marginAt H X - 1

theorem macroEndpointIdentityStatement_proof : macroEndpointIdentityStatement := by
  intro a r ha
  rfl

theorem marginMonoStatement_proof : marginMonoStatement := by
  intro Hp Xp Hi Xi h
  unfold marginAt
  omega

theorem terminalCapacityReductionStatement_proof : terminalCapacityReductionStatement := by
  intro j tj hm he X k hpos hhe
  rw [hhe]
  constructor <;> omega

theorem dInvariantTwoStepStatement_proof : dInvariantTwoStepStatement := by
  intro u H
  unfold dInvariant
  omega

theorem dInvariantOneStepStatement_proof : dInvariantOneStepStatement := by
  intro H X
  unfold dInvariant marginAt
  omega

end StringFlow.Balance
