import PhOne
import Domination

/-!
# PH-2: first-run local lower bound

This module formalizes PH-2 from `ph_qb_gc_chain.md` section 4 in the
cleared-denominator style used by `PhOne.lean`.  For a word whose first
step is a C3 step of weight `t` followed by `r` steps of weight `1`,
the analytic lower bound

    Lambda >= Phi_PH(t,r) = 1 + 2^(t-lambda) * (1-2^(-r*alpha))/(1-2^(-alpha))

with `lambda = log2 5` and `alpha = lambda - 1` is equivalent, after
multiplying by `3*5^r`, to the integer inequality

    3 * localLambda(firstRunWord t r ++ tail)
      >= 5^(tail.length) * (3*5^r + 2^t*(5^r - 2^r)).

The factor `3` and the terms `(5^r - 2^r)/5^r` come from
`2^(-alpha) = 2/5`.
-/

namespace StringFlow.PH

open StringFlow.PMI

/-- The word `[1,1,...,1]` of length `r`. -/
def ones : Nat → List Nat
  | 0 => []
  | r + 1 => 1 :: ones r

/-- A word consisting of a C3 step of weight `t` followed by `r`
steps of weight `1`. -/
def firstRunWord (t r : Nat) : List Nat :=
  t :: ones r

/-- Numerator of `Phi_PH(t,r)` after clearing the `3*5^r`
denominator. -/
def phiNumerator (t r : Nat) : Nat :=
  3 * 5 ^ r + 2 ^ t * (5 ^ r - 2 ^ r)

/-- Length of the word of `r` ones. -/
theorem ones_length (r : Nat) : (ones r).length = r := by
  induction r with
  | zero => simp [ones]
  | succ r ih => simp [ones, ih]

/-- The first `k` entries of `ones r` have weight `k` for `k <= r`. -/
theorem wordPrefixWeight_ones (r k : Nat) (hk : k ≤ r) :
    wordPrefixWeight (ones r) k = k := by
  induction r generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [ones, wordPrefixWeight]
  | succ r ih =>
      cases k with
      | zero => simp [ones, wordPrefixWeight]
      | succ k =>
          have hk' : k ≤ r := by omega
          have h := ih k hk'
          simp [ones, wordPrefixWeight, h]
          omega

/-- The prefix weight after the C3 step and the first `k` ones is
`t + k` for `k <= r`. -/
theorem wordPrefixWeight_firstRun (t r k : Nat) (hk : k ≤ r) :
    wordPrefixWeight (firstRunWord t r) (k + 1) = t + k := by
  unfold firstRunWord
  simp [wordPrefixWeight, wordPrefixWeight_ones r k hk]

/-- `localLambda` of a nonempty word splits into the head term and the
tail scaled by `2^t`. -/
theorem localLambda_cons (t : Nat) (ts : List Nat) :
    localLambda (t :: ts) = 5 ^ ts.length + 2 ^ t * localLambda ts := by
  unfold localLambda
  rw [show (t :: ts).length = ts.length + 1 by simp]
  rw [range_succ_cons ts.length]
  simp [wordPrefixWeight]
  rw [← sum_map_mul_left (List.range ts.length) (2 ^ t)
      (fun j =>
        2 ^ wordPrefixWeight ts j * 5 ^ (ts.length - 1 - j))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  dsimp
  simp [wordPrefixWeight]
  have hjlt : j < ts.length := List.mem_range.mp hj
  have hsub : ts.length - (j + 1) = ts.length - 1 - j := by omega
  rw [hsub, Nat.pow_add]
  ac_rfl

/-- Exact geometric sum for a run of `r` ones:
`3 * localLambda(ones r) = 5^r - 2^r`. -/
theorem localLambda_ones_eq (r : Nat) :
    3 * localLambda (ones r) = 5 ^ r - 2 ^ r := by
  induction r with
  | zero => simp [ones, localLambda]
  | succ r ih =>
      calc
        3 * localLambda (ones (r + 1))
            = 3 * localLambda (1 :: ones r) := by rfl
        _ = 3 * (5 ^ r + 2 * localLambda (ones r)) := by
            rw [localLambda_cons, ones_length]
        _ = 3 * 5 ^ r + 2 * (3 * localLambda (ones r)) := by
            have h1 : 3 * (5 ^ r + 2 * localLambda (ones r)) =
                3 * 5 ^ r + 3 * (2 * localLambda (ones r)) := by
              rw [Nat.mul_add]
            have h2 : 3 * (2 * localLambda (ones r)) =
                2 * (3 * localLambda (ones r)) := by ac_rfl
            rw [h1, h2]
        _ = 3 * 5 ^ r + 2 * (5 ^ r - 2 ^ r) := by rw [ih]
        _ = 5 ^ (r + 1) - 2 ^ (r + 1) := by
            have hsub : 2 * (5 ^ r - 2 ^ r) = 2 * 5 ^ r - 2 * 2 ^ r := by
              rw [Nat.mul_sub_left_distrib]
            have h5 : 5 ^ (r + 1) = 5 * 5 ^ r := by
              rw [Nat.pow_succ]
              rw [Nat.mul_comm]
            have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by
              rw [Nat.pow_succ]
              rw [Nat.mul_comm]
            have hle2 : 2 ^ r ≤ 5 ^ r :=
              Nat.pow_le_pow_left (show 2 ≤ 5 by decide) r
            rw [hsub, h5, h2]
            omega

/-- Exact PH-2 identity for the canonical first-run word:
`3 * localLambda(firstRunWord t r) = phiNumerator t r`. -/
theorem localLambda_firstRun_eq (t r : Nat) :
    3 * localLambda (firstRunWord t r) = phiNumerator t r := by
  unfold firstRunWord phiNumerator
  calc
    3 * localLambda (t :: ones r)
        = 3 * (5 ^ r + 2 ^ t * localLambda (ones r)) := by
            rw [localLambda_cons, ones_length]
    _ = 3 * 5 ^ r + 2 ^ t * (3 * localLambda (ones r)) := by
            have h1 : 3 * (5 ^ r + 2 ^ t * localLambda (ones r)) =
                3 * 5 ^ r + 3 * (2 ^ t * localLambda (ones r)) := by
              rw [Nat.mul_add]
            have h2 : 3 * (2 ^ t * localLambda (ones r)) =
                2 ^ t * (3 * localLambda (ones r)) := by ac_rfl
            rw [h1, h2]
    _ = 3 * 5 ^ r + 2 ^ t * (5 ^ r - 2 ^ r) := by
            rw [localLambda_ones_eq]

/-- Appending a word scales the prefix contribution by `5^(|q|)` and
adds the tail contribution scaled by `2^(wordWeight p)`. -/
theorem localLambda_append (p q : List Nat) :
    localLambda (p ++ q) =
      5 ^ q.length * localLambda p + 2 ^ StringFlow.wordWeight p * localLambda q := by
  induction p with
  | nil =>
      simp [localLambda, StringFlow.wordWeight]
  | cons t ts ih =>
      calc
        localLambda ((t :: ts) ++ q)
            = localLambda (t :: (ts ++ q)) := by rfl
        _ = 5 ^ (ts ++ q).length + 2 ^ t * localLambda (ts ++ q) := by
            rw [localLambda_cons]
        _ = 5 ^ (ts.length + q.length) +
            2 ^ t * (5 ^ q.length * localLambda ts +
              2 ^ StringFlow.wordWeight ts * localLambda q) := by
                rw [List.length_append, ih]
        _ = 5 ^ q.length * (5 ^ ts.length + 2 ^ t * localLambda ts) +
            2 ^ (t + StringFlow.wordWeight ts) * localLambda q := by
                rw [Nat.pow_add]
                rw [Nat.pow_add]
                rw [Nat.mul_add, Nat.mul_add]
                ac_rfl
        _ = 5 ^ q.length * localLambda (t :: ts) +
            2 ^ StringFlow.wordWeight (t :: ts) * localLambda q := by
                rw [localLambda_cons]
                ac_rfl

/-- PH-2: for every word that starts with a C3 step of weight `t`
followed by `r` ones, the local factor is at least
`Phi_PH(t,r)`, with the nonnegative tail accounted for in the
cleared-denominator form. -/
theorem ph2_lower_bound (t r : Nat) (tail : List Nat) :
    3 * localLambda (firstRunWord t r ++ tail) ≥
      5 ^ tail.length * phiNumerator t r := by
  let p := firstRunWord t r
  have hge : 5 ^ tail.length * localLambda p ≤
      localLambda (p ++ tail) := by
    rw [localLambda_append]
    exact Nat.le_add_right _ _
  have h3 : 3 * (5 ^ tail.length * localLambda p) ≤
      3 * localLambda (p ++ tail) :=
    Nat.mul_le_mul_left 3 hge
  have h3' : 3 * (5 ^ tail.length * localLambda p) =
      5 ^ tail.length * (3 * localLambda p) := by ac_rfl
  have hphi : 3 * localLambda p = phiNumerator t r :=
    localLambda_firstRun_eq t r
  rw [h3', hphi] at h3
  simpa [p] using h3

/-- A word has a first-run prefix of weight `t` and length `r`. -/
def hasFirstRunPrefix (t r : Nat) (w : List Nat) : Prop :=
  ∃ tail : List Nat, w = firstRunWord t r ++ tail

/-- PH-2 in terms of the actual word length: the remaining suffix may
have length `w.length - (r+1)`. -/
theorem ph2_lower_bound_of_firstRunPrefix (t r : Nat) (w : List Nat)
    (hw : hasFirstRunPrefix t r w) :
    3 * localLambda w ≥ 5 ^ (w.length - (r + 1)) * phiNumerator t r := by
  rcases hw with ⟨tail, rfl⟩
  have hlen : (firstRunWord t r ++ tail).length = (r + 1) + tail.length := by
    simp [firstRunWord, ones_length]
    omega
  have hpow : (firstRunWord t r ++ tail).length - (r + 1) = tail.length := by
    rw [hlen]
    omega
  rw [hpow]
  exact ph2_lower_bound t r tail

end StringFlow.PH
