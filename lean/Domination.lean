import Init

/-!
# Word domination for the first C3 hit time

This module formalizes the domination lemma from 52.21.2quater.
A finite rising word `w` over `{1,2}` dominates a start `m` when the
first-C3 word of `m` is a prefix of `w`.  The domination predicate is
decided locally, one accelerated step per word symbol.  If it holds,
the first C3 start is reached within `w.length` steps and the total
prefix weight is bounded by `wordWeight w`.
-/

namespace StringFlow

/-- A C3 start: `n ≡ 3 (mod 8)`, equivalently `v_2(5n+1) ≥ 3`. -/
def isC3 (n : Nat) : Bool := n % 8 = 3

/-- Total weight of a rising word: `Σ t_j` over `t_j ∈ {1,2}`. -/
def wordWeight : List Nat → Nat
  | [] => 0
  | t :: ts => t + wordWeight ts

/-- `domWord w m`: the actual first-C3 word of `m` is a prefix of `w`.
An already-C3 start is dominated by every word; otherwise the first
accelerated step must have exactly the head weight of `w` and the tail
must dominate the next value. -/
def domWord : List Nat → Nat → Bool
  | [], n => n % 8 = 3
  | t :: ts, n =>
      if n % 8 = 3 then true
      else if n % 8 = 7 then t = 2 && domWord ts ((5 * n + 1) / 4)
      else t = 1 && domWord ts ((5 * n + 1) / 2)

/-- `domWordLE w m`: pointwise weight domination.  The actual
first-C3 word of `m` is a prefix of `w` and each actual weight is at
most the corresponding entry of `w`.  This is weaker than `domWord`
and lets one word dominate more starts. -/
def domWordLE : List Nat → Nat → Bool
  | [], n => n % 8 = 3
  | t :: ts, n =>
      if n % 8 = 3 then true
      else if n % 8 = 7 then 2 ≤ t && domWordLE ts ((5 * n + 1) / 4)
      else 1 ≤ t && domWordLE ts ((5 * n + 1) / 2)

/-- First-C3 prefix as `(hit, weight)`.  If no C3 start is reached
within `fuel` steps, `hit` is false and the weight is 0. -/
def firstC3H : Nat → Nat → Bool × Nat
  | 0, n => if n % 8 = 3 then (true, 0) else (false, 0)
  | fuel + 1, n =>
      if n % 8 = 3 then (true, 0)
      else if n % 8 = 7 then
        let p := firstC3H fuel ((5 * n + 1) / 4)
        (p.1, p.2 + 2)
      else
        let p := firstC3H fuel ((5 * n + 1) / 2)
        (p.1, p.2 + 1)

/-- Domination lemma: a dominated start reaches C3 within the word
length and its prefix weight is at most the word weight. -/
theorem domWord_firstC3H (w : List Nat) :
    ∀ m : Nat, domWord w m = true →
    ∃ S : Nat, firstC3H w.length m = (true, S) ∧ S ≤ wordWeight w := by
  induction w with
  | nil =>
      intro m h
      have hc3 : m % 8 = 3 := by simpa [domWord] using h
      refine ⟨0, ?_⟩
      simp [firstC3H, hc3]
  | cons t ts ih =>
      intro m h
      by_cases hc3 : m % 8 = 3
      · refine ⟨0, ?_⟩
        simp [firstC3H, hc3]
      · by_cases h7 : m % 8 = 7
        · have ht : t = 2 := by
            simp [domWord, h7] at h
            exact h.1
          have hdom : domWord ts ((5 * m + 1) / 4) = true := by
            simp [domWord, h7] at h
            exact h.2
          rcases ih ((5 * m + 1) / 4) hdom with ⟨S, hS, hle⟩
          refine ⟨S + 2, ?_, ?_⟩
          · simp [firstC3H, h7, hS]
          · simp [ht, wordWeight]
            omega
        · have ht : t = 1 := by
            simp [domWord, hc3, h7] at h
            exact h.1
          have hdom : domWord ts ((5 * m + 1) / 2) = true := by
            simp [domWord, hc3, h7] at h
            exact h.2
          rcases ih ((5 * m + 1) / 2) hdom with ⟨S, hS, hle⟩
          refine ⟨S + 1, ?_, ?_⟩
          · simp [firstC3H, hc3, h7, hS]
          · simp [ht, wordWeight]
            omega

/-- Pointwise domination lemma: a pointwise-dominated start reaches
C3 within the word length and its prefix weight is at most the word
weight. -/
theorem domWordLE_firstC3H (w : List Nat) :
    ∀ m : Nat, domWordLE w m = true →
    ∃ S : Nat, firstC3H w.length m = (true, S) ∧ S ≤ wordWeight w := by
  induction w with
  | nil =>
      intro m h
      have hc3 : m % 8 = 3 := by simpa [domWordLE] using h
      refine ⟨0, ?_⟩
      simp [firstC3H, hc3]
  | cons t ts ih =>
      intro m h
      by_cases hc3 : m % 8 = 3
      · refine ⟨0, ?_⟩
        simp [firstC3H, hc3]
      · by_cases h7 : m % 8 = 7
        · have ht : 2 ≤ t := by
            simp [domWordLE, h7] at h
            exact h.1
          have hdom : domWordLE ts ((5 * m + 1) / 4) = true := by
            simp [domWordLE, h7] at h
            exact h.2
          rcases ih ((5 * m + 1) / 4) hdom with ⟨S, hS, hle⟩
          refine ⟨S + 2, ?_, ?_⟩
          · simp [firstC3H, h7, hS]
          · simp [wordWeight]
            omega
        · have ht : 1 ≤ t := by
            simp [domWordLE, hc3, h7] at h
            exact h.1
          have hdom : domWordLE ts ((5 * m + 1) / 2) = true := by
            simp [domWordLE, hc3, h7] at h
            exact h.2
          rcases ih ((5 * m + 1) / 2) hdom with ⟨S, hS, hle⟩
          refine ⟨S + 1, ?_, ?_⟩
          · simp [firstC3H, hc3, h7, hS]
          · simp [wordWeight]
            omega

/-- Prefix weight returned by `firstC3H` (0 when no hit). -/
def firstC3S (fuel n : Nat) : Nat := (firstC3H fuel n).2

/-- Weight form of the domination lemma. -/
theorem domWord_weight_le (w : List Nat) (m : Nat)
    (h : domWord w m = true) : firstC3S w.length m ≤ wordWeight w := by
  rcases domWord_firstC3H w m h with ⟨S, hS, hle⟩
  simp [firstC3S, hS]
  exact hle

/-- Weight form of the pointwise domination lemma. -/
theorem domWordLE_weight_le (w : List Nat) (m : Nat)
    (h : domWordLE w m = true) : firstC3S w.length m ≤ wordWeight w := by
  rcases domWordLE_firstC3H w m h with ⟨S, hS, hle⟩
  simp [firstC3S, hS]
  exact hle

/-- Admissible starts: at least 7, odd, not divisible by 5. -/
def admissibleB (m : Nat) : Bool :=
  decide (7 ≤ m) && decide (m % 2 = 1) && decide (m % 5 ≠ 0)

/-- Propositional form of `admissibleB`. -/
def admissible (m : Nat) : Prop := 7 ≤ m ∧ m % 2 = 1 ∧ m % 5 ≠ 0

theorem admissibleB_eq (m : Nat) : admissibleB m = true ↔ admissible m := by
  simp [admissibleB, admissible, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Check `P` for every `m` in `[lo, hi)`. -/
def allInRange (lo hi : Nat) (P : Nat → Bool) : Bool :=
  if hi ≤ lo then true
  else P (hi - 1) && allInRange lo (hi - 1) P
termination_by hi - lo
decreasing_by omega

theorem allInRange_spec (lo hi : Nat) (P : Nat → Bool) :
    allInRange lo hi P = true →
    ∀ m : Nat, lo ≤ m → m < hi → P m = true := by
  induction hi with
  | zero =>
      intro h m hlo hlt
      omega
  | succ hi ih =>
      intro h m hlo hlt
      have h' : allInRange lo hi P = true := by
        unfold allInRange at h
        by_cases hle : hi + 1 ≤ lo
        · omega
        · have hAnd : P hi = true ∧ allInRange lo hi P = true := by
            simpa [hle] using h
          exact hAnd.2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact ih h' m hlo hlt'
      · subst m
        unfold allInRange at h
        by_cases hle : hi + 1 ≤ lo
        · omega
        · have hAnd : P hi = true ∧ allInRange lo hi P = true := by
            simpa [hle] using h
          exact hAnd.1

/-- Interval certificate: one word dominates every admissible start in
`[lo, hi)`, and the word itself has weight at most `cap`. -/
def domCert (cap lo hi : Nat) (w : List Nat) : Bool :=
  decide (wordWeight w ≤ cap) && allInRange lo hi (fun m =>
    !admissibleB m || domWordLE w m)

/-- Certificate soundness: the domination lemma applied to every
admissible start in the interval. -/
theorem domCert_spec (cap lo hi : Nat) (w : List Nat) :
    domCert cap lo hi w = true →
    ∀ m : Nat, lo ≤ m → m < hi → admissible m →
      ∃ S : Nat, firstC3H w.length m = (true, S) ∧ S ≤ cap := by
  intro h m hlo hlt hadm
  have hWeight : wordWeight w ≤ cap := by
    simp [domCert, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hRange : allInRange lo hi (fun m => !admissibleB m || domWordLE w m) = true := by
    simp [domCert, Bool.and_eq_true] at h
    exact h.2
  have hAdm : admissibleB m = true := by
    exact (admissibleB_eq m).2 hadm
  have hDom := allInRange_spec lo hi (fun m => !admissibleB m || domWordLE w m)
    hRange m hlo hlt
  have hWord : domWordLE w m = true := by
    simpa [hAdm] using hDom
  rcases domWordLE_firstC3H w m hWord with ⟨S, hS, hle⟩
  refine ⟨S, hS, Nat.le_trans hle hWeight⟩

end StringFlow
