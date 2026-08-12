import Domination

/-!
# Basin-bound certificates from word domination

This module turns the pointwise domination lemma into an interval
certificate format.  A certificate is a finite list of contiguous
`(lo, hi, w)` blocks.  `certsOK` checks that the blocks cover
`[lo, hi)` and that every admissible start in each block is dominated
by its word with `wordWeight w <= cap`.  `certsOK_spec` then lifts the
domination lemma to the whole interval.
-/

namespace StringFlow

/-- One certificate block: word `w` dominates every admissible start
in `[lo, hi)`, and the word weight is bounded by the cap. -/
structure Cert where
  lo : Nat
  hi : Nat
  w : List Nat
deriving DecidableEq

/-- A single block is valid when `domCert cap lo hi w` holds. -/
def certOK (cap : Nat) (c : Cert) : Bool :=
  domCert cap c.lo c.hi c.w

/-- Contiguous certificate list for `[lo, hi)`: the first block starts
at `lo`, each next block starts where the previous one ended, and the
last block ends at `hi`. -/
def certsOK (cap lo hi : Nat) : List Cert → Bool
  | [] => decide (hi ≤ lo)
  | c :: cs => decide (c.lo = lo) && certOK cap c && certsOK cap c.hi hi cs

/-- First certificate block containing `m`, if any. -/
def coverCert : List Cert → Nat → Option Cert
  | [], _ => none
  | c :: cs, m =>
      if _ : c.lo ≤ m ∧ m < c.hi then some c else coverCert cs m

/-- Certificate soundness: the domination lemma applied to the block
that covers `m`. -/
theorem certsOK_spec (cap lo hi : Nat) (cs : List Cert) :
    certsOK cap lo hi cs = true →
    ∀ m : Nat, lo ≤ m → m < hi → admissible m →
      ∃ c : Cert, coverCert cs m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ cap := by
  induction cs generalizing lo with
  | nil =>
      intro h m hlo hlt hadm
      simp [certsOK] at h
      omega
  | cons c cs ih =>
      intro h m hlo hlt hadm
      have hHead : c.lo = lo := by
        simp [certsOK, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1
      have hCert : certOK cap c = true := by
        simp [certsOK, Bool.and_eq_true] at h
        exact h.1.2
      have hTail : certsOK cap c.hi hi cs = true := by
        simp [certsOK, Bool.and_eq_true] at h
        exact h.2
      by_cases hmc : m < c.hi
      · have hc : c.lo ≤ m := by rw [hHead]; exact hlo
        have hCover : coverCert (c :: cs) m = some c := by
          simp [coverCert, hc, hmc]
        rcases domCert_spec cap c.lo c.hi c.w hCert m hc hmc hadm with
          ⟨S, hS, hle⟩
        refine ⟨c, hCover, S, hS, hle⟩
      · have hge : c.hi ≤ m := by omega
        rcases ih c.hi hTail m hge hlt hadm with ⟨c', hCover', hRes⟩
        refine ⟨c', ?_, hRes⟩
        have hn : ¬ (c.lo ≤ m ∧ m < c.hi) := by omega
        simp [coverCert, hn, hCover']

end StringFlow
