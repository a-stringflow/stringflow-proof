import BasinCert

/-!
# Basin certificates over all odd starts

The `BasinCert.lean` chain only quantifies over the admissible starts
used by the cycle proof (`7 <= m`, odd, `5 ∤ m`).  B-L needs the same
first-C3 bound for every odd `m <= 10^6`, including `5 | m`, because a
W leaf is allowed to be divisible by 5.

This module is the same domination-certificate soundness statement with
the predicate replaced by oddness.  It reuses `Cert`, `coverCert`,
`allInRange_spec`, `domWordLE`, and `firstC3H` from the existing chain.
-/

namespace StringFlow

/-- Oddness predicate used by the B-L all-odd certificate. -/
def oddB (m : Nat) : Bool := decide (m % 2 = 1)

/-- Propositional form of `oddB`. -/
def odd (m : Nat) : Prop := m % 2 = 1

theorem oddB_eq (m : Nat) : oddB m = true -> odd m := by
  simp [oddB, odd, decide_eq_true_eq]

theorem odd_eq_oddB (m : Nat) : odd m -> oddB m = true := by
  simp [oddB, odd]

/-- All-odd interval certificate: one word dominates every odd start in
`[lo, hi)`, and the word has weight at most `cap`. -/
def domCertAllOdd (cap lo hi : Nat) (w : List Nat) : Bool :=
  decide (wordWeight w <= cap) && allInRange lo hi (fun m =>
    !oddB m || domWordLE w m)

/-- Soundness of the all-odd interval certificate. -/
theorem domCertAllOdd_spec (cap lo hi : Nat) (w : List Nat) :
    domCertAllOdd cap lo hi w = true ->
      forall m : Nat, lo <= m -> m < hi -> odd m ->
        exists S : Nat, firstC3H w.length m = (true, S) /\ S <= cap := by
  intro h m hlo hlt hod
  have hWeight : wordWeight w <= cap := by
    simp [domCertAllOdd, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hRange : allInRange lo hi (fun m => !oddB m || domWordLE w m) = true := by
    simp [domCertAllOdd, Bool.and_eq_true] at h
    exact h.2
  have hOdd : oddB m = true := by
    exact odd_eq_oddB m hod
  have hDom := allInRange_spec lo hi (fun m => !oddB m || domWordLE w m)
    hRange m hlo hlt
  have hWord : domWordLE w m = true := by
    simpa [hOdd] using hDom
  rcases domWordLE_firstC3H w m hWord with ⟨S, hS, hle⟩
  refine ⟨S, hS, Nat.le_trans hle hWeight⟩

/-- One all-odd certificate block. -/
def certOKAllOdd (cap : Nat) (c : Cert) : Bool :=
  domCertAllOdd cap c.lo c.hi c.w

/-- Contiguous all-odd certificate list for `[lo, hi)`. -/
def certsOKAllOdd (cap lo hi : Nat) : List Cert -> Bool
  | [] => decide (hi <= lo)
  | c :: cs => decide (c.lo = lo) && certOKAllOdd cap c && certsOKAllOdd cap c.hi hi cs

/-- Soundness of the all-odd certificate list. -/
theorem certsOKAllOdd_spec (cap lo hi : Nat) (cs : List Cert) :
    certsOKAllOdd cap lo hi cs = true ->
      forall m : Nat, lo <= m -> m < hi -> odd m ->
        exists c : Cert, coverCert cs m = some c /\
          exists S : Nat, firstC3H c.w.length m = (true, S) /\ S <= cap := by
  induction cs generalizing lo with
  | nil =>
      intro h m hlo hlt hod
      simp [certsOKAllOdd] at h
      omega
  | cons c cs ih =>
      intro h m hlo hlt hod
      have hHead : c.lo = lo := by
        simp [certsOKAllOdd, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1
      have hCert : certOKAllOdd cap c = true := by
        simp [certsOKAllOdd, Bool.and_eq_true] at h
        exact h.1.2
      have hTail : certsOKAllOdd cap c.hi hi cs = true := by
        simp [certsOKAllOdd, Bool.and_eq_true] at h
        exact h.2
      by_cases hmc : m < c.hi
      · have hc : c.lo <= m := by rw [hHead]; exact hlo
        have hCover : coverCert (c :: cs) m = some c := by
          simp [coverCert, hc, hmc]
        rcases domCertAllOdd_spec cap c.lo c.hi c.w hCert m hc hmc hod with
          ⟨S, hS, hle⟩
        refine ⟨c, hCover, S, hS, hle⟩
      · have hge : c.hi <= m := by omega
        rcases ih c.hi hTail m hge hlt hod with ⟨c', hCover', hRes⟩
        refine ⟨c', ?_, hRes⟩
        have hn : ¬ (c.lo <= m /\ m < c.hi) := by omega
        simp [coverCert, hn, hCover']

end StringFlow
