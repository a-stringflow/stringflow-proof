import CycleBridge
import RealOrbitLocalLemma
import RealOrbitCharge
import RiseDecompositionAssembly

namespace StringFlow

namespace Amiya

/-- The rise suffix beginning at global word depth `j`. -/
def blockWordFrom (w : List Nat) (j : Nat) : List Nat :=
  (w.drop j).take (CycleBridge.risePrefixLength (w.drop j))

/-- The global depth just after the rise suffix beginning at `j`. -/
def blockEndFrom (w : List Nat) (j : Nat) : Nat :=
  j + (blockWordFrom w j).length

/-- A `t=1` rank threshold is exactly the `hfail_t1` valuation bound,
once the reset equation identifies the block head. -/
theorem hfail_t1_of_rank
    (j k0 s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 1 1 rj)
    (hrank : 2 * j + 11 ≤ twoValuation (rj + 1)) :
    2 * j + 12 ≤ twoValuation (5 ^ (k0 + 1) * s + 5 ^ j - 2) := by
  have hval := RealOrbitLocalLemma.t1WindowValue_eq_twoValuation_rj_plus_one
    j k0 s rj hreset
  have htarget : 2 * j + 12 ≤ BlockAutomaton.t1WindowValue j k0 s := by
    rw [hval]
    omega
  simpa [BlockAutomaton.t1WindowValue] using htarget

/-- A `t=2` rank threshold is exactly the `hfail_t2` valuation bound,
once the reset equation identifies the block head. -/
theorem hfail_t2_of_rank
    (j k0 δ s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 2 δ rj)
    (hrank : 2 * j + 9 ≤ twoValuation (rj + 1)) :
    2 * j + 11 ≤ twoValuation (5 ^ (k0 + 1) * s + δ * 5 ^ j) := by
  have hval := RealOrbitLocalLemma.t2WindowValue_eq_twoValuation_rj_plus_one
    j k0 δ s rj hreset
  have htarget : 2 * j + 11 ≤ BlockAutomaton.t2WindowValue j k0 δ s := by
    rw [hval]
    omega
  simpa [BlockAutomaton.t2WindowValue] using htarget

/-- The `hfail_t1` valuation lower bound gives back the exact block-head
rank threshold. -/
theorem hfail_t1_rank_of_hfail
    (j k0 s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 1 1 rj)
    (hfail : 2 * j + 12 ≤ twoValuation (5 ^ (k0 + 1) * s + 5 ^ j - 2)) :
    2 * j + 11 ≤ twoValuation (rj + 1) := by
  have hval := RealOrbitLocalLemma.t1WindowValue_eq_twoValuation_rj_plus_one
    j k0 s rj hreset
  have hf : 2 * j + 12 ≤ BlockAutomaton.t1WindowValue j k0 s := by
    simpa [BlockAutomaton.t1WindowValue] using hfail
  rw [hval] at hf
  omega

/-- The `hfail_t2` valuation lower bound gives back the exact block-head
rank threshold. -/
theorem hfail_t2_rank_of_hfail
    (j k0 δ s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 2 δ rj)
    (hfail : 2 * j + 11 ≤ twoValuation (5 ^ (k0 + 1) * s + δ * 5 ^ j)) :
    2 * j + 9 ≤ twoValuation (rj + 1) := by
  have hval := RealOrbitLocalLemma.t2WindowValue_eq_twoValuation_rj_plus_one
    j k0 δ s rj hreset
  have hf : 2 * j + 11 ≤ BlockAutomaton.t2WindowValue j k0 δ s := by
    simpa [BlockAutomaton.t2WindowValue] using hfail
  rw [hval] at hf
  omega

/-- The `t=1` failure lower bound follows from a local hident block and
the corresponding block-head rank threshold. -/
theorem hfail_t1_of_local_block_rank
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : CycleBridge.LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (ht1 : t = 1)
    (hrank : 2 * j + 11 ≤ twoValuation (rj + 1)) :
    2 * j + 12 ≤ twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ j - 2) := by
  rcases CycleBridge.local_hident_to_reset_reachability d with
    ⟨hreset, _hreach⟩
  have hδ1 : δ = 1 := d.hδ.1 ht1
  subst t
  rw [hδ1] at hreset
  exact hfail_t1_of_rank j rt.k rt.s rj hreset hrank

/-- The `t=2` failure lower bound follows from a local hident block and
the corresponding block-head rank threshold. -/
theorem hfail_t2_of_local_block_rank
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : CycleBridge.LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (ht2 : t = 2)
    (hrank : 2 * j + 9 ≤ twoValuation (rj + 1)) :
    2 * j + 11 ≤ twoValuation (5 ^ (rt.k + 1) * rt.s + δ * 5 ^ j) := by
  rcases CycleBridge.local_hident_to_reset_reachability d with
    ⟨hreset, _hreach⟩
  subst t
  exact hfail_t2_of_rank j rt.k δ rt.s rj hreset hrank

end Amiya

end StringFlow
