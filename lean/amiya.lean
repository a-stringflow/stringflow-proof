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

/-- Per-block tail capacity: rank plus rise charge stays inside the
tail budget. -/
def tailPerBlockCapacity {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) : Prop :=
  ∀ r : Nat, r < d.blockCount →
    CycleBridge.cycleRiseBlockTailRank d r +
        CycleBridge.cycleRiseBlockCharge d r ≤
      2 * (CycleBridge.cycleRiseBlockTailDepth d r -
          CycleBridge.cycleRiseBlockTailResetWeight d r) + 12

/-- Per-block tail capacity plus the local rise balance sums exactly to
the weak global comparison.  Therefore the strict global comparison (6)
cannot be concluded from `realOrbitChargeBound`; the missing merge is a
genuinely separate input, not a corollary. -/
theorem tailPerBlockCapacity_implies_weak_global_comparison
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w)
    (hcap : tailPerBlockCapacity d) :
    2 * CycleBridge.cycleRiseBlockH2Sum d ≤
      CycleBridge.cycleRiseBlockTailAvoidBudgetSum d := by
  dsimp [CycleBridge.cycleRiseBlockH2Sum,
    CycleBridge.cycleRiseBlockTailAvoidBudgetSum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => CycleBridge.riseCountTwo (d.suffixWord r))]
  refine List.sum_le_sum ?_
  intro r hr
  have hrlt : r < d.blockCount := List.mem_range.mp hr
  have hbal : 2 * CycleBridge.riseCountTwo (d.suffixWord r) ≤
      CycleBridge.cycleRiseBlockTailRank d r +
        CycleBridge.cycleRiseBlockCharge d r := by
    simpa [CycleBridge.cycleRiseBlockTailRank] using
      CycleBridge.cycleRiseBlockBalance d r hrlt
  have hc := hcap r hrlt
  omega

/-- The rank lower bound attached to a word depth `j` and its incoming
rise weight `t`.  This is the direct hfail input: once the reset
equation at depth `j` is supplied, it converts to `hfail_t1`/`hfail_t2`
through the valuation bridge. -/
def hfailRankLowerBoundAt
    (m : Nat) (w : List Nat) (j t : Nat) : Prop :=
  (t = 1 → 2 * j + 11 ≤
    twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1)) ∧
  (t = 2 → 2 * j + 9 ≤
    twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1))

/-- The precise open hfail goal: every real `CycleQb8Input` with
`5^P < 2^S` has a rise-block head, written at a word depth `j` with
incoming rise weight `t`, whose rank reaches the branchwise failure
threshold.  This target is deliberately not expressed through the
`CycleRiseBlockDecomposition` block heads, because every such maximal
rise endpoint has rank exactly two
(`CycleBridge.cycleRiseBlockHeadRank_two`).  The missing piece is
exactly this rank lower bound, not the rejected strict global
comparison (6). -/
def hfailRankLowerBoundTarget : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
    5 ^ P < 2 ^ S →
      ∃ j t : Nat,
        1 ≤ j ∧ j < P ∧
        (t = 1 ∨ t = 2) ∧
        w.getI (j - 1) = t ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        hfailRankLowerBoundAt m w j t

/-- Maximum `v2(x+1)` along a rise word. -/
def maxRankAlong (r : Nat) : List Nat → Nat
  | [] => twoValuation (r + 1)
  | t :: ts => max (twoValuation (r + 1))
    (maxRankAlong (CycleBridge.riseStep r t) ts)

/-- The starting rank is controlled by the maximum along the word. -/
lemma maxRankAlong_ge_initial (r : Nat) (ts : List Nat) :
    twoValuation (r + 1) ≤ maxRankAlong r ts := by
  induction ts generalizing r with
  | nil => simp [maxRankAlong]
  | cons t ts ih =>
      dsimp [maxRankAlong]
      exact le_max_left _ _

/-- The endpoint rank is controlled by the maximum along the word. -/
lemma maxRankAlong_ge_endpoint (r : Nat) (ts : List Nat) :
    twoValuation (CycleBridge.riseRun r ts + 1) ≤ maxRankAlong r ts := by
  induction ts generalizing r with
  | nil => simp [maxRankAlong, CycleBridge.riseRun]
  | cons t ts ih =>
      dsimp [maxRankAlong]
      exact le_max_of_le_right (ih (CycleBridge.riseStep r t))

/-- Every rise-suffix endpoint of a cyclic rise decomposition has rank
exactly two, including the wrapping endpoint. -/
theorem cycleRiseBlockSuffixEndpointRank_two_all
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockSuffixEndpointRank d r = 2 := by
  by_cases hrnext : r + 1 < d.blockCount
  · exact CycleBridge.cycleRiseBlockSuffixEndpointRank_eq_two d r hr hrnext
  · have hpos : 0 < d.blockCount := lt_of_le_of_lt (Nat.zero_le r) hr
    have hstate := CycleBridge.cycleRiseBlockSuffixEndpoint_eq_nextHead d r hr
    have hnext : CycleBridge.cycleRiseBlockNextHeadState d r =
        StringFlow.Word.wordOrbit (w.take (d.headDepth 0)) m := by
      dsimp [CycleBridge.cycleRiseBlockNextHeadState, CycleBridge.cycleRiseBlockNextHeadDepth]
      rw [if_neg hrnext]
      have hmod0 : (d.headDepth 0 + P) % P = d.headDepth 0 := by
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (d.hhead_lt 0 hpos)
      rw [hmod0]
    have hrank : twoValuation (CycleBridge.cycleRiseBlockNextHeadState d r + 1) = 2 := by
      rw [hnext]
      exact CycleBridge.cycleRiseBlockHeadRank_two d 0 hpos
    simp [CycleBridge.cycleRiseBlockSuffixEndpointRank, hstate, hrank]

/-- Endpoint rank exactly two gives the exact tail-rank lower bound
`2 + 2*N - F ≤ v2(r0+1)` for every cyclic rise block. -/
theorem cycleRiseBlockTailRank_lower_of_endpoint_two
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    2 + 2 * CycleBridge.riseCountTwo (d.suffixWord r) -
        CycleBridge.cycleRiseBlockCharge d r ≤
      CycleBridge.cycleRiseBlockTailRank d r := by
  have hend := CycleBridge.cycleRiseBlockEndpointRank_le d r hr
  have htwo := cycleRiseBlockSuffixEndpointRank_two_all d r hr
  have hle : 2 + 2 * CycleBridge.riseCountTwo (d.suffixWord r) ≤
      CycleBridge.cycleRiseBlockTailRank d r +
        CycleBridge.cycleRiseBlockCharge d r := by
    have hend0 := hend
    rw [htwo] at hend0
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hend0
  omega

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

/-- The `t=1` hfail bound follows from the open rank-lower-bound target
once the same depth `j` is supplied with a real local hident block. -/
theorem hfail_t1_of_hfailRankLowerBoundAt
    {m : Nat} {w : List Nat}
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : CycleBridge.LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (ht1 : t = 1)
    (hrj : rj = StringFlow.Word.wordOrbit (w.take j) m)
    (hrank : hfailRankLowerBoundAt m w j t) :
    2 * j + 12 ≤ twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ j - 2) := by
  have h0 : 2 * j + 11 ≤
      twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1) := hrank.1 ht1
  have hrank' : 2 * j + 11 ≤ twoValuation (rj + 1) := by
    rwa [← hrj] at h0
  exact hfail_t1_of_local_block_rank d ht1 hrank'

/-- The `t=2` hfail bound follows from the open rank-lower-bound target
once the same depth `j` is supplied with a real local hident block. -/
theorem hfail_t2_of_hfailRankLowerBoundAt
    {m : Nat} {w : List Nat}
    {j Wp Wj q Aj rj t δ : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (d : CycleBridge.LocalHidentBlock j Wp Wj q Aj rj t δ rt)
    (ht2 : t = 2)
    (hrj : rj = StringFlow.Word.wordOrbit (w.take j) m)
    (hrank : hfailRankLowerBoundAt m w j t) :
    2 * j + 11 ≤ twoValuation (5 ^ (rt.k + 1) * rt.s + δ * 5 ^ j) := by
  have h0 : 2 * j + 9 ≤
      twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1) := hrank.2 ht2
  have hrank' : 2 * j + 9 ≤ twoValuation (rj + 1) := by
    rwa [← hrj] at h0
  exact hfail_t2_of_local_block_rank d ht2 hrank'

end Amiya

end StringFlow
