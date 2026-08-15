import CycleBridge
import kaltsit
import BlockAutomaton
import RiseDecompositionAssembly
import amiya

/-!
# Trinity: the joint main-theorem skeleton for hterm, the unified core,
and hfail

The three components are not independent lemmas.  Each of them can only
be proved inside the assumption that a `CycleQb8Input` exists, and each
must use the concrete `hstart`/`hcycle` content of that input.  This
file fixes the joint skeleton so that all three components converge on
one contradiction:

    CycleQb8Input h
    -> hterm  : a real block reset (`IsLocalResetTerminal`)
    -> unified core : corrected window upper bound
    -> hfail  : failure lower bound on the same block
    -> contradiction

`TrinityBlock` is the block-level conjunction of the three sides.  The
assembly `trinityBlockExistsOfComponents` is deliberately left as an
open definition: it is the place where the three components will be
joined, and it is not to be treated as an independent theorem.
-/

namespace StringFlow

namespace Trinity

/-- hterm component: every real `CycleQb8Input` supplies a real rise
block whose terminal satisfies the local reset structure. -/
def HtermComponent : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
      ∃ b L t delta : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        CycleBridge.IsLocalResetTerminal t L
          (StringFlow.Word.wordOrbit ((CycleBridge.cyclicSegmentAt w b).take L)
            (StringFlow.Word.wordOrbit (w.take b) m)) delta rt

/-- The selected predecessor identity now carries `hres` on the chosen
block, so it directly closes the hterm component. -/
theorem HtermComponent_of_selected_identity
    (hpre : CycleBridge.cycleQb8InputSelectedRealPredecessorIdentity) :
    HtermComponent :=
  CycleBridge.cycleQb8InputSelectedHtermOfRealPredecessorIdentity hpre

/-- A failure window already carries the real previous terminal and
the reset head, so it directly supplies the hterm component at the same
depth `j` (rotated to the start of the word). -/
theorem HtermComponent_of_failure_window
    (hF : CycleBridge.failureWindowExistence) : HtermComponent := by
  intro m S P w rise c3 h
  rcases hF m S P w rise c3 h with ⟨j, k0, t, delta, s, fw⟩
  rcases fw.hreach with
    ⟨r, _rj, _hk, hprod, hodd, hnd5, _hslt, hOrbitR, _hreset, _hOddRj, _hOrbitRj⟩
  let rt : S6Audit.AngelinaGilbertaRealTerminal :=
    { r := r
      s := s
      k := k0
      hprod := hprod
      hs_odd := hodd
      hs_not_five := hnd5
      hreach := hOrbitR }
  have hterm : CycleBridge.IsLocalResetTerminal t j
      (StringFlow.Word.wordOrbit (w.take j) m) delta rt :=
    (CycleBridge.isLocalResetTerminal_iff_resetHeadEq t j
      (StringFlow.Word.wordOrbit (w.take j) m) delta rt fw.ht fw.hδ).mpr fw.hreset
  have _hjle : j ≤ w.length := by
    rw [h.hlength]
    exact le_of_lt fw.hj_lt
  have hstate : StringFlow.Word.wordOrbit
      ((CycleBridge.cyclicSegmentAt w 0).take j)
      (StringFlow.Word.wordOrbit (w.take 0) m) =
      StringFlow.Word.wordOrbit (w.take j) m := by
    unfold CycleBridge.cyclicSegmentAt
    simp [StringFlow.Word.wordOrbit]
  refine ⟨0, j, t, delta, rt, ?_⟩
  rw [hstate]
  exact hterm

/-- Shared block data for the trinity assembly: the concrete selected
rise block `(b, L, t, delta, rt)` together with the whole `hres` chain.
Both hterm and hfail consume the same copy of this data. -/
structure SelectedBlockData {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) : Type where
  blockB : Nat
  blockL : Nat
  stepT : Nat
  stepDelta : Nat
  rt : S6Audit.AngelinaGilbertaRealTerminal
  hb : CycleBridge.IsCyclicC3RiseBoundaryAt w blockB
  hLge3 : 3 ≤ blockL
  hLle : blockL ≤ w.length
  hpen : (CycleBridge.cyclicSegmentAt w blockB).getI (blockL - 2) = 1
  hseg : ∀ k : Nat, k < blockL →
    (CycleBridge.cyclicSegmentAt w blockB).getI k = 1 ∨
    (CycleBridge.cyclicSegmentAt w blockB).getI k = 2
  hres : ∀ j : Nat, j < blockL - 2 →
    5 * StringFlow.Word.wordOrbit (w.take (blockB - 1)) m + 1 ≡
      2 ^ (CycleBridge.cyclicSegmentAt w blockB).getI j *
        StringFlow.Word.wordOrbit (w.take (blockB - 1)) m
        [MOD 5 ^ (j + 1)]
  ht_last : stepT = (CycleBridge.cyclicSegmentAt w blockB).getI (blockL - 1)
  ht : stepT = 1 ∨ stepT = 2
  hdelta : (stepT = 1 → stepDelta = 1) ∧
    (stepT = 2 → stepDelta = 1 ∨ stepDelta = 3)
  hrt : rt.r = (5 * StringFlow.Word.wordOrbit (w.take (blockB - 1)) m + 1) / 2
  hpred : CycleBridge.cyclic_real_predecessor_identity h blockB hb blockL hLge3 hLle hseg
    stepT stepDelta ht_last ht hdelta rt hrt

/-- The selected predecessor identity extracts into the shared block
data, so hterm and hfail can consume the same `(b, L, hres)`. -/
theorem SelectedBlockData_of_selected_identity
    (hpre : CycleBridge.cycleQb8InputSelectedRealPredecessorIdentity)
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    ∃ _ : SelectedBlockData h, True := by
  rcases hpre m S P w rise c3 h with
    ⟨b, L, t, delta, rt, hb, hLge3, hLle, hpen, hseg, hres,
      ht_last, ht, hdelta, hrt, hpred⟩
  refine ⟨⟨b, L, t, delta, rt, hb, hLge3, hLle, hpen, hseg, hres,
    ht_last, ht, hdelta, hrt, hpred⟩, trivial⟩

/-- Local corrected window upper bounds at the selected maximal rise
endpoint: `hterm` is derived from the carried `hpred`, and the outgoing
C3 edge fixes the head rank at two, so both decisive bounds follow
without the global `decisiveWindowValuationBoundCorrected`. -/
theorem SelectedBlockData_local_window_bounds
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (data : SelectedBlockData h)
    (hstop : data.blockL = w.length ∨
      3 ≤ (CycleBridge.cyclicSegmentAt w data.blockB).getI data.blockL) :
    (data.stepT = 1 →
        BlockAutomaton.t1WindowValue data.blockL data.rt.k data.rt.s ≤
          2 * data.blockL + 11) ∧
    (data.stepT = 2 →
        BlockAutomaton.t2WindowValue data.blockL data.rt.k data.stepDelta data.rt.s ≤
          2 * data.blockL + 10) := by
  have hterm : CycleBridge.IsLocalResetTerminal data.stepT data.blockL
      (StringFlow.Word.wordOrbit
        ((CycleBridge.cyclicSegmentAt w data.blockB).take data.blockL)
        (StringFlow.Word.wordOrbit (w.take data.blockB) m))
      data.stepDelta data.rt :=
    CycleBridge.cyclic_real_predecessor_identity_to_hterm
      h data.blockB data.blockL data.stepT data.stepDelta
      data.hb data.hLge3 data.hLle data.hseg data.ht_last data.ht
      data.hdelta data.rt data.hrt data.hpred
  have hLpos : 1 ≤ data.blockL := by
    exact le_trans (by norm_num : 1 ≤ 3) data.hLge3
  exact RealOrbitLocalLemma.cyclic_local_reset_window_bounds_at_maximal_endpoint
    h data.blockB data.hb hLpos data.hLle data.hseg hstop
    data.rt data.ht data.hdelta hterm

/-- The selected block's carried `hpred` constructs the genuine local
reset `hterm` at the same `(b, L, t, delta, rt)`. -/
theorem SelectedBlockData_hterm
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (data : SelectedBlockData h) :
    CycleBridge.IsLocalResetTerminal data.stepT data.blockL
      (StringFlow.Word.wordOrbit
        ((CycleBridge.cyclicSegmentAt w data.blockB).take data.blockL)
        (StringFlow.Word.wordOrbit (w.take data.blockB) m))
      data.stepDelta data.rt :=
  CycleBridge.cyclic_real_predecessor_identity_to_hterm
    h data.blockB data.blockL data.stepT data.stepDelta
    data.hb data.hLge3 data.hLle data.hseg data.ht_last data.ht
    data.hdelta data.rt data.hrt data.hpred

/-- The hfail-selected block data: exactly the shared hterm block data
`(b, L, hres)` together with the concrete bad-prefix depth and the
rank lower bound at that depth.  The 5-adic `hres` chain is carried as
a field, not derived from the 2-adic layer condition. -/
structure SelectedHfailBlockData {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    Type extends SelectedBlockData h where
  hfailDepth : Nat
  hfailDepth_pos : 1 ≤ hfailDepth
  hfailDepth_lt : blockB + hfailDepth < P
  hincoming : w.getI (blockB + hfailDepth - 1) = stepT
  houtgoing : w.getI (blockB + hfailDepth) = 1 ∨
    w.getI (blockB + hfailDepth) = 2
  hrank : Amiya.hfailRankLowerBoundAt m w (blockB + hfailDepth) stepT

/-- The hfail block selection: every real `CycleQb8Input` supplies one
selected hfail block carrying the same `(b, L, hres)` as hterm. -/
def cycleQb8InputSelectedHfailBlock : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    ∀ h : CycleBridge.CycleQb8Input m S P w rise c3,
      ∃ _ : SelectedHfailBlockData h, True

/-- Unified-core component: the corrected decisive window upper bound.
It is the only window-bound statement the downstream bridge may consume. -/
def UnifiedCoreComponent : Prop :=
  BlockAutomaton.decisiveWindowValuationBoundCorrected

/-- hfail component: every real `CycleQb8Input` supplies a failure
window, i.e. the failure lower bound together with the real reset and
reachability data. -/
def HfailComponent : Prop :=
  CycleBridge.failureWindowExistence

/-- Block-level trinity: one real rise block carries the hterm reset
structure, the corrected window upper bound, and the failure lower
bound at the same length `L`. -/
structure TrinityBlock {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (b L t delta : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal) : Prop where
  ht : t = 1 ∨ t = 2
  hdelta : (t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3)
  hterm : CycleBridge.IsLocalResetTerminal t L
    (StringFlow.Word.wordOrbit ((CycleBridge.cyclicSegmentAt w b).take L)
      (StringFlow.Word.wordOrbit (w.take b) m)) delta rt
  hwin_t1 : t = 1 → BlockAutomaton.t1WindowValue L rt.k rt.s ≤ 2 * L + 11
  hwin_t2 : t = 2 → BlockAutomaton.t2WindowValue L rt.k delta rt.s ≤ 2 * L + 10
  hfail_t1 : t = 1 → 2 * L + 12 ≤ BlockAutomaton.t1WindowValue L rt.k rt.s
  hfail_t2 : t = 2 → 2 * L + 11 ≤ BlockAutomaton.t2WindowValue L rt.k delta rt.s

/-- A selected maximal rise block assembles into a `TrinityBlock`
once the same-block failure lower bounds are supplied; the window upper
bounds are local and no global decisive bound is needed. -/
theorem TrinityBlock_of_selected_block
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (data : SelectedBlockData h)
    (hstop : data.blockL = w.length ∨
      3 ≤ (CycleBridge.cyclicSegmentAt w data.blockB).getI data.blockL)
    (hfail_t1 : data.stepT = 1 →
      2 * data.blockL + 12 ≤
        BlockAutomaton.t1WindowValue data.blockL data.rt.k data.rt.s)
    (hfail_t2 : data.stepT = 2 →
      2 * data.blockL + 11 ≤
        BlockAutomaton.t2WindowValue data.blockL data.rt.k
          data.stepDelta data.rt.s) :
    TrinityBlock h data.blockB data.blockL data.stepT data.stepDelta data.rt := by
  have hwin := SelectedBlockData_local_window_bounds h data hstop
  exact {
    ht := data.ht
    hdelta := data.hdelta
    hterm := SelectedBlockData_hterm h data
    hwin_t1 := hwin.1
    hwin_t2 := hwin.2
    hfail_t1 := hfail_t1
    hfail_t2 := hfail_t2
  }

/-- The three sides of a trinity block contradict: the hfail lower
bound is one above the unified-core upper bound at the same `L`.  This
is the exact algebraic core of the joint proof; no orbit input is used
beyond the block itself. -/
theorem trinity_block_contradicts {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (b L t delta : Nat) (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (tb : TrinityBlock h b L t delta rt) : False := by
  rcases tb with ⟨ht, hdelta, _hterm,
    hwin_t1, hwin_t2, hfail_t1, hfail_t2⟩
  rcases ht with ht1 | ht2
  · have hf : 2 * L + 12 ≤ BlockAutomaton.t1WindowValue L rt.k rt.s :=
      hfail_t1 ht1
    have hw : BlockAutomaton.t1WindowValue L rt.k rt.s ≤ 2 * L + 11 :=
      hwin_t1 ht1
    exact CycleBridge.failure_window_contradicts_t1 L rt.k rt.s
      (BlockAutomaton.t1WindowValue L rt.k rt.s) hf hw
  · rcases hdelta.2 ht2 with hd1 | hd3
    · subst delta
      exact CycleBridge.failure_window_contradicts_t2 L rt.k 1 rt.s
        (BlockAutomaton.t2WindowValue L rt.k 1 rt.s)
        (hfail_t2 ht2) (hwin_t2 ht2)
    · subst delta
      exact CycleBridge.failure_window_contradicts_t2 L rt.k 3 rt.s
        (BlockAutomaton.t2WindowValue L rt.k 3 rt.s)
        (hfail_t2 ht2) (hwin_t2 ht2)

/-- Every real `CycleQb8Input` admits a trinity block. -/
def trinityBlockExists : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    ∀ h : CycleBridge.CycleQb8Input m S P w rise c3,
      ∃ b L t delta : Nat, ∃ rt : S6Audit.AngelinaGilbertaRealTerminal,
        TrinityBlock h b L t delta rt

/-- A trinity block in every `CycleQb8Input` rules out a positive cycle
of `7`: the block's lower and upper bounds contradict. -/
theorem trinity_no_cycle_of_block_exists
    (hA : trinityBlockExists) : ¬ OrbitCycle 7 := by
  intro hcycle
  rcases CycleBridge.orbit_cycle_imp_cycle_qb8_input hcycle with
    ⟨c, p, m, S, w, rise, c3, hinput, _hw, _hrise, _hc3, _hS, _hm⟩
  rcases hA m S p w rise c3 hinput with ⟨b, L, t, delta, rt, tb⟩
  exact trinity_block_contradicts hinput b L t delta rt tb

/-- Conditional unboundedness from the trinity-block skeleton. -/
theorem trinity_unbounded_of_block_exists
    (hA : trinityBlockExists) : IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 (trinity_no_cycle_of_block_exists hA)

/-- Open assembly: the three components must be joined into a trinity
block.  This is deliberately a definition, not a theorem: it is the
remaining joint work, and it is not to be treated as blocked. -/
def trinityBlockExistsOfComponents : Prop :=
  HtermComponent → UnifiedCoreComponent → HfailComponent → trinityBlockExists

/-- Top-level conditional assembly: once the unified-core window bound
and the hfail failure window are supplied, the closed bridge already
gives unboundedness.  The hterm component remains an explicit part of
the trinity signature; its proof is the source of the real reset data
used by the hfail construction. -/
theorem trinity_unbounded_of_components
    (_hH : HtermComponent) (hU : UnifiedCoreComponent) (hF : HfailComponent) :
    IsUnboundedOrbit 7 := by
  exact CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window
    hU hF

/-- hterm-side valuation: the selected mod `5^(L-1)` congruence at a
real C3-to-rise block whose penultimate rise step is `1`.  This is the
shared valuation fact behind `HtermComponent`.  It is stated here in
self-contained form; the corresponding file-level statement lives in
`RiseDecompositionAssembly.cyclic_real_predecessor_congruence_selected`. -/
def HtermValuation : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    ∀ _h : CycleBridge.CycleQb8Input m S P w rise c3,
      ∀ b L : Nat, ∀ _hb : CycleBridge.IsCyclicC3RiseBoundaryAt w b,
        ∀ _hLge3 : 3 ≤ L, ∀ _hLle : L ≤ w.length,
          ∀ _hseg : ∀ k : Nat, k < L →
            (CycleBridge.cyclicSegmentAt w b).getI k = 1 ∨
            (CycleBridge.cyclicSegmentAt w b).getI k = 2,
            (CycleBridge.cyclicSegmentAt w b).getI (L - 2) = 1 →
            ∀ _hres : ∀ j : Nat, j < L - 2 →
              5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1 ≡
                2 ^ (CycleBridge.cyclicSegmentAt w b).getI j *
                  StringFlow.Word.wordOrbit (w.take (b - 1)) m
                  [MOD 5 ^ (j + 1)],
            StringFlow.Word.wordOrbit
              ((CycleBridge.cyclicSegmentAt w b).take (L - 1))
              (StringFlow.Word.wordOrbit (w.take b) m) %
                5 ^ (L - 1) =
              (2 ^ (w.getI (b - 1) - 1) *
                StringFlow.Word.wordOrbit (w.take b) m) %
                5 ^ (L - 1)

/-- The hterm valuation closes from the selected block's `hres` chain:
this is exactly the telescope theorem in `RiseDecompositionAssembly`. -/
theorem HtermValuation_of_residue_chain : HtermValuation := by
  intro m S P w rise c3 h b L hb hLge3 hLle hseg hpen hres
  exact CycleBridge.cyclic_real_predecessor_congruence_selected_of_residue_chain
    h b L hb hLge3 hLle hpen hres

/-- Unified-core valuation: the corrected decisive window upper bound. -/
def UnifiedCoreValuation : Prop :=
  BlockAutomaton.decisiveWindowValuationBoundCorrected

/-- hfail-side valuation: for the concrete `(c,p)` supplied by
`hcycle`, the internal rank lower bound holds on the 7-orbit states
`fiveXPlusOneOrbit 7 (c+j)`.  This is the shared valuation fact behind
`HfailComponent`.  It is stated here in self-contained form; the
corresponding layer reduction lives in
`amiya.cycleWordLayerCondition` /
`amiya.cycleWordInternalRankLowerBound`. -/
def HfailValuation : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    ∀ _h : CycleBridge.CycleQb8Input m S P w rise c3,
      ∃ c p j t : Nat,
        StringFlow.fiveXPlusOneOrbit 7 c = m ∧
        w = CycleBridge.cycleWord c p ∧
        1 ≤ j ∧ j < p ∧
        (t = 1 ∨ t = 2) ∧
        (CycleBridge.cycleWord c p).getI (j - 1) = t ∧
        (t = 1 → 2 * j + 11 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1)) ∧
        (t = 2 → 2 * j + 9 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1))

/-- The exact layer input behind `HfailValuation`: one concrete
`(c, p, j, t)` at which `cycleWordLayerCondition` holds. -/
def HfailLayerCondition : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    ∀ _h : CycleBridge.CycleQb8Input m S P w rise c3,
      ∃ c p j t : Nat,
        m = StringFlow.fiveXPlusOneOrbit 7 c ∧
        w = CycleBridge.cycleWord c p ∧
        1 ≤ j ∧ j < p ∧
        (t = 1 ∨ t = 2) ∧
        (CycleBridge.cycleWord c p).getI (j - 1) = t ∧
        ((CycleBridge.cycleWord c p).getI j = 1 ∨
          (CycleBridge.cycleWord c p).getI j = 2) ∧
        Amiya.cycleWordLayerCondition c p j t

/-- The hfail valuation closes from the layer condition: the existing
`cycleWordInternalRankLowerBound` bridge and the `hcycle` prefix
identity rewrite the carried rank bound to the concrete orbit state. -/
theorem HfailValuation_of_layer
    (hlayer : HfailLayerCondition) : HfailValuation := by
  intro m S P w rise c3 h
  rcases hlayer m S P w rise c3 h with
    ⟨c, p, j, t, hm, hw, hj1, hjp, ht, hinc, hout, hlc⟩
  have hS : S = StringFlow.wordWeight (CycleBridge.cycleWord c p) := by
    rw [← h.hweight, hw]
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hrank := Amiya.cycleWordInternalRankLowerBound_of_layer
    c p j t hj1 hjp ht hinc hout hlc
  rcases Amiya.cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt
    h c p hw hm hP hS hrank with
    ⟨j', t', hj1', hjp', _hreal, ht', hinc', _hout', hrank'⟩
  have hjp'p : j' < p := by rwa [hP] at hjp'
  have hpre : StringFlow.Word.wordOrbit (w.take j') m =
      StringFlow.fiveXPlusOneOrbit 7 (c + j') := by
    rw [hw, hm]
    exact CycleBridge.cycleWord_prefix_orbit_eq c p j' (le_of_lt hjp'p)
  refine ⟨c, p, j', t', hm.symm, hw, hj1', hjp'p, ht',
    (by simpa [hw] using hinc'), ?_, ?_⟩
  · intro ht1
    have hr := hrank'.1 ht1
    rw [hpre] at hr
    exact hr
  · intro ht2
    have hr := hrank'.2 ht2
    rw [hpre] at hr
    exact hr

/-- The hfail valuation closes from the selected hfail block: the same
`(b, L, hres)` data carried by hterm supplies the concrete orbit
prefix, and the carried rank lower bound is rewritten to the
`hcycle`-anchored orbit state. -/
theorem HfailValuation_of_selected_hfail
    (hsel : cycleQb8InputSelectedHfailBlock) : HfailValuation := by
  intro m S P w rise c3 h
  rcases hsel m S P w rise c3 h with ⟨d, _⟩
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  let j : Nat := d.blockB + d.hfailDepth
  have hjp : j < p := by
    dsimp [j]
    rw [← hP]
    exact d.hfailDepth_lt
  have hpre : StringFlow.Word.wordOrbit (w.take j) m =
      StringFlow.fiveXPlusOneOrbit 7 (c + j) := by
    rw [hw, hm]
    exact CycleBridge.cycleWord_prefix_orbit_eq c p j (le_of_lt hjp)
  refine ⟨c, p, j, d.stepT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hm.symm
  · exact hw
  · dsimp [j]
    have hle : d.hfailDepth ≤ d.blockB + d.hfailDepth := by
      rw [Nat.add_comm]
      exact Nat.le_add_right d.hfailDepth d.blockB
    exact Nat.le_trans d.hfailDepth_pos hle
  · exact hjp
  · exact d.ht
  · simpa [j, hw] using d.hincoming
  · intro ht1
    have hr := d.hrank.1 ht1
    rw [show d.blockB + d.hfailDepth = j by rfl] at hr
    rw [hpre] at hr
    exact hr
  · intro ht2
    have hr := d.hrank.2 ht2
    rw [show d.blockB + d.hfailDepth = j by rfl] at hr
    rw [hpre] at hr
    exact hr

/-- The hfail valuation also closes directly from the failure-window
component: the carried failure lower bounds convert back to the exact
prefix rank lower bounds, and `hcycle` anchors them to the concrete
orbit states. -/
theorem HfailValuation_of_failure_window
    (hF : CycleBridge.failureWindowExistence) : HfailValuation := by
  intro m S P w rise c3 h
  rcases hF m S P w rise c3 h with ⟨j, k0, t, delta, s, fw⟩
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hj1 : 1 ≤ j := by
    have hk : k0 + 1 ≤ j := fw.hk
    omega
  have hjp : j < p := by
    rw [← hP]
    exact fw.hj_lt
  have hpre : StringFlow.Word.wordOrbit (w.take j) m =
      StringFlow.fiveXPlusOneOrbit 7 (c + j) := by
    rw [hw, hm]
    exact CycleBridge.cycleWord_prefix_orbit_eq c p j (le_of_lt hjp)
  refine ⟨c, p, j, t, hm.symm, hw, hj1, hjp, fw.ht,
    (by simpa [hw] using fw.hincoming), ?_, ?_⟩
  · intro ht1
    have hδ1 : delta = 1 := fw.hδ.1 ht1
    subst t
    subst delta
    have hrank := Amiya.hfail_t1_rank_of_hfail j k0 s
      (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset (fw.hfail_t1 rfl)
    rw [hpre] at hrank
    exact hrank
  · intro ht2
    subst t
    have hrank := Amiya.hfail_t2_rank_of_hfail j k0 delta s
      (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset (fw.hfail_t2 rfl)
    rw [hpre] at hrank
    exact hrank

/-- The joint 7-orbit valuation core: the three valuation facts are
projections of one shared structure.  This is deliberately a
definition, not a theorem: proving it once is the remaining joint
work. -/
def TrinityCoreValuation : Prop :=
  HtermValuation ∧ UnifiedCoreValuation ∧ HfailValuation

/-- The joint valuation core closes once the exact layer condition and
the corrected window upper bound are supplied.  hterm is already
closed from the selected `hres` chain; hfail closes from the layer
condition via the internal rank bridge. -/
theorem TrinityCoreValuation_of_layer_and_window
    (hlayer : HfailLayerCondition)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    TrinityCoreValuation := by
  exact ⟨HtermValuation_of_residue_chain, hwin, HfailValuation_of_layer hlayer⟩

/-- The joint valuation core closes from the selected hfail block:
the same `(b, L, hres)` data is consumed by hterm and hfail, so only
the corrected window upper bound remains as an external valuation
input. -/
theorem TrinityCoreValuation_of_selected_hfail_and_window
    (hsel : cycleQb8InputSelectedHfailBlock)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    TrinityCoreValuation := by
  exact ⟨HtermValuation_of_residue_chain, hwin, HfailValuation_of_selected_hfail hsel⟩

/-- The joint valuation core closes from the two real components that
the failure-window route still needs: `failureWindowExistence` and the
corrected decisive window upper bound.  hterm and the hfail valuation
are both projections of the failure window. -/
theorem TrinityCoreValuation_of_failure_window_and_window_bound
    (hF : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    TrinityCoreValuation := by
  exact ⟨HtermValuation_of_residue_chain, hwin, HfailValuation_of_failure_window hF⟩

/-- Open assembly from the joint valuation core to a trinity block in
every `CycleQb8Input`.  This is the trinity-level join of the three
shared valuation facts; it is not to be treated as blocked. -/
def trinityBlockExistsOfCoreValuation : Prop :=
  TrinityCoreValuation → trinityBlockExists

/-- The final trinity-level assembly: once the joint valuation core is
closed and the core valuation is converted to a trinity block, the
public divergence statement follows. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_core
    (hcore : TrinityCoreValuation)
    (hasm : trinityBlockExistsOfCoreValuation) :
    IsUnboundedOrbit 7 :=
  trinity_unbounded_of_block_exists (hasm hcore)

/-- Direct final bridge on the failure-window route: the corrected
window upper bound and `failureWindowExistence` already suffice for the
public divergence statement. -/
theorem five_x_plus_one_diverges_at_7_of_failure_window_and_window_bound
    (hF : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    IsUnboundedOrbit 7 :=
  CycleBridge.five_x_plus_one_diverges_at_7_of_window_bound_and_failure_window
    hwin hF

end Trinity

end StringFlow
