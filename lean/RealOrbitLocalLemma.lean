import PmiLocalLemma
import BlockAutomaton
import S6AuditStage1
import UnifiedCoreBridge
import CycleBridge
import kaltsit

/-!
# Real-orbit window reduction

The two corrected window valuations are exactly the block-head rank
`v2(rj+1)` plus the fixed reset-step constant.  This file proves only
those exact algebraic reductions; it does not claim the block-head rank
bound itself.
-/

namespace StringFlow.RealOrbitLocalLemma

open S6Audit

/-- For a `t=1` reset, the window value is `1+v2(rj+1)`. -/
theorem t1WindowValue_eq_twoValuation_rj_plus_one
    (j k0 s rj : Nat) (hreset : ResetHeadEq s j k0 1 1 rj) :
    BlockAutomaton.t1WindowValue j k0 s =
      1 + twoValuation (rj + 1) := by
  unfold BlockAutomaton.t1WindowValue
  rcases hreset with h1 | h2
  · rcases h1 with ⟨_ht, _hδ, heq⟩
    rw [← heq]
    have hpos : 0 < rj + 1 := by positivity
    have hval := StringFlow.twoValuation_mul_two (rj + 1) hpos
    simpa [Nat.add_comm] using hval
  · rcases h2 with ⟨ht, _hδ, _heq⟩
    omega

/-- For a `t=2` reset, the window value is `2+v2(rj+1)`. -/
theorem t2WindowValue_eq_twoValuation_rj_plus_one
    (j k0 δ s rj : Nat) (hreset : ResetHeadEq s j k0 2 δ rj) :
    BlockAutomaton.t2WindowValue j k0 δ s =
      2 + twoValuation (rj + 1) := by
  unfold BlockAutomaton.t2WindowValue
  rcases hreset with h1 | h2
  · rcases h1 with ⟨ht, _hδ, _heq⟩
    omega
  · rcases h2 with ⟨_ht, _hδ, heq⟩
    rw [← heq]
    have hpos : 0 < rj + 1 := by positivity
    have hval := StringFlow.Lte.twoValuation_mul_two_pow 2 (rj + 1) hpos
    simpa [Nat.add_comm] using hval

/-- The corrected `t=1` window bound is exactly the block-head rank
bound `v2(rj+1) ≤ 2j+10`. -/
theorem t1WindowBoundCorrected_iff_rj_rank
    (j k0 s rj : Nat)
    (hreset : ResetHeadEq s j k0 1 1 rj) :
    (BlockAutomaton.t1WindowValue j k0 s ≤ 2 * j + 11) ↔
      twoValuation (rj + 1) ≤ 2 * j + 10 := by
  have hval := t1WindowValue_eq_twoValuation_rj_plus_one j k0 s rj hreset
  rw [hval]
  omega

/-- The corrected `t=2` window bound is exactly the block-head rank
bound `v2(rj+1) ≤ 2j+8`. -/
theorem t2WindowBoundCorrected_iff_rj_rank
    (j k0 δ s rj : Nat)
    (hreset : ResetHeadEq s j k0 2 δ rj) :
    (BlockAutomaton.t2WindowValue j k0 δ s ≤ 2 * j + 10) ↔
      twoValuation (rj + 1) ≤ 2 * j + 8 := by
  have hval := t2WindowValue_eq_twoValuation_rj_plus_one j k0 δ s rj hreset
  rw [hval]
  omega

/-- The depth-aligned reset-window hypothesis: `r` is the even
intermediate of the depth `j-2 → j-1` step of the actual 7-orbit. -/
def ResetWindowReachabilityAtDepth
    (j k0 t δ s r rj : Nat) : Prop :=
  ResetWindowReachability j k0 t δ s ∧
  r = (5 * fullOrbitIter (j - 2) + 1) / 2 ∧
  s * 5 ^ k0 = r + 1

/-- For fixed reset parameters, the reset equation determines its block
head uniquely.  This lets an outer, explicitly named `rj` inherit the
full-orbit witness stored existentially in `ResetWindowReachability`. -/
theorem resetHeadEq_rj_unique
    (j k0 t δ s rj₁ rj₂ : Nat)
    (h₁ : ResetHeadEq s j k0 t δ rj₁)
    (h₂ : ResetHeadEq s j k0 t δ rj₂) :
    rj₁ = rj₂ := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · rcases h₁ with ⟨_ht₁, _hδ₁, heq₁⟩
    rcases h₂ with ⟨_ht₂, _hδ₂, heq₂⟩
    omega
  · rcases h₁ with ⟨ht₁, _hδ₁, _heq₁⟩
    rcases h₂ with ⟨ht₂, _hδ₂, _heq₂⟩
    omega
  · rcases h₁ with ⟨ht₁, _hδ₁, _heq₁⟩
    rcases h₂ with ⟨ht₂, _hδ₂, _heq₂⟩
    omega
  · rcases h₁ with ⟨_ht₁, _hδ₁, heq₁⟩
    rcases h₂ with ⟨_ht₂, _hδ₂, heq₂⟩
    omega

/-- A reachable reset window has positive reset depth. -/
theorem resetWindowReachability_j_pos
    (j k0 t δ s : Nat)
    (hreach : ResetWindowReachability j k0 t δ s) :
    1 ≤ j := by
  rcases hreach with ⟨_r, _rj, hk, _hprod, _hodd, _hnd5, _hslt,
    _hOrbitR, _hreset, _hOddRj, _hOrbitRj⟩
  omega

/-- The explicitly named reset head is on the full orbit whenever it
satisfies the same reset equation as a reachable-window witness. -/
theorem resetWindowReachability_explicit_fullOrbit
    (j k0 t δ s rj : Nat)
    (hreset : ResetHeadEq s j k0 t δ rj)
    (hreach : ResetWindowReachability j k0 t δ s) :
    FullOrbitFrom7 rj := by
  rcases hreach with ⟨_r, rj', _hk, _hprod, _hodd, _hnd5, _hslt,
    _hOrbitR, hreset', _hOddRj, hOrbitRj⟩
  have hrj : rj = rj' :=
    resetHeadEq_rj_unique j k0 t δ s rj rj' hreset hreset'
  simpa [hrj] using hOrbitRj

/-- A positive-depth reset head cannot be the initial full-orbit state
`7`, since the reset equation forces residue `3` or `4` modulo `5`. -/
theorem resetHeadEq_ne_seven_of_j_pos
    (j k0 t δ s rj : Nat) (hj : 1 ≤ j)
    (hreset : ResetHeadEq s j k0 t δ rj) :
    rj ≠ 7 := by
  have hmod := reset_head_mod_five s j k0 t δ rj hj hreset
  rcases hreset with h₁ | h₂
  · have hr : rj % 5 = 3 := hmod.1 h₁.1
    intro heq
    subst rj
    norm_num at hr
  · have hr : rj % 5 = 4 := hmod.2 h₂.1
    intro heq
    subst rj
    norm_num at hr

/-- The explicit reset head occurs at a positive full-orbit depth. -/
theorem resetWindowReachability_explicit_fullOrbit_pos
    (j k0 t δ s rj : Nat)
    (hreset : ResetHeadEq s j k0 t δ rj)
    (hreach : ResetWindowReachability j k0 t δ s) :
    ∃ n : Nat, 1 ≤ n ∧ fullOrbitIter n = rj := by
  have hj : 1 ≤ j := resetWindowReachability_j_pos j k0 t δ s hreach
  have hne : rj ≠ 7 := resetHeadEq_ne_seven_of_j_pos
    j k0 t δ s rj hj hreset
  rcases resetWindowReachability_explicit_fullOrbit
      j k0 t δ s rj hreset hreach with ⟨n, hiter⟩
  refine ⟨n, ?_, hiter⟩
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  simp [fullOrbitIter] at hiter
  exact hne hiter.symm

/-- Eliminate the window parameters `s,k0` down to the genuine previous
terminal `r`: its successor is below `5^(j-1)` and it is reachable in
the general divisor-word orbit. -/
theorem resetWindowReachability_previous_data
    (j k0 t δ s : Nat)
    (hreach : ResetWindowReachability j k0 t δ s) :
    ∃ r : Nat,
      s * 5 ^ k0 = r + 1 ∧
      r + 1 < 5 ^ (j - 1) ∧
      GeneralOrbitFrom7 r := by
  rcases hreach with ⟨r, _rj, hk, hprod, _hodd, _hnd5, hslt,
    hOrbitR, _hreset, _hOddRj, _hOrbitRj⟩
  have hk' : k0 ≤ j - 1 := by omega
  have hmul : s * 5 ^ k0 < 5 ^ (j - 1 - k0) * 5 ^ k0 :=
    Nat.mul_lt_mul_of_pos_right hslt (Nat.pow_pos (by decide : 0 < 5))
  have hpow : 5 ^ (j - 1 - k0) * 5 ^ k0 = 5 ^ (j - 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  refine ⟨r, hprod, ?_, hOrbitR⟩
  rw [hpow] at hmul
  rw [← hprod]
  exact hmul

/-- The depth alignment forces the previous terminal to have no
factor of `5`: `k0 = 0`. -/
theorem previousTerminalDepth_k0_eq_zero
    (j k0 t δ s r _rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t δ s r rj) :
    k0 = 0 := by
  rcases hAt with ⟨_hreach, hdepth, hprod⟩
  let f := fullOrbitIter (j - 2)
  have hoddF : IsOdd f := fullOrbitIter_odd (j - 2)
  have hmod : (5 * f + 1) % 2 = 0 := by
    have hf : f % 2 = 1 := hoddF
    rw [Nat.add_mod, Nat.mul_mod]
    rw [show 5 % 2 = 1 by norm_num, hf]
  have hdvd : 2 ∣ 5 * f + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have h2r : 2 * r = 5 * f + 1 := by
    have hmul := Nat.mul_div_cancel' hdvd
    simpa [← hdepth, f] using hmul
  have hkey : 2 * s * 5 ^ k0 = 5 * f + 3 := by
    have hprod' : 2 * (s * 5 ^ k0) = 2 * r + 2 := by nlinarith [hprod]
    have h2r' : 2 * r + 2 = 5 * f + 3 := by nlinarith [h2r]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hprod'.trans h2r'
  by_contra hkne
  have hkpos : 1 ≤ k0 := by omega
  have hpow5 : (5 ^ k0) % 5 = 0 := by
    have hdvd5 : 5 ∣ 5 ^ k0 := by
      refine ⟨5 ^ (k0 - 1), ?_⟩
      rw [show k0 = (k0 - 1) + 1 by omega]
      rw [Nat.pow_succ]
      rw [Nat.mul_comm]
      rw [show k0 - 1 + 1 - 1 = k0 - 1 by omega]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd5
  have hright : (5 * f + 3) % 5 = 3 := by norm_num
  have hleft : (2 * s * 5 ^ k0) % 5 = 0 := by
    rw [Nat.mul_mod]
    rw [hpow5]
    simp
  have hkeymod : (2 * s * 5 ^ k0) % 5 = (5 * f + 3) % 5 := by
    rw [hkey]
  rw [hleft, hright] at hkeymod
  norm_num at hkeymod

/-- With `k0=0`, the previous-terminal odd part is exactly
`(5*f(j-2)+3)/2`. -/
theorem previousTerminalDepth_s_eq
    (j k0 t δ s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t δ s r rj) :
    s = (5 * fullOrbitIter (j - 2) + 3) / 2 := by
  have hk0 : k0 = 0 := previousTerminalDepth_k0_eq_zero j k0 t δ s r rj hAt
  subst k0
  rcases hAt with ⟨_hreach, hdepth, hprod⟩
  let f := fullOrbitIter (j - 2)
  have hoddF : IsOdd f := fullOrbitIter_odd (j - 2)
  have hmod : (5 * f + 1) % 2 = 0 := by
    have hf : f % 2 = 1 := hoddF
    rw [Nat.add_mod, Nat.mul_mod]
    rw [show 5 % 2 = 1 by norm_num, hf]
  have hdvd : 2 ∣ 5 * f + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have h2r : 2 * r = 5 * f + 1 := by
    have hmul := Nat.mul_div_cancel' hdvd
    simpa [← hdepth, f] using hmul
  have hprod' : s = r + 1 := by simpa using hprod
  have htwos : 2 * s = 5 * f + 3 := by nlinarith
  have hdvd3 : 2 ∣ 5 * f + 3 := ⟨s, htwos.symm⟩
  have hmul := Nat.mul_div_cancel' hdvd3
  have hdiv_s : (5 * f + 3) / 2 = s :=
    Nat.mul_left_cancel (by decide : 0 < 2) (hmul.trans htwos.symm)
  exact hdiv_s.symm

/-- Once reverse stripping has stopped, further fuel does not move it. -/
theorem reverseStripN_stop_all (S : Nat)
    (h4 : S % 5 ≠ 4) (h0 : S % 5 ≠ 0) :
    ∀ n : Nat, reverseStripN n S = S := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reverseStripN_stop n S h4 h0]

/-- The depth-aligned reset state strips once to
`f(j-2)+1`, where `f` is the real full orbit. -/
theorem reverseStripN_one_s_eq_fullOrbit_plus_one
    (j k0 t δ s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t δ s r rj) :
    reverseStripN 1 s = fullOrbitIter (j - 2) + 1 := by
  let f := fullOrbitIter (j - 2)
  have hs : s = (5 * f + 3) / 2 := by
    simpa [f] using previousTerminalDepth_s_eq j k0 t δ s r rj hAt
  have hodd : IsOdd f := by
    dsimp [f]
    exact fullOrbitIter_odd (j - 2)
  have hmod : (5 * f + 3) % 2 = 0 := by
    have hf : f % 2 = 1 := hodd
    rw [Nat.add_mod, Nat.mul_mod]
    rw [show 5 % 2 = 1 by norm_num, hf]
  have hdvd : 2 ∣ 5 * f + 3 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have h2s : 2 * s = 5 * f + 3 := by
    rw [hs]
    exact Nat.mul_div_cancel' hdvd
  have hsmod : s % 5 = 4 := s_mod_five_of_t1 f s h2s
  have hdiv : (2 * s + 2) / 5 = f + 1 := div_t1 f s h2s
  change reverseStripN (0 + 1) s = f + 1
  rw [reverseStripN_t1 0 s hsmod, hdiv]
  rfl

/-- A small step of the real full orbit reverses under
`reverseStripN`: `f(i)+1` strips to `f(i-1)+1` when
`orbitStepWeight(i-1) <= 2`. -/
theorem reverseStripN_fullOrbit_step_le_two (i : Nat)
    (hi : 1 ≤ i) (hsmall : orbitStepWeight (i - 1) ≤ 2) :
    reverseStripN 1 (fullOrbitIter i + 1) =
      fullOrbitIter (i - 1) + 1 := by
  let x := fullOrbitIter (i - 1)
  have hge1 : 1 ≤ orbitStepWeight (i - 1) := by
    dsimp [orbitStepWeight]
    exact twoValuation_five_mul_add_one_ge_one (fullOrbitIter (i - 1))
      (fullOrbitIter_odd (i - 1))
  have hcase : orbitStepWeight (i - 1) = 1 ∨ orbitStepWeight (i - 1) = 2 := by
    omega
  have hiter : fullOrbitIter i = fullOrbitStep x := by
    dsimp [x]
    have hi' : i = Nat.succ (i - 1) := by omega
    rw [hi']
    rfl
  rcases hcase with h1 | h2
  · have hmul0 := fullOrbitStep_mul_eq x
    have h1' : S6Audit.twoValuation (5 * x + 1) = 1 := by
      simpa [x, orbitStepWeight] using h1
    rw [h1'] at hmul0
    have hmul : 2 * fullOrbitStep x = 5 * x + 1 := by
      simpa using hmul0
    have hstep : 2 * fullOrbitIter i = 5 * x + 1 := by
      rw [hiter]
      exact hmul
    have h2s : 2 * (fullOrbitIter i + 1) = 5 * x + 3 := by omega
    have hsmod : (fullOrbitIter i + 1) % 5 = 4 :=
      s_mod_five_of_t1 x (fullOrbitIter i + 1) h2s
    have hdiv : (2 * (fullOrbitIter i + 1) + 2) / 5 = x + 1 :=
      div_t1 x (fullOrbitIter i + 1) h2s
    change reverseStripN (0 + 1) (fullOrbitIter i + 1) = x + 1
    rw [reverseStripN_t1 0 (fullOrbitIter i + 1) hsmod, hdiv]
    rfl
  · have hmul0 := fullOrbitStep_mul_eq x
    have h2' : S6Audit.twoValuation (5 * x + 1) = 2 := by
      simpa [x, orbitStepWeight] using h2
    rw [h2'] at hmul0
    have hmul : 4 * fullOrbitStep x = 5 * x + 1 := by
      simpa using hmul0
    have hstep : 4 * fullOrbitIter i = 5 * x + 1 := by
      rw [hiter]
      exact hmul
    have h4s : 4 * (fullOrbitIter i + 1) = 5 * x + 5 := by omega
    have hsmod : (fullOrbitIter i + 1) % 5 = 0 :=
      s_mod_five_of_t2 x (fullOrbitIter i + 1) h4s
    have hdiv : (4 * (fullOrbitIter i + 1)) / 5 = x + 1 :=
      div_t2 x (fullOrbitIter i + 1) h4s
    change reverseStripN (0 + 1) (fullOrbitIter i + 1) = x + 1
    rw [reverseStripN_t2 0 (fullOrbitIter i + 1) hsmod, hdiv]
    rfl

/-- The inverse residue `2^W == 4 (mod 5)` pins `W == 2 (mod 4)`. -/
lemma two_pow_mod5_eq_four_imp (W : Nat) (h : (2 ^ W) % 5 = 4) :
    W % 4 = 2 := by
  have hdiv := Nat.div_add_mod W 4
  have hpow : 2 ^ W = 2 ^ (4 * (W / 4)) * 2 ^ (W % 4) := by
    have hW : W = 4 * (W / 4) + W % 4 := hdiv.symm
    conv_lhs => rw [hW]
    rw [Nat.pow_add]
  have hq := two_pow_four_mul_mod5 (W / 4)
  have hmod : (2 ^ W) % 5 = (2 ^ (W % 4)) % 5 := by
    rw [hpow, Nat.mul_mod, hq]
    norm_num
  have hlt : W % 4 < 4 := Nat.mod_lt W (by norm_num)
  interval_cases hw : W % 4
  · norm_num at hmod h
    omega
  · norm_num at hmod h
    omega
  · rfl
  · norm_num at hmod h
    omega

/-- The first fixed barrier: the real orbit state at depth 16 is not
enterable by a `t=1` or `t=2` reverse step. -/
theorem reverseStripN_fullOrbit_step_16_stop :
    reverseStripN 1 (fullOrbitIter 16 + 1) = fullOrbitIter 16 + 1 := by
  have hmod : (fullOrbitIter 16 + 1) % 5 = 3 := by
    norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  have h4 : (fullOrbitIter 16 + 1) % 5 ≠ 4 := by omega
  have h0 : (fullOrbitIter 16 + 1) % 5 ≠ 0 := by omega
  change reverseStripN (0 + 1) (fullOrbitIter 16 + 1) = fullOrbitIter 16 + 1
  exact reverseStripN_stop 0 (fullOrbitIter 16 + 1) h4 h0

/-- The second fixed barrier: the real orbit state at depth 18 is not
enterable by a `t=1` or `t=2` reverse step. -/
theorem reverseStripN_fullOrbit_step_18_stop :
    reverseStripN 1 (fullOrbitIter 18 + 1) = fullOrbitIter 18 + 1 := by
  have hmod : (fullOrbitIter 18 + 1) % 5 = 2 := by
    norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  have h4 : (fullOrbitIter 18 + 1) % 5 ≠ 4 := by omega
  have h0 : (fullOrbitIter 18 + 1) % 5 ≠ 0 := by omega
  change reverseStripN (0 + 1) (fullOrbitIter 18 + 1) = fullOrbitIter 18 + 1
  exact reverseStripN_stop 0 (fullOrbitIter 18 + 1) h4 h0

/-- `reverseStripN` is compositional: one step followed by `n` steps
equals `n+1` steps. -/
theorem reverseStripN_succ (n S : Nat) :
    reverseStripN (n + 1) S = reverseStripN n (reverseStripN 1 S) := by
  by_cases h4 : S % 5 = 4
  · have hstep := reverseStripN_t1 0 S h4
    have hstepn := reverseStripN_t1 n S h4
    rw [hstepn, hstep]
    rfl
  · by_cases h0 : S % 5 = 0
    · have hstep := reverseStripN_t2 0 S h0
      have hstepn := reverseStripN_t2 n S h0
      rw [hstepn, hstep]
      rfl
    · have hne4 : S % 5 ≠ 4 := h4
      have hne0 : S % 5 ≠ 0 := h0
      have hstep := reverseStripN_stop 0 S hne4 hne0
      have hstepn := reverseStripN_stop n S hne4 hne0
      have hall := reverseStripN_stop_all S hne4 hne0 n
      rw [hstepn, hstep, hall]

/-- The depth-16 barrier is permanent under arbitrary fuel. -/
theorem reverseStripN_fullOrbit_step_16_no_eight :
    ∀ m : Nat, reverseStripN m (fullOrbitIter 16 + 1) ≠ 8 := by
  intro m
  have hmod : (fullOrbitIter 16 + 1) % 5 = 3 := by
    norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  have h4 : (fullOrbitIter 16 + 1) % 5 ≠ 4 := by omega
  have h0 : (fullOrbitIter 16 + 1) % 5 ≠ 0 := by omega
  have hstop := reverseStripN_stop_all (fullOrbitIter 16 + 1) h4 h0 m
  intro h8
  rw [hstop] at h8
  norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at h8

/-- The depth-17 state strips once to the depth-16 barrier, so it never
reaches `8`. -/
theorem reverseStripN_fullOrbit_step_17_no_eight :
    ∀ m : Nat, reverseStripN m (fullOrbitIter 17 + 1) ≠ 8 := by
  intro m
  cases m with
  | zero =>
      intro h
      norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at h
      rw [reverseStripN] at h
      norm_num at h
  | succ n =>
      have hsmall : orbitStepWeight 16 ≤ 2 := by
        rw [orbitStepWeight_16_eq_one]
        norm_num
      have hfirst := reverseStripN_fullOrbit_step_le_two 17 (by norm_num) hsmall
      have hcomp := reverseStripN_succ n (fullOrbitIter 17 + 1)
      rw [hcomp, hfirst]
      exact reverseStripN_fullOrbit_step_16_no_eight n

/-- The depth-18 barrier is permanent under arbitrary fuel. -/
theorem reverseStripN_fullOrbit_step_18_no_eight :
    ∀ m : Nat, reverseStripN m (fullOrbitIter 18 + 1) ≠ 8 := by
  intro m
  have hmod : (fullOrbitIter 18 + 1) % 5 = 2 := by
    norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  have h4 : (fullOrbitIter 18 + 1) % 5 ≠ 4 := by omega
  have h0 : (fullOrbitIter 18 + 1) % 5 ≠ 0 := by omega
  have hstop := reverseStripN_stop_all (fullOrbitIter 18 + 1) h4 h0 m
  intro h8
  rw [hstop] at h8
  norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at h8

/-- Any legal `{1,2}` witness for the depth-aligned even terminal has
length at most 16: otherwise its prefix would have to contain the
depth-15 step of weight 3. -/
theorem previous_terminal_word_length_le_16
    (s j k r : Nat) (w : List Nat)
    (hprev : IsPreviousEvenTerminal s j k)
    (hprod : s * 5 ^ k = r + 1)
    (hk : k = 0)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hw : StringFlow.Word.wordOrbit w 7 = r) :
    w.length ≤ 16 := by
  subst k
  rcases hprev with ⟨r0, hprod0, hodd, _hnd5, _hlt, _horbit⟩
  have hr0 : r0 = r := by
    have hprod' : s = r + 1 := by simpa using hprod
    have hprod0' : s = r0 + 1 := by simpa using hprod0
    omega
  subst r0
  have hr_even : r % 2 = 0 := by
    have hodd' : s % 2 = 1 := hodd
    have hmod : (r + 1) % 2 = 1 := by
      rw [← hprod]
      simpa [hodd'] using (by rfl : (r + 1) % 2 = (s * 5 ^ 0) % 2)
    have hcases : r % 2 = 0 ∨ r % 2 = 1 := by omega
    rcases hcases with h0 | h1
    · exact h0
    · have hbad : (r + 1) % 2 = 0 := by
        rw [Nat.add_mod, h1]
      omega
  have hprefix := legal_word_prefix_exact_of_even_terminal w r hvalid hok hw hr_even
  by_contra hnot
  have hgt : 16 < w.length := by omega
  have hprefix15 := hprefix 15 (by omega)
  have hw15 : orbitStepWeight 15 = 3 := fullOrbit_first_t_ge3_is_exactly_3.2
  have hget_mem : w.getD 15 0 ∈ w :=
    UnifiedCoreAudit.getD_mem_of_lt w 15 0 (by omega)
  have ht12 : w.getD 15 0 = 1 ∨ w.getD 15 0 = 2 :=
    hok (w.getD 15 0) hget_mem
  have hval : w.getD 15 0 = 3 := hprefix15.trans hw15
  rw [hval] at ht12
  have hbad : 3 = 1 ∨ 3 = 2 := ht12
  omega

/-- The exact prefix information in a legal terminal witness identifies
`f(w.length-1)` with the depth-aligned state `f(j-2)`. -/
theorem previous_terminal_word_endpoint_depth_eq
    (s j k r : Nat) (w : List Nat)
    (hprev : IsPreviousEvenTerminal s j k)
    (hprod : s * 5 ^ k = r + 1)
    (hk : k = 0)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hw : StringFlow.Word.wordOrbit w 7 = r)
    (hr_even : r % 2 = 0)
    (hdepth : r = (5 * fullOrbitIter (j - 2) + 1) / 2) :
    fullOrbitIter (w.length - 1) = fullOrbitIter (j - 2) := by
  subst k
  rcases hprev with ⟨r0, hprod0, hodd, hnd5, _hlt, _horbit⟩
  have hr0 : r0 = r := by
    have hprod' : s = r + 1 := by simpa using hprod
    have hprod0' : s = r0 + 1 := by simpa using hprod0
    omega
  subst r0
  have hs0 : s = StringFlow.Word.wordOrbit w 7 + 1 := by
    have hprod' : s = r + 1 := by simpa using hprod
    rw [hprod', hw]
  have hne : w ≠ [] := by
    intro hw0
    subst w
    have h7 : 7 = r := by simpa [StringFlow.Word.wordOrbit] using hw
    rw [← h7] at hr_even
    norm_num at hr_even
  have hs0_mul : s * 5 ^ 0 = StringFlow.Word.wordOrbit w 7 + 1 := by
    simpa using hs0
  have hlast : StringFlow.Word.wordLast w = 1 :=
    previous_terminal_word_last_one_of_k0 w s 0 hvalid hok hne hs0_mul
      (by rfl) hnd5
  have hsplit : w = w.dropLast ++ [1] := by
    simpa [hlast] using word_eq_dropLast_append_last w hne
  let w' : List Nat := w.dropLast
  have hvalid_split : StringFlow.Word.wordValid (w' ++ [1]) 7 := by
    dsimp [w']
    rwa [← hsplit]
  have hparts := (wordValid_append_singleton w' 7 1).mp hvalid_split
  have hdvd' : (5 * StringFlow.Word.wordOrbit w' 7 + 1) % 2 = 0 := hparts.2
  have horbit : StringFlow.Word.wordOrbit w 7 =
      (5 * StringFlow.Word.wordOrbit w' 7 + 1) / 2 := by
    rw [hsplit]
    exact wordOrbit_append_singleton w' 7 1
  have h2w : 2 * StringFlow.Word.wordOrbit w 7 =
      5 * StringFlow.Word.wordOrbit w' 7 + 1 := by
    rw [horbit]
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdvd')
  let f := fullOrbitIter (j - 2)
  have hoddF : IsOdd f := by
    dsimp [f]
    exact fullOrbitIter_odd (j - 2)
  have hmodF : (5 * f + 1) % 2 = 0 := by
    have hf : f % 2 = 1 := hoddF
    rw [Nat.add_mod, Nat.mul_mod]
    rw [show 5 % 2 = 1 by norm_num, hf]
  have hdvdF : 2 ∣ 5 * f + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmodF
  have h2r : 2 * r = 5 * f + 1 := by
    rw [hdepth]
    exact Nat.mul_div_cancel' hdvdF
  have h2r' : 2 * r = 5 * StringFlow.Word.wordOrbit w' 7 + 1 := by
    rw [← hw]
    exact h2w
  have hcancel : 5 * StringFlow.Word.wordOrbit w' 7 = 5 * f := by omega
  have hw'f : StringFlow.Word.wordOrbit w' 7 = f :=
    Nat.mul_left_cancel (by decide : 0 < 5) hcancel
  have hprefix := legal_word_prefix_exact_of_even_terminal w r hvalid hok hw hr_even
  have hprefix' : ∀ k : Nat, k < w.length - 1 →
      w.getD k 0 = orbitStepWeight k := by
    intro k hk
    exact hprefix k (by omega)
  have htake : w.take (w.length - 1) = orbitSegmentWord 1 (w.length - 1) :=
    word_take_eq_segment_of_prefix_exact w (w.length - 1) hprefix' (by omega)
  have hw_take : w' = w.take (w.length - 1) := by
    dsimp [w']
    exact List.dropLast_eq_take
  have hwprefix : StringFlow.Word.wordOrbit w' 7 =
      fullOrbitIter (w.length - 1) := by
    rw [hw_take, htake]
    have h := orbitSegmentWord_orbit 1 (w.length - 1)
    have h0 : fullOrbitIter 0 = 7 := rfl
    rw [h0] at h
    have hidx : 1 - 1 + (w.length - 1) = w.length - 1 := by omega
    rwa [hidx] at h
  exact hwprefix.symm.trans hw'f

/-- A depth-aligned reset window has depth at least 2. -/
theorem resetWindowDepth_j_ge_two
    (j k0 t δ s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t δ s r rj) :
    2 ≤ j := by
  have hk : k0 = 0 :=
    previousTerminalDepth_k0_eq_zero j k0 t δ s r rj hAt
  subst k0
  have hs_pos : 1 ≤ s := by
    have hprod : s * 5 ^ 0 = r + 1 := by simpa using hAt.2.2
    omega
  rcases hAt.1 with ⟨_r0, _rj0, hk0, _hprod0, _hodd, _hnd5, hslt,
    _hOrbit, _hreset, _hOdd, _hOrbitRj⟩
  have hk0' : 1 ≤ j := by simpa using hk0
  have hslt' : s < 5 ^ (j - 1) := by simpa using hslt
  by_contra hnot
  have hjle : j ≤ 1 := by omega
  have hsub : j - 1 = 0 := by omega
  rw [hsub] at hslt'
  omega

/-- With the real previous terminal at depth at most 15, the `t=1` reset
head rank is a finite prefix check. -/
theorem rjRankT1Bound_of_depth_le_15
    (j k0 s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 1 1 s r rj)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hdepth : j - 2 <= 15) :
    twoValuation (rj + 1) <= 2 * j + 10 := by
  have hk : k0 = 0 :=
    previousTerminalDepth_k0_eq_zero j k0 1 1 s r rj hAt
  have hs : s = (5 * fullOrbitIter (j - 2) + 3) / 2 :=
    previousTerminalDepth_s_eq j k0 1 1 s r rj hAt
  subst k0
  have hj2 : 2 ≤ j := resetWindowDepth_j_ge_two j 0 1 1 s r rj hAt
  rcases hreset with h1 | h2
  . rcases h1 with ⟨_ht, _hd1, heq⟩
    obtain ⟨d, hd_eq⟩ : ∃ d : Nat, d = j - 2 := ⟨j - 2, rfl⟩
    have hs_d : s = (5 * fullOrbitIter d + 3) / 2 := by
      rw [← hd_eq] at hs
      exact hs
    clear hs
    have hd15 : d <= 15 := by
      rw [hd_eq]
      exact hdepth
    have hjd : j = d + 2 := by
      rw [hd_eq]
      omega
    subst j
    let N : Nat := 5 * s + 5 ^ (d + 2) - 2
    have hN : 2 * (rj + 1) = N := by
      simpa [N, Nat.add_comm] using heq
    have hrj1 : rj + 1 = N / 2 := by omega
    rw [hrj1]
    dsimp [N] at hN ⊢
    rw [hs_d] at hN ⊢
    interval_cases d
    all_goals
      norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at hN
    all_goals
      norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
  . rcases h2 with ⟨ht, _hdelta, _heq⟩
    norm_num at ht

/-- With the real previous terminal at depth at most 15, the `t=2` reset
head rank is a finite prefix check. -/
theorem rjRankT2Bound_of_depth_le_15
    (j k0 s r rj : Nat) (delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 2 delta s r rj)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hdepth : j - 2 <= 15) :
    twoValuation (rj + 1) <= 2 * j + 8 := by
  have hk : k0 = 0 :=
    previousTerminalDepth_k0_eq_zero j k0 2 delta s r rj hAt
  have hs : s = (5 * fullOrbitIter (j - 2) + 3) / 2 :=
    previousTerminalDepth_s_eq j k0 2 delta s r rj hAt
  subst k0
  have hj2 : 2 ≤ j := resetWindowDepth_j_ge_two j 0 2 delta s r rj hAt
  rcases hreset with h1 | h2
  . rcases h1 with ⟨ht, _hdelta, _heq⟩
    norm_num at ht
  . rcases h2 with ⟨_ht, hd12, heq⟩
    obtain ⟨d, hd_eq⟩ : ∃ d : Nat, d = j - 2 := ⟨j - 2, rfl⟩
    have hs_d : s = (5 * fullOrbitIter d + 3) / 2 := by
      rw [← hd_eq] at hs
      exact hs
    clear hs
    have hd15 : d <= 15 := by
      rw [hd_eq]
      exact hdepth
    have hjd : j = d + 2 := by
      rw [hd_eq]
      omega
    subst j
    rcases hd12 with hd1 | hd3
    . subst delta
      let N : Nat := 5 * s + 1 * 5 ^ (d + 2)
      have hN : 4 * (rj + 1) = N := by
        simpa [N, Nat.add_comm] using heq
      have hrj1 : rj + 1 = N / 4 := by omega
      rw [hrj1]
      dsimp [N] at hN ⊢
      rw [hs_d] at hN ⊢
      interval_cases d
      all_goals
        norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at hN
      all_goals
        norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]
    . subst delta
      let N : Nat := 5 * s + 3 * 5 ^ (d + 2)
      have hN : 4 * (rj + 1) = N := by
        simpa [N, Nat.add_comm] using heq
      have hrj1 : rj + 1 = N / 4 := by omega
      rw [hrj1]
      dsimp [N] at hN ⊢
      rw [hs_d] at hN ⊢
      interval_cases d
      all_goals
        norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ] at hN
      all_goals
        norm_num [fullOrbitIter, fullOrbitStep, StringFlow.twoValuation_succ]

/-- The exact `t=1` reset identity after eliminating the previous
terminal odd part. -/
theorem rjPlusOne_t1_identity
    (j k0 s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 1 1 s r rj)
    (hreset : ResetHeadEq s j k0 1 1 rj) :
    k0 = 0 ∧
      s = (5 * fullOrbitIter (j - 2) + 3) / 2 ∧
        4 * (rj + 1) =
          25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11 := by
  have hk : k0 = 0 := previousTerminalDepth_k0_eq_zero j k0 1 1 s r rj hAt
  have hs : s = (5 * fullOrbitIter (j - 2) + 3) / 2 :=
    previousTerminalDepth_s_eq j k0 1 1 s r rj hAt
  subst k0
  rcases hreset with h1 | h2
  · rcases h1 with ⟨ht, hd, heq⟩
    have h2s : 2 * s = 5 * fullOrbitIter (j - 2) + 3 := by
      let f := fullOrbitIter (j - 2)
      have hodd : IsOdd f := by
        dsimp [f]
        exact fullOrbitIter_odd (j - 2)
      have hmod : (5 * f + 3) % 2 = 0 := by
        have hf : f % 2 = 1 := hodd
        rw [Nat.add_mod, Nat.mul_mod]
        rw [show 5 % 2 = 1 by norm_num, hf]
      have hdvd : 2 ∣ 5 * f + 3 := Nat.dvd_iff_mod_eq_zero.mpr hmod
      rw [hs]
      simpa [f] using Nat.mul_div_cancel' hdvd
    have h2rj : 2 * (rj + 1) = 5 * s + 5 ^ j - 2 := by
      simpa [Nat.add_comm] using heq
    have h4rj : 4 * (rj + 1) = 10 * s + 2 * 5 ^ j - 4 := by omega
    have h10s : 10 * s = 25 * fullOrbitIter (j - 2) + 15 := by
      nlinarith [h2s]
    have hmain : 4 * (rj + 1) =
        25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11 := by
      rw [h4rj, h10s]
      omega
    exact ⟨by rfl, hs, hmain⟩
  · rcases h2 with ⟨ht, _hdelta, _heq⟩
    norm_num at ht

/-- The exact `t=2` reset identity after eliminating the previous
terminal odd part. -/
theorem rjPlusOne_t2_identity
    (j k0 s r rj : Nat) (delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 2 delta s r rj)
    (hreset : ResetHeadEq s j k0 2 delta rj) :
    k0 = 0 ∧
      s = (5 * fullOrbitIter (j - 2) + 3) / 2 ∧
        8 * (rj + 1) =
          25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j := by
  have hk : k0 = 0 := previousTerminalDepth_k0_eq_zero j k0 2 delta s r rj hAt
  have hs : s = (5 * fullOrbitIter (j - 2) + 3) / 2 :=
    previousTerminalDepth_s_eq j k0 2 delta s r rj hAt
  subst k0
  rcases hreset with h1 | h2
  · rcases h1 with ⟨ht, _hdelta, _heq⟩
    norm_num at ht
  · rcases h2 with ⟨ht, hd12, heq⟩
    have h2s : 2 * s = 5 * fullOrbitIter (j - 2) + 3 := by
      let f := fullOrbitIter (j - 2)
      have hodd : IsOdd f := by
        dsimp [f]
        exact fullOrbitIter_odd (j - 2)
      have hmod : (5 * f + 3) % 2 = 0 := by
        have hf : f % 2 = 1 := hodd
        rw [Nat.add_mod, Nat.mul_mod]
        rw [show 5 % 2 = 1 by norm_num, hf]
      have hdvd : 2 ∣ 5 * f + 3 := Nat.dvd_iff_mod_eq_zero.mpr hmod
      rw [hs]
      simpa [f] using Nat.mul_div_cancel' hdvd
    have h4rj : 4 * (rj + 1) = 5 * s + delta * 5 ^ j := by
      simpa [Nat.add_comm] using heq
    have h8rj : 8 * (rj + 1) = 10 * s + 2 * delta * 5 ^ j := by
      nlinarith [h4rj]
    have h10s : 10 * s = 25 * fullOrbitIter (j - 2) + 15 := by
      nlinarith [h2s]
    have hmain : 8 * (rj + 1) =
        25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j := by
      rw [h8rj, h10s]
    exact ⟨by rfl, hs, hmain⟩

/-- Weak-window `t=1` identity after eliminating `s,k0` in favour of
the actual previous terminal `r`.  No depth alignment is used. -/
theorem rjPlusOne_t1_identity_of_reset_reachability
    (j k0 s rj : Nat)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hreach : ResetWindowReachability j k0 1 1 s) :
    ∃ r : Nat,
      s * 5 ^ k0 = r + 1 ∧
      r + 1 < 5 ^ (j - 1) ∧
      GeneralOrbitFrom7 r ∧
      2 * (rj + 1) = 5 * r + 5 ^ j + 3 := by
  rcases resetWindowReachability_previous_data j k0 1 1 s hreach with
    ⟨r, hprod, hrlt, hOrbitR⟩
  rcases hreset with h₁ | h₂
  · rcases h₁ with ⟨_ht, _hδ, heq⟩
    have hfive : 5 ^ (k0 + 1) * s = 5 * (r + 1) := by
      rw [Nat.pow_succ]
      nlinarith [hprod]
    refine ⟨r, hprod, hrlt, hOrbitR, ?_⟩
    rw [heq, hfive]
    omega
  · rcases h₂ with ⟨ht, _hδ, _heq⟩
    norm_num at ht

/-- Weak-window `t=2` identity after eliminating `s,k0` in favour of
the actual previous terminal `r`. -/
theorem rjPlusOne_t2_identity_of_reset_reachability
    (j k0 delta s rj : Nat)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hreach : ResetWindowReachability j k0 2 delta s) :
    ∃ r : Nat,
      s * 5 ^ k0 = r + 1 ∧
      r + 1 < 5 ^ (j - 1) ∧
      GeneralOrbitFrom7 r ∧
      4 * (rj + 1) = 5 * r + 5 + delta * 5 ^ j := by
  rcases resetWindowReachability_previous_data j k0 2 delta s hreach with
    ⟨r, hprod, hrlt, hOrbitR⟩
  rcases hreset with h₁ | h₂
  · rcases h₁ with ⟨ht, _hδ, _heq⟩
    norm_num at ht
  · rcases h₂ with ⟨_ht, _hδ, heq⟩
    have hfive : 5 ^ (k0 + 1) * s = 5 * (r + 1) := by
      rw [Nat.pow_succ]
      nlinarith [hprod]
    refine ⟨r, hprod, hrlt, hOrbitR, ?_⟩
    rw [heq, hfive]
    omega

/-- The weak-window `t=1` rank target is exactly the valuation bound on
the eliminated previous-terminal expression. -/
theorem t1Rank_iff_previous_terminal_valuation
    (j k0 s rj : Nat)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hreach : ResetWindowReachability j k0 1 1 s) :
    ∃ r : Nat,
      s * 5 ^ k0 = r + 1 ∧
      r + 1 < 5 ^ (j - 1) ∧
      GeneralOrbitFrom7 r ∧
      ((twoValuation (rj + 1) ≤ 2 * j + 10) ↔
        twoValuation (5 * r + 5 ^ j + 3) ≤ 2 * j + 11) := by
  rcases rjPlusOne_t1_identity_of_reset_reachability
      j k0 s rj hreset hreach with ⟨r, hprod, hrlt, hOrbitR, hid⟩
  have hval := StringFlow.twoValuation_mul_two (rj + 1) (by positivity)
  have hv : twoValuation (5 * r + 5 ^ j + 3) =
      1 + twoValuation (rj + 1) := by
    rw [← hid]
    simpa [Nat.add_comm] using hval
  refine ⟨r, hprod, hrlt, hOrbitR, ?_⟩
  rw [hv]
  omega

/-- The weak-window `t=2` rank target is exactly the valuation bound on
the eliminated previous-terminal expression. -/
theorem t2Rank_iff_previous_terminal_valuation
    (j k0 delta s rj : Nat)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hreach : ResetWindowReachability j k0 2 delta s) :
    ∃ r : Nat,
      s * 5 ^ k0 = r + 1 ∧
      r + 1 < 5 ^ (j - 1) ∧
      GeneralOrbitFrom7 r ∧
      ((twoValuation (rj + 1) ≤ 2 * j + 8) ↔
        twoValuation (5 * r + 5 + delta * 5 ^ j) ≤ 2 * j + 10) := by
  rcases rjPlusOne_t2_identity_of_reset_reachability
      j k0 delta s rj hreset hreach with ⟨r, hprod, hrlt, hOrbitR, hid⟩
  have hval := StringFlow.Lte.twoValuation_mul_two_pow
    2 (rj + 1) (by positivity)
  have hv : twoValuation (5 * r + 5 + delta * 5 ^ j) =
      2 + twoValuation (rj + 1) := by
    rw [← hid]
    simpa [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hval
  refine ⟨r, hprod, hrlt, hOrbitR, ?_⟩
  rw [hv]
  omega

/-- Starting from a concrete occurrence of the cycle-word head, every
prefix occurs at the correspondingly shifted full-orbit depth.  This is
the indexed strengthening of `cycleQb8Input_prefix_full_reachable`; it
keeps the occurrence index needed to identify the incoming edge. -/
theorem cycleQb8Input_prefix_fullOrbitIter_of_start
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (n0 : Nat) (hstart : fullOrbitIter n0 = m)
    (j : Nat) (hj : j <= w.length) :
    fullOrbitIter (n0 + j) =
      StringFlow.Word.wordOrbit (w.take j) m := by
  induction j with
  | zero =>
      simpa [StringFlow.Word.wordOrbit] using hstart
  | succ j ih =>
      have hjw : j < w.length := by omega
      have hprev := ih (by omega : j <= w.length)
      have hstep := StringFlow.CycleBridge.wordOrbit_take_succ w m j hjw
      have hex : twoValuation
          (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) =
          w.getI j := h.hexact j hjw
      have hexS : S6Audit.twoValuation
          (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) =
          w.getI j := by simpa using hex
      have hnext : StringFlow.Word.wordOrbit (w.take (j + 1)) m =
          fullOrbitStep (StringFlow.Word.wordOrbit (w.take j) m) := by
        rw [hstep]
        unfold fullOrbitStep
        rw [hexS]
      have hidx : n0 + (j + 1) = (n0 + j) + 1 := by omega
      rw [hidx]
      change fullOrbitStep (fullOrbitIter (n0 + j)) =
        StringFlow.Word.wordOrbit (w.take (j + 1)) m
      rw [hprev, hnext]

/-- A positive cycle-word prefix carries its exact real incoming full
orbit edge.  In particular the last word entry is not merely congruent
to the incoming weight: it is that weight at a concrete occurrence. -/
theorem cycleQb8Input_prefix_occurrence_with_incoming
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : 1 <= j) (hjl : j <= w.length) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (j - 1)) m /\
      orbitStepWeight (n - 1) = w.getI (j - 1) := by
  rcases h.hstart with ⟨n0, hstart⟩
  let n := n0 + j
  have hstate := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart j hjl
  have hprev := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart (j - 1) (by omega)
  have hidx : n - 1 = n0 + (j - 1) := by
    dsimp [n]
    omega
  refine ⟨n, by dsimp [n]; omega, hstate, ?_, ?_⟩
  · rw [hidx]
    exact hprev
  · rw [hidx]
    unfold orbitStepWeight
    rw [hprev]
    exact h.hexact (j - 1) (by omega)

/-- Along a cyclic rotation, the `k`-th displayed entry is still the
exact outgoing full-orbit weight at time `n0+b+k`.  Period transport is
used in the wrapping branch. -/
theorem cycleQb8Input_cyclic_orbitStepWeight_of_start
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (n0 : Nat) (hstart : fullOrbitIter n0 = m)
    (b : Nat) (hb : b <= w.length)
    (k : Nat) (hk : k < w.length) :
    orbitStepWeight ((n0 + b) + k) =
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k := by
  have hlenpos : 0 < w.length := by
    have := StringFlow.CycleBridge.cycleQb8Input_length_ge_two h
    omega
  have hperiodWord := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart w.length (by omega)
  have htake : w.take w.length = w := List.take_length
  have hperiod : fullOrbitIter (n0 + w.length) = fullOrbitIter n0 := by
    rw [hperiodWord, htake, h.hclosed, hstart]
  let r := (b + k) % w.length
  have hrlt : r < w.length := by
    dsimp [r]
    exact Nat.mod_lt _ hlenpos
  have hprefix := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart r (Nat.le_of_lt hrlt)
  have hentry := StringFlow.CycleBridge.cyclicSegmentAt_getI_mod
    w b k hb hk
  have hstate : fullOrbitIter ((n0 + b) + k) =
      StringFlow.Word.wordOrbit (w.take r) m := by
    by_cases hnon : b + k < w.length
    · have hr : r = b + k := by
        dsimp [r]
        exact Nat.mod_eq_of_lt hnon
      have hidx : (n0 + b) + k = n0 + r := by omega
      rw [hidx]
      exact hprefix
    · have hge : w.length <= b + k := by omega
      have hlt2 : b + k < 2 * w.length := by omega
      have hr : r = b + k - w.length := by
        dsimp [r]
        rw [Nat.mod_eq_sub_mod hge]
        exact Nat.mod_eq_of_lt (by omega)
      have hsum : b + k = w.length + r := by omega
      have hidx : (n0 + b) + k = (n0 + w.length) + r := by omega
      have hshift : fullOrbitIter ((n0 + w.length) + r) =
          fullOrbitIter (n0 + r) := by
        induction r with
        | zero => simpa using hperiod
        | succ r ihr =>
            have hleft : (n0 + w.length) + (r + 1) =
                ((n0 + w.length) + r) + 1 := by omega
            have hright : n0 + (r + 1) = (n0 + r) + 1 := by omega
            rw [hleft, hright]
            change fullOrbitStep (fullOrbitIter ((n0 + w.length) + r)) =
              fullOrbitStep (fullOrbitIter (n0 + r))
            rw [ihr]
      rw [hidx]
      exact hshift.trans hprefix
  unfold orbitStepWeight
  rw [hstate]
  have hexact := h.hexact r hrlt
  exact hexact.trans hentry.symm

/-- Every prefix of a cyclic rotation occurs at the corresponding
shifted full-orbit time, including when the prefix crosses the end of
the original word. -/
theorem cycleQb8Input_cyclic_prefix_fullOrbitIter_of_start
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (n0 : Nat) (hstart : fullOrbitIter n0 = m)
    (b : Nat) (hb : b <= w.length)
    (L : Nat) (hL : L <= w.length) :
    fullOrbitIter ((n0 + b) + L) =
      StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m) := by
  let u := StringFlow.CycleBridge.cyclicSegmentAt w b
  let q := StringFlow.Word.wordOrbit (w.take b) m
  induction L with
  | zero =>
      have hbase := cycleQb8Input_prefix_fullOrbitIter_of_start
        h n0 hstart b hb
      simpa [u, q, StringFlow.Word.wordOrbit] using hbase
  | succ L ih =>
      have hLlt : L < w.length := by omega
      have hulen : u.length = w.length := by
        dsimp [u]
        exact StringFlow.CycleBridge.cyclicSegmentAt_length w b hb
      have hLu : L < u.length := by simpa [hulen] using hLlt
      have hword := StringFlow.CycleBridge.wordOrbit_take_succ
        u q L hLu
      have hweight := cycleQb8Input_cyclic_orbitStepWeight_of_start
        h n0 hstart b hb L hLlt
      have hexact : twoValuation
          (5 * StringFlow.Word.wordOrbit (u.take L) q + 1) = u.getI L := by
        unfold orbitStepWeight at hweight
        rw [ih (by omega)] at hweight
        exact hweight
      have hexactS : S6Audit.twoValuation
          (5 * StringFlow.Word.wordOrbit (u.take L) q + 1) = u.getI L := by
        simpa using hexact
      have hnext : StringFlow.Word.wordOrbit (u.take (L + 1)) q =
          fullOrbitStep (StringFlow.Word.wordOrbit (u.take L) q) := by
        rw [hword]
        unfold fullOrbitStep
        rw [hexactS]
      have hidx : (n0 + b) + (L + 1) = ((n0 + b) + L) + 1 := by omega
      rw [hidx]
      change fullOrbitStep (fullOrbitIter ((n0 + b) + L)) =
        StringFlow.Word.wordOrbit (u.take (L + 1)) q
      rw [ih (by omega), hnext]

/-- A positive cyclic local prefix has a concrete real incoming edge.
Both endpoint states are the rotated local word states; no global
linear index is substituted for the local depth `L`. -/
theorem cycleQb8Input_cyclic_prefix_occurrence_with_incoming
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b L : Nat) (hb : b <= w.length)
    (hLpos : 1 <= L) (hLle : L <= w.length) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m) /\
      fullOrbitIter (n - 1) = StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take (L - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) /\
      orbitStepWeight (n - 1) =
        (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1) := by
  rcases h.hstart with ⟨n0, hstart⟩
  let n := (n0 + b) + L
  have hstate := cycleQb8Input_cyclic_prefix_fullOrbitIter_of_start
    h n0 hstart b hb L hLle
  have hprev := cycleQb8Input_cyclic_prefix_fullOrbitIter_of_start
    h n0 hstart b hb (L - 1) (by omega)
  have hidx : n - 1 = (n0 + b) + (L - 1) := by
    dsimp [n]
    omega
  have hweight := cycleQb8Input_cyclic_orbitStepWeight_of_start
    h n0 hstart b hb (L - 1) (by omega)
  refine ⟨n, by dsimp [n]; omega, hstate, ?_, ?_⟩
  · rw [hidx]
    exact hprev
  · rw [hidx]
    exact hweight

/-- The full-orbit predecessor equation for `rj` at depth `n`. -/
theorem fullOrbit_predecessor_mul
    (n rj : Nat) (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    2 ^ orbitStepWeight (n - 1) * rj =
      5 * fullOrbitIter (n - 1) + 1 := by
  have hn' : n = (n - 1) + 1 := by omega
  rw [hn'] at hiter
  change fullOrbitStep (fullOrbitIter (n - 1)) = rj at hiter
  have hmul := fullOrbitStep_mul_eq (fullOrbitIter (n - 1))
  unfold orbitStepWeight
  rw [hiter] at hmul
  exact hmul

/-- The rank of a state obtained from `7` by a legal word of length
`j` is bounded by the word length: once the word identity is cleared,
the denominator has total weight at least `j`, while the numerator is
only slightly larger than a constant times `5^j`. -/
lemma word_state_rank_bound_of_length
    (j W A r : Nat)
    (hW : j <= W)
    (hA : A < 5 ^ j)
    (hrpos : 0 < r)
    (hid : 2 ^ W * r = 7 * 5 ^ j + A) :
    twoValuation (r + 1) <= 2 * j + 8 := by
  have hNpos : 0 < 7 * 5 ^ j + A + 2 ^ W := by positivity
  have hN : 2 ^ W * (r + 1) = 7 * 5 ^ j + A + 2 ^ W := by
    nlinarith [hid]
  have hiff := StringFlow.Lte.twoValuation_le_iff_not_dvd_pow
    (r + 1) (2 * j + 8) (by positivity)
  apply hiff.mpr
  intro hdvd
  have hdvdN : Dvd.dvd (2 ^ (W + 2 * j + 9)) (2 ^ W * (r + 1)) := by
    have hK : 2 * j + 8 + 1 = 2 * j + 9 := by omega
    rw [hK] at hdvd
    rcases hdvd with ⟨t, ht⟩
    rw [ht]
    rw [Nat.pow_add]
    ring_nf
    exact ⟨t, by ring⟩
  have hNlt : 7 * 5 ^ j + A + 2 ^ W < 2 ^ (W + 2 * j + 9) := by
    by_cases hW5 : 2 ^ W <= 7 * 5 ^ j
    · have hsmall : 15 * 5 ^ j <= 2 ^ (3 * j + 9) := by
        have h5le8 : 5 ^ j <= 8 ^ j :=
          Nat.pow_le_pow_left (by decide : 5 <= 8) j
        have h8 : 8 ^ j = 2 ^ (3 * j) := by
          have hbase : (8 : Nat) = 2 ^ 3 := by norm_num
          calc
            8 ^ j = (2 ^ 3) ^ j := by rw [hbase]
            _ = 2 ^ (3 * j) := by rw [Nat.pow_mul]
        have h16 : 16 * 5 ^ j <= 16 * 8 ^ j :=
          Nat.mul_le_mul_left 16 h5le8
        have h512 : 16 * 8 ^ j <= 512 * 8 ^ j := by
          exact Nat.mul_le_mul_right (8 ^ j) (by norm_num : 16 <= 512)
        have h512pow : 512 * 8 ^ j = 2 ^ (3 * j + 9) := by
          rw [h8]
          have h512 : (512 : Nat) = 2 ^ 9 := by norm_num
          rw [h512, Nat.pow_add]
          rw [Nat.mul_comm]
        have h15 : 15 * 5 ^ j < 16 * 5 ^ j := by
          have hpos : 0 < 5 ^ j := by positivity
          nlinarith
        have h15le : 15 * 5 ^ j <= 2 ^ (3 * j + 9) := by
          have hlt := lt_of_lt_of_le h15 h16
          have hlt2 := lt_of_lt_of_le hlt h512
          rw [h512pow] at hlt2
          exact le_of_lt hlt2
        exact h15le
      have hNsmall : 7 * 5 ^ j + A + 2 ^ W < 15 * 5 ^ j := by
        nlinarith [hA, hW5]
      have hpow : 2 ^ (3 * j + 9) <= 2 ^ (W + 2 * j + 9) := by
        exact Nat.pow_le_pow_right (by decide : 1 <= 2) (by omega : 3 * j + 9 <= W + 2 * j + 9)
      exact lt_of_lt_of_le hNsmall (le_trans hsmall hpow)
    · have hW5' : 7 * 5 ^ j < 2 ^ W := by omega
      have hNsmall : 7 * 5 ^ j + A + 2 ^ W < 3 * 2 ^ W := by
        nlinarith [hA, hW5']
      have hthree : 3 * 2 ^ W <= 2 ^ (W + 2 * j + 9) := by
        have hge : 3 <= 2 ^ (2 * j + 9) := by
          have h9 : 9 <= 2 * j + 9 := by omega
          have hpow : 2 ^ 9 <= 2 ^ (2 * j + 9) :=
            Nat.pow_le_pow_right (by decide : 1 <= 2) h9
          norm_num at hpow
          exact le_trans (by norm_num : 3 <= 512) hpow
        have hpow : 2 ^ W * 2 ^ (2 * j + 9) = 2 ^ (W + 2 * j + 9) := by
          rw [Nat.pow_add]
          ring_nf
        have hpow' : 2 ^ (2 * j + 9) * 2 ^ W = 2 ^ (W + 2 * j + 9) := by
          rw [Nat.mul_comm]
          exact hpow
        have hmul : 3 * 2 ^ W <= (2 ^ (2 * j + 9)) * 2 ^ W :=
          Nat.mul_le_mul_right (2 ^ W) hge
        rw [Nat.mul_comm] at hmul
        rw [hpow'] at hmul
        rw [Nat.mul_comm] at hmul
        exact hmul
      exact lt_of_lt_of_le hNsmall hthree
  have hleN := Nat.le_of_dvd (by positivity) hdvdN
  have hleN' : 2 ^ (W + 2 * j + 9) <= 7 * 5 ^ j + A + 2 ^ W := by
    rw [hN] at hleN
    exact hleN
  have hcontra := lt_of_le_of_lt hleN' hNlt
  omega

/-- The total weight of a word whose entries are at least one is at
least its length. -/
lemma wordWeight_ge_length_of_ge_one
    (w : List Nat) (hpos : forall t : Nat, List.Mem t w -> 1 <= t) :
    w.length <= StringFlow.wordWeight w := by
  induction w with
  | nil => simp [StringFlow.wordWeight]
  | cons t ts ih =>
      have ht : 1 <= t := hpos t (by exact List.mem_cons_self)
      have hts : forall u : Nat, List.Mem u ts -> 1 <= u := by
        intro u hu
        exact hpos u (List.mem_cons.mpr (Or.inr hu))
      have ih' := ih hts
      simp [StringFlow.wordWeight, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
      omega

/-- A list whose entries are exactly one or two is `wordOK`. -/
lemma wordOK_of_mem_one_two
    (w : List Nat) (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2) :
    StringFlow.Word.wordOK w := by
  induction w with
  | nil => simp [StringFlow.Word.wordOK]
  | cons t ts ih =>
      have ht : t = 1 \/ t = 2 := hsteps t (by exact List.mem_cons_self)
      have hts : forall u : Nat, List.Mem u ts -> u = 1 \/ u = 2 := by
        intro u hu
        exact hsteps u (List.mem_cons.mpr (Or.inr hu))
      have ih' := ih hts
      constructor
      · omega
      · exact ih'

/-- A valid word from a positive state stays positive. -/
lemma wordOrbit_pos_of_valid
    (w : List Nat) (x : Nat) (hx : 0 < x)
    (hvalid : StringFlow.Word.wordValid w x) :
    0 < StringFlow.Word.wordOrbit w x := by
  induction w generalizing x with
  | nil =>
      simp [StringFlow.Word.wordOrbit, hx]
  | cons t ts ih =>
      have htail : StringFlow.Word.wordValid ts
          ((5 * x + 1) / 2 ^ t) := hvalid.2
      have hnumpos : 0 < 5 * x + 1 := by positivity
      have hdiv : 2 ^ t <= 5 * x + 1 := by
        have hdvd : Dvd.dvd (2 ^ t) (5 * x + 1) :=
          Nat.dvd_iff_mod_eq_zero.mpr hvalid.1
        exact Nat.le_of_dvd hnumpos hdvd
      have hquotpos : 0 < (5 * x + 1) / 2 ^ t := by
        exact Nat.div_pos hdiv (by positivity : 0 < 2 ^ t)
      have ih' := ih ((5 * x + 1) / 2 ^ t) hquotpos htail
      simpa [StringFlow.Word.wordOrbit] using ih'

/-- Every endpoint of a legal `{1,2}` word from `7` has rank at most
twice the word length plus eight.  This is the weight-budget version of
the two corrected window bounds. -/
theorem word_endpoint_rank_bound
    (w : List Nat) (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7) :
    twoValuation (StringFlow.Word.wordOrbit w 7 + 1) <= 2 * w.length + 8 := by
  have hid := StringFlow.Word.word_orbit_identity w 7 hvalid
  have hOK : StringFlow.Word.wordOK w := wordOK_of_mem_one_two w hsteps
  have hA : StringFlow.Word.wordA w < 5 ^ w.length :=
    StringFlow.Word.wordA_lt_five_pow w hOK
  have hpos_entries : forall t : Nat, List.Mem t w -> 1 <= t := by
    intro t ht
    rcases hsteps t ht with h1 | h2 <;> omega
  have hW : w.length <= StringFlow.wordWeight w :=
    wordWeight_ge_length_of_ge_one w hpos_entries
  have hrpos : 0 < StringFlow.Word.wordOrbit w 7 :=
    wordOrbit_pos_of_valid w 7 (by norm_num) hvalid
  have hid' : 2 ^ StringFlow.wordWeight w * StringFlow.Word.wordOrbit w 7 =
      7 * 5 ^ w.length + StringFlow.Word.wordA w := by
    simpa [Nat.mul_comm] using hid
  exact word_state_rank_bound_of_length w.length
    (StringFlow.wordWeight w) (StringFlow.Word.wordA w)
    (StringFlow.Word.wordOrbit w 7) hW hA hrpos hid'

/-- The corrected `t=1` window bound follows directly when the block
head is the endpoint of a legal `{1,2}` word of length `j`. -/
theorem t1WindowBound_of_block_word_endpoint
    (j k0 s rj : Nat) (w : List Nat)
    (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hlen : w.length = j)
    (hend : StringFlow.Word.wordOrbit w 7 = rj)
    (hreset : ResetHeadEq s j k0 1 1 rj) :
    BlockAutomaton.t1WindowValue j k0 s <= 2 * j + 11 := by
  have hrank := word_endpoint_rank_bound w hsteps hvalid
  have hval := t1WindowValue_eq_twoValuation_rj_plus_one j k0 s rj hreset
  rw [hval, ← hlen, ← hend]
  omega

/-- The corrected `t=2` window bound follows directly when the block
head is the endpoint of a legal `{1,2}` word of length `j`. -/
theorem t2WindowBound_of_block_word_endpoint
    (j k0 delta s rj : Nat) (w : List Nat)
    (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hlen : w.length = j)
    (hend : StringFlow.Word.wordOrbit w 7 = rj)
    (hreset : ResetHeadEq s j k0 2 delta rj) :
    BlockAutomaton.t2WindowValue j k0 delta s <= 2 * j + 10 := by
  have hrank := word_endpoint_rank_bound w hsteps hvalid
  have hval := t2WindowValue_eq_twoValuation_rj_plus_one j k0 delta s rj hreset
  rw [hval, ← hlen, ← hend]
  omega

/-- The word-endpoint version of the `t=1` block-head rank bound. -/
theorem rjRankT1Bound_of_word_endpoint
    (j rj : Nat) (w : List Nat)
    (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hlen : w.length = j)
    (hend : StringFlow.Word.wordOrbit w 7 = rj) :
    twoValuation (rj + 1) <= 2 * j + 10 := by
  have hrank := word_endpoint_rank_bound w hsteps hvalid
  have hrank' : twoValuation (rj + 1) <= 2 * j + 8 := by
    rw [← hend, ← hlen]
    exact hrank
  omega

/-- The word-endpoint version of the `t=2` block-head rank bound. -/
theorem rjRankT2Bound_of_word_endpoint
    (j rj : Nat) (w : List Nat)
    (hsteps : forall t : Nat, List.Mem t w -> t = 1 \/ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hlen : w.length = j)
    (hend : StringFlow.Word.wordOrbit w 7 = rj) :
    twoValuation (rj + 1) <= 2 * j + 8 := by
  have hrank := word_endpoint_rank_bound w hsteps hvalid
  rw [← hend, ← hlen]
  exact hrank

/-- The real full-orbit step weight into `rj` has the same mod-4
residue as the reset weight `t`.  Depth alignment is not needed: the
reset equation and positive reset depth already determine the residue. -/
theorem fullOrbitStepWeight_mod4_of_reset_of_j_pos
    (n j k0 s rj : Nat) (t delta : Nat)
    (hj : 1 ≤ j)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (t = 1 → orbitStepWeight (n - 1) % 4 = 1) ∧
      (t = 2 → orbitStepWeight (n - 1) % 4 = 2) := by
  have hmod := reset_head_mod_five s j k0 t delta rj hj hreset
  have hpred := fullOrbit_predecessor_mul n rj hn hiter
  let w := orbitStepWeight (n - 1)
  have hmod1 : (2 ^ w * rj) % 5 = 1 := by
    dsimp [w] at hpred ⊢
    rw [hpred]
    rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  constructor
  · intro ht
    have hrj3 : rj % 5 = 3 := hmod.1 ht
    let x := (2 ^ w) % 5
    have hmulmod : (x * (rj % 5)) % 5 = 1 := by
      rw [Nat.mul_mod] at hmod1
      dsimp [x] at hmod1 ⊢
      exact hmod1
    rw [hrj3] at hmulmod
    have hxlt : x < 5 := by
      dsimp [x]
      exact Nat.mod_lt (2 ^ w) (by decide)
    have hxeq : x = 2 := by
      interval_cases x <;> norm_num at hmulmod <;> omega
    have hx2 : (2 ^ w) % 5 = 2 := by
      dsimp [x] at hxeq
      exact hxeq
    have hw1 : w % 4 = 1 := two_pow_mod5_eq_two_imp w hx2
    exact hw1
  · intro ht
    have hrj4 : rj % 5 = 4 := hmod.2 ht
    let x := (2 ^ w) % 5
    have hmulmod : (x * (rj % 5)) % 5 = 1 := by
      rw [Nat.mul_mod] at hmod1
      dsimp [x] at hmod1 ⊢
      exact hmod1
    rw [hrj4] at hmulmod
    have hxlt : x < 5 := by
      dsimp [x]
      exact Nat.mod_lt (2 ^ w) (by decide)
    have hxeq : x = 4 := by
      interval_cases x <;> norm_num at hmulmod <;> omega
    have hx4 : (2 ^ w) % 5 = 4 := by
      dsimp [x] at hxeq
      exact hxeq
    have hw2 : w % 4 = 2 := two_pow_mod5_eq_four_imp w hx4
    exact hw2

/-- Backward-compatible depth-aligned wrapper for
`fullOrbitStepWeight_mod4_of_reset_of_j_pos`. -/
theorem fullOrbitStepWeight_mod4_of_reset
    (n j k0 s r rj : Nat) (t delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (t = 1 → orbitStepWeight (n - 1) % 4 = 1) ∧
      (t = 2 → orbitStepWeight (n - 1) % 4 = 2) := by
  have hj : 1 ≤ j := by
    have := resetWindowDepth_j_ge_two j k0 t delta s r rj hAt
    omega
  exact fullOrbitStepWeight_mod4_of_reset_of_j_pos
    n j k0 s rj t delta hj hreset hn hiter

/-- If the rank `v2(f(n)+1)` is at least three, then the next rank is
the previous rank minus two.  The step weight into the next state is
exactly two, and the factor `5*oddPart` is odd. -/
theorem fullOrbitIter_rank_drop_two (n : Nat)
    (hrank : 3 ≤ twoValuation (fullOrbitIter n + 1)) :
    twoValuation (fullOrbitIter (n + 1) + 1) =
      twoValuation (fullOrbitIter n + 1) - 2 := by
  let a := fullOrbitIter n + 1
  let p := twoValuation a
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ p * c := by
    dsimp [p, c]
    exact StringFlow.n_eq_two_pow_mul_oddPart a hpos
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hcpos : 0 < c := by
    have hz : c % 2 = 1 := hcodd
    by_contra hnot
    have hc0 : c = 0 := by omega
    rw [hc0] at hz
    norm_num at hz
  have hf : fullOrbitIter n = 2 ^ p * c - 1 := by
    dsimp [a] at hdec
    omega
  have hp3 : 3 ≤ p := by simpa [p] using hrank
  let d := 2 ^ (p - 2) * c
  have hpowp : 2 ^ p = 4 * 2 ^ (p - 2) := by
    have hp_eq : p = (p - 2) + 2 := by omega
    calc
      2 ^ p = 2 ^ ((p - 2) + 2) := by
        conv_lhs => rw [hp_eq]
      _ = 2 ^ (p - 2) * 2 ^ 2 := by rw [Nat.pow_add]
      _ = 4 * (2 ^ (p - 2)) := by
        have hpow2 : 2 ^ 2 = 4 := by norm_num
        rw [hpow2]
        ring_nf
  have hf_d : fullOrbitIter n = 4 * d - 1 := by
    rw [hf]
    have hcalc : 2 ^ p * c = 4 * d := by
      rw [hpowp]
      dsimp [d]
      ring_nf
    rw [hcalc]
  have hnum : 5 * (fullOrbitIter n) + 1 = 4 * (5 * d - 1) := by
    rw [hf_d]
    have hd_pos : 0 < d := by
      dsimp [d]
      exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ (p - 2)) hcpos
    omega
  have hd_even : d % 2 = 0 := by
    dsimp [d]
    have hpow2 : (2 ^ (p - 2)) % 2 = 0 := by
      have hge : 1 ≤ p - 2 := by omega
      exact StringFlow.Lte.pow_two_even_mod (p - 2) hge
    exact StringFlow.Lte.even_mul_mod_two (2 ^ (p - 2)) c hpow2
  have hd_eq : d = 2 * (d / 2) := by
    have hdvd : 2 ∣ d := Nat.dvd_iff_mod_eq_zero.mpr hd_even
    have hdec := Nat.div_add_mod d 2
    rw [hd_even] at hdec
    omega
  have hbodd : (5 * d - 1) % 2 = 1 := by
    rw [hd_eq]
    rw [show 5 * (2 * (d / 2)) = 2 * (5 * (d / 2)) by ring]
    have hq_pos : 0 < 5 * (d / 2) := by
      have hd_pos : 0 < d := by
        dsimp [d]
        exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ (p - 2)) hcpos
      have hd_ge2 : 2 ≤ d := by omega
      have hd_half : 0 < d / 2 := Nat.div_pos hd_ge2 (by decide)
      exact Nat.mul_pos (by decide : 0 < 5) hd_half
    have hdecomp : 2 * (5 * (d / 2)) - 1 =
        2 * (5 * (d / 2) - 1) + 1 := by omega
    rw [hdecomp]
    rw [Nat.add_mod]
    norm_num
  have hval := StringFlow.Lte.twoValuation_mul_two_pow_eq
    2 (5 * d - 1) hbodd
  have hval4 : twoValuation (4 * (5 * d - 1)) = 2 := by
    change twoValuation (2 ^ 2 * (5 * d - 1)) = 2
    exact hval
  have hnext : fullOrbitIter (n + 1) = 5 * d - 1 := by
    change fullOrbitStep (fullOrbitIter n) = 5 * d - 1
    unfold fullOrbitStep
    rw [hnum]
    change (4 * (5 * d - 1)) /
        2 ^ twoValuation (4 * (5 * d - 1)) = 5 * d - 1
    rw [hval4]
    norm_num [Nat.mul_div_cancel_left]
  rw [hnext]
  have hfac := StringFlow.Lte.twoValuation_mul_two_pow_eq
    (p - 2) (5 * c) (by
      rw [Nat.mul_mod]
      rw [show 5 % 2 = 1 by norm_num, hcodd])
  have hzero : 5 * d - 1 + 1 = 5 * d := by omega
  rw [hzero]
  have hcalc : 5 * d = 2 ^ (p - 2) * (5 * c) := by
    dsimp [d]
    ring
  rw [hcalc, hfac]

/-- Iterating the rank-drop law: if the starting rank is large enough
to survive `q` steps, then it loses exactly `2q`. -/
theorem fullOrbitIter_rank_drop_two_iter (n q : Nat)
    (hlarge : 2 * q + 3 <= twoValuation (fullOrbitIter n + 1)) :
    twoValuation (fullOrbitIter (n + q) + 1) =
      twoValuation (fullOrbitIter n + 1) - 2 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hlarge' : 2 * q + 3 <=
          twoValuation (fullOrbitIter n + 1) := by omega
      have ih' := ih hlarge'
      have hcurrent : 3 <=
          twoValuation (fullOrbitIter (n + q) + 1) := by
        rw [ih']
        omega
      have hdrop := fullOrbitIter_rank_drop_two (n + q) hcurrent
      have hidx : n + (q + 1) = n + q + 1 := by omega
      rw [hidx, hdrop, ih']
      omega

/-- A positive-period full-orbit state has rank at most `2P+2`.
Otherwise `P` consecutive forced `t=2` steps would return to the same
state with rank lower by `2P`. -/
theorem fullOrbit_periodic_state_rank_le (n P : Nat)
    (hP : 1 <= P)
    (hperiod : fullOrbitIter (n + P) = fullOrbitIter n) :
    twoValuation (fullOrbitIter n + 1) <= 2 * P + 2 := by
  by_contra hnot
  have hlarge : 2 * P + 3 <= twoValuation (fullOrbitIter n + 1) := by
    omega
  have hdrop := fullOrbitIter_rank_drop_two_iter n P hlarge
  rw [hperiod] at hdrop
  omega

/-- Equality of two full-orbit states propagates through every common
future shift.  This is the deterministic-orbit interface needed to
transport the cycle period from the word head to any prefix state. -/
theorem fullOrbitIter_eq_shift (a b q : Nat)
    (hab : fullOrbitIter a = fullOrbitIter b) :
    fullOrbitIter (a + q) = fullOrbitIter (b + q) := by
  induction q with
  | zero => simpa using hab
  | succ q ih =>
      have ha : a + (q + 1) = (a + q) + 1 := by omega
      have hb : b + (q + 1) = (b + q) + 1 := by omega
      rw [ha, hb]
      change fullOrbitStep (fullOrbitIter (a + q)) =
        fullOrbitStep (fullOrbitIter (b + q))
      rw [ih]

/-- Every state represented by a prefix of a closed QB-8 word has rank
at most `2P+2`.  The proof uses the concrete occurrence supplied by
`hstart`, transports the period to that occurrence, and then applies
the exact rank-drop obstruction for a periodic full-orbit state. -/
theorem cycleQb8Input_prefix_rank_le_period
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j <= w.length) :
    twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1) <=
      2 * P + 2 := by
  rcases h.hstart with ⟨n0, hstart⟩
  have hprefix := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart j hj
  have hPword : P <= w.length := by rw [h.hlength]
  have hperiodWord := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart P hPword
  have htake : w.take P = w := by
    apply List.take_of_length_le
    rw [h.hlength]
  have hperiod0 : fullOrbitIter (n0 + P) = fullOrbitIter n0 := by
    rw [hperiodWord, htake, h.hclosed, hstart]
  have hshift := fullOrbitIter_eq_shift (n0 + P) n0 j hperiod0
  have hperiodj : fullOrbitIter ((n0 + j) + P) =
      fullOrbitIter (n0 + j) := by
    have hidx : (n0 + j) + P = (n0 + P) + j := by omega
    rw [hidx]
    exact hshift
  have hrank := fullOrbit_periodic_state_rank_le (n0 + j) P
    (by have := StringFlow.CycleBridge.cycleQb8Input_P_ge_two h; omega)
    hperiodj
  rw [hprefix] at hrank
  exact hrank

/-- From any proper prefix of a closed QB-8 word, some outgoing C3
edge occurs within the next `P` full-orbit steps.  The proof rotates
the concrete C3 index through the exact full-orbit period. -/
theorem cycleQb8Input_c3_within_period_after_prefix
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (n0 : Nat) (hstart : fullOrbitIter n0 = m)
    (j : Nat) (hjP : j < P) :
    exists q : Nat, q < P /\
      3 <= orbitStepWeight ((n0 + j) + q) := by
  rcases StringFlow.CycleBridge.cycleQb8Input_exists_c3_index h with
    ⟨i, hiw, hc3⟩
  have hiP : i < P := by
    rw [← h.hlength]
    exact hiw
  have hprefixi := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart i (Nat.le_of_lt hiw)
  have hweighti : orbitStepWeight (n0 + i) = w.getI i := by
    unfold orbitStepWeight
    rw [hprefixi]
    exact h.hexact i hiw
  by_cases hji : j <= i
  · refine ⟨i - j, by omega, ?_⟩
    have hidx : (n0 + j) + (i - j) = n0 + i := by omega
    rw [hidx, hweighti]
    exact hc3
  · have hPword : P <= w.length := by rw [h.hlength]
    have hperiodWord := cycleQb8Input_prefix_fullOrbitIter_of_start
      h n0 hstart P hPword
    have htake : w.take P = w := by
      apply List.take_of_length_le
      rw [h.hlength]
    have hperiod0 : fullOrbitIter (n0 + P) = fullOrbitIter n0 := by
      rw [hperiodWord, htake, h.hclosed, hstart]
    have hperiodi := fullOrbitIter_eq_shift (n0 + P) n0 i hperiod0
    have hweightPeriod : orbitStepWeight ((n0 + P) + i) =
        orbitStepWeight (n0 + i) := by
      unfold orbitStepWeight
      rw [hperiodi]
    refine ⟨P - j + i, by omega, ?_⟩
    have hidx : (n0 + j) + (P - j + i) = (n0 + P) + i := by omega
    rw [hidx, hweightPeriod, hweighti]
    exact hc3

/-- A rank-one state advances to `5*oddPart(f+1)-1`; therefore the
next rank is the valuation of that single linear expression. -/
theorem fullOrbitIter_rank_one_step (n : Nat)
    (hrank : twoValuation (fullOrbitIter n + 1) = 1) :
    twoValuation (fullOrbitIter (n + 1) + 1) =
      twoValuation (5 * StringFlow.oddPart (fullOrbitIter n + 1) - 1) := by
  let a := fullOrbitIter n + 1
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ 1 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart a hpos
    rw [hrank] at h
    simpa [a, Nat.pow_one] using h
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hf : fullOrbitIter n = 2 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hcdec : c = 2 * (c / 2) + 1 := by
    have h := (Nat.div_add_mod c 2).symm
    rw [hcodd] at h
    omega
  have hnum : 5 * fullOrbitIter n + 1 = 2 * (5 * c - 2) := by
    rw [hf, hcdec]
    omega
  have hbodd : (5 * c - 2) % 2 = 1 := by
    rw [hcdec]
    omega
  have hval := StringFlow.Lte.twoValuation_mul_two_pow_eq 1 (5 * c - 2) hbodd
  have hnext : fullOrbitIter (n + 1) = 5 * c - 2 := by
    change fullOrbitStep (fullOrbitIter n) = 5 * c - 2
    unfold fullOrbitStep
    rw [hnum]
    have hval2 : twoValuation (2 * (5 * c - 2)) = 1 := by
      simpa [Nat.pow_one] using hval
    change (2 * (5 * c - 2)) /
        2 ^ twoValuation (2 * (5 * c - 2)) = 5 * c - 2
    rw [hval2]
    norm_num [Nat.mul_div_cancel_left]
  rw [hnext]
  rw [show 5 * c - 2 + 1 = 5 * c - 1 by omega]

/-- The incoming step weight of a rank-one full-orbit state is exactly
`1`; this is the rank-dynamics half of the reset-weight alignment. -/
theorem orbitStepWeight_of_rank_one (n : Nat)
    (hrank : twoValuation (fullOrbitIter n + 1) = 1) :
    orbitStepWeight n = 1 := by
  let a := fullOrbitIter n + 1
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart a hpos
    rw [hrank] at h
    simpa [a, Nat.pow_one] using h
  have hf : fullOrbitIter n = 2 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hcdec : c = 2 * (c / 2) + 1 := by
    have h := (Nat.div_add_mod c 2).symm
    rw [hcodd] at h
    omega
  have hnum : 5 * fullOrbitIter n + 1 = 2 * (5 * c - 2) := by
    rw [hf, hcdec]
    omega
  have hbodd : (5 * c - 2) % 2 = 1 := by
    rw [hcdec]
    omega
  have hval := StringFlow.Lte.twoValuation_mul_two_pow_eq 1 (5 * c - 2) hbodd
  have hnext_state : fullOrbitIter (n + 1) = 5 * c - 2 := by
    change fullOrbitStep (fullOrbitIter n) = 5 * c - 2
    unfold fullOrbitStep
    rw [hnum]
    have hval2 : twoValuation (2 * (5 * c - 2)) = 1 := by
      simpa [Nat.pow_one] using hval
    change (2 * (5 * c - 2)) /
        2 ^ twoValuation (2 * (5 * c - 2)) = 5 * c - 2
    rw [hval2]
    norm_num [Nat.mul_div_cancel_left]
  have hstep : 5 * fullOrbitIter n + 1 = 2 * fullOrbitIter (n + 1) := by
    rw [hnum, hnext_state]
  have hmul := fullOrbitStep_mul_eq (fullOrbitIter n)
  have hnext_pos : 0 < fullOrbitIter (n + 1) := by
    have hodd : fullOrbitIter (n + 1) % 2 = 1 := fullOrbitIter_odd (n + 1)
    by_contra hnot
    have h0 : fullOrbitIter (n + 1) = 0 := by omega
    rw [h0] at hodd
    norm_num at hodd
  have hcancel : 2 ^ orbitStepWeight n = 2 := by
    have hleft : 2 ^ orbitStepWeight n * fullOrbitIter (n + 1) =
        5 * fullOrbitIter n + 1 := by
      change 2 ^ twoValuation (5 * fullOrbitIter n + 1) *
          fullOrbitStep (fullOrbitIter n) = 5 * fullOrbitIter n + 1
      exact hmul
    have hright : 2 * fullOrbitIter (n + 1) = 5 * fullOrbitIter n + 1 := by
      rw [← hstep]
    have hcomm : fullOrbitIter (n + 1) * 2 ^ orbitStepWeight n =
        fullOrbitIter (n + 1) * 2 := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (hleft.trans hright.symm)
    exact Nat.eq_of_mul_eq_mul_left hnext_pos hcomm
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hcancel

/-- A rank-two state advances to the odd part of `5*oddPart(f+1)-1`;
the next state has rank `v2(q+1)`, where `q` is that odd part. -/
theorem fullOrbitIter_rank_two_step (n : Nat)
    (hrank : twoValuation (fullOrbitIter n + 1) = 2) :
    fullOrbitIter (n + 1) + 1 =
      StringFlow.oddPart (5 * StringFlow.oddPart (fullOrbitIter n + 1) - 1) + 1 := by
  let a := fullOrbitIter n + 1
  let c := StringFlow.oddPart a
  let b := 5 * c - 1
  let q := StringFlow.oddPart b
  let v := twoValuation b
  have hposa : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ 2 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart a hposa
    rw [hrank] at h
    simpa [a, Nat.pow_two] using h
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hposa
  have hf : fullOrbitIter n = 4 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hbpos : 0 < b := by
    dsimp [b]
    have hcpos : 0 < c := by
      have hz : c % 2 = 1 := hcodd
      by_contra hnot
      have hc0 : c = 0 := by omega
      rw [hc0] at hz
      norm_num at hz
    omega
  have hdecb : b = 2 ^ v * q := by
    dsimp [q, v]
    exact StringFlow.n_eq_two_pow_mul_oddPart b hbpos
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    exact StringFlow.oddPart_odd_of_pos b hbpos
  have hnum : 5 * fullOrbitIter n + 1 = 4 * b := by
    rw [hf]
    dsimp [b]
    omega
  have hfac : 4 * (2 ^ v * q) = 2 ^ (2 + v) * q := by
    change 2 ^ 2 * (2 ^ v * q) = 2 ^ (2 + v) * q
    have hpow : 2 ^ 2 * 2 ^ v = 2 ^ (2 + v) := by
      rw [← Nat.pow_add]
    calc
      2 ^ 2 * (2 ^ v * q) = (2 ^ 2 * 2 ^ v) * q := by ring
      _ = 2 ^ (2 + v) * q := by rw [hpow]
  have hval := StringFlow.Lte.twoValuation_mul_two_pow_eq
    (2 + v) q hqodd
  have hstep : fullOrbitIter (n + 1) = q := by
    change fullOrbitStep (fullOrbitIter n) = q
    unfold fullOrbitStep
    rw [hnum, hdecb, hfac]
    change (2 ^ (2 + v) * q) /
        2 ^ twoValuation (2 ^ (2 + v) * q) = q
    rw [hval]
    rw [Nat.mul_div_cancel_left q (by positivity : 0 < 2 ^ (2 + v))]
  rw [hstep]

/-- The state transition for rank at least three is explicit:
`f(n+1)=5*2^(p-2)*oddPart(f(n)+1)-1`, where `p=v2(f(n)+1)`. -/
theorem fullOrbitIter_rank_ge_three_state (n : Nat)
    (hrank : 3 ≤ twoValuation (fullOrbitIter n + 1)) :
    fullOrbitIter (n + 1) =
      5 * 2 ^ (twoValuation (fullOrbitIter n + 1) - 2) *
          StringFlow.oddPart (fullOrbitIter n + 1) - 1 := by
  let a := fullOrbitIter n + 1
  let p := twoValuation a
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ p * c := by
    dsimp [p, c]
    exact StringFlow.n_eq_two_pow_mul_oddPart a hpos
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hf : fullOrbitIter n = 2 ^ p * c - 1 := by
    dsimp [a] at hdec
    omega
  have hp3 : 3 ≤ p := by simpa [p] using hrank
  let Y := 5 * 2 ^ (p - 2) * c - 1
  have hYodd : Y % 2 = 1 := by
    dsimp [Y]
    have hpow2 : (2 ^ (p - 2)) % 2 = 0 := by
      have hge : 1 ≤ p - 2 := by omega
      exact StringFlow.Lte.pow_two_even_mod (p - 2) hge
    have hmul : (5 * 2 ^ (p - 2) * c) % 2 = 0 := by
      have h5pow : (5 * 2 ^ (p - 2)) % 2 = 0 := by
        rw [Nat.mul_mod, hpow2]
      exact StringFlow.Lte.even_mul_mod_two (5 * 2 ^ (p - 2)) c h5pow
    have hdvd : 2 ∣ 5 * 2 ^ (p - 2) * c :=
      Nat.dvd_iff_mod_eq_zero.mpr hmul
    rcases hdvd with ⟨d, hd⟩
    have hcpos : 0 < c := by
      have hz : c % 2 = 1 := hcodd
      by_contra hnot
      have hc0 : c = 0 := by omega
      rw [hc0] at hz
      norm_num at hz
    have horigpos : 0 < 5 * 2 ^ (p - 2) * c := by
      have h5powpos : 0 < 5 * 2 ^ (p - 2) :=
        Nat.mul_pos (by positivity : 0 < 5)
          (Nat.pow_pos (by decide : 0 < 2))
      exact Nat.mul_pos h5powpos hcpos
    have hdpos : 0 < d := by nlinarith [hd, horigpos]
    rw [hd]
    have hdecomp : 2 * d - 1 = 2 * (d - 1) + 1 := by omega
    rw [hdecomp, Nat.add_mod]
    norm_num
  have hfac : 5 * fullOrbitIter n + 1 = 4 * Y := by
    dsimp [Y]
    have hpow : 2 ^ p = 4 * 2 ^ (p - 2) := by
      have hp_eq : p = (p - 2) + 2 := by omega
      calc
        2 ^ p = 2 ^ ((p - 2) + 2) := by
          conv_lhs => rw [hp_eq]
        _ = 2 ^ (p - 2) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = 4 * 2 ^ (p - 2) := by
          have hpow2 : 2 ^ 2 = 4 := by norm_num
          change 2 ^ (p - 2) * 2 ^ 2 = 4 * 2 ^ (p - 2)
          rw [hpow2]
          exact Nat.mul_comm _ _
    let d := 2 ^ (p - 2) * c
    have hf' : fullOrbitIter n = 4 * d - 1 := by
      rw [hf, hpow]
      dsimp [d]
      ring_nf
    have hdpos : 0 < d := by
      dsimp [d]
      have hcpos : 0 < c := by
        have hz : c % 2 = 1 := hcodd
        by_contra hnot
        have hc0 : c = 0 := by omega
        rw [hc0] at hz
        norm_num at hz
      exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
    have hnum' : 5 * (4 * d - 1) + 1 = 4 * (5 * d - 1) := by
      omega
    rw [hf', hnum']
    dsimp [d]
    ring_nf
  have hvalY := StringFlow.Lte.twoValuation_mul_two_pow_eq 2 Y hYodd
  have hstep : fullOrbitStep (fullOrbitIter n) = Y := by
    unfold fullOrbitStep
    have hval : twoValuation (5 * fullOrbitIter n + 1) = 2 := by
      rw [hfac]
      change twoValuation (2 ^ 2 * Y) = 2
      exact hvalY
    change (5 * fullOrbitIter n + 1) /
        2 ^ twoValuation (5 * fullOrbitIter n + 1) = Y
    rw [hval, hfac]
    change 4 * Y / 4 = Y
    rw [Nat.mul_div_cancel_left Y (by decide : 0 < 4)]
  change fullOrbitStep (fullOrbitIter n) =
      5 * 2 ^ (p - 2) * c - 1
  rw [hstep]

/-- The incoming step weight from a rank-`≥3` state is exactly `2`. -/
theorem orbitStepWeight_of_rank_ge_three (n : Nat)
    (hrank : 3 ≤ twoValuation (fullOrbitIter n + 1)) :
    orbitStepWeight n = 2 := by
  let a := fullOrbitIter n + 1
  let p := twoValuation a
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ p * c := by
    dsimp [p, c]
    exact StringFlow.n_eq_two_pow_mul_oddPart a hpos
  have hf : fullOrbitIter n = 2 ^ p * c - 1 := by
    dsimp [a] at hdec
    omega
  have hp3 : 3 ≤ p := by simpa [p] using hrank
  have hstate := fullOrbitIter_rank_ge_three_state n hrank
  have hnext : fullOrbitIter (n + 1) = 5 * 2 ^ (p - 2) * c - 1 := by
    simpa [p, c, a] using hstate
  have hfac : 5 * fullOrbitIter n + 1 = 4 * fullOrbitIter (n + 1) := by
    have hpow : 2 ^ p = 4 * 2 ^ (p - 2) := by
      have hp_eq : p = (p - 2) + 2 := by omega
      calc
        2 ^ p = 2 ^ ((p - 2) + 2) := by
          conv_lhs => rw [hp_eq]
        _ = 2 ^ (p - 2) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = 4 * 2 ^ (p - 2) := by
          have hpow2 : 2 ^ 2 = 4 := by norm_num
          change 2 ^ (p - 2) * 2 ^ 2 = 4 * 2 ^ (p - 2)
          rw [hpow2]
          exact Nat.mul_comm _ _
    have hcpos : 0 < c := by
      have hcodd : c % 2 = 1 := by
        dsimp [c]
        exact StringFlow.oddPart_odd_of_pos a hpos
      have hz : c % 2 = 1 := hcodd
      by_contra hnot
      have hc0 : c = 0 := by omega
      rw [hc0] at hz
      norm_num at hz
    let d := 2 ^ (p - 2) * c
    have hnext_d : fullOrbitIter (n + 1) = 5 * d - 1 := by
      rw [hnext]
      dsimp [d]
      ring_nf
    have hf_d : fullOrbitIter n = 4 * d - 1 := by
      rw [hf]
      have hcalc : 2 ^ p * c = 4 * d := by
        rw [hpow]
        dsimp [d]
        ring_nf
      rw [hcalc]
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
    have hnum' : 5 * (4 * d - 1) + 1 = 4 * (5 * d - 1) := by
      omega
    rw [hf_d, hnext_d, hnum']
  have hmul := fullOrbitStep_mul_eq (fullOrbitIter n)
  have hnext_pos : 0 < fullOrbitIter (n + 1) := by
    have hodd : fullOrbitIter (n + 1) % 2 = 1 := fullOrbitIter_odd (n + 1)
    by_contra hnot
    have h0 : fullOrbitIter (n + 1) = 0 := by omega
    rw [h0] at hodd
    norm_num at hodd
  have hcancel : 2 ^ orbitStepWeight n = 4 := by
    have hleft : 2 ^ orbitStepWeight n * fullOrbitIter (n + 1) =
        5 * fullOrbitIter n + 1 := by
      change 2 ^ twoValuation (5 * fullOrbitIter n + 1) *
          fullOrbitStep (fullOrbitIter n) = 5 * fullOrbitIter n + 1
      exact hmul
    have hright : 4 * fullOrbitIter (n + 1) = 5 * fullOrbitIter n + 1 := by
      rw [← hfac]
    have hcomm : fullOrbitIter (n + 1) * 2 ^ orbitStepWeight n =
        fullOrbitIter (n + 1) * 4 := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (hleft.trans hright.symm)
    exact Nat.eq_of_mul_eq_mul_left hnext_pos hcomm
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hcancel

/-- A sufficiently high-rank cycle prefix forces a concrete run of
outgoing weight-two edges.  This is the word-level form of the exact
rank-drop law, with no abstract reachability or reset parameters left. -/
theorem cycleQb8Input_forced_two_after_prefix
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (j q : Nat) (hjq : j + q < w.length)
    (hrank : 2 * q + 3 <=
      twoValuation (StringFlow.Word.wordOrbit (w.take j) m + 1)) :
    forall k : Nat, k <= q -> w.getI (j + k) = 2 := by
  rcases h.hstart with ⟨n0, hstart⟩
  have hjw : j <= w.length := by omega
  have hprefix0 := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart j hjw
  have hrank0 : 2 * q + 3 <=
      twoValuation (fullOrbitIter (n0 + j) + 1) := by
    rw [hprefix0]
    exact hrank
  intro k hk
  have hjk : j + k < w.length := by omega
  have hlarge : 2 * k + 3 <=
      twoValuation (fullOrbitIter (n0 + j) + 1) := by omega
  have hdrop := fullOrbitIter_rank_drop_two_iter (n0 + j) k hlarge
  have hrankk : 3 <=
      twoValuation (fullOrbitIter ((n0 + j) + k) + 1) := by
    rw [hdrop]
    omega
  have hweight := orbitStepWeight_of_rank_ge_three ((n0 + j) + k) hrankk
  have hprefixk := cycleQb8Input_prefix_fullOrbitIter_of_start
    h n0 hstart (j + k) (Nat.le_of_lt hjk)
  have hidx : (n0 + j) + k = n0 + (j + k) := by omega
  unfold orbitStepWeight at hweight
  rw [hidx, hprefixk] at hweight
  have hexact := h.hexact (j + k) hjk
  exact hexact.symm.trans hweight

/-- The incoming step weight from a rank-two state is
`2+v2(5*oddPart(f+1)-1)`. -/
theorem orbitStepWeight_of_rank_two (n : Nat)
    (hrank : twoValuation (fullOrbitIter n + 1) = 2) :
    orbitStepWeight n =
      2 + twoValuation (5 * StringFlow.oddPart (fullOrbitIter n + 1) - 1) := by
  let a := fullOrbitIter n + 1
  let c := StringFlow.oddPart a
  let b := 5 * c - 1
  let q := StringFlow.oddPart b
  let v := twoValuation b
  have hposa : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ 2 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart a hposa
    rw [hrank] at h
    simpa [a, Nat.pow_two] using h
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hposa
  have hbpos : 0 < b := by
    dsimp [b]
    have hcpos : 0 < c := by
      have hz : c % 2 = 1 := hcodd
      by_contra hnot
      have hc0 : c = 0 := by omega
      rw [hc0] at hz
      norm_num at hz
    omega
  have hdecb : b = 2 ^ v * q := by
    dsimp [q, v]
    exact StringFlow.n_eq_two_pow_mul_oddPart b hbpos
  have hqodd : q % 2 = 1 := by
    dsimp [q]
    exact StringFlow.oddPart_odd_of_pos b hbpos
  have hstate := fullOrbitIter_rank_two_step n hrank
  have hnext : fullOrbitIter (n + 1) = q := by
    simpa [q, b, c, a] using hstate
  have hf : fullOrbitIter n = 4 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hfac : 5 * fullOrbitIter n + 1 = 2 ^ (2 + v) * q := by
    rw [hf]
    dsimp [b] at hdecb
    have hnum : 5 * (4 * c - 1) + 1 = 4 * (5 * c - 1) := by omega
    rw [hnum, hdecb]
    have hpow : 2 ^ 2 * 2 ^ v = 2 ^ (2 + v) := by
      rw [← Nat.pow_add]
    calc
      4 * (2 ^ v * q) = 2 ^ 2 * (2 ^ v * q) := by norm_num
      _ = (2 ^ 2 * 2 ^ v) * q := by ring
      _ = 2 ^ (2 + v) * q := by rw [hpow]
  have hmul := fullOrbitStep_mul_eq (fullOrbitIter n)
  have hnext_pos : 0 < fullOrbitIter (n + 1) := by
    have hodd : fullOrbitIter (n + 1) % 2 = 1 := fullOrbitIter_odd (n + 1)
    by_contra hnot
    have h0 : fullOrbitIter (n + 1) = 0 := by omega
    rw [h0] at hodd
    norm_num at hodd
  have hcancel : 2 ^ orbitStepWeight n = 2 ^ (2 + v) := by
    have hleft : 2 ^ orbitStepWeight n * fullOrbitIter (n + 1) =
        5 * fullOrbitIter n + 1 := by
      change 2 ^ twoValuation (5 * fullOrbitIter n + 1) *
          fullOrbitStep (fullOrbitIter n) = 5 * fullOrbitIter n + 1
      exact hmul
    have hright : 2 ^ (2 + v) * fullOrbitIter (n + 1) =
        5 * fullOrbitIter n + 1 := by
      rw [hnext, hfac]
    have hcomm : fullOrbitIter (n + 1) * 2 ^ orbitStepWeight n =
        fullOrbitIter (n + 1) * 2 ^ (2 + v) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (hleft.trans hright.symm)
    exact Nat.eq_of_mul_eq_mul_left hnext_pos hcomm
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hcancel

/-- For a `t=1` reset, the real incoming step weight has only the
rank-one branch `w=1` and the rank-two branch `w=2+v` with
`v≡3 (mod 4)`. -/
theorem reset_t1_incoming_weight_exact_of_j_pos
    (n j k0 s rj : Nat)
    (hj : 1 ≤ j)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (twoValuation (fullOrbitIter (n - 1) + 1) = 1 ∧
        orbitStepWeight (n - 1) = 1) ∨
      (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
        twoValuation
            (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 3) := by
  have hmod := fullOrbitStepWeight_mod4_of_reset_of_j_pos
    n j k0 s rj 1 1 hj hreset hn hiter
  have hw1 : orbitStepWeight (n - 1) % 4 = 1 := hmod.1 rfl
  let p := twoValuation (fullOrbitIter (n - 1) + 1)
  by_cases hp1 : p = 1
  · left
    have hrank1 : twoValuation (fullOrbitIter (n - 1) + 1) = 1 := by
      dsimp [p] at hp1
      exact hp1
    exact ⟨hp1, orbitStepWeight_of_rank_one (n - 1) hrank1⟩
  · by_cases hp2 : p = 2
    · right
      have hrank2 : twoValuation (fullOrbitIter (n - 1) + 1) = 2 := by
        dsimp [p] at hp2
        exact hp2
      have hstep := orbitStepWeight_of_rank_two (n - 1) hrank2
      let v := twoValuation
        (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1)
      have hv3 : v % 4 = 3 := by
        have hw : orbitStepWeight (n - 1) = 2 + v := by
          simpa [v] using hstep
        rw [hw] at hw1
        omega
      exact ⟨hp2, hv3⟩
    · exfalso
      have hpge : 3 ≤ p := by
        have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ 3 ≤ p := by omega
        rcases hcases with h0 | h1 | h2 | hge
        · dsimp [p] at h0
          have hposv : 0 < fullOrbitIter (n - 1) + 1 := by positivity
          have hoddv := StringFlow.twoValuation_eq_zero_odd
            (fullOrbitIter (n - 1) + 1) hposv h0
          have hfodd : fullOrbitIter (n - 1) % 2 = 1 := fullOrbitIter_odd (n - 1)
          have hsum : (fullOrbitIter (n - 1) + 1) % 2 =
              (fullOrbitIter (n - 1) % 2 + 1) % 2 := by rw [Nat.add_mod]
          rw [hsum, hfodd] at hoddv
          norm_num at hoddv
        · exact False.elim (hp1 h1)
        · exact False.elim (hp2 h2)
        · exact hge
      have hrank3 : 3 ≤ twoValuation (fullOrbitIter (n - 1) + 1) := by
        dsimp [p] at hpge
        exact hpge
      have hw2 : orbitStepWeight (n - 1) = 2 :=
        orbitStepWeight_of_rank_ge_three (n - 1) hrank3
      rw [hw2] at hw1
      norm_num at hw1

/-- Backward-compatible depth-aligned wrapper for
`reset_t1_incoming_weight_exact_of_j_pos`. -/
theorem reset_t1_incoming_weight_exact
    (n j k0 s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 1 1 s r rj)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (twoValuation (fullOrbitIter (n - 1) + 1) = 1 ∧
        orbitStepWeight (n - 1) = 1) ∨
      (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
        twoValuation
            (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 3) := by
  have hj : 1 ≤ j := by
    have := resetWindowDepth_j_ge_two j k0 1 1 s r rj hAt
    omega
  exact reset_t1_incoming_weight_exact_of_j_pos
    n j k0 s rj hj hreset hn hiter

/-- For a `t=2` reset, the real incoming step weight has only the
rank-`≥3` branch `w=2` and the rank-two branch `w=2+v` with
`v≡0 (mod 4)`. -/
theorem reset_t2_incoming_weight_exact_of_j_pos
    (n j k0 s rj delta : Nat)
    (hj : 1 ≤ j)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (3 ≤ twoValuation (fullOrbitIter (n - 1) + 1) ∧
        orbitStepWeight (n - 1) = 2) ∨
      (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
        twoValuation
            (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 0) := by
  have hmod := fullOrbitStepWeight_mod4_of_reset_of_j_pos
    n j k0 s rj 2 delta hj hreset hn hiter
  have hw2 : orbitStepWeight (n - 1) % 4 = 2 := hmod.2 rfl
  let p := twoValuation (fullOrbitIter (n - 1) + 1)
  by_cases hp1 : p = 1
  · exfalso
    have hrank1 : twoValuation (fullOrbitIter (n - 1) + 1) = 1 := by
      dsimp [p] at hp1
      exact hp1
    have hw1 : orbitStepWeight (n - 1) = 1 :=
      orbitStepWeight_of_rank_one (n - 1) hrank1
    rw [hw1] at hw2
    norm_num at hw2
  · by_cases hp2 : p = 2
    · right
      have hrank2 : twoValuation (fullOrbitIter (n - 1) + 1) = 2 := by
        dsimp [p] at hp2
        exact hp2
      have hstep := orbitStepWeight_of_rank_two (n - 1) hrank2
      let v := twoValuation
        (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1)
      have hv0 : v % 4 = 0 := by
        have hw : orbitStepWeight (n - 1) = 2 + v := by
          simpa [v] using hstep
        rw [hw] at hw2
        omega
      exact ⟨hp2, hv0⟩
    · left
      have hpge : 3 ≤ p := by
        have hcases : p = 0 ∨ p = 1 ∨ p = 2 ∨ 3 ≤ p := by omega
        rcases hcases with h0 | h1 | h2 | hge
        · dsimp [p] at h0
          have hposv : 0 < fullOrbitIter (n - 1) + 1 := by positivity
          have hoddv := StringFlow.twoValuation_eq_zero_odd
            (fullOrbitIter (n - 1) + 1) hposv h0
          have hfodd : fullOrbitIter (n - 1) % 2 = 1 := fullOrbitIter_odd (n - 1)
          have hsum : (fullOrbitIter (n - 1) + 1) % 2 =
              (fullOrbitIter (n - 1) % 2 + 1) % 2 := by rw [Nat.add_mod]
          rw [hsum, hfodd] at hoddv
          norm_num at hoddv
        · exact False.elim (hp1 h1)
        · exact False.elim (hp2 h2)
        · exact hge
      have hrank3 : 3 ≤ twoValuation (fullOrbitIter (n - 1) + 1) := by
        dsimp [p] at hpge
        exact hpge
      exact ⟨hrank3, orbitStepWeight_of_rank_ge_three (n - 1) hrank3⟩

/-- Backward-compatible depth-aligned wrapper for
`reset_t2_incoming_weight_exact_of_j_pos`. -/
theorem reset_t2_incoming_weight_exact
    (n j k0 s r rj delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 2 delta s r rj)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (3 ≤ twoValuation (fullOrbitIter (n - 1) + 1) ∧
        orbitStepWeight (n - 1) = 2) ∨
      (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
        twoValuation
            (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 0) := by
  have hj : 1 ≤ j := by
    have := resetWindowDepth_j_ge_two j k0 2 delta s r rj hAt
    omega
  exact reset_t2_incoming_weight_exact_of_j_pos
    n j k0 s rj delta hj hreset hn hiter

/-- When the real incoming weight agrees with the reset weight, the
two equations determine the full-orbit predecessor `f(n-1)`.  This
algebraic identity does not require depth alignment. -/
theorem reset_full_predecessor_alignment_core
    (n j k0 t delta s r rj : Nat)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj)
    (hw : orbitStepWeight (n - 1) = t) :
    5 * fullOrbitIter (n - 1) =
      5 ^ (k0 + 1) * s + delta * 5 ^ j - 5 := by
  have hpred := fullOrbit_predecessor_mul n rj hn hiter
  rcases hreset with h1 | h2
  · rcases h1 with ⟨ht, hd1, heq⟩
    have hwt : orbitStepWeight (n - 1) = 1 := by
      simpa [ht] using hw
    subst delta
    have hfull : 2 * rj = 5 * fullOrbitIter (n - 1) + 1 := by
      change 2 ^ 1 * rj = 5 * fullOrbitIter (n - 1) + 1
      rw [hwt] at hpred
      exact hpred
    have hreset' : 2 * (rj + 1) = 5 ^ (k0 + 1) * s + 5 ^ j - 2 := by
      simpa using heq
    omega
  · rcases h2 with ⟨ht, hd, heq⟩
    have hwt : orbitStepWeight (n - 1) = 2 := by
      simpa [ht] using hw
    have hfull : 4 * rj = 5 * fullOrbitIter (n - 1) + 1 := by
      change 2 ^ 2 * rj = 5 * fullOrbitIter (n - 1) + 1
      rw [hwt] at hpred
      exact hpred
    have hreset' : 4 * (rj + 1) = 5 ^ (k0 + 1) * s + delta * 5 ^ j := by
      simpa using heq
    omega

/-- Backward-compatible depth-aligned wrapper for
`reset_full_predecessor_alignment_core`. -/
theorem reset_full_predecessor_alignment
    (n j k0 t delta s r rj : Nat)
    (_hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj)
    (hw : orbitStepWeight (n - 1) = t) :
    5 * fullOrbitIter (n - 1) =
      5 ^ (k0 + 1) * s + delta * 5 ^ j - 5 :=
  reset_full_predecessor_alignment_core
    n j k0 t delta s r rj hreset hn hiter hw

/-- In the equal-weight branches, the reset predecessor is exactly
`f(n-1)`.  Positive reset depth is the only depth input needed. -/
theorem reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    (n j k0 t delta s r rj : Nat)
    (hj : 1 ≤ j)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj)
    (hw : orbitStepWeight (n - 1) = t) :
    5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1) := by
  have hAl := reset_full_predecessor_alignment_core
    n j k0 t delta s r rj hreset hn hiter hw
  let x := 5 ^ k0 * s + delta * 5 ^ (j - 1) - 1
  have hpow1 : 5 ^ (k0 + 1) * s = 5 * (5 ^ k0 * s) := by
    rw [Nat.pow_succ]
    ring
  have hpow2 : delta * 5 ^ j = 5 * (delta * 5 ^ (j - 1)) := by
    have hj_eq : j = (j - 1) + 1 := by omega
    conv_lhs => rw [hj_eq, Nat.pow_succ]
    ring
  have hx : 5 * x + 1 = 5 * fullOrbitIter (n - 1) + 1 := by
    dsimp [x]
    rw [hAl, hpow1, hpow2]
    omega
  have hfive : 5 * x = 5 * fullOrbitIter (n - 1) := by omega
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) hfive

/-- Backward-compatible depth-aligned wrapper for
`reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos`. -/
theorem reset_predecessor_eq_fullOrbit_of_aligned_weight
    (n j k0 t delta s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj)
    (hw : orbitStepWeight (n - 1) = t) :
    5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1) := by
  have hj : 1 ≤ j := by
    have := resetWindowDepth_j_ge_two j k0 t delta s r rj hAt
    omega
  exact reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    n j k0 t delta s r rj hj hreset hn hiter hw

/-- Exact real-predecessor split for a weakly reachable `t=1` window.
In the aligned branch the reset predecessor is the actual full-orbit
predecessor; the only alternative is the rank-two/high-weight branch. -/
theorem reset_t1_real_predecessor_cases
    (j k0 s rj : Nat)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hreach : ResetWindowReachability j k0 1 1 s) :
    ∃ n : Nat, 1 ≤ n ∧ fullOrbitIter n = rj ∧
      ((twoValuation (fullOrbitIter (n - 1) + 1) = 1 ∧
          orbitStepWeight (n - 1) = 1 ∧
          5 ^ k0 * s + 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1)) ∨
        (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
          twoValuation
              (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 3)) := by
  have hj : 1 ≤ j := resetWindowReachability_j_pos j k0 1 1 s hreach
  rcases resetWindowReachability_explicit_fullOrbit_pos
      j k0 1 1 s rj hreset hreach with ⟨n, hn, hiter⟩
  have hcases := reset_t1_incoming_weight_exact_of_j_pos
    n j k0 s rj hj hreset hn hiter
  refine ⟨n, hn, hiter, ?_⟩
  rcases hcases with hsmall | hlarge
  · left
    refine ⟨hsmall.1, hsmall.2, ?_⟩
    simpa using
      (reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
        n j k0 1 1 s 0 rj hj hreset hn hiter hsmall.2)
  · exact Or.inr hlarge

/-- Exact real-predecessor split for a weakly reachable `t=2` window.
The aligned branch has incoming weight two; the alternative starts at
predecessor rank two and has the extra valuation divisible by four. -/
theorem reset_t2_real_predecessor_cases
    (j k0 delta s rj : Nat)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hreach : ResetWindowReachability j k0 2 delta s) :
    ∃ n : Nat, 1 ≤ n ∧ fullOrbitIter n = rj ∧
      ((3 ≤ twoValuation (fullOrbitIter (n - 1) + 1) ∧
          orbitStepWeight (n - 1) = 2 ∧
          5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 =
            fullOrbitIter (n - 1)) ∨
        (twoValuation (fullOrbitIter (n - 1) + 1) = 2 ∧
          twoValuation
              (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) % 4 = 0)) := by
  have hj : 1 ≤ j := resetWindowReachability_j_pos j k0 2 delta s hreach
  rcases resetWindowReachability_explicit_fullOrbit_pos
      j k0 2 delta s rj hreset hreach with ⟨n, hn, hiter⟩
  have hcases := reset_t2_incoming_weight_exact_of_j_pos
    n j k0 s rj delta hj hreset hn hiter
  refine ⟨n, hn, hiter, ?_⟩
  rcases hcases with hsmall | hlarge
  · left
    refine ⟨hsmall.1, hsmall.2, ?_⟩
    exact reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
      n j k0 2 delta s 0 rj hj hreset hn hiter hsmall.2
  · exact Or.inr hlarge

/-- A failure window with separate global and local coordinates.

`g` is the global cycle-word prefix at the block head, whereas `j` is
the reset depth inside the selected local block.  In the intended
cyclic-block construction these are respectively `b + L` and `L`.
Keeping both coordinates in the type prevents the legacy identification
of the global prefix with the local reset depth. -/
structure LocalDepthFailureWindow
    (m S P : Nat) (w rise c3 : List Nat)
    (g j k0 t delta s : Nat) : Prop where
  hinput : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3
  hg_pos : 1 <= g
  hg_lt : g < P
  ht : t = 1 \/ t = 2
  hincoming : w.getI (g - 1) = t
  hdelta : (t = 1 -> delta = 1) /\
    (t = 2 -> delta = 1 \/ delta = 3)
  hreset : ResetHeadEq s j k0 t delta
    (StringFlow.Word.wordOrbit (w.take g) m)
  hreach : ResetWindowReachability j k0 t delta s
  hs_odd : s % 2 = 1
  hs_not_five : Not (5 ∣ s)
  hk : k0 + 1 <= j
  hs_lt : s < 5 ^ (j - k0 - 1)
  hfail_t1 : t = 1 -> 2 * j + 12 <=
    twoValuation (5 ^ (k0 + 1) * s + 5 ^ j - 2)
  hfail_t2 : t = 2 -> 2 * j + 11 <=
    twoValuation (5 ^ (k0 + 1) * s + delta * 5 ^ j)

/-- The fully sourced cyclic form of a local-depth failure window.
It retains the boundary index `b` and the single real terminal `rt`;
the embedded window is forced to use global head `b+j`, local reset
depth `j`, and exactly `rt.k, rt.s`. -/
structure CyclicLocalFailureWindow
    (m S P : Nat) (w rise c3 : List Nat)
    (b j t delta : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal) : Prop where
  hboundary : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b
  hterminal : rt.r =
    (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2
  hwindow : LocalDepthFailureWindow m S P w rise c3
    (b + j) j rt.k t delta rt.s

/-- Fully cyclic failure window.  Unlike the non-wrapping compatibility
wrapper above, its head and incoming edge stay in the rotated local
word, so it covers both sides of the end of `w`.  The local reset depth
is exactly `j`, and the unique previous terminal is retained as `rt`. -/
structure CyclicDepthFailureWindow
    (m S P : Nat) (w rise c3 : List Nat)
    (b j t delta : Nat)
    (rt : S6Audit.AngelinaGilbertaRealTerminal) : Prop where
  hinput : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3
  hboundary : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b
  hj_pos : 1 <= j
  hj_le : j <= w.length
  hterminal : rt.r =
    (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2
  ht : t = 1 \/ t = 2
  hincoming :
    (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (j - 1) = t
  hdelta : (t = 1 -> delta = 1) /\
    (t = 2 -> delta = 1 \/ delta = 3)
  hreset : ResetHeadEq rt.s j rt.k t delta
    (StringFlow.Word.wordOrbit
      ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
      (StringFlow.Word.wordOrbit (w.take b) m))
  hreach : ResetWindowReachability j rt.k t delta rt.s
  hk : rt.k + 1 <= j
  hs_lt : rt.s < 5 ^ (j - rt.k - 1)
  hfail_t1 : t = 1 -> 2 * j + 12 <=
    twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ j - 2)
  hfail_t2 : t = 2 -> 2 * j + 11 <=
    twoValuation (5 ^ (rt.k + 1) * rt.s + delta * 5 ^ j)

/-- A local `hident` block supplies the reset equation and reachability
at local depth `j`; the concrete word occurrence remains at the
independent global prefix `g`. -/
theorem local_hident_to_localDepthFailureWindow
    {m S P : Nat} {w rise c3 : List Nat}
    {g j Wp Wj q Aj rj t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (hg_pos : 1 <= g) (hg_lt : g < P)
    (hrj_eq : rj = StringFlow.Word.wordOrbit (w.take g) m)
    (hincoming : w.getI (g - 1) = t)
    (d : StringFlow.CycleBridge.LocalHidentBlock
      j Wp Wj q Aj rj t delta rt)
    (hfail_t1 : t = 1 -> 2 * j + 12 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ j - 2))
    (hfail_t2 : t = 2 -> 2 * j + 11 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + delta * 5 ^ j)) :
    LocalDepthFailureWindow m S P w rise c3
      g j rt.k t delta rt.s := by
  rcases StringFlow.CycleBridge.local_hident_to_reset_reachability d with
    ⟨hreset, hreach⟩
  exact {
    hinput := h
    hg_pos := hg_pos
    hg_lt := hg_lt
    ht := d.ht
    hincoming := hincoming
    hdelta := d.hδ
    hreset := by
      rw [← hrj_eq]
      exact hreset
    hreach := hreach
    hs_odd := rt.hs_odd
    hs_not_five := rt.hs_not_five
    hk := d.hk
    hs_lt := d.hs_lt
    hfail_t1 := hfail_t1
    hfail_t2 := hfail_t2
  }

/-- Correct non-wrapping assembly from the cyclic local block.  The
local hident has depth `L`; only its head is translated to the global
prefix `b+L`.  The previous terminal remains the terminal constructed
at the cyclic boundary `b-1`. -/
theorem cyclic_local_block_to_failure_window_nonwrap
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b L t delta : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hL : 1 <= L) (hhead_lt : b + L < P)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2)
    (ht_last : t =
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 \/ t = 2)
    (hdelta : (t = 1 -> delta = 1) /\
      (t = 2 -> delta = 1 \/ delta = 3))
    (hterm : StringFlow.CycleBridge.IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) delta rt)
    (hk : rt.k + 1 <= L)
    (hslt : rt.s < 5 ^ (L - rt.k - 1))
    (hfail_t1 : t = 1 -> 2 * L + 12 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ L - 2))
    (hfail_t2 : t = 2 -> 2 * L + 11 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + delta * 5 ^ L)) :
    CyclicLocalFailureWindow m S P w rise c3 b L t delta rt := by
  have hhead_le : b + L <= w.length := by
    rw [h.hlength]
    exact Nat.le_of_lt hhead_lt
  have hLle : L <= w.length := by omega
  have hhead_eq :=
    StringFlow.CycleBridge.cyclic_local_head_eq_global_nonwrap
      (m := m) b L hhead_le
  have hglobal_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) :=
    StringFlow.CycleBridge.cycleQb8Input_prefix_full_reachable
      h (b + L) hhead_le
  have hglobal_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit (w.take (b + L)) m) :=
    S6Audit.FullOrbitFrom7_odd _ hglobal_reach
  have hlocal_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) := by
    rw [hhead_eq]
    exact hglobal_reach
  have hlocal_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) := by
    rw [hhead_eq]
    exact hglobal_odd
  rcases StringFlow.CycleBridge.cycleQb8Input_cyclic_local_hident_block
      h b L t delta hb hL hLle rt ht_last ht hdelta hterm hk hslt
      hlocal_odd hlocal_reach with
    ⟨q, Aj, Wp, Wj, d⟩
  have hnonwrap : b + (L - 1) < w.length := by
    rw [h.hlength]
    omega
  have hentry := StringFlow.CycleBridge.cyclicSegmentAt_getI_nonwrap
    w b (L - 1) hnonwrap
  have hincoming : w.getI (b + L - 1) = t := by
    calc
      w.getI (b + L - 1) = w.getI (b + (L - 1)) := by
        congr 1
        omega
      _ = (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1) :=
        hentry.symm
      _ = t := ht_last.symm
  have hfw := local_hident_to_localDepthFailureWindow
    h (by omega) hhead_lt hhead_eq hincoming d hfail_t1 hfail_t2
  exact {
    hboundary := hb
    hterminal := hrt
    hwindow := hfw
  }

/-- Wrap-aware assembly of the fully cyclic failure window.  The local
block data, reset equation, reachability witness, and failure thresholds
all use depth `L`; `b` appears only in the rotated word and in the exact
source of `rt`. -/
theorem cyclic_local_block_to_cyclicDepthFailureWindow
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b L t delta : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hL : 1 <= L) (hLle : L <= w.length)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2)
    (ht_last : t =
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 \/ t = 2)
    (hdelta : (t = 1 -> delta = 1) /\
      (t = 2 -> delta = 1 \/ delta = 3))
    (hterm : StringFlow.CycleBridge.IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) delta rt)
    (hk : rt.k + 1 <= L)
    (hslt : rt.s < 5 ^ (L - rt.k - 1))
    (hfail_t1 : t = 1 -> 2 * L + 12 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ L - 2))
    (hfail_t2 : t = 2 -> 2 * L + 11 <=
      twoValuation (5 ^ (rt.k + 1) * rt.s + delta * 5 ^ L)) :
    CyclicDepthFailureWindow m S P w rise c3 b L t delta rt := by
  have hble : b <= w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  rcases h.hstart with ⟨n0, hstart⟩
  have hlocal_state := cycleQb8Input_cyclic_prefix_fullOrbitIter_of_start
    h n0 hstart b hble L hLle
  have hlocal_reach : S6Audit.FullOrbitFrom7
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) :=
    ⟨(n0 + b) + L, hlocal_state⟩
  have hlocal_odd : S6Audit.IsOdd
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) :=
    S6Audit.FullOrbitFrom7_odd _ hlocal_reach
  rcases StringFlow.CycleBridge.cycleQb8Input_cyclic_local_hident_block
      h b L t delta hb hL hLle rt ht_last ht hdelta hterm hk hslt
      hlocal_odd hlocal_reach with
    ⟨q, Aj, Wp, Wj, d⟩
  rcases StringFlow.CycleBridge.local_hident_to_reset_reachability d with
    ⟨hreset, hreach⟩
  exact {
    hinput := h
    hboundary := hb
    hj_pos := hL
    hj_le := hLle
    hterminal := hrt
    ht := ht
    hincoming := ht_last.symm
    hdelta := hdelta
    hreset := hreset
    hreach := hreach
    hk := hk
    hs_lt := hslt
    hfail_t1 := hfail_t1
    hfail_t2 := hfail_t2
  }

/-- The corrected two-coordinate window aligns its reset predecessor
with the actual full-orbit predecessor at the global word prefix `g`,
while the reset formula retains the local exponent `j`. -/
theorem localDepthFailureWindow_real_predecessor_alignment
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take g) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (g - 1)) m /\
      orbitStepWeight (n - 1) = t /\
      5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 =
        fullOrbitIter (n - 1) := by
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hgl : g <= w.length := by
    rw [fw.hinput.hlength]
    exact Nat.le_of_lt fw.hg_lt
  rcases cycleQb8Input_prefix_occurrence_with_incoming
      fw.hinput g fw.hg_pos hgl with
    ⟨n, hn, hiter, hprev, hwWord⟩
  have hw : orbitStepWeight (n - 1) = t := by
    rw [hwWord, fw.hincoming]
  have hpred := reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    n j k0 t delta s 0 (StringFlow.Word.wordOrbit (w.take g) m)
    hj fw.hreset hn hiter hw
  exact ⟨n, hn, hiter, hprev, hw, hpred⟩

/-- Exact predecessor alignment for the fully cyclic window.  The
concrete orbit states are rotated local prefixes, while the reset
predecessor keeps the same local exponent `j`. -/
theorem cyclicDepthFailureWindow_real_predecessor_alignment
    {m S P : Nat} {w rise c3 : List Nat}
    {b j t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (fw : CyclicDepthFailureWindow
      m S P w rise c3 b j t delta rt) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m) /\
      fullOrbitIter (n - 1) = StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take (j - 1))
        (StringFlow.Word.wordOrbit (w.take b) m) /\
      orbitStepWeight (n - 1) = t /\
      5 ^ rt.k * rt.s + delta * 5 ^ (j - 1) - 1 =
        fullOrbitIter (n - 1) := by
  have hble : b <= w.length := by
    rcases fw.hboundary.2.1 with hlast | hrange
    · omega
    · omega
  rcases cycleQb8Input_cyclic_prefix_occurrence_with_incoming
      fw.hinput b j hble fw.hj_pos fw.hj_le with
    ⟨n, hn, hiter, hprev, hwWord⟩
  have hw : orbitStepWeight (n - 1) = t := by
    rw [hwWord, fw.hincoming]
  have hpred := reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    n j rt.k t delta rt.s 0
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m))
    fw.hj_pos fw.hreset hn hiter hw
  exact ⟨n, hn, hiter, hprev, hw, hpred⟩

/-- A genuine failure window retains the exact incoming cycle-word
entry, so its reset predecessor is the actual full-orbit predecessor.
This is the interface that was lost when only `t` and reachability were
stored independently. -/
theorem failureWindow_real_predecessor_alignment
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (j - 1)) m /\
      orbitStepWeight (n - 1) = t /\
      5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 =
        fullOrbitIter (n - 1) := by
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hjl : j <= w.length := by
    rw [fw.hinput.hlength]
    exact Nat.le_of_lt fw.hj_lt
  rcases cycleQb8Input_prefix_occurrence_with_incoming
      fw.hinput j hj hjl with ⟨n, hn, hiter, hprev, hwWord⟩
  have hw : orbitStepWeight (n - 1) = t := by
    rw [hwWord, fw.hincoming]
  have hpred := reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    n j k0 t delta s 0 (StringFlow.Word.wordOrbit (w.take j) m)
    hj fw.hreset hn hiter hw
  exact ⟨n, hn, hiter, hprev, hw, hpred⟩

/-- In the `t=1` failure branch the actual predecessor has rank one.
The formal rank-two alternative would force incoming weight at least
five and is therefore excluded by the retained word entry. -/
theorem failureWindow_t1_predecessor_rank_one
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 1) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (j - 1)) m /\
      orbitStepWeight (n - 1) = 1 /\
      twoValuation (fullOrbitIter (n - 1) + 1) = 1 /\
      5 ^ k0 * s + 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1) := by
  have hdelta : delta = 1 := fw.hδ.1 ht
  subst t
  subst delta
  rcases failureWindow_real_predecessor_alignment fw with
    ⟨n, hn, hiter, hprev, hw, hpred⟩
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hcases := reset_t1_incoming_weight_exact_of_j_pos
    n j k0 s (StringFlow.Word.wordOrbit (w.take j) m)
    hj fw.hreset hn hiter
  rcases hcases with hsmall | hlarge
  · exact ⟨n, hn, hiter, hprev, hw, hsmall.1, by simpa using hpred⟩
  · have hweight := orbitStepWeight_of_rank_two (n - 1) hlarge.1
    have hvge : 3 <= twoValuation
        (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) := by
      omega
    omega

/-- For a positive input, `5*oddPart(a)-1` is positive and even. -/
lemma twoValuation_five_oddPart_sub_one_ge_one
    (a : Nat) (ha : 0 < a) :
    1 <= twoValuation (5 * StringFlow.oddPart a - 1) := by
  let c := StringFlow.oddPart a
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a ha
  have hcpos : 0 < c := by
    by_contra hnot
    have hc0 : c = 0 := by omega
    rw [hc0] at hcodd
    norm_num at hcodd
  have hzpos : 0 < 5 * c - 1 := by omega
  have hcdec : c = 2 * (c / 2) + 1 := by
    have h := (Nat.div_add_mod c 2).symm
    rw [hcodd] at h
    omega
  have heven : (5 * c - 1) % 2 = 0 := by
    rw [hcdec]
    omega
  have hdvd : 2 ^ 1 ∣ 5 * c - 1 := by
    simpa using Nat.dvd_of_mod_eq_zero heven
  exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
    (5 * c - 1) 1 hzpos).mpr hdvd

/-- An odd state whose outgoing exact `5x+1` weight is at least three
has rank exactly two.  This is the local C3/head-rank identity. -/
lemma state_rank_eq_two_of_outgoing_c3
    (x : Nat) (hodd : IsOdd x)
    (hc3 : 3 <= twoValuation (5 * x + 1)) :
    twoValuation (x + 1) = 2 := by
  have hnumpos : 0 < 5 * x + 1 := by positivity
  have hdvd8 : 2 ^ 3 ∣ 5 * x + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 * x + 1) 3 hnumpos).mp hc3
  have hmod8 : (5 * x + 1) % 8 = 0 := by
    simpa using Nat.dvd_iff_mod_eq_zero.mp hdvd8
  have hxmod : x % 8 = 3 := by
    have hxlt : x % 8 < 8 := Nat.mod_lt x (by norm_num)
    rw [Nat.add_mod, Nat.mul_mod] at hmod8
    norm_num at hmod8
    interval_cases hx : x % 8 <;> omega
  have hx1mod8 : (x + 1) % 8 = 4 := by
    rw [Nat.add_mod, hxmod]
  have hdvd4 : 2 ^ 2 ∣ x + 1 := by
    have hmod4 : (x + 1) % 4 = 0 := by
      have hmodmod := Nat.mod_mod_of_dvd (x + 1) (by norm_num : 4 ∣ 8)
      rw [hx1mod8] at hmodmod
      simpa using hmodmod.symm
    simpa using Nat.dvd_iff_mod_eq_zero.mpr hmod4
  have hge2 : 2 <= twoValuation (x + 1) :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (x + 1) 2 (by positivity)).mpr hdvd4
  by_contra hne
  have hge3 : 3 <= twoValuation (x + 1) := by omega
  have hdvd8' : 2 ^ 3 ∣ x + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (x + 1) 3 (by positivity)).mp hge3
  have hzero8 : (x + 1) % 8 = 0 := by
    simpa using Nat.dvd_iff_mod_eq_zero.mp hdvd8'
  omega

/-- A single C3 step has the generalized reset form
`2^(t-2) * (rj+1) = 5^(k+1)*s + 2^(t-2) - 1` when the input head
satisfies `x+1 = 4 * 5^k * s`. -/
theorem c3_step_reset_identity
    (x k s t rj : Nat)
    (hx : x + 1 = 4 * 5 ^ k * s)
    (ht : 3 <= t)
    (hstep : 2 ^ t * rj = 5 * x + 1) :
    2 ^ (t - 2) * (rj + 1) =
      5 ^ (k + 1) * s + 2 ^ (t - 2) - 1 := by
  have hspos : 0 < s := by
    have hxpos : 0 < x + 1 := by positivity
    rw [hx] at hxpos
    exact Nat.pos_of_ne_zero (by
      intro hs0
      rw [hs0, Nat.mul_zero] at hxpos
      omega)
  have hxeq : x = 4 * 5 ^ k * s - 1 := by omega
  have hB0pos : 0 < 4 * 5 ^ k * s := by positivity
  have h5base : 5 * (5 ^ k * s) = 5 ^ (k + 1) * s := by
    rw [Nat.pow_succ]
    ring
  have h5x : 5 * x + 1 = 4 * (5 ^ (k + 1) * s - 1) := by
    calc
      5 * x + 1 = 5 * (4 * 5 ^ k * s - 1) + 1 := by rw [hxeq]
      _ = 5 * (4 * 5 ^ k * s) - 4 := by omega
      _ = 4 * (5 * (5 ^ k * s)) - 4 := by ring
      _ = 4 * (5 ^ (k + 1) * s) - 4 := by rw [h5base]
      _ = 4 * (5 ^ (k + 1) * s - 1) := by omega
  have hpow : 2 ^ t = 4 * 2 ^ (t - 2) := by
    have ht_decomp : t = 2 + (t - 2) := by omega
    rw [ht_decomp, Nat.pow_add]
    norm_num
  have hstep4 : 4 * (2 ^ (t - 2) * rj) = 4 * (5 ^ (k + 1) * s - 1) := by
    calc
      4 * (2 ^ (t - 2) * rj) = (4 * 2 ^ (t - 2)) * rj := by ring
      _ = 2 ^ t * rj := by rw [hpow]
      _ = 5 * x + 1 := hstep
      _ = 4 * (5 ^ (k + 1) * s - 1) := h5x
  have hcancel : 2 ^ (t - 2) * rj = 5 ^ (k + 1) * s - 1 := by
    exact Nat.mul_left_cancel (by norm_num : 0 < 4) hstep4
  have hrewrite : 5 ^ (k + 1) * s - 1 + 2 ^ (t - 2) =
      5 ^ (k + 1) * s + 2 ^ (t - 2) - 1 := by
    have hBge1 : 1 <= 5 ^ (k + 1) * s := by omega
    omega
  calc
    2 ^ (t - 2) * (rj + 1)
        = 2 ^ (t - 2) * rj + 2 ^ (t - 2) := by ring
    _ = (5 ^ (k + 1) * s - 1) + 2 ^ (t - 2) := by rw [hcancel]
    _ = 5 ^ (k + 1) * s + 2 ^ (t - 2) - 1 := hrewrite

/-- A real C3 step from a reachable head satisfying the `4 * 5^k * s0`
form supplies the C3-tail reset window with the same head parameter. -/
theorem c3_step_reset_window_reachability
    (x k0 s0 t rj j : Nat)
    (hx : x + 1 = 4 * 5 ^ k0 * s0)
    (hodd : IsOdd s0) (hnd5 : ¬ 5 ∣ s0)
    (hk : k0 + 1 ≤ j) (hslt : s0 < 5 ^ (j - 1 - k0))
    (hxFull : FullOrbitFrom7 x)
    (ht : 3 ≤ t) (hstep : 2 ^ t * rj = 5 * x + 1)
    (hrj_full : rj = fullOrbitStep x) :
    ResetWindowReachabilityC3 j k0 t s0 := by
  refine ⟨x, rj, hk, hx, hodd, hnd5, hslt, hxFull, ?_, ?_, ?_⟩
  · exact ⟨ht, c3_step_reset_identity x k0 s0 t rj hx ht hstep⟩
  · rw [hrj_full]
    exact FullOrbitFrom7_odd (fullOrbitStep x) (by
      rcases hxFull with ⟨n, hn⟩
      exact ⟨n + 1, by simpa [fullOrbitIter, fullOrbitStep, hn]⟩)
  · rw [hrj_full]
    rcases hxFull with ⟨n, hn⟩
    exact ⟨n + 1, by simpa [fullOrbitIter, fullOrbitStep, hn]⟩
/-- If a failure-window endpoint is also known to be the head of the
next C3 chain, its rank is exactly two. -/

theorem failureWindow_rank_two_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hout : 3 <= w.getI j) :
    twoValuation
      (StringFlow.Word.wordOrbit (w.take j) m + 1) = 2 := by
  have hjltw : j < w.length := by
    rw [fw.hinput.hlength]
    exact fw.hj_lt
  have hjle : j <= w.length := Nat.le_of_lt hjltw
  have hreach := StringFlow.CycleBridge.cycleQb8Input_prefix_full_reachable
    fw.hinput j hjle
  have hodd : IsOdd (StringFlow.Word.wordOrbit (w.take j) m) :=
    FullOrbitFrom7_odd _ hreach
  have hexact := fw.hinput.hexact j hjltw
  apply state_rank_eq_two_of_outgoing_c3
    (StringFlow.Word.wordOrbit (w.take j) m) hodd
  rw [hexact]
  exact hout

/-- Hence an actual maximal-rise endpoint (whose next word entry is
C3) can never satisfy either failure lower bound.  This pinpoints the
separate selection issue: producing a `FailureWindow` at such an
endpoint is itself the contradiction, not a source of a new rank
estimate. -/
theorem failureWindow_false_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hout : 3 <= w.getI j) : False := by
  have hrank := failureWindow_rank_two_of_outgoing_c3 fw hout
  rcases fw.ht with ht1 | ht2
  · have hfail0 := fw.hfail_t1 ht1
    have hdelta : delta = 1 := fw.hδ.1 ht1
    subst t
    subst delta
    have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
      simpa [BlockAutomaton.t1WindowValue] using hfail0
    have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
      j k0 s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
    rw [hwindow, hrank] at hfail
    omega
  · have hfail0 := fw.hfail_t2 ht2
    subst t
    have hfail : 2 * j + 11 <=
        BlockAutomaton.t2WindowValue j k0 delta s := by
      simpa [BlockAutomaton.t2WindowValue] using hfail0
    have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
      j k0 delta s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
    rw [hwindow, hrank] at hfail
    omega

/-- Therefore a failure window cannot be the endpoint of the actual
non-wrapping maximal rise run selected by `cycleQb8Input_exists_c3_rise_run`.
The maximality stop is converted to the genuine global outgoing C3
entry before applying the exact rank-two contradiction. -/
theorem failureWindow_false_of_maximal_rise_endpoint_nonwrap
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s b L : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hdepth : j = b + L)
    (hstop : L = w.length \/
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI L) : False := by
  have hbL : b + L < P := by
    rw [← hdepth]
    exact fw.hj_lt
  have hout :=
    StringFlow.CycleBridge.maximal_cyclic_rise_run_outgoing_c3_nonwrap
      fw.hinput.hlength hbL hstop
  apply failureWindow_false_of_outgoing_c3 fw
  rw [hdepth]
  exact hout

/-- In the `t=2` failure branch the actual predecessor has rank at
least three, and the reset predecessor is again the genuine full-orbit
predecessor.  Rank two would add a positive extra valuation to the
incoming weight, contradicting the exact word weight `2`. -/
theorem failureWindow_t2_predecessor_rank_ge_three
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 2) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (j - 1)) m /\
      orbitStepWeight (n - 1) = 2 /\
      3 <= twoValuation (fullOrbitIter (n - 1) + 1) /\
      5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 =
        fullOrbitIter (n - 1) := by
  subst t
  rcases failureWindow_real_predecessor_alignment fw with
    ⟨n, hn, hiter, hprev, hw, hpred⟩
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hcases := reset_t2_incoming_weight_exact_of_j_pos
    n j k0 s (StringFlow.Word.wordOrbit (w.take j) m) delta
    hj fw.hreset hn hiter
  rcases hcases with hlarge | heq
  · exact ⟨n, hn, hiter, hprev, hw, hlarge.1, hpred⟩
  · have hweight := orbitStepWeight_of_rank_two (n - 1) heq.1
    have hvpos := twoValuation_five_oddPart_sub_one_ge_one
      (fullOrbitIter (n - 1) + 1) (by positivity)
    omega

/-- The `t=1` failure inequality is exactly a spike in the rank-one
predecessor transition.  All reset parameters disappear from the final
valuation. -/
theorem failureWindow_t1_forces_real_predecessor_spike
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 1) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      twoValuation (fullOrbitIter (n - 1) + 1) = 1 /\
      2 * j + 11 <= twoValuation
        (5 * StringFlow.oddPart
          (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) - 1) := by
  have hdelta : delta = 1 := fw.hδ.1 ht
  rcases failureWindow_t1_predecessor_rank_one fw ht with
    ⟨n, hn, hiter, hprev, _hw, hrank1, _hpred⟩
  have hfail0 := fw.hfail_t1 ht
  subst t
  subst delta
  have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
    simpa [BlockAutomaton.t1WindowValue] using hfail0
  have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
    j k0 s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
  rw [hwindow] at hfail
  have hstep := fullOrbitIter_rank_one_step (n - 1) hrank1
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx, hiter] at hstep
  refine ⟨n, hn, hiter, hrank1, ?_⟩
  rw [← hprev]
  rw [← hstep]
  omega

/-- The `t=2` failure inequality is exactly an excessive rank of the
real predecessor.  The normal rank-drop theorem removes the reset
expression and the block head. -/
theorem failureWindow_t2_forces_real_predecessor_rank
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 2) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take j) m /\
      2 * j + 11 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) := by
  rcases failureWindow_t2_predecessor_rank_ge_three fw ht with
    ⟨n, hn, hiter, hprev, _hw, hrank3, _hpred⟩
  have hfail0 := fw.hfail_t2 ht
  subst t
  have hfail : 2 * j + 11 <= BlockAutomaton.t2WindowValue j k0 delta s := by
    simpa [BlockAutomaton.t2WindowValue] using hfail0
  have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
    j k0 delta s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
  rw [hwindow] at hfail
  have hdrop := fullOrbitIter_rank_drop_two (n - 1) hrank3
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx, hiter] at hdrop
  refine ⟨n, hn, hiter, ?_⟩
  rw [← hprev]
  omega

/-- In a two-coordinate `t=1` window the actual predecessor has rank
one.  The local reset depth is `j`, while both concrete orbit states
are indexed by the global prefix `g`. -/
theorem localDepthFailureWindow_t1_predecessor_rank_one
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (ht : t = 1) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take g) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (g - 1)) m /\
      orbitStepWeight (n - 1) = 1 /\
      twoValuation (fullOrbitIter (n - 1) + 1) = 1 /\
      5 ^ k0 * s + 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1) := by
  have hdelta : delta = 1 := fw.hdelta.1 ht
  subst t
  subst delta
  rcases localDepthFailureWindow_real_predecessor_alignment fw with
    ⟨n, hn, hiter, hprev, hw, hpred⟩
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hcases := reset_t1_incoming_weight_exact_of_j_pos
    n j k0 s (StringFlow.Word.wordOrbit (w.take g) m)
    hj fw.hreset hn hiter
  rcases hcases with hsmall | hlarge
  · exact ⟨n, hn, hiter, hprev, hw, hsmall.1, by simpa using hpred⟩
  · have hweight := orbitStepWeight_of_rank_two (n - 1) hlarge.1
    have hvge : 3 <= twoValuation
        (5 * StringFlow.oddPart (fullOrbitIter (n - 1) + 1) - 1) := by
      omega
    omega

/-- In a two-coordinate `t=2` window the actual predecessor has rank
at least three.  Again the valuation theorem uses local depth `j`, and
the occurrence theorem uses global prefix `g`. -/
theorem localDepthFailureWindow_t2_predecessor_rank_ge_three
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (ht : t = 2) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take g) m /\
      fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit (w.take (g - 1)) m /\
      orbitStepWeight (n - 1) = 2 /\
      3 <= twoValuation (fullOrbitIter (n - 1) + 1) /\
      5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 =
        fullOrbitIter (n - 1) := by
  subst t
  rcases localDepthFailureWindow_real_predecessor_alignment fw with
    ⟨n, hn, hiter, hprev, hw, hpred⟩
  have hj : 1 <= j := by
    have hk := fw.hk
    omega
  have hcases := reset_t2_incoming_weight_exact_of_j_pos
    n j k0 s (StringFlow.Word.wordOrbit (w.take g) m) delta
    hj fw.hreset hn hiter
  rcases hcases with hlarge | heq
  · exact ⟨n, hn, hiter, hprev, hw, hlarge.1, hpred⟩
  · have hweight := orbitStepWeight_of_rank_two (n - 1) heq.1
    have hvpos := twoValuation_five_oddPart_sub_one_ge_one
      (fullOrbitIter (n - 1) + 1) (by positivity)
    omega

/-- The local-depth `t=1` failure is an exact spike at the real
predecessor of global prefix `g`; all reset parameters are eliminated. -/
theorem localDepthFailureWindow_t1_forces_real_predecessor_spike
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (ht : t = 1) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take g) m /\
      twoValuation (fullOrbitIter (n - 1) + 1) = 1 /\
      2 * j + 11 <= twoValuation
        (5 * StringFlow.oddPart
          (StringFlow.Word.wordOrbit (w.take (g - 1)) m + 1) - 1) := by
  have hdelta : delta = 1 := fw.hdelta.1 ht
  rcases localDepthFailureWindow_t1_predecessor_rank_one fw ht with
    ⟨n, hn, hiter, hprev, _hw, hrank1, _hpred⟩
  have hfail0 := fw.hfail_t1 ht
  subst t
  subst delta
  have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
    simpa [BlockAutomaton.t1WindowValue] using hfail0
  have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
    j k0 s (StringFlow.Word.wordOrbit (w.take g) m) fw.hreset
  rw [hwindow] at hfail
  have hstep := fullOrbitIter_rank_one_step (n - 1) hrank1
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx, hiter] at hstep
  refine ⟨n, hn, hiter, hrank1, ?_⟩
  rw [← hprev]
  rw [← hstep]
  omega

/-- The local-depth `t=2` failure is exactly a lower bound on the
rank of the real predecessor of global prefix `g`. -/
theorem localDepthFailureWindow_t2_forces_real_predecessor_rank
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (ht : t = 2) :
    exists n : Nat, 1 <= n /\
      fullOrbitIter n = StringFlow.Word.wordOrbit (w.take g) m /\
      2 * j + 11 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take (g - 1)) m + 1) := by
  rcases localDepthFailureWindow_t2_predecessor_rank_ge_three fw ht with
    ⟨n, hn, hiter, hprev, _hw, hrank3, _hpred⟩
  have hfail0 := fw.hfail_t2 ht
  subst t
  have hfail : 2 * j + 11 <= BlockAutomaton.t2WindowValue j k0 delta s := by
    simpa [BlockAutomaton.t2WindowValue] using hfail0
  have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
    j k0 delta s (StringFlow.Word.wordOrbit (w.take g) m) fw.hreset
  rw [hwindow] at hfail
  have hdrop := fullOrbitIter_rank_drop_two (n - 1) hrank3
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx, hiter] at hdrop
  refine ⟨n, hn, hiter, ?_⟩
  rw [← hprev]
  omega

/-- A C3 edge leaving the global head `g` fixes the head rank at two;
the proof uses no identification between `g` and local depth `j`. -/
theorem localDepthFailureWindow_rank_two_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (hout : 3 <= w.getI g) :
    twoValuation
      (StringFlow.Word.wordOrbit (w.take g) m + 1) = 2 := by
  have hgltw : g < w.length := by
    rw [fw.hinput.hlength]
    exact fw.hg_lt
  have hgle : g <= w.length := Nat.le_of_lt hgltw
  have hreach := StringFlow.CycleBridge.cycleQb8Input_prefix_full_reachable
    fw.hinput g hgle
  have hodd : IsOdd (StringFlow.Word.wordOrbit (w.take g) m) :=
    FullOrbitFrom7_odd _ hreach
  have hexact := fw.hinput.hexact g hgltw
  apply state_rank_eq_two_of_outgoing_c3
    (StringFlow.Word.wordOrbit (w.take g) m) hodd
  rw [hexact]
  exact hout

/-- Hence a correctly coordinated failure window cannot end immediately
before a C3 edge.  The lower threshold uses local depth `j`, while the
rank-two identity is at global prefix `g`. -/
theorem localDepthFailureWindow_false_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {g j k0 t delta s : Nat}
    (fw : LocalDepthFailureWindow
      m S P w rise c3 g j k0 t delta s)
    (hout : 3 <= w.getI g) : False := by
  have hrank := localDepthFailureWindow_rank_two_of_outgoing_c3 fw hout
  rcases fw.ht with ht1 | ht2
  · have hdelta : delta = 1 := fw.hdelta.1 ht1
    have hfail0 := fw.hfail_t1 ht1
    subst t
    subst delta
    have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
      simpa [BlockAutomaton.t1WindowValue] using hfail0
    have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
      j k0 s (StringFlow.Word.wordOrbit (w.take g) m) fw.hreset
    rw [hwindow, hrank] at hfail
    omega
  · have hfail0 := fw.hfail_t2 ht2
    subst t
    have hfail : 2 * j + 11 <=
        BlockAutomaton.t2WindowValue j k0 delta s := by
      simpa [BlockAutomaton.t2WindowValue] using hfail0
    have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
      j k0 delta s (StringFlow.Word.wordOrbit (w.take g) m) fw.hreset
    rw [hwindow, hrank] at hfail
    omega

/-- At a non-wrapping maximal cyclic rise endpoint, the stop condition
is the actual outgoing C3 edge, so a fully sourced cyclic failure
window is impossible. -/
theorem cyclicLocalFailureWindow_false_of_maximal_endpoint_nonwrap
    {m S P : Nat} {w rise c3 : List Nat}
    {b j t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (fw : CyclicLocalFailureWindow
      m S P w rise c3 b j t delta rt)
    (hstop : j = w.length \/
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j) : False := by
  have hout :=
    StringFlow.CycleBridge.maximal_cyclic_rise_run_outgoing_c3_nonwrap
      fw.hwindow.hinput.hlength fw.hwindow.hg_lt hstop
  exact localDepthFailureWindow_false_of_outgoing_c3 fw.hwindow hout

/-- A cyclic rise run selected after a genuine C3 boundary cannot fill
the whole period: its last local entry would simultaneously be a rise
entry and the boundary C3 entry. -/
theorem cycleQb8Input_cyclic_rise_run_length_lt
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b L : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hLpos : 1 <= L) (hLle : L <= w.length)
    (hall : forall k : Nat, k < L ->
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2) :
    L < w.length := by
  have hlenpos : 0 < w.length := hb.1
  have hble : b <= w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hbpos : 1 <= b := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · exact hrange.1
  by_contra hnot
  have hLeq : L = w.length := by omega
  let k := w.length - 1
  have hklt : k < L := by
    dsimp [k]
    omega
  have hrise := hall k hklt
  have hkword : k < w.length := by
    dsimp [k]
    omega
  have hentry := StringFlow.CycleBridge.cyclicSegmentAt_getI_mod
    w b k hble hkword
  have hmod : (b + k) % w.length = b - 1 := by
    have hsum : b + k = w.length + (b - 1) := by
      dsimp [k]
      omega
    have hrem : b - 1 < w.length := by omega
    simp [hsum, Nat.mod_eq_of_lt hrem]
  have hc3local :
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k := by
    rw [hentry, hmod]
    exact hb.2.2.1
  rcases hrise with h1 | h2
  · omega
  · omega

/-- Wrap-aware rank-two identity for any cyclic prefix followed by a
C3 entry.  It depends only on the exact cycle word, not on a failure
window or reset parameters. -/
theorem cycleQb8Input_cyclic_head_rank_two_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b j : Nat) (hble : b <= w.length)
    (hjle : j <= w.length) (hjlt : j < w.length)
    (hout : 3 <=
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j) :
    twoValuation
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m) + 1) = 2 := by
  rcases h.hstart with ⟨n0, hstart⟩
  have hstate := cycleQb8Input_cyclic_prefix_fullOrbitIter_of_start
    h n0 hstart b hble j hjle
  have hweight := cycleQb8Input_cyclic_orbitStepWeight_of_start
    h n0 hstart b hble j hjlt
  unfold orbitStepWeight at hweight
  rw [hstate] at hweight
  have hweight' : twoValuation
      (5 * StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m) + 1) =
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j := by
    simpa using hweight
  have hodd : IsOdd
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m)) := by
    rw [← hstate]
    exact fullOrbitIter_odd ((n0 + b) + j)
  apply state_rank_eq_two_of_outgoing_c3
    (StringFlow.Word.wordOrbit
      ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
      (StringFlow.Word.wordOrbit (w.take b) m)) hodd
  rw [hweight']
  exact hout

/-- Exact relation between the one-division real terminal at a cyclic
C3-to-rise boundary and the following fully accelerated rise-start
state.  The remaining `c-1` divisions are retained as a power of two. -/
theorem cycleQb8Input_boundary_terminal_eq
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2) :
    rt.r = 2 ^ (w.getI (b - 1) - 1) *
      StringFlow.Word.wordOrbit (w.take b) m := by
  have hbpos : 1 <= b := by
    have hlenpos := hb.1
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hble : b <= w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  rcases cycleQb8Input_prefix_occurrence_with_incoming
      h b hbpos hble with
    ⟨n, hn, hiter, hprev, hw⟩
  have hmul := fullOrbit_predecessor_mul n
    (StringFlow.Word.wordOrbit (w.take b) m) hn hiter
  rw [hw, hprev] at hmul
  have hc3 : 3 <= w.getI (b - 1) := hb.2.2.1
  let x := StringFlow.Word.wordOrbit (w.take (b - 1)) m
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hxodd : x % 2 = 1 := by
    dsimp [x]
    have hreach := StringFlow.CycleBridge.cycleQb8Input_prefix_full_reachable
      h (b - 1) (by omega)
    exact S6Audit.FullOrbitFrom7_odd _ hreach
  have heven : (5 * x + 1) % 2 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [hxodd]
  have hdvd2 : 2 ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr heven
  have h2rt : 2 * rt.r = 5 * x + 1 := by
    rw [hrt]
    dsimp [x]
    exact Nat.mul_div_cancel' hdvd2
  have hmul' : 2 ^ w.getI (b - 1) * q = 5 * x + 1 := by
    simpa [x, q] using hmul
  have hpoweq : 2 ^ w.getI (b - 1) =
      2 * 2 ^ (w.getI (b - 1) - 1) := by
    have hcpos : 1 <= w.getI (b - 1) := by omega
    have hc : w.getI (b - 1) = (w.getI (b - 1) - 1) + 1 := by omega
    conv_lhs => rw [hc, Nat.pow_succ]
    ring
  have hcancel : 2 * rt.r =
      2 * (2 ^ (w.getI (b - 1) - 1) * q) := by
    rw [h2rt, ← hmul', hpoweq]
    ring
  have heq : rt.r = 2 ^ (w.getI (b - 1) - 1) * q := by
    omega
  simpa [q] using heq

/-- Since a boundary C3 weight is at least three, its one-division
terminal is at least four times the following rise-start state. -/
theorem cycleQb8Input_boundary_terminal_four_head_le
    {m S P : Nat} {w rise c3 : List Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2) :
    4 * StringFlow.Word.wordOrbit (w.take b) m <= rt.r := by
  have heq := cycleQb8Input_boundary_terminal_eq h b hb rt hrt
  have hc3 : 3 <= w.getI (b - 1) := hb.2.2.1
  have hpow : 4 <= 2 ^ (w.getI (b - 1) - 1) := by
    have he : 2 <= w.getI (b - 1) - 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) he
    norm_num at hp ⊢
    exact hp
  rw [heq]
  exact Nat.mul_le_mul_right _ hpow

/-- A genuine boundary terminal cannot reset to the endpoint of a
cyclic rise suffix of length one or two.  Exact incoming-edge alignment
identifies the reset predecessor with the real prefix state; the C3
boundary terminal is already at least `4*q`, whereas zero or one rise
step leaves that predecessor strictly below `4*q`. -/
theorem cyclic_local_reset_length_ge_three
    {m S P : Nat} {w rise c3 : List Nat}
    {L t delta : Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hLpos : 1 <= L) (hLle : L <= w.length)
    (hall : forall k : Nat, k < L ->
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (hrt : rt.r =
      (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2)
    (ht_last : t =
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1))
    (ht : t = 1 \/ t = 2)
    (hdelta : (t = 1 -> delta = 1) /\
      (t = 2 -> delta = 1 \/ delta = 3))
    (hterm : StringFlow.CycleBridge.IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) delta rt) :
    3 <= L := by
  have hble : b <= w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hreset : S6Audit.ResetHeadEq rt.s L rt.k t delta
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) :=
    (StringFlow.CycleBridge.isLocalResetTerminal_iff_resetHeadEq
      t L
        (StringFlow.Word.wordOrbit
          ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
          (StringFlow.Word.wordOrbit (w.take b) m))
        delta rt ht hdelta).mp hterm
  rcases cycleQb8Input_cyclic_prefix_occurrence_with_incoming
      h b L hble hLpos hLle with
    ⟨n, hn, hiter, hprev, hwWord⟩
  have hw : orbitStepWeight (n - 1) = t := by
    rw [hwWord, ← ht_last]
  have hpred := reset_predecessor_eq_fullOrbit_of_aligned_weight_of_j_pos
    n L rt.k t delta rt.s 0
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m))
      hLpos hreset hn hiter hw
  have hprod : 5 ^ rt.k * rt.s = rt.r + 1 := by
    simpa [Nat.mul_comm] using rt.hprod
  have hxprev : fullOrbitIter (n - 1) =
      rt.r + delta * 5 ^ (L - 1) := by
    omega
  let q := StringFlow.Word.wordOrbit (w.take b) m
  have hqpos : 0 < q := by
    have hreach := StringFlow.CycleBridge.cycleQb8Input_prefix_full_reachable
      h b hble
    have hodd : q % 2 = 1 := by
      dsimp [q]
      exact S6Audit.FullOrbitFrom7_odd _ hreach
    omega
  have hfour : 4 * q <= rt.r := by
    dsimp [q]
    exact cycleQb8Input_boundary_terminal_four_head_le h b hb rt hrt
  have hdeltapos : 0 < delta := by
    rcases ht with ht1 | ht2
    · have := hdelta.1 ht1
      omega
    · rcases hdelta.2 ht2 with hd1 | hd3 <;> omega
  by_contra hnot
  have hcases : L = 1 \/ L = 2 := by omega
  rcases hcases with hL1 | hL2
  · subst L
    have hprevq : fullOrbitIter (n - 1) = q := by
      simpa [q, StringFlow.Word.wordOrbit] using hprev
    rw [hprevq] at hxprev
    norm_num at hxprev
    nlinarith
  · subst L
    have honele : 1 <= w.length := by omega
    rcases cycleQb8Input_cyclic_prefix_occurrence_with_incoming
        h b 1 hble (by omega) honele with
      ⟨n1, hn1, hiter1, hprev1, hw1⟩
    have hmul1 := fullOrbit_predecessor_mul n1
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take 1) q)
      hn1 hiter1
    have hprevq : fullOrbitIter (n1 - 1) = q := by
      simpa [q, StringFlow.Word.wordOrbit] using hprev1
    rw [hw1, hprevq] at hmul1
    have ha := hall 0 (by omega)
    have hxprev1 : fullOrbitIter (n - 1) =
        StringFlow.Word.wordOrbit
          ((StringFlow.CycleBridge.cyclicSegmentAt w b).take 1) q := by
      simpa [q] using hprev
    rw [hxprev1] at hxprev
    rcases ha with ha1 | ha2
    · rw [ha1] at hmul1
      norm_num at hmul1 hxprev
      nlinarith
    · rw [ha2] at hmul1
      norm_num at hmul1 hxprev
      nlinarith

/-- The corrected window bounds at a maximal cyclic rise endpoint need
only the genuine local reset equation.  The quotient data
`q,Aj,Wp,Wj`, the size fields `hk,hs_lt`, and the PMI failure bounds do
not enter: the outgoing C3 edge fixes the real head rank at two, while
`IsLocalResetTerminal` is exactly the corresponding `ResetHeadEq`. -/
theorem cyclic_local_reset_window_bounds_at_maximal_endpoint
    {m S P : Nat} {w rise c3 : List Nat}
    {L t delta : Nat}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hLpos : 1 <= L) (hLle : L <= w.length)
    (hall : forall k : Nat, k < L ->
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2)
    (hstop : L = w.length \/
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI L)
    (rt : S6Audit.AngelinaGilbertaRealTerminal)
    (ht : t = 1 \/ t = 2)
    (hdelta : (t = 1 -> delta = 1) /\
      (t = 2 -> delta = 1 \/ delta = 3))
    (hterm : StringFlow.CycleBridge.IsLocalResetTerminal t L
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) delta rt) :
    (t = 1 -> BlockAutomaton.t1WindowValue L rt.k rt.s <=
      2 * L + 11) /\
    (t = 2 -> BlockAutomaton.t2WindowValue L rt.k delta rt.s <=
      2 * L + 10) := by
  have hble : b <= w.length := by
    rcases hb.2.1 with hlast | hrange
    · omega
    · omega
  have hLlt := cycleQb8Input_cyclic_rise_run_length_lt
    h b L hb hLpos hLle hall
  have hc3 : 3 <=
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI L := by
    rcases hstop with hfull | hc3
    · omega
    · exact hc3
  have hrank := cycleQb8Input_cyclic_head_rank_two_of_outgoing_c3
    h b L hble hLle hLlt hc3
  have hreset : S6Audit.ResetHeadEq rt.s L rt.k t delta
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) :=
    (StringFlow.CycleBridge.isLocalResetTerminal_iff_resetHeadEq
      t L
        (StringFlow.Word.wordOrbit
          ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
          (StringFlow.Word.wordOrbit (w.take b) m))
        delta rt ht hdelta).mp hterm
  constructor
  · intro ht1
    have hdelta1 : delta = 1 := hdelta.1 ht1
    subst t
    subst delta
    have hvalue := t1WindowValue_eq_twoValuation_rj_plus_one
      L rt.k rt.s
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) hreset
    rw [hvalue, hrank]
    omega
  · intro ht2
    subst t
    have hvalue := t2WindowValue_eq_twoValuation_rj_plus_one
      L rt.k delta rt.s
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
        (StringFlow.Word.wordOrbit (w.take b) m)) hreset
    rw [hvalue, hrank]
    omega

/-- Positive original window bounds at the actual maximal cyclic rise
endpoint.  The local hident depth is `L`; exact cyclic occurrence and
the stopping C3 edge give head rank two, after which the existing
`windowValue = t + v2(head+1)` identities close both branches. -/
theorem localHidentBlock_window_bounds_at_maximal_cyclic_endpoint
    {m S P : Nat} {w rise c3 : List Nat}
    {L t delta q Aj Wp Wj : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3)
    (b : Nat)
    (hb : StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b)
    (hLpos : 1 <= L) (hLle : L <= w.length)
    (hall : forall k : Nat, k < L ->
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2)
    (hstop : L = w.length \/
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI L)
    (d : StringFlow.CycleBridge.LocalHidentBlock
      L Wp Wj q Aj
        (StringFlow.Word.wordOrbit
          ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
          (StringFlow.Word.wordOrbit (w.take b) m))
        t delta rt) :
    (t = 1 -> BlockAutomaton.t1WindowValue L rt.k rt.s <=
      2 * L + 11) /\
    (t = 2 -> BlockAutomaton.t2WindowValue L rt.k delta rt.s <=
      2 * L + 10) := by
  exact cyclic_local_reset_window_bounds_at_maximal_endpoint
    h b hb hLpos hLle hall hstop rt d.ht d.hδ d.hterm

/-- The head of a fully cyclic window has rank two whenever the next
rotated word entry is C3.  This statement is wrap-invariant. -/
theorem cyclicDepthFailureWindow_rank_two_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {b j t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (fw : CyclicDepthFailureWindow
      m S P w rise c3 b j t delta rt)
    (hjlt : j < w.length)
    (hout : 3 <=
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j) :
    twoValuation
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m) + 1) = 2 := by
  have hble : b <= w.length := by
    rcases fw.hboundary.2.1 with hlast | hrange
    · omega
    · omega
  exact cycleQb8Input_cyclic_head_rank_two_of_outgoing_c3
    fw.hinput b j hble fw.hj_le hjlt hout

/-- A fully cyclic failure window cannot be followed by a C3 edge.
The contradiction is the exact identity `windowValue = t+v2(head+1)`
against the wrap-aware head rank `2`. -/
theorem cyclicDepthFailureWindow_false_of_outgoing_c3
    {m S P : Nat} {w rise c3 : List Nat}
    {b j t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (fw : CyclicDepthFailureWindow
      m S P w rise c3 b j t delta rt)
    (hjlt : j < w.length)
    (hout : 3 <=
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j) : False := by
  have hrank := cyclicDepthFailureWindow_rank_two_of_outgoing_c3
    fw hjlt hout
  rcases fw.ht with ht1 | ht2
  · have hdelta : delta = 1 := fw.hdelta.1 ht1
    have hfail0 := fw.hfail_t1 ht1
    subst t
    subst delta
    have hfail : 2 * j + 12 <=
        BlockAutomaton.t1WindowValue j rt.k rt.s := by
      simpa [BlockAutomaton.t1WindowValue] using hfail0
    have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
      j rt.k rt.s
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m)) fw.hreset
    rw [hwindow, hrank] at hfail
    omega
  · have hfail0 := fw.hfail_t2 ht2
    subst t
    have hfail : 2 * j + 11 <=
        BlockAutomaton.t2WindowValue j rt.k delta rt.s := by
      simpa [BlockAutomaton.t2WindowValue] using hfail0
    have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
      j rt.k delta rt.s
      (StringFlow.Word.wordOrbit
        ((StringFlow.CycleBridge.cyclicSegmentAt w b).take j)
        (StringFlow.Word.wordOrbit (w.take b) m)) fw.hreset
    rw [hwindow, hrank] at hfail
    omega

/-- Therefore a fully sourced failure at the actual maximal cyclic rise
endpoint is impossible, with no non-wrapping hypothesis. -/
theorem cyclicDepthFailureWindow_false_of_maximal_endpoint
    {m S P : Nat} {w rise c3 : List Nat}
    {b j t delta : Nat}
    {rt : S6Audit.AngelinaGilbertaRealTerminal}
    (fw : CyclicDepthFailureWindow
      m S P w rise c3 b j t delta rt)
    (hall : forall k : Nat, k < j ->
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
      (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2)
    (hstop : j = w.length \/
      3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI j) : False := by
  have hjlt := cycleQb8Input_cyclic_rise_run_length_lt
    fw.hinput b j fw.hboundary fw.hj_pos fw.hj_le hall
  rcases hstop with hfull | hc3
  · omega
  · exact cyclicDepthFailureWindow_false_of_outgoing_c3 fw hjlt hc3

/-- The exact remaining local arithmetic interface on the structurally
selected cyclic rise run.  All list/period/terminal coordinates are
fixed before this proposition asks for `delta`, the local terminal
equation, the 5-adic size conditions, and the two branchwise failure
lower bounds.  No strict global PMI comparison is included. -/
def cyclicRiseRunLocalResetFailureCore : Prop :=
  forall (m S P : Nat) (w rise c3 : List Nat),
    forall (h : StringFlow.CycleBridge.CycleQb8Input m S P w rise c3),
    forall (b L t : Nat),
      StringFlow.CycleBridge.IsCyclicC3RiseBoundaryAt w b ->
      1 <= L -> L <= w.length ->
      t = (StringFlow.CycleBridge.cyclicSegmentAt w b).getI (L - 1) ->
      (t = 1 \/ t = 2) ->
      (forall k : Nat, k < L ->
        (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 1 \/
        (StringFlow.CycleBridge.cyclicSegmentAt w b).getI k = 2) ->
      (L = w.length \/
        3 <= (StringFlow.CycleBridge.cyclicSegmentAt w b).getI L) ->
      exists rt : S6Audit.AngelinaGilbertaRealTerminal,
      exists delta : Nat,
        rt.r =
          (5 * StringFlow.Word.wordOrbit (w.take (b - 1)) m + 1) / 2 /\
        ((t = 1 -> delta = 1) /\
          (t = 2 -> delta = 1 \/ delta = 3)) /\
        StringFlow.CycleBridge.IsLocalResetTerminal t L
          (StringFlow.Word.wordOrbit
            ((StringFlow.CycleBridge.cyclicSegmentAt w b).take L)
            (StringFlow.Word.wordOrbit (w.take b) m)) delta rt /\
        rt.k + 1 <= L /\
        rt.s < 5 ^ (L - rt.k - 1) /\
        (t = 1 -> 2 * L + 12 <=
          twoValuation (5 ^ (rt.k + 1) * rt.s + 5 ^ L - 2)) /\
        (t = 2 -> 2 * L + 11 <=
          twoValuation
            (5 ^ (rt.k + 1) * rt.s + delta * 5 ^ L))

/-- The corrected cyclic local core alone rules out a positive repeat:
the structural selector supplies `b,L,t`, the core supplies the single
real terminal and local reset data, and the wrap-aware C3 contradiction
closes the selected block. -/
theorem no_cycle_of_cyclicRiseRunLocalResetFailureCore
    (hcore : cyclicRiseRunLocalResetFailureCore) :
    Not (StringFlow.OrbitCycle 7) := by
  intro hcycle
  rcases StringFlow.CycleBridge.orbit_cycle_imp_cycle_qb8_input hcycle with
    ⟨_c, p, m, S, w, rise, c3, hinput, _hw, _hrise, _hc3, _hS, _hm⟩
  rcases StringFlow.CycleBridge.cycleQb8Input_exists_c3_rise_run
      m S p w rise c3 hinput with
    ⟨b, L, t, hb, hL, hLle, ht_last, ht, hall, hstop⟩
  rcases hcore m S p w rise c3 hinput b L t hb hL hLle ht_last ht
      hall hstop with
    ⟨rt, delta, hrt, hdelta, hterm, hk, hslt, hfail_t1, hfail_t2⟩
  have fw := cyclic_local_block_to_cyclicDepthFailureWindow
    hinput b L t delta hb hL hLle rt hrt ht_last ht hdelta hterm
      hk hslt hfail_t1 hfail_t2
  exact cyclicDepthFailureWindow_false_of_maximal_endpoint fw hall hstop

/-- Audit of this particular combined core: because its local data are
already contradictory at the maximal endpoint, universal existence of
such data is equivalent to absence of cycle inputs.  This equivalence
concerns only the combined reset-plus-failure package; it says nothing
about other valuation or predecessor routes. -/
theorem no_cycle_iff_cyclicRiseRunLocalResetFailureCore :
    Not (StringFlow.OrbitCycle 7) ↔
      cyclicRiseRunLocalResetFailureCore := by
  constructor
  · intro hno m S P w rise c3 hinput
    exact False.elim
      (hno (StringFlow.CycleBridge.cycleQb8Input_imp_orbit_cycle hinput))
  · exact no_cycle_of_cyclicRiseRunLocalResetFailureCore

/-- Conditional final assembly through the corrected fully cyclic
local interface. -/
theorem five_x_plus_one_diverges_at_7_of_cyclic_local_core
    (hcore : cyclicRiseRunLocalResetFailureCore) :
    StringFlow.IsUnboundedOrbit 7 :=
  StringFlow.unbounded_of_no_cycle 7
    (no_cycle_of_cyclicRiseRunLocalResetFailureCore hcore)

/-- A corrected failure at depth `j` forces at least five further
positions in the ambient cycle period.  For `t=1` this is the head-rank
lower bound itself; for `t=2` it is the stronger genuine-predecessor
rank obtained after exact incoming-edge alignment. -/
theorem failureWindow_depth_plus_five_le_period
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    j + 5 <= P := by
  have hjP : j < P := fw.hj_lt
  rcases fw.ht with ht1 | ht2
  · have hdelta : delta = 1 := fw.hδ.1 ht1
    have hfail0 := fw.hfail_t1 ht1
    subst t
    subst delta
    have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
      simpa [BlockAutomaton.t1WindowValue] using hfail0
    have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
      j k0 s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
    rw [hwindow] at hfail
    have hjw : j <= w.length := by
      rw [fw.hinput.hlength]
      omega
    have hupper := cycleQb8Input_prefix_rank_le_period fw.hinput j hjw
    omega
  · rcases failureWindow_t2_forces_real_predecessor_rank fw ht2 with
      ⟨_n, _hn, _hiter, hlower⟩
    have hjw : j - 1 <= w.length := by
      rw [fw.hinput.hlength]
      omega
    have hupper := cycleQb8Input_prefix_rank_le_period
      fw.hinput (j - 1) hjw
    omega

/-- The failure bounds themselves give an exact lower bound on the
rank of the real cycle-word head: `2j+11` for `t=1`, and `2j+9` for
`t=2`. -/
theorem failureWindow_head_rank_lower
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    (t = 1 /\ 2 * j + 11 <= twoValuation
      (StringFlow.Word.wordOrbit (w.take j) m + 1)) \/
    (t = 2 /\ 2 * j + 9 <= twoValuation
      (StringFlow.Word.wordOrbit (w.take j) m + 1)) := by
  rcases fw.ht with ht1 | ht2
  · left
    refine ⟨ht1, ?_⟩
    have hdelta : delta = 1 := fw.hδ.1 ht1
    have hfail0 := fw.hfail_t1 ht1
    subst t
    subst delta
    have hfail : 2 * j + 12 <= BlockAutomaton.t1WindowValue j k0 s := by
      simpa [BlockAutomaton.t1WindowValue] using hfail0
    have hwindow := t1WindowValue_eq_twoValuation_rj_plus_one
      j k0 s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
    rw [hwindow] at hfail
    omega
  · right
    refine ⟨ht2, ?_⟩
    have hfail0 := fw.hfail_t2 ht2
    subst t
    have hfail : 2 * j + 11 <=
        BlockAutomaton.t2WindowValue j k0 delta s := by
      simpa [BlockAutomaton.t2WindowValue] using hfail0
    have hwindow := t2WindowValue_eq_twoValuation_rj_plus_one
      j k0 delta s (StringFlow.Word.wordOrbit (w.take j) m) fw.hreset
    rw [hwindow] at hfail
    omega

/-- Consequently every in-range suffix short enough to be covered by
the failure rank is a genuine run of weight-two edges. -/
theorem failureWindow_forced_two_tail
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s q : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hfit : j + q < P)
    (hq1 : t = 1 -> q <= j + 4)
    (hq2 : t = 2 -> q <= j + 3) :
    forall k : Nat, k <= q -> w.getI (j + k) = 2 := by
  have hjq : j + q < w.length := by
    rw [fw.hinput.hlength]
    exact hfit
  rcases failureWindow_head_rank_lower fw with h1 | h2
  · have hrank : 2 * q + 3 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take j) m + 1) := by
      have hq := hq1 h1.1
      omega
    exact cycleQb8Input_forced_two_after_prefix
      fw.hinput j q hjq hrank
  · have hrank : 2 * q + 3 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take j) m + 1) := by
      have hq := hq2 h2.1
      omega
    exact cycleQb8Input_forced_two_after_prefix
      fw.hinput j q hjq hrank

/-- Quantitative C3-separation forced by a failure window.  If the
next displayed C3 entry is `q` positions after the failure head, then
`q >= j+5` in the `t=1` branch and `q >= j+4` in the `t=2` branch. -/
theorem failureWindow_next_c3_distance_lower
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s q : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hfit : j + q < P) (hc3 : 3 <= w.getI (j + q)) :
    (t = 1 -> j + 5 <= q) /\ (t = 2 -> j + 4 <= q) := by
  constructor
  · intro ht
    by_contra hnot
    have hq : q <= j + 4 := by omega
    have htwo := failureWindow_forced_two_tail fw hfit
      (fun _ => hq) (fun ht2 => by omega)
    have heq := htwo q (by omega)
    omega
  · intro ht
    by_contra hnot
    have hq : q <= j + 3 := by omega
    have htwo := failureWindow_forced_two_tail fw hfit
      (fun ht1 => by omega) (fun _ => hq)
    have heq := htwo q (by omega)
    omega

/-- Combining the head-rank lower bound with the guaranteed C3 edge in
one period sharpens the period obstruction.  A `t=1` failure needs at
least `j+6` period positions; a `t=2` failure needs at least `j+5`. -/
theorem failureWindow_period_lower_refined
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    (t = 1 -> j + 6 <= P) /\ (t = 2 -> j + 5 <= P) := by
  rcases fw.hinput.hstart with ⟨n0, hstart⟩
  have hjw : j <= w.length := by
    rw [fw.hinput.hlength]
    exact Nat.le_of_lt fw.hj_lt
  have hhead := cycleQb8Input_prefix_fullOrbitIter_of_start
    fw.hinput n0 hstart j hjw
  rcases cycleQb8Input_c3_within_period_after_prefix
      fw.hinput n0 hstart j fw.hj_lt with ⟨q, hqP, hc3⟩
  have hranks := failureWindow_head_rank_lower fw
  constructor
  · intro ht
    by_contra hnot
    have hq : q <= j + 4 := by omega
    have hrankWord : 2 * j + 11 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take j) m + 1) := by
      rcases hranks with h1 | h2
      · exact h1.2
      · omega
    have hrank0 : 2 * q + 3 <=
        twoValuation (fullOrbitIter (n0 + j) + 1) := by
      rw [hhead]
      omega
    have hdrop := fullOrbitIter_rank_drop_two_iter (n0 + j) q hrank0
    have hrankq : 3 <= twoValuation
        (fullOrbitIter ((n0 + j) + q) + 1) := by
      rw [hdrop]
      omega
    have htwo := orbitStepWeight_of_rank_ge_three ((n0 + j) + q) hrankq
    omega
  · intro ht
    by_contra hnot
    have hq : q <= j + 3 := by omega
    have hrankWord : 2 * j + 9 <= twoValuation
        (StringFlow.Word.wordOrbit (w.take j) m + 1) := by
      rcases hranks with h1 | h2
      · omega
      · exact h2.2
    have hrank0 : 2 * q + 3 <=
        twoValuation (fullOrbitIter (n0 + j) + 1) := by
      rw [hhead]
      omega
    have hdrop := fullOrbitIter_rank_drop_two_iter (n0 + j) q hrank0
    have hrankq : 3 <= twoValuation
        (fullOrbitIter ((n0 + j) + q) + 1) := by
      rw [hdrop]
      omega
    have htwo := orbitStepWeight_of_rank_ge_three ((n0 + j) + q) hrankq
    omega

/-- Minimal `t=1` remainder after exact orbit alignment: a genuine
failure-window predecessor cannot create a rank-one spike above the
window threshold. -/
def cycleFailureT1PredecessorSpikeBound : Prop :=
  forall (m S P : Nat) (w rise c3 : List Nat)
    (j k0 t delta s : Nat),
    StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s ->
    t = 1 ->
    twoValuation
      (5 * StringFlow.oddPart
        (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) - 1) <=
      2 * j + 10

/-- Minimal `t=2` remainder after exact orbit alignment: the genuine
predecessor rank is at most `2j+10`. -/
def cycleFailureT2PredecessorRankBound : Prop :=
  forall (m S P : Nat) (w rise c3 : List Nat)
    (j k0 t delta s : Nat),
    StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s ->
    t = 2 ->
    twoValuation
      (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) <=
      2 * j + 10

/-- The two predecessor bounds contradict every genuine failure
window; no corrected-window wrapper is used in this reduction. -/
theorem failureWindow_false_of_real_predecessor_bounds
    (h1 : cycleFailureT1PredecessorSpikeBound)
    (h2 : cycleFailureT2PredecessorRankBound)
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) : False := by
  rcases fw.ht with ht1 | ht2
  · rcases failureWindow_t1_forces_real_predecessor_spike fw ht1 with
      ⟨_n, _hn, _hiter, _hrank, hlarge⟩
    have hsmall := h1 m S P w rise c3 j k0 t delta s fw ht1
    omega
  · rcases failureWindow_t2_forces_real_predecessor_rank fw ht2 with
      ⟨_n, _hn, _hiter, hlarge⟩
    have hsmall := h2 m S P w rise c3 j k0 t delta s fw ht2
    omega

/-- Exact conditional no-cycle assembly for the predecessor route. -/
theorem no_cycle_of_failure_window_and_real_predecessor_bounds
    (hfw : StringFlow.CycleBridge.failureWindowExistence)
    (h1 : cycleFailureT1PredecessorSpikeBound)
    (h2 : cycleFailureT2PredecessorRankBound) :
    ¬ StringFlow.OrbitCycle 7 := by
  intro hcycle
  rcases StringFlow.CycleBridge.orbit_cycle_imp_cycle_qb8_input hcycle with
    ⟨_c, p, m, S, w, rise, c3, hinput, _hw, _hrise, _hc3, _hS, _hm⟩
  rcases hfw m S p w rise c3 hinput with
    ⟨j, k0, t, delta, s, fw⟩
  exact failureWindow_false_of_real_predecessor_bounds h1 h2 fw

/-- Exact conditional final assembly for the predecessor route. -/
theorem five_x_plus_one_diverges_at_7_of_real_predecessor_bounds
    (hfw : StringFlow.CycleBridge.failureWindowExistence)
    (h1 : cycleFailureT1PredecessorSpikeBound)
    (h2 : cycleFailureT2PredecessorRankBound) :
    StringFlow.IsUnboundedOrbit 7 :=
  StringFlow.unbounded_of_no_cycle 7
    (no_cycle_of_failure_window_and_real_predecessor_bounds hfw h1 h2)

/-- The `t=1` double expression: the reset identity and the exact
full-orbit predecessor equation eliminate `rj+1`. -/
theorem t1DoubleExpression
    (j k0 s r rj n : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 1 1 s r rj)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    2 ^ orbitStepWeight (n - 1) *
        (25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11) =
      4 * (5 * fullOrbitIter (n - 1) + 1 +
          2 ^ orbitStepWeight (n - 1)) := by
  have hid := rjPlusOne_t1_identity j k0 s r rj hAt hreset
  have hA : 4 * (rj + 1) =
      25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11 := hid.2.2
  have hpred := fullOrbit_predecessor_mul n rj hn hiter
  have hB : 2 ^ orbitStepWeight (n - 1) * (rj + 1) =
      5 * fullOrbitIter (n - 1) + 1 +
        2 ^ orbitStepWeight (n - 1) := by
    nlinarith [hpred]
  have hmain : 2 ^ orbitStepWeight (n - 1) *
        (25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11) =
      4 * (5 * fullOrbitIter (n - 1) + 1 +
          2 ^ orbitStepWeight (n - 1)) := by
    calc
      2 ^ orbitStepWeight (n - 1) *
          (25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11) =
          2 ^ orbitStepWeight (n - 1) * (4 * (rj + 1)) := by rw [hA]
      _ = 4 * (2 ^ orbitStepWeight (n - 1) * (rj + 1)) := by ring
      _ = 4 * (5 * fullOrbitIter (n - 1) + 1 +
            2 ^ orbitStepWeight (n - 1)) := by rw [hB]
  exact hmain

/-- The `t=2` double expression: the reset identity and the exact
full-orbit predecessor equation eliminate `rj+1`. -/
theorem t2DoubleExpression
    (j k0 s r rj n : Nat) (delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 2 delta s r rj)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    2 ^ orbitStepWeight (n - 1) *
        (25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j) =
      8 * (5 * fullOrbitIter (n - 1) + 1 +
          2 ^ orbitStepWeight (n - 1)) := by
  have hid := rjPlusOne_t2_identity j k0 s r rj delta hAt hreset
  have hA : 8 * (rj + 1) =
      25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j := hid.2.2
  have hpred := fullOrbit_predecessor_mul n rj hn hiter
  have hB : 2 ^ orbitStepWeight (n - 1) * (rj + 1) =
      5 * fullOrbitIter (n - 1) + 1 +
        2 ^ orbitStepWeight (n - 1) := by
    nlinarith [hpred]
  have hmain : 2 ^ orbitStepWeight (n - 1) *
        (25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j) =
      8 * (5 * fullOrbitIter (n - 1) + 1 +
          2 ^ orbitStepWeight (n - 1)) := by
    calc
      2 ^ orbitStepWeight (n - 1) *
          (25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j) =
          2 ^ orbitStepWeight (n - 1) * (8 * (rj + 1)) := by rw [hA]
      _ = 8 * (2 ^ orbitStepWeight (n - 1) * (rj + 1)) := by ring
      _ = 8 * (5 * fullOrbitIter (n - 1) + 1 +
            2 ^ orbitStepWeight (n - 1)) := by rw [hB]
  exact hmain

/-- The `t=1` rank bound is equivalent to the remaining reset-valuation
congruence after eliminating `s`. -/
theorem t1Rank_iff_reset_valuation
    (j k0 s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 1 1 s r rj)
    (hreset : ResetHeadEq s j k0 1 1 rj) :
    (twoValuation (rj + 1) ≤ 2 * j + 10) ↔
      twoValuation (25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11) ≤
        2 * j + 12 := by
  have hid := rjPlusOne_t1_identity j k0 s r rj hAt hreset
  have hmain : 4 * (rj + 1) =
      25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11 := hid.2.2
  have hpos : 0 < rj + 1 := by positivity
  have hval := StringFlow.Lte.twoValuation_mul_two_pow 2 (rj + 1) hpos
  have hF : twoValuation (25 * fullOrbitIter (j - 2) + 2 * 5 ^ j + 11) =
      2 + twoValuation (rj + 1) := by
    rw [← hmain]
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hval
  constructor
  · intro h
    rw [hF]
    omega
  · intro h
    rw [hF] at h
    omega

/-- The `t=2` rank bound is equivalent to the remaining reset-valuation
congruence after eliminating `s`. -/
theorem t2Rank_iff_reset_valuation
    (j k0 s r rj : Nat) (delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 2 delta s r rj)
    (hreset : ResetHeadEq s j k0 2 delta rj) :
    (twoValuation (rj + 1) ≤ 2 * j + 8) ↔
      twoValuation
          (25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j) ≤
        2 * j + 11 := by
  have hid := rjPlusOne_t2_identity j k0 s r rj delta hAt hreset
  have hmain : 8 * (rj + 1) =
      25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j := hid.2.2
  have hpos : 0 < rj + 1 := by positivity
  have hval := StringFlow.Lte.twoValuation_mul_two_pow 3 (rj + 1) hpos
  have hF : twoValuation
        (25 * fullOrbitIter (j - 2) + 15 + 2 * delta * 5 ^ j) =
      3 + twoValuation (rj + 1) := by
    rw [← hmain]
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hval
  constructor
  · intro h
    rw [hF]
    omega
  · intro h
    rw [hF] at h
    omega

/-- If a positive integer lies below `2^(K+1)`, then its two-adic
valuation is at most `K`.  This is the direct size form of the
`twoValuation_le_iff_not_dvd_pow` criterion. -/
lemma twoValuation_le_of_lt_two_pow
    (n K : Nat) (hn : 0 < n) (hlt : n < 2 ^ (K + 1)) :
    twoValuation n ≤ K := by
  have hiff := StringFlow.Lte.twoValuation_le_iff_not_dvd_pow n K hn
  apply hiff.mpr
  intro hdvd
  have hle : 2 ^ (K + 1) ≤ n := Nat.le_of_dvd hn hdvd
  omega

/-- On the whole range `j ≤ 34`, the elementary state-size estimate
`rj + 1 ≤ 5^j` is already strong enough for the corrected `t=1`
rank target. -/
lemma five_pow_lt_two_pow_t1_small
    (j : Nat) (hj : j ≤ 34) :
    5 ^ j < 2 ^ (2 * j + 11) := by
  interval_cases j <;> norm_num

/-- On the whole range `j ≤ 27`, the elementary state-size estimate
`rj + 1 ≤ 5^j` is already strong enough for the corrected `t=2`
rank target. -/
lemma five_pow_lt_two_pow_t2_small
    (j : Nat) (hj : j ≤ 27) :
    5 ^ j < 2 ^ (2 * j + 9) := by
  interval_cases j <;> norm_num

/-- The sharper predecessor-size comparison used by genuine `t=2`
failure windows.  It remains valid through depth `35`. -/
lemma four_mul_five_pow_pred_lt_two_pow_t2_small
    (j : Nat) (hjpos : 1 <= j) (hj : j <= 35) :
    4 * 5 ^ (j - 1) < 2 ^ (2 * j + 11) := by
  interval_cases j <;> norm_num

/-- In the `delta=1` branch the predecessor is below
`2*5^(j-1)`, extending the direct range through depth `38`. -/
lemma two_mul_five_pow_pred_lt_two_pow_t2_delta_one
    (j : Nat) (hjpos : 1 <= j) (hj : j <= 38) :
    2 * 5 ^ (j - 1) < 2 ^ (2 * j + 11) := by
  interval_cases j <;> norm_num

/-- Direct inequality chain for the genuine `t=2` predecessor through
depth `35`:

`x+1 = 5^k s + delta*5^(j-1)`
`     < 4*5^(j-1)`
`     < 2^(2j+11)`.

Consequently `v2(x+1) <= 2j+10`. -/
theorem failureWindow_t2_predecessor_rank_bound_of_j_le_35
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 2) (hj : j <= 35) :
    twoValuation
      (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) <=
      2 * j + 10 := by
  have hjpos : 1 <= j := by
    have hk := fw.hk
    omega
  have hdelta : delta = 1 ∨ delta = 3 := fw.hδ.2 ht
  have hdeltale : delta <= 3 := by
    rcases hdelta with rfl | rfl <;> norm_num
  have hterm_lt : 5 ^ k0 * s < 5 ^ (j - 1) := by
    rcases resetWindowReachability_previous_data
        j k0 t delta s fw.hreach with
      ⟨r, hprod, hrlt, _hreachR⟩
    have hprod' : 5 ^ k0 * s = r + 1 := by
      simpa [Nat.mul_comm] using hprod
    rwa [hprod']
  rcases failureWindow_real_predecessor_alignment fw with
    ⟨n, _hn, _hiter, hprev, _hw, hpred⟩
  let x := StringFlow.Word.wordOrbit (w.take (j - 1)) m
  have hsumpos : 0 < 5 ^ k0 * s + delta * 5 ^ (j - 1) := by
    have hpowpos : 0 < 5 ^ (j - 1) := by positivity
    have hdeltapos : 0 < delta := by
      rcases hdelta with rfl | rfl <;> norm_num
    positivity
  have hxsum : x + 1 = 5 ^ k0 * s + delta * 5 ^ (j - 1) := by
    dsimp [x]
    rw [← hprev]
    omega
  have hsize : x + 1 < 4 * 5 ^ (j - 1) := by
    rw [hxsum]
    have hdelta_mul : delta * 5 ^ (j - 1) <= 3 * 5 ^ (j - 1) :=
      Nat.mul_le_mul_right (5 ^ (j - 1)) hdeltale
    omega
  have hpow := four_mul_five_pow_pred_lt_two_pow_t2_small j hjpos hj
  have hlt : x + 1 < 2 ^ (2 * j + 11) := lt_trans hsize hpow
  exact twoValuation_le_of_lt_two_pow (x + 1) (2 * j + 10)
    (by positivity) (by simpa [Nat.add_assoc] using hlt)

/-- Direct `delta=1` refinement of the genuine `t=2` predecessor
bound through depth `38`. -/
theorem failureWindow_t2_delta_one_predecessor_rank_bound_of_j_le_38
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 2) (hdelta : delta = 1) (hj : j <= 38) :
    twoValuation
      (StringFlow.Word.wordOrbit (w.take (j - 1)) m + 1) <=
      2 * j + 10 := by
  have hjpos : 1 <= j := by
    have hk := fw.hk
    omega
  have hterm_lt : 5 ^ k0 * s < 5 ^ (j - 1) := by
    rcases resetWindowReachability_previous_data
        j k0 t delta s fw.hreach with
      ⟨r, hprod, hrlt, _hreachR⟩
    have hprod' : 5 ^ k0 * s = r + 1 := by
      simpa [Nat.mul_comm] using hprod
    rwa [hprod']
  rcases failureWindow_real_predecessor_alignment fw with
    ⟨n, _hn, _hiter, hprev, _hw, hpred⟩
  let x := StringFlow.Word.wordOrbit (w.take (j - 1)) m
  have hxsum : x + 1 = 5 ^ k0 * s + 5 ^ (j - 1) := by
    dsimp [x]
    rw [← hprev]
    rw [hdelta] at hpred
    omega
  have hsize : x + 1 < 2 * 5 ^ (j - 1) := by
    rw [hxsum]
    omega
  have hpow := two_mul_five_pow_pred_lt_two_pow_t2_delta_one
    j hjpos hj
  have hlt : x + 1 < 2 ^ (2 * j + 11) := lt_trans hsize hpow
  exact twoValuation_le_of_lt_two_pow (x + 1) (2 * j + 10)
    (by positivity) (by simpa [Nat.add_assoc] using hlt)

/-- Every reachable `t=1` reset head with `j ≤ 34` satisfies the
required rank bound.  Only the reset equation and its inherited size
bound are used; no orbit enumeration enters the proof. -/
theorem rjRankT1Bound_of_j_le_34
    (j k0 s rj : Nat)
    (hreset : ResetHeadEq s j k0 1 1 rj)
    (hreach : ResetWindowReachability j k0 1 1 s)
    (hj : j ≤ 34) :
    twoValuation (rj + 1) ≤ 2 * j + 10 := by
  rcases hreach with ⟨_r, _rj', hk, _hprod, _hodd, _hnd5, hslt,
    _hOrbitR, _hreset', _hOddRj, _hOrbitRj⟩
  have hrj : rj < 5 ^ j :=
    reset_head_lt_five_pow s j k0 1 1 rj hk hslt hreset
  have hrj1 : rj + 1 ≤ 5 ^ j := by omega
  have hlt : rj + 1 < 2 ^ (2 * j + 11) :=
    lt_of_le_of_lt hrj1 (five_pow_lt_two_pow_t1_small j hj)
  exact twoValuation_le_of_lt_two_pow (rj + 1) (2 * j + 10)
    (by positivity) (by simpa [Nat.add_assoc] using hlt)

/-- Every reachable `t=2` reset head with `j ≤ 27` satisfies the
required rank bound.  Again this is a direct size argument, independent
of any finite orbit scan. -/
theorem rjRankT2Bound_of_j_le_27
    (j k0 delta s rj : Nat)
    (hreset : ResetHeadEq s j k0 2 delta rj)
    (hreach : ResetWindowReachability j k0 2 delta s)
    (hj : j ≤ 27) :
    twoValuation (rj + 1) ≤ 2 * j + 8 := by
  rcases hreach with ⟨_r, _rj', hk, _hprod, _hodd, _hnd5, hslt,
    _hOrbitR, _hreset', _hOddRj, _hOrbitRj⟩
  have hrj : rj < 5 ^ j :=
    reset_head_lt_five_pow s j k0 2 delta rj hk hslt hreset
  have hrj1 : rj + 1 ≤ 5 ^ j := by omega
  have hlt : rj + 1 < 2 ^ (2 * j + 9) :=
    lt_of_le_of_lt hrj1 (five_pow_lt_two_pow_t2_small j hj)
  exact twoValuation_le_of_lt_two_pow (rj + 1) (2 * j + 8)
    (by positivity) (by simpa [Nat.add_assoc] using hlt)

/-- A corrected failure window cannot lie in either range already
covered by the direct size estimates.  Real predecessor alignment
extends the `t=2` range from `27` through `35`. -/
theorem failureWindow_impossible_of_small_depth
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (hsmall : (t = 1 ∧ j ≤ 34) ∨ (t = 2 ∧ j ≤ 35)) : False := by
  rcases hsmall with ⟨ht, hj⟩ | ⟨ht, hj⟩
  · have hdelta : delta = 1 := fw.hδ.1 ht
    subst t
    subst delta
    let rj := StringFlow.Word.wordOrbit (w.take j) m
    have hrank : twoValuation (rj + 1) ≤ 2 * j + 10 :=
      rjRankT1Bound_of_j_le_34 j k0 s rj fw.hreset fw.hreach hj
    have hwin : BlockAutomaton.t1WindowValue j k0 s ≤ 2 * j + 11 :=
      (t1WindowBoundCorrected_iff_rj_rank j k0 s rj fw.hreset).mpr hrank
    exact StringFlow.CycleBridge.failure_window_contradicts_t1 j k0 s
      (BlockAutomaton.t1WindowValue j k0 s) (fw.hfail_t1 rfl) hwin
  · subst t
    have hsmall := failureWindow_t2_predecessor_rank_bound_of_j_le_35
      fw rfl hj
    rcases failureWindow_t2_forces_real_predecessor_rank fw rfl with
      ⟨_n, _hn, _hiter, hlarge⟩
    omega

/-- The sharper `delta=1` predecessor estimate excludes the additional
depths `36,37,38` in the `t=2` branch. -/
theorem failureWindow_t2_delta_one_impossible_of_j_le_38
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s)
    (ht : t = 2) (hdelta : delta = 1) (hj : j <= 38) : False := by
  have hsmall :=
    failureWindow_t2_delta_one_predecessor_rank_bound_of_j_le_38
      fw ht hdelta hj
  rcases failureWindow_t2_forces_real_predecessor_rank fw ht with
    ⟨_n, _hn, _hiter, hlarge⟩
  omega

/-- Consequently every corrected failure window is forced into the
large-depth remainder: `j ≥ 35` in the `t=1` branch and `j ≥ 36` in
the `t=2` branch. -/
theorem failureWindow_large_depth
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    (t = 1 → 35 ≤ j) ∧ (t = 2 → 36 ≤ j) := by
  constructor
  · intro ht
    by_contra hnot
    exact failureWindow_impossible_of_small_depth fw
      (Or.inl ⟨ht, by omega⟩)
  · intro ht
    by_contra hnot
    exact failureWindow_impossible_of_small_depth fw
      (Or.inr ⟨ht, by omega⟩)

/-- Refined branchwise large-depth remainder: `delta=1` starts only at
depth `39`, while `delta=3` retains the sharp direct cutoff `36`. -/
theorem failureWindow_large_depth_refined
    {m S P : Nat} {w rise c3 : List Nat}
    {j k0 t delta s : Nat}
    (fw : StringFlow.CycleBridge.FailureWindow
      m S P w rise c3 j k0 t delta s) :
    (t = 1 -> 35 <= j) /\
    (t = 2 -> delta = 1 -> 39 <= j) /\
    (t = 2 -> delta = 3 -> 36 <= j) := by
  have hbase := failureWindow_large_depth fw
  refine ⟨hbase.1, ?_, ?_⟩
  · intro ht hdelta
    by_contra hnot
    exact failureWindow_t2_delta_one_impossible_of_j_le_38
      fw ht hdelta (by omega)
  · intro ht _hdelta
    exact hbase.2 ht

/-- The remaining analytic statement for corrected `t=1` windows:
every real-orbit reset head has rank at most `2j+10`. -/
def rjRankT1Bound : Prop :=
  ∀ j k0 s : Nat, ∀ rj : Nat,
    ResetHeadEq s j k0 1 1 rj →
    ResetWindowReachability j k0 1 1 s →
    twoValuation (rj + 1) ≤ 2 * j + 10

/-- The remaining analytic statement for corrected `t=2` windows:
every real-orbit reset head has rank at most `2j+8`. -/
def rjRankT2Bound : Prop :=
  ∀ j k0 δ s : Nat, ∀ rj : Nat,
    ResetHeadEq s j k0 2 δ rj →
    ResetWindowReachability j k0 2 δ s →
    twoValuation (rj + 1) ≤ 2 * j + 8

/-- The exact large-depth remainder of the `t=1` rank problem. -/
def rjRankT1LargeBound : Prop :=
  ∀ j k0 s : Nat, ∀ rj : Nat,
    35 ≤ j →
    ResetHeadEq s j k0 1 1 rj →
    ResetWindowReachability j k0 1 1 s →
    twoValuation (rj + 1) ≤ 2 * j + 10

/-- The exact large-depth remainder of the `t=2` rank problem. -/
def rjRankT2LargeBound : Prop :=
  ∀ j k0 delta s : Nat, ∀ rj : Nat,
    28 ≤ j →
    ResetHeadEq s j k0 2 delta rj →
    ResetWindowReachability j k0 2 delta s →
    twoValuation (rj + 1) ≤ 2 * j + 8

/-- The full `t=1` rank statement is equivalent to its `j ≥ 35`
remainder; all smaller depths are already closed above. -/
theorem rjRankT1Bound_iff_large :
    rjRankT1Bound ↔ rjRankT1LargeBound := by
  constructor
  · intro h j k0 s rj _hj hreset hreach
    exact h j k0 s rj hreset hreach
  · intro h j k0 s rj hreset hreach
    by_cases hj : j ≤ 34
    · exact rjRankT1Bound_of_j_le_34 j k0 s rj hreset hreach hj
    · exact h j k0 s rj (by omega) hreset hreach

/-- The full `t=2` rank statement is equivalent to its `j ≥ 28`
remainder; all smaller depths are already closed above. -/
theorem rjRankT2Bound_iff_large :
    rjRankT2Bound ↔ rjRankT2LargeBound := by
  constructor
  · intro h j k0 delta s rj _hj hreset hreach
    exact h j k0 delta s rj hreset hreach
  · intro h j k0 delta s rj hreset hreach
    by_cases hj : j ≤ 27
    · exact rjRankT2Bound_of_j_le_27 j k0 delta s rj hreset hreach hj
    · exact h j k0 delta s rj (by omega) hreset hreach

/-- The `t=1` corrected window bound follows from the real-orbit
block-head rank bound. -/
theorem t1WindowBoundCorrected_of_rjRankT1Bound
    (hrank : rjRankT1Bound) :
    ∀ j k0 a t s : Nat, BlockAutomaton.t1WindowBoundCorrected j k0 a t s := by
  intro j k0 a t s ha ht hreach
  subst t
  rcases hreach with ⟨r, rj, hk, hprod, hodd, hnd5, hslt, hOrbitR,
    hreset, hOddRj, hOrbitRj⟩
  have hbound := hrank j k0 s rj hreset
    ⟨r, rj, hk, hprod, hodd, hnd5, hslt, hOrbitR, hreset, hOddRj, hOrbitRj⟩
  exact (t1WindowBoundCorrected_iff_rj_rank j k0 s rj hreset).mpr hbound

/-- The `t=2` corrected window bound follows from the real-orbit
block-head rank bound. -/
theorem t2WindowBoundCorrected_of_rjRankT2Bound
    (hrank : rjRankT2Bound) :
    ∀ j k0 a t δ s : Nat,
      BlockAutomaton.t2WindowBoundCorrected j k0 a t δ s := by
  intro j k0 a t δ s ha ht hδ hreach
  subst t
  rcases hreach with ⟨r, rj, hk, hprod, hodd, hnd5, hslt, hOrbitR,
    hreset, hOddRj, hOrbitRj⟩
  have hbound := hrank j k0 δ s rj hreset
    ⟨r, rj, hk, hprod, hodd, hnd5, hslt, hOrbitR, hreset, hOddRj, hOrbitRj⟩
  exact (t2WindowBoundCorrected_iff_rj_rank j k0 δ s rj hreset).mpr hbound

/-- With both real-orbit block-head rank bounds, the corrected decisive
window bound is assembled. -/
theorem decisiveWindowValuationBoundCorrected_of_rjRankBounds
    (h1 : rjRankT1Bound) (h2 : rjRankT2Bound) :
    BlockAutomaton.decisiveWindowValuationBoundCorrected := by
  constructor
  · exact t2WindowBoundCorrected_of_rjRankT2Bound h2
  · exact t1WindowBoundCorrected_of_rjRankT1Bound h1

end StringFlow.RealOrbitLocalLemma
