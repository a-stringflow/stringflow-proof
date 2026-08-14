import PmiLocalLemma
import BlockAutomaton
import S6AuditStage1
import UnifiedCoreBridge

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
residue as the reset weight `t`. -/
theorem fullOrbitStepWeight_mod4_of_reset
    (n j k0 s r rj : Nat) (t delta : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj) :
    (t = 1 → orbitStepWeight (n - 1) % 4 = 1) ∧
      (t = 2 → orbitStepWeight (n - 1) % 4 = 2) := by
  have hj : 2 ≤ j := resetWindowDepth_j_ge_two j k0 t delta s r rj hAt
  have hmod := reset_head_mod_five s j k0 t delta rj (by omega) hreset
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
  have hmod := fullOrbitStepWeight_mod4_of_reset
    n j k0 s r rj 1 1 hAt hreset hn hiter
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

/-- For a `t=2` reset, the real incoming step weight has only the
rank-`≥3` branch `w=2` and the rank-two branch `w=2+v` with
`v≡0 (mod 4)`. -/
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
  have hmod := fullOrbitStepWeight_mod4_of_reset
    n j k0 s r rj 2 delta hAt hreset hn hiter
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

/-- When the real incoming weight agrees with the reset weight, the
two equations determine the full-orbit predecessor `f(n-1)` from the
depth-aligned previous terminal.  This is the missing depth connection
in the two branches where the weights are exactly equal. -/
theorem reset_full_predecessor_alignment
    (n j k0 t delta s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
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

/-- In the equal-weight branches, the reset predecessor is exactly
`f(n-1)`.  This is the depth connection replacing the candidate word
argument: the two exact equations already force the same 5-linear form. -/
theorem reset_predecessor_eq_fullOrbit_of_aligned_weight
    (n j k0 t delta s r rj : Nat)
    (hAt : ResetWindowReachabilityAtDepth j k0 t delta s r rj)
    (hreset : ResetHeadEq s j k0 t delta rj)
    (hn : 1 ≤ n)
    (hiter : fullOrbitIter n = rj)
    (hw : orbitStepWeight (n - 1) = t) :
    5 ^ k0 * s + delta * 5 ^ (j - 1) - 1 = fullOrbitIter (n - 1) := by
  have hAl := reset_full_predecessor_alignment
    n j k0 t delta s r rj hAt hreset hn hiter hw
  let x := 5 ^ k0 * s + delta * 5 ^ (j - 1) - 1
  have hj : 2 ≤ j := resetWindowDepth_j_ge_two j k0 t delta s r rj hAt
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
