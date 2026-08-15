import S6Audit

/-!
# Stage 1 counterexample: v2 parity invariant does not extend to `GeneralOrbitFrom7`

`GeneralOrbitFrom7` allows arbitrary step weights, including `t=0` and
`t>=3`.  The old 25-state invariant `orbit25_v2_odd_of_five` cannot be
ported to this superset: the state `1989379` is reachable via the explicit
word below, yet `1989379` is odd, `5 | 1989380`, and
`twoValuation 1989380 = 2` is even.

This is a finite regression certificate, not a substitute for the stage-1
proof.  It shows that coverage extension must either restrict to the real
reset-head subfamily or use a different invariant.
-/

namespace S6Audit

/-- Finite certificate: `1989379` kills the naive v2-parity extension. -/
theorem general_orbit_v2_parity_invariant_counterexample :
    GeneralOrbitFrom7 1989379 ∧ IsOdd 1989379 ∧ 5 ∣ 1989380 ∧
      twoValuation 1989380 = 2 := by
  constructor
  · let w : List Nat :=
      [2,1,2,1,1,2,1,1,1,2,2,2,2,1,1,2,0,3,2,1,4,1,2,2,1,4,1,2]
    refine ⟨w, ?_, ?_⟩
    · have hb : wordValidBool w 7 = true := by native_decide
      exact (wordValidBool_eq_true w 7).mp hb
    · native_decide
  · constructor
    · norm_num [IsOdd]
    · constructor
      · norm_num
      · native_decide

/--
Finite exclusion: the counterexample `1989379` is not a legal `t=2`
reset head under the size bound `0 < s0 < 5^(j-1-k)`.

This does not close stage 1.  It only shows that the naive counterexample
is outside the reset-head subfamily, so the t=2 reset branch remains open
as a real proof target instead of being disproved by this orbit state.
-/
theorem counterexample_not_t2_reset_head
    (s0 j k δ : Nat)
    (hRes : 4 * (1989379 + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j)
    (hδ : δ = 1 ∨ δ = 3)
    (hjk : k + 1 ≤ j)
    (hs0 : 0 < s0)
    (hs0lt : s0 < 5 ^ (j - 1 - k)) :
    False := by
  have hj : 1 ≤ j := by omega
  have h5k1 : 5 ^ (k + 1) = 5 * 5 ^ k := by
    have hsucc : k + 1 = Nat.succ k := by omega
    rw [hsucc, Nat.pow_succ, Nat.mul_comm]
  have h5j : 5 ^ j = 5 * 5 ^ (j - 1) := by
    have hsucc : j = Nat.succ (j - 1) := by omega
    rw [hsucc, Nat.pow_succ, Nat.mul_comm]
    rw [Nat.succ_sub_one]
  have hres5 : 1591504 = 5 ^ k * s0 + δ * 5 ^ (j - 1) := by
    rw [h5k1, h5j] at hRes
    norm_num at hRes
    have hmul : 5 * 1591504 = 5 * (5 ^ k * s0 + δ * 5 ^ (j - 1)) := by
      nlinarith
    exact Nat.mul_left_cancel (by norm_num : 0 < 5) hmul
  by_cases hk : k = 0
  · subst k
    rcases hδ with hδ1 | hδ3
    · let P : Nat := 5 ^ (j - 1)
      have hresP : 1591504 = s0 + P := by
        simpa [P, hδ1] using hres5
      have hs0ltP : s0 < P := by
        simpa [P] using hs0lt
      have hPlt : P < 1591504 := by
        nlinarith [hresP, hs0]
      have hgt : 1591504 < 2 * P := by
        nlinarith [hresP, hs0ltP]
      by_cases hge : 9 ≤ j - 1
      · have hPge : 1953125 ≤ P := by
          have h := Nat.pow_le_pow_right (by decide : 0 < 5) hge
          simpa [P] using h
        nlinarith
      · have hle : j - 1 ≤ 8 := by omega
        have hPle : P ≤ 390625 := by
          have h := Nat.pow_le_pow_right (by decide : 0 < 5) hle
          simpa [P] using h
        nlinarith
    · let P : Nat := 5 ^ (j - 1)
      have hresP : 1591504 = s0 + 3 * P := by
        simpa [P, hδ3] using hres5
      have hs0ltP : s0 < P := by
        simpa [P] using hs0lt
      have h3Plt : 3 * P < 1591504 := by
        nlinarith [hresP, hs0]
      have hgt : 1591504 < 4 * P := by
        nlinarith [hresP, hs0ltP]
      by_cases hge : 9 ≤ j - 1
      · have hPge : 1953125 ≤ P := by
          have h := Nat.pow_le_pow_right (by decide : 0 < 5) hge
          simpa [P] using h
        nlinarith
      · have hle : j - 1 ≤ 8 := by omega
        have hPle : P ≤ 390625 := by
          have h := Nat.pow_le_pow_right (by decide : 0 < 5) hle
          simpa [P] using h
        nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hdvd1 : 5 ∣ 5 ^ k * s0 := by
      refine dvd_mul_of_dvd_left ?_ s0
      refine ⟨5 ^ (k - 1), ?_⟩
      have hsucc : k = Nat.succ (k - 1) := by omega
      rw [hsucc, Nat.pow_succ, Nat.mul_comm]
      rw [Nat.succ_sub_one]
    have hdvd2 : 5 ∣ δ * 5 ^ (j - 1) := by
      refine dvd_mul_of_dvd_right ?_ δ
      refine ⟨5 ^ (j - 2), ?_⟩
      have hsucc : j - 1 = Nat.succ (j - 2) := by omega
      rw [hsucc, Nat.pow_succ, Nat.mul_comm]
    have hdvd : 5 ∣ 5 ^ k * s0 + δ * 5 ^ (j - 1) := dvd_add hdvd1 hdvd2
    rw [← hres5] at hdvd
    norm_num at hdvd

/--
Corollary 15.2: the `N` invariant is preserved by one block.

If the next block head has depth `j+L+1` and the next terminal has
5-adic chain length `k+1+L`, then `N = j-k-1` does not change.
-/
theorem n_invariant (j k L : Nat) (hjk : k + 1 ≤ j) :
    (j + L + 1) - (k + 1 + L) - 1 = j - k - 1 := by
  omega

/-- A legal chain step stays positive: `0 < s_m` and exact divisibility
force `0 < s_{m+1} = chainStep s_m U_m δ_m N`. -/
theorem chain_step_pos (s U δ N : Nat) (hs : 0 < s)
    (hdiv : 2 ^ U ∣ s + δ * 5 ^ N) :
    0 < chainStep s U δ N := by
  have hn : 0 < s + δ * 5 ^ N := Nat.add_pos_left hs (δ * 5 ^ N)
  have hle : 2 ^ U ≤ s + δ * 5 ^ N := Nat.le_of_dvd hn hdiv
  have hq : 0 < (s + δ * 5 ^ N) / 2 ^ U := Nat.div_pos hle (by positivity)
  simpa [chainStep] using hq

/--
Lemma 16.1, case 3 (pure `t=2` chain step): if `s_m < 5^N/4`,
`δ_m ∈ {1,3}`, `U_m ≥ 4`, and the step is exact, then the successor
still satisfies `s_{m+1} < 5^N/4`.

This is the size-transfer half of the block-layer recurrence; it does not
by itself close the post-exit coverage gap.
-/
theorem chain_step_lt_fourth
    (N U δ s : Nat)
    (hs : s < 5 ^ N / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (hU : 4 ≤ U)
    (hdiv : 2 ^ U ∣ s + δ * 5 ^ N) :
    (s + δ * 5 ^ N) / 2 ^ U < 5 ^ N / 4 := by
  let q := (s + δ * 5 ^ N) / 2 ^ U
  have h4s : 4 * s < 5 ^ N := by
    have hlt' := (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mp hs
    have hlt'' : 4 * s < 5 ^ N - 3 := by simpa [Nat.mul_comm] using hlt'
    exact lt_of_lt_of_le hlt'' (Nat.sub_le (5 ^ N) 3)
  have hδle : δ ≤ 3 := by rcases hδ with h1 | h3 <;> omega
  have hU16 : 16 ≤ 2 ^ U := by
    have h := pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hU
    simpa using h
  have hqeq : s + δ * 5 ^ N = 2 ^ U * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hdiv).symm
  have h16q : 16 * q ≤ s + δ * 5 ^ N := by
    rw [hqeq]
    exact Nat.mul_le_mul_right q hU16
  have h4sum : 4 * (s + δ * 5 ^ N) < 13 * 5 ^ N := by
    have hδ5 : 4 * δ * 5 ^ N ≤ 12 * 5 ^ N := by nlinarith
    nlinarith [h4s, hδ5]
  have h64q : 64 * q < 13 * 5 ^ N := by
    have h1 : 64 * q ≤ 4 * (s + δ * 5 ^ N) := by nlinarith [h16q]
    exact lt_of_le_of_lt h1 h4sum
  have h4q : 4 * q < 5 ^ N - 3 := by
    by_cases hN3 : 3 ≤ N
    · have h5Nge : 48 ≤ 3 * 5 ^ N := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 5) hN3
        nlinarith
      have h4q3 : 4 * q + 3 < 5 ^ N := by
        nlinarith [h64q, h5Nge]
      omega
    · have hNlt : N < 3 := by omega
      interval_cases N
      · norm_num at hs
      · norm_num at hs h16q ⊢
        omega
      · norm_num at hs h16q ⊢
        omega
  have hq4 : q * 4 < 5 ^ N - 3 := by
    simpa [Nat.mul_comm] using h4q
  simpa [q] using (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mpr hq4

/-- A `t=2` odd hit forces the cleared reset-head form
`rj + 1 = 5^(k+1) * (t0 * 2^(U-2))` and the size bound `t0 < 5^N/4`.
This is the stage-1 algebra isolated for the `GeneralOrbitFrom7 rj`
attack; it does not use reachability of `rj`. -/
theorem stage1_m1_t2_hit_rj_form
    (N s0 U δ j k rj t0 : Nat)
    (hN : N = j - k - 1)
    (hjk : k + 1 ≤ j)
    (hU : 4 ≤ U)
    (hS0lt : s0 < 5 ^ N)
    (hS0lt4 : s0 < 5 ^ N / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (hres : ResetHeadEq s0 j k 2 δ rj)
    (hmod : t0 * 2 ^ U ≡ s0 [MOD 5 ^ N])
    (hHit : OddHit t0 N U δ) :
    rj + 1 = 5 ^ (k + 1) * (t0 * 2 ^ (U - 2)) ∧ t0 < 5 ^ N / 4 := by
  have hred := oddHit_reduces N U δ s0 t0 hδ hS0lt hmod hHit
  have hteq : t0 * 2 ^ U = s0 + δ * 5 ^ N := hred.2
  have hteq' : s0 + δ * 5 ^ N = 2 ^ U * t0 := by
    nlinarith [hteq]
  have hdiv : 2 ^ U ∣ s0 + δ * 5 ^ N := by
    exact ⟨t0, hteq'⟩
  have hlt := chain_step_lt_fourth N U δ s0 hS0lt4 hδ hU hdiv
  have ht0eq : (s0 + δ * 5 ^ N) / 2 ^ U = t0 := by
    rw [hteq']
    exact Nat.mul_div_cancel_left t0 (by positivity : 0 < 2 ^ U)
  have ht0lt : t0 < 5 ^ N / 4 := by
    rw [← ht0eq]
    exact hlt
  rcases hres with h1 | h2
  · rcases h1 with ⟨ht, hδ', hres1⟩
    norm_num at ht
  · rcases h2 with ⟨ht2, hδ2, hres2⟩
    have h5j : 5 ^ j = 5 ^ (k + 1) * 5 ^ N := by
      have hjk' : j = (k + 1) + N := by omega
      rw [hjk', Nat.pow_add]
    have hres2' : 4 * (rj + 1) = 5 ^ (k + 1) * (s0 + δ * 5 ^ N) := by
      rw [h5j] at hres2
      have hre : 5 ^ (k + 1) * s0 + δ * (5 ^ (k + 1) * 5 ^ N) =
          5 ^ (k + 1) * (s0 + δ * 5 ^ N) := by ring
      rwa [hre] at hres2
    have hres2'' : 4 * (rj + 1) = 5 ^ (k + 1) * (t0 * 2 ^ U) := by
      rw [← hteq] at hres2'
      simpa [Nat.mul_assoc] using hres2'
    have hpow4 : 2 ^ U = 4 * 2 ^ (U - 2) := by
      have hUeq : U = 2 + (U - 2) := by omega
      rw [hUeq, Nat.pow_add]
      norm_num
    have hmain : 4 * (rj + 1) = 4 * (5 ^ (k + 1) * (t0 * 2 ^ (U - 2))) := by
      rw [hres2'', hpow4]
      ring
    have hcancel : rj + 1 = 5 ^ (k + 1) * (t0 * 2 ^ (U - 2)) :=
      Nat.mul_left_cancel (by norm_num : 0 < 4) hmain
    exact ⟨hcancel, ht0lt⟩

/-- Along a pure `t=2` chain, every state stays below `5^N/4`: the
single-step bound iterates to all `m ≤ M`. This is the size-transfer
induction used by Lemma 16.1 case 3. -/
theorem chain_all_lt_fourth
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (h0 : s 0 < 5 ^ N / 4)
    (hδ : ∀ m : Nat, m < M → δ m = 1 ∨ δ m = 3)
    (hU : ∀ m : Nat, m < M → 4 ≤ U m)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    ∀ m : Nat, m ≤ M → s m < 5 ^ N / 4 := by
  intro m hm
  induction m with
  | zero => simpa using h0
  | succ m ih =>
      have hm' : m < M := by omega
      have hprev : s m < 5 ^ N / 4 := ih (by omega)
      have hlt := chain_step_lt_fourth N (U m) (δ m) (s m) hprev
        (hδ m hm') (hU m hm') (hdiv m hm')
      have heq : s (m + 1) = chainStep (s m) (U m) (δ m) N :=
        hchain m hm'
      rw [heq]
      exact hlt

/-- Along a pure `t=2` chain, every state is positive and below
`5^N/4`. This bundles the exact size premises used by the
`audit_36_28_*` chain. -/
theorem chain_all_pos_lt_fourth
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (h0pos : 0 < s 0)
    (h0lt : s 0 < 5 ^ N / 4)
    (hδ : ∀ m : Nat, m < M → δ m = 1 ∨ δ m = 3)
    (hU : ∀ m : Nat, m < M → 4 ≤ U m)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    ∀ m : Nat, m ≤ M → 0 < s m ∧ s m < 5 ^ N / 4 := by
  have hlt_all := chain_all_lt_fourth N M s U δ h0lt hδ hU hdiv hchain
  intro m hm
  induction m with
  | zero => exact ⟨h0pos, h0lt⟩
  | succ m ih =>
      have hm' : m < M := by omega
      have hprev := ih (by omega)
      have hpos : 0 < s (m + 1) := by
        have hpos' := chain_step_pos (s m) (U m) (δ m) N hprev.1
          (hdiv m hm')
        rw [hchain m hm']
        exact hpos'
      exact ⟨hpos, hlt_all (m + 1) hm⟩

/-- Corollary 36.28.5 along the whole chain: every step satisfies the
exact integer bound `4·2^(U_m) < (4δ_m+1)·5^N`. -/
theorem chain_audit_36_28_5_all
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (h0pos : 0 < s 0)
    (h0lt : s 0 < 5 ^ N / 4)
    (hδ : ∀ m : Nat, m < M → δ m = 1 ∨ δ m = 3)
    (hU : ∀ m : Nat, m < M → 4 ≤ U m)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    ∀ m : Nat, m < M → 4 * 2 ^ U m < (4 * δ m + 1) * 5 ^ N := by
  have hprem := chain_all_pos_lt_fourth N M s U δ h0pos h0lt hδ hU hdiv hchain
  intro m hm
  have hsz := (hprem m (by omega)).2
  exact audit_36_28_5_exact N (U m) (δ m) (s m) hsz (hδ m hm) (hdiv m hm)

/-- Chain-level collapse: if the first block of a pure `t=2` chain is
not an odd hit, then no later block is an odd hit. This uses the reverse
descent of 36.28.6 and the size premises of 36.28.5. -/
theorem chain_no_hit_of_base
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (h0 : ¬ ChainHit s U δ N 0)
    (hodd : ∀ m : Nat, m ≤ M → IsOdd (s m))
    (hnd5 : ∀ m : Nat, m ≤ M → ¬ 5 ∣ s m)
    (h0pos : 0 < s 0)
    (h0lt : s 0 < 5 ^ N / 4)
    (hδ : ∀ m : Nat, m < M → δ m = 1 ∨ δ m = 3)
    (hU : ∀ m : Nat, m < M → 4 ≤ U m)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    ¬ ChainHit s U δ N M := by
  have hsize := chain_all_pos_lt_fourth N M s U δ h0pos h0lt hδ hU hdiv hchain
  have hdesc : ∀ m : Nat, m ≤ M → ChainHit s U δ N m → ChainHit s U δ N 0 := by
    intro m hm
    induction m with
    | zero => intro h; exact h
    | succ m ih =>
        intro hhit
        have hm_lt : m < M := by omega
        have hprev_size := hsize m (by omega)
        have hcur_size := hsize (m + 1) (by omega)
        have hprev_hit := audit_36_28_6 N (s m) (s (m + 1)) (U m) (δ m)
          (hchain m hm_lt) (hdiv m hm_lt)
          hprev_size.1 hprev_size.2 hcur_size.2
          (hodd (m + 1) (by omega)) (hnd5 (m + 1) (by omega))
        have hprev : ChainHit s U δ N m := by
          simpa [ChainHit] using hprev_hit
        exact ih (by omega) hprev
  intro hM
  exact h0 (hdesc M (by omega) hM)

/-- Conditional closure of the whole pure `t=2` chain: if the general
orbit `M=1` exclusion `Stage1PureT2M1Exclusion` holds, then no chain of
length `M` has an odd hit. -/
theorem pure_t2_chain_no_hit_of_stage1
    (hM1 : Stage1PureT2M1Exclusion)
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (hN : 1 ≤ N)
    (hS0 : 0 < s 0 ∧ s 0 < 5 ^ N ∧ IsOdd (s 0) ∧ ¬ 5 ∣ s 0)
    (h0lt : s 0 < 5 ^ N / 4)
    (hUeven : ∃ L : Nat, U 0 = 2 * L + 2 ∧ 1 ≤ L)
    (hδ0 : δ 0 = 1 ∨ δ 0 = 3)
    (hReach0 : GeneralIsGloballyReachable (s 0) N (δ 0))
    (hodd : ∀ m : Nat, m ≤ M → IsOdd (s m))
    (hnd5 : ∀ m : Nat, m ≤ M → ¬ 5 ∣ s m)
    (hδ : ∀ m : Nat, m < M → δ m = 1 ∨ δ m = 3)
    (hU : ∀ m : Nat, m < M → 4 ≤ U m)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    ¬ ChainHit s U δ N M := by
  have hU0ge : 4 ≤ U 0 := by
    rcases hUeven with ⟨L, hUeq, hLge⟩
    omega
  have h0 : ¬ ChainHit s U δ N 0 := by
    intro hhit
    have hb := hM1 N (s 0) (U 0) (δ 0) hN hS0 hU0ge hUeven hδ0 hReach0
    have hb' : ¬ ChainHit s U δ N 0 := by
      simpa [ChainHit] using hb
    exact hb' hhit
  exact chain_no_hit_of_base N M s U δ h0 hodd hnd5 hS0.1 h0lt
    hδ hU hdiv hchain

/--
Lemma 16.1, case 2 (k=0 macro-chain size bound, non-strict form): from
`s0 = (5^(a+1)*C-7)/2`, `1≤a`, `p+a+2=N`, `0<C`, and
`C ≤ (5^(p+1)+3)/4^a`, we get `s0 < 5^N/4`.

The strict `<` version is not derivable from `C=(5r_p+3)/4^a` and
`r_p<5^p` in general; the non-strict bound plus the `-7` margin is the
provable algebraic core.
-/
theorem s_k0_size_lt_fourth
    (s0 a p C N : Nat)
    (hdef : s0 = (5 ^ (a + 1) * C - 7) / 2)
    (ha : 1 ≤ a)
    (hN : p + a + 2 = N)
    (hCpos : 0 < C)
    (hC_le : C ≤ (5 ^ (p + 1) + 3) / 4 ^ a) :
    s0 < 5 ^ N / 4 := by
  have hpow5a : 25 ≤ 5 ^ (a + 1) := by
    have h2 : 2 ≤ a + 1 := by omega
    have h := Nat.pow_le_pow_right (by decide : 0 < 5) h2
    simpa using h
  have hBge7 : 7 ≤ 5 ^ (a + 1) * C := by
    have hC1 : 1 ≤ C := by omega
    have hprod : 25 * 1 ≤ 5 ^ (a + 1) * C := Nat.mul_le_mul hpow5a hC1
    nlinarith
  have h2le : 2 * s0 ≤ 5 ^ (a + 1) * C - 7 := by
    have h := Nat.mul_div_le (5 ^ (a + 1) * C - 7) 2
    rwa [← hdef] at h
  have h2s : 2 * s0 < 5 ^ (a + 1) * C := by
    have h2 : 2 * s0 + 7 ≤ 5 ^ (a + 1) * C := by omega
    omega
  have h4aC_le : 4 ^ a * C ≤ 5 ^ (p + 1) + 3 := by
    have h := (Nat.le_div_iff_mul_le (by positivity : 0 < 4 ^ a)).mp hC_le
    simpa [Nat.mul_comm] using h
  have hrewrite : 5 ^ (a + 1) * (5 ^ (p + 1) + 3) = 5 ^ N + 3 * 5 ^ (a + 1) := by
    calc
      5 ^ (a + 1) * (5 ^ (p + 1) + 3)
          = 5 ^ (a + 1) * 5 ^ (p + 1) + 5 ^ (a + 1) * 3 := by rw [Nat.mul_add]
      _ = 5 ^ ((a + 1) + (p + 1)) + 5 ^ (a + 1) * 3 := by rw [← Nat.pow_add]
      _ = 5 ^ N + 3 * 5 ^ (a + 1) := by
          rw [show (a + 1) + (p + 1) = N by omega]
          congr 1
          ring
  have hle2 : 4 ^ a * (5 ^ (a + 1) * C) ≤ 5 ^ (a + 1) * (5 ^ (p + 1) + 3) := by
    have h := Nat.mul_le_mul_left (5 ^ (a + 1)) h4aC_le
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hmain : 2 * 4 ^ a * s0 < 5 ^ N + 3 * 5 ^ (a + 1) := by
    have hlt1 : 4 ^ a * (2 * s0) < 4 ^ a * (5 ^ (a + 1) * C) :=
      (Nat.mul_lt_mul_left (by positivity : 0 < 4 ^ a)).2 h2s
    have hlt2 := lt_of_lt_of_le hlt1 hle2
    simpa [hrewrite, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlt2
  have hmain5 : 10 * 4 ^ a * s0 < 5 * 5 ^ N + 15 * 5 ^ (a + 1) := by
    have h5 := (Nat.mul_lt_mul_left (by decide : 0 < 5)).2 hmain
    ring_nf at h5 ⊢
    exact h5
  have hineq2 : 5 * 5 ^ N + 15 * 5 ^ (a + 1) ≤ (2 * 5 ^ N + 35) * 4 ^ a := by
    by_cases ha1 : a = 1
    · subst a
      norm_num
      have hNge : 3 ≤ N := by omega
      have h5N : 125 ≤ 5 ^ N := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 5) hNge
        simpa using h
      nlinarith
    · have ha2 : 2 ≤ a := by omega
      have h4a : 16 ≤ 4 ^ a := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 4) ha2
        simpa using h
      have h5aN : 5 ^ (a + 1) ≤ 5 ^ N := by
        have hle : a + 1 ≤ N := by omega
        exact Nat.pow_le_pow_right (by decide : 0 < 5) hle
      have hmain2 : 5 * 5 ^ N + 15 * 5 ^ (a + 1) ≤ 32 * 5 ^ N := by
        nlinarith [h5aN]
      have h32 : 32 * 5 ^ N ≤ (2 * 5 ^ N + 35) * 4 ^ a := by
        have hle : 32 ≤ 2 * 4 ^ a := by nlinarith [h4a]
        have h1 : 32 * 5 ^ N ≤ 2 * 4 ^ a * 5 ^ N := by
          have h1' := Nat.mul_le_mul_right (5 ^ N) hle
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1'
        have h2 : 2 * 4 ^ a * 5 ^ N ≤ (2 * 5 ^ N + 35) * 4 ^ a := by
          have h2' := Nat.mul_le_mul_right (4 ^ a) (by omega : 2 * 5 ^ N ≤ 2 * 5 ^ N + 35)
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2'
        exact le_trans h1 h2
      exact le_trans hmain2 h32
  have hlt : 10 * 4 ^ a * s0 < (2 * 5 ^ N + 35) * 4 ^ a :=
    lt_of_lt_of_le hmain5 hineq2
  have hlt' : 4 ^ a * (10 * s0) < 4 ^ a * (2 * 5 ^ N + 35) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlt
  have hcancel : 10 * s0 < 2 * 5 ^ N + 35 :=
    (Nat.mul_lt_mul_left (by positivity : 0 < 4 ^ a)).1 hlt'
  have hP : 85 ≤ 5 ^ N := by
    have hNge : 3 ≤ N := by omega
    have h := Nat.pow_le_pow_right (by decide : 0 < 5) hNge
    nlinarith
  have h20 : 20 * s0 < 5 * 5 ^ N - 15 := by
    have h20a : 20 * s0 < 4 * 5 ^ N + 70 := by
      have h2 := (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hcancel
      ring_nf at h2 ⊢
      exact h2
    have hle4 : 4 * 5 ^ N + 70 ≤ 5 * 5 ^ N - 15 := by omega
    exact lt_of_lt_of_le h20a hle4
  have h4s : 4 * s0 < 5 ^ N - 3 := by
    have h5lt : 5 * (4 * s0) < 5 * (5 ^ N - 3) := by
      have hrew1 : 5 * (4 * s0) = 20 * s0 := by ring
      have hrew2 : 5 * (5 ^ N - 3) = 5 * 5 ^ N - 15 := by
        have hP3 : 3 ≤ 5 ^ N := by omega
        omega
      rw [hrew1, hrew2]
      exact h20
    exact (Nat.mul_lt_mul_left (by decide : 0 < 5)).1 h5lt
  have hq4 : s0 * 4 < 5 ^ N - 3 := by
    simpa [Nat.mul_comm] using h4s
  exact (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mpr hq4

/--
Attach the `k=0` algebraic size bound to the macro-chain structure:
if `C = (5*r_p+3)/4^a` and `r_p < 5^p`, then `s0 < 5^N/4`.
-/
theorem s_k0_macro_size_lt_fourth
    (s0 a p rp C N : Nat)
    (hdef : s0 = (5 ^ (a + 1) * C - 7) / 2)
    (hCdef : C = (5 * rp + 3) / 4 ^ a)
    (hrp : rp < 5 ^ p)
    (ha : 1 ≤ a)
    (hN : p + a + 2 = N)
    (hCpos : 0 < C) :
    s0 < 5 ^ N / 4 := by
  apply s_k0_size_lt_fourth s0 a p C N hdef ha hN hCpos
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 4 ^ a)]
  have hle1 : 4 ^ a * C ≤ 5 * rp + 3 := by
    have h := Nat.mul_div_le (5 * rp + 3) (4 ^ a)
    rwa [← hCdef] at h
  have hle2 : 5 * rp + 3 ≤ 5 ^ (p + 1) + 3 := by
    have h5 : 5 * rp < 5 ^ (p + 1) := by
      have h1 : 5 * rp < 5 * 5 ^ p := (Nat.mul_lt_mul_left (by decide : 0 < 5)).2 hrp
      have hpow : 5 ^ (p + 1) = 5 * 5 ^ p := by
        have hsucc : p + 1 = Nat.succ p := by omega
        rw [hsucc, Nat.pow_succ, Nat.mul_comm]
      rwa [← hpow] at h1
    omega
  simpa [Nat.mul_comm] using (le_trans hle1 hle2)

/--
k=0 terminal identity (Int layer): if the even macro endpoint satisfies
`r_i + 1 = 2*5^(a-1)*C`, and two exact `t=1` steps lead to `r2`, then
the terminal odd part `s0 = r2 + 1` satisfies
`2*s0 + 7 = 5^(a+1)*C`, i.e. `s0 = (5^(a+1)*C - 7)/2`.
-/
theorem two_t1_terminal_odd_part
    (s0 C r_i r1 r2 : Int) (a : Nat)
    (ha : 1 ≤ a)
    (hend : r_i + 1 = 2 * (5 ^ (a - 1) : Int) * C)
    (hdiv1 : 2 * r1 = 5 * r_i + 1)
    (hdiv2 : 2 * r2 = 5 * r1 + 1)
    (hdef : s0 = r2 + 1) :
    2 * s0 + 7 = (5 ^ (a + 1) : Int) * C := by
  have hpow : (5 : Int) * (5 ^ (a - 1) : Int) = (5 ^ a : Int) := by
    have hsucc : a = Nat.succ (a - 1) := by omega
    rw [hsucc, pow_succ]
    rw [Nat.succ_sub_one]
    ring
  have hpow2 : (5 : Int) * (5 ^ a : Int) = (5 ^ (a + 1) : Int) := by
    have hsucc : a + 1 = Nat.succ a := by omega
    rw [hsucc, pow_succ]
    ring
  have hend5 : 5 * (r_i + 1) = 5 * (2 * (5 ^ (a - 1) : Int) * C) := by
    rw [hend]
  have hend6 : 5 * r_i + 5 = 2 * (5 ^ a : Int) * C := by
    have h10 : 10 * (5 ^ (a - 1) : Int) = 2 * (5 ^ a : Int) := by
      rw [← hpow]
      ring
    have h5' : 5 * r_i + 5 = 10 * (5 ^ (a - 1) : Int) * C := by
      ring_nf at hend5 ⊢
      exact hend5
    rw [h10] at h5'
    simpa [Int.mul_assoc] using h5'
  have h1 : 5 * r_i + 1 = 2 * ((5 ^ a : Int) * C - 2) := by
    have htmp : 2 * ((5 ^ a : Int) * C - 2) = 2 * (5 ^ a : Int) * C - 4 := by ring
    rw [htmp]
    rw [← hend6]
    ring
  have hr1' : r1 = (5 ^ a : Int) * C - 2 := by
    rw [h1] at hdiv1
    nlinarith
  have h2 : 5 * r1 + 1 = (5 ^ (a + 1) : Int) * C - 9 := by
    rw [hr1']
    have hrew : (5 : Int) * ((5 ^ a : Int) * C - 2) + 1 =
        (5 : Int) * ((5 ^ a : Int) * C) - 9 := by ring
    rw [hrew]
    have hrew2 : (5 : Int) * ((5 ^ a : Int) * C) = (5 ^ (a + 1) : Int) * C := by
      rw [← hpow2]
      ring
    rw [hrew2]
  have hr2' : 2 * r2 = (5 ^ (a + 1) : Int) * C - 9 := by
    rw [h2] at hdiv2
    exact hdiv2
  rw [hdef]
  rw [show 2 * (r2 + 1) + 7 = 2 * r2 + 9 by ring]
  rw [hr2']
  ring

/--
Old-convention algebraic size lemma (kept only as a standalone result):
under `s0 = (5^a*C-1)/2^(2k)` with exact divisibility, `1≤a`, `1≤k`,
`0<C`, `p+a+1=N`, and `4^a*C ≤ 5^(p+1)-2`, one gets
`s0 ≤ 5^N/(4^a*4^k)`.

This is NOT the terminal odd-part identity.  The Lean terminal form is
`4^k*5^k*s0 = 2*5^(a+k-1)*C`, proved in `terminal_odd_part_after_k_t2`;
the strict bound under that identity is handled there and in the docs.
-/
theorem s_k_ge1_size_le
    (s0 a k p C N : Nat)
    (hdef : s0 = (5 ^ a * C - 1) / 2 ^ (2 * k))
    (hdiv : 2 ^ (2 * k) ∣ 5 ^ a * C - 1)
    (ha : 1 ≤ a) (hk : 1 ≤ k) (hCpos : 0 < C)
    (hN : p + a + 1 = N)
    (hC : 4 ^ a * C ≤ 5 ^ (p + 1) - 2) :
    s0 ≤ 5 ^ N / (4 ^ a * 4 ^ k) := by
  have h4k : 4 ^ k = 2 ^ (2 * k) := by
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← Nat.pow_mul]
  have hM0 : 2 ^ (2 * k) * s0 = 5 ^ a * C - 1 := by
    have h := Nat.mul_div_cancel' hdiv
    rwa [← hdef] at h
  have h5a : 1 ≤ 5 ^ a := by
    have hpos : 0 < 5 ^ a := Nat.pow_pos (by decide : 0 < 5)
    omega
  have hge1 : 1 ≤ 5 ^ a * C := by nlinarith [hCpos, h5a]
  have hM1 : 2 ^ (2 * k) * s0 + 1 = 5 ^ a * C := by omega
  have hpow5 : 5 ^ a * 5 ^ (p + 1) = 5 ^ N := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hC' : 4 ^ a * C + 2 ≤ 5 ^ (p + 1) := by
    have h5p : 5 ≤ 5 ^ (p + 1) := by
      have h1 : 1 ≤ p + 1 := by omega
      have h := Nat.pow_le_pow_right (by decide : 0 < 5) h1
      simpa using h
    have hge2 : 2 ≤ 5 ^ (p + 1) := by omega
    omega
  have hC'' : 5 ^ a * (4 ^ a * C) + 2 * 5 ^ a ≤ 5 ^ N := by
    have h := Nat.mul_le_mul_left (5 ^ a) hC'
    rw [hpow5] at h
    simpa [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hM2 : 4 ^ a * 4 ^ k * s0 + 4 ^ a = 5 ^ a * (4 ^ a * C) := by
    have h := congrArg (fun z => 4 ^ a * z) hM1
    rw [← h4k] at h
    simpa [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hmain : 4 ^ a * 4 ^ k * s0 + 4 ^ a + 2 * 5 ^ a ≤ 5 ^ N := by
    nlinarith [hM2, hC'']
  have hle : 4 ^ a * 4 ^ k * s0 ≤ 5 ^ N := by
    have ho : 0 ≤ 4 ^ a := by positivity
    have hi : 0 ≤ 5 ^ a := by positivity
    nlinarith [hmain, ho, hi]
  have hMpos : 0 < 4 ^ a * 4 ^ k := by
    have hpa : 4 ≤ 4 ^ a := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 4) ha
      simpa using h
    have hpk : 4 ≤ 4 ^ k := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 4) hk
      simpa using h
    positivity
  rw [Nat.le_div_iff_mul_le hMpos]
  simpa [Nat.mul_comm] using hle

/--
Corrected macro `C` input bound: from `C=(5r+3)/4^a` and `r<5^p`,
the sharp input bound `4^a*C ≤ 5^(p+1)-2` holds without requiring
exact divisibility of `5r+3` by `4^a`.
-/
theorem macroC_bound_corrected
    (a p r C : Nat)
    (hC : C = (5 * r + 3) / 4 ^ a)
    (hr : r < 5 ^ p) :
    4 ^ a * C ≤ 5 ^ (p + 1) - 2 := by
  have hle1 : 4 ^ a * C ≤ 5 * r + 3 := by
    have h := Nat.mul_div_le (5 * r + 3) (4 ^ a)
    rwa [← hC] at h
  have hle2 : 5 * r + 3 ≤ 5 ^ (p + 1) - 2 := by
    have hrle : r ≤ 5 ^ p - 1 := by omega
    have hpow : 5 ^ (p + 1) = 5 * 5 ^ p := by
      have hsucc : p + 1 = Nat.succ p := by omega
      rw [hsucc, Nat.pow_succ, Nat.mul_comm]
    have hP : 1 ≤ 5 ^ p := by omega
    rw [hpow]
    have hrle' : 5 * r ≤ 5 * (5 ^ p - 1) := Nat.mul_le_mul_left 5 hrle
    have hrew : 5 * (5 ^ p - 1) + 3 = 5 * 5 ^ p - 2 := by omega
    nlinarith [hrle', hrew]
  exact le_trans hle1 hle2

/--
Int-layer closed form for an exact `t=2` chain:
`4^n*(r_n+1) = 5^n*(r_0+1)`.

This is the affine core used in `terminal_odd_part_after_k_t2`; it yields
the Lean terminal identity `4^k*5^k*s0 = 2*5^(a+k-1)*C`, not the old
`s0 = (5^a*C-1)/2^(2k)` convention.
-/
lemma t2_chain_plus_one
    (r : Nat → Int) (n : Nat)
    (hstep : ∀ m : Nat, m < n → 4 * r (m + 1) = 5 * r m + 1) :
    4 ^ n * (r n + 1) = 5 ^ n * (r 0 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep' : ∀ m : Nat, m < n → 4 * r (m + 1) = 5 * r m + 1 := by
        intro m hm
        exact hstep m (by omega)
      have hih := ih hstep'
      have hlast : 4 * r (n + 1) = 5 * r n + 1 := hstep n (by omega)
      have h4 : 4 * (r (n + 1) + 1) = 5 * (r n + 1) := by
        nlinarith [hlast]
      calc
        4 ^ (n + 1) * (r (n + 1) + 1)
            = (4 ^ n * 4) * (r (n + 1) + 1) := by rw [pow_succ]
        _ = 4 ^ n * (4 * (r (n + 1) + 1)) := by ring
        _ = 4 ^ n * (5 * (r n + 1)) := by rw [h4]
        _ = 5 * (4 ^ n * (r n + 1)) := by ring
        _ = 5 * (5 ^ n * (r 0 + 1)) := by rw [hih]
        _ = (5 ^ n * 5) * (r 0 + 1) := by ring
        _ = 5 ^ (n + 1) * (r 0 + 1) := by rw [pow_succ]

/--
Actual terminal odd-part consequence of the macro endpoint identity
plus `k` exact `t=2` steps:
`4^k * 5^k * s0 = 2 * 5^(a+k-1) * C`.

This follows from `r0+1 = 2*5^(a-1)*C` and `r_k+1 = 5^k*s0`.  The old
docs form `(5^a*C-1)/2^(2k)` is not canonical; the markdown has been
updated to this Lean convention.
-/
theorem terminal_odd_part_after_k_t2
    (r : Nat → Int) (s0 C : Int) (a k : Nat)
    (ha : 1 ≤ a)
    (hstart : r 0 + 1 = 2 * (5 ^ (a - 1) : Int) * C)
    (hterm : r k + 1 = (5 ^ k : Int) * s0)
    (hsteps : ∀ m : Nat, m < k → 4 * r (m + 1) = 5 * r m + 1) :
    4 ^ k * (5 ^ k : Int) * s0 = 2 * (5 ^ (a + k - 1) : Int) * C := by
  have hchain := t2_chain_plus_one r k hsteps
  rw [hterm, hstart] at hchain
  have hpow : (5 ^ k : Int) * (5 ^ (a - 1) : Int) = (5 ^ (a + k - 1) : Int) := by
    rw [← pow_add]
    congr 1
    omega
  have hrhs : (5 ^ k : Int) * (2 * (5 ^ (a - 1) : Int) * C) =
      2 * (5 ^ (a + k - 1) : Int) * C := by
    calc
      (5 ^ k : Int) * (2 * (5 ^ (a - 1) : Int) * C)
          = 2 * ((5 ^ k : Int) * (5 ^ (a - 1) : Int)) * C := by ring
      _ = 2 * (5 ^ (a + k - 1) : Int) * C := by rw [hpow]
  rw [hrhs] at hchain
  ring_nf at hchain ⊢
  exact hchain

/-! ## A1 hard-region algebra (a=1, p≥46)

These lemmas formalize the first algebraic equivalences of section 29
of the document.  They do not close statement A1; they isolate the
parts that are already strict algebra before the word-structure
congruence is used.
-/

/-- `q*` in the upper half forces `2*r ≥ 5^p`, i.e. `r ≥ 5^p/2`.
This is the first half of section 22.4 / 29.4. -/
theorem a1_r_lower_of_qstar_upper (W p q A r : Nat)
    (hW : 1 ≤ W)
    (hq : 2 ^ (W - 1) ≤ q)
    (hr : 2 ^ W * r = A + 5 ^ p * q) :
    2 * r ≥ 5 ^ p := by
  have hpow : 2 ^ W = 2 * 2 ^ (W - 1) := by
    have hW' : W = 1 + (W - 1) := by omega
    rw [hW', Nat.pow_add]
    norm_num
  have hqmul : 2 ^ (W - 1) * 5 ^ p ≤ q * 5 ^ p := by
    exact Nat.mul_le_mul_right (5 ^ p) hq
  have hge0 : 2 ^ (W - 1) * 5 ^ p ≤ A + 5 ^ p * q := by
    nlinarith [hqmul]
  have hle' : 2 ^ (W - 1) * (2 * r) = A + 5 ^ p * q := by
    rw [← hr]
    rw [hpow]
    ring
  have hge : 2 ^ (W - 1) * 5 ^ p ≤ 2 ^ (W - 1) * (2 * r) := by
    rw [hle']
    exact hge0
  exact Nat.le_of_mul_le_mul_left hge (by positivity : 0 < 2 ^ (W - 1))

/-- Section 29.1: with `a=1`, the failure equation in terms of `C`
is exactly the cleared `125r+47+8δ·5^(p+3)=2^(U+3)t` form. -/
theorem a1_valuation_form (p U δ C r t : Nat)
    (hCeq : 4 * C = 5 * r + 3)
    (hfail : 4 * (25 * C - 7 + 2 * δ * 5 ^ (p + 3)) =
      2 ^ (U + 3) * t) :
    125 * r + 47 + 8 * δ * 5 ^ (p + 3) =
      2 ^ (U + 3) * t := by
  have h125 : 4 * (25 * C) = 125 * r + 75 := by
    calc
      4 * (25 * C) = 25 * (4 * C) := by ring
      _ = 25 * (5 * r + 3) := by rw [hCeq]
      _ = 125 * r + 75 := by ring
  have hleft : 4 * (25 * C - 7) = 125 * r + 47 := by
    rw [Nat.mul_sub_left_distrib]
    rw [h125]
    omega
  have htail : 4 * (2 * δ * 5 ^ (p + 3)) = 8 * δ * 5 ^ (p + 3) := by
    ring
  have hfail' : 4 * (25 * C - 7) + 4 * (2 * δ * 5 ^ (p + 3)) =
      2 ^ (U + 3) * t := by
    simpa [Nat.mul_add] using hfail
  rw [hleft, htail] at hfail'
  exact hfail'

/--
The current `GeneralOrbitFrom7`-based `Stage1PureT2M1Exclusion` is
false.  The old `(N=5,s0=59,U=4,δ=1)` witness has reset head `3979`,
and `3979` is `GeneralOrbitFrom7`-reachable via an explicit non-full
word.  This is a formal counterexample, not a proof of the corrected
statement; the corrected predicate must use the full accelerated orbit
instead of arbitrary divisor words.
-/
theorem stage1_pure_t2_m1_exclusion_false_of_general_orbit :
    ¬ Stage1PureT2M1Exclusion := by
  intro h
  have h58 : GeneralOrbitFrom7 58 := by
    refine ⟨[2,1,1], ?_, ?_⟩
    · have hb : wordValidBool [2,1,1] 7 = true := by native_decide
      exact (wordValidBool_eq_true [2,1,1] 7).mp hb
    · native_decide
  have h3979 : GeneralOrbitFrom7 3979 := by
    let w : List Nat :=
      [1,0,2,0,2,0,5,0,2,1,5,4,0,5,1,1,4,3,2,1,1,2]
    refine ⟨w, ?_, ?_⟩
    · have hb : wordValidBool w 7 = true := by native_decide
      exact (wordValidBool_eq_true w 7).mp hb
    · native_decide
  have hreset : ResetHeadEq 59 6 0 2 1 3979 := by
    right
    constructor
    · rfl
    · constructor
      · left
        rfl
      · norm_num
  have hreach : GeneralIsGloballyReachable 59 5 1 := by
    refine ⟨6, 0, 58, 3979, 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num [IsOdd]
    · norm_num
    · norm_num
    · exact h58
    · exact hreset
    · norm_num [IsOdd]
    · exact h3979
  have hhit199 : OddHit 199 5 4 1 := by
    norm_num [OddHit, InInterval, IsOdd]
  have ht0 : leastResidue (59 * pow2Inv 4 5) (5 ^ 5) = 199 := by
    native_decide
  have hhit : OddHit (leastResidue (59 * pow2Inv 4 5) (5 ^ 5)) 5 4 1 := by
    rw [ht0]
    exact hhit199
  exact h 5 59 4 1 (by norm_num) (by norm_num [IsOdd]) (by norm_num)
    (⟨1, by norm_num, by norm_num⟩) (Or.inl rfl) hreach hhit

/-- The full accelerated 5x+1 step: divide by the exact 2-adic
valuation, not by an arbitrary divisor. -/
def fullOrbitStep (x : Nat) : Nat :=
  (5 * x + 1) / 2 ^ twoValuation (5 * x + 1)

/-- The deterministic full accelerated orbit starting at `7`. -/
def fullOrbitIter : Nat → Nat
  | 0 => 7
  | n + 1 => fullOrbitStep (fullOrbitIter n)

/-- Reachability in the full accelerated orbit of `7`.  This is the
corrected reachability predicate: `GeneralOrbitFrom7` is too permissive
and makes `Stage1PureT2M1Exclusion` false. -/
def FullOrbitFrom7 (x : Nat) : Prop :=
  ∃ n : Nat, fullOrbitIter n = x

/-- The document's "深度 `j-1` 的真实偶数终端": the previous even
terminal is the even intermediate of the full-orbit step from depth
`j-2` to depth `j-1`. -/
def PreviousTerminalAtDepth (s0 j k r_prev : Nat) : Prop :=
  IsPreviousEvenTerminal s0 j k ∧
    r_prev = (5 * fullOrbitIter (j - 2) + 1) / 2

/-- The corrected general reachability predicate for the stage-1 pure
`t=2` `M=1` exclusion. -/
def FullIsGloballyReachable (s0 N δ : Nat) : Prop :=
  ∃ j k r rj t : Nat,
    k + 1 ≤ j ∧
    N = j - k - 1 ∧
    s0 * 5 ^ k = r + 1 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k) ∧
    FullOrbitFrom7 r ∧
    ResetHeadEq s0 j k t δ rj ∧
    IsOdd rj ∧
    FullOrbitFrom7 rj

/-- The corrected stage-1 pure `t=2` `M=1` exclusion: reachability is
the full accelerated orbit of `7`, not arbitrary divisor words.  This
statement is not yet proved. -/
def Stage1PureT2M1ExclusionFull : Prop :=
  ∀ (N s0 U δ : Nat),
    1 ≤ N →
    (0 < s0 ∧ s0 < 5 ^ N ∧ IsOdd s0 ∧ ¬ 5 ∣ s0) →
    4 ≤ U →
    (∃ L : Nat, U = 2 * L + 2 ∧ 1 ≤ L) →
    δ = 1 ∨ δ = 3 →
    FullIsGloballyReachable s0 N δ →
    ¬ OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ

/-- Corrected full reachability: the previous terminal `r` may be even, so
it must be reachable in the general divisor-word orbit; only the reset head
`rj` must lie on the odd-only full accelerated orbit. -/
def FullIsGloballyReachableCorrected (s0 N δ : Nat) : Prop :=
  ∃ j k r rj t : Nat,
    k + 1 ≤ j ∧
    N = j - k - 1 ∧
    s0 * 5 ^ k = r + 1 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k) ∧
    GeneralOrbitFrom7 r ∧
    ResetHeadEq s0 j k t δ rj ∧
    IsOdd rj ∧
    FullOrbitFrom7 rj

/-- Corrected reset-window reachability with the outer window
parameters `j`, `k0`, `t` fixed.  Unlike
`FullIsGloballyReachableCorrected`, this does not leave `j,k` as fresh
existentials: the previous-terminal equation, the size bound, and the
reset equation all use the exact `j,k0` of the decisive window. -/
def ResetWindowReachability (j k0 t δ s : Nat) : Prop :=
  ∃ r rj : Nat,
    k0 + 1 ≤ j ∧
    s * 5 ^ k0 = r + 1 ∧
    IsOdd s ∧ ¬ 5 ∣ s ∧
    s < 5 ^ (j - 1 - k0) ∧
    GeneralOrbitFrom7 r ∧
    ResetHeadEq s j k0 t δ rj ∧
    IsOdd rj ∧
    FullOrbitFrom7 rj

/-- Corrected C3-tail reset-window reachability: `rj` is the state after
the C3 chain whose head satisfies `x + 1 = 4 * 5^k0 * s0`; the head
`x` is on the full orbit and `rj` is its exact accelerated successor. -/
def ResetWindowReachabilityC3 (j k0 t s0 : Nat) : Prop :=
  ∃ x rj : Nat,
    k0 + 1 ≤ j ∧
    x + 1 = 4 * 5 ^ k0 * s0 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k0) ∧
    FullOrbitFrom7 x ∧
    ResetHeadEqC3 s0 j k0 t rj ∧
    IsOdd rj ∧
    FullOrbitFrom7 rj
/-- A `ResetWindowReachability` witness projects to the generic
`FullIsGloballyReachableCorrected` form.  The converse is deliberately
not claimed: the generic form may use a different `j,k` than the window
parameters. -/
theorem ResetWindowReachability_imp_full_corrected
    (j k0 t δ s : Nat)
    (h : ResetWindowReachability j k0 t δ s) :
    FullIsGloballyReachableCorrected s (j - k0 - 1) δ := by
  rcases h with ⟨r, rj, hk, hprod, hodd, hnd5, hslt, hOrbitR, hReset,
    hOddRj, hOrbitRj⟩
  exact ⟨j, k0, r, rj, t, hk, rfl, hprod, hodd, hnd5, hslt, hOrbitR,
    hReset, hOddRj, hOrbitRj⟩

/-- The corrected stage-1 pure `t=2` `M=1` exclusion, with the previous
terminal in the general orbit and the reset head on the full orbit. -/
def Stage1PureT2M1ExclusionFullCorrected : Prop :=
  ∀ (N s0 U δ : Nat),
    1 ≤ N →
    (0 < s0 ∧ s0 < 5 ^ N ∧ IsOdd s0 ∧ ¬ 5 ∣ s0) →
    4 ≤ U →
    (∃ L : Nat, U = 2 * L + 2 ∧ 1 ≤ L) →
    δ = 1 ∨ δ = 3 →
    FullIsGloballyReachableCorrected s0 N δ →
    ¬ OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ

/-- The full accelerated step maps odd states to odd states. -/
theorem fullOrbitStep_odd (x : Nat) :
    IsOdd (fullOrbitStep x) := by
  have hpos : 0 < 5 * x + 1 := by positivity
  have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos
  have hoddPart : StringFlow.oddPart (5 * x + 1) % 2 = 1 :=
    StringFlow.oddPart_odd_of_pos (5 * x + 1) hpos
  have hv : twoValuation
      (2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1)) =
      twoValuation (5 * x + 1) := by
    exact StringFlow.Lte.twoValuation_mul_two_pow_eq
      (twoValuation (5 * x + 1)) (StringFlow.oddPart (5 * x + 1)) hoddPart
  unfold fullOrbitStep
  rw [hdec, hv]
  have hcancel : 2 ^ twoValuation (5 * x + 1) *
      StringFlow.oddPart (5 * x + 1) /
      2 ^ twoValuation (5 * x + 1) =
      StringFlow.oddPart (5 * x + 1) := by
    exact Nat.mul_div_cancel_left (StringFlow.oddPart (5 * x + 1))
      (by positivity : 0 < 2 ^ twoValuation (5 * x + 1))
  rw [hcancel]
  exact hoddPart

/-- Every state of the full accelerated orbit of `7` is odd. -/
theorem fullOrbitIter_odd : ∀ n : Nat, IsOdd (fullOrbitIter n) := by
  intro n
  induction n with
  | zero => norm_num [fullOrbitIter, IsOdd]
  | succ n ih => exact fullOrbitStep_odd (fullOrbitIter n)

/-- Every state of the full accelerated orbit of `7` is odd. -/
lemma FullOrbitFrom7_odd (x : Nat) (h : FullOrbitFrom7 x) : IsOdd x := by
  rcases h with ⟨n, hn⟩
  rw [← hn]
  exact fullOrbitIter_odd n

/-- The old `FullIsGloballyReachable` is empty: it requires the even
previous terminal `r` to belong to the odd-only full orbit. -/
theorem FullIsGloballyReachable_empty (s0 N δ : Nat) :
    ¬ FullIsGloballyReachable s0 N δ := by
  intro h
  rcases h with ⟨j, k, r, rj, t, hjk, hN, hprod, hodd, hnd5, hs0lt,
    hOrbitR, hReset, hOddRj, hOrbitRj⟩
  have hROdd : IsOdd r := FullOrbitFrom7_odd r hOrbitR
  have hr1mod : (r + 1) % 2 = 0 := by
    change r % 2 = 1 at hROdd
    rw [Nat.add_mod, hROdd]
  have hprodmod : (s0 * 5 ^ k) % 2 = 1 := by
    have h5 : 5 ^ k % 2 = 1 := StringFlow.Lte.five_pow_odd k
    rw [Nat.mul_mod, hodd, h5]
  have hprodmod0 : (s0 * 5 ^ k) % 2 = 0 := by
    rw [hprod]
    exact hr1mod
  have hlt : (s0 * 5 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
  omega

/-- The exact accelerated step is a legal general-orbit step. -/
theorem fullOrbitStep_general (x : Nat) (h : GeneralOrbitFrom7 x) :
    GeneralOrbitFrom7 (fullOrbitStep x) := by
  have hvalid : (5 * x + 1) % 2 ^ twoValuation (5 * x + 1) = 0 := by
    have hpos : 0 < 5 * x + 1 := by positivity
    have hdec := StringFlow.n_eq_two_pow_mul_oddPart (5 * x + 1) hpos
    have hodd : StringFlow.oddPart (5 * x + 1) % 2 = 1 :=
      StringFlow.oddPart_odd_of_pos (5 * x + 1) hpos
    have hv : twoValuation
        (2 ^ twoValuation (5 * x + 1) * StringFlow.oddPart (5 * x + 1)) =
        twoValuation (5 * x + 1) := by
      exact StringFlow.Lte.twoValuation_mul_two_pow_eq
        (twoValuation (5 * x + 1)) (StringFlow.oddPart (5 * x + 1)) hodd
    rw [hdec, hv]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  exact general_orbit_step x (twoValuation (5 * x + 1)) hvalid h

/-- `7` is trivially in the general orbit. -/
theorem general_orbit_seven : GeneralOrbitFrom7 7 := by
  refine ⟨[], ?_, ?_⟩
  · simp [StringFlow.Word.wordValid]
  · rfl

/-- Every finite prefix of the full accelerated orbit stays in the
general orbit. -/
theorem fullOrbitIter_general : ∀ n : Nat,
    GeneralOrbitFrom7 (fullOrbitIter n) := by
  intro n
  induction n with
  | zero => simpa [fullOrbitIter] using general_orbit_seven
  | succ n ih =>
      have hstep := fullOrbitStep_general (fullOrbitIter n) ih
      simpa [fullOrbitIter] using hstep

/-- The full accelerated orbit is a subrelation of the general orbit. -/
theorem FullOrbitFrom7_imp_general (x : Nat) (h : FullOrbitFrom7 x) :
    GeneralOrbitFrom7 x := by
  rcases h with ⟨n, hx⟩
  have hgen := fullOrbitIter_general n
  simpa [hx] using hgen

/-- The full-orbit reachability predicate implies the general one. -/
theorem FullIsGloballyReachable_imp_general (s0 N δ : Nat)
    (h : FullIsGloballyReachable s0 N δ) :
    GeneralIsGloballyReachable s0 N δ := by
  rcases h with ⟨j, k, r, rj, t, hjk, hN, hprod, hodd, hnd5, hs0lt,
    hOrbitR, hReset, hOddRj, hOrbitRj⟩
  refine ⟨j, k, r, rj, t, hjk, hN, hprod, hodd, hnd5, hs0lt,
    FullOrbitFrom7_imp_general r hOrbitR, hReset, hOddRj,
    FullOrbitFrom7_imp_general rj hOrbitRj⟩

end S6Audit
