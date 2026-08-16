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

/-- A PMI-B bad prefix length in a cycle word: the prefix of length
`j` has weight at least `j·log2 5`, so `5^j <= 2^W_j`.  This predicate
is withdrawn as the hfail `j` source (see the 13-cycle shadow note
below); the hfail rank target now takes `j` from real orbit prefixes. -/
def badPrefixAt (P : Nat) (w : List Nat) (j : Nat) : Prop :=
  1 ≤ j ∧ j < P ∧
    5 ^ j ≤ 2 ^ StringFlow.wordWeight (w.take j)

/-- A word depth `j` is a real orbit prefix of `w` from `m`: the full
orbit from `7` passes through the prefix state at depth `n0 + j`.  This
is the internal source of `j` for the rank-bound step inside the
no-cycle proof: it explicitly uses `hstart`, so the derivation cannot
silently apply to arbitrary cycle words such as the 13 shadow.  It is
an internal tool, not an open target by itself. -/
def realPrefixDepth (m : Nat) (w : List Nat) (j : Nat) : Prop :=
  ∃ n0 : Nat,
    S6Audit.fullOrbitIter n0 = m ∧
    S6Audit.fullOrbitIter (n0 + j) =
      StringFlow.Word.wordOrbit (w.take j) m

/-- Every prefix of a `CycleQb8Input` word is a real orbit prefix:
`hstart` supplies the occurrence index `n0`, and the exact orbit step
data gives `fullOrbitIter (n0 + j) = wordOrbit (w.take j) m`. -/
theorem realPrefixDepth_of_cycleQb8Input
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j ≤ w.length) :
    realPrefixDepth m w j := by
  rcases h.hstart with ⟨n0, hn0⟩
  exact ⟨n0, hn0,
    StringFlow.RealOrbitLocalLemma.cycleQb8Input_prefix_fullOrbitIter_of_start
      h n0 hn0 j hj⟩

/-- Exact PMI frame under the concrete `hcycle` occurrence: the
selected 7-cycle word satisfies
`aTotal5 P (fun j => w.getI j) = 5 * m * (2 ^ S - 5 ^ P)`.  This is the
exact algebraic intermediate of the main-theorem derivation; it
explicitly uses `hcycle` and remains true for the 13 shadow
(`aTotal5 = 195 = 5*13*(2^7-5^3)`), so the contradiction cannot come
from the frame alone. -/
theorem cycleQb8Input_aTotal5_equation
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    StringFlow.PMI.aTotal5 P (fun j => w.getI j) =
      5 * m * (2 ^ S - 5 ^ P) := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, hS, _hrise, _hc3⟩
  have hclosed : StringFlow.Word.wordOrbit (CycleBridge.cycleWord c p)
      (StringFlow.fiveXPlusOneOrbit 7 c) =
      StringFlow.fiveXPlusOneOrbit 7 c := by
    simpa [hw, hm] using h.hclosed
  have halg := CycleBridge.cycleWord_pmi_algebraic c p hclosed
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hS' : S = CycleBridge.cycleWordTotalWeight c p := by
    dsimp [CycleBridge.cycleWordTotalWeight]
    exact hS
  have hstep : CycleBridge.cycleWordStepAt c p = fun j => w.getI j := by
    funext j
    dsimp [CycleBridge.cycleWordStepAt]
    rw [hw]
  rw [← hS'] at halg
  rw [← hm] at halg
  rw [hstep] at halg
  rw [← hP] at halg
  exact halg

/-- The concrete occurrence index supplied by `hcycle`: `m` is the
`c`-th state of the full orbit from `7`, and every prefix state of the
cycle word occurs at the corresponding shifted orbit depth.  This is
the hcycle-specific strengthening of `realPrefixDepth_of_cycleQb8Input`;
it uses `hcycle`'s `c`, not the arbitrary `hstart` witness. -/
theorem cycleQb8Input_prefix_fullOrbitIter_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j ≤ w.length) :
    ∃ c : Nat,
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      S6Audit.fullOrbitIter (c + j) =
        StringFlow.Word.wordOrbit (w.take j) m := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, _hw, hm, _hS, _hrise, _hc3⟩
  refine ⟨c, hm, ?_⟩
  exact StringFlow.RealOrbitLocalLemma.cycleQb8Input_prefix_fullOrbitIter_of_start
    h c (by
      rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
      exact hm.symm) j hj

/-- The selected 7-cycle word's prefix states are exactly the concrete
orbit states at the shifted indices: `wordOrbit (w.take j) m =
fiveXPlusOneOrbit 7 (c+j)`.  This is the concrete 2-adic/5-adic
structure of the hcycle occurrence used by the internal rank-bound
step. -/
theorem cycleQb8Input_prefix_state_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j ≤ w.length) :
    ∃ c : Nat,
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      StringFlow.Word.wordOrbit (w.take j) m =
        StringFlow.fiveXPlusOneOrbit 7 (c + j) := by
  rcases cycleQb8Input_prefix_fullOrbitIter_of_hcycle h j hj with
    ⟨c, hm, hiter⟩
  refine ⟨c, hm, ?_⟩
  rw [← hiter]
  exact CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit (c + j)

/-- The exact step weights of the selected 7-cycle word are the
2-adic valuations at the concrete orbit indices: `w.getI k =
twoValuation (5 * fiveXPlusOneOrbit 7 (c+k) + 1)`.  This is the
cycleWord weight-sequence content of `hcycle`. -/
theorem cycleQb8Input_step_weight_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (k : Nat) (hk : k < w.length) :
    ∃ c : Nat,
      w.getI k = S6Audit.twoValuation
        (5 * StringFlow.fiveXPlusOneOrbit 7 (c + k) + 1) := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, _hm, _hS, _hrise, _hc3⟩
  refine ⟨c, ?_⟩
  have hlen : w.length = p := by
    rw [hw, CycleBridge.cycleWord_length]
  have hk' : k < p := by
    rw [← hlen]
    exact hk
  rw [hw]
  exact CycleBridge.cycleWord_getI_eq c p k hk'

/-- Concrete orbit size bound under `hcycle`: every prefix state of
the selected 7-cycle word is below `5^(c+j)` once the shifted index is
at least two.  This is the 5-adic size half of the concrete structure,
the last provable ingredient of the current toolkit. -/
theorem cycleQb8Input_state_bound_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j ≤ w.length) :
    ∃ c : Nat,
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      (2 ≤ c + j → StringFlow.Word.wordOrbit (w.take j) m < 5 ^ (c + j)) := by
  rcases cycleQb8Input_prefix_state_of_hcycle h j hj with ⟨c, hm, hstate⟩
  refine ⟨c, hm, ?_⟩
  intro hge
  rw [hstate]
  exact CycleBridge.fiveXPlusOneOrbit_lt_five_pow (c + j) hge

/-- The cycle word entry at depth `i` is the exact accelerated orbit
step weight at the concrete orbit index `c+i`. -/
theorem cycleWord_step_orbitWeight
    (c p i : Nat) (hi : i < p) :
    S6Audit.orbitStepWeight (c + i) =
      (CycleBridge.cycleWord c p).getI i := by
  unfold S6Audit.orbitStepWeight
  have hpre : StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take i)
      (StringFlow.fiveXPlusOneOrbit 7 c) =
      StringFlow.fiveXPlusOneOrbit 7 (c + i) :=
    CycleBridge.cycleWord_prefix_orbit_eq c p i (le_of_lt hi)
  have hstep := CycleBridge.cycleWord_step_exact c p i hi
  rw [hpre] at hstep
  simpa [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] using hstep

/-- Exact rank automaton for a `t=2` step of the concrete cycle word:
the current state has rank at least three and the next state loses
exactly two. -/
theorem t2_step_rank_ge_three_of_word
    (c p i : Nat) (hi : i < p)
    (hw : (CycleBridge.cycleWord c p).getI i = 2) :
    3 ≤ twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1) ∧
    twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i + 1) + 1) =
      twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1) - 2 := by
  have hweight : S6Audit.orbitStepWeight (c + i) = 2 := by
    rw [cycleWord_step_orbitWeight c p i hi, hw]
  let n := c + i
  have hodd : S6Audit.IsOdd (StringFlow.fiveXPlusOneOrbit 7 n) :=
    CycleBridge.fiveXPlusOneOrbit_odd_7 n
  have hpos1 : 0 < StringFlow.fiveXPlusOneOrbit 7 n + 1 := by positivity
  have hrank_pos : 1 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) := by
    have heven : (StringFlow.fiveXPlusOneOrbit 7 n + 1) % 2 = 0 := by
      have hmod : StringFlow.fiveXPlusOneOrbit 7 n % 2 = 1 := hodd
      rw [Nat.add_mod, hmod]
    have hdvd : 2 ∣ StringFlow.fiveXPlusOneOrbit 7 n + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr heven
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) 1 hpos1).mpr hdvd
  have hrank_ge : 3 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) := by
    by_cases hge3 : 3 ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 n + 1)
    · exact hge3
    · exfalso
      have hle2 : twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 n + 1) ≤ 2 := by omega
      have hcases : twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 n + 1) = 1 ∨
          twoValuation (StringFlow.fiveXPlusOneOrbit 7 n + 1) = 2 := by omega
      rcases hcases with h1 | h2
      · have hw1 : S6Audit.orbitStepWeight n = 1 := by
          have hr1 : twoValuation (S6Audit.fullOrbitIter n + 1) = 1 := by
            rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
            exact h1
          exact RealOrbitLocalLemma.orbitStepWeight_of_rank_one n hr1
        have hw2 : S6Audit.orbitStepWeight n = 2 := by simpa [n] using hweight
        omega
      · have hv : 1 ≤ twoValuation
            (5 * StringFlow.oddPart
              (StringFlow.fiveXPlusOneOrbit 7 n + 1) - 1) :=
          StringFlow.RealOrbitLocalLemma.twoValuation_five_oddPart_sub_one_ge_one
            (StringFlow.fiveXPlusOneOrbit 7 n + 1) (by positivity)
        have hr2 : twoValuation (S6Audit.fullOrbitIter n + 1) = 2 := by
          rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
          exact h2
        have hstep' : S6Audit.orbitStepWeight n = 2 + twoValuation
            (5 * StringFlow.oddPart
              (StringFlow.fiveXPlusOneOrbit 7 n + 1) - 1) := by
          have h := RealOrbitLocalLemma.orbitStepWeight_of_rank_two n hr2
          rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] at h
          exact h
        have hw2 : S6Audit.orbitStepWeight n = 2 := by simpa [n] using hweight
        rw [hstep'] at hw2
        omega
  have hdrop := RealOrbitLocalLemma.fullOrbitIter_rank_drop_two (c + i) (by
    simpa [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] using hrank_ge)
  constructor
  · simpa [n] using hrank_ge
  · simpa [Nat.add_assoc, CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
      using hdrop

/-- Exact rank automaton for a `t=1` step of the concrete cycle word:
the current state has rank exactly one. -/
theorem t1_step_rank_eq_one
    (c p i : Nat) (hi : i < p)
    (hw : (CycleBridge.cycleWord c p).getI i = 1) :
    twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1) = 1 := by
  have hweight : S6Audit.orbitStepWeight (c + i) = 1 := by
    rw [cycleWord_step_orbitWeight c p i hi, hw]
  let n := c + i
  have hodd : S6Audit.IsOdd (StringFlow.fiveXPlusOneOrbit 7 n) :=
    CycleBridge.fiveXPlusOneOrbit_odd_7 n
  have hpos1 : 0 < StringFlow.fiveXPlusOneOrbit 7 n + 1 := by positivity
  have hrank_pos : 1 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) := by
    have heven : (StringFlow.fiveXPlusOneOrbit 7 n + 1) % 2 = 0 := by
      have hmod : StringFlow.fiveXPlusOneOrbit 7 n % 2 = 1 := hodd
      rw [Nat.add_mod, hmod]
    have hdvd : 2 ∣ StringFlow.fiveXPlusOneOrbit 7 n + 1 :=
      Nat.dvd_iff_mod_eq_zero.mpr heven
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) 1 hpos1).mpr hdvd
  by_contra hne
  have hge2 : 2 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) := by
    by_contra hnot2
    have hlt2 : twoValuation (StringFlow.fiveXPlusOneOrbit 7 n + 1) < 2 :=
      Nat.lt_of_not_ge hnot2
    have hle1 : twoValuation (StringFlow.fiveXPlusOneOrbit 7 n + 1) ≤ 1 :=
      Nat.le_of_lt_succ hlt2
    exact hne (le_antisymm hle1 hrank_pos)
  by_cases h2 : twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 n + 1) = 2
  · have hr2 : twoValuation (S6Audit.fullOrbitIter n + 1) = 2 := by
      rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
      exact h2
    have hstep' : S6Audit.orbitStepWeight n = 2 + twoValuation
        (5 * StringFlow.oddPart
          (StringFlow.fiveXPlusOneOrbit 7 n + 1) - 1) := by
      have h := RealOrbitLocalLemma.orbitStepWeight_of_rank_two n hr2
      rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] at h
      exact h
    have hw1 : S6Audit.orbitStepWeight n = 1 := by simpa [n] using hweight
    rw [hstep'] at hw1
    have hv : 1 ≤ twoValuation
        (5 * StringFlow.oddPart
          (StringFlow.fiveXPlusOneOrbit 7 n + 1) - 1) :=
      StringFlow.RealOrbitLocalLemma.twoValuation_five_oddPart_sub_one_ge_one
        (StringFlow.fiveXPlusOneOrbit 7 n + 1) (by positivity)
    omega
  · have hge3 : 3 ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 n + 1) := by omega
    have hrank3 : 3 ≤ twoValuation (S6Audit.fullOrbitIter n + 1) := by
      simpa [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] using hge3
    have hw2 : S6Audit.orbitStepWeight n = 2 :=
      RealOrbitLocalLemma.orbitStepWeight_of_rank_ge_three n hrank3
    have hw1 : S6Audit.orbitStepWeight n = 1 := by simpa [n] using hweight
    omega

/-- Exact rank automaton for a C3 step of the concrete cycle word:
the current state has rank exactly two. -/
theorem c3_step_rank_eq_two
    (c p i : Nat) (hi : i < p)
    (hw : 3 ≤ (CycleBridge.cycleWord c p).getI i) :
    twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1) = 2 := by
  have hweight : 3 ≤ S6Audit.orbitStepWeight (c + i) := by
    rw [cycleWord_step_orbitWeight c p i hi]
    exact hw
  have hc3 : 3 ≤ twoValuation
      (5 * StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1) := by
    simpa [S6Audit.orbitStepWeight,
      CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit] using hweight
  exact StringFlow.RealOrbitLocalLemma.state_rank_eq_two_of_outgoing_c3
    (StringFlow.fiveXPlusOneOrbit 7 (c + i))
    (CycleBridge.fiveXPlusOneOrbit_odd_7 (c + i))
    hc3

/-- Generic rank automaton: rank-two state has outgoing weight at
least three. -/
lemma step_weight_ge_three_of_rank_two (r : Nat) (_hodd : S6Audit.IsOdd r)
    (hrank : twoValuation (r + 1) = 2) :
    3 ≤ twoValuation (5 * r + 1) := by
  let a := r + 1
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ 2 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart a hpos
    rw [hrank] at h
    simpa [a] using h
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hcpos : 0 < c := by
    by_contra hnot
    have hz : c = 0 := by omega
    rw [hz] at hcodd
    norm_num at hcodd
  have hr : r = 4 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hnum : 5 * r + 1 = 4 * (5 * c - 1) := by
    rw [hr]
    have hcge1 : 1 ≤ c := by omega
    omega
  have hcdec : c = 2 * (c / 2) + 1 := by
    have h := (Nat.div_add_mod c 2).symm
    rw [hcodd] at h
    omega
  have hbpos : 0 < 5 * c - 1 := by
    rw [hcdec]
    omega
  have hbeven : (5 * c - 1) % 2 = 0 := by
    rw [hcdec]
    omega
  have hdvd : 2 ∣ 5 * c - 1 := Nat.dvd_iff_mod_eq_zero.mpr hbeven
  have hge1 : 1 ≤ twoValuation (5 * c - 1) :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * c - 1) 1 hbpos).mpr hdvd
  have hval := StringFlow.Lte.twoValuation_mul_two_pow 2 (5 * c - 1) hbpos
  have hv4 : twoValuation (4 * (5 * c - 1)) = 2 + twoValuation (5 * c - 1) := by
    have h4 : (2 ^ 2 : Nat) = 4 := by norm_num
    simpa [h4, Nat.mul_comm] using hval
  rw [hnum, hv4]
  omega

/-- Generic rank automaton: rank at least three has outgoing weight
exactly two. -/
lemma step_weight_eq_two_of_rank_ge_three (r : Nat) (_hodd : S6Audit.IsOdd r)
    (hrank : 3 ≤ twoValuation (r + 1)) :
    twoValuation (5 * r + 1) = 2 := by
  let a := r + 1
  let p := twoValuation a
  let c := StringFlow.oddPart a
  have hpos : 0 < a := by dsimp [a]; positivity
  have hdec : a = 2 ^ p * c := by
    dsimp [p, c]
    exact StringFlow.n_eq_two_pow_mul_oddPart a hpos
  have hf : r = 2 ^ p * c - 1 := by
    dsimp [a] at hdec
    omega
  have hcodd : c % 2 = 1 := by
    dsimp [c]
    exact StringFlow.oddPart_odd_of_pos a hpos
  have hcpos : 0 < c := by
    by_contra hnot
    have hz : c = 0 := by omega
    rw [hz] at hcodd
    norm_num at hcodd
  have hp3 : 3 ≤ p := by simpa [p, a] using hrank
  have hpow : 2 ^ p = 4 * 2 ^ (p - 2) := by
    have hp_eq : p = (p - 2) + 2 := by omega
    calc
      2 ^ p = 2 ^ ((p - 2) + 2) := by
        conv_lhs => rw [hp_eq]
      _ = 2 ^ (p - 2) * 2 ^ 2 := by rw [Nat.pow_add]
      _ = 4 * 2 ^ (p - 2) := by ring
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
    have hposY : 0 < 5 * 2 ^ (p - 2) * c := by
      have hpowpos : 0 < 2 ^ (p - 2) := Nat.pow_pos (by decide : 0 < 2)
      have h5pos : 0 < 5 * 2 ^ (p - 2) := Nat.mul_pos (by norm_num) hpowpos
      exact Nat.mul_pos h5pos hcpos
    have hdpos : 0 < d := by nlinarith [hd, hposY]
    rw [hd]
    have hdecomp : 2 * d - 1 = 2 * (d - 1) + 1 := by omega
    rw [hdecomp, Nat.add_mod]
    norm_num
  have hfac : 5 * r + 1 = 4 * Y := by
    dsimp [Y]
    let d := 2 ^ (p - 2) * c
    have hf' : r = 4 * d - 1 := by
      rw [hf, hpow]
      dsimp [d]
      ring_nf
    have hnum' : 5 * (4 * d - 1) + 1 = 4 * (5 * d - 1) := by
      have hdpos : 0 < d := by
        dsimp [d]
        exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
      omega
    rw [hf', hnum']
    dsimp [d]
    ring_nf
  have hvalY := StringFlow.Lte.twoValuation_mul_two_pow_eq 2 Y hYodd
  rw [hfac]
  change twoValuation (2 ^ 2 * Y) = 2
  exact hvalY

/-- Generic rank automaton: rank-one state has outgoing weight exactly
one. -/
lemma step_weight_one_of_rank_one (r : Nat) (_hodd : S6Audit.IsOdd r)
    (hrank : twoValuation (r + 1) = 1) :
    twoValuation (5 * r + 1) = 1 := by
  let a := r + 1
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
  have hcpos : 0 < c := by
    by_contra hnot
    have hz : c = 0 := by omega
    rw [hz] at hcodd
    norm_num at hcodd
  have hcdec : c = 2 * (c / 2) + 1 := by
    have h := (Nat.div_add_mod c 2).symm
    rw [hcodd] at h
    omega
  have hf : r = 2 * c - 1 := by
    dsimp [a] at hdec
    omega
  have hnum : 5 * r + 1 = 2 * (5 * c - 2) := by
    rw [hf, hcdec]
    omega
  have hbodd : (5 * c - 2) % 2 = 1 := by
    rw [hcdec]
    omega
  have hbpos : 0 < 5 * c - 2 := by
    rw [hcdec]
    omega
  have hval := StringFlow.Lte.twoValuation_mul_two_pow_eq 1 (5 * c - 2) hbodd
  rw [hnum]
  change twoValuation (2 ^ 1 * (5 * c - 2)) = 1
  exact hval

/-- Generic rank automaton: outgoing weight two forces rank at least
three. -/
lemma rank_ge_three_of_step_weight_two (r : Nat) (hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 2) :
    3 ≤ twoValuation (r + 1) := by
  have hpos : 0 < r + 1 := by positivity
  have hge1 : 1 ≤ twoValuation (r + 1) := by
    have heven : (r + 1) % 2 = 0 := by
      have hmod : r % 2 = 1 := hodd
      rw [Nat.add_mod, hmod]
    have hdvd : 2 ∣ r + 1 := Nat.dvd_iff_mod_eq_zero.mpr heven
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (r + 1) 1 hpos).mpr hdvd
  by_cases h1 : twoValuation (r + 1) = 1
  · exfalso
    have hw1 : twoValuation (5 * r + 1) = 1 :=
      step_weight_one_of_rank_one r hodd h1
    omega
  · by_cases h2 : twoValuation (r + 1) = 2
    · exfalso
      have hw3 : 3 ≤ twoValuation (5 * r + 1) :=
        step_weight_ge_three_of_rank_two r hodd h2
      omega
    · have hge3 : 3 ≤ twoValuation (r + 1) := by omega
      exact hge3

/-- Generic rank automaton: outgoing weight one forces rank exactly
one. -/
lemma rank_one_of_step_weight_one (r : Nat) (hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 1) :
    twoValuation (r + 1) = 1 := by
  have hpos : 0 < r + 1 := by positivity
  have hge1 : 1 ≤ twoValuation (r + 1) := by
    have heven : (r + 1) % 2 = 0 := by
      have hmod : r % 2 = 1 := hodd
      rw [Nat.add_mod, hmod]
    have hdvd : 2 ∣ r + 1 := Nat.dvd_iff_mod_eq_zero.mpr heven
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (r + 1) 1 hpos).mpr hdvd
  by_cases h2 : twoValuation (r + 1) = 2
  · exfalso
    have hw3 : 3 ≤ twoValuation (5 * r + 1) :=
      step_weight_ge_three_of_rank_two r hodd h2
    omega
  · by_cases hge3 : 3 ≤ twoValuation (r + 1)
    · exfalso
      have hw2 : twoValuation (5 * r + 1) = 2 :=
        step_weight_eq_two_of_rank_ge_three r hodd hge3
      omega
    · have hle2 : twoValuation (r + 1) ≤ 2 := by omega
      have heq : twoValuation (r + 1) = 1 := by omega
      exact heq

/-- A `t=1` step never lowers the rank of an odd state. -/
lemma rank_le_next_of_step_one (r : Nat) (hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 1) :
    twoValuation (r + 1) ≤
      twoValuation (CycleBridge.riseStep r 1 + 1) := by
  have hr1 : twoValuation (r + 1) = 1 := rank_one_of_step_weight_one r hodd h
  let c := StringFlow.oddPart (r + 1)
  have hpos : 0 < r + 1 := by positivity
  have hcodd : c % 2 = 1 := StringFlow.oddPart_odd_of_pos (r + 1) hpos
  have hcpos : 0 < c := by
    by_contra hnot
    have hz : c = 0 := by omega
    rw [hz] at hcodd
    norm_num at hcodd
  have hdec : r + 1 = 2 * c := by
    dsimp [c]
    have h := StringFlow.n_eq_two_pow_mul_oddPart (r + 1) hpos
    rw [hr1] at h
    simpa [Nat.pow_one] using h
  have hr : r = 2 * c - 1 := by omega
  have hstep : CycleBridge.riseStep r 1 + 1 = 5 * c - 1 := by
    unfold CycleBridge.riseStep
    rw [hr]
    have hcge1 : 1 ≤ c := by omega
    omega
  rw [hstep]
  have hge : 1 ≤ twoValuation (5 * c - 1) :=
    StringFlow.RealOrbitLocalLemma.twoValuation_five_oddPart_sub_one_ge_one
      (r + 1) hpos
  omega

/-- The recharge contributed by a `t=1` step is exactly the rank
increase. -/
lemma riseCharge_eq_of_step_one (r : Nat) (hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 1) :
    CycleBridge.riseCharge r 1 =
      twoValuation (CycleBridge.riseStep r 1 + 1) -
        twoValuation (r + 1) := by
  have hle := rank_le_next_of_step_one r hodd h
  unfold CycleBridge.riseCharge
  simp

/-- `t=1` successors of odd exact states stay odd. -/
lemma riseStep_odd_of_step_one (r : Nat) (_hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 1) :
    S6Audit.IsOdd (CycleBridge.riseStep r 1) := by
  have hdvd : 2 ^ 1 ∣ 5 * r + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * r + 1) 1
      (by positivity)).mp (by omega)
  have hstep : 2 ^ 1 * CycleBridge.riseStep r 1 = 5 * r + 1 := by
    unfold CycleBridge.riseStep
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd
  exact StringFlow.RealOrbitLocalLemma.odd_of_twoValuation_mul_eq_five_mul_add_one
    r 1 (CycleBridge.riseStep r 1) h hstep

/-- `t=2` successors of odd exact states stay odd. -/
lemma riseStep_odd_of_step_two (r : Nat) (_hodd : S6Audit.IsOdd r)
    (h : twoValuation (5 * r + 1) = 2) :
    S6Audit.IsOdd (CycleBridge.riseStep r 2) := by
  have hdvd : 2 ^ 2 ∣ 5 * r + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * r + 1) 2
      (by positivity)).mp (by omega)
  have hstep : 2 ^ 2 * CycleBridge.riseStep r 2 = 5 * r + 1 := by
    unfold CycleBridge.riseStep
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd
  exact StringFlow.RealOrbitLocalLemma.odd_of_twoValuation_mul_eq_five_mul_add_one
    r 2 (CycleBridge.riseStep r 2) h hstep

/-- Rank-accounting invariant along a rise word:
`charge + initialRank = 2·countTwo + finalRank`.  This is the exact
source of the recovery: every `t=2` step spends two, every `t=1` step
records its nonnegative gain. -/
theorem riseChargeSum_add_initial_eq_two_mul_countTwo_add_endpoint
    (r0 : Nat) (ts : List Nat)
    (hodd : S6Audit.IsOdd r0)
    (hok : ∀ t ∈ ts, t = 1 ∨ t = 2)
    (hexact : ∀ k, k < ts.length →
      twoValuation (5 * CycleBridge.riseRun r0 (ts.take k) + 1) = ts.getI k) :
    CycleBridge.riseChargeSum r0 ts + twoValuation (r0 + 1) =
      2 * CycleBridge.riseCountTwo ts +
        twoValuation (CycleBridge.riseRun r0 ts + 1) := by
  induction ts generalizing r0 with
  | nil => simp [CycleBridge.riseRun, CycleBridge.riseCountTwo,
      CycleBridge.riseChargeSum]
  | cons t ts ih =>
      rcases hok t (by simp) with ht1 | ht2
      · subst t
        let r1 := CycleBridge.riseStep r0 1
        have hfirst : twoValuation (5 * r0 + 1) = 1 := by
          have h0 := hexact 0 (by simp)
          simpa [CycleBridge.riseRun] using h0
        have hodd1 : S6Audit.IsOdd r1 := by
          dsimp [r1]
          exact riseStep_odd_of_step_one r0 hodd hfirst
        have htail := ih r1 hodd1
          (fun u hu => hok u (by simp [hu]))
          (fun k hk => by
            have hk' : k + 1 < (1 :: ts).length := by simp [hk]
            have h := hexact (k + 1) hk'
            have hrun : CycleBridge.riseRun r0 ((1 :: ts).take (k + 1)) =
                CycleBridge.riseRun r1 (ts.take k) := by
              rw [List.take_cons (by omega)]
              simp [CycleBridge.riseRun, CycleBridge.riseStep, r1]
            have hidx : (1 :: ts).getI (k + 1) = ts.getI k := by
              rw [List.getI_cons_succ]
            rwa [hrun, hidx] at h)
        have hcharge : CycleBridge.riseCharge r0 1 + twoValuation (r0 + 1) =
            twoValuation (r1 + 1) := by
          dsimp [r1]
          have hc := riseCharge_eq_of_step_one r0 hodd hfirst
          have hle := rank_le_next_of_step_one r0 hodd hfirst
          omega
        have hrun : CycleBridge.riseRun r0 (1 :: ts) = CycleBridge.riseRun r1 ts := by
          simp [CycleBridge.riseRun, CycleBridge.riseStep, r1]
        simp [CycleBridge.riseChargeSum, CycleBridge.riseCountTwo, hrun]
        dsimp [r1]
        have htail' : CycleBridge.riseChargeSum (CycleBridge.riseStep r0 1) ts +
              twoValuation (CycleBridge.riseStep r0 1 + 1) =
            2 * CycleBridge.riseCountTwo ts +
              twoValuation (CycleBridge.riseRun (CycleBridge.riseStep r0 1) ts + 1) := by
          simpa [r1] using htail
        have hcharge' : CycleBridge.riseCharge r0 1 + twoValuation (r0 + 1) =
              twoValuation (CycleBridge.riseStep r0 1 + 1) := by
          simpa [r1] using hcharge
        omega
      · subst t
        let r1 := CycleBridge.riseStep r0 2
        have hfirst : twoValuation (5 * r0 + 1) = 2 := by
          have h0 := hexact 0 (by simp)
          simpa [CycleBridge.riseRun] using h0
        have hodd1 : S6Audit.IsOdd r1 := by
          dsimp [r1]
          exact riseStep_odd_of_step_two r0 hodd hfirst
        have htail := ih r1 hodd1
          (fun u hu => hok u (by simp [hu]))
          (fun k hk => by
            have hk' : k + 1 < (2 :: ts).length := by simp [hk]
            have h := hexact (k + 1) hk'
            have hrun : CycleBridge.riseRun r0 ((2 :: ts).take (k + 1)) =
                CycleBridge.riseRun r1 (ts.take k) := by
              rw [List.take_cons (by omega)]
              simp [CycleBridge.riseRun, CycleBridge.riseStep, r1]
            have hidx : (2 :: ts).getI (k + 1) = ts.getI k := by
              rw [List.getI_cons_succ]
            rwa [hrun, hidx] at h)
        have hdrop := CycleBridge.t2Step_valuation_drop r0 hfirst
        have hdrop_eq : twoValuation (r1 + 1) + 2 = twoValuation (r0 + 1) := by
          dsimp [r1, CycleBridge.riseStep]
          have h := hdrop.2
          have hge2 : 2 ≤ twoValuation (r0 + 1) := hdrop.1
          have h' : twoValuation (CycleBridge.riseStep r0 2 + 1) =
              twoValuation (r0 + 1) - 2 := by
            simpa [CycleBridge.riseStep, show (2 ^ 2 : Nat) = 4 by norm_num] using h
          omega
        have hrun : CycleBridge.riseRun r0 (2 :: ts) = CycleBridge.riseRun r1 ts := by
          simp [CycleBridge.riseRun, CycleBridge.riseStep, r1]
        have hcharge : CycleBridge.riseCharge r0 2 = 0 := by
          unfold CycleBridge.riseCharge
          simp
        simp [CycleBridge.riseChargeSum, CycleBridge.riseCountTwo, hrun, hcharge]
        dsimp [r1]
        have htail' : CycleBridge.riseChargeSum (CycleBridge.riseStep r0 2) ts +
              twoValuation (CycleBridge.riseStep r0 2 + 1) =
            2 * CycleBridge.riseCountTwo ts +
              twoValuation (CycleBridge.riseRun (CycleBridge.riseStep r0 2) ts + 1) := by
          simpa [r1] using htail
        have hdrop_eq' : twoValuation (CycleBridge.riseStep r0 2 + 1) + 2 =
              twoValuation (r0 + 1) := by
          simpa [r1] using hdrop_eq
        omega

/-- Concrete orbit rank at a cycle-word prefix: `R i` in the
noLongT2Run rank-language reduction. -/
def cycleWordRank (c i : Nat) : Nat :=
  twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + i) + 1)

/-- Failure of the `t=2` orbit-rank target is exactly the pointwise
upper bound `R j ≤ 2j+8` on every incoming-`t=2` prefix with outgoing
`{1,2}`.  This is the rank-language form of Stage 1. -/
theorem cycleWordT2OrbitTarget_failure_iff
    (c p : Nat) :
    (¬ ∃ j : Nat,
      1 ≤ j ∧ j < p ∧
      (CycleBridge.cycleWord c p).getI (j - 1) = 2 ∧
      ((CycleBridge.cycleWord c p).getI j = 1 ∨
        (CycleBridge.cycleWord c p).getI j = 2) ∧
      2 * j + 9 ≤ cycleWordRank c j) ↔
      ∀ j : Nat, 1 ≤ j → j < p →
        (CycleBridge.cycleWord c p).getI (j - 1) = 2 →
        ((CycleBridge.cycleWord c p).getI j = 1 ∨
          (CycleBridge.cycleWord c p).getI j = 2) →
        cycleWordRank c j ≤ 2 * j + 8 := by
  constructor
  · intro hnot j hj1 hjp hinc hout
    by_contra hle
    have hge : 2 * j + 9 ≤ cycleWordRank c j := by omega
    exact hnot ⟨j, hj1, hjp, hinc, hout, hge⟩
  · intro hall h
    rcases h with ⟨j, hj1, hjp, hinc, hout, hge⟩
    have hle := hall j hj1 hjp hinc hout
    omega

/-- The exact word numerator under `hcycle`: `wordA w =
m * (2^S - 5^P)`.  This is the wordA form of
`cycleQb8Input_aTotal5_equation`; it is the exact left-hand side used
by the rotated-word and block equations. -/
theorem cycleQb8Input_wordA_equation
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    StringFlow.Word.wordA w = m * (2 ^ S - 5 ^ P) := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  have hA : StringFlow.Word.wordA w =
      StringFlow.PMI.aTotal P (fun j => w.getI j) := by
    have hAw := CycleBridge.cycleWord_wordA_eq_pmi_aTotal c p
    have hstep : CycleBridge.cycleWordStepAt c p = fun j => w.getI j := by
      funext j
      dsimp [CycleBridge.cycleWordStepAt]
      rw [hw]
    have hP : P = p := by
      rw [← h.hlength, hw, CycleBridge.cycleWord_length]
    rw [← hw] at hAw
    rw [hstep, ← hP] at hAw
    exact hAw
  have hframe := cycleQb8Input_aTotal5_equation h
  have h5 : 5 * StringFlow.PMI.aTotal P (fun j => w.getI j) =
      5 * (m * (2 ^ S - 5 ^ P)) := by
    rw [← StringFlow.PMI.aTotal5_eq_five_mul_aTotal P (fun j => w.getI j)]
    simpa [Nat.mul_assoc] using hframe
  have hcancel := Nat.mul_left_cancel (by norm_num : 0 < 5) h5
  rwa [hA]

/-- Prefix-numerator lower bound from the global minimum:
`2^(W_i)·y_i = 5^i·m + A_i` and `hglobal_min` give
`A_i ≥ m·(2^(W_i) − 5^i)`.  The end `i = P` is covered by the
closed-word identity, where `y_P = m`; no PMI frame is needed here. -/
theorem wordA_take_ge_of_global_min
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (i : Nat) (hi : i ≤ P) :
    StringFlow.Word.wordA (w.take i) ≥
      m * (2 ^ StringFlow.wordWeight (w.take i) - 5 ^ i) := by
  have hlen : (w.take i).length = i := by
    rw [List.length_take_of_le]
    rw [h.hlength]
    exact hi
  have hvalid : StringFlow.Word.wordValid (w.take i) m := by
    have hsplit : w.take i ++ w.drop i = w := List.take_append_drop i w
    have hv : StringFlow.Word.wordValid (w.take i ++ w.drop i) m := by
      rw [hsplit]
      exact h.hvalid
    exact ((S6Audit.wordValid_append (w.take i) (w.drop i) m).mp hv).1
  have hid := StringFlow.Word.word_orbit_identity (w.take i) m hvalid
  have hmin : m ≤ StringFlow.Word.wordOrbit (w.take i) m := by
    by_cases hiP : i = P
    · subst i
      have htake : w.take P = w := by
        apply List.take_of_length_le
        rw [h.hlength]
      rw [htake]
      exact le_of_eq h.hclosed.symm
    · have hlt : i < P := by omega
      exact h.hglobal_min i hlt
  have hmul : 2 ^ StringFlow.wordWeight (w.take i) * m ≤
      2 ^ StringFlow.wordWeight (w.take i) *
        StringFlow.Word.wordOrbit (w.take i) m :=
    Nat.mul_le_mul_left (2 ^ StringFlow.wordWeight (w.take i)) hmin
  have hid' : 2 ^ StringFlow.wordWeight (w.take i) *
        StringFlow.Word.wordOrbit (w.take i) m =
      5 ^ i * m + StringFlow.Word.wordA (w.take i) := by
    rw [hlen] at hid
    exact hid
  have hleq : m * 5 ^ i + StringFlow.Word.wordA (w.take i) ≥
      m * 2 ^ StringFlow.wordWeight (w.take i) := by
    rw [hid'] at hmul
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have hsub : m * 2 ^ StringFlow.wordWeight (w.take i) -
        m * 5 ^ i ≤ StringFlow.Word.wordA (w.take i) := by omega
  have hdist : m * (2 ^ StringFlow.wordWeight (w.take i) - 5 ^ i) =
      m * 2 ^ StringFlow.wordWeight (w.take i) - m * 5 ^ i := by
    rw [Nat.mul_sub_left_distrib]
  rw [hdist]
  exact hsub

/-- The same prefix-numerator lower bound, explicitly carrying the
`hcycle` concrete orbit parameters: `w = cycleWord c p` and
`m = fiveXPlusOneOrbit 7 c`. -/
theorem cycleQb8Input_wordA_take_ge_global_min_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (i : Nat) (hi : i ≤ P) :
    ∃ c p : Nat,
      w = CycleBridge.cycleWord c p ∧
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      StringFlow.Word.wordA (w.take i) ≥
        m * (2 ^ StringFlow.wordWeight (w.take i) - 5 ^ i) := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  refine ⟨c, p, hw, hm, wordA_take_ge_of_global_min h i hi⟩

/-- Concrete orbit-prefix form of the lower bound: in addition to the
numerator inequality, every prefix state is the exact shifted orbit
state `fiveXPlusOneOrbit 7 (c+j)`. -/
theorem cycleQb8Input_wordA_take_ge_global_min_orbit_prefix
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (i : Nat) (hi : i ≤ P) :
    ∃ c p : Nat,
      w = CycleBridge.cycleWord c p ∧
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      (∀ j : Nat, j ≤ i →
        StringFlow.Word.wordOrbit (w.take j) m =
          StringFlow.fiveXPlusOneOrbit 7 (c + j)) ∧
      StringFlow.Word.wordA (w.take i) ≥
        m * (2 ^ StringFlow.wordWeight (w.take i) - 5 ^ i) := by
  rcases cycleQb8Input_wordA_take_ge_global_min_of_hcycle h i hi with
    ⟨c, p, hw, hm, hA⟩
  refine ⟨c, p, hw, hm, ?_, hA⟩
  intro j hj
  have hlenp : w.length = p := by
    rw [hw, CycleBridge.cycleWord_length]
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hjle : j ≤ p := by omega
  rw [hw, hm]
  exact CycleBridge.cycleWord_prefix_orbit_eq c p j hjle

/-- Real-orbit C3 constraint: immediately before a C3 step the state
is large enough that the following state is still at or above the
global minimum.  Equivalently `m·2^t ≤ 5·y_j + 1`. -/
theorem cycleQb8Input_c3_step_global_min
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (j : Nat) (hj : j < P) (hc3 : 3 ≤ w.getI j) :
    m * 2 ^ w.getI j ≤
      5 * StringFlow.Word.wordOrbit (w.take j) m + 1 := by
  have hjw : j < w.length := by
    rw [h.hlength]
    exact hj
  have hsucc := CycleBridge.wordOrbit_take_succ w m j hjw
  have hy_next : m ≤ StringFlow.Word.wordOrbit (w.take (j + 1)) m := by
    by_cases hlast : j + 1 = P
    · have hJ : j = P - 1 := by omega
      subst j
      have htake : w.take P = w := by
        apply List.take_of_length_le
        rw [h.hlength]
      rw [hlast]
      rw [htake]
      exact le_of_eq h.hclosed.symm
    · have hlt : j + 1 < P := by omega
      exact h.hglobal_min (j + 1) hlt
  have hdiv : StringFlow.Word.wordOrbit (w.take (j + 1)) m =
      (5 * StringFlow.Word.wordOrbit (w.take j) m + 1) /
        2 ^ w.getI j := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsucc
  rw [hdiv] at hy_next
  have hpos : 0 < 2 ^ w.getI j := Nat.pow_pos (by decide)
  exact (Nat.le_div_iff_mul_le hpos).mp hy_next

/-- The list-form prefix numerator agrees with the PMI `aTotal`
expansion over the word entries. -/
theorem wordA_eq_pmi_aTotal (w : List Nat) :
    StringFlow.Word.wordA w =
      StringFlow.PMI.aTotal w.length (fun j => w.getI j) := by
  rw [StringFlow.SurvEx.wordA_eq_localLambda]
  exact StringFlow.PH.localLambda_eq_pmi_aTotal w

/-- Total word weight agrees with the PMI prefix weight at full
length. -/
theorem wordWeight_eq_pmi_prefixWeight (w : List Nat) :
    StringFlow.wordWeight w =
      StringFlow.PMI.prefixWeight (fun j => w.getI j) w.length := by
  rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum w w.length]
  rw [StringFlow.TD0.wordWeight_eq_sum w]
  rw [List.take_of_length_le (Nat.le_refl w.length)]

/-- The global-minimum numerator bound in PMI prefix form:
`aTotal_i ≥ m·(2^(W_i) − 5^i)`. -/
theorem wordA_take_ge_global_min_aTotal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (i : Nat) (hi : i ≤ P) :
    StringFlow.PMI.aTotal i (fun j => (w.take i).getI j) ≥
      m * (2 ^ StringFlow.PMI.prefixWeight
          (fun j => (w.take i).getI j) i - 5 ^ i) := by
  have hA := wordA_take_ge_of_global_min h i hi
  have hlen : (w.take i).length = i := by
    rw [List.length_take_of_le]
    rw [h.hlength]
    exact hi
  rwa [wordA_eq_pmi_aTotal (w.take i),
    wordWeight_eq_pmi_prefixWeight (w.take i), hlen] at hA

/-- PMI numerator recurrence summed over all proper prefixes:
`A_P = 4·Σ_{i=1}^{P-1} A_i + Σ_{i=0}^{P-1} 2^(W_i)`. -/
theorem aTotal_eq_four_sum_and_pow (P : Nat) (t : Nat → Nat) :
    StringFlow.PMI.aTotal P t =
      4 * ((List.range (P - 1)).map
        (fun i => StringFlow.PMI.aTotal (i + 1) t)).sum +
        ((List.range P).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight t i)).sum := by
  induction P with
  | zero => simp [StringFlow.PMI.aTotal]
  | succ P ih =>
      by_cases hP : P = 0
      · subst P
        simp [StringFlow.PMI.aTotal, StringFlow.PMI.prefixWeight]
      · have hpow : (List.range (P + 1)).map
            (fun i => 2 ^ StringFlow.PMI.prefixWeight t i) =
            (List.range P).map
              (fun i => 2 ^ StringFlow.PMI.prefixWeight t i) ++
                [2 ^ StringFlow.PMI.prefixWeight t P] := by
          rw [List.range_succ, List.map_append]
          simp
        rw [show (P + 1) - 1 = P by omega]
        rw [hpow, List.sum_append, List.sum_singleton]
        rw [StringFlow.PMI.aTotal_succ]
        have hPrev : (List.range P).map
            (fun i => StringFlow.PMI.aTotal (i + 1) t) =
            (List.range (P - 1)).map
              (fun i => StringFlow.PMI.aTotal (i + 1) t) ++
                [StringFlow.PMI.aTotal P t] := by
          rw [show P = (P - 1) + 1 by omega]
          rw [List.range_succ, List.map_append]
          simp
        rw [hPrev, List.sum_append, List.sum_singleton]
        rw [ih]
        ring

/-- The PMI prefix weight of the original word entries is the same as
the PMI prefix weight of the `take` prefix. -/
lemma prefixWeight_take_eq (w : List Nat) (i : Nat) :
    StringFlow.PMI.prefixWeight (fun j => w.getI j) i =
      StringFlow.PMI.prefixWeight (fun j => (w.take i).getI j) i := by
  rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum w i]
  rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum (w.take i) i]
  have htake : (w.take i).take i = w.take i := by
    apply List.take_of_length_le
    rw [List.length_take]
    exact Nat.min_le_left i w.length
  rw [htake]

/-- Prefix weights at `j ≤ i` agree between the original word and its
`take i` prefix. -/
lemma prefixWeight_take_le_eq (w : List Nat) (i j : Nat) (hji : j ≤ i) :
    StringFlow.PMI.prefixWeight (fun k => w.getI k) j =
      StringFlow.PMI.prefixWeight (fun k => (w.take i).getI k) j := by
  rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum w j]
  rw [StringFlow.TD0.prefixWeight_getI_eq_take_sum (w.take i) j]
  have htake : (w.take i).take j = w.take j := by
    rw [List.take_take]
    congr 1
    omega
  rw [htake]

/-- The PMI numerator of the original word entries at prefix length
`i` agrees with the numerator of the actual `take i` prefix. -/
theorem aTotal_take_eq (w : List Nat) (i : Nat) :
    StringFlow.PMI.aTotal i (fun j => w.getI j) =
      StringFlow.PMI.aTotal i (fun j => (w.take i).getI j) := by
  unfold StringFlow.PMI.aTotal
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjlt : j < i := List.mem_range.mp hj
  have hp := congrArg (fun x => 2 ^ x)
    (prefixWeight_take_le_eq w i j (le_of_lt hjlt))
  exact congrArg (fun x => 5 ^ (i - 1 - j) * x) hp

/-- The summed PMI recurrence plus the global-minimum prefix bound:
`A_P ≥ 4·m·Σ_{i=1}^{P-1}(2^(W_i)−5^i) + Σ_{i=0}^{P-1}2^(W_i)`. -/
theorem wordA_sum_ge_global_min_aTotal
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    StringFlow.PMI.aTotal P (fun j => w.getI j) ≥
      4 * m * ((List.range (P - 1)).map
        (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
                  5 ^ (i + 1))).sum +
        ((List.range P).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) i)).sum := by
  have hsum := aTotal_eq_four_sum_and_pow P (fun j => w.getI j)
  let sumA : Nat := ((List.range (P - 1)).map
    (fun i => StringFlow.PMI.aTotal (i + 1) (fun j => w.getI j))).sum
  let sumB : Nat := ((List.range (P - 1)).map
    (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
              5 ^ (i + 1))).sum
  let sumPow : Nat := ((List.range P).map
    (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) i)).sum
  have hA : sumA ≥ m * sumB := by
    dsimp [sumA, sumB]
    have hle : ((List.range (P - 1)).map (fun i =>
          m * (2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
                5 ^ (i + 1)))).sum ≤
        ((List.range (P - 1)).map (fun i =>
          StringFlow.PMI.aTotal (i + 1) (fun j => w.getI j))).sum := by
      apply List.sum_le_sum
      intro i hi
      have hlt : i < P - 1 := List.mem_range.mp hi
      have hile : i + 1 ≤ P := by omega
      have hb := wordA_take_ge_global_min_aTotal h (i + 1) hile
      rw [← aTotal_take_eq w (i + 1)] at hb
      rw [← prefixWeight_take_le_eq w (i + 1) (i + 1) (Nat.le_refl (i + 1))] at hb
      exact hb
    have hmap : ((List.range (P - 1)).map (fun i =>
          m * (2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
                5 ^ (i + 1)))).sum =
        m * ((List.range (P - 1)).map (fun i =>
          2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
            5 ^ (i + 1))).sum := by
      rw [← StringFlow.PMI.sum_map_mul_left (List.range (P - 1)) m
        (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
          5 ^ (i + 1))]
    rw [← hmap]
    exact hle
  have h4 : 4 * sumA ≥ 4 * (m * sumB) := by nlinarith
  have h4' : 4 * sumA ≥ 4 * m * sumB := by
    simpa [Nat.mul_assoc] using h4
  have hgoal : StringFlow.PMI.aTotal P (fun j => w.getI j) ≥
      4 * m * sumB + sumPow := by
    rw [hsum]
    dsimp [sumA, sumB, sumPow]
    exact Nat.add_le_add_right h4' sumPow
  simpa [sumB, sumPow] using hgoal

/-- PMI merge: the exact numerator `m·(2^S − 5^P)` dominates the
global-minimum weighted sum of prefix terms. -/
theorem cycleQb8Input_pmi_sum_ge_global_min
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    m * (2 ^ S - 5 ^ P) ≥
      4 * m * ((List.range (P - 1)).map
        (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) (i + 1) -
                  5 ^ (i + 1))).sum +
        ((List.range P).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight (fun j => w.getI j) i)).sum := by
  have hA : StringFlow.PMI.aTotal P (fun j => w.getI j) =
      m * (2 ^ S - 5 ^ P) := by
    have h0 := cycleQb8Input_wordA_equation h
    rw [wordA_eq_pmi_aTotal w] at h0
    rwa [h.hlength] at h0
  rw [← hA]
  exact wordA_sum_ge_global_min_aTotal h

/-- The PMI/global-minimum sum inequality, rewritten onto the concrete
`hcycle` orbit word `cycleWord c p` with `m = fiveXPlusOneOrbit 7 c`.
This is the orbit-anchored form that must be joined with the
`noLongT2Run` run-sum bound. -/
theorem cycleQb8Input_pmi_sum_ge_global_min_of_hcycle
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    ∃ c p : Nat,
      w = CycleBridge.cycleWord c p ∧
      m = StringFlow.fiveXPlusOneOrbit 7 c ∧
      m * (2 ^ S - 5 ^ P) ≥
        4 * m * ((List.range (P - 1)).map
          (fun i => 2 ^ StringFlow.PMI.prefixWeight
              (CycleBridge.cycleWordStepAt c p) (i + 1) - 5 ^ (i + 1))).sum +
          ((List.range P).map
            (fun i => 2 ^ StringFlow.PMI.prefixWeight
              (CycleBridge.cycleWordStepAt c p) i)).sum := by
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  have hineq := cycleQb8Input_pmi_sum_ge_global_min h
  have hstep : (fun j => w.getI j) = CycleBridge.cycleWordStepAt c p := by
    funext j
    dsimp [CycleBridge.cycleWordStepAt]
    rw [hw]
  rw [hstep] at hineq
  exact ⟨c, p, hw, hm, hineq⟩

/-- The internal rank-bound step for the selected 7-cycle word, stated
directly at the concrete orbit states `fiveXPlusOneOrbit 7 (c+j)`.
This is deliberately not a `∀ CycleQb8Input` lemma and not an
independent open target: it is the trinity-internal assertion filled by
`HtermComponent`/`HfailComponent` inside `trinityBlockExistsOfComponents`.
The `13` shadow is false here because `13` is not an orbit state of
`7`; the assertion is only usable inside the no-cycle contradiction for
the specific `(c,p)` supplied by `hcycle`. -/
def cycleWordInternalRankLowerBound (c p : Nat) : Prop :=
  ∃ j t : Nat,
    1 ≤ j ∧ j < p ∧
    (t = 1 ∨ t = 2) ∧
    (CycleBridge.cycleWord c p).getI (j - 1) = t ∧
    ((CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2) ∧
    (t = 1 → 2 * j + 11 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1)) ∧
    (t = 2 → 2 * j + 9 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1))

/-- 5-adic telescope layer condition, `t=1`: the rank lower bound at
depth `j` follows once the concrete numerator
`5^j·m + A + 2^W` is divisible by `2^(W + 2j + 11)`.  Here `A` is the
prefix word numerator and `W` the prefix weight, so
`(5^j·m + A) / 2^W` is the prefix state.  This is a one-direction layer
reduction, not a new equivalence. -/
theorem rank_lower_t1_of_numerator
    (j W A m : Nat)
    (hN : 2 ^ W ∣ 5 ^ j * m + A)
    (hdiv : 2 ^ (W + 2 * j + 11) ∣ 5 ^ j * m + A + 2 ^ W) :
    2 * j + 11 ≤ twoValuation ((5 ^ j * m + A) / 2 ^ W + 1) := by
  let N := 5 ^ j * m + A
  have hsum : (N + 2 ^ W) / 2 ^ W = N / 2 ^ W + 1 := by
    rcases hN with ⟨a, ha⟩
    have h : 2 ^ W * (a + 1) = N + 2 ^ W := by
      change 2 ^ W * (a + 1) = 5 ^ j * m + A + 2 ^ W
      rw [ha]
      ring
    have hcancel : (2 ^ W * (a + 1)) / 2 ^ W = a + 1 :=
      Nat.mul_div_cancel_left (a + 1) (by positivity : 0 < 2 ^ W)
    rw [← h]
    have ha' : N / 2 ^ W = a := by
      change (5 ^ j * m + A) / 2 ^ W = a
      rw [ha]
      exact Nat.mul_div_cancel_left a (by positivity : 0 < 2 ^ W)
    rw [ha']
    exact hcancel
  have hdvd : 2 ^ W ∣ N + 2 ^ W := by
    rcases hN with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    change 5 ^ j * m + A + 2 ^ W = 2 ^ W * (a + 1)
    rw [ha]
    ring
  have hpos : 0 < N + 2 ^ W := by positivity
  have hvalN : W + 2 * j + 11 ≤ twoValuation (N + 2 ^ W) :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (N + 2 ^ W)
      (W + 2 * j + 11) hpos).mpr (by simpa [N] using hdiv)
  rcases hdvd with ⟨q, hq⟩
  have hqpos : 0 < q := by
    by_contra hnot
    have hz : q = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.mul_zero] at hq
    omega
  have hmul := StringFlow.Lte.twoValuation_mul_two_pow W q hqpos
  rw [← hq] at hmul
  have hquot : twoValuation ((N + 2 ^ W) / 2 ^ W) =
      twoValuation (N + 2 ^ W) - W := by
    have hdivq : (2 ^ W * q) / 2 ^ W = q :=
      Nat.mul_div_cancel_left q (by positivity : 0 < 2 ^ W)
    rw [← hq] at hdivq
    rw [hdivq]
    omega
  rw [← hsum]
  rw [hquot]
  omega

/-- 5-adic telescope layer condition, `t=2`: same layer reduction with
threshold `2j+9` and modulus `2^(W + 2j + 9)`. -/
theorem rank_lower_t2_of_numerator
    (j W A m : Nat)
    (hN : 2 ^ W ∣ 5 ^ j * m + A)
    (hdiv : 2 ^ (W + 2 * j + 9) ∣ 5 ^ j * m + A + 2 ^ W) :
    2 * j + 9 ≤ twoValuation ((5 ^ j * m + A) / 2 ^ W + 1) := by
  let N := 5 ^ j * m + A
  have hsum : (N + 2 ^ W) / 2 ^ W = N / 2 ^ W + 1 := by
    rcases hN with ⟨a, ha⟩
    have h : 2 ^ W * (a + 1) = N + 2 ^ W := by
      change 2 ^ W * (a + 1) = 5 ^ j * m + A + 2 ^ W
      rw [ha]
      ring
    have hcancel : (2 ^ W * (a + 1)) / 2 ^ W = a + 1 :=
      Nat.mul_div_cancel_left (a + 1) (by positivity : 0 < 2 ^ W)
    rw [← h]
    have ha' : N / 2 ^ W = a := by
      change (5 ^ j * m + A) / 2 ^ W = a
      rw [ha]
      exact Nat.mul_div_cancel_left a (by positivity : 0 < 2 ^ W)
    rw [ha']
    exact hcancel
  have hdvd : 2 ^ W ∣ N + 2 ^ W := by
    rcases hN with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    change 5 ^ j * m + A + 2 ^ W = 2 ^ W * (a + 1)
    rw [ha]
    ring
  have hpos : 0 < N + 2 ^ W := by positivity
  have hvalN : W + 2 * j + 9 ≤ twoValuation (N + 2 ^ W) :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (N + 2 ^ W)
      (W + 2 * j + 9) hpos).mpr (by simpa [N] using hdiv)
  rcases hdvd with ⟨q, hq⟩
  have hqpos : 0 < q := by
    by_contra hnot
    have hz : q = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.mul_zero] at hq
    omega
  have hmul := StringFlow.Lte.twoValuation_mul_two_pow W q hqpos
  rw [← hq] at hmul
  have hquot : twoValuation ((N + 2 ^ W) / 2 ^ W) =
      twoValuation (N + 2 ^ W) - W := by
    have hdivq : (2 ^ W * q) / 2 ^ W = q :=
      Nat.mul_div_cancel_left q (by positivity : 0 < 2 ^ W)
    rw [← hq] at hdivq
    rw [hdivq]
    omega
  rw [← hsum]
  rw [hquot]
  omega

/-- The exact 5-adic telescope layer condition for the selected 7-cycle
word at depth `j`: the concrete numerator `5^j·m + A_j + 2^W_j` must
have high 2-adic valuation.  `A_j` and `W_j` are the prefix word
numerator and prefix weight of `cycleWord c p`. -/
def cycleWordLayerCondition (c p j t : Nat) : Prop :=
  let W := StringFlow.wordWeight ((CycleBridge.cycleWord c p).take j)
  let A := StringFlow.Word.wordA ((CycleBridge.cycleWord c p).take j)
  (t = 1 → 2 ^ (W + 2 * j + 11) ∣
    5 ^ j * StringFlow.fiveXPlusOneOrbit 7 c + A + 2 ^ W) ∧
  (t = 2 → 2 ^ (W + 2 * j + 9) ∣
    5 ^ j * StringFlow.fiveXPlusOneOrbit 7 c + A + 2 ^ W)

/-- Shifted `t=2` run: `t2Run (r k) i` follows the sequence `r`.
This is the recursion-shaped version of the pure `t=2` run, used to
feed `CycleBridge.pure_t2_balance` with the concrete orbit states. -/
lemma t2Run_shift_eq (r : Nat → Nat) (k i : Nat)
    (hstep : ∀ s : Nat, s < i → r (k + s + 1) = (5 * r (k + s) + 1) / 4) :
    CycleBridge.t2Run (r k) i = r (k + i) := by
  induction i generalizing k with
  | zero => simp [CycleBridge.t2Run]
  | succ i ih =>
      have h0 : r (k + 1) = (5 * r k + 1) / 4 := by
        simpa using hstep 0 (by omega)
      have htail : ∀ s : Nat, s < i → r ((k + 1) + s + 1) =
          (5 * r ((k + 1) + s) + 1) / 4 := by
        intro s hs
        have hs' : s + 1 < i + 1 := by omega
        have h := hstep (s + 1) hs'
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      calc
        CycleBridge.t2Run (r k) (i + 1)
            = CycleBridge.t2Run ((5 * r k + 1) / 4) i := by rfl
        _ = CycleBridge.t2Run (r (k + 1)) i := by rw [← h0]
        _ = r ((k + 1) + i) := ih (k + 1) htail
        _ = r (k + (i + 1)) := by
          congr 1
          omega

/-- Exact rank relation over one pure `t=2` run:
`v2(y_s+1) = v2(y_{s+N}+1) + 2N`.  This is the local summand of the
maximal-run telescoping; the global sum over all runs is obtained by
adding this identity over every maximal run. -/
theorem t2_run_rank_sum (r : Nat → Nat) (s N : Nat)
    (hstep : ∀ i : Nat, i < N → r (s + i + 1) = (5 * r (s + i) + 1) / 4)
    (hdiv : ∀ i : Nat, i < N → (5 * r (s + i) + 1) % 4 = 0) :
    twoValuation (r s + 1) =
      twoValuation (r (s + N) + 1) + 2 * N := by
  let f : Nat → Nat := fun i => r (s + i)
  have hsteps : ∀ i : Nat, i < N →
      f (i + 1) = (5 * f i + 1) / 4 ∧ (5 * f i + 1) % 4 = 0 := by
    intro i hi
    constructor
    · simpa [f, Nat.add_assoc] using hstep i hi
    · simpa [f] using hdiv i hi
  have hmul := UnifiedCoreAudit.t2_run_mul f N hsteps
  have hpos : 0 < f N + 1 := by positivity
  have hpos0 : 0 < f 0 + 1 := by positivity
  have hpow : 4 ^ N = 2 ^ (2 * N) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← Nat.pow_mul]
  have hval4 : twoValuation (4 ^ N * (f N + 1)) =
      2 * N + twoValuation (f N + 1) := by
    rw [hpow]
    exact StringFlow.Lte.twoValuation_mul_two_pow (2 * N) (f N + 1) hpos
  have h5odd : (5 ^ N) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hval5 : twoValuation (5 ^ N * (f 0 + 1)) = twoValuation (f 0 + 1) :=
    StringFlow.Lte.twoValuation_mul_odd (5 ^ N) (f 0 + 1) h5odd hpos0
  have hcong := congrArg twoValuation hmul
  rw [hval4, hval5] at hcong
  have hfin : twoValuation (f 0 + 1) =
      twoValuation (f N + 1) + 2 * N := by omega
  simpa [f] using hfin

/-- One maximal `t=2` run: start depth and length. -/
structure T2Run where
  start : Nat
  length : Nat
deriving instance Inhabited for StringFlow.Amiya.T2Run

/-- Global sum of the exact rank relation over a list of `t=2` runs:
`Σ (v2(y_{s}+1) - v2(y_{s+N}+1)) = 2 * Σ N`.  This is the
summation-level intermediate; no disjointness hypothesis is needed for
the identity itself. -/
theorem t2_runs_rank_sum (r : Nat → Nat) (runs : List T2Run)
    (hstep : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        r ((runs.getI k).start + i + 1) = (5 * r ((runs.getI k).start + i) + 1) / 4)
    (hdiv : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        (5 * r ((runs.getI k).start + i) + 1) % 4 = 0) :
    (runs.map (fun run => twoValuation (r run.start + 1) -
        twoValuation (r (run.start + run.length) + 1))).sum =
      2 * (runs.map (fun run => run.length)).sum := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hstep0 : ∀ i : Nat, i < run.length →
          r (run.start + i + 1) = (5 * r (run.start + i) + 1) / 4 := by
        intro i hi
        simpa using hstep 0 (by simp) i hi
      have hdiv0 : ∀ i : Nat, i < run.length →
          (5 * r (run.start + i) + 1) % 4 = 0 := by
        intro i hi
        exact hdiv 0 (by simp) i hi
      have htail : ∀ k : Nat, k < runs.length →
          ∀ i : Nat, i < (runs.getI k).length →
            r ((runs.getI k).start + i + 1) = (5 * r ((runs.getI k).start + i) + 1) / 4 := by
        intro k hk i hi
        have := hstep (k + 1) (by simp [hk]) i hi
        simpa [List.getI_cons_succ] using this
      have hdiv_tail : ∀ k : Nat, k < runs.length →
          ∀ i : Nat, i < (runs.getI k).length →
            (5 * r ((runs.getI k).start + i) + 1) % 4 = 0 := by
        intro k hk i hi
        have := hdiv (k + 1) (by simp [hk]) i hi
        simpa [List.getI_cons_succ] using this
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have hsingle := t2_run_rank_sum r run.start run.length hstep0 hdiv0
      have hdiff : twoValuation (r run.start + 1) -
          twoValuation (r (run.start + run.length) + 1) = 2 * run.length := by
        exact Nat.sub_eq_of_eq_add
          (a := twoValuation (r run.start + 1))
          (b := twoValuation (r (run.start + run.length) + 1))
          (c := 2 * run.length) (by simpa [Nat.add_comm] using hsingle)
      rw [ih htail hdiv_tail, hdiff]
      ring

/-- Boolean predicate for `t=2` entries, for `List.takeWhile`. -/
def t2Pred (u : Nat) : Bool :=
  decide (u = 2)

/-- Maximal `t=2` runs of a list, with global start offsets: at each
head `2` the whole leading run of twos is recorded, then the scan
continues after it; a non-`2` head is skipped. -/
def maxT2RunsFrom (ts : List Nat) (base : Nat) : List T2Run :=
  match ts with
  | [] => []
  | t :: rest =>
      if ht : t = 2 then
        let L := (List.takeWhile t2Pred (t :: rest)).length
        { start := base, length := L } :: maxT2RunsFrom ((t :: rest).drop L) (base + L)
      else
        maxT2RunsFrom rest (base + 1)
termination_by ts.length
decreasing_by
  · simp_wf
    have hpos : 0 < (List.takeWhile t2Pred (t :: rest)).length := by
      have hb : t2Pred t = true := by
        unfold t2Pred
        exact decide_eq_true ht
      rw [List.takeWhile_cons_of_pos hb]
      simp
    omega
  · simp_wf

/-- The maximal runs of a list. -/
def maxT2Runs (ts : List Nat) : List T2Run :=
  maxT2RunsFrom ts 0

/-- Dropping preserves `getI`: `(u.drop k).getI j = u.getI (k+j)`. -/
lemma getI_drop (u : List Nat) (k j : Nat) :
    (u.drop k).getI j = u.getI (k + j) := by
  by_cases hj : j < (u.drop k).length
  · have hk : k + j < u.length := by
      rw [List.length_drop] at hj
      omega
    rw [List.getI_eq_getElem (u.drop k) hj]
    rw [List.getI_eq_getElem u hk]
    exact List.getElem_drop (α := Nat) (xs := u) (i := k) (j := j) (h := hj)
  · have hnj : (u.drop k).getI j = 0 := by
      unfold List.getI
      exact List.getD_eq_default (u.drop k) 0 (Nat.le_of_not_gt hj)
    have hnk : u.getI (k + j) = 0 := by
      unfold List.getI
      have hge : ¬ k + j < u.length := by
        intro hlt
        have hj' : j < (u.drop k).length := by
          rw [List.length_drop]
          omega
        exact hj hj'
      exact List.getD_eq_default u 0 (Nat.le_of_not_gt hge)
    rw [hnj, hnk]

/-- Every entry of the leading `t=2` run is two. -/
lemma takeWhile_two_getI (ts : List Nat) (i : Nat)
    (hi : i < (List.takeWhile t2Pred ts).length) :
    ts.getI i = 2 := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
      by_cases ht : t = 2
      · have hb : t2Pred t = true := by
          unfold t2Pred
          exact decide_eq_true ht
        rw [List.takeWhile_cons_of_pos hb] at hi
        cases i with
        | zero => simp [ht]
        | succ i =>
            have hi' : i < (List.takeWhile t2Pred ts).length := by
              simpa using hi
            rw [List.getI_cons_succ]
            exact ih i hi'
      · have hb : t2Pred t = false := by
          unfold t2Pred
          exact decide_eq_false ht
        have hb' : ¬ t2Pred t = true := by
          intro htrue
          rw [hb] at htrue
          contradiction
        rw [List.takeWhile_cons_of_neg hb'] at hi
        simp at hi

/-- The leading `t=2` run length never exceeds the list length. -/
lemma takeWhile_two_length_le (ts : List Nat) :
    (List.takeWhile t2Pred ts).length ≤ ts.length :=
  (List.takeWhile_prefix t2Pred).length_le

/-- Recorded run starts are not before the scan base. -/
lemma maxT2RunsFrom_start_ge (ts : List Nat) (base : Nat) :
    ∀ run ∈ maxT2RunsFrom ts base, base ≤ run.start := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            intro run hmem
            have hmem0 : run = { start := base, length := L } ∨
                run ∈ maxT2RunsFrom ((t :: rest).drop L) (base + L) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_pos ht] at hmem'
              simpa [List.mem_cons] using hmem'
            rcases hmem0 with hrfl | hmem'
            · subst run
              simp
            · have hrec := hih run hmem'
              omega
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            intro run hmem
            have hmem0 : run ∈ maxT2RunsFrom rest (base + 1) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_neg ht] at hmem'
              exact hmem'
            have hrec := hih run hmem0
            omega

/-- The runs recorded by `maxT2RunsFrom` never extend past the list. -/
lemma maxT2RunsFrom_bounds (ts : List Nat) (base : Nat) :
    ∀ run ∈ maxT2RunsFrom ts base, run.start + run.length ≤ base + ts.length := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            intro run hmem
            have hmem0 : run = { start := base, length := L } ∨
                run ∈ maxT2RunsFrom ((t :: rest).drop L) (base + L) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_pos ht] at hmem'
              simpa [List.mem_cons] using hmem'
            rcases hmem0 with hrfl | hmem'
            · subst run
              simp
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
            · have hb := hih run hmem'
              have hdrop : ((t :: rest).drop L).length = (t :: rest).length - L :=
                List.length_drop
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            intro run hmem
            have hmem0 : run ∈ maxT2RunsFrom rest (base + 1) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_neg ht] at hmem'
              exact hmem'
            have hrec := hih run hmem0
            omega

/-- Every entry covered by a recorded run is `2`. -/
lemma maxT2RunsFrom_mem_two (ts : List Nat) (base : Nat) :
    ∀ run ∈ maxT2RunsFrom ts base,
      ∀ i : Nat, i < run.length → ts.getI (run.start - base + i) = 2 := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            intro run hmem i hi
            have hmem0 : run = { start := base, length := L } ∨
                run ∈ maxT2RunsFrom ((t :: rest).drop L) (base + L) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_pos ht] at hmem'
              simpa [List.mem_cons] using hmem'
            rcases hmem0 with hrfl | hmem'
            · subst run
              simpa using takeWhile_two_getI (t :: rest) i (by simpa [L] using hi)
            · have hb := hih run hmem' i hi
              have hdrop : ((t :: rest).drop L).getI (run.start - (base + L) + i) =
                  (t :: rest).getI (L + (run.start - (base + L) + i)) :=
                getI_drop (t :: rest) L (run.start - (base + L) + i)
              have hstart : L + (run.start - (base + L) + i) = run.start - base + i := by
                have hge : base + L ≤ run.start :=
                  maxT2RunsFrom_start_ge ((t :: rest).drop L) (base + L) run hmem'
                omega
              rw [hdrop, hstart] at hb
              exact hb
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            intro run hmem i hi
            have hmem0 : run ∈ maxT2RunsFrom rest (base + 1) := by
              have hmem' : run ∈ maxT2RunsFrom (t :: rest) base := hmem
              rw [maxT2RunsFrom] at hmem'
              rw [dif_neg ht] at hmem'
              exact hmem'
            have hb := hih run hmem0 i hi
            have hdrop : rest.getI (run.start - (base + 1) + i) =
                (t :: rest).getI (1 + (run.start - (base + 1) + i)) :=
              getI_drop (t :: rest) 1 (run.start - (base + 1) + i)
            have hstart : 1 + (run.start - (base + 1) + i) = run.start - base + i := by
              have hge : base + 1 ≤ run.start :=
                maxT2RunsFrom_start_ge rest (base + 1) run hmem0
              omega
            rw [hdrop, hstart] at hb
            exact hb

/-- Counting twos commutes with list append. -/
lemma riseCountTwo_append (l m : List Nat) :
    CycleBridge.riseCountTwo (l ++ m) =
      CycleBridge.riseCountTwo l + CycleBridge.riseCountTwo m := by
  induction l with
  | nil => simp [CycleBridge.riseCountTwo]
  | cons t ts ih =>
      by_cases ht : t = 2 <;>
        simp [CycleBridge.riseCountTwo, ih, ht,
          Nat.add_comm, Nat.add_left_comm]

/-- The leading `t=2` run consists entirely of twos. -/
lemma riseCountTwo_takeWhile_two (ts : List Nat) :
    CycleBridge.riseCountTwo (List.takeWhile t2Pred ts) =
      (List.takeWhile t2Pred ts).length := by
  induction ts with
  | nil => simp [List.takeWhile, CycleBridge.riseCountTwo]
  | cons t ts ih =>
      by_cases ht : t = 2
      · have hb : t2Pred t = true := by
          unfold t2Pred
          exact decide_eq_true ht
        rw [List.takeWhile_cons_of_pos hb]
        simp [CycleBridge.riseCountTwo, ih, ht, Nat.add_comm]
      · have hb : t2Pred t = false := by
          unfold t2Pred
          exact decide_eq_false ht
        have hb' : ¬ t2Pred t = true := by
          intro h
          rw [hb] at h
          contradiction
        rw [List.takeWhile_cons_of_neg hb']
        simp [CycleBridge.riseCountTwo]

/-- Dropping while `t2Pred` is the same as dropping the leading run. -/
lemma dropWhile_eq_drop_length_takeWhile (p : Nat → Bool) (ts : List Nat) :
    List.dropWhile p ts = ts.drop (List.takeWhile p ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      by_cases hp : p t = true
      · rw [List.takeWhile_cons_of_pos hp, List.dropWhile_cons_of_pos hp]
        simp [ih]
      · rw [List.takeWhile_cons_of_neg hp, List.dropWhile_cons_of_neg hp]
        simp

/-- The total number of twos splits at the leading `t=2` run. -/
lemma riseCountTwo_leading_two (ts : List Nat) :
    CycleBridge.riseCountTwo ts =
      (List.takeWhile t2Pred ts).length +
        CycleBridge.riseCountTwo (ts.drop (List.takeWhile t2Pred ts).length) := by
  have hsplit := List.takeWhile_append_dropWhile (p := t2Pred) (l := ts)
  have hdrop := dropWhile_eq_drop_length_takeWhile t2Pred ts
  calc
    CycleBridge.riseCountTwo ts
        = CycleBridge.riseCountTwo
            (List.takeWhile t2Pred ts ++ List.dropWhile t2Pred ts) := by
          congr 1
          exact hsplit.symm
    _ = (List.takeWhile t2Pred ts).length +
          CycleBridge.riseCountTwo (List.dropWhile t2Pred ts) := by
          rw [riseCountTwo_append, riseCountTwo_takeWhile_two]
    _ = (List.takeWhile t2Pred ts).length +
          CycleBridge.riseCountTwo
            (ts.drop (List.takeWhile t2Pred ts).length) := by
          rw [hdrop]

/-- The sum of maximal `t=2` run lengths is the total number of twos. -/
lemma maxT2RunsFrom_length_sum (ts : List Nat) (base : Nat) :
    ((maxT2RunsFrom ts base).map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo ts := by
  revert base
  induction ts using (measure List.length).wf.induction with
  | h ts ih =>
      intro base
      cases ts with
      | nil => simp [maxT2RunsFrom, CycleBridge.riseCountTwo]
      | cons t rest =>
          by_cases ht : t = 2
          · let L := (List.takeWhile t2Pred (t :: rest)).length
            have hpos : 0 < L := by
              dsimp [L]
              have hb : t2Pred t = true := by
                unfold t2Pred
                exact decide_eq_true ht
              rw [List.takeWhile_cons_of_pos hb]
              simp
            have hlt : ((t :: rest).drop L).length < (t :: rest).length := by
              rw [List.length_drop]
              have hLle : L ≤ (t :: rest).length :=
                takeWhile_two_length_le (t :: rest)
              omega
            have hih := ih ((t :: rest).drop L) hlt (base + L)
            have hsum :
                ((maxT2RunsFrom (t :: rest) base).map
                  (fun run => run.length)).sum =
                  L + ((maxT2RunsFrom ((t :: rest).drop L) (base + L)).map
                    (fun run => run.length)).sum := by
              rw [maxT2RunsFrom]
              rw [dif_pos ht]
              simp [L]
            rw [hsum, hih]
            rw [← riseCountTwo_leading_two (t :: rest)]
          · have hlt : rest.length < (t :: rest).length := by simp
            have hih := ih rest hlt (base + 1)
            have hsum :
                ((maxT2RunsFrom (t :: rest) base).map
                  (fun run => run.length)).sum =
                  ((maxT2RunsFrom rest (base + 1)).map
                    (fun run => run.length)).sum := by
              rw [maxT2RunsFrom]
              rw [dif_neg ht]
            rw [hsum, hih]
            simp [CycleBridge.riseCountTwo, ht]

/-- The `t2_runs_rank_sum` identity instantiated on one cyclic rise
block: summing the exact per-run rank identity over the maximal `t=2`
runs of the block's rise suffix gives `2 * riseCountTwo (suffixWord r)`. -/
theorem block_t2_runs_rank_sum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    let y : Nat → Nat := fun k =>
      CycleBridge.riseRun (CycleBridge.cycleRiseBlockC3TailState d r)
        ((d.suffixWord r).take k)
    ((maxT2Runs (d.suffixWord r)).map (fun run =>
      twoValuation (y run.start + 1) -
        twoValuation (y (run.start + run.length) + 1))).sum =
      2 * CycleBridge.riseCountTwo (d.suffixWord r) := by
  let y : Nat → Nat := fun k =>
    CycleBridge.riseRun (CycleBridge.cycleRiseBlockC3TailState d r)
      ((d.suffixWord r).take k)
  let runs : List T2Run := maxT2Runs (d.suffixWord r)
  let ts := d.suffixWord r
  have hruns_two : ∀ run ∈ runs, ∀ i : Nat, i < run.length →
      ts.getI (run.start + i) = 2 := by
    intro run hmem i hi
    have h := maxT2RunsFrom_mem_two ts 0 run hmem i hi
    simpa using h
  have hvalid : StringFlow.Word.wordValid ts
      (CycleBridge.cycleRiseBlockC3TailState d r) :=
    (CycleBridge.suffixWord_valid_of_cycleRiseBlock d r hr).1
  have hmem_of_getI : ∀ k : Nat, k < runs.length → (runs.getI k) ∈ runs := by
    intro k hk
    rw [List.getI_eq_getElem runs hk]
    exact List.getElem_mem hk
  have hstep : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        y ((runs.getI k).start + i + 1) =
          (5 * y ((runs.getI k).start + i) + 1) / 4 := by
    intro k hk i hi
    let run := runs.getI k
    have hmem : run ∈ runs := hmem_of_getI k hk
    have ht2 : ts.getI (run.start + i) = 2 := hruns_two run hmem i hi
    have hb : run.start + i < ts.length := by
      have hbnd := maxT2RunsFrom_bounds ts 0 run hmem
      dsimp [run] at hi hbnd ⊢
      omega
    have hsucc := CycleBridge.wordOrbit_take_succ ts
      (CycleBridge.cycleRiseBlockC3TailState d r) (run.start + i) hb
    have hpre1 : StringFlow.Word.wordOrbit (ts.take (run.start + i))
        (CycleBridge.cycleRiseBlockC3TailState d r) = y (run.start + i) := by
      dsimp [y]
      rw [CycleBridge.riseRun_eq_wordOrbit]
    have hpre2 : StringFlow.Word.wordOrbit (ts.take (run.start + i + 1))
        (CycleBridge.cycleRiseBlockC3TailState d r) = y (run.start + i + 1) := by
      dsimp [y]
      rw [CycleBridge.riseRun_eq_wordOrbit]
    rw [hpre1, hpre2, ht2] at hsucc
    simpa using hsucc
  have hdiv : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        (5 * y ((runs.getI k).start + i) + 1) % 4 = 0 := by
    intro k hk i hi
    let run := runs.getI k
    have hmem : run ∈ runs := hmem_of_getI k hk
    have ht2 : ts.getI (run.start + i) = 2 := hruns_two run hmem i hi
    have hb : run.start + i < ts.length := by
      have hbnd := maxT2RunsFrom_bounds ts 0 run hmem
      dsimp [run] at hi hbnd ⊢
      omega
    have hdvd := UnifiedCoreAudit.wordValid_drop_head ts
      (CycleBridge.cycleRiseBlockC3TailState d r) (run.start + i) hvalid hb
    have hpre1 : StringFlow.Word.wordOrbit (ts.take (run.start + i))
        (CycleBridge.cycleRiseBlockC3TailState d r) = y (run.start + i) := by
      dsimp [y]
      rw [CycleBridge.riseRun_eq_wordOrbit]
    rw [hpre1, ht2] at hdvd
    simpa using hdvd
  have hsum := t2_runs_rank_sum y runs hstep hdiv
  have hlen : (runs.map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo ts := by
    simpa [runs, ts, maxT2Runs]
      using maxT2RunsFrom_length_sum (d.suffixWord r) 0
  rw [hlen] at hsum
  simpa [ts, runs] using hsum

/-- Global `List.sum` intermediate: summing the block-level run
identities over all cyclic rise blocks gives `2 * H2` on the left and
the sum of all per-run rank differences on the right. -/
theorem t2_runs_global_sum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    2 * CycleBridge.cycleRiseBlockH2Sum d =
      ((List.range d.blockCount).map
        (fun r =>
          ((maxT2Runs (d.suffixWord r)).map (fun run =>
            twoValuation (CycleBridge.riseRun
                (CycleBridge.cycleRiseBlockC3TailState d r)
                ((d.suffixWord r).take run.start) + 1) -
              twoValuation (CycleBridge.riseRun
                (CycleBridge.cycleRiseBlockC3TailState d r)
                ((d.suffixWord r).take (run.start + run.length)) + 1))).sum)).sum := by
  dsimp [CycleBridge.cycleRiseBlockH2Sum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => CycleBridge.riseCountTwo (d.suffixWord r))]
  rw [List.map_congr_left (fun r hr =>
    (block_t2_runs_rank_sum d r (List.mem_range.mp hr)).symm)]

/-- Block-boundary telescoping: summing the block balances gives the
global upper bound `2*H2 ≤ Σ (tailRank + charge)` across all cyclic
rise blocks. -/
theorem cycleRiseBlockH2Sum_le_tailRank_charge_sum
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    2 * CycleBridge.cycleRiseBlockH2Sum d ≤
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r +
          CycleBridge.cycleRiseBlockCharge d r)).sum := by
  dsimp [CycleBridge.cycleRiseBlockH2Sum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => CycleBridge.riseCountTwo (d.suffixWord r))]
  exact List.sum_le_sum (fun r hr =>
    CycleBridge.cycleRiseBlockBalance d r (List.mem_range.mp hr))

/-- The `t2_runs_rank_sum` identity on the whole cycle word: summing
the exact per-run rank identity over all maximal `t=2` runs of
`cycleWord c p` gives twice the total number of `t=2` steps. -/
theorem cycleWord_t2_runs_rank_sum (c p : Nat) :
    let y : Nat → Nat := fun i => StringFlow.fiveXPlusOneOrbit 7 (c + i)
    ((maxT2Runs (CycleBridge.cycleWord c p)).map (fun run =>
      twoValuation (y run.start + 1) -
        twoValuation (y (run.start + run.length) + 1))).sum =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
  let y : Nat → Nat := fun i => StringFlow.fiveXPlusOneOrbit 7 (c + i)
  let runs : List T2Run := maxT2Runs (CycleBridge.cycleWord c p)
  let w := CycleBridge.cycleWord c p
  have hruns_two : ∀ run ∈ runs, ∀ i : Nat, i < run.length →
      w.getI (run.start + i) = 2 := by
    intro run hmem i hi
    have h := maxT2RunsFrom_mem_two w 0 run hmem i hi
    simpa using h
  have hmem_of_getI : ∀ k : Nat, k < runs.length → (runs.getI k) ∈ runs := by
    intro k hk
    rw [List.getI_eq_getElem runs hk]
    exact List.getElem_mem hk
  have hstep : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        y ((runs.getI k).start + i + 1) =
          (5 * y ((runs.getI k).start + i) + 1) / 4 := by
    intro k hk i hi
    let run := runs.getI k
    have hmem : run ∈ runs := hmem_of_getI k hk
    have ht2 : w.getI (run.start + i) = 2 := hruns_two run hmem i hi
    have hb : run.start + i < p := by
      have hbnd := maxT2RunsFrom_bounds w 0 run hmem
      rw [CycleBridge.cycleWord_length] at hbnd
      dsimp [run] at hi hbnd ⊢
      omega
    have hsucc := CycleBridge.wordOrbit_take_succ w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    have hpre1 : StringFlow.Word.wordOrbit (w.take (run.start + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i)
        (le_of_lt hb)
    have hpre2 : StringFlow.Word.wordOrbit (w.take (run.start + i + 1))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i + 1) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i + 1)
        (by omega)
    rw [hpre1, hpre2, ht2] at hsucc
    simpa using hsucc
  have hdiv : ∀ k : Nat, k < runs.length →
      ∀ i : Nat, i < (runs.getI k).length →
        (5 * y ((runs.getI k).start + i) + 1) % 4 = 0 := by
    intro k hk i hi
    let run := runs.getI k
    have hmem : run ∈ runs := hmem_of_getI k hk
    have ht2 : w.getI (run.start + i) = 2 := hruns_two run hmem i hi
    have hb : run.start + i < p := by
      have hbnd := maxT2RunsFrom_bounds w 0 run hmem
      rw [CycleBridge.cycleWord_length] at hbnd
      dsimp [run] at hi hbnd ⊢
      omega
    have hdvd := UnifiedCoreAudit.wordValid_drop_head w
      (StringFlow.fiveXPlusOneOrbit 7 c) (run.start + i)
      (CycleBridge.cycleWord_wordValid c p)
      (by simpa [w, CycleBridge.cycleWord_length] using hb)
    have hpre1 : StringFlow.Word.wordOrbit (w.take (run.start + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) = y (run.start + i) := by
      dsimp [y, w]
      exact CycleBridge.cycleWord_prefix_orbit_eq c p (run.start + i)
        (le_of_lt hb)
    rw [hpre1, ht2] at hdvd
    simpa using hdvd
  have hsum := t2_runs_rank_sum y runs hstep hdiv
  have hlen : (runs.map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo w := by
    simpa [runs, w, maxT2Runs]
      using maxT2RunsFrom_length_sum w 0
  rw [hlen] at hsum
  simpa [w, runs] using hsum

/-- The `t=2` layer condition closes once the prefix state itself has
rank at least `2j+9`.  This is the reverse of
`rank_lower_t2_of_numerator`: divisibility is read back from the rank
of `y_j = wordOrbit (w.take j) m`. -/
theorem cycleWordLayerCondition_of_rank_lower
    (c p j : Nat)
    (hjp : j < p)
    (hrank : 2 * j + 9 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1)) :
    cycleWordLayerCondition c p j 2 := by
  let W := StringFlow.wordWeight ((CycleBridge.cycleWord c p).take j)
  let A := StringFlow.Word.wordA ((CycleBridge.cycleWord c p).take j)
  let m := StringFlow.fiveXPlusOneOrbit 7 c
  have hlen : ((CycleBridge.cycleWord c p).take j).length = j := by
    rw [List.length_take_of_le (by
      rw [CycleBridge.cycleWord_length]
      exact le_of_lt hjp)]
  have hvalid : StringFlow.Word.wordValid ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c) := by
    have hsplit : ((CycleBridge.cycleWord c p).take j) ++
        ((CycleBridge.cycleWord c p).drop j) = CycleBridge.cycleWord c p :=
      List.take_append_drop j (CycleBridge.cycleWord c p)
    have hfull : StringFlow.Word.wordValid (CycleBridge.cycleWord c p)
        (StringFlow.fiveXPlusOneOrbit 7 c) :=
      CycleBridge.cycleWord_wordValid c p
    have hparts := (S6Audit.wordValid_append ((CycleBridge.cycleWord c p).take j)
        ((CycleBridge.cycleWord c p).drop j)
        (StringFlow.fiveXPlusOneOrbit 7 c)).mp (by simpa [hsplit] using hfull)
    exact hparts.1
  have hid : 2 ^ W * StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
        (StringFlow.fiveXPlusOneOrbit 7 c) = 5 ^ j * m + A := by
    have hid0 := StringFlow.Word.word_orbit_identity
      ((CycleBridge.cycleWord c p).take j) (StringFlow.fiveXPlusOneOrbit 7 c) hvalid
    dsimp [W, A, m] at hid0 ⊢
    rw [hlen] at hid0
    exact hid0
  have hpre : StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c) = StringFlow.fiveXPlusOneOrbit 7 (c + j) :=
    CycleBridge.cycleWord_prefix_orbit_eq c p j (le_of_lt hjp)
  have hprod : 5 ^ j * m + A + 2 ^ W =
      2 ^ W * (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
    calc
      5 ^ j * m + A + 2 ^ W = (2 ^ W * StringFlow.Word.wordOrbit
          ((CycleBridge.cycleWord c p).take j)
          (StringFlow.fiveXPlusOneOrbit 7 c)) + 2 ^ W := by rw [← hid]
      _ = 2 ^ W * (StringFlow.Word.wordOrbit
          ((CycleBridge.cycleWord c p).take j)
          (StringFlow.fiveXPlusOneOrbit 7 c) + 1) := by ring
      _ = 2 ^ W * (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by rw [hpre]
  have hxpos : 0 < StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1 := by positivity
  have hval0 : twoValuation (5 ^ j * m + A + 2 ^ W) =
      W + twoValuation (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
    rw [hprod]
    exact StringFlow.Lte.twoValuation_mul_two_pow W
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) hxpos
  have hpos : 0 < 5 ^ j * m + A + 2 ^ W := by
    rw [hprod]
    positivity
  have hdiv : 2 ^ (W + 2 * j + 9) ∣ 5 ^ j * m + A + 2 ^ W := by
    have hge : W + 2 * j + 9 ≤ twoValuation (5 ^ j * m + A + 2 ^ W) := by
      rw [hval0]
      omega
    exact (StringFlow.Lte.twoValuation_ge_iff_dvd_pow
      (5 ^ j * m + A + 2 ^ W) (W + 2 * j + 9) hpos).mp hge
  constructor
  · intro ht1
    omega
  · intro ht2
    simpa [cycleWordLayerCondition, W, A, m] using hdiv

/-- The `t=2` layer condition at prefix `j` follows from a pure `t=2`
run of length `N` after `j` once the budget
`2j+9 <= 2N` holds.  The run's endpoint does not need an explicit
rank-two premise: `pure_t2_balance` already charges `2N` from the
start state. -/
theorem cycleWordLayerCondition_of_t2_run_budget
    (c p j N : Nat)
    (hjp : j < p) (hjN : j + N ≤ p)
    (hbudget : 2 * j + 9 ≤ 2 * N)
    (hrun : ∀ i : Nat, i < N → (CycleBridge.cycleWord c p).getI (j + i) = 2) :
    cycleWordLayerCondition c p j 2 := by
  let r : Nat → Nat := fun i => StringFlow.fiveXPlusOneOrbit 7 (c + j + i)
  have hstep : ∀ s : Nat, s < N → r (s + 1) = (5 * r s + 1) / 4 := by
    intro s hs
    have hsucc := CycleBridge.wordOrbit_take_succ (CycleBridge.cycleWord c p)
      (StringFlow.fiveXPlusOneOrbit 7 c) (j + s) (by
        rw [CycleBridge.cycleWord_length]
        omega)
    have hpre1 : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + s))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + s)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + s) (by omega)
    have hpre2 : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + s + 1))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + s + 1)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + s + 1) (by omega)
    rw [hpre1, hpre2] at hsucc
    rw [hrun s hs] at hsucc
    dsimp [r]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc
  have hsteps : ∀ i : Nat, i < N →
      twoValuation (5 * CycleBridge.t2Run (r 0) i + 1) = 2 := by
    intro i hi
    have ht := t2Run_shift_eq r 0 i
      (fun s hs => by simpa [Nat.add_assoc] using hstep s (by omega))
    rw [ht]
    have hv := CycleBridge.cycleWord_step_exact c p (j + i) (by omega)
    have hpre : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + i)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + i) (by omega)
    rw [hpre] at hv
    rw [hrun i hi] at hv
    dsimp [r]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
  have hbal := CycleBridge.pure_t2_balance (r 0) N hsteps
  have hrank : 2 * j + 9 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
    have hbal' : 2 * N ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
      simpa [r] using hbal
    omega
  exact cycleWordLayerCondition_of_rank_lower c p j hjp hrank

/-- The layer condition closes the internal rank bound: once the
concrete 2-adic divisibility holds at a real rise-block head `j`, the
same `j,t` satisfy `cycleWordInternalRankLowerBound`.  This is the
one-direction telescope bridge; the divisibility itself is the
remaining valuation input. -/
theorem cycleWordInternalRankLowerBound_of_layer
    (c p j t : Nat)
    (hj1 : 1 ≤ j) (hjp : j < p)
    (ht : t = 1 ∨ t = 2)
    (hinc : (CycleBridge.cycleWord c p).getI (j - 1) = t)
    (hout : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2)
    (hlayer : cycleWordLayerCondition c p j t) :
    cycleWordInternalRankLowerBound c p := by
  let W := StringFlow.wordWeight ((CycleBridge.cycleWord c p).take j)
  let A := StringFlow.Word.wordA ((CycleBridge.cycleWord c p).take j)
  let m := StringFlow.fiveXPlusOneOrbit 7 c
  have hlen : ((CycleBridge.cycleWord c p).take j).length = j := by
    rw [List.length_take_of_le (by
      rw [CycleBridge.cycleWord_length]
      exact le_of_lt hjp)]
  have hvalid : StringFlow.Word.wordValid ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c) := by
    have hsplit : ((CycleBridge.cycleWord c p).take j) ++
        ((CycleBridge.cycleWord c p).drop j) = CycleBridge.cycleWord c p :=
      List.take_append_drop j (CycleBridge.cycleWord c p)
    have hfull : StringFlow.Word.wordValid (CycleBridge.cycleWord c p)
        (StringFlow.fiveXPlusOneOrbit 7 c) :=
      CycleBridge.cycleWord_wordValid c p
    have hparts := (S6Audit.wordValid_append ((CycleBridge.cycleWord c p).take j)
        ((CycleBridge.cycleWord c p).drop j)
        (StringFlow.fiveXPlusOneOrbit 7 c)).mp (by simpa [hsplit] using hfull)
    exact hparts.1
  have hid : 2 ^ W * StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
        (StringFlow.fiveXPlusOneOrbit 7 c) = 5 ^ j * m + A := by
    have hid0 := StringFlow.Word.word_orbit_identity
      ((CycleBridge.cycleWord c p).take j) (StringFlow.fiveXPlusOneOrbit 7 c) hvalid
    dsimp [W, A, m] at hid0 ⊢
    rw [hlen] at hid0
    exact hid0
  have hpre : StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c) = StringFlow.fiveXPlusOneOrbit 7 (c + j) :=
    CycleBridge.cycleWord_prefix_orbit_eq c p j (le_of_lt hjp)
  have hdivW : 2 ^ W ∣ 5 ^ j * m + A := by
    exact ⟨StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c), by
        rw [← hid]⟩
  refine ⟨j, t, hj1, hjp, ht, hinc, hout, ?_, ?_⟩
  · intro ht1
    have hdiv : 2 ^ (W + 2 * j + 11) ∣ 5 ^ j * m + A + 2 ^ W := by
      simpa [m, cycleWordLayerCondition, W, A] using hlayer.1 ht1
    have hrank := rank_lower_t1_of_numerator j W A m hdivW hdiv
    have hq : (5 ^ j * m + A) / 2 ^ W =
        StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
          (StringFlow.fiveXPlusOneOrbit 7 c) := by
      exact Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 ^ W)
        (by simpa [Nat.mul_comm] using hid.symm)
    rw [hq, hpre] at hrank
    exact hrank
  · intro ht2
    have hdiv : 2 ^ (W + 2 * j + 9) ∣ 5 ^ j * m + A + 2 ^ W := by
      simpa [m, cycleWordLayerCondition, W, A] using hlayer.2 ht2
    have hrank := rank_lower_t2_of_numerator j W A m hdivW hdiv
    have hq : (5 ^ j * m + A) / 2 ^ W =
        StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
          (StringFlow.fiveXPlusOneOrbit 7 c) := by
      exact Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 ^ W)
        (by simpa [Nat.mul_comm] using hid.symm)
    rw [hq, hpre] at hrank
    exact hrank

/-- Concrete orbit-rank bridge: a `t=2` entry `j` with outgoing
`{1,2}` and rank `2j+9` already closes the internal rank lower bound.
The `hcycle` parameters `c,p` enter only through the exact orbit state
`fiveXPlusOneOrbit 7 (c+j)`. -/
theorem cycleWordInternalRankLowerBound_of_orbit_rank
    (c p j : Nat)
    (hj1 : 1 ≤ j) (hjp : j < p)
    (hinc : (CycleBridge.cycleWord c p).getI (j - 1) = 2)
    (hout : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2)
    (hrank : 2 * j + 9 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1)) :
    cycleWordInternalRankLowerBound c p :=
  cycleWordInternalRankLowerBound_of_layer c p j 2 hj1 hjp
    (Or.inr rfl) hinc hout
    (cycleWordLayerCondition_of_rank_lower c p j hjp hrank)

/-- The remaining pure combinatorial budget: prefix `j` is entered by a
`t=2` step and is followed by a pure `t=2` run of length `N` with
`2j+9 <= 2N`. -/
def cycleWordT2RunBudget (c p : Nat) : Prop :=
  ∃ j N : Nat,
    1 ≤ j ∧ j + N ≤ p ∧
    2 * j + 9 ≤ 2 * N ∧
    (CycleBridge.cycleWord c p).getI (j - 1) = 2 ∧
    (∀ i : Nat, i < N → (CycleBridge.cycleWord c p).getI (j + i) = 2)

/-- Direct `t=2` rank extraction from the pure run budget: the same
`j` satisfies `2j+9 ≤ v2(fiveXPlusOneOrbit 7 (c+j)+1)` with the
incoming/outgoing `{1,2}` conditions. -/
theorem cycleWordT2RankOfBudget (c p : Nat) (hbudget : cycleWordT2RunBudget c p) :
    ∃ j : Nat,
      1 ≤ j ∧ j < p ∧
      (CycleBridge.cycleWord c p).getI (j - 1) = 2 ∧
      ((CycleBridge.cycleWord c p).getI j = 1 ∨
        (CycleBridge.cycleWord c p).getI j = 2) ∧
      2 * j + 9 ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
  rcases hbudget with ⟨j, N, hj1, hjN, hb, hinc, hrun⟩
  have hNpos : 1 ≤ N := by nlinarith
  have hjp : j < p := by omega
  have hout : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2 :=
    Or.inr (hrun 0 hNpos)
  let r : Nat → Nat := fun i => StringFlow.fiveXPlusOneOrbit 7 (c + j + i)
  have hstep : ∀ s : Nat, s < N → r (s + 1) = (5 * r s + 1) / 4 := by
    intro s hs
    have hsucc := CycleBridge.wordOrbit_take_succ (CycleBridge.cycleWord c p)
      (StringFlow.fiveXPlusOneOrbit 7 c) (j + s) (by
        rw [CycleBridge.cycleWord_length]
        omega)
    have hpre1 : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + s))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + s)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + s) (by omega)
    have hpre2 : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + s + 1))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + s + 1)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + s + 1) (by omega)
    rw [hpre1, hpre2] at hsucc
    rw [hrun s hs] at hsucc
    dsimp [r]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc
  have hsteps : ∀ i : Nat, i < N →
      twoValuation (5 * CycleBridge.t2Run (r 0) i + 1) = 2 := by
    intro i hi
    have ht := t2Run_shift_eq r 0 i
      (fun s hs => by simpa [Nat.add_assoc] using hstep s (by omega))
    rw [ht]
    have hv := CycleBridge.cycleWord_step_exact c p (j + i) (by omega)
    have hpre : StringFlow.Word.wordOrbit
        ((CycleBridge.cycleWord c p).take (j + i))
        (StringFlow.fiveXPlusOneOrbit 7 c) =
        StringFlow.fiveXPlusOneOrbit 7 (c + (j + i)) :=
      CycleBridge.cycleWord_prefix_orbit_eq c p (j + i) (by omega)
    rw [hpre] at hv
    rw [hrun i hi] at hv
    dsimp [r]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
  have hbal := CycleBridge.pure_t2_balance (r 0) N hsteps
  have hrank : 2 * j + 9 ≤ twoValuation
      (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
    have hbal' : 2 * N ≤ twoValuation
        (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
      simpa [r] using hbal
    omega
  exact ⟨j, hj1, hjp, hinc, hout, hrank⟩

/-- A pure `t=2` run budget closes the internal rank bound directly:
the layer bridge `cycleWordLayerCondition_of_t2_run_budget` feeds the
existing `cycleWordInternalRankLowerBound_of_layer`. -/
theorem cycleWordInternalRankLowerBound_of_t2_run_budget
    (c p j N : Nat)
    (hj1 : 1 ≤ j) (hjp : j < p) (hjN : j + N ≤ p)
    (hbudget : 2 * j + 9 ≤ 2 * N)
    (hinc : (CycleBridge.cycleWord c p).getI (j - 1) = 2)
    (hout : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2)
    (hrun : ∀ i : Nat, i < N → (CycleBridge.cycleWord c p).getI (j + i) = 2) :
    cycleWordInternalRankLowerBound c p :=
  cycleWordInternalRankLowerBound_of_layer c p j 2 hj1 hjp
    (Or.inr rfl) hinc hout
    (cycleWordLayerCondition_of_t2_run_budget c p j N hjp hjN hbudget hrun)

/-- The budget closes the internal rank bound through the `t=2` layer
bridge.  This is the exact place where `cycleWordT2RunBudget` is the
only remaining input. -/
theorem cycleWordInternalRankLowerBound_of_t2_run_budget_exists
    (c p : Nat) (hbudget : cycleWordT2RunBudget c p) :
    cycleWordInternalRankLowerBound c p := by
  rcases hbudget with ⟨j, N, hj1, hjN, hb, hinc, hrun⟩
  have hNpos : 1 ≤ N := by nlinarith
  have hjp : j < p := by omega
  exact cycleWordInternalRankLowerBound_of_t2_run_budget
    c p j N hj1 hjp hjN hb hinc (Or.inr (hrun 0 hNpos)) hrun

/-- Anti-proof hypothesis: every maximal `t=2` run entered by a
`t=2` step has length at most `s+4`.  This is the word-structure
constraint used in the PMI contradiction. -/
def noLongT2Run (c p : Nat) : Prop :=
  ∀ s N : Nat, 1 ≤ s → s + N ≤ p →
    (CycleBridge.cycleWord c p).getI (s - 1) = 2 →
    (∀ i : Nat, i < N → (CycleBridge.cycleWord c p).getI (s + i) = 2) →
    N ≤ s + 4

/-- The negation of `noLongT2Run` is exactly the positive budget
`cycleWordT2RunBudget`: an incoming-`t=2` prefix followed by at least
`s+5` further `t=2` steps. -/
theorem cycleWordT2RunBudget_of_noLongT2Run_false
    (c p : Nat) (h : ¬ noLongT2Run c p) :
    cycleWordT2RunBudget c p := by
  unfold noLongT2Run at h
  push Not at h
  rcases h with ⟨s, N, hs, hsp, hinc, hrun, hN⟩
  have hb : 2 * s + 9 ≤ 2 * N := by omega
  exact ⟨s, N, hs, hsp, hb, hinc, hrun⟩

/-- Under `noLongT2Run`, every maximal `t=2` run of the cycle word has
length at most `start + 6` (the `N_s ≤ s+4` bound shifted by one). -/
lemma noLongT2Run_run_length_le (c p : Nat)
    (h : noLongT2Run c p) :
    ∀ run ∈ maxT2Runs (CycleBridge.cycleWord c p),
      run.length ≤ run.start + 6 := by
  intro run hmem
  by_cases hL : run.length = 0
  · omega
  · have hpos : 0 < run.length := Nat.pos_of_ne_zero hL
    have hmem_two : ∀ i : Nat, i < run.length →
        (CycleBridge.cycleWord c p).getI (run.start + i) = 2 := by
      intro i hi
      have h := maxT2RunsFrom_mem_two (CycleBridge.cycleWord c p) 0 run hmem i hi
      simpa using h
    have hN : run.length - 1 ≤ (run.start + 1) + 4 := by
      apply h (run.start + 1) (run.length - 1)
      · omega
      · have hbnd := maxT2RunsFrom_bounds (CycleBridge.cycleWord c p) 0 run hmem
        rw [CycleBridge.cycleWord_length] at hbnd
        omega
      · have := hmem_two 0 hpos
        simpa using this
      · intro i hi
        have hi' : i + 1 < run.length := by omega
        have := hmem_two (i + 1) hi'
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    omega

/-- Global upper bound from `noLongT2Run`: `2*H2 ≤ Σ (2*a + 12)`
over all maximal `t=2` runs of the cycle word. -/
theorem cycleWord_noLongT2Run_sum_bound (c p : Nat)
    (h : noLongT2Run c p) :
    2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) ≤
      ((maxT2Runs (CycleBridge.cycleWord c p)).map
        (fun run => 2 * run.start + 12)).sum := by
  let w := CycleBridge.cycleWord c p
  have hle : ∀ run ∈ maxT2Runs w, 2 * run.length ≤ 2 * run.start + 12 := by
    intro run hmem
    have hb := noLongT2Run_run_length_le c p h run (by simpa [w] using hmem)
    omega
  have hlen : ((maxT2Runs w).map (fun run => run.length)).sum =
      CycleBridge.riseCountTwo w := by
    simpa [w, maxT2Runs] using maxT2RunsFrom_length_sum w 0
  have hmain : 2 * CycleBridge.riseCountTwo w ≤
      ((maxT2Runs w).map (fun run => 2 * run.start + 12)).sum := by
    calc
      2 * CycleBridge.riseCountTwo w
          = ((maxT2Runs w).map (fun run => 2 * run.length)).sum := by
            rw [← hlen, List.sum_map_mul_left (maxT2Runs w)
              (fun run => run.length) 2]
      _ ≤ ((maxT2Runs w).map (fun run => 2 * run.start + 12)).sum :=
            List.sum_le_sum hle
  simpa [w] using hmain

/-- Left leg `L` of the run-budget comparison: the exact rank drop
across every maximal `t=2` run of the concrete cycle word. -/
def t2RunRankSum (c p : Nat) : Nat :=
  ((maxT2Runs (CycleBridge.cycleWord c p)).map
    (fun run => cycleWordRank c run.start -
      cycleWordRank c (run.start + run.length))).sum

/-- Right leg `U`: the `noLongT2Run` run-sum bound side. -/
def t2RunBoundSum (c p : Nat) : Nat :=
  ((maxT2Runs (CycleBridge.cycleWord c p)).map
    (fun run => 2 * run.start + 12)).sum

/-- The strict comparison `L > U` in concrete terms. -/
def t2RunRankSumGtBoundSum (c p : Nat) : Prop :=
  t2RunBoundSum c p < t2RunRankSum c p

/-- `L = 2*H2` by the exact per-run rank-drop identity. -/
theorem t2RunRankSum_eq_two_mul_riseCountTwo (c p : Nat) :
    t2RunRankSum c p =
      2 * CycleBridge.riseCountTwo (CycleBridge.cycleWord c p) := by
  unfold t2RunRankSum
  simpa [cycleWordRank] using cycleWord_t2_runs_rank_sum c p

/-- Under `noLongT2Run`, the second leg `2*H2 ≤ U` holds; hence
`L ≤ U`. -/
theorem t2RunRankSum_le_t2RunBoundSum_of_noLongT2Run
    (c p : Nat) (h : noLongT2Run c p) :
    t2RunRankSum c p ≤ t2RunBoundSum c p := by
  rw [t2RunRankSum_eq_two_mul_riseCountTwo]
  unfold t2RunBoundSum
  exact cycleWord_noLongT2Run_sum_bound c p h

/-- The strict leg `L > U` contradicts `noLongT2Run`. -/
theorem noLongT2Run_false_of_t2RunRankSumGtBoundSum
    (c p : Nat) (hgt : t2RunRankSumGtBoundSum c p)
    (hno : noLongT2Run c p) : False := by
  have hle := t2RunRankSum_le_t2RunBoundSum_of_noLongT2Run c p hno
  unfold t2RunRankSumGtBoundSum at hgt
  omega

/-- Concrete 13-shadow check of the exact frame: for the 13-cycle word
`(1,1,5)` with `m = 13`, `P = 3`, `S = 7`, the PMI frame holds with
both sides `195`, so the exact frame alone cannot contradict the
shadow. -/
theorem thirteen_cycle_aTotal5_frame :
    StringFlow.PMI.aTotal5 3 (fun j => ([1, 1, 5] : List Nat).getI j) =
      5 * 13 * (2 ^ StringFlow.wordWeight [1, 1, 5] - 5 ^ 3) ∧
    StringFlow.PMI.aTotal5 3 (fun j => ([1, 1, 5] : List Nat).getI j) =
      195 := by
  constructor
  · decide
  · decide

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

/-- Bridge from the internal concrete rank bound to the interface rank
predicate: once `cycleWordInternalRankLowerBound c p` holds for the
`hcycle` parameters, the same `j,t` satisfy `realPrefixDepth` and
`hfailRankLowerBoundAt`.  The rewriting uses the concrete prefix-state
identity `cycleWord_prefix_orbit_eq`, so the derivation is anchored to
`hcycle`. -/
theorem cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hP : P = p) (_hS : S = StringFlow.wordWeight (CycleBridge.cycleWord c p))
    (hrank : cycleWordInternalRankLowerBound c p) :
    ∃ j t : Nat,
      1 ≤ j ∧ j < P ∧ realPrefixDepth m w j ∧
        (t = 1 ∨ t = 2) ∧
        w.getI (j - 1) = t ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        hfailRankLowerBoundAt m w j t := by
  rcases hrank with ⟨j, t, hj1, hjp, ht, hinc, hout, hr1, hr2⟩
  have hjp_le : j ≤ p := le_of_lt hjp
  have hpre : StringFlow.Word.wordOrbit ((CycleBridge.cycleWord c p).take j)
      (StringFlow.fiveXPlusOneOrbit 7 c) =
      StringFlow.fiveXPlusOneOrbit 7 (c + j) :=
    CycleBridge.cycleWord_prefix_orbit_eq c p j hjp_le
  refine ⟨j, t, hj1, ?_, ?_, ht, ?_, ?_, ?_⟩
  · rw [hP]
    exact hjp
  · refine ⟨c, ?_, ?_⟩
    · rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
      exact hm.symm
    · rw [CycleBridge.fullOrbitIter_eq_fiveXPlusOneOrbit]
      rw [hw, hm]
      exact hpre.symm
  · rw [hw]
    exact hinc
  · rw [hw]
    exact hout
  · constructor
    · intro ht1
      have hrank' : 2 * j + 11 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := hr1 ht1
      rw [hw, hm, hpre]
      exact hrank'
    · intro ht2
      have hrank' : 2 * j + 9 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := hr2 ht2
      rw [hw, hm, hpre]
      exact hrank'

/-- Direct layer-to-interface bridge: the exact
`cycleWordLayerCondition` at a real rise-block head is composed with
the internal rank bridge and the `hcycle` prefix identity, yielding the
`hfailRankLowerBoundAt` interface at the same `j, t`. -/
theorem hfailRankLowerBound_of_layer
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p j t : Nat)
    (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hP : P = p)
    (hS : S = StringFlow.wordWeight (CycleBridge.cycleWord c p))
    (hj1 : 1 ≤ j) (hjp : j < p)
    (ht : t = 1 ∨ t = 2)
    (hinc : (CycleBridge.cycleWord c p).getI (j - 1) = t)
    (hout : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2)
    (hlayer : cycleWordLayerCondition c p j t) :
    ∃ j t : Nat,
      1 ≤ j ∧ j < P ∧ realPrefixDepth m w j ∧
        (t = 1 ∨ t = 2) ∧
        w.getI (j - 1) = t ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        hfailRankLowerBoundAt m w j t :=
  cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt
    h c p hw hm hP hS
    (cycleWordInternalRankLowerBound_of_layer
      c p j t hj1 hjp ht hinc hout hlayer)

/-- Main-theorem internal step, not an independent open lemma.  Under
the hypothesis `h : CycleBridge.CycleQb8Input ...` (a positive cycle of
`7`), the selected 7-cycle word should force a rise-block head at a
real orbit prefix depth `j` with incoming rise weight `t` whose rank
reaches the branchwise threshold.  The depth `j` is supplied by
`realPrefixDepth` (hence by `hstart`), not by the withdrawn PMI-B
bad-prefix predicate; `hfailBudgetLowerBoundAt` is the exact budget
intermediate.  This statement is false in the 13-shadow model (`7`
entering `{13,33,83}`) and vacuous when `7` diverges, so it cannot be
discharged as a standalone hfail prerequisite; it is only usable inside
the no-cycle contradiction for the concrete `hcycle` word.  The main
open target is `CycleBridge.failureWindowExistence`. -/
def hfailRankLowerBoundTarget : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
      ∃ j t : Nat,
        1 ≤ j ∧ j < P ∧
        realPrefixDepth m w j ∧
        (t = 1 ∨ t = 2) ∧
        w.getI (j - 1) = t ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        hfailRankLowerBoundAt m w j t

/-- Exact real-orbit valuation target for the `t=2` hfail branch:
at an incoming `t=2` prefix `j` with outgoing `{1,2}`, the concrete
7-orbit state `fiveXPlusOneOrbit 7 (c+j)` has rank at least `2j+9`.
The `hcycle` parameters `c,p` are explicit, so the statement cannot
be instantiated by the 13/17 shadows. -/
def cycleQb8InputT2OrbitRankTarget : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
    ∀ c p : Nat,
      w = CycleBridge.cycleWord c p →
      m = StringFlow.fiveXPlusOneOrbit 7 c →
      ∃ j : Nat,
        1 ≤ j ∧ j < p ∧
        w.getI (j - 1) = 2 ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        2 * j + 9 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1)

/-- The `¬ noLongT2Run` branch of the orbit-rank target: a real
`hcycle` word whose `t=2` runs contain the positive budget already
supplies the required prefix `j` and the concrete orbit valuation. -/
theorem cycleQb8InputT2OrbitRankTarget_of_noLongT2Run_false
    {m S P : Nat} {w rise c3 : List Nat}
    (_h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat)
    (hw : w = CycleBridge.cycleWord c p)
    (_hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hnot : ¬ noLongT2Run c p) :
    ∃ j : Nat,
      1 ≤ j ∧ j < p ∧
        w.getI (j - 1) = 2 ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        2 * j + 9 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
  have hb : cycleWordT2RunBudget c p :=
    cycleWordT2RunBudget_of_noLongT2Run_false c p hnot
  rcases cycleWordT2RankOfBudget c p hb with
    ⟨j, hj1, hjp, hinc, hout, hrk⟩
  refine ⟨j, hj1, hjp, ?_, ?_, hrk⟩
  · simpa [hw] using hinc
  · simpa [hw] using hout

/-- The orbit-rank target follows once the strict run-sum comparison
`L > U` is supplied; the `¬ noLongT2Run` branch then supplies the
concrete `j`. -/
theorem cycleQb8InputT2OrbitRankTarget_of_rank_gt
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (c p : Nat) (hw : w = CycleBridge.cycleWord c p)
    (hm : m = StringFlow.fiveXPlusOneOrbit 7 c)
    (hgt : t2RunRankSumGtBoundSum c p) :
    ∃ j : Nat,
      1 ≤ j ∧ j < p ∧
        w.getI (j - 1) = 2 ∧
        (w.getI j = 1 ∨ w.getI j = 2) ∧
        2 * j + 9 ≤ twoValuation
          (StringFlow.fiveXPlusOneOrbit 7 (c + j) + 1) := by
  by_cases hno : noLongT2Run c p
  · exact False.elim (noLongT2Run_false_of_t2RunRankSumGtBoundSum c p hgt hno)
  · exact cycleQb8InputT2OrbitRankTarget_of_noLongT2Run_false h c p hw hm hno

/-- The remaining combinatorial target under the concrete `hcycle`
parameters: every real `CycleQb8Input` supplies a
`cycleWordT2RunBudget`. -/
def cycleQb8InputT2RunBudget : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
      ∃ c p : Nat, w = CycleBridge.cycleWord c p ∧
        m = StringFlow.fiveXPlusOneOrbit 7 c ∧
        cycleWordT2RunBudget c p

/-- The `t=2` run budget closes the hfail rank-lower-bound interface:
the internal rank bridge and the existing `hcycle` prefix identity do
all remaining rewriting. -/
theorem hfailRankLowerBoundTarget_of_t2_run_budget
    (hbudget : cycleQb8InputT2RunBudget) :
    hfailRankLowerBoundTarget := by
  intro m S P w rise c3 h
  rcases hbudget m S P w rise c3 h with ⟨c, p, hw, hm, hb⟩
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hS : S = StringFlow.wordWeight (CycleBridge.cycleWord c p) := by
    rw [← h.hweight, hw]
  exact cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt
    h c p hw hm hP hS
    (cycleWordInternalRankLowerBound_of_t2_run_budget_exists c p hb)

/-- The exact orbit-rank target closes the hfail rank interface:
the outgoing condition is explicit, and the rank is rewritten through
`cycleWordInternalRankLowerBound_of_orbit_rank`. -/
theorem hfailRankLowerBoundTarget_of_t2_orbit_rank
    (hrank : cycleQb8InputT2OrbitRankTarget) :
    hfailRankLowerBoundTarget := by
  intro m S P w rise c3 h
  rcases CycleBridge.cycleQb8Input_cycle_params h with
    ⟨c, p, hw, hm, _hS, _hrise, _hc3⟩
  rcases hrank m S P w rise c3 h c p hw hm with
    ⟨j, hj1, hjp, hinc, hout, hrk⟩
  have hP : P = p := by
    rw [← h.hlength, hw, CycleBridge.cycleWord_length]
  have hS : S = StringFlow.wordWeight (CycleBridge.cycleWord c p) := by
    rw [← h.hweight, hw]
  have hinc' : (CycleBridge.cycleWord c p).getI (j - 1) = 2 := by
    simpa [hw] using hinc
  have hout' : (CycleBridge.cycleWord c p).getI j = 1 ∨
      (CycleBridge.cycleWord c p).getI j = 2 := by
    simpa [hw] using hout
  exact cycleWordInternalRankLowerBound_to_hfailRankLowerBoundAt
    h c p hw hm hP hS
    (cycleWordInternalRankLowerBound_of_orbit_rank
      c p j hj1 hjp hinc' hout' hrk)

/-- Internal assembly bridge, not a standalone pending proposition: a
real-prefix rank lower bound at a real orbit depth carries a real
terminal `rt` and a genuine `ResetHeadEq`.  The old name is kept for
continuity, but the `j` source is `realPrefixDepth`, not `badPrefixAt`.
The local `hfail_t1/t2_of_hfailRankLowerBoundAt` conversions only
reduce a rank bound inside an already constructed `LocalHidentBlock`;
they do not connect a bare rank to the failure window. -/
def bad_prefix_terminal_alignment : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
    ∀ j t : Nat,
      1 ≤ j → j < P → realPrefixDepth m w j →
      (t = 1 ∨ t = 2) →
      w.getI (j - 1) = t →
      hfailRankLowerBoundAt m w j t →
      ∃ rt : S6Audit.AngelinaGilbertaRealTerminal, ∃ delta : Nat,
        ((t = 1 → delta = 1) ∧ (t = 2 → delta = 1 ∨ delta = 3)) ∧
        S6Audit.ResetHeadEq rt.s j rt.k t delta
          (StringFlow.Word.wordOrbit (w.take j) m)

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

/-- Period closure inside one cyclic rise block: the rank spent by
`t=2` steps is paid by the C3-tail rank plus the `t=1` recharge, and
the rise suffix returns to rank two. -/
theorem cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    CycleBridge.cycleRiseBlockCharge d r +
        CycleBridge.cycleRiseBlockTailRank d r =
      2 * CycleBridge.riseCountTwo (d.suffixWord r) + 2 := by
  let head := CycleBridge.cycleRiseBlockC3TailState d r
  have hfull : S6Audit.FullOrbitFrom7 head := by
    dsimp [head]
    have htail_lt : CycleBridge.cycleRiseBlockTailDepth d r - 1 < P :=
      CycleBridge.cycleRiseBlockTailDepth_lt_succ d r hr
    have hle : d.headDepth r + (d.c3Word r).length ≤ w.length := by
      dsimp [CycleBridge.cycleRiseBlockTailDepth] at htail_lt
      have hP : w.length = P := d.hperiod
      omega
    exact CycleBridge.cycleQb8Input_prefix_full_reachable h
      (d.headDepth r + (d.c3Word r).length) hle
  have hodd : S6Audit.IsOdd head := S6Audit.FullOrbitFrom7_odd head hfull
  have hendRank : twoValuation
      (CycleBridge.cycleRiseBlockSuffixEndpointState d r + 1) = 2 :=
    cycleRiseBlockSuffixEndpointRank_two_all d r hr
  have hbal := riseChargeSum_add_initial_eq_two_mul_countTwo_add_endpoint
    head (d.suffixWord r) hodd (d.hsuffix_one_two r hr) (d.hsuffix_exact r hr)
  unfold CycleBridge.cycleRiseBlockCharge at hbal ⊢
  unfold CycleBridge.cycleRiseBlockTailRank at ⊢
  dsimp [head] at hbal ⊢
  have hendRank' : twoValuation
      (CycleBridge.riseRun (CycleBridge.cycleRiseBlockC3TailState d r)
        (d.suffixWord r) + 1) = 2 := by
    simpa [CycleBridge.cycleRiseBlockSuffixEndpointState] using hendRank
  rw [hendRank'] at hbal
  omega

/-- Summed period-closure identity over all cyclic rise blocks:
`Σ charge + Σ tailRank = 2·H2 + 2·K`. -/
theorem cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockCharge d r)).sum +
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum =
      2 * CycleBridge.cycleRiseBlockH2Sum d + 2 * d.blockCount := by
  have hsumPer : ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockCharge d r +
        CycleBridge.cycleRiseBlockTailRank d r)).sum =
      ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r) + 2)).sum := by
    have hmapPer : (List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockCharge d r +
          CycleBridge.cycleRiseBlockTailRank d r) =
      (List.range d.blockCount).map
        (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r) + 2) := by
      apply List.map_congr_left
      intro r hr
      exact cycleRiseBlockCharge_add_tailRank_eq_two_mul_H2_add_two h d r
        (List.mem_range.mp hr)
    rw [hmapPer]
  have hsplit : ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockCharge d r +
        CycleBridge.cycleRiseBlockTailRank d r)).sum =
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockCharge d r)).sum +
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockTailRank d r)).sum := by
    rw [List.sum_map_add]
  have hright : ((List.range d.blockCount).map
      (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r) + 2)).sum =
      2 * CycleBridge.cycleRiseBlockH2Sum d + 2 * d.blockCount := by
    rw [List.sum_map_add]
    dsimp [CycleBridge.cycleRiseBlockH2Sum]
    have hA : ((List.range d.blockCount).map
        (fun r => 2 * CycleBridge.riseCountTwo (d.suffixWord r))).sum =
        2 * ((List.range d.blockCount).map
          (fun r => CycleBridge.riseCountTwo (d.suffixWord r))).sum := by
      exact StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
        (fun r => CycleBridge.riseCountTwo (d.suffixWord r))
    have hB : ((List.range d.blockCount).map (fun _ => 2)).sum =
        2 * d.blockCount := by
      rw [List.map_const', List.sum_replicate, List.length_range]
      simp [Nat.mul_comm]
    rw [hA, hB]
  rw [hsplit] at hsumPer
  rw [hright] at hsumPer
  exact hsumPer

/-- Combining the period-closure identity with the C3 chain rank-gain
telescope gives the global recovery budget:
`Σ charge + Σ residual = 2·H2 + Σ c3Weight`. -/
theorem cycleRiseBlockChargeSum_add_residualSum_eq_two_mul_H2_add_c3WeightSum
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3)
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
      (fun r => CycleBridge.cycleRiseBlockCharge d r)).sum +
      ((List.range d.blockCount).map
        (fun r => CycleBridge.cycleRiseBlockC3ResidualSum d r)).sum =
      2 * CycleBridge.cycleRiseBlockH2Sum d +
        ((List.range d.blockCount).map (fun r => (d.c3Word r).sum)).sum := by
  have hper := cycleRiseBlockChargeSum_add_tailRankSum_eq_two_mul_H2_add_two_mul_blockCount
    h d
  have hc3 := CycleBridge.cycleRiseBlockTailRankSum_add_c3WeightSum d
  omega

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

/-- The open budget side of the rank target: a rise block whose exact
tail lower bound `2+2N-F` already crosses the tail-depth threshold. -/
def hfailBudgetLowerBoundAt {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat) : Prop :=
  2 * (CycleBridge.cycleRiseBlockTailDepth d r + 1) + 11 ≤
    2 + 2 * CycleBridge.riseCountTwo (d.suffixWord r) -
      CycleBridge.cycleRiseBlockCharge d r

/-- The budget threshold is exactly the `t=2` budget form
`2b+11 ≤ 2N-F` after the exact block identity
`charge + tailRank = 2N + 2` cancels the two units. -/
theorem hfailBudgetLowerBoundAt_iff_t2_budget
    {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) (r : Nat) :
    hfailBudgetLowerBoundAt d r ↔
      2 * CycleBridge.cycleRiseBlockTailDepth d r + 11 ≤
        2 * CycleBridge.riseCountTwo (d.suffixWord r) -
          CycleBridge.cycleRiseBlockCharge d r := by
  unfold hfailBudgetLowerBoundAt
  omega

/-- Every cyclic rise block is strictly below the budget threshold:
`2N-F ≤ 2b+10`.  The real-orbit contradiction shows this cannot hold
together with `2^S > 5^P` on a concrete `hcycle` word. -/
def cycleRiseBlockAllBelowBudget {m S P : Nat} {w : List Nat}
    (d : CycleBridge.CycleRiseBlockDecomposition m S P w) : Prop :=
  ∀ r : Nat, r < d.blockCount →
    2 * CycleBridge.riseCountTwo (d.suffixWord r) -
        CycleBridge.cycleRiseBlockCharge d r ≤
      2 * CycleBridge.cycleRiseBlockTailDepth d r + 10

/-- The exact missing `N`/`F` budget: some cyclic rise block satisfies
`2+2N-F` at or above the tail-depth threshold. -/
def hfailBudgetLowerBound : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleBridge.CycleQb8Input m S P w rise c3 →
      ∃ d : CycleBridge.CycleRiseBlockDecomposition m S P w,
        ∃ r : Nat, r < d.blockCount ∧ hfailBudgetLowerBoundAt d r

/-- The budget proposition is exactly what converts the exact
tail-rank lower bound into a concrete tail-rank threshold. -/
theorem tailRankThreshold_of_hfailBudget
    (hbudget : hfailBudgetLowerBound)
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleBridge.CycleQb8Input m S P w rise c3) :
    ∃ d : CycleBridge.CycleRiseBlockDecomposition m S P w,
      ∃ r : Nat, r < d.blockCount ∧
        2 * (CycleBridge.cycleRiseBlockTailDepth d r + 1) + 11 ≤
          CycleBridge.cycleRiseBlockTailRank d r := by
  rcases hbudget m S P w rise c3 h with ⟨d, r, hr, hb⟩
  exact ⟨d, r, hr, le_trans hb
    (cycleRiseBlockTailRank_lower_of_endpoint_two d r hr)⟩

/-
`cycleQb8Input_bad_prefix_exists` is withdrawn as an open hfail input.
The 13-cycle shadow `(13,33,83)` with word `(1,1,5)` satisfies every
structural field of `CycleBridge.CycleQb8Input` except `hstart`/`hcycle`
and has `badCount = 0`, so `cycleWord_pmi_b_count` +
`cycleQb8Input_weak_comparison` + `cycleQb8Input_last_step_c3` cannot
force a bad prefix.  It must not be used as an hfail prerequisite; if
the main no-cycle theorem ever needs it internally (under `OrbitCycle
7`), it must be rederived from the concrete `hcycle` occurrence `(c,p)`
with `m = fiveXPlusOneOrbit 7 c`, not assumed from the shadow. -/

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

/-- Final contradiction algebra, `t=1`: an internal rank lower bound
`2j+11 ≤ v2(rj+1)` at a reset head contradicts the corrected window
upper bound.  This is the closing step of the no-cycle assembly; it
does not produce the rank bound itself. -/
theorem rank_lower_contradicts_corrected_upper_t1
    (j k0 s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 1 1 rj)
    (hlow : 2 * j + 11 ≤ twoValuation (rj + 1))
    (hup : BlockAutomaton.t1WindowValue j k0 s ≤ 2 * j + 11) :
    False := by
  have hiff := RealOrbitLocalLemma.t1WindowBoundCorrected_iff_rj_rank
    j k0 s rj hreset
  have hrankup : twoValuation (rj + 1) ≤ 2 * j + 10 := hiff.mp hup
  omega

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

/-- Final contradiction algebra, `t=2`: an internal rank lower bound
`2j+9 ≤ v2(rj+1)` at a reset head contradicts the corrected window
upper bound.  This is the closing step of the no-cycle assembly; it
does not produce the rank bound itself. -/
theorem rank_lower_contradicts_corrected_upper_t2
    (j k0 δ s rj : Nat)
    (hreset : S6Audit.ResetHeadEq s j k0 2 δ rj)
    (hlow : 2 * j + 9 ≤ twoValuation (rj + 1))
    (hup : BlockAutomaton.t2WindowValue j k0 δ s ≤ 2 * j + 10) :
    False := by
  have hiff := RealOrbitLocalLemma.t2WindowBoundCorrected_iff_rj_rank
    j k0 δ s rj hreset
  have hrankup : twoValuation (rj + 1) ≤ 2 * j + 8 := hiff.mp hup
  omega

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

/-- Local conversion only: it turns a rank bound inside an already
constructed `LocalHidentBlock` into the `t=1` window bound.  It does not
connect a bare bad-prefix rank to the failure window; that connection is
`bad_prefix_terminal_alignment`. -/
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

/-- Local conversion only: see `hfail_t1_of_hfailRankLowerBoundAt`. -/
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
