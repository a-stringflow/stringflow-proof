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
    (runs.map (fun run => twoValuation (r (run.start + 1)) -
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
      have hdiff : twoValuation (r (run.start + 1)) -
          twoValuation (r (run.start + run.length) + 1) = 2 * run.length := by
        exact Nat.sub_eq_of_eq_add
          (a := twoValuation (r (run.start + 1)))
          (b := twoValuation (r (run.start + run.length) + 1))
          (c := 2 * run.length) hsingle
      rw [ih htail hdiv_tail, hdiff]
      ring

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

/-- The remaining pure combinatorial budget: prefix `j` is entered by a
`t=2` step and is followed by a pure `t=2` run of length `N` with
`2j+9 <= 2N`. -/
def cycleWordT2RunBudget (c p : Nat) : Prop :=
  ∃ j N : Nat,
    1 ≤ j ∧ j + N ≤ p ∧
    2 * j + 9 ≤ 2 * N ∧
    (CycleBridge.cycleWord c p).getI (j - 1) = 2 ∧
    (∀ i : Nat, i < N → (CycleBridge.cycleWord c p).getI (j + i) = 2)

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
