import Mathlib
import Gc
import Gc7Window
import PhOne
import Td1Final
import Td1Interp

/-!
# TD-0/TD-1 real-system bridge

This module imports Mathlib's real numbers and connects the cleared
GC-7 window to the section-13.1 real window:

    m <= (5 + (5/3) * 2^delta) / (5 * (2^delta - 1)),

where `2^delta = 2^T / 5^P` is realized by `Real.log` and `Real.rpow`.
The TD-0/TD-1 final assembly is stated in `Td0Final.lean`.
-/

namespace StringFlow.TD0

/-- The exact ratio `2^T / 5^P` as a real number. -/
noncomputable def qReal (T P : Nat) : Real :=
  (((2 ^ T : Nat) : Real) / ((5 ^ P : Nat) : Real))

/-- `log_2 q` using Mathlib's real logarithm. -/
noncomputable def deltaOfQ (q : Real) : Real :=
  Real.log q / Real.log 2

/-- `2^delta = q` for every positive real `q`. -/
theorem two_rpow_deltaOfQ (q : Real) (hq : 0 < q) :
    (2 : Real) ^ deltaOfQ q = q := by
  unfold deltaOfQ
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2)
      (Real.log q / Real.log 2)]
  have hlog2 : Real.log (2 : Real) ≠ 0 := by
    have hpos : 0 < Real.log (2 : Real) :=
      Real.log_pos (by norm_num : (1 : Real) < 2)
    exact ne_of_gt hpos
  have hprod : Real.log (2 : Real) * (Real.log q / Real.log (2 : Real)) =
      Real.log q := by
    field_simp [hlog2]
  rw [hprod]
  exact Real.exp_log hq

/-- The ratio is positive for every `T, P`. -/
theorem qReal_pos (T P : Nat) : 0 < qReal T P := by
  unfold qReal
  exact div_pos (Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 2)))
    (Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 5)))

/-- The ratio is strictly greater than one when `2^T - 5^P > 0`. -/
theorem qReal_gt_one (T P : Nat) (hD : 0 < 2 ^ T - 5 ^ P) :
    1 < qReal T P := by
  have hlt : (5 ^ P : Nat) < 2 ^ T := by omega
  unfold qReal
  have h5pos : 0 < ((5 ^ P : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 5))
  have hlt' : ((5 ^ P : Nat) : Real) < ((2 ^ T : Nat) : Real) := by
    exact_mod_cast hlt
  exact (one_lt_div h5pos).2 hlt'

/-- `2^T = 5^P * (2^T / 5^P)` as a real identity. -/
theorem two_pow_eq_five_pow_mul_q (T P : Nat) :
    ((2 ^ T : Nat) : Real) = ((5 ^ P : Nat) : Real) * qReal T P := by
  unfold qReal
  have h5 : ((5 ^ P : Nat) : Real) ≠ 0 := by
    exact_mod_cast (pow_ne_zero P (by norm_num : (5 : Nat) ≠ 0))
  field_simp [h5]

/-- The real logarithm base 2. -/
noncomputable def log2Real (x : Real) : Real :=
  Real.log x / Real.log 2

/-- `log_2(2^T / 5^P) = T - P log_2 5` as a real identity. -/
theorem deltaOfQ_eq_sub (T P : Nat) :
    deltaOfQ (qReal T P) =
      (T : Real) - (P : Real) * log2Real 5 := by
  unfold deltaOfQ log2Real qReal
  have h2pow : ((2 ^ T : Nat) : Real) ≠ 0 := by
    exact_mod_cast (pow_ne_zero T (by norm_num : (2 : Nat) ≠ 0))
  have h5pow : ((5 ^ P : Nat) : Real) ≠ 0 := by
    exact_mod_cast (pow_ne_zero P (by norm_num : (5 : Nat) ≠ 0))
  have hlog2 : Real.log (2 : Real) ≠ 0 := by
    have hpos : 0 < Real.log (2 : Real) :=
      Real.log_pos (by norm_num : (1 : Real) < 2)
    exact ne_of_gt hpos
  rw [Real.log_div h2pow h5pow]
  rw [Nat.cast_pow, Nat.cast_pow]
  rw [Real.log_pow, Real.log_pow]
  field_simp [hlog2]
  ring_nf

/-- `log_2 5 < 19/8`, from the integer power comparison
`5^8 < 2^19`. -/
theorem log2_five_lt_nineteen_eighths :
    log2Real 5 < (19 / 8 : Real) := by
  unfold log2Real
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  have hpow : (5 ^ 8 : Nat) < 2 ^ 19 := by norm_num
  have hpowReal : ((5 ^ 8 : Nat) : Real) < ((2 ^ 19 : Nat) : Real) := by
    exact_mod_cast hpow
  have hloglt : Real.log ((5 ^ 8 : Nat) : Real) <
      Real.log ((2 ^ 19 : Nat) : Real) :=
    Real.log_lt_log (by positivity) hpowReal
  have h5 : Real.log ((5 ^ 8 : Nat) : Real) = 8 * Real.log (5 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h2 : Real.log ((2 ^ 19 : Nat) : Real) = 19 * Real.log (2 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [h5, h2] at hloglt
  exact (div_lt_iff₀ hlog2).2 (by nlinarith)

/-- `log_2 5 > 2`. -/
theorem log2_five_gt_two : (2 : Real) < log2Real 5 := by
  unfold log2Real
  have hlt : Real.log (4 : Real) < Real.log (5 : Real) :=
    Real.log_lt_log (by norm_num : 0 < (4 : Real)) (by norm_num : (4 : Real) < 5)
  have h4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4] at hlt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  rw [lt_div_iff₀ hlog2]
  exact hlt

/-- `log_2(4/3) < 1/2`, from `(4/3)^2 < 2`. -/
theorem log2_four_thirds_lt_half :
    log2Real (4 / 3) < (1 / 2 : Real) := by
  unfold log2Real
  have hlt : (4 / 3 : Real) ^ 2 < 2 := by norm_num
  have hpos : 0 < (4 / 3 : Real) := by norm_num
  have hloglt : Real.log ((4 / 3 : Real) ^ 2) < Real.log (2 : Real) :=
    Real.log_lt_log (by positivity) hlt
  have hpow : Real.log ((4 / 3 : Real) ^ 2) =
      2 * Real.log (4 / 3 : Real) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hloglt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  rw [div_lt_iff₀ hlog2]
  nlinarith

/-- Margin-balance necessary condition: if a prefix has nonnegative
margin `N*log2 5 - W_N >= 0`, then its minimal step-weight counts
satisfy `(3-log2 5)*C3 <= (log2 5-1)*C1 + (log2 5-2)*C2`. -/
theorem margin_balance_necessary (c1 c2 c3 : Nat)
    (h : (c1 + c2 + c3 : Real) * log2Real 5 ≥
      (c1 + 2 * c2 + 3 * c3 : Real)) :
    (3 - log2Real 5) * (c3 : Real) ≤
      (log2Real 5 - 1) * (c1 : Real) +
        (log2Real 5 - 2) * (c2 : Real) := by
  nlinarith

/-- Strict version of the margin-balance necessary condition. -/
theorem margin_balance_necessary_strict (c1 c2 c3 : Nat)
    (h : (c1 + c2 + c3 : Real) * log2Real 5 >
      (c1 + 2 * c2 + 3 * c3 : Real)) :
    (3 - log2Real 5) * (c3 : Real) <
      (log2Real 5 - 1) * (c1 : Real) +
        (log2Real 5 - 2) * (c2 : Real) := by
  nlinarith

/-- From `2^W < 5^j` one obtains `W < j*log_2 5`. -/
theorem log2_of_pow_lt_pow (W j : Nat) (h : 2 ^ W < 5 ^ j) :
    (W : Real) < (j : Real) * log2Real 5 := by
  unfold log2Real
  have hpos2 : 0 < ((2 ^ W : Nat) : Real) := by positivity
  have hpos5 : 0 < ((5 ^ j : Nat) : Real) := by positivity
  have hlt : ((2 ^ W : Nat) : Real) < ((5 ^ j : Nat) : Real) := by
    exact_mod_cast h
  have hloglt := Real.log_lt_log hpos2 hlt
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow] at hloglt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  field_simp [hlog2.ne'] at hloglt ⊢
  norm_num at hloglt
  nlinarith

/-- From `2^S < 2 * 5^P` one obtains `S < P*log_2 5 + 1`. -/
theorem log2_of_pow_lt_two_mul (S P : Nat) (h : 2 ^ S < 2 * 5 ^ P) :
    (S : Real) < (P : Real) * log2Real 5 + 1 := by
  unfold log2Real
  have hpowR : ((2 ^ S : Nat) : Real) < ((2 * 5 ^ P : Nat) : Real) := by
    exact_mod_cast h
  have h2lt : ((2 ^ S : Nat) : Real) <
      (2 : Real) * ((5 ^ P : Nat) : Real) := by
    exact_mod_cast h
  have h2s : 0 < ((2 ^ S : Nat) : Real) := by positivity
  have h5p : 0 < ((5 ^ P : Nat) : Real) := by positivity
  have hloglt : Real.log ((2 ^ S : Nat) : Real) <
      Real.log ((2 : Real) * ((5 ^ P : Nat) : Real)) :=
    Real.log_lt_log h2s h2lt
  have hlogmul : Real.log ((2 : Real) * ((5 ^ P : Nat) : Real)) =
      Real.log (2 : Real) + Real.log ((5 ^ P : Nat) : Real) := by
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (by positivity : ((5 ^ P : Nat) : Real) ≠ 0)]
  rw [hlogmul] at hloglt
  have h2 : Real.log ((2 ^ S : Nat) : Real) =
      (S : Real) * Real.log (2 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h5 : Real.log ((5 ^ P : Nat) : Real) =
      (P : Real) * Real.log (5 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [h2, h5] at hloglt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  field_simp [hlog2.ne'] at hloglt ⊢
  nlinarith

/-- From `5^j < 2^W` one obtains `j*log_2 5 < W`. -/
theorem log2_of_pow_gt_pow (W j : Nat) (h : 5 ^ j < 2 ^ W) :
    (j : Real) * log2Real 5 < (W : Real) := by
  unfold log2Real
  have hpos5 : 0 < ((5 ^ j : Nat) : Real) := by positivity
  have hpos2 : 0 < ((2 ^ W : Nat) : Real) := by positivity
  have hlt : ((5 ^ j : Nat) : Real) < ((2 ^ W : Nat) : Real) := by
    exact_mod_cast h
  have hloglt := Real.log_lt_log hpos5 hlt
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow] at hloglt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  field_simp [hlog2.ne'] at hloglt ⊢
  norm_num at hloglt
  nlinarith

/-- Number of `t=1` entries in a list. -/
def countOne (l : List Nat) : Nat :=
  (l.filter (fun t => t = 1)).length

/-- Number of `t=2` entries in a list. -/
def countTwo (l : List Nat) : Nat :=
  (l.filter (fun t => t = 2)).length

/-- Number of entries at least `3`. -/
def countAtLeastThree (l : List Nat) : Nat :=
  (l.filter (fun t => 3 ≤ t)).length

/-- Every positive entry is counted by exactly one of the three
classes. -/
theorem count_sum_length (l : List Nat) (hpos : ∀ t ∈ l, 1 ≤ t) :
    countOne l + countTwo l + countAtLeastThree l = l.length := by
  induction l with
  | nil => simp [countOne, countTwo, countAtLeastThree]
  | cons t ts ih =>
      have hpos_t : 1 ≤ t := hpos t (by simp)
      have hpos_ts : ∀ u ∈ ts, 1 ≤ u := by
        intro u hu
        exact hpos u (by simp [hu])
      by_cases h1 : t = 1
      · subst t
        simp [countOne, countTwo, countAtLeastThree]
        unfold countOne countTwo countAtLeastThree at ih
        have hih := ih hpos_ts
        rw [← hih]
        omega
      · by_cases h2 : t = 2
        · subst t
          simp [countOne, countTwo, countAtLeastThree]
          unfold countOne countTwo countAtLeastThree at ih
          have hih := ih hpos_ts
          rw [← hih]
          omega
        · by_cases h3 : 3 ≤ t
          · simp [countOne, countTwo, countAtLeastThree, h1, h2, h3]
            unfold countOne countTwo countAtLeastThree at ih
            have hih := ih hpos_ts
            rw [← hih]
            omega
          · exfalso
            omega

/-- The weighted count lower bound is at most the total word weight. -/
theorem counts_weight_le (l : List Nat) :
    countOne l + 2 * countTwo l + 3 * countAtLeastThree l ≤
      StringFlow.wordWeight l := by
  induction l with
  | nil => simp [countOne, countTwo, countAtLeastThree, StringFlow.wordWeight]
  | cons t ts ih =>
      by_cases h1 : t = 1
      · subst t
        simp [countOne, countTwo, countAtLeastThree, StringFlow.wordWeight]
        unfold countOne countTwo countAtLeastThree at ih
        omega
      · by_cases h2 : t = 2
        · subst t
          simp [countOne, countTwo, countAtLeastThree, StringFlow.wordWeight]
          unfold countOne countTwo countAtLeastThree at ih
          omega
        · by_cases h3 : 3 ≤ t
          · simp [countOne, countTwo, countAtLeastThree, StringFlow.wordWeight, h1, h2, h3]
            unfold countOne countTwo countAtLeastThree at ih
            omega
          · simp [countOne, countTwo, countAtLeastThree, StringFlow.wordWeight, h1, h2, h3]
            unfold countOne countTwo countAtLeastThree at ih
            omega

/-- Prefix weight of a list equals the sum of its `take`. -/
theorem prefixWeight_getI_eq_take_sum (l : List Nat) (j : Nat) :
    StringFlow.PMI.prefixWeight (fun j => l.getI j) j = (l.take j).sum := by
  induction j generalizing l with
  | zero => simp [StringFlow.PMI.prefixWeight]
  | succ j ih =>
      cases l with
      | nil =>
          simpa [StringFlow.PMI.prefixWeight] using ih ([] : List Nat)
      | cons t ts =>
          rw [StringFlow.PH.prefixWeight_cons_getI]
          rw [ih ts]
          simp [List.take, List.sum_cons]

/-- From the cycle equation and `A < 5^P + 2^T`, one obtains
`6 * 2^T < 8 * 5^P`. -/
theorem pow_six_lt_eight_mul (P T m A : Nat)
    (hcyc : 2 ^ T * m = 5 ^ P * m + A)
    (hD : 5 ^ P < 2 ^ T)
    (hm7 : 7 ≤ m)
    (hAlt : A < 5 ^ P + 2 ^ T) :
    6 * 2 ^ T < 8 * 5 ^ P := by
  have hDle : 5 ^ P ≤ 2 ^ T := by omega
  have hA : m * (2 ^ T - 5 ^ P) = A := by
    have hsub : 2 ^ T * m - 5 ^ P * m = A := by
      rw [hcyc]
      omega
    have hrewrite : m * (2 ^ T - 5 ^ P) = 2 ^ T * m - 5 ^ P * m := by
      rw [Nat.mul_sub, Nat.mul_comm m (2 ^ T), Nat.mul_comm m (5 ^ P)]
    rwa [← hrewrite] at hsub
  have h7le : 7 * (2 ^ T - 5 ^ P) ≤ m * (2 ^ T - 5 ^ P) :=
    Nat.mul_le_mul_right (2 ^ T - 5 ^ P) hm7
  have h7lt : 7 * (2 ^ T - 5 ^ P) < 5 ^ P + 2 ^ T := by
    have hle : 7 * (2 ^ T - 5 ^ P) ≤ A := by
      rwa [hA] at h7le
    exact lt_of_le_of_lt hle hAlt
  have hD7 : 7 * (2 ^ T - 5 ^ P) = 7 * 2 ^ T - 7 * 5 ^ P := by
    rw [Nat.mul_sub]
  rw [hD7] at h7lt
  omega

/-- From `6 * 2^T < 8 * 5^P`, take logarithms to get
`T < P * log_2 5 + log_2(4/3)`. -/
theorem log_lt_of_pow_six (P T : Nat) (hpow : 6 * 2 ^ T < 8 * 5 ^ P) :
    (T : Real) < (P : Real) * log2Real 5 + log2Real (4 / 3) := by
  unfold log2Real
  have hpowR : ((6 * 2 ^ T : Nat) : Real) < ((8 * 5 ^ P : Nat) : Real) := by
    exact_mod_cast hpow
  have h2lt : ((2 ^ T : Nat) : Real) <
      (4 / 3 : Real) * ((5 ^ P : Nat) : Real) := by
    have hpowR' : (6 : Real) * ((2 ^ T : Nat) : Real) <
        (8 : Real) * ((5 ^ P : Nat) : Real) := by
      convert hpowR using 1
      · norm_num
      · norm_num
    nlinarith
  have h2t : 0 < ((2 ^ T : Nat) : Real) := by positivity
  have h5p : 0 < ((5 ^ P : Nat) : Real) := by positivity
  have h43 : 0 < (4 / 3 : Real) := by norm_num
  have hloglt : Real.log ((2 ^ T : Nat) : Real) <
      Real.log ((4 / 3 : Real) * ((5 ^ P : Nat) : Real)) :=
    Real.log_lt_log h2t h2lt
  have hlogmul : Real.log ((4 / 3 : Real) * ((5 ^ P : Nat) : Real)) =
      Real.log (4 / 3 : Real) + Real.log ((5 ^ P : Nat) : Real) := by
    rw [Real.log_mul (by norm_num : (4 / 3 : Real) ≠ 0)
      (by positivity : ((5 ^ P : Nat) : Real) ≠ 0)]
  rw [hlogmul] at hloglt
  have h2 : Real.log ((2 ^ T : Nat) : Real) =
      (T : Real) * Real.log (2 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have h5 : Real.log ((5 ^ P : Nat) : Real) =
      (P : Real) * Real.log (5 : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [h2, h5] at hloglt
  have hlog2 : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 2)
  field_simp [hlog2.ne']
  nlinarith

/-- Structural B0: `6 * 2^T < 8 * 5^P`, `S <= 64`, and the
length/weight identities force `P < 205`, without any `tCeil` input. -/
theorem P_lt_205_of_pow_six (P Q b U S T : Nat)
    (hb1 : 1 ≤ b)
    (hUge0 : 0 ≤ U)
    (hS : S = P - Q + U)
    (hQleP : Q ≤ P)
    (hSle : S ≤ 64)
    (hT : T = S + 3 * Q + b)
    (hpow : 6 * 2 ^ T < 8 * 5 ^ P) :
    P < 205 := by
  let lam : Real := log2Real 5
  let c : Real := log2Real (4 / 3)
  have hlog := log_lt_of_pow_six P T hpow
  have hTR : (T : Real) = (S : Real) + 3 * (Q : Real) + (b : Real) := by
    exact_mod_cast hT
  have hSR : (S : Real) = (P : Real) - (Q : Real) + (U : Real) := by
    rw [hS]
    norm_cast
  have hlam : lam < 19 / 8 := by simpa [lam] using log2_five_lt_nineteen_eighths
  have hc : c < 1 / 2 := by simpa [c] using log2_four_thirds_lt_half
  have hb1' : (1 : Real) ≤ (b : Real) := by exact_mod_cast hb1
  have hU' : (0 : Real) ≤ (U : Real) := by exact_mod_cast hUge0
  have hSle' : (S : Real) ≤ 64 := by exact_mod_cast hSle
  have hQge0 : (0 : Real) ≤ (Q : Real) := by positivity
  have hQlt : (Q : Real) < 140 := by
    have hlog' : (T : Real) < (P : Real) * lam + c := by
      simpa [lam, c] using hlog
    have hQbound : (Q : Real) * (3 - lam) <
        (S : Real) * (lam - 1) - (U : Real) * lam - (b : Real) + c := by
      nlinarith
    nlinarith
  have hP : (P : Real) < 205 := by
    nlinarith
  exact_mod_cast hP

/-- A `{1,2}` word has `wordOK`. -/
theorem wordOK_of_mem_one_two (w : List Nat) (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    StringFlow.Word.wordOK w := by
  induction w with
  | nil => simp [StringFlow.Word.wordOK]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      have hok' : ∀ x ∈ ts, x = 1 ∨ x = 2 := by
        intro x hx
        exact hok x (by simp [hx])
      have ih' := ih hok'
      rcases ht with rfl | rfl <;> simp [StringFlow.Word.wordOK, ih']

/-- From the structural upper bounds, the total numerator satisfies
`A < 5^P + 2^T`. -/
theorem A_lt_five_pow_add_two_pow (b Q L _U S T P : Nat) (w : List Nat) (ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hwlen : w.length = L)
    (hb : b = 1 ∨ b = 2)
    (hQlen : ts.length = Q)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hsum : ts.sum = 3 * Q + b)
    (_hS : StringFlow.wordWeight w = S)
    (hP : P = L + Q)
    (hT : T = S + 3 * Q + b)
    (hA : 5 ^ Q * StringFlow.Word.wordA w +
        2 ^ S * StringFlow.GC.chainA ts = A) :
    A < 5 ^ P + 2 ^ T := by
  have hwOK : StringFlow.Word.wordOK w := wordOK_of_mem_one_two w hok
  have hAw : StringFlow.Word.wordA w < 5 ^ L := by
    simpa [hwlen] using (StringFlow.Word.wordA_lt_five_pow w hwOK)
  have hAc : StringFlow.GC.chainA ts < 2 * 8 ^ Q :=
    StringFlow.TD1.chainA_le_two_eight_pow b Q ts hb hQ2 hQlen hhead hge (by omega)
  have h1 : 5 ^ Q * StringFlow.Word.wordA w < 5 ^ Q * 5 ^ L :=
    Nat.mul_lt_mul_of_pos_left hAw (by positivity : 0 < 5 ^ Q)
  have h2 : 2 ^ S * StringFlow.GC.chainA ts < 2 ^ S * (2 * 8 ^ Q) :=
    Nat.mul_lt_mul_of_pos_left hAc (by positivity : 0 < 2 ^ S)
  have h5 : 5 ^ Q * 5 ^ L = 5 ^ P := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h8 : 2 ^ S * (2 * 8 ^ Q) = 2 ^ (S + 3 * Q + 1) := by
    have h83 : 8 ^ Q = 2 ^ (3 * Q) :=
      (StringFlow.GC.two_pow_three_mul_eq_eight_pow Q).symm
    rw [h83]
    have h2pow : 2 * 2 ^ (3 * Q) = 2 ^ (3 * Q + 1) := by
      rw [Nat.pow_add]
      ring
    rw [h2pow]
    rw [← Nat.pow_add]
    rw [Nat.add_assoc]
  have hTle : S + 3 * Q + 1 ≤ T := by rw [hT]; omega
  have h2T : 2 ^ (S + 3 * Q + 1) ≤ 2 ^ T :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hTle
  have hAlt : A < 5 ^ P + 2 ^ T := by
    rw [← hA]
    have hsumlt : 5 ^ Q * StringFlow.Word.wordA w +
        2 ^ S * StringFlow.GC.chainA ts < 5 ^ Q * 5 ^ L + 2 ^ S * (2 * 8 ^ Q) := by
      omega
    rw [h5, h8] at hsumlt
    have hle : 5 ^ Q * 5 ^ L + 2 ^ (S + 3 * Q + 1) ≤ 5 ^ P + 2 ^ T := by
      rw [h5]
      omega
    omega
  exact hAlt

/-- B0: from the `uReq` identity, `S <= 64`, the exact power
inequality `5^P < 2^T`, and the fractional-part bound `delta < 1`,
one obtains `P < 205`. -/
theorem P_lt_205_of_b0 (P Q b U T : Nat)
    (hb1 : 1 ≤ b)
    (hUge0 : 0 ≤ U)
    (hT : T = P + 2 * Q + b + U)
    (hSle : (T : Real) - ((3 * Q + b : Nat) : Real) ≤ 64)
    (hpow : 5 ^ P < 2 ^ T)
    (hδlt1 : (T : Real) - (P : Real) * log2Real 5 < 1) :
    P < 205 := by
  let lam : Real := log2Real 5
  let δ : Real := (T : Real) - (P : Real) * lam
  have hTReal : (T : Real) =
      (P : Real) + 2 * (Q : Real) + (b : Real) + (U : Real) := by
    exact_mod_cast hT
  have hU' : (0 : Real) ≤ (U : Real) := by exact_mod_cast hUge0
  have hb1' : (1 : Real) ≤ (b : Real) := by exact_mod_cast hb1
  have hδpos : 0 < δ := by
    have h5p : 0 < ((5 ^ P : Nat) : Real) := by positivity
    have h2t : 0 < ((2 ^ T : Nat) : Real) := by positivity
    have hloglt : Real.log ((5 ^ P : Nat) : Real) <
        Real.log ((2 ^ T : Nat) : Real) :=
      Real.log_lt_log h5p (by exact_mod_cast hpow)
    have h5 : Real.log ((5 ^ P : Nat) : Real) =
        (P : Real) * Real.log (5 : Real) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    have h2 : Real.log ((2 ^ T : Nat) : Real) =
        (T : Real) * Real.log (2 : Real) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    rw [h5, h2] at hloglt
    have hlog2pos : 0 < Real.log (2 : Real) :=
      Real.log_pos (by norm_num : (1 : Real) < 2)
    dsimp [lam, δ, log2Real]
    have hlt : (P : Real) * (Real.log (5 : Real) / Real.log (2 : Real)) <
        (T : Real) := by
      field_simp [hlog2pos.ne']
      nlinarith
    nlinarith
  have hδlt1' : δ < 1 := by simpa [δ, lam] using hδlt1
  have hbd : 0 < (b : Real) - δ := by nlinarith
  have h2Q : (2 * Q : Real) ≤ (T : Real) - (P : Real) - (b : Real) := by
    nlinarith
  have h3Q : (3 * Q : Real) ≤
      (3 / 2 : Real) * ((T : Real) - (P : Real) - (b : Real)) := by
    nlinarith
  have hSdown : P * (3 - lam) / 2 + (b - δ) / 2 ≤
      (T : Real) - ((3 * Q + b : Nat) : Real) := by
    have hright : (T : Real) - ((3 * Q + b : Nat) : Real) =
        (T : Real) - 3 * (Q : Real) - (b : Real) := by
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    rw [hright]
    have hδeq : (T : Real) = (P : Real) * lam + δ := by
      unfold δ
      ring
    nlinarith
  have hPle : P * (3 - lam) / 2 < 64 := by
    have hsum := le_trans hSdown hSle
    have hpos : 0 < (b : Real) - δ := hbd
    nlinarith
  have hlam : lam < 19 / 8 := by simpa [lam] using log2_five_lt_nineteen_eighths
  have h3lpos : 0 < 3 - lam := by nlinarith
  have hPle' : (P : Real) < 128 / (3 - lam) := by
    have hPle'' : (P : Real) * (3 - lam) < 128 := by nlinarith
    rw [lt_div_iff₀ h3lpos]
    nlinarith
  have hbound : 128 / (3 - lam) < 205 := by
    rw [div_lt_iff₀ h3lpos]
    nlinarith
  have hP : (P : Real) < 205 := lt_of_lt_of_le hPle' (le_of_lt hbound)
  exact_mod_cast hP

/-- The section-13.1 `delta` with `T = tCeil P`. -/
noncomputable def deltaCeil (P : Nat) : Real :=
  deltaOfQ (qReal (StringFlow.tCeil P) P)

/-- `deltaCeil P = T(P) - P log_2 5`. -/
theorem deltaCeil_eq (P : Nat) :
    deltaCeil P =
      (StringFlow.tCeil P : Real) - (P : Real) * log2Real 5 := by
  unfold deltaCeil
  exact deltaOfQ_eq_sub (StringFlow.tCeil P) P

/-- GC-7 in the section-13.1 real ratio form. -/
theorem gc7_real_window_ratio (rise c3 : List Nat) (m : Nat)
    (hpm : StringFlow.GC.pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t)
    (hD : 0 < 2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) :
    (m : Real) ≤
      (5 + (5 / 3 : Real) * qReal (rise.sum + c3.sum)
        (rise.length + c3.length)) /
      (5 * (qReal (rise.sum + c3.sum) (rise.length + c3.length) - 1)) := by
  let T : Nat := rise.sum + c3.sum
  let P : Nat := rise.length + c3.length
  change (m : Real) ≤
    (5 + (5 / 3 : Real) * qReal T P) /
    (5 * (qReal T P - 1))
  have hnat := StringFlow.GC.gc7_m_cleared_bound rise c3 m hpm hrise hc3
  have hcast : ((3 * m * (2 ^ T - 5 ^ P) : Nat) : Real) ≤
      ((3 * 5 ^ P + 2 ^ T : Nat) : Real) := by
    dsimp [T, P]
    exact_mod_cast hnat
  have hle : 5 ^ P ≤ 2 ^ T := by
    dsimp [T, P]
    omega
  have hsub : ((2 ^ T - 5 ^ P : Nat) : Real) =
      ((2 ^ T : Nat) : Real) - ((5 ^ P : Nat) : Real) := by
    exact Nat.cast_sub hle
  have hcastReal :
      (3 : Real) * (m : Real) *
          (((2 ^ T : Nat) : Real) - ((5 ^ P : Nat) : Real)) ≤
        (3 * ((5 ^ P : Nat) : Real) + ((2 ^ T : Nat) : Real)) := by
    have hrewrite : ((3 * m * (2 ^ T - 5 ^ P) : Nat) : Real) =
        (3 : Real) * (m : Real) *
          (((2 ^ T : Nat) : Real) - ((5 ^ P : Nat) : Real)) := by
      norm_cast
    have hrhs : ((3 * 5 ^ P + 2 ^ T : Nat) : Real) =
        (3 : Real) * ((5 ^ P : Nat) : Real) + ((2 ^ T : Nat) : Real) := by
      norm_cast
    rw [hrewrite, hrhs] at hcast
    exact hcast
  have hpow : ((2 ^ T : Nat) : Real) =
      ((5 ^ P : Nat) : Real) * qReal T P := by
    exact two_pow_eq_five_pow_mul_q T P
  rw [hpow] at hcastReal
  have h5pos : 0 < ((5 ^ P : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 5))
  have hqgt : 1 < qReal T P := qReal_gt_one T P (by dsimp [T, P]; exact hD)
  have hqpos : 0 < qReal T P := by linarith
  have hq1 : 0 < qReal T P - 1 := by linarith
  have hden : 0 < 5 * (qReal T P - 1) := by positivity
  have hden3 : 0 < 3 * (qReal T P - 1) := by positivity
  have hcast' : 3 * (m : Real) * (qReal T P - 1) ≤ 3 + qReal T P := by
    have htmp := hcastReal
    field_simp [h5pos.ne'] at htmp
    nlinarith [htmp]
  have hm : (m : Real) * (3 * (qReal T P - 1)) ≤ 3 + qReal T P := by
    nlinarith [hcast']
  have hgoal : (m : Real) * (5 * (qReal T P - 1)) ≤
      5 + (5 / 3 : Real) * qReal T P := by
    have hmul : (5 / 3 : Real) * ((m : Real) * (3 * (qReal T P - 1))) ≤
        (5 / 3 : Real) * (3 + qReal T P) := by
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    ring_nf at hmul ⊢
    exact hmul
  exact (le_div_iff₀ hden).2 hgoal

/-- GC-7 in the section-13.1 real `delta` form. -/
theorem gc7_real_window_delta (rise c3 : List Nat) (m : Nat)
    (hpm : StringFlow.GC.pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t)
    (hD : 0 < 2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) :
    (m : Real) ≤
      (5 + (5 / 3 : Real) * (2 : Real) ^ deltaOfQ
        (qReal (rise.sum + c3.sum) (rise.length + c3.length))) /
      (5 * ((2 : Real) ^ deltaOfQ
        (qReal (rise.sum + c3.sum) (rise.length + c3.length)) - 1)) := by
  let T : Nat := rise.sum + c3.sum
  let P : Nat := rise.length + c3.length
  have hqpos : 0 < qReal T P := qReal_pos T P
  have hrewrite : (2 : Real) ^ deltaOfQ (qReal T P) = qReal T P :=
    two_rpow_deltaOfQ (qReal T P) hqpos
  rw [show (rise.sum + c3.sum) = T by rfl,
      show (rise.length + c3.length) = P by rfl]
  rw [hrewrite]
  exact gc7_real_window_ratio rise c3 m hpm hrise hc3 hD

/-- GC-7 excludes the upper half of the ceiling identity: a real
cycle with `m >= 7` has `2^T < 2 * 5^P`, without any prior
`tCeil`/feasibility input. -/
theorem pow_two_lt_two_mul_of_gc7 (rise c3 : List Nat) (m : Nat)
    (hpm : StringFlow.GC.pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t)
    (hm7 : 7 ≤ m)
    (hD : 0 < 2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) :
    2 ^ (rise.sum + c3.sum) < 2 * 5 ^ (rise.length + c3.length) := by
  let T : Nat := rise.sum + c3.sum
  let P : Nat := rise.length + c3.length
  change 2 ^ T < 2 * 5 ^ P
  by_contra hnot
  have hge : 2 * 5 ^ P ≤ 2 ^ T := by omega
  have hqge : (2 : Real) ≤ qReal T P := by
    unfold qReal
    have h5pos : 0 < ((5 ^ P : Nat) : Real) :=
      Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 5))
    rw [le_div_iff₀ h5pos]
    have hcast : ((2 * 5 ^ P : Nat) : Real) ≤ ((2 ^ T : Nat) : Real) := by
      exact_mod_cast hge
    simpa [Nat.cast_mul] using hcast
  have hwin : (m : Real) ≤
      (5 + (5 / 3 : Real) * qReal T P) / (5 * (qReal T P - 1)) := by
    simpa [T, P] using (gc7_real_window_ratio rise c3 m hpm hrise hc3 hD)
  have hden : 0 < 5 * (qReal T P - 1) := by
    have hq1 : 1 < qReal T P := qReal_gt_one T P (by dsimp [T, P]; exact hD)
    nlinarith
  have hgoal : 5 + (5 / 3 : Real) * qReal T P ≤
      (5 / 3 : Real) * (5 * (qReal T P - 1)) := by
    nlinarith [hqge]
  have hrhs : (5 + (5 / 3 : Real) * qReal T P) /
      (5 * (qReal T P - 1)) ≤ 5 / 3 := by
    exact (div_le_iff₀ hden).2 hgoal
  have hmle : (m : Real) ≤ 5 / 3 := le_trans hwin hrhs
  have hm7' : (7 : Real) ≤ (m : Real) := by exact_mod_cast hm7
  nlinarith

/-- The exact ceiling identity follows from GC-7 plus the certified
`P` range: `5^P < 2^T` gives `tCeil P <= T`, and the GC-7 window
gives `2^T < 2 * 5^P`, hence `T <= tCeil P`. -/
theorem tCeil_eq_of_gc7_and_cycle (rise c3 : List Nat) (m : Nat)
    (hpm : StringFlow.GC.pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t)
    (hm7 : 7 ≤ m)
    (hP9 : 9 ≤ rise.length + c3.length)
    (hP205 : rise.length + c3.length < 205)
    (hD : 0 < 2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) :
    StringFlow.tCeil (rise.length + c3.length) =
      rise.sum + c3.sum := by
  let T : Nat := rise.sum + c3.sum
  let P : Nat := rise.length + c3.length
  change StringFlow.tCeil P = T
  have hP9' : 9 ≤ P := by simpa [P] using hP9
  have hP205' : P < 205 := by simpa [P] using hP205
  have hle1 : StringFlow.tCeil P ≤ T :=
    StringFlow.tCeil_le_of_pow_lt P T hP9' hP205' (by
      dsimp [T, P]
      omega)
  have hle2 : T ≤ StringFlow.tCeil P :=
    StringFlow.tCeil_ge_of_pow_two_lt P T hP9' hP205'
      (pow_two_lt_two_mul_of_gc7 rise c3 m hpm hrise hc3 hm7 hD)
  omega

/-- The C3 tail shifts by the accumulated weight:
`c3PartFrom R c3 = 2^R * c3PartFrom 0 c3`. -/
theorem c3PartFrom_mul_shift (R : Nat) (c3 : List Nat) :
    StringFlow.GC.c3PartFrom R c3 =
      2 ^ R * StringFlow.GC.c3PartFrom 0 c3 := by
  induction c3 generalizing R with
  | nil => simp [StringFlow.GC.c3PartFrom]
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.GC.c3PartFrom]
      | cons u us =>
          simp [StringFlow.GC.c3PartFrom]
          rw [Nat.pow_add, Nat.pow_add, ih (R + t), ih t]
          ring

/-- The word weight is the list sum. -/
theorem wordWeight_eq_sum (l : List Nat) :
    StringFlow.wordWeight l = l.sum := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [StringFlow.wordWeight, ih]

/-- With an empty rising segment, `pmiTotal` is `5 * chainA`. -/
theorem pmiTotal_empty_rise (c3 : List Nat) (hne : c3 ≠ []) :
    StringFlow.GC.pmiTotal [] c3 = 5 * StringFlow.GC.chainA c3 := by
  unfold StringFlow.GC.pmiTotal
  simp [StringFlow.GC.risePart]
  induction c3 with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.GC.c3PartFrom, StringFlow.GC.chainA]
      | cons u us =>
          have hshift := c3PartFrom_mul_shift t (u :: us)
          have ih' := ih (by simp)
          simp [StringFlow.GC.chainA, StringFlow.GC.c3PartFrom] at ih'
          simp [StringFlow.GC.chainA, StringFlow.GC.c3PartFrom]
          rw [hshift]
          have ih'' : 5 ^ us.length * 5 + StringFlow.GC.c3PartFrom 0 (u :: us) =
              5 * (5 ^ us.length + 2 ^ u * StringFlow.GC.chainA us) := by
            simpa [Nat.pow_succ] using ih'
          have hmul := congrArg (fun x => 2 ^ t * x) ih''
          ring_nf at ih'
          ring_nf
          ring_nf at hmul
          nlinarith [hmul]

/-- The cleared PMI numerator is five times the total cycle numerator:
`pmiTotal rise c3 = 5 * (5^Q * wordA rise + 2^S * chainA c3)` for a
nonempty C3 segment. -/
theorem pmiTotal_eq_five_mul (rise c3 : List Nat) (hc3 : c3 ≠ []) :
    StringFlow.GC.pmiTotal rise c3 =
      5 * (5 ^ c3.length * StringFlow.Word.wordA rise +
        2 ^ StringFlow.wordWeight rise * StringFlow.GC.chainA c3) := by
  induction rise with
  | nil =>
      rw [pmiTotal_empty_rise c3 hc3]
      simp [StringFlow.Word.wordA, StringFlow.wordWeight]
  | cons t ts ih =>
      have hsum : StringFlow.wordWeight ts = ts.sum := wordWeight_eq_sum ts
      have hshift :
          StringFlow.GC.c3PartFrom (t + ts.sum) c3 =
            2 ^ t * StringFlow.GC.c3PartFrom (ts.sum) c3 := by
        rw [c3PartFrom_mul_shift (t + ts.sum) c3,
            c3PartFrom_mul_shift ts.sum c3]
        rw [Nat.pow_add]
        ring
      simp [StringFlow.GC.pmiTotal, StringFlow.GC.risePart,
        StringFlow.Word.wordA, StringFlow.wordWeight] at ih ⊢
      rw [hsum] at ih ⊢
      rw [hshift]
      have ih2 := congrArg (fun x => 2 ^ t * x) ih
      ring_nf at ih ⊢
      ring_nf at ih2
      nlinarith [ih2]

/-- The GC-7 numerator input `hpm` follows from the exact cycle
equation: `5^Q * wordA + 2^S * chainA = m * D` implies
`pmiTotal = 5 * m * D`. -/
theorem pmiTotal_eq_five_mul_D (rise c3 : List Nat) (m : Nat) (hc3 : c3 ≠ [])
    (hcyc : 5 ^ c3.length * StringFlow.Word.wordA rise +
        2 ^ StringFlow.wordWeight rise * StringFlow.GC.chainA c3 =
        m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length))) :
    StringFlow.GC.pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) := by
  rw [pmiTotal_eq_five_mul rise c3 hc3]
  rw [hcyc]
  ac_rfl

end StringFlow.TD0
