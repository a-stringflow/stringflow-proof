import S6Audit
import WordWindow
import PhTwo
import FinalStatement

/-!
# SURV-EX conditional audit interface

This module formalizes the SURV-EX / SURV-RAY conditional statement
53.4-LB as an explicit implication.  It does not prove the condition
fields; each field is an audit hypothesis whose status is documented
in `docs/surv_ex_fake_wall_audit.md`.  The L-B'c pre-insertion branch
is now proved as `lb_prime_c`; the other L-B' subcases remain open.

The only bridge proved here is the assembly step:
`SurvExConditions -> SurvEx53_4LB -> SurvExTd0 -> IsUnboundedOrbit 7`.
No field of `SurvExConditions` is asserted as a theorem.
-/

namespace StringFlow.SurvEx

/-- The word numerator agrees with the PH local factor. -/
theorem wordA_eq_localLambda (w : List Nat) :
    StringFlow.Word.wordA w = StringFlow.PH.localLambda w := by
  induction w with
  | nil => rfl
  | cons t ts ih =>
      simp [StringFlow.Word.wordA, StringFlow.PH.localLambda_cons, ih]

/-- Closed form for the all-ones word numerator:
`3 * A(ones L) = 5^L - 2^L`. -/
theorem wordA_ones_eq (L : Nat) :
    3 * StringFlow.Word.wordA (StringFlow.PH.ones L) =
      5 ^ L - 2 ^ L := by
  rw [wordA_eq_localLambda]
  exact StringFlow.PH.localLambda_ones_eq L

/-- Total weight of the all-ones word is its length. -/
theorem wordWeight_ones (L : Nat) :
    StringFlow.wordWeight (StringFlow.PH.ones L) = L := by
  induction L with
  | zero => simp [StringFlow.PH.ones, StringFlow.wordWeight]
  | succ L ih =>
      simp [StringFlow.PH.ones, StringFlow.wordWeight, ih]
      omega

/-- Number of `t=2` steps in a word. -/
def countTwo : List Nat → Nat
  | [] => 0
  | t :: ts => (if t = 2 then 1 else 0) + countTwo ts

/-- Membership in `{1,2}` implies `wordOK`. -/
theorem wordOK_of_mem_one_two (w : List Nat) (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    StringFlow.Word.wordOK w := by
  induction w with
  | nil => simp [StringFlow.Word.wordOK]
  | cons t ts ih =>
      simp [StringFlow.Word.wordOK]
      constructor
      · rcases hok t (by simp) with h1 | h2 <;> omega
      · exact ih (fun t ht => hok t (by simp [ht]))

/-- Structural H3 hypothesis: `2*U <= L+1` with last step weight 1. -/
def RisingWord (w : List Nat) : Prop :=
  (∀ t ∈ w, t = 1 ∨ t = 2) ∧
  StringFlow.Word.wordLast w = 1 ∧
  2 * countTwo w ≤ w.length + 1

/-- Least positive start in the word's C3 congruence class. -/
def MinimalStart (w : List Nat) : Nat :=
  StringFlow.Word.wordRepresentative w

/-- L-B' weak residual bound, exact integer form: `(5r)^5 >= 2^S`. -/
def LBPrimeWeak (w : List Nat) : Prop :=
  (5 * MinimalStart w) ^ 5 ≥ 2 ^ StringFlow.wordWeight w

/-- L-B' for all structurally valid rising words. -/
def LBPrimeAll : Prop :=
  ∀ w : List Nat, RisingWord w → LBPrimeWeak w

/-- L-B'a: `r ≡ 3 (mod 5)` implies the strong bound `r^5 >= 2^S`. -/
def LBPrimeA : Prop :=
  ∀ w : List Nat, RisingWord w →
    MinimalStart w % 5 = 3 →
    (MinimalStart w) ^ 5 ≥ 2 ^ StringFlow.wordWeight w

/-- L-B'b: `r ≡ 4 (mod 5)` implies `(3r)^5 >= 2^S`. -/
def LBPrimeB : Prop :=
  ∀ w : List Nat, RisingWord w →
    MinimalStart w % 5 = 4 →
    (3 * MinimalStart w) ^ 5 ≥ 2 ^ StringFlow.wordWeight w

/-- The pre-inserted start obtained by writing
`5 * r' + 1 = 2^t * (r + k * 2^(S+3))`. -/
def preinsertedStart (w : List Nat) (t k : Nat) : Nat :=
  (2 ^ t * (MinimalStart w + k * 2 ^ (StringFlow.wordWeight w + 3)) - 1) / 5

/-- Exact identity for the pre-inserted start when the divisibility
residue is `1`. -/
theorem preinsertedStart_eq
    (w : List Nat) (t k : Nat)
    (hk : (2 ^ t * (MinimalStart w + k * 2 ^ (StringFlow.wordWeight w + 3))) % 5 = 1) :
    5 * preinsertedStart w t k + 1 =
      2 ^ t * (MinimalStart w + k * 2 ^ (StringFlow.wordWeight w + 3)) := by
  let r := MinimalStart w
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  let N := 2 ^ t * (r + k * M)
  have hNmod : N % 5 = 1 := by
    simpa [r, S, M, N] using hk
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0] at hNmod
    norm_num at hNmod
  have hdec : N = 5 * (N / 5) + 1 := by
    have h := Nat.div_add_mod N 5
    rw [hNmod] at h
    omega
  have hN1 : N - 1 = 5 * (N / 5) := by
    omega
  have hmain : preinsertedStart w t k = N / 5 := by
    unfold preinsertedStart
    dsimp [r, S, M, N]
    rw [hN1]
    rw [Nat.mul_div_right (N / 5) (by decide : 0 < 5)]
  rw [hmain]
  exact hdec.symm

/-- The pre-inserted start lies in the new residue window. -/
theorem preinsertedStart_lt
    (w : List Nat) (t k : Nat)
    (_ht : t = 1 ∨ t = 2) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    preinsertedStart w t k <
      2 ^ (StringFlow.wordWeight (t :: w) + 3) := by
  let r := MinimalStart w
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  let N := 2 ^ t * (r + k * M)
  have hr : r < M := by
    dsimp [r, M]
    exact StringFlow.Word.wordRepresentative_lt w
  have hsum : r + k * M < 5 * M := by
    have hkM : k * M ≤ 4 * M := Nat.mul_le_mul_right M hk4
    nlinarith [hr, hkM]
  have hNlt5 : N < 5 * (2 ^ t * M) := by
    dsimp [N]
    calc
      2 ^ t * (r + k * M) < 2 ^ t * (5 * M) :=
        Nat.mul_lt_mul_of_pos_left hsum (by positivity : 0 < 2 ^ t)
      _ = 5 * (2 ^ t * M) := by ring
  have hNpos : 0 < N := by
    dsimp [N]
    have hMpos : 0 < M := by positivity
    have hkM : 0 < k * M := Nat.mul_pos (by omega) hMpos
    have hrk : 0 < r + k * M := by omega
    positivity
  have h5r : 5 * preinsertedStart w t k ≤ N - 1 := by
    unfold preinsertedStart
    dsimp [r, S, M, N]
    exact Nat.mul_div_le (2 ^ t * (MinimalStart w + k * 2 ^ (S + 3)) - 1) 5
  have h5r1 : 5 * preinsertedStart w t k + 1 ≤ N := by
    have hsub : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)
    nlinarith
  have hlt : 5 * preinsertedStart w t k + 1 < 5 * (2 ^ t * M) :=
    Nat.lt_of_le_of_lt h5r1 hNlt5
  have hlt' : preinsertedStart w t k < 2 ^ t * M := by
    have h5 : 5 * preinsertedStart w t k < 5 * (2 ^ t * M) := by nlinarith
    nlinarith
  have hpow : 2 ^ (StringFlow.wordWeight (t :: w) + 3) = 2 ^ t * M := by
    dsimp [S, M]
    rw [StringFlow.wordWeight]
    rw [show (t + S) + 3 = t + (S + 3) by omega]
    rw [Nat.pow_add]
  rwa [hpow]

/-- L-B'c branch is formally proved: pre-insertion with `k >= 1`
preserves the minimal start and satisfies the weak residual bound. -/
theorem lb_prime_c_branch
    (w : List Nat) (t k : Nat)
    (hw : RisingWord w)
    (ht : t = 1 ∨ t = 2)
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hk5 : (2 ^ t * (MinimalStart w + k * 2 ^ (StringFlow.wordWeight w + 3))) % 5 = 1) :
    MinimalStart (t :: w) = preinsertedStart w t k ∧
      LBPrimeWeak (t :: w) := by
  let r := MinimalStart w
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  let r' := preinsertedStart w t k
  have hOKw : StringFlow.Word.wordOK w := wordOK_of_mem_one_two w hw.1
  have hOKtw : StringFlow.Word.wordOK (t :: w) := by
    simp [StringFlow.Word.wordOK]
    constructor
    · rcases ht with ht1 | ht2 <;> omega
    · exact hOKw
  have hrepr : (5 ^ w.length * r + StringFlow.Word.wordA w) % M =
      (3 * 2 ^ S) % M := by
    simpa [r, S, M, MinimalStart] using StringFlow.Word.wordRepresentative_spec w
  have hfive : 5 * r' + 1 = 2 ^ t * (r + k * M) := by
    simpa [r, S, M, r'] using preinsertedStart_eq w t k hk5
  have hlt : r' < 2 ^ (StringFlow.wordWeight (t :: w) + 3) := by
    simpa [r', S, M] using preinsertedStart_lt w t k ht hk1 hk4
  have hreprNew :
      (5 ^ (t :: w).length * r' + StringFlow.Word.wordA (t :: w)) %
          2 ^ (StringFlow.wordWeight (t :: w) + 3) =
        (3 * 2 ^ StringFlow.wordWeight (t :: w)) %
          2 ^ (StringFlow.wordWeight (t :: w) + 3) := by
    let X := 5 ^ w.length * r + StringFlow.Word.wordA w
    let R := 3 * 2 ^ S
    have hX : X % M = R % M := by
      simpa [X, R, r, S, M] using hrepr
    have hXk : (X + k * (5 ^ w.length * M)) % M = R % M := by
      have hmul : k * (5 ^ w.length * M) = (k * 5 ^ w.length) * M := by ring
      rw [hmul]
      rw [Nat.add_mul_mod_self_right X (k * 5 ^ w.length) M]
      exact hX
    have hprod : 2 ^ (StringFlow.wordWeight (t :: w) + 3) = 2 ^ t * M := by
      dsimp [S, M]
      rw [StringFlow.wordWeight]
      rw [show (t + S) + 3 = t + (S + 3) by omega]
      rw [Nat.pow_add]
    have hLHS : 5 ^ (t :: w).length * r' + StringFlow.Word.wordA (t :: w) =
        2 ^ t * (X + k * (5 ^ w.length * M)) := by
      have hlen : (t :: w).length = w.length + 1 := by simp
      rw [hlen]
      dsimp [X]
      rw [StringFlow.Word.wordA]
      rw [Nat.pow_succ]
      calc
        5 ^ w.length * 5 * r' + (5 ^ w.length + 2 ^ t * StringFlow.Word.wordA w)
            = 5 ^ w.length * (5 * r' + 1) + 2 ^ t * StringFlow.Word.wordA w := by ring
        _ = 5 ^ w.length * (2 ^ t * (r + k * M)) +
            2 ^ t * StringFlow.Word.wordA w := by rw [hfive]
        _ = 2 ^ t * (5 ^ w.length * r + StringFlow.Word.wordA w +
            k * (5 ^ w.length * M)) := by ring
    have hRHS : 3 * 2 ^ StringFlow.wordWeight (t :: w) = 2 ^ t * R := by
      dsimp [R]
      rw [StringFlow.wordWeight]
      rw [Nat.pow_add]
      ring
    rw [hLHS, hRHS, hprod]
    rw [Nat.mul_mod_mul_left (2 ^ t) (X + k * (5 ^ w.length * M)) M]
    rw [Nat.mul_mod_mul_left (2 ^ t) R M]
    exact congrArg (fun z => 2 ^ t * z) hXk
  have hvalidNew : StringFlow.Word.wordValid (t :: w) r' ∧
      StringFlow.Word.wordOrbit (t :: w) r' % 8 = 3 :=
    StringFlow.Word.wordValid_of_endpoint_congruence (t :: w) hOKtw r' hreprNew
  have hiff := StringFlow.Word.word_representative_iff (t :: w) hOKtw r' hlt
  have heqRep : r' = MinimalStart (t :: w) := by
    exact hiff.mp hvalidNew
  have hS' : StringFlow.wordWeight (t :: w) = t + S := rfl
  have hMpow : 2 ^ (t + S + 3) = 2 ^ t * M := by
    dsimp [M]
    rw [show (t + S) + 3 = t + (S + 3) by omega]
    rw [Nat.pow_add]
  have hkM : M ≤ r + k * M := by
    have hMpos : 0 < M := by positivity
    have h1 : M ≤ k * M := by
      have hk1' : 1 ≤ k := hk1
      nlinarith
    omega
  have hbig : 2 ^ (t + S + 3) ≤ 5 * r' + 1 := by
    rw [hMpow, hfive]
    exact Nat.mul_le_mul_left (2 ^ t) hkM
  have h5r : 2 ^ (t + S + 3) - 1 ≤ 5 * r' := by omega
  have h5rge : 2 ^ StringFlow.wordWeight (t :: w) ≤ 5 * r' := by
    rw [hS']
    have hle : 2 ^ (t + S) ≤ 2 ^ (t + S + 3) - 1 := by
      have hpow : 2 ^ (t + S + 3) = 8 * 2 ^ (t + S) := by
        rw [Nat.pow_add]
        ring
      rw [hpow]
      have hpos : 0 < 2 ^ (t + S) := by positivity
      omega
    exact le_trans hle h5r
  have hpow5 : (5 * r') ^ 5 ≥ 2 ^ StringFlow.wordWeight (t :: w) := by
    have h1 : (2 ^ StringFlow.wordWeight (t :: w)) ^ 5 ≤ (5 * r') ^ 5 :=
      Nat.pow_le_pow_left h5rge 5
    have h2 : 2 ^ StringFlow.wordWeight (t :: w) ≤
        (2 ^ StringFlow.wordWeight (t :: w)) ^ 5 := by
      have hle : StringFlow.wordWeight (t :: w) ≤
          StringFlow.wordWeight (t :: w) * 5 := by nlinarith
      calc
        2 ^ StringFlow.wordWeight (t :: w)
            ≤ 2 ^ (StringFlow.wordWeight (t :: w) * 5) :=
              Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
        _ = (2 ^ StringFlow.wordWeight (t :: w)) ^ 5 := by
              rw [Nat.pow_mul]
    exact le_trans h2 h1
  constructor
  · exact heqRep.symm
  · rw [LBPrimeWeak, ← heqRep]
    exact hpow5

/-- L-B'c branch: pre-insertion with `k >= 1` preserves the minimal
start formula and satisfies the weak residual bound.  The doc claims
this branch is proved; the Lean theorem is still pending. -/
def LBPrimeC : Prop :=
  ∀ (w : List Nat) (t k : Nat),
    RisingWord w →
    t = 1 ∨ t = 2 →
    1 ≤ k → k ≤ 4 →
    (2 ^ t * (MinimalStart w + k * 2 ^ (StringFlow.wordWeight w + 3))) % 5 = 1 →
    MinimalStart (t :: w) = preinsertedStart w t k ∧
      LBPrimeWeak (t :: w)

/-- L-B'c is closed in Lean. -/
theorem lb_prime_c : LBPrimeC := by
  intro w t k hw ht hk1 hk4 hk5
  exact lb_prime_c_branch w t k hw ht hk1 hk4 hk5

/-- L-B' restricted to words with no `t=2` step. -/
def LBPrimeU0 : Prop :=
  ∀ w : List Nat, RisingWord w → countTwo w = 0 → LBPrimeWeak w

/-- L-B' restricted to words with exactly one `t=2` step. -/
def LBPrimeU1 : Prop :=
  ∀ w : List Nat, RisingWord w → countTwo w = 1 → LBPrimeWeak w

/-- L-B' restricted to words with exactly two `t=2` steps.  This is
the only documented open subcase of L-B'a/b. -/
def LBPrimeU2 : Prop :=
  ∀ w : List Nat, RisingWord w → countTwo w = 2 → LBPrimeWeak w

/-- The documented reduction of L-B': `U >= 3` is closed by L-B'c,
`U = 0,1` are closed analytically, and `U = 2` is the remaining open
subcase.  This predicate is the formal decomposition, not a proof. -/
def LBPrimeReduction : Prop :=
  (∀ w : List Nat, RisingWord w → 3 ≤ countTwo w → LBPrimeWeak w) ∧
  LBPrimeU0 ∧ LBPrimeU1 ∧ LBPrimeU2

/-- Audit fields of the conditional SURV-EX statement 53.4-LB.
Each field is an explicit hypothesis; no field is proved here. -/
structure SurvExConditions where
  sx1 : Prop
  sx2_lucas : Prop
  sx2_exclusion : Prop
  sx3_ab : Prop
  sx3_interval : Prop
  sx3_c : Prop
  sx4 : Prop
  main_chain_53 : Prop
  surv_ray : Prop
  simons_s1 : Prop
  lb_prime : Prop

/-- Conditional statement 53.4-LB, formalized as an implication. -/
def SurvEx53_4LB : Prop :=
  SurvExConditions → SurvExTd0

/-- Assembly bridge: if the conditional statement and its explicit
conditions hold, then the no-cycle interface closes and divergence
follows.  This is not a proof of the condition fields. -/
theorem divergence_of_surv_ex_53_4_lb
    (hC : SurvExConditions) (h53 : SurvEx53_4LB) :
    IsUnboundedOrbit 7 :=
  five_x_plus_one_diverges_at_7_of_surv_ex_td0 (h53 hC)

end StringFlow.SurvEx
