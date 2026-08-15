import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ScratchLift
import WordWindow

/-!
# S6 Equivalence-Chain Audit (2026-08-11)

This file only declares and audits statements; it adds no new mathematical
reductions.

Protocol:
- No `axiom` is used to hide a gap;
- Every `sorry` is audited separately; the status table is at the end of the file;
- `local_lemma_final` is now closed and the file has no `sorry`;
  `pure_t2_m1_no_odd_hit` was given its premises under correction tickets
  9, 9a, 10 and closed under the 25-state exhaustion layer of ticket 14.
- Intermediate lemmas already have mathematical proofs in the document;
  in this file they were initially marked with `sorry` as
  "formalization pending port", not as mathematical true cards.
-/

namespace S6Audit

/-- 2-adic valuation on naturals (`v_2`). -/
abbrev twoValuation := StringFlow.twoValuation

/-- Least nonnegative residue of `a` modulo `m`. -/
def leastResidue (a m : Nat) : Nat := a % m

/-- `2^e` is not divisible by 5. -/
theorem pow_two_mod_five_ne_zero (e : Nat) : (2 ^ e) % 5 ≠ 0 := by
  induction e with
  | zero => decide
  | succ e ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      have hlt : (2 ^ e) % 5 < 5 := Nat.mod_lt _ (by decide)
      have hcases : (2 ^ e) % 5 = 1 ∨ (2 ^ e) % 5 = 2 ∨
          (2 ^ e) % 5 = 3 ∨ (2 ^ e) % 5 = 4 := by omega
      rcases hcases with h1 | h2 | h3 | h4
      · rw [h1]; decide
      · rw [h2]; decide
      · rw [h3]; decide
      · rw [h4]; decide

/-- Modular inverse of `2^e` modulo `5^N`, as the least residue
produced by Hensel lifting. -/
def pow2Inv (e N : Nat) : Nat :=
  StringFlow.Lte.invFive (2 ^ e) N % 5 ^ N

/-- Correctness: `2^e * pow2Inv e N ≡ 1 (mod 5^N)`. -/
theorem pow2Inv_correct (e N : Nat) : 2 ^ e * pow2Inv e N ≡ 1 [MOD 5 ^ N] := by
  unfold pow2Inv
  by_cases hN : 1 ≤ N
  · have hspec := StringFlow.Lte.invFive_spec (2 ^ e) (pow_two_mod_five_ne_zero e) (N - 1)
    have hspec' : (2 ^ e * StringFlow.Lte.invFive (2 ^ e) N) % 5 ^ N = 1 := by
      simpa [Nat.sub_add_cancel hN] using hspec
    rw [Nat.ModEq]
    have hmod1 : 1 % 5 ^ N = 1 :=
      Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 5) (by omega : N ≠ 0))
    simpa [Nat.mul_mod, hmod1] using hspec'
  · have hN0 : N = 0 := by omega
    subst hN0
    rw [Nat.ModEq]
    simp [StringFlow.Lte.invFive]

/-- Additive composition of inverse residues modulo `5^N`. -/
theorem pow2Inv_composition (e1 e2 N : Nat) :
    (pow2Inv e1 N * pow2Inv e2 N) % 5 ^ N = pow2Inv (e1 + e2) N % 5 ^ N := by
  let x := pow2Inv e1 N
  let y := pow2Inv e2 N
  let z := pow2Inv (e1 + e2) N
  have hx : (2 ^ e1 * x) % 5 ^ N = 1 % 5 ^ N := by
    dsimp [x]
    simpa [Nat.ModEq] using pow2Inv_correct e1 N
  have hy : (2 ^ e2 * y) % 5 ^ N = 1 % 5 ^ N := by
    dsimp [y]
    simpa [Nat.ModEq] using pow2Inv_correct e2 N
  have hz : (2 ^ (e1 + e2) * z) % 5 ^ N = 1 % 5 ^ N := by
    dsimp [z]
    simpa [Nat.ModEq] using pow2Inv_correct (e1 + e2) N
  have hxy : (2 ^ (e1 + e2) * (x * y)) % 5 ^ N = 1 % 5 ^ N := by
    rw [Nat.pow_add]
    rw [show (2 ^ e1 * 2 ^ e2) * (x * y) = (2 ^ e1 * x) * (2 ^ e2 * y) by ring]
    rw [Nat.mul_mod, Nat.mul_mod]
    rw [hx, hy]
    simp
  have hxy' : 2 ^ (e1 + e2) * (x * y) ≡ 1 [MOD 5 ^ N] := by
    rw [Nat.ModEq]
    exact hxy
  have hz' : 2 ^ (e1 + e2) * z ≡ 1 [MOD 5 ^ N] := by
    rw [Nat.ModEq]
    exact hz
  have hsame : 2 ^ (e1 + e2) * (x * y) ≡ 2 ^ (e1 + e2) * z [MOD 5 ^ N] :=
    hxy'.trans hz'.symm
  have hcop : Nat.gcd (5 ^ N) (2 ^ (e1 + e2)) = 1 := by
    have h := Nat.Coprime.pow_right N
      (Nat.Coprime.pow_left (e1 + e2) (by decide : Nat.Coprime 2 5))
    simpa [Nat.gcd_comm] using h
  have hmodeq : x * y ≡ z [MOD 5 ^ N] :=
    Nat.ModEq.cancel_left_of_coprime hcop hsame
  dsimp [x, y, z] at hmodeq ⊢
  exact hmodeq

/-- Oddness for natural numbers: `n % 2 = 1`. -/
def IsOdd (n : Nat) : Prop := n % 2 = 1

/-- Chain step `s_{m+1} = (s_m + δ_m * 5^N) / 2^(U_m)`. -/
def chainStep (s U δ N : Nat) : Nat :=
  (s + δ * 5 ^ N) / 2 ^ U

/-- Cumulative sum `S_m = Σ_{r<m} U_r`, with `S 0 = 0`. -/
def cumulativeS (U : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cumulativeS U m + U m

/-- `Σ_{m<M} δ_m·2^(S_m)` in the cleared chain closed form. -/
def chainSum (U δ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | M + 1 => chainSum U δ M + δ M * 2 ^ cumulativeS U M

/--
Cleared-denominator form of the interval in (F):

`δ*5^N/2^U < t0 < (δ+1/4)*5^N/2^U`

is equivalent, for integers, to

`4*δ*5^N < 4*t0*2^U ∧ 4*t0*2^U < (4*δ+1)*5^N`.
-/
def InInterval (t0 N U δ : Nat) : Prop :=
  4 * δ * 5 ^ N < 4 * t0 * 2 ^ U ∧
  4 * t0 * 2 ^ U < (4 * δ + 1) * 5 ^ N

/-- Block hit predicate: `t0` odd and inside (F). -/
def OddHit (t0 N U δ : Nat) : Prop :=
  IsOdd t0 ∧ InInterval t0 N U δ

/-- The `t0` predicate evaluated at chain index `m`. -/
def ChainHit (s U δ : Nat → Nat) (N m : Nat) : Prop :=
  OddHit
    (leastResidue (s m * pow2Inv (U m) N) (5 ^ N))
    N (U m) (δ m)

/-! ## Part 1: audit chain 36.28.1 -- 36.28.7 -/

/--
36.28.1.  `s_M ≡ s_0·2^(-S_M) (mod 5^N)`.

Premises: chain recurrence, `U_m=2L_m+2`, modular-inverse specification.
The mathematical proof is in the document; here the statement is
formalized and the proof port is pending.
-/
theorem audit_36_28_1
    (N M : Nat) (s0 : Nat) (s : Nat → Nat) (U δ L : Nat → Nat)
    (hS0 : s 0 = s0)
    (_hU : ∀ m : Nat, m < M → U m = 2 * L m + 2)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M →
      s (m + 1) = chainStep (s m) (U m) (δ m) N)
    :
    s M ≡ s 0 * pow2Inv (cumulativeS U M) N [MOD 5 ^ N] := by
  induction M with
  | zero =>
      rw [Nat.ModEq, hS0, cumulativeS]
      have h0 : pow2Inv 0 N % 5 ^ N = 1 % 5 ^ N := by
        simpa [Nat.ModEq] using pow2Inv_correct 0 N
      rw [Nat.mul_mod, h0]
      simp
  | succ M ih =>
      have hih' : s M ≡ s 0 * pow2Inv (cumulativeS U M) N [MOD 5 ^ N] := by
        exact ih
          (fun m hm => _hU m (by omega))
          (fun m hm => hdiv m (by omega))
          (fun m hm => hchain m (by omega))
      have hstep := hchain M (by omega)
      have hdivM := hdiv M (by omega)
      have heq : 2 ^ U M * s (M + 1) = s M + δ M * 5 ^ N := by
        rw [hstep]
        unfold chainStep
        exact Nat.mul_div_cancel' hdivM
      have hmodstep : 2 ^ U M * s (M + 1) ≡ s M [MOD 5 ^ N] := by
        rw [Nat.ModEq, heq, Nat.add_mod]
        have h5 : (δ M * 5 ^ N) % 5 ^ N = 0 := by
          rw [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
        rw [h5, Nat.add_zero]
        simp
      have hinv : 2 ^ U M * pow2Inv (U M) N ≡ 1 [MOD 5 ^ N] := by
        exact pow2Inv_correct (U M) N
      have hsm1 : s (M + 1) ≡ s M * pow2Inv (U M) N [MOD 5 ^ N] := by
        have hmul := hmodstep.mul_right (pow2Inv (U M) N)
        have hcancel : (2 ^ U M * s (M + 1)) * pow2Inv (U M) N
            ≡ s (M + 1) [MOD 5 ^ N] := by
          have hre : (2 ^ U M * s (M + 1)) * pow2Inv (U M) N
              = (2 ^ U M * pow2Inv (U M) N) * s (M + 1) := by ring
          rw [hre]
          simpa using hinv.mul_right (s (M + 1))
        exact hcancel.symm.trans hmul
      have hsm1' : s (M + 1) ≡
          (s 0 * pow2Inv (cumulativeS U M) N) * pow2Inv (U M) N
          [MOD 5 ^ N] :=
        hsm1.trans (hih'.mul_right (pow2Inv (U M) N))
      have hcomp : pow2Inv (cumulativeS U M) N * pow2Inv (U M) N
          ≡ pow2Inv (cumulativeS U M + U M) N [MOD 5 ^ N] := by
        rw [Nat.ModEq]
        exact pow2Inv_composition (cumulativeS U M) (U M) N
      rw [cumulativeS]
      have hreassoc : (s 0 * pow2Inv (cumulativeS U M) N) *
          pow2Inv (U M) N
          = s 0 * (pow2Inv (cumulativeS U M) N * pow2Inv (U M) N) := by
        ring
      rw [hreassoc] at hsm1'
      exact hsm1'.trans (hcomp.mul_left (s 0))

/-- Corollary 15.3, cleared integer form:
`s_M·2^(S_M) = s_0 + 5^N·Σ_{m<M} δ_m·2^(S_m)`. -/
theorem chain_closed_form
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (hdiv : ∀ m : Nat, m < M → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M → s (m + 1) = chainStep (s m) (U m) (δ m) N) :
    s M * 2 ^ cumulativeS U M = s 0 + 5 ^ N * chainSum U δ M := by
  induction M with
  | zero => simp [cumulativeS, chainSum]
  | succ M ih =>
      have hih := ih
        (fun m hm => hdiv m (by omega))
        (fun m hm => hchain m (by omega))
      have hih' : 2 ^ cumulativeS U M * s M = s 0 + 5 ^ N * chainSum U δ M := by
        simpa [Nat.mul_comm] using hih
      have hdivM := hdiv M (by omega)
      have hchainM := hchain M (by omega)
      have hstep : 2 ^ U M * s (M + 1) = s M + δ M * 5 ^ N := by
        rw [hchainM]
        unfold chainStep
        exact Nat.mul_div_cancel' hdivM
      have hpow : 2 ^ cumulativeS U (M + 1) =
          2 ^ cumulativeS U M * 2 ^ U M := by
        rw [cumulativeS, Nat.pow_add]
      calc
        s (M + 1) * 2 ^ cumulativeS U (M + 1)
            = (2 ^ cumulativeS U M * 2 ^ U M) * s (M + 1) := by
              rw [hpow]
              ring
        _ = 2 ^ cumulativeS U M * (2 ^ U M * s (M + 1)) := by ring
        _ = 2 ^ cumulativeS U M * (s M + δ M * 5 ^ N) := by rw [hstep]
        _ = 2 ^ cumulativeS U M * s M +
            2 ^ cumulativeS U M * (δ M * 5 ^ N) := by ring
        _ = (s 0 + 5 ^ N * chainSum U δ M) +
            2 ^ cumulativeS U M * (δ M * 5 ^ N) := by rw [hih']
        _ = s 0 + 5 ^ N *
            (chainSum U δ M + δ M * 2 ^ cumulativeS U M) := by ring
        _ = s 0 + 5 ^ N * chainSum U δ (M + 1) := by rw [chainSum]

/--
36.28.3, corrected version. Failure of block `M` (valuation exactly
`U_M`, odd quotient) is equivalent to `OddHit t0 N U_M δ_M`. Without
oddness, the interval condition alone corresponds to `v_2 ≥ U_M`.
-/
lemma chain_next_lt_five_pow (N U δ s : Nat)
    (hs : s < 5 ^ N / 4) (hδ : δ = 1 ∨ δ = 3) (hU : 4 ≤ U) :
    (s + δ * 5 ^ N) / 2 ^ U < 5 ^ N := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ U)]
  have hs4 : 4 * s < 5 ^ N := by
    have hlt' := (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mp hs
    have hlt'' : 4 * s < 5 ^ N - 3 := by simpa [Nat.mul_comm] using hlt'
    exact lt_of_lt_of_le hlt'' (Nat.sub_le (5 ^ N) 3)
  have hδle : δ ≤ 3 := by rcases hδ with h1 | h3 <;> omega
  have hUge16 : 16 ≤ 2 ^ U := by
    have h := pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hU
    simpa using h
  have hlt16 : 4 * (s + δ * 5 ^ N) < 16 * 5 ^ N := by
    have hδprod : 4 * δ * 5 ^ N ≤ 12 * 5 ^ N := by nlinarith
    nlinarith
  have hle16 : 16 * 5 ^ N ≤ 4 * (5 ^ N * 2 ^ U) := by
    have hle : 16 ≤ 4 * 2 ^ U := by nlinarith [hUge16]
    nlinarith
  have hprod4 : 4 * (s + δ * 5 ^ N) < 4 * (5 ^ N * 2 ^ U) :=
    lt_of_lt_of_le hlt16 hle16
  nlinarith

theorem audit_36_28_3
    (N M : Nat) (L : Nat → Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (hU_all : ∀ m : Nat, m < M + 1 → U m = 2 * L m + 2)
    (hdiv : ∀ m : Nat, m < M + 1 → 2 ^ U m ∣ s m + δ m * 5 ^ N)
    (hchain : ∀ m : Nat, m < M + 1 →
      s (m + 1) = chainStep (s m) (U m) (δ m) N)
    (hSM_pos : 0 < s M)
    (hSM_lt : s M < 5 ^ N / 4)
    (hUge : 4 ≤ U M)
    (hδ : δ M = 1 ∨ δ M = 3) :
    (twoValuation (s M + δ M * 5 ^ N) = U M) ↔
      OddHit
        (leastResidue (s 0 * pow2Inv (cumulativeS U M + U M) N) (5 ^ N))
        N (U M) (δ M) := by
  let t0 := leastResidue (s 0 * pow2Inv (cumulativeS U M + U M) N) (5 ^ N)
  have hcong := audit_36_28_1 N (M + 1) (s 0) s U δ L rfl
    (fun m hm => hU_all m (by omega))
    (fun m hm => hdiv m (by omega))
    (fun m hm => hchain m (by omega))
  have hcong' : s (M + 1) ≡ s 0 * pow2Inv (cumulativeS U M + U M) N [MOD 5 ^ N] := by
    simpa [cumulativeS] using hcong
  have hnext_lt : s (M + 1) < 5 ^ N := by
    have hlt := chain_next_lt_five_pow N (U M) (δ M) (s M) hSM_lt hδ hUge
    rwa [show (s M + δ M * 5 ^ N) / 2 ^ U M = s (M + 1) by
      rw [hchain M (by omega)]
      rfl] at hlt
  have ht0eq : t0 = s (M + 1) := by
    unfold t0 leastResidue
    rw [Nat.ModEq] at hcong'
    have hmod : s 0 * pow2Inv (cumulativeS U M + U M) N % 5 ^ N =
        s (M + 1) % 5 ^ N := hcong'.symm
    rw [hmod, Nat.mod_eq_of_lt hnext_lt]
  constructor
  · intro hV
    let t := (s M + δ M * 5 ^ N) / 2 ^ U M
    have ht_eq_next : t = s (M + 1) := by
      rw [hchain M (by omega)]
      rfl
    have hdivM : 2 ^ U M ∣ s M + δ M * 5 ^ N := hdiv M (by omega)
    have hnpos : 0 < s M + δ M * 5 ^ N :=
      Nat.add_pos_left hSM_pos (δ M * 5 ^ N)
    have hdec := StringFlow.n_eq_two_pow_mul_oddPart (s M + δ M * 5 ^ N) hnpos
    have hpow : 2 ^ twoValuation (s M + δ M * 5 ^ N) = 2 ^ U M := by rw [hV]
    have hdec' : s M + δ M * 5 ^ N =
        2 ^ U M * StringFlow.oddPart (s M + δ M * 5 ^ N) := by
      rw [hpow] at hdec
      exact hdec
    have hdivM' : s M + δ M * 5 ^ N = 2 ^ U M * t := by
      rw [show t = (s M + δ M * 5 ^ N) / 2 ^ U M by rfl]
      exact (Nat.mul_div_cancel' hdivM).symm
    have ht_odd : t % 2 = 1 := by
      have hcancel : StringFlow.oddPart (s M + δ M * 5 ^ N) = t := by
        apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ U M)
        rw [← hdec', hdivM']
      rw [← hcancel]
      exact StringFlow.oddPart_odd_of_pos (s M + δ M * 5 ^ N) hnpos
    have ht0eq' : t0 = t := ht0eq.trans ht_eq_next.symm
    have h2pow : 2 ^ U M * t = s M + δ M * 5 ^ N := hdivM'.symm
    have h4eq : 4 * t * 2 ^ U M = 4 * s M + 4 * δ M * 5 ^ N := by
      rw [show 4 * t * 2 ^ U M = 4 * (2 ^ U M * t) by ring]
      rw [h2pow]
      ring
    have hs4 : 4 * s M < 5 ^ N := by
      have hlt' := (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mp hSM_lt
      have hlt'' : 4 * s M < 5 ^ N - 3 := by simpa [Nat.mul_comm] using hlt'
      exact lt_of_lt_of_le hlt'' (Nat.sub_le (5 ^ N) 3)
    have hinterval_low : 4 * δ M * 5 ^ N < 4 * t0 * 2 ^ U M := by
      rw [ht0eq', h4eq]
      have hspos4 : 0 < 4 * s M := Nat.mul_pos (by decide : 0 < 4) hSM_pos
      omega
    have hinterval_high : 4 * t0 * 2 ^ U M < (4 * δ M + 1) * 5 ^ N := by
      rw [ht0eq', h4eq]
      rw [show (4 * δ M + 1) * 5 ^ N = 4 * δ M * 5 ^ N + 5 ^ N by ring]
      omega
    exact ⟨by
      change IsOdd t0
      rw [ht0eq']
      exact ht_odd, hinterval_low, hinterval_high⟩
  · intro hHit
    have ht_odd : t0 % 2 = 1 := hHit.1
    have h2pow : 2 ^ U M * s (M + 1) = s M + δ M * 5 ^ N := by
      rw [hchain M (by omega)]
      unfold chainStep
      exact Nat.mul_div_cancel' (hdiv M (by omega))
    have hval : twoValuation (s M + δ M * 5 ^ N) = U M := by
      rw [← h2pow]
      rw [← ht0eq]
      exact StringFlow.Lte.twoValuation_mul_two_pow_eq (U M) t0 ht_odd
    exact hval

/--
36.28.5, exact integer form (correction ticket 5).

The document originally stated the real logarithm bound
`U_m < 2.322·N + 1.7`; that is not an independent goal. The chain step
directly gives the pure integer inequality `4·2^U < (4δ+1)·5^N`.
-/
theorem audit_36_28_5_exact
    (N U δ s : Nat)
    (hs : s < 5 ^ N / 4)
    (hδ : δ = 1 ∨ δ = 3)
    (hdiv : 2 ^ U ∣ s + δ * 5 ^ N) :
    4 * 2 ^ U < (4 * δ + 1) * 5 ^ N := by
  have hδpos : 0 < δ * 5 ^ N := by
    rcases hδ with h1 | h3
    · rw [h1]
      exact Nat.mul_pos (by decide : 0 < 1) (Nat.pow_pos (by decide : 0 < 5))
    · rw [h3]
      exact Nat.mul_pos (by decide : 0 < 3) (Nat.pow_pos (by decide : 0 < 5))
  have hnpos : 0 < s + δ * 5 ^ N := Nat.add_pos_right s hδpos
  have hle : 2 ^ U ≤ s + δ * 5 ^ N := Nat.le_of_dvd hnpos hdiv
  have hs4 : 4 * s < 5 ^ N := by
    have hlt' := (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mp hs
    have hlt'' : 4 * s < 5 ^ N - 3 := by simpa [Nat.mul_comm] using hlt'
    exact lt_of_lt_of_le hlt'' (Nat.sub_le (5 ^ N) 3)
  have hmain : 4 * (s + δ * 5 ^ N) < (4 * δ + 1) * 5 ^ N := by
    rw [show (4 * δ + 1) * 5 ^ N = 4 * δ * 5 ^ N + 5 ^ N by ring]
    nlinarith
  calc
    4 * 2 ^ U ≤ 4 * (s + δ * 5 ^ N) := Nat.mul_le_mul_left 4 hle
    _ < (4 * δ + 1) * 5 ^ N := hmain

/--
36.28.6, reverse descent lemma (with the true predecessor parameters).

If `scur` is the next state of a legal chain, then the previous block is
automatically an odd hit. The true predecessor is `sprev` with parameters
`Uprev, δprev`, not the current block parameters.
-/
theorem audit_36_28_6
    (N sprev scur Uprev δprev : Nat)
    (hchain : scur = chainStep sprev Uprev δprev N)
    (hdiv : 2 ^ Uprev ∣ sprev + δprev * 5 ^ N)
    (hprev_pos : 0 < sprev)
    (hprev_small : sprev < 5 ^ N / 4)
    (hscur_small : scur < 5 ^ N / 4)
    (hscur_odd : IsOdd scur)
    (_hscur_nd5 : ¬ 5 ∣ scur) :
    OddHit
      (leastResidue (sprev * pow2Inv Uprev N) (5 ^ N))
      N Uprev δprev := by
  let t0 := leastResidue (sprev * pow2Inv Uprev N) (5 ^ N)
  have heq : 2 ^ Uprev * scur = sprev + δprev * 5 ^ N := by
    rw [hchain]
    unfold chainStep
    exact Nat.mul_div_cancel' hdiv
  have hpow : 2 ^ Uprev * scur ≡ sprev [MOD 5 ^ N] := by
    rw [Nat.ModEq, heq, Nat.add_mod]
    have h5 : (δprev * 5 ^ N) % 5 ^ N = 0 := by
      rw [Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
    rw [h5, Nat.add_zero]
    simp
  have hinv : 2 ^ Uprev * pow2Inv Uprev N ≡ 1 [MOD 5 ^ N] :=
    pow2Inv_correct Uprev N
  have hmul := hpow.mul_right (pow2Inv Uprev N)
  have hleft : 2 ^ Uprev * scur * pow2Inv Uprev N ≡ scur [MOD 5 ^ N] := by
    have hre : 2 ^ Uprev * scur * pow2Inv Uprev N =
        scur * (2 ^ Uprev * pow2Inv Uprev N) := by ring
    rw [hre]
    simpa using hinv.mul_left scur
  have hmod : scur ≡ sprev * pow2Inv Uprev N [MOD 5 ^ N] :=
    hleft.symm.trans hmul
  have hscur_lt : scur < 5 ^ N :=
    lt_of_lt_of_le hscur_small (Nat.div_le_self (5 ^ N) 4)
  have ht0 : t0 = scur := by
    unfold t0 leastResidue
    rw [Nat.ModEq] at hmod
    have hmod' : sprev * pow2Inv Uprev N % 5 ^ N = scur % 5 ^ N := hmod.symm
    rw [hmod', Nat.mod_eq_of_lt hscur_lt]
  have h4eq : 4 * scur * 2 ^ Uprev = 4 * sprev + 4 * δprev * 5 ^ N := by
    rw [show 4 * scur * 2 ^ Uprev = 4 * (2 ^ Uprev * scur) by ring]
    rw [heq]
    ring
  have h4sprev : 4 * sprev < 5 ^ N := by
    have hlt' := (Nat.lt_div_iff_mul_lt (by decide : 0 < 4)).mp hprev_small
    have hlt'' : 4 * sprev < 5 ^ N - 3 := by simpa [Nat.mul_comm] using hlt'
    exact lt_of_lt_of_le hlt'' (Nat.sub_le (5 ^ N) 3)
  have hinterval_low : 4 * δprev * 5 ^ N < 4 * t0 * 2 ^ Uprev := by
    rw [ht0, h4eq]
    have hspos4 : 0 < 4 * sprev := Nat.mul_pos (by decide : 0 < 4) hprev_pos
    omega
  have hinterval_high : 4 * t0 * 2 ^ Uprev < (4 * δprev + 1) * 5 ^ N := by
    rw [ht0, h4eq]
    rw [show (4 * δprev + 1) * 5 ^ N = 4 * δprev * 5 ^ N + 5 ^ N by ring]
    omega
  exact ⟨by
    change IsOdd t0
    rw [ht0]
    exact hscur_odd, hinterval_low, hinterval_high⟩

/--
36.28.7, failure-chain collapse. If block `m` fails and `m≥1`, then block
`m-1` already fails; hence a minimal counterexample can only occur at
`M=1`.
-/
theorem audit_36_28_7
    (N M : Nat) (s : Nat → Nat) (U δ : Nat → Nat)
    (h0 : ¬ ChainHit s U δ N 0)
    (hdesc : ∀ m : Nat, m ≥ 1 → ChainHit s U δ N m →
      ChainHit s U δ N (m - 1)) :
    ¬ ChainHit s U δ N M := by
  induction M with
  | zero => exact h0
  | succ M ih =>
      intro h
      have hprev := hdesc (M + 1) (by omega) h
      exact ih hprev

/-! ## Part 2: pure t=2 remainder (M=1 base case) -/

/--
`IsGloballyReachable s0 N δ` (correction tickets 4, 8, 9, 9a, 10): the
previous even terminal `r` itself lies on the real orbit of 7, and `s0` is
only its 5-adic odd part; the orbit word must satisfy `wordValid`; the block
head `rj` obtained from the reset equation of 36.27/15.1 must also lie on
the orbit of 7; `δ` is both the reset-step and chain-step parameter, and
`rj` is odd.
-/
def OrbitFrom7 (x : Nat) : Prop :=
  ∃ w : List Nat,
    (∀ t ∈ w, t = 1 ∨ t = 2) ∧
    StringFlow.Word.wordValid w 7 ∧
    StringFlow.Word.wordOrbit w 7 = x

/-- `s0` is the odd part of the previous even terminal `r+1` after dividing
by `5^k`, with `r` on the orbit of 7. -/
def IsPreviousEvenTerminal (s0 j k : Nat) : Prop :=
  ∃ r : Nat,
    s0 * 5 ^ k = r + 1 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k) ∧
    OrbitFrom7 r

/-- Correction ticket 9a: the reset block head is given by the exact
equation of 36.27/15.1 and cannot be written as `(5r+1)/2^(t_j)`.
For `t_j=1` use `δ=1`; for `t_j=2` use `δ∈{1,3}`. -/
def ResetHeadEq (s0 j k t δ rj : Nat) : Prop :=
  (t = 1 ∧ δ = 1 ∧ 2 * (rj + 1) = 5 ^ (k + 1) * s0 + 5 ^ j - 2) ∨
  (t = 2 ∧ (δ = 1 ∨ δ = 3) ∧ 4 * (rj + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j)

/-- C3-chain reset equation: a C3 step `2^t * rj = 5x + 1` from a head
`x` with `x + 1 = 4 * 5^k * s0` gives the tail reset identity
`2^(t-2) * (rj + 1) = 5^(k+1) * s0 + 2^(t-2) - 1`. -/
def ResetHeadEqC3 (s0 _j k t rj : Nat) : Prop :=
  3 <= t /\
    2 ^ (t - 2) * (rj + 1) =
      5 ^ (k + 1) * s0 + 2 ^ (t - 2) - 1
def IsGloballyReachable (s0 N δ : Nat) : Prop :=
  ∃ j k r rj t : Nat,
    k + 1 ≤ j ∧
    N = j - k - 1 ∧
    s0 * 5 ^ k = r + 1 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k) ∧
    OrbitFrom7 r ∧
    ResetHeadEq s0 j k t δ rj ∧
    IsOdd rj ∧
    OrbitFrom7 rj

/-! ## Pure t=2: 25-state exhaustion and t=1 predecessors (ticket 14) -/

/-- The finite 25-state orbit table from ticket 14. -/
@[reducible]
def orbit25Table : List Nat :=
  [7, 9, 18, 23, 29, 58, 73, 183, 229, 458, 573,
   1433, 3583, 4479, 5599, 6999, 8749, 8958,
   11198, 13998, 17498, 21873, 54683, 68354, 136708]

/-- Membership in the 25-state orbit table. -/
@[reducible]
def InOrbit25 (x : Nat) : Prop := x ∈ orbit25Table

/-- Finite case split for table membership. -/
lemma orbit25_mem_cases (x : Nat) (hx : x ∈ orbit25Table) :
    x = 7 ∨ x = 9 ∨ x = 18 ∨ x = 23 ∨ x = 29 ∨ x = 58 ∨
    x = 73 ∨ x = 183 ∨ x = 229 ∨ x = 458 ∨ x = 573 ∨ x = 1433 ∨
    x = 3583 ∨ x = 4479 ∨ x = 5599 ∨ x = 6999 ∨ x = 8749 ∨ x = 8958 ∨
    x = 11198 ∨ x = 13998 ∨ x = 17498 ∨ x = 21873 ∨ x = 54683 ∨
    x = 68354 ∨ x = 136708 := by
  simpa [orbit25Table] using hx

/-- Every legal `{1,2}` successor of a table state stays in the table. -/
theorem orbit25_closed_prop :
    ∀ x ∈ orbit25Table, ∀ t : Nat, t = 1 ∨ t = 2 →
      (5 * x + 1) % 2 ^ t = 0 → InOrbit25 ((5 * x + 1) / 2 ^ t) := by
  intro x hx t ht hdiv
  rcases orbit25_mem_cases x hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  <;> rcases ht with rfl | rfl
  <;> norm_num at hdiv
  <;> first | contradiction | simp [InOrbit25, orbit25Table]

/-- The two leaves have no legal `{1,2}` step. -/
theorem orbit25_leaf (x : Nat) (hx : x = 68354 ∨ x = 136708) :
    ∀ t : Nat, t = 1 ∨ t = 2 → (5 * x + 1) % 2 ^ t ≠ 0 := by
  rcases hx with rfl | rfl <;> intro t ht <;> rcases ht with rfl | rfl <;> norm_num

/-- Any `wordValid` word over `{1,2}` started at a table state stays in
the table. -/
theorem wordValid_mem_orbit25 (w : List Nat) (x : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hx : InOrbit25 x)
    (hvalid : StringFlow.Word.wordValid w x) :
    InOrbit25 (StringFlow.Word.wordOrbit w x) := by
  induction w generalizing x with
  | nil => simpa [StringFlow.Word.wordOrbit, StringFlow.Word.wordValid] using hx
  | cons t ts ih =>
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      have hdiv : (5 * x + 1) % 2 ^ t = 0 := hvalid.1
      have hnext : InOrbit25 ((5 * x + 1) / 2 ^ t) :=
        orbit25_closed_prop x hx t ht hdiv
      have htail : StringFlow.Word.wordValid ts ((5 * x + 1) / 2 ^ t) := hvalid.2
      have hok_tail : ∀ a ∈ ts, a = 1 ∨ a = 2 := by
        intro a ha
        exact hok a (by simp [ha])
      have ih' := ih ((5 * x + 1) / 2 ^ t) hok_tail hnext htail
      simpa [StringFlow.Word.wordOrbit] using ih'

/-- `OrbitFrom7` is exactly membership in the finite 25-state table. -/
theorem OrbitFrom7_mem_orbit25 (x : Nat) (h : OrbitFrom7 x) :
    InOrbit25 x := by
  rcases h with ⟨w, hok, hvalid, hw⟩
  have hm := wordValid_mem_orbit25 w 7 hok (by simp [InOrbit25, orbit25Table]) hvalid
  rwa [← hw]

/-- Odd table states with `5 | x+1` have odd `v2(x+1)`. -/
theorem orbit25_v2_odd_of_five (x : Nat) (hx : InOrbit25 x) (hodd : IsOdd x)
    (h5 : 5 ∣ x + 1) :
    IsOdd (twoValuation (x + 1)) := by
  rcases orbit25_mem_cases x hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  <;> norm_num at h5
  <;> first | contradiction | simp [IsOdd, StringFlow.twoValuation_succ]

/-- Every table state is at most the largest leaf `136708`. -/
theorem orbit25_le (x : Nat) (hx : InOrbit25 x) : x ≤ 136708 := by
  rcases orbit25_mem_cases x hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  <;> norm_num

/-- Every even table state other than `136708` is `2 mod 4`. -/
theorem orbit25_even_mod4 (x : Nat) (hx : InOrbit25 x) (heven : x % 2 = 0) :
    x = 136708 ∨ x % 4 = 2 := by
  rcases orbit25_mem_cases x hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  <;> norm_num at heven
  <;> first | contradiction | simp

/-- `wordLast` agrees with `List.getLast`. -/
theorem wordLast_eq_getLast (w : List Nat) (hne : w ≠ []) :
    StringFlow.Word.wordLast w = w.getLast hne := by
  induction w with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.Word.wordLast]
      | cons u us =>
          have ih' := ih (by simp)
          simp [StringFlow.Word.wordLast]
          exact ih'

/-- Deleting the last entry cannot introduce a new element. -/
theorem mem_dropLast_imp_mem {w : List Nat} {t : Nat} (h : t ∈ w.dropLast) :
    t ∈ w := by
  induction w with
  | nil => simp at h
  | cons a as ih =>
      cases as with
      | nil => simp [List.dropLast] at h
      | cons b bs =>
          have h' : t = a ∨ t ∈ (b :: bs).dropLast := by
            simpa [List.dropLast] using h
          rcases h' with rfl | h''
          · simp
          · exact List.mem_cons_of_mem a (ih h'')

/-- The last entry of a nonempty word belongs to the word. -/
theorem wordLast_mem (w : List Nat) (hne : w ≠ []) :
    StringFlow.Word.wordLast w ∈ w := by
  induction w with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.Word.wordLast]
      | cons u us =>
          have ih' := ih (by simp)
          simp [StringFlow.Word.wordLast, ih']

/-- A nonempty word is its prefix plus its last entry. -/
theorem word_eq_dropLast_append_last (w : List Nat) (hne : w ≠ []) :
    w = w.dropLast ++ [StringFlow.Word.wordLast w] := by
  induction w with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [StringFlow.Word.wordLast]
      | cons u us =>
          have ih' := ih (by simp)
          simp [List.dropLast, StringFlow.Word.wordLast]
          rw [← ih']

/-- All `{1,2}` words of exact length `n`, in forward order. -/
def allWords : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      (allWords n).map (fun w => w ++ [1]) ++
      (allWords n).map (fun w => w ++ [2])

/-- All `{1,2}` words of length at most `n`. -/
def allWordsUpTo : Nat → List (List Nat)
  | 0 => allWords 0
  | n + 1 => allWords (n + 1) ++ allWordsUpTo n

/-- A `{1,2}` word of length `k` belongs to `allWords k`. -/
lemma mem_allWords_of_ok (w : List Nat) (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    w ∈ allWords w.length := by
  induction h : w.length generalizing w with
  | zero =>
      cases w with
      | nil => simp [allWords]
      | cons t ts => simp at h
  | succ n ih =>
      cases w with
      | nil => simp at h
      | cons t ts =>
          have hne : t :: ts ≠ [] := by simp
          let last := StringFlow.Word.wordLast (t :: ts)
          have hdecomp : t :: ts = (t :: ts).dropLast ++ [last] := by
            simpa [last] using word_eq_dropLast_append_last (t :: ts) hne
          have hlastmem : last ∈ t :: ts := by
            simpa [last] using wordLast_mem (t :: ts) hne
          have hlast : last = 1 ∨ last = 2 := hok last hlastmem
          have hdropok : ∀ a ∈ (t :: ts).dropLast, a = 1 ∨ a = 2 := by
            intro a ha
            exact hok a (mem_dropLast_imp_mem ha)
          have hlen' : (t :: ts).dropLast.length + 1 = n + 1 := by
            have hlenApp : ((t :: ts).dropLast ++ [last]).length =
                (t :: ts).dropLast.length + 1 := by
              rw [List.length_append]
              simp
            rw [← hdecomp] at hlenApp
            rw [h] at hlenApp
            exact hlenApp.symm
          have hlen : (t :: ts).dropLast.length = n := by omega
          have hmemdrop : (t :: ts).dropLast ∈
              allWords ((t :: ts).dropLast.length) :=
            by
              simpa [hlen] using ih (t :: ts).dropLast hdropok hlen
          rw [hdecomp]
          simp [allWords]
          rcases hlast with h1 | h2
          · left
            constructor
            · simpa [hlen] using hmemdrop
            · exact h1.symm
          · right
            constructor
            · simpa [hlen] using hmemdrop
            · exact h2.symm

/-- A `{1,2}` word of length at most `n` belongs to `allWordsUpTo n`. -/
lemma mem_allWordsUpTo_of_length_and_ok (w : List Nat) (n : Nat)
    (hw : w.length ≤ n) (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    w ∈ allWordsUpTo n := by
  induction n with
  | zero =>
      have hlen : w.length = 0 := by omega
      cases w with
      | nil => simp [allWordsUpTo, allWords]
      | cons t ts => simp at hlen
  | succ n ih =>
      by_cases hsmall : w.length ≤ n
      · exact List.mem_append.mpr (Or.inr (ih hsmall))
      · have hlen : w.length = n + 1 := by omega
        have hm := mem_allWords_of_ok w hok
        have hm' : w ∈ allWords (n + 1) := by simpa [hlen] using hm
        exact List.mem_append.mpr (Or.inl hm')

/-- Boolean `∀` over a finite list, kept reducible for kernel `decide`
closure. -/
def allBool {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | a :: as => p a && allBool p as

lemma allBool_eq_true {α : Type} (p : α → Bool) (l : List α) :
    allBool p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [allBool]
  | cons a as ih => simp [allBool, ih]

/-- Boolean version of `StringFlow.Word.wordValid`. -/
def wordValidBool : List Nat → Nat → Bool
  | [], _ => true
  | t :: ts, x => decide ((5 * x + 1) % 2 ^ t = 0) && wordValidBool ts ((5 * x + 1) / 2 ^ t)

lemma wordValidBool_eq_true (w : List Nat) (x : Nat) :
    wordValidBool w x = true ↔ StringFlow.Word.wordValid w x := by
  induction w generalizing x with
  | nil => simp [wordValidBool, StringFlow.Word.wordValid]
  | cons t ts ih =>
      simp [wordValidBool, StringFlow.Word.wordValid, ih]

/-- Boolean condition for a valid word from `7` to `229`. -/
def path229CondBool (w : List Nat) : Bool :=
  wordValidBool w 7 && decide (StringFlow.Word.wordOrbit w 7 = 229) &&
    allBool (fun t => decide (t = 1) || decide (t = 2)) w

set_option maxRecDepth 100000 in
/-- Finite uniqueness of the word from `7` to `229` among words of length
at most `8`: the only candidate is `[2,1,2,1,1,2]`. -/
theorem path229_search_all :
    allBool (fun w =>
      if path229CondBool w
        then decide (w = [2, 1, 2, 1, 1, 2])
        else true)
      (allWordsUpTo 8) = true := by
  decide

/-- Any valid word of length at most `8` from `7` to `229` is
`[2,1,2,1,1,2]`. -/
lemma path229_unique_of_length_le_8 (w : List Nat)
    (hw : w.length ≤ 8)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hend : StringFlow.Word.wordOrbit w 7 = 229) :
    w = [2, 1, 2, 1, 1, 2] := by
  have hmem : w ∈ allWordsUpTo 8 :=
    mem_allWordsUpTo_of_length_and_ok w 8 hw hok
  have hall := (allBool_eq_true
    (fun w =>
      if path229CondBool w
        then decide (w = [2, 1, 2, 1, 1, 2])
        else true)
    (allWordsUpTo 8)).mp path229_search_all w hmem
  have hvalid_bool : wordValidBool w 7 = true :=
    (wordValidBool_eq_true w 7).mpr hvalid
  have hend_bool : decide (StringFlow.Word.wordOrbit w 7 = 229) = true :=
    decide_eq_true_eq.mpr hend
  have hok_bool : allBool (fun t => decide (t = 1) || decide (t = 2)) w = true := by
    exact (allBool_eq_true (fun t => decide (t = 1) || decide (t = 2)) w).mpr
      (fun t ht => by rcases hok t ht with rfl | rfl <;> simp)
  have hcond : path229CondBool w = true := by
    simp [path229CondBool, hvalid_bool, hend_bool, hok_bool]
  rw [hcond] at hall
  exact decide_eq_true_eq.mp hall

/-- A legal `{1,2}` step strictly increases any state `x ≥ 7`. -/
lemma step_gt (x t : Nat) (ht : t = 1 ∨ t = 2) (hx : 7 ≤ x)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    x < (5 * x + 1) / 2 ^ t := by
  have hdvd : 2 ^ t ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr hdiv
  rcases hdvd with ⟨q, hq⟩
  have hqeq : (5 * x + 1) / 2 ^ t = q := by
    have hm : (2 ^ t * q) / 2 ^ t = q :=
      Nat.mul_div_right q (Nat.pow_pos (by decide : 0 < 2))
    rwa [← hq] at hm
  have hnum : 2 ^ t * (x + 1) ≤ 5 * x + 1 := by
    rcases ht with rfl | rfl <;> nlinarith [hx]
  have hle : x + 1 ≤ q := by
    have hq' : 2 ^ t * (x + 1) ≤ 2 ^ t * q := by
      simpa [hq] using hnum
    exact Nat.le_of_mul_le_mul_left hq' (Nat.pow_pos (by decide : 0 < 2))
  have hlt : x < x + 1 := by omega
  rw [hqeq]
  exact lt_of_lt_of_le hlt hle

/-- A nonempty valid `{1,2}` word strictly increases every state `x ≥ 7`. -/
lemma wordOrbit_gt (w : List Nat) (x : Nat)
    (hx : 7 ≤ x) (hne : w ≠ [])
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w x) :
    x < StringFlow.Word.wordOrbit w x := by
  cases w with
  | nil => contradiction
  | cons t ts =>
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      have hgt := step_gt x t ht hx hvalid.1
      cases ts with
      | nil => simpa [StringFlow.Word.wordOrbit] using hgt
      | cons u us =>
          have hok_tail : ∀ a ∈ u :: us, a = 1 ∨ a = 2 := by
            intro a ha
            exact hok a (by simp [ha])
          have hx' : 7 ≤ (5 * x + 1) / 2 ^ t := by omega
          have htail := wordOrbit_gt (u :: us) ((5 * x + 1) / 2 ^ t) hx' (by simp)
            hok_tail hvalid.2
          simp [StringFlow.Word.wordOrbit]
          exact lt_trans hgt htail

/-- Decomposition of `wordValid` at a cons cell. -/
lemma wordValid_cons (t : Nat) (ts : List Nat) (x : Nat) :
    StringFlow.Word.wordValid (t :: ts) x ↔
      (5 * x + 1) % 2 ^ t = 0 ∧
        StringFlow.Word.wordValid ts ((5 * x + 1) / 2 ^ t) := by
  rfl

/-- Decomposition of `wordOrbit` at a cons cell. -/
lemma wordOrbit_cons (t : Nat) (ts : List Nat) (x : Nat) :
    StringFlow.Word.wordOrbit (t :: ts) x =
      StringFlow.Word.wordOrbit ts ((5 * x + 1) / 2 ^ t) := by
  rfl

/-- No valid `{1,2}` word from `18`, `58` or `458` can end at `229`. -/
lemma no_word_from_dead_to_229 (w : List Nat) (x : Nat)
    (hx : x = 18 ∨ x = 58 ∨ x = 458)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w x)
    (hend : StringFlow.Word.wordOrbit w x = 229) : False := by
  rcases hx with rfl | rfl | rfl
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        have hsplit := (wordValid_cons t ts 18).mp hvalid
        have hdiv : (5 * 18 + 1) % 2 ^ t = 0 := hsplit.1
        rcases ht with rfl | rfl <;> norm_num at hdiv
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        have hsplit := (wordValid_cons t ts 58).mp hvalid
        have hdiv : (5 * 58 + 1) % 2 ^ t = 0 := hsplit.1
        rcases ht with rfl | rfl <;> norm_num at hdiv
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        have hsplit := (wordValid_cons t ts 458).mp hvalid
        have hdiv : (5 * 458 + 1) % 2 ^ t = 0 := hsplit.1
        rcases ht with rfl | rfl <;> norm_num at hdiv

/-- A valid `{1,2}` word from `229` that ends at `229` must be empty. -/
lemma no_nonempty_word_from_229 (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w 229)
    (hend : StringFlow.Word.wordOrbit w 229 = 229) :
    w = [] := by
  by_contra h
  have hgt := wordOrbit_gt w 229 (by norm_num) h hok hvalid
  omega

/-- Forced path from the six relevant orbit states to `229`. -/
lemma word_to_229_forced (x : Nat) (w : List Nat)
    (hx : x = 7 ∨ x = 9 ∨ x = 23 ∨ x = 29 ∨ x = 73 ∨ x = 183)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w x)
    (hend : StringFlow.Word.wordOrbit w x = 229) :
    (x = 7 ∧ w = [2, 1, 2, 1, 1, 2]) ∨
    (x = 9 ∧ w = [1, 2, 1, 1, 2]) ∨
    (x = 23 ∧ w = [2, 1, 1, 2]) ∨
    (x = 29 ∧ w = [1, 1, 2]) ∨
    (x = 73 ∧ w = [1, 2]) ∨
    (x = 183 ∧ w = [2]) := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 7).mp hvalid
          have htail : StringFlow.Word.wordValid ts 18 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 18 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          exact False.elim (no_word_from_dead_to_229 ts 18 (Or.inl rfl)
            (fun a ha => hok a (by simp [ha])) htail htail_end)
        · have hsplit := (wordValid_cons 2 ts 7).mp hvalid
          have htail : StringFlow.Word.wordValid ts 9 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 9 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hres := word_to_229_forced 9 ts (Or.inr (Or.inl rfl))
            (fun a ha => hok a (by simp [ha])) htail htail_end
          rcases hres with h | h | h | h | h | h
          · norm_num at h
          · rcases h with ⟨_, hts_eq⟩
            subst hts_eq
            left
            constructor <;> rfl
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · norm_num at h
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 9).mp hvalid
          have htail : StringFlow.Word.wordValid ts 23 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 23 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hres := word_to_229_forced 23 ts (Or.inr (Or.inr (Or.inl rfl)))
            (fun a ha => hok a (by simp [ha])) htail htail_end
          rcases hres with h | h | h | h | h | h
          · norm_num at h
          · norm_num at h
          · rcases h with ⟨_, hts_eq⟩
            subst hts_eq
            right
            left
            constructor <;> rfl
          · norm_num at h
          · norm_num at h
          · norm_num at h
        · have hsplit := (wordValid_cons 2 ts 9).mp hvalid
          have hdiv : (5 * 9 + 1) % 4 = 0 := hsplit.1
          norm_num at hdiv
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 23).mp hvalid
          have htail : StringFlow.Word.wordValid ts 58 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 58 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          exact False.elim (no_word_from_dead_to_229 ts 58 (Or.inr (Or.inl rfl))
            (fun a ha => hok a (by simp [ha])) htail htail_end)
        · have hsplit := (wordValid_cons 2 ts 23).mp hvalid
          have htail : StringFlow.Word.wordValid ts 29 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 29 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hres := word_to_229_forced 29 ts (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (fun a ha => hok a (by simp [ha])) htail htail_end
          rcases hres with h | h | h | h | h | h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · rcases h with ⟨_, hts_eq⟩
            subst hts_eq
            right
            right
            left
            constructor <;> rfl
          · norm_num at h
          · norm_num at h
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 29).mp hvalid
          have htail : StringFlow.Word.wordValid ts 73 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 73 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hres := word_to_229_forced 73 ts (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            (fun a ha => hok a (by simp [ha])) htail htail_end
          rcases hres with h | h | h | h | h | h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · rcases h with ⟨_, hts_eq⟩
            subst hts_eq
            right
            right
            right
            left
            constructor <;> rfl
          · norm_num at h
        · have hsplit := (wordValid_cons 2 ts 29).mp hvalid
          have hdiv : (5 * 29 + 1) % 4 = 0 := hsplit.1
          norm_num at hdiv
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 73).mp hvalid
          have htail : StringFlow.Word.wordValid ts 183 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 183 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hres := word_to_229_forced 183 ts (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
            (fun a ha => hok a (by simp [ha])) htail htail_end
          rcases hres with h | h | h | h | h | h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · norm_num at h
          · rcases h with ⟨_, hts_eq⟩
            subst hts_eq
            right
            right
            right
            right
            left
            constructor <;> rfl
        · have hsplit := (wordValid_cons 2 ts 73).mp hvalid
          have hdiv : (5 * 73 + 1) % 4 = 0 := hsplit.1
          norm_num at hdiv
  · cases w with
    | nil => simp [StringFlow.Word.wordOrbit] at hend
    | cons t ts =>
        have ht : t = 1 ∨ t = 2 := hok t (by simp)
        rcases ht with rfl | rfl
        · have hsplit := (wordValid_cons 1 ts 183).mp hvalid
          have htail : StringFlow.Word.wordValid ts 458 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 458 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          exact False.elim (no_word_from_dead_to_229 ts 458 (Or.inr (Or.inr rfl))
            (fun a ha => hok a (by simp [ha])) htail htail_end)
        · have hsplit := (wordValid_cons 2 ts 183).mp hvalid
          have htail : StringFlow.Word.wordValid ts 229 := by
            norm_num at hsplit
            exact hsplit
          have htail_end : StringFlow.Word.wordOrbit ts 229 = 229 := by
            have h := hend
            simpa [wordOrbit_cons] using h
          have hts : ts = [] := no_nonempty_word_from_229 ts
            (fun a ha => hok a (by simp [ha])) htail htail_end
          subst ts
          right
          right
          right
          right
          right
          constructor <;> rfl

/-- Any valid `{1,2}` word from `7` to `229` is forced to be
`[2,1,2,1,1,2]`, with no length hypothesis. -/
lemma path229_unique (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w 7)
    (hend : StringFlow.Word.wordOrbit w 7 = 229) :
    w = [2, 1, 2, 1, 1, 2] := by
  have hres := word_to_229_forced 7 w (Or.inl rfl) hok hvalid hend
  rcases hres with h | h | h | h | h | h
  · rcases h with ⟨_, hts_eq⟩
    subst hts_eq
    rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

/-- Orbit along an appended singleton. -/
theorem wordOrbit_append_singleton (pre : List Nat) (x t : Nat) :
    StringFlow.Word.wordOrbit (pre ++ [t]) x =
      (5 * StringFlow.Word.wordOrbit pre x + 1) / 2 ^ t := by
  induction pre generalizing x with
  | nil => simp [StringFlow.Word.wordOrbit]
  | cons a as ih =>
      calc
        StringFlow.Word.wordOrbit ((a :: as) ++ [t]) x
            = StringFlow.Word.wordOrbit (as ++ [t]) ((5 * x + 1) / 2 ^ a) := by
                simp [StringFlow.Word.wordOrbit]
        _ = (5 * StringFlow.Word.wordOrbit as ((5 * x + 1) / 2 ^ a) + 1) / 2 ^ t :=
                ih ((5 * x + 1) / 2 ^ a)
        _ = (5 * StringFlow.Word.wordOrbit (a :: as) x + 1) / 2 ^ t := by
                simp [StringFlow.Word.wordOrbit]

/-- Validity splits across an appended singleton. -/
theorem wordValid_append_singleton (pre : List Nat) (x t : Nat) :
    StringFlow.Word.wordValid (pre ++ [t]) x ↔
      StringFlow.Word.wordValid pre x ∧
        (5 * StringFlow.Word.wordOrbit pre x + 1) % 2 ^ t = 0 := by
  induction pre generalizing x with
  | nil => simp [StringFlow.Word.wordValid, StringFlow.Word.wordOrbit]
  | cons a as ih =>
      constructor
      · intro h
        have h1 : (5 * x + 1) % 2 ^ a = 0 := h.1
        have htail := (ih ((5 * x + 1) / 2 ^ a)).mp h.2
        constructor
        · exact ⟨h1, htail.1⟩
        · simpa [StringFlow.Word.wordOrbit] using htail.2
      · rintro ⟨⟨h1, htail1⟩, htail2⟩
        constructor
        · exact h1
        · exact (ih ((5 * x + 1) / 2 ^ a)).mpr
            ⟨htail1, by simpa [StringFlow.Word.wordOrbit] using htail2⟩

/-- Orbit along a concatenated word. -/
theorem wordOrbit_append (w1 w2 : List Nat) (x : Nat) :
    StringFlow.Word.wordOrbit (w1 ++ w2) x =
      StringFlow.Word.wordOrbit w2 (StringFlow.Word.wordOrbit w1 x) := by
  induction w1 generalizing x with
  | nil => simp [StringFlow.Word.wordOrbit]
  | cons t ts ih =>
      simp [StringFlow.Word.wordOrbit]
      exact ih ((5 * x + 1) / 2 ^ t)

/-- Validity splits across concatenation. -/
theorem wordValid_append (w1 w2 : List Nat) (x : Nat) :
    StringFlow.Word.wordValid (w1 ++ w2) x ↔
      StringFlow.Word.wordValid w1 x ∧
        StringFlow.Word.wordValid w2 (StringFlow.Word.wordOrbit w1 x) := by
  induction w1 generalizing x with
  | nil => simp [StringFlow.Word.wordValid, StringFlow.Word.wordOrbit]
  | cons t ts ih =>
      constructor
      · intro h
        have h1 : (5 * x + 1) % 2 ^ t = 0 := h.1
        have htail := (ih ((5 * x + 1) / 2 ^ t)).mp h.2
        constructor
        · exact ⟨h1, htail.1⟩
        · simpa [StringFlow.Word.wordOrbit] using htail.2
      · rintro ⟨⟨h1, htail1⟩, htail2⟩
        constructor
        · exact h1
        · exact (ih ((5 * x + 1) / 2 ^ t)).mpr
            ⟨htail1, by simpa [StringFlow.Word.wordOrbit] using htail2⟩

/--
Phase 1 coverage extension: the full legal block orbit (arbitrary step
weights, including `t=0` and `t≥3`). The only difference from
`OrbitFrom7` is dropping the `t∈{1,2}` restriction; the semantics of
`wordValid` remain "divisibility only", consistent with the block-layer
semantics.
-/
def GeneralOrbitFrom7 (x : Nat) : Prop :=
  ∃ w : List Nat,
    StringFlow.Word.wordValid w 7 ∧
    StringFlow.Word.wordOrbit w 7 = x

/-- `OrbitFrom7` is a subrelation of `GeneralOrbitFrom7` (necessary direction). -/
theorem orbit_from7_imp_general (x : Nat) (h : OrbitFrom7 x) :
    GeneralOrbitFrom7 x := by
  rcases h with ⟨w, hok, hvalid, horbit⟩
  exact ⟨w, hvalid, horbit⟩

/-- The general-orbit analogue of `IsGloballyReachable`: the previous
terminal and the reset block head are both reachable in the full
`GeneralOrbitFrom7`. -/
def GeneralIsGloballyReachable (s0 N δ : Nat) : Prop :=
  ∃ j k r rj t : Nat,
    k + 1 ≤ j ∧
    N = j - k - 1 ∧
    s0 * 5 ^ k = r + 1 ∧
    IsOdd s0 ∧ ¬ 5 ∣ s0 ∧
    s0 < 5 ^ (j - 1 - k) ∧
    GeneralOrbitFrom7 r ∧
    ResetHeadEq s0 j k t δ rj ∧
    IsOdd rj ∧
    GeneralOrbitFrom7 rj

/-- The exact stage-1 pure `t=2` `M=1` open statement in the general
orbit. This is the analogue of `pure_t2_m1_no_odd_hit` with
`GeneralIsGloballyReachable`; it is encoded here, not claimed. -/
def Stage1PureT2M1Exclusion : Prop :=
  ∀ (N s0 U δ : Nat),
    1 ≤ N →
    (0 < s0 ∧ s0 < 5 ^ N ∧ IsOdd s0 ∧ ¬ 5 ∣ s0) →
    4 ≤ U →
    (∃ L : Nat, U = 2 * L + 2 ∧ 1 ≤ L) →
    δ = 1 ∨ δ = 3 →
    GeneralIsGloballyReachable s0 N δ →
    ¬ OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ

/-- The 25-state reachability predicate is a subrelation of the general
one, so every currently closed base case lies inside the new predicate. -/
theorem globallyReachable_imp_general (s0 N δ : Nat)
    (h : IsGloballyReachable s0 N δ) :
    GeneralIsGloballyReachable s0 N δ := by
  rcases h with ⟨j, k, r, rj, t, hjk, hN, hprod, hodd, hnd5, hs0lt,
    hOrbitR, hReset, hOddRj, hOrbitRj⟩
  refine ⟨j, k, r, rj, t, hjk, hN, hprod, hodd, hnd5, hs0lt, ?_, hReset, hOddRj, ?_⟩
  · exact orbit_from7_imp_general r hOrbitR
  · exact orbit_from7_imp_general rj hOrbitRj

/-- The general orbit is closed under legal single steps: if `x` is
reachable and the `t` step divides, then the successor is reachable. -/
theorem general_orbit_step (x t : Nat) (hvalid : (5 * x + 1) % 2 ^ t = 0)
    (h : GeneralOrbitFrom7 x) :
    GeneralOrbitFrom7 ((5 * x + 1) / 2 ^ t) := by
  rcases h with ⟨w, hvalidw, horbit⟩
  refine ⟨w ++ [t], ?_, ?_⟩
  · rw [wordValid_append_singleton]
    constructor
    · exact hvalidw
    · simpa [horbit] using hvalid
  · rw [wordOrbit_append_singleton]
    rw [horbit]

/-- A `t=0` step (entering the next odd number after an even exit) is
legal in the general orbit. -/
theorem general_orbit_step_t0 (x : Nat) (h : GeneralOrbitFrom7 x) :
    GeneralOrbitFrom7 (5 * x + 1) := by
  simpa using general_orbit_step x 0 (by
    change (5 * x + 1) % 1 = 0
    exact Nat.mod_one (5 * x + 1)) h

/-- A valid word ending in `1` remains valid after deleting the last step,
and its endpoint is the `t=1` successor of the prefix endpoint. -/
theorem wordValid_pred_last_one (w : List Nat) (x : Nat)
    (hvalid : StringFlow.Word.wordValid w x)
    (hlast : StringFlow.Word.wordLast w = 1) :
    StringFlow.Word.wordValid w.dropLast x ∧
      StringFlow.Word.wordOrbit w x =
        (5 * StringFlow.Word.wordOrbit w.dropLast x + 1) / 2 := by
  have hne : w ≠ [] := by
    intro h
    subst w
    simp [StringFlow.Word.wordLast] at hlast
  have hw : w = w.dropLast ++ [1] := by
    simpa [hlast] using word_eq_dropLast_append_last w hne
  have hsplit : StringFlow.Word.wordValid w x ↔
      StringFlow.Word.wordValid w.dropLast x ∧
        (5 * StringFlow.Word.wordOrbit w.dropLast x + 1) % 2 = 0 := by
    rw [hw]
    simpa using wordValid_append_singleton w.dropLast x 1
  have hs := hsplit.mp hvalid
  constructor
  · exact hs.1
  · have hleft : StringFlow.Word.wordOrbit w x =
        StringFlow.Word.wordOrbit (w.dropLast ++ [1]) x :=
      congrArg (fun z => StringFlow.Word.wordOrbit z x) hw
    have hright : StringFlow.Word.wordOrbit (w.dropLast ++ [1]) x =
        (5 * StringFlow.Word.wordOrbit w.dropLast x + 1) / 2 :=
      wordOrbit_append_singleton w.dropLast x 1
    exact hleft.trans hright

/-- If `y` is orbit-reachable and `y % 5 = 3`, its `t=1` predecessor is
also orbit-reachable. -/
theorem OrbitFrom7_pred_of_mod_three (y : Nat) (hy : OrbitFrom7 y)
    (hmod : y % 5 = 3) :
    ∃ x : Nat, OrbitFrom7 x ∧ 2 * y = 5 * x + 1 := by
  rcases hy with ⟨w, hok, hvalid, hw⟩
  have hne : w ≠ [] := by
    intro h
    subst w
    simp [StringFlow.Word.wordOrbit] at hw
    omega
  have hlast12 : StringFlow.Word.wordLast w = 1 ∨ StringFlow.Word.wordLast w = 2 := by
    exact hok (StringFlow.Word.wordLast w) (wordLast_mem w hne)
  have hlast1 : StringFlow.Word.wordLast w = 1 := by
    rcases hlast12 with h1 | h2
    · exact h1
    · have h5 := StringFlow.Word.wordOrbit_mod_five_of_last_two w 7 hvalid h2
      rw [hw] at h5
      omega
  have hvp := wordValid_pred_last_one w 7 hvalid hlast1
  let x := StringFlow.Word.wordOrbit w.dropLast 7
  refine ⟨x, ?_, ?_⟩
  · exact ⟨w.dropLast, fun t ht => hok t (mem_dropLast_imp_mem ht), hvp.1, rfl⟩
  · have hw' : w = w.dropLast ++ [1] := by
      simpa [hlast1] using word_eq_dropLast_append_last w hne
    have hvalid' : StringFlow.Word.wordValid (w.dropLast ++ [1]) 7 := by
      rwa [← hw']
    have hsplit := (wordValid_append_singleton w.dropLast 7 1).mp hvalid'
    have hdiv : (5 * x + 1) % 2 = 0 := by
      simpa [x] using hsplit.2
    have hy' : StringFlow.Word.wordOrbit w 7 = (5 * x + 1) / 2 := by
      simpa [x] using hvp.2
    rw [← hw, hy']
    exact Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)

/-- `5^n ≡ 1 (mod 4)` for every `n`. -/
lemma five_pow_mod_four (n : Nat) : 5 ^ n % 4 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- An odd hit inside `(F)` forces the cleared equation
`t0*2^U = s0 + δ*5^N` and the smallness `4*s0 < 5^N`. -/
theorem oddHit_reduces (N U δ s0 t0 : Nat)
    (hδ : δ = 1 ∨ δ = 3)
    (hs0lt : s0 < 5 ^ N)
    (hmod : t0 * 2 ^ U ≡ s0 [MOD 5 ^ N])
    (hHit : OddHit t0 N U δ) :
    4 * s0 < 5 ^ N ∧ t0 * 2 ^ U = s0 + δ * 5 ^ N := by
  let a := t0 * 2 ^ U
  have hlow : 4 * δ * 5 ^ N < 4 * a := by
    dsimp [a]
    simpa [Nat.mul_assoc] using hHit.2.1
  have hhigh : 4 * a < (4 * δ + 1) * 5 ^ N := by
    dsimp [a]
    simpa [Nat.mul_assoc] using hHit.2.2
  have hδpos : 0 < δ := by rcases hδ with rfl | rfl <;> norm_num
  have hδle : 1 ≤ δ := by omega
  have ha_gt : δ * 5 ^ N < a := by
    nlinarith [hlow]
  have h5lt : 5 ^ N < a := by
    have hle5 : 5 ^ N ≤ δ * 5 ^ N := Nat.le_mul_of_pos_left (5 ^ N) hδpos
    exact lt_of_le_of_lt hle5 ha_gt
  have hs0le : s0 < a := lt_trans hs0lt h5lt
  have hmod' : a ≡ s0 [MOD 5 ^ N] := by
    simpa [a] using hmod
  change a % 5 ^ N = s0 % 5 ^ N at hmod'
  have hsub0 : (a - s0) % 5 ^ N = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq hmod'
  have hsubdvd : 5 ^ N ∣ a - s0 := Nat.dvd_iff_mod_eq_zero.mpr hsub0
  rcases hsubdvd with ⟨q, hq⟩
  have haeq : a = s0 + q * 5 ^ N := by
    have hq' : a - s0 = q * 5 ^ N := by simpa [Nat.mul_comm] using hq
    omega
  have hlow' : 4 * δ * 5 ^ N < 4 * (s0 + q * 5 ^ N) := by
    simpa [a, haeq] using hlow
  have hhigh' : 4 * (s0 + q * 5 ^ N) < (4 * δ + 1) * 5 ^ N := by
    simpa [a, haeq] using hhigh
  have hqge : δ ≤ q := by
    by_contra h
    have hqlt : q < δ := by omega
    have hqle : q + 1 ≤ δ := by omega
    nlinarith [hs0lt]
  have hqle' : q ≤ δ := by
    by_contra h
    have hqgt : δ < q := by omega
    have hqge' : δ + 1 ≤ q := by omega
    nlinarith [hs0lt]
  have hqeq : q = δ := by omega
  constructor
  · have h4s : 4 * s0 + 4 * δ * 5 ^ N < 4 * δ * 5 ^ N + 5 ^ N := by
      nlinarith [hhigh']
    nlinarith
  · have h : a = s0 + δ * 5 ^ N := by
      simpa [hqeq] using haeq
    simpa [a] using h

/-- `t0 = ⟨s0·2^(-U)⟩_{5^N}` satisfies `t0·2^U ≡ s0 (mod 5^N)`. -/
lemma t0_congruence (N U s0 : Nat) :
    leastResidue (s0 * pow2Inv U N) (5 ^ N) * 2 ^ U ≡ s0 [MOD 5 ^ N] := by
  let inv := pow2Inv U N
  let t0 := (s0 * inv) % 5 ^ N
  have hmod1 : s0 * inv ≡ t0 [MOD 5 ^ N] := by
    dsimp [t0]
    exact (Nat.mod_modEq (s0 * inv) (5 ^ N)).symm
  have hinv : 2 ^ U * inv ≡ 1 [MOD 5 ^ N] := by
    dsimp [inv]
    exact pow2Inv_correct U N
  have hleft : (s0 * inv) * 2 ^ U ≡ t0 * 2 ^ U [MOD 5 ^ N] :=
    hmod1.mul_right (2 ^ U)
  have hright : (s0 * inv) * 2 ^ U ≡ s0 [MOD 5 ^ N] := by
    have hre : (s0 * inv) * 2 ^ U = s0 * (2 ^ U * inv) := by ring
    rw [hre]
    simpa using hinv.mul_left s0
  exact hleft.symm.trans hright

/-- A `t=1` reset head cannot occur in a pure `t=2` chain odd hit: the
hit equation forces `rj` even, contradicting `IsOdd rj`. This removes
the `t=1` branch from the general-orbit `M=1` exclusion. -/
lemma stage1_m1_no_t1_branch
    (N s0 U δ j k rj t : Nat)
    (hN : N = j - k - 1)
    (hjk_le : k + 1 ≤ j)
    (hU : 4 ≤ U)
    (hS0pos : 0 < s0)
    (hS0lt : s0 < 5 ^ N)
    (hres : ResetHeadEq s0 j k t δ rj)
    (ht : t = 1)
    (hOddRj : IsOdd rj)
    (hHit : OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ) :
    False := by
  let t0 := leastResidue (s0 * pow2Inv U N) (5 ^ N)
  have hcong : t0 * 2 ^ U ≡ s0 [MOD 5 ^ N] := by
    dsimp [t0]
    exact t0_congruence N U s0
  rcases hres with h1 | h2
  · rcases h1 with ⟨ht1, hδ1, hres1⟩
    have hred := oddHit_reduces N U δ s0 t0
      (by rw [hδ1]; exact Or.inl rfl) hS0lt hcong hHit
    have hte : t0 * 2 ^ U = s0 + 5 ^ N := by
      simpa [hδ1] using hred.2
    have hjk : j = k + 1 + N := by omega
    have h5j : 5 ^ j = 5 ^ (k + 1) * 5 ^ N := by
      rw [hjk, Nat.pow_add]
    have hmul : 5 ^ (k + 1) * s0 + 5 ^ (k + 1) * 5 ^ N =
        5 ^ (k + 1) * (s0 + 5 ^ N) := by ring
    have hge2 : 2 ≤ 5 ^ (k + 1) * (s0 + 5 ^ N) := by
      have h1 : 1 ≤ 5 ^ (k + 1) := Nat.one_le_pow (k + 1) 5 (by decide)
      have h5Nge : 1 ≤ 5 ^ N := Nat.one_le_pow N 5 (by decide)
      have h2 : 2 ≤ s0 + 5 ^ N := by omega
      nlinarith [h1, h2]
    have hres' : 2 * (rj + 1) = 5 ^ (k + 1) * (s0 + 5 ^ N) - 2 := by
      rw [hres1, h5j, hmul]
    have hres_add : 2 * (rj + 1) + 2 = 5 ^ (k + 1) * (s0 + 5 ^ N) := by
      rw [hres']
      exact Nat.sub_add_cancel hge2
    have hres_t : 2 * (rj + 1) + 2 = 5 ^ (k + 1) * t0 * 2 ^ U := by
      rw [hres_add]
      have hte' : s0 + 5 ^ N = t0 * 2 ^ U := hte.symm
      rw [hte']
      ring
    have hleft : 2 * (rj + 2) = 5 ^ (k + 1) * t0 * 2 ^ U := by
      have hre : 2 * (rj + 2) = 2 * (rj + 1) + 2 := by ring
      rw [hre]
      exact hres_t
    have hpowU : 2 ^ U = 2 * 2 ^ (U - 1) := by
      have hUeq : U = 1 + (U - 1) := by omega
      rw [hUeq, Nat.pow_add]
      norm_num
    have h2eq : 2 * (rj + 2) = 2 * (5 ^ (k + 1) * t0 * 2 ^ (U - 1)) := by
      rw [hleft, hpowU]
      ring
    have hcancel : rj + 2 = 5 ^ (k + 1) * t0 * 2 ^ (U - 1) :=
      Nat.mul_left_cancel (by norm_num : 0 < 2) h2eq
    have hpowU1 : 2 ^ (U - 1) = 2 * 2 ^ (U - 2) := by
      have hUeq2 : U - 1 = 1 + (U - 2) := by omega
      rw [hUeq2, Nat.pow_add]
    let q := 5 ^ (k + 1) * t0 * 2 ^ (U - 2)
    have hrhs : 5 ^ (k + 1) * t0 * 2 ^ (U - 1) = 2 * q := by
      dsimp [q]
      rw [hpowU1]
      ring
    have h2rhs : rj + 2 = 2 * q := by
      rw [hcancel, hrhs]
    have ht0pos : 0 < t0 := by
      by_contra hle
      have h0 : t0 = 0 := by omega
      change OddHit t0 N U δ at hHit
      rw [h0] at hHit
      simp [OddHit, IsOdd] at hHit
    have hqpos : 1 ≤ q := by
      have h1 : 1 ≤ 5 ^ (k + 1) := Nat.one_le_pow (k + 1) 5 (by decide)
      have h2 : 1 ≤ t0 := by omega
      have h3 : 1 ≤ 2 ^ (U - 2) := Nat.one_le_pow (U - 2) 2 (by decide)
      dsimp [q]
      nlinarith
    have hdec : rj = 2 * (q - 1) := by omega
    have hEven : 2 ∣ rj := ⟨q - 1, hdec⟩
    have hmod0 : rj % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hEven
    have hodd : rj % 2 = 1 := by simpa [IsOdd] using hOddRj
    omega
  · rcases h2 with ⟨ht2, hδ2, hres2⟩
    rw [ht] at ht2
    norm_num at ht2

/-- Under an odd hit, the reset branch of a pure `t=2` `M=1` block
cannot be `t=1`; the hit equation would make the reset head even. -/
lemma stage1_m1_reset_is_t2
    (N s0 U δ j k _r rj t : Nat)
    (hN : N = j - k - 1)
    (hjk_le : k + 1 ≤ j)
    (hU : 4 ≤ U)
    (hS0pos : 0 < s0)
    (hS0lt : s0 < 5 ^ N)
    (hres : ResetHeadEq s0 j k t δ rj)
    (hOddRj : IsOdd rj)
    (hHit : OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ) :
    t = 2 := by
  rcases hres with h1 | h2
  · exfalso
    exact stage1_m1_no_t1_branch N s0 U δ j k rj t hN hjk_le hU hS0pos
      hS0lt (Or.inl h1) h1.1 hOddRj hHit
  · exact h2.1

/-- The `t=2`-only version of the general-orbit `M=1` exclusion: the
witness is required to use the `t=2` reset branch. -/
def Stage1PureT2M1ExclusionT2 : Prop :=
  ∀ (N s0 U δ : Nat),
    1 ≤ N →
    (0 < s0 ∧ s0 < 5 ^ N ∧ IsOdd s0 ∧ ¬ 5 ∣ s0) →
    4 ≤ U →
    (∃ L : Nat, U = 2 * L + 2 ∧ 1 ≤ L) →
    δ = 1 ∨ δ = 3 →
    (∃ j k r rj t : Nat,
      k + 1 ≤ j ∧ N = j - k - 1 ∧ s0 * 5 ^ k = r + 1 ∧
      IsOdd s0 ∧ ¬ 5 ∣ s0 ∧ s0 < 5 ^ (j - 1 - k) ∧
      GeneralOrbitFrom7 r ∧ ResetHeadEq s0 j k t δ rj ∧
      t = 2 ∧ IsOdd rj ∧ GeneralOrbitFrom7 rj) →
    ¬ OddHit (leastResidue (s0 * pow2Inv U N) (5 ^ N)) N U δ

/-- The full general-orbit `M=1` exclusion reduces to its `t=2` branch:
the `t=1` branch is already excluded by parity. -/
theorem stage1_pure_t2_m1_exclusion_of_t2
    (hT2 : Stage1PureT2M1ExclusionT2) :
    Stage1PureT2M1Exclusion := by
  intro N s0 U δ hN hS0 hU hUeven hδ hReach hHit
  rcases hReach with ⟨j, k, r, rj, t, hjk_le, hNdef, hprod, hodd_s0,
    hnd5_s0, hs0lt, hOrbitR, hReset, hOddRj, hOrbitRj⟩
  have ht2 : t = 2 :=
    stage1_m1_reset_is_t2 N s0 U δ j k r rj t hNdef hjk_le hU hS0.1
      hS0.2.1 hReset hOddRj hHit
  have hw : ∃ j k r rj t : Nat,
      k + 1 ≤ j ∧ N = j - k - 1 ∧ s0 * 5 ^ k = r + 1 ∧
      IsOdd s0 ∧ ¬ 5 ∣ s0 ∧ s0 < 5 ^ (j - 1 - k) ∧
      GeneralOrbitFrom7 r ∧ ResetHeadEq s0 j k t δ rj ∧
      t = 2 ∧ IsOdd rj ∧ GeneralOrbitFrom7 rj :=
    ⟨j, k, r, rj, t, hjk_le, hNdef, hprod, hodd_s0, hnd5_s0, hs0lt,
      hOrbitR, hReset, ht2, hOddRj, hOrbitRj⟩
  exact hT2 N s0 U δ hN hS0 hU hUeven hδ hw hHit

/-- The `t=1` reset algebra: if `rj=(5x+1)/2`, then the previous
terminal is `x = r + 5^(j-1)`. -/
theorem t1_reset_prev_state (s0 j k r rj x : Nat)
    (hj : 1 ≤ j)
    (hs0 : s0 * 5 ^ k = r + 1)
    (hreset : 2 * (rj + 1) = 5 ^ (k + 1) * s0 + 5 ^ j - 2)
    (hprev : 2 * rj = 5 * x + 1) :
    x = r + 5 ^ (j - 1) := by
  have h5k : 5 ^ (k + 1) = 5 * 5 ^ k := by
    rw [Nat.pow_succ]
    ring_nf
  have hj' : j = (j - 1) + 1 := by omega
  have h5j : 5 ^ j = 5 * 5 ^ (j - 1) := by
    conv_lhs => rw [hj']
    rw [Nat.pow_succ]
    ring_nf
  have h5jge : 2 ≤ 5 ^ j := by
    have h1 : 1 ≤ 5 ^ j := Nat.one_le_pow j 5 (by decide)
    omega
  have hsub5 : 5 ^ j - 2 + 2 = 5 ^ j := Nat.sub_add_cancel h5jge
  have hres' : 2 * (rj + 1) = 5 * (5 ^ k * s0) + (5 * 5 ^ (j - 1) - 2) := by
    rw [h5k, h5j] at hreset
    have hge2 : 2 ≤ 5 * 5 ^ (j - 1) := by
      simpa [h5j] using h5jge
    have hrew : 5 * 5 ^ k * s0 + 5 * 5 ^ (j - 1) - 2 =
        5 * (5 ^ k * s0) + (5 * 5 ^ (j - 1) - 2) := by
      simpa [Nat.mul_assoc] using (Nat.add_sub_assoc hge2 (5 * 5 ^ k * s0))
    rwa [hrew] at hreset
  have hsum : 2 * (rj + 1) + 2 = 5 * (x + 1) := by
    nlinarith [hprev]
  have hsub5' : 5 * 5 ^ (j - 1) - 2 + 2 = 5 * 5 ^ (j - 1) := by
    simpa [h5j] using hsub5
  have hxeq : 5 * (x + 1) = 5 * (5 ^ k * s0 + 5 ^ (j - 1)) := by
    have hA : 2 * (rj + 1) + 2 = 5 * (5 ^ k * s0 + 5 ^ (j - 1)) := by
      nlinarith [hres', hsub5']
    nlinarith [hsum, hA]
  have hcancel : x + 1 = 5 ^ k * s0 + 5 ^ (j - 1) :=
    Nat.mul_left_cancel (by decide : 0 < 5) hxeq
  nlinarith [hs0, hcancel]

/-- A `t=1` reset head is `3 mod 5`. -/
lemma t1_reset_rj_mod_five (s0 j k rj : Nat)
    (hj : 1 ≤ j)
    (hreset : 2 * (rj + 1) = 5 ^ (k + 1) * s0 + 5 ^ j - 2) :
    rj % 5 = 3 := by
  have h5k : 5 ^ (k + 1) = 5 * 5 ^ k := by
    rw [Nat.pow_succ]
    ring_nf
  have hj' : j = (j - 1) + 1 := by omega
  have h5j : 5 ^ j = 5 * 5 ^ (j - 1) := by
    conv_lhs => rw [hj']
    rw [Nat.pow_succ]
    ring_nf
  have h5jge2 : 2 ≤ 5 ^ j := by
    have h1 : 1 ≤ 5 ^ j := Nat.one_le_pow j 5 (by decide)
    omega
  have hsub5 : 5 ^ j - 2 + 2 = 5 ^ j := Nat.sub_add_cancel h5jge2
  have hgeZ : 1 ≤ 5 ^ k * s0 + 5 ^ (j - 1) := by
    have h1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by decide)
    omega
  have hrew : 2 * (rj + 1) = 5 * (5 ^ k * s0 + 5 ^ (j - 1) - 1) + 3 := by
    rw [h5k, h5j] at hreset
    have hge2 : 2 ≤ 5 * 5 ^ (j - 1) := by simpa [h5j] using h5jge2
    have hrew' : 5 * 5 ^ k * s0 + 5 * 5 ^ (j - 1) - 2 =
        5 * (5 ^ k * s0) + (5 * 5 ^ (j - 1) - 2) := by
      simpa [Nat.mul_assoc] using (Nat.add_sub_assoc hge2 (5 * 5 ^ k * s0))
    rw [hrew'] at hreset
    have hsub5' : 5 * 5 ^ (j - 1) - 2 + 2 = 5 * 5 ^ (j - 1) := by
      simpa [h5j] using hsub5
    have hres2 : 2 * (rj + 1) + 2 = 5 * (5 ^ k * s0 + 5 ^ (j - 1)) := by
      nlinarith [hreset, hsub5']
    have hZ : 5 ^ k * s0 + 5 ^ (j - 1) =
        (5 ^ k * s0 + 5 ^ (j - 1) - 1) + 1 := by omega
    nlinarith [hres2, hZ]
  have hmod : (2 * (rj + 1)) % 5 = 3 := by
    rw [hrew]
    rw [Nat.add_mod, Nat.mul_mod]
    norm_num
  have h2mod : (2 * rj) % 5 = 1 := by
    have hmod2 : (2 * rj + 2) % 5 = 3 := by
      simpa [Nat.mul_add] using hmod
    have hsplit : (2 * rj + 2) % 5 = ((2 * rj) % 5 + 2) % 5 := by
      rw [Nat.add_mod]
    rw [hsplit] at hmod2
    have hlt : (2 * rj) % 5 < 5 := Nat.mod_lt (2 * rj) (by decide)
    omega
  have hmod3 : (2 * (rj % 5)) % 5 = 1 := by
    simpa [Nat.mul_mod] using h2mod
  have hcases : rj % 5 = 0 ∨ rj % 5 = 1 ∨ rj % 5 = 2 ∨ rj % 5 = 3 ∨ rj % 5 = 4 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · simp [h0] at hmod3
  · simp [h1] at hmod3
  · simp [h2] at hmod3
  · exact h3
  · simp [h4] at hmod3

/-- A `t=2` reset block head always has `5 | rj+1`. -/
lemma t2_reset_rj_plus_one_mod_five (s0 j k δ rj : Nat)
    (hj : 1 ≤ j)
    (hreset : 4 * (rj + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j) :
    5 ∣ rj + 1 := by
  have hdvd : 5 ∣ 4 * (rj + 1) := by
    refine ⟨5 ^ k * s0 + δ * 5 ^ (j - 1), ?_⟩
    rw [hreset]
    have hsucck : k + 1 = Nat.succ k := by omega
    have hpowk : 5 ^ (k + 1) = 5 * 5 ^ k := by
      rw [hsucck, Nat.pow_succ, Nat.mul_comm]
    have hsuccj : j = Nat.succ (j - 1) := by omega
    have hpowj : 5 ^ j = 5 * 5 ^ (j - 1) := by
      rw [hsuccj, Nat.pow_succ, Nat.mul_comm]
      rw [Nat.succ_sub_one]
    rw [hpowk, hpowj]
    ring
  have hcop : Nat.Coprime 4 5 := by decide
  exact hcop.symm.dvd_of_dvd_mul_left hdvd

/-- A `t=2` reset block head satisfies `rj ≡ 4 (mod 5)`. -/
lemma t2_reset_rj_mod_five (s0 j k δ rj : Nat)
    (hj : 1 ≤ j)
    (hreset : 4 * (rj + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j) :
    rj % 5 = 4 := by
  have hdvd := t2_reset_rj_plus_one_mod_five s0 j k δ rj hj hreset
  have hmod : (rj + 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hsplit : (rj + 1) % 5 = (rj % 5 + 1) % 5 := by
    rw [Nat.add_mod]
  rw [hsplit] at hmod
  have hlt : rj % 5 < 5 := Nat.mod_lt rj (by decide)
  omega

/-- The reset equation fixes the block head modulo `5` in both branches:
`t=1` gives `rj≡3`, `t=2` gives `rj≡4` (`5 | rj+1`). -/
theorem reset_head_mod_five (s0 j k t δ rj : Nat)
    (hj : 1 ≤ j)
    (hReset : ResetHeadEq s0 j k t δ rj) :
    (t = 1 → rj % 5 = 3) ∧ (t = 2 → rj % 5 = 4) := by
  rcases hReset with h1 | h2
  · rcases h1 with ⟨ht1, hδ1, hres1⟩
    constructor
    · intro ht
      rw [ht1] at ht
      exact t1_reset_rj_mod_five s0 j k rj hj hres1
    · intro ht
      rw [ht1] at ht
      norm_num at ht
  · rcases h2 with ⟨ht2, hδ2, hres2⟩
    constructor
    · intro ht
      rw [ht2] at ht
      norm_num at ht
    · intro ht
      rw [ht2] at ht
      exact t2_reset_rj_mod_five s0 j k δ rj hj hres2

/-- Combining the mod-5 class with oddness fixes the block head modulo
`10`: `t=1→rj≡3`, `t=2→rj≡9`. -/
theorem reset_head_mod_ten (s0 j k t δ rj : Nat)
    (hj : 1 ≤ j)
    (hReset : ResetHeadEq s0 j k t δ rj)
    (hodd : IsOdd rj) :
    (t = 1 → rj % 10 = 3) ∧ (t = 2 → rj % 10 = 9) := by
  have hmod5 := reset_head_mod_five s0 j k t δ rj hj hReset
  have h2 : rj % 2 = 1 := by simpa [IsOdd] using hodd
  have hrel : rj % 5 = (rj % 10) % 5 := by
    have hdec : rj = 10 * (rj / 10) + rj % 10 := (Nat.div_add_mod rj 10).symm
    rw [hdec, Nat.add_mod, Nat.mul_mod]
    norm_num
  have hrel2 : rj % 2 = (rj % 10) % 2 := by
    have hdec : rj = 10 * (rj / 10) + rj % 10 := (Nat.div_add_mod rj 10).symm
    rw [hdec, Nat.add_mod, Nat.mul_mod]
    norm_num
  constructor
  · intro ht
    have h5 : rj % 5 = 3 := hmod5.1 ht
    have h5' : (rj % 10) % 5 = 3 := by
      rw [← hrel]
      exact h5
    have h2' : (rj % 10) % 2 = 1 := by
      rw [← hrel2]
      exact h2
    have hrlt : rj % 10 < 10 := Nat.mod_lt rj (by decide)
    interval_cases rj % 10 <;> try norm_num at h5' <;> try norm_num at h2' <;> try rfl
  · intro ht
    have h5 : rj % 5 = 4 := hmod5.2 ht
    have h5' : (rj % 10) % 5 = 4 := by
      rw [← hrel]
      exact h5
    have h2' : (rj % 10) % 2 = 1 := by
      rw [← hrel2]
      exact h2
    have hrlt : rj % 10 < 10 := Nat.mod_lt rj (by decide)
    interval_cases rj % 10 <;> try norm_num at h5' <;> try norm_num at h2' <;> try rfl

/-- A reset block head always satisfies the state bound `rj < 5^j`,
using only the previous-terminal size bound and the reset equation. -/
theorem reset_head_lt_five_pow (s0 j k t δ rj : Nat)
    (hjk : k + 1 ≤ j)
    (hs0 : s0 < 5 ^ (j - 1 - k))
    (hReset : ResetHeadEq s0 j k t δ rj) :
    rj < 5 ^ j := by
  have h5s0 : 5 ^ (k + 1) * s0 < 5 ^ j := by
    have hsum : (k + 1) + (j - 1 - k) = j := by omega
    have hpow : 5 ^ (k + 1) * 5 ^ (j - 1 - k) = 5 ^ j := by
      rw [← Nat.pow_add]
      rw [hsum]
    have hlt := Nat.mul_lt_mul_of_pos_left hs0
      (Nat.pow_pos (by decide : 0 < 5) : 0 < 5 ^ (k + 1))
    simpa [hpow] using hlt
  rcases hReset with h1 | h2
  · rcases h1 with ⟨ht1, hδ1, hres1⟩
    have hsum : 5 ^ (k + 1) * s0 + 5 ^ j - 2 < 2 * 5 ^ j := by
      omega
    have hres1' : 2 * (rj + 1) < 2 * 5 ^ j := by
      omega
    have hlt : rj + 1 < 5 ^ j := by omega
    omega
  · rcases h2 with ⟨ht2, hδ2, hres2⟩
    have hδle : δ ≤ 3 := by rcases hδ2 with hδ1 | hδ3 <;> omega
    have hδprod : δ * 5 ^ j ≤ 3 * 5 ^ j :=
      Nat.mul_le_mul_right (5 ^ j) hδle
    have hsum : 5 ^ (k + 1) * s0 + δ * 5 ^ j < 4 * 5 ^ j := by
      nlinarith [h5s0, hδprod]
    have hres2' : 4 * (rj + 1) < 4 * 5 ^ j := by
      omega
    have hlt : rj + 1 < 5 ^ j := by omega
    omega

/-- A reset block head is not too small: `5^j <= 2^t*rj`.  The reset
equation and the positivity of the odd part `s0` give the lower bound
directly.  Together with `reset_head_lt_five_pow` this is the exact
block-head size interval needed by the `q0` interval
`[2^Wp, 2^Wj)` of `All36_20Premises`. -/
theorem reset_head_lower_bound (s0 j k t δ rj : Nat)
    (hodd : IsOdd s0)
    (hReset : ResetHeadEq s0 j k t δ rj) :
    5 ^ j ≤ 2 ^ t * rj := by
  have hs0pos : 0 < s0 := by
    have hmod : s0 % 2 = 1 := hodd
    omega
  have h5s0 : 5 ≤ 5 ^ (k + 1) * s0 := by
    have h5pow : 5 ≤ 5 ^ (k + 1) := by
      have hk : 1 ≤ k + 1 := by omega
      simpa using (Nat.pow_le_pow_right (by decide : 0 < 5) hk)
    nlinarith
  rcases hReset with h1 | h2
  · rcases h1 with ⟨ht, hδ, heq⟩
    subst t
    subst δ
    have hsub : 3 ≤ 5 ^ (k + 1) * s0 - 2 := by omega
    have hge : 5 ^ j + 3 ≤ 2 * (rj + 1) := by
      rw [heq]
      omega
    omega
  · rcases h2 with ⟨ht, hδ, heq⟩
    subst t
    have hδpos : 0 < δ := by
      rcases hδ with hδ1 | hδ3 <;> omega
    have hge : 5 ^ j + 5 ≤ 4 * (rj + 1) := by
      rw [heq]
      nlinarith
    omega

/-- The reset block-head size interval: `5^j <= 2^t*rj < 2^t*5^j`,
assembled from the lower bound above and `reset_head_lt_five_pow`. -/
theorem reset_head_size_bounds (s0 j k t δ rj : Nat)
    (hodd : IsOdd s0)
    (hjk : k + 1 ≤ j)
    (hs0 : s0 < 5 ^ (j - 1 - k))
    (hReset : ResetHeadEq s0 j k t δ rj) :
    5 ^ j ≤ 2 ^ t * rj ∧ rj < 5 ^ j :=
  ⟨reset_head_lower_bound s0 j k t δ rj hodd hReset,
    reset_head_lt_five_pow s0 j k t δ rj hjk hs0 hReset⟩

/-- A C3 reset head also satisfies `rj < 5^j`: from
`2^(t-2)*(rj+1) = 5^(k+1)*s0 + 2^(t-2) - 1` and the size bound on
`s0`, the whole right-hand side stays below `2^(t-2)*5^j`. -/
theorem reset_head_c3_lt_five_pow
    (s0 j k t rj : Nat)
    (hjk : k + 1 ≤ j)
    (hs0 : s0 < 5 ^ (j - 1 - k))
    (hReset : ResetHeadEqC3 s0 j k t rj) :
    rj < 5 ^ j := by
  rcases hReset with ⟨ht, heq⟩
  have h5s0 : 5 ^ (k + 1) * s0 < 5 ^ j := by
    have hsum : (k + 1) + (j - 1 - k) = j := by omega
    have hpow : 5 ^ (k + 1) * 5 ^ (j - 1 - k) = 5 ^ j := by
      rw [← Nat.pow_add]
      rw [hsum]
    have hlt := Nat.mul_lt_mul_of_pos_left hs0
      (Nat.pow_pos (by decide : 0 < 5) : 0 < 5 ^ (k + 1))
    simpa [hpow] using hlt
  let A := 2 ^ (t - 2)
  have htA : 2 ≤ A := by
    dsimp [A]
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ t - 2)
    simpa using h
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hle : 5 ^ j + A - 1 ≤ A * 5 ^ j := by
    have hA1pos : 0 < A - 1 := by omega
    have h5 : 5 ^ j ≤ (A - 1) * 5 ^ j :=
      Nat.le_mul_of_pos_left (5 ^ j) hA1pos
    have hA1eq : A * 5 ^ j = (A - 1) * 5 ^ j + 5 ^ j := by
      have hA : A = A - 1 + 1 := by omega
      conv_lhs => rw [hA]
      ring
    rw [hA1eq]
    have hA1le : A - 1 ≤ (A - 1) * 5 ^ j :=
      Nat.le_mul_of_pos_right (A - 1) (by positivity)
    omega
  have hlt2 : 5 ^ (k + 1) * s0 + A - 1 < A * 5 ^ j := by
    have hsumlt : 5 ^ (k + 1) * s0 + A - 1 < 5 ^ j + A - 1 := by omega
    exact lt_of_lt_of_le hsumlt hle
  have hltmul : A * (rj + 1) < A * 5 ^ j := by
    have heq' : A * (rj + 1) = 5 ^ (k + 1) * s0 + A - 1 := by
      dsimp [A]
      exact heq
    rw [heq']
    exact hlt2
  have hlt' : rj + 1 < 5 ^ j :=
    (Nat.mul_lt_mul_left hApos).1 hltmul
  omega

/-- Nat version of the exact `t=2` chain closed form:
`4^n*(r_n+1) = 5^n*(r_0+1)`. -/
lemma t2_chain_plus_one_nat (r : Nat → Nat) (n : Nat)
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

/-- Lemma 15.1, t=2 branch: after a `t=2` reset and `L` further exact
`t=2` steps, the new terminal odd part is
`s' = (s0 + δ*5^(j-k-1)) / 2^(2L+2)`, with terminal chain length
`k+1+L`. -/
theorem terminal_s_transfer_t2
    (s0 j k δ rj : Nat) (L : Nat)
    (hjk : k + 1 ≤ j)
    (hreset : 4 * (rj + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j)
    (r : Nat → Nat) (hrj : r 0 = rj)
    (hsteps : ∀ m : Nat, m < L → 4 * r (m + 1) = 5 * r m + 1)
    (hdiv : 2 ^ (2 * L + 2) ∣ s0 + δ * 5 ^ (j - k - 1)) :
    r L + 1 = 5 ^ (k + 1 + L) *
      ((s0 + δ * 5 ^ (j - k - 1)) / 2 ^ (2 * L + 2)) := by
  let N := j - k - 1
  let s' := (s0 + δ * 5 ^ N) / 2 ^ (2 * L + 2)
  have hchain := t2_chain_plus_one_nat r L hsteps
  have hrj' : 4 ^ L * (r L + 1) = 5 ^ L * (rj + 1) := by
    simpa [hrj] using hchain
  have hpow4 : 4 ^ (L + 1) = 2 ^ (2 * L + 2) := by
    rw [show 4 = 2 ^ 2 by decide]
    rw [← Nat.pow_mul]
    congr 1
  have hresmul : 4 ^ (L + 1) * (r L + 1) =
      5 ^ (k + 1 + L) * (s0 + δ * 5 ^ N) := by
    have hleft : 4 ^ (L + 1) * (r L + 1) = 5 ^ L * (4 * (rj + 1)) := by
      calc
        4 ^ (L + 1) * (r L + 1)
        = 4 * (4 ^ L * (r L + 1)) := by
          rw [pow_succ]
          ring
        _ = 4 * (5 ^ L * (rj + 1)) := by rw [hrj']
        _ = 5 ^ L * (4 * (rj + 1)) := by ring
    rw [hleft]
    have hN' : j = k + 1 + N := by dsimp [N]; omega
    have h5a : 5 ^ L * (5 ^ (k + 1) * s0) = 5 ^ (k + 1 + L) * s0 := by
      have hpow : 5 ^ L * 5 ^ (k + 1) = 5 ^ (k + 1 + L) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      calc
        5 ^ L * (5 ^ (k + 1) * s0) = (5 ^ L * 5 ^ (k + 1)) * s0 := by ring
        _ = 5 ^ (k + 1 + L) * s0 := by rw [hpow]
    have h5b : 5 ^ L * (δ * 5 ^ j) = 5 ^ (k + 1 + L) * (δ * 5 ^ N) := by
      have h1 : 5 ^ L * 5 ^ j = 5 ^ (j + L) := by
        rw [← Nat.pow_add]
        ring
      have h2 : 5 ^ (k + 1 + L) * 5 ^ N = 5 ^ (k + 1 + L + N) := by
        rw [← Nat.pow_add]
      have hN2 : k + 1 + L + N = j + L := by dsimp [N]; omega
      calc
        5 ^ L * (δ * 5 ^ j) = δ * (5 ^ L * 5 ^ j) := by ring
        _ = δ * 5 ^ (j + L) := by rw [h1]
        _ = δ * 5 ^ (k + 1 + L + N) := by rw [← hN2]
        _ = 5 ^ (k + 1 + L) * (δ * 5 ^ N) := by
          rw [← h2]
          ring
    have h5 : 5 ^ L * (5 ^ (k + 1) * s0 + δ * 5 ^ j) =
        5 ^ (k + 1 + L) * (s0 + δ * 5 ^ N) := by
      rw [Nat.mul_add, h5a, h5b]
      ring
    rw [hreset, h5]
  have hs' : s' * 2 ^ (2 * L + 2) = s0 + δ * 5 ^ N := by
    dsimp [s']
    have h := Nat.mul_div_cancel' hdiv
    simpa [Nat.mul_comm] using h
  have hresmul' : 4 ^ (L + 1) * (r L + 1) =
      4 ^ (L + 1) * (5 ^ (k + 1 + L) * s') := by
    rw [hresmul]
    have hs'' : s0 + δ * 5 ^ N = 2 ^ (2 * L + 2) * s' := by
      simpa [Nat.mul_comm] using hs'.symm
    rw [hs'', ← hpow4]
    ring
  have hpos : 0 < 4 ^ (L + 1) := by positivity
  have hcancel := Nat.mul_left_cancel hpos hresmul'
  simpa [s', hpow4] using hcancel

/-- The `t=2` transfer is exactly the chain step of Corollary 15.2:
`s' = chainStep s0 (2L+2) δ N`. -/
theorem terminal_s_chain_step_t2
    (s0 j k δ rj : Nat) (L : Nat)
    (hjk : k + 1 ≤ j)
    (hreset : 4 * (rj + 1) = 5 ^ (k + 1) * s0 + δ * 5 ^ j)
    (r : Nat → Nat) (hrj : r 0 = rj)
    (hsteps : ∀ m : Nat, m < L → 4 * r (m + 1) = 5 * r m + 1)
    (hdiv : 2 ^ (2 * L + 2) ∣ s0 + δ * 5 ^ (j - k - 1)) :
    r L + 1 = 5 ^ (k + 1 + L) *
      chainStep s0 (2 * L + 2) δ (j - k - 1) := by
  have h := terminal_s_transfer_t2 s0 j k δ rj L hjk hreset r hrj hsteps hdiv
  unfold chainStep
  simpa using h

/-- Lemma 15.1, t=1 branch: after a `t=1` reset and `L` further exact
`t=2` steps, the new terminal odd part is
`s' = (5^(k+1)*s0 + 5^j - 2) / 2^(2L+1)`, with terminal chain length
`L`. -/
theorem terminal_s_transfer_t1
    (s0 j k rj : Nat) (L : Nat)
    (_hjk : k + 1 ≤ j)
    (hreset : 2 * (rj + 1) = 5 ^ (k + 1) * s0 + 5 ^ j - 2)
    (r : Nat → Nat) (hrj : r 0 = rj)
    (hsteps : ∀ m : Nat, m < L → 4 * r (m + 1) = 5 * r m + 1)
    (hdiv : 2 ^ (2 * L + 1) ∣ 5 ^ (k + 1) * s0 + 5 ^ j - 2) :
    r L + 1 = 5 ^ L *
      ((5 ^ (k + 1) * s0 + 5 ^ j - 2) / 2 ^ (2 * L + 1)) := by
  let s' := (5 ^ (k + 1) * s0 + 5 ^ j - 2) / 2 ^ (2 * L + 1)
  have hchain := t2_chain_plus_one_nat r L hsteps
  have hrj' : 4 ^ L * (r L + 1) = 5 ^ L * (rj + 1) := by
    simpa [hrj] using hchain
  have hpow2 : 2 * 4 ^ L = 2 ^ (2 * L + 1) := by
    have h4 : 4 ^ L = 2 ^ (2 * L) := by
      rw [show 4 = 2 ^ 2 by decide]
      rw [← Nat.pow_mul]
    rw [h4]
    rw [Nat.pow_succ]
    ring
  have hmain : 2 ^ (2 * L + 1) * (r L + 1) =
      5 ^ L * (5 ^ (k + 1) * s0 + 5 ^ j - 2) := by
    have hleft : 2 * (4 ^ L * (r L + 1)) = 5 ^ L * (2 * (rj + 1)) := by
      rw [hrj']
      ring
    have hre : 2 ^ (2 * L + 1) * (r L + 1) = 2 * (4 ^ L * (r L + 1)) := by
      rw [← hpow2]
      ring
    rw [hre, hleft, hreset]
  have hs' : s' * 2 ^ (2 * L + 1) = 5 ^ (k + 1) * s0 + 5 ^ j - 2 := by
    dsimp [s']
    have h := Nat.mul_div_cancel' hdiv
    simpa [Nat.mul_comm] using h
  have hmain' : 2 ^ (2 * L + 1) * (r L + 1) =
      2 ^ (2 * L + 1) * (5 ^ L * s') := by
    rw [hmain]
    have hs'' : 5 ^ (k + 1) * s0 + 5 ^ j - 2 = 2 ^ (2 * L + 1) * s' := by
      simpa [Nat.mul_comm] using hs'.symm
    rw [hs'']
    ring
  have hpos : 0 < 2 ^ (2 * L + 1) := by positivity
  have hcancel := Nat.mul_left_cancel hpos hmain'
  simpa [s'] using hcancel

/-- If `2*rj = 5*x+1` with `rj` odd, then `x ≡ 1 (mod 4)`. -/
lemma prev_mod_four_of_odd (rj x : Nat)
    (hrjodd : IsOdd rj)
    (hprev : 2 * rj = 5 * x + 1) :
    x % 4 = 1 := by
  have hrjodd' : rj % 2 = 1 := by simpa [IsOdd] using hrjodd
  have hmod_eq : (2 * rj) % 4 = (5 * x + 1) % 4 := by rw [hprev]
  have h2mod : (2 * rj) % 4 = 2 := by
    have hmodrel : rj % 2 = (rj % 4) % 2 := by
      have hdec : rj = 4 * (rj / 4) + rj % 4 := (Nat.div_add_mod rj 4).symm
      rw [hdec, Nat.add_mod, Nat.mul_mod]
      norm_num
    have hcases : rj % 4 = 0 ∨ rj % 4 = 1 ∨ rj % 4 = 2 ∨ rj % 4 = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · exfalso
      rw [hmodrel, h0] at hrjodd'
      norm_num at hrjodd'
    · norm_num [Nat.mul_mod, h1]
    · exfalso
      rw [hmodrel, h2] at hrjodd'
      norm_num at hrjodd'
    · norm_num [Nat.mul_mod, h3]
  have h5mod : (5 * x + 1) % 4 = (x + 1) % 4 := by
    have hx : 5 * x + 1 = (x + 1) + 4 * x := by ring
    rw [hx]
    simp [Nat.mul_comm, Nat.add_mul_mod_self_right]
  have hsum : (x + 1) % 4 = 2 := by
    rw [← h5mod]
    rw [← hmod_eq]
    exact h2mod
  have hxsum : (x + 1) % 4 = (x % 4 + 1) % 4 := by
    rw [Nat.add_mod]
  rw [hxsum] at hsum
  have hlt : x % 4 < 4 := Nat.mod_lt x (by decide)
  omega

/--
Counterexample / missing premise (not a provable true card): the pure t=2
M=1 base-case exclusion.

Exact predicate: for `N s0 U δ`, if `1≤N`, `0<s0`, `s0<5^N`,
`IsOdd s0`, `¬5∣s0`, `4≤U`, `δ=1∨δ=3`,
`∃L, U=2L+2 ∧ 1≤L`, `IsGloballyReachable s0 N δ`, then
`¬ OddHit (leastResidue (s0 * pow2Inv U N) (5^N)) N U δ`.
Ticket 9 completed the predicate as "previous terminal reachable +
reset step legal + block head reachable"; ticket 9a replaced the reset
block head with the exact equation of 36.27/15.1, filtering the old
witnesses `(59,5,4,1)` etc. because their block heads are not in the
25-state orbit. Ticket 10 added `U=2L+2` and let `δ` serve as both the
reset and chain parameter. The statement is closed under the exhaustion
layer of ticket 14, and `pure_t2_m1_no_odd_hit` compiles without `sorry`.
-/
theorem pure_t2_m1_no_odd_hit
    (N s0 U δ : Nat)
    (_hN : 1 ≤ N)
    (hS0 : 0 < s0 ∧ s0 < 5 ^ N ∧ IsOdd s0 ∧ ¬ 5 ∣ s0)
    (hU : 4 ≤ U)
    (hUeven : ∃ L, U = 2 * L + 2 ∧ 1 ≤ L)
    (hδ : δ = 1 ∨ δ = 3)
    (hReach : IsGloballyReachable s0 N δ) :
    ¬ OddHit
        (leastResidue (s0 * pow2Inv U N) (5 ^ N))
        N U δ := by
  intro hHit
  rcases hS0 with ⟨hS0pos, hS0lt, hS0odd, hS0nd5⟩
  let t0 := leastResidue (s0 * pow2Inv U N) (5 ^ N)
  have hcong : t0 * 2 ^ U ≡ s0 [MOD 5 ^ N] := by
    dsimp [t0]
    exact t0_congruence N U s0
  have hred := oddHit_reduces N U δ s0 t0 hδ hS0lt hcong hHit
  have h4s : 4 * s0 < 5 ^ N := hred.1
  have heq : t0 * 2 ^ U = s0 + δ * 5 ^ N := hred.2
  have ht0odd : IsOdd t0 := hHit.1
  rcases hReach with
    ⟨j, k, r, rj, t, hkj, hNdef, hs0eq, hS0odd2, hS0nd52, hs0lt2,
      hOrbitR, hReset, hOddRj, hOrbitRj⟩
  rcases hReset with hReset1 | hReset2
  · rcases hReset1 with ⟨ht1, hδ1, hres1⟩
    have hj : 1 ≤ j := by omega
    have hmod5 : rj % 5 = 3 := t1_reset_rj_mod_five s0 j k rj hj hres1
    have hpred := OrbitFrom7_pred_of_mod_three rj hOrbitRj hmod5
    rcases hpred with ⟨x, hOrbitX, hprev⟩
    have hxeq := t1_reset_prev_state s0 j k r rj x hj hs0eq hres1 hprev
    have hodd_rp1 : IsOdd (r + 1) := by
      rw [← hs0eq]
      have h5odd : 5 ^ k % 2 = 1 := StringFlow.Lte.five_pow_odd k
      have hmul : (s0 * 5 ^ k) % 2 = 1 := by
        rw [Nat.mul_mod, hS0odd, h5odd]
      exact hmul
    have hevenr : r % 2 = 0 := by
      have hmod : (r + 1) % 2 = (r % 2 + 1) % 2 := by rw [Nat.add_mod]
      change (r + 1) % 2 = 1 at hodd_rp1
      rw [hmod] at hodd_rp1
      have hcases : r % 2 = 0 ∨ r % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · exact h0
      · exfalso
        rw [h1] at hodd_rp1
        norm_num at hodd_rp1
    have hInr : InOrbit25 r := OrbitFrom7_mem_orbit25 r hOrbitR
    have hmod4r := orbit25_even_mod4 r hInr hevenr
    rcases hmod4r with hr136 | hrmod4
    · subst r
      have hxle : x ≤ 136708 := orbit25_le x (OrbitFrom7_mem_orbit25 x hOrbitX)
      have hxgt : 136708 < x := by
        have h5ge1 : 1 ≤ 5 ^ (j - 1) := Nat.one_le_pow (j - 1) 5 (by decide)
        omega
      omega
    · have hxmod3 : x % 4 = 3 := by
        have h5mod : 5 ^ (j - 1) % 4 = 1 := five_pow_mod_four (j - 1)
        have hsum : (r + 5 ^ (j - 1)) % 4 = (r % 4 + 5 ^ (j - 1) % 4) % 4 := by
          rw [Nat.add_mod]
        rw [hxeq, hsum, hrmod4, h5mod]
      have hxmod1 : x % 4 = 1 := prev_mod_four_of_odd rj x hOddRj hprev
      omega
  · rcases hReset2 with ⟨ht2, hδ2, hres2⟩
    have h5j : 5 ^ j = 5 ^ (k + 1) * 5 ^ N := by
      have hjk' : j = (k + 1) + N := by omega
      rw [hjk', Nat.pow_add]
    have hres2' : 4 * (rj + 1) = 5 ^ (k + 1) * (s0 + δ * 5 ^ N) := by
      rw [h5j] at hres2
      have hre : 5 ^ (k + 1) * s0 + δ * (5 ^ (k + 1) * 5 ^ N) =
          5 ^ (k + 1) * (s0 + δ * 5 ^ N) := by ring
      rwa [hre] at hres2
    have hres2'' : 4 * (rj + 1) = 5 ^ (k + 1) * t0 * 2 ^ U := by
      rw [← heq] at hres2'
      simpa [Nat.mul_assoc] using hres2'
    have hpos : 0 < rj + 1 := by omega
    have hleft : twoValuation (4 * (rj + 1)) = 2 + twoValuation (rj + 1) := by
      have h := StringFlow.Lte.twoValuation_mul_two_pow 2 (rj + 1) hpos
      simpa using h
    have hoddprod : (5 ^ (k + 1) * t0) % 2 = 1 := by
      have h5odd : 5 ^ (k + 1) % 2 = 1 := StringFlow.Lte.five_pow_odd (k + 1)
      rw [Nat.mul_mod, h5odd, ht0odd]
    have hright : twoValuation (5 ^ (k + 1) * t0 * 2 ^ U) = U := by
      have hre : 5 ^ (k + 1) * t0 * 2 ^ U = 2 ^ U * (5 ^ (k + 1) * t0) := by ring
      rw [hre]
      exact StringFlow.Lte.twoValuation_mul_two_pow_eq U (5 ^ (k + 1) * t0) hoddprod
    have hv2 : twoValuation (rj + 1) = U - 2 := by
      have hleft' : twoValuation (5 ^ (k + 1) * t0 * 2 ^ U) =
          2 + twoValuation (rj + 1) := by
        rw [hres2''] at hleft
        exact hleft
      have hh : 2 + twoValuation (rj + 1) = U := by
        rw [← hleft', hright]
      omega
    have hdvd5 : 5 ^ (k + 1) ∣ 4 * (rj + 1) := by
      refine ⟨t0 * 2 ^ U, ?_⟩
      rw [hres2'']
      ring
    have hcop : Nat.Coprime 4 (5 ^ (k + 1)) := by
      exact Nat.Coprime.pow_right (k + 1) (by decide : Nat.Coprime 4 5)
    have hdvd1 : 5 ^ (k + 1) ∣ rj + 1 := hcop.symm.dvd_of_dvd_mul_left hdvd5
    have h5dvd : 5 ∣ rj + 1 := by
      refine dvd_trans ?_ hdvd1
      use 5 ^ k
      rw [Nat.pow_succ]
      ring
    have hInrj : InOrbit25 rj := OrbitFrom7_mem_orbit25 rj hOrbitRj
    have hv2odd := orbit25_v2_odd_of_five rj hInrj hOddRj h5dvd
    rcases hUeven with ⟨L, hUeq, hL⟩
    have hv2even : twoValuation (rj + 1) % 2 = 0 := by
      rw [hv2, hUeq]
      norm_num
    have hv2odd' : twoValuation (rj + 1) % 2 = 1 := by
      simpa [IsOdd] using hv2odd
    omega

/-! ## Part 3: local lemma (u=1 half) -/

/-- The least nonnegative representative of `-a` modulo `m`. -/
def negResidue (a m : Nat) : Nat :=
  (m - a % m) % m

/-- The least nonnegative inverse of the odd number `5^s` modulo `2^m`. -/
def pow5Inv (s m : Nat) : Nat :=
  StringFlow.Word.invOdd (5 ^ s) (m - 1) % 2 ^ m

/-- Word molecule `A_n = Σ_{t=0}^{n-1} 2^(W_t)·5^(n-1-t)`. -/
def wordMolecule (weight : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ weight n + 5 * wordMolecule weight n

/-- Explicit premises for the word-weight function and the block-head scope.

`H_ge : 3 ≤ H_s` is an extra premise (not listed in document 36.20; it is
needed for `H_s-2` to make sense); `r_j_lt` encodes the block-head state
bound `0 ≤ r_j < 5^j`. Correction ticket 7: `W0_def`, `j_pos`,
`weight_step` and `valid_prefix` encode full word legality; endpoint
integrality alone does not express a "legal δ=0 block". -/
structure All36_20Premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) : Prop where
  Wp_def : Wp = weight (j - 1)
  Wj_def : Wj = weight j
  Ws_def : W_s = weight s
  tj_mem : Wj = Wp + 1 ∨ Wj = Wp + 2
  Aj_mol : Aj = wordMolecule weight j
  Aj_lt : Aj < 5 ^ j
  q_ge : 2 ^ Wp ≤ q
  q_lt : q < 2 ^ Wj
  q0_def : q = negResidue (A_s * pow5Inv s W_s) (2 ^ W_s)
  r_s_eq : r_s = (A_s + 5 ^ s * q) / 2 ^ W_s
  r_s_int : (A_s + 5 ^ s * q) % 2 ^ W_s = 0
  r_s_lt : r_s < 5 ^ s
  r_s_mod8 : r_s % 8 = 5
  L_val : L + 4 = twoValuation (3 * r_s + 1)
  H_def : H_s = 2 * s + 13 - 2 * (W_s - Wp)
  H_ge : 3 ≤ H_s
  A_s_mol : A_s = wordMolecule weight s
  A_s_lt : A_s < 5 ^ s
  r_j_int : (Aj + 5 ^ j * q) % 2 ^ Wj = 0
  r_j_lt : (Aj + 5 ^ j * q) / 2 ^ Wj < 5 ^ j
  Wj_le_Ws : Wj ≤ W_s
  j_le_s : j ≤ s
  W0_def : weight 0 = 0
  j_pos : 1 ≤ j
  weight_step : ∀ k : Nat, k < s → weight (k + 1) = weight k + 1 ∨
    weight (k + 1) = weight k + 2
  valid_prefix : ∀ k : Nat, k ≤ s →
    (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0

/-- The least nonnegative representative of
`u = ⟨-5^(-(L+3))⟩_{2^(H_s-1)}`. -/
def uResidue (L H : Nat) : Nat :=
  negResidue (StringFlow.Word.invOdd (5 ^ (L + 3)) (H - 1)) (2 ^ H)

/-- `uResidue` is the least nonnegative residue, strictly below the modulus. -/
lemma uResidue_lt_pow (L H : Nat) : uResidue L H < 2 ^ H := by
  unfold uResidue negResidue
  exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))

/-- `(B2)` implies `(B3)`: use `uResidue 0 (H-1) < 2^(H-1)` and merge
the exponents. -/
lemma b2_imp_b3 (s n Δ H : Nat) (hH : 1 ≤ H)
    (h : 3 * 5 ^ s + (3 * 5 ^ n - 2 * 4 ^ n) ≤
      2 ^ (Δ + 4) * uResidue 0 (H - 1)) :
    3 * 5 ^ s + (3 * 5 ^ n - 2 * 4 ^ n) ≤ 2 ^ (Δ + H + 3) := by
  have hu := uResidue_lt_pow 0 (H - 1)
  have hmul : 2 ^ (Δ + 4) * uResidue 0 (H - 1) ≤
      2 ^ (Δ + 4) * 2 ^ (H - 1) :=
    Nat.mul_le_mul_left (2 ^ (Δ + 4)) (le_of_lt hu)
  have hpow : 2 ^ (Δ + 4) * 2 ^ (H - 1) = 2 ^ (Δ + H + 3) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  exact le_trans h (le_trans hmul (by rw [hpow]))

/-- `B = Σ_{u=0}^{n-1} 2^(W_{j+u}-W_j)·5^(n-1-u)`. -/
def blockB (weight : Nat → Nat) (j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (weight (j + n) - weight j) + 5 * blockB weight j n

/-- If each step weight is at most 2, then the weight difference from `j`
to `j+n` is at most `2n`. -/
lemma weight_diff_le_two_mul (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    weight (j + n) - weight j ≤ 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep' : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hih := ih hstep'
      have hstepn : weight (j + n + 1) = weight (j + n) + 1 ∨
          weight (j + n + 1) = weight (j + n) + 2 := by
        have := hstep (j + n) (by omega)
        simpa [Nat.add_assoc] using this
      have hle : weight (j + n + 1) - weight j ≤ (weight (j + n) - weight j) + 2 := by
        rcases hstepn with h1 | h2 <;> omega
      have hle' : weight (j + (n + 1)) - weight j ≤
          (weight (j + n) - weight j) + 2 := by
        simpa [Nat.add_assoc] using hle
      have hgoal : weight (j + (n + 1)) - weight j ≤ 2 * (n + 1) := by
        omega
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgoal

/-- If each step weight is at least 1, then `n ≤ weight n`. -/
lemma weight_ge (weight : Nat → Nat) (n : Nat)
    (h0 : weight 0 = 0)
    (hstep : ∀ k, k < n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    n ≤ weight n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
      have hstep' : ∀ k, k < n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hprev : n ≤ weight n := ih hstep'
      have hnext : weight n + 1 ≤ weight (n + 1) := by
        rcases hstep n (by omega) with h1 | h2 <;> omega
      omega

/-- Under legal word steps, `B_n ≤ 5^n - 4^n`. -/
lemma blockB_le (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    blockB weight j n ≤ 5 ^ n - 4 ^ n := by
  induction n with
  | zero => simp [blockB]
  | succ n ih =>
      have hstep' : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hih := ih hstep'
      have hdiff := weight_diff_le_two_mul weight j n hstep'
      have h2 : 2 ^ (weight (j + n) - weight j) ≤ 4 ^ n := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hdiff
        have h4 : 4 ^ n = 2 ^ (2 * n) := by
          rw [show 4 = 2 ^ 2 by norm_num]
          rw [← Nat.pow_mul]
        rw [h4]
        exact hpow
      simp [blockB]
      have h5 : 5 ^ (n + 1) = 5 * 5 ^ n := by
        rw [show n + 1 = Nat.succ n by omega]
        rw [Nat.pow_succ]
        ring
      have h4' : 4 ^ (n + 1) = 4 * 4 ^ n := by
        rw [show n + 1 = Nat.succ n by omega]
        rw [Nat.pow_succ]
        ring
      rw [h5, h4']
      have h5mul : 5 * blockB weight j n ≤ 5 * (5 ^ n - 4 ^ n) :=
        Nat.mul_le_mul_left 5 hih
      have hsum : 2 ^ (weight (j + n) - weight j) + 5 * blockB weight j n ≤
          4 ^ n + 5 * (5 ^ n - 4 ^ n) :=
        Nat.add_le_add h2 h5mul
      have htail : 4 ^ n + 5 * (5 ^ n - 4 ^ n) ≤ 5 * 5 ^ n - 4 * 4 ^ n := by
        rw [Nat.mul_sub_left_distrib]
        have hle45 : 4 * 4 ^ n ≤ 5 * 4 ^ n :=
          Nat.mul_le_mul_right (4 ^ n) (by decide : 4 ≤ 5)
        have h45 : 4 ^ n ≤ 5 ^ n :=
          Nat.pow_le_pow_left (by decide : 4 ≤ 5) n
        omega
      exact le_trans hsum htail

/-- Under legal word steps, `3B + 2^Δ ≤ 3·5^n - 2·4^n`, i.e. (B1)
of document 36.26.1. -/
lemma three_blockB_add_two_pow_le (weight : Nat → Nat) (j n Δ : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2)
    (hΔ : Δ ≤ 2 * n) :
    3 * blockB weight j n + 2 ^ Δ ≤ 3 * 5 ^ n - 2 * 4 ^ n := by
  have hB := blockB_le weight j n hstep
  have h2Δ : 2 ^ Δ ≤ 4 ^ n := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hΔ
    have h4 : 4 ^ n = 2 ^ (2 * n) := by
      rw [show 4 = 2 ^ 2 by norm_num]
      rw [← Nat.pow_mul]
    rw [h4]
    exact hpow
  have h3 : 3 * blockB weight j n ≤ 3 * (5 ^ n - 4 ^ n) :=
    Nat.mul_le_mul_left 3 hB
  have hsum : 3 * blockB weight j n + 2 ^ Δ ≤ 3 * (5 ^ n - 4 ^ n) + 4 ^ n :=
    Nat.add_le_add h3 h2Δ
  have htail : 3 * (5 ^ n - 4 ^ n) + 4 ^ n ≤ 3 * 5 ^ n - 2 * 4 ^ n := by
    rw [Nat.mul_sub_left_distrib]
    have h45 : 4 ^ n ≤ 5 ^ n := Nat.pow_le_pow_left (by decide : 4 ≤ 5) n
    have hle23 : 2 * 4 ^ n ≤ 3 * 4 ^ n :=
      Nat.mul_le_mul_right (4 ^ n) (by decide : 2 ≤ 3)
    omega
  exact le_trans hsum htail

/-- Derive (B1) from the 36.20 premises:
`3B + 2^Δ ≤ 3·5^n - 2·4^n`. -/
theorem blockB_bound_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight) :
    3 * blockB weight j (s - j) + 2 ^ (W_s - Wj) ≤
      3 * 5 ^ (s - j) - 2 * 4 ^ (s - j) := by
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hdiff : W_s - Wj ≤ 2 * (s - j) := by
    have hd := weight_diff_le_two_mul weight j (s - j) hstep
    simpa [hsum, hPrem.Ws_def, hPrem.Wj_def] using hd
  exact three_blockB_add_two_pow_le weight j (s - j) (W_s - Wj) hstep hdiff

/-- The accelerated state at depth `k` of the block with parameter `q`. -/
def blockState (weight : Nat → Nat) (q k : Nat) : Nat :=
  (wordMolecule weight k + 5 ^ k * q) / 2 ^ weight k

/-- One legal block step advances `blockState` by `t`. -/
lemma blockState_step (weight : Nat → Nat) (q k t : Nat)
    (hW : weight (k + 1) = weight k + t)
    (hprev : (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0)
    (hnext : (wordMolecule weight (k + 1) + 5 ^ (k + 1) * q) %
        2 ^ (weight (k + 1)) = 0) :
    (5 * blockState weight q k + 1) % 2 ^ t = 0 ∧
      (5 * blockState weight q k + 1) / 2 ^ t = blockState weight q (k + 1) := by
  let A := wordMolecule weight k
  let W := weight k
  let A' := wordMolecule weight (k + 1)
  have hA : A' = 5 * A + 2 ^ W := by
    dsimp [A, A']
    rw [wordMolecule]
    ring
  have hprev' : 2 ^ W ∣ A + 5 ^ k * q := Nat.dvd_iff_mod_eq_zero.mpr hprev
  have hnext' : 2 ^ (W + t) ∣ A' + 5 ^ (k + 1) * q := by
    rw [← hW]
    exact Nat.dvd_iff_mod_eq_zero.mpr hnext
  have hnum : 5 * blockState weight q k + 1 =
      (A' + 5 ^ (k + 1) * q) / 2 ^ W := by
    dsimp [blockState]
    let x := (A + 5 ^ k * q) / 2 ^ W
    have hdec : A + 5 ^ k * q = 2 ^ W * x := by
      dsimp [x]
      exact (Nat.mul_div_cancel' hprev').symm
    have hnum1 : 5 * x + 1 = (5 * (A + 5 ^ k * q) + 2 ^ W) / 2 ^ W := by
      rw [hdec]
      have hfac : 5 * (2 ^ W * x) + 2 ^ W = 2 ^ W * (5 * x + 1) := by ring
      rw [hfac]
      exact (Nat.mul_div_right (5 * x + 1) (m := 2 ^ W)
        (Nat.pow_pos (by decide : 0 < 2))).symm
    have h5k : 5 ^ (k + 1) = 5 * 5 ^ k := by
      rw [Nat.pow_succ]
      ring_nf
    have hnum2 : 5 * (A + 5 ^ k * q) + 2 ^ W = A' + 5 ^ (k + 1) * q := by
      rw [hA, h5k]
      ring
    rw [hnum2] at hnum1
    exact hnum1
  have hdvdW : 2 ^ W * 2 ^ t ∣ A' + 5 ^ (k + 1) * q := by
    simpa [Nat.pow_add] using hnext'
  have hdvd_t : 2 ^ t ∣ (A' + 5 ^ (k + 1) * q) / 2 ^ W := by
    rcases hdvdW with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hre : A' + 5 ^ (k + 1) * q = 2 ^ W * (2 ^ t * c) := by
      rw [hc]
      ring
    rw [hre]
    exact Nat.mul_div_right (2 ^ t * c) (m := 2 ^ W)
      (Nat.pow_pos (by decide : 0 < 2))
  constructor
  · rw [hnum]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd_t
  · rw [hnum]
    have hdivdiv : ((A' + 5 ^ (k + 1) * q) / 2 ^ W) / 2 ^ t =
        (A' + 5 ^ (k + 1) * q) / (2 ^ W * 2 ^ t) := by
      rw [Nat.div_div_eq_div_mul]
    rw [hdivdiv, ← Nat.pow_add]
    dsimp [blockState, A', W]
    rw [hW]

/-- A legal block started inside the 25-state orbit stays in the table. -/
lemma blockState_mem_orbit25 (j s : Nat) (weight : Nat → Nat) (q : Nat)
    (hjs : j ≤ s)
    (hstep : ∀ k, k < s → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2)
    (hvalid : ∀ k, k ≤ s → (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0)
    (hj : InOrbit25 (blockState weight q j)) :
    InOrbit25 (blockState weight q s) := by
  induction s with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      exact hj
  | succ s ih =>
      by_cases hjs' : j ≤ s
      · have hstep_small : ∀ k, k < s → weight (k + 1) = weight k + 1 ∨
            weight (k + 1) = weight k + 2 := by
          intro k hk
          exact hstep k (by omega)
        have hvalid_small : ∀ k, k ≤ s →
            (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
          intro k hk
          exact hvalid k (by omega)
        have hmem_s : InOrbit25 (blockState weight q s) :=
          ih hjs' hstep_small hvalid_small
        have hstep_s : weight (s + 1) = weight s + 1 ∨ weight (s + 1) = weight s + 2 :=
          hstep s (by omega)
        rcases hstep_s with h1 | h2
        · have hstep' := blockState_step weight q s 1 h1
            (hvalid s (by omega)) (hvalid (s + 1) (by omega))
          have hnext := orbit25_closed_prop (blockState weight q s) hmem_s 1
            (Or.inl rfl) hstep'.1
          rw [hstep'.2] at hnext
          exact hnext
        · have hstep' := blockState_step weight q s 2 h2
            (hvalid s (by omega)) (hvalid (s + 1) (by omega))
          have hnext := orbit25_closed_prop (blockState weight q s) hmem_s 2
            (Or.inr rfl) hstep'.1
          rw [hstep'.2] at hnext
          exact hnext
      · have hj_eq : j = s + 1 := by omega
        subst j
        exact hj

/-- The block tail `r_s` is also in the 25-state orbit. -/
theorem r_s_mem_orbit25_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r) :
    InOrbit25 r_s := by
  have hmem_j : InOrbit25 (blockState weight q j) := by
    have hbsj : blockState weight q j = (Aj + 5 ^ j * q) / 2 ^ Wj := by
      dsimp [blockState]
      rw [← hPrem.Aj_mol, ← hPrem.Wj_def]
    rw [hbsj, ← hrj]
    exact OrbitFrom7_mem_orbit25 r hReach
  have hmem_s := blockState_mem_orbit25 j s weight q hPrem.j_le_s
    hPrem.weight_step hPrem.valid_prefix hmem_j
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def]
    exact hPrem.r_s_eq.symm
  simpa [hbss] using hmem_s

/-- The suffix word of block steps from depth `j`. -/
def blockWord (weight : Nat → Nat) (j : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => blockWord weight j n ++ [weight (j + n + 1) - weight (j + n)]

/-- Every entry of a block suffix is `1` or `2`. -/
lemma blockWord_mem (weight : Nat → Nat) (j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2) :
    ∀ t ∈ blockWord weight j n, t = 1 ∨ t = 2 := by
  induction n with
  | zero => simp [blockWord]
  | succ n ih =>
      have hstep_small : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hlast : weight (j + n + 1) - weight (j + n) = 1 ∨
          weight (j + n + 1) - weight (j + n) = 2 := by
        have h := hstep (j + n) (by omega)
        rcases h with h1 | h2 <;> omega
      intro t ht
      rw [blockWord] at ht
      rw [List.mem_append] at ht
      rcases ht with ht | ht
      · exact ih hstep_small t ht
      · simp at ht
        subst t
        exact hlast

/-- A block suffix is a valid word and advances the block state. -/
lemma blockWord_valid (weight : Nat → Nat) (q j n : Nat)
    (hstep : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2)
    (hvalid : ∀ k, k ≤ j + n → (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0) :
    StringFlow.Word.wordValid (blockWord weight j n) (blockState weight q j) ∧
      StringFlow.Word.wordOrbit (blockWord weight j n) (blockState weight q j) =
        blockState weight q (j + n) := by
  induction n with
  | zero =>
      simp [blockWord, blockState, StringFlow.Word.wordValid, StringFlow.Word.wordOrbit]
  | succ n ih =>
      have hstep_small : ∀ k, k < j + n → weight (k + 1) = weight k + 1 ∨
          weight (k + 1) = weight k + 2 := by
        intro k hk
        exact hstep k (by omega)
      have hvalid_small : ∀ k, k ≤ j + n →
          (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
        intro k hk
        exact hvalid k (by omega)
      have ih' := ih hstep_small hvalid_small
      have hlast : weight (j + n + 1) - weight (j + n) = 1 ∨
          weight (j + n + 1) - weight (j + n) = 2 := by
        have h := hstep (j + n) (by omega)
        rcases h with h1 | h2 <;> omega
      rcases hlast with hlast1 | hlast2
      · have hW1 : weight (j + n + 1) = weight (j + n) + 1 := by
          have h := hstep (j + n) (by omega)
          rcases h with h1 | h2 <;> omega
        have hstep' := blockState_step weight q (j + n) 1 hW1
          (hvalid (j + n) (by omega)) (hvalid (j + n + 1) (by omega))
        have hdef : blockWord weight j (n + 1) = blockWord weight j n ++ [1] := by
          simp [blockWord, hlast1]
        have hwv : StringFlow.Word.wordValid (blockWord weight j n ++ [1])
            (blockState weight q j) := by
          rw [wordValid_append_singleton]
          constructor
          · exact ih'.1
          · rw [ih'.2]
            simpa [Nat.pow_one] using hstep'.1
        have hwo : StringFlow.Word.wordOrbit (blockWord weight j n ++ [1])
            (blockState weight q j) = blockState weight q (j + n + 1) := by
          rw [wordOrbit_append_singleton]
          rw [ih'.2]
          simpa [Nat.pow_one] using hstep'.2
        rw [hdef]
        exact ⟨hwv, hwo⟩
      · have hW2 : weight (j + n + 1) = weight (j + n) + 2 := by
          have h := hstep (j + n) (by omega)
          rcases h with h1 | h2 <;> omega
        have hstep' := blockState_step weight q (j + n) 2 hW2
          (hvalid (j + n) (by omega)) (hvalid (j + n + 1) (by omega))
        have hdef : blockWord weight j (n + 1) = blockWord weight j n ++ [2] := by
          simp [blockWord, hlast2]
        have hwv : StringFlow.Word.wordValid (blockWord weight j n ++ [2])
            (blockState weight q j) := by
          rw [wordValid_append_singleton]
          constructor
          · exact ih'.1
          · rw [ih'.2]
            simpa [Nat.pow_two] using hstep'.1
        have hwo : StringFlow.Word.wordOrbit (blockWord weight j n ++ [2])
            (blockState weight q j) = blockState weight q (j + n + 1) := by
          rw [wordOrbit_append_singleton]
          rw [ih'.2]
          simpa [Nat.pow_two] using hstep'.2
        rw [hdef]
        exact ⟨hwv, hwo⟩

/-- The full block tail `r_s` is orbit-reachable from 7. -/
theorem OrbitFrom7_r_s_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r) :
    OrbitFrom7 r_s := by
  rcases hReach with ⟨w, hokw, hvalidw, horbitw⟩
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hvalid : ∀ k, k ≤ j + (s - j) →
      (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
    intro k hk
    have hks : k ≤ s := by omega
    exact hPrem.valid_prefix k hks
  have hbw := blockWord_valid weight q j (s - j) hstep hvalid
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def, hPrem.r_s_eq]
  have hwv : StringFlow.Word.wordValid (blockWord weight j (s - j)) r := by
    rw [← hbsj]
    exact hbw.1
  have hwo : StringFlow.Word.wordOrbit (blockWord weight j (s - j)) r = r_s := by
    rw [← hbsj, ← hbss]
    have hbw2 : StringFlow.Word.wordOrbit (blockWord weight j (s - j))
        (blockState weight q j) = blockState weight q (j + (s - j)) := hbw.2
    simpa [hsum] using hbw2
  have hok_block : ∀ t ∈ blockWord weight j (s - j), t = 1 ∨ t = 2 :=
    blockWord_mem weight j (s - j) hstep
  refine ⟨w ++ blockWord weight j (s - j), ?_, ?_, ?_⟩
  · intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact hokw t ht
    · exact hok_block t ht
  · rw [wordValid_append]
    rw [horbitw]
    exact ⟨hvalidw, hwv⟩
  · rw [wordOrbit_append]
    rw [horbitw, hwo]

/-- The same block-tail reachability holds in the general orbit: if the
block head `r` is `GeneralOrbitFrom7`-reachable and 36.20 holds, then the
block tail `r_s` is also general-orbit reachable. This is the coverage
half of the post-exit block transfer; it does not by itself prove that
every block head satisfies 36.20. -/
theorem GeneralOrbitFrom7_r_s_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : GeneralOrbitFrom7 r) :
    GeneralOrbitFrom7 r_s := by
  rcases hReach with ⟨w, hvalidw, horbitw⟩
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hvalid : ∀ k, k ≤ j + (s - j) →
      (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
    intro k hk
    have hks : k ≤ s := by omega
    exact hPrem.valid_prefix k hks
  have hbw := blockWord_valid weight q j (s - j) hstep hvalid
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def, hPrem.r_s_eq]
  have hwv : StringFlow.Word.wordValid (blockWord weight j (s - j)) r := by
    rw [← hbsj]
    exact hbw.1
  have hwo : StringFlow.Word.wordOrbit (blockWord weight j (s - j)) r = r_s := by
    rw [← hbsj, ← hbss]
    have hbw2 : StringFlow.Word.wordOrbit (blockWord weight j (s - j))
        (blockState weight q j) = blockState weight q (j + (s - j)) := hbw.2
    simpa [hsum] using hbw2
  refine ⟨w ++ blockWord weight j (s - j), ?_, ?_⟩
  · rw [wordValid_append]
    rw [horbitw]
    exact ⟨hvalidw, hwv⟩
  · rw [wordOrbit_append]
    rw [horbitw, hwo]

/-- Every intermediate block state from depth `j` to depth `s` stays in
the general orbit, provided the block head is `GeneralOrbitFrom7`
reachable and the block word is legal. This is the per-state coverage
half of the post-exit block transfer. -/
lemma blockState_general_orbit_of_legal_block
    (j s : Nat) (weight : Nat → Nat) (q r : Nat)
    (hjs : j ≤ s)
    (hstep : ∀ k, k < s → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2)
    (hvalid : ∀ k, k ≤ s → (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0)
    (hrj : blockState weight q j = r)
    (hReach : GeneralOrbitFrom7 r) :
    ∀ n : Nat, n ≤ s - j → GeneralOrbitFrom7 (blockState weight q (j + n)) := by
  intro n
  induction n with
  | zero =>
      intro hn
      simpa [hrj] using hReach
  | succ n ih =>
      intro hn
      have hnle : n ≤ s - j := by omega
      have hprev : GeneralOrbitFrom7 (blockState weight q (j + n)) := ih hnle
      have hkn : j + n < s := by omega
      have hstep' := hstep (j + n) hkn
      rcases hstep' with h1 | h2
      · have hstep1 := blockState_step weight q (j + n) 1 h1
          (hvalid (j + n) (by omega)) (hvalid (j + n + 1) (by omega))
        have hnext := general_orbit_step (blockState weight q (j + n)) 1
          hstep1.1 hprev
        rw [show j + (n + 1) = (j + n) + 1 by omega]
        rw [hstep1.2] at hnext
        exact hnext
      · have hstep2 := blockState_step weight q (j + n) 2 h2
          (hvalid (j + n) (by omega)) (hvalid (j + n + 1) (by omega))
        have hnext := general_orbit_step (blockState weight q (j + n)) 2
          hstep2.1 hprev
        rw [show j + (n + 1) = (j + n) + 1 by omega]
        rw [hstep2.2] at hnext
        exact hnext

/-- Under the 36.20 premises, every block state between the block head
and the block tail is `GeneralOrbitFrom7` reachable. -/
theorem blockState_general_orbit_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : GeneralOrbitFrom7 r)
    (k : Nat) (hjk : j ≤ k) (hks : k ≤ s) :
    GeneralOrbitFrom7 (blockState weight q k) := by
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hall := blockState_general_orbit_of_legal_block j s weight q r
    hPrem.j_le_s hPrem.weight_step hPrem.valid_prefix hbsj hReach
  have hn : k - j ≤ s - j := by omega
  have hk' : j + (k - j) = k := Nat.add_sub_of_le hjk
  have hreach := hall (k - j) hn
  simpa [hk'] using hreach

/-- With `r_s=229`, the whole orbit word from `7` is forced to the unique
path `[2,1,2,1,1,2]`; its block suffix is therefore one of the seven
suffixes of that path. -/
lemma concat_word_eq_path_of_rs229
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r)
    (hrs : r_s = 229) :
    ∃ w : List Nat,
      (∀ t ∈ w, t = 1 ∨ t = 2) ∧
      w ++ blockWord weight j (s - j) = [2, 1, 2, 1, 1, 2] := by
  rcases hReach with ⟨w, hokw, hvalidw, horbitw⟩
  have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
  have hstep : ∀ k, k < j + (s - j) → weight (k + 1) = weight k + 1 ∨
      weight (k + 1) = weight k + 2 := by
    intro k hk
    have hks : k < s := by omega
    exact hPrem.weight_step k hks
  have hvalid : ∀ k, k ≤ j + (s - j) →
      (wordMolecule weight k + 5 ^ k * q) % 2 ^ weight k = 0 := by
    intro k hk
    have hks : k ≤ s := by omega
    exact hPrem.valid_prefix k hks
  have hbw := blockWord_valid weight q j (s - j) hstep hvalid
  have hbsj : blockState weight q j = r := by
    dsimp [blockState]
    rw [← hPrem.Aj_mol, ← hPrem.Wj_def, ← hrj]
  have hbss : blockState weight q s = r_s := by
    dsimp [blockState]
    rw [← hPrem.A_s_mol, ← hPrem.Ws_def, hPrem.r_s_eq]
  have hwv : StringFlow.Word.wordValid (blockWord weight j (s - j)) r := by
    rw [← hbsj]
    exact hbw.1
  have hwo : StringFlow.Word.wordOrbit (blockWord weight j (s - j)) r = r_s := by
    rw [← hbsj, ← hbss]
    have hbw2 : StringFlow.Word.wordOrbit (blockWord weight j (s - j))
        (blockState weight q j) = blockState weight q (j + (s - j)) := hbw.2
    simpa [hsum] using hbw2
  have hok_block : ∀ t ∈ blockWord weight j (s - j), t = 1 ∨ t = 2 :=
    blockWord_mem weight j (s - j) hstep
  have hok_all : ∀ t ∈ w ++ blockWord weight j (s - j), t = 1 ∨ t = 2 := by
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact hokw t ht
    · exact hok_block t ht
  have hvalid_all : StringFlow.Word.wordValid
      (w ++ blockWord weight j (s - j)) 7 := by
    rw [wordValid_append]
    rw [horbitw]
    exact ⟨hvalidw, hwv⟩
  have horbit_all : StringFlow.Word.wordOrbit
      (w ++ blockWord weight j (s - j)) 7 = 229 := by
    rw [wordOrbit_append, horbitw, hwo, hrs]
  have hunique := path229_unique (w ++ blockWord weight j (s - j))
    hok_all hvalid_all horbit_all
  exact ⟨w, hokw, hunique⟩

set_option maxRecDepth 100000 in
/-- Finite closure: among words of length at most `6`, the suffix of the
unique `7→229` path is one of the seven listed suffixes. -/
theorem suffix_of_path229_search :
    allBool (fun w =>
      allBool (fun b =>
        if decide (w ++ b = [2, 1, 2, 1, 1, 2] ∧
                   (∀ t ∈ w, t = 1 ∨ t = 2) ∧
                   (∀ t ∈ b, t = 1 ∨ t = 2))
          then decide (b ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                              [1,2,1,1,2], [2,1,2,1,1,2]])
          else true)
        (allWordsUpTo 6))
      (allWordsUpTo 6) = true := by
  decide

/-- Any suffix of the unique `7→229` path is one of seven candidates. -/
lemma suffix_of_path229 (w b : List Nat)
    (hwb : w ++ b = [2, 1, 2, 1, 1, 2])
    (hokw : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hokb : ∀ t ∈ b, t = 1 ∨ t = 2) :
    b ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2], [2,1,2,1,1,2]] := by
  have hlen : w.length + b.length = 6 := by
    rw [← List.length_append, hwb]
    norm_num
  have hwlen : w.length ≤ 6 := by omega
  have hblen : b.length ≤ 6 := by omega
  have hmemw : w ∈ allWordsUpTo 6 :=
    mem_allWordsUpTo_of_length_and_ok w 6 hwlen hokw
  have hmemb : b ∈ allWordsUpTo 6 :=
    mem_allWordsUpTo_of_length_and_ok b 6 hblen hokb
  have hsearch := suffix_of_path229_search
  have hallw := (allBool_eq_true (fun w =>
      allBool (fun b =>
        if decide (w ++ b = [2, 1, 2, 1, 1, 2] ∧
                   (∀ t ∈ w, t = 1 ∨ t = 2) ∧
                   (∀ t ∈ b, t = 1 ∨ t = 2))
          then decide (b ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                             [1,2,1,1,2], [2,1,2,1,1,2]])
          else true)
        (allWordsUpTo 6))
      (allWordsUpTo 6)).mp hsearch w hmemw
  have hallb := (allBool_eq_true (fun b =>
      if decide (w ++ b = [2, 1, 2, 1, 1, 2] ∧
                 (∀ t ∈ w, t = 1 ∨ t = 2) ∧
                 (∀ t ∈ b, t = 1 ∨ t = 2))
        then decide (b ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                           [1,2,1,1,2], [2,1,2,1,1,2]])
        else true)
      (allWordsUpTo 6)).mp hallw b hmemb
  have hcond : decide (w ++ b = [2, 1, 2, 1, 1, 2] ∧
      (∀ t ∈ w, t = 1 ∨ t = 2) ∧ (∀ t ∈ b, t = 1 ∨ t = 2)) = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hwb, hokw, hokb⟩
  rw [hcond] at hallb
  exact decide_eq_true_eq.mp hallb

/-- Total step weight of a suffix. -/
def sumSuffix : List Nat → Nat
  | [] => 0
  | t :: ts => t + sumSuffix ts

lemma sumSuffix_append (l : List Nat) (t : Nat) :
    sumSuffix (l ++ [t]) = sumSuffix l + t := by
  induction l with
  | nil => simp [sumSuffix]
  | cons a as ih => simp [sumSuffix, ih]; ring

lemma blockWord_length (weight : Nat → Nat) (j n : Nat) :
    (blockWord weight j n).length = n := by
  induction n with
  | zero => simp [blockWord]
  | succ n ih => simp [blockWord, ih]

lemma weight_mono_le (weight : Nat → Nat) (j n : Nat)
    (hmono : ∀ k, k < j + n → weight k ≤ weight (k + 1)) :
    weight j ≤ weight (j + n) := by
  revert hmono
  induction n with
  | zero => intro hmono; simp
  | succ n ih =>
      intro hmono
      have hprev : weight j ≤ weight (j + n) :=
        ih (fun k hk => hmono k (by omega))
      exact le_trans hprev (hmono (j + n) (by omega))

lemma blockWord_sum (weight : Nat → Nat) (j n : Nat)
    (hmono : ∀ k, k < j + n → weight k ≤ weight (k + 1)) :
    sumSuffix (blockWord weight j n) = weight (j + n) - weight j := by
  induction n with
  | zero => simp [blockWord, sumSuffix]
  | succ n ih =>
      have hmono' : ∀ k, k < j + n → weight k ≤ weight (k + 1) := by
        intro k hk
        exact hmono k (by omega)
      have hdef : blockWord weight j (n + 1) =
          blockWord weight j n ++ [weight (j + n + 1) - weight (j + n)] := by
        simp [blockWord]
      rw [hdef, sumSuffix_append, ih hmono']
      have hle_jn : weight j ≤ weight (j + n) := weight_mono_le weight j n hmono'
      have hle1 : weight (j + n) ≤ weight (j + n + 1) := hmono (j + n) (by omega)
      have h : j + (n + 1) = j + n + 1 := by omega
      rw [h]
      omega

/-- Termwise step differences when
`blockWord weight 2 4 = [2,1,1,2]`. -/
lemma blockWord_2112_weights (weight : Nat → Nat)
    (hblock : blockWord weight 2 4 = [2, 1, 1, 2]) :
    weight 3 - weight 2 = 2 ∧ weight 4 - weight 3 = 1 ∧
    weight 5 - weight 4 = 1 ∧ weight 6 - weight 5 = 2 := by
  have hb : blockWord weight 2 4 =
      [weight 3 - weight 2, weight 4 - weight 3,
       weight 5 - weight 4, weight 6 - weight 5] := by
    simp [blockWord]
  rw [hb] at hblock
  simp at hblock
  exact hblock

/-- Termwise step differences when
`blockWord weight 2 5 = [1,2,1,1,2]`. -/
lemma blockWord_12112_weights (weight : Nat → Nat)
    (hblock : blockWord weight 2 5 = [1, 2, 1, 1, 2]) :
    weight 3 - weight 2 = 1 ∧ weight 4 - weight 3 = 2 ∧
    weight 5 - weight 4 = 1 ∧ weight 6 - weight 5 = 1 ∧
    weight 7 - weight 6 = 2 := by
  have hb : blockWord weight 2 5 =
      [weight 3 - weight 2, weight 4 - weight 3,
       weight 5 - weight 4, weight 6 - weight 5,
       weight 7 - weight 6] := by
    simp [blockWord]
  rw [hb] at hblock
  simp at hblock
  exact hblock

/-- Termwise step differences when
`blockWord weight 2 6 = [2,1,2,1,1,2]`. -/
lemma blockWord_212112_weights (weight : Nat → Nat)
    (hblock : blockWord weight 2 6 = [2, 1, 2, 1, 1, 2]) :
    weight 3 - weight 2 = 2 ∧ weight 4 - weight 3 = 1 ∧
    weight 5 - weight 4 = 2 ∧ weight 6 - weight 5 = 1 ∧
    weight 7 - weight 6 = 1 ∧ weight 8 - weight 7 = 2 := by
  have hb : blockWord weight 2 6 =
      [weight 3 - weight 2, weight 4 - weight 3,
       weight 5 - weight 4, weight 6 - weight 5,
       weight 7 - weight 6, weight 8 - weight 7] := by
    simp [blockWord]
  rw [hb] at hblock
  simp at hblock
  exact hblock

/-- B3 holds for every non-full suffix candidate, for `sfx.length+1 ≤ s ≤ 9`
and `e∈{1,2}`. -/
theorem b3_short_suffix_search :
    allBool (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then decide (
                  3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                    2 ^ (sumSuffix sfx + (2 * s + 13 - 2 * (sumSuffix sfx + e)) + 3))
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]] = true := by
  simp [allBool, sumSuffix]
  decide

/-- Extracted B3 bound for a non-full suffix. -/
lemma b3_of_short_suffix (sfx : List Nat) (s e : Nat)
    (hsfx : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]])
    (hs : sfx.length + 1 ≤ s) (hs9 : s ≤ 9) (he : e = 1 ∨ e = 2) :
    3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (sumSuffix sfx + (2 * s + 13 - 2 * (sumSuffix sfx + e)) + 3) := by
  have hsearch := b3_short_suffix_search
  have hall1 := (allBool_eq_true (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then decide (
                  3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                    2 ^ (sumSuffix sfx + (2 * s + 13 - 2 * (sumSuffix sfx + e)) + 3))
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]]).mp hsearch sfx hsfx
  have hcond_sfx : decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2], [1,2,1,1,2]]) = true :=
    decide_eq_true_eq.mpr hsfx
  rw [hcond_sfx] at hall1
  have hsrange : s ∈ List.range 10 := by
    simp [List.mem_range]
    omega
  have hall2 := (allBool_eq_true (fun s =>
      if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
        then allBool (fun e =>
          if decide (e = 1 ∨ e = 2)
            then decide (
              3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                2 ^ (sumSuffix sfx + (2 * s + 13 - 2 * (sumSuffix sfx + e)) + 3))
            else true)
          [1, 2]
        else true)
      (List.range 10)).mp hall1 s hsrange
  have hcond_s : decide (sfx.length + 1 ≤ s ∧ s ≤ 9) = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hs, hs9⟩
  rw [hcond_s] at hall2
  have hmem_e : e ∈ [1, 2] := by
    rcases he with rfl | rfl <;> simp
  have hall3 := (allBool_eq_true (fun e =>
      if decide (e = 1 ∨ e = 2)
        then decide (
          3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
            2 ^ (sumSuffix sfx + (2 * s + 13 - 2 * (sumSuffix sfx + e)) + 3))
        else true)
      [1, 2]).mp hall2 e hmem_e
  have hcond_e : decide (e = 1 ∨ e = 2) = true := decide_eq_true_eq.mpr he
  rw [hcond_e] at hall3
  exact decide_eq_true_eq.mp hall3

set_option maxRecDepth 100000 in
/-- Combined finite closure: for every suffix candidate satisfying the
reachable block-head bounds, the q-interval bound, and `W_s ≡ 2 (mod 4)`,
at least one of B2/B3 holds. -/
theorem b2b3_suffix_qbound_search :
    allBool (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                         [1,2,1,1,2], [2,1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then allBool (fun Wp =>
                  if decide (
                      let j := s - sfx.length
                      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                      (Wp + e + sumSuffix sfx) % 4 = 2 ∧
                      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
                    then decide (
                      let Δ := sumSuffix sfx
                      let H := 2 * s + 13 - 2 * (Δ + e)
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + H + 3))
                    else true)
                  (List.range 17)
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2],
       [1,2,1,1,2], [2,1,2,1,1,2]] = true := by
  decide

/-- Extracted B2/B3 closure for a suffix candidate satisfying the block-head
reachability, q-interval, and `W_s ≡ 2 (mod 4)` conditions. -/
lemma b2b3_of_suffix_qbound (sfx : List Nat) (s e Wp : Nat)
    (hsfx : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                   [1,2,1,1,2], [2,1,2,1,1,2]])
    (hs : sfx.length + 1 ≤ s) (hs9 : s ≤ 9)
    (he : e = 1 ∨ e = 2)
    (hWp : let j := s - sfx.length; j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1))
    (hmod : (Wp + e + sumSuffix sfx) % 4 = 2)
    (hq1 : 5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx))
    (hq2 : 229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1)) :
    (let Δ := sumSuffix sfx
     let H := 2 * s + 13 - 2 * (Δ + e)
     3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
       2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
     3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
       2 ^ (Δ + H + 3)) := by
  have hsearch := b2b3_suffix_qbound_search
  have hall1 := (allBool_eq_true (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                         [1,2,1,1,2], [2,1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then allBool (fun Wp =>
                  if decide (
                      let j := s - sfx.length
                      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                      (Wp + e + sumSuffix sfx) % 4 = 2 ∧
                      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
                    then decide (
                      let Δ := sumSuffix sfx
                      let H := 2 * s + 13 - 2 * (Δ + e)
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + H + 3))
                    else true)
                  (List.range 17)
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2],
       [1,2,1,1,2], [2,1,2,1,1,2]]).mp hsearch sfx hsfx
  have hcond_sfx : decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
      [1,2,1,1,2], [2,1,2,1,1,2]]) = true := decide_eq_true_eq.mpr hsfx
  rw [hcond_sfx] at hall1
  have hsrange : s ∈ List.range 10 := by
    simp [List.mem_range]
    omega
  have hall2 := (allBool_eq_true (fun s =>
      if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
        then allBool (fun e =>
          if decide (e = 1 ∨ e = 2)
            then allBool (fun Wp =>
              if decide (
                  let j := s - sfx.length
                  j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                  (Wp + e + sumSuffix sfx) % 4 = 2 ∧
                  5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                  229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
                then decide (
                  let Δ := sumSuffix sfx
                  let H := 2 * s + 13 - 2 * (Δ + e)
                  3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                    2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
                  3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                    2 ^ (Δ + H + 3))
                else true)
              (List.range 17)
            else true)
          [1, 2]
        else true)
      (List.range 10)).mp hall1 s hsrange
  have hcond_s : decide (sfx.length + 1 ≤ s ∧ s ≤ 9) = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hs, hs9⟩
  rw [hcond_s] at hall2
  have hmem_e : e ∈ [1, 2] := by
    rcases he with rfl | rfl <;> simp
  have hall3 := (allBool_eq_true (fun e =>
      if decide (e = 1 ∨ e = 2)
        then allBool (fun Wp =>
          if decide (
              let j := s - sfx.length
              j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
              (Wp + e + sumSuffix sfx) % 4 = 2 ∧
              5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
              229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
            then decide (
              let Δ := sumSuffix sfx
              let H := 2 * s + 13 - 2 * (Δ + e)
              3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
              3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                2 ^ (Δ + H + 3))
            else true)
          (List.range 17)
        else true)
      [1, 2]).mp hall2 e hmem_e
  have hcond_e : decide (e = 1 ∨ e = 2) = true := decide_eq_true_eq.mpr he
  rw [hcond_e] at hall3
  have hWp' : s - sfx.length - 1 ≤ Wp ∧ Wp ≤ 2 * (s - sfx.length - 1) := by
    dsimp at hWp
    exact hWp
  have hmem_Wp : Wp ∈ List.range 17 := by
    simp [List.mem_range]
    rcases hWp' with ⟨hlo, hhi⟩
    have hle : Wp ≤ 16 := by
      let j := s - sfx.length
      have hj : j ≤ 9 := by omega
      have h2j : 2 * (j - 1) ≤ 16 := by omega
      omega
    omega
  have hall4 := (allBool_eq_true (fun Wp =>
      if decide (
          let j := s - sfx.length
          j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
          (Wp + e + sumSuffix sfx) % 4 = 2 ∧
          5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
          229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
        then decide (
          let Δ := sumSuffix sfx
          let H := 2 * s + 13 - 2 * (Δ + e)
          3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
            2 ^ (Δ + 4) * uResidue 0 (H - 1) ∨
          3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
            2 ^ (Δ + H + 3))
        else true)
      (List.range 17)).mp hall3 Wp hmem_Wp
  have hcond_Wp : decide (
      let j := s - sfx.length
      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
      (Wp + e + sumSuffix sfx) % 4 = 2 ∧
      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1)) = true := by
    change decide (
      s - sfx.length - 1 ≤ Wp ∧ Wp ≤ 2 * (s - sfx.length - 1) ∧
      (Wp + e + sumSuffix sfx) % 4 = 2 ∧
      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1)) = true
    apply decide_eq_true_eq.mpr
    exact ⟨hWp'.1, hWp'.2, hmod, hq1, hq2⟩
  rw [hcond_Wp] at hall4
  exact decide_eq_true_eq.mp hall4

/-- After excluding the four "B3-only" pseudo-candidates, the `q` interval
and the block-head weight bound directly give B2. This is a finite closure;
the four excluded tuples are ruled out by `bad_*_false_of_premises` using
the 5-adic integrality of `r_s=229`. -/
lemma suffix_seven_cases (sfx : List Nat)
    (h : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                [1,2,1,1,2], [2,1,2,1,1,2]]) :
    sfx = [] ∨ sfx = [2] ∨ sfx = [1,2] ∨ sfx = [1,1,2] ∨
    sfx = [2,1,1,2] ∨ sfx = [1,2,1,1,2] ∨ sfx = [2,1,2,1,1,2] := by
  simpa using h

set_option maxRecDepth 100000 in
theorem b2_suffix_qbound_nonbad_search :
    allBool (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                         [1,2,1,1,2], [2,1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then allBool (fun Wp =>
                  if decide (
                      let j := s - sfx.length
                      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
                      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
                      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
                      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2))
                    then decide (
                      let Δ := sumSuffix sfx
                      let H := 2 * s + 13 - 2 * (Δ + e)
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + 4) * uResidue 0 (H - 1))
                    else true)
                  (List.range 17)
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2],
       [1,2,1,1,2], [2,1,2,1,1,2]] = true := by
  decide

/-- After excluding the four pseudo-candidates, the true `q`-interval
tuples satisfy B2. -/
lemma b2_of_suffix_qbound_nonbad (sfx : List Nat) (s e Wp : Nat)
    (hsfx : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                   [1,2,1,1,2], [2,1,2,1,1,2]])
    (hs : sfx.length + 1 ≤ s) (hs9 : s ≤ 9)
    (he : e = 1 ∨ e = 2)
    (hWp : let j := s - sfx.length; j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1))
    (hq1 : 5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx))
    (hq2 : 229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1))
    (hbad1 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1))
    (hbad2 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2))
    (hbad3 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1))
    (hbad4 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2))
    (hbad5 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1))
    (hbad6 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2)) :
    let Δ := sumSuffix sfx
    let H := 2 * s + 13 - 2 * (Δ + e)
    3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (Δ + 4) * uResidue 0 (H - 1) := by
  have hsearch := b2_suffix_qbound_nonbad_search
  have hall1 := (allBool_eq_true (fun sfx =>
      if decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                         [1,2,1,1,2], [2,1,2,1,1,2]])
        then allBool (fun s =>
          if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
            then allBool (fun e =>
              if decide (e = 1 ∨ e = 2)
                then allBool (fun Wp =>
                  if decide (
                      let j := s - sfx.length
                      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
                      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
                      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
                      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
                      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2))
                    then decide (
                      let Δ := sumSuffix sfx
                      let H := 2 * s + 13 - 2 * (Δ + e)
                      3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                        2 ^ (Δ + 4) * uResidue 0 (H - 1))
                    else true)
                  (List.range 17)
                else true)
              [1, 2]
            else true)
          (List.range 10)
        else true)
      [[], [2], [1,2], [1,1,2], [2,1,1,2],
       [1,2,1,1,2], [2,1,2,1,1,2]]).mp hsearch sfx hsfx
  have hcond_sfx : decide (sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
      [1,2,1,1,2], [2,1,2,1,1,2]]) = true := decide_eq_true_eq.mpr hsfx
  rw [hcond_sfx] at hall1
  have hsrange : s ∈ List.range 10 := by
    simp [List.mem_range]
    omega
  have hall2 := (allBool_eq_true (fun s =>
      if decide (sfx.length + 1 ≤ s ∧ s ≤ 9)
        then allBool (fun e =>
          if decide (e = 1 ∨ e = 2)
            then allBool (fun Wp =>
              if decide (
                  let j := s - sfx.length
                  j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
                  5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
                  229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
                  ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
                  ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
                  ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
                  ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
                  ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
                  ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2))
                then decide (
                  let Δ := sumSuffix sfx
                  let H := 2 * s + 13 - 2 * (Δ + e)
                  3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                    2 ^ (Δ + 4) * uResidue 0 (H - 1))
                else true)
              (List.range 17)
            else true)
          [1, 2]
        else true)
      (List.range 10)).mp hall1 s hsrange
  have hcond_s : decide (sfx.length + 1 ≤ s ∧ s ≤ 9) = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hs, hs9⟩
  rw [hcond_s] at hall2
  have hmem_e : e ∈ [1, 2] := by
    rcases he with rfl | rfl <;> simp
  have hall3 := (allBool_eq_true (fun e =>
      if decide (e = 1 ∨ e = 2)
        then allBool (fun Wp =>
          if decide (
              let j := s - sfx.length
              j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
              5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
              229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
              ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
              ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
              ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
              ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
              ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
              ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2))
            then decide (
              let Δ := sumSuffix sfx
              let H := 2 * s + 13 - 2 * (Δ + e)
              3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
                2 ^ (Δ + 4) * uResidue 0 (H - 1))
            else true)
          (List.range 17)
        else true)
      [1, 2]).mp hall2 e hmem_e
  have hcond_e : decide (e = 1 ∨ e = 2) = true := decide_eq_true_eq.mpr he
  rw [hcond_e] at hall3
  have hWp' : s - sfx.length - 1 ≤ Wp ∧ Wp ≤ 2 * (s - sfx.length - 1) := by
    dsimp at hWp
    exact hWp
  have hmem_Wp : Wp ∈ List.range 17 := by
    simp [List.mem_range]
    rcases hWp' with ⟨hlo, hhi⟩
    have hle : Wp ≤ 16 := by
      let j := s - sfx.length
      have hj : j ≤ 9 := by omega
      have h2j : 2 * (j - 1) ≤ 16 := by omega
      omega
    omega
  have hall4 := (allBool_eq_true (fun Wp =>
      if decide (
          let j := s - sfx.length
          j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
          5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
          229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
          ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
          ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
          ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
          ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
          ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
          ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2))
        then decide (
          let Δ := sumSuffix sfx
          let H := 2 * s + 13 - 2 * (Δ + e)
          3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
            2 ^ (Δ + 4) * uResidue 0 (H - 1))
        else true)
      (List.range 17)).mp hall3 Wp hmem_Wp
  have hcond_Wp : decide (
      let j := s - sfx.length
      j - 1 ≤ Wp ∧ Wp ≤ 2 * (j - 1) ∧
      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2)) = true := by
    change decide (
      s - sfx.length - 1 ≤ Wp ∧ Wp ≤ 2 * (s - sfx.length - 1) ∧
      5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) ∧
      229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) ∧
      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) ∧
      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) ∧
      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) ∧
      ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2)) = true
    apply decide_eq_true_eq.mpr
    exact ⟨hWp'.1, hWp'.2, hq1, hq2, hbad1, hbad2, hbad3, hbad4, hbad5, hbad6⟩
  rw [hcond_Wp] at hall4
  exact decide_eq_true_eq.mp hall4

/-- The pseudo-candidate `[2,1,1,2]` (`s=6`, `Wj-Wp=2`) cannot satisfy
the integrality equation for `r_s=229`. -/
lemma bad_suffix_2112_no_div (weight : Nat → Nat) (Wp : Nat)
    (hW0 : weight 0 = 0) (hW1 : weight 1 = Wp)
    (hW2 : weight 2 = Wp + 2) (hW3 : weight 3 = Wp + 4)
    (hW4 : weight 4 = Wp + 5) (hW5 : weight 5 = Wp + 6)
    (hWp : Wp = 1 ∨ Wp = 2) :
    ¬ 5 ^ 6 ∣ 229 * 2 ^ (Wp + 8) - wordMolecule weight 6 := by
  rcases hWp with rfl | rfl
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5]
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5]

/-- The pseudo-candidate `[1,2,1,1,2]` (`s=7`, `Wj-Wp=2`) cannot satisfy
the integrality equation for `r_s=229`. -/
lemma bad_suffix_12112_no_div (weight : Nat → Nat) (Wp : Nat)
    (hW0 : weight 0 = 0) (hW1 : weight 1 = Wp)
    (hW2 : weight 2 = Wp + 2) (hW3 : weight 3 = Wp + 3)
    (hW4 : weight 4 = Wp + 5) (hW5 : weight 5 = Wp + 6)
    (hW6 : weight 6 = Wp + 7)
    (hWp : Wp = 1 ∨ Wp = 2) :
    ¬ 5 ^ 7 ∣ 229 * 2 ^ (Wp + 9) - wordMolecule weight 7 := by
  rcases hWp with rfl | rfl
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6]
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6]

/-- The full 36.20 premises rule out the pseudo-candidate `[2,1,1,2]`. -/
lemma bad_2112_false_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [2, 1, 1, 2])
    (hs : s = 6) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 4 := by
    rw [hblock]; simp
  have hsj : s - j = 4 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_2112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6⟩
  have hmono : ∀ k, k < 6 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 4 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 6 := by omega
  have hW6 : weight 6 = Wp + 8 := by omega
  have hnot := bad_suffix_2112_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 6 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 6 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 6 * q = 2 ^ W_s * ((A_s + 5 ^ 6 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 6 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 6 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 6 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 8 := by
    rw [hPrem.Ws_def]
    exact hW6
  have hA : A_s = wordMolecule weight 6 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

/-- The full 36.20 premises rule out the pseudo-candidate `[1,2,1,1,2]`. -/
lemma bad_12112_false_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [1, 2, 1, 1, 2])
    (hs : s = 7) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 5 := by
    rw [hblock]; simp
  have hsj : s - j = 5 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_12112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6, h7⟩
  have hmono : ∀ k, k < 7 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 3 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 6 := by omega
  have hW6 : weight 6 = Wp + 7 := by omega
  have hW7 : weight 7 = Wp + 9 := by omega
  have hnot := bad_suffix_12112_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hW6 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 7 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 7 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 7 * q = 2 ^ W_s * ((A_s + 5 ^ 7 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 7 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 7 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 7 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 9 := by
    rw [hPrem.Ws_def]
    exact hW7
  have hA : A_s = wordMolecule weight 7 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

/-- The pseudo-candidate `[2,1,2,1,1,2]` (`s=8`, `Wj-Wp=2`) cannot
satisfy the integrality equation for `r_s=229`. -/
lemma bad_suffix_full_no_div (weight : Nat → Nat) (Wp : Nat)
    (hW0 : weight 0 = 0) (hW1 : weight 1 = Wp)
    (hW2 : weight 2 = Wp + 2) (hW3 : weight 3 = Wp + 4)
    (hW4 : weight 4 = Wp + 5) (hW5 : weight 5 = Wp + 7)
    (hW6 : weight 6 = Wp + 8) (hW7 : weight 7 = Wp + 9)
    (hWp : Wp = 1 ∨ Wp = 2) :
    ¬ 5 ^ 8 ∣ 229 * 2 ^ (Wp + 11) - wordMolecule weight 8 := by
  rcases hWp with rfl | rfl
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6, hW7]
  · norm_num [wordMolecule, hW0, hW1, hW2, hW3, hW4, hW5, hW6, hW7]

/-- The full 36.20 premises rule out the pseudo-candidate
`[2,1,2,1,1,2]`. -/
lemma bad_full_false_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (_hReach : OrbitFrom7 r)
    (hrs : r_s = 229)
    (hblock : blockWord weight j (s - j) = [2, 1, 2, 1, 1, 2])
    (hs : s = 8) (hWp : Wp = 1 ∨ Wp = 2) (he : Wj - Wp = 2) :
    False := by
  have hlen : (blockWord weight j (s - j)).length = 6 := by
    rw [hblock]; simp
  have hsj : s - j = 6 := by
    rw [blockWord_length weight j (s - j)] at hlen
    exact hlen
  subst s
  have hj : j = 2 := by omega
  subst j
  have hW1 : weight 1 = Wp := by
    have h := hPrem.Wp_def
    simpa using h.symm
  have hW2 : weight 2 = Wp + 2 := by
    have hWj := hPrem.Wj_def
    omega
  have hw := blockWord_212112_weights weight hblock
  rcases hw with ⟨h3, h4, h5, h6, h7, h8⟩
  have hmono : ∀ k, k < 8 → weight k ≤ weight (k + 1) := by
    intro k hk
    rcases hPrem.weight_step k (by omega) with h1 | h2 <;> omega
  have hW3 : weight 3 = Wp + 4 := by omega
  have hW4 : weight 4 = Wp + 5 := by omega
  have hW5 : weight 5 = Wp + 7 := by omega
  have hW6 : weight 6 = Wp + 8 := by omega
  have hW7 : weight 7 = Wp + 9 := by omega
  have hW8 : weight 8 = Wp + 11 := by omega
  have hnot := bad_suffix_full_no_div weight Wp hPrem.W0_def hW1 hW2 hW3 hW4 hW5 hW6 hW7 hWp
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ 8 * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ 8 * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ 8 * q = 2 ^ W_s * ((A_s + 5 ^ 8 * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ 8 * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hdvd : 5 ^ 8 ∣ 229 * 2 ^ W_s - A_s := by
    have hle : A_s ≤ 229 * 2 ^ W_s := by
      have h := h229
      omega
    have heq : 229 * 2 ^ W_s - A_s = 5 ^ 8 * q := by omega
    rw [heq]
    exact ⟨q, rfl⟩
  have hWs : W_s = Wp + 11 := by
    rw [hPrem.Ws_def]
    exact hW8
  have hA : A_s = wordMolecule weight 8 := hPrem.A_s_mol
  rw [hWs, hA] at hdvd
  exact hnot hdvd

/-- Among the 25 orbit states, only `229` satisfies the block-tail
residue and valuation constraints. -/
lemma r_s_eq_229_of_orbit25 (r_s L : Nat)
    (hIn : InOrbit25 r_s) (hmod8 : r_s % 8 = 5)
    (hL : L + 4 = twoValuation (3 * r_s + 1)) :
    r_s = 229 := by
  rcases orbit25_mem_cases r_s hIn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  <;> (first | rfl | (simp at hmod8 <;> omega) |
        (simp [StringFlow.twoValuation_succ] at hL))

/-- The full premises force the block tail `r_s = 229`. -/
theorem r_s_eq_229_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r) :
    r_s = 229 := by
  exact r_s_eq_229_of_orbit25 r_s L
    (r_s_mem_orbit25_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach)
    hPrem.r_s_mod8 hPrem.L_val

/-- For `s≥10`, `2^(s+13) < 5^s`. -/
lemma five_pow_gt_two_pow_add (s : Nat) (h : 10 ≤ s) :
    2 ^ (s + 13) < 5 ^ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs : 10 ≤ s
      · have hprev : 2 ^ (s + 13) < 5 ^ s := ih hs
        have hmul : 2 * 2 ^ (s + 13) < 5 * 5 ^ s := by
          have h1 : 2 * 2 ^ (s + 13) < 2 * 5 ^ s :=
            (Nat.mul_lt_mul_left (by decide : 0 < 2)).2 hprev
          have h2 : 2 * 5 ^ s < 5 * 5 ^ s :=
            (Nat.mul_lt_mul_right (Nat.pow_pos (by decide : 0 < 5))).2 (by norm_num : 2 < 5)
          exact lt_trans h1 h2
        have h2 : 2 ^ (s + 14) = 2 * 2 ^ (s + 13) := by
          rw [show s + 14 = (s + 13) + 1 by omega, Nat.pow_succ]
          ring
        have h5 : 5 ^ (s + 1) = 5 * 5 ^ s := by
          rw [Nat.pow_succ]
          ring
        rw [h2, h5]
        exact hmul
      · have hs9 : s = 9 := by omega
        subst s
        norm_num

/-- The full premises bound the block length: `s ≤ 9`. -/
theorem s_le_9_of_premises
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r) :
    s ≤ 9 := by
  have hrs : r_s = 229 :=
    r_s_eq_229_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ s * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ s * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ s * q = 2 ^ W_s * ((A_s + 5 ^ s * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ s * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hqge : 2 ^ Wp ≤ q := hPrem.q_ge
  have hq : 5 ^ s * 2 ^ Wp ≤ 229 * 2 ^ W_s := by
    have hle : 5 ^ s * 2 ^ Wp ≤ A_s + 5 ^ s * q := by
      have h1 : 5 ^ s * 2 ^ Wp ≤ 5 ^ s * q := Nat.mul_le_mul_left (5 ^ s) hqge
      omega
    rw [← h229] at hle
    exact hle
  have hWp_le_Wj : Wp ≤ Wj := by
    rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hWj_le_Ws : Wj ≤ W_s := hPrem.Wj_le_Ws
  have hWp_le_Ws : Wp ≤ W_s := le_trans hWp_le_Wj hWj_le_Ws
  have hWs : W_s = Wp + (W_s - Wp) := by omega
  have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
    conv_lhs => rw [hWs]
    rw [Nat.pow_add]
  have hq' : 5 ^ s * 2 ^ Wp ≤ 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) := by
    rwa [hpowWs] at hq
  have hcancel : 5 ^ s ≤ 229 * 2 ^ (W_s - Wp) := by
    have hle : 5 ^ s * 2 ^ Wp ≤ (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq'
    exact Nat.le_of_mul_le_mul_right hle (Nat.pow_pos (by decide : 0 < 2))
  have hD : W_s - Wp = (W_s - Wj) + (Wj - Wp) := by omega
  have h5le : 5 ^ s ≤ 229 * 2 ^ ((W_s - Wj) + (Wj - Wp)) := by
    rw [← hD]
    exact hcancel
  let X := (W_s - Wj) + (Wj - Wp)
  have h229le : 229 * 2 ^ X ≤ 2 ^ (X + 8) := by
    have h229 : 229 ≤ 2 ^ 8 := by norm_num
    have hmul : 229 * 2 ^ X ≤ 2 ^ 8 * 2 ^ X := Nat.mul_le_mul_right (2 ^ X) h229
    have hpow : 2 ^ 8 * 2 ^ X = 2 ^ (X + 8) := by
      rw [Nat.add_comm, ← Nat.pow_add]
    rwa [hpow] at hmul
  have h5le2 : 5 ^ s ≤ 2 ^ (X + 8) := le_trans h5le h229le
  have hHs : H_s = 2 * s + 13 - 2 * (W_s - Wp) := hPrem.H_def
  have h2le : 2 * (W_s - Wp) ≤ 2 * s + 10 := by
    have hBle : 2 * (W_s - Wp) ≤ 2 * s + 13 := by
      by_contra h
      have hgt : 2 * s + 13 < 2 * (W_s - Wp) := by omega
      have hsub0 : 2 * s + 13 - 2 * (W_s - Wp) = 0 :=
        Nat.sub_eq_zero_of_le (by omega)
      have hge : 3 ≤ H_s := hPrem.H_ge
      rw [hHs, hsub0] at hge
      norm_num at hge
    have hsum : H_s + 2 * (W_s - Wp) = 2 * s + 13 := by
      rw [hHs]
      exact Nat.sub_add_cancel hBle
    have hge : 3 ≤ H_s := hPrem.H_ge
    omega
  have h2le' : W_s - Wp ≤ s + 5 := by
    have hle' : 2 * (W_s - Wp) ≤ 2 * (s + 5) := by nlinarith [h2le]
    exact Nat.le_of_mul_le_mul_left hle' (by norm_num : 0 < 2)
  have hXle : X ≤ s + 5 := by
    dsimp [X]
    rw [← hD]
    exact h2le'
  have hpowle : 2 ^ (X + 8) ≤ 2 ^ (s + 13) := by
    have hle : X + 8 ≤ s + 13 := by omega
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hle
  have h5le3 : 5 ^ s ≤ 2 ^ (s + 13) := le_trans h5le2 hpowle
  by_contra h
  have hs : 10 ≤ s := by omega
  have hgt := five_pow_gt_two_pow_add s hs
  omega

/-- CRT representative combining two residue classes. -/
def crtRep (a b n m : Nat) (h : a ≡ b [MOD Nat.gcd n m]) : Nat :=
  (Nat.chineseRemainder' h).1

theorem crtRep_left (a b n m : Nat) (h : a ≡ b [MOD Nat.gcd n m]) :
    crtRep a b n m h ≡ a [MOD n] :=
  (Nat.chineseRemainder' h).2.1

theorem crtRep_right (a b n m : Nat) (h : a ≡ b [MOD Nat.gcd n m]) :
    crtRep a b n m h ≡ b [MOD m] :=
  (Nat.chineseRemainder' h).2.2

/-- `2^K` and `5` are coprime, so the CRT compatibility condition is trivial. -/
theorem crt_coprime_2_5 (K : Nat) (a b : Nat) :
    a ≡ b [MOD Nat.gcd (2 ^ K) 5] := by
  have hcop : Nat.Coprime (2 ^ K) 5 :=
    Nat.Coprime.pow_left K (by decide : Nat.Coprime 2 5)
  simp [Nat.ModEq, hcop, Nat.mod_one]

/-- `(m - a%m)%m` is the least nonnegative representative of `-a` modulo `m`. -/
theorem negResidue_spec (a m : Nat) (hm : 0 < m) :
    (negResidue a m + a % m) % m = 0 := by
  unfold negResidue
  simpa using StringFlow.Word.wrapped_add_mod 0 (a % m) m (Nat.mod_lt a hm) hm hm

/-- If `a ≡ b (mod m)` and `b ≤ a`, then `m ∣ a-b`. -/
theorem dvd_sub_of_modEq {a b m : Nat} (h : a ≡ b [MOD m]) (_hb : b ≤ a) :
    m ∣ a - b := by
  have hmod : a % m = b % m := by simpa [Nat.ModEq] using h
  have hsub0 : (a - b) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq hmod
  exact Nat.dvd_iff_mod_eq_zero.mpr hsub0

/-- `3·5^n·(2^K2·5)` is always positive. -/
lemma three_five_pow_mul_pos (n K2 : Nat) :
    0 < 3 * 5 ^ n * (2 ^ K2 * 5) := by
  exact Nat.mul_pos
    (Nat.mul_pos (by decide : 0 < 3) (Nat.pow_pos (by decide : 0 < 5)))
    (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (by decide : 0 < 5))

/-- The Hensel inverse of an odd `a` modulo `2^K`, combined with the
multiplicative form after taking residues. -/
theorem invOdd_mod_pow_spec (a K : Nat) (ha : a % 2 = 1) (hK : 1 ≤ K) :
    (a * (StringFlow.Word.invOdd a (K - 1) % 2 ^ K)) % 2 ^ K = 1 % 2 ^ K := by
  have hspec := StringFlow.Word.invOdd_spec a ha (K - 1)
  have hspec' : (a * StringFlow.Word.invOdd a (K - 1)) % 2 ^ K = 1 := by
    simpa [Nat.sub_add_cancel hK] using hspec
  have hmod1 : 1 % 2 ^ K = 1 :=
    Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : K ≠ 0))
  rw [hmod1]
  simpa [Nat.mul_mod] using hspec'

/-- The least `t` such that `R ≤ B0 + C·t`, requiring `0 < C`. -/
def liftToNonneg (B0 R C : Nat) (hC : 0 < C) : Nat :=
  Nat.find (p := fun t => R ≤ B0 + C * t) ⟨R, by
    have hCR : R ≤ C * R := Nat.le_mul_of_pos_left R hC
    omega⟩

theorem liftToNonneg_spec (B0 R C : Nat) (hC : 0 < C) :
    R ≤ B0 + C * liftToNonneg B0 R C hC := by
  unfold liftToNonneg
  exact Nat.find_spec (p := fun t => R ≤ B0 + C * t) ⟨R, by
    have hCR : R ≤ C * R := Nat.le_mul_of_pos_left R hC
    omega⟩

/--
`r_j0`: the CRT least nonnegative solution of 36.26 (correction ticket 3).
First take the CRT least residue `r0`, then add `t·2^K2·5` so that the
full equation has `m'≥0`. Modulo `2^(Δ+L+H_s+3)` it is given by
`3·5^n·r_j0 ≡ 2^(Δ+L+4)·u - 3B - 2^Δ`, and modulo 5 by
`r_j0 ≡ 2^(-t_j)`.
-/
def rj0 (j Wp Wj _q _Aj _A_s s W_s _r_s L H_s : Nat)
    (weight : Nat → Nat) : Nat :=
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let u := uResidue L (H_s - 1)
  let inv35 := StringFlow.Word.invOdd (3 * 5 ^ n) (K2 - 1) % 2 ^ K2
  let num := (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) % 2 ^ K2
  let res2 := (num * inv35) % 2 ^ K2
  let res5 := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5
  let r0 := crtRep res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  let M := 2 ^ K2 * 5
  let C := 3 * 5 ^ n * M
  let B0 := 3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ
  let R := 2 ^ (Δ + L + 4) * u
  r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M

/-- `rj0` satisfies the mod-5 block-head congruence `r_j0 ≡ 2^(-t_j)`. -/
theorem rj0_spec_5 (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≡
      StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5 [MOD 5] := by
  unfold rj0
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let u := uResidue L (H_s - 1)
  let inv35 := StringFlow.Word.invOdd (3 * 5 ^ n) (K2 - 1) % 2 ^ K2
  let num := (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) % 2 ^ K2
  let res2 := (num * inv35) % 2 ^ K2
  let res5 := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5
  let r0 := crtRep res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  let M := 2 ^ K2 * 5
  let C := 3 * 5 ^ n * M
  let B0 := 3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ
  let R := 2 ^ (Δ + L + 4) * u
  have h := crtRep_right res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  rw [Nat.ModEq] at h ⊢
  have hM0 : M % 5 = 0 := by
    dsimp [M]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  have hmod : (r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M) % 5 =
      r0 % 5 := by
    rw [Nat.add_mod, Nat.mul_mod, hM0]
    simp
  rw [hmod]
  simpa [n, Δ, K2, B, u, inv35, num, res2, res5, r0, M, C, B0, R] using h

/-- `rj0` satisfies the congruence of 36.26 modulo `2^K2`. -/
theorem rj0_spec_2 (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) :
    3 * 5 ^ (s - j) * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
        3 * blockB weight j (s - j) + 2 ^ (W_s - Wj)
      ≡ 2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1)
      [MOD 2 ^ (W_s - Wj + L + H_s + 3)] := by
  unfold rj0
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let u := uResidue L (H_s - 1)
  let inv35 := StringFlow.Word.invOdd (3 * 5 ^ n) (K2 - 1) % 2 ^ K2
  let num := (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) % 2 ^ K2
  let res2 := (num * inv35) % 2 ^ K2
  let res5 := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5
  let r0 := crtRep res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  let M := 2 ^ K2 * 5
  let C := 3 * 5 ^ n * M
  let B0 := 3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ
  let R := 2 ^ (Δ + L + 4) * u
  have hK : 1 ≤ K2 := by dsimp [K2]; omega
  have hM2 : M % 2 ^ K2 = 0 := by
    dsimp [M]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  have hlift0 : liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M % 2 ^ K2 = 0 := by
    rw [Nat.mul_mod, hM2]
    simp
  have hres0 : r0 + liftToNonneg B0 R C (three_five_pow_mul_pos n K2) * M ≡ r0
      [MOD 2 ^ K2] := by
    rw [Nat.ModEq]
    rw [Nat.add_mod, hlift0]
    simp
  have hres : rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≡ res2 [MOD 2 ^ K2] := by
    unfold rj0
    dsimp [n, Δ, K2, B, u, inv35, num, res2, res5, r0, M, C, B0, R]
    exact hres0.trans (crtRep_left res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5))
  have hinv : 3 * 5 ^ n * inv35 ≡ 1 [MOD 2 ^ K2] := by
    have hodd : (3 * 5 ^ n) % 2 = 1 := by
      rw [Nat.mul_mod, StringFlow.Lte.five_pow_odd n]
    dsimp [inv35]
    rw [Nat.ModEq]
    exact invOdd_mod_pow_spec (3 * 5 ^ n) K2 hodd hK
  have hcancel : (3 * 5 ^ n) * ((num * inv35) % 2 ^ K2) % 2 ^ K2 =
      num % 2 ^ K2 :=
    StringFlow.Word.mul_mod_inv (3 * 5 ^ n) num inv35 (2 ^ K2) (by
      rw [Nat.ModEq] at hinv
      have hmod1 : 1 % 2 ^ K2 = 1 :=
        Nat.mod_eq_of_lt (one_lt_pow' (by decide : 1 < 2) (by omega : K2 ≠ 0))
      simpa [inv35, hmod1] using hinv)
  have hres2eq : 3 * 5 ^ n * res2 ≡ num [MOD 2 ^ K2] := by
    dsimp [res2]
    rw [Nat.ModEq]
    exact hcancel
  have hnum : num ≡ 2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2) [MOD 2 ^ K2] := by
    dsimp [num]
    exact Nat.mod_modEq (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) (2 ^ K2)
  have hstep : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≡
      2 ^ (Δ + L + 4) * u + negResidue (3 * B + 2 ^ Δ) (2 ^ K2) [MOD 2 ^ K2] :=
    hres.mul_left (3 * 5 ^ n) |>.trans hres2eq |>.trans hnum
  have hneg : negResidue (3 * B + 2 ^ Δ) (2 ^ K2) + (3 * B + 2 ^ Δ) ≡ 0
      [MOD 2 ^ K2] := by
    have hspec := negResidue_spec (3 * B + 2 ^ Δ) (2 ^ K2)
      (Nat.pow_pos (by decide : 0 < 2))
    have hmod : (3 * B + 2 ^ Δ) ≡ (3 * B + 2 ^ Δ) % 2 ^ K2 [MOD 2 ^ K2] :=
      (Nat.mod_modEq (3 * B + 2 ^ Δ) (2 ^ K2)).symm
    have hsummod : negResidue (3 * B + 2 ^ Δ) (2 ^ K2) + (3 * B + 2 ^ Δ) ≡
        negResidue (3 * B + 2 ^ Δ) (2 ^ K2) + (3 * B + 2 ^ Δ) % 2 ^ K2
        [MOD 2 ^ K2] :=
      hmod.add_left (negResidue (3 * B + 2 ^ Δ) (2 ^ K2))
    have hspec' : negResidue (3 * B + 2 ^ Δ) (2 ^ K2) +
        (3 * B + 2 ^ Δ) % 2 ^ K2 ≡ 0 [MOD 2 ^ K2] := by
      rw [Nat.ModEq]
      exact hspec
    exact hsummod.trans hspec'
  have hsum : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
      (3 * B + 2 ^ Δ) ≡ 2 ^ (Δ + L + 4) * u [MOD 2 ^ K2] := by
    have hadd := hstep.add_right (3 * B + 2 ^ Δ)
    have hzero : (2 ^ (Δ + L + 4) * u) + 0 ≡ 2 ^ (Δ + L + 4) * u [MOD 2 ^ K2] := by
      rw [Nat.ModEq]
      simp
    have hcancel' : (2 ^ (Δ + L + 4) * u + negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) +
        (3 * B + 2 ^ Δ) ≡ 2 ^ (Δ + L + 4) * u [MOD 2 ^ K2] := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (hneg.add_left (2 ^ (Δ + L + 4) * u)).trans hzero
    exact hadd.trans hcancel'
  simpa [rj0, n, Δ, K2, B, u, inv35, num, res2, res5, r0, M, C, B0, R, Nat.add_assoc] using hsum

/-- Full integer equation: `rj0` satisfies 36.26 with `m' ≥ 0`
(correction ticket 3). -/
theorem rj0_spec_eq (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) (hH : 1 ≤ H_s) :
    ∃ m' : Nat,
      3 * 5 ^ (s - j) * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
          3 * blockB weight j (s - j) + 2 ^ (W_s - Wj)
        = 2 ^ (W_s - Wj + L + 4) *
            (uResidue L (H_s - 1) + m' * 2 ^ (H_s - 1)) := by
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let u := uResidue L (H_s - 1)
  let inv35 := StringFlow.Word.invOdd (3 * 5 ^ n) (K2 - 1) % 2 ^ K2
  let num := (2 ^ (Δ + L + 4) * u +
      negResidue (3 * B + 2 ^ Δ) (2 ^ K2)) % 2 ^ K2
  let res2 := (num * inv35) % 2 ^ K2
  let res5 := StringFlow.Lte.invMod5 (2 ^ (Wj - Wp)) % 5
  let r0 := crtRep res2 res5 (2 ^ K2) 5 (crt_coprime_2_5 K2 res2 res5)
  let M := 2 ^ K2 * 5
  let C := 3 * 5 ^ n * M
  let B0 := 3 * 5 ^ n * r0 + 3 * B + 2 ^ Δ
  let R := 2 ^ (Δ + L + 4) * u
  let t := liftToNonneg B0 R C (three_five_pow_mul_pos n K2)
  let LHS := B0 + C * t
  have hLHS : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight +
      3 * B + 2 ^ Δ = LHS := by
    unfold rj0
    dsimp [n, Δ, K2, B, u, inv35, num, res2, res5, r0, M, C, B0, R, t, LHS]
    ring
  have hge : R ≤ LHS := by
    dsimp [LHS, t]
    exact liftToNonneg_spec B0 R C (three_five_pow_mul_pos n K2)
  have hcong := rj0_spec_2 j Wp Wj q Aj A_s s W_s r_s L H_s weight
  have hcong' : LHS ≡ R [MOD 2 ^ K2] := by
    simpa [n, Δ, K2, B, u, R, ← hLHS] using hcong
  have hdvd : 2 ^ K2 ∣ LHS - R := dvd_sub_of_modEq hcong' hge
  let m' := (LHS - R) / 2 ^ K2
  refine ⟨m', ?_⟩
  have hmod0 : (LHS - R) % 2 ^ K2 = 0 := by
    rcases hdvd with ⟨k, hk⟩
    rw [hk]
    rw [Nat.mul_mod, Nat.mod_self]
    simp
  have hdiv : LHS - R = m' * 2 ^ K2 := by
    dsimp [m']
    have hdm := Nat.div_add_mod (LHS - R) (2 ^ K2)
    rw [hmod0] at hdm
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdm.symm
  have hmain : LHS = R + m' * 2 ^ K2 := by
    rw [← hdiv]
    rw [Nat.add_comm]
    exact (Nat.sub_add_cancel hge).symm
  have hpow : 2 ^ K2 = 2 ^ (Δ + L + 4) * 2 ^ (H_s - 1) := by
    rw [← Nat.pow_add]
    congr 1
    dsimp [K2]
    omega
  have hrhs : R + m' * 2 ^ K2 =
      2 ^ (Δ + L + 4) * (u + m' * 2 ^ (H_s - 1)) := by
    dsimp [R]
    rw [hpow]
    ring
  rw [hLHS]
  rw [hmain]
  exact hrhs

/--
Sufficient conditions: if the inverse term is large enough when `m'=0`,
and `2^K2` is large enough when `m'≥1`, then `rj0 ≥ 5^j`. This is not a
new equivalent reduction; it scales the exact integer equation of 36.26
into two size conditions.
-/
theorem rj0_ge_of_size_bounds
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hj : j ≤ s) (hH : 1 ≤ H_s)
    (hB : 3 * blockB weight j (s - j) + 2 ^ (W_s - Wj) ≤
      3 * 5 ^ (s - j) - 2 * 4 ^ (s - j))
    (hBase : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1))
    (hPow : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + H_s + 3)) :
    5 ^ j ≤ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
  let n := s - j
  let Δ := W_s - Wj
  let K2 := Δ + L + H_s + 3
  let B := blockB weight j n
  let base := 2 ^ (Δ + L + 4) * uResidue L (H_s - 1)
  have hSpec := rj0_spec_eq j Wp Wj q Aj A_s s W_s r_s L H_s weight hH
  rcases hSpec with ⟨m', hm'⟩
  have hpowS : 5 ^ s = 5 ^ n * 5 ^ j := by
    dsimp [n]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hB' : 3 * B + 2 ^ Δ ≤ 3 * 5 ^ n - 2 * 4 ^ n := by
    dsimp [B, Δ]
    simpa [n, B, Δ] using hB
  have hBase' : 3 * 5 ^ s + (3 * 5 ^ n - 2 * 4 ^ n) ≤ base := by
    dsimp [base]
    simpa [n, Δ] using hBase
  have hPow' : 3 * 5 ^ s + (3 * 5 ^ n - 2 * 4 ^ n) ≤ 2 ^ K2 := by
    dsimp [K2]
    simpa [n, Δ] using hPow
  by_cases hm0 : m' = 0
  · subst m'
    have heq0 : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight + 3 * B + 2 ^ Δ =
        base := by
      simpa [n, Δ, B, base] using hm'
    have heq : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight + (3 * B + 2 ^ Δ) =
        base := by
      nlinarith [heq0]
    have hnum : 3 * 5 ^ s ≤
        3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
      nlinarith [hBase', hB', heq]
    have hpos : 0 < 3 * 5 ^ n := by
      exact Nat.mul_pos (by decide : 0 < 3) (Nat.pow_pos (by decide : 0 < 5))
    have hmul' : 3 * 5 ^ n * 5 ^ j ≤ 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
      nlinarith [hnum, hpowS]
    exact Nat.le_of_mul_le_mul_left hmul' hpos
  · have hm'ge : 1 ≤ m' := by omega
    have heq0 : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight + 3 * B + 2 ^ Δ =
        2 ^ (Δ + L + 4) * (uResidue L (H_s - 1) + m' * 2 ^ (H_s - 1)) := by
      simpa [n, Δ, B] using hm'
    have hpowK : 2 ^ (Δ + L + 4) * (m' * 2 ^ (H_s - 1)) = m' * 2 ^ K2 := by
      dsimp [K2]
      have hsum : (Δ + L + 4) + (H_s - 1) = Δ + L + H_s + 3 := by omega
      calc
        2 ^ (Δ + L + 4) * (m' * 2 ^ (H_s - 1))
            = m' * (2 ^ (Δ + L + 4) * 2 ^ (H_s - 1)) := by ring
        _ = m' * 2 ^ ((Δ + L + 4) + (H_s - 1)) := by rw [← Nat.pow_add]
        _ = m' * 2 ^ (Δ + L + H_s + 3) := by rw [hsum]
    have heq : 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight + (3 * B + 2 ^ Δ) =
        base + m' * 2 ^ K2 := by
      have hdist : 2 ^ (Δ + L + 4) * (uResidue L (H_s - 1) + m' * 2 ^ (H_s - 1)) =
          base + 2 ^ (Δ + L + 4) * (m' * 2 ^ (H_s - 1)) := by
        dsimp [base]
        rw [Nat.mul_add]
      nlinarith [heq0, hdist, hpowK]
    have hpow2 : 2 ^ K2 ≤ base + m' * 2 ^ K2 := by
      have hmulge : 2 ^ K2 ≤ m' * 2 ^ K2 := by
        have h1 : 1 * 2 ^ K2 ≤ m' * 2 ^ K2 := Nat.mul_le_mul_right (2 ^ K2) hm'ge
        simpa using h1
      omega
    have hnum : 3 * 5 ^ s ≤
        3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
      nlinarith [hPow', hpow2, heq]
    have hpos : 0 < 3 * 5 ^ n := by
      exact Nat.mul_pos (by decide : 0 < 3) (Nat.pow_pos (by decide : 0 < 5))
    have hmul' : 3 * 5 ^ n * 5 ^ j ≤ 3 * 5 ^ n * rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
      nlinarith [hnum, hpowS]
    exact Nat.le_of_mul_le_mul_left hmul' hpos

/--
Given that (B1) is derived from the 36.20 premises, (B2)/(B3) are two
sufficient inverse-size conditions; they do not always hold, so this is
not a full closure but a formalized path forward. This theorem contains
no new equivalent reduction.
-/
theorem local_lemma_final_of_size_conditions
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hBase2 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1))
    (hPow3 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
     2 ^ (W_s - Wj + L + H_s + 3)) :
    5 ^ j ≤ rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight := by
  have hH : 1 ≤ H_s := by
    have hge := hPrem.H_ge
    omega
  exact rj0_ge_of_size_bounds j Wp Wj q Aj A_s s W_s r_s L H_s weight
    hPrem.j_le_s hH
    (blockB_bound_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem)
    hBase2 hPow3

/--
The local lemma (u=1 half) is closed.

Exact predicate: for `j Wp Wj q Aj A_s s W_s r_s L H_s weight r`, if
`All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight` and
`r=(Aj+5^j·q)/2^(Wj)` and `OrbitFrom7 r`, then `rj0 ... ≥ 5^j`.
Proof route: `r_s=229` forces the unique path suffix; after ruling out
the six pseudo-candidates by 5-adic integrality, the `q` interval gives a
finite closure yielding B2, then `uResidue < 2^(H-1)` yields B3, and
finally `local_lemma_final_of_size_conditions` is invoked.
-/
theorem local_lemma_final
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat) (weight : Nat → Nat) (r : Nat)
    (hPrem : All36_20Premises j Wp Wj q Aj A_s s W_s r_s L H_s weight)
    (hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj)
    (hReach : OrbitFrom7 r) :
    rj0 j Wp Wj q Aj A_s s W_s r_s L H_s weight ≥ 5 ^ j := by
  let sfx := blockWord weight j (s - j)
  let e := Wj - Wp
  have hj_le_s : j ≤ s := hPrem.j_le_s
  have hrs : r_s = 229 :=
    r_s_eq_229_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  have hs9 : s ≤ 9 :=
    s_le_9_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r hPrem hrj hReach
  have hL0 : L = 0 := by
    have h := hPrem.L_val
    rw [hrs] at h
    simp [StringFlow.twoValuation_succ] at h
    omega
  rcases concat_word_eq_path_of_rs229 j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs with ⟨w, hokw, hconcat⟩
  have hsfx : sfx ∈ [[], [2], [1,2], [1,1,2], [2,1,1,2],
                     [1,2,1,1,2], [2,1,2,1,1,2]] := by
    dsimp [sfx]
    exact suffix_of_path229 w (blockWord weight j (s - j)) hconcat hokw
      (blockWord_mem weight j (s - j) (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks))
  have hs_len : sfx.length + 1 ≤ s := by
    dsimp [sfx]
    rw [blockWord_length]
    have hpos : 1 ≤ j := hPrem.j_pos
    omega
  have he : e = 1 ∨ e = 2 := by
    have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
    dsimp [e]
    rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hD : W_s - Wj = sumSuffix sfx := by
    dsimp [sfx]
    have h := blockWord_sum weight j (s - j) (by
      intro k hk
      have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
      have hks : k < s := by omega
      rcases hPrem.weight_step k hks with h1 | h2 <;> omega)
    have hsum : j + (s - j) = s := Nat.add_sub_of_le hPrem.j_le_s
    rw [hsum, ← hPrem.Ws_def, ← hPrem.Wj_def] at h
    exact h.symm
  have hn : s - j = sfx.length := by
    dsimp [sfx]
    exact (blockWord_length weight j (s - j)).symm
  have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
  have hWsWp : W_s - Wp = e + sumSuffix sfx := by
    dsimp [e]
    have hWj_le_Ws : Wj ≤ W_s := hPrem.Wj_le_Ws
    omega
  have hHdef : H_s = 2 * s + 13 - 2 * (sumSuffix sfx + e) := by
    rw [hPrem.H_def]
    rw [hWsWp]
    simp [Nat.add_comm]
  have hj_eq : s - sfx.length = j := by
    dsimp [sfx]
    rw [blockWord_length]
    omega
  have hWpB : let jj := s - sfx.length; jj - 1 ≤ Wp ∧ Wp ≤ 2 * (jj - 1) := by
    dsimp
    rw [hj_eq]
    constructor
    · rw [hPrem.Wp_def]
      have hge := weight_ge weight (j - 1) hPrem.W0_def (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks)
      exact hge
    · rw [hPrem.Wp_def]
      have hle := weight_diff_le_two_mul weight 0 (j - 1) (by
        intro k hk
        have hsum : j + (s - j) = s := Nat.add_sub_of_le hj_le_s
        have hks : k < s := by omega
        exact hPrem.weight_step k hks)
      simpa [hPrem.W0_def] using hle
  have h229 : 229 * 2 ^ W_s = A_s + 5 ^ s * q := by
    have h := hPrem.r_s_eq
    rw [hrs] at h
    have hdiv : (A_s + 5 ^ s * q) % 2 ^ W_s = 0 := hPrem.r_s_int
    have hdec : A_s + 5 ^ s * q = 2 ^ W_s * ((A_s + 5 ^ s * q) / 2 ^ W_s) :=
      (Nat.mul_div_cancel' (Nat.dvd_iff_mod_eq_zero.mpr hdiv)).symm
    rw [← h] at hdec
    have hdec' : A_s + 5 ^ s * q = 229 * 2 ^ W_s := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdec
    exact hdec'.symm
  have hq1 : 5 ^ s ≤ 229 * 2 ^ (e + sumSuffix sfx) := by
    have hqge : 2 ^ Wp ≤ q := hPrem.q_ge
    have hle : 5 ^ s * 2 ^ Wp ≤ 229 * 2 ^ W_s := by
      have h2 : 5 ^ s * 2 ^ Wp ≤ A_s + 5 ^ s * q := by
        have h1 : 5 ^ s * 2 ^ Wp ≤ 5 ^ s * q := Nat.mul_le_mul_left (5 ^ s) hqge
        omega
      rw [← h229] at h2
      exact h2
    have hWp_le_Ws : Wp ≤ W_s := by
      have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
      exact le_trans hWp_le_Wj hPrem.Wj_le_Ws
    have hWs : W_s = Wp + (W_s - Wp) := by omega
    have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
      conv_lhs => rw [hWs]
      rw [Nat.pow_add]
    have hle' : 5 ^ s * 2 ^ Wp ≤ 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) := by
      rwa [hpowWs] at hle
    have hcancel : 5 ^ s ≤ 229 * 2 ^ (W_s - Wp) := by
      have hle2 : 5 ^ s * 2 ^ Wp ≤ (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle'
      exact Nat.le_of_mul_le_mul_right hle2 (Nat.pow_pos (by decide : 0 < 2))
    rwa [hWsWp] at hcancel
  have hq2 : 229 * 2 ^ (e + sumSuffix sfx) < 5 ^ s * (2 ^ e + 1) := by
    have hqlt : q < 2 ^ Wj := hPrem.q_lt
    have hlt : 229 * 2 ^ W_s < A_s + 5 ^ s * 2 ^ Wj := by
      have h1 : 5 ^ s * q < 5 ^ s * 2 ^ Wj :=
        (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < 5))).2 hqlt
      rw [h229]
      exact Nat.add_lt_add_left h1 A_s
    have hlt2 : A_s + 5 ^ s * 2 ^ Wj < 5 ^ s * (1 + 2 ^ Wj) := by
      have hA : A_s < 5 ^ s := hPrem.A_s_lt
      have hlt' : A_s + 5 ^ s * 2 ^ Wj < 5 ^ s + 5 ^ s * 2 ^ Wj :=
        Nat.add_lt_add_right hA (5 ^ s * 2 ^ Wj)
      simpa [Nat.mul_add, Nat.mul_one] using hlt'
    have hlt3 : 229 * 2 ^ W_s < 5 ^ s * (1 + 2 ^ Wj) := lt_trans hlt hlt2
    have hWj_eq : Wj = Wp + e := by
      dsimp [e]
      rcases hPrem.tj_mem with h1 | h2 <;> omega
    have hle : 1 + 2 ^ Wj ≤ (2 ^ e + 1) * 2 ^ Wp := by
      have hpowWj : 2 ^ Wj = 2 ^ e * 2 ^ Wp := by
        rw [hWj_eq, Nat.pow_add, Nat.mul_comm]
      rw [hpowWj]
      have hWp_ge1 : 1 ≤ 2 ^ Wp := Nat.one_le_pow Wp 2 (by omega)
      nlinarith
    have hlt4 : 229 * 2 ^ W_s < 5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) :=
      lt_of_lt_of_le hlt3 (Nat.mul_le_mul_left (5 ^ s) hle)
    have hpowWs : 2 ^ W_s = 2 ^ Wp * 2 ^ (W_s - Wp) := by
      have hWs : W_s = Wp + (W_s - Wp) := by
        have hWp_le_Ws : Wp ≤ W_s := by
          have hWp_le_Wj : Wp ≤ Wj := by rcases hPrem.tj_mem with h1 | h2 <;> omega
          exact le_trans hWp_le_Wj hPrem.Wj_le_Ws
        omega
      conv_lhs => rw [hWs]
      rw [Nat.pow_add]
    have hlt5 : 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) <
        5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) := by
      simpa [hpowWs] using hlt4
    have hleft : 229 * (2 ^ Wp * 2 ^ (W_s - Wp)) =
        (229 * 2 ^ (W_s - Wp)) * 2 ^ Wp := by ring
    have hright : 5 ^ s * ((2 ^ e + 1) * 2 ^ Wp) =
        (5 ^ s * (2 ^ e + 1)) * 2 ^ Wp := by ring
    rw [hleft, hright] at hlt5
    have hlt6 : 229 * 2 ^ (W_s - Wp) < 5 ^ s * (2 ^ e + 1) := by
      exact Nat.lt_of_mul_lt_mul_right hlt5
    rwa [hWsWp] at hlt6
  have hbad1 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs6, he2, hWp1⟩
    exact bad_2112_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs6 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad2 : ¬ (sfx = [2,1,1,2] ∧ s = 6 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs6, he2, hWp2⟩
    exact bad_2112_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs6 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hbad3 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs7, he2, hWp1⟩
    exact bad_12112_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs7 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad4 : ¬ (sfx = [1,2,1,1,2] ∧ s = 7 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs7, he2, hWp2⟩
    exact bad_12112_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs7 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hbad5 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 1) := by
    intro hb
    rcases hb with ⟨hsfx, hs8, he2, hWp1⟩
    exact bad_full_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs8 (Or.inl hWp1)
      (by simpa [e] using he2)
  have hbad6 : ¬ (sfx = [2,1,2,1,1,2] ∧ s = 8 ∧ e = 2 ∧ Wp = 2) := by
    intro hb
    rcases hb with ⟨hsfx, hs8, he2, hWp2⟩
    exact bad_full_false_of_premises j Wp Wj q Aj A_s s W_s r_s L H_s weight r
      hPrem hrj hReach hrs (by simpa [sfx] using hsfx) hs8 (Or.inr hWp2)
      (by simpa [e] using he2)
  have hB2 : 3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (sumSuffix sfx + 4) *
        uResidue 0 (2 * s + 13 - 2 * (sumSuffix sfx + e) - 1) := by
    exact b2_of_suffix_qbound_nonbad sfx s e Wp hsfx hs_len hs9 he hWpB hq1 hq2
      hbad1 hbad2 hbad3 hbad4 hbad5 hbad6
  have hH1 : 1 ≤ H_s := by
    have h := hPrem.H_ge
    omega
  have hB3 : 3 * 5 ^ s + (3 * 5 ^ sfx.length - 2 * 4 ^ sfx.length) ≤
      2 ^ (sumSuffix sfx + H_s + 3) :=
    b2_imp_b3 s sfx.length (sumSuffix sfx) H_s hH1 (by
      rw [hHdef]
      exact hB2)
  have hBase2 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + 4) * uResidue L (H_s - 1) := by
    rw [hL0, hn, hD, hHdef]
    simpa [Nat.add_assoc] using hB2
  have hPow3 : 3 * 5 ^ s + (3 * 5 ^ (s - j) - 2 * 4 ^ (s - j)) ≤
      2 ^ (W_s - Wj + L + H_s + 3) := by
    rw [hL0, hn, hD]
    simpa [Nat.add_assoc] using hB3
  exact local_lemma_final_of_size_conditions j Wp Wj q Aj A_s s W_s r_s L H_s weight hPrem hBase2 hPow3

/-!
# Status table

| Theorem | Status | Description |
|---|---|---|
| `pow2Inv_correct` | proved | least nonnegative representative of the Hensel inverse |
| `pow2Inv_composition` | proved | additive composition of inverses |
| `audit_36_28_1` | proved | 5-adic pinning along the chain |
| `audit_36_28_3` | proved | failure iff `OddHit t0`; premises completed |
| `audit_36_28_5_exact` | proved | pure integer inequality `4·2^U < (4δ+1)·5^N` |
| `audit_36_28_6` | proved | reverse descent with the true predecessor parameters |
| `audit_36_28_7` | proved | descent iteration rules out every `M` |
| `IsGloballyReachable` | encoded | orbit object is `r`, with strict bounds, `k+1≤j`, `wordValid`, shared `δ`, `IsOdd rj`, exact reset block-head reachability (tickets 8, 9, 9a, 10) |
| `orbit25_closed_prop` | proved | 25-state successor closure (ticket 14) |
| `orbit25_leaf` | proved | `68354`, `136708` have no legal step |
| `wordValid_mem_orbit25` | proved | every `wordValid` path ends in the table |
| `OrbitFrom7_mem_orbit25` | proved | `OrbitFrom7` reduces to table membership |
| `allWords` / `allWordsUpTo` | defined | finite-length `{1,2}` word enumeration layer for finite uniqueness proofs |
| `path229_search_all` | proved | the legal 7→229 word of length ≤8 is unique: `[2,1,2,1,1,2]` (kernel `decide` finite closure) |
| `path229_unique_of_length_le_8` | proved | uniqueness lemma: under the length bound, every legal 7→229 word equals `[2,1,2,1,1,2]` |
| `step_gt` | proved | a legal `{1,2}` step strictly increases at `x≥7` |
| `wordOrbit_gt` | proved | a nonempty legal word strictly increases at `x≥7` |
| `wordValid_cons` / `wordOrbit_cons` | proved | cons decomposition of `wordValid`/`wordOrbit` |
| `no_word_from_dead_to_229` | proved | `18`, `58`, `458` cannot legally reach `229` |
| `no_nonempty_word_from_229` | proved | no nonempty legal word from `229` returns to `229` |
| `word_to_229_forced` | proved | paths from the six relevant orbit states to `229` are forced |
| `path229_unique` | proved | every legal 7→229 word equals `[2,1,2,1,1,2]` without a length assumption |
| `concat_word_eq_path_of_rs229` | proved | when `r_s=229`, the whole word `w++blockWord` equals the unique path |
| `suffix_of_path229_search` | proved | the unique path has only 7 suffix candidates (kernel `decide` closure) |
| `suffix_of_path229` | proved | every suffix of the unique path lies in the 7-candidate table |
| `sumSuffix` | defined | total step weight of a suffix |
| `b3_short_suffix_search` / `b3_of_short_suffix` | proved | non-full suffixes satisfy the B3 size bound for `s≤9` |
| `b2b3_suffix_qbound_search` / `b2b3_of_suffix_qbound` | proved | finite closure of B2/B3 under the `q` interval, `Wp` reachability and `W_s≡2 (mod 4)` |
| `orbit25_v2_odd_of_five` | proved | if `5∣x+1` then `v2(x+1)` is odd |
| `orbit25_le` | proved | orbit bound `136708` |
| `orbit25_even_mod4` | proved | mod 4 classification of even terminals |
| `wordValid_pred_last_one` | proved | deleting the last `t=1` step stays legal and gives the predecessor |
| `OrbitFrom7_pred_of_mod_three` | proved | if `y%5=3` then the `t=1` predecessor is still on the orbit |
| `five_pow_mod_four` | proved | `5^n ≡ 1 (mod 4)` |
| `oddHit_reduces` | proved | `OddHit` reduces to `t0·2^U=s0+δ·5^N` and `4s0<5^N` |
| `t0_congruence` | proved | `t0·2^U ≡ s0 (mod 5^N)` |
| `t1_reset_prev_state` | proved | a `t=1` reset gives `x=r+5^(j-1)` |
| `t1_reset_rj_mod_five` | proved | a `t=1` reset block head satisfies `rj≡3 (mod 5)` |
| `t2_reset_rj_plus_one_mod_five` / `t2_reset_rj_mod_five` | proved | a `t=2` reset block head satisfies `5 | rj+1`, i.e. `rj≡4 (mod 5)` |
| `reset_head_mod_five` | proved | `ResetHeadEq` fixes the block head modulo `5`: `t=1→3`, `t=2→4` |
| `reset_head_mod_ten` | proved | `ResetHeadEq` plus oddness fix the block head modulo `10`: `t=1→3`, `t=2→9` |
| `reset_head_lt_five_pow` | proved | `ResetHeadEq` plus the previous-terminal size bound gives the block-head state bound `rj < 5^j` |
| `t2_chain_plus_one_nat` | proved | Nat exact `t=2` chain closed form `4^n*(r_n+1)=5^n*(r_0+1)` |
| `terminal_s_transfer_t2` | proved | Lemma 15.1 t=2 branch: `s'=(s0+δ*5^N)/2^(2L+2)`, terminal chain length `k+1+L` |
| `terminal_s_transfer_t1` | proved | Lemma 15.1 t=1 branch: `s'=(5^(k+1)*s0+5^j-2)/2^(2L+1)`, terminal chain length `L` |
| `terminal_s_chain_step_t2` | proved | `t=2` transfer equals `chainStep s0 (2L+2) δ N` (Corollary 15.2 bridge) |
| `chainSum` / `chain_closed_form` | proved | Corollary 15.3 cleared form: `s_M·2^(S_M)=s_0+5^N·Σδ_m·2^(S_m)` |
| `chain_all_lt_fourth` | proved | pure `t=2` chain size induction: `s_m<5^N/4` for every `m≤M` (Lemma 16.1 case 3) |
| `chain_all_pos_lt_fourth` | proved | pure `t=2` chain size premises: `0<s_m<5^N/4` for every `m≤M` |
| `chain_audit_36_28_5_all` | proved | Corollary 36.28.5 along the chain: `4·2^(U_m)<(4δ_m+1)·5^N` for every `m<M` |
| `chain_no_hit_of_base` | proved | base no-hit descends to the whole chain: `¬ChainHit 0 ⇒ ¬ChainHit M` |
| `pure_t2_chain_no_hit_of_stage1` | proved (conditional) | `Stage1PureT2M1Exclusion` closes the whole pure `t=2` chain: `¬ChainHit M` |
| `stage1_m1_no_t1_branch` | proved | a `t=1` reset head cannot occur in an odd hit: the hit equation forces `rj` even |
| `stage1_m1_reset_is_t2` | proved | under an odd hit the reset branch is `t=2` |
| `Stage1PureT2M1ExclusionT2` | defined | `t=2`-only version of the general-orbit `M=1` exclusion (open) |
| `stage1_pure_t2_m1_exclusion_of_t2` | proved (conditional) | full `Stage1PureT2M1Exclusion` reduces to `Stage1PureT2M1ExclusionT2` |
| `prev_mod_four_of_odd` | proved | if `2rj=5x+1` and `rj` is odd then `x≡1 (mod 4)` |
| `All36_20Premises` | encoded | includes `Aj`, `q0`, `H_s`, the `r_j` bound, word molecule, word-step legality and prefix integrality (ticket 7) |
| `rj0` | defined | CRT residue first, then lifted to `m'≥0` |
| `rj0_spec_2` | proved | congruence modulo `2^K2` |
| `rj0_spec_5` | proved | `r_j0 ≡ 2^(-t_j) (mod 5)` |
| `rj0_spec_eq` | proved | the full integer equation holds with `m'≥0` |
| `rj0_ge_of_size_bounds` | proved | size sufficiency: `m'=0` uses the `base` lower bound and `m'≥1` uses the `2^K2` lower bound to get `rj0≥5^j` |
| `blockB_le` | proved | under legal word steps, `B≤5^n-4^n` |
| `three_blockB_add_two_pow_le` | proved | `3B+2^Δ≤3·5^n-2·4^n` |
| `blockB_bound_of_premises` | proved | the 36.20 premises imply (B1) |
| `weight_ge` | proved | if every step weight is at least 1 then `n ≤ weight n` |
| `uResidue_lt_pow` / `b2_imp_b3` | proved | B2 implies B3 |
| `blockState` | defined | accelerated state `(A_k+5^k q)/2^(W_k)` at block depth `k` |
| `blockState_step` | proved | a legal block step advances `blockState` and preserves integrality |
| `blockState_mem_orbit25` | proved | a legal block starting in the 25-state table stays in the table |
| `r_s_mem_orbit25_of_premises` | proved | the 36.20 premises and `OrbitFrom7 r` imply `r_s∈25-state table` |
| `wordOrbit_append` | proved | word orbits split along concatenation |
| `wordValid_append` | proved | word validity splits along concatenation |
| `blockWord` | defined | block suffix word `[t_j,...,t_{s-1}]` |
| `blockWord_mem` | proved | every step of the block suffix word is `1` or `2` |
| `blockWord_valid` | proved | the block suffix word is legal and reaches `r_s` |
| `blockWord_*_weights` | proved | termwise step-difference extraction for the three pseudo-suffixes |
| `OrbitFrom7_r_s_of_premises` | proved | the 36.20 premises and `OrbitFrom7 r` imply `OrbitFrom7 r_s` |
| `GeneralOrbitFrom7_r_s_of_premises` | proved | the 36.20 premises and `GeneralOrbitFrom7 r` imply `GeneralOrbitFrom7 r_s`; stage-1 coverage half for block tails |
| `blockState_general_orbit_of_legal_block` / `blockState_general_orbit_of_premises` | proved | every intermediate block state stays `GeneralOrbitFrom7`-reachable under the 36.20 premises; per-state coverage half |
| `GeneralOrbitFrom7` | defined | phase 1: full legal block orbit (arbitrary step weights, including `t=0` and `t≥3`) |
| `orbit_from7_imp_general` | proved | `OrbitFrom7` implies the general orbit |
| `GeneralIsGloballyReachable` | defined | general-orbit analogue of `IsGloballyReachable`: previous terminal and reset head both `GeneralOrbitFrom7` |
| `Stage1PureT2M1Exclusion` | defined | exact stage-1 pure `t=2` `M=1` open statement in the general orbit (not claimed) |
| `globallyReachable_imp_general` | proved | `IsGloballyReachable` implies `GeneralIsGloballyReachable` |
| `general_orbit_step` / `general_orbit_step_t0` | proved | the general orbit is closed under legal single steps and `t=0` steps |
| `r_s_eq_229_of_orbit25` | proved | among the 25 states, only `229` satisfies `r_s%8=5` and `v2(3r_s+1)≥4` |
| `r_s_eq_229_of_premises` | proved | the full 36.20 premises and `OrbitFrom7 r` force `r_s=229` and `L=0` |
| `five_pow_gt_two_pow_add` | proved | for `s≥10`, `2^(s+13)<5^s` |
| `s_le_9_of_premises` | proved | the full premises force the block length `s≤9` |
| `b2_suffix_qbound_nonbad_search` / `b2_of_suffix_qbound_nonbad` | proved | after excluding the six pseudo-candidates, the `q`-interval tuples satisfy B2 |
| `bad_suffix_*_no_div` / `bad_*_false_of_premises` | proved | the six pseudo-candidates are excluded by the 5-adic integrality of `r_s=229` |
| `local_lemma_final_of_size_conditions` | proved | under (B1), only the two inverse-size conditions (B2)/(B3) remain |
| `uResidue` | defined | least nonnegative representative of `-5^(-(L+3))` |
| `pure_t2_m1_no_odd_hit` | **proved** | pure `t=2` `M=1` base-case exclusion closed, no `sorry` |
| `local_lemma_final` | **proved** | the 36.20 premises + `r=(Aj+5^j q)/2^Wj` + `OrbitFrom7 r` imply `rj0 ≥ 5^j`, no `sorry` |

Current `sorry` count: 0; protocol conditions 1--5 are all satisfied
(correction tickets 6--8 and 10 completed). The 25-state exhaustion and
the t=1 predecessor lemmas of ticket 14 were restored into this file and
compile; `pure_t2_m1_no_odd_hit` is closed in the same exhaustion layer.
`OrbitFrom7_r_s_of_premises` was added: under the full 36.20 word
legality and `OrbitFrom7 r`, `r_s` is reachable by a single `wordValid`
word path and therefore lies in the 25-state table.
Then `r_s_eq_229_of_premises` forces `r_s=229`, hence `L=0`, and
`s_le_9_of_premises` forces `s≤9`. The word-structure bounds (B1), (B2),
(B3) are all closed: `b2_suffix_qbound_nonbad` gives B2 after excluding
the six pseudo-candidates, `b2_imp_b3` gives B3, and the six
pseudo-candidates are excluded by `bad_*_false_of_premises` using the
5-adic integrality of `r_s=229`. `local_lemma_final` compiles without
`sorry`.
Phase 1 is underway: `GeneralOrbitFrom7` and its single-step closure
compile with zero `sorry`. This still does not prove that a block head
after a reset automatically satisfies 36.20; that coverage extension is
the next open statement.
-/

end S6Audit
