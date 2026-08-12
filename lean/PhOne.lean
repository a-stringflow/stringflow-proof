import Pmi
import Mathlib.Data.List.GetD

/-!
# PH-1: word contribution decomposition

This module formalizes PH-1 from `ph_qb_gc_chain.md` section 3 in the
same cleared-denominator style as `Pmi.lean`.  The analytic statement

    C_i = 2^(-M_{c_i}) * Lambda_i,

with `M_j = j*log2 5 - W_j`, is equivalent, after substituting
`2^(-M_j) = 2^(W_j)/5^j` and multiplying both sides by `5^(c_i+L_i-1)`,
to the integer identity

    sum_{k=0}^{L_i-1} 2^(W_{c_i+k}) * 5^(L_i-1-k)
      = 2^(W_{c_i}) *
        sum_{k=0}^{L_i-1} 2^(W_w(k)) * 5^(L_i-1-k),

where `W_w(k)` is the prefix weight inside the word
`w = [t_{c_i}, ..., t_{c_i+L_i-1}]`.

The two core lemmas are:

1. `prefixWeight_segment`: for `k <= L`,
   `W_{c+k} = W_c + W_w(k)` (the algebraic form of the `M` recurrence);
2. `ph1_word_decomposition`: the integer identity above.
-/

namespace StringFlow.PH

open StringFlow.PMI

/-- Prefix weight inside a finite word: `W_w(0)=0`,
`W_w(k+1)=W_w(k)+t_k`. -/
def wordPrefixWeight : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | t :: ts, k + 1 => t + wordPrefixWeight ts k

/-- The finite word cut from a global step sequence at offset `c`. -/
def wordWeights (t : Nat → Nat) (c L : Nat) : List Nat :=
  (List.range L).map (fun k => t (c + k))

/-- Numerator of the local factor `Lambda` after clearing the
`5^(L-1)` denominator. -/
def localLambda (w : List Nat) : Nat :=
  ((List.range w.length).map (fun k =>
    2 ^ wordPrefixWeight w k * 5 ^ (w.length - 1 - k))).sum

/-- Numerator of the word contribution `C` after clearing the
`5^(c+L-1)` denominator. -/
def wordContribution (t : Nat → Nat) (c L : Nat) : Nat :=
  ((List.range L).map (fun k =>
    2 ^ prefixWeight t (c + k) * 5 ^ (L - 1 - k))).sum

/-- Prefixing one global step shifts the word. -/
theorem wordWeights_succ (t : Nat → Nat) (c L : Nat) :
    wordWeights t c (L + 1) = t c :: wordWeights t (c + 1) L := by
  unfold wordWeights
  rw [range_succ_cons L]
  simp [Nat.add_left_comm, Nat.add_comm]

/-- The first `k+1` entries of a nonempty word have weight
`head + first k entries of the tail`. -/
theorem wordPrefixWeight_wordWeights_succ (t : Nat → Nat) (c L k : Nat) :
    wordPrefixWeight (wordWeights t c (L + 1)) (k + 1) =
      t c + wordPrefixWeight (wordWeights t (c + 1) L) k := by
  rw [wordWeights_succ]
  simp [wordPrefixWeight]

/-- The algebraic form of the PH-1 `M` recurrence:
`W_{c+k} = W_c + W_w(k)` for `k <= L`. -/
theorem prefixWeight_segment (t : Nat → Nat) :
    ∀ (c L k : Nat), k ≤ L →
      prefixWeight t (c + k) =
        prefixWeight t c + wordPrefixWeight (wordWeights t c L) k := by
  intro c L
  induction L generalizing c with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simp [wordWeights, wordPrefixWeight]
  | succ L ih =>
      intro k hk
      cases k with
      | zero =>
          rw [wordWeights_succ]
          simp [wordPrefixWeight]
      | succ k =>
          have hk' : k ≤ L := by omega
          have htail := ih (c + 1) k hk'
          have hsuccW :
              wordPrefixWeight (wordWeights t c (L + 1)) (k + 1) =
                t c + wordPrefixWeight (wordWeights t (c + 1) L) k := by
            exact wordPrefixWeight_wordWeights_succ t c L k
          calc
            prefixWeight t (c + (k + 1))
                = prefixWeight t ((c + 1) + k) := by
                    rw [show c + (k + 1) = (c + 1) + k by omega]
            _ = prefixWeight t (c + 1) +
                wordPrefixWeight (wordWeights t (c + 1) L) k := htail
            _ = (prefixWeight t c + t c) +
                wordPrefixWeight (wordWeights t (c + 1) L) k := by
                simp [prefixWeight]
            _ = prefixWeight t c +
                (t c + wordPrefixWeight (wordWeights t (c + 1) L) k) := by omega
            _ = prefixWeight t c +
                wordPrefixWeight (wordWeights t c (L + 1)) (k + 1) := by
                rw [hsuccW]

/-- PH-1: the word contribution decomposes as the global starting
weight times a local factor that depends only on the word's internal
step weights.  This is the cleared-denominator integer identity. -/
theorem ph1_word_decomposition (t : Nat → Nat) (c L : Nat) :
    wordContribution t c L =
      2 ^ prefixWeight t c * localLambda (wordWeights t c L) := by
  unfold wordContribution localLambda
  rw [show (wordWeights t c L).length = L by simp [wordWeights]]
  rw [← sum_map_mul_left (List.range L) (2 ^ prefixWeight t c)
      (fun k =>
        2 ^ wordPrefixWeight (wordWeights t c L) k * 5 ^ (L - 1 - k))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  have hkleq : k ≤ L := by
    exact Nat.le_of_lt (List.mem_range.mp hk)
  have hseg := prefixWeight_segment t c L k hkleq
  rw [hseg, Nat.pow_add]
  ac_rfl

/-- Two global cuts are the same word whenever their step weights
agree pointwise. -/
theorem wordWeights_eq_of_agree (t s : Nat → Nat) (c d L : Nat)
    (h : ∀ k, k < L → t (c + k) = s (d + k)) :
    wordWeights t c L = wordWeights s d L := by
  unfold wordWeights
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

/-- PH-1 independence: the local factor depends only on the word's
internal step weights, not on the global sequence, the offset, or the
period length (beyond the word itself). -/
theorem localLambda_eq_of_wordWeights_agree (t s : Nat → Nat) (c d L : Nat)
    (h : ∀ k, k < L → t (c + k) = s (d + k)) :
    localLambda (wordWeights t c L) = localLambda (wordWeights s d L) := by
  rw [wordWeights_eq_of_agree t s c d L h]

/-- PMI prefix weight of a consed entry sequence shifts by the head. -/
theorem prefixWeight_cons_getI (t : Nat) (ts : List Nat) (j : Nat) :
    StringFlow.PMI.prefixWeight (fun k => (t :: ts).getI k) (j + 1) =
      t + StringFlow.PMI.prefixWeight (fun k => ts.getI k) j := by
  induction j with
  | zero => simp [StringFlow.PMI.prefixWeight]
  | succ j ih =>
      rw [StringFlow.PMI.prefixWeight]
      rw [ih]
      rw [StringFlow.PMI.prefixWeight]
      rw [List.getI_cons_succ]
      omega

/-- Prefix weight inside a word equals the PMI prefix weight of its
entries. -/
theorem wordPrefixWeight_eq_prefixWeight_getD (w : List Nat) (j : Nat) :
    wordPrefixWeight w j = StringFlow.PMI.prefixWeight
      (fun j => w.getI j) j := by
  induction j generalizing w with
  | zero => cases w <;> simp [wordPrefixWeight, StringFlow.PMI.prefixWeight]
  | succ j ih =>
      cases w with
      | nil =>
          simp [wordPrefixWeight]
          rw [StringFlow.PMI.prefixWeight]
          simpa [Nat.add_zero, wordPrefixWeight] using (ih [])
      | cons t ts =>
          simp [wordPrefixWeight]
          rw [prefixWeight_cons_getI]
          rw [ih ts]

/-- The PH local numerator is exactly the list-form PMI numerator. -/
theorem localLambda_eq_pmi_aTotal (w : List Nat) :
    localLambda w = StringFlow.PMI.aTotal w.length
      (fun j => w.getI j) := by
  unfold localLambda StringFlow.PMI.aTotal
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  rw [wordPrefixWeight_eq_prefixWeight_getD]
  ac_rfl

end StringFlow.PH
