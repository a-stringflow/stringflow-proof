import Mathlib
import WordWindow

/-!
# Rising-prefix numerator bound (44.2)

For a real rising word of length `L` with exactly `U` steps of weight
`2`, the prefix numerator satisfies

    A_u <= A_max(L,U)

where `A_max` is the closed form of `ph_qb_gc_chain.md` section 44.2.
The maximum is attained by putting all `t=2` steps at the front, and
the recursive definition below is exactly that maximum:

    A_max(0,0) = 0,
    A_max(L+1,0) = 5^L + 2 * A_max(L,0),
    A_max(L+1,U+1) = 5^L + 4 * A_max(L,U).
-/

namespace StringFlow

/-- The maximal rising-prefix numerator with `L` steps, `U` of which
are `t=2`.  The recursion puts the `2`s at the front. -/
def amaxWord : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, _ + 1 => 0
  | L + 1, 0 => 5 ^ L + 2 * amaxWord L 0
  | L + 1, U + 1 => 5 ^ L + 4 * amaxWord L U

/-- Moving one `2` to the front at most doubles the maximum. -/
theorem amaxWord_mono_two (L U : Nat) :
    amaxWord L (U + 1) ≤ 2 * amaxWord L U := by
  induction L generalizing U with
  | zero =>
      cases U <;> simp [amaxWord]
  | succ L ih =>
      cases U with
      | zero =>
          simp [amaxWord]
          ring_nf
          omega
      | succ U =>
          have ih' := ih U
          have hmul : 4 * amaxWord L (U + 1) ≤ 8 * amaxWord L U := by
            nlinarith [ih']
          simp [amaxWord]
          ring_nf
          rw [show 1 + U = U + 1 by omega]
          omega

/-- Prepending a `t=1` step stays below the maximum with the same
number of `2`s. -/
theorem amaxWord_succ_one_le (L U : Nat) :
    5 ^ L + 2 * amaxWord L U ≤ amaxWord (L + 1) U := by
  cases U with
  | zero =>
      simp [amaxWord]
  | succ U =>
      have h := amaxWord_mono_two L U
      have hmul : 2 * amaxWord L (U + 1) ≤ 4 * amaxWord L U := by
        nlinarith [h]
      simp [amaxWord]
      ring_nf
      rw [show 1 + U = U + 1 by omega]
      omega

/-- The cleared three-fold form of `A_max`:
`3*A_max + 2*5^(L-U)*4^U + 2^(L+U) = 3*5^L`. -/
theorem three_mul_amaxWord_add (L U : Nat) (hU : U ≤ L) :
    3 * amaxWord L U + 2 * 5 ^ (L - U) * 4 ^ U + 2 ^ (L + U) = 3 * 5 ^ L := by
  induction L generalizing U with
  | zero =>
      have hU0 : U = 0 := by omega
      subst U
      simp [amaxWord]
  | succ L ih =>
      by_cases hU0 : U = 0
      · subst U
        have h := ih 0 (by omega)
        have hL1 : L + 1 - 0 = L + 1 := by omega
        have h4 : 4 ^ 0 = 1 := by decide
        have h' : 3 * amaxWord L 0 + 2 * 5 ^ L + 2 ^ L = 3 * 5 ^ L := by
          simpa [hL1, h4] using h
        rw [amaxWord, hL1, h4]
        simp [Nat.pow_succ, Nat.mul_comm]
        nlinarith [h']
      · have hUpos : ∃ V, U = V + 1 := by
          cases U with
          | zero => omega
          | succ V => exact ⟨V, rfl⟩
        rcases hUpos with ⟨V, rfl⟩
        have hU' : V ≤ L := by omega
        have h := ih V hU'
        have hsub : (L + 1) - (V + 1) = L - V := by omega
        have h4 : 4 ^ (V + 1) = 4 ^ V * 4 := by rw [Nat.pow_succ]
        rw [amaxWord, hsub, h4]
        rw [show L + 1 + (V + 1) = (L + V) + 2 by omega]
        rw [Nat.pow_add]
        norm_num
        simp [Nat.pow_succ, Nat.mul_comm]
        nlinarith [h]

/-- The exact `hmax` form of `A_max(L,U)`:
`A_max / 5^L = 1 - (2/3)(4/5)^U - 1/(3B)` with `B = 5^L / 2^(L+U)`. -/
theorem amaxWord_div_eq_hmax (L U : Nat) (hU : U ≤ L) :
    (amaxWord L U : Rat) / (5 ^ L : Rat) =
      1 - (2 / 3 : Rat) * ((4 / 5 : Rat) ^ U) -
        (1 : Rat) / (3 * ((5 ^ L : Rat) / (2 ^ (L + U) : Rat))) := by
  have h := three_mul_amaxWord_add L U hU
  have hRat : ((3 * amaxWord L U + 2 * 5 ^ (L - U) * 4 ^ U + 2 ^ (L + U) : Nat) : Rat) =
      ((3 * 5 ^ L : Nat) : Rat) := by
    exact_mod_cast h
  have h5 : (5 ^ L : Rat) ≠ 0 := by positivity
  have h2 : (2 ^ (L + U) : Rat) ≠ 0 := by positivity
  field_simp [h5, h2]
  have hrho : ((4 / 5 : Rat) ^ U) * (5 ^ L : Rat) =
      (5 ^ (L - U) : Rat) * (4 ^ U : Rat) := by
    have hpow : (4 / 5 : Rat) ^ U =
        ((4 ^ U : Nat) : Rat) / ((5 ^ U : Nat) : Rat) := by
      rw [div_pow]
      norm_num
    have hL : L = (L - U) + U := by omega
    calc
      (4 / 5 : Rat) ^ U * 5 ^ L
          = ((4 ^ U : Nat) : Rat) / ((5 ^ U : Nat) : Rat) * 5 ^ L := by
              rw [hpow]
      _ = (5 ^ (L - U) : Rat) * (4 ^ U : Rat) := by
              field_simp [h5]
              have hL2 : (5 ^ L : Rat) = (5 ^ (L - U + U) : Rat) :=
                congrArg (fun e => (5 : Rat) ^ e) hL
              rw [hL2]
              rw [pow_add]
              simp [Nat.cast_pow]
              ring
  have h2p : (2 ^ (L + U) : Rat) = (2 ^ L : Rat) * (2 ^ U : Rat) := by
    exact pow_add (2 : Rat) L U
  have hRat' : (3 * amaxWord L U : Rat) + (2 * 5 ^ (L - U) * 4 ^ U : Rat) +
      (2 ^ (L + U) : Rat) = (3 * 5 ^ L : Rat) := by
    exact_mod_cast h
  ring_nf
  nlinarith [hRat', hrho, h2p]

/-- A real `{1,2}` word satisfies `A_u <= A_max(L,U)`. -/
theorem wordA_le_amaxWord (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    Word.wordA w ≤ amaxWord w.length (w.filter (fun t => t = 2)).length := by
  induction w with
  | nil => simp [Word.wordA, amaxWord]
  | cons t ts ih =>
      have hok' : ∀ x ∈ ts, x = 1 ∨ x = 2 := by
        intro x hx
        exact hok x (by simp [hx])
      have ih' := ih hok'
      have ht : t = 1 ∨ t = 2 := hok t (by simp)
      rcases ht with ht1 | ht2
      · subst t
        have h := amaxWord_succ_one_le ts.length (ts.filter (fun x => x = 2)).length
        simp [Word.wordA]
        have hmul : 2 * Word.wordA ts ≤
            2 * amaxWord ts.length (ts.filter (fun x => x = 2)).length :=
          Nat.mul_le_mul_left 2 ih'
        omega
      · subst t
        simp [Word.wordA]
        have hmul : 4 * Word.wordA ts ≤
            4 * amaxWord ts.length (ts.filter (fun x => x = 2)).length :=
          Nat.mul_le_mul_left 4 ih'
        simp [amaxWord]
        omega

end StringFlow
