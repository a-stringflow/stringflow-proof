import ScratchLift
import WordWindow

namespace StringFlow.Word

/-- Explicit least nonnegative representative of
`q ≡ -N/40 * 2^{-S} (mod 5^L)`. -/
def survivorQ0 (P N L : Nat) : Nat :=
  ((5 ^ L - N % 5 ^ L) * StringFlow.Lte.invFive P L) % 5 ^ L

/-- `invFive` is correct at every exponent `L >= 1`. -/
theorem invFive_spec_at (P L : Nat) (hP : P % 5 ≠ 0) (hL : 1 ≤ L) :
    (P * StringFlow.Lte.invFive P L) % 5 ^ L = 1 := by
  cases L with
  | zero => omega
  | succ L' =>
      exact StringFlow.Lte.invFive_spec P hP L'

/-- `2^n` is not divisible by 5. -/
theorem two_pow_mod_five_ne_zero (n : Nat) : (2 ^ n) % 5 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      have hlt : (2 ^ n) % 5 < 5 := Nat.mod_lt _ (by decide)
      have hcases : (2 ^ n) % 5 = 1 ∨ (2 ^ n) % 5 = 2 ∨
          (2 ^ n) % 5 = 3 ∨ (2 ^ n) % 5 = 4 := by omega
      rcases hcases with h1 | h2 | h3 | h4
      · rw [h1]
        native_decide
      · rw [h2]
        native_decide
      · rw [h3]
        native_decide
      · rw [h4]
        native_decide

/-- Swap the first two factors of an associative product. -/
theorem mul_left_swap (a b c : Nat) : a * (b * c) = b * (a * c) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a b, Nat.mul_assoc]

/-- If `N <= Q*m`, the residue of `Q*m - N` is the negative of the
residue of `N`: `(Q*m-N)%Q = (Q-N%Q)%Q`. -/
theorem mod_of_mul_sub (Q m N : Nat) (hQ : 0 < Q) (hle : N ≤ Q * m) :
    (Q * m - N) % Q = (Q - N % Q) % Q := by
  let r := N % Q
  let k := N / Q
  have hdec : N = Q * k + r := by
    dsimp [r, k]
    exact (Nat.div_add_mod N Q).symm
  have hrltQ : r < Q := by
    dsimp [r]
    exact Nat.mod_lt N hQ
  have hkmul : Q * k ≤ Q * m := by
    have hkmul' : Q * k + r ≤ Q * m := by
      rw [← hdec]
      exact hle
    omega
  have hqle : k ≤ m := Nat.le_of_mul_le_mul_left hkmul hQ
  by_cases hr : r = 0
  · have hN0 : N = Q * k := by simpa [hr] using hdec
    have hdiff : Q * m - N = Q * (m - k) := by
      rw [hN0]
      rw [Nat.mul_sub_left_distrib]
    rw [hdiff]
    change (Q * (m - k)) % Q = (Q - r) % Q
    rw [hr]
    rw [Nat.mul_mod_right]
    simp
  · have hklt : k < m := by
      have hklt' : Q * k < Q * m := by
        have hle' : Q * k + r ≤ Q * m := by
          rw [← hdec]
          exact hle
        omega
      exact (Nat.mul_lt_mul_left hQ).1 hklt'
    have hsubmul : Q * (m - k) = Q * m - Q * k := by
      rw [Nat.mul_sub_left_distrib]
    have hdiff : Q * m - N = Q * (m - k) - r := by
      rw [hdec, hsubmul, Nat.sub_sub]
    let s := m - k - 1
    have hms : m - k = s + 1 := by
      dsimp [s]
      omega
    have hform : Q * (m - k) - r = Q * s + (Q - r) := by
      rw [hms]
      rw [Nat.mul_add]
      simp
      rw [Nat.add_sub_assoc (Nat.le_of_lt hrltQ) (Q * s)]
    have hQrlt : Q - r < Q := by omega
    have hmod : (Q * (m - k) - r) % Q = Q - r := by
      rw [hform]
      rw [Nat.add_comm]
      rw [Nat.add_mul_mod_self_left (Q - r) Q s]
      exact Nat.mod_eq_of_lt hQrlt
    rw [hdiff, hmod]
    change Q - r = (Q - r) % Q
    rw [Nat.mod_eq_of_lt hQrlt]

/-- Residue of both sides of `P*q+N=Q*m`. -/
theorem add_eq_mul_mod_eq (P q N Q m : Nat) (hQ : 0 < Q)
    (h : P * q + N = Q * m) :
    (P * q) % Q = (Q - N % Q) % Q := by
  have hle : N ≤ Q * m := by omega
  have hsub : P * q = Q * m - N := by omega
  rw [hsub]
  exact mod_of_mul_sub Q m N hQ hle

/-- Multiplying by an inverse identifies residues modulo `Q`. -/
theorem mod_cancel_mul_left (P a b inv Q : Nat) (_hQ : 0 < Q)
    (hinv : (P * inv) % Q = 1)
    (hmod : (P * a) % Q = (P * b) % Q) :
    a % Q = b % Q := by
  have hleft : (P * ((a * inv) % Q)) % Q = a % Q :=
    mul_mod_inv P a inv Q hinv
  have hright : (P * ((b * inv) % Q)) % Q = b % Q :=
    mul_mod_inv P b inv Q hinv
  have hmid : (P * ((a * inv) % Q)) % Q = (P * ((b * inv) % Q)) % Q := by
    have h1 (x : Nat) : (P * ((x * inv) % Q)) % Q =
        (P * (x * inv)) % Q := by
      rw [Nat.mul_mod, Nat.mul_mod]
      simp
    have h2 (x : Nat) : (P * (x * inv)) % Q =
        (((P * x) % Q) * (inv % Q)) % Q := by
      rw [← Nat.mul_assoc]
      rw [Nat.mul_mod]
    rw [h1 a, h1 b, h2 a, h2 b, hmod]
  rw [← hleft, ← hright]
  exact hmid

/-- The survivor parameter `q` is congruent to the explicit `q_0`
modulo `5^L`. -/
theorem survivor_q_mod (P q N m L : Nat) (hP : P % 5 ≠ 0) (hL : 1 ≤ L)
    (h : P * q + N = 5 ^ L * m) :
    q % 5 ^ L = survivorQ0 P N L := by
  let Q := 5 ^ L
  have hQ : 0 < Q := Nat.pow_pos (by decide)
  have hinv : (P * StringFlow.Lte.invFive P L) % Q = 1 := by
    dsimp [Q]
    exact invFive_spec_at P L hP hL
  have hPq0 : (P * survivorQ0 P N L) % Q = (Q - N % Q) % Q := by
    have hstep := mul_mod_inv P (Q - N % Q) (StringFlow.Lte.invFive P L) Q hinv
    simpa [survivorQ0, Q] using hstep
  have hPq : (P * q) % Q = (Q - N % Q) % Q := by
    exact add_eq_mul_mod_eq P q N Q m hQ (by simpa [Q] using h)
  have hcancel := mod_cancel_mul_left P q (survivorQ0 P N L)
    (StringFlow.Lte.invFive P L) Q hQ hinv
  have hres : q % Q = survivorQ0 P N L % Q := hcancel (by
    rw [hPq, hPq0])
  have hsmall : survivorQ0 P N L < Q := by
    unfold survivorQ0
    exact Nat.mod_lt _ hQ
  rw [show survivorQ0 P N L % Q = survivorQ0 P N L by
    exact Nat.mod_eq_of_lt hsmall] at hres
  dsimp [Q] at hres
  exact hres

/-- If `P*q+N=5^L*m`, then `m` differs from the explicit
representative `(P*q_0+N)/5^L` by a multiple of `P`. -/
theorem survivor_m_explicit (P q N m L : Nat) (hP : P % 5 ≠ 0)
    (hL : 1 ≤ L) (h : P * q + N = 5 ^ L * m) :
    ∃ k, m = (P * survivorQ0 P N L + N) / 5 ^ L + P * k := by
  let Q := 5 ^ L
  have hQ : 0 < Q := Nat.pow_pos (by decide)
  have hq0 : q % Q = survivorQ0 P N L := by
    exact survivor_q_mod P q N m L hP hL h
  let k := q / Q
  have hqdec : q = Q * k + q % Q := by
    have hd := (Nat.div_add_mod q Q).symm
    simpa [k] using hd
  have hqrep : q = Q * k + survivorQ0 P N L := by
    rw [hqdec, hq0]
  have hPk_le : P * k ≤ m := by
    have hqge : Q * k ≤ q := by omega
    have hprod_le : P * (Q * k) ≤ P * q := Nat.mul_le_mul_left P hqge
    have hQm : P * q + N = Q * m := by simpa [Q] using h
    have hPq_le : P * q ≤ Q * m := by omega
    have hPQ : P * (Q * k) = Q * (P * k) := mul_left_swap P Q k
    have hle : Q * (P * k) ≤ Q * m := by
      rw [← hPQ]
      exact Nat.le_trans hprod_le hPq_le
    exact Nat.le_of_mul_le_mul_left hle hQ
  have hmain : Q * (m - P * k) = P * survivorQ0 P N L + N := by
    have h' : P * (Q * k + survivorQ0 P N L) + N = Q * m := by
      rw [← hqrep]
      simpa [Q] using h
    have hPQ : P * (Q * k) = Q * (P * k) := mul_left_swap P Q k
    rw [Nat.mul_add, hPQ] at h'
    have hsubmul : Q * (m - P * k) = Q * m - Q * (P * k) := by
      rw [Nat.mul_sub_left_distrib]
    rw [hsubmul]
    omega
  have hdiv : (P * survivorQ0 P N L + N) / Q = m - P * k := by
    rw [← hmain]
    rw [Nat.mul_div_right (m - P * k) hQ]
  refine ⟨k, ?_⟩
  rw [hdiv]
  omega

/-- Balance form of the survivor parameterization: `P*q+N/40=Q*m`. -/
theorem word_survivor_balance_div (w : List Nat) (B m y0 : Nat)
    (hB : B = 40 * m + 23)
    (hsur : ∃ q, 2 ^ StringFlow.wordWeight w * (y0 + 40 * q) =
      5 ^ w.length * B + wordA w)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * y0) :
    ∃ q, 2 ^ StringFlow.wordWeight w * q +
      (2 ^ StringFlow.wordWeight w * y0 - wordA w - 23 * 5 ^ w.length) / 40 =
      5 ^ w.length * m := by
  rcases hsur with ⟨q, hq⟩
  have hm := word_survivor_m_equation w B m y0 q hB hq
  let P := 2 ^ StringFlow.wordWeight w
  let Q := 5 ^ w.length
  let N := P * y0 - wordA w - 23 * Q
  have hm' : P * y0 + 40 * P * q = 40 * Q * m + 23 * Q + wordA w := by
    simpa [P, Q] using hm
  have hpos' : 23 * Q + wordA w ≤ P * y0 := by simpa [P, Q] using hpos
  have hge : P * q ≤ Q * m :=
    survivor_balance_ge P Q (wordA w) y0 m q hm' hpos'
  have h40 : 40 * (Q * m - P * q) = N := by
    dsimp [N]
    exact survivor_balance_eq P Q (wordA w) y0 m q hm' hpos' hge
  have hNdiv : P * q + N / 40 = Q * m := by
    rw [← h40]
    rw [Nat.mul_div_right (Q * m - P * q) (by decide : 0 < 40)]
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hge
  exact ⟨q, by simpa [P, Q, N] using hNdiv⟩

/-- Explicit forward direction of Corollary 35.4: `m` is congruent to
the explicit representative `(2^S*q_0+N/40)/5^L` modulo `2^S`. -/
theorem word_survivor_m_explicit_general (w : List Nat) (B m y0 : Nat)
    (hB : B = 40 * m + 23)
    (hsur : ∃ q, 2 ^ StringFlow.wordWeight w * (y0 + 40 * q) =
      5 ^ w.length * B + wordA w)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * y0)
    (hw : 1 ≤ w.length) :
    ∃ k,
      m = (2 ^ StringFlow.wordWeight w *
            survivorQ0 (2 ^ StringFlow.wordWeight w)
              ((2 ^ StringFlow.wordWeight w * y0 - wordA w -
                23 * 5 ^ w.length) / 40) w.length +
            (2 ^ StringFlow.wordWeight w * y0 - wordA w -
              23 * 5 ^ w.length) / 40) /
            5 ^ w.length +
          2 ^ StringFlow.wordWeight w * k := by
  let P := 2 ^ StringFlow.wordWeight w
  let Q := 5 ^ w.length
  let N := P * y0 - wordA w - 23 * Q
  rcases word_survivor_balance_div w B m y0 hB hsur hpos with ⟨q, hNdiv⟩
  have hNdiv' : P * q + N / 40 = Q * m := by simpa [P, Q, N] using hNdiv
  have hP : P % 5 ≠ 0 := by
    dsimp [P]
    exact two_pow_mod_five_ne_zero (StringFlow.wordWeight w)
  have hNdiv5 : P * q + N / 40 = 5 ^ w.length * m := by
    simpa [Q] using hNdiv'
  have hm := survivor_m_explicit P q (N / 40) m w.length hP hw hNdiv5
  simpa [P, Q, N] using hm

/-- Corollary 35.4, `t=1` branch: explicit `q_0` parameterization. -/
theorem word_survivor_m_explicit_last_one (w : List Nat) (B m : Nat)
    (hB : B = 40 * m + 23) (hlast : wordLast w = 1)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * 3) :
    ∃ k,
      m = (2 ^ StringFlow.wordWeight w *
            survivorQ0 (2 ^ StringFlow.wordWeight w)
              ((2 ^ StringFlow.wordWeight w * 3 - wordA w -
                23 * 5 ^ w.length) / 40) w.length +
            (2 ^ StringFlow.wordWeight w * 3 - wordA w -
              23 * 5 ^ w.length) / 40) /
            5 ^ w.length +
          2 ^ StringFlow.wordWeight w * k := by
  have hsur := word_survivor_rev_last_one w B hvalid hend hlast
  have hw : 1 ≤ w.length := by
    cases w with
    | nil => simp [wordLast] at hlast
    | cons t ts => simp
  exact word_survivor_m_explicit_general w B m 3 hB hsur hpos hw

/-- Corollary 35.4, `t=2` branch: explicit `q_0` parameterization. -/
theorem word_survivor_m_explicit_last_two (w : List Nat) (B m : Nat)
    (hB : B = 40 * m + 23) (hlast : wordLast w = 2)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * 19) :
    ∃ k,
      m = (2 ^ StringFlow.wordWeight w *
            survivorQ0 (2 ^ StringFlow.wordWeight w)
              ((2 ^ StringFlow.wordWeight w * 19 - wordA w -
                23 * 5 ^ w.length) / 40) w.length +
            (2 ^ StringFlow.wordWeight w * 19 - wordA w -
              23 * 5 ^ w.length) / 40) /
            5 ^ w.length +
          2 ^ StringFlow.wordWeight w * k := by
  have hsur := word_survivor_rev_last_two w B hvalid hend hlast
  have hw : 1 ≤ w.length := by
    cases w with
    | nil => simp [wordLast] at hlast
    | cons t ts => simp
  exact word_survivor_m_explicit_general w B m 19 hB hsur hpos hw

end StringFlow.Word
