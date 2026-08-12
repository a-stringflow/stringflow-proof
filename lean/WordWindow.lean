import Domination
import LteMacro

namespace StringFlow.Word

/-- Prefix numerator `A_L` of a word:
`A = 5^(len tail) + 2^t * A(tail)`. -/
def wordA : List Nat → Nat
  | [] => 0
  | t :: ts => 5 ^ ts.length + 2 ^ t * wordA ts

/-- Accelerated orbit along a word. -/
def wordOrbit : List Nat → Nat → Nat
  | [], x => x
  | t :: ts, x => wordOrbit ts ((5 * x + 1) / 2 ^ t)

/-- Each word step is exact for `x`. -/
def wordValid : List Nat → Nat → Prop
  | [], _ => True
  | t :: ts, x => (5 * x + 1) % 2 ^ t = 0 ∧ wordValid ts ((5 * x + 1) / 2 ^ t)

/-- All word steps have weight at most 2. -/
def wordOK : List Nat → Prop
  | [] => True
  | t :: ts => t ≤ 2 ∧ wordOK ts

/-- Last entry of a nonempty word (0 for the empty word). -/
def wordLast : List Nat → Nat
  | [] => 0
  | [t] => t
  | _ :: ts => wordLast ts

/-- The last step weight is at most the total word weight. -/
theorem wordLast_le_wordWeight (w : List Nat) (hw : wordOK w) :
    wordLast w ≤ StringFlow.wordWeight w := by
  cases w with
  | nil => simp [wordLast, StringFlow.wordWeight]
  | cons t ts =>
      by_cases hts : ts = []
      · subst ts
        simp [wordLast, StringFlow.wordWeight]
      · have hwts : wordOK ts := hw.2
        have ih := wordLast_le_wordWeight ts hwts
        simp [wordLast, StringFlow.wordWeight]
        omega

/-- Modulo 5, only the last step contributes to `A_L`:
`A_L ≡ 2^(S - last) (mod 5)`. -/
theorem wordA_mod_five_of_wordLast (w : List Nat) (hw : wordOK w) (hne : w ≠ []) :
    wordA w % 5 = (2 ^ (StringFlow.wordWeight w - wordLast w)) % 5 := by
  induction w with
  | nil => simp at hne
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        simp [wordA, StringFlow.wordWeight, wordLast]
      · have hwts : wordOK ts := hw.2
        have hne' : ts ≠ [] := hts
        have ih' := ih hwts hne'
        have hlast : wordLast ts ≤ StringFlow.wordWeight ts :=
          wordLast_le_wordWeight ts hwts
        have hmain : wordA (t :: ts) % 5 =
            (2 ^ (StringFlow.wordWeight (t :: ts) - wordLast (t :: ts))) % 5 := by
          simp [wordA, StringFlow.wordWeight, wordLast]
          rw [Nat.add_mod, Nat.mul_mod]
          have h5 : (5 ^ ts.length) % 5 = 0 := by
            have hlen : 1 ≤ ts.length := by
              cases ts with
              | nil => contradiction
              | cons a as => simp
            have hdvd : 5 ∣ 5 ^ ts.length := by
              refine ⟨5 ^ (ts.length - 1), ?_⟩
              have hsucc : ts.length = Nat.succ (ts.length - 1) := by omega
              conv =>
                lhs
                rw [hsucc]
                rw [Nat.pow_succ]
              rw [Nat.mul_comm]
            rwa [← Nat.dvd_iff_mod_eq_zero]
          rw [h5]
          rw [ih']
          have hexp : t + (StringFlow.wordWeight ts - wordLast ts) =
              t + StringFlow.wordWeight ts - wordLast ts := by omega
          have hpow : 2 ^ (t + (StringFlow.wordWeight ts - wordLast ts)) =
              2 ^ t * 2 ^ (StringFlow.wordWeight ts - wordLast ts) := by
            rw [Nat.pow_add]
          rw [← hexp, hpow, Nat.mul_mod]
          simp
        exact hmain

/-- `2^(n+4) ≡ 2^n (mod 5)`. -/
theorem pow_two_mod_five_period (n : Nat) :
    (2 ^ (n + 4)) % 5 = (2 ^ n) % 5 := by
  have h4 : (2 ^ 4) % 5 = 1 := by native_decide
  rw [Nat.pow_add, Nat.mul_mod, h4]
  simp

/-- `A_L < 5^L` for words over `{1,2}`. -/
theorem wordA_lt_five_pow (w : List Nat) (hw : wordOK w) :
    wordA w < 5 ^ w.length := by
  induction w with
  | nil => simp [wordA]
  | cons t ts ih =>
      have ht : t ≤ 2 := hw.1
      have hts : wordOK ts := hw.2
      have ih' := ih hts
      have h2 : 2 ^ t ≤ 4 := by
        by_cases h0 : t = 0
        · rw [h0]
          native_decide
        · by_cases h1 : t = 1
          · rw [h1]
            native_decide
          · have h2' : t = 2 := by omega
            rw [h2']
            native_decide
      have h4 : 2 ^ t * wordA ts < 4 * 5 ^ ts.length := by
        have hmul := Nat.mul_le_mul_right (wordA ts) h2
        have hstrict : 2 ^ t * wordA ts < 2 ^ t * 5 ^ ts.length := by
          exact Nat.mul_lt_mul_of_pos_left ih' (Nat.pow_pos (by decide))
        have hle : 2 ^ t * 5 ^ ts.length ≤ 4 * 5 ^ ts.length := by
          exact Nat.mul_le_mul_right (5 ^ ts.length) h2
        omega
      have hsum : 5 ^ ts.length + 2 ^ t * wordA ts < 5 * 5 ^ ts.length := by
        omega
      change wordA (t :: ts) < 5 ^ (ts.length + 1)
      simp [wordA]
      have hpow : 5 ^ (ts.length + 1) = 5 * 5 ^ ts.length := by
        rw [show ts.length + 1 = Nat.succ ts.length by omega]
        rw [Nat.pow_succ]
        rw [Nat.mul_comm]
      rw [hpow]
      exact hsum

/-- `A_L <= 5^L - 4^L` for words over `{1,2}`. -/
theorem wordA_le_five_pow_sub_four_pow (w : List Nat) (hw : wordOK w) :
    wordA w ≤ 5 ^ w.length - 4 ^ w.length := by
  induction w with
  | nil => simp [wordA]
  | cons t ts ih =>
      have ht : t ≤ 2 := hw.1
      have hts : wordOK ts := hw.2
      have ih' := ih hts
      have h2 : 2 ^ t ≤ 4 := by
        by_cases h0 : t = 0
        · rw [h0]
          native_decide
        · by_cases h1 : t = 1
          · rw [h1]
            native_decide
          · have h2' : t = 2 := by omega
            rw [h2']
            native_decide
      have hpow5 : 5 ^ (ts.length + 1) = 5 * 5 ^ ts.length := by
        rw [show ts.length + 1 = Nat.succ ts.length by omega]
        rw [Nat.pow_succ]
        rw [Nat.mul_comm]
      have hpow4 : 4 ^ (ts.length + 1) = 4 * 4 ^ ts.length := by
        rw [show ts.length + 1 = Nat.succ ts.length by omega]
        rw [Nat.pow_succ]
        rw [Nat.mul_comm]
      change wordA (t :: ts) ≤ 5 ^ (ts.length + 1) - 4 ^ (ts.length + 1)
      simp [wordA]
      rw [hpow5, hpow4]
      have hle4 : 4 ^ ts.length ≤ 5 ^ ts.length :=
        Nat.pow_le_pow_left (show 4 ≤ 5 by decide) ts.length
      have hmul1 : 2 ^ t * wordA ts ≤ 4 * wordA ts :=
        Nat.mul_le_mul_right (wordA ts) h2
      have hmul2 : 4 * wordA ts ≤ 4 * (5 ^ ts.length - 4 ^ ts.length) :=
        Nat.mul_le_mul_left 4 ih'
      have hmul : 2 ^ t * wordA ts ≤ 4 * (5 ^ ts.length - 4 ^ ts.length) :=
        Nat.le_trans hmul1 hmul2
      have hsub : 4 * (5 ^ ts.length - 4 ^ ts.length) =
          4 * 5 ^ ts.length - 4 * 4 ^ ts.length := by
        rw [Nat.mul_sub_left_distrib]
      have hle4' : 4 * 4 ^ ts.length ≤ 4 * 5 ^ ts.length :=
        Nat.mul_le_mul_left 4 hle4
      have hsum : 5 ^ ts.length + 2 ^ t * wordA ts ≤
          5 ^ ts.length + 4 * (5 ^ ts.length - 4 ^ ts.length) := by omega
      have hright : 5 ^ ts.length + 4 * (5 ^ ts.length - 4 ^ ts.length) =
          5 * 5 ^ ts.length - 4 * 4 ^ ts.length := by
        rw [hsub]
        omega
      omega

/-- Word orbit identity:
`2^S * orbit = 5^L * x + A_L`. -/
theorem word_orbit_identity (w : List Nat) (x : Nat) (h : wordValid w x) :
    2 ^ StringFlow.wordWeight w * wordOrbit w x =
      5 ^ w.length * x + wordA w := by
  induction w generalizing x with
  | nil =>
      simp [wordOrbit, wordA, StringFlow.wordWeight]
  | cons t ts ih =>
      have hdiv : (5 * x + 1) % 2 ^ t = 0 := h.1
      have htail : wordValid ts ((5 * x + 1) / 2 ^ t) := h.2
      have hstep : 2 ^ t * ((5 * x + 1) / 2 ^ t) = 5 * x + 1 := by
        have hdvd : 2 ^ t ∣ 5 * x + 1 := Nat.dvd_iff_mod_eq_zero.mpr hdiv
        rcases hdvd with ⟨q, hq⟩
        have hq' : (5 * x + 1) / 2 ^ t = q := by
          have hm : (2 ^ t * q) / 2 ^ t = q :=
            Nat.mul_div_right (n := q) (m := 2 ^ t) (Nat.pow_pos (by decide))
          rw [← hq] at hm
          exact hm
        rw [hq']
        exact hq.symm
      have ih' := ih ((5 * x + 1) / 2 ^ t) htail
      have hfive : 5 ^ ts.length * (5 * x + 1) =
          5 ^ (ts.length + 1) * x + 5 ^ ts.length := by
        rw [Nat.mul_add]
        have hswap : 5 ^ ts.length * (5 * x) = 5 ^ (ts.length + 1) * x := by
          calc
            5 ^ ts.length * (5 * x)
                = (5 ^ ts.length * 5) * x := by
                    rw [Nat.mul_assoc]
            _ = 5 ^ (ts.length + 1) * x := by rw [Nat.pow_succ]
        rw [hswap]
        simp
      calc
        2 ^ StringFlow.wordWeight (t :: ts) * wordOrbit (t :: ts) x
            = 2 ^ (t + StringFlow.wordWeight ts) *
                wordOrbit ts ((5 * x + 1) / 2 ^ t) := by
                simp [StringFlow.wordWeight, wordOrbit]
        _ = 2 ^ t * (2 ^ StringFlow.wordWeight ts *
                wordOrbit ts ((5 * x + 1) / 2 ^ t)) := by
                rw [Nat.pow_add]
                rw [Nat.mul_assoc]
        _ = 2 ^ t * (5 ^ ts.length * ((5 * x + 1) / 2 ^ t) + wordA ts) := by
                rw [ih']
        _ = 2 ^ t * (5 ^ ts.length * ((5 * x + 1) / 2 ^ t)) + 2 ^ t * wordA ts := by
                rw [Nat.mul_add]
        _ = 5 ^ ts.length * (2 ^ t * ((5 * x + 1) / 2 ^ t)) + 2 ^ t * wordA ts := by
                simp [Nat.mul_assoc, Nat.mul_comm]
        _ = 5 ^ ts.length * (5 * x + 1) + 2 ^ t * wordA ts := by rw [hstep]
        _ = 5 ^ (ts.length + 1) * x + (5 ^ ts.length + 2 ^ t * wordA ts) := by
                rw [hfive]
                omega
        _ = 5 ^ (t :: ts).length * x + wordA (t :: ts) := by
                simp [wordA, Nat.pow_succ]

/-- If a valid word ends at a C3 point, the affine orbit value is
`3*2^S` modulo `2^(S+3)`. -/
theorem word_endpoint_congruence (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hend : wordOrbit w x % 8 = 3) :
    (5 ^ w.length * x + wordA w) % 2 ^ (StringFlow.wordWeight w + 3) =
      (3 * 2 ^ StringFlow.wordWeight w) % 2 ^ (StringFlow.wordWeight w + 3) := by
  have hid := word_orbit_identity w x hvalid
  let S := StringFlow.wordWeight w
  let y := wordOrbit w x
  have hy : y % 8 = 3 := hend
  have hdec : y = 8 * (y / 8) + 3 := by
    have h := Nat.div_add_mod y 8
    rw [hy] at h
    omega
  have hpow : 2 ^ (S + 3) = 2 ^ S * 8 := by
    rw [show 8 = 2 ^ 3 by rfl]
    rw [← Nat.pow_add]
  have hmain : 2 ^ S * y = 3 * 2 ^ S + 2 ^ (S + 3) * (y / 8) := by
    calc
      2 ^ S * y = 2 ^ S * (8 * (y / 8) + 3) := by
          conv =>
            lhs
            rw [hdec]
      _ = 3 * 2 ^ S + 2 ^ (S + 3) * (y / 8) := by
          rw [hpow]
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
            Nat.add_comm]
  have hid' : 5 ^ w.length * x + wordA w = 2 ^ S * y := by
    simpa [S, y, Nat.mul_comm] using hid.symm
  rw [hid']
  rw [hmain]
  have hq : (2 ^ (S + 3) * (y / 8)) % 2 ^ (S + 3) = 0 := by
    rw [Nat.mul_mod]
    simp
  rw [Nat.add_mod, hq]
  simp [S, Nat.add_comm]

/-- Equal residues imply divisibility of the ordered difference. -/
theorem dvd_sub_of_mod_eq (a b m : Nat) (_hm : 0 < m) (hle : a ≤ b)
    (h : a % m = b % m) : m ∣ b - a := by
  have ha : a = m * (a / m) + a % m := by
    have h := Nat.div_add_mod a m
    simpa [Nat.mul_comm] using h.symm
  have hb : b = m * (b / m) + b % m := by
    have h := Nat.div_add_mod b m
    simpa [Nat.mul_comm] using h.symm
  have hba : b - a = m * (b / m - a / m) := by
    have hmain : b - a = (m * (b / m) + b % m) - (m * (a / m) + a % m) := by
      rw [← hb, ← ha]
    rw [h] at hmain
    have hmid : (m * (b / m) + b % m) - (m * (a / m) + b % m) =
        m * (b / m) - m * (a / m) := by omega
    rw [hmid] at hmain
    rw [← Nat.mul_sub_left_distrib] at hmain
    exact hmain
  rw [hba]
  exact ⟨b / m - a / m, rfl⟩

/-- Multiplying by `5^L` does not change divisibility by a power of two. -/
theorem dvd_two_pow_of_five_pow_mul (L k n : Nat) :
    2 ^ k ∣ 5 ^ L * n → 2 ^ k ∣ n := by
  induction L with
  | zero => intro h; simpa using h
  | succ L ih =>
      intro h
      have h' : 2 ^ k ∣ 5 ^ L * n := by
        have hpow : 5 ^ (L + 1) * n = 5 * (5 ^ L * n) := by
          rw [Nat.pow_succ]
          simp [Nat.mul_comm, Nat.mul_left_comm]
        rw [hpow] at h
        exact StringFlow.Lte.dvd_two_pow_of_odd_mul k (5 ^ L * n) h
      exact ih h'

/-- A valid word ending at C3 has at most one start below `2^(S+3)`. -/
theorem word_representative_unique (w : List Nat) (x1 x2 : Nat)
    (hv1 : wordValid w x1) (hv2 : wordValid w x2)
    (he1 : wordOrbit w x1 % 8 = 3) (he2 : wordOrbit w x2 % 8 = 3)
    (hx1 : x1 < 2 ^ (StringFlow.wordWeight w + 3))
    (hx2 : x2 < 2 ^ (StringFlow.wordWeight w + 3)) :
    x1 = x2 := by
  let M := StringFlow.wordWeight w + 3
  let L := w.length
  let A := wordA w
  have hc1 := word_endpoint_congruence w x1 hv1 he1
  have hc2 := word_endpoint_congruence w x2 hv2 he2
  have hc : (5 ^ L * x1 + A) % 2 ^ M = (5 ^ L * x2 + A) % 2 ^ M := by
    rw [hc1, hc2]
  by_cases hle : x1 ≤ x2
  · have hlef : 5 ^ L * x1 + A ≤ 5 ^ L * x2 + A := by
      have hmul : 5 ^ L * x1 ≤ 5 ^ L * x2 := Nat.mul_le_mul_left (5 ^ L) hle
      omega
    have hdvd : 2 ^ M ∣ (5 ^ L * x2 + A) - (5 ^ L * x1 + A) :=
      dvd_sub_of_mod_eq (5 ^ L * x1 + A) (5 ^ L * x2 + A) (2 ^ M)
        (show 0 < 2 ^ M by exact Nat.pow_pos (by decide)) hlef hc
    have hdvd' : 2 ^ M ∣ 5 ^ L * (x2 - x1) := by
      have hsub : (5 ^ L * x2 + A) - (5 ^ L * x1 + A) = 5 ^ L * (x2 - x1) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [← hsub]
      exact hdvd
    have hdiv : 2 ^ M ∣ x2 - x1 :=
      dvd_two_pow_of_five_pow_mul L M (x2 - x1) hdvd'
    have hlt : x2 - x1 < 2 ^ M := by
      have hx2' : x2 < 2 ^ M := by simpa [M] using hx2
      omega
    have hz : x2 - x1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  · have hle2 : x2 ≤ x1 := by omega
    have hlef : 5 ^ L * x2 + A ≤ 5 ^ L * x1 + A := by
      have hmul : 5 ^ L * x2 ≤ 5 ^ L * x1 := Nat.mul_le_mul_left (5 ^ L) hle2
      omega
    have hdvd : 2 ^ M ∣ (5 ^ L * x1 + A) - (5 ^ L * x2 + A) :=
      dvd_sub_of_mod_eq (5 ^ L * x2 + A) (5 ^ L * x1 + A) (2 ^ M)
        (show 0 < 2 ^ M by exact Nat.pow_pos (by decide)) hlef hc.symm
    have hdvd' : 2 ^ M ∣ 5 ^ L * (x1 - x2) := by
      have hsub : (5 ^ L * x1 + A) - (5 ^ L * x2 + A) = 5 ^ L * (x1 - x2) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [← hsub]
      exact hdvd
    have hdiv : 2 ^ M ∣ x1 - x2 :=
      dvd_two_pow_of_five_pow_mul L M (x1 - x2) hdvd'
    have hlt : x1 - x2 < 2 ^ M := by
      have hx1' : x1 < 2 ^ M := by simpa [M] using hx1
      omega
    have hz : x1 - x2 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega

/-- First-C3 weight at most 6 and below the W window. -/
def isLowWeightW (B : Nat) : Bool :=
  let r := StringFlow.firstC3H 20 B
  r.1 && decide (r.2 ≤ 6) && decide (B < 2 ^ (r.2 + 3))

/-- `t=2` low-weight exclusion: no `B=40m+23>330` has first-C3
weight at most 6 while lying below `2^(S+3)`. -/
theorem t2_low_weight_excluded (B S : Nat)
    (hmod : B % 40 = 23) (hgt : 330 < B) (hS : S ≤ 6)
    (hfirst : StringFlow.firstC3H 20 B = (true, S))
    (hbound : B < 2 ^ (S + 3)) : False := by
  have hBlt : B < 512 := by
    have hpow : 2 ^ (S + 3) ≤ 2 ^ 9 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hdec : B = 40 * (B / 40) + 23 := by
    have h := Nat.div_add_mod B 40
    rw [hmod] at h
    omega
  have hqge : 8 ≤ B / 40 := by omega
  have hqle : B / 40 ≤ 12 := by omega
  have hcases : B / 40 = 8 ∨ B / 40 = 9 ∨ B / 40 = 10 ∨
      B / 40 = 11 ∨ B / 40 = 12 := by
    by_cases h8 : B / 40 = 8
    · exact Or.inl h8
    · by_cases h9 : B / 40 = 9
      · exact Or.inr (Or.inl h9)
      · by_cases h10 : B / 40 = 10
        · exact Or.inr (Or.inr (Or.inl h10))
        · by_cases h11 : B / 40 = 11
          · exact Or.inr (Or.inr (Or.inr (Or.inl h11)))
          · have h12 : B / 40 = 12 := by omega
            exact Or.inr (Or.inr (Or.inr (Or.inr h12)))
  rcases hcases with h8 | h9 | h10 | h11 | h12
  · have hB : B = 343 := by omega
    subst B
    have hw : isLowWeightW 343 = true := by
      dsimp [isLowWeightW]
      rw [hfirst]
      simp [hS, hbound]
    have hbad : isLowWeightW 343 = false := by native_decide
    simp [hw] at hbad
  · have hB : B = 383 := by omega
    subst B
    have hw : isLowWeightW 383 = true := by
      dsimp [isLowWeightW]
      rw [hfirst]
      simp [hS, hbound]
    have hbad : isLowWeightW 383 = false := by native_decide
    simp [hw] at hbad
  · have hB : B = 423 := by omega
    subst B
    have hw : isLowWeightW 423 = true := by
      dsimp [isLowWeightW]
      rw [hfirst]
      simp [hS, hbound]
    have hbad : isLowWeightW 423 = false := by native_decide
    simp [hw] at hbad
  · have hB : B = 463 := by omega
    subst B
    have hw : isLowWeightW 463 = true := by
      dsimp [isLowWeightW]
      rw [hfirst]
      simp [hS, hbound]
    have hbad : isLowWeightW 463 = false := by native_decide
    simp [hw] at hbad
  · have hB : B = 503 := by omega
    subst B
    have hw : isLowWeightW 503 = true := by
      dsimp [isLowWeightW]
      rw [hfirst]
      simp [hS, hbound]
    have hbad : isLowWeightW 503 = false := by native_decide
    simp [hw] at hbad

/-- Each word has at most one `t=2` candidate `40m+23` below the W
window. -/
theorem word_representative_unique_t2 (w : List Nat) (m1 m2 : Nat)
    (hv1 : wordValid w (40 * m1 + 23)) (hv2 : wordValid w (40 * m2 + 23))
    (he1 : wordOrbit w (40 * m1 + 23) % 8 = 3)
    (he2 : wordOrbit w (40 * m2 + 23) % 8 = 3)
    (hx1 : 40 * m1 + 23 < 2 ^ (StringFlow.wordWeight w + 3))
    (hx2 : 40 * m2 + 23 < 2 ^ (StringFlow.wordWeight w + 3)) :
    m1 = m2 := by
  have h := word_representative_unique w (40 * m1 + 23) (40 * m2 + 23)
    hv1 hv2 he1 he2 hx1 hx2
  omega

/-- Each word has at most one `t=1` candidate `20m+13` below the W
window. -/
theorem word_representative_unique_t1 (w : List Nat) (m1 m2 : Nat)
    (hv1 : wordValid w (20 * m1 + 13)) (hv2 : wordValid w (20 * m2 + 13))
    (he1 : wordOrbit w (20 * m1 + 13) % 8 = 3)
    (he2 : wordOrbit w (20 * m2 + 13) % 8 = 3)
    (hx1 : 20 * m1 + 13 < 2 ^ (StringFlow.wordWeight w + 3))
    (hx2 : 20 * m2 + 13 < 2 ^ (StringFlow.wordWeight w + 3)) :
    m1 = m2 := by
  have h := word_representative_unique w (20 * m1 + 13) (20 * m2 + 13)
    hv1 hv2 he1 he2 hx1 hx2
  omega

/-- If `p≡3 mod 8`, then the accelerated step has weight at least 3,
so it is not an allowed `t∈{1,2}` step. -/
theorem eight_dvd_five_mul_add_one_of_mod_eight_three (p : Nat)
    (hp : p % 8 = 3) : 8 ∣ 5 * p + 1 := by
  have hdec : p = 8 * (p / 8) + 3 := by
    have h := Nat.div_add_mod p 8
    rw [hp] at h
    omega
  refine ⟨5 * (p / 8) + 2, ?_⟩
  rw [hdec]
  omega

theorem t2_parent_mod_eight (m : Nat) :
    (50 * m + 29) % 8 = (2 * m + 5) % 8 := by
  simp [Nat.add_mod, Nat.mul_mod]

theorem t1_parent_mod_eight (m : Nat) :
    (50 * m + 33) % 8 = (2 * m + 1) % 8 := by
  simp [Nat.add_mod, Nat.mul_mod]

theorem t2_parent_class (m : Nat) (hm : m % 4 = 3) :
    (50 * m + 29) % 8 = 3 := by
  rw [t2_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 3 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 3) + 5 = 8 * (m / 4) + 11 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h11 : 11 % 8 = 3 := by native_decide
  rw [h8m, h11]

theorem t1_parent_class (m : Nat) (hm : m % 4 = 1) :
    (50 * m + 33) % 8 = 3 := by
  rw [t1_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 1 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 1) + 1 = 8 * (m / 4) + 3 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h3 : 3 % 8 = 3 := by native_decide
  rw [h8m, h3]

theorem t2_parent_mod_eight_zero (m : Nat) (hm : m % 4 = 0) :
    (50 * m + 29) % 8 = 5 := by
  rw [t2_parent_mod_eight]
  have hdec : m = 4 * (m / 4) := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4)) + 5 = 8 * (m / 4) + 5 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h5 : 5 % 8 = 5 := by native_decide
  rw [h8m, h5]

theorem t2_parent_mod_eight_one (m : Nat) (hm : m % 4 = 1) :
    (50 * m + 29) % 8 = 7 := by
  rw [t2_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 1 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 1) + 5 = 8 * (m / 4) + 7 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h7 : 7 % 8 = 7 := by native_decide
  rw [h8m, h7]

theorem t1_parent_mod_eight_zero (m : Nat) (hm : m % 4 = 0) :
    (50 * m + 33) % 8 = 1 := by
  rw [t1_parent_mod_eight]
  have hdec : m = 4 * (m / 4) := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4)) + 1 = 8 * (m / 4) + 1 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h1 : 1 % 8 = 1 := by native_decide
  rw [h8m, h1]

theorem t1_parent_mod_eight_two (m : Nat) (hm : m % 4 = 2) :
    (50 * m + 33) % 8 = 5 := by
  rw [t1_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 2 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 2) + 1 = 8 * (m / 4) + 5 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h5 : 5 % 8 = 5 := by native_decide
  rw [h8m, h5]

theorem t1_parent_mod_eight_three (m : Nat) (hm : m % 4 = 3) :
    (50 * m + 33) % 8 = 7 := by
  rw [t1_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 3 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 3) + 1 = 8 * (m / 4) + 7 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h7 : 7 % 8 = 7 := by native_decide
  rw [h8m, h7]

theorem t2_parent_mod_eight_two (m : Nat) (hm : m % 4 = 2) :
    (50 * m + 29) % 8 = 1 := by
  rw [t2_parent_mod_eight]
  have hdec : m = 4 * (m / 4) + 2 := by
    have h := Nat.div_add_mod m 4
    rw [hm] at h
    omega
  have hlin : 2 * (4 * (m / 4) + 2) + 5 = 8 * (m / 4) + 9 := by omega
  rw [hdec]
  rw [hlin]
  rw [Nat.add_mod]
  have h8m : (8 * (m / 4)) % 8 = 0 := by
    rw [Nat.mul_mod]
    simp
  have h9 : 9 % 8 = 1 := by native_decide
  rw [h8m, h9]

theorem step_weight_one_of_mod8 (p : Nat) (hp : p % 8 = 1 ∨ p % 8 = 5) :
    (5 * p + 1) % 4 = 2 := by
  have hdec : p = 8 * (p / 8) + p % 8 := by
    have h := Nat.div_add_mod p 8
    simpa [Nat.mul_comm] using h.symm
  rcases hp with h1 | h5
  · rw [hdec, h1]
    have hlin : 5 * (8 * (p / 8) + 1) + 1 = 40 * (p / 8) + 6 := by omega
    rw [hlin]
    rw [Nat.add_mod, Nat.mul_mod]
    have h40 : 40 % 4 = 0 := by native_decide
    have h6 : 6 % 4 = 2 := by native_decide
    rw [h40, h6]
    simp
  · rw [hdec, h5]
    have hlin : 5 * (8 * (p / 8) + 5) + 1 = 40 * (p / 8) + 26 := by omega
    rw [hlin]
    rw [Nat.add_mod, Nat.mul_mod]
    have h40 : 40 % 4 = 0 := by native_decide
    have h26 : 26 % 4 = 2 := by native_decide
    rw [h40, h26]
    simp

theorem step_weight_two_of_mod8 (p : Nat) (hp : p % 8 = 7) :
    (5 * p + 1) % 8 = 4 := by
  have hdec : p = 8 * (p / 8) + p % 8 := by
    have h := Nat.div_add_mod p 8
    simpa [Nat.mul_comm] using h.symm
  rw [hdec, hp]
  have hlin : 5 * (8 * (p / 8) + 7) + 1 = 40 * (p / 8) + 36 := by omega
  rw [hlin]
  rw [Nat.add_mod, Nat.mul_mod]
  have h40 : 40 % 8 = 0 := by native_decide
  have h36 : 36 % 8 = 4 := by native_decide
  rw [h40, h36]
  simp

/-- A residue `4 mod 8` is `0 mod 4`. -/
theorem mod4_zero_of_mod8_four (p : Nat) (h : p % 8 = 4) : p % 4 = 0 := by
  have hmod : p % 4 = (p % 8) % 4 :=
    (Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)).symm
  rw [hmod, h]

/-- The `t = 2` step is exact exactly when the parent is `7 mod 8`. -/
theorem step_two_mod4_of_mod8_seven (p : Nat) (hp : p % 8 = 7) :
    (5 * p + 1) % 4 = 0 :=
  mod4_zero_of_mod8_four (5 * p + 1) (step_weight_two_of_mod8 p hp)

theorem t2_first_step_one (m : Nat) (hm : m % 4 = 0 ∨ m % 4 = 2) :
    (5 * (50 * m + 29) + 1) % 4 = 2 := by
  rcases hm with hm0 | hm2
  · exact step_weight_one_of_mod8 (50 * m + 29)
      (Or.inr (t2_parent_mod_eight_zero m hm0))
  · exact step_weight_one_of_mod8 (50 * m + 29)
      (Or.inl (t2_parent_mod_eight_two m hm2))

theorem t2_first_step_two (m : Nat) (hm : m % 4 = 1) :
    (5 * (50 * m + 29) + 1) % 8 = 4 :=
  step_weight_two_of_mod8 (50 * m + 29) (t2_parent_mod_eight_one m hm)

theorem t1_first_step_one (m : Nat) (hm : m % 4 = 0 ∨ m % 4 = 2) :
    (5 * (50 * m + 33) + 1) % 4 = 2 := by
  rcases hm with hm0 | hm2
  · exact step_weight_one_of_mod8 (50 * m + 33)
      (Or.inl (t1_parent_mod_eight_zero m hm0))
  · exact step_weight_one_of_mod8 (50 * m + 33)
      (Or.inr (t1_parent_mod_eight_two m hm2))

theorem t1_first_step_two (m : Nat) (hm : m % 4 = 3) :
    (5 * (50 * m + 33) + 1) % 8 = 4 :=
  step_weight_two_of_mod8 (50 * m + 33) (t1_parent_mod_eight_three m hm)

theorem t2_parent_not_W_class (m : Nat) (hm : m % 4 = 3) :
    8 ∣ 5 * (50 * m + 29) + 1 :=
  eight_dvd_five_mul_add_one_of_mod_eight_three (50 * m + 29)
    (t2_parent_class m hm)

theorem t1_parent_not_W_class (m : Nat) (hm : m % 4 = 1) :
    8 ∣ 5 * (50 * m + 33) + 1 :=
  eight_dvd_five_mul_add_one_of_mod_eight_three (50 * m + 33)
    (t1_parent_class m hm)

/-- Hensel lifting step for the inverse of an odd number modulo
powers of two. -/
theorem invOdd_step (a b N : Nat) (ha : a % 2 = 1)
    (hmod : (a * b) % 2 ^ N = 1) :
    (a * b) % 2 ^ (N + 1) = 1 ∨ (a * (b + 2 ^ N)) % 2 ^ (N + 1) = 1 := by
  by_cases h1 : (a * b) % 2 ^ (N + 1) = 1
  · exact Or.inl h1
  · right
    have hab0 : a * b ≠ 0 := by
      intro hz
      rw [hz] at hmod
      have hm : (0 : Nat) % 2 ^ N = 0 := by simp
      rw [hm] at hmod
      omega
    have hge1 : 1 ≤ a * b := by omega
    have hdvd : 2 ^ N ∣ a * b - 1 :=
      StringFlow.Lte.dvd_sub_one_of_mod_eq_one (a * b) (2 ^ N) (by omega) hmod
    rcases hdvd with ⟨k, hk⟩
    have hab : a * b = 1 + k * 2 ^ N := by
      have hsub := Nat.sub_add_cancel hge1
      rw [hk] at hsub
      rw [Nat.mul_comm] at hsub
      omega
    have hkodd : k % 2 = 1 := by
      by_cases hk1 : k % 2 = 1
      · exact hk1
      · have hkmod0 : k % 2 = 0 := by
          have hlt : k % 2 < 2 := Nat.mod_lt k (by decide)
          omega
        have hdvdM : 2 ^ (N + 1) ∣ k * 2 ^ N := by
          rcases (Nat.dvd_iff_mod_eq_zero.mpr hkmod0) with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          rw [hq]
          have hpow : 2 * 2 ^ N = 2 ^ (N + 1) := by
            rw [show N + 1 = Nat.succ N by omega]
            rw [Nat.pow_succ]
            rw [Nat.mul_comm]
          simp [Nat.mul_assoc, Nat.mul_comm, hpow]
        have hdvd1 : 2 ^ (N + 1) ∣ a * b - 1 := by
          rw [hab]
          have hsub1 : (1 + k * 2 ^ N) - 1 = k * 2 ^ N := by omega
          rw [hsub1]
          exact hdvdM
        have hmod1 : (a * b) % 2 ^ (N + 1) = 1 := by
          rcases hdvd1 with ⟨q, hq⟩
          have hsub := Nat.sub_add_cancel hge1
          rw [hq] at hsub
          rw [Nat.mul_comm] at hsub
          have hdec : a * b = 1 + q * 2 ^ (N + 1) := by omega
          rw [hdec]
          rw [Nat.mul_comm q (2 ^ (N + 1))]
          rw [Nat.add_mul_mod_self_left]
          simp
        exact False.elim (h1 hmod1)
    have hka_even : (k + a) % 2 = 0 := by
      rw [Nat.add_mod, hkodd, ha]
    have hprod : a * (b + 2 ^ N) = 1 + (k + a) * 2 ^ N := by
      rw [Nat.mul_add, hab]
      rw [Nat.add_mul]
      omega
    have hdvdM2 : 2 ^ (N + 1) ∣ (k + a) * 2 ^ N := by
      rcases (Nat.dvd_iff_mod_eq_zero.mpr hka_even) with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hq]
      have hpow : 2 * 2 ^ N = 2 ^ (N + 1) := by
        rw [show N + 1 = Nat.succ N by omega]
        rw [Nat.pow_succ]
        rw [Nat.mul_comm]
      simp [Nat.mul_assoc, Nat.mul_comm, hpow]
    have hres : (a * (b + 2 ^ N)) % 2 ^ (N + 1) = 1 := by
      rcases hdvdM2 with ⟨q2, hq2⟩
      have hdec2 : a * (b + 2 ^ N) = 1 + q2 * 2 ^ (N + 1) := by
        rw [hprod]
        rw [Nat.mul_comm (k + a) (2 ^ N)]
        rw [Nat.mul_comm] at hq2
        rw [hq2]
        rw [Nat.mul_comm q2 (2 ^ (N + 1))]
      rw [hdec2]
      rw [Nat.mul_comm q2 (2 ^ (N + 1))]
      rw [Nat.add_mul_mod_self_left]
      simp
    exact hres

/-- Inverse of an odd number modulo `2^(n+1)`, by Hensel lifting. -/
def invOdd (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 =>
      let b := invOdd a n
      if (a * b) % 2 ^ (n + 2) = 1 then b else b + 2 ^ (n + 1)

/-- Correctness of `invOdd`: `a * invOdd a n ≡ 1 (mod 2^(n+1))`. -/
theorem invOdd_spec (a : Nat) (ha : a % 2 = 1) :
    ∀ n : Nat, (a * invOdd a n) % 2 ^ (n + 1) = 1 := by
  intro n
  induction n with
  | zero =>
      simp [invOdd]
      simpa using ha
  | succ n ih =>
      by_cases hcheck : (a * invOdd a n) % 2 ^ (n + 2) = 1
      · simp [invOdd, hcheck]
      · have hstep := invOdd_step a (invOdd a n) (n + 1) ha ih
        rcases hstep with h1 | h2
        · exfalso
          exact hcheck h1
        · simp [invOdd, hcheck]
          exact h2

/-- `(x+M)%M = x%M`. -/
theorem add_mod_mul_one (x M : Nat) : (x + M) % M = x % M := by
  calc
    (x + M) % M = (x + M * 1) % M := by
        conv =>
          lhs
          lhs
          rw [show M = M * 1 by simp]
    _ = x % M := by rw [Nat.add_mul_mod_self_left]

/-- Wrapped addition `R-A` modulo `M` returns `R` after adding `A`. -/
theorem wrapped_add_mod (R A M : Nat) (hA : A < M) (hR : R < M) (hM : 0 < M) :
    (((R + M - A) % M) + A) % M = R := by
  by_cases hle : A ≤ R
  · have hsub : R + M - A = M + (R - A) := by omega
    have hmodstep : (M + (R - A)) % M = R - A := by
      rw [Nat.add_comm]
      rw [add_mod_mul_one (R - A) M]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsub, hmodstep]
    have hsum : (R - A) + A = R := by omega
    rw [hsum, Nat.mod_eq_of_lt hR]
  · have hlt : R < A := by omega
    have hval : R + M - A = M - (A - R) := by omega
    have hlt2 : M - (A - R) < M := by omega
    have hmod : (M - (A - R)) % M = M - (A - R) := Nat.mod_eq_of_lt hlt2
    have hdec : A = R + (A - R) := by omega
    have hdlt : A - R < M := by omega
    have hd : A - R ≤ M := Nat.le_of_lt hdlt
    have hcancel : M - (A - R) + (A - R) = M := Nat.sub_add_cancel hd
    have hsum' : A + (M - (A - R)) = R + M := by
      rw [hdec]
      have hsub2 : R + (A - R) - R = A - R := by omega
      rw [hsub2]
      rw [Nat.add_assoc]
      rw [Nat.add_comm (A - R) (M - (A - R))]
      rw [hcancel]
    have hsum : (M - (A - R)) + A = R + M := by
      rw [Nat.add_comm]
      exact hsum'
    rw [hval, hmod, hsum]
    rw [add_mod_mul_one R M]
    rw [Nat.mod_eq_of_lt hR]

/-- Cancellation of an odd inverse inside a product modulo `M`. -/
theorem mul_mod_inv (a b inv M : Nat) (h : (a * inv) % M = 1) :
    (a * ((b * inv) % M)) % M = b % M := by
  have hm1 : (a * ((b * inv) % M)) % M = (a * (b * inv)) % M := by
    rw [Nat.mul_mod, Nat.mul_mod]
    simp
  have hm2 : (a * (b * inv)) % M = (b * (a * inv)) % M := by
    calc
      (a * (b * inv)) % M = ((a * b) * inv) % M := by rw [← Nat.mul_assoc]
      _ = ((b * a) * inv) % M := by rw [Nat.mul_comm a b]
      _ = (b * (a * inv)) % M := by rw [Nat.mul_assoc]
  have hm3 : (b * (a * inv)) % M = b % M := by
    rw [Nat.mul_mod, h]
    simp
  rw [hm1, hm2, hm3]

/-- Explicit word representative: the unique residue below `2^(S+3)`
that makes the endpoint C3 congruence hold. -/
def wordRepresentative (w : List Nat) : Nat :=
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  let A := wordA w % M
  let T := ((3 * 2 ^ S) % M + M - A) % M
  let inv := invOdd (5 ^ w.length) (S + 2)
  (T * inv) % M

/-- `wordRepresentative` satisfies the endpoint C3 congruence. -/
theorem wordRepresentative_spec (w : List Nat) :
    (5 ^ w.length * wordRepresentative w + wordA w) %
        2 ^ (StringFlow.wordWeight w + 3) =
      (3 * 2 ^ StringFlow.wordWeight w) %
        2 ^ (StringFlow.wordWeight w + 3) := by
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  let A := wordA w % M
  let T := ((3 * 2 ^ S) % M + M - A) % M
  let inv := invOdd (5 ^ w.length) (S + 2)
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hA : A < M := by
    dsimp [A]
    exact Nat.mod_lt (wordA w) hM
  have hR : (3 * 2 ^ S) % M < M := Nat.mod_lt _ hM
  have hT : T < M := by
    dsimp [T]
    exact Nat.mod_lt _ hM
  have hTadd : (T + A) % M = (3 * 2 ^ S) % M := by
    dsimp [T, A]
    exact wrapped_add_mod ((3 * 2 ^ S) % M) (wordA w % M) M
      (Nat.mod_lt (wordA w) hM) hR hM
  have hinv : (5 ^ w.length * inv) % M = 1 := by
    dsimp [inv]
    exact invOdd_spec (5 ^ w.length)
      (StringFlow.Lte.five_pow_odd w.length) (S + 2)
  have hmain : (5 ^ w.length * wordRepresentative w + wordA w) % M =
      (5 ^ w.length * ((T * inv) % M) + A) % M := by
    dsimp [wordRepresentative, A, T, inv, M, S]
    simp [Nat.add_mod]
  calc
    (5 ^ w.length * wordRepresentative w + wordA w) % M
        = (5 ^ w.length * ((T * inv) % M) + A) % M := hmain
    _ = ((5 ^ w.length * ((T * inv) % M)) % M + A) % M := by
        rw [Nat.add_mod]
        rw [Nat.mod_eq_of_lt hA]
    _ = (T + A) % M := by
        have hmul := mul_mod_inv (5 ^ w.length) T inv M hinv
        rw [hmul]
        rw [Nat.mod_eq_of_lt hT]
    _ = (3 * 2 ^ S) % M := hTadd

/-- The endpoint C3 congruence is sufficient for the word to be valid
and to end at a C3 point. -/
theorem wordValid_of_endpoint_congruence (w : List Nat) (hw : wordOK w) (x : Nat)
    (hx : (5 ^ w.length * x + wordA w) % 2 ^ (StringFlow.wordWeight w + 3) =
          (3 * 2 ^ StringFlow.wordWeight w) % 2 ^ (StringFlow.wordWeight w + 3)) :
    wordValid w x ∧ wordOrbit w x % 8 = 3 := by
  induction w generalizing x with
  | nil =>
      constructor
      · simp [wordValid]
      · simp [wordA, StringFlow.wordWeight] at hx
        simp [wordOrbit]
        exact hx
  | cons t ts ih =>
      let S' := StringFlow.wordWeight ts
      let S := t + S'
      let M := 2 ^ (S + 3)
      let E := 5 ^ (ts.length + 1) * x + wordA (t :: ts)
      let R := 3 * 2 ^ S
      have hE : E % M = R % M := by
        simpa [E, R, M, S, S', StringFlow.wordWeight] using hx
      have hdecomp :
          E = 5 ^ ts.length * (5 * x + 1) + 2 ^ t * wordA ts := by
        dsimp [E]
        rw [wordA]
        have hpow : 5 ^ (ts.length + 1) = 5 * 5 ^ ts.length := by
          rw [show ts.length + 1 = Nat.succ ts.length by omega]
          rw [Nat.pow_succ]
          rw [Nat.mul_comm]
        rw [hpow, Nat.mul_add]
        simp [Nat.mul_assoc, Nat.mul_comm]
        omega
      have hE' : (5 ^ ts.length * (5 * x + 1) + 2 ^ t * wordA ts) % M = R % M := by
        rw [← hdecomp]
        exact hE
      have hMpos : 0 < M := by
        dsimp [M]
        exact Nat.pow_pos (by decide)
      have hdvdM : 2 ^ t ∣ M := by
        dsimp [M, S]
        exact Nat.pow_dvd_pow 2 (by omega)
      have hdvdR : 2 ^ t ∣ R := by
        dsimp [R, S]
        have hts : t ≤ t + StringFlow.wordWeight ts := by omega
        have hd : 2 ^ t ∣ 2 ^ (t + StringFlow.wordWeight ts) :=
          Nat.pow_dvd_pow 2 hts
        exact Nat.dvd_trans hd (Nat.dvd_mul_left (2 ^ (t + StringFlow.wordWeight ts)) 3)
      have hEmod2 : E % 2 ^ t = R % 2 ^ t := by
        calc
          E % 2 ^ t = (E % M) % 2 ^ t := (Nat.mod_mod_of_dvd E hdvdM).symm
          _ = (R % M) % 2 ^ t := by rw [hE]
          _ = R % 2 ^ t := Nat.mod_mod_of_dvd R hdvdM
      have hRmod : R % 2 ^ t = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvdR
      have hEdiv : 2 ^ t ∣ E := by
        rw [Nat.dvd_iff_mod_eq_zero]
        rw [hEmod2, hRmod]
      have hQ : 2 ^ t ∣ 2 ^ t * wordA ts := ⟨wordA ts, rfl⟩
      have hP : 2 ^ t ∣ 5 ^ ts.length * (5 * x + 1) := by
        have hsub : 2 ^ t ∣ E - 2 ^ t * wordA ts := by
          exact Nat.dvd_sub hEdiv hQ
        have hsub' : E - 2 ^ t * wordA ts = 5 ^ ts.length * (5 * x + 1) := by
          rw [hdecomp]
          omega
        simpa [hsub'] using hsub
      have hdiv5 : 2 ^ t ∣ 5 * x + 1 :=
        dvd_two_pow_of_five_pow_mul ts.length t (5 * x + 1) hP
      have hfirst : (5 * x + 1) % 2 ^ t = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv5
      let y := (5 * x + 1) / 2 ^ t
      let E' := 5 ^ ts.length * y + wordA ts
      let R' := 3 * 2 ^ S'
      let M' := 2 ^ (S' + 3)
      have hyeq : 2 ^ t * y = 5 * x + 1 := by
        dsimp [y]
        have h := Nat.div_add_mod (5 * x + 1) (2 ^ t)
        rw [hfirst] at h
        omega
      have hEprod : 2 ^ t * E' = E := by
        dsimp [E', E]
        calc
          2 ^ t * (5 ^ ts.length * y + wordA ts)
              = 5 ^ ts.length * (2 ^ t * y) + 2 ^ t * wordA ts := by
                  rw [Nat.mul_add]
                  simp [Nat.mul_assoc, Nat.mul_comm]
          _ = 5 ^ ts.length * (5 * x + 1) + 2 ^ t * wordA ts := by rw [hyeq]
          _ = E := hdecomp.symm
      have hMprod : 2 ^ t * M' = M := by
        dsimp [M', M, S, S']
        rw [show (t + StringFlow.wordWeight ts) + 3 =
            t + (StringFlow.wordWeight ts + 3) by omega]
        rw [← Nat.pow_add]
      have hRprod : 2 ^ t * R' = R := by
        dsimp [R', R, S, S']
        calc
          2 ^ t * (3 * 2 ^ S') = 3 * (2 ^ t * 2 ^ S') := by
              ac_rfl
          _ = 3 * 2 ^ (t + S') := by rw [Nat.pow_add]
      have hmodmul :
          (2 ^ t * E') % (2 ^ t * M') = (2 ^ t * R') % (2 ^ t * M') := by
        rw [hEprod, hMprod, hRprod]
        exact hE
      have hdiv1 : (2 ^ t * E') % (2 ^ t * M') = 2 ^ t * (E' % M') := by
        exact Nat.mul_mod_mul_left (2 ^ t) E' M'
      have hdiv2 : (2 ^ t * R') % (2 ^ t * M') = 2 ^ t * (R' % M') := by
        exact Nat.mul_mod_mul_left (2 ^ t) R' M'
      have hmul : 2 ^ t * (E' % M') = 2 ^ t * (R' % M') := by
        rw [← hdiv1, ← hdiv2]
        exact hmodmul
      have htail : E' % M' = R' % M' :=
        Nat.mul_left_cancel (Nat.pow_pos (by decide) : 0 < 2 ^ t) hmul
      have hwts : wordOK ts := hw.2
      have hih := ih hwts y htail
      refine ⟨⟨hfirst, hih.1⟩, ?_⟩
      · dsimp [wordOrbit, y]
        exact hih.2

/-- The explicit representative is below the `W` window. -/
theorem wordRepresentative_lt (w : List Nat) :
    wordRepresentative w < 2 ^ (StringFlow.wordWeight w + 3) := by
  let S := StringFlow.wordWeight w
  let M := 2 ^ (S + 3)
  dsimp [wordRepresentative, M, S]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

/-- `wordRepresentative` is valid for its word and ends at C3. -/
theorem wordRepresentative_valid (w : List Nat) (hw : wordOK w) :
    wordValid w (wordRepresentative w) ∧ wordOrbit w (wordRepresentative w) % 8 = 3 := by
  exact wordValid_of_endpoint_congruence w hw (wordRepresentative w)
    (wordRepresentative_spec w)

/-- Representative uniqueness for valid `w`-words ending at C3:
below `2^(S+3)`, `wordValid w x ∧ wordOrbit w x % 8 = 3` iff
`x = wordRepresentative w`.  This is not yet the "first C3 word is
`w`" form of Lemma 34.1; that additionally needs `wordFirst`. -/
theorem word_representative_iff (w : List Nat) (hw : wordOK w) (x : Nat)
    (hx : x < 2 ^ (StringFlow.wordWeight w + 3)) :
    (wordValid w x ∧ wordOrbit w x % 8 = 3) ↔ x = wordRepresentative w := by
  constructor
  · intro h
    have hrep := wordRepresentative_valid w hw
    exact word_representative_unique w x (wordRepresentative w) h.1 hrep.1 h.2 hrep.2
      hx (wordRepresentative_lt w)
  · intro hxeq
    subst x
    exact wordRepresentative_valid w hw

/-- The first C3 word is exactly `w`: every prefix before the end is
not C3, all steps are exact, and the endpoint is C3. -/
def wordFirst : List Nat → Nat → Prop
  | [], x => x % 8 = 3
  | t :: ts, x => x % 8 ≠ 3 ∧ (5 * x + 1) % 2 ^ t = 0 ∧
      wordFirst ts ((5 * x + 1) / 2 ^ t)

theorem odd_after_even (y : Nat) (hy : y % 2 = 0) : (5 * y + 1) % 2 = 1 := by
  rw [Nat.add_mod, Nat.mul_mod, hy]

theorem not_dvd_two_pow_of_odd (n k : Nat) (h : n % 2 = 1) (hk : 1 ≤ k) :
    n % 2 ^ k ≠ 0 := by
  intro hz
  have hdvd : 2 ^ k ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hz
  have hpow : 2 ∣ 2 ^ k := by
    simpa using Nat.pow_dvd_pow 2 hk
  have hdvd2 : 2 ∣ n := Nat.dvd_trans hpow hdvd
  have hn : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd2
  omega

theorem even_not_c3 (y : Nat) (hy : y % 2 = 0) : y % 8 ≠ 3 := by
  intro h
  have hmod : y % 8 % 2 = y % 2 := by
    exact Nat.mod_mod_of_dvd y (by decide : 2 ∣ 8)
  rw [h] at hmod
  simp at hmod
  omega

theorem even_of_c3_step (x t : Nat) (hx : x % 8 = 3) (ht12 : t = 1 ∨ t = 2)
    (hdiv : (5 * x + 1) % 2 ^ t = 0) :
    ((5 * x + 1) / 2 ^ t) % 2 = 0 := by
  rcases ht12 with ht1 | ht2
  · subst t
    have hdec : x = 8 * (x / 8) + 3 := by
      have h := Nat.div_add_mod x 8
      rw [hx] at h
      omega
    have hlin : 5 * (8 * (x / 8) + 3) + 1 = 8 * (5 * (x / 8) + 2) := by omega
    have hyeq : 2 * ((5 * x + 1) / 2) = 5 * x + 1 := by
      have h := Nat.div_add_mod (5 * x + 1) 2
      rw [hdiv] at h
      omega
    have hprod : 2 * (4 * (5 * (x / 8) + 2)) = 5 * x + 1 := by
      calc
        2 * (4 * (5 * (x / 8) + 2)) = 8 * (5 * (x / 8) + 2) := by omega
        _ = 5 * x + 1 := by
            conv =>
              rhs
              rw [hdec]
            exact hlin.symm
    have hquot : (5 * x + 1) / 2 = 4 * (5 * (x / 8) + 2) := by
      have h2 : 2 * ((5 * x + 1) / 2) = 2 * (4 * (5 * (x / 8) + 2)) := by
        rw [hyeq, hprod]
      exact Nat.mul_left_cancel (by decide : 0 < 2) h2
    rw [hquot]
    rw [Nat.mul_mod]
    simp
  · subst t
    have hdec : x = 8 * (x / 8) + 3 := by
      have h := Nat.div_add_mod x 8
      rw [hx] at h
      omega
    have hlin : 5 * (8 * (x / 8) + 3) + 1 = 8 * (5 * (x / 8) + 2) := by omega
    have hyeq : 4 * ((5 * x + 1) / 4) = 5 * x + 1 := by
      have h := Nat.div_add_mod (5 * x + 1) 4
      rw [hdiv] at h
      omega
    have hprod : 4 * (2 * (5 * (x / 8) + 2)) = 5 * x + 1 := by
      calc
        4 * (2 * (5 * (x / 8) + 2)) = 8 * (5 * (x / 8) + 2) := by omega
        _ = 5 * x + 1 := by
            conv =>
              rhs
              rw [hdec]
            exact hlin.symm
    have hquot : (5 * x + 1) / 4 = 2 * (5 * (x / 8) + 2) := by
      have h4 : 4 * ((5 * x + 1) / 4) = 4 * (2 * (5 * (x / 8) + 2)) := by
        rw [hyeq, hprod]
      exact Nat.mul_left_cancel (by decide : 0 < 4) h4
    rw [hquot]
    rw [Nat.mul_mod]
    simp

/-- If the first C3 word is `w`, then the word is valid and ends at
C3. -/
theorem wordValid_of_wordFirst (w : List Nat) (x : Nat) (h : wordFirst w x) :
    wordValid w x ∧ wordOrbit w x % 8 = 3 := by
  induction w generalizing x with
  | nil =>
      constructor
      · simp [wordValid]
      · simpa [wordFirst, wordOrbit] using h
  | cons t ts ih =>
      rcases h with ⟨hxne, hdiv, htail⟩
      have ih' := ih ((5 * x + 1) / 2 ^ t) htail
      constructor
      · exact ⟨hdiv, ih'.1⟩
      · simpa [wordOrbit] using ih'.2

/-- For words over `{1,2}`, a valid word ending at C3 has no earlier
C3 prefix, so its first C3 word is exactly `w`. -/
theorem wordFirst_of_wordValid (w : List Nat) (x : Nat)
    (hw : wordOK w) (hpos : ∀ t ∈ w, 1 ≤ t)
    (hvalid : wordValid w x) (hend : wordOrbit w x % 8 = 3) :
    wordFirst w x := by
  induction w generalizing x with
  | nil =>
      simpa [wordFirst, wordOrbit] using hend
  | cons t ts ih =>
      have ht1 : 1 ≤ t := hpos t (by simp)
      have ht2 : t ≤ 2 := hw.1
      have ht12 : t = 1 ∨ t = 2 := by omega
      refine ⟨?hxne, hvalid.1, ?htail⟩
      · intro hx3
        have hy : ((5 * x + 1) / 2 ^ t) % 2 = 0 :=
          even_of_c3_step x t hx3 ht12 hvalid.1
        cases ts with
        | nil =>
            have hyeq : wordOrbit [t] x = (5 * x + 1) / 2 ^ t := by
              simp [wordOrbit]
            have hnot : ((5 * x + 1) / 2 ^ t) % 8 ≠ 3 := even_not_c3 _ hy
            rw [hyeq] at hend
            exact hnot hend
        | cons t2 ts2 =>
            have htailValid : wordValid (t2 :: ts2) ((5 * x + 1) / 2 ^ t) :=
              hvalid.2
            have hdiv2 : (5 * ((5 * x + 1) / 2 ^ t) + 1) % 2 ^ t2 = 0 :=
              htailValid.1
            have hodd : (5 * ((5 * x + 1) / 2 ^ t) + 1) % 2 = 1 :=
              odd_after_even _ hy
            have ht2ge : 1 ≤ t2 := hpos t2 (by simp)
            have hne : (5 * ((5 * x + 1) / 2 ^ t) + 1) % 2 ^ t2 ≠ 0 :=
              not_dvd_two_pow_of_odd _ t2 hodd ht2ge
            exact hne hdiv2
      · have hend_tail : wordOrbit ts ((5 * x + 1) / 2 ^ t) % 8 = 3 := by
          simpa [wordOrbit] using hend
        exact ih ((5 * x + 1) / 2 ^ t) hw.2
          (fun a ha => hpos a (List.mem_cons_of_mem t ha)) hvalid.2 hend_tail

/-- Lemma 34.1: below `2^(S+3)`, the first C3 word is `w` if and only
if `x` is the explicit representative. -/
theorem word_representative_iff_first (w : List Nat) (hw : wordOK w)
    (hpos : ∀ t ∈ w, 1 ≤ t) (x : Nat)
    (hx : x < 2 ^ (StringFlow.wordWeight w + 3)) :
    wordFirst w x ↔ x = wordRepresentative w := by
  constructor
  · intro h
    have hv := wordValid_of_wordFirst w x h
    exact (word_representative_iff w hw x hx).mp hv
  · intro hxeq
    subst x
    have hv := wordRepresentative_valid w hw
    exact wordFirst_of_wordValid w (wordRepresentative w) hw hpos hv.1 hv.2

/-- CRT over `8` and `5`: residue `3 mod 8`, `3 mod 5` is `3 mod 40`. -/
theorem c3_mod40_of_mod8_mod5 (y : Nat) (h8 : y % 8 = 3) (h5 : y % 5 = 3) :
    y % 40 = 3 := by
  have hr : y % 40 < 40 := Nat.mod_lt y (by decide)
  have hr8 : (y % 40) % 8 = 3 := by
    have hdec : y = 40 * (y / 40) + y % 40 := by
      exact (Nat.div_add_mod y 40).symm
    rw [hdec] at h8
    have hmod8 : (40 * (y / 40) + y % 40) % 8 = (y % 40) % 8 := by
      rw [show 40 * (y / 40) = (y / 40 * 5) * 8 by omega]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_right (y % 40) (y / 40 * 5) 8
    rw [hmod8] at h8
    exact h8
  have hr5 : (y % 40) % 5 = 3 := by
    have hdec : y = 40 * (y / 40) + y % 40 := by
      exact (Nat.div_add_mod y 40).symm
    rw [hdec] at h5
    have hmod5 : (40 * (y / 40) + y % 40) % 5 = (y % 40) % 5 := by
      rw [show 40 * (y / 40) = (y / 40 * 8) * 5 by omega]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_right (y % 40) (y / 40 * 8) 5
    rw [hmod5] at h5
    exact h5
  omega

/-- CRT over `8` and `5`: residue `3 mod 8`, `4 mod 5` is `19 mod 40`. -/
theorem c3_mod40_of_mod8_mod4 (y : Nat) (h8 : y % 8 = 3) (h5 : y % 5 = 4) :
    y % 40 = 19 := by
  have hr : y % 40 < 40 := Nat.mod_lt y (by decide)
  have hr8 : (y % 40) % 8 = 3 := by
    have hdec : y = 40 * (y / 40) + y % 40 := by
      exact (Nat.div_add_mod y 40).symm
    rw [hdec] at h8
    have hmod8 : (40 * (y / 40) + y % 40) % 8 = (y % 40) % 8 := by
      rw [show 40 * (y / 40) = (y / 40 * 5) * 8 by omega]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_right (y % 40) (y / 40 * 5) 8
    rw [hmod8] at h8
    exact h8
  have hr5 : (y % 40) % 5 = 4 := by
    have hdec : y = 40 * (y / 40) + y % 40 := by
      exact (Nat.div_add_mod y 40).symm
    rw [hdec] at h5
    have hmod5 : (40 * (y / 40) + y % 40) % 5 = (y % 40) % 5 := by
      rw [show 40 * (y / 40) = (y / 40 * 8) * 5 by omega]
      rw [Nat.add_comm]
      exact Nat.add_mul_mod_self_right (y % 40) (y / 40 * 8) 5
    rw [hmod5] at h5
    exact h5
  omega

/-- If `2y == 1 (mod 5)`, then `y == 3 (mod 5)`. -/
theorem two_mul_mod_five_eq_one_imp (y : Nat) (h : (2 * y) % 5 = 1) :
    y % 5 = 3 := by
  have hr : y % 5 < 5 := Nat.mod_lt y (by decide)
  omega

/-- If `4y == 1 (mod 5)`, then `y == 4 (mod 5)`. -/
theorem four_mul_mod_five_eq_one_imp (y : Nat) (h : (4 * y) % 5 = 1) :
    y % 5 = 4 := by
  have hr : y % 5 < 5 := Nat.mod_lt y (by decide)
  omega

/-- The final orbit residue mod 5 is determined by the last step:
`wordLast = 1` forces `y == 3 (mod 5)`. -/
theorem wordOrbit_mod_five_of_last_one (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hlast : wordLast w = 1) :
    wordOrbit w x % 5 = 3 := by
  induction w generalizing x with
  | nil =>
      simp [wordLast] at hlast
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        have ht : t = 1 := by
          simp [wordLast] at hlast
          exact hlast
        have hdiv : (5 * x + 1) % 2 ^ t = 0 := hvalid.1
        subst t
        let y := (5 * x + 1) / 2
        have hyeq : 2 * y = 5 * x + 1 := by
          dsimp [y]
          have h := Nat.div_add_mod (5 * x + 1) 2
          rw [hdiv] at h
          omega
        have hmod : (2 * y) % 5 = 1 := by
          rw [hyeq]
          rw [Nat.add_mod, Nat.mul_mod]
          simp
        exact two_mul_mod_five_eq_one_imp y hmod
      · have hvalid_tail : wordValid ts ((5 * x + 1) / 2 ^ t) := hvalid.2
        have hlast_tail : wordLast ts = 1 := by
          simp [wordLast] at hlast
          exact hlast
        have hy : wordOrbit (t :: ts) x = wordOrbit ts ((5 * x + 1) / 2 ^ t) := by
          simp [wordOrbit]
        rw [hy]
        exact ih ((5 * x + 1) / 2 ^ t) hvalid_tail hlast_tail

/-- The final orbit residue mod 5 is determined by the last step:
`wordLast = 2` forces `y == 4 (mod 5)`. -/
theorem wordOrbit_mod_five_of_last_two (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hlast : wordLast w = 2) :
    wordOrbit w x % 5 = 4 := by
  induction w generalizing x with
  | nil =>
      simp [wordLast] at hlast
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        have ht : t = 2 := by
          simp [wordLast] at hlast
          exact hlast
        have hdiv : (5 * x + 1) % 2 ^ t = 0 := hvalid.1
        subst t
        let y := (5 * x + 1) / 4
        have hyeq : 4 * y = 5 * x + 1 := by
          dsimp [y]
          have h := Nat.div_add_mod (5 * x + 1) 4
          rw [hdiv] at h
          omega
        have hmod : (4 * y) % 5 = 1 := by
          rw [hyeq]
          rw [Nat.add_mod, Nat.mul_mod]
          simp
        exact four_mul_mod_five_eq_one_imp y hmod
      · have hvalid_tail : wordValid ts ((5 * x + 1) / 2 ^ t) := hvalid.2
        have hlast_tail : wordLast ts = 2 := by
          simp [wordLast] at hlast
          exact hlast
        have hy : wordOrbit (t :: ts) x = wordOrbit ts ((5 * x + 1) / 2 ^ t) := by
          simp [wordOrbit]
        rw [hy]
        exact ih ((5 * x + 1) / 2 ^ t) hvalid_tail hlast_tail

/-- Lemma 35.1, `t=1` branch: a valid word ending at C3 with last
step `1` has final orbit `3 mod 40`. -/
theorem word_endpoint_crt_last_one (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hend : wordOrbit w x % 8 = 3)
    (hlast : wordLast w = 1) :
    wordOrbit w x % 40 = 3 := by
  exact c3_mod40_of_mod8_mod5 (wordOrbit w x) hend
    (wordOrbit_mod_five_of_last_one w x hvalid hlast)

/-- Lemma 35.1, `t=2` branch: a valid word ending at C3 with last
step `2` has final orbit `19 mod 40`. -/
theorem word_endpoint_crt_last_two (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hend : wordOrbit w x % 8 = 3)
    (hlast : wordLast w = 2) :
    wordOrbit w x % 40 = 19 := by
  exact c3_mod40_of_mod8_mod4 (wordOrbit w x) hend
    (wordOrbit_mod_five_of_last_two w x hvalid hlast)

/-- Lemma 35.1, mod 80: a valid word ending at C3 with last step `1`
has final orbit `3` or `43 mod 80`; with last step `2`, `19` or `59`. -/
theorem word_endpoint_mod80 (w : List Nat) (x : Nat)
    (hvalid : wordValid w x) (hend : wordOrbit w x % 8 = 3) :
    (wordLast w = 1 → wordOrbit w x % 80 = 3 ∨ wordOrbit w x % 80 = 43) ∧
    (wordLast w = 2 → wordOrbit w x % 80 = 19 ∨ wordOrbit w x % 80 = 59) := by
  constructor
  · intro hlast
    have h40 : wordOrbit w x % 40 = 3 :=
      word_endpoint_crt_last_one w x hvalid hend hlast
    let r := wordOrbit w x % 80
    have hlt : r < 80 := Nat.mod_lt (wordOrbit w x) (by decide : 0 < 80)
    have h40r : r % 40 = 3 := by
      have hmod := (Nat.mod_mod_of_dvd (wordOrbit w x) (by decide : 40 ∣ 80)).symm
      dsimp [r]
      rw [← hmod]
      exact h40
    have hdec : r = 40 * (r / 40) + r % 40 := by
      have h := Nat.div_add_mod r 40
      simpa [Nat.mul_comm] using h.symm
    change r = 3 ∨ r = 43
    rw [hdec, h40r]
    have hq : r / 40 = 0 ∨ r / 40 = 1 := by
      have hqle : r / 40 < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 40)]
        omega
      omega
    rcases hq with hq0 | hq1
    · left
      rw [hq0]
    · right
      rw [hq1]
  · intro hlast
    have h40 : wordOrbit w x % 40 = 19 :=
      word_endpoint_crt_last_two w x hvalid hend hlast
    let r := wordOrbit w x % 80
    have hlt : r < 80 := Nat.mod_lt (wordOrbit w x) (by decide : 0 < 80)
    have h40r : r % 40 = 19 := by
      have hmod := (Nat.mod_mod_of_dvd (wordOrbit w x) (by decide : 40 ∣ 80)).symm
      dsimp [r]
      rw [← hmod]
      exact h40
    have hdec : r = 40 * (r / 40) + r % 40 := by
      have h := Nat.div_add_mod r 40
      simpa [Nat.mul_comm] using h.symm
    change r = 19 ∨ r = 59
    rw [hdec, h40r]
    have hq : r / 40 = 0 ∨ r / 40 = 1 := by
      have hqle : r / 40 < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 40)]
        omega
      omega
    rcases hq with hq0 | hq1
    · left
      rw [hq0]
    · right
      rw [hq1]

/-- If `y == 3 (mod 8)`, then `2^S*y == 3*2^S (mod 2^(S+3))`. -/
theorem mul_two_pow_mod_of_mod8 (S y : Nat) (hy : y % 8 = 3) :
    (2 ^ S * y) % 2 ^ (S + 3) = (3 * 2 ^ S) % 2 ^ (S + 3) := by
  have hdec : y = 8 * (y / 8) + 3 := by
    have h := Nat.div_add_mod y 8
    rw [hy] at h
    omega
  have hpow : 2 ^ (S + 3) = 2 ^ S * 8 := by
    rw [show 8 = 2 ^ 3 by rfl]
    rw [Nat.pow_add]
  calc
    (2 ^ S * y) % 2 ^ (S + 3)
        = (2 ^ S * (8 * (y / 8) + 3)) % 2 ^ (S + 3) := by
            rw [show 2 ^ S * y = 2 ^ S * (8 * (y / 8) + 3) by rw [← hdec]]
    _ = (2 ^ S * 3 + 2 ^ S * (8 * (y / 8))) % 2 ^ (S + 3) := by
            rw [Nat.mul_add, Nat.add_comm]
    _ = (3 * 2 ^ S + 2 ^ (S + 3) * (y / 8)) % 2 ^ (S + 3) := by
            have hswap : 2 ^ S * (8 * (y / 8)) = 2 ^ (S + 3) * (y / 8) := by
              rw [← Nat.mul_assoc]
              rw [hpow.symm]
            rw [Nat.mul_comm 3 (2 ^ S), hswap]
    _ = (3 * 2 ^ S) % 2 ^ (S + 3) := by
            rw [show 2 ^ (S + 3) * (y / 8) = (y / 8) * 2 ^ (S + 3) by
              rw [Nat.mul_comm]]
            exact Nat.add_mul_mod_self_right (3 * 2 ^ S) (y / 8) (2 ^ (S + 3))

/-- The affine orbit value `2^S*y` with `y == 3 (mod 8)` makes the word
valid and forces the C3 endpoint. -/
theorem word_valid_of_orbit_affine (w : List Nat) (hw : wordOK w) (x y : Nat)
    (h : 5 ^ w.length * x + wordA w = 2 ^ StringFlow.wordWeight w * y)
    (hy : y % 8 = 3) :
    wordValid w x ∧ wordOrbit w x % 8 = 3 := by
  have hx : (5 ^ w.length * x + wordA w) % 2 ^ (StringFlow.wordWeight w + 3) =
      (3 * 2 ^ StringFlow.wordWeight w) % 2 ^ (StringFlow.wordWeight w + 3) := by
    rw [h]
    exact mul_two_pow_mod_of_mod8 (StringFlow.wordWeight w) y hy
  exact wordValid_of_endpoint_congruence w hw x hx

/-- If the affine orbit value equals `2^S*y` with `y == 3 (mod 8)`, the
word start is valid and ends at C3. -/
theorem word_valid_of_survivor (w : List Nat) (hw : wordOK w) (B y : Nat)
    (h : 2 ^ StringFlow.wordWeight w * y = 5 ^ w.length * B + wordA w)
    (hy : y % 8 = 3) :
    wordValid w B ∧ wordOrbit w B % 8 = 3 :=
  word_valid_of_orbit_affine w hw B y h.symm hy

theorem mod8_of_3_add_40_mul (q : Nat) : (3 + 40 * q) % 8 = 3 := by
  rw [show 40 * q = (5 * q) * 8 by omega]
  rw [Nat.add_mul_mod_self_right 3 (5 * q) 8]

theorem mod8_of_19_add_40_mul (q : Nat) : (19 + 40 * q) % 8 = 3 := by
  rw [show 19 + 40 * q = 3 + (2 + 5 * q) * 8 by omega]
  rw [Nat.add_mul_mod_self_right 3 (2 + 5 * q) 8]

theorem word_survivor_rev_last_one (w : List Nat) (B : Nat)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hlast : wordLast w = 1) :
    ∃ q, 2 ^ StringFlow.wordWeight w * (3 + 40 * q) = 5 ^ w.length * B + wordA w := by
  let y := wordOrbit w B
  have hy40 : y % 40 = 3 := by
    dsimp [y]
    exact word_endpoint_crt_last_one w B hvalid hend hlast
  have hdec : y = 40 * (y / 40) + 3 := by
    have h := Nat.div_add_mod y 40
    rw [hy40] at h
    omega
  refine ⟨y / 40, ?_⟩
  have hid : 2 ^ StringFlow.wordWeight w * y = 5 ^ w.length * B + wordA w := by
    dsimp [y]
    exact word_orbit_identity w B hvalid
  rw [hdec] at hid
  rw [Nat.add_comm] at hid
  exact hid

theorem word_survivor_rev_last_two (w : List Nat) (B : Nat)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hlast : wordLast w = 2) :
    ∃ q, 2 ^ StringFlow.wordWeight w * (19 + 40 * q) = 5 ^ w.length * B + wordA w := by
  let y := wordOrbit w B
  have hy40 : y % 40 = 19 := by
    dsimp [y]
    exact word_endpoint_crt_last_two w B hvalid hend hlast
  have hdec : y = 40 * (y / 40) + 19 := by
    have h := Nat.div_add_mod y 40
    rw [hy40] at h
    omega
  refine ⟨y / 40, ?_⟩
  have hid : 2 ^ StringFlow.wordWeight w * y = 5 ^ w.length * B + wordA w := by
    dsimp [y]
    exact word_orbit_identity w B hvalid
  rw [hdec] at hid
  rw [Nat.add_comm] at hid
  exact hid

/-- Corollary 35.2, `t=1` branch: a start is a valid `w`-word ending
at C3 iff its affine orbit value comes from endpoint `3 + 40q`. -/
theorem word_survivor_iff_last_one (w : List Nat) (hw : wordOK w) (B : Nat)
    (hlast : wordLast w = 1) :
    (wordValid w B ∧ wordOrbit w B % 8 = 3) ↔
      ∃ q, 2 ^ StringFlow.wordWeight w * (3 + 40 * q) = 5 ^ w.length * B + wordA w := by
  constructor
  · intro h
    exact word_survivor_rev_last_one w B h.1 h.2 hlast
  · rintro ⟨q, hq⟩
    exact word_valid_of_survivor w hw B (3 + 40 * q) hq (mod8_of_3_add_40_mul q)

/-- Corollary 35.2, `t=2` branch: a start is a valid `w`-word ending
at C3 iff its affine orbit value comes from endpoint `19 + 40q`. -/
theorem word_survivor_iff_last_two (w : List Nat) (hw : wordOK w) (B : Nat)
    (hlast : wordLast w = 2) :
    (wordValid w B ∧ wordOrbit w B % 8 = 3) ↔
      ∃ q, 2 ^ StringFlow.wordWeight w * (19 + 40 * q) = 5 ^ w.length * B + wordA w := by
  constructor
  · intro h
    exact word_survivor_rev_last_two w B h.1 h.2 hlast
  · rintro ⟨q, hq⟩
    exact word_valid_of_survivor w hw B (19 + 40 * q) hq (mod8_of_19_add_40_mul q)

/-- Balance inequality for the survivor parameterization. -/
theorem survivor_balance_ge (P Q A y0 m q : Nat)
    (hm : P * y0 + 40 * P * q = 40 * Q * m + 23 * Q + A)
    (hpos : 23 * Q + A ≤ P * y0) :
    P * q ≤ Q * m := by
  have h2 : 40 * Q * m ≥ 40 * P * q := by omega
  have h2' : 40 * (P * q) ≤ 40 * (Q * m) := by
    simpa [Nat.mul_assoc] using h2
  exact Nat.le_of_mul_le_mul_left h2' (by decide : 0 < 40)

/-- Balance equation for the survivor parameterization. -/
theorem survivor_balance_eq (P Q A y0 m q : Nat)
    (hm : P * y0 + 40 * P * q = 40 * Q * m + 23 * Q + A)
    (hpos : 23 * Q + A ≤ P * y0) (_hge : P * q ≤ Q * m) :
    40 * (Q * m - P * q) = P * y0 - A - 23 * Q := by
  have h40eq : 40 * (Q * m - P * q) = 40 * Q * m - 40 * P * q := by
    rw [Nat.mul_sub_left_distrib]
    conv =>
      lhs
      lhs
      rw [← Nat.mul_assoc]
    conv =>
      lhs
      rhs
      rw [← Nat.mul_assoc]
  rw [h40eq]
  omega

/-- Algebraic core of the survivor formula: expanding `B = 40m+23`
in the affine orbit equation gives the balance equation. -/
theorem word_survivor_m_equation (w : List Nat) (B m y0 q : Nat)
    (hB : B = 40 * m + 23)
    (hq : 2 ^ StringFlow.wordWeight w * (y0 + 40 * q) =
      5 ^ w.length * B + wordA w) :
    2 ^ StringFlow.wordWeight w * y0 + 40 * 2 ^ StringFlow.wordWeight w * q =
      40 * 5 ^ w.length * m + 23 * 5 ^ w.length + wordA w := by
  rw [hB] at hq
  have hleft : 2 ^ StringFlow.wordWeight w * (y0 + 40 * q) =
      2 ^ StringFlow.wordWeight w * y0 + 40 * 2 ^ StringFlow.wordWeight w * q := by
    rw [Nat.mul_add]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have hright : 5 ^ w.length * (40 * m + 23) + wordA w =
      40 * 5 ^ w.length * m + 23 * 5 ^ w.length + wordA w := by
    rw [Nat.mul_add]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  rw [hleft, hright] at hq
  exact hq

/-- Forward direction of Corollary 35.4: every survivor
`B = 40m+23` is parameterized by
`m = (2^S*q + N/40)/5^L` for some integer `q`, provided the balance
`N = 2^S*y0 - A_L - 23*5^L` is nonnegative. -/
theorem word_survivor_m_formula_general (w : List Nat) (B m y0 : Nat)
    (hB : B = 40 * m + 23)
    (hsur : ∃ q, 2 ^ StringFlow.wordWeight w * (y0 + 40 * q) =
      5 ^ w.length * B + wordA w)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * y0) :
    ∃ q, m = (2 ^ StringFlow.wordWeight w * q +
               (2 ^ StringFlow.wordWeight w * y0 - wordA w - 23 * 5 ^ w.length) / 40) /
             5 ^ w.length := by
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
  refine ⟨q, ?_⟩
  rw [hNdiv]
  rw [Nat.mul_div_right m (Nat.pow_pos (by decide) : 0 < Q)]

/-- Corollary 35.4, `t=1` branch: the forward `m` formula with
endpoint `y0=3`. -/
theorem word_survivor_m_formula_last_one (w : List Nat) (B m : Nat)
    (hB : B = 40 * m + 23) (hlast : wordLast w = 1)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * 3) :
    ∃ q, m = (2 ^ StringFlow.wordWeight w * q +
               (2 ^ StringFlow.wordWeight w * 3 - wordA w - 23 * 5 ^ w.length) / 40) /
             5 ^ w.length :=
  word_survivor_m_formula_general w B m 3 hB
    (word_survivor_rev_last_one w B hvalid hend hlast) hpos

/-- Corollary 35.4, `t=2` branch: the forward `m` formula with
endpoint `y0=19`. -/
theorem word_survivor_m_formula_last_two (w : List Nat) (B m : Nat)
    (hB : B = 40 * m + 23) (hlast : wordLast w = 2)
    (hvalid : wordValid w B) (hend : wordOrbit w B % 8 = 3)
    (hpos : 23 * 5 ^ w.length + wordA w ≤ 2 ^ StringFlow.wordWeight w * 19) :
    ∃ q, m = (2 ^ StringFlow.wordWeight w * q +
               (2 ^ StringFlow.wordWeight w * 19 - wordA w - 23 * 5 ^ w.length) / 40) /
             5 ^ w.length :=
  word_survivor_m_formula_general w B m 19 hB
    (word_survivor_rev_last_two w B hvalid hend hlast) hpos

end StringFlow.Word
