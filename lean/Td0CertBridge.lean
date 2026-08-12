import StageOneScan
import Td1Interp

/-!
# TD-0 certificate bridge

This module connects the stage-one word certificate in
`StageOneScan.lean` to the chain numerator used by `Td0Final.lean`.
The bridge is built in layers:

1. `auOf` is exactly the GC chain numerator `chainA`;
2. the B-family chain list is a singleton equal to `A_max,5`;
3. the per-word certificate extraction is lifted from the per-triple
   scan.
-/

namespace StringFlow

/-- The accumulator form of `auOf` satisfies
`auOfAux A W ts = 5^len * A + 2^W * chainA ts`. -/
theorem auOfAux_eq (A W : Nat) (ts : List Nat) :
    auOfAux A W ts = 5 ^ ts.length * A + 2 ^ W * StringFlow.GC.chainA ts := by
  induction ts generalizing A W with
  | nil => simp [auOfAux, StringFlow.GC.chainA]
  | cons t ts ih =>
      change auOfAux (5 * A + 2 ^ W) (W + t) ts =
        5 ^ (t :: ts).length * A + 2 ^ W * StringFlow.GC.chainA (t :: ts)
      rw [ih]
      simp [StringFlow.GC.chainA, Nat.pow_succ, Nat.pow_add]
      ring

/-- `auOf` is the GC chain numerator. -/
theorem auOf_eq_chainA (ts : List Nat) :
    auOf ts = StringFlow.GC.chainA ts := by
  unfold auOf
  simpa using (auOfAux_eq 0 0 ts)

/-- `WordWindow.wordA` is the same chain numerator as `GC.chainA`. -/
theorem wordA_eq_chainA (w : List Nat) :
    StringFlow.Word.wordA w = StringFlow.GC.chainA w := by
  induction w with
  | nil => simp [StringFlow.Word.wordA, StringFlow.GC.chainA]
  | cons t ts ih =>
      simp [StringFlow.Word.wordA, StringFlow.GC.chainA, ih]

/-- `auOf` agrees with the word-window chain numerator. -/
theorem auOf_eq_wordA (w : List Nat) :
    auOf w = StringFlow.Word.wordA w := by
  rw [auOf_eq_chainA, wordA_eq_chainA]

/-- The word-orbit identity, specialized to `M0 = wordOrbit w m`. -/
theorem rising_equation_of_wordValid (w : List Nat) (m M0 : Nat)
    (h : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0) :
    2 ^ StringFlow.wordWeight w * M0 =
      5 ^ w.length * m + StringFlow.Word.wordA w := by
  rw [← hM0]
  exact StringFlow.Word.word_orbit_identity w m h

/-- Same, with `wordA` written as the GC chain numerator. -/
theorem rising_equation_chainA (w : List Nat) (m M0 : Nat)
    (h : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0) :
    2 ^ StringFlow.wordWeight w * M0 =
      5 ^ w.length * m + StringFlow.GC.chainA w := by
  rw [← wordA_eq_chainA]
  exact rising_equation_of_wordValid w m M0 h hM0

/-- Combining the rising equation with the C3 chain closed form gives
the global cycle equation (52.3), in additive form. -/
theorem cycle_equation_of_rising_and_chain
    (L Q S T : Nat) (m M0 Achain Au : Nat)
    (hrise : 2 ^ S * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain) :
    2 ^ (S + T) * m =
      5 ^ (L + Q) * m + 5 ^ Q * Au + 2 ^ S * Achain := by
  have h1 : 2 ^ (S + T) * m =
      2 ^ S * 5 ^ Q * M0 + 2 ^ S * Achain := by
    rw [Nat.pow_add]
    calc
      (2 ^ S * 2 ^ T) * m = 2 ^ S * (2 ^ T * m) := by rw [Nat.mul_assoc]
      _ = 2 ^ S * (5 ^ Q * M0 + Achain) := by rw [hchain]
      _ = 2 ^ S * 5 ^ Q * M0 + 2 ^ S * Achain := by
          rw [Nat.mul_add]
          ac_rfl
  have h2 : 2 ^ S * 5 ^ Q * M0 =
      5 ^ (L + Q) * m + 5 ^ Q * Au := by
    rw [Nat.pow_add]
    have h' : 5 ^ Q * (2 ^ S * M0) = 5 ^ Q * (5 ^ L * m + Au) := by
      rw [hrise]
    nlinarith [h']
  calc
    2 ^ (S + T) * m = 2 ^ S * 5 ^ Q * M0 + 2 ^ S * Achain := h1
    _ = (5 ^ (L + Q) * m + 5 ^ Q * Au) + 2 ^ S * Achain := by rw [h2]
    _ = 5 ^ (L + Q) * m + 5 ^ Q * Au + 2 ^ S * Achain := by omega

/-- A positive cycle equation forces `5^(L+Q) < 2^(S+T)`. -/
theorem pow_lt_of_cycle_equation (L Q S T m A : Nat)
    (h : 2 ^ (S + T) * m = 5 ^ (L + Q) * m + A)
    (hA : 0 < A) :
    5 ^ (L + Q) < 2 ^ (S + T) := by
  have hlt : 5 ^ (L + Q) * m < 2 ^ (S + T) * m := by
    rw [h]
    omega
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- The upper power inequality `2^(S+T) < 2 * 5^(L+Q)` is equivalent
to the total numerator being below `5^(L+Q) * m`. -/
theorem pow_two_lt_iff_numerator_lt (L Q S T m A : Nat)
    (h : 2 ^ (S + T) * m = 5 ^ (L + Q) * m + A) (hm : 0 < m) :
    2 ^ (S + T) < 2 * 5 ^ (L + Q) ↔ A < 5 ^ (L + Q) * m := by
  have hrewrite : 2 * 5 ^ (L + Q) * m =
      5 ^ (L + Q) * m + 5 ^ (L + Q) * m := by ring
  constructor
  · intro hlt
    have hltm : (2 ^ (S + T)) * m < (2 * 5 ^ (L + Q)) * m :=
      Nat.mul_lt_mul_of_pos_right hlt hm
    have hltm' : 5 ^ (L + Q) * m + A < 2 * 5 ^ (L + Q) * m := by
      rwa [h] at hltm
    rw [hrewrite] at hltm'
    omega
  · intro hA
    have hlt : 5 ^ (L + Q) * m + A < 2 * 5 ^ (L + Q) * m := by
      rw [hrewrite]
      omega
    have hlt' : 2 ^ (S + T) * m < 2 * 5 ^ (L + Q) * m := by
      rwa [← h] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt'

/-- From the rising and chain equations, `tCeil(L+Q) <= S+T` once the
total numerator is positive and `P` is in the certified range. -/
theorem tCeil_le_total_of_cycle (L Q S T m M0 Au Achain : Nat)
    (hrise : 2 ^ S * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hA : 0 < Achain)
    (hP9 : 9 ≤ L + Q) (hP205 : L + Q < 205) :
    StringFlow.tCeil (L + Q) ≤ S + T := by
  have hcyc := cycle_equation_of_rising_and_chain L Q S T m M0 Achain Au hrise hchain
  have hcyc' : 2 ^ (S + T) * m =
      5 ^ (L + Q) * m + (5 ^ Q * Au + 2 ^ S * Achain) := by
    simpa [Nat.add_assoc] using hcyc
  have hpos : 0 < 5 ^ Q * Au + 2 ^ S * Achain := by
    have h2 : 0 < 2 ^ S * Achain :=
      Nat.mul_pos (Nat.pow_pos (show 0 < 2 by decide)) hA
    omega
  have hlt := pow_lt_of_cycle_equation L Q S T m
    (5 ^ Q * Au + 2 ^ S * Achain) hcyc' hpos
  exact StringFlow.tCeil_le_of_pow_lt (L + Q) (S + T) hP9 hP205 hlt

/-- The B-family chain-value list is a singleton. -/
theorem chainAValsB_singleton (Q : Nat) :
    chainAVals 2 Q =
      [StringFlow.GC.chainA
        ([5] ++ (List.range (Q - 1)).map (fun _ => 3))] := by
  unfold chainAVals
  simp
  rw [auOf_eq_chainA]

/-- Minimum of a singleton list. -/
theorem listMin_singleton (x : Nat) : listMin [x] = x := by
  simp [listMin]

/-- Maximum of a singleton list. -/
theorem listMax_singleton (x : Nat) : listMax [x] = x := by
  simp [listMax]

/-- Length of the B-family chain word. -/
theorem bWord_length (Q : Nat) (hQ : 1 ≤ Q) :
    ([5] ++ (List.range (Q - 1)).map (fun _ => 3)).length = Q := by
  simp
  omega

/-- Every weight in the B-family chain word is at least `3`. -/
theorem bWord_all_ge (Q : Nat) :
    ∀ t ∈ ([5] ++ (List.range (Q - 1)).map (fun _ => 3)), 3 ≤ t := by
  intro t ht
  simp at ht
  omega

/-- Sum of `3` repeated along `range n`. -/
theorem range_const_sum (n : Nat) :
    ((List.range n).map (fun _ => 3)).sum = 3 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ]
      simp [List.map_append, List.sum_append]
      omega

/-- Total weight of the B-family chain word is `3Q + 2`. -/
theorem bWord_sum (Q : Nat) (hQ : 1 ≤ Q) :
    ([5] ++ (List.range (Q - 1)).map (fun _ => 3)).sum =
      3 * Q + 2 := by
  rw [List.sum_append]
  simp
  omega

/-- The B-family singleton chain value is exactly `A_max,5`. -/
theorem bWord_chainA_eq_amaxB (Q : Nat) (hQ : 2 ≤ Q) :
    StringFlow.GC.chainA
      ([5] ++ (List.range (Q - 1)).map (fun _ => 3)) =
      StringFlow.TD1.amaxB Q := by
  have hlen := bWord_length Q (by omega)
  have hhead : ∀ a as,
      ([5] ++ (List.range (Q - 1)).map (fun _ => 3)) = a :: as → a = 5 := by
    intro a as h
    simp at h
    exact h.1.symm
  have hge := bWord_all_ge Q
  have hsum := bWord_sum Q (by omega)
  have hsum' :
      ([5] ++ (List.range (Q - 1)).map (fun _ => 3)).sum =
        3 * ([5] ++ (List.range (Q - 1)).map (fun _ => 3)).length + 2 := by
    rw [hlen]
    exact hsum
  have h := StringFlow.TD1.chainA_eq_amaxB
    ([5] ++ (List.range (Q - 1)).map (fun _ => 3))
    (by rw [hlen]; exact hQ) hhead hge hsum'
  have hlen' : (Q - 1) + 1 = Q := by omega
  simpa [hlen'] using h

/-- Minimum of the B-family chain values is `A_max,5`. -/
theorem listMin_chainAValsB (Q : Nat) (hQ : 2 ≤ Q) :
    listMin (chainAVals 2 Q) = StringFlow.TD1.amaxB Q := by
  rw [chainAValsB_singleton Q]
  rw [listMin_singleton]
  exact bWord_chainA_eq_amaxB Q hQ

/-- Maximum of the B-family chain values is `A_max,5`. -/
theorem listMax_chainAValsB (Q : Nat) (hQ : 2 ≤ Q) :
    listMax (chainAVals 2 Q) = StringFlow.TD1.amaxB Q := by
  rw [chainAValsB_singleton Q]
  rw [listMax_singleton]
  exact bWord_chainA_eq_amaxB Q hQ

/-- Minimum of the A-family chain values is `A0` on the stage-one
range. -/
theorem listMin_chainAValsA (Q : Nat) (hQ2 : 2 ≤ Q) (hQ50 : Q ≤ 50) :
    listMin (chainAVals 1 Q) = StringFlow.TD1.a0 Q := by
  interval_cases Q
  all_goals native_decide

/-- Maximum of the A-family chain values is `A_max,3` on the
stage-one range. -/
theorem listMax_chainAValsA (Q : Nat) (hQ2 : 2 ≤ Q) (hQ50 : Q ≤ 50) :
    listMax (chainAVals 1 Q) = StringFlow.TD1.amaxA Q := by
  interval_cases Q
  all_goals native_decide

/-- A-family word certificate with the chain window rewritten to
`A0` and `A_max,3`. -/
theorem wordBadA_cleared (Q L : Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50)
    (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ combinations (L - 1) (tableU 1 Q L)) :
    wordBad Q L (tableS 1 Q L) (tableM0 1 Q L) (tableMod 1 Q L)
      (tableTarget 1 Q L) (tableInv5 1 Q L) (tableD 1 Q L)
      (StringFlow.TD1.a0 Q) (StringFlow.TD1.amaxA Q)
      (tableUpper 1 Q L) pos = true := by
  rw [← listMin_chainAValsA Q (by omega) hQ50]
  rw [← listMax_chainAValsA Q (by omega) hQ50]
  exact wordBad_of_stageOneScanOK 1 Q L pos (by decide) (by decide)
    hQ8 hQ50 hL1 hL25 (by simpa using hmem)

/-- B-family word certificate with the chain window rewritten to the
unique `A_max,5`. -/
theorem wordBadB_cleared (Q L : Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50)
    (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ combinations (L - 1) (tableU 2 Q L - 1)) :
    wordBad Q L (tableS 2 Q L) (tableM0 2 Q L) (tableMod 2 Q L)
      (tableTarget 2 Q L) (tableInv5 2 Q L) (tableD 2 Q L)
      (listMin (chainAVals 2 Q)) (listMax (chainAVals 2 Q))
      (tableUpper 2 Q L) pos = true := by
  exact wordBad_of_stageOneScanOK 2 Q L pos (by decide) (by decide)
    hQ8 hQ50 hL1 hL25 (by simpa using hmem)

/-- The wrapped difference `R-A` modulo `M` satisfies
`(subMod R A M + A) % M = R`. -/
theorem subMod_add_congr (R A M : Nat) (hA : A < M) (hR : R < M)
    (hM : 0 < M) :
    (subMod R A M + A) % M = R := by
  unfold subMod
  rw [Nat.mod_eq_of_lt hA]
  exact StringFlow.Word.wrapped_add_mod R A M hA hR hM

/-- The residue `r = (target - Au) * inv5 (mod mod)` is the unique
representative of `m` below `mod` when the endpoint congruence and the
`5^L` inverse both hold. -/
theorem r_eq_of_congruence (L mod target inv5 Au m r : Nat)
    (hcong : (5 ^ L * m + Au) % mod = target % mod)
    (hinv : (inv5 * 5 ^ L) % mod = 1)
    (hr : r = subMod (target % mod) Au mod * inv5 % mod)
    (hm : m < mod) (hrlt : r < mod) (hmod : 0 < mod)
    (hmod1 : 1 < mod) :
    r = m := by
  let A := Au % mod
  let R := target % mod
  let D := subMod R A mod
  have hA : A < mod := by
    dsimp [A]
    exact Nat.mod_lt Au hmod
  have hR : R < mod := by
    dsimp [R]
    exact Nat.mod_lt target hmod
  have hsub : (subMod R A mod + A) % mod = R :=
    subMod_add_congr R A mod hA hR hmod
  have hAu : Au ≡ A [MOD mod] := by
    dsimp [A]
    exact (Nat.mod_modEq Au mod).symm
  have hcongA : 5 ^ L * m + A ≡ R [MOD mod] := by
    have h1 : 5 ^ L * m + Au ≡ R [MOD mod] := by
      rw [Nat.ModEq]
      simpa [R] using hcong
    exact (hAu.add_left (5 ^ L * m)).symm.trans h1
  have hD : D + A ≡ R [MOD mod] := by
    rw [Nat.ModEq]
    have hD' : (subMod R A mod + A) % mod = R := hsub
    dsimp [D]
    simpa [R] using hD'
  have hDm : D ≡ 5 ^ L * m [MOD mod] := by
    have h : D + A ≡ 5 ^ L * m + A [MOD mod] := by
      exact (hcongA.trans hD.symm).symm
    exact Nat.ModEq.add_right_cancel' A h
  have hsubDef : subMod (target % mod) Au mod = subMod R A mod := by
    dsimp [A, R]
    unfold subMod
    simp
  have hrD : r ≡ D * inv5 [MOD mod] := by
    rw [Nat.ModEq]
    rw [hr]
    simp [hsubDef, D]
  have hinv' : 5 ^ L * inv5 ≡ 1 [MOD mod] := by
    rw [Nat.ModEq]
    rw [Nat.mul_comm]
    rw [Nat.mod_eq_of_lt hmod1]
    exact hinv
  have hmul : (5 ^ L * m) * inv5 ≡ m [MOD mod] := by
    have h1 := hinv'.mul_left m
    have h2 : m * (5 ^ L * inv5) = (5 ^ L * m) * inv5 := by
      ring
    rw [h2] at h1
    simpa using h1
  have htrans : r ≡ m [MOD mod] := by
    have hstep : r ≡ (5 ^ L * m) * inv5 [MOD mod] :=
      hrD.trans (hDm.mul_right inv5)
    exact hstep.trans hmul
  exact Nat.ModEq.eq_of_lt_of_lt htrans hrlt hm

/-- Lifting the boolean `wordBad` certificate to the propositional
interval exclusion `Areq < cmin ∨ Areq > cmax`, once the active
`up`/range/inequality/divisibility hypotheses are supplied. -/
theorem wordBad_imp_areq (Q L S m0 mod target inv5 D cmin cmax Au r Areq : Nat)
    (pos : List Nat)
    (hword : wordBad Q L S m0 mod target inv5 D cmin cmax true pos = true)
    (hAu : Au = auOfPos L pos)
    (hr : r = subMod (target % mod) Au mod * inv5 % mod)
    (hrge : 7 ≤ r) (hrlt : r < m0)
    (hineq : 5 ^ Q * Au ≤ D * r)
    (hdiv : (D * r - 5 ^ Q * Au) % 2 ^ S = 0)
    (hAreq : Areq = (D * r - 5 ^ Q * Au) / 2 ^ S) :
    Areq < cmin ∨ Areq > cmax := by
  unfold wordBad at hword
  simp [← hAu, ← hr, hrge, hrlt, hineq, hdiv, ← hAreq] at hword
  exact hword

/-- Combining the rising equation and the C3 chain equation into the
global `D * m` form used by the word certificate. -/
theorem global_D_equation
    (L Q S T TT m M0 Au Achain D : Nat)
    (hrise : 2 ^ S * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hTT : S + T = TT)
    (hD : D = 2 ^ TT - 5 ^ (L + Q)) :
    D * m = 5 ^ Q * Au + 2 ^ S * Achain := by
  have hcycle := cycle_equation_of_rising_and_chain L Q S T m M0 Achain Au hrise hchain
  rw [hTT] at hcycle
  subst D
  rw [Nat.sub_mul]
  omega

/-- The certificate quotient `(D*m - 5^Q*Au) / 2^S` is exactly the
C3 chain numerator `Achain`. -/
theorem areq_cert_eq_chainA (D m S Q Au Achain : Nat)
    (hglob : D * m = 5 ^ Q * Au + 2 ^ S * Achain) :
    (D * m - 5 ^ Q * Au) / 2 ^ S = Achain := by
  have hle : 5 ^ Q * Au ≤ D * m := by omega
  have hsub : D * m - 5 ^ Q * Au = 2 ^ S * Achain := by omega
  rw [hsub]
  exact Nat.mul_div_right Achain (Nat.pow_pos (by decide : 0 < 2))

/-- If `(a+1) mod 64 = 32` and `a < 64`, then `a = 31`. -/
theorem mod_add_one_eq_thirty_one_of_lt (a : Nat) (ha : a < 64)
    (h : (a + 1) % 64 = 32) : a = 31 := by
  have hcases : a + 1 = 64 ∨ a + 1 < 64 := by omega
  rcases hcases with h64 | hlt
  · exfalso
    rw [h64] at h
    have hh : ¬ (64 % 64 = 32) := by decide
    exact hh h
  · have hmod : (a + 1) % 64 = a + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod] at h
    omega

/-- `32x ≡ 32 (mod 64)` for odd `x`. -/
theorem mul32_mod64_of_odd (x : Nat) (hx : x % 2 = 1) : (32 * x) % 64 = 32 := by
  have hxdec : x = 2 * (x / 2) + x % 2 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod x 2).symm
  calc
    (32 * x) % 64 = (32 * (2 * (x / 2) + x % 2)) % 64 := by
      conv =>
        lhs
        rw [hxdec]
    _ = (64 * (x / 2) + 32 * (x % 2)) % 64 := by
      congr 1
      rw [Nat.mul_add]
      have h1 : 32 * (2 * (x / 2)) = 64 * (x / 2) := by
        rw [← Nat.mul_assoc]
      rw [h1]
    _ = (32 * (x % 2)) % 64 := by
      rw [Nat.add_mod, Nat.mul_mod]
      simp
    _ = 32 := by
      rw [hx]

/-- Solving `5n ≡ r (mod 64)` by multiplying with `13 = 5^{-1}`. -/
theorem five_mul_mod64_eq_mul_inv (r n : Nat) (hr : (5 * n) % 64 = r) :
    n % 64 = (r * 13) % 64 := by
  have h65 : (5 * 13) % 64 = 1 := by decide
  calc
    n % 64 = ((n * (5 * 13)) % 64) := by
      rw [Nat.mul_mod, h65]
      simp
    _ = (((5 * n) * 13) % 64) := by
      congr 1
      rw [← Nat.mul_assoc, Nat.mul_comm n 5]
    _ = (((5 * n) % 64 * 13) % 64) := by
      exact (StringFlow.GC.mod_mul_self_right (5 * n) 13 64).symm
    _ = (r * 13) % 64 := by rw [hr]

/-- GC-42 for the B-family first chain weight: `t = 5` forces the
chain start to be `19 mod 64`. -/
theorem gc42_mod64_of_weight_five (n n' : Nat)
    (hstep : 2 ^ 5 * n' = 5 * n + 1) (hodd : n' % 2 = 1) :
    n % 64 = 19 := by
  have hmod : (5 * n + 1) % 64 = 32 := by
    rw [← hstep]
    have h32 : 2 ^ 5 = 32 := by decide
    rw [h32]
    exact mul32_mod64_of_odd n' hodd
  have hlt : (5 * n) % 64 < 64 := Nat.mod_lt _ (by decide)
  have hadd : ((5 * n) % 64 + 1) % 64 = 32 := by
    rw [Nat.add_mod] at hmod
    have h1 : 1 % 64 = 1 := by decide
    simpa [h1, Nat.add_comm] using hmod
  have h5n : (5 * n) % 64 = 31 :=
    mod_add_one_eq_thirty_one_of_lt ((5 * n) % 64) hlt hadd
  have h19 : (31 * 13) % 64 = 19 := by decide
  simpa [h19] using five_mul_mod64_eq_mul_inv 31 n h5n

/-- 52.17 A-family endpoint congruence: an orbit ending at
`M0 ≡ 11 (mod 16)` satisfies the full `2^(S+4)` congruence. -/
theorem word_endpoint_mod16_of_mod16 (w : List Nat) (m M0 : Nat)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (h16 : M0 % 16 = 11) :
    (5 ^ w.length * m + StringFlow.Word.wordA w) %
        2 ^ (StringFlow.wordWeight w + 4) =
      (11 * 2 ^ StringFlow.wordWeight w) %
        2 ^ (StringFlow.wordWeight w + 4) := by
  have hid := StringFlow.Word.word_orbit_identity w m hvalid
  have hM0' : 2 ^ StringFlow.wordWeight w * M0 =
      5 ^ w.length * m + StringFlow.Word.wordA w := by
    rw [← hM0]
    simpa [Nat.mul_comm] using hid
  have hdec : M0 = 16 * (M0 / 16) + 11 := by
    have h := Nat.div_add_mod M0 16
    rw [h16] at h
    omega
  rw [← hM0']
  rw [hdec]
  let S := StringFlow.wordWeight w
  change (2 ^ S * (16 * (M0 / 16) + 11)) % 2 ^ (S + 4) =
    (11 * 2 ^ S) % 2 ^ (S + 4)
  have hpow : 2 ^ (S + 4) = 16 * 2 ^ S := by
    rw [show 16 = 2 ^ 4 by decide]
    rw [← Nat.pow_add]
    rw [show S + 4 = 4 + S by omega]
  have hmul : 2 ^ S * (16 * (M0 / 16) + 11) =
      11 * 2 ^ S + 2 ^ (S + 4) * (M0 / 16) := by
    rw [hpow]
    ring
  rw [hmul]
  simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.add_mul_mod_self_right (11 * 2 ^ S) (M0 / 16) (2 ^ (S + 4)))

/-- 52.17 B-family endpoint congruence: an orbit ending at
`M0 ≡ 19 (mod 64)` satisfies the full `2^(S+6)` congruence. -/
theorem word_endpoint_mod64_of_mod64 (w : List Nat) (m M0 : Nat)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (h64 : M0 % 64 = 19) :
    (5 ^ w.length * m + StringFlow.Word.wordA w) %
        2 ^ (StringFlow.wordWeight w + 6) =
      (19 * 2 ^ StringFlow.wordWeight w) %
        2 ^ (StringFlow.wordWeight w + 6) := by
  have hid := StringFlow.Word.word_orbit_identity w m hvalid
  have hM0' : 2 ^ StringFlow.wordWeight w * M0 =
      5 ^ w.length * m + StringFlow.Word.wordA w := by
    rw [← hM0]
    simpa [Nat.mul_comm] using hid
  have hdec : M0 = 64 * (M0 / 64) + 19 := by
    have h := Nat.div_add_mod M0 64
    rw [h64] at h
    omega
  rw [← hM0']
  rw [hdec]
  let S := StringFlow.wordWeight w
  change (2 ^ S * (64 * (M0 / 64) + 19)) % 2 ^ (S + 6) =
    (19 * 2 ^ S) % 2 ^ (S + 6)
  have hpow : 2 ^ (S + 6) = 64 * 2 ^ S := by
    rw [show 64 = 2 ^ 6 by decide]
    rw [← Nat.pow_add]
    rw [show S + 6 = 6 + S by omega]
  have hmul : 2 ^ S * (64 * (M0 / 64) + 19) =
      19 * 2 ^ S + 2 ^ (S + 6) * (M0 / 64) := by
    rw [hpow]
    ring
  rw [hmul]
  simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.add_mul_mod_self_right (19 * 2 ^ S) (M0 / 64) (2 ^ (S + 6)))

/-- The A-family C3 chain starts at `11 mod 16` when the first chain
weight is `3` and the chain has at least two steps. -/
theorem chainFirst_mod16_of_c3Exact_weight_three (ns ts : List Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hQ : 2 ≤ ts.length) :
    StringFlow.GC.chainFirst ns % 16 = 11 := by
  cases ts with
  | nil => simp at hQ
  | cons t ts' =>
      have ht : t = 3 := hhead t ts' rfl
      cases ns with
      | nil => simp [StringFlow.GC.c3Exact] at hc3
      | cons n ns' =>
          cases ns' with
          | nil => simp [StringFlow.GC.c3Exact] at hc3
          | cons n' ns'' =>
              rcases hc3 with ⟨hstep, htail⟩
              have hstep' : 2 ^ 3 * n' = 5 * n + 1 := by
                simpa [ht] using hstep
              have hn'odd : n' % 2 = 1 := by
                cases ts' with
                | nil => contradiction
                | cons t2 ts2 =>
                    have ht2ge : 3 ≤ t2 := hge t2 (by simp)
                    have htail' : StringFlow.GC.c3Exact (n' :: ns'') (t2 :: ts2) := by
                      simpa using htail
                    cases ns'' with
                    | nil => simp [StringFlow.GC.c3Exact] at htail'
                    | cons n'' ns''' =>
                        have hstep2 : 2 ^ t2 * n'' = 5 * n' + 1 := by
                          simp [StringFlow.GC.c3Exact] at htail'
                          exact htail'.1
                        have h2dvd : 2 ∣ 2 ^ t2 := by
                          refine ⟨2 ^ (t2 - 1), ?_⟩
                          have hsub : t2 = (t2 - 1) + 1 := by omega
                          conv =>
                            lhs
                            rw [hsub, Nat.pow_add]
                          rw [show 2 ^ 1 = 2 by decide]
                          conv =>
                            lhs
                            rw [Nat.mul_comm]
                        have h2dvd' : 2 ∣ 2 ^ t2 * n'' :=
                          dvd_trans h2dvd (dvd_mul_right (2 ^ t2) n'')
                        have hmod2 : (5 * n' + 1) % 2 = 0 := by
                          rw [← hstep2]
                          exact Nat.dvd_iff_mod_eq_zero.mp h2dvd'
                        have hcases : n' % 2 = 0 ∨ n' % 2 = 1 := by omega
                        rcases hcases with h0 | h1
                        · have hmod2' : (n' + 1) % 2 = 0 := by
                            rw [Nat.add_mod, Nat.mul_mod] at hmod2
                            simp at hmod2
                            exact hmod2
                          have hdec : n' = 2 * (n' / 2) := by
                            have h := Nat.div_add_mod n' 2
                            rw [h0] at h
                            omega
                          rw [hdec] at hmod2'
                          have hodd' : (2 * (n' / 2) + 1) % 2 = 1 := by
                            rw [Nat.add_mod, Nat.mul_mod]
                            simp
                          rw [hodd'] at hmod2'
                          contradiction
                        · exact h1
              exact StringFlow.GC.gc42_mod16_of_weight_three n n' hstep' hn'odd

/-- The B-family C3 chain starts at `19 mod 64` when the first chain
weight is `5` and the chain has at least two steps. -/
theorem chainFirst_mod64_of_c3Exact_weight_five (ns ts : List Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hQ : 2 ≤ ts.length) :
    StringFlow.GC.chainFirst ns % 64 = 19 := by
  cases ts with
  | nil => simp at hQ
  | cons t ts' =>
      have ht : t = 5 := hhead t ts' rfl
      cases ns with
      | nil => simp [StringFlow.GC.c3Exact] at hc3
      | cons n ns' =>
          cases ns' with
          | nil => simp [StringFlow.GC.c3Exact] at hc3
          | cons n' ns'' =>
              rcases hc3 with ⟨hstep, htail⟩
              have hstep' : 2 ^ 5 * n' = 5 * n + 1 := by
                simpa [ht] using hstep
              have hn'odd : n' % 2 = 1 := by
                cases ts' with
                | nil => contradiction
                | cons t2 ts2 =>
                    have ht2ge : 3 ≤ t2 := hge t2 (by simp)
                    have htail' : StringFlow.GC.c3Exact (n' :: ns'') (t2 :: ts2) := by
                      simpa using htail
                    cases ns'' with
                    | nil => simp [StringFlow.GC.c3Exact] at htail'
                    | cons n'' ns''' =>
                        have hstep2 : 2 ^ t2 * n'' = 5 * n' + 1 := by
                          simp [StringFlow.GC.c3Exact] at htail'
                          exact htail'.1
                        have h2dvd : 2 ∣ 2 ^ t2 := by
                          refine ⟨2 ^ (t2 - 1), ?_⟩
                          have hsub : t2 = (t2 - 1) + 1 := by omega
                          conv =>
                            lhs
                            rw [hsub, Nat.pow_add]
                          rw [show 2 ^ 1 = 2 by decide]
                          conv =>
                            lhs
                            rw [Nat.mul_comm]
                        have h2dvd' : 2 ∣ 2 ^ t2 * n'' :=
                          dvd_trans h2dvd (dvd_mul_right (2 ^ t2) n'')
                        have hmod2 : (5 * n' + 1) % 2 = 0 := by
                          rw [← hstep2]
                          exact Nat.dvd_iff_mod_eq_zero.mp h2dvd'
                        have hcases : n' % 2 = 0 ∨ n' % 2 = 1 := by omega
                        rcases hcases with h0 | h1
                        · have hmod2' : (n' + 1) % 2 = 0 := by
                            rw [Nat.add_mod, Nat.mul_mod] at hmod2
                            simp at hmod2
                            exact hmod2
                          have hdec : n' = 2 * (n' / 2) := by
                            have h := Nat.div_add_mod n' 2
                            rw [h0] at h
                            omega
                          rw [hdec] at hmod2'
                          have hodd' : (2 * (n' / 2) + 1) % 2 = 1 := by
                            rw [Nat.add_mod, Nat.mul_mod]
                            simp
                          rw [hodd'] at hmod2'
                          contradiction
                        · exact h1
              exact gc42_mod64_of_weight_five n n' hstep' hn'odd

/-- The stage-one table certificate: on a feasible triple the
tabulated modulus, target, and `5^L` inverse have exactly the 52.17
forms. -/
theorem table_spec (b Q L : Nat)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (hfeas : feasible b Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25) :
    tableU b Q L = uReq b Q L ∧
    tableS b Q L = L + uReq b Q L ∧
    tableMod b Q L = 2 ^ (tableS b Q L + if b = 1 then 4 else 6) ∧
    tableTarget b Q L = (if b = 1 then 11 else 19) * 2 ^ tableS b Q L ∧
    (tableInv5 b Q L * 5 ^ L) % tableMod b Q L = 1 := by
  let P : Nat → Nat → Nat → Bool := fun b Q L =>
    ! feasible b Q L ||
      let T := tCeil (L + Q)
      let U := uReq b Q L
      let S := L + U
      let m0 := if S <= 6 then 7 else max 7 ((2^(S-6)) - 1)
      let mod := if b = 1 then 2^(S+4) else 2^(S+6)
      let target := (if b = 1 then 11 else 19) * 2^S
      decide (tableU b Q L = U) &&
      decide (tableS b Q L = S) &&
      decide (tableM0 b Q L = m0) &&
      decide (tableMod b Q L = mod) &&
      decide (tableTarget b Q L = target) &&
      decide (tableD b Q L = 2^T - 5^(L+Q)) &&
      decide ((tableInv5 b Q L * 5^L) % mod = 1) &&
      decide (tableUpper b Q L = upperAt b Q L m0)
  have hcheck := stageOneScan_check
  simp [stageOneScanOK] at hcheck
  rcases hcheck with ⟨⟨htables, _hlower⟩, _htriples⟩
  have htables' : (allInRange 8 51
      (fun Q => allInRange 1 26 (fun L => allInRange 1 3 (fun b => P b Q L)))) = true := by
    simpa [P, tablesOK] using htables
  have hQ51 : Q < 51 := by omega
  have hQrange := allInRange_spec 8 51
    (fun Q => allInRange 1 26 (fun L => allInRange 1 3 (fun b => P b Q L)))
    htables' Q hQ8 hQ51
  have hL26 : L < 26 := by omega
  have hLrange := allInRange_spec 1 26
    (fun L => allInRange 1 3 (fun b => P b Q L)) hQrange L hL1 hL26
  have hb3 : b < 3 := by omega
  have hbcheck := allInRange_spec 1 3 (fun b => P b Q L) hLrange b hb1 hb3
  have hbcheck' : P b Q L = true := hbcheck
  simp [P, hfeas, Bool.and_eq_true] at hbcheck'
  have hU : tableU b Q L = uReq b Q L := hbcheck'.1.1.1.1.1.1.1
  have hS : tableS b Q L = L + uReq b Q L := hbcheck'.1.1.1.1.1.1.2
  have hM0 : tableM0 b Q L =
      (if L + uReq b Q L ≤ 6 then 7 else max 7 (2 ^ (L + uReq b Q L - 6) - 1)) :=
    hbcheck'.1.1.1.1.1.2
  have hMod : tableMod b Q L =
      (if b = 1 then 2 ^ (L + uReq b Q L + 4) else 2 ^ (L + uReq b Q L + 6)) :=
    hbcheck'.1.1.1.1.2
  have hTarget : tableTarget b Q L =
      (if b = 1 then 11 * 2 ^ (L + uReq b Q L) else 19 * 2 ^ (L + uReq b Q L)) :=
    hbcheck'.1.1.1.2
  have hD : tableD b Q L = 2 ^ tCeil (L + Q) - 5 ^ (L + Q) :=
    hbcheck'.1.1.2
  have hInv : (tableInv5 b Q L * 5 ^ L) %
      (if b = 1 then 2 ^ (L + uReq b Q L + 4) else 2 ^ (L + uReq b Q L + 6)) = 1 :=
    hbcheck'.1.2
  let S := L + uReq b Q L
  have hS' : tableS b Q L = S := by
    simpa [S] using hS
  have hModEq : tableMod b Q L =
      (if b = 1 then 2 ^ (S + 4) else 2 ^ (S + 6)) := by
    simpa [S] using hMod
  have hTargetEq : tableTarget b Q L =
      (if b = 1 then 11 else 19) * 2 ^ S := by
    simpa [S] using hTarget
  have hInvEq : (tableInv5 b Q L * 5 ^ L) %
      (if b = 1 then 2 ^ (S + 4) else 2 ^ (S + 6)) = 1 := by
    simpa [S] using hInv
  have hMod' : tableMod b Q L =
      2 ^ (tableS b Q L + if b = 1 then 4 else 6) := by
    rw [← hS'] at hModEq
    by_cases hb : b = 1
    · simp [hb] at hModEq ⊢
      exact hModEq
    · simp [hb] at hModEq ⊢
      exact hModEq
  have hTarget' : tableTarget b Q L =
      (if b = 1 then 11 else 19) * 2 ^ tableS b Q L := by
    rw [← hS'] at hTargetEq
    by_cases hb : b = 1
    · simp [hb] at hTargetEq ⊢
      exact hTargetEq
    · simp [hb] at hTargetEq ⊢
      exact hTargetEq
  have hInv' : (tableInv5 b Q L * 5 ^ L) % tableMod b Q L = 1 := by
    by_cases hb : b = 1
    · have hModEqA : tableMod b Q L = 2 ^ (S + 4) := by
        simpa [hb] using hModEq
      rw [← hModEqA] at hInvEq
      simpa [hb] using hInvEq
    · have hModEqB : tableMod b Q L = 2 ^ (S + 6) := by
        simpa [hb] using hModEq
      rw [← hModEqB] at hInvEq
      simpa [hb] using hInvEq
  exact ⟨hU, hS', hMod', hTarget', hInv'⟩

/-- The stage-one table denominator `tableD` has the exact closed
form `2^tCeil(L+Q) - 5^(L+Q)` on every feasible triple. -/
theorem tableD_spec (b Q L : Nat)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (hfeas : feasible b Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25) :
    tableD b Q L = 2 ^ tCeil (L + Q) - 5 ^ (L + Q) := by
  let P : Nat → Nat → Nat → Bool := fun b Q L =>
    ! feasible b Q L ||
      let T := tCeil (L + Q)
      let U := uReq b Q L
      let S := L + U
      let m0 := if S <= 6 then 7 else max 7 ((2^(S-6)) - 1)
      let mod := if b = 1 then 2^(S+4) else 2^(S+6)
      let target := (if b = 1 then 11 else 19) * 2^S
      decide (tableU b Q L = U) &&
      decide (tableS b Q L = S) &&
      decide (tableM0 b Q L = m0) &&
      decide (tableMod b Q L = mod) &&
      decide (tableTarget b Q L = target) &&
      decide (tableD b Q L = 2^T - 5^(L+Q)) &&
      decide ((tableInv5 b Q L * 5^L) % mod = 1) &&
      decide (tableUpper b Q L = upperAt b Q L m0)
  have hcheck := stageOneScan_check
  simp [stageOneScanOK] at hcheck
  rcases hcheck with ⟨⟨htables, _hlower⟩, _htriples⟩
  have htables' : (allInRange 8 51
      (fun Q => allInRange 1 26 (fun L => allInRange 1 3 (fun b => P b Q L)))) = true := by
    simpa [P, tablesOK] using htables
  have hQ51 : Q < 51 := by omega
  have hQrange := allInRange_spec 8 51
    (fun Q => allInRange 1 26 (fun L => allInRange 1 3 (fun b => P b Q L)))
    htables' Q hQ8 hQ51
  have hL26 : L < 26 := by omega
  have hLrange := allInRange_spec 1 26
    (fun L => allInRange 1 3 (fun b => P b Q L)) hQrange L hL1 hL26
  have hb3 : b < 3 := by omega
  have hbcheck := allInRange_spec 1 3 (fun b => P b Q L) hLrange b hb1 hb3
  have hbcheck' : P b Q L = true := hbcheck
  simp [P, hfeas, Bool.and_eq_true] at hbcheck'
  exact hbcheck'.1.1.2

/-- The A-family table certificate from 52.17. -/
theorem table_A_spec (Q L : Nat)
    (hfeas : feasible 1 Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25) :
    tableMod 1 Q L = 2 ^ (tableS 1 Q L + 4) ∧
    tableTarget 1 Q L = 11 * 2 ^ tableS 1 Q L ∧
    (tableInv5 1 Q L * 5 ^ L) % tableMod 1 Q L = 1 := by
  have h := table_spec 1 Q L (by decide) (by decide) hfeas hQ8 hQ50 hL1 hL25
  rcases h with ⟨_hU, _hS, hMod, hTarget, hInv⟩
  exact ⟨hMod, hTarget, hInv⟩

/-- The B-family table certificate from 52.17. -/
theorem table_B_spec (Q L : Nat)
    (hfeas : feasible 2 Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25) :
    tableMod 2 Q L = 2 ^ (tableS 2 Q L + 6) ∧
    tableTarget 2 Q L = 19 * 2 ^ tableS 2 Q L ∧
    (tableInv5 2 Q L * 5 ^ L) % tableMod 2 Q L = 1 := by
  have h := table_spec 2 Q L (by decide) (by decide) hfeas hQ8 hQ50 hL1 hL25
  rcases h with ⟨_hU, _hS, hMod, hTarget, hInv⟩
  exact ⟨hMod, hTarget, hInv⟩

/-- The full A-family 52.17 congruence: the tabulated modulus and
target match the endpoint congruence of the real rising word, and the
tabulated `5^L` inverse is certified. -/
theorem congruence_52_17_A (Q L m M0 Au : Nat) (w : List Nat)
    (hfeas : feasible 1 Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = tableS 1 Q L)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (h16 : M0 % 16 = 11)
    (hAu : Au = StringFlow.Word.wordA w) :
    (5 ^ L * m + Au) % tableMod 1 Q L = tableTarget 1 Q L % tableMod 1 Q L ∧
    (tableInv5 1 Q L * 5 ^ L) % tableMod 1 Q L = 1 := by
  have hspec := table_A_spec Q L hfeas hQ8 hQ50 hL1 hL25
  rcases hspec with ⟨hMod, hTarget, hInv⟩
  have hcong0 := word_endpoint_mod16_of_mod16 w m M0 hvalid hM0 h16
  have hAu' : StringFlow.Word.wordA w = Au := hAu.symm
  have hcong : (5 ^ L * m + Au) % 2 ^ (tableS 1 Q L + 4) =
      (11 * 2 ^ tableS 1 Q L) % 2 ^ (tableS 1 Q L + 4) := by
    rw [hwlen, hAu', hwS] at hcong0
    exact hcong0
  constructor
  · rw [hMod, hTarget]
    exact hcong
  · simpa [hMod] using hInv

/-- The full B-family 52.17 congruence: the tabulated modulus and
target match the endpoint congruence of the real rising word, and the
tabulated `5^L` inverse is certified. -/
theorem congruence_52_17_B (Q L m M0 Au : Nat) (w : List Nat)
    (hfeas : feasible 2 Q L = true)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = tableS 2 Q L)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (h64 : M0 % 64 = 19)
    (hAu : Au = StringFlow.Word.wordA w) :
    (5 ^ L * m + Au) % tableMod 2 Q L = tableTarget 2 Q L % tableMod 2 Q L ∧
    (tableInv5 2 Q L * 5 ^ L) % tableMod 2 Q L = 1 := by
  have hspec := table_B_spec Q L hfeas hQ8 hQ50 hL1 hL25
  rcases hspec with ⟨hMod, hTarget, hInv⟩
  have hcong0 := word_endpoint_mod64_of_mod64 w m M0 hvalid hM0 h64
  have hAu' : StringFlow.Word.wordA w = Au := hAu.symm
  have hcong : (5 ^ L * m + Au) % 2 ^ (tableS 2 Q L + 6) =
      (19 * 2 ^ tableS 2 Q L) % 2 ^ (tableS 2 Q L + 6) := by
    rw [hwlen, hAu', hwS] at hcong0
    exact hcong0
  constructor
  · rw [hMod, hTarget]
    exact hcong
  · simpa [hMod] using hInv

end StringFlow
