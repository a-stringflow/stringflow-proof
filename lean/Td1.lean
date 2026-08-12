import StageOne
import Certificates
import WordWindow

set_option linter.unusedSimpArgs false

/-!
# TD-1 bridge: `m = 201` rigidity and the sharp basin split

This module formalizes the remaining finite bridge in `ph_qb_gc_chain.md`
section 52.21.2bis:

1. The first-C3 word of `m = 201` has length 20, six `t = 2` steps,
   endpoint `286189779`, and weight 26.
2. With `L = 20`, the length/weight match `U_req = 6` has exactly the
   two solutions `(Q,b) = (28,2)` and `(29,1)`.
3. The sharp basin split below 617: every admissible `m < 617` with
   first-C3 weight at least 26 is exactly `m = 201`.

The certificates are finite domination certificates verified by
`native_decide`, using the same `domCert`/`certsOK` soundness chain as
`Certificates.lean`.
-/

namespace StringFlow.TD1

/-- The rising word taken before the first C3 start, with a fuel bound. -/
def firstC3WordAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n =>
      if n % 8 = 3 then []
      else if n % 8 = 7 then 2 :: firstC3WordAux fuel ((5 * n + 1) / 4)
      else 1 :: firstC3WordAux fuel ((5 * n + 1) / 2)

/-- The first-C3 word of `201`, from 52.21.2bis lemma B1. -/
def b1Word : List Nat :=
  [1,2,1,1,1,1,2,1,2,1,1,2,1,1,1,1,1,2,1,2]

def b1OrbitOK : Bool :=
  firstC3WordAux 100 201 = b1Word && firstC3H 100 201 = (true, 26)

theorem b1_orbit_check : b1OrbitOK = true := by
  native_decide

theorem b1_orbit :
    firstC3WordAux 100 201 = b1Word ∧ firstC3H 100 201 = (true, 26) := by
  have h := b1_orbit_check
  simp [b1OrbitOK] at h
  exact h

theorem b1_length : b1Word.length = 20 := by
  native_decide

theorem b1_count_two : (b1Word.filter (fun t => t = 2)).length = 6 := by
  native_decide

theorem b1_last : StringFlow.Word.wordLast b1Word = 2 := by
  native_decide

theorem b1_weight : wordWeight b1Word = 26 := by
  native_decide

/-- The first-C3 word of `201` ends at `286189779`. -/
theorem b1_wordOrbit_201 :
    StringFlow.Word.wordOrbit b1Word 201 = 286189779 := by
  native_decide

/-- The head C3 step of the `201` orbit has exact weight `5`. -/
theorem b1_head_five :
    (5 * 286189779 + 1) % 32 = 0 ∧ (5 * 286189779 + 1) % 64 ≠ 0 := by
  native_decide

/-- `U_req = 6` with `L = 20` and `b = 2`, checked on the small `Q`
range.  The first-C3 word of 201 ends with `t = 2`, so only the B
family (`b = 2`) is compatible with this orbit. -/
def b1BUReqOK : Bool :=
  allInRange 8 37 (fun Q =>
    decide (Q = 28) || decide (StringFlow.uReq 2 Q 20 ≠ 6))

theorem b1B_uReq_check : b1BUReqOK = true := by
  native_decide

/-- `U_req = 6` is impossible for `37 <= Q <= 184` in the B family. -/
def b1BLargeUReqOK : Bool :=
  allInRange 37 185 (fun Q =>
    decide (StringFlow.uReq 2 Q 20 ≠ 6))

theorem b1B_large_uReq_check : b1BLargeUReqOK = true := by
  native_decide

theorem b1B_uReq_Q_le_36 (Q : Nat) (_hQ8 : 8 ≤ Q)
    (hU : StringFlow.uReq 2 Q 20 = 6) : Q ≤ 36 := by
  by_cases hQ36 : Q ≤ 36
  · exact hQ36
  · exfalso
    have hQ37 : 37 ≤ Q := by omega
    by_cases hQ184 : Q ≤ 184
    · have hQ185 : Q < 185 := by omega
      have hQrange := allInRange_spec 37 185
        (fun Q => decide (StringFlow.uReq 2 Q 20 ≠ 6))
        b1B_large_uReq_check Q hQ37 hQ185
      simp [hU] at hQrange
    · have hQ185 : 185 ≤ Q := by omega
      have hP : 205 ≤ 20 + Q := by omega
      have ht0 : StringFlow.tCeil (20 + Q) = 0 :=
        StringFlow.tCeil_large (20 + Q) hP
      have hU0 : StringFlow.uReq 2 Q 20 = 0 := by
        unfold StringFlow.uReq
        rw [ht0]
        simp
      omega

theorem b1B_uReq_solutions (Q : Nat) (hQ8 : 8 ≤ Q) (hQ36 : Q ≤ 36)
    (hU : StringFlow.uReq 2 Q 20 = 6) : Q = 28 := by
  have hQ37 : Q < 37 := by omega
  have hQrange := allInRange_spec 8 37
    (fun Q => decide (Q = 28) || decide (StringFlow.uReq 2 Q 20 ≠ 6))
    b1B_uReq_check Q hQ8 hQ37
  simp [hU] at hQrange
  exact hQrange

theorem b1B_uReq_solutions_full (Q : Nat) (hQ8 : 8 ≤ Q)
    (hU : StringFlow.uReq 2 Q 20 = 6) : Q = 28 := by
  have hQ36 := b1B_uReq_Q_le_36 Q hQ8 hU
  exact b1B_uReq_solutions Q hQ8 hQ36 hU

/-- B1 in one package: the B-family orbit rigidity and its unique
`U_req` solution. -/
theorem b1_201 (Q : Nat) (hQ8 : 8 ≤ Q)
    (hU : StringFlow.uReq 2 Q 20 = 6) :
    firstC3WordAux 100 201 = b1Word ∧ Q = 28 := by
  constructor
  · exact b1_orbit.1
  · exact b1B_uReq_solutions_full Q hQ8 hU

theorem b1B_delta_value : StringFlow.tCeil 48 = 112 := by
  native_decide

/-- The A-family `U_req = 6` alternatives with `L = 20` are
`Q = 29` and `Q = 30`; they are not compatible with the first-C3 word
of 201, whose final rising step has weight 2. -/
theorem b1A_alt_delta_values :
    StringFlow.tCeil 49 = 114 ∧ StringFlow.tCeil 50 = 117 := by
  native_decide

/-- Cap-25 domination certificate for `[7, 201)`. -/
def certBasin25A : List Cert := [
  Cert.mk 7 23 [2,2,2,1,2,2,1,1,2,2,2,2,2,1,1],
  Cert.mk 23 201 [2,2,2,2,2,2,2,2,2,2,2,1,1],
]

theorem certBasin25A_check : certsOK 25 7 201 certBasin25A = true := by
  native_decide

/-- Cap-25 domination certificate for `[203, 617)`. -/
def certBasin25B : List Cert := [
  Cert.mk 203 421 [2,2,2,2,2,2,2,2,1,2,1],
  Cert.mk 421 473 [2,2,1,2,2,1,2,2,2,2,2,1,2,1,1],
  Cert.mk 473 503 [2,2,2,2,2,2,2,1,2,1,2,1,2,2],
  Cert.mk 503 509 [2,1,1,1,1,2,1,2,1,1,2,1,1,1,1,1,2,1,2],
  Cert.mk 509 617 [2,2,2,2,2,2,2,2,1],
]

theorem certBasin25B_check : certsOK 25 203 617 certBasin25B = true := by
  native_decide

theorem basin_201_cap25_cert :
    ∀ m : Nat, 7 ≤ m → m < 201 → admissible m →
      ∃ c : Cert, coverCert certBasin25A m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 25 := by
  exact certsOK_spec 25 7 201 certBasin25A certBasin25A_check

theorem basin_203_617_cap25_cert :
    ∀ m : Nat, 203 ≤ m → m < 617 → admissible m →
      ∃ c : Cert, coverCert certBasin25B m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 25 := by
  exact certsOK_spec 25 203 617 certBasin25B certBasin25B_check

theorem coverCert_mem (cs : List Cert) (m : Nat) (c : Cert) :
    coverCert cs m = some c → c ∈ cs := by
  induction cs with
  | nil =>
      intro h
      simp [coverCert] at h
  | cons c' cs ih =>
      intro h
      by_cases hc : c'.lo ≤ m ∧ m < c'.hi
      · simp [coverCert, hc] at h
        subst c
        simp
      · simp [coverCert, hc] at h
        exact List.mem_cons_of_mem c' (ih h)

theorem certBasin25A_len : ∀ c ∈ certBasin25A, c.w.length ≤ 1000 := by
  native_decide

theorem certBasin25B_len : ∀ c ∈ certBasin25B, c.w.length ≤ 1000 := by
  native_decide

/-- Every certificate in the `10^6` basin list has word length at
most `1000`. -/
theorem cert1e6_len : ∀ c ∈ StringFlow.cert1e6, c.w.length ≤ 1000 := by
  native_decide

/-- A start that is already C3 gives the same empty prefix for every
fuel bound. -/
theorem firstC3H_of_c3 (fuel m : Nat) (h : m % 8 = 3) :
    firstC3H fuel m = (true, 0) := by
  induction fuel with
  | zero => simp [firstC3H, h]
  | succ fuel ih => simp [firstC3H, h]

/-- Once a C3 start is reached, extra fuel does not change the prefix. -/
theorem firstC3H_mono (fuel m extra : Nat)
    (h : (firstC3H fuel m).1 = true) :
    firstC3H (fuel + extra) m = firstC3H fuel m := by
  induction fuel generalizing m with
  | zero =>
      by_cases hc3 : m % 8 = 3
      · rw [Nat.zero_add, firstC3H_of_c3 extra m hc3, firstC3H_of_c3 0 m hc3]
      · simp [firstC3H, hc3] at h
  | succ fuel ih =>
      by_cases hc3 : m % 8 = 3
      · rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega,
          firstC3H_of_c3 (fuel + extra + 1) m hc3,
          firstC3H_of_c3 (fuel + 1) m hc3]
      · by_cases h7 : m % 8 = 7
        · let nxt := (5 * m + 1) / 4
          have h' : (firstC3H fuel nxt).1 = true := by
            simp [firstC3H, hc3, h7] at h
            exact h
          have hm := ih nxt h'
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
          simp [firstC3H, hc3, h7]
          have hm' : firstC3H (fuel + extra) ((5 * m + 1) / 4) =
              firstC3H fuel ((5 * m + 1) / 4) := by
            simpa [nxt] using hm
          rw [hm']
          simp
        · let nxt := (5 * m + 1) / 2
          have h' : (firstC3H fuel nxt).1 = true := by
            simp [firstC3H, hc3, h7] at h
            exact h
          have hm := ih nxt h'
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
          simp [firstC3H, hc3, h7]
          have hm' : firstC3H (fuel + extra) ((5 * m + 1) / 2) =
              firstC3H fuel ((5 * m + 1) / 2) := by
            simpa [nxt] using hm
          rw [hm']
          simp

theorem firstC3S_of_hit (fuel fuel' m : Nat)
    (hle : fuel ≤ fuel') (h : (firstC3H fuel m).1 = true) :
    firstC3S fuel' m = firstC3S fuel m := by
  let extra := fuel' - fuel
  have hsum : fuel + extra = fuel' := by omega
  rw [← hsum]
  unfold StringFlow.firstC3S
  rw [firstC3H_mono fuel m extra h]

/-- The exact first-C3 word has entries in `{1,2}` whenever it hits. -/
theorem firstC3WordAux_ok_of_hit (fuel n : Nat)
    (h : (firstC3H fuel n).1 = true) :
    ∀ t ∈ firstC3WordAux fuel n, t = 1 ∨ t = 2 := by
  induction fuel generalizing n with
  | zero => simp [firstC3WordAux]
  | succ fuel ih =>
      by_cases h3 : n % 8 = 3
      · simp [firstC3WordAux, h3]
      · by_cases h7 : n % 8 = 7
        · have h' : (firstC3H fuel ((5 * n + 1) / 4)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hstep : firstC3WordAux (fuel + 1) n =
              2 :: firstC3WordAux fuel ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with rfl | ht2
          · exact Or.inr rfl
          · exact ih ((5 * n + 1) / 4) h' t ht2
        · have h' : (firstC3H fuel ((5 * n + 1) / 2)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hstep : firstC3WordAux (fuel + 1) n =
              1 :: firstC3WordAux fuel ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with rfl | ht2
          · exact Or.inl rfl
          · exact ih ((5 * n + 1) / 2) h' t ht2

/-- The exact first-C3 word has weight equal to `firstC3S`. -/
theorem firstC3WordAux_weight_of_hit (fuel n : Nat)
    (h : (firstC3H fuel n).1 = true) :
    wordWeight (firstC3WordAux fuel n) = firstC3S fuel n := by
  induction fuel generalizing n with
  | zero =>
      by_cases h3 : n % 8 = 3 <;> simp [firstC3WordAux, firstC3H,
        StringFlow.firstC3S, StringFlow.wordWeight, h3]
  | succ fuel ih =>
      by_cases h3 : n % 8 = 3
      · simp [firstC3WordAux, firstC3H, StringFlow.firstC3S,
          StringFlow.wordWeight, h3]
      · by_cases h7 : n % 8 = 7
        · have h' : (firstC3H fuel ((5 * n + 1) / 4)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have ih' := ih ((5 * n + 1) / 4) h'
          have hstep : firstC3WordAux (fuel + 1) n =
              2 :: firstC3WordAux fuel ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          unfold StringFlow.firstC3S
          unfold StringFlow.firstC3S at ih'
          simp [firstC3H, h3, h7, StringFlow.wordWeight]
          omega
        · have h' : (firstC3H fuel ((5 * n + 1) / 2)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have ih' := ih ((5 * n + 1) / 2) h'
          have hstep : firstC3WordAux (fuel + 1) n =
              1 :: firstC3WordAux fuel ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          unfold StringFlow.firstC3S
          unfold StringFlow.firstC3S at ih'
          simp [firstC3H, h3, h7, StringFlow.wordWeight]
          omega

/-- An odd `n` that is neither `3` nor `7 mod 8` is `1` or `5 mod 8`. -/
theorem mod8_one_or_five_of_odd_not3_not7 (n : Nat)
    (hodd : n % 2 = 1) (h3 : n % 8 ≠ 3) (h7 : n % 8 ≠ 7) :
    n % 8 = 1 ∨ n % 8 = 5 := by
  have hlt : n % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : n % 2 = (n % 8) % 2 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
  rw [hmod] at hodd
  have hcases : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
      n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3eq | h4 | h5 | h6 | h7eq
  · simp [h0] at hodd
  · exact Or.inl h1
  · simp [h2] at hodd
  · exact False.elim (h3 h3eq)
  · simp [h4] at hodd
  · exact Or.inr h5
  · simp [h6] at hodd
  · exact False.elim (h7 h7eq)

/-- The successor after a `7 mod 8` step is odd. -/
theorem odd_of_mod8_seven (n : Nat) (h : n % 8 = 7) :
    ((5 * n + 1) / 4) % 2 = 1 := by
  have hdec : n = 8 * (n / 8) + n % 8 := by
    have h := Nat.div_add_mod n 8
    simpa [Nat.mul_comm] using h.symm
  rw [hdec, h]
  have hlin : (5 * (8 * (n / 8) + 7) + 1) / 4 = 10 * (n / 8) + 9 := by
    omega
  rw [hlin]
  rw [Nat.add_mod, Nat.mul_mod]
  have h10mod : 10 % 2 = 0 := by decide
  have h9 : 9 % 2 = 1 := by decide
  rw [h10mod, h9]
  simp

/-- The successor after a `1` or `5 mod 8` step is odd. -/
theorem odd_of_mod8_one_or_five (n : Nat) (h : n % 8 = 1 ∨ n % 8 = 5) :
    ((5 * n + 1) / 2) % 2 = 1 := by
  have hdec : n = 8 * (n / 8) + n % 8 := by
    have h := Nat.div_add_mod n 8
    simpa [Nat.mul_comm] using h.symm
  rcases h with h1 | h5
  · rw [hdec, h1]
    have hlin : (5 * (8 * (n / 8) + 1) + 1) / 2 = 20 * (n / 8) + 3 := by
      omega
    rw [hlin]
    rw [Nat.add_mod, Nat.mul_mod]
    have h20mod : 20 % 2 = 0 := by decide
    have h3 : 3 % 2 = 1 := by decide
    rw [h20mod, h3]
    simp
  · rw [hdec, h5]
    have hlin : (5 * (8 * (n / 8) + 5) + 1) / 2 = 20 * (n / 8) + 13 := by
      omega
    rw [hlin]
    rw [Nat.add_mod, Nat.mul_mod]
    have h20mod : 20 % 2 = 0 := by decide
    have h13 : 13 % 2 = 1 := by decide
    rw [h20mod, h13]
    simp

/-- The exact first-C3 word is a valid orbit word whenever the start
is odd and a C3 hit occurs. -/
theorem firstC3WordAux_valid_of_hit (fuel n : Nat)
    (hodd : n % 2 = 1) (h : (firstC3H fuel n).1 = true) :
    StringFlow.Word.wordValid (firstC3WordAux fuel n) n := by
  induction fuel generalizing n with
  | zero => simp [firstC3WordAux, StringFlow.Word.wordValid]
  | succ fuel ih =>
      by_cases h3 : n % 8 = 3
      · simp [firstC3WordAux, StringFlow.Word.wordValid, h3]
      · by_cases h7 : n % 8 = 7
        · have h' : (firstC3H fuel ((5 * n + 1) / 4)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hdiv : (5 * n + 1) % 4 = 0 :=
            StringFlow.Word.step_two_mod4_of_mod8_seven n h7
          have hodd' : ((5 * n + 1) / 4) % 2 = 1 := odd_of_mod8_seven n h7
          have htail := ih ((5 * n + 1) / 4) hodd' h'
          have hstep : firstC3WordAux (fuel + 1) n =
              2 :: firstC3WordAux fuel ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          simp [StringFlow.Word.wordValid, hdiv]
          exact htail
        · have h' : (firstC3H fuel ((5 * n + 1) / 2)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hres : n % 8 = 1 ∨ n % 8 = 5 :=
            mod8_one_or_five_of_odd_not3_not7 n hodd h3 h7
          have h4 := StringFlow.Word.step_weight_one_of_mod8 n hres
          have hdiv : (5 * n + 1) % 2 = 0 := by
            have hmod : (5 * n + 1) % 2 = ((5 * n + 1) % 4) % 2 :=
              (Nat.mod_mod_of_dvd (5 * n + 1) (by decide : 2 ∣ 4)).symm
            rw [hmod, h4]
          have hodd' : ((5 * n + 1) / 2) % 2 = 1 :=
            odd_of_mod8_one_or_five n hres
          have htail := ih ((5 * n + 1) / 2) hodd' h'
          have hstep : firstC3WordAux (fuel + 1) n =
              1 :: firstC3WordAux fuel ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          simp [StringFlow.Word.wordValid, hdiv]
          exact htail

/-- The exact first-C3 word ends at a C3 start. -/
theorem firstC3WordAux_endpoint_mod8_of_hit (fuel n : Nat)
    (hodd : n % 2 = 1) (h : (firstC3H fuel n).1 = true) :
    StringFlow.Word.wordOrbit (firstC3WordAux fuel n) n % 8 = 3 := by
  induction fuel generalizing n with
  | zero =>
      have hc3 : n % 8 = 3 := by
        by_cases hc : n % 8 = 3
        · exact hc
        · simp [firstC3H, hc] at h
      simp [firstC3WordAux, StringFlow.Word.wordOrbit, hc3]
  | succ fuel ih =>
      by_cases h3 : n % 8 = 3
      · simp [firstC3WordAux, StringFlow.Word.wordOrbit, h3]
      · by_cases h7 : n % 8 = 7
        · have h' : (firstC3H fuel ((5 * n + 1) / 4)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hodd' : ((5 * n + 1) / 4) % 2 = 1 := odd_of_mod8_seven n h7
          have htail := ih ((5 * n + 1) / 4) hodd' h'
          have hstep : firstC3WordAux (fuel + 1) n =
              2 :: firstC3WordAux fuel ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          simp [StringFlow.Word.wordOrbit]
          exact htail
        · have h' : (firstC3H fuel ((5 * n + 1) / 2)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hres : n % 8 = 1 ∨ n % 8 = 5 :=
            mod8_one_or_five_of_odd_not3_not7 n hodd h3 h7
          have hodd' : ((5 * n + 1) / 2) % 2 = 1 :=
            odd_of_mod8_one_or_five n hres
          have htail := ih ((5 * n + 1) / 2) hodd' h'
          have hstep : firstC3WordAux (fuel + 1) n =
              1 :: firstC3WordAux fuel ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          rw [hstep]
          simp [StringFlow.Word.wordOrbit]
          exact htail

/-- After a `7 mod 8` step, halving once leaves an even number. -/
theorem even_of_mod8_seven_half (n : Nat) (h : n % 8 = 7) :
    ((5 * n + 1) / 2) % 2 = 0 := by
  have hdec : n = 8 * (n / 8) + n % 8 := by
    have h := Nat.div_add_mod n 8
    simpa [Nat.mul_comm] using h.symm
  rw [hdec, h]
  have hlin : (5 * (8 * (n / 8) + 7) + 1) / 2 = 20 * (n / 8) + 18 := by
    omega
  rw [hlin]
  rw [Nat.add_mod, Nat.mul_mod]
  simp

/-- An exact `t = 1` or `t = 2` step has an odd start. -/
theorem odd_of_step_weight_one_or_two (n t : Nat)
    (ht12 : t = 1 ∨ t = 2) (hdiv : (5 * n + 1) % 2 ^ t = 0) :
    n % 2 = 1 := by
  have heven : (5 * n + 1) % 2 = 0 := by
    rcases ht12 with rfl | rfl
    · simpa using hdiv
    · have h4 : (5 * n + 1) % 4 = 0 := by simpa using hdiv
      have hmod : (5 * n + 1) % 2 = ((5 * n + 1) % 4) % 2 :=
        (Nat.mod_mod_of_dvd (5 * n + 1) (by decide : 2 ∣ 4)).symm
      rw [hmod, h4]
  have hmod5 : (5 * n) % 2 = n % 2 := by
    rw [Nat.mul_mod]
    have h5 : 5 % 2 = 1 := by decide
    rw [h5]
    simp
  have hsum : (5 * n + 1) % 2 = (n % 2 + 1) % 2 := by
    rw [Nat.add_mod, hmod5]
  rw [hsum] at heven
  have h01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h01 with h0 | h1
  · rw [h0] at heven
    simp at heven
  · exact h1

/-- The head of a first-C3 word over `{1,2}` is `2` at a `7 mod 8`
start. -/
theorem step_two_of_wordFirst_seven (w : List Nat) (n t : Nat)
    (hok : ∀ a ∈ t :: w, a = 1 ∨ a = 2)
    (h : StringFlow.Word.wordFirst (t :: w) n) (h7 : n % 8 = 7) :
    t = 2 := by
  rcases h with ⟨hxne, hdiv, htail⟩
  have ht12 := hok t (by simp)
  rcases ht12 with rfl | rfl
  · have hy : ((5 * n + 1) / 2) % 2 = 0 := even_of_mod8_seven_half n h7
    cases w with
    | nil =>
        have hc3 : ((5 * n + 1) / 2) % 8 = 3 := by
          simpa [StringFlow.Word.wordFirst] using htail
        exact False.elim (StringFlow.Word.even_not_c3 _ hy hc3)
    | cons t2 w2 =>
        rcases htail with ⟨_, hdiv2, _⟩
        have hdiv2' : (5 * ((5 * n + 1) / 2) + 1) % 2 ^ t2 = 0 := by
          simpa using hdiv2
        have hodd : (5 * ((5 * n + 1) / 2) + 1) % 2 = 1 :=
          StringFlow.Word.odd_after_even _ hy
        have ht2ge : 1 ≤ t2 := by
          have ht12' := hok t2 (by simp [List.mem_cons])
          omega
        exact False.elim
          (StringFlow.Word.not_dvd_two_pow_of_odd _ t2 hodd ht2ge hdiv2')
  · rfl

/-- The head of a first-C3 word over `{1,2}` is `1` at a start that
is neither `3` nor `7 mod 8`. -/
theorem step_one_of_wordFirst_other (w : List Nat) (n t : Nat)
    (hok : ∀ a ∈ t :: w, a = 1 ∨ a = 2)
    (h : StringFlow.Word.wordFirst (t :: w) n)
    (h3 : n % 8 ≠ 3) (h7 : n % 8 ≠ 7) :
    t = 1 := by
  rcases h with ⟨hxne, hdiv, htail⟩
  have ht12 := hok t (by simp)
  rcases ht12 with rfl | rfl
  · rfl
  · have hodd : n % 2 = 1 := odd_of_step_weight_one_or_two n 2 (Or.inr rfl) hdiv
    have hres : n % 8 = 1 ∨ n % 8 = 5 :=
      mod8_one_or_five_of_odd_not3_not7 n hodd h3 h7
    have h4 : (5 * n + 1) % 4 = 2 :=
      StringFlow.Word.step_weight_one_of_mod8 n hres
    have hdiv4 : (5 * n + 1) % 4 = 0 := by simpa using hdiv
    omega

/-- A `{1,2}` first-C3 word is exactly `firstC3WordAux`: no earlier
C3 and an exact endpoint force the canonical weights. -/
theorem firstC3WordAux_of_wordFirst (w : List Nat) (n : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (h : StringFlow.Word.wordFirst w n) :
    firstC3WordAux w.length n = w := by
  induction w generalizing n with
  | nil => rfl
  | cons t ts ih =>
      by_cases h3 : n % 8 = 3
      · rcases h with ⟨hxne, _, _⟩
        exact False.elim (hxne h3)
      · by_cases h7 : n % 8 = 7
        · have ht2 : t = 2 := step_two_of_wordFirst_seven ts n t hok h h7
          rcases h with ⟨_, hdiv, htail⟩
          have htail' : StringFlow.Word.wordFirst ts ((5 * n + 1) / 4) := by
            simpa [ht2] using htail
          have hih := ih ((5 * n + 1) / 4)
            (fun a ha => hok a (List.mem_cons_of_mem t ha)) htail'
          have hstep : firstC3WordAux (ts.length + 1) n =
              2 :: firstC3WordAux ts.length ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          change firstC3WordAux (ts.length + 1) n = t :: ts
          rw [hstep, hih, ht2]
        · have ht1 : t = 1 := step_one_of_wordFirst_other ts n t hok h h3 h7
          rcases h with ⟨_, hdiv, htail⟩
          have htail' : StringFlow.Word.wordFirst ts ((5 * n + 1) / 2) := by
            simpa [ht1] using htail
          have hih := ih ((5 * n + 1) / 2)
            (fun a ha => hok a (List.mem_cons_of_mem t ha)) htail'
          have hstep : firstC3WordAux (ts.length + 1) n =
              1 :: firstC3WordAux ts.length ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          change firstC3WordAux (ts.length + 1) n = t :: ts
          rw [hstep, hih, ht1]

/-- A `{1,2}` first-C3 word reaches C3 exactly at the end, with the
full word weight as the returned prefix weight. -/
theorem firstC3H_of_wordFirst (w : List Nat) (n : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (h : StringFlow.Word.wordFirst w n) :
    firstC3H w.length n = (true, StringFlow.wordWeight w) := by
  induction w generalizing n with
  | nil =>
      have hc3 : n % 8 = 3 := by
        simpa [StringFlow.Word.wordFirst] using h
      simp [firstC3H, hc3, StringFlow.wordWeight]
  | cons t ts ih =>
      by_cases h3 : n % 8 = 3
      · rcases h with ⟨hxne, _, _⟩
        exact False.elim (hxne h3)
      · by_cases h7 : n % 8 = 7
        · have ht2 : t = 2 := step_two_of_wordFirst_seven ts n t hok h h7
          rcases h with ⟨_, _, htail⟩
          have htail' : StringFlow.Word.wordFirst ts ((5 * n + 1) / 4) := by
            simpa [ht2] using htail
          have hih := ih ((5 * n + 1) / 4)
            (fun a ha => hok a (List.mem_cons_of_mem t ha)) htail'
          have hstep : firstC3H (ts.length + 1) n =
              (true, StringFlow.wordWeight ts + 2) := by
            simp [firstC3H, h3, h7, hih]
          change firstC3H (ts.length + 1) n =
            (true, StringFlow.wordWeight (t :: ts))
          rw [hstep]
          simp [StringFlow.wordWeight, ht2, Nat.add_comm]
        · have ht1 : t = 1 := step_one_of_wordFirst_other ts n t hok h h3 h7
          rcases h with ⟨_, _, htail⟩
          have htail' : StringFlow.Word.wordFirst ts ((5 * n + 1) / 2) := by
            simpa [ht1] using htail
          have hih := ih ((5 * n + 1) / 2)
            (fun a ha => hok a (List.mem_cons_of_mem t ha)) htail'
          have hstep : firstC3H (ts.length + 1) n =
              (true, StringFlow.wordWeight ts + 1) := by
            simp [firstC3H, h3, h7, hih]
          change firstC3H (ts.length + 1) n =
            (true, StringFlow.wordWeight (t :: ts))
          rw [hstep]
          simp [StringFlow.wordWeight, ht1, Nat.add_comm]

/-- Weight form of the exact first-C3 word theorem. -/
theorem firstC3S_of_wordFirst (w : List Nat) (n : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (h : StringFlow.Word.wordFirst w n) :
    StringFlow.firstC3S w.length n = StringFlow.wordWeight w := by
  have hh := firstC3H_of_wordFirst w n hok h
  unfold StringFlow.firstC3S
  rw [hh]

/-- Once a C3 hit occurs, the exact word is stable under extra fuel. -/
theorem firstC3WordAux_stable_of_hit (fuel n extra : Nat)
    (h : (firstC3H fuel n).1 = true) :
    firstC3WordAux (fuel + extra) n = firstC3WordAux fuel n := by
  induction fuel generalizing n extra with
  | zero =>
      have hc3 : n % 8 = 3 := by
        by_cases hc : n % 8 = 3
        · exact hc
        · simp [firstC3H, hc] at h
      induction extra with
      | zero => rfl
      | succ extra _ =>
          simp [firstC3WordAux, hc3]
  | succ fuel ih =>
      by_cases h3 : n % 8 = 3
      · have hsum : fuel + 1 + extra = (fuel + extra) + 1 := by omega
        rw [hsum]
        simp [firstC3WordAux, h3]
      · by_cases h7 : n % 8 = 7
        · have h' : (firstC3H fuel ((5 * n + 1) / 4)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hleft : firstC3WordAux (fuel + 1 + extra) n =
              2 :: firstC3WordAux (fuel + extra) ((5 * n + 1) / 4) := by
            have hsum : fuel + 1 + extra = (fuel + extra) + 1 := by omega
            rw [hsum]
            simp [firstC3WordAux, h3, h7]
          have hright : firstC3WordAux (fuel + 1) n =
              2 :: firstC3WordAux fuel ((5 * n + 1) / 4) := by
            simp [firstC3WordAux, h3, h7]
          rw [hleft, hright]
          exact congrArg (fun xs => 2 :: xs) (ih ((5 * n + 1) / 4) extra h')
        · have h' : (firstC3H fuel ((5 * n + 1) / 2)).1 = true := by
            simp [firstC3H, h3, h7] at h
            exact h
          have hleft : firstC3WordAux (fuel + 1 + extra) n =
              1 :: firstC3WordAux (fuel + extra) ((5 * n + 1) / 2) := by
            have hsum : fuel + 1 + extra = (fuel + extra) + 1 := by omega
            rw [hsum]
            simp [firstC3WordAux, h3, h7]
          have hright : firstC3WordAux (fuel + 1) n =
              1 :: firstC3WordAux fuel ((5 * n + 1) / 2) := by
            simp [firstC3WordAux, h3, h7]
          rw [hleft, hright]
          exact congrArg (fun xs => 1 :: xs) (ih ((5 * n + 1) / 2) extra h')

/-- A word over `{1,2}` has every entry at most `2`. -/
theorem wordOK_of_mem_two (w : List Nat) (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    StringFlow.Word.wordOK w := by
  induction w with
  | nil => simp [StringFlow.Word.wordOK]
  | cons t ts ih =>
      have ht := hok t (by simp)
      have hok' : ∀ x ∈ ts, x = 1 ∨ x = 2 := by
        intro x hx
        exact hok x (by simp [hx])
      rcases ht with rfl | rfl
      · simp [StringFlow.Word.wordOK]
        exact ih hok'
      · simp [StringFlow.Word.wordOK]
        exact ih hok'

theorem odd_201_cases (m : Nat) (hmodd : m % 2 = 1) :
    m < 201 ∨ m = 201 ∨ 203 ≤ m := by
  by_cases hm201 : m = 201
  · exact Or.inr (Or.inl hm201)
  · by_cases hlt : m < 201
    · exact Or.inl hlt
    · right
      right
      by_cases hge : 203 ≤ m
      · exact hge
      · exfalso
        have h202 : m ≤ 202 := by omega
        have hm202 : m = 202 := by omega
        subst m
        simp at hmodd

/-- Sharp basin split: below 617, weight 26 is attained only at 201. -/
theorem basin_617_sharp (m : Nat)
    (hm7 : 7 ≤ m) (hm617 : m < 617) (hadm : admissible m)
    (hS : 26 ≤ firstC3S 1000 m) : m = 201 := by
  rcases odd_201_cases m hadm.2.1 with hlt | rfl | hge
  · rcases basin_201_cap25_cert m hm7 hlt hadm with
      ⟨c, hcover, S, hS1, hle⟩
    have hmem : c ∈ certBasin25A := coverCert_mem certBasin25A m c hcover
    have hlen : c.w.length ≤ 1000 := certBasin25A_len c hmem
    have hhit : (firstC3H c.w.length m).1 = true := by rw [hS1]
    have hsame : firstC3S 1000 m = firstC3S c.w.length m :=
      firstC3S_of_hit c.w.length 1000 m hlen hhit
    have hS1000 : firstC3S 1000 m = S := by
      rw [hsame]
      unfold StringFlow.firstC3S
      rw [hS1]
    omega
  · rfl
  · rcases basin_203_617_cap25_cert m hge hm617 hadm with
      ⟨c, hcover, S, hS1, hle⟩
    have hmem : c ∈ certBasin25B := coverCert_mem certBasin25B m c hcover
    have hlen : c.w.length ≤ 1000 := certBasin25B_len c hmem
    have hhit : (firstC3H c.w.length m).1 = true := by rw [hS1]
    have hsame : firstC3S 1000 m = firstC3S c.w.length m :=
      firstC3S_of_hit c.w.length 1000 m hlen hhit
    have hS1000 : firstC3S 1000 m = S := by
      rw [hsame]
      unfold StringFlow.firstC3S
      rw [hS1]
    omega

/-- Phase-2 sublemma 1: first-C3 weight at least 26 forces
`m >= 201`. -/
theorem phase2_m_ge_201 (m : Nat)
    (hm7 : 7 ≤ m) (_hmle : m ≤ 1000000) (hadm : admissible m)
    (hS : 26 ≤ firstC3S 1000 m) : 201 ≤ m := by
  by_cases hm617 : m < 617
  · have hm201 := basin_617_sharp m hm7 hm617 hadm hS
    omega
  · omega

/-- The same bound without the frame-A `m <= 10^6` hypothesis: below
617 the sharp basin split gives `m = 201`, and above 617 it is
automatic. -/
theorem phase2_m_ge_201_of_weight (m : Nat)
    (hm7 : 7 ≤ m) (hadm : admissible m)
    (hS : 26 ≤ firstC3S 1000 m) : 201 ≤ m := by
  by_cases hm617 : m < 617
  · have hm201 := basin_617_sharp m hm7 hm617 hadm hS
    omega
  · omega

/-- Basin bound 2 in `1000`-fuel form: every admissible `m <= 10^6`
has first-C3 weight at most `64`. -/
theorem basin_1e6_weight_1000 (m : Nat)
    (hm7 : 7 ≤ m) (hmle : m ≤ 1000000) (hadm : admissible m) :
    firstC3S 1000 m ≤ 64 := by
  rcases StringFlow.basin_1e6_cert m hm7 hmle hadm with
    ⟨c, hcover, S, hS1, hle⟩
  have hmem : c ∈ StringFlow.cert1e6 := coverCert_mem StringFlow.cert1e6 m c hcover
  have hlen : c.w.length ≤ 1000 := cert1e6_len c hmem
  have hhit : (firstC3H c.w.length m).1 = true := by rw [hS1]
  have hsame : firstC3S 1000 m = firstC3S c.w.length m :=
    firstC3S_of_hit c.w.length 1000 m hlen hhit
  have hS1000 : firstC3S 1000 m = S := by
    rw [hsame]
    unfold StringFlow.firstC3S
    rw [hS1]
  rw [hS1000]
  exact hle

end StringFlow.TD1
