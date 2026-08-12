import Mathlib
import Td1
import StageOneScan

/-!
# TD-1 phase-2 exact rational checks

This module certifies the two exact `mt >= 8/3` checks used by
`ph_qb_gc_chain.md` 52.21.2bis:

- `201 * t(31) >= 8/3`,
- `617 * t(59) >= 8/3`,

where `t(P) = 2 * (1 - 5^P / 2^T)` and `T = tCeil P` is the tabulated
ceiling of `P * log2 5`.  No `Real`/`log` is needed: this is the exact
rational form of `t = 2 * (1 - 2^(-delta))`.
-/

namespace StringFlow.TD1

/-- The exact rising-step factor `t = 2 * (1 - 2^(-delta))` for a
given `P`, expressed as `2 * (1 - 5^P / 2^T)`. -/
def tRat (P : Nat) : Rat :=
  2 * (1 - ((5 ^ P : Nat) : Rat) / ((2 ^ tCeil P : Nat) : Rat))

/-- The phase-2 upper-branch condition `m * t >= 8/3`. -/
def phase2Upper (m P : Nat) : Bool :=
  decide ((m : Rat) * tRat P >= (8 / 3 : Rat))

/-- The two delta-record checks from 52.21.2bis. -/
def phase2DeltaOK : Bool :=
  phase2Upper 201 31 && phase2Upper 617 59

theorem phase2_delta_check : phase2DeltaOK = true := by
  native_decide

theorem phase2_upper_201_31 : phase2Upper 201 31 = true := by
  native_decide

theorem phase2_upper_617_59 : phase2Upper 617 59 = true := by
  native_decide

theorem phase2_upper_617_31 : phase2Upper 617 31 = true := by
  native_decide

/-- Phase-2 feasibility: the length/weight match is realizable with
`S = L + U <= 64`.  Values with `P >= 205` are automatically
infeasible because `tCeil P = 0`. -/
def feasible64 (b Q L : Nat) : Bool :=
  let T := tCeil (L + Q)
  let U := uReq b Q L
  decide (1 ≤ b && b ≤ 2 && 8 ≤ Q && 1 ≤ L &&
          L + 3 * Q + b ≤ T &&
          (if b = 1 then U ≤ L - 1 else 1 ≤ U && U ≤ L) &&
          L + U ≤ 64)

/-- B0 certificate: every phase-2 feasible triple has `P <= 188`. -/
def b0OK : Bool :=
  allInRange 8 205 (fun Q =>
    allInRange 1 205 (fun L =>
      allInRange 1 3 (fun b =>
        ! feasible64 b Q L || decide (L + Q ≤ 188))))

theorem tCeil_pos_lt_205 (P : Nat) (h : 0 < tCeil P) : P < 205 := by
  by_cases hP : P < 205
  · exact hP
  · have ht := tCeil_large P (by omega)
    omega

theorem feasible64_T_pos (b Q L : Nat) (h : feasible64 b Q L = true) :
    0 < tCeil (L + Q) := by
  have hp := of_decide_eq_true h
  simp at hp
  omega

theorem b0_check : b0OK = true := by
  native_decide

theorem b0_spec (b Q L : Nat) (h : feasible64 b Q L = true) :
    L + Q ≤ 188 := by
  have hP : L + Q < 205 := tCeil_pos_lt_205 (L + Q) (feasible64_T_pos b Q L h)
  have hp := of_decide_eq_true h
  simp at hp
  have hQ8 : 8 ≤ Q := by omega
  have hQ : Q < 205 := by omega
  have hL1 : 1 ≤ L := by omega
  have hL : L < 205 := by omega
  have hb1 : 1 ≤ b := by omega
  have hb2 : b < 3 := by omega
  have hQrange := allInRange_spec 8 205
    (fun Q =>
      allInRange 1 205 (fun L =>
        allInRange 1 3 (fun b =>
          ! feasible64 b Q L || decide (L + Q ≤ 188))))
    b0_check Q hQ8 hQ
  have hLrange := allInRange_spec 1 205
    (fun L =>
      allInRange 1 3 (fun b =>
        ! feasible64 b Q L || decide (L + Q ≤ 188)))
    hQrange L hL1 hL
  have hbrange := allInRange_spec 1 3
    (fun b => ! feasible64 b Q L || decide (L + Q ≤ 188))
    hLrange b hb1 hb2
  have hbr := hbrange
  simp [h] at hbr
  exact hbr

/-- Phase-2 feasibility forces the certified `P` range
`9 <= L+Q < 205`. -/
theorem feasible64_range (b Q L : Nat) (h : feasible64 b Q L = true) :
    9 ≤ L + Q ∧ L + Q < 205 := by
  have hT : 0 < tCeil (L + Q) := feasible64_T_pos b Q L h
  have hP : L + Q < 205 := tCeil_pos_lt_205 (L + Q) hT
  have hp := of_decide_eq_true h
  simp at hp
  constructor <;> omega

/-- Phase-2 feasibility forces `Q >= 8`. -/
theorem feasible64_Q_ge_8 (b Q L : Nat) (h : feasible64 b Q L = true) :
    8 ≤ Q := by
  have hp := of_decide_eq_true h
  simp at hp
  omega

/-- Phase-2 feasibility forces `L >= 1`. -/
theorem feasible64_L_ge_1 (b Q L : Nat) (h : feasible64 b Q L = true) :
    1 ≤ L := by
  have hp := of_decide_eq_true h
  simp at hp
  omega

/-- Phase-2 feasibility from the exact cycle parameters: the wrapper
derives `feasible64` once `tCeil(L+Q) = L+3Q+b+U`, the `U` bounds,
and `S <= 64` are known. -/
theorem feasible64_of_cycle_params (b Q L U : Nat)
    (hb : b = 1 ∨ b = 2) (hQ8 : 8 ≤ Q) (hL1 : 1 ≤ L)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L)
    (hS64 : L + U ≤ 64) :
    feasible64 b Q L = true := by
  rcases hb with rfl | rfl
  · unfold feasible64 uReq
    rw [hT]
    rw [show (L + 3 * Q + 1 + U) - (L + 3 * Q + 1) = U by omega]
    have hU1' : U ≤ L - 1 := by simpa using hU1
    simp [hQ8, hL1, hU1', hS64, Nat.add_comm]
    try omega
  · unfold feasible64 uReq
    rw [hT]
    rw [show (L + 3 * Q + 2 + U) - (L + 3 * Q + 2) = U by omega]
    have hU1' : 1 ≤ U ∧ U ≤ L := by simpa using hU1
    simp [hQ8, hL1, hU1', hS64, Nat.add_comm]
    try omega

/-- From the exact ceiling identity, `uReq = U` follows. -/
theorem uReq_eq_of_tCeil (b Q L U : Nat)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U) :
    StringFlow.uReq b Q L = U := by
  unfold StringFlow.uReq
  rw [hT]
  omega

/-- From feasibility and `uReq = U`, recover the exact
`tCeil(L+Q) = L + 3Q + b + U`. -/
theorem uReq_T_of_feasible (b Q L U : Nat)
    (hfeas : feasible64 b Q L = true) (hU : StringFlow.uReq b Q L = U) :
    tCeil (L + Q) = L + 3 * Q + b + U := by
  unfold StringFlow.uReq at hU
  have hp := of_decide_eq_true hfeas
  simp at hp
  omega

/-- Phase-2 feasibility plus `uReq = U` gives `U <= L`. -/
theorem uReq_le_L_of_feasible (b Q L U : Nat)
    (hb : b = 1 ∨ b = 2) (hfeas : feasible64 b Q L = true)
    (hU : StringFlow.uReq b Q L = U) : U ≤ L := by
  rcases hb with rfl | rfl
  · have hp := of_decide_eq_true hfeas
    simp [hU] at hp
    omega
  · have hp := of_decide_eq_true hfeas
    simp [hU] at hp
    omega

/-- Phase-2 feasibility plus `uReq = U` gives the strict A/B family
`U` bounds from 52.7/52.12: the A family has `t_last = 1` and the
B family has `t_last = 2`. -/
theorem uReq_bounds_of_feasible (b Q L U : Nat)
    (hfeas : feasible64 b Q L = true) (hU : StringFlow.uReq b Q L = U) :
    if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L := by
  unfold feasible64 at hfeas
  rw [hU] at hfeas
  have hp := of_decide_eq_true hfeas
  simp at hp
  exact hp.left.right

/-- A phase-2-feasible triple with the stage-one parameter ranges and
`S <= 25` is also stage-one feasible. -/
theorem feasible_of_feasible64 (b Q L : Nat)
    (h : feasible64 b Q L = true)
    (hQ50 : Q ≤ 50) (hL25 : L ≤ 25)
    (hS25 : L + StringFlow.uReq b Q L ≤ 25) :
    StringFlow.feasible b Q L = true := by
  unfold feasible64 StringFlow.uReq at h
  unfold StringFlow.feasible StringFlow.uReq
  unfold StringFlow.uReq at hS25
  have hp := of_decide_eq_true h
  simp at hp
  simp [hp, hQ50, hL25, Nat.add_comm, Bool.and_eq_true, decide_eq_true_eq]
  rw [Nat.add_comm Q L]
  rcases hp with ⟨hA, hS64⟩
  rcases hA with ⟨hB, hUb⟩
  rcases hB with ⟨hC, hTle⟩
  rcases hC with ⟨hD, hL1⟩
  rcases hD with ⟨hE, hQ8⟩
  rcases hE with ⟨hb1, hb2⟩
  by_cases hb1case : b = 1
  · subst b
    simp at hUb ⊢
    omega
  · have hb2' : b = 2 := by omega
    subst b
    simp at hUb ⊢
    omega

/-- Stage-one parameter certificate: with `S <= 25`, phase-2
feasibility forces `Q <= 50`. -/
def stage1QOK : Bool :=
  allInRange 8 205 (fun Q =>
    allInRange 1 3 (fun b =>
      allInRange 1 26 (fun L =>
        ! feasible64 b Q L || decide (25 < L + StringFlow.uReq b Q L) ||
          decide (Q ≤ 50))))

theorem stage1Q_check : stage1QOK = true := by
  native_decide

theorem stage1_Q_le_50 (b Q L : Nat)
    (h : feasible64 b Q L = true)
    (hS25 : L + StringFlow.uReq b Q L ≤ 25) : Q ≤ 50 := by
  have hb1 : 1 ≤ b := by
    have hp := of_decide_eq_true h
    simp at hp
    omega
  have hb2 : b < 3 := by
    have hp := of_decide_eq_true h
    simp at hp
    omega
  have hQ8 : 8 ≤ Q := feasible64_Q_ge_8 b Q L h
  have hQ205 : Q < 205 := by
    have hrange := feasible64_range b Q L h
    omega
  have hL1 : 1 ≤ L := feasible64_L_ge_1 b Q L h
  have hL26 : L < 26 := by
    have hUge0 : 0 ≤ StringFlow.uReq b Q L := by omega
    omega
  have hQ := allInRange_spec 8 205
    (fun Q => allInRange 1 3 (fun b =>
      allInRange 1 26 (fun L =>
        ! feasible64 b Q L || decide (25 < L + StringFlow.uReq b Q L) ||
          decide (Q ≤ 50))))
    stage1Q_check Q hQ8 hQ205
  have hb := allInRange_spec 1 3
    (fun b => allInRange 1 26 (fun L =>
        ! feasible64 b Q L || decide (25 < L + StringFlow.uReq b Q L) ||
          decide (Q ≤ 50)))
    hQ b hb1 hb2
  have hL := allInRange_spec 1 26
    (fun L => ! feasible64 b Q L || decide (25 < L + StringFlow.uReq b Q L) ||
          decide (Q ≤ 50))
    hb L hL1 hL26
  simp [h] at hL
  rcases hL with hbad | hq
  · exfalso
    omega
  · exact hq

/-- With `S <= 25`, the rise length is at most `25`. -/
theorem stage1_L_le_25 (b Q L : Nat)
    (hS25 : L + StringFlow.uReq b Q L ≤ 25) : L ≤ 25 := by
  omega

/-- On every stage-one feasible triple, the threshold `tableM0` is
strictly below the modulus `tableMod`. -/
def stage1M0LtModOK : Bool :=
  allInRange 8 51 (fun Q =>
    allInRange 1 26 (fun L =>
      allInRange 1 3 (fun b =>
        ! StringFlow.feasible b Q L ||
          decide (StringFlow.tableM0 b Q L < StringFlow.tableMod b Q L))))

theorem stage1M0LtMod_check : stage1M0LtModOK = true := by
  native_decide

theorem stage1_m0_lt_mod (b Q L : Nat)
    (hfeas : StringFlow.feasible b Q L = true) :
    StringFlow.tableM0 b Q L < StringFlow.tableMod b Q L := by
  have hb1 : 1 ≤ b := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hb2 : b < 3 := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hQ8 : 8 ≤ Q := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hQ51 : Q < 51 := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hL1 : 1 ≤ L := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hL26 : L < 26 := by
    have hp := of_decide_eq_true hfeas
    simp at hp
    omega
  have hQ := allInRange_spec 8 51
    (fun Q => allInRange 1 26 (fun L =>
      allInRange 1 3 (fun b =>
        ! StringFlow.feasible b Q L ||
          decide (StringFlow.tableM0 b Q L < StringFlow.tableMod b Q L))))
    stage1M0LtMod_check Q hQ8 hQ51
  have hL := allInRange_spec 1 26
    (fun L => allInRange 1 3 (fun b =>
        ! StringFlow.feasible b Q L ||
          decide (StringFlow.tableM0 b Q L < StringFlow.tableMod b Q L)))
    hQ L hL1 hL26
  have hb := allInRange_spec 1 3
    (fun b => ! StringFlow.feasible b Q L ||
          decide (StringFlow.tableM0 b Q L < StringFlow.tableMod b Q L))
    hL b hb1 hb2
  simp [hfeas] at hb
  exact hb

/-- The threshold bound `m < tableM0` implies the modulus bound
`m < tableMod` on stage-one feasible triples. -/
theorem stage1_hmmod_of_hmlt (b Q L m : Nat)
    (hfeas : StringFlow.feasible b Q L = true)
    (hmlt : m < StringFlow.tableM0 b Q L) :
    m < StringFlow.tableMod b Q L :=
  lt_trans hmlt (stage1_m0_lt_mod b Q L hfeas)

/-- The exact Rat form of the G5' record checks: for `P < 59`,
`t(P) >= t(31)`, and for `59 <= P < 205`, `t(P) >= t(59)`. -/
def phase2RecordRatOK : Bool :=
  allInRange 9 59 (fun P => decide (tRat 31 ≤ tRat P)) &&
    allInRange 59 205 (fun P => decide (tRat 59 ≤ tRat P))

theorem phase2_record_rat_check : phase2RecordRatOK = true := by
  native_decide

theorem phase2_tRat_ge_t31 (P : Nat) (hP9 : 9 ≤ P) (hP59 : P < 59) :
    tRat 31 ≤ tRat P := by
  have hAll := phase2_record_rat_check
  have h1 : allInRange 9 59 (fun P => decide (tRat 31 ≤ tRat P)) = true := by
    simp [phase2RecordRatOK] at hAll
    exact hAll.1
  have hP := allInRange_spec 9 59 (fun P => decide (tRat 31 ≤ tRat P))
    h1 P hP9 hP59
  exact of_decide_eq_true hP

theorem phase2_tRat_ge_t59 (P : Nat) (hP59 : 59 ≤ P) (hP205 : P < 205) :
    tRat 59 ≤ tRat P := by
  have hAll := phase2_record_rat_check
  have h2 : allInRange 59 205 (fun P => decide (tRat 59 ≤ tRat P)) = true := by
    simp [phase2RecordRatOK] at hAll
    exact hAll.2
  have hP := allInRange_spec 59 205 (fun P => decide (tRat 59 ≤ tRat P))
    h2 P hP59 hP205
  exact of_decide_eq_true hP

/-- The phase-2 upper-bound certificate: the two record checks and
the two base `mt >= 8/3` checks. -/
def phase2UpperBoundOK : Bool :=
  phase2RecordRatOK && phase2DeltaOK

theorem phase2_upper_bound_check : phase2UpperBoundOK = true := by
  native_decide

/-- Decode a `phase2Upper` boolean certificate. -/
theorem phase2_upper_spec (m P : Nat) (h : phase2Upper m P = true) :
    (m : Rat) * tRat P ≥ (8 / 3 : Rat) := by
  exact of_decide_eq_true h

/-- In phase 2, `m >= 617` and `9 <= P < 205` already give
`m * t(P) >= 8/3`: use the G5' record at `P = 59` or `P = 31`. -/
theorem phase2_mt_ge_of_m_ge_617 (m P : Nat)
    (hm : 617 ≤ m) (hP9 : 9 ≤ P) (hP205 : P < 205) :
    (m : Rat) * tRat P ≥ (8 / 3 : Rat) := by
  by_cases hP59 : P < 59
  · have ht := phase2_tRat_ge_t31 P hP9 hP59
    have hbase : (617 : Rat) * tRat 31 ≥ (8 / 3 : Rat) :=
      phase2_upper_spec 617 31 phase2_upper_617_31
    have hnonneg : 0 ≤ tRat 31 := by native_decide
    have hnonneg' : 0 ≤ tRat P := le_trans hnonneg ht
    have hmul : (617 : Rat) * tRat P ≤ (m : Rat) * tRat P := by
      have hmRat : (617 : Rat) ≤ (m : Rat) := by exact_mod_cast hm
      nlinarith
    nlinarith
  · have hP59le : 59 ≤ P := by omega
    have ht := phase2_tRat_ge_t59 P hP59le hP205
    have hbase : (617 : Rat) * tRat 59 ≥ (8 / 3 : Rat) :=
      phase2_upper_spec 617 59 phase2_upper_617_59
    have hnonneg : 0 ≤ tRat 59 := by native_decide
    have hnonneg' : 0 ≤ tRat P := le_trans hnonneg ht
    have hmul : (617 : Rat) * tRat P ≤ (m : Rat) * tRat P := by
      have hmRat : (617 : Rat) ≤ (m : Rat) := by exact_mod_cast hm
      nlinarith
    nlinarith

/-- In phase 2, `m >= 201` and `9 <= P < 59` already give
`m * t(P) >= 8/3` from the G5' record at `P = 31`. -/
theorem phase2_mt_ge_of_m_ge_201 (m P : Nat)
    (hm : 201 ≤ m) (hP9 : 9 ≤ P) (hP59 : P < 59) :
    (m : Rat) * tRat P ≥ (8 / 3 : Rat) := by
  have ht := phase2_tRat_ge_t31 P hP9 hP59
  have hbase : (201 : Rat) * tRat 31 ≥ (8 / 3 : Rat) :=
    phase2_upper_spec 201 31 phase2_upper_201_31
  have hnonneg : 0 ≤ tRat 31 := by native_decide
  have hnonneg' : 0 ≤ tRat P := le_trans hnonneg ht
  have hmul : (201 : Rat) * tRat P ≤ (m : Rat) * tRat P := by
    have hmRat : (201 : Rat) ≤ (m : Rat) := by exact_mod_cast hm
    nlinarith
  nlinarith

/-- B2 in Rat form: with the B1 bridge (`m < 617` forces `m = 201`
and `P < 59`), every phase-2 `P` in `[9,205)` satisfies
`m * t(P) >= 8/3`. -/
theorem phase2_mt_ge_of_b2 (m P : Nat)
    (hP9 : 9 ≤ P) (hP205 : P < 205)
    (h201 : m < 617 → m = 201 ∧ P < 59) :
    (m : Rat) * tRat P ≥ (8 / 3 : Rat) := by
  by_cases hm617 : m < 617
  · rcases h201 hm617 with ⟨rfl, hP59⟩
    exact phase2_mt_ge_of_m_ge_201 201 P (by omega) hP9 hP59
  · have hm617' : 617 ≤ m := by omega
    exact phase2_mt_ge_of_m_ge_617 m P hm617' hP9 hP205

/-- B1 bridge in P form: `L = 20`, `b = 2`, `U_req = 6` force
`Q = 28`, hence `P = 20 + Q < 59`. -/
theorem phase2_b1_P_lt_59 (Q P : Nat)
    (hQ8 : 8 ≤ Q) (hU : StringFlow.uReq 2 Q 20 = 6)
    (hP : P = 20 + Q) : P < 59 := by
  have hQ28 := b1B_uReq_solutions_full Q hQ8 hU
  omega

/-- The B1 bridge used by `phase2_mt_ge_of_b2`: for `m = 201`,
`m < 617` is automatic and the P bound comes from B1. -/
theorem phase2_b1_bridge (m Q P : Nat)
    (hm201 : m = 201) (hQ8 : 8 ≤ Q)
    (hU : StringFlow.uReq 2 Q 20 = 6) (hP : P = 20 + Q) :
    m < 617 → m = 201 ∧ P < 59 := by
  intro hm617
  have hP59 := phase2_b1_P_lt_59 Q P hQ8 hU hP
  constructor <;> omega

/-- B1 in wrapper-ready form: once `m = 201`, `L = 20` and
`U_req = 6` are known, the `Qb8Cycle2.hB1` condition follows. -/
theorem phase2_b1_condition_of_201 (m Q L : Nat)
    (hm201 : m = 201) (hQ8 : 8 ≤ Q)
    (hL20 : L = 20) (hU : StringFlow.uReq 2 Q L = 6) :
    m < 617 → m = 201 ∧ L + Q < 59 := by
  intro hm617
  have hP59 : L + Q < 59 := by
    rw [hL20]
    have hU20 : StringFlow.uReq 2 Q 20 = 6 := by
      rw [hL20] at hU
      exact hU
    exact phase2_b1_P_lt_59 Q (20 + Q) hQ8 hU20 rfl
  constructor <;> omega

/-- B1 + B2 package: once the wrapper supplies `m = 201`,
`L = 20`, `b = 2`, `U_req = 6` and `P = 20 + Q`, phase 2 gives
`m * t(P) >= 8/3`. -/
theorem phase2_mt_ge_of_b2_of_201 (m Q P : Nat)
    (hm201 : m = 201) (hQ8 : 8 ≤ Q)
    (hU : StringFlow.uReq 2 Q 20 = 6) (hP : P = 20 + Q)
    (hP9 : 9 ≤ P) (hP205 : P < 205) :
    (m : Rat) * tRat P ≥ (8 / 3 : Rat) := by
  exact phase2_mt_ge_of_b2 m P hP9 hP205
    (phase2_b1_bridge m Q P hm201 hQ8 hU hP)

end StringFlow.TD1
