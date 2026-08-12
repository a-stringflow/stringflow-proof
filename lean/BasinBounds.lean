import Init

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Basin bounds for the 5x+1 first C3 hit

This module formalizes the finite orbit statements used by 52.21.2:
for the accelerated 5x+1 map, every admissible `m` below a bound
reaches its first C3 start with total prefix weight `S = L + U` at
most a fixed cap.  The finite bounds are proved by kernel `decide`.
-/

namespace StringFlow

/-- `n` is a C3 start: `5n+1` is divisible by 8 (for odd `n`, `n ≡ 3 (mod 8)`). -/
def isC3 (n : Nat) : Prop := n % 8 = 3

/-- One accelerated step on an odd non-C3 value:
weight 2 for `n ≡ 7 (mod 8)`, weight 1 otherwise. -/
def stepC3 (n : Nat) : Nat :=
  if n % 8 = 7 then (5 * n + 1) / 4 else (5 * n + 1) / 2

/-- Iterate until the first C3 hit; return `(L, U, M)` or `none` if no
hit occurs within `fuel` steps. -/
def iterateC3 : Nat → Nat → Option (Nat × Nat × Nat)
  | 0, n => if n % 8 = 3 then some (0, 0, n) else none
  | fuel + 1, n =>
      if n % 8 = 3 then some (0, 0, n)
      else if n % 8 = 7 then
        match iterateC3 fuel ((5 * n + 1) / 4) with
        | some (L, U, M) => some (L + 1, U + 1, M)
        | none => none
      else
        match iterateC3 fuel ((5 * n + 1) / 2) with
        | some (L, U, M) => some (L + 1, U, M)
        | none => none

/-- The prefix weight `S = L + U` reaches C3 within `fuel` steps and
obeys `S ≤ cap`. -/
def basinOKBool (fuel cap : Nat) (m : Nat) : Bool :=
  match iterateC3 fuel m with
  | some (L, U, _) => decide (L + U ≤ cap)
  | none => false

/-- The first-C3 prefix weight `S = L + U` (0 if the fuel cap is hit
without reaching C3). -/
def basinS (fuel : Nat) (m : Nat) : Nat :=
  match iterateC3 fuel m with
  | some (L, U, _) => L + U
  | none => 0

theorem basinOKBool_eq_true (fuel cap m : Nat) :
    basinOKBool fuel cap m = true ↔
      ∃ L U M, iterateC3 fuel m = some (L, U, M) ∧ L + U ≤ cap := by
  unfold basinOKBool
  cases h : iterateC3 fuel m with
  | none => constructor <;> intro h2 <;> simp at h2
  | some p => cases p with
    | mk L p2 => cases p2 with
      | mk U M =>
        simp only [decide_eq_true_eq]
        constructor
        · intro hle
          exact ⟨L, U, M, rfl, hle⟩
        · rintro ⟨L', U', M', hEq, hle⟩
          cases hEq
          exact hle

/-- Admissible starts: at least 7, odd, and not divisible by 5. -/
def admissible (m : Nat) : Prop := 7 ≤ m ∧ m % 2 = 1 ∧ m % 5 ≠ 0

/-- Boolean version of `admissible`. -/
def admissibleB (m : Nat) : Bool :=
  decide (7 ≤ m) && decide (m % 2 = 1) && decide (m % 5 ≠ 0)

theorem admissibleB_eq (m : Nat) : admissibleB m = true ↔ admissible m := by
  simp [admissibleB, admissible, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Check the basin bound for every admissible `m < N`, by recursion. -/
def allBasinOK (fuel cap : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
      (if admissibleB n then basinOKBool fuel cap n else true)
      && allBasinOK fuel cap n

theorem allBasinOK_spec (fuel cap N : Nat) :
    allBasinOK fuel cap N = true →
    ∀ m : Nat, admissible m → m < N → basinOKBool fuel cap m = true := by
  induction N with
  | zero =>
      intro h m hm hlt
      omega
  | succ N ih =>
      intro h m hm hlt
      have hN : allBasinOK fuel cap N = true := by
        have := congrArg (fun b : Bool => b && allBasinOK fuel cap N) h
        -- `h` unfolds to `(if ...) && allBasinOK ... = true`
        simp [allBasinOK, Bool.and_eq_true] at h
        exact h.2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hltN | heqN
      · exact ih hN m hm hltN
      · subst m
        simp [allBasinOK] at h
        have : admissibleB N = true := by
          rw [admissibleB_eq]
          exact hm
        simp [this] at h
        exact h.1

/-- Check `P` for every `m` in `[lo, hi)`. -/
def allInRange (lo hi : Nat) (P : Nat → Bool) : Bool :=
  if hi ≤ lo then true
  else P (hi - 1) && allInRange lo (hi - 1) P
termination_by hi
decreasing_by omega

theorem allInRange_spec (lo hi : Nat) (P : Nat → Bool) :
    allInRange lo hi P = true →
    ∀ m : Nat, lo ≤ m → m < hi → P m = true := by
  induction hi with
  | zero =>
      intro h m hlo hlt
      omega
  | succ hi ih =>
      intro h m hlo hlt
      have h' : allInRange lo hi P = true := by
        unfold allInRange at h
        by_cases hle : hi + 1 ≤ lo
        · omega
        · have hAnd : P hi = true ∧ allInRange lo hi P = true := by
            simpa [hle] using h
          exact hAnd.2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact ih h' m hlo hlt'
      · subst m
        unfold allInRange at h
        by_cases hle : hi + 1 ≤ lo
        · omega
        · have hAnd : P hi = true ∧ allInRange lo hi P = true := by
            simpa [hle] using h
          exact hAnd.1

/-- `S = 26` only at `m = 201`, restricted to admissible starts. -/
def s26only201Adm (m : Nat) : Bool :=
  if admissibleB m then decide (basinS 100 m = 26 → m = 201) else true

theorem s26only201Adm_check : allInRange 7 617 s26only201Adm = true := by
  native_decide

/-- Sharp basin bound 1: among admissible `m < 617`, first-C3 weight
`S = 26` occurs only at `m = 201`. -/
theorem basin_617_sharp :
    ∀ m : Nat, 7 ≤ m → m < 617 → m % 2 = 1 → m % 5 ≠ 0 →
      basinS 100 m = 26 → m = 201 := by
  intro m hm7 hm617 ho h5 hS
  have h := allInRange_spec 7 617 s26only201Adm s26only201Adm_check m hm7 hm617
  have hAdm : admissibleB m = true := (admissibleB_eq m).2 ⟨hm7, ho, h5⟩
  rcases (by simpa [s26only201Adm, hAdm, decide_eq_true_eq] using h :
      ¬ basinS 100 m = 26 ∨ m = 201) with hnot | heq
  · exact False.elim (hnot hS)
  · exact heq

/-- Basin bound 1 as a closed kernel computation:
`allBasinOK 100 26 617 = true`. -/
theorem basin_617_check : allBasinOK 100 26 617 = true := by
  native_decide

/-- Basin bound 1: every admissible `m < 617` has first C3 weight `S ≤ 26`. -/
theorem basin_617 :
    ∀ m : Nat, 7 ≤ m → m < 617 → m % 2 = 1 → m % 5 ≠ 0 →
      basinOKBool 100 26 m = true := by
  intro m hm7 hm617 ho h5
  exact allBasinOK_spec 100 26 617 basin_617_check m
    ⟨hm7, ho, h5⟩ hm617

/-- Strict small-basin check: `m < 201` implies `S ≤ 25`. -/
theorem basin_201_check : allBasinOK 100 25 201 = true := by
  native_decide

/-- Strict small basin: every admissible `m < 201` has `S ≤ 25`. -/
theorem basin_201 :
    ∀ m : Nat, 7 ≤ m → m < 201 → m % 2 = 1 → m % 5 ≠ 0 →
      basinOKBool 100 25 m = true := by
  intro m hm7 hm201 ho h5
  exact allBasinOK_spec 100 25 201 basin_201_check m
    ⟨hm7, ho, h5⟩ hm201

/-- Stage-2 sublemma 1, finite part: an admissible start below 201
cannot have first-C3 weight `S ≥ 26`. -/
theorem m_min_ge_201 :
    ∀ m : Nat, 7 ≤ m → m < 201 → m % 2 = 1 → m % 5 ≠ 0 →
      basinS 100 m < 26 := by
  intro m hm7 hm201 ho h5
  rcases (basinOKBool_eq_true 100 25 m).mp (basin_201 m hm7 hm201 ho h5) with
    ⟨L, U, M, hIter, hLe⟩
  simp [basinS, hIter]
  omega

/-- Contrapositive form of sublemma 1's finite part:
`S ≥ 26` forces `m ≥ 201`. -/
theorem S_ge_26_imp_m_ge_201 :
    ∀ m : Nat, 7 ≤ m → m % 2 = 1 → m % 5 ≠ 0 →
      26 ≤ basinS 100 m → 201 ≤ m := by
  intro m hm7 ho h5 hS
  by_cases hm : m < 201
  · have hlt := m_min_ge_201 m hm7 hm ho h5
    omega
  · omega

/-- The `m = 201` orbit: `L = 20`, `U = 6`, first C3 at `M = 286189779`. -/
theorem m201_orbit :
    iterateC3 100 201 = some (20, 6, 286189779) := by
  native_decide

/-- Integer form of `U_req = 6` for `L = 20`:
`ceil((20+Q)*log2 5) = 26 + 3*Q + b`. -/
def ureq6OK (Q b : Nat) : Bool :=
  decide (8 ≤ Q ∧ 1 ≤ b ∧ b ≤ 2 ∧
    2^(25 + 3*Q + b) < 5^(20 + Q) ∧ 5^(20 + Q) ≤ 2^(26 + 3*Q + b))

theorem b1_pow_step (A B : Nat) (h : 5^A ≤ 2^B) : 5^(A+1) ≤ 2^(B+3) := by
  calc
    5^(A+1) = 5^A * 5 := by rw [Nat.pow_succ]
    _ ≤ 2^B * 5 := Nat.mul_le_mul_right 5 h
    _ ≤ 2^B * 8 := Nat.mul_le_mul_left (2^B) (by omega)
    _ = 2^(B+3) := by rw [Nat.pow_add]

theorem b1_pow_base : 5^51 ≤ 2^119 := by
  native_decide

theorem b1_pow_from31 (k : Nat) : 5^(51 + k) ≤ 2^(119 + 3*k) := by
  induction k with
  | zero => simpa using b1_pow_base
  | succ k ih =>
      have hstep := b1_pow_step (51 + k) (119 + 3*k) ih
      have h5e : 51 + (k+1) = 51 + k + 1 := by omega
      have h5 : 5^(51 + (k+1)) = 5^(51 + k + 1) := by rw [h5e]
      have h2e : 119 + 3*(k+1) = 119 + 3*k + 3 := by omega
      have h2 : 2^(119 + 3*(k+1)) = 2^(119 + 3*k + 3) := by rw [h2e]
      rw [h5, h2]
      exact hstep

theorem b1_pow_bound (Q : Nat) (hQ : 31 ≤ Q) : 5^(20 + Q) ≤ 2^(25 + 3*Q + 1) := by
  let k := Q - 31
  have hQeq : Q = 31 + k := Nat.sub_add_cancel hQ
  have hk := b1_pow_from31 k
  rw [hQeq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk

theorem b1_Q_le_30 (Q b : Nat) (hQ8 : 8 ≤ Q) (hb2 : b ≤ 2) (hb1 : 1 ≤ b)
    (hLow : 2^(25 + 3*Q + b) < 5^(20 + Q)) : Q ≤ 30 := by
  by_contra hQgt
  have hQ31 : 31 ≤ Q := by omega
  have hbnd := b1_pow_bound Q hQ31
  have hle : 2^(25 + 3*Q + b) ≤ 2^(25 + 3*Q + 1) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hchain : 5^(20 + Q) ≤ 2^(25 + 3*Q + b) := le_trans hbnd hle
  exact (Nat.lt_irrefl _) (lt_of_lt_of_le hLow hchain)

/-- Solution check for the `m = 201` rigidity lemma. -/
def b1_solutionOK (Q b : Nat) : Bool :=
  if ureq6OK Q b then decide ((Q = 28 ∧ b = 2) ∨ (Q = 29 ∧ b = 1)) else true

def b1_allOK : Bool :=
  allInRange 8 31 (fun Q => allInRange 1 3 (fun b => b1_solutionOK Q b))

theorem b1_allOK_check : b1_allOK = true := by
  native_decide

/-- B1: `U_req = 6` for `L = 20` has exactly the two solutions
`(Q,b) = (28,2)` and `(29,1)`. -/
theorem b1_ureq6_solutions (Q b : Nat) (hQ8 : 8 ≤ Q) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hOK : ureq6OK Q b = true) : (Q = 28 ∧ b = 2) ∨ (Q = 29 ∧ b = 1) := by
  have hTrue : 8 ≤ Q ∧ 1 ≤ b ∧ b ≤ 2 ∧
      2^(25 + 3*Q + b) < 5^(20 + Q) ∧ 5^(20 + Q) ≤ 2^(26 + 3*Q + b) := by
    simpa [ureq6OK, hQ8, hb1, hb2] using hOK
  rcases hTrue with ⟨_, _, _, hLow, hUp⟩
  have hQ30 : Q ≤ 30 := b1_Q_le_30 Q b hQ8 hb2 hb1 hLow
  have hQlt : Q < 31 := by omega
  have hP : allInRange 1 3 (fun b => b1_solutionOK Q b) = true :=
    allInRange_spec 8 31 (fun Q => allInRange 1 3 (fun b => b1_solutionOK Q b))
      b1_allOK_check Q hQ8 hQlt
  have hblt : b < 3 := by omega
  have hbP : b1_solutionOK Q b = true :=
    allInRange_spec 1 3 (fun b => b1_solutionOK Q b) hP b hb1 hblt
  unfold b1_solutionOK at hbP
  rw [hOK] at hbP
  simpa [decide_eq_true_eq] using hbP

/-- Tail-recursive first-C3 prefix weight: `firstC3S fuel n s` returns
`s` if `n` reaches a C3 start within `fuel` steps, else `0`. -/
def firstC3S : Nat → Nat → Nat → Nat
  | 0, n, s => if n % 8 = 3 then s else 0
  | fuel + 1, n, s =>
      if n % 8 = 3 then s
      else if n % 8 = 7 then firstC3S fuel ((5 * n + 1) / 4) (s + 2)
      else firstC3S fuel ((5 * n + 1) / 2) (s + 1)

/-- Verify every admissible `m` in `[lo, lo+n)` has
`firstC3S fuel m 0 ≤ cap`. -/
def blockOKCount (fuel cap lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
      let m := lo + n
      (if admissibleB m then
        let s := firstC3S fuel m 0
        decide (s ≤ cap)
       else true)
      && blockOKCount fuel cap lo n

theorem blockOKCount_spec (fuel cap lo : Nat) :
    ∀ n : Nat, blockOKCount fuel cap lo n = true →
    ∀ k : Nat, k < n → 7 ≤ lo + k → (lo + k) % 2 = 1 → (lo + k) % 5 ≠ 0 →
      firstC3S fuel (lo + k) 0 ≤ cap := by
  intro n
  induction n with
  | zero =>
      intro h k hk
      omega
  | succ n ih =>
      intro h k hk h7 ho h5
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | hkeq
      · have hrest : blockOKCount fuel cap lo n = true := by
          simp [blockOKCount, Bool.and_eq_true] at h
          exact h.2
        exact ih hrest k hklt h7 ho h5
      · subst k
        simp [blockOKCount, Bool.and_eq_true] at h
        have hAdm : admissibleB (lo + n) = true := by
          simp [admissibleB, h7, ho, h5]
        have hOK : decide (firstC3S fuel (lo + n) 0 ≤ cap) = true := by
          simpa [hAdm] using h.1
        exact by simpa [decide_eq_true_eq] using hOK

-- The 10^6 basin bound, closed by the fast verifier `blockOKCount`.
theorem basin_1e6_check : blockOKCount 100 64 7 (1000001 - 7) = true := by
  native_decide

/-- Basin bound 2: every admissible `m ≤ 10^6` has first C3 weight
`S ≤ 64`. -/
theorem basin_1e6 :
    ∀ m : Nat, 7 ≤ m → m ≤ 1000000 → m % 2 = 1 → m % 5 ≠ 0 →
      firstC3S 100 m 0 ≤ 64 := by
  intro m hm7 hmle ho h5
  have hm1 : m < 1000001 := Nat.lt_succ_of_le hmle
  have hk : m - 7 < 1000001 - 7 := by omega
  have hk7 : 7 + (m - 7) = m := by omega
  have h7' : 7 ≤ 7 + (m - 7) := by omega
  have ho' : (7 + (m - 7)) % 2 = 1 := by simpa [hk7] using ho
  have h5' : (7 + (m - 7)) % 5 ≠ 0 := by simpa [hk7] using h5
  exact blockOKCount_spec 100 64 7 (1000001 - 7) basin_1e6_check (m - 7) hk h7' ho' h5'

#print axioms StringFlow.basin_617_check
#print axioms StringFlow.basin_617
#print axioms StringFlow.basin_201_check
#print axioms StringFlow.basin_201
#print axioms StringFlow.m_min_ge_201
#print axioms StringFlow.S_ge_26_imp_m_ge_201
#print axioms StringFlow.m201_orbit
#print axioms StringFlow.basin_617_sharp
#print axioms StringFlow.basin_1e6_check
#print axioms StringFlow.basin_1e6

end StringFlow
