import Valuation

/-!
# The `F_b` family (Problem 1)

For odd `b`, `F_b` is the map that halves even numbers and adds `b` to
odd numbers.  This module formalizes the reduced map
`U_b(o) = oddpart(o+b)` on odd inputs, the one-step reduction of
`F_b` to `U_b`, and the strict decrease of `U_b` above `b`.
-/

namespace StringFlow

/-- `F_b(n) = n/2` for even `n`, `n+b` for odd `n`. -/
def fStep (b n : Nat) : Nat := if n % 2 = 0 then n / 2 else n + b

/-- The reduced map on odd numbers: `U_b(o) = oddpart(o+b)`. -/
def uStep (b o : Nat) : Nat := oddPart (o + b)

/-- Halving step. -/
def halve (n : Nat) : Nat := n / 2

/-- `k`-fold iteration of a map. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate f k (f n)

theorem fStep_odd (b o : Nat) (ho : o % 2 = 1) : fStep b o = o + b := by
  unfold fStep
  rw [if_neg (by omega)]

theorem fStep_even (b m : Nat) (hm : m % 2 = 0) : fStep b m = m / 2 := by
  unfold fStep
  rw [if_pos hm]

theorem uStep_odd (b o : Nat) (hb : 0 < b) : uStep b o % 2 = 1 := by
  unfold uStep
  apply oddPart_odd_of_pos
  omega

/-- Above `b`, the reduced map strictly decreases. -/
theorem uStep_lt_of_lt (b o : Nat) (hb : b < o) (hbodd : b % 2 = 1)
    (ho : o % 2 = 1) : uStep b o < o := by
  unfold uStep
  have hob : (o + b) % 2 = 0 := by omega
  have hle := oddPart_le_half_of_even (o + b) hob
  have hhalf : (o + b) / 2 < o := by omega
  exact Nat.lt_of_le_of_lt hle hhalf

/-- Halving `k` times kills exactly the power-of-two factor. -/
theorem iterate_halve_pow_mul (k m : Nat) : iterate halve k (2 ^ k * m) = m := by
  induction k generalizing m with
  | zero => simp [iterate]
  | succ k ih =>
      have hpow : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
        calc
          2 ^ (k + 1) * m = (2 ^ k * 2) * m := by rw [Nat.pow_succ]
          _ = 2 ^ k * (2 * m) := by rw [Nat.mul_assoc]
          _ = 2 * (2 ^ k * m) := by
            rw [← Nat.mul_assoc]
            rw [Nat.mul_comm (2 ^ k) 2]
            rw [Nat.mul_assoc]
      rw [iterate]
      rw [hpow]
      change iterate halve k ((2 * (2 ^ k * m)) / 2) = m
      have hdiv : (2 * (2 ^ k * m)) / 2 = 2 ^ k * m :=
        Nat.mul_div_right (2 ^ k * m) (by omega)
      rw [hdiv]
      exact ih m

/-- While the current value is divisible by two, `F_b` acts like halving. -/
theorem iterate_fStep_eq_halve_while_even (b m k : Nat) (hk : k ≤ twoValuation m) :
    iterate (fStep b) k m = iterate halve k m := by
  induction k generalizing m with
  | zero => simp [iterate]
  | succ k ih =>
      have hkpos : 0 < m := by
        have h0 : m = 0 ∨ 0 < m := Nat.eq_zero_or_pos m
        rcases h0 with hm0 | hmpos
        · subst hm0
          simp at hk
        · exact hmpos
      have hmeven : m % 2 = 0 := by
        have h01 : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
        rcases h01 with h0 | h1
        · exact h0
        · have hv : twoValuation m = 0 := twoValuation_odd m h1
          omega
      have hstep : fStep b m = m / 2 := fStep_even b m hmeven
      have hsplit : m = 2 * (m / 2) := by
        have hd := Nat.div_add_mod m 2
        rw [hmeven] at hd
        omega
      have hmhalf : 0 < m / 2 := by omega
      have hvhalf : twoValuation (m / 2) = twoValuation m - 1 := by
        calc
          twoValuation (m / 2) = twoValuation (2 * (m / 2)) - 1 := by
            rw [twoValuation_mul_two (m / 2) hmhalf]
            omega
          _ = twoValuation m - 1 := by rw [← hsplit]
      have hkle : k ≤ twoValuation (m / 2) := by
        rw [hvhalf]
        omega
      calc
        iterate (fStep b) (k + 1) m = iterate (fStep b) k (fStep b m) := by rw [iterate]
        _ = iterate (fStep b) k (m / 2) := by rw [hstep]
        _ = iterate halve k (m / 2) := ih (m / 2) hkle
        _ = iterate halve (k + 1) m := by
          rw [iterate]
          rfl

/-- One full `F_b` run from an odd number reaches `U_b(o)`. -/
theorem iterate_fStep_odd_reaches_uStep (b o : Nat) (hb : 0 < b) (ho : o % 2 = 1) :
    iterate (fStep b) (twoValuation (o + b) + 1) o = uStep b o := by
  have hdec := n_eq_two_pow_mul_oddPart (o + b) (by omega)
  have hhalve1 : iterate halve (twoValuation (o + b)) (o + b) = oddPart (o + b) := by
    calc
      iterate halve (twoValuation (o + b)) (o + b)
          = iterate halve (twoValuation (o + b))
              (2 ^ twoValuation (o + b) * oddPart (o + b)) := by
            congr 1
      _ = oddPart (o + b) := by
        rw [iterate_halve_pow_mul (twoValuation (o + b)) (oddPart (o + b))]
  have hhalve2 : iterate (fStep b) (twoValuation (o + b)) (o + b) =
      iterate halve (twoValuation (o + b)) (o + b) :=
    iterate_fStep_eq_halve_while_even b (o + b) (twoValuation (o + b)) (by omega)
  have hsplit : iterate (fStep b) (twoValuation (o + b) + 1) o =
      iterate (fStep b) (twoValuation (o + b)) (o + b) := by
    rw [iterate]
    rw [fStep_odd b o ho]
  calc
    iterate (fStep b) (twoValuation (o + b) + 1) o
        = iterate (fStep b) (twoValuation (o + b)) (o + b) := hsplit
    _ = iterate halve (twoValuation (o + b)) (o + b) := hhalve2
    _ = oddPart (o + b) := hhalve1
    _ = uStep b o := rfl

/-- `n` is periodic under `f` with positive period `k`. -/
def IsPeriodic (f : Nat → Nat) (k n : Nat) : Prop := 0 < k ∧ iterate f k n = n

/-- `n` lies on a cycle of `f`. -/
def IsCyclePoint (f : Nat → Nat) (n : Nat) : Prop := ∃ k : Nat, IsPeriodic f k n

/-- Odd numbers `o <= b` are mapped by `U_b` into `[0,b]`. -/
theorem uStep_le_b_of_le (b o : Nat) (hbodd : b % 2 = 1) (ho : o % 2 = 1)
    (hle : o ≤ b) : uStep b o ≤ b := by
  unfold uStep
  have hob : (o + b) % 2 = 0 := by omega
  have hhalf : oddPart (o + b) ≤ (o + b) / 2 := oddPart_le_half_of_even (o + b) hob
  have hle2 : (o + b) / 2 ≤ b := by omega
  exact Nat.le_trans hhalf hle2

/-- One `U_b` step from below `o` stays below `o`. -/
theorem uStep_lt_of_bound_one (b o x : Nat) (hbodd : b % 2 = 1) (hb : b < o)
    (hx : x % 2 = 1) (hxlt : x < o) : uStep b x < o := by
  have hlg := Nat.lt_or_ge b x
  rcases hlg with hb | hxle
  · exact Nat.lt_trans (uStep_lt_of_lt b x hb hbodd hx) hxlt
  · exact Nat.lt_of_le_of_lt (uStep_le_b_of_le b x hbodd hx hxle) hb

/-- Any positive number of `U_b` steps from below `o` stays below `o`. -/
theorem iterate_uStep_lt_of_bound (b o k x : Nat) (hbodd : b % 2 = 1) (hx : x % 2 = 1)
    (hb : b < o) (hxlt : x < o) (hk : 0 < k) : iterate (uStep b) k x < o := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
      rw [iterate]
      have hu : uStep b x < o := uStep_lt_of_bound_one b o x hbodd hb hx hxlt
      have huodd : (uStep b x) % 2 = 1 := uStep_odd b x (by omega)
      have hk0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
      rcases hk0 with hkz | hkpos
      · subst hkz
        simp [iterate]
        exact hu
      · exact ih (uStep b x) huodd hu hkpos

/-- Above `b`, every positive iterate of `U_b` strictly decreases. -/
theorem iterate_uStep_lt_of_gt (b o k : Nat) (hbodd : b % 2 = 1) (ho : o % 2 = 1)
    (hb : b < o) (hk : 0 < k) : iterate (uStep b) k o < o := by
  cases k with
  | zero => omega
  | succ k =>
      rw [iterate]
      have huo : uStep b o < o := uStep_lt_of_lt b o hb hbodd ho
      have huodd : (uStep b o) % 2 = 1 := uStep_odd b o (by omega)
      have hk0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
      rcases hk0 with hkz | hkpos
      · subst hkz
        simp [iterate]
        exact huo
      · exact iterate_uStep_lt_of_bound b o k (uStep b o) hbodd huodd hb huo hkpos

/-- No odd `o > b` is a cycle point of `U_b`. -/
theorem not_cyclePoint_uStep_of_gt (b o : Nat) (hbodd : b % 2 = 1) (ho : o % 2 = 1)
    (hb : b < o) : ¬ IsCyclePoint (uStep b) o := by
  rintro ⟨k, hkpos, hper⟩
  have hlt : iterate (uStep b) k o < o := iterate_uStep_lt_of_gt b o k hbodd ho hb hkpos
  rw [hper] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Halving never increases a number. -/
theorem iterate_halve_le (k m : Nat) : iterate halve k m ≤ m := by
  induction k generalizing m with
  | zero => simp [iterate]
  | succ k ih =>
      rw [iterate]
      have h1 : iterate halve k (m / 2) ≤ m / 2 := ih (m / 2)
      have h2 : m / 2 ≤ m := by omega
      exact Nat.le_trans h1 h2

/-- From an odd `o <= b`, one `F_b` step stays below `2b`. -/
theorem fStep_le_two_b_of_odd_le (b o : Nat) (ho : o % 2 = 1) (hle : o ≤ b) :
    fStep b o ≤ 2 * b := by
  rw [fStep_odd b o ho]
  omega

/-- From an even `m <= 2b`, one `F_b` step stays below `2b`. -/
theorem fStep_le_two_b_of_even_le (b m : Nat) (hm : m % 2 = 0) (hle : m ≤ 2 * b) :
    fStep b m ≤ 2 * b := by
  rw [fStep_even b m hm]
  omega

/-- One full run from an odd `o <= b` stays inside `[0,2b]`. -/
theorem iterate_fStep_le_two_b_run (b o k : Nat) (hbodd : b % 2 = 1) (ho : o % 2 = 1)
    (hle : o ≤ b) (hk : k ≤ twoValuation (o + b) + 1) :
    iterate (fStep b) k o ≤ 2 * b := by
  cases k with
  | zero =>
      simp [iterate]
      omega
  | succ k =>
      rw [iterate]
      have hstep : fStep b o = o + b := fStep_odd b o ho
      rw [hstep]
      have hk' : k ≤ twoValuation (o + b) := by omega
      have heq := iterate_fStep_eq_halve_while_even b (o + b) k hk'
      rw [heq]
      have hdec : iterate halve k (o + b) ≤ o + b := iterate_halve_le k (o + b)
      have hle2 : o + b ≤ 2 * b := by omega
      exact Nat.le_trans hdec hle2

/-!
# `F_b` cycle structure (Problem 1)

This block formalizes Theorems 1.1 and 1.2 of the problem-1 notes:
`F_b` cycles correspond to `U_b` cycles on odd points at most `b`,
every positive `F_b` cycle is contained in `[1, 2b]`, and every positive
orbit eventually enters a cycle.  The key tool is the run decomposition:
from an odd `o <= b`, the orbit runs `o -> o+b -> ... -> U_b(o)`, and the
length of that run is `uRunLen b o`.
-/

/-- Length of one full `F_b` run starting from odd `o`. -/
def uRunLen (b o : Nat) : Nat := twoValuation (o + b) + 1

/-- Total length of the first `k` runs starting from odd `o`. -/
def uRunLenSum (b o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => uRunLen b o + uRunLenSum b (uStep b o) k

/-- A run always has positive length. -/
theorem uRunLen_pos (b o : Nat) : 0 < uRunLen b o := by
  unfold uRunLen
  omega

/-- A positive number of runs has positive total length. -/
theorem uRunLenSum_pos (b o : Nat) (k : Nat) (hk : 0 < k) : 0 < uRunLenSum b o k := by
  cases k with
  | zero => omega
  | succ k =>
      unfold uRunLenSum
      have hr : 0 < uRunLen b o := uRunLen_pos b o
      omega

/-- `f^(k+1)(n) = f(f^k(n))`. -/
theorem iterate_succ_apply (f : Nat → Nat) (k n : Nat) :
    iterate f (k + 1) n = f (iterate f k n) := by
  induction k generalizing n with
  | zero => simp [iterate]
  | succ k ih =>
      calc
        iterate f (k + 1 + 1) n = iterate f (k + 1) (f n) := by rw [iterate]
        _ = f (iterate f k (f n)) := by rw [ih]
        _ = f (iterate f (k + 1) n) := by rw [iterate]

/-- Applying `f` `b` more times after `a` is the same as `a+b` times. -/
theorem iterate_add (f : Nat → Nat) (a b n : Nat) :
    iterate f (a + b) n = iterate f b (iterate f a n) := by
  induction b generalizing a n with
  | zero => simp [iterate]
  | succ b ih =>
      calc
        iterate f (a + (b + 1)) n = iterate f ((a + b) + 1) n := by
          rw [show a + (b + 1) = (a + b) + 1 by omega]
        _ = f (iterate f (a + b) n) := by rw [iterate_succ_apply]
        _ = f (iterate f b (iterate f a n)) := by rw [ih]
        _ = iterate f (b + 1) (iterate f a n) := by rw [iterate_succ_apply]

/-- Iterates of a periodic point are periodic with the same period. -/
theorem iterate_periodic (f : Nat → Nat) (k j n : Nat)
    (hper : iterate f k n = n) : iterate f k (iterate f j n) = iterate f j n := by
  calc
    iterate f k (iterate f j n) = iterate f (j + k) n := by rw [iterate_add]
    _ = iterate f (k + j) n := by congr 1; omega
    _ = iterate f j (iterate f k n) := by rw [iterate_add]
    _ = iterate f j n := by rw [hper]

/-- Iterates of a cycle point are cycle points. -/
theorem iterate_cyclePoint (f : Nat → Nat) (j n : Nat) :
    IsCyclePoint f n → IsCyclePoint f (iterate f j n) := by
  rintro ⟨k, hkpos, hper⟩
  exact ⟨k, hkpos, iterate_periodic f k j n hper⟩

/-- The image of a cycle point under `F_b` is a cycle point. -/
theorem fStep_cyclePoint_of_cyclePoint (b n : Nat) (hc : IsCyclePoint (fStep b) n) :
    IsCyclePoint (fStep b) (fStep b n) := by
  simpa [iterate] using iterate_cyclePoint (fStep b) 1 n hc

/-- `U_b(o)` is the endpoint of the `F_b` run starting at odd `o`. -/
theorem uStep_cyclePoint_of_fCyclePoint (b o : Nat) (hb : 0 < b) (ho : o % 2 = 1)
    (hc : IsCyclePoint (fStep b) o) : IsCyclePoint (fStep b) (uStep b o) := by
  have hrun := iterate_fStep_odd_reaches_uStep b o hb ho
  rw [← hrun]
  exact iterate_cyclePoint (fStep b) (twoValuation (o + b) + 1) o hc

/-- From a positive start, the orbit reaches an odd point at most `b`. -/
theorem exists_odd_le_b_iterate (b : Nat) (hbodd : b % 2 = 1) (hb : 0 < b) :
    ∀ n : Nat, 0 < n → ∃ o j, o % 2 = 1 ∧ o ≤ b ∧ iterate (fStep b) j n = o := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      have h01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
      rcases h01 with h0 | h1
      · have hsplit : n = 2 * (n / 2) := by
          have hd := Nat.div_add_mod n 2
          rw [h0] at hd
          omega
        have hn2 : 0 < n / 2 := by omega
        have hlt : n / 2 < n := by omega
        obtain ⟨o, j, ho, hle, hj⟩ := ih (n / 2) hlt hn2
        refine ⟨o, j + 1, ho, hle, ?_⟩
        calc
          iterate (fStep b) (j + 1) n = iterate (fStep b) j (fStep b n) := by rw [iterate]
          _ = iterate (fStep b) j (n / 2) := by rw [fStep_even b n h0]
          _ = o := hj
      · by_cases hnle : n ≤ b
        · exact ⟨n, 0, h1, hnle, rfl⟩
        · have hgt : b < n := by omega
          have hu : uStep b n < n := uStep_lt_of_lt b n hgt hbodd h1
          have huodd : uStep b n % 2 = 1 := uStep_odd b n hb
          have hupos : 0 < uStep b n := by
            by_cases hz : uStep b n = 0
            · rw [hz] at huodd
              simp at huodd
            · omega
          obtain ⟨o, j, ho, hle, hj⟩ := ih (uStep b n) hu hupos
          have hrun : iterate (fStep b) (uRunLen b n) n = uStep b n := by
            simpa [uRunLen] using iterate_fStep_odd_reaches_uStep b n hb h1
          refine ⟨o, uRunLen b n + j, ho, hle, ?_⟩
          calc
            iterate (fStep b) (uRunLen b n + j) n
                = iterate (fStep b) j (iterate (fStep b) (uRunLen b n) n) := by rw [iterate_add]
            _ = iterate (fStep b) j (uStep b n) := by rw [hrun]
            _ = o := hj

/-- The first `k` runs together simulate `k` steps of `U_b`. -/
theorem iterate_fStep_uRunLenSum (b o k : Nat) (hbodd : b % 2 = 1) (hb : 0 < b)
    (ho : o % 2 = 1) (hle : o ≤ b) :
    iterate (fStep b) (uRunLenSum b o k) o = iterate (uStep b) k o := by
  induction k generalizing o with
  | zero =>
      simp [uRunLenSum, iterate]
  | succ k ih =>
      unfold uRunLenSum
      have hrun : iterate (fStep b) (uRunLen b o) o = uStep b o := by
        simpa [uRunLen] using iterate_fStep_odd_reaches_uStep b o hb ho
      have huodd : uStep b o % 2 = 1 := uStep_odd b o hb
      have hule : uStep b o ≤ b := uStep_le_b_of_le b o hbodd ho hle
      calc
        iterate (fStep b) (uRunLen b o + uRunLenSum b (uStep b o) k) o
            = iterate (fStep b) (uRunLenSum b (uStep b o) k)
                (iterate (fStep b) (uRunLen b o) o) := by
              rw [iterate_add]
        _ = iterate (fStep b) (uRunLenSum b (uStep b o) k) (uStep b o) := by rw [hrun]
        _ = iterate (uStep b) k (uStep b o) := ih (uStep b o) huodd hule
        _ = iterate (uStep b) (k + 1) o := by rw [iterate]

/-- From an odd `o <= b`, every `F_b` iterate stays at most `2b`. -/
theorem iterate_fStep_le_two_b_of_odd_le (b : Nat) (hbodd : b % 2 = 1) (hb : 0 < b) :
    ∀ j : Nat, ∀ o : Nat, o % 2 = 1 → o ≤ b → iterate (fStep b) j o ≤ 2 * b := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
      intro o ho hle
      have h01 : j < uRunLen b o ∨ uRunLen b o ≤ j := Nat.lt_or_ge j (uRunLen b o)
      rcases h01 with hjl | hjr
      · have hk : j ≤ twoValuation (o + b) + 1 := by
          simpa [uRunLen] using Nat.le_of_lt hjl
        exact iterate_fStep_le_two_b_run b o j hbodd ho hle hk
      · have hrun : iterate (fStep b) (uRunLen b o) o = uStep b o := by
          simpa [uRunLen] using iterate_fStep_odd_reaches_uStep b o hb ho
        have huodd : uStep b o % 2 = 1 := uStep_odd b o hb
        have hule : uStep b o ≤ b := uStep_le_b_of_le b o hbodd ho hle
        let j' := j - uRunLen b o
        have hsplit : j = uRunLen b o + j' := by
          dsimp [j']
          exact (Nat.add_sub_of_le hjr).symm
        have hjlt : j' < j := by
          dsimp [j']
          have hrpos : 0 < uRunLen b o := uRunLen_pos b o
          omega
        have hrec : iterate (fStep b) j' (uStep b o) ≤ 2 * b :=
          ih j' hjlt (uStep b o) huodd hule
        calc
          iterate (fStep b) j o = iterate (fStep b) (uRunLen b o + j') o := by rw [hsplit]
          _ = iterate (fStep b) j' (iterate (fStep b) (uRunLen b o) o) := by rw [iterate_add]
          _ = iterate (fStep b) j' (uStep b o) := by rw [hrun]
          _ ≤ 2 * b := hrec

/-- Halving `s < v2(N)` times leaves an even number. -/
theorem iterate_halve_even_of_lt_twoValuation (N s : Nat) (hN : 0 < N)
    (hs : s < twoValuation N) : iterate halve s N % 2 = 0 := by
  let v := twoValuation N
  let q := oddPart N
  have hdec : N = 2 ^ v * q := by
    dsimp [v, q]
    exact n_eq_two_pow_mul_oddPart N hN
  have hsplit : N = 2 ^ s * (2 ^ (v - s) * q) := by
    calc
      N = 2 ^ v * q := hdec
      _ = 2 ^ (s + (v - s)) * q := by
        congr 1
        congr 1
        omega
      _ = (2 ^ s * 2 ^ (v - s)) * q := by rw [Nat.pow_add]
      _ = 2 ^ s * (2 ^ (v - s) * q) := by rw [Nat.mul_assoc]
  have hrun : iterate halve s N = 2 ^ (v - s) * q := by
    calc
      iterate halve s N = iterate halve s (2 ^ s * (2 ^ (v - s) * q)) := by rw [hsplit]
      _ = 2 ^ (v - s) * q := iterate_halve_pow_mul s (2 ^ (v - s) * q)
  have hpow2 : 2 ^ (v - s) * q = 2 * (2 ^ (v - s - 1) * q) := by
    have h1 : v - s = (v - s - 1) + 1 := by omega
    have hpow : 2 ^ (v - s) = 2 * 2 ^ (v - s - 1) := by
      calc
        2 ^ (v - s) = 2 ^ ((v - s - 1) + 1) := by
          exact congrArg (fun x => 2 ^ x) h1
        _ = 2 ^ (v - s - 1) * 2 := by rw [Nat.pow_succ]
        _ = 2 * 2 ^ (v - s - 1) := by rw [Nat.mul_comm]
    calc
      2 ^ (v - s) * q = (2 * 2 ^ (v - s - 1)) * q := by rw [hpow]
      _ = 2 * (2 ^ (v - s - 1) * q) := by rw [Nat.mul_assoc]
  calc
    iterate halve s N % 2 = (2 ^ (v - s) * q) % 2 := by rw [hrun]
    _ = (2 * (2 ^ (v - s - 1) * q)) % 2 := by rw [hpow2]
    _ = 0 := by omega

/-- Inside a run from odd `o`, positions strictly between the endpoints are even. -/
theorem iterate_fStep_even_of_lt_runLen (b o t : Nat) (hbodd : b % 2 = 1)
    (ho : o % 2 = 1) (htpos : 0 < t) (ht : t < uRunLen b o) :
    iterate (fStep b) t o % 2 = 0 := by
  have ht1 : t = 1 ∨ 1 < t := by omega
  rcases ht1 with ht1 | ht1
  · subst t
    calc
      iterate (fStep b) 1 o % 2 = (o + b) % 2 := by
        simp [iterate]
        rw [fStep_odd b o ho]
      _ = 0 := by omega
  · let s := t - 1
    have hss : t = s + 1 := by
      dsimp [s]
      omega
    have hsv : s < twoValuation (o + b) := by
      dsimp [s]
      unfold uRunLen at ht
      omega
    have hle_s : s ≤ twoValuation (o + b) := by omega
    have heq := iterate_fStep_eq_halve_while_even b (o + b) s hle_s
    have hstep : fStep b o = o + b := fStep_odd b o ho
    calc
      iterate (fStep b) t o % 2 = iterate (fStep b) (s + 1) o % 2 := by rw [hss]
      _ = iterate (fStep b) s (fStep b o) % 2 := by rw [iterate]
      _ = iterate (fStep b) s (o + b) % 2 := by rw [hstep]
      _ = iterate halve s (o + b) % 2 := by rw [heq]
      _ = 0 := iterate_halve_even_of_lt_twoValuation (o + b) s (by omega) hsv

/-- From an odd `o <= b`, the only odd iterates are the run endpoints. -/
theorem iterate_fStep_odd_is_run_boundary (b : Nat) (hbodd : b % 2 = 1) (hb : 0 < b) :
    ∀ t : Nat, ∀ o : Nat, o % 2 = 1 → o ≤ b → 0 < t →
      iterate (fStep b) t o % 2 = 1 → ∃ p : Nat, 0 < p ∧ t = uRunLenSum b o p := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
      intro o ho hle ht htodd
      have h01 : t < uRunLen b o ∨ uRunLen b o ≤ t := Nat.lt_or_ge t (uRunLen b o)
      rcases h01 with htl | htr
      · have heven := iterate_fStep_even_of_lt_runLen b o t hbodd ho ht htl
        exfalso
        omega
      · let r := uRunLen b o
        let t' := t - r
        have hsplit : t = r + t' := by
          dsimp [t', r]
          exact (Nat.add_sub_of_le htr).symm
        have hrun : iterate (fStep b) r o = uStep b o := by
          dsimp [r]
          simpa [uRunLen] using iterate_fStep_odd_reaches_uStep b o hb ho
        have huodd : uStep b o % 2 = 1 := uStep_odd b o hb
        have hule : uStep b o ≤ b := uStep_le_b_of_le b o hbodd ho hle
        by_cases ht'0 : t' = 0
        · have ht'0r : t - r = 0 := by simpa [t'] using ht'0
          refine ⟨1, by omega, ?_⟩
          calc
            t = r := by
              rw [show t = r + (t - r) from hsplit]
              rw [ht'0r]
              simp
            _ = uRunLenSum b o 1 := by
              dsimp [r]
              simp [uRunLenSum]
        · have ht'pos : 0 < t' := Nat.pos_of_ne_zero ht'0
          have ht'lt : t' < t := by
            dsimp [t']
            have hrpos : 0 < r := by dsimp [r]; exact uRunLen_pos b o
            omega
          have htodd' : iterate (fStep b) t' (uStep b o) % 2 = 1 := by
            calc
              iterate (fStep b) t' (uStep b o) % 2
                  = iterate (fStep b) t' (iterate (fStep b) r o) % 2 := by rw [← hrun]
              _ = iterate (fStep b) (r + t') o % 2 := by rw [iterate_add]
              _ = iterate (fStep b) t o % 2 := by rw [hsplit]
              _ = 1 := htodd
          obtain ⟨q, hqpos, hq⟩ := ih t' ht'lt (uStep b o) huodd hule ht'pos htodd'
          refine ⟨q + 1, by omega, ?_⟩
          calc
            t = r + t' := hsplit
            _ = r + uRunLenSum b (uStep b o) q := by rw [hq]
            _ = uRunLenSum b o (q + 1) := by
              dsimp [r]
              simp [uRunLenSum]

/-- An odd cycle point of `F_b` at most `b` is a `U_b` cycle point. -/
theorem uStep_cyclePoint_of_fStep_cyclePoint_odd_le_b (b o : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (ho : o % 2 = 1) (hle : o ≤ b) (hc : IsCyclePoint (fStep b) o) :
    IsCyclePoint (uStep b) o := by
  rcases hc with ⟨k, hkpos, hper⟩
  have hodd_k : iterate (fStep b) k o % 2 = 1 := by
    rw [hper]
    exact ho
  obtain ⟨p, hp, hpk⟩ := iterate_fStep_odd_is_run_boundary b hbodd hb k o ho hle hkpos hodd_k
  refine ⟨p, hp, ?_⟩
  calc
    iterate (uStep b) p o = iterate (fStep b) (uRunLenSum b o p) o := by
      rw [iterate_fStep_uRunLenSum b o p hbodd hb ho hle]
    _ = iterate (fStep b) k o := by rw [hpk]
    _ = o := hper

/-- A `U_b` cycle point with odd value at most `b` is an `F_b` cycle point. -/
theorem fStep_cyclePoint_of_uStep_cyclePoint (b o : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (ho : o % 2 = 1) (hle : o ≤ b) :
    IsCyclePoint (uStep b) o → IsCyclePoint (fStep b) o := by
  rintro ⟨k, hkpos, hper⟩
  refine ⟨uRunLenSum b o k, uRunLenSum_pos b o k hkpos, ?_⟩
  calc
    iterate (fStep b) (uRunLenSum b o k) o = iterate (uStep b) k o :=
      iterate_fStep_uRunLenSum b o k hbodd hb ho hle
    _ = o := hper

/-- Theorem 1.1: on odd points at most `b`, `U_b` cycles and `F_b` cycles coincide. -/
theorem uStep_cyclePoint_iff_fStep_cyclePoint (b o : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (ho : o % 2 = 1) (hle : o ≤ b) :
    IsCyclePoint (uStep b) o ↔ IsCyclePoint (fStep b) o := by
  constructor
  · exact fStep_cyclePoint_of_uStep_cyclePoint b o hbodd hb ho hle
  · exact uStep_cyclePoint_of_fStep_cyclePoint_odd_le_b b o hbodd hb ho hle

/-- Every positive `F_b` cycle contains an odd `o <= b` which is a `U_b` cycle point. -/
theorem exists_uStep_cyclePoint_of_fStep_cyclePoint (b n : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (hn : 0 < n) (hc : IsCyclePoint (fStep b) n) :
    ∃ o : Nat, o % 2 = 1 ∧ o ≤ b ∧ IsCyclePoint (uStep b) o := by
  obtain ⟨o, j, ho, hle, hj⟩ := exists_odd_le_b_iterate b hbodd hb n hn
  have hcF : IsCyclePoint (fStep b) o := by
    rcases hc with ⟨k, hkpos, hper⟩
    refine ⟨k, hkpos, ?_⟩
    calc
      iterate (fStep b) k o = iterate (fStep b) k (iterate (fStep b) j n) := by rw [hj]
      _ = iterate (fStep b) (j + k) n := by rw [iterate_add]
      _ = iterate (fStep b) (k + j) n := by congr 1; omega
      _ = iterate (fStep b) j (iterate (fStep b) k n) := by rw [iterate_add]
      _ = iterate (fStep b) j n := by rw [hper]
      _ = o := hj
  exact ⟨o, ho, hle, uStep_cyclePoint_of_fStep_cyclePoint_odd_le_b b o hbodd hb ho hle hcF⟩

/-- A periodic point returns to itself after `k * s` steps. -/
theorem iterate_period_mul (f : Nat → Nat) (k s n : Nat)
    (hper : iterate f k n = n) : iterate f (k * s) n = n := by
  induction s with
  | zero => simp [iterate]
  | succ s ih =>
      calc
        iterate f (k * (s + 1)) n = iterate f (k * s + k) n := by
          rw [show k * (s + 1) = k * s + k by rw [Nat.mul_add, Nat.mul_one]]
        _ = iterate f k (iterate f (k * s) n) := by rw [iterate_add]
        _ = iterate f k n := by rw [ih]
        _ = n := hper

/-- Theorem 1.2 (first part): every positive `F_b` cycle lies in `[1, 2b]`. -/
theorem fStep_cyclePoint_le_two_b (b n : Nat) (hbodd : b % 2 = 1) (hb : 0 < b)
    (hn : 0 < n) (hc : IsCyclePoint (fStep b) n) : n ≤ 2 * b := by
  obtain ⟨o, j, ho, hle, hj⟩ := exists_odd_le_b_iterate b hbodd hb n hn
  rcases hc with ⟨k, hkpos, hper⟩
  let i := k * (j + 1) - j
  have hsub : j ≤ k * (j + 1) := by
    induction k with
    | zero => omega
    | succ k ih =>
        rw [Nat.add_mul, Nat.one_mul]
        omega
  have hji : j + i = k * (j + 1) := by
    dsimp [i]
    exact Nat.add_sub_of_le hsub
  have hperiod : iterate (fStep b) (k * (j + 1)) n = n :=
    iterate_period_mul (fStep b) k (j + 1) n hper
  have hn_eq : iterate (fStep b) i o = n := by
    calc
      iterate (fStep b) i o = iterate (fStep b) i (iterate (fStep b) j n) := by rw [hj]
      _ = iterate (fStep b) (j + i) n := by rw [iterate_add]
      _ = iterate (fStep b) (k * (j + 1)) n := by rw [hji]
      _ = n := hperiod
  have hbound : iterate (fStep b) i o ≤ 2 * b :=
    iterate_fStep_le_two_b_of_odd_le b hbodd hb i o ho hle
  rwa [hn_eq] at hbound

/-- Finite pigeonhole: `m+1` values below `m` must repeat. -/
theorem exists_repeat_lt (m : Nat) : ∀ seq : Nat → Nat,
    (∀ i, i ≤ m → seq i < m) → ∃ i j, i < j ∧ j ≤ m ∧ seq i = seq j := by
  induction m with
  | zero =>
      intro seq h
      have h0 : seq 0 < 0 := h 0 (by omega)
      exact (Nat.not_lt_zero (seq 0) h0).elim
  | succ m ih =>
      intro seq h
      let v := seq (m + 1)
      have hv : v < m + 1 := h (m + 1) (by omega)
      by_cases hocc : ∃ i ≤ m, seq i = v
      · rcases hocc with ⟨i, hile, hi⟩
        refine ⟨i, m + 1, ?_, ?_, ?_⟩
        · omega
        · omega
        · rw [hi]
      · have hnot : ∀ i, i ≤ m → seq i ≠ v := by
          intro i hile hi
          exact hocc ⟨i, hile, hi⟩
        let g : Nat → Nat := fun i => if seq i < v then seq i else seq i - 1
        have hg : ∀ i, i ≤ m → g i < m := by
          intro i hile
          have hsi : seq i < m + 1 := h i (by omega)
          have hsiv : seq i ≠ v := hnot i hile
          by_cases hlt : seq i < v
          · dsimp [g]
            rw [if_pos hlt]
            omega
          · dsimp [g]
            rw [if_neg hlt]
            have hge : v ≤ seq i := Nat.not_lt.mp hlt
            have hgt : v < seq i := Nat.lt_of_le_of_ne hge (fun hv => hsiv hv.symm)
            omega
        obtain ⟨i, j, hij, hjle, hgij⟩ := ih g hg
        have hseq_eq : seq i = seq j := by
          have hile : i ≤ m := by omega
          have hnoti : seq i ≠ v := hnot i hile
          have hnotj : seq j ≠ v := hnot j hjle
          by_cases hil : seq i < v
          · have hjl : seq j < v := by
              by_cases hjnl : seq j < v
              · exact hjnl
              · have hgi : g i = seq i := by simp [g, hil]
                have hgj : g j = seq j - 1 := by simp [g, hjnl]
                omega
            have hgi : g i = seq i := by simp [g, hil]
            have hgj : g j = seq j := by simp [g, hjl]
            omega
          · have hgi : g i = seq i - 1 := by simp [g, hil]
            by_cases hjl : seq j < v
            · have hgj : g j = seq j := by simp [g, hjl]
              omega
            · have hgj : g j = seq j - 1 := by simp [g, hjl]
              omega
        refine ⟨i, j, hij, by omega, hseq_eq⟩

/-- Theorem 1.2 (second part): every positive `F_b` orbit eventually enters a cycle. -/
theorem eventually_cyclePoint (b n : Nat) (hbodd : b % 2 = 1) (hb : 0 < b)
    (hn : 0 < n) : ∃ j, IsCyclePoint (fStep b) (iterate (fStep b) j n) := by
  obtain ⟨o, J, ho, hle, hJ⟩ := exists_odd_le_b_iterate b hbodd hb n hn
  let m := 2 * b + 1
  obtain ⟨i, j, hij, hjle, hij_eq⟩ := exists_repeat_lt m (fun t => iterate (fStep b) t o) (by
    intro t ht
    have htb : iterate (fStep b) t o ≤ 2 * b :=
      iterate_fStep_le_two_b_of_odd_le b hbodd hb t o ho hle
    dsimp [m] at ht
    omega)
  have hperiod : iterate (fStep b) (j - i) (iterate (fStep b) i o) = iterate (fStep b) i o := by
    have hlei : i ≤ j := by omega
    have hji : i + (j - i) = j := Nat.add_sub_of_le hlei
    calc
      iterate (fStep b) (j - i) (iterate (fStep b) i o)
          = iterate (fStep b) (i + (j - i)) o := by rw [iterate_add]
      _ = iterate (fStep b) j o := by rw [hji]
      _ = iterate (fStep b) i o := hij_eq.symm
  have hci : IsCyclePoint (fStep b) (iterate (fStep b) i o) :=
    ⟨j - i, by omega, hperiod⟩
  have hlift : iterate (fStep b) (J + i) n = iterate (fStep b) i o := by
    calc
      iterate (fStep b) (J + i) n = iterate (fStep b) i (iterate (fStep b) J n) := by rw [iterate_add]
      _ = iterate (fStep b) i o := by rw [hJ]
  refine ⟨J + i, ?_⟩
  rwa [hlift]

/-!
# `F_b` cycle parity words

Writing the parities of the `F_b` orbit around a cycle, the word has
exactly `p` ones where `p` is the number of `U_b` steps (equivalently
the number of odd points on the cycle).  This is the `F_b`-side version
of the cycle-length/word-weight relation behind Theorem 1.8 of the
problem-1 notes.
-/

/-- Count of indices `i < n` whose bit value `f i` is set. -/
def bitCount (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => f n + bitCount n f

/-- Recursion of the bit count. -/
theorem bitCount_succ (n : Nat) (f : Nat → Nat) :
    bitCount (n + 1) f = f n + bitCount n f := rfl

/-- Splitting the index range at `a`. -/
theorem bitCount_add (a b : Nat) (f : Nat → Nat) :
    bitCount (a + b) f = bitCount a f + bitCount b (fun i => f (a + i)) := by
  induction b generalizing a with
  | zero => simp [bitCount]
  | succ b ih =>
      calc
        bitCount (a + (b + 1)) f = bitCount ((a + b) + 1) f := by
          rw [show a + (b + 1) = (a + b) + 1 by omega]
        _ = f (a + b) + bitCount (a + b) f := by rw [bitCount_succ]
        _ = f (a + b) + (bitCount a f + bitCount b (fun i => f (a + i))) := by rw [ih]
        _ = bitCount a f + (f (a + b) + bitCount b (fun i => f (a + i))) := by omega
        _ = bitCount a f + bitCount (b + 1) (fun i => f (a + i)) := by
          rw [bitCount_succ]

/-- Pointwise equality on the whole range gives equal counts. -/
theorem bitCount_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : bitCount n f = bitCount n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : f n = g n := h n (by omega)
      have hrest : bitCount n f = bitCount n g := ih (fun i hi => h i (by omega))
      rw [bitCount_succ, bitCount_succ, h1, hrest]

/-- The all-zero word has count zero. -/
theorem bitCount_zero_const (n : Nat) : bitCount n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bitCount_succ]
      simp [ih]

/-- Splitting the first index off. -/
theorem bitCount_split_start (n : Nat) (f : Nat → Nat) :
    bitCount (n + 1) f = f 0 + bitCount n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih =>
      calc
        bitCount (n + 1 + 1) f = f (n + 1) + bitCount (n + 1) f := by
          rw [bitCount_succ]
        _ = f (n + 1) + (f 0 + bitCount n (fun i => f (i + 1))) := by rw [ih]
        _ = f 0 + (f (n + 1) + bitCount n (fun i => f (i + 1))) := by omega
        _ = f 0 + bitCount (n + 1) (fun i => f (i + 1)) := by
          rw [bitCount_succ]

/-- A word with a single initial one has count one. -/
theorem bitCount_single_initial (n : Nat) (f : Nat → Nat) (hn : 0 < n)
    (hf0 : f 0 = 1) (hfe : ∀ i, 1 ≤ i → i < n → f i = 0) :
    bitCount n f = 1 := by
  cases n with
  | zero => omega
  | succ n =>
      have hsplit := bitCount_split_start n f
      rw [hsplit]
      have hzero : bitCount n (fun i => f (i + 1)) = 0 := by
        have hc := bitCount_congr (n := n)
          (f := fun i => f (i + 1)) (g := fun _ => 0) (by
            intro i hi
            have h1 : 1 ≤ i + 1 := by omega
            have hlt : i + 1 < n + 1 := by omega
            exact hfe (i + 1) h1 hlt)
        rw [hc]
        exact bitCount_zero_const n
      rw [hzero]
      rw [hf0]

/-- Inside the first run from odd `o`, only the initial point is odd. -/
theorem bitCount_first_run (b o : Nat) (hbodd : b % 2 = 1)
    (ho : o % 2 = 1) :
    bitCount (uRunLen b o) (fun i => iterate (fStep b) i o % 2) = 1 := by
  let f : Nat → Nat := fun i => iterate (fStep b) i o % 2
  have hf0 : f 0 = 1 := by
    dsimp [f]
    change iterate (fStep b) 0 o % 2 = 1
    simp [iterate]
    exact ho
  have hfe : ∀ i, 1 ≤ i → i < uRunLen b o → f i = 0 := by
    intro i hi1 hi
    dsimp [f]
    exact iterate_fStep_even_of_lt_runLen b o i hbodd ho hi1 hi
  exact bitCount_single_initial (uRunLen b o) f (uRunLen_pos b o) hf0 hfe

/-- One `U_b` period `p` is an `F_b` period of length `uRunLenSum b o p`. -/
theorem fStep_period_of_uStep_period (b o p : Nat) (hbodd : b % 2 = 1) (hb : 0 < b)
    (ho : o % 2 = 1) (hle : o ≤ b) (hper : iterate (uStep b) p o = o) :
    iterate (fStep b) (uRunLenSum b o p) o = o := by
  rw [iterate_fStep_uRunLenSum b o p hbodd hb ho hle]
  exact hper

/-- The first `p` runs of an `F_b` orbit from odd `o <= b` contain exactly
`p` odd points. -/
theorem fStep_parityWord_count_of_uStep_steps (b o p : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (ho : o % 2 = 1) (hle : o ≤ b) :
    bitCount (uRunLenSum b o p) (fun i => iterate (fStep b) i o % 2) = p := by
  induction p generalizing o with
  | zero =>
      simp [uRunLenSum, bitCount]
  | succ p ih =>
      have huodd : uStep b o % 2 = 1 := uStep_odd b o hb
      have hule : uStep b o ≤ b := uStep_le_b_of_le b o hbodd ho hle
      have hrun : iterate (fStep b) (uRunLen b o) o = uStep b o := by
        simpa [uRunLen] using iterate_fStep_odd_reaches_uStep b o hb ho
      have hcongr : ∀ i, i < uRunLenSum b (uStep b o) p →
          (fun j => iterate (fStep b) (uRunLen b o + j) o % 2) i
            = (fun j => iterate (fStep b) j (uStep b o) % 2) i := by
        intro i hi
        change iterate (fStep b) (uRunLen b o + i) o % 2 = iterate (fStep b) i (uStep b o) % 2
        have hadd := iterate_add (fStep b) (uRunLen b o) i o
        rw [hadd]
        rw [hrun]
      calc
        bitCount (uRunLenSum b o (p + 1)) (fun i => iterate (fStep b) i o % 2)
            = bitCount (uRunLen b o + uRunLenSum b (uStep b o) p)
                (fun i => iterate (fStep b) i o % 2) := by
              simp [uRunLenSum]
        _ = bitCount (uRunLen b o) (fun i => iterate (fStep b) i o % 2)
              + bitCount (uRunLenSum b (uStep b o) p)
                  (fun i => iterate (fStep b) (uRunLen b o + i) o % 2) := by
              rw [bitCount_add]
        _ = 1 + bitCount (uRunLenSum b (uStep b o) p)
                  (fun i => iterate (fStep b) i (uStep b o) % 2) := by
              rw [bitCount_first_run b o hbodd ho]
              congr 1
              exact bitCount_congr hcongr
        _ = 1 + p := by
              rw [ih (uStep b o) huodd hule]
        _ = p + 1 := by omega

/-- The `F_b` parity word of one `U_b` period contains exactly `p` ones. -/
theorem fStep_parityWord_count_of_uStep_period (b o p : Nat) (hbodd : b % 2 = 1)
    (hb : 0 < b) (ho : o % 2 = 1) (hle : o ≤ b)
    (_hper : iterate (uStep b) p o = o) :
    bitCount (uRunLenSum b o p) (fun i => iterate (fStep b) i o % 2) = p :=
  fStep_parityWord_count_of_uStep_steps b o p hbodd hb ho hle

end StringFlow
