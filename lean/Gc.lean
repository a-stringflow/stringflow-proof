import Mathlib
import Qb
import Pmi
import ScratchLift
import WordWindow

/-!
# GC: global-composition lemmas on the main proof chain

This module formalizes the algebraic and modular core of the GC lemmas
from `ph_qb_gc_chain.md`:

- GC-4: closed form and residual of a C3 chain, together with the
  unique-small-representative corollary;
- GC-3: mod-3 closure of an accelerated step;
- GC-42: mod-16 classification of C3 starts by weight;
- GC-41: the `b = 0` branch (all C3 weights equal to 3) is excluded
  inside frame A.

All statements use `Nat` and cleared exact recurrences; no `Real` or
`log` is introduced.
-/

namespace StringFlow.GC

/-- `A_chain = sum_{k=0}^{Q-1} 5^(Q-1-k) * 2^(U_k)`. -/
def chainA : List Nat → Nat
  | [] => 0
  | t :: ts => 5 ^ ts.length + 2 ^ t * chainA ts

/-- First chain weight (0 for the empty list). -/
def firstWeight : List Nat → Nat
  | t :: _ => t
  | [] => 0

/-- A nonempty C3 chain has positive numerator. -/
theorem chainA_pos (ts : List Nat) (h : ts ≠ []) : 0 < chainA ts := by
  cases ts with
  | nil => contradiction
  | cons t ts' =>
      unfold chainA
      exact Nat.add_pos_left (Nat.pow_pos (show 0 < 5 by decide))
        (2 ^ t * chainA ts')

/-- First element of a chain (0 for the empty list). -/
def chainFirst : List Nat → Nat
  | [] => 0
  | n :: _ => n

/-- Last element of a chain (0 for the empty list). -/
def chainLast : List Nat → Nat
  | [] => 0
  | [n] => n
  | _ :: ns => chainLast ns

/-- Exact C3 chain: `2^t_i * N_{i+1} = 5*N_i + 1`. -/
def c3Exact : List Nat → List Nat → Prop
  | [], [] => True
  | [_], [] => True
  | n :: n' :: ns, t :: ts =>
      2 ^ t * n' = 5 * n + 1 ∧ c3Exact (n' :: ns) ts
  | _, _ => False

/-- Exact C3 chain where every step uses the full 2-adic valuation. -/
def c3ExactMax : List Nat → List Nat → Prop
  | [], [] => True
  | [_], [] => True
  | n :: n' :: ns, t :: ts =>
      2 ^ t * n' = 5 * n + 1 ∧ (5 * n + 1) % 2 ^ (t + 1) ≠ 0 ∧
        c3ExactMax (n' :: ns) ts
  | _, _ => False

/-- The head step of a maximal C3 chain has full valuation. -/
theorem head_max_of_c3ExactMax (ns : List Nat) (a : Nat) (as : List Nat)
    (h : c3ExactMax ns (a :: as)) :
    (5 * chainFirst ns + 1) % 2 ^ (a + 1) ≠ 0 := by
  cases ns with
  | nil => simp [c3ExactMax] at h
  | cons n rest =>
      cases rest with
      | nil => simp [c3ExactMax] at h
      | cons n' rest' =>
          rcases h with ⟨hstep, hmax, htail⟩
          simpa [chainFirst] using hmax

/-- Maximality implies exactness of the C3 chain. -/
theorem c3Exact_of_c3ExactMax (ns ts : List Nat) (h : c3ExactMax ns ts) :
    c3Exact ns ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [c3Exact]
      | cons n rest =>
          cases rest with
          | nil => simp [c3Exact]
          | cons n' rest' => simp [c3ExactMax] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3ExactMax] at h
      | cons n rest =>
          cases rest with
          | nil => simp [c3ExactMax] at h
          | cons n' rest' =>
              rcases h with ⟨hstep, hmax, htail⟩
              simp [c3Exact]
              exact ⟨hstep, ih (n' :: rest') htail⟩

/-- In a C3 step with weight at least `3`, the previous chain node is
odd. -/
theorem c3_prev_odd_of_weight_ge_three (n t n' : Nat)
    (hstep : 2 ^ t * n' = 5 * n + 1) (ht : 3 ≤ t) :
    n % 2 = 1 := by
  have hdiv8 : 8 ∣ 5 * n + 1 := by
    rw [← hstep]
    have h3dvd : 2 ^ 3 ∣ 2 ^ t := Nat.pow_dvd_pow 2 ht
    rcases h3dvd with ⟨r, hr⟩
    refine ⟨r * n', ?_⟩
    rw [hr]
    rw [show 2 ^ 3 = 8 by decide]
    rw [Nat.mul_assoc]
  have hmod2 : (5 * n + 1) % 2 = 0 := by
    have h2dvd : 2 ∣ 5 * n + 1 := Nat.dvd_trans (by decide : 2 ∣ 8) hdiv8
    exact Nat.dvd_iff_mod_eq_zero.mp h2dvd
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · exfalso
    have hodd := StringFlow.Word.odd_after_even n hn0
    omega
  · exact hn1

/-- If the successor of a C3 step is odd, the step uses the full
2-adic valuation. -/
theorem c3_step_max_of_odd_succ (n n' t : Nat)
    (hstep : 2 ^ t * n' = 5 * n + 1) (hodd : n' % 2 = 1) :
    (5 * n + 1) % 2 ^ (t + 1) ≠ 0 := by
  intro hz
  have hdiv : 2 ^ (t + 1) ∣ 5 * n + 1 := Nat.dvd_iff_mod_eq_zero.mpr hz
  have hdiv' : 2 ^ (t + 1) ∣ 2 ^ t * n' := by
    simpa [hstep.symm] using hdiv
  rcases hdiv' with ⟨k, hk⟩
  have hk' : 2 ^ t * n' = 2 ^ t * (2 * k) := by
    rw [hk]
    rw [Nat.pow_succ]
    rw [Nat.mul_assoc]
  have hn' : n' = 2 * k := Nat.mul_left_cancel (Nat.pow_pos (by decide)) hk'
  have hn0 : n' % 2 = 0 := by
    rw [hn']
    simp
  omega

/-- Every node of a C3 chain is odd when all weights are at least
`3` and the last node is odd. -/
theorem c3_chain_all_odd_of_weight_ge_three_last (ns ts : List Nat)
    (h : c3Exact ns ts) (hge : ∀ t ∈ ts, 3 ≤ t)
    (hlast : chainLast ns % 2 = 1) :
    ∀ n ∈ ns, n % 2 = 1 := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => intro n hn; simp at hn
      | cons n ns' =>
          cases ns' with
          | nil =>
              intro x hx
              rw [List.mem_cons] at hx
              rcases hx with rfl | hrest
              · simpa [chainLast] using hlast
              · simp at hrest
          | cons n' ns'' => simp [c3Exact] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3Exact] at h
      | cons n ns' =>
          cases ns' with
          | nil => simp [c3Exact] at h
          | cons n' ns'' =>
              rcases h with ⟨hstep, htail⟩
              have hhead : n % 2 = 1 :=
                c3_prev_odd_of_weight_ge_three n t n' hstep (hge t (by simp))
              have hlast' : chainLast (n' :: ns'') % 2 = 1 := by
                simpa [chainLast] using hlast
              have htail' := ih (n' :: ns'') htail
                (fun a ha => hge a (by simp [ha])) hlast'
              intro x hx
              rw [List.mem_cons] at hx
              rcases hx with rfl | hrest
              · exact hhead
              · exact htail' x hrest

/-- An exact C3 chain whose nodes are all odd is automatically a
maximal C3 chain. -/
theorem c3ExactMax_of_c3Exact_of_odd (ns ts : List Nat)
    (h : c3Exact ns ts) (hodd : ∀ n ∈ ns, n % 2 = 1) :
    c3ExactMax ns ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [c3ExactMax]
      | cons n ns' =>
          cases ns' with
          | nil => simp [c3ExactMax]
          | cons n' ns'' => simp [c3Exact] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3Exact] at h
      | cons n ns' =>
          cases ns' with
          | nil => simp [c3Exact] at h
          | cons n' ns'' =>
              rcases h with ⟨hstep, htail⟩
              have hmax : (5 * n + 1) % 2 ^ (t + 1) ≠ 0 :=
                c3_step_max_of_odd_succ n n' t hstep (hodd n' (by simp))
              have htail' := ih (n' :: ns'')
                htail (fun x hx => hodd x (by simp [hx]))
              simp [c3ExactMax]
              exact ⟨hstep, hmax, htail'⟩

/-- A real C3 chain, whose weights are at least `3` and whose last
node is odd, is automatically maximal. -/
theorem c3ExactMax_of_c3Exact_of_ge_three_last (ns ts : List Nat)
    (h : c3Exact ns ts) (hge : ∀ t ∈ ts, 3 ≤ t)
    (hlast : chainLast ns % 2 = 1) :
    c3ExactMax ns ts :=
  c3ExactMax_of_c3Exact_of_odd ns ts h
    (c3_chain_all_odd_of_weight_ge_three_last ns ts h hge hlast)

/-- Exact-step divisibility for a QB structural C3 chain: every step
`2^t | 5n+1`, so `c3Step` is the exact accelerated value. -/
def c3ChainExactSteps : List Nat → List Nat → Prop
  | [], [] => True
  | [_], [] => True
  | n :: n' :: ns, t :: ts =>
      (5 * n + 1) % 2 ^ t = 0 ∧ c3ChainExactSteps (n' :: ns) ts
  | _, _ => False

/-- An exact GC C3 chain supplies the exact-step divisibility
predicate used by the QB bridge. -/
theorem c3ChainExactSteps_of_c3Exact (ns ts : List Nat)
    (h : c3Exact ns ts) :
    c3ChainExactSteps ns ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [c3ChainExactSteps]
      | cons n rest =>
          cases rest with
          | nil => simp [c3ChainExactSteps]
          | cons n' rest' => simp [c3Exact] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3Exact] at h
      | cons n rest =>
          cases rest with
          | nil => simp [c3Exact] at h
          | cons n' rest' =>
              rcases h with ⟨hstep, htail⟩
              have hdiv : (5 * n + 1) % 2 ^ t = 0 := by
                rw [← hstep]
                exact Nat.mul_mod_right (2 ^ t) n'
              simp [c3ChainExactSteps]
              exact ⟨hdiv, ih (n' :: rest') htail⟩

/-- An exact GC C3 chain with all nodes at least `7` and all weights
at least `3` is a QB structural C3 chain. -/
theorem c3Chain_of_c3Exact (ns ts : List Nat)
    (h : c3Exact ns ts)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (h7 : ∀ n ∈ ns, 7 ≤ n) :
    StringFlow.QB.c3Chain ns ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [StringFlow.QB.c3Chain]
      | cons n rest =>
          cases rest with
          | nil => simp [StringFlow.QB.c3Chain]
          | cons n' rest' => simp [c3Exact] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3Exact] at h
      | cons n rest =>
          cases rest with
          | nil => simp [c3Exact] at h
          | cons n' rest' =>
              rcases h with ⟨hstep, htail⟩
              have hn : 7 ≤ n := h7 n (by simp)
              have ht : 3 ≤ t := hge t (by simp)
              have hstep' : n' = StringFlow.QB.c3Step n t := by
                unfold StringFlow.QB.c3Step
                have hdiv : (5 * n + 1) / 2 ^ t = n' := by
                  rw [← hstep]
                  exact Nat.mul_div_right n' (Nat.pow_pos (by decide))
                exact hdiv.symm
              have hge' : ∀ t ∈ ts', 3 ≤ t :=
                fun a ha => hge a (by simp [ha])
              have h7' : ∀ n ∈ n' :: rest', 7 ≤ n :=
                fun x hx => h7 x (by simp [hx])
              simp [StringFlow.QB.c3Chain]
              exact ⟨hstep', hn, ht, ih (n' :: rest') htail hge' h7'⟩

/-- A QB structural C3 chain with exact steps is a `GC.c3Exact`
chain. -/
theorem c3Exact_of_c3Chain (ns ts : List Nat)
    (hchain : StringFlow.QB.c3Chain ns ts)
    (hdiv : c3ChainExactSteps ns ts) :
    c3Exact ns ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [c3Exact]
      | cons n rest =>
          cases rest with
          | nil => simp [c3Exact]
          | cons n' rest' => simp [c3ChainExactSteps] at hdiv
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3ChainExactSteps] at hdiv
      | cons n rest =>
          cases rest with
          | nil => simp [c3ChainExactSteps] at hdiv
          | cons n' rest' =>
              rcases hchain with ⟨hstep, _hn, _ht, htail⟩
              rcases hdiv with ⟨hdivstep, hdivtail⟩
              have hEq : 2 ^ t * n' = 5 * n + 1 := by
                rw [hstep]
                unfold StringFlow.QB.c3Step
                have hd := Nat.dvd_iff_mod_eq_zero.mpr hdivstep
                have hmul := Nat.div_mul_cancel hd
                rw [Nat.mul_comm]
                exact hmul
              simp [c3Exact]
              exact ⟨hEq, ih (n' :: rest') htail hdivtail⟩

/-- Every weight of a QB structural C3 chain is at least `3`. -/
theorem c3Chain_weights_ge_three (ns ts : List Nat)
    (h : StringFlow.QB.c3Chain ns ts)
    (hdiv : c3ChainExactSteps ns ts) :
    ∀ t ∈ ts, 3 ≤ t := by
  induction ts generalizing ns with
  | nil =>
      intro t ht
      simp at ht
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3ChainExactSteps] at hdiv
      | cons n rest =>
          cases rest with
          | nil => simp [c3ChainExactSteps] at hdiv
          | cons n' rest' =>
              rcases h with ⟨_, _, ht, htail⟩
              rcases hdiv with ⟨_hdivstep, hdivtail⟩
              intro a ha
              rw [List.mem_cons] at ha
              rcases ha with rfl | htailmem
              · exact ht
              · exact ih (n' :: rest') htail hdivtail a htailmem

/-- A QB structural C3 chain with exact steps and an odd last node
is automatically a maximal `GC.c3ExactMax` chain. -/
theorem c3ExactMax_of_c3Chain (ns ts : List Nat)
    (hchain : StringFlow.QB.c3Chain ns ts)
    (hdiv : c3ChainExactSteps ns ts)
    (hlast : chainLast ns % 2 = 1) :
    c3ExactMax ns ts :=
  c3ExactMax_of_c3Exact_of_ge_three_last ns ts
    (c3Exact_of_c3Chain ns ts hchain hdiv)
    (c3Chain_weights_ge_three ns ts hchain hdiv)
    hlast

/-- The `chainA` numerator modulo `64` has only its first two terms:
later terms contain `2^(t_i+t_j)` with `t_i + t_j >= 6`. -/
theorem chainA_mod64_of_ge_three (ts : List Nat)
    (hge : ∀ t ∈ ts, 3 ≤ t) (hQ : 2 ≤ ts.length) :
    chainA ts % 64 =
      (5 ^ (ts.length - 1) + 5 ^ (ts.length - 2) * 2 ^ firstWeight ts) %64 := by
  cases ts with
  | nil => simp at hQ
  | cons t rest =>
      cases rest with
      | nil => simp at hQ
      | cons t2 rest2 =>
          have ht : 3 ≤ t := hge t (by simp)
          have ht2 : 3 ≤ t2 := hge t2 (by simp)
          have hsumge : 6 ≤ t + t2 := by omega
          have hbig : (2 ^ (t + t2) * chainA rest2) % 64 = 0 := by
            have h64 : 64 ∣ 2 ^ (t + t2) := by
              rw [show 64 = 2 ^ 6 by decide]
              exact Nat.pow_dvd_pow 2 hsumge
            have hd : 64 ∣ 2 ^ (t + t2) * chainA rest2 :=
              by
                rcases h64 with ⟨k, hk⟩
                refine ⟨k * chainA rest2, ?_⟩
                rw [hk]
                rw [Nat.mul_assoc]
            exact Nat.dvd_iff_mod_eq_zero.mp hd
          have hmain : chainA (t :: t2 :: rest2) =
              5 ^ (rest2.length + 1) + 2 ^ t * 5 ^ rest2.length +
                2 ^ (t + t2) * chainA rest2 := by
            simp [chainA]
            have hpow : 2 ^ (t + t2) = 2 ^ t * 2 ^ t2 := by
              rw [Nat.pow_add]
            rw [hpow]
            rw [Nat.mul_add]
            simp [Nat.add_assoc, Nat.mul_assoc]
          have hmod : (5 ^ (rest2.length + 1) + 2 ^ t * 5 ^ rest2.length +
                2 ^ (t + t2) * chainA rest2) % 64 =
              (5 ^ (rest2.length + 1) + 5 ^ rest2.length * 2 ^ t) % 64 := by
            simp [Nat.add_assoc, Nat.add_mod, Nat.add_mod, hbig,
              Nat.add_comm, Nat.mul_comm]
          have hlen1 : (t :: t2 :: rest2).length - 1 = rest2.length + 1 := by
            simp [List.length]
          have hlen2 : (t :: t2 :: rest2).length - 2 = rest2.length := by
            simp [List.length]
          rw [hlen1, hlen2]
          simp [firstWeight]
          rw [hmain, hmod]

/-- From the closed form and `T >= 6`, the required numerator
satisfies `5^Q*M0 + A ≡ 0 (mod 64)`. -/
theorem req_mod64_sum_zero (T m Q M0 A : Nat)
    (hT : 6 ≤ T) (hchain : 2 ^ T * m = 5 ^ Q * M0 + A) :
    (5 ^ Q * M0 + A) % 64 = 0 := by
  have h64 : 64 ∣ 2 ^ T := by
    rw [show 64 = 2 ^ 6 by decide]
    exact Nat.pow_dvd_pow 2 hT
  have hd : 64 ∣ 2 ^ T * m := by
    rcases h64 with ⟨k, hk⟩
    refine ⟨k * m, ?_⟩
    rw [hk]
    rw [Nat.mul_assoc]
  have hmod : (2 ^ T * m) % 64 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [hchain.symm]
  exact hmod

/-- GC-1/GC-4: a C3 chain has the closed form
`2^T * N_{Q+1} = 5^Q * N_1 + A_chain`. -/
theorem c3_chain_closed_form (ns ts : List Nat) (h : c3Exact ns ts) :
    2 ^ ts.sum * chainLast ns = 5 ^ ts.length * chainFirst ns + chainA ts := by
  induction ts generalizing ns with
  | nil =>
      cases ns with
      | nil => simp [chainA, chainLast, chainFirst]
      | cons n ns' =>
          cases ns' with
          | nil => simp [chainA, chainLast, chainFirst]
          | cons n' ns'' => simp [c3Exact] at h
  | cons t ts' ih =>
      cases ns with
      | nil => simp [c3Exact] at h
      | cons n ns' =>
          cases ns' with
          | nil => simp [c3Exact] at h
          | cons n' ns'' =>
              rcases h with ⟨hstep, htail⟩
              have htail' := ih (n' :: ns'') htail
              simp [chainA, chainLast, chainFirst] at htail' ⊢
              rw [Nat.pow_add]
              rw [Nat.mul_assoc]
              rw [htail']
              rw [Nat.mul_add]
              have hmul : 2 ^ t * (5 ^ ts'.length * n') =
                  5 ^ ts'.length * (2 ^ t * n') := by
                rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ t) (5 ^ ts'.length),
                  Nat.mul_assoc]
              rw [hmul, hstep]
              rw [Nat.mul_add]
              have hmul5 : 5 ^ ts'.length * (5 * n) =
                  5 ^ (ts'.length + 1) * n := by
                rw [← Nat.mul_assoc]
                have hpow : 5 ^ ts'.length * 5 = 5 ^ (ts'.length + 1) := by
                  change 5 ^ ts'.length * 5 = 5 ^ ts'.length.succ
                  rw [← Nat.pow_succ]
                rw [hpow]
              rw [hmul5]
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- GC-4 residual, exact form:
`(2^T * N_{Q+1}) % 5^Q = A_chain % 5^Q`. -/
theorem c3_chain_residual (ns ts : List Nat) (h : c3Exact ns ts) :
    (2 ^ ts.sum * chainLast ns) % 5 ^ ts.length =
      chainA ts % 5 ^ ts.length := by
  rw [c3_chain_closed_form ns ts h]
  rw [Nat.add_comm]
  exact Nat.add_mul_mod_self_left (chainA ts) (5 ^ ts.length)
    (chainFirst ns)

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
        decide
      · rw [h2]
        decide
      · rw [h3]
        decide
      · rw [h4]
        decide

/-- GC-4 residual after multiplying by the inverse of `2^T` modulo
`5^Q`: `N_{Q+1} ≡ A_chain * 2^(-T) (mod 5^Q)`. -/
theorem c3_chain_residual_inverse (ns ts : List Nat) (hQ : 0 < ts.length)
    (h : c3Exact ns ts) :
    chainLast ns % 5 ^ ts.length =
      (chainA ts * StringFlow.Lte.invFive (2 ^ ts.sum) (ts.length)) %
        5 ^ ts.length := by
  let Q := ts.length
  let T := ts.sum
  let A := chainA ts
  let inv := StringFlow.Lte.invFive (2 ^ T) Q
  have hmod : (2 ^ T * chainLast ns) % 5 ^ Q = A % 5 ^ Q := by
    dsimp [T, A]
    exact c3_chain_residual ns ts h
  have h2 : (2 ^ T) % 5 ≠ 0 := two_pow_mod_five_ne_zero T
  have hspec0 := StringFlow.Lte.invFive_spec (2 ^ T) h2 (Q - 1)
  have hsub : (Q - 1) + 1 = Q := by omega
  rw [hsub] at hspec0
  have hspec : (2 ^ T * inv) % 5 ^ Q = 1 := by
    dsimp [inv]
    exact hspec0
  have hmul := StringFlow.Word.mul_mod_inv (2 ^ T) (chainLast ns) inv
    (5 ^ Q) hspec
  have hprod : ((2 ^ T * chainLast ns) % 5 ^ Q * inv) % 5 ^ Q =
      (A % 5 ^ Q * inv) % 5 ^ Q := by
    rw [hmod]
  have hleft : (2 ^ T * ((chainLast ns * inv) % 5 ^ Q)) % 5 ^ Q =
      ((2 ^ T * chainLast ns) * inv) % 5 ^ Q := by
    have hmod_in : (2 ^ T * ((chainLast ns * inv) % 5 ^ Q)) % 5 ^ Q =
        (2 ^ T * (chainLast ns * inv)) % 5 ^ Q := by
      rw [Nat.mul_mod, Nat.mul_mod]
      simp
    have hassoc : 2 ^ T * (chainLast ns * inv) =
        (2 ^ T * chainLast ns) * inv := by
      rw [← Nat.mul_assoc]
    rw [hmod_in, ← hassoc]
  have hright : ((2 ^ T * chainLast ns) * inv) % 5 ^ Q =
      (A * inv) % 5 ^ Q := by
    calc
      ((2 ^ T * chainLast ns) * inv) % 5 ^ Q
          = (((2 ^ T * chainLast ns) % 5 ^ Q) * inv) % 5 ^ Q := by
              rw [Nat.mul_mod, Nat.mul_mod]
              simp
      _ = (A * inv) % 5 ^ Q := by
              rw [hmod]
              rw [Nat.mul_mod, Nat.mul_mod]
              simp
  calc
    chainLast ns % 5 ^ Q
        = (2 ^ T * ((chainLast ns * inv) % 5 ^ Q)) % 5 ^ Q := hmul.symm
    _ = ((2 ^ T * chainLast ns) * inv) % 5 ^ Q := hleft
    _ = (A * inv) % 5 ^ Q := hright
    _ = (chainA ts * inv) % 5 ^ Q := rfl

/-- Two numbers below a modulus with the same residue are equal. -/
theorem eq_of_mod_eq_lt {a b M : Nat} (ha : a < M) (hb : b < M)
    (hmod : a % M = b % M) : a = b := by
  rw [Nat.mod_eq_of_lt ha] at hmod
  rw [Nat.mod_eq_of_lt hb] at hmod
  exact hmod

/-- GC-4 uniqueness corollary: for `Q >= 9`, the residual class has at
most one representative in `(7, 10^6]`. -/
theorem c3_residual_unique_small (ts : List Nat) (hQ : 9 ≤ ts.length)
    (m1 m2 : Nat) (_hm1 : 7 < m1) (_hm2 : 7 < m2)
    (hb1 : m1 ≤ 10 ^ 6) (hb2 : m2 ≤ 10 ^ 6)
    (h1 : m1 % 5 ^ ts.length =
      (chainA ts * StringFlow.Lte.invFive (2 ^ ts.sum) (ts.length)) %
        5 ^ ts.length)
    (h2 : m2 % 5 ^ ts.length =
      (chainA ts * StringFlow.Lte.invFive (2 ^ ts.sum) (ts.length)) %
        5 ^ ts.length) :
    m1 = m2 := by
  have h59 : 5 ^ 9 > 10 ^ 6 := by decide
  have h5 : 5 ^ 9 ≤ 5 ^ ts.length :=
    Nat.pow_le_pow_right (by decide : 0 < 5) hQ
  have hM : 10 ^ 6 < 5 ^ ts.length := by omega
  have hlt1 : m1 < 5 ^ ts.length := Nat.lt_of_le_of_lt hb1 hM
  have hlt2 : m2 < 5 ^ ts.length := Nat.lt_of_le_of_lt hb2 hM
  have hsame : m1 % 5 ^ ts.length = m2 % 5 ^ ts.length := by
    rw [h1, h2]
  exact eq_of_mod_eq_lt hlt1 hlt2 hsame

/-- `2^t mod 3 = 1` when `t` is even, `= 2` when `t` is odd. -/
theorem two_pow_mod3 (t : Nat) :
    (2 ^ t) % 3 = if t % 2 = 0 then 1 else 2 := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      by_cases ht : t % 2 = 0
      · have hsucc : (t + 1) % 2 = 1 := by
          rw [Nat.add_mod]
          simp [ht]
        rw [ih, ht, hsucc]
        decide
      · have hlt : t % 2 < 2 := Nat.mod_lt t (by decide)
        have ht1 : t % 2 = 1 := by omega
        have hsucc : (t + 1) % 2 = 0 := by
          rw [Nat.add_mod]
          simp [ht1]
        rw [ih, ht1, hsucc]
        decide

/-- GC-3, even weight: `n' ≡ 1 - n (mod 3)`. -/
theorem c3_mod3_of_even (n n' t : Nat)
    (hstep : 2 ^ t * n' = 5 * n + 1) (ht : t % 2 = 0) :
    (n' + n) % 3 = 1 := by
  have hmod0 : (2 ^ t * n') % 3 = (5 * n + 1) % 3 := by
    rw [hstep]
  rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod] at hmod0
  have h2 : (2 ^ t) % 3 = 1 := by
    rw [two_pow_mod3 t]
    simp [ht]
  have h1 : 1 % 3 = 1 := by decide
  have h5 : 5 % 3 = 2 := by decide
  simp [Nat.mul_mod, h2, h1, h5] at hmod0
  have hsum : (n' + n) % 3 = (n' % 3 + n % 3) % 3 := by
    rw [Nat.add_mod]
  rw [hsum, hmod0]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0]
  · rw [h1]
  · rw [h2]

/-- GC-3, odd weight: `n' ≡ n - 1 (mod 3)`. -/
theorem c3_mod3_of_odd (n n' t : Nat)
    (hstep : 2 ^ t * n' = 5 * n + 1) (ht : t % 2 = 1) :
    (n' + 1) % 3 = n % 3 := by
  have hmod0 : (2 ^ t * n') % 3 = (5 * n + 1) % 3 := by
    rw [hstep]
  rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod] at hmod0
  have h2 : (2 ^ t) % 3 = 2 := by
    rw [two_pow_mod3 t]
    simp [ht]
  have h1 : 1 % 3 = 1 := by decide
  have h5 : 5 % 3 = 2 := by decide
  simp [Nat.mul_mod, h2, h1, h5] at hmod0
  have hsum : (n' + 1) % 3 = (n' % 3 + 1) % 3 := by
    rw [Nat.add_mod]
  rw [hsum]
  have hltn : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hltn' : n' % 3 < 3 := Nat.mod_lt n' (by decide)
  have hcasesn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hcasesn' : n' % 3 = 0 ∨ n' % 3 = 1 ∨ n' % 3 = 2 := by omega
  rcases hcasesn with h0 | h1 | h2
  · rcases hcasesn' with h0' | h1' | h2'
    · rw [h0, h0'] at hmod0 ⊢
      simp at hmod0 ⊢
    · rw [h0, h1'] at hmod0 ⊢
      simp at hmod0 ⊢
    · rw [h0, h2'] at hmod0 ⊢
  · rcases hcasesn' with h0' | h1' | h2'
    · rw [h1, h0'] at hmod0 ⊢
    · rw [h1, h1'] at hmod0 ⊢
      simp at hmod0 ⊢
    · rw [h1, h2'] at hmod0 ⊢
      simp at hmod0 ⊢
  · rcases hcasesn' with h0' | h1' | h2'
    · rw [h2, h0'] at hmod0 ⊢
      simp at hmod0 ⊢
    · rw [h2, h1'] at hmod0 ⊢
    · rw [h2, h2'] at hmod0 ⊢
      simp at hmod0 ⊢

/-- If `(a+1) mod 16 = 8` and `a < 16`, then `a = 7`. -/
theorem mod_add_one_eq_seven_of_lt (a : Nat) (ha : a < 16)
    (h : (a + 1) % 16 = 8) : a = 7 := by
  have hcases : a + 1 = 16 ∨ a + 1 < 16 := by omega
  rcases hcases with h16 | hlt
  · exfalso
    rw [h16] at h
    have hh : ¬ (16 % 16 = 8) := by decide
    exact hh h
  · have hmod : (a + 1) % 16 = a + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod] at h
    omega

/-- If `(a+1) mod 16 = 0` and `a < 16`, then `a = 15`. -/
theorem mod_add_one_eq_fifteen_of_lt (a : Nat) (ha : a < 16)
    (h : (a + 1) % 16 = 0) : a = 15 := by
  have hcases : a + 1 = 16 ∨ a + 1 < 16 := by omega
  rcases hcases with h16 | hlt
  · omega
  · exfalso
    have hmod : (a + 1) % 16 = a + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod] at h
    omega

/-- `((a mod m) * b) mod m = (a * b) mod m`. -/
theorem mod_mul_self_right (a b m : Nat) :
    ((a % m) * b) % m = (a * b) % m := by
  rw [Nat.mul_mod, Nat.mul_mod]
  simp

/-- Solving `5n ≡ r (mod 16)` by multiplying with `13 = 5^{-1}`. -/
theorem five_mul_mod_eq_mul_inv (r n : Nat) (hr : (5 * n) % 16 = r) :
    n % 16 = (r * 13) % 16 := by
  have h65 : (5 * 13) % 16 = 1 := by decide
  calc
    n % 16 = ((n * (5 * 13)) % 16) := by
      rw [Nat.mul_mod, h65]
      simp
    _ = (((5 * n) * 13) % 16) := by
      congr 1
      rw [← Nat.mul_assoc, Nat.mul_comm n 5]
    _ = (((5 * n) % 16 * 13) % 16) := by
      exact (mod_mul_self_right (5 * n) 13 16).symm
    _ = (r * 13) % 16 := by rw [hr]

/-- `8x ≡ 8 (mod 16)` for odd `x`. -/
theorem mul8_mod16_of_odd (x : Nat) (hx : x % 2 = 1) : (8 * x) % 16 = 8 := by
  have hxdec : x = 2 * (x / 2) + x % 2 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod x 2).symm
  calc
    (8 * x) % 16 = (8 * (2 * (x / 2) + x % 2)) % 16 := by
      conv =>
        lhs
        rw [hxdec]
    _ = (16 * (x / 2) + 8 * (x % 2)) % 16 := by
      congr 1
      rw [Nat.mul_add]
      have h1 : 8 * (2 * (x / 2)) = 16 * (x / 2) := by
        rw [← Nat.mul_assoc]
      rw [h1]
    _ = (8 * (x % 2)) % 16 := by
      rw [Nat.add_mod, Nat.mul_mod]
      simp
    _ = 8 := by
      rw [hx]

/-- GC-42, `t_i = 3`: `N_i ≡ 11 (mod 16)`. -/
theorem gc42_mod16_of_weight_three (n n' : Nat)
    (hstep : 2 ^ 3 * n' = 5 * n + 1) (hodd : n' % 2 = 1) :
    n % 16 = 11 := by
  have hmod : (5 * n + 1) % 16 = 8 := by
    rw [← hstep]
    exact mul8_mod16_of_odd n' hodd
  have hlt : (5 * n) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hadd : ((5 * n) % 16 + 1) % 16 = 8 := by
    rw [Nat.add_mod] at hmod
    have h1 : 1 % 16 = 1 := by decide
    simpa [h1, Nat.add_comm] using hmod
  have h5n : (5 * n) % 16 = 7 :=
    mod_add_one_eq_seven_of_lt ((5 * n) % 16) hlt hadd
  simpa using five_mul_mod_eq_mul_inv 7 n h5n

/-- GC-42, `t_i >= 4`: `N_i ≡ 3 (mod 16)`. -/
theorem gc42_mod16_of_weight_ge_four (n t n' : Nat)
    (hstep : 2 ^ t * n' = 5 * n + 1) (ht : 4 ≤ t) :
    n % 16 = 3 := by
  have hdvd : 16 ∣ 2 ^ t * n' := by
    refine ⟨2 ^ (t - 4) * n', ?_⟩
    have hsub : t - 4 + 4 = t := by omega
    rw [← hsub, Nat.pow_add]
    have h4 : 2 ^ 4 = 16 := by decide
    rw [h4]
    rw [Nat.mul_comm (2 ^ (t - 4)) 16]
    rw [← Nat.mul_assoc]
    rw [show t - 4 + 4 - 4 = t - 4 by omega]
  have hmod0 : (5 * n + 1) % 16 = 0 := by
    rw [← hstep]
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hlt : (5 * n) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hadd : ((5 * n) % 16 + 1) % 16 = 0 := by
    rw [Nat.add_mod] at hmod0
    have h1 : 1 % 16 = 1 := by decide
    simpa [h1, Nat.add_comm] using hmod0
  have h5n : (5 * n) % 16 = 15 :=
    mod_add_one_eq_fifteen_of_lt ((5 * n) % 16) hlt hadd
  simpa using five_mul_mod_eq_mul_inv 15 n h5n

/-- All C3 weights in a chain are equal to `3`. -/
def allThree : List Nat → Prop
  | [] => True
  | t :: ts => t = 3 ∧ allThree ts

/-- A `3`-chain has total weight `3 * length`. -/
theorem allThree_sum (ts : List Nat) (h : allThree ts) :
    ts.sum = 3 * ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
      rcases h with ⟨ht, hts⟩
      have ih' := ih hts
      rw [ht]
      simp [List.sum_cons, ih']
      omega

/-- `2^(3n) = 8^n`. -/
theorem two_pow_three_mul_eq_eight_pow (n : Nat) :
    2 ^ (3 * n) = 8 ^ n := by
  calc
    2 ^ (3 * n) = (2 ^ 3) ^ n := by rw [Nat.pow_mul]
    _ = 8 ^ n := by rw [show 2 ^ 3 = 8 by decide]

/-- `5^n <= 8^n`. -/
theorem five_pow_le_eight_pow (n : Nat) : 5 ^ n ≤ 8 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        5 ^ (n + 1) = 5 * 5 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ 8 * 5 ^ n := Nat.mul_le_mul_right (5 ^ n) (by decide : 5 ≤ 8)
        _ ≤ 8 * 8 ^ n := Nat.mul_le_mul_left (8) ih
        _ = 8 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- `5^n < 8^n` for `n >= 1`. -/
theorem five_pow_lt_eight_pow (n : Nat) (hn : 1 ≤ n) : 5 ^ n < 8 ^ n := by
  cases n with
  | zero => omega
  | succ m =>
      have hle : 5 ^ m ≤ 8 ^ m := five_pow_le_eight_pow m
      have h5lt : 5 ^ m * 5 < 8 ^ m * 8 := by
        have h5le : 5 ^ m * 5 ≤ 8 ^ m * 5 :=
          Nat.mul_le_mul_right 5 hle
        have hlt8 : 8 ^ m * 5 < 8 ^ m * 8 := by
          have hpos : 0 < 8 ^ m := Nat.pow_pos (by decide : 0 < 8)
          exact Nat.mul_lt_mul_of_pos_left (by decide : 5 < 8) hpos
        omega
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

/-- One step of the closed-form numerator for a `3`-chain. -/
theorem three_mul_chainA_succ (n : Nat) :
    3 * 5 ^ n + 8 * (8 ^ n - 5 ^ n) = 8 ^ (n + 1) - 5 ^ (n + 1) := by
  rw [Nat.pow_succ, Nat.pow_succ]
  rw [Nat.mul_sub]
  have hle : 5 ^ n ≤ 8 ^ n := five_pow_le_eight_pow n
  omega

/-- `(x - M) mod M = x mod M` when `M <= x`. -/
theorem sub_mod_of_mod_eq (x M : Nat) (hle : M ≤ x) :
    (x - M) % M = x % M := by
  have hsum : M + (x - M) = x := Nat.add_sub_of_le hle
  calc
    (x - M) % M = (M + (x - M)) % M := by
      rw [Nat.add_comm]
      simp
    _ = x % M := by rw [hsum]

/-- For a `3`-chain, `3 * A_chain = 8^Q - 5^Q`. -/
theorem three_mul_chainA (ts : List Nat) (h : allThree ts) :
    3 * chainA ts = 8 ^ ts.length - 5 ^ ts.length := by
  induction ts with
  | nil => simp [chainA]
  | cons t ts ih =>
      rcases h with ⟨ht, hts⟩
      have ih' := ih hts
      change 3 * (5 ^ ts.length + 2 ^ t * chainA ts) =
        8 ^ (ts.length + 1) - 5 ^ (ts.length + 1)
      rw [ht]
      have h8 : 2 ^ 3 = 8 := by decide
      rw [h8]
      rw [Nat.mul_add]
      have hswap : 3 * (8 * chainA ts) = 8 * (3 * chainA ts) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 3 8, Nat.mul_assoc]
      rw [hswap]
      rw [ih']
      exact three_mul_chainA_succ ts.length

/-- GC-41 algebraic core: with all C3 weights equal to `3`,
`3 * 8^Q * N_{Q+1} ≡ 8^Q (mod 5^Q)`. -/
theorem gc41_three_mul_congruence (ns ts : List Nat) (h : c3Exact ns ts)
    (hts : allThree ts) :
    (3 * 8 ^ ts.length * chainLast ns) % 5 ^ ts.length =
      (8 ^ ts.length) % 5 ^ ts.length := by
  have hclosed := c3_chain_closed_form ns ts h
  have hsum := allThree_sum ts hts
  have hpow : 2 ^ ts.sum = 8 ^ ts.length := by
    rw [hsum]
    exact two_pow_three_mul_eq_eight_pow ts.length
  have hclosed' : 8 ^ ts.length * chainLast ns =
      5 ^ ts.length * chainFirst ns + chainA ts := by
    simpa [hpow] using hclosed
  have hA := three_mul_chainA ts hts
  rw [Nat.mul_assoc]
  rw [hclosed']
  rw [Nat.mul_add, hA]
  have hzero : (3 * (5 ^ ts.length * chainFirst ns)) % 5 ^ ts.length = 0 := by
    rw [Nat.mul_mod]
    simp
  rw [Nat.add_mod, hzero]
  have hsub : (8 ^ ts.length - 5 ^ ts.length) % 5 ^ ts.length =
      (8 ^ ts.length) % 5 ^ ts.length :=
    sub_mod_of_mod_eq (8 ^ ts.length) (5 ^ ts.length)
      (five_pow_le_eight_pow ts.length)
  rw [hsub]
  simp

/-- Modular cancellation by a unit: `a*b ≡ a*c (mod M)` implies
`b ≡ c (mod M)` when `a` has inverse `inv` modulo `M`. -/
theorem mod_mul_cancel (a b c M inv : Nat) (hinv : (a * inv) % M = 1)
    (h : (a * b) % M = (a * c) % M) : b % M = c % M := by
  have hb : (((a * b) % M) * inv) % M = b % M := by
    calc
      (((a * b) % M) * inv) % M = ((a * b) * inv) % M := by
        rw [Nat.mul_mod, Nat.mul_mod]
        simp
      _ = (a * (b * inv)) % M := by rw [← Nat.mul_assoc]
      _ = (a * ((b * inv) % M)) % M := by
        rw [Nat.mul_mod, Nat.mul_mod]
        simp
      _ = b % M := StringFlow.Word.mul_mod_inv a b inv M hinv
  have hc : (((a * c) % M) * inv) % M = c % M := by
    calc
      (((a * c) % M) * inv) % M = ((a * c) * inv) % M := by
        rw [Nat.mul_mod, Nat.mul_mod]
        simp
      _ = (a * (c * inv)) % M := by rw [← Nat.mul_assoc]
      _ = (a * ((c * inv) % M)) % M := by
        rw [Nat.mul_mod, Nat.mul_mod]
        simp
      _ = c % M := StringFlow.Word.mul_mod_inv a c inv M hinv
  have h' : (((a * b) % M) * inv) % M = (((a * c) % M) * inv) % M := by
    rw [h]
  rw [hb, hc] at h'
  exact h'

/-- `8^n` is not divisible by 5. -/
theorem eight_pow_mod_five_ne_zero (n : Nat) : (8 ^ n) % 5 ≠ 0 := by
  have hpow : 8 ^ n = 2 ^ (3 * n) := by
    calc
      8 ^ n = (2 ^ 3) ^ n := by rw [show 8 = 2 ^ 3 by decide]
      _ = 2 ^ (3 * n) := by rw [Nat.pow_mul]
  rw [hpow]
  exact two_pow_mod_five_ne_zero (3 * n)

/-- GC-41 residual in the `3m ≡ 1 (mod 5^Q)` form. -/
theorem gc41_three_mul_residue (ns ts : List Nat) (hQ : 0 < ts.length)
    (h : c3Exact ns ts) (hts : allThree ts) :
    (3 * chainLast ns) % 5 ^ ts.length = 1 := by
  let Q := ts.length
  have hcong := gc41_three_mul_congruence ns ts h hts
  have h2 : (8 ^ Q) % 5 ≠ 0 := eight_pow_mod_five_ne_zero Q
  let inv := StringFlow.Lte.invFive (8 ^ Q) Q
  have hsub : (Q - 1) + 1 = Q := by omega
  have hinv0 := StringFlow.Lte.invFive_spec (8 ^ Q) h2 (Q - 1)
  rw [hsub] at hinv0
  have hcong' : (8 ^ Q * (3 * chainLast ns)) % 5 ^ Q =
      (8 ^ Q * 1) % 5 ^ Q := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcong
  have hcancel := mod_mul_cancel (8 ^ Q) (3 * chainLast ns) 1 (5 ^ Q) inv
    hinv0 hcong'
  have hmod1 : (1 : Nat) % 5 ^ ts.length = 1 := by
    apply Nat.mod_eq_of_lt
    have hlen : 1 ≤ ts.length := by omega
    have h5 : 5 ≤ 5 ^ ts.length := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 5) hlen
    omega
  change (3 * chainLast ns) % 5 ^ ts.length = 1
  simpa [Q, hmod1] using hcancel

/-- GC-41 candidate for `Q = 8`: only `260417` is odd and small. -/
theorem gc41_q8_candidate (m : Nat) (hmle : m ≤ 10 ^ 6) (hodd : m % 2 = 1)
    (hmod : (3 * m) % 5 ^ 8 = 1) : m = 260417 := by
  have hM : 5 ^ 8 = 390625 := by decide
  rw [hM] at hmod
  have hdiv : 3 * m = 390625 * (3 * m / 390625) + 1 := by
    have h := Nat.div_add_mod (3 * m) 390625
    rw [hmod] at h
    simpa [Nat.mul_comm] using h.symm
  have hlt : 3 * m < 8 * 390625 := by omega
  have hq : (3 * m / 390625) = 0 ∨ (3 * m / 390625) = 1 ∨
      (3 * m / 390625) = 2 ∨ (3 * m / 390625) = 3 ∨
      (3 * m / 390625) = 4 ∨ (3 * m / 390625) = 5 ∨
      (3 * m / 390625) = 6 ∨ (3 * m / 390625) = 7 := by omega
  rcases hq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [h0] at hdiv
    omega
  · rw [h1] at hdiv
    omega
  · rw [h2] at hdiv
    have hm : m = 260417 := by omega
    exact hm
  · rw [h3] at hdiv
    omega
  · rw [h4] at hdiv
    omega
  · rw [h5] at hdiv
    have hm : m = 651042 := by omega
    rw [hm] at hodd
    have hh : ¬ (651042 % 2 = 1) := by decide
    exact False.elim (hh hodd)
  · rw [h6] at hdiv
    omega
  · rw [h7] at hdiv
    omega

/-- GC-41: `Q = 9` gives an even candidate, excluded by parity. -/
theorem gc41_q9_no_odd (m : Nat) (hmle : m ≤ 10 ^ 6) (hodd : m % 2 = 1)
    (hmod : (3 * m) % 5 ^ 9 = 1) : False := by
  have hM : 5 ^ 9 = 1953125 := by decide
  rw [hM] at hmod
  have hdiv : 3 * m = 1953125 * (3 * m / 1953125) + 1 := by
    have h := Nat.div_add_mod (3 * m) 1953125
    rw [hmod] at h
    simpa [Nat.mul_comm] using h.symm
  have hlt : 3 * m < 2 * 1953125 := by omega
  have hq : (3 * m / 1953125) = 0 ∨ (3 * m / 1953125) = 1 := by omega
  rcases hq with h0 | h1
  · rw [h0] at hdiv
    omega
  · rw [h1] at hdiv
    have hm : m = 651042 := by omega
    rw [hm] at hodd
    have hh : ¬ (651042 % 2 = 1) := by decide
    exact False.elim (hh hodd)

/-- GC-41: for `Q >= 10`, the modulus exceeds `3m`, so no odd candidate. -/
theorem gc41_q_ge10_no (Q m : Nat) (hQ : 10 ≤ Q) (hmle : m ≤ 10 ^ 6)
    (hmod : (3 * m) % 5 ^ Q = 1) : False := by
  have hM : 3 * 10 ^ 6 < 5 ^ 10 := by decide
  have hpow : 5 ^ 10 ≤ 5 ^ Q :=
    Nat.pow_le_pow_right (by decide : 0 < 5) hQ
  have hlt : 3 * m < 5 ^ Q := by omega
  have hmod' : (3 * m) % 5 ^ Q = 3 * m := Nat.mod_eq_of_lt hlt
  rw [hmod'] at hmod
  omega

/-- GC-41: the `b = 0` branch (all C3 weights `3`) is impossible in
frame A. -/
theorem gc41_b_zero_no_solution (ns ts : List Nat) (h : c3Exact ns ts)
    (hts : allThree ts)
    (hnext : 2 ^ 3 * chainFirst ns = 5 * chainLast ns + 1)
    (hbound : chainLast ns ≤ 10 ^ 6) (hodd : chainLast ns % 2 = 1)
    (hQ : 8 ≤ ts.length) : False := by
  have hres := gc41_three_mul_residue ns ts (by omega) h hts
  have hcases : ts.length = 8 ∨ ts.length = 9 ∨ 10 ≤ ts.length := by omega
  rcases hcases with h8 | h9 | hge10
  · have hm : chainLast ns = 260417 := by
      simpa [h8] using gc41_q8_candidate (chainLast ns) hbound hodd
        (by simpa [h8] using hres)
    have hmod8 : (5 * chainLast ns + 1) % 8 = 0 := by
      rw [← hnext]
      simp
    rw [hm] at hmod8
    have hh : ¬ ((5 * 260417 + 1) % 8 = 0) := by decide
    exact False.elim (hh hmod8)
  · exact gc41_q9_no_odd (chainLast ns) hbound hodd
      (by simpa [h9] using hres)
  · exact gc41_q_ge10_no ts.length (chainLast ns) hge10 hbound
      (by simpa [hge10] using hres)

/-- GC-43: clearing the denominators in
`(C_0 - B) m <= R_0 + A_chain / 5^Q`.  The input is the C3 chain
equation `5^Q N_1 = 2^T m - A_chain` and the rising bound
`2^S N_1 <= 5^L m + A_max`. -/
theorem gc43_linear_bound (L S Q T N1 m Achain Amax : Nat)
    (hcoef : 5 ^ (L + Q) ≤ 2 ^ (T + S))
    (hchain : 5 ^ Q * N1 + Achain = 2 ^ T * m)
    (hrise : 2 ^ S * N1 ≤ 5 ^ L * m + Amax) :
    (2 ^ (T + S) - 5 ^ (L + Q)) * m ≤
      5 ^ Q * Amax + 2 ^ S * Achain := by
  have hrise' : 5 ^ Q * (2 ^ S * N1) ≤
      5 ^ Q * (5 ^ L * m + Amax) :=
    Nat.mul_le_mul_left (5 ^ Q) hrise
  have hsub : 5 ^ Q * (2 ^ S * N1) = 2 ^ S * (2 ^ T * m - Achain) := by
    have hsub' : 5 ^ Q * N1 = 2 ^ T * m - Achain := by omega
    calc
      5 ^ Q * (2 ^ S * N1) = (5 ^ Q * 2 ^ S) * N1 := by rw [← Nat.mul_assoc]
      _ = (2 ^ S * 5 ^ Q) * N1 := by rw [Nat.mul_comm (5 ^ Q) (2 ^ S)]
      _ = 2 ^ S * (5 ^ Q * N1) := by rw [Nat.mul_assoc]
      _ = 2 ^ S * (2 ^ T * m - Achain) := by rw [hsub']
  have h2 : 2 ^ S * (2 ^ T * m - Achain) ≤
      5 ^ (L + Q) * m + 5 ^ Q * Amax := by
    have hpow : 5 ^ Q * 5 ^ L = 5 ^ (L + Q) := by
      rw [Nat.pow_add]
      rw [Nat.mul_comm]
    rw [← hsub]
    calc
      5 ^ Q * (2 ^ S * N1) ≤ 5 ^ Q * (5 ^ L * m + Amax) := hrise'
      _ = 5 ^ (L + Q) * m + 5 ^ Q * Amax := by
          rw [Nat.mul_add, ← Nat.mul_assoc, hpow]
  have hpowT : 2 ^ S * 2 ^ T = 2 ^ (T + S) := by
    rw [Nat.pow_add]
    rw [Nat.mul_comm]
  have hleft : 2 ^ S * (2 ^ T * m - Achain) =
      2 ^ (T + S) * m - 2 ^ S * Achain := by
    rw [Nat.mul_sub]
    rw [← Nat.mul_assoc, hpowT]
  have h3 : 2 ^ (T + S) * m ≤
      5 ^ (L + Q) * m + 5 ^ Q * Amax + 2 ^ S * Achain := by
    rw [hleft] at h2
    have hA : Achain ≤ 2 ^ T * m := by omega
    have hge : 2 ^ S * Achain ≤ 2 ^ (T + S) * m := by
      calc
        2 ^ S * Achain ≤ 2 ^ S * (2 ^ T * m) :=
          Nat.mul_le_mul_left (2 ^ S) hA
        _ = 2 ^ (T + S) * m := by
            rw [← Nat.mul_assoc, hpowT]
    omega
  have hmul : 5 ^ (L + Q) * m ≤ 2 ^ (T + S) * m :=
    Nat.mul_le_mul_right m hcoef
  have hsplit : (2 ^ (T + S) - 5 ^ (L + Q)) * m +
      5 ^ (L + Q) * m = 2 ^ (T + S) * m := by
    rw [← Nat.add_mul]
    rw [Nat.sub_add_cancel hcoef]
  omega

/-- `4^n <= 5^n`. -/
theorem four_pow_le_five_pow (n : Nat) : 4 ^ n ≤ 5 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        4 ^ (n + 1) = 4 * 4 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ 5 * 4 ^ n := Nat.mul_le_mul_right (4 ^ n) (by decide : 4 ≤ 5)
        _ ≤ 5 * 5 ^ n := Nat.mul_le_mul_left (5) ih
        _ = 5 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Rising-segment contribution to the PMI sum. -/
def risePart : List Nat → List Nat → Nat
  | [], _ => 0
  | t :: rise, c3 => 5 ^ (c3.length + rise.length) * 2 ^ t +
      2 ^ t * risePart rise c3

/-- The integer geometric sum matching `risePart`:
`sum_{j=0}^{L-1} 5^(c+L-1-j) * 4^(j+1)`. -/
def geomRise : Nat → Nat → Nat
  | 0, _ => 0
  | L + 1, c => 5 ^ (c + L) * 4 + 4 * geomRise L c

/-- Stronger invariant for the rising geometric sum. -/
theorem geomRise_invariant (L c : Nat) :
    geomRise L c + 4 ^ L * 5 ^ c ≤ 4 * 5 ^ (L + c) := by
  induction L with
  | zero =>
      simp [geomRise]
  | succ L ih =>
      have ih' := ih
      simp [geomRise]
      rw [show L + 1 + c = (L + c) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]
      rw [show 4 ^ L * 4 = 4 * 4 ^ L by rw [Nat.mul_comm]]
      rw [show c + L = L + c by omega]
      rw [show L + c + 1 = (L + c).succ by omega]
      rw [Nat.pow_succ, Nat.mul_comm]
      rw [show (4 * 4 ^ L) * 5 ^ c = 4 * (4 ^ L * 5 ^ c) by
        rw [← Nat.mul_assoc]]
      omega

/-- Bound of the rising geometric sum:
`geomRise L c <= 4 * 5^(L+c)`. -/
theorem geomRise_bound (L c : Nat) :
    geomRise L c ≤ 4 * 5 ^ (L + c) := by
  have h := geomRise_invariant L c
  omega

/-- `risePart` is bounded by the geometric sum. -/
theorem risePart_le_geomRise (rise c3 : List Nat)
    (hr : ∀ t ∈ rise, t ≤ 2) :
    risePart rise c3 ≤ geomRise rise.length c3.length := by
  induction rise with
  | nil => simp [risePart, geomRise]
  | cons t rise ih =>
      have ht : t ≤ 2 := hr t (by simp)
      have h2 : 2 ^ t ≤ 4 := by
        have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> decide
      have ih' := ih (fun x hx => hr x (by simp [hx]))
      simp [risePart]
      calc
        5 ^ (c3.length + rise.length) * 2 ^ t + 2 ^ t * risePart rise c3
            ≤ 5 ^ (c3.length + rise.length) * 4 +
                4 * geomRise rise.length c3.length := by
              have h1 : 5 ^ (c3.length + rise.length) * 2 ^ t ≤
                  5 ^ (c3.length + rise.length) * 4 :=
                Nat.mul_le_mul_left (5 ^ (c3.length + rise.length)) h2
              have h3 : 2 ^ t * risePart rise c3 ≤
                  4 * geomRise rise.length c3.length :=
                Nat.mul_le_mul h2 ih'
              omega
        _ = geomRise (rise.length + 1) c3.length := by
              simp [geomRise]

/-- Rising segment contributes at most `4 * 5^P`. -/
theorem risePart_bound (rise c3 : List Nat)
    (hr : ∀ t ∈ rise, t ≤ 2) :
    risePart rise c3 ≤ 4 * 5 ^ (rise.length + c3.length) := by
  have h := risePart_le_geomRise rise c3 hr
  have hb := geomRise_bound rise.length c3.length
  omega

/-- The C3-segment geometric tail:
`sum_{m=1}^{Q-1} 5^m * 8^(Q-1-m)`. -/
def geomTail : Nat → Nat
  | 0 => 0
  | 1 => 0
  | Q + 2 => 8 * geomTail (Q + 1) + 5 ^ (Q + 1)

/-- Stronger invariant for the C3 geometric tail. -/
theorem geomTail_invariant (Q : Nat) :
    24 * geomTail (Q + 1) + 8 * 5 ^ (Q + 1) ≤ 5 * 8 ^ (Q + 1) := by
  induction Q with
  | zero => simp [geomTail]
  | succ Q ih =>
      simp [geomTail]
      rw [show 5 ^ (Q + 2) = 5 * 5 ^ (Q + 1) by
        rw [show Q + 2 = (Q + 1).succ by omega, Nat.pow_succ, Nat.mul_comm]]
      rw [show 8 ^ (Q + 2) = 8 * 8 ^ (Q + 1) by
        rw [show Q + 2 = (Q + 1).succ by omega, Nat.pow_succ, Nat.mul_comm]]
      omega

/-- C3 geometric tail bound:
`24 * geomTail (Q+1) <= 5 * 8^(Q+1)`. -/
theorem geomTail_bound (Q : Nat) :
    24 * geomTail (Q + 1) ≤ 5 * 8 ^ (Q + 1) := by
  have h := geomTail_invariant Q
  omega

/-- C3-segment contribution, parameterized by the weight already
accumulated before the C3 segment. -/
def c3PartFrom : Nat → List Nat → Nat
  | _, [] => 0
  | _, [_] => 0
  | R, t :: ts => 5 ^ ts.length * 2 ^ (R + t) + c3PartFrom (R + t) ts

/-- A C3 list has weight at least `3 * length`. -/
theorem c3_sum_ge (c3 : List Nat) (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    3 * c3.length ≤ c3.sum := by
  induction c3 with
  | nil => simp
  | cons t ts ih =>
      have ht : 3 ≤ t := hc3 t (by simp)
      have ih' := ih (fun x hx => hc3 x (by simp [hx]))
      simp [List.sum_cons]
      omega

/-- Recurrence of `geomTail` for positive length. -/
theorem geomTail_succ_of_pos (len : Nat) (h : 0 < len) :
    geomTail (len + 1) = 8 * geomTail len + 5 ^ len := by
  cases len with
  | zero => omega
  | succ m =>
      change geomTail (Nat.succ m + 1) =
        8 * geomTail (Nat.succ m) + 5 ^ Nat.succ m
      have hlen : Nat.succ m + 1 = m + 2 := by omega
      rw [hlen]
      simp [geomTail]

/-- C3-segment contribution is bounded by the geometric tail:
`c3PartFrom R c3 <= 2^(T - 3(Q-1)) * geomTail Q`. -/
theorem c3PartFrom_le (R : Nat) (c3 : List Nat)
    (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    c3PartFrom R c3 ≤
      2 ^ (R + c3.sum - 3 * (c3.length - 1)) * geomTail c3.length := by
  induction c3 generalizing R with
  | nil => simp [c3PartFrom, geomTail]
  | cons t ts ih =>
      by_cases hts : ts = []
      · simp [c3PartFrom, geomTail, hts]
      · have hlen : 0 < ts.length := by
          cases ts with
          | nil => contradiction
          | cons a as => simp
        have ht : 3 ≤ t := hc3 t (by simp)
        have ih' := ih (R + t) (fun x hx => hc3 x (by simp [hx]))
        have hsum : 3 * ts.length ≤ ts.sum :=
          c3_sum_ge ts (fun x hx => hc3 x (by simp [hx]))
        simp [c3PartFrom]
        rw [show R + (t + ts.sum) = R + t + ts.sum by omega]
        have hIH : c3PartFrom (R + t) ts ≤
            2 ^ (R + t + ts.sum - 3 * (ts.length - 1)) *
              geomTail ts.length := ih'
        have hdiff : R + t + ts.sum - 3 * (ts.length - 1) =
            (R + t + ts.sum - 3 * ts.length) + 3 := by omega
        have hpow : 2 ^ (R + t + ts.sum - 3 * (ts.length - 1)) =
            8 * 2 ^ (R + t + ts.sum - 3 * ts.length) := by
          rw [hdiff, Nat.pow_add]
          rw [show 2 ^ 3 = 8 by decide]
          rw [Nat.mul_comm]
        have hfirst : 5 ^ ts.length * 2 ^ (R + t) ≤
            2 ^ (R + t + ts.sum - 3 * ts.length) * 5 ^ ts.length := by
          have hexp : R + t ≤ R + t + ts.sum - 3 * ts.length := by omega
          have h2 : 2 ^ (R + t) ≤ 2 ^ (R + t + ts.sum - 3 * ts.length) :=
            Nat.pow_le_pow_right (by decide : 0 < 2) hexp
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_right (5 ^ ts.length) h2
        have htail : c3PartFrom (R + t) ts ≤
            8 * 2 ^ (R + t + ts.sum - 3 * ts.length) *
              geomTail ts.length := by
          calc
            c3PartFrom (R + t) ts
                ≤ 2 ^ (R + t + ts.sum - 3 * (ts.length - 1)) *
                    geomTail ts.length := hIH
            _ = (8 * 2 ^ (R + t + ts.sum - 3 * ts.length)) *
                    geomTail ts.length := by rw [hpow]
            _ = 8 * 2 ^ (R + t + ts.sum - 3 * ts.length) *
                    geomTail ts.length := by rw [Nat.mul_assoc]
        have hrec : geomTail (ts.length + 1) =
            8 * geomTail ts.length + 5 ^ ts.length :=
          geomTail_succ_of_pos ts.length hlen
        calc
          5 ^ ts.length * 2 ^ (R + t) + c3PartFrom (R + t) ts
              ≤ 2 ^ (R + t + ts.sum - 3 * ts.length) * 5 ^ ts.length +
                  8 * 2 ^ (R + t + ts.sum - 3 * ts.length) *
                    geomTail ts.length := by
                exact Nat.add_le_add hfirst htail
            _ = 2 ^ (R + t + ts.sum - 3 * ts.length) *
                  (5 ^ ts.length + 8 * geomTail ts.length) := by
                  rw [show 8 * 2 ^ (R + t + ts.sum - 3 * ts.length) *
                        geomTail ts.length =
                      2 ^ (R + t + ts.sum - 3 * ts.length) *
                        (8 * geomTail ts.length) by ac_rfl]
                  rw [Nat.mul_add]
            _ = 2 ^ (R + t + ts.sum - 3 * ts.length) *
                  geomTail (ts.length + 1) := by
                  rw [Nat.add_comm (5 ^ ts.length) (8 * geomTail ts.length)]
                  rw [hrec]

/-- The total PMI numerator under the spike decomposition:
the `j=0` term, the rising segment, and the C3 tail. -/
def pmiTotal (rise c3 : List Nat) : Nat :=
  5 ^ (rise.length + c3.length) + risePart rise c3 +
    c3PartFrom rise.sum c3

/-- Prefix weight after `j` steps of the concatenated word. -/
def prefixWeightList (l : List Nat) (j : Nat) : Nat :=
  (l.take j).sum

/-- The `P`-term PMI numerator in list form:
`sum_{j=0}^{P-1} 5^(P-j) * 2^(W_j)`, matching `Pmi.aTotal5`. -/
def pmiSum (rise c3 : List Nat) : Nat :=
  ((List.range (rise.length + c3.length)).map
    (fun j =>
      5 ^ (rise.length + c3.length - j) *
        2 ^ prefixWeightList (rise ++ c3) j)).sum

/-- Cleared-denominator C3 tail bound:
`3 * c3PartFrom <= 5 * 2^(R + S)`. -/
theorem c3PartFrom_cleared_bound (R : Nat) (c3 : List Nat)
    (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    3 * c3PartFrom R c3 ≤ 5 * 2 ^ (R + c3.sum) := by
  by_cases hQ : c3.length ≤ 1
  · have hzero : c3PartFrom R c3 = 0 := by
      cases c3 with
      | nil => simp [c3PartFrom]
      | cons t ts =>
          have hts : ts = [] := by
            cases ts with
            | nil => rfl
            | cons a as =>
                simp at hQ
          simp [c3PartFrom, hts]
    rw [hzero]
    omega
  · have hQge2 : 2 ≤ c3.length := by omega
    have hsum : 3 * c3.length ≤ c3.sum := c3_sum_ge c3 hc3
    have hle := c3PartFrom_le R c3 hc3
    have hgeom : 24 * geomTail c3.length ≤ 5 * 8 ^ c3.length := by
      have hg := geomTail_bound (c3.length - 1)
      have hsub : (c3.length - 1) + 1 = c3.length := by omega
      rwa [hsub] at hg
    let A : Nat := 2 ^ (R + c3.sum - 3 * (c3.length - 1))
    have hmul24 : 24 * c3PartFrom R c3 ≤
        24 * (A * geomTail c3.length) := by
      change 24 * c3PartFrom R c3 ≤
        24 * (2 ^ (R + c3.sum - 3 * (c3.length - 1)) *
          geomTail c3.length)
      exact Nat.mul_le_mul_left 24 hle
    have hassoc : 24 * (A * geomTail c3.length) =
        A * (24 * geomTail c3.length) := by
      rw [← Nat.mul_assoc, Nat.mul_comm 24 A, Nat.mul_assoc]
    have hgeom24 : 24 * (A * geomTail c3.length) ≤
        A * (5 * 8 ^ c3.length) := by
      rw [hassoc]
      exact Nat.mul_le_mul_left A hgeom
    have htail24 : 24 * c3PartFrom R c3 ≤
        A * (5 * 8 ^ c3.length) := Nat.le_trans hmul24 hgeom24
    have hpow8 : A * (5 * 8 ^ c3.length) =
        5 * 2 ^ (R + c3.sum + 3) := by
      have h8 : 8 ^ c3.length = 2 ^ (3 * c3.length) :=
        (two_pow_three_mul_eq_eight_pow c3.length).symm
      rw [h8]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm A 5]
      rw [Nat.mul_assoc]
      rw [show A = 2 ^ (R + c3.sum - 3 * (c3.length - 1)) by rfl]
      rw [← Nat.pow_add]
      congr 1
      congr 1
      have hsubok : 3 * (c3.length - 1) ≤ R + c3.sum := by omega
      omega
    have h24 : 24 * c3PartFrom R c3 ≤ 5 * 2 ^ (R + c3.sum + 3) := by
      rw [hpow8] at htail24
      exact htail24
    have hright : 5 * 2 ^ (R + c3.sum + 3) =
        8 * (5 * 2 ^ (R + c3.sum)) := by
      have hshift : R + c3.sum + 3 = (R + c3.sum) + 3 := by omega
      rw [hshift, Nat.pow_add]
      rw [show 2 ^ 3 = 8 by decide]
      rw [← Nat.mul_assoc]
      rw [Nat.mul_comm (5 * 2 ^ (R + c3.sum)) 8]
    have h8le : 8 * (3 * c3PartFrom R c3) ≤
        8 * (5 * 2 ^ (R + c3.sum)) := by
      have h24' : 8 * (3 * c3PartFrom R c3) ≤
          5 * 2 ^ (R + c3.sum + 3) := by
        have h24eq : 8 * (3 * c3PartFrom R c3) = 24 * c3PartFrom R c3 := by
          omega
        calc
          8 * (3 * c3PartFrom R c3) = 24 * c3PartFrom R c3 := h24eq
          _ ≤ 5 * 2 ^ (R + c3.sum + 3) := h24
      simpa [hright] using h24'
    exact Nat.le_of_mul_le_mul_left h8le (by decide : 0 < 8)

/-- GC-7 cleared-denominator PMI upper bound under the spike
decomposition: `3 * pmiTotal <= 3 * 5^(P+1) + 5 * 2^T`. -/
theorem gc7_pmi_cleared_bound (rise c3 : List Nat)
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    3 * pmiTotal rise c3 ≤
      3 * 5 ^ (rise.length + c3.length + 1) +
        5 * 2 ^ (rise.sum + c3.sum) := by
  let P : Nat := rise.length + c3.length
  have hr := risePart_bound rise c3 hrise
  have hc := c3PartFrom_cleared_bound rise.sum c3 hc3
  have hr3 : 3 * risePart rise c3 ≤ 12 * 5 ^ P := by
    have h' : 3 * risePart rise c3 ≤ 3 * (4 * 5 ^ P) := by
      simpa [P] using (Nat.mul_le_mul_left 3 hr)
    omega
  have hsum : 3 * pmiTotal rise c3 =
      3 * 5 ^ P + 3 * risePart rise c3 + 3 * c3PartFrom rise.sum c3 := by
    unfold pmiTotal
    simp [P, Nat.mul_add]
  rw [hsum]
  have hriseTotal : 3 * 5 ^ P + 3 * risePart rise c3 ≤
      3 * 5 ^ (P + 1) := by
    have hpow : 5 ^ (P + 1) = 5 * 5 ^ P := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    omega
  have htarget : 3 * 5 ^ P + 3 * risePart rise c3 +
      3 * c3PartFrom rise.sum c3 ≤
      3 * 5 ^ (P + 1) + 5 * 2 ^ (rise.sum + c3.sum) := by
    exact Nat.add_le_add hriseTotal hc
  simpa [P] using htarget

/-- GC-7 `m` narrow window, cleared denominators:
from the PMI numerator identity one obtains
`3*m*(2^T-5^P) <= 3*5^P + 2^T`. -/
theorem gc7_m_cleared_bound (rise c3 : List Nat) (m : Nat)
    (hpm : pmiTotal rise c3 =
      5 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)))
    (hrise : ∀ t ∈ rise, t ≤ 2)
    (hc3 : ∀ t ∈ c3, 3 ≤ t) :
    3 * m * (2 ^ (rise.sum + c3.sum) - 5 ^ (rise.length + c3.length)) ≤
      3 * 5 ^ (rise.length + c3.length) +
        2 ^ (rise.sum + c3.sum) := by
  let P : Nat := rise.length + c3.length
  let T : Nat := rise.sum + c3.sum
  have hgc : 3 * pmiTotal rise c3 ≤
      3 * 5 ^ (P + 1) + 5 * 2 ^ T := by
    simpa [P, T] using (gc7_pmi_cleared_bound rise c3 hrise hc3)
  have hfive : 5 * (3 * m * (2 ^ T - 5 ^ P)) = 3 * pmiTotal rise c3 := by
    rw [hpm]
    ac_rfl
  have hright : 15 * 5 ^ P + 5 * 2 ^ T = 5 * (3 * 5 ^ P + 2 ^ T) := by
    omega
  have hle5 : 5 * (3 * m * (2 ^ T - 5 ^ P)) ≤
      5 * (3 * 5 ^ P + 2 ^ T) := by
    rw [hfive]
    have hP : 3 * 5 ^ (P + 1) = 15 * 5 ^ P := by
      rw [show 5 ^ (P + 1) = 5 * 5 ^ P by rw [Nat.pow_succ, Nat.mul_comm]]
      omega
    rw [hP] at hgc
    rw [hright] at hgc
    exact hgc
  exact Nat.le_of_mul_le_mul_left hle5 (by decide : 0 < 5)

/-- Number of `t = 2` steps in a rising segment. -/
def countTwo : List Nat → Nat
  | [] => 0
  | t :: ts => (if t = 2 then 1 else 0) + countTwo ts

/-- GC-15 `U = 0` core: an all-`1` rising segment contributes at most
`(5/3) * 5^P` to the PMI numerator, cleared as
`3 * risePart <= 5 * 5^P`. -/
theorem gc15_rise_all_one_bound (rise c3 : List Nat)
    (hrise : ∀ t ∈ rise, t = 1) :
    3 * risePart rise c3 ≤ 5 * 5 ^ (rise.length + c3.length) := by
  induction rise generalizing c3 with
  | nil => simp [risePart]
  | cons t ts ih =>
      have ht : t = 1 := hrise t (by simp)
      subst t
      have ih' := ih c3 (fun x hx => hrise x (by simp [hx]))
      let P : Nat := ts.length + c3.length
      have hterm : 3 * (5 ^ (c3.length + ts.length) * 2) ≤ 6 * 5 ^ P := by
        have hP : c3.length + ts.length = P := by omega
        rw [hP]
        omega
      have htail : 3 * (2 * risePart ts c3) ≤ 10 * 5 ^ P := by
        have h2 : 3 * (2 * risePart ts c3) = 2 * (3 * risePart ts c3) := by
          omega
        rw [h2]
        have h3 : 3 * risePart ts c3 ≤ 5 * 5 ^ P := by
          simpa [P] using ih'
        have h4 : 2 * (3 * risePart ts c3) ≤ 2 * (5 * 5 ^ P) := by
          exact Nat.mul_le_mul_left 2 h3
        have h5 : 2 * (5 * 5 ^ P) = 10 * 5 ^ P := by omega
        simpa [h5] using h4
      have hsum : 3 * (5 ^ (c3.length + ts.length) * 2 +
          2 * risePart ts c3) ≤ 16 * 5 ^ P := by
        have hsum' : 3 * (5 ^ (c3.length + ts.length) * 2 +
            2 * risePart ts c3) =
            3 * (5 ^ (c3.length + ts.length) * 2) +
              3 * (2 * risePart ts c3) := by
          rw [Nat.mul_add]
        rw [hsum']
        omega
      have htarget : 16 * 5 ^ P ≤ 5 * 5 ^ ((1 :: ts).length + c3.length) := by
        have hexp : (1 :: ts).length + c3.length = P + 1 := by
          simp [P]
          omega
        rw [hexp]
        have hpow : 5 ^ (P + 1) = 5 * 5 ^ P := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow]
        omega
      have hle : 3 * risePart (1 :: ts) c3 ≤ 16 * 5 ^ P := by
        change 3 * (5 ^ (c3.length + ts.length) * 2 +
          2 * risePart ts c3) ≤ 16 * 5 ^ P
        exact hsum
      exact Nat.le_trans hle htarget

/-- Prefix weight after `j + 1` steps of a consed word. -/
theorem prefixWeightList_cons (t : Nat) (l : List Nat) (j : Nat) :
    prefixWeightList (t :: l) (j + 1) = t + prefixWeightList l j := by
  unfold prefixWeightList
  rw [List.take_cons (by omega)]
  rw [show j + 1 - 1 = j by omega]
  simp

/-- C3 part shifts by a head weight: `c3PartFrom (R + t) c3 =
`2^t * c3PartFrom R c3`. -/
theorem c3PartFrom_add (R t : Nat) (c3 : List Nat) :
    c3PartFrom (R + t) c3 = 2 ^ t * c3PartFrom R c3 := by
  induction c3 generalizing R with
  | nil => simp [c3PartFrom]
  | cons u us ih =>
      cases us with
      | nil => simp [c3PartFrom]
      | cons v vs =>
          simp [c3PartFrom]
          rw [show R + t + u = (R + u) + t by omega]
          rw [ih (R + u)]
          rw [Nat.pow_add]
          ring

/-- Removing the first step of the concatenated word shifts the PMI
sum: `pmiSum (t :: rise) c3 = 5^(P+1) + 2^t * pmiSum rise c3`. -/
theorem pmiSum_cons (t : Nat) (rise c3 : List Nat) :
    pmiSum (t :: rise) c3 =
      5 ^ ((t :: rise).length + c3.length) + 2 ^ t * pmiSum rise c3 := by
  unfold pmiSum
  have hlen : (t :: rise).length + c3.length =
      (rise ++ c3).length + 1 := by
    simp [List.length_append]
    omega
  rw [hlen]
  rw [StringFlow.PMI.range_succ_cons (rise ++ c3).length]
  rw [List.map_cons, List.sum_cons]
  rw [List.map_map]
  simp [prefixWeightList]
  change (List.map (fun j =>
      5 ^ (rise.length + c3.length + 1 - (j + 1)) *
        2 ^ prefixWeightList (t :: (rise ++ c3)) (j + 1))
      (List.range (rise.length + c3.length))).sum =
    2 ^ t * (List.map (fun j =>
      5 ^ (rise.length + c3.length - j) *
        2 ^ prefixWeightList (rise ++ c3) j)
      (List.range (rise.length + c3.length))).sum
  have hpoint : ∀ j : Nat,
      5 ^ (rise.length + c3.length + 1 - (j + 1)) *
           2 ^ prefixWeightList (t :: (rise ++ c3)) (j + 1) =
         2 ^ t * (5 ^ (rise.length + c3.length - j) *
           2 ^ prefixWeightList (rise ++ c3) j) := by
    intro j
    have hpc := prefixWeightList_cons t (rise ++ c3) j
    change 5 ^ (rise.length + c3.length + 1 - (j + 1)) *
        2 ^ prefixWeightList (t :: (rise ++ c3)) (j + 1) =
      2 ^ t * (5 ^ (rise.length + c3.length - j) *
        2 ^ prefixWeightList (rise ++ c3) j)
    rw [hpc, Nat.pow_add]
    rw [show rise.length + c3.length + 1 - (j + 1) =
        rise.length + c3.length - j by omega]
    ring
  have hmap : (List.map (fun j =>
      5 ^ (rise.length + c3.length + 1 - (j + 1)) *
         2 ^ prefixWeightList (t :: (rise ++ c3)) (j + 1))
         (List.range (rise.length + c3.length))).sum =
      2 ^ t * (List.map (fun j =>
        5 ^ (rise.length + c3.length - j) *
          2 ^ prefixWeightList (rise ++ c3) j)
          (List.range (rise.length + c3.length))).sum := by
    have hmapEq : List.map (fun j =>
        5 ^ (rise.length + c3.length + 1 - (j + 1)) *
           2 ^ prefixWeightList (t :: (rise ++ c3)) (j + 1))
          (List.range (rise.length + c3.length)) =
        List.map (fun j => 2 ^ t *
          (5 ^ (rise.length + c3.length - j) *
            2 ^ prefixWeightList (rise ++ c3) j))
          (List.range (rise.length + c3.length)) := by
      apply List.map_congr_left
      intro j hj
      exact hpoint j
    rw [hmapEq]
    exact StringFlow.PMI.sum_map_mul_left (List.range (rise.length + c3.length))
      (2 ^ t)
      (fun j => 5 ^ (rise.length + c3.length - j) *
        2 ^ prefixWeightList (rise ++ c3) j)
  rw [hmap]

/-- C3 contribution starting from zero with a nonempty tail. -/
theorem c3PartFrom_zero_cons (t u : Nat) (us : List Nat) :
    c3PartFrom 0 (t :: u :: us) =
      5 ^ (us.length + 1) * 2 ^ t + 2 ^ t * c3PartFrom 0 (u :: us) := by
  simp [c3PartFrom]
  have hshift : c3PartFrom t (u :: us) =
      2 ^ t * c3PartFrom 0 (u :: us) := by
    simpa using c3PartFrom_add 0 t (u :: us)
  rw [hshift]

/-- PMI sum with an empty rising segment and a nonempty C3 segment. -/
theorem pmiSum_nil (c3 : List Nat) (hc3 : c3 ≠ []) :
    pmiSum [] c3 = 5 ^ c3.length + c3PartFrom 0 c3 := by
  induction c3 with
  | nil => contradiction
  | cons t ts ih =>
      cases ts with
      | nil => simp [pmiSum, prefixWeightList, c3PartFrom]
      | cons u us =>
          have hsame : pmiSum [] (t :: u :: us) =
              pmiSum (t :: []) (u :: us) := by
            unfold pmiSum
            simp [prefixWeightList, List.length_cons,
              List.length_nil, List.cons_append]
            rw [show us.length + 1 + 1 = 1 + (us.length + 1) by omega]
          rw [hsame, pmiSum_cons]
          have hih := ih (by simp : u :: us ≠ [])
          rw [hih]
          rw [c3PartFrom_zero_cons]
          simp [Nat.mul_add, Nat.mul_comm]
          ring_nf

/-- The cleared PMI total satisfies the same head recurrence. -/
theorem pmiTotal_cons (t : Nat) (rise c3 : List Nat) :
    pmiTotal (t :: rise) c3 =
      5 ^ ((t :: rise).length + c3.length) + 2 ^ t * pmiTotal rise c3 := by
  unfold pmiTotal
  change 5 ^ ((t :: rise).length + c3.length) +
      risePart (t :: rise) c3 + c3PartFrom (t + rise.sum) c3 =
    5 ^ ((t :: rise).length + c3.length) +
      2 ^ t * (5 ^ (rise.length + c3.length) + risePart rise c3 +
        c3PartFrom rise.sum c3)
  have hc : c3PartFrom (t + rise.sum) c3 =
      2 ^ t * c3PartFrom rise.sum c3 := by
    rw [Nat.add_comm t rise.sum]
    exact c3PartFrom_add rise.sum t c3
  rw [hc]
  simp [risePart]
  have hcomm : c3.length + rise.length = rise.length + c3.length := by
    omega
  rw [hcomm]
  ring_nf

/-- The spike-decomposed PMI numerator equals the list-form PMI
sum for the concatenated word `rise ++ c3`, for a nonempty C3
segment. -/
theorem pmiSum_eq_pmiTotal (rise c3 : List Nat) (hc3 : c3 ≠ []) :
    pmiSum rise c3 = pmiTotal rise c3 := by
  induction rise generalizing c3 with
  | nil => rw [pmiSum_nil c3 hc3]; unfold pmiTotal; simp [risePart]
  | cons t ts ih =>
      rw [pmiSum_cons, pmiTotal_cons, ih c3 hc3]

end StringFlow.GC
