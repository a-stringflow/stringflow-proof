import WordWindow
import AutomatonInterface
import SurvivorExplicit

namespace StringFlow.QWindow

/-- Bad residue `q_V = (-(5A+3*2^W) * 5^{-(i+1)}) mod 2^E`. -/
def badResidue (A W i E : Nat) : Nat :=
  let M := 2 ^ E
  let N := 5 * A + 3 * 2 ^ W
  let inv := StringFlow.Word.invOdd (5 ^ (i + 1)) (E - 1)
  ((M - N % M) * inv) % M

/-- Carry balance `B_i = ((q_V - q_i) / 2^W) mod 2^(H+1)`. -/
def carryBalance (A W i q H : Nat) : Nat :=
  let E := W + H + 1
  let M := 2 ^ E
  let qV := badResidue A W i E
  let d := (qV + M - q % 2 ^ W) % M
  d / 2 ^ W % 2 ^ (H + 1)

/-- Carry bit `c_i`: the bit of `q_V` at position `W+H+1`, i.e. the
bit gained when the window is lifted from `2^(W+H+1)` to
`2^(W+H+2)`. -/
def carryBit (A W i H : Nat) : Nat :=
  (badResidue A W i (W + H + 2) / 2 ^ (W + H + 1)) % 2

/-- Lifted `q_V`: the bad residue with one extra high bit supplied by
`c_i`. -/
def badResidueLift (A W i H : Nat) : Nat :=
  badResidue A W i (W + H + 1) +
    carryBit A W i H * 2 ^ (W + H + 1)

/-- Inverse correctness of `badResidue`. -/
theorem badResidue_spec (A W i E : Nat) (hE : 1 ≤ E) :
    (5 ^ (i + 1) * badResidue A W i E) % 2 ^ E =
      (2 ^ E - (5 * A + 3 * 2 ^ W) % 2 ^ E) % 2 ^ E := by
  unfold badResidue
  let M := 2 ^ E
  let N := 5 * A + 3 * 2 ^ W
  let inv := StringFlow.Word.invOdd (5 ^ (i + 1)) (E - 1)
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hodd : (5 ^ (i + 1)) % 2 = 1 :=
    StringFlow.Lte.five_pow_odd (i + 1)
  have hinv : ((5 ^ (i + 1)) * inv) % M = 1 := by
    dsimp [inv, M]
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 1)) hodd (E - 1)
    have hpow : 2 ^ ((E - 1) + 1) = 2 ^ E := by
      congr 1
      omega
    simpa [hpow] using h
  have hstep := StringFlow.Word.mul_mod_inv (5 ^ (i + 1))
    (M - N % M) inv M hinv
  simpa [N, inv, M] using hstep

/-- Multiplying by a wrapped residue gives the same residue as the
unwrapped product. -/
theorem mul_mod_mul_mod (a b M : Nat) :
    (a * (b % M)) % M = (a * b) % M := by
  rw [Nat.mul_mod, Nat.mul_mod]
  simp

/-- `(b+M-t)%M` is the wrapped representative of `b-t`. -/
theorem wrapped_sub_add (b t M : Nat) (hM : 0 < M) (hb : b < M)
    (ht : t < M) :
    (((b + M - t) % M) + t) % M = b % M := by
  let r := (b + M - t) % M
  by_cases hle : t ≤ b
  · have hval : b + M - t = M + (b - t) := by omega
    have hmod : (M + (b - t)) % M = b - t := by
      rw [Nat.add_comm]
      rw [StringFlow.Word.add_mod_mul_one (b - t) M]
      exact Nat.mod_eq_of_lt (by omega)
    have hr : r = b - t := by
      dsimp [r]
      rw [hval, hmod]
    have hsum : r + t = b := by omega
    rw [hsum]
  · have hval : b + M - t = M - (t - b) := by omega
    have hlt : M - (t - b) < M := by omega
    have hmod : (M - (t - b)) % M = M - (t - b) := Nat.mod_eq_of_lt hlt
    have hr : r = M - (t - b) := by
      dsimp [r]
      rw [hval, hmod]
    have hsum : r + t = M + b := by omega
    rw [hsum, Nat.add_mod]
    have hbmod : b % M = b := Nat.mod_eq_of_lt hb
    have hMmod : M % M = 0 := Nat.mod_self M
    rw [hbmod, hMmod]
    simp
    exact Nat.mod_eq_of_lt hb

/-- Wrapped subtraction distributes through multiplication modulo `M`. -/
theorem mul_wrapped_sub_add (a b t M : Nat) (hM : 0 < M) (hb : b < M)
    (ht : t < M) :
    (a * ((b + M - t) % M) + a * t) % M = (a * b) % M := by
  let r := (b + M - t) % M
  have hsum := wrapped_sub_add b t M hM hb ht
  calc
    (a * r + a * t) % M = (a * (r + t)) % M := by rw [Nat.mul_add]
    _ = (a * ((r + t) % M)) % M := (mul_mod_mul_mod a (r + t) M).symm
    _ = (a * (b % M)) % M := by rw [hsum]
    _ = (a * b) % M := mul_mod_mul_mod a b M

/-- From `(a+b)%M = c%M`, recover `a%M` as the modular subtraction
`(c%M + M - b%M)%M`. -/
theorem mod_sub_of_add_eq (a b c M : Nat) (hM : 0 < M)
    (h : (a + b) % M = c % M) :
    a % M = (c % M + M - b % M) % M := by
  let r := a % M
  let s := b % M
  let t := c % M
  have hrs : (r + s) % M = t := by
    have hmod := Nat.add_mod a b M
    rw [hmod] at h
    simpa [r, s, t] using h
  have hrlt : r < M := by
    dsimp [r]
    exact Nat.mod_lt a hM
  have hslt : s < M := by
    dsimp [s]
    exact Nat.mod_lt b hM
  by_cases hlt : r + s < M
  · have hmod : (r + s) % M = r + s := Nat.mod_eq_of_lt hlt
    rw [hmod] at hrs
    have hts : t + M - s = M + r := by omega
    rw [hts]
    rw [Nat.add_comm]
    rw [StringFlow.Word.add_mod_mul_one r M]
    change r = r % M
    exact (Nat.mod_eq_of_lt hrlt).symm
  · have hge : M ≤ r + s := by omega
    have hlt2 : r + s - M < M := by omega
    have hmod : (r + s) % M = r + s - M := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt hlt2
    rw [hmod] at hrs
    have hts : t + M - s = r := by omega
    rw [hts]
    change r = r % M
    exact (Nat.mod_eq_of_lt hrlt).symm

/-- `M-a` is either `0` or `M-a`, depending on whether `a=0`. -/
theorem mod_minus_self (a M : Nat) (ha : a < M) :
    (M - a) % M = if a = 0 then 0 else M - a := by
  by_cases ha0 : a = 0
  · simp [ha0]
  · have hlt : M - a < M := by omega
    simp [ha0, Nat.mod_eq_of_lt hlt]

/-- Negative-residue addition: `(-X) + (-y) ≡ -(X+y) (mod M)`. -/
theorem mod_sub_neg_add (X y M : Nat) (hM : 0 < M) :
    ((M - X % M) % M + M - y % M) % M =
      (M - (X + y) % M) % M := by
  let a := X % M
  let b := y % M
  have ha : a < M := by
    dsimp [a]
    exact Nat.mod_lt X hM
  have hb : b < M := by
    dsimp [b]
    exact Nat.mod_lt y hM
  have hma := mod_minus_self a M ha
  have hmain : ((M - a) % M + M - b) % M = (M - (a + b) % M) % M := by
    by_cases hab0 : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      simp [ha0, hb0]
    · by_cases hlt : a + b < M
      · have hmodab : (a + b) % M = a + b := Nat.mod_eq_of_lt hlt
        have hL : ((M - a) % M + M - b) % M = M - (a + b) := by
          by_cases ha0 : a = 0
          · have hbpos : 0 < b := by omega
            rw [hma, ha0]
            simp
            exact Nat.mod_eq_of_lt (by omega)
          · have hma' : (M - a) % M = M - a := by
              rw [hma]
              simp [ha0]
            rw [hma']
            have hval : M - a + M - b = 2 * M - (a + b) := by omega
            rw [hval]
            have hge : M ≤ 2 * M - (a + b) := by omega
            have hlt2 : 2 * M - (a + b) - M < M := by omega
            rw [Nat.mod_eq_sub_mod hge]
            have hred : 2 * M - (a + b) - M = M - (a + b) := by omega
            rw [hred]
            exact Nat.mod_eq_of_lt (by omega)
        rw [hmodab]
        have htarget : M - (a + b) < M := by omega
        rw [Nat.mod_eq_of_lt htarget]
        exact hL
      · by_cases heq : a + b = M
        · have hL : ((M - a) % M + M - b) % M = 0 := by
            by_cases ha0 : a = 0
            · have hbM : b = M := by omega
              omega
            · have hma' : (M - a) % M = M - a := by
                rw [hma]
                simp [ha0]
              rw [hma']
              have hval : M - a + M - b = M := by omega
              rw [hval, Nat.mod_self]
          rw [heq, Nat.mod_self]
          simp
          exact hL
        · have hgt : M < a + b := by omega
          have hmodab : (a + b) % M = a + b - M := by
            rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hgt)]
            exact Nat.mod_eq_of_lt (by omega)
          have hL : ((M - a) % M + M - b) % M = 2 * M - (a + b) := by
            have ha0 : a ≠ 0 := by
              intro hz
              have : M < b := by omega
              omega
            have hma' : (M - a) % M = M - a := by
              rw [hma]
              simp [ha0]
            rw [hma']
            have hval : M - a + M - b = 2 * M - (a + b) := by omega
            rw [hval]
            exact Nat.mod_eq_of_lt (by omega)
          have hR : (M - (a + b - M)) % M = 2 * M - (a + b) := by
            have hRval : M - (a + b - M) = 2 * M - (a + b) := by omega
            rw [hRval]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hmodab]
          rw [hR]
          exact hL
  simpa [a, b] using hmain

/-- Multiplying by the negative residue `-y` gives `-(a*y)`. -/
theorem mul_mod_neg (a y M : Nat) (hM : 0 < M) :
    (a * ((M - y % M) % M)) % M = (M - (a * y) % M) % M := by
  let s := y % M
  have hs : s < M := by
    dsimp [s]
    exact Nat.mod_lt y hM
  have hsum : a * (M - s) + a * s = a * M := by
    rw [← Nat.mul_add]
    have hsub : (M - s) + s = M := Nat.sub_add_cancel (Nat.le_of_lt hs)
    rw [hsub]
  have hMmul : (a * M) % M = 0 := by
    rw [Nat.mul_comm]
    rw [Nat.mul_mod_right]
  have hsum0 : (a * (M - s) + a * s) % M = 0 := by
    rw [hsum, hMmul]
  have hsubRhs := mod_sub_of_add_eq (a * (M - s)) (a * s) 0 M hM (by
    simpa using hsum0)
  have hy : (a * s) % M = (a * y) % M := by
    dsimp [s]
    exact mul_mod_mul_mod a y M
  have hval : 0 + M - (a * y) % M = M - (a * y) % M := by omega
  calc
    (a * ((M - y % M) % M)) % M
        = (a * (M - y % M)) % M := by
            rw [mul_mod_mul_mod a (M - y % M) M]
    _ = (a * (M - s)) % M := by dsimp [s]
    _ = (0 + M - (a * s) % M) % M := hsubRhs
    _ = (M - (a * y) % M) % M := by rw [hy, hval]

/-- A number below `2^E` with the bad-residue congruence is exactly
`badResidue`. -/
theorem badResidue_eq_of_spec (A W i E x : Nat) (hE : 1 ≤ E)
    (hx : x < 2 ^ E)
    (h : (5 ^ (i + 1) * x) % 2 ^ E =
      (2 ^ E - (5 * A + 3 * 2 ^ W) % 2 ^ E) % 2 ^ E) :
    x = badResidue A W i E := by
  let M := 2 ^ E
  let N := 5 * A + 3 * 2 ^ W
  let inv := StringFlow.Word.invOdd (5 ^ (i + 1)) (E - 1)
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hodd : (5 ^ (i + 1)) % 2 = 1 :=
    StringFlow.Lte.five_pow_odd (i + 1)
  have hinv : ((5 ^ (i + 1)) * inv) % M = 1 := by
    dsimp [inv, M]
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 1)) hodd (E - 1)
    have hpow : 2 ^ ((E - 1) + 1) = 2 ^ E := by
      congr 1
      omega
    simpa [hpow] using h
  have hspec := badResidue_spec A W i E hE
  have hcancel := StringFlow.Word.mod_cancel_mul_left (5 ^ (i + 1))
    x (badResidue A W i E) inv M hM hinv (by
      rw [h, hspec])
  have hxmod : x % M = x := Nat.mod_eq_of_lt hx
  have hbmod : badResidue A W i E % M = badResidue A W i E := by
    unfold badResidue
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hM)
  rw [hxmod, hbmod] at hcancel
  exact hcancel

/-- If `(a+b)%M=0`, then `b%M` is the negative residue of `a%M`. -/
theorem mod_add_eq_zero_imp (a b M : Nat) (hM : 0 < M)
    (h : (a + b) % M = 0) :
    b % M = (M - a % M) % M := by
  let r := a % M
  have hrlt : r < M := by
    dsimp [r]
    exact Nat.mod_lt a hM
  have hb : b % M < M := Nat.mod_lt b hM
  have hres : (r + b % M) % M = 0 := by
    dsimp [r]
    rw [Nat.add_mod] at h
    exact h
  by_cases hr0 : r = 0
  · have hb0 : b % M = 0 := by
      have hres' : (b % M) % M = 0 := by simpa [hr0] using hres
      have hmod : (b % M) % M = b % M := Nat.mod_eq_of_lt hb
      rw [hmod] at hres'
      exact hres'
    change b % M = (M - r) % M
    rw [hb0]
    simp [hr0]
  · have hge : M ≤ r + b % M := by
      by_cases hge' : M ≤ r + b % M
      · exact hge'
      · have hlt' : r + b % M < M := by omega
        have hmod : (r + b % M) % M = r + b % M := Nat.mod_eq_of_lt hlt'
        rw [hmod] at hres
        omega
    have hsub : r + b % M - M < M := by omega
    have hsub0 : r + b % M - M = 0 := by
      have hres' : (r + b % M - M) % M = 0 := by
        rw [Nat.mod_eq_sub_mod hge] at hres
        exact hres
      have hmod : (r + b % M - M) % M = r + b % M - M :=
        Nat.mod_eq_of_lt hsub
      rw [hmod] at hres'
      exact hres'
    have hbM : b % M = M - r := by omega
    change b % M = (M - r) % M
    rw [hbM]
    have hMr : M - r < M := by omega
    exact (Nat.mod_eq_of_lt hMr).symm

/-- The converse modular identity: if `b%M` is the negative residue
of `a%M`, then `(a+b)%M=0`. -/
theorem mod_add_eq_zero_of_b_eq_neg (a b M : Nat) (hM : 0 < M)
    (h : b % M = (M - a % M) % M) :
    (a + b) % M = 0 := by
  let r := a % M
  have hrlt : r < M := by
    dsimp [r]
    exact Nat.mod_lt a hM
  have hb : b % M < M := Nat.mod_lt b hM
  have hbM : b % M = (M - r) % M := by
    simpa [r] using h
  by_cases hr0 : r = 0
  · have hb0 : b % M = 0 := by
      have hb0' : (M - 0) % M = 0 := by simp
      simpa [hr0, hb0'] using hbM
    have hmod := Nat.add_mod a b M
    rw [hmod]
    have hres : (r + b % M) % M = 0 := by
      rw [hr0, hb0]
      simp
    simpa [r] using hres
  · have hMr : M - r < M := by omega
    have hb0 : b % M = M - r := by
      rw [hbM]
      exact Nat.mod_eq_of_lt hMr
    have hsum : r + b % M = M := by omega
    have hres : (r + b % M) % M = 0 := by
      rw [hsum]
      exact Nat.mod_self M
    have hmod := Nat.add_mod a b M
    rw [hmod]
    exact hres

/-- A zero residue modulo a multiple is zero modulo the divisor. -/
theorem mod_zero_of_dvd_mod (a M T : Nat) (hT : T ∣ M)
    (h : a % M = 0) : a % T = 0 := by
  exact Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans hT (Nat.dvd_iff_mod_eq_zero.mpr h))

/-- Low window of `q_V` is the numerator residue `q`:
`q_V ≡ q (mod 2^W)`. -/
theorem badResidue_mod_two_pow_eq_q (A W i q H r : Nat)
    (hW : 1 ≤ W) (_hq : q < 2 ^ W) (hrep : A + 5 ^ i * q = 2 ^ W * r) :
    badResidue A W i (W + H + 1) % 2 ^ W = q % 2 ^ W := by
  let T := 2 ^ W
  let E := W + H + 1
  let M := 2 ^ E
  let N := 5 * A + 3 * 2 ^ W
  let b := badResidue A W i E
  have hTpos : 0 < T := Nat.pow_pos (by decide)
  have hMpos : 0 < M := Nat.pow_pos (by decide)
  have hodd : (5 ^ (i + 1)) % 2 = 1 :=
    StringFlow.Lte.five_pow_odd (i + 1)
  have hTdvdM : T ∣ M := by
    dsimp [T, M]
    refine ⟨2 ^ (E - W), ?_⟩
    have hpow : 2 ^ W * 2 ^ (E - W) = 2 ^ E := by
      rw [← Nat.pow_add]
      congr 1
      omega
    exact hpow.symm
  have hspecM : (N + 5 ^ (i + 1) * b) % M = 0 :=
    mod_add_eq_zero_of_b_eq_neg N (5 ^ (i + 1) * b) M hMpos (by
      dsimp [N, b]
      exact badResidue_spec A W i E (by omega))
  have hbT : (N + 5 ^ (i + 1) * b) % T = 0 :=
    mod_zero_of_dvd_mod (N + 5 ^ (i + 1) * b) M T hTdvdM hspecM
  have hpow5 : 5 * 5 ^ i = 5 ^ (i + 1) := by
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have h5q : 5 * (5 ^ i * q) = 5 ^ (i + 1) * q := by
    rw [← Nat.mul_assoc]
    rw [hpow5]
  have hrel5 : 5 * A + 5 ^ (i + 1) * q = 2 ^ W * (5 * r) := by
    calc
      5 * A + 5 ^ (i + 1) * q = 5 * A + 5 * (5 ^ i * q) := by rw [h5q]
      _ = 5 * (A + 5 ^ i * q) := by rw [Nat.mul_add]
      _ = 5 * (2 ^ W * r) := by rw [hrep]
      _ = 2 ^ W * (5 * r) := by
          rw [← Nat.mul_assoc]
          rw [Nat.mul_comm 5 (2 ^ W)]
          rw [Nat.mul_assoc]
  have hzero5 : (5 * A + 5 ^ (i + 1) * q) % T = 0 := by
    rw [hrel5]
    rw [Nat.mul_mod_right]
  have hqT : (N + 5 ^ (i + 1) * q) % T = 0 := by
    have hsum : N + 5 ^ (i + 1) * q = (5 * A + 5 ^ (i + 1) * q) + 3 * 2 ^ W := by
      dsimp [N]
      omega
    rw [hsum, Nat.add_mod]
    rw [hzero5]
    have h3 : (3 * 2 ^ W) % T = 0 := by
      dsimp [T]
      rw [Nat.mul_comm]
      rw [Nat.mul_mod_right]
    rw [h3]
    simp
  have hneg_b : (5 ^ (i + 1) * b) % T = (T - N % T) % T :=
    mod_add_eq_zero_imp N (5 ^ (i + 1) * b) T hTpos (by simpa [N] using hbT)
  have hneg_q : (5 ^ (i + 1) * q) % T = (T - N % T) % T :=
    mod_add_eq_zero_imp N (5 ^ (i + 1) * q) T hTpos (by simpa [N] using hqT)
  let invT := StringFlow.Word.invOdd (5 ^ (i + 1)) (W - 1)
  have hinvT : ((5 ^ (i + 1)) * invT) % T = 1 := by
    dsimp [invT, T]
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 1)) hodd (W - 1)
    have hpow : 2 ^ ((W - 1) + 1) = 2 ^ W := by
      congr 1
      omega
    simpa [hpow] using h
  have hcancel := StringFlow.Word.mod_cancel_mul_left (5 ^ (i + 1))
    b q invT T hTpos hinvT (by rw [hneg_b, hneg_q])
  simpa [b, T] using hcancel

/-- Failure is equivalent to `q_i` being congruent to the bad residue
modulo `2^(W+H+1)`. -/
theorem failure_iff_q_mod_badResidue (A W i q H : Nat) :
    StringFlow.Automaton.failureCongruence A W i q H ↔
      q % 2 ^ (W + H + 1) = badResidue A W i (W + H + 1) := by
  let E := W + H + 1
  let M := 2 ^ E
  let N := 5 * A + 3 * 2 ^ W
  let inv := StringFlow.Word.invOdd (5 ^ (i + 1)) (E - 1)
  let b := badResidue A W i E
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hodd : (5 ^ (i + 1)) % 2 = 1 :=
    StringFlow.Lte.five_pow_odd (i + 1)
  have hinv : ((5 ^ (i + 1)) * inv) % M = 1 := by
    dsimp [inv, M]
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 1)) hodd (E - 1)
    have hpow : 2 ^ ((E - 1) + 1) = 2 ^ E := by
      congr 1
    simpa [hpow] using h
  have h1 : ((5 ^ (i + 1)) * b) % M = (M - N % M) % M := by
    dsimp [b, N]
    exact badResidue_spec A W i E (by omega)
  constructor
  · intro hf
    unfold StringFlow.Automaton.failureCongruence at hf
    rcases hf with ⟨z, hz⟩
    have hzero : (N + 5 ^ (i + 1) * q) % M = 0 := by
      rw [hz]
      change (z * 2 ^ (W + H + 1)) % M = 0
      rw [Nat.mul_comm z M]
      rw [Nat.mul_mod_right]
    have hq : (5 ^ (i + 1) * q) % M = (M - N % M) % M :=
      mod_add_eq_zero_imp N (5 ^ (i + 1) * q) M hM (by simpa [N, M] using hzero)
    have hcancel := StringFlow.Word.mod_cancel_mul_left (5 ^ (i + 1))
      q b inv M hM hinv
    have hbmod : b % M = b := Nat.mod_eq_of_lt (by
      dsimp [b]
      unfold badResidue
      exact Nat.mod_lt _ hM)
    have hqmod : q % M = b := by
      have hc := hcancel (by rw [hq, h1])
      rw [hbmod] at hc
      exact hc
    simpa [E, M, b] using hqmod
  · intro hqmod
    have hq : q % M = b := by simpa [E, M, b] using hqmod
    have hbmod : b % M = b := Nat.mod_eq_of_lt (by
      dsimp [b]
      unfold badResidue
      exact Nat.mod_lt _ hM)
    have hqb : (5 ^ (i + 1) * q) % M = (5 ^ (i + 1) * b) % M := by
      have hprod (x : Nat) : (5 ^ (i + 1) * x) % M =
          ((5 ^ (i + 1) % M) * (x % M)) % M := by
        rw [Nat.mul_mod]
      rw [hprod q, hprod b, hq, hbmod]
    have hneg : (5 ^ (i + 1) * q) % M = (M - N % M) % M := by
      rw [hqb, h1]
    have hzero : (N + 5 ^ (i + 1) * q) % M = 0 :=
      mod_add_eq_zero_of_b_eq_neg N (5 ^ (i + 1) * q) M hM (by
        simpa [N, M] using hneg)
    have hdvd : M ∣ N + 5 ^ (i + 1) * q := Nat.dvd_iff_mod_eq_zero.mpr (by
      simpa [N, M] using hzero)
    rcases hdvd with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hz]
    rw [Nat.mul_comm z M]

/-- If `q_V >= 2^W`, the failure congruence cannot hold. -/
theorem not_failure_of_badResidue_ge (A W i q H : Nat)
    (hq : q < 2 ^ W)
    (hge : 2 ^ W ≤ badResidue A W i (W + H + 1)) :
    ¬ StringFlow.Automaton.failureCongruence A W i q H := by
  intro hf
  let E := W + H + 1
  let M := 2 ^ E
  let b := badResidue A W i E
  have heq : q % M = b := by
    have h := (failure_iff_q_mod_badResidue A W i q H).mp hf
    simpa [E, M, b] using h
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hb : b < M := by
    dsimp [b]
    unfold badResidue
    exact Nat.mod_lt _ hM
  have hqM : q < M := by
    have hlt : 2 ^ W < 2 ^ (W + H + 1) := by
      exact Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega)
    exact Nat.lt_trans hq hlt
  have hqmod : q % M = q := Nat.mod_eq_of_lt hqM
  have hbmod : b % M = b := Nat.mod_eq_of_lt hb
  have hqeq : q = b := by
    rw [hqmod] at heq
    simpa [hbmod] using heq
  have hge' : 2 ^ W ≤ b := by simpa [E, b] using hge
  omega

/-- Full equivalence: `q_V >= 2^W` iff the failure congruence fails,
for any `q<2^W` coming from a delta=0 numerator representation. -/
theorem badResidue_ge_iff_not_failure (A W i q H : Nat)
    (hW : 1 ≤ W)
    (hq : q < 2 ^ W)
    (hrep : ∃ r, A + 5 ^ i * q = 2 ^ W * r) :
    (2 ^ W ≤ badResidue A W i (W + H + 1)) ↔
      ¬ StringFlow.Automaton.failureCongruence A W i q H := by
  constructor
  · exact not_failure_of_badResidue_ge A W i q H hq
  · intro hnot
    by_cases hge : 2 ^ W ≤ badResidue A W i (W + H + 1)
    · exact hge
    · let T := 2 ^ W
      let E := W + H + 1
      let M := 2 ^ E
      let N := 5 * A + 3 * 2 ^ W
      let b := badResidue A W i E
      have hTpos : 0 < T := Nat.pow_pos (by decide)
      have hMpos : 0 < M := Nat.pow_pos (by decide)
      have hodd : (5 ^ (i + 1)) % 2 = 1 :=
        StringFlow.Lte.five_pow_odd (i + 1)
      have hTdvdM : T ∣ M := by
        dsimp [T, M]
        refine ⟨2 ^ (E - W), ?_⟩
        have hpow : 2 ^ W * 2 ^ (E - W) = 2 ^ E := by
          rw [← Nat.pow_add]
          congr 1
          omega
        exact hpow.symm
      have hb_lt : b < T := by
        have hb_lt0 : badResidue A W i (W + H + 1) < 2 ^ W := by omega
        dsimp [b, T]
        exact hb_lt0
      have hspecM : (N + 5 ^ (i + 1) * b) % M = 0 :=
        mod_add_eq_zero_of_b_eq_neg N (5 ^ (i + 1) * b) M hMpos (by
          dsimp [N, b]
          exact badResidue_spec A W i E (by omega))
      have hbT : (N + 5 ^ (i + 1) * b) % T = 0 :=
        mod_zero_of_dvd_mod (N + 5 ^ (i + 1) * b) M T hTdvdM hspecM
      rcases hrep with ⟨r, hr⟩
      have hpow5 : 5 * 5 ^ i = 5 ^ (i + 1) := by
        rw [Nat.pow_succ]
        rw [Nat.mul_comm]
      have h5q : 5 * (5 ^ i * q) = 5 ^ (i + 1) * q := by
        rw [← Nat.mul_assoc]
        rw [hpow5]
      have hrel5 : 5 * A + 5 ^ (i + 1) * q = 2 ^ W * (5 * r) := by
        calc
          5 * A + 5 ^ (i + 1) * q = 5 * A + 5 * (5 ^ i * q) := by rw [h5q]
          _ = 5 * (A + 5 ^ i * q) := by rw [Nat.mul_add]
          _ = 5 * (2 ^ W * r) := by rw [hr]
          _ = 2 ^ W * (5 * r) := by
              rw [← Nat.mul_assoc]
              rw [Nat.mul_comm 5 (2 ^ W)]
              rw [Nat.mul_assoc]
      have hzero5 : (5 * A + 5 ^ (i + 1) * q) % T = 0 := by
        rw [hrel5]
        rw [Nat.mul_mod_right]
      have hqT : (N + 5 ^ (i + 1) * q) % T = 0 := by
        have hsum : N + 5 ^ (i + 1) * q =
            (5 * A + 5 ^ (i + 1) * q) + 3 * 2 ^ W := by
          dsimp [N]
          omega
        rw [hsum, Nat.add_mod]
        rw [hzero5]
        have h3 : (3 * 2 ^ W) % T = 0 := by
          dsimp [T]
          rw [Nat.mul_comm]
          rw [Nat.mul_mod_right]
        rw [h3]
        simp
      have hneg_b : (5 ^ (i + 1) * b) % T = (T - N % T) % T :=
        mod_add_eq_zero_imp N (5 ^ (i + 1) * b) T hTpos (by simpa [N] using hbT)
      have hneg_q : (5 ^ (i + 1) * q) % T = (T - N % T) % T :=
        mod_add_eq_zero_imp N (5 ^ (i + 1) * q) T hTpos (by simpa [N] using hqT)
      let invT := StringFlow.Word.invOdd (5 ^ (i + 1)) (W - 1)
      have hinvT : ((5 ^ (i + 1)) * invT) % T = 1 := by
        dsimp [invT, T]
        have h := StringFlow.Word.invOdd_spec (5 ^ (i + 1)) hodd (W - 1)
        have hpow : 2 ^ ((W - 1) + 1) = 2 ^ W := by
          congr 1
          omega
        simpa [hpow] using h
      have hcancel := StringFlow.Word.mod_cancel_mul_left (5 ^ (i + 1))
        b q invT T hTpos hinvT (by rw [hneg_b, hneg_q])
      have hqM : q < M := by
        dsimp [M]
        have hlt : 2 ^ W < 2 ^ (W + H + 1) := by
          exact Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega)
        exact Nat.lt_trans hq hlt
      have hbq : b = q := by
        have hbmod : b % T = b := Nat.mod_eq_of_lt hb_lt
        have hqmod : q % T = q := Nat.mod_eq_of_lt hq
        rw [hbmod, hqmod] at hcancel
        exact hcancel
      have hfail : StringFlow.Automaton.failureCongruence A W i q H :=
        (failure_iff_q_mod_badResidue A W i q H).mpr (by
          dsimp [E, M, b] at hbq
          rw [hbq]
          exact Nat.mod_eq_of_lt hqM)
      exact False.elim (hnot hfail)

/-- Symmetric form of the same equivalence: local-lemma failure is
exactly the low `q_V` window. -/
theorem localLemma_iff_qV_ge (A W i q H : Nat)
    (hW : 1 ≤ W)
    (hq : q < 2 ^ W)
    (hrep : ∃ r, A + 5 ^ i * q = 2 ^ W * r) :
    (¬ StringFlow.Automaton.failureCongruence A W i q H) ↔
      2 ^ W ≤ badResidue A W i (W + H + 1) :=
  (badResidue_ge_iff_not_failure A W i q H hW hq hrep).symm

/-- `B_i = 0` is exactly the failure congruence: the carry balance is
the high window of `q_V-q`. -/
theorem carryBalance_zero_iff_failure (A W i q H r : Nat)
    (hW : 1 ≤ W) (hq : q < 2 ^ W) (hrep : A + 5 ^ i * q = 2 ^ W * r) :
    carryBalance A W i q H = 0 ↔
      StringFlow.Automaton.failureCongruence A W i q H := by
  let T := 2 ^ W
  let E := W + H + 1
  let M := 2 ^ E
  let b := badResidue A W i E
  have hTpos : 0 < T := Nat.pow_pos (by decide)
  have hMpos : 0 < M := Nat.pow_pos (by decide)
  have hbM : b < M := by
    dsimp [b]
    unfold badResidue
    exact Nat.mod_lt _ hMpos
  have hbT : b % T = q % T :=
    badResidue_mod_two_pow_eq_q A W i q H r hW hq hrep
  constructor
  · intro hcb
    by_cases hfail : StringFlow.Automaton.failureCongruence A W i q H
    · exact hfail
    · have hge : T ≤ b := by
        have h := (localLemma_iff_qV_ge A W i q H hW hq ⟨r, hrep⟩).mp hfail
        simpa [T, b] using h
      have hqT : q % T = q := Nat.mod_eq_of_lt hq
      have hbdec0 : b = T * (b / T) + b % T := (Nat.div_add_mod b T).symm
      have hbdec : b = T * (b / T) + q := by
        rw [hbT, hqT] at hbdec0
        exact hbdec0
      let k := b / T
      have hbdec' : b = T * k + q := by
        simpa [k] using hbdec
      have hkge : 1 ≤ k := by
        dsimp [k]
        by_cases hk0 : b / T = 0
        · have hbq0 : b = q := by
            rw [hk0] at hbdec
            simpa using hbdec
          omega
        · have hdivpos : 0 < b / T := Nat.pos_of_ne_zero hk0
          omega
      have hbk_lt : k < 2 ^ (H + 1) := by
        have hmul_lt : T * k < M := by
          have hle : T * k ≤ b := by
            rw [hbdec']
            omega
          exact Nat.lt_of_le_of_lt hle hbM
        have hM' : M = T * 2 ^ (H + 1) := by
          dsimp [T, M, E]
          rw [← Nat.pow_add]
          congr 1
        rw [hM'] at hmul_lt
        exact (Nat.mul_lt_mul_left hTpos).1 hmul_lt
      have hd_eq : (b + M - q) % M = b - q := by
        have hqle : q ≤ b := by omega
        have hval : b + M - q = M + (b - q) := by omega
        rw [hval]
        rw [Nat.add_comm]
        rw [StringFlow.Word.add_mod_mul_one (b - q) M]
        exact Nat.mod_eq_of_lt (by omega)
      have hcb_val : carryBalance A W i q H = k % 2 ^ (H + 1) := by
        unfold carryBalance
        dsimp [E, M, b]
        have hqT' : q % 2 ^ W = q := hqT
        rw [hqT']
        have hd_eq' : ((b + M - q) % M) = b - q := by
          simpa [b, M] using hd_eq
        rw [hd_eq']
        have hbdec'' : b = 2 ^ W * k + q := by
          simpa [T, k] using hbdec'
        rw [hbdec'']
        have hsub : 2 ^ W * k + q - q = 2 ^ W * k := by omega
        rw [hsub]
        rw [Nat.mul_div_right k (Nat.pow_pos (by decide))]
      have hk0 : k = 0 := by
        have hkmod : k % 2 ^ (H + 1) = 0 := by
          rw [← hcb_val]
          exact hcb
        have hkmod' : k % 2 ^ (H + 1) = k := Nat.mod_eq_of_lt hbk_lt
        rw [hkmod'] at hkmod
        exact hkmod
      omega
  · intro hfail
    have hqM : q < M := by
      dsimp [M]
      have hlt : 2 ^ W < 2 ^ (W + H + 1) := by
        exact Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega)
      exact Nat.lt_trans hq hlt
    have hqmod : q % M = b := by
      have h := (failure_iff_q_mod_badResidue A W i q H).mp hfail
      simpa [E, M, b] using h
    have hbq : b = q := by
      have hqmod' : q % M = q := Nat.mod_eq_of_lt hqM
      rw [hqmod'] at hqmod
      exact hqmod.symm
    unfold carryBalance
    dsimp [E, M, b]
    have hqT : q % 2 ^ W = q := Nat.mod_eq_of_lt hq
    rw [hqT]
    have hbq' : badResidue A W i (W + H + 1) = q := by
      simpa [E, M, b] using hbq
    rw [hbq']
    have hval : q + M - q = M := by omega
    rw [hval, Nat.mod_self]
    simp

/-- `B_i != 0` is exactly the local-lemma side (no failure). -/
theorem carryBalance_ne_zero_iff_not_failure (A W i q H r : Nat)
    (hW : 1 ≤ W) (hq : q < 2 ^ W) (hrep : A + 5 ^ i * q = 2 ^ W * r) :
    carryBalance A W i q H ≠ 0 ↔
      ¬ StringFlow.Automaton.failureCongruence A W i q H := by
  constructor
  · intro hne hf
    exact hne ((carryBalance_zero_iff_failure A W i q H r hW hq hrep).mpr hf)
  · intro hn hz
    exact hn ((carryBalance_zero_iff_failure A W i q H r hW hq hrep).mp hz)

/-- Exact `t=2` recurrence for `q_V`: one `t=2` step shifts the bad
residue by `-2^(W+1)*5^{-(i+2)}` modulo the same window. -/
theorem badResidue_step_two (A W i H : Nat) (hH : 2 ≤ H) :
    badResidue (5 * A + 2 ^ W) (W + 2) (i + 1) (W + H + 1) =
      (badResidue A W i (W + H + 1) + 2 ^ (W + H + 1) -
        (2 ^ (W + 1) * StringFlow.Word.invOdd (5 ^ (i + 2)) (W + H)) %
          2 ^ (W + H + 1)) % 2 ^ (W + H + 1) := by
  let M := 2 ^ (W + H + 1)
  let E := W + H + 1
  let N := 5 * A + 3 * 2 ^ W
  let b := badResidue A W i E
  let A' := 5 * A + 2 ^ W
  let W' := W + 2
  let N' := 5 * A' + 3 * 2 ^ W'
  let p := StringFlow.Word.invOdd (5 ^ (i + 2)) (W + H)
  let t := (2 ^ (W + 1) * p) % M
  let rhs := (b + M - t) % M
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hE : 1 ≤ E := by omega
  have hbM : b < M := by
    dsimp [b]
    unfold badResidue
    exact Nat.mod_lt _ hM
  have htM : t < M := by
    dsimp [t]
    exact Nat.mod_lt _ hM
  have hrhsM : rhs < M := by
    dsimp [rhs]
    exact Nat.mod_lt _ hM
  have hbSpec : (5 ^ (i + 1) * b) % M = (M - N % M) % M := by
    dsimp [N, b]
    exact badResidue_spec A W i E hE
  have hpSpec : (5 ^ (i + 2) * p) % M = 1 := by
    dsimp [p, M]
    have hodd : (5 ^ (i + 2)) % 2 = 1 :=
      StringFlow.Lte.five_pow_odd (i + 2)
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 2)) hodd (W + H)
    have hpow : 2 ^ ((W + H) + 1) = 2 ^ (W + H + 1) := by omega
    simpa [hpow] using h
  have hsum0 : (N + 5 ^ (i + 1) * b) % M = 0 :=
    mod_add_eq_zero_of_b_eq_neg N (5 ^ (i + 1) * b) M hM (by
      simpa [N] using hbSpec)
  have h5pow : 5 * 5 ^ (i + 1) = 5 ^ (i + 2) := by
    have hpow : 5 ^ (i + 2) = 5 ^ (i + 1) * 5 := by
      rw [show i + 2 = Nat.succ (i + 1) by omega]
      rw [Nat.pow_succ]
    rw [hpow, Nat.mul_comm]
  have hfac : 5 * (N + 5 ^ (i + 1) * b) = 5 * N + 5 ^ (i + 2) * b := by
    calc
      5 * (N + 5 ^ (i + 1) * b)
          = 5 * N + 5 * (5 ^ (i + 1) * b) := by rw [Nat.mul_add]
      _ = 5 * N + (5 * 5 ^ (i + 1)) * b := by rw [Nat.mul_assoc]
      _ = 5 * N + 5 ^ (i + 2) * b := by rw [h5pow]
  have hsum0' : (5 * N + 5 ^ (i + 2) * b) % M = 0 := by
    have hmul0 : (5 * (N + 5 ^ (i + 1) * b)) % M = 0 := by
      rw [Nat.mul_mod]
      rw [hsum0]
      simp
    rw [hfac] at hmul0
    exact hmul0
  have hbSpec5 : (5 ^ (i + 2) * b) % M = (M - (5 * N) % M) % M :=
    mod_add_eq_zero_imp (5 * N) (5 ^ (i + 2) * b) M hM hsum0'
  have htSpec : (5 ^ (i + 2) * t) % M = 2 ^ (W + 1) := by
    dsimp [t]
    rw [mul_mod_mul_mod (5 ^ (i + 2)) (2 ^ (W + 1) * p) M]
    have hswap := StringFlow.Word.mul_left_swap (5 ^ (i + 2)) (2 ^ (W + 1)) p
    rw [hswap]
    rw [Nat.mul_mod, hpSpec]
    simp
    have hlt : 2 ^ (W + 1) < 2 ^ (W + H + 1) := by
      exact Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega)
    exact Nat.mod_eq_of_lt hlt
  have hsumRhs := mul_wrapped_sub_add (5 ^ (i + 2)) b t M hM hbM htM
  have hsubRhs := mod_sub_of_add_eq (5 ^ (i + 2) * rhs)
    (5 ^ (i + 2) * t) (5 ^ (i + 2) * b) M hM hsumRhs
  have h2 : 2 ^ (W + 1) = 2 * 2 ^ W := by
    rw [show W + 1 = Nat.succ W by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have h22 : 2 ^ (W + 2) = 4 * 2 ^ W := by
    have hpow := Nat.pow_add 2 W 2
    have h4 : 2 ^ 2 = 4 := by native_decide
    rw [hpow, h4]
    rw [Nat.mul_comm]
  have hN' : 5 * N + 2 ^ (W + 1) = N' := by
    dsimp [N, N', A', W']
    rw [h2, h22]
    omega
  have hrhsSpec : (5 ^ (i + 2) * rhs) % M = (M - N' % M) % M := by
    rw [hbSpec5, htSpec] at hsubRhs
    have hneg := mod_sub_neg_add (5 * N) (2 ^ (W + 1)) M hM
    have hyt : (2 ^ (W + 1)) % M = 2 ^ (W + 1) := by
      have hlt : 2 ^ (W + 1) < 2 ^ (W + H + 1) := by
        exact Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega)
      exact Nat.mod_eq_of_lt hlt
    rw [hyt] at hneg
    rw [hneg] at hsubRhs
    rw [hN'] at hsubRhs
    exact hsubRhs
  have hx : rhs < 2 ^ E := by
    dsimp [E]
    exact hrhsM
  have hfinal : rhs = badResidue A' W' (i + 1) E :=
    badResidue_eq_of_spec A' W' (i + 1) E rhs hE hx (by
      simpa [A', W', N'] using hrhsSpec)
  dsimp [E, M, N, b, A', W', N', p, t, rhs] at hfinal
  exact hfinal.symm

/-- Exact `t=1` recurrence for `q_V`, with the modulus lifted by one
bit: `q_V' = q_V + 2^(W+2)*5^{-(i+2)} (mod 2^(W+H+2))`. -/
theorem badResidue_step_one (A W i H : Nat) (hH : 2 ≤ H) :
    badResidue (5 * A + 2 ^ W) (W + 1) (i + 1) (W + H + 2) =
      (badResidue A W i (W + H + 2) + 2 ^ (W + H + 2) -
        ((2 ^ (W + H + 2) -
          (2 ^ (W + 2) * StringFlow.Word.invOdd (5 ^ (i + 2)) (W + H + 1)) %
            2 ^ (W + H + 2)) % 2 ^ (W + H + 2))) %
        2 ^ (W + H + 2) := by
  let M := 2 ^ (W + H + 2)
  let E := W + H + 2
  let N := 5 * A + 3 * 2 ^ W
  let b := badResidue A W i E
  let A' := 5 * A + 2 ^ W
  let W' := W + 1
  let N' := 5 * A' + 3 * 2 ^ W'
  let p := StringFlow.Word.invOdd (5 ^ (i + 2)) (W + H + 1)
  let y := (2 ^ (W + 2) * p) % M
  let t := (M - y) % M
  let rhs := (b + M - t) % M
  have hM : 0 < M := Nat.pow_pos (by decide)
  have hE : 1 ≤ E := by omega
  have hbM : b < M := by
    dsimp [b]
    unfold badResidue
    exact Nat.mod_lt _ hM
  have htM : t < M := by
    dsimp [t]
    exact Nat.mod_lt _ hM
  have hrhsM : rhs < M := by
    dsimp [rhs]
    exact Nat.mod_lt _ hM
  have hbSpec : (5 ^ (i + 1) * b) % M = (M - N % M) % M := by
    dsimp [N, b]
    exact badResidue_spec A W i E hE
  have hpSpec : (5 ^ (i + 2) * p) % M = 1 := by
    dsimp [p, M]
    have hodd : (5 ^ (i + 2)) % 2 = 1 :=
      StringFlow.Lte.five_pow_odd (i + 2)
    have h := StringFlow.Word.invOdd_spec (5 ^ (i + 2)) hodd (W + H + 1)
    have hpow : 2 ^ ((W + H + 1) + 1) = 2 ^ (W + H + 2) := by rfl
    simpa [hpow] using h
  have hsum0 : (N + 5 ^ (i + 1) * b) % M = 0 :=
    mod_add_eq_zero_of_b_eq_neg N (5 ^ (i + 1) * b) M hM (by
      simpa [N] using hbSpec)
  have h5pow : 5 * 5 ^ (i + 1) = 5 ^ (i + 2) := by
    have hpow : 5 ^ (i + 2) = 5 ^ (i + 1) * 5 := by
      rw [show i + 2 = Nat.succ (i + 1) by omega]
      rw [Nat.pow_succ]
    rw [hpow, Nat.mul_comm]
  have hfac : 5 * (N + 5 ^ (i + 1) * b) = 5 * N + 5 ^ (i + 2) * b := by
    calc
      5 * (N + 5 ^ (i + 1) * b)
          = 5 * N + 5 * (5 ^ (i + 1) * b) := by rw [Nat.mul_add]
      _ = 5 * N + (5 * 5 ^ (i + 1)) * b := by rw [Nat.mul_assoc]
      _ = 5 * N + 5 ^ (i + 2) * b := by rw [h5pow]
  have hsum0' : (5 * N + 5 ^ (i + 2) * b) % M = 0 := by
    have hmul0 : (5 * (N + 5 ^ (i + 1) * b)) % M = 0 := by
      rw [Nat.mul_mod]
      rw [hsum0]
      simp
    rw [hfac] at hmul0
    exact hmul0
  have hbSpec5 : (5 ^ (i + 2) * b) % M = (M - (5 * N) % M) % M :=
    mod_add_eq_zero_imp (5 * N) (5 ^ (i + 2) * b) M hM hsum0'
  have htSpec : (5 ^ (i + 2) * t) % M = (M - 2 ^ (W + 2)) % M := by
    dsimp [t]
    have h := mul_mod_neg (5 ^ (i + 2)) (2 ^ (W + 2) * p) M hM
    have hy : (5 ^ (i + 2) * (2 ^ (W + 2) * p)) % M = 2 ^ (W + 2) := by
      have hswap := StringFlow.Word.mul_left_swap (5 ^ (i + 2)) (2 ^ (W + 2)) p
      rw [hswap]
      rw [Nat.mul_mod, hpSpec]
      simp
      have hExp : W + 2 < W + H + 2 := by omega
      have hlt : 2 ^ (W + 2) < 2 ^ (W + H + 2) := by
        exact Nat.pow_lt_pow_right (show 1 < 2 by decide) hExp
      exact Nat.mod_eq_of_lt hlt
    rw [h, hy]
  have hsumRhs := mul_wrapped_sub_add (5 ^ (i + 2)) b t M hM hbM htM
  have hsubRhs := mod_sub_of_add_eq (5 ^ (i + 2) * rhs)
    (5 ^ (i + 2) * t) (5 ^ (i + 2) * b) M hM hsumRhs
  have h2 : 2 ^ (W + 1) = 2 * 2 ^ W := by
    rw [show W + 1 = Nat.succ W by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  have h22 : 2 ^ (W + 2) = 4 * 2 ^ W := by
    have hpow := Nat.pow_add 2 W 2
    have h4 : 2 ^ 2 = 4 := by native_decide
    rw [hpow, h4]
    rw [Nat.mul_comm]
  have hN' : (5 * N + (M - 2 ^ (W + 2))) % M = N' % M := by
    have hle : 2 ^ (W + 2) ≤ 5 * N := by
      dsimp [N]
      rw [h22]
      have h1 : 4 * 2 ^ W ≤ 15 * 2 ^ W :=
        Nat.mul_le_mul_right (2 ^ W) (by omega)
      have h2' : 15 * 2 ^ W ≤ 5 * (5 * A + 3 * 2 ^ W) := by omega
      exact Nat.le_trans h1 h2'
    have hle' : 4 * 2 ^ W ≤ 5 * N := by
      rw [h22] at hle
      exact hle
    have hzM : 2 ^ (W + 2) ≤ M := by
      dsimp [M]
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (by omega)
    have hsum : 5 * N + (M - 2 ^ (W + 2)) =
        (5 * N - 2 ^ (W + 2)) + M := by
      dsimp [M]
      rw [h22]
      omega
    rw [hsum, Nat.add_mod]
    have hMmod : M % M = 0 := Nat.mod_self M
    rw [hMmod, Nat.add_zero]
    have hN'eq : 5 * N - 2 ^ (W + 2) = N' := by
      dsimp [N, N', A', W']
      rw [h22, h2]
      omega
    rw [hN'eq]
    exact Nat.mod_eq_of_lt (Nat.mod_lt N' hM)
  have hrhsSpec : (5 ^ (i + 2) * rhs) % M = (M - N' % M) % M := by
    rw [hbSpec5, htSpec] at hsubRhs
    have hneg := mod_sub_neg_add (5 * N) (M - 2 ^ (W + 2)) M hM
    rw [hneg] at hsubRhs
    rw [hN'] at hsubRhs
    exact hsubRhs
  have hx : rhs < 2 ^ E := by
    dsimp [E]
    exact hrhsM
  have hfinal : rhs = badResidue A' W' (i + 1) E :=
    badResidue_eq_of_spec A' W' (i + 1) E rhs hE hx (by
      simpa [A', W', N'] using hrhsSpec)
  dsimp [E, M, N, b, A', W', N', p, y, t, rhs] at hfinal
  exact hfinal.symm

/-- Sufficient window lower bound: if the window height is too large
for the minimal representative, failure is impossible and hence
`q_V >= 2^W`. -/
theorem qV_ge_of_height_large (A W i q H r _u : Nat)
    (hW : 1 ≤ W) (hq : q < 2 ^ W)
    (hrep : A + 5 ^ i * q = 2 ^ W * r)
    (hmin : r < 5 ^ i)
    (hbig : 5 ^ (i + 1) + 3 < 2 ^ (H + 1)) :
    2 ^ W ≤ badResidue A W i (W + H + 1) := by
  have hnot : ¬ StringFlow.Automaton.failureCongruence A W i q H := by
    intro hf
    have hb := StringFlow.Automaton.failureCongruence_height_bound
      A W i q H r hrep hmin hf
    omega
  exact (localLemma_iff_qV_ge A W i q H hW hq ⟨r, hrep⟩).mp hnot

/-- Exact reduction: the q-window lower bound is the negation of
`2^(H+1) | 5r+3`. -/
theorem qV_ge_iff_not_two_pow_dvd (A W i q H r : Nat)
    (hW : 1 ≤ W) (hq : q < 2 ^ W)
    (hrep : A + 5 ^ i * q = 2 ^ W * r) :
    (2 ^ W ≤ badResidue A W i (W + H + 1)) ↔
      ¬ (2 ^ (H + 1) ∣ 5 * r + 3) := by
  have h1 := localLemma_iff_qV_ge A W i q H hW hq ⟨r, hrep⟩
  have hfail_iff : StringFlow.Automaton.failureCongruence A W i q H ↔
      2 ^ (H + 1) ∣ 5 * r + 3 := by
    have hM := StringFlow.Automaton.five_r_plus_three_affine A W i q r hrep
    have hpow : 2 ^ (W + H + 1) = 2 ^ W * 2 ^ (H + 1) := by
      rw [← Nat.pow_add]
      congr 1
    constructor
    · intro hf
      rcases hf with ⟨z, hz⟩
      have hz' : 2 ^ W * (5 * r + 3) = 2 ^ W * (z * 2 ^ (H + 1)) := by
        rw [hM] at hz
        rw [hpow] at hz
        rw [hz]
        exact StringFlow.Word.mul_left_swap z (2 ^ W) (2 ^ (H + 1))
      have hz'' : 2 ^ W * (5 * r + 3) = 2 ^ W * (2 ^ (H + 1) * z) := by
        rw [hz']
        rw [Nat.mul_comm (2 ^ (H + 1)) z]
      exact ⟨z, Nat.mul_left_cancel (Nat.pow_pos (show 0 < 2 by decide)) hz''⟩
    · intro hdvd
      rcases hdvd with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [hM, hz, hpow]
      rw [Nat.mul_comm (2 ^ (H + 1)) z]
      exact (StringFlow.Word.mul_left_swap z (2 ^ W) (2 ^ (H + 1))).symm
  constructor
  · intro hge hdvd
    exact (h1.mpr hge) (hfail_iff.mpr hdvd)
  · intro hnot
    exact h1.mp (by
      intro hf
      exact hnot (hfail_iff.mp hf))

/-- A delta=0 window is reachable from the start of the accelerated
orbit: a valid `{1,2}` word of length `i` and weight `W` ends at `r`,
with a block split whose prefix widths are `Wp` and `Wj`. -/
def ReachableWindow (A W i q r Wp Wj : Nat) : Prop :=
  ∃ (w : List Nat) (j : Nat),
    1 ≤ j ∧ j ≤ i ∧
    StringFlow.Word.wordOK w ∧
    StringFlow.Word.wordValid w q ∧
    w.length = i ∧
    StringFlow.Word.wordA w = A ∧
    StringFlow.wordWeight w = W ∧
    StringFlow.wordWeight (w.take j) = Wj ∧
    StringFlow.wordWeight (w.take (j - 1)) = Wp ∧
    StringFlow.Word.wordOrbit w q = r

/-- The q-window statement is exactly the valuation statement
`¬ 2^(H+1) | 5r+3` under the delta=0 hypotheses. -/
theorem qVWindowStatement_iff_valuation :
    (∀ (A W i q H r u Wp Wj : Nat),
      Wp < Wj → Wj ≤ W → 2 ^ Wp ≤ q → q < 2 ^ Wj →
    H = 2 * i + 13 - 2 * (W - Wp) → 3 ≤ H →
    A + 5 ^ i * q = 2 ^ W * r → A < 5 ^ i → r < 5 ^ i →
    r + 1 = 2 * u → u % 2 = 1 → ReachableWindow A W i q r Wp Wj →
    2 ^ W ≤ badResidue A W i (W + H + 1)) ↔
      ∀ (A W i q H r u Wp Wj : Nat),
        Wp < Wj →
        Wj ≤ W →
        2 ^ Wp ≤ q →
        q < 2 ^ Wj →
        H = 2 * i + 13 - 2 * (W - Wp) →
        3 ≤ H →
        A + 5 ^ i * q = 2 ^ W * r →
        A < 5 ^ i →
        r < 5 ^ i →
        r + 1 = 2 * u →
        u % 2 = 1 →
        ReachableWindow A W i q r Wp Wj →
        ¬ 2 ^ (H + 1) ∣ 5 * r + 3 := by
  constructor
  · intro hll
    intro A W i q H r u Wp Wj
      hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    have hq : q < 2 ^ W :=
      Nat.lt_of_lt_of_le hqmax (Nat.pow_le_pow_right (show 0 < 2 by decide) hWj)
    have hW : 1 ≤ W := by
      by_cases hW0 : W = 0
      · have : Wj ≤ 0 := by omega
        omega
      · omega
    have hge := hll A W i q H r u Wp Wj
      hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    exact (qV_ge_iff_not_two_pow_dvd A W i q H r hW hq hrep).mp hge
  · intro hval
    intro A W i q H r u Wp Wj
      hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    have hq : q < 2 ^ W :=
      Nat.lt_of_lt_of_le hqmax (Nat.pow_le_pow_right (show 0 < 2 by decide) hWj)
    have hW : 1 ≤ W := by
      by_cases hW0 : W = 0
      · have : Wj ≤ 0 := by omega
        omega
      · omega
    have hnot := hval A W i q H r u Wp Wj
      hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    exact (qV_ge_iff_not_two_pow_dvd A W i q H r hW hq hrep).mpr hnot

/-- The open q-window statement: from the delta=0 hypotheses,
`q_V >= 2^W_i`. -/
def qVWindowStatement : Prop :=
  ∀ (A W i q H r u Wp Wj : Nat),
    Wp < Wj →
    Wj ≤ W →
    2 ^ Wp ≤ q →
    q < 2 ^ Wj →
    H = 2 * i + 13 - 2 * (W - Wp) →
    3 ≤ H →
    A + 5 ^ i * q = 2 ^ W * r →
    A < 5 ^ i →
    r < 5 ^ i →
    r + 1 = 2 * u →
    u % 2 = 1 →
    ReachableWindow A W i q r Wp Wj →
    2 ^ W ≤ badResidue A W i (W + H + 1)

/-- Large-height part of the q-window statement: closed by
`qV_ge_of_height_large`. -/
def qVWindowLargeHeight : Prop :=
  ∀ (A W i q H r u Wp Wj : Nat),
    Wp < Wj →
    Wj ≤ W →
    2 ^ Wp ≤ q →
    q < 2 ^ Wj →
    H = 2 * i + 13 - 2 * (W - Wp) →
    3 ≤ H →
    A + 5 ^ i * q = 2 ^ W * r →
    A < 5 ^ i →
    r < 5 ^ i →
    r + 1 = 2 * u →
    u % 2 = 1 →
    ReachableWindow A W i q r Wp Wj →
    5 ^ (i + 1) + 3 < 2 ^ (H + 1) →
    2 ^ W ≤ badResidue A W i (W + H + 1)

/-- The large-height part is closed by the existing size bound. -/
theorem qVWindowLargeHeight_holds : qVWindowLargeHeight := by
  intro A W i q H r u Wp Wj
    hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach hbig
  have hq : q < 2 ^ W :=
    Nat.lt_of_lt_of_le hqmax (Nat.pow_le_pow_right (show 0 < 2 by decide) hWj)
  have hW : 1 ≤ W := by
    by_cases hW0 : W = 0
    · have : Wj ≤ 0 := by omega
      omega
    · omega
  exact qV_ge_of_height_large A W i q H r u hW hq hrep hmin hbig

/-- Remaining small-height part of the q-window statement. -/
def qVWindowRemaining : Prop :=
  ∀ (A W i q H r u Wp Wj : Nat),
    Wp < Wj →
    Wj ≤ W →
    2 ^ Wp ≤ q →
    q < 2 ^ Wj →
    H = 2 * i + 13 - 2 * (W - Wp) →
    3 ≤ H →
    A + 5 ^ i * q = 2 ^ W * r →
    A < 5 ^ i →
    r < 5 ^ i →
    r + 1 = 2 * u →
    u % 2 = 1 →
    ReachableWindow A W i q r Wp Wj →
    ¬ (5 ^ (i + 1) + 3 < 2 ^ (H + 1)) →
    2 ^ W ≤ badResidue A W i (W + H + 1)

/-- The full q-window statement is exactly the large-height part plus
the remaining small-height part. -/
theorem qVWindowStatement_iff_large_and_remaining :
    qVWindowStatement ↔ (qVWindowLargeHeight ∧ qVWindowRemaining) := by
  constructor
  · intro hll
    constructor
    · intro A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach hbig
      exact hll A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    · intro A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach hsmall
      exact hll A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
  · intro hparts
    intro A W i q H r u Wp Wj
      hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach
    by_cases hbig : 5 ^ (i + 1) + 3 < 2 ^ (H + 1)
    · exact hparts.1 A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach hbig
    · exact hparts.2 A W i q H r u Wp Wj
        hWp hWj hqmin hqmax hH hcap hrep hAbound hmin hu huodd hreach hbig

/-- In the remaining small-height case, the window height is bounded by
the size of the minimal representative: `2^H <= 5^(i+1)`. -/
theorem remaining_height_bound (i H : Nat)
    (hrem : ¬ (5 ^ (i + 1) + 3 < 2 ^ (H + 1))) :
    2 ^ H ≤ 5 ^ (i + 1) := by
  have hle : 2 ^ (H + 1) ≤ 5 ^ (i + 1) + 3 := by omega
  have h5pos : 3 ≤ 5 ^ (i + 1) := by
    have hpow : 1 ≤ i + 1 := by omega
    have h5 : 5 ≤ 5 ^ (i + 1) :=
      Nat.pow_le_pow_right (show 0 < 5 by decide) hpow
    omega
  have hdouble : 5 ^ (i + 1) + 3 ≤ 2 * 5 ^ (i + 1) := by omega
  have hle2 : 2 ^ (H + 1) ≤ 2 * 5 ^ (i + 1) := Nat.le_trans hle hdouble
  have hpow : 2 ^ (H + 1) = 2 * 2 ^ H := by
    rw [show H + 1 = Nat.succ H by omega]
    rw [Nat.pow_succ]
    rw [Nat.mul_comm]
  rw [hpow] at hle2
  exact Nat.le_of_mul_le_mul_left hle2 (by decide)

/-- The same height bound expressed through `H = 2i+13-2D`. -/
theorem remaining_D_height_bound (i D H : Nat)
    (hH : H = 2 * i + 13 - 2 * D)
    (hrem : ¬ (5 ^ (i + 1) + 3 < 2 ^ (H + 1))) :
    2 ^ (2 * i + 13 - 2 * D) ≤ 5 ^ (i + 1) := by
  rw [← hH]
  exact remaining_height_bound i H hrem

/-- The A-bound-only window statement: the exact form that adds
`A < 5^i` but omits the delta=0 reachability premise. This form is
false. -/
def qVWindowStatementABoundOnly : Prop :=
  ∀ (A W i q H r u Wp Wj : Nat),
    Wp < Wj →
    Wj ≤ W →
    2 ^ Wp ≤ q →
    q < 2 ^ Wj →
    H = 2 * i + 13 - 2 * (W - Wp) →
    3 ≤ H →
    A < 5 ^ i →
    A + 5 ^ i * q = 2 ^ W * r →
    r < 5 ^ i →
    r + 1 = 2 * u →
    u % 2 = 1 →
    2 ^ W ≤ badResidue A W i (W + H + 1)

/-- Counterexample to the A-bound-only form:
`(A,W,i,q,H,r,u,Wp,Wj) = (2966,10,5,2,3,9,5,0,2)` satisfies all
hypotheses, including `A < 5^5`, but `q_V = 2 < 2^10`. -/
theorem qVWindowStatementABoundOnly_counterexample :
    ¬ qVWindowStatementABoundOnly := by
  intro h
  have hc := h 2966 10 5 2 3 9 5 0 2
    (by decide) (by decide) (by decide) (by decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hb : badResidue 2966 10 5 14 = 2 := by native_decide
  change 2 ^ 10 ≤ badResidue 2966 10 5 14 at hc
  rw [hb] at hc
  have hbad : Not (2 ^ 10 ≤ 2) := by native_decide
  exact hbad hc

end StringFlow.QWindow
