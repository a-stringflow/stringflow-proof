import Td1Interp
import Td0Real
import Td0CertBridge
import ScratchOrbit
import Td0Phase2

/-!
# TD-0/TD-1 final window contradiction

The two branch arguments in `ph_qb_gc_chain.md` section 52 close with
the same final step: if `M0 = N1`, the chain numerator `A_chain`
equals the interval numerator `A_req` (`2*8^Q*m - 5^Q*M0` for the A
family, `4*8^Q*m - 5^Q*M0` for the B family).  Therefore the
interpolation bounds `A0 < A_chain < A_max` contradict the
interval-exclusion certificates.

This module states that final contradiction.  The interval-exclusion
certificate comes from the stage-one tables; the explicit C3 chain
closed form comes from GC-4, and the interpolation bounds
`A0 <= A_chain <= A_max` are now derived here from `Td1Interp`.
-/

namespace StringFlow.TD0

/-- `2 * 8^n = 2^(3n+1)`. -/
theorem two_mul_eight_pow_eq (n : Nat) : 2 * 8 ^ n = 2 ^ (3 * n + 1) := by
  have h8 : 8 ^ n = 2 ^ (3 * n) := by
    rw [show 8 = 2 ^ 3 by decide, ← Nat.pow_mul]
  calc
    2 * 8 ^ n = 2 * 2 ^ (3 * n) := by rw [h8]
    _ = 2 ^ (3 * n) * 2 := by rw [Nat.mul_comm]
    _ = 2 ^ (3 * n + 1) := by rw [Nat.pow_succ]

/-- `4 * 8^n = 2^(3n+2)`. -/
theorem four_mul_eight_pow_eq (n : Nat) : 4 * 8 ^ n = 2 ^ (3 * n + 2) := by
  have h8 : 8 ^ n = 2 ^ (3 * n) := by
    rw [show 8 = 2 ^ 3 by decide, ← Nat.pow_mul]
  calc
    4 * 8 ^ n = 4 * 2 ^ (3 * n) := by rw [h8]
    _ = 2 ^ (3 * n) * 4 := by rw [Nat.mul_comm]
    _ = 2 ^ (3 * n) * 2 ^ 2 := by rw [show 4 = 2 ^ 2 by decide]
    _ = 2 ^ (3 * n + 2) := by rw [← Nat.pow_add]

/-- From the A-family total-weight identity, `sum = 3*len + 1`. -/
theorem sum_eq_of_two_mul_eight (ts : List Nat)
    (hT : 2 ^ ts.sum = 2 * 8 ^ ts.length) :
    ts.sum = 3 * ts.length + 1 := by
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by
    change 2 ^ ts.sum = 2 ^ (3 * ts.length + 1)
    rw [hT, two_mul_eight_pow_eq ts.length])

/-- From the B-family total-weight identity, `sum = 3*len + 2`. -/
theorem sum_eq_of_four_mul_eight (ts : List Nat)
    (hT : 4 * 8 ^ ts.length = 2 ^ ts.sum) :
    ts.sum = 3 * ts.length + 2 := by
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by
    change 2 ^ ts.sum = 2 ^ (3 * ts.length + 2)
    rw [← hT, four_mul_eight_pow_eq ts.length])

/-- From the total-weight identity `(L+U)+sum = tCeil(L+Q)` and the
chain-weight identity, the exact `tCeil` form follows. -/
theorem tCeil_eq_of_chain_sum (b Q L U : Nat) (ts : List Nat)
    (hb : b = 1 ∨ b = 2)
    (hQlen : ts.length = Q)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hTsum : (L + U) + ts.sum = StringFlow.tCeil (L + Q)) :
    StringFlow.tCeil (L + Q) = L + 3 * Q + b + U := by
  rcases hb with rfl | rfl
  · have hsum := sum_eq_of_two_mul_eight ts (by simpa using hTchain)
    rw [hQlen] at hsum
    omega
  · have hsum := sum_eq_of_four_mul_eight ts (by simpa using hTchain)
    rw [hQlen] at hsum
    omega

/-- In the A family, `A_req = A_chain` when `M0 = N1` and the chain
has `2^T_chain = 2 * 8^Q`. -/
theorem td1A_chain_areq_eq (Q m M0 Achain : Nat)
    (hchain : 2 * 8 ^ Q * m = 5 ^ Q * M0 + Achain) :
    StringFlow.TD1.areqA Q m M0 = Achain := by
  unfold StringFlow.TD1.areqA
  omega

/-- A-family final contradiction: chain interpolation plus interval
exclusion cannot both hold. -/
theorem td1A_chain_window_contradicts (Q m M0 Achain : Nat)
    (hchain : 2 * 8 ^ Q * m = 5 ^ Q * M0 + Achain)
    (hA0le : StringFlow.TD1.a0 Q ≤ Achain)
    (hAmaxle : Achain ≤ StringFlow.TD1.amaxA Q)
    (hExcl : StringFlow.TD1.areqA Q m M0 > StringFlow.TD1.amaxA Q ∨
             StringFlow.TD1.areqA Q m M0 < StringFlow.TD1.a0 Q) :
    False := by
  have hareq : StringFlow.TD1.areqA Q m M0 = Achain :=
    td1A_chain_areq_eq Q m M0 Achain hchain
  rcases hExcl with hgt | hlt
  · have hle : StringFlow.TD1.areqA Q m M0 ≤ StringFlow.TD1.amaxA Q := by
      omega
    omega
  · have hge : StringFlow.TD1.a0 Q ≤ StringFlow.TD1.areqA Q m M0 := by
      omega
    omega

/-- In the B family, `A_req = A_chain` when `M0 = N1` and the chain
has `2^T_chain = 4 * 8^Q`. -/
theorem td1B_chain_areq_eq (Q m M0 Achain : Nat)
    (hchain : 4 * 8 ^ Q * m = 5 ^ Q * M0 + Achain) :
    StringFlow.TD1.areqB Q m M0 = Achain := by
  unfold StringFlow.TD1.areqB
  omega

/-- B-family final contradiction: chain interpolation plus interval
exclusion cannot both hold. -/
theorem td1B_chain_window_contradicts (Q m M0 Achain : Nat)
    (hchain : 4 * 8 ^ Q * m = 5 ^ Q * M0 + Achain)
    (hA0le : StringFlow.TD1.a0 Q ≤ Achain)
    (hAmaxle : Achain ≤ StringFlow.TD1.amaxB Q)
    (hExcl : StringFlow.TD1.areqB Q m M0 > StringFlow.TD1.amaxB Q ∨
             StringFlow.TD1.areqB Q m M0 < StringFlow.TD1.a0 Q) :
    False := by
  have hareq : StringFlow.TD1.areqB Q m M0 = Achain :=
    td1B_chain_areq_eq Q m M0 Achain hchain
  rcases hExcl with hgt | hlt
  · have hle : StringFlow.TD1.areqB Q m M0 ≤ StringFlow.TD1.amaxB Q := by
      omega
    omega
  · have hge : StringFlow.TD1.a0 Q ≤ StringFlow.TD1.areqB Q m M0 := by
      omega
    omega

/-- A-family chain closed form specialized to `N_{Q+1} = m` and
`2^T_chain = 2 * 8^Q`. -/
theorem td1A_chain_closed_form_of_eq (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 2 ^ ts.sum = 2 * 8 ^ ts.length) :
    2 * 8 ^ ts.length * m =
      5 ^ ts.length * StringFlow.GC.chainFirst ns + StringFlow.GC.chainA ts := by
  have h := StringFlow.GC.c3_chain_closed_form ns ts hc3
  rw [hlast] at h
  rw [hT] at h
  exact h

/-- A-family TD-1 closure assembled from the C3 closed form, the
chain interpolation bounds, and the interval exclusion. -/
theorem td1A_closed (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 2 ^ ts.sum = 2 * 8 ^ ts.length)
    (hA0le : StringFlow.TD1.a0 ts.length ≤ StringFlow.GC.chainA ts)
    (hAmaxle : StringFlow.GC.chainA ts ≤ StringFlow.TD1.amaxA ts.length)
    (hExcl : StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) >
               StringFlow.TD1.amaxA ts.length ∨
             StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) <
               StringFlow.TD1.a0 ts.length) :
    False := by
  exact td1A_chain_window_contradicts ts.length m (StringFlow.GC.chainFirst ns)
    (StringFlow.GC.chainA ts)
    (td1A_chain_closed_form_of_eq ns ts m hc3 hlast hT)
    hA0le hAmaxle hExcl

/-- A-family TD-1 closure with the interpolation bounds derived from
the C3 chain data: `A0 <= A_chain <= A_max` now follows from the
weight conditions `3 <= t`, `t_1 = 3`, and the budget `b = 1`. -/
theorem td1A_closed_of_chain (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 2 ^ ts.sum = 2 * 8 ^ ts.length)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hExcl : StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) >
               StringFlow.TD1.amaxA ts.length ∨
             StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) <
               StringFlow.TD1.a0 ts.length) :
    False := by
  have hsum_eq : ts.sum = 3 * ts.length + 1 := sum_eq_of_two_mul_eight ts hT
  have hsum : ts.sum ≤ 3 * ts.length + 1 := by omega
  exact td1A_closed ns ts m hc3 hlast hT
    (StringFlow.TD1.chainA_ge_a0 ts hge)
    (StringFlow.TD1.chainA_le_amaxA ts hQ hhead hge hsum)
    hExcl

/-- B-family chain closed form specialized to `N_{Q+1} = m` and
`2^T_chain = 4 * 8^Q`. -/
theorem td1B_chain_closed_form_of_eq (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 4 * 8 ^ ts.length = 2 ^ ts.sum) :
    4 * 8 ^ ts.length * m =
      5 ^ ts.length * StringFlow.GC.chainFirst ns + StringFlow.GC.chainA ts := by
  have h := StringFlow.GC.c3_chain_closed_form ns ts hc3
  rw [hlast] at h
  rw [← hT] at h
  exact h

/-- B-family TD-1 closure assembled from the C3 closed form, the
chain interpolation bounds, and the interval exclusion. -/
theorem td1B_closed (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hA0le : StringFlow.TD1.a0 ts.length ≤ StringFlow.GC.chainA ts)
    (hAmaxle : StringFlow.GC.chainA ts ≤ StringFlow.TD1.amaxB ts.length)
    (hExcl : StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) >
               StringFlow.TD1.amaxB ts.length ∨
             StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) <
               StringFlow.TD1.a0 ts.length) :
    False := by
  exact td1B_chain_window_contradicts ts.length m (StringFlow.GC.chainFirst ns)
    (StringFlow.GC.chainA ts)
    (td1B_chain_closed_form_of_eq ns ts m hc3 hlast hT)
    hA0le hAmaxle hExcl

/-- B-family TD-1 closure with the interpolation bounds derived from
the C3 chain data: `A0 <= A_chain <= A_max` now follows from the
weight conditions `3 <= t`, `t_1 = 5`, and the budget `b = 2`. -/
theorem td1B_closed_of_chain (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hExcl : StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) >
               StringFlow.TD1.amaxB ts.length ∨
             StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) <
               StringFlow.TD1.a0 ts.length) :
    False := by
  have hsum_eq : ts.sum = 3 * ts.length + 2 := sum_eq_of_four_mul_eight ts hT
  have hsum : ts.sum ≤ 3 * ts.length + 2 := by omega
  exact td1B_closed ns ts m hc3 hlast hT
    (StringFlow.TD1.chainA_ge_a0 ts hge)
    (StringFlow.TD1.chainA_le_amaxB ts hQ hhead hge hsum)
    hExcl

/-- B-family closure from the tight chain: the certificate only needs
to exclude the unique value `A_max,5`, since `b = 2` forces
`A_chain = A_max,5`. -/
theorem td1B_closed_eq_amaxB (ns ts : List Nat) (m : Nat)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hlast : StringFlow.GC.chainLast ns = m)
    (hT : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hQ : 2 ≤ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hNe : StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) ≠
      StringFlow.TD1.amaxB ts.length) :
    False := by
  have hsum_eq : ts.sum = 3 * ts.length + 2 := sum_eq_of_four_mul_eight ts hT
  have hchain_eq : StringFlow.GC.chainA ts =
      StringFlow.TD1.amaxB ts.length :=
    StringFlow.TD1.chainA_eq_amaxB ts hQ hhead hge hsum_eq
  have hareq : StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) =
      StringFlow.GC.chainA ts :=
    td1B_chain_areq_eq ts.length m (StringFlow.GC.chainFirst ns)
      (StringFlow.GC.chainA ts)
      (td1B_chain_closed_form_of_eq ns ts m hc3 hlast hT)
  exact hNe (by rw [hareq, hchain_eq])

/-- The word certificate's `Areq` equals `A_req` for the A family and
is excluded from the A-family interval. -/
theorem wordBadA_areq_excl
    (Q L S TT T m0 mod target inv5 D m M0 Au Achain : Nat) (pos : List Nat)
    (hword : StringFlow.wordBad Q L S m0 mod target inv5 D
      (StringFlow.TD1.a0 Q) (StringFlow.TD1.amaxA Q) true pos = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % mod = target % mod)
    (hinv : (inv5 * 5 ^ L) % mod = 1)
    (hm7 : 7 ≤ m) (hmmod : m < mod) (hmlt : m < m0)
    (hrise : 2 ^ S * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hTT : S + T = TT)
    (hD : D = 2 ^ TT - 5 ^ (L + Q))
    (hT3 : T = 3 * Q + 1) :
    StringFlow.TD1.areqA Q m M0 > StringFlow.TD1.amaxA Q ∨
      StringFlow.TD1.areqA Q m M0 < StringFlow.TD1.a0 Q := by
  let r := StringFlow.subMod (target % mod) Au mod * inv5 % mod
  have hr : r = StringFlow.subMod (target % mod) Au mod * inv5 % mod := rfl
  have hmod0 : 0 < mod := by omega
  have hmod1 : 1 < mod := by omega
  have hrlt : r < mod := by
    dsimp [r]
    exact Nat.mod_lt _ hmod0
  have hrm : r = m :=
    StringFlow.r_eq_of_congruence L mod target inv5 Au m r hcong hinv hr hmmod hrlt hmod0 hmod1
  have hrmge : 7 ≤ r := by rw [hrm]; exact hm7
  have hrmlt : r < m0 := by rw [hrm]; exact hmlt
  have hglob : D * m = 5 ^ Q * Au + 2 ^ S * Achain :=
    StringFlow.global_D_equation L Q S T TT m M0 Au Achain D hrise hchain hTT hD
  have hineq : 5 ^ Q * Au ≤ D * m := by omega
  have hineqr : 5 ^ Q * Au ≤ D * r := by rw [hrm]; exact hineq
  have hsub : D * m - 5 ^ Q * Au = 2 ^ S * Achain := by omega
  have hdiv : (D * m - 5 ^ Q * Au) % 2 ^ S = 0 := by
    rw [hsub]
    exact Nat.mul_mod_right (2 ^ S) Achain
  have hdivr : (D * r - 5 ^ Q * Au) % 2 ^ S = 0 := by
    rw [hrm]
    exact hdiv
  have hcert := StringFlow.wordBad_imp_areq Q L S m0 mod target inv5 D
    (StringFlow.TD1.a0 Q) (StringFlow.TD1.amaxA Q) Au r
    ((D * r - 5 ^ Q * Au) / 2 ^ S) pos hword hAu hr hrmge hrmlt hineqr hdivr rfl
  have hAreqCert : (D * m - 5 ^ Q * Au) / 2 ^ S = Achain :=
    StringFlow.areq_cert_eq_chainA D m S Q Au Achain hglob
  have hcert' : (D * m - 5 ^ Q * Au) / 2 ^ S < StringFlow.TD1.a0 Q ∨
      (D * m - 5 ^ Q * Au) / 2 ^ S > StringFlow.TD1.amaxA Q := by
    simpa [hrm] using hcert
  have h2 : 2 ^ T = 2 * 8 ^ Q := by
    rw [hT3, two_mul_eight_pow_eq]
  have hchainA : 2 * 8 ^ Q * m = 5 ^ Q * M0 + Achain := by
    rw [h2] at hchain
    simpa [Nat.mul_assoc] using hchain
  have hAreqA_eq : StringFlow.TD1.areqA Q m M0 = Achain :=
    td1A_chain_areq_eq Q m M0 Achain hchainA
  rcases hcert' with hlt | hgt
  · right
    rw [hAreqA_eq]
    rw [hAreqCert] at hlt
    exact hlt
  · left
    rw [hAreqA_eq]
    rw [hAreqCert] at hgt
    exact hgt

/-- The B-family word certificate excludes the unique `A_max,5`, so
`A_req` cannot equal `A_max,5`. -/
theorem wordBadB_areq_excl
    (Q L S TT T m0 mod target inv5 D m M0 Au Achain : Nat) (pos : List Nat)
    (hword : StringFlow.wordBad Q L S m0 mod target inv5 D
      (StringFlow.TD1.amaxB Q) (StringFlow.TD1.amaxB Q) true pos = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % mod = target % mod)
    (hinv : (inv5 * 5 ^ L) % mod = 1)
    (hm7 : 7 ≤ m) (hmmod : m < mod) (hmlt : m < m0)
    (hrise : 2 ^ S * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hTT : S + T = TT)
    (hD : D = 2 ^ TT - 5 ^ (L + Q))
    (hT3 : T = 3 * Q + 2) :
    StringFlow.TD1.areqB Q m M0 ≠ StringFlow.TD1.amaxB Q := by
  let r := StringFlow.subMod (target % mod) Au mod * inv5 % mod
  have hr : r = StringFlow.subMod (target % mod) Au mod * inv5 % mod := rfl
  have hmod0 : 0 < mod := by omega
  have hmod1 : 1 < mod := by omega
  have hrlt : r < mod := by
    dsimp [r]
    exact Nat.mod_lt _ hmod0
  have hrm : r = m :=
    StringFlow.r_eq_of_congruence L mod target inv5 Au m r hcong hinv hr hmmod hrlt hmod0 hmod1
  have hrmge : 7 ≤ r := by rw [hrm]; exact hm7
  have hrmlt : r < m0 := by rw [hrm]; exact hmlt
  have hglob : D * m = 5 ^ Q * Au + 2 ^ S * Achain :=
    StringFlow.global_D_equation L Q S T TT m M0 Au Achain D hrise hchain hTT hD
  have hineq : 5 ^ Q * Au ≤ D * m := by omega
  have hineqr : 5 ^ Q * Au ≤ D * r := by rw [hrm]; exact hineq
  have hsub : D * m - 5 ^ Q * Au = 2 ^ S * Achain := by omega
  have hdiv : (D * m - 5 ^ Q * Au) % 2 ^ S = 0 := by
    rw [hsub]
    exact Nat.mul_mod_right (2 ^ S) Achain
  have hdivr : (D * r - 5 ^ Q * Au) % 2 ^ S = 0 := by
    rw [hrm]
    exact hdiv
  have hcert := StringFlow.wordBad_imp_areq Q L S m0 mod target inv5 D
    (StringFlow.TD1.amaxB Q) (StringFlow.TD1.amaxB Q) Au r
    ((D * r - 5 ^ Q * Au) / 2 ^ S) pos hword hAu hr hrmge hrmlt hineqr hdivr rfl
  have hAreqCert : (D * m - 5 ^ Q * Au) / 2 ^ S = Achain :=
    StringFlow.areq_cert_eq_chainA D m S Q Au Achain hglob
  have hcert' : (D * m - 5 ^ Q * Au) / 2 ^ S < StringFlow.TD1.amaxB Q ∨
      (D * m - 5 ^ Q * Au) / 2 ^ S > StringFlow.TD1.amaxB Q := by
    simpa [hrm] using hcert
  have h2 : 2 ^ T = 4 * 8 ^ Q := by
    rw [hT3]
    exact (four_mul_eight_pow_eq Q).symm
  have hchainB : 4 * 8 ^ Q * m = 5 ^ Q * M0 + Achain := by
    rw [h2] at hchain
    simpa [Nat.mul_assoc] using hchain
  have hAreqB_eq : StringFlow.TD1.areqB Q m M0 = Achain :=
    td1B_chain_areq_eq Q m M0 Achain hchainB
  intro hEq
  rw [hAreqB_eq] at hEq
  rcases hcert' with hlt | hgt
  · have hchain_lt : Achain < StringFlow.TD1.amaxB Q := by
      rw [hAreqCert] at hlt
      exact hlt
    omega
  · have hchain_gt : Achain > StringFlow.TD1.amaxB Q := by
      rw [hAreqCert] at hgt
      exact hgt
    omega

/-- The tabulated A-family certificate, specialized to the stage-one
word `pos`, supplies the A-family interval exclusion. -/
theorem td1A_cert_areq_excl
    (Q L TT T m M0 Au Achain : Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ StringFlow.combinations (L - 1) (StringFlow.tableU 1 Q L))
    (hup : StringFlow.tableUpper 1 Q L = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % StringFlow.tableMod 1 Q L =
      StringFlow.tableTarget 1 Q L % StringFlow.tableMod 1 Q L)
    (hinv : (StringFlow.tableInv5 1 Q L * 5 ^ L) %
      StringFlow.tableMod 1 Q L = 1)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 1 Q L)
    (hmlt : m < StringFlow.tableM0 1 Q L)
    (hrise : 2 ^ StringFlow.tableS 1 Q L * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hTT : StringFlow.tableS 1 Q L + T = TT)
    (hD : StringFlow.tableD 1 Q L = 2 ^ TT - 5 ^ (L + Q))
    (hT3 : T = 3 * Q + 1) :
    StringFlow.TD1.areqA Q m M0 > StringFlow.TD1.amaxA Q ∨
      StringFlow.TD1.areqA Q m M0 < StringFlow.TD1.a0 Q := by
  have hword := StringFlow.wordBadA_cleared Q L pos hQ8 hQ50 hL1 hL25 hmem
  rw [hup] at hword
  exact wordBadA_areq_excl Q L (StringFlow.tableS 1 Q L) TT T
    (StringFlow.tableM0 1 Q L) (StringFlow.tableMod 1 Q L)
    (StringFlow.tableTarget 1 Q L) (StringFlow.tableInv5 1 Q L)
    (StringFlow.tableD 1 Q L) m M0 Au Achain pos hword hAu hcong hinv
    hm7 hmmod hmlt hrise hchain hTT hD hT3

/-- The tabulated B-family certificate, specialized to the stage-one
word `pos`, supplies the B-family `A_req != A_max,5` exclusion. -/
theorem td1B_cert_areq_excl
    (Q L TT T m M0 Au Achain : Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ StringFlow.combinations (L - 1) (StringFlow.tableU 2 Q L - 1))
    (hup : StringFlow.tableUpper 2 Q L = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % StringFlow.tableMod 2 Q L =
      StringFlow.tableTarget 2 Q L % StringFlow.tableMod 2 Q L)
    (hinv : (StringFlow.tableInv5 2 Q L * 5 ^ L) %
      StringFlow.tableMod 2 Q L = 1)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 2 Q L)
    (hmlt : m < StringFlow.tableM0 2 Q L)
    (hrise : 2 ^ StringFlow.tableS 2 Q L * M0 = 5 ^ L * m + Au)
    (hchain : 2 ^ T * m = 5 ^ Q * M0 + Achain)
    (hTT : StringFlow.tableS 2 Q L + T = TT)
    (hD : StringFlow.tableD 2 Q L = 2 ^ TT - 5 ^ (L + Q))
    (hT3 : T = 3 * Q + 2) :
    StringFlow.TD1.areqB Q m M0 ≠ StringFlow.TD1.amaxB Q := by
  have hword := StringFlow.wordBadB_cleared Q L pos hQ8 hQ50 hL1 hL25 hmem
  rw [StringFlow.listMin_chainAValsB Q (by omega),
      StringFlow.listMax_chainAValsB Q (by omega)] at hword
  rw [hup] at hword
  exact wordBadB_areq_excl Q L (StringFlow.tableS 2 Q L) TT T
    (StringFlow.tableM0 2 Q L) (StringFlow.tableMod 2 Q L)
    (StringFlow.tableTarget 2 Q L) (StringFlow.tableInv5 2 Q L)
    (StringFlow.tableD 2 Q L) m M0 Au Achain pos hword hAu hcong hinv
    hm7 hmmod hmlt hrise hchain hTT hD hT3

/-- A-family final closure: the tabulated word certificate supplies
the interval exclusion for the real C3 chain, so the chain cannot
close. -/
theorem td1A_cert_closed
    (Q L TT m M0 Au : Nat) (ns ts : List Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ StringFlow.combinations (L - 1) (StringFlow.tableU 1 Q L))
    (hup : StringFlow.tableUpper 1 Q L = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % StringFlow.tableMod 1 Q L =
      StringFlow.tableTarget 1 Q L % StringFlow.tableMod 1 Q L)
    (hinv : (StringFlow.tableInv5 1 Q L * 5 ^ L) %
      StringFlow.tableMod 1 Q L = 1)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 1 Q L)
    (hmlt : m < StringFlow.tableM0 1 Q L)
    (hrise : 2 ^ StringFlow.tableS 1 Q L * M0 = 5 ^ L * m + Au)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 2 ^ ts.sum = 2 * 8 ^ ts.length)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hTT : StringFlow.tableS 1 Q L + ts.sum = TT)
    (hD : StringFlow.tableD 1 Q L = 2 ^ TT - 5 ^ (L + Q)) :
    False := by
  have hchainT := StringFlow.GC.c3_chain_closed_form ns ts hc3
  rw [hlchain, hfirst, hQlen] at hchainT
  have hT3 : ts.sum = 3 * Q + 1 := by
    have hsum := sum_eq_of_two_mul_eight ts hTchain
    rw [hQlen] at hsum
    exact hsum
  have hExcl := td1A_cert_areq_excl Q L TT ts.sum m M0 Au
    (StringFlow.GC.chainA ts) pos hQ8 hQ50 hL1 hL25 hmem hup hAu hcong
    hinv hm7 hmmod hmlt hrise hchainT hTT hD hT3
  have hExcl' : StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) >
        StringFlow.TD1.amaxA ts.length ∨
      StringFlow.TD1.areqA ts.length m (StringFlow.GC.chainFirst ns) <
        StringFlow.TD1.a0 ts.length := by
    simpa [hQlen, hfirst] using hExcl
  exact td1A_closed_of_chain ns ts m hc3 hlchain hTchain
    (by rw [hQlen]; exact hQ2) hhead hge hExcl'

/-- B-family final closure: the tabulated word certificate excludes
the unique `A_max,5`, so the tight B-family chain cannot close. -/
theorem td1B_cert_closed
    (Q L TT m M0 Au : Nat) (ns ts : List Nat) (pos : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hmem : pos ∈ StringFlow.combinations (L - 1) (StringFlow.tableU 2 Q L - 1))
    (hup : StringFlow.tableUpper 2 Q L = true)
    (hAu : Au = StringFlow.auOfPos L pos)
    (hcong : (5 ^ L * m + Au) % StringFlow.tableMod 2 Q L =
      StringFlow.tableTarget 2 Q L % StringFlow.tableMod 2 Q L)
    (hinv : (StringFlow.tableInv5 2 Q L * 5 ^ L) %
      StringFlow.tableMod 2 Q L = 1)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 2 Q L)
    (hmlt : m < StringFlow.tableM0 2 Q L)
    (hrise : 2 ^ StringFlow.tableS 2 Q L * M0 = 5 ^ L * m + Au)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hTT : StringFlow.tableS 2 Q L + ts.sum = TT)
    (hD : StringFlow.tableD 2 Q L = 2 ^ TT - 5 ^ (L + Q)) :
    False := by
  have hchainT := StringFlow.GC.c3_chain_closed_form ns ts hc3
  rw [hlchain, hfirst, hQlen] at hchainT
  have hT3 : ts.sum = 3 * Q + 2 := by
    have hsum := sum_eq_of_four_mul_eight ts hTchain
    rw [hQlen] at hsum
    exact hsum
  have hNe := td1B_cert_areq_excl Q L TT ts.sum m M0 Au
    (StringFlow.GC.chainA ts) pos hQ8 hQ50 hL1 hL25 hmem hup hAu hcong
    hinv hm7 hmmod hmlt hrise hchainT hTT hD hT3
  have hNe' : StringFlow.TD1.areqB ts.length m (StringFlow.GC.chainFirst ns) ≠
      StringFlow.TD1.amaxB ts.length := by
    simpa [hQlen, hfirst] using hNe
  exact td1B_closed_eq_amaxB ns ts m hc3 hlchain hTchain
    (by rw [hQlen]; exact hQ2) hhead hge hNe'

/-- A-family final closure from the real rising word: the 52.17
congruence system and the orbit-to-`pos` bridge supply every input of
`td1A_cert_closed`. -/
theorem td1A_cert_closed_of_word
    (Q L TT m M0 : Nat) (ns ts w : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hfeas : StringFlow.feasible 1 Q L = true)
    (hup : StringFlow.tableUpper 1 Q L = true)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = StringFlow.tableS 1 Q L)
    (hlast : StringFlow.Word.wordLast w = 1)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 1 Q L)
    (hmlt : m < StringFlow.tableM0 1 Q L)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 2 ^ ts.sum = 2 * 8 ^ ts.length)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hTT : StringFlow.tableS 1 Q L + ts.sum = TT)
    (hD : StringFlow.tableD 1 Q L = 2 ^ TT - 5 ^ (L + Q)) :
    False := by
  let pos := StringFlow.twosPositions w
  let Au := StringFlow.Word.wordA w
  have hAuW : Au = StringFlow.Word.wordA w := rfl
  have hAuPos : Au = StringFlow.auOfPos L pos := by
    dsimp [pos, Au]
    rw [← hwlen]
    exact StringFlow.wordA_eq_auOfPos_of_twosPositions w hok
  have hmemW : StringFlow.twosPositions w ∈
      StringFlow.combinations (L - 1)
        ((w.filter (fun t => t = 2)).length) := by
    simpa [hwlen] using
      (StringFlow.twosPositions_mem_combinations_of_last_one w hlast)
  have hcount : (w.filter (fun t => t = 2)).length =
      StringFlow.tableU 1 Q L := by
    have hfs := StringFlow.filter_count_eq_wordWeight_sub_length w hok
    have hspec := StringFlow.table_spec 1 Q L (by decide) (by decide)
      hfeas hQ8 hQ50 hL1 hL25
    rcases hspec with ⟨hU, hS, _hMod, _hTarget, _hInv⟩
    rw [hwS, hwlen] at hfs
    rw [hS] at hfs
    rw [hU]
    omega
  have hmem : pos ∈
      StringFlow.combinations (L - 1) (StringFlow.tableU 1 Q L) := by
    dsimp [pos]
    simpa [hcount] using hmemW
  have hrise : 2 ^ StringFlow.tableS 1 Q L * M0 = 5 ^ L * m + Au := by
    have h := StringFlow.rising_equation_of_wordValid w m M0 hvalid hM0
    rw [hwS, hwlen, ← hAuW] at h
    exact h
  have h16 : M0 % 16 = 11 := by
    rw [← hfirst]
    exact StringFlow.chainFirst_mod16_of_c3Exact_weight_three ns ts hc3 hhead hge
      (by rw [hQlen]; exact hQ2)
  have hconghinv := StringFlow.congruence_52_17_A Q L m M0 Au w
    hfeas hQ8 hQ50 hL1 hL25 hwlen hwS hvalid hM0 h16 hAuW
  rcases hconghinv with ⟨hcong, hinv⟩
  exact td1A_cert_closed Q L TT m M0 Au ns ts pos hQ8 hQ50 hL1 hL25 hmem hup
    hAuPos hcong hinv hm7 hmmod hmlt hrise hQlen hc3 hfirst hlchain hTchain
    hQ2 hhead hge hTT hD

/-- B-family final closure from the real rising word: the 52.17
congruence system and the orbit-to-`pos` bridge supply every input of
`td1B_cert_closed`. -/
theorem td1B_cert_closed_of_word
    (Q L TT m M0 : Nat) (ns ts w : List Nat)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hfeas : StringFlow.feasible 2 Q L = true)
    (hup : StringFlow.tableUpper 2 Q L = true)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = StringFlow.tableS 2 Q L)
    (hlast : StringFlow.Word.wordLast w = 2)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod 2 Q L)
    (hmlt : m < StringFlow.tableM0 2 Q L)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hTT : StringFlow.tableS 2 Q L + ts.sum = TT)
    (hD : StringFlow.tableD 2 Q L = 2 ^ TT - 5 ^ (L + Q)) :
    False := by
  let pos := StringFlow.twosPositions w.dropLast
  let Au := StringFlow.Word.wordA w
  have hAuW : Au = StringFlow.Word.wordA w := rfl
  have hAuPos : Au = StringFlow.auOfPos L pos := by
    dsimp [pos, Au]
    rw [← hwlen]
    exact StringFlow.wordA_eq_auOfPos_of_twosPositions_dropLast w hok hlast
  have hmemW : StringFlow.twosPositions w.dropLast ∈
      StringFlow.combinations (L - 1)
        ((w.dropLast.filter (fun t => t = 2)).length) := by
    simpa [hwlen] using
      (StringFlow.twosPositions_mem_combinations_of_last_two w hlast)
  have hcount : (w.dropLast.filter (fun t => t = 2)).length =
      StringFlow.tableU 2 Q L - 1 := by
    have hfs := StringFlow.filter_count_eq_wordWeight_sub_length w hok
    have hfc := StringFlow.filter_count_of_last_two w hlast
    have hspec := StringFlow.table_spec 2 Q L (by decide) (by decide)
      hfeas hQ8 hQ50 hL1 hL25
    rcases hspec with ⟨hU, hS, _hMod, _hTarget, _hInv⟩
    rw [hwS, hwlen] at hfs
    rw [hS] at hfs
    rw [hU]
    omega
  have hmem : pos ∈
      StringFlow.combinations (L - 1) (StringFlow.tableU 2 Q L - 1) := by
    dsimp [pos]
    simpa [hcount] using hmemW
  have hrise : 2 ^ StringFlow.tableS 2 Q L * M0 = 5 ^ L * m + Au := by
    have h := StringFlow.rising_equation_of_wordValid w m M0 hvalid hM0
    rw [hwS, hwlen, ← hAuW] at h
    exact h
  have h64 : M0 % 64 = 19 := by
    rw [← hfirst]
    exact StringFlow.chainFirst_mod64_of_c3Exact_weight_five ns ts hc3 hhead hge
      (by rw [hQlen]; exact hQ2)
  have hconghinv := StringFlow.congruence_52_17_B Q L m M0 Au w
    hfeas hQ8 hQ50 hL1 hL25 hwlen hwS hvalid hM0 h64 hAuW
  rcases hconghinv with ⟨hcong, hinv⟩
  exact td1B_cert_closed Q L TT m M0 Au ns ts pos hQ8 hQ50 hL1 hL25 hmem hup
    hAuPos hcong hinv hm7 hmmod hmlt hrise hQlen hc3 hfirst hlchain hTchain
    hQ2 hhead hge hTT hD

/-- TD-0 final assembly: the real rising word and C3 chain from a
QB-8/frame-A setup split into the A family (`b = 1`) or the B family
(`b = 2`), and both branches are contradictory. -/
theorem td0_cert_closed
    (b Q L TT m M0 : Nat) (ns ts w : List Nat)
    (hb : b = 1 ∨ b = 2)
    (hQ8 : 8 ≤ Q) (hQ50 : Q ≤ 50) (hL1 : 1 ≤ L) (hL25 : L ≤ 25)
    (hfeas : StringFlow.feasible b Q L = true)
    (hup : StringFlow.tableUpper b Q L = true)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = StringFlow.tableS b Q L)
    (hlast : StringFlow.Word.wordLast w = b)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hm7 : 7 ≤ m) (hmmod : m < StringFlow.tableMod b Q L)
    (hmlt : m < StringFlow.tableM0 b Q L)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hQ2 : 2 ≤ Q)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t)
    (hTT : StringFlow.tableS b Q L + ts.sum = TT)
    (hD : StringFlow.tableD b Q L = 2 ^ TT - 5 ^ (L + Q)) :
    False := by
  rcases hb with hb1 | hb2
  · subst hb1
    exact td1A_cert_closed_of_word Q L TT m M0 ns ts w hQ8 hQ50 hL1 hL25
      hfeas hup hwlen hwS hlast hok hm7 hmmod hmlt hvalid hM0 hQlen hc3
      hfirst hlchain hTchain hQ2 hhead hge hTT hD
  · subst hb2
    exact td1B_cert_closed_of_word Q L TT m M0 ns ts w hQ8 hQ50 hL1 hL25
      hfeas hup hwlen hwS hlast hok hm7 hmmod hmlt hvalid hM0 hQlen hc3
      hfirst hlchain hTchain hQ2 hhead hge hTT hD

/-- If every entry is `1` or `2` and the weight equals the length,
then there are no `2` entries. -/
theorem twosPositions_eq_nil_of_weight_eq_length (w : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hw : StringFlow.wordWeight w = w.length) :
    StringFlow.twosPositions w = [] := by
  induction w with
  | nil => simp [StringFlow.twosPositions]
  | cons t ts ih =>
      have ht : t = 1 := by
        rcases hok t (by simp) with h1 | h2
        · exact h1
        · subst t
          simp [StringFlow.wordWeight] at hw
          have hge : ts.length ≤ StringFlow.wordWeight ts :=
            StringFlow.wordWeight_ge_length ts (fun x hx => by
              rcases hok x (by simp [hx]) with h3 | h4 <;> omega)
          omega
      subst t
      have htail : StringFlow.wordWeight ts = ts.length := by
        simp [StringFlow.wordWeight] at hw
        omega
      have ih' := ih (fun x hx => hok x (by simp [hx])) htail
      simp [StringFlow.twosPositions, ih']

/-- In the exceptional B-family triple `(2,8,7)`, the rising word
has two `2` entries, one of them last; among the six possible places
for the other `2`, `A_u` is at most `36373`. -/
theorem wordA_le_36373_special_B (w : List Nat)
    (hwlen : w.length = 7)
    (hwS : StringFlow.wordWeight w = 9)
    (hlast : StringFlow.Word.wordLast w = 2)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    StringFlow.Word.wordA w ≤ 36373 := by
  cases w with
  | nil => simp at hwlen
  | cons a0 rest0 =>
    cases rest0 with
    | nil => simp at hwlen
    | cons a1 rest1 =>
      cases rest1 with
      | nil => simp at hwlen
      | cons a2 rest2 =>
        cases rest2 with
        | nil => simp at hwlen
        | cons a3 rest3 =>
          cases rest3 with
          | nil => simp at hwlen
          | cons a4 rest4 =>
            cases rest4 with
            | nil => simp at hwlen
            | cons a5 rest5 =>
              cases rest5 with
              | nil => simp at hwlen
              | cons a6 rest6 =>
                cases rest6 with
                | nil =>
                  have hsum : a0 + a1 + a2 + a3 + a4 + a5 + a6 = 9 := by
                    simp [StringFlow.wordWeight] at hwS
                    omega
                  have hlast' : a6 = 2 := by
                    simp [StringFlow.Word.wordLast] at hlast
                    exact hlast
                  have ha0 : a0 = 1 ∨ a0 = 2 := hok a0 (by simp)
                  have ha1 : a1 = 1 ∨ a1 = 2 := hok a1 (by simp)
                  have ha2 : a2 = 1 ∨ a2 = 2 := hok a2 (by simp)
                  have ha3 : a3 = 1 ∨ a3 = 2 := hok a3 (by simp)
                  have ha4 : a4 = 1 ∨ a4 = 2 := hok a4 (by simp)
                  have ha5 : a5 = 1 ∨ a5 = 2 := hok a5 (by simp)
                  by_cases h20 : a0 = 2
                  · have hrest : a1 = 1 ∧ a2 = 1 ∧ a3 = 1 ∧ a4 = 1 ∧ a5 = 1 := by
                      omega
                    rcases hrest with ⟨h1, h2, h3, h4, h5⟩
                    subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                    norm_num [StringFlow.Word.wordA]
                  · have h01 : a0 = 1 := by omega
                    by_cases h21 : a1 = 2
                    · have hrest : a2 = 1 ∧ a3 = 1 ∧ a4 = 1 ∧ a5 = 1 := by omega
                      rcases hrest with ⟨h2, h3, h4, h5⟩
                      subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                      norm_num [StringFlow.Word.wordA]
                    · have h11 : a1 = 1 := by omega
                      by_cases h22 : a2 = 2
                      · have hrest : a3 = 1 ∧ a4 = 1 ∧ a5 = 1 := by omega
                        rcases hrest with ⟨h3, h4, h5⟩
                        subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                        norm_num [StringFlow.Word.wordA]
                      · have h12 : a2 = 1 := by omega
                        by_cases h23 : a3 = 2
                        · have hrest : a4 = 1 ∧ a5 = 1 := by omega
                          rcases hrest with ⟨h4, h5⟩
                          subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                          norm_num [StringFlow.Word.wordA]
                        · have h13 : a3 = 1 := by omega
                          by_cases h24 : a4 = 2
                          · have h5 : a5 = 1 := by omega
                            subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                            norm_num [StringFlow.Word.wordA]
                          · have h14 : a4 = 1 := by omega
                            have h15 : a5 = 2 := by omega
                            subst a0; subst a1; subst a2; subst a3; subst a4; subst a5; subst a6
                            norm_num [StringFlow.Word.wordA]
                | cons _ _ => simp at hwlen

/-- Except for the two special lower-branch triples, every feasible
stage-one triple has `tableUpper = true`. -/
def tableUpperExceptOK : Bool :=
  StringFlow.allInRange 1 3 (fun b =>
    StringFlow.allInRange 8 51 (fun Q =>
      StringFlow.allInRange 1 26 (fun L =>
        (! StringFlow.feasible b Q L ||
          StringFlow.tableUpper b Q L = true ||
          (b = 1 && Q = 20 && L = 11) ||
          (b = 2 && Q = 8 && L = 7)))))

theorem tableUpperExcept_check : tableUpperExceptOK = true := by
  native_decide

theorem tableUpper_of_feasible_not_special (b Q L : Nat)
    (hfeas : StringFlow.feasible b Q L = true)
    (hnotA : ¬ (b = 1 ∧ Q = 20 ∧ L = 11))
    (hnotB : ¬ (b = 2 ∧ Q = 8 ∧ L = 7)) :
    StringFlow.tableUpper b Q L = true := by
  have hb1 : 1 ≤ b := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hb2 : b < 3 := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hQ8 : 8 ≤ Q := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hQ51 : Q < 51 := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hL1 : 1 ≤ L := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hL26 : L < 26 := by
    have h := of_decide_eq_true hfeas
    simp at h
    omega
  have hb := StringFlow.allInRange_spec 1 3
    (fun b => StringFlow.allInRange 8 51 (fun Q =>
      StringFlow.allInRange 1 26 (fun L =>
        (! StringFlow.feasible b Q L ||
          StringFlow.tableUpper b Q L = true ||
          (b = 1 && Q = 20 && L = 11) ||
          (b = 2 && Q = 8 && L = 7)))))
    tableUpperExcept_check b hb1 hb2
  have hQ := StringFlow.allInRange_spec 8 51
    (fun Q => StringFlow.allInRange 1 26 (fun L =>
      (! StringFlow.feasible b Q L ||
        StringFlow.tableUpper b Q L = true ||
        (b = 1 && Q = 20 && L = 11) ||
        (b = 2 && Q = 8 && L = 7))))
    hb Q hQ8 hQ51
  have hL := StringFlow.allInRange_spec 1 26
    (fun L =>
      (! StringFlow.feasible b Q L ||
        StringFlow.tableUpper b Q L = true ||
        (b = 1 && Q = 20 && L = 11) ||
        (b = 2 && Q = 8 && L = 7)))
    hQ L hL1 hL26
  simp [hfeas] at hL
  rcases hL with hupA | hB
  · rcases hupA with hup | hA
    · exact hup
    · rcases hA with ⟨hA1, rfl⟩
      rcases hA1 with ⟨rfl, rfl⟩
      exact False.elim (hnotA ⟨rfl, rfl, rfl⟩)
  · rcases hB with ⟨hB1, rfl⟩
    rcases hB1 with ⟨rfl, rfl⟩
    exact False.elim (hnotB ⟨rfl, rfl, rfl⟩)

/-- All inputs needed by the TD-0 closure, packaged as one datum.
This is the interface that a frame-A + QB-8 cycle wrapper must
construct.  The two stage-one lower-branch triples are handled inside
`td0_closed_of_data`, so `tableUpper` is not required to be `true`. -/
structure Td0Data (b Q L TT m M0 : Nat) (ns ts w : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hQ8 : 8 ≤ Q
  hQ50 : Q ≤ 50
  hL1 : 1 ≤ L
  hL25 : L ≤ 25
  hfeas : StringFlow.feasible b Q L = true
  hwlen : w.length = L
  hwS : StringFlow.wordWeight w = StringFlow.tableS b Q L
  hlast : StringFlow.Word.wordLast w = b
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hm7 : 7 ≤ m
  hmmod : m < StringFlow.tableMod b Q L
  hmlt : m < StringFlow.tableM0 b Q L
  hvalid : StringFlow.Word.wordValid w m
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hQ2 : 2 ≤ Q
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hTT : StringFlow.tableS b Q L + ts.sum = TT
  hD : StringFlow.tableD b Q L = 2 ^ TT - 5 ^ (L + Q)

/-- The exceptional B-family triple `(2,8,7)` is impossible by the
global cycle equation and the finite `sixAuOK` maximum. -/
theorem td0_B_special_false (TT m M0 : Nat) (ns ts w : List Nat)
    (h : Td0Data 2 8 7 TT m M0 ns ts w) : False := by
  let Au := StringFlow.Word.wordA w
  let Achain := StringFlow.GC.chainA ts
  have hTchain' : 4 * 8 ^ ts.length = 2 ^ ts.sum := by
    simpa using h.hTchain
  have hhead5 : ∀ a as, ts = a :: as → a = 5 := by
    intro a as hts
    have hh := h.hhead a as hts
    simpa using hh
  have hAu_le : Au ≤ 36373 := by
    dsimp [Au]
    exact wordA_le_36373_special_B w h.hwlen h.hwS h.hlast h.hok
  have hAchain : Achain = 21614413 := by
    dsimp [Achain]
    have hQlen2 : 2 ≤ ts.length := by
      rw [h.hQlen]
      exact h.hQ2
    have hA := StringFlow.TD1.chainA_eq_amaxB ts hQlen2 hhead5 h.hge
      (sum_eq_of_four_mul_eight ts hTchain')
    rw [h.hQlen] at hA
    exact hA
  have hS9 : StringFlow.tableS 2 8 7 = 9 := by native_decide
  have hsum26 : ts.sum = 26 := by
    have hsum := sum_eq_of_four_mul_eight ts hTchain'
    rw [h.hQlen] at hsum
    norm_num at hsum
    exact hsum
  let D := StringFlow.tableD 2 8 7
  have hD35 : D = 2 ^ 35 - 5 ^ (7 + 8) := by
    dsimp [D]
    native_decide
  have hrise' : 2 ^ 9 * M0 = 5 ^ 7 * m + Au := by
    have h0 := StringFlow.rising_equation_of_wordValid w m M0 h.hvalid h.hM0
    dsimp [Au] at h0 ⊢
    rw [h.hwlen, h.hwS, hS9] at h0
    exact h0
  have hchain' : 2 ^ 26 * m = 5 ^ 8 * M0 + Achain := by
    have h0 := StringFlow.GC.c3_chain_closed_form ns ts h.hc3
    dsimp [Achain] at h0 ⊢
    rw [h.hfirst, h.hlchain, h.hQlen, hsum26] at h0
    exact h0
  have hglob : D * m = 5 ^ 8 * Au + 2 ^ 9 * Achain :=
    StringFlow.global_D_equation 7 8 9 26 35 m M0 Au Achain D hrise' hchain'
      (by norm_num) hD35
  have hinf : 5 ^ 8 * 36373 + 2 ^ 9 * 21614413 < 7 * D := by
    dsimp [D]
    native_decide
  have hleft : 7 * D ≤ D * m := by
    have hmul := Nat.mul_le_mul_right D h.hm7
    simpa [Nat.mul_comm] using hmul
  have hright_le : 5 ^ 8 * Au + 2 ^ 9 * Achain ≤ 25274782581 := by
    have h1 : 5 ^ 8 * Au ≤ 5 ^ 8 * 36373 :=
      Nat.mul_le_mul_left (5 ^ 8) hAu_le
    have h2 : 2 ^ 9 * Achain ≤ 2 ^ 9 * 21614413 := by
      rw [hAchain]
    have hmax : 5 ^ 8 * 36373 + 2 ^ 9 * 21614413 = 25274782581 := by
      native_decide
    nlinarith
  omega

/-- The exceptional lower-branch triple `(1,20,11)` has no residue
below its `m0 = 31` threshold; the unique word forces `m = 6573`. -/
theorem td0_A_special_false (TT m M0 : Nat) (ns ts w : List Nat)
    (h : Td0Data 1 20 11 TT m M0 ns ts w) : False := by
  have hS11 : StringFlow.tableS 1 20 11 = 11 := by native_decide
  have hwS' : StringFlow.wordWeight w = w.length := by
    rw [h.hwS, hS11, h.hwlen]
  have hpos : StringFlow.twosPositions w = [] :=
    twosPositions_eq_nil_of_weight_eq_length w h.hok hwS'
  have hAuPos : StringFlow.Word.wordA w = StringFlow.auOfPos 11 [] := by
    have hA := StringFlow.wordA_eq_auOfPos_of_twosPositions w h.hok
    rw [h.hwlen, hpos] at hA
    exact hA
  let mod := StringFlow.tableMod 1 20 11
  let target := StringFlow.tableTarget 1 20 11
  let inv5 := StringFlow.tableInv5 1 20 11
  let r := StringFlow.subMod (target % mod) (StringFlow.Word.wordA w) mod * inv5 % mod
  have hr : r = 17749 := by
    dsimp [r, mod, target, inv5]
    rw [hAuPos]
    native_decide
  have hhead3 : ∀ a as, ts = a :: as → a = 3 := by
    intro a as hts
    have hh := h.hhead a as hts
    simpa using hh
  have h16 : M0 % 16 = 11 := by
    rw [← h.hfirst]
    have hQlen2 : 2 ≤ ts.length := by
      rw [h.hQlen]
      exact h.hQ2
    exact StringFlow.chainFirst_mod16_of_c3Exact_weight_three ns ts h.hc3
      hhead3 h.hge hQlen2
  have hcong := StringFlow.congruence_52_17_A 20 11 m M0
    (StringFlow.Word.wordA w) w h.hfeas (by omega) (by omega)
    (by omega) (by omega) h.hwlen h.hwS h.hvalid h.hM0 h16 rfl
  rcases hcong with ⟨hcong, hinv⟩
  have hmodpos : 0 < mod := by native_decide
  have hmod1 : 1 < mod := by native_decide
  have hrlt : r < mod := by
    rw [hr]
    native_decide
  have hrDef : r = StringFlow.subMod (target % mod) (StringFlow.Word.wordA w) mod *
      inv5 % mod := rfl
  have hmeq : r = m := StringFlow.r_eq_of_congruence 11 mod target inv5
    (StringFlow.Word.wordA w) m r hcong hinv hrDef h.hmmod hrlt hmodpos hmod1
  have hm17749 : 17749 = m := by
    rw [hr] at hmeq
    exact hmeq
  have hM0val : StringFlow.tableM0 1 20 11 = 31 := by native_decide
  have hmlt31 : m < 31 := by simpa [hM0val] using h.hmlt
  omega

/-- TD-0 is closed from a single `Td0Data` datum. -/
theorem td0_closed_of_data (b Q L TT m M0 : Nat) (ns ts w : List Nat)
    (h : Td0Data b Q L TT m M0 ns ts w) : False :=
  by
    by_cases hA : b = 1 ∧ Q = 20 ∧ L = 11
    · rcases hA with ⟨rfl, rfl, rfl⟩
      exact td0_A_special_false TT m M0 ns ts w h
    by_cases hB : b = 2 ∧ Q = 8 ∧ L = 7
    · rcases hB with ⟨rfl, rfl, rfl⟩
      exact td0_B_special_false TT m M0 ns ts w h
    have hnot : ¬ ((b = 1 ∧ Q = 20 ∧ L = 11) ∨
        (b = 2 ∧ Q = 8 ∧ L = 7)) := by
      intro hx
      rcases hx with hx | hx
      · exact hA hx
      · exact hB hx
    have hup' : StringFlow.tableUpper b Q L = true :=
      tableUpper_of_feasible_not_special b Q L h.hfeas hA hB
    exact td0_cert_closed b Q L TT m M0 ns ts w h.hb h.hQ8 h.hQ50 h.hL1 h.hL25
      h.hfeas hup' h.hwlen h.hwS h.hlast h.hok h.hm7 h.hmmod h.hmlt
      h.hvalid h.hM0 h.hQlen h.hc3 h.hfirst h.hlchain h.hTchain h.hQ2
      h.hhead h.hge h.hTT h.hD

/-- From the real rising equation and `Au <= Amax`, the orbit ratio
`M0/m` is bounded by `(5^L*m + Amax) / (2^(L+U)*m)`. -/
theorem m0_div_m_le_Rmax (L U m M0 Au Amax : Nat)
    (hm : 0 < m)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAu : Au ≤ Amax) :
    (M0 : Rat) / (m : Rat) ≤
      ((5 ^ L * m + Amax : Nat) : Rat) / ((2 ^ (L + U) * m : Nat) : Rat) := by
  have hle : 2 ^ (L + U) * M0 ≤ 5 ^ L * m + Amax := by
    rw [hrise]
    omega
  have hleRat : ((2 ^ (L + U) * M0 : Nat) : Rat) ≤
      ((5 ^ L * m + Amax : Nat) : Rat) := by
    exact_mod_cast hle
  have hleRat' : (M0 : Rat) * ((2 ^ (L + U) : Nat) : Rat) ≤
      ((5 ^ L * m + Amax : Nat) : Rat) := by
    norm_num at hleRat ⊢
    simpa [mul_comm] using hleRat
  field_simp [show (m : Rat) ≠ 0 by positivity,
    show ((2 ^ (L + U) : Nat) : Rat) ≠ 0 by positivity]
  ring_nf
  rw [pow_add] at hleRat'
  norm_num at hleRat' ⊢
  nlinarith [hleRat']

/-- The same bound rewritten in the `B*(1 + Amax/(5^L*m))` form. -/
theorem rmax_eq (L U m Amax : Nat) (hm : 0 < m) :
    ((5 ^ L * m + Amax : Nat) : Rat) / ((2 ^ (L + U) * m : Nat) : Rat) =
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / ((5 ^ L : Rat) * (m : Rat))) := by
  have h5 : (5 ^ L : Rat) ≠ 0 := by positivity
  have h2 : (2 ^ (L + U) : Rat) ≠ 0 := by positivity
  have hmRat : (m : Rat) ≠ 0 := by positivity
  field_simp [h5, h2, hmRat]
  simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring_nf

/-- Phase-2 A-family upper branch plus the real rising word gives
`M0/m < U_A`. -/
theorem upperBranchA_ratio_lt
    (Q L U m M0 Au Amax : Nat)
    (hUp : StringFlow.TD0.upperBranch 1 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 1 + U)
    (hm : 0 < m)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax) :
    (M0 : Rat) / (m : Rat) <
      2 * (8 / 5 : Rat) ^ Q -
        (2 * (8 / 5 : Rat) ^ Q - 89 / 25) / (3 * (m : Rat)) := by
  have hUeq : StringFlow.uReq 1 Q L = U := by
    unfold StringFlow.uReq
    rw [hT]
    omega
  have hB : StringFlow.TD0.phase2B 1 Q L =
      (5 ^ L : Rat) / (2 ^ (L + U) : Rat) :=
    StringFlow.TD0.phase2B_eq 1 Q L U (Or.inl rfl) hT
  have hUp' :
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (1 - (2 / 3 : Rat) * ((4 / 5 : Rat) ^ U) -
          (1 : Rat) / (3 * ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)))) /
            (m : Rat)) <
        2 * (8 / 5 : Rat) ^ Q -
          (2 * (8 / 5 : Rat) ^ Q - 89 / 25) / (3 * (m : Rat)) := by
    simpa [StringFlow.TD0.upperBranch, hUeq, hB] using
      (StringFlow.TD0.upperBranchA_prop Q L m hUp)
  have hmax := StringFlow.amaxWord_div_eq_hmax L U hUle
  have hAmax' : (Amax : Rat) / (5 ^ L : Rat) =
      1 - (2 / 3 : Rat) * ((4 / 5 : Rat) ^ U) -
        (1 : Rat) / (3 * ((5 ^ L : Rat) / (2 ^ (L + U) : Rat))) := by
    rw [hAmax]
    exact hmax
  have hUp2 :
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) <
        2 * (8 / 5 : Rat) ^ Q -
          (2 * (8 / 5 : Rat) ^ Q - 89 / 25) / (3 * (m : Rat)) := by
    rw [← hAmax'] at hUp'
    simpa using hUp'
  have hRle0 : (M0 : Rat) / (m : Rat) ≤
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / ((5 ^ L : Rat) * (m : Rat))) := by
    have h1 := m0_div_m_le_Rmax L U m M0 Au Amax hm hrise hAuLe
    rw [rmax_eq L U m Amax hm] at h1
    exact h1
  have hRle : (M0 : Rat) / (m : Rat) ≤
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) := by
    have hEq :
        ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
          (1 + (Amax : Rat) / ((5 ^ L : Rat) * (m : Rat))) =
        ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
          (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) := by
      field_simp [show (m : Rat) ≠ 0 by positivity,
        show (5 ^ L : Rat) ≠ 0 by positivity,
        show (2 ^ (L + U) : Rat) ≠ 0 by positivity]
    rw [← hEq]
    exact hRle0
  exact lt_of_le_of_lt hRle hUp2

/-- Phase-2 B-family upper branch plus the real rising word gives
`M0/m < U_B`. -/
theorem upperBranchB_ratio_lt
    (Q L U m M0 Au Amax : Nat)
    (hUp : StringFlow.TD0.upperBranch 2 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 2 + U)
    (hm : 0 < m)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax) :
    (M0 : Rat) / (m : Rat) <
      4 * (8 / 5 : Rat) ^ Q -
        (4 * (8 / 5 : Rat) ^ Q - 29 / 5) / (3 * (m : Rat)) := by
  have hUeq : StringFlow.uReq 2 Q L = U := by
    unfold StringFlow.uReq
    rw [hT]
    omega
  have hB : StringFlow.TD0.phase2B 2 Q L =
      (5 ^ L : Rat) / (2 ^ (L + U) : Rat) :=
    StringFlow.TD0.phase2B_eq 2 Q L U (Or.inr rfl) hT
  have hUp' :
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (1 - (2 / 3 : Rat) * ((4 / 5 : Rat) ^ U) -
          (1 : Rat) / (3 * ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)))) /
            (m : Rat)) <
        4 * (8 / 5 : Rat) ^ Q -
          (4 * (8 / 5 : Rat) ^ Q - 29 / 5) / (3 * (m : Rat)) := by
    simpa [StringFlow.TD0.upperBranch, hUeq, hB] using
      (StringFlow.TD0.upperBranchB_prop Q L m hUp)
  have hmax := StringFlow.amaxWord_div_eq_hmax L U hUle
  have hAmax' : (Amax : Rat) / (5 ^ L : Rat) =
      1 - (2 / 3 : Rat) * ((4 / 5 : Rat) ^ U) -
        (1 : Rat) / (3 * ((5 ^ L : Rat) / (2 ^ (L + U) : Rat))) := by
    rw [hAmax]
    exact hmax
  have hUp2 :
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) <
        4 * (8 / 5 : Rat) ^ Q -
          (4 * (8 / 5 : Rat) ^ Q - 29 / 5) / (3 * (m : Rat)) := by
    rw [← hAmax'] at hUp'
    simpa using hUp'
  have hRle0 : (M0 : Rat) / (m : Rat) ≤
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / ((5 ^ L : Rat) * (m : Rat))) := by
    have h1 := m0_div_m_le_Rmax L U m M0 Au Amax hm hrise hAuLe
    rw [rmax_eq L U m Amax hm] at h1
    exact h1
  have hRle : (M0 : Rat) / (m : Rat) ≤
      ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
        (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) := by
    have hEq :
        ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
          (1 + (Amax : Rat) / ((5 ^ L : Rat) * (m : Rat))) =
        ((5 ^ L : Rat) / (2 ^ (L + U) : Rat)) *
          (1 + (Amax : Rat) / (5 ^ L : Rat) / (m : Rat)) := by
      field_simp [show (m : Rat) ≠ 0 by positivity,
        show (5 ^ L : Rat) ≠ 0 by positivity,
        show (2 ^ (L + U) : Rat) ≠ 0 by positivity]
    rw [← hEq]
    exact hRle0
  exact lt_of_le_of_lt hRle hUp2

/-- `A_max,3(Q)/5^Q = (2*(8/5)^Q - 89/25)/3`. -/
theorem amaxA_div_eq (Q : Nat) (hQ2 : 2 ≤ Q) :
    (StringFlow.TD1.amaxA Q : Rat) / (5 ^ Q : Rat) =
      (2 * (8 / 5 : Rat) ^ Q - 89 / 25) / 3 := by
  have hA := StringFlow.TD1.a0_three_mul Q
  have hS := StringFlow.TD1.three_mul_s3 Q hQ2
  have h5 := StringFlow.TD1.five_pow_eq_25_mul Q hQ2
  have hsum : 3 * StringFlow.TD1.amaxA Q = 2 * 8 ^ Q - 89 * 5 ^ (Q - 2) := by
    unfold StringFlow.TD1.amaxA
    rw [Nat.mul_add, hA, hS, h5]
    have hle8 : 25 * 5 ^ (Q - 2) ≤ 8 ^ Q := by
      rw [← h5]
      exact StringFlow.GC.five_pow_le_eight_pow Q
    have hle64 : 64 * 5 ^ (Q - 2) ≤ 8 ^ Q := StringFlow.TD1.s3_le_eight Q hQ2
    omega
  have hsumRat : ((3 * StringFlow.TD1.amaxA Q : Nat) : Rat) =
      ((2 * 8 ^ Q - 89 * 5 ^ (Q - 2) : Nat) : Rat) := by
    exact_mod_cast hsum
  have hle64 : 64 * 5 ^ (Q - 2) <= 8 ^ Q :=
    StringFlow.TD1.s3_le_eight Q hQ2
  have hgeNat : 89 * 5 ^ (Q - 2) <= 2 * 8 ^ Q := by
    have h2 : 128 * 5 ^ (Q - 2) <= 2 * 8 ^ Q := by
      nlinarith [hle64]
    omega
  have hsumRat' : ((3 * StringFlow.TD1.amaxA Q : Nat) : Rat) =
      (2 * 8 ^ Q : Rat) - 89 * (5 ^ (Q - 2) : Rat) := by
    rw [Nat.cast_sub hgeNat] at hsumRat
    norm_num at hsumRat ⊢
    exact hsumRat
  have h5Rat : (5 ^ Q : Rat) = 25 * (5 ^ (Q - 2) : Rat) := by
    have h := (by exact_mod_cast h5 : ((5 ^ Q : Nat) : Rat) =
      ((25 * 5 ^ (Q - 2) : Nat) : Rat))
    simpa [Nat.cast_mul, Nat.cast_pow] using h
  have h85 : (8 / 5 : Rat) ^ Q =
      ((8 ^ Q : Nat) : Rat) / ((5 ^ Q : Nat) : Rat) := by
    rw [div_pow]
    norm_num
  have h8Rat : (8 ^ Q : Rat) = (5 ^ Q : Rat) * (8 / 5 : Rat) ^ Q := by
    rw [h85]
    field_simp [show (5 ^ Q : Rat) ≠ 0 by positivity]
    push_cast
    ring
  have hpow : ((5 ^ (Q - 2) : Nat) : Rat) ≠ 0 := by positivity
  have h3 : (3 : Rat) ≠ 0 := by norm_num
  have h5Q : (5 ^ Q : Rat) ≠ 0 := by positivity
  calc
    (StringFlow.TD1.amaxA Q : Rat) / (5 ^ Q : Rat)
        = ((2 * 8 ^ Q - 89 * 5 ^ (Q - 2) : Nat) : Rat) /
            (3 * (5 ^ Q : Rat)) := by
            field_simp [h3, h5Q]
            norm_num at hsumRat ⊢
            simpa [mul_comm] using hsumRat
    _ = ((3 * StringFlow.TD1.amaxA Q : Nat) : Rat) /
            (3 * (5 ^ Q : Rat)) := by
            rw [hsumRat]
    _ = ((2 * 8 ^ Q : Rat) - 89 * (5 ^ (Q - 2) : Rat)) /
            (3 * (5 ^ Q : Rat)) := by
            rw [hsumRat']
    _ = (2 * (5 ^ Q : Rat) * (8 / 5 : Rat) ^ Q -
            89 * (5 ^ (Q - 2) : Rat)) /
            (3 * (25 * (5 ^ (Q - 2) : Rat))) := by
            rw [h8Rat, h5Rat]
            field_simp [hpow]
    _ = (2 * (8 / 5 : Rat) ^ Q - 89 / 25) / 3 := by
            field_simp [hpow, h3]
            rw [h5Rat]
            ring_nf

/-- `A_max,5(Q)/5^Q = (4*(8/5)^Q - 29/5)/3`. -/
theorem amaxB_div_eq (Q : Nat) (hQ2 : 2 ≤ Q) :
    (StringFlow.TD1.amaxB Q : Rat) / (5 ^ Q : Rat) =
      (4 * (8 / 5 : Rat) ^ Q - 29 / 5) / 3 := by
  have hS := StringFlow.TD1.three_mul_s3 Q hQ2
  have h5sub : 5 ^ (Q - 1) = 5 * 5 ^ (Q - 2) := by
    have hQ : Q - 1 = (Q - 2) + 1 := by omega
    rw [hQ, Nat.pow_succ]
    ring
  have h4S : 12 * StringFlow.TD1.s3 Q =
      4 * 8 ^ Q - 256 * 5 ^ (Q - 2) := by
    calc
      12 * StringFlow.TD1.s3 Q = 4 * (3 * StringFlow.TD1.s3 Q) := by ring
      _ = 4 * (8 ^ Q - 64 * 5 ^ (Q - 2)) := by rw [hS]
      _ = 4 * 8 ^ Q - 256 * 5 ^ (Q - 2) := by
        rw [Nat.mul_sub_left_distrib]
        ring_nf
  have h4S' : StringFlow.TD1.s3 Q * 12 =
      4 * 8 ^ Q - 256 * 5 ^ (Q - 2) := by
    rw [Nat.mul_comm]
    exact h4S
  have hB : 3 * StringFlow.TD1.amaxB Q = 4 * 8 ^ Q - 145 * 5 ^ (Q - 2) := by
    unfold StringFlow.TD1.amaxB
    calc
      3 * (5 ^ (Q - 1) + 32 * 5 ^ (Q - 2) + 4 * StringFlow.TD1.s3 Q)
          = 3 * 5 ^ (Q - 1) + 96 * 5 ^ (Q - 2) +
              StringFlow.TD1.s3 Q * 12 := by ring_nf
      _ = 3 * 5 ^ (Q - 1) + 96 * 5 ^ (Q - 2) +
              (4 * 8 ^ Q - 256 * 5 ^ (Q - 2)) := by rw [h4S']
      _ = 4 * 8 ^ Q - 145 * 5 ^ (Q - 2) := by
        rw [h5sub]
        have hle64 : 64 * 5 ^ (Q - 2) <= 8 ^ Q :=
          StringFlow.TD1.s3_le_eight Q hQ2
        have hge : 256 * 5 ^ (Q - 2) <= 4 * 8 ^ Q := by
          nlinarith [hle64]
        omega
  have hBsumRat : ((3 * StringFlow.TD1.amaxB Q : Nat) : Rat) =
      ((4 * 8 ^ Q - 145 * 5 ^ (Q - 2) : Nat) : Rat) := by
    exact_mod_cast hB
  have hle64 : 64 * 5 ^ (Q - 2) <= 8 ^ Q :=
    StringFlow.TD1.s3_le_eight Q hQ2
  have hgeNat : 145 * 5 ^ (Q - 2) <= 4 * 8 ^ Q := by
    have h4 : 256 * 5 ^ (Q - 2) <= 4 * 8 ^ Q := by
      nlinarith [hle64]
    omega
  have hBsumRat' : ((3 * StringFlow.TD1.amaxB Q : Nat) : Rat) =
      (4 * 8 ^ Q : Rat) - 145 * (5 ^ (Q - 2) : Rat) := by
    rw [Nat.cast_sub hgeNat] at hBsumRat
    norm_num at hBsumRat ⊢
    exact hBsumRat
  have h5Rat : (5 ^ Q : Rat) = 25 * (5 ^ (Q - 2) : Rat) := by
    have h := (by exact_mod_cast StringFlow.TD1.five_pow_eq_25_mul Q hQ2 :
      ((5 ^ Q : Nat) : Rat) = ((25 * 5 ^ (Q - 2) : Nat) : Rat))
    simpa [Nat.cast_mul, Nat.cast_pow] using h
  have h85 : (8 / 5 : Rat) ^ Q =
      ((8 ^ Q : Nat) : Rat) / ((5 ^ Q : Nat) : Rat) := by
    rw [div_pow]
    norm_num
  have h8Rat : (8 ^ Q : Rat) = (5 ^ Q : Rat) * (8 / 5 : Rat) ^ Q := by
    rw [h85]
    field_simp [show (5 ^ Q : Rat) ≠ 0 by positivity]
    push_cast
    ring
  have hpow : (5 ^ (Q - 2) : Rat) ≠ 0 := by positivity
  have h3 : (3 : Rat) ≠ 0 := by norm_num
  have h5Q : (5 ^ Q : Rat) ≠ 0 := by positivity
  calc
    (StringFlow.TD1.amaxB Q : Rat) / (5 ^ Q : Rat)
        = ((4 * 8 ^ Q - 145 * 5 ^ (Q - 2) : Nat) : Rat) /
            (3 * (5 ^ Q : Rat)) := by
            field_simp [h3, h5Q]
            norm_num at hBsumRat ⊢
            simpa [mul_comm] using hBsumRat
    _ = ((3 * StringFlow.TD1.amaxB Q : Nat) : Rat) /
            (3 * (5 ^ Q : Rat)) := by
            rw [hBsumRat]
    _ = ((4 * 8 ^ Q : Rat) - 145 * (5 ^ (Q - 2) : Rat)) /
            (3 * (5 ^ Q : Rat)) := by
            rw [hBsumRat']
    _ = (4 * (5 ^ Q : Rat) * (8 / 5 : Rat) ^ Q -
            145 * (5 ^ (Q - 2) : Rat)) /
            (3 * (25 * (5 ^ (Q - 2) : Rat))) := by
            rw [h8Rat, h5Rat]
            field_simp [hpow]
    _ = (4 * (8 / 5 : Rat) ^ Q - 29 / 5) / 3 := by
            field_simp [hpow, h3]
            rw [h5Rat]
            ring_nf

/-- The upper-branch A-family subtractive term equals
`A_max,3(Q)/5^Q` divided by `m`. -/
theorem amaxA_div_mul (Q m : Nat) (hQ2 : 2 ≤ Q) (hm : 0 < m) :
    ((2 * (8 / 5 : Rat) ^ Q - 89 / 25) / (3 * (m : Rat))) =
      ((StringFlow.TD1.amaxA Q : Rat) / (5 ^ Q : Rat)) / (m : Rat) := by
  have h3 : (3 : Rat) ≠ 0 := by norm_num
  have hmRat : (m : Rat) ≠ 0 := by positivity
  rw [amaxA_div_eq Q hQ2]
  field_simp [h3, hmRat]

/-- The upper-branch B-family subtractive term equals
`A_max,5(Q)/5^Q` divided by `m`. -/
theorem amaxB_div_mul (Q m : Nat) (hQ2 : 2 ≤ Q) (hm : 0 < m) :
    ((4 * (8 / 5 : Rat) ^ Q - 29 / 5) / (3 * (m : Rat))) =
      ((StringFlow.TD1.amaxB Q : Rat) / (5 ^ Q : Rat)) / (m : Rat) := by
  have h3 : (3 : Rat) ≠ 0 := by norm_num
  have hmRat : (m : Rat) ≠ 0 := by positivity
  rw [amaxB_div_eq Q hQ2]
  field_simp [h3, hmRat]

/-- The power identity `(8/5)^Q * 5^Q = 8^Q`. -/
theorem eight_pow_rat_mul (Q : Nat) :
    (8 / 5 : Rat) ^ Q * (5 ^ Q : Rat) = (8 ^ Q : Rat) := by
  have h85 : (8 / 5 : Rat) ^ Q =
      ((8 ^ Q : Nat) : Rat) / ((5 ^ Q : Nat) : Rat) := by
    rw [div_pow]
    norm_num
  rw [h85]
  field_simp [show (5 ^ Q : Rat) ≠ 0 by positivity]
  push_cast
  ring

/-- A strict upper bound on `M0/m` is exactly `A_req > A_max,3` in
cleared integer form. -/
theorem areqA_gt_amax_of_ratio_lt (Q m M0 : Nat)
    (hm : 0 < m)
    (hR : (M0 : Rat) / (m : Rat) <
      2 * (8 / 5 : Rat) ^ Q -
        ((StringFlow.TD1.amaxA Q : Rat) / (5 ^ Q : Rat)) / (m : Rat)) :
    StringFlow.TD1.areqA Q m M0 > StringFlow.TD1.amaxA Q := by
  have hmRat : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
  have h5 : (5 ^ Q : Rat) ≠ 0 := by positivity
  have hR' : ((5 ^ Q * M0 + StringFlow.TD1.amaxA Q : Nat) : Rat) <
      ((2 * 8 ^ Q * m : Nat) : Rat) := by
    have hR1 : (5 ^ Q : Rat) * (M0 : Rat) <
        2 * (8 / 5 : Rat) ^ Q * (5 ^ Q : Rat) * (m : Rat) -
          (StringFlow.TD1.amaxA Q : Rat) := by
      field_simp [hmRat.ne', h5] at hR
      simpa [mul_comm, mul_left_comm, mul_assoc] using hR
    have hR1' : (5 ^ Q : Rat) * (M0 : Rat) <
        2 * (8 ^ Q : Rat) * (m : Rat) -
          (StringFlow.TD1.amaxA Q : Rat) := by
      nlinarith [hR1, eight_pow_rat_mul Q]
    norm_num at hR1' ⊢
    nlinarith [hR1']
  have hNat : 5 ^ Q * M0 + StringFlow.TD1.amaxA Q < 2 * 8 ^ Q * m := by
    exact_mod_cast hR'
  unfold StringFlow.TD1.areqA
  omega

/-- Equality with `A_max,5` forces the exact ratio equality whose
strict counterpart is the B-family upper branch. -/
theorem areqB_eq_amax_ratio_eq (Q m M0 : Nat) (hm : 0 < m)
    (hEq : StringFlow.TD1.areqB Q m M0 = StringFlow.TD1.amaxB Q) :
    (M0 : Rat) / (m : Rat) =
      4 * (8 / 5 : Rat) ^ Q -
        ((StringFlow.TD1.amaxB Q : Rat) / (5 ^ Q : Rat)) / (m : Rat) := by
  have hmRat : (m : Rat) ≠ 0 := by positivity
  have h5 : (5 ^ Q : Rat) ≠ 0 := by positivity
  have hBpos : 0 < StringFlow.TD1.amaxB Q := by
    unfold StringFlow.TD1.amaxB
    positivity
  have hNat : 5 ^ Q * M0 = 4 * 8 ^ Q * m - StringFlow.TD1.amaxB Q := by
    unfold StringFlow.TD1.areqB at hEq
    omega
  have hge : StringFlow.TD1.amaxB Q <= 4 * 8 ^ Q * m := by
    unfold StringFlow.TD1.areqB at hEq
    omega
  have hNatRat : ((5 ^ Q * M0 : Nat) : Rat) =
      ((4 * 8 ^ Q * m - StringFlow.TD1.amaxB Q : Nat) : Rat) := by
    exact_mod_cast hNat
  have hNatRat' : (5 ^ Q : Rat) * (M0 : Rat) =
      4 * (8 ^ Q : Rat) * (m : Rat) -
        (StringFlow.TD1.amaxB Q : Rat) := by
    rw [Nat.cast_sub hge] at hNatRat
    norm_num at hNatRat ⊢
    exact hNatRat
  have hRat1 : (5 ^ Q : Rat) * (M0 : Rat) =
      4 * (8 / 5 : Rat) ^ Q * (5 ^ Q : Rat) * (m : Rat) -
        (StringFlow.TD1.amaxB Q : Rat) := by
    calc
      (5 ^ Q : Rat) * (M0 : Rat) =
          4 * (8 ^ Q : Rat) * (m : Rat) -
            (StringFlow.TD1.amaxB Q : Rat) := hNatRat'
      _ = 4 * (8 / 5 : Rat) ^ Q * (5 ^ Q : Rat) * (m : Rat) -
            (StringFlow.TD1.amaxB Q : Rat) := by
            rw [← eight_pow_rat_mul Q]
            ring
  field_simp [h5, hmRat]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hRat1

/-- A strict upper bound on `M0/m` excludes the B-family tight value
`A_req = A_max,5`. -/
theorem areqB_ne_amax_of_ratio_lt (Q m M0 : Nat)
    (hm : 0 < m)
    (hR : (M0 : Rat) / (m : Rat) <
      4 * (8 / 5 : Rat) ^ Q -
        ((StringFlow.TD1.amaxB Q : Rat) / (5 ^ Q : Rat)) / (m : Rat)) :
    StringFlow.TD1.areqB Q m M0 ≠ StringFlow.TD1.amaxB Q := by
  intro hEq
  have hEqRat := areqB_eq_amax_ratio_eq Q m M0 hm hEq
  rw [hEqRat] at hR
  exact (lt_irrefl _ hR)

/-- Phase-2 A-family upper branch plus the real rising word supplies
the cleared interval exclusion `A_req > A_max,3`. -/
theorem upperBranchA_areq_gt
    (Q L U m M0 Au Amax : Nat)
    (hUp : StringFlow.TD0.upperBranch 1 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 1 + U)
    (hm : 0 < m) (hQ2 : 2 ≤ Q)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax) :
    StringFlow.TD1.areqA Q m M0 > StringFlow.TD1.amaxA Q := by
  have hRat := upperBranchA_ratio_lt Q L U m M0 Au Amax hUp hT hm
    hAmax hUle hrise hAuLe
  rw [amaxA_div_mul Q m hQ2 hm] at hRat
  exact areqA_gt_amax_of_ratio_lt Q m M0 hm hRat

/-- Phase-2 B-family upper branch plus the real rising word excludes
the tight value `A_req = A_max,5`. -/
theorem upperBranchB_areq_ne
    (Q L U m M0 Au Amax : Nat)
    (hUp : StringFlow.TD0.upperBranch 2 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 2 + U)
    (hm : 0 < m) (hQ2 : 2 ≤ Q)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax) :
    StringFlow.TD1.areqB Q m M0 ≠ StringFlow.TD1.amaxB Q := by
  have hRat := upperBranchB_ratio_lt Q L U m M0 Au Amax hUp hT hm
    hAmax hUle hrise hAuLe
  rw [amaxB_div_mul Q m hQ2 hm] at hRat
  exact areqB_ne_amax_of_ratio_lt Q m M0 hm hRat

/-- Phase-2 A-family closure: the 44.2 upper branch gives
`A_req > A_max,3`, which contradicts the C3 chain interpolation. -/
theorem td1A_phase2_closed
    (Q L U m M0 Au Amax : Nat) (ns ts : List Nat)
    (hUp : StringFlow.TD0.upperBranch 1 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 1 + U)
    (hm : 0 < m) (hQ2 : 2 ≤ Q)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 2 ^ ts.sum = 2 * 8 ^ ts.length)
    (hhead : ∀ a as, ts = a :: as → a = 3)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    False := by
  have hgt := upperBranchA_areq_gt Q L U m M0 Au Amax hUp hT hm hQ2
    hAmax hUle hrise hAuLe
  have hExcl' : StringFlow.TD1.areqA ts.length m
        (StringFlow.GC.chainFirst ns) >
      StringFlow.TD1.amaxA ts.length ∨
    StringFlow.TD1.areqA ts.length m
        (StringFlow.GC.chainFirst ns) <
      StringFlow.TD1.a0 ts.length := by
    left
    simpa [hQlen, hfirst] using hgt
  exact td1A_closed_of_chain ns ts m hc3 hlchain hTchain
    (by rw [hQlen]; exact hQ2) hhead hge hExcl'

/-- Phase-2 B-family closure: the 44.2 upper branch excludes the
tight value `A_max,5`, so the B-family chain cannot close. -/
theorem td1B_phase2_closed
    (Q L U m M0 Au Amax : Nat) (ns ts : List Nat)
    (hUp : StringFlow.TD0.upperBranch 2 Q L m = true)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 2 + U)
    (hm : 0 < m) (hQ2 : 2 ≤ Q)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hUle : U ≤ L)
    (hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au)
    (hAuLe : Au ≤ Amax)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    False := by
  have hne := upperBranchB_areq_ne Q L U m M0 Au Amax hUp hT hm hQ2
    hAmax hUle hrise hAuLe
  have hNe' : StringFlow.TD1.areqB ts.length m
        (StringFlow.GC.chainFirst ns) ≠
      StringFlow.TD1.amaxB ts.length := by
    simpa [hQlen, hfirst] using hne
  exact td1B_closed_eq_amaxB ns ts m hc3 hlchain hTchain
    (by rw [hQlen]; exact hQ2) hhead hge hNe'

/-- From a real `{1,2}` word with `U` twos, the prefix numerator is
bounded by the 44.2 maximum. -/
theorem wordA_le_amax_of_count (w : List Nat) (L U Amax Au : Nat)
    (hwlen : w.length = L)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hAmax : Amax = StringFlow.amaxWord L U)
    (hAu : Au = StringFlow.Word.wordA w)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2) :
    Au ≤ Amax := by
  have h := StringFlow.wordA_le_amaxWord w hok
  rw [hwlen, hUcount, ← hAmax, ← hAu] at h
  exact h

/-- The real rising equation for a phase-2 word with weight
`S = L + U`. -/
theorem rising_equation_of_phase2_word (w : List Nat) (L U m M0 Au : Nat)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = L + U)
    (hAu : Au = StringFlow.Word.wordA w)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0) :
    2 ^ (L + U) * M0 = 5 ^ L * m + Au := by
  have h := StringFlow.rising_equation_of_wordValid w m M0 hvalid hM0
  rw [hwS, hwlen, ← hAu] at h
  exact h

/-- All phase-2 inputs packaged as one datum.  The 44.2 upper branch
is assumed already certified; the frame-A + QB-8 wrapper can produce
it from the B1/B2 + G5' rational checks. -/
structure Td0Data2 (b Q L U m M0 Au Amax : Nat) (ns ts w : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hQ2 : 2 ≤ Q
  hUle : U ≤ L
  hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U
  hwlen : w.length = L
  hwS : StringFlow.wordWeight w = L + U
  hUcount : (w.filter (fun t => t = 2)).length = U
  hAmax : Amax = StringFlow.amaxWord L U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hAu : Au = StringFlow.Word.wordA w
  hm : 0 < m
  hvalid : StringFlow.Word.wordValid w m
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hUp : StringFlow.TD0.upperBranch b Q L m = true

/-- Phase-2 TD-0 closure from one packaged datum. -/
theorem td0_phase2_closed (b Q L U m M0 Au Amax : Nat) (ns ts w : List Nat)
    (h : Td0Data2 b Q L U m M0 Au Amax ns ts w) : False := by
  rcases h.hb with rfl | rfl
  · have hUp : StringFlow.TD0.upperBranch 1 Q L m = true := by
      simpa using h.hUp
    have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 1 + U := by
      simpa using h.hT
    have hAuLe : Au ≤ Amax :=
      wordA_le_amax_of_count w L U Amax Au h.hwlen h.hUcount h.hAmax h.hAu h.hok
    have hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au :=
      rising_equation_of_phase2_word w L U m M0 Au h.hwlen h.hwS h.hAu
        h.hvalid h.hM0
    exact td1A_phase2_closed Q L U m M0 Au Amax ns ts hUp hT h.hm h.hQ2
      h.hAmax h.hUle hrise hAuLe h.hQlen h.hc3 h.hfirst h.hlchain
      (by simpa using h.hTchain) (by simpa using h.hhead) h.hge
  · have hUp : StringFlow.TD0.upperBranch 2 Q L m = true := by
      simpa using h.hUp
    have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + 2 + U := by
      simpa using h.hT
    have hAuLe : Au ≤ Amax :=
      wordA_le_amax_of_count w L U Amax Au h.hwlen h.hUcount h.hAmax h.hAu h.hok
    have hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + Au :=
      rising_equation_of_phase2_word w L U m M0 Au h.hwlen h.hwS h.hAu
        h.hvalid h.hM0
    exact td1B_phase2_closed Q L U m M0 Au Amax ns ts hUp hT h.hm h.hQ2
      h.hAmax h.hUle hrise hAuLe h.hQlen h.hc3 h.hfirst h.hlchain
      (by simpa using h.hTchain) (by simpa using h.hhead) h.hge

/-- Phase-2 QB-8 cycle inputs before the 44.2 upper branch is
certified.  The wrapper derives `upperBranch` from B1/B2 + G5'. -/
structure Qb8Cycle2 (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hfeas : StringFlow.TD1.feasible64 b Q L = true
  hU : StringFlow.uReq b Q L = U
  hB1 : m < 617 → m = 201 ∧ L + Q < 59
  hwlen : w.length = L
  hwS : StringFlow.wordWeight w = L + U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hS26 : 26 ≤ L + U

/-- From a phase-2 QB-8 cycle, construct the `Td0Data2` datum. -/
theorem qb8_cycle2_to_td0Data2 (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Cycle2 b Q L U m M0 w ns ts) :
    Td0Data2 b Q L U m M0 (StringFlow.Word.wordA w)
      (StringFlow.amaxWord L U) ns ts w := by
  have hUcount : (w.filter (fun t => t = 2)).length = U := by
    have hfs := StringFlow.filter_count_eq_wordWeight_sub_length w h.hok
    rw [h.hwS, h.hwlen] at hfs
    have hsub : (L + U) - L = U := by
      rw [Nat.add_comm]
      exact Nat.add_sub_cancel U L
    rw [hsub] at hfs
    exact hfs
  have hm : 0 < m := lt_of_lt_of_le (by norm_num : 0 < 7) h.hm7
  have hrange := StringFlow.TD1.feasible64_range b Q L h.hfeas
  have hP9 : 9 ≤ L + Q := hrange.1
  have hP205 : L + Q < 205 := hrange.2
  have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U :=
    StringFlow.TD1.uReq_T_of_feasible b Q L U h.hfeas h.hU
  have hUle : U ≤ L :=
    StringFlow.TD1.uReq_le_L_of_feasible b Q L U h.hb h.hfeas h.hU
  have hQ2 : 2 ≤ Q := by
    have hQ8 := StringFlow.TD1.feasible64_Q_ge_8 b Q L h.hfeas
    omega
  have hmt : (m : Rat) * StringFlow.TD1.tRat (L + Q) ≥ (8 / 3 : Rat) :=
    StringFlow.TD1.phase2_mt_ge_of_b2 m (L + Q) hP9 hP205 h.hB1
  have hltpow : 5 ^ (L + Q) < 2 ^ StringFlow.tCeil (L + Q) :=
    StringFlow.tCeil_pow_lt (L + Q) hP9 hP205
  have hUp : StringFlow.TD0.upperBranch b Q L m = true :=
    StringFlow.TD0.upperBranch_of_mt_ge b Q L m h.hb hm hltpow hmt
  exact {
    hb := h.hb
    hQ2 := hQ2
    hUle := hUle
    hT := hT
    hwlen := h.hwlen
    hwS := h.hwS
    hUcount := hUcount
    hAmax := rfl
    hok := h.hok
    hAu := rfl
    hm := hm
    hvalid := h.hvalid
    hM0 := h.hM0
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hfirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge
    hUp := hUp }

/-- Phase-2 QB-8 closure: no phase-2 QB-8 cycle exists. -/
theorem qb8_phase2_closed (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Cycle2 b Q L U m M0 w ns ts) : False :=
  td0_phase2_closed b Q L U m M0 (StringFlow.Word.wordA w)
    (StringFlow.amaxWord L U) ns ts w (qb8_cycle2_to_td0Data2 b Q L U m M0 w ns ts h)

/-- Real orbit inputs for a frame-A QB-8 cycle.  The remaining
analytic bridge is to certify these fields from the actual orbit. -/
structure Qb8Orbit (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hfeas : StringFlow.TD1.feasible64 b Q L = true
  hU : StringFlow.uReq b Q L = U
  hSfirst : StringFlow.firstC3S 1000 m = L + U
  h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2
  hwlen : w.length = L
  hwS : StringFlow.wordWeight w = L + U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- From a frame-A QB-8 orbit, construct the phase-2 datum.  The
`m < 617` B1 case is closed by `basin_617_sharp` and
`phase2_b1_condition_of_201`. -/
theorem qb8_cycle2_of_orbit
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Orbit b Q L U m M0 w ns ts) :
    Qb8Cycle2 b Q L U m M0 w ns ts := by
  have hB1 : m < 617 → m = 201 ∧ L + Q < 59 := by
    intro hm617
    have hS : 26 ≤ StringFlow.firstC3S 1000 m := by
      rw [h.hSfirst]
      exact h.hS26
    have hm201 : m = 201 := StringFlow.TD1.basin_617_sharp m h.hm7 hm617 h.hadm hS
    have h201 := h.h201 hm201
    rcases h201 with ⟨hL20, hU6, rfl⟩
    have hU' : StringFlow.uReq 2 Q L = 6 := by
      simpa [hU6] using h.hU
    exact StringFlow.TD1.phase2_b1_condition_of_201 m Q L hm201 h.hQ8 hL20 hU' hm617
  exact {
    hb := h.hb
    hm7 := h.hm7
    hfeas := h.hfeas
    hU := h.hU
    hB1 := hB1
    hwlen := h.hwlen
    hwS := h.hwS
    hok := h.hok
    hvalid := h.hvalid
    hM0 := h.hM0
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hfirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge
    hS26 := h.hS26 }

/-- Frame-A + QB-8 orbit closure: no phase-2 QB-8 orbit exists. -/
theorem td0_of_qb8_orbit
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Orbit b Q L U m M0 w ns ts) : False :=
  qb8_phase2_closed b Q L U m M0 w ns ts
    (qb8_cycle2_of_orbit b Q L U m M0 w ns ts h)

/-- The `m = 201` B1 orbit is a fully constructed `Qb8Orbit`: the
word shape and first-C3 weight come from `b1_orbit`/`b1_length`/
`b1_count_two`/`b1_weight`, and only the C3 chain fields remain as
inputs. -/
theorem qb8_orbit_of_201
    (Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hm : m = 201)
    (hQ8 : 8 ≤ Q)
    (hfeas : StringFlow.TD1.feasible64 2 Q L = true)
    (hU : StringFlow.uReq 2 Q L = U)
    (hw : w = StringFlow.TD1.b1Word)
    (hwlen : w.length = L)
    (hwS : StringFlow.wordWeight w = L + U)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hfirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    Qb8Orbit 2 Q L U m M0 w ns ts := by
  have hS26eq : L + U = 26 := by
    rw [← hwS, hw]
    exact StringFlow.TD1.b1_weight
  have hSfirst : StringFlow.firstC3S 1000 m = L + U := by
    have h201or := StringFlow.TD1.b1_orbit
    have hhit : (StringFlow.firstC3H 100 201).1 = true := by
      rw [h201or.2]
    have hsame : StringFlow.firstC3S 1000 201 = StringFlow.firstC3S 100 201 :=
      StringFlow.TD1.firstC3S_of_hit 100 1000 201 (by norm_num) hhit
    have hS : StringFlow.firstC3S 100 201 = 26 := by
      unfold StringFlow.firstC3S
      rw [h201or.2]
    have hS1000 : StringFlow.firstC3S 1000 201 = 26 := by
      rw [hsame, hS]
    rw [hm, hS1000, hS26eq]
  have h201field : m = 201 → L = 20 ∧ U = 6 ∧ 2 = 2 := by
    intro _
    have hL20 : L = 20 := by
      have hlen : StringFlow.TD1.b1Word.length = 20 :=
        StringFlow.TD1.b1_length
      rw [hw] at hwlen
      omega
    have hU6 : U = 6 := by
      have hweight : StringFlow.wordWeight w = 26 := by
        rw [hw]
        exact StringFlow.TD1.b1_weight
      omega
    constructor
    · exact hL20
    · constructor
      · exact hU6
      · rfl
  exact {
    hb := Or.inr rfl
    hm7 := by rw [hm]; norm_num
    hmle := by rw [hm]; norm_num
    hadm := by rw [hm]; norm_num [StringFlow.admissible]
    hQ8 := hQ8
    hS26 := by rw [hS26eq]
    hfeas := hfeas
    hU := hU
    hSfirst := hSfirst
    h201 := h201field
    hwlen := hwlen
    hwS := hwS
    hok := hok
    hvalid := hvalid
    hM0 := hM0
    hQlen := hQlen
    hc3 := hc3
    hfirst := hfirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }

/-- A real first-C3 orbit: the exact word is `firstC3WordAux 1000 m`,
and the first-C3 hit records its weight.  The `{1,2}` word shape,
`wordWeight = L+U`, and word validity are derived from
`firstC3WordAux_ok_of_hit`, `firstC3WordAux_weight_of_hit`, and
`firstC3WordAux_valid_of_hit`. -/
structure FirstC3Orbit (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hfeas : StringFlow.TD1.feasible64 b Q L = true
  hU : StringFlow.uReq b Q L = U
  hfirst : StringFlow.firstC3H 1000 m = (true, L + U)
  hw : w = StringFlow.TD1.firstC3WordAux 1000 m
  hwlen : w.length = L
  hM0 : StringFlow.Word.wordOrbit w m = M0
  h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hchainFirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- Stage-one `Td0Data` construction from a real first-C3 orbit with
`S <= 25`: the remaining stage-one inputs are the family last step,
the threshold residue bounds, and the table totals. -/
theorem td0_data_of_firstC3_orbit_stage1
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts)
    (hS25 : L + U ≤ 25)
    (hlast : StringFlow.Word.wordLast w = b)
    (hmlt : m < StringFlow.tableM0 b Q L) :
    Td0Data b Q L (StringFlow.tCeil (L + Q)) m M0 ns ts w := by
  have hL1 : 1 ≤ L := StringFlow.TD1.feasible64_L_ge_1 b Q L h.hfeas
  have hQ50 : Q ≤ 50 :=
    StringFlow.TD1.stage1_Q_le_50 b Q L h.hfeas (by simpa [h.hU] using hS25)
  have hL25 : L ≤ 25 :=
    StringFlow.TD1.stage1_L_le_25 b Q L (by simpa [h.hU] using hS25)
  have hfeas : StringFlow.feasible b Q L = true :=
    StringFlow.TD1.feasible_of_feasible64 b Q L h.hfeas hQ50 hL25
      (by simpa [h.hU] using hS25)
  have hQ2 : 2 ≤ Q := le_trans (by norm_num : 2 ≤ 8) h.hQ8
  have hhit : (StringFlow.firstC3H 1000 m).1 = true := by
    rw [h.hfirst]
  have hoddm : m % 2 = 1 := h.hadm.2.1
  have hok : ∀ t ∈ w, t = 1 ∨ t = 2 := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_ok_of_hit 1000 m hhit
  have hvalid : StringFlow.Word.wordValid w m := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_valid_of_hit 1000 m hoddm hhit
  have hweight : StringFlow.wordWeight w = L + U := by
    rw [h.hw]
    have hw' := StringFlow.TD1.firstC3WordAux_weight_of_hit 1000 m hhit
    unfold StringFlow.firstC3S at hw'
    rw [h.hfirst] at hw'
    exact hw'
  have hb1 : 1 ≤ b := by
    rcases h.hb with rfl | rfl <;> norm_num
  have hb2 : b ≤ 2 := by
    rcases h.hb with rfl | rfl <;> norm_num
  have hspec := StringFlow.table_spec b Q L hb1 hb2 hfeas h.hQ8 hQ50 hL1 hL25
  rcases hspec with ⟨_hUt, hSt, _hMod, _hTarget, _hInv⟩
  have hSt' : StringFlow.tableS b Q L = L + U := by
    rw [h.hU] at hSt
    exact hSt
  have htsum : ts.sum = 3 * Q + b := by
    rcases h.hb with rfl | rfl
    · have hs := sum_eq_of_two_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
    · have hs := sum_eq_of_four_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
  have hTceq : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U :=
    StringFlow.TD1.uReq_T_of_feasible b Q L U h.hfeas h.hU
  have hTT : StringFlow.tableS b Q L + ts.sum = StringFlow.tCeil (L + Q) := by
    rw [hSt', htsum, hTceq]
    omega
  have hD : StringFlow.tableD b Q L =
      2 ^ StringFlow.tCeil (L + Q) - 5 ^ (L + Q) :=
    StringFlow.tableD_spec b Q L hb1 hb2 hfeas h.hQ8 hQ50 hL1 hL25
  have hmmod : m < StringFlow.tableMod b Q L :=
    StringFlow.TD1.stage1_hmmod_of_hmlt b Q L m hfeas hmlt
  have hwS : StringFlow.wordWeight w = StringFlow.tableS b Q L :=
    hweight.trans hSt'.symm
  exact {
    hb := h.hb
    hQ8 := h.hQ8
    hQ50 := hQ50
    hL1 := hL1
    hL25 := hL25
    hfeas := hfeas
    hwlen := h.hwlen
    hwS := hwS
    hlast := hlast
    hok := hok
    hm7 := h.hm7
    hmmod := hmmod
    hmlt := hmlt
    hvalid := hvalid
    hM0 := h.hM0
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hchainFirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hQ2 := hQ2
    hhead := h.hhead
    hge := h.hge
    hTT := hTT
    hD := hD }

/-- A real first-C3 orbit supplies a `Qb8Orbit`; the exact word
theorems above remove `hok`/`hwS`/`hSfirst` from the input. -/
theorem qb8_orbit_of_firstC3
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have hhit : (StringFlow.firstC3H 1000 m).1 = true := by
    rw [h.hfirst]
  have hSfirst : StringFlow.firstC3S 1000 m = L + U := by
    unfold StringFlow.firstC3S
    simp [h.hfirst]
  have hok : ∀ t ∈ w, t = 1 ∨ t = 2 := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_ok_of_hit 1000 m hhit
  have hwS : StringFlow.wordWeight w = L + U := by
    rw [h.hw]
    have hweight := StringFlow.TD1.firstC3WordAux_weight_of_hit 1000 m hhit
    rw [hweight, hSfirst]
  have hvalid : StringFlow.Word.wordValid w m := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_valid_of_hit 1000 m h.hadm.2.1 hhit
  exact {
    hb := h.hb
    hm7 := h.hm7
    hmle := h.hmle
    hadm := h.hadm
    hQ8 := h.hQ8
    hS26 := h.hS26
    hfeas := h.hfeas
    hU := h.hU
    hSfirst := hSfirst
    h201 := h.h201
    hwlen := h.hwlen
    hwS := hwS
    hok := hok
    hvalid := hvalid
    hM0 := h.hM0
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hchainFirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge }

/-- A real first-C3 word plus the analytic orbit data supplies a
`FirstC3Orbit` datum; `hfirst`/`hw` are derived from the word. -/
theorem firstC3_orbit_of_firstWord
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hb : b = 1 ∨ b = 2)
    (hm7 : 7 ≤ m) (hmle : m ≤ 10 ^ 6)
    (hadm : StringFlow.admissible m)
    (hQ8 : 8 ≤ Q) (hS26 : 26 ≤ L + U)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L)
    (h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2)
    (hne : w ≠ [])
    (hwlen : w.length = L)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hchainFirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    FirstC3Orbit b Q L U m M0 w ns ts := by
  have hwordOK : StringFlow.Word.wordOK w := by
    exact StringFlow.TD1.wordOK_of_mem_two w hok
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    rcases hok t ht with rfl | rfl <;> omega
  have hfirstWord : StringFlow.Word.wordFirst w m :=
    StringFlow.Word.wordFirst_of_wordValid w m hwordOK hpos hvalid hend
  have hhitlen : StringFlow.firstC3H w.length m = (true, StringFlow.wordWeight w) :=
    StringFlow.TD1.firstC3H_of_wordFirst w m hok hfirstWord
  have hword : StringFlow.TD1.firstC3WordAux w.length m = w :=
    StringFlow.TD1.firstC3WordAux_of_wordFirst w m hok hfirstWord
  have hhit : (StringFlow.firstC3H w.length m).1 = true := by
    rw [hhitlen]
  have hmono := StringFlow.TD1.firstC3H_mono w.length m (1000 - w.length) hhit
  have hsum : w.length + (1000 - w.length) = 1000 := by omega
  rw [hsum] at hmono
  have h1000 : StringFlow.firstC3H 1000 m = (true, StringFlow.wordWeight w) := by
    rw [hmono, hhitlen]
  have hfs : U = StringFlow.wordWeight w - L := by
    rw [← hUcount, ← hwlen]
    exact StringFlow.filter_count_eq_wordWeight_sub_length w hok
  have hle : L ≤ StringFlow.wordWeight w := by
    rw [← hwlen]
    exact StringFlow.wordWeight_ge_length w hpos
  have hwS : StringFlow.wordWeight w = L + U := by omega
  have hfirst : StringFlow.firstC3H 1000 m = (true, L + U) := by
    rw [h1000, hwS]
  have hS1000 : StringFlow.firstC3S 1000 m = L + U := by
    unfold StringFlow.firstC3S
    rw [hfirst]
  have hS64 : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m hm7 hmle hadm
    rw [hS1000] at hb
    exact hb
  have hlenpos : 0 < w.length := by
    cases w with
    | nil => contradiction
    | cons t ts => simp
  have hL1 : 1 ≤ L := by omega
  have hfeas : StringFlow.TD1.feasible64 b Q L = true :=
    StringFlow.TD1.feasible64_of_cycle_params b Q L U hb hQ8 hL1 hT hU1 hS64
  have hU : StringFlow.uReq b Q L = U :=
    StringFlow.TD1.uReq_eq_of_tCeil b Q L U hT
  have hs := StringFlow.TD1.firstC3WordAux_stable_of_hit w.length m
    (1000 - w.length) hhit
  rw [hsum] at hs
  have hw : w = StringFlow.TD1.firstC3WordAux 1000 m := by
    rw [hs, hword]
  exact {
    hb := hb
    hm7 := hm7
    hmle := hmle
    hadm := hadm
    hQ8 := hQ8
    hS26 := hS26
    hfeas := hfeas
    hU := hU
    hfirst := hfirst
    hw := hw
    hwlen := hwlen
    hM0 := hM0
    h201 := h201
    hQlen := hQlen
    hc3 := hc3
    hchainFirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }

/-- The first-C3 weight of a real first-C3 word is exactly `L + U`
at fuel `1000`. -/
theorem firstC3S_1000_of_firstWord (w : List Nat) (m L U : Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hwlen : w.length = L) :
    StringFlow.firstC3S 1000 m = L + U := by
  have hwordOK : StringFlow.Word.wordOK w := StringFlow.TD1.wordOK_of_mem_two w hok
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    rcases hok t ht with rfl | rfl <;> omega
  have hfirstWord : StringFlow.Word.wordFirst w m :=
    StringFlow.Word.wordFirst_of_wordValid w m hwordOK hpos hvalid hend
  have hhitlen : StringFlow.firstC3H w.length m = (true, StringFlow.wordWeight w) :=
    StringFlow.TD1.firstC3H_of_wordFirst w m hok hfirstWord
  have hhit : (StringFlow.firstC3H w.length m).1 = true := by rw [hhitlen]
  have hmono := StringFlow.TD1.firstC3H_mono w.length m (1000 - w.length) hhit
  have hsum : w.length + (1000 - w.length) = 1000 := by omega
  rw [hsum] at hmono
  have h1000 : StringFlow.firstC3H 1000 m = (true, StringFlow.wordWeight w) := by
    rw [hmono, hhitlen]
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  unfold StringFlow.firstC3S
  rw [h1000, hwS]

/-- Phase-2 closure from a real first-C3 orbit datum. -/
theorem td0_of_firstC3_orbit (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_firstC3 b Q L U m M0 w ns ts h)

/-- Phase-2 closure directly from a real first-C3 word plus the
analytic orbit data. -/
theorem td0_of_firstWord_orbit
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hb : b = 1 ∨ b = 2)
    (hm7 : 7 ≤ m) (hmle : m ≤ 10 ^ 6)
    (hadm : StringFlow.admissible m)
    (hQ8 : 8 ≤ Q) (hS26 : 26 ≤ L + U)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L)
    (h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2)
    (hne : w ≠ [])
    (hwlen : w.length = L)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hchainFirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) : False :=
  td0_of_firstC3_orbit b Q L U m M0 w ns ts
    (firstC3_orbit_of_firstWord b Q L U m M0 w ns ts hok hvalid hend hfuel
      hUcount hb hm7 hmle hadm hQ8 hS26 hT hU1 h201 hne hwlen hM0 hQlen hc3
      hchainFirst hlchain hTchain hhead hge)

/-- `(16*k) % 32` is `16` or `0` according to the parity of `k`. -/
theorem mul_sixteen_mod_thirty_two (k : Nat) :
    (16 * k) % 32 = 16 * (k % 2) := by
  have h01 : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
  rcases h01 with h0 | h1
  · have hsplit : k = 2 * (k / 2) := by
      have hd := Nat.div_add_mod k 2
      rw [h0] at hd
      omega
    rw [hsplit]
    have h32 : 16 * (2 * (k / 2)) = 32 * (k / 2) := by ring
    rw [h32]
    simp
  · have hsplit : k = 2 * (k / 2) + 1 := by
      have hd := Nat.div_add_mod k 2
      rw [h1] at hd
      omega
    rw [hsplit]
    have h32 : 16 * (2 * (k / 2) + 1) = 32 * (k / 2) + 16 := by ring
    rw [h32]
    rw [Nat.add_mod]
    simp [h1]

/-- Residue `3 mod 80` forces `5M+1` divisible by `16`. -/
theorem mod16_zero_of_mod80_three (M0 : Nat) (h : M0 % 80 = 3) :
    (5 * M0 + 1) % 16 = 0 := by
  have hdec : M0 = 80 * (M0 / 80) + 3 := by
    have hd := Nat.div_add_mod M0 80
    rw [h] at hd
    omega
  rw [hdec]
  have hlin : 5 * (80 * (M0 / 80) + 3) + 1 = 16 * (25 * (M0 / 80) + 1) := by
    omega
  rw [hlin]
  rw [Nat.mul_mod]
  simp

/-- Residue `43 mod 80` makes `5M+1` not divisible by `32`. -/
theorem mod32_ne_zero_of_mod80_forty_three (M0 : Nat) (h : M0 % 80 = 43) :
    (5 * M0 + 1) % 32 ≠ 0 := by
  have hdec : M0 = 80 * (M0 / 80) + 43 := by
    have hd := Nat.div_add_mod M0 80
    rw [h] at hd
    omega
  rw [hdec]
  have hlin : 5 * (80 * (M0 / 80) + 43) + 1 =
      32 * (12 * (M0 / 80) + 6) + (16 * (M0 / 80) + 24) := by omega
  rw [hlin]
  rw [Nat.add_mod]
  have h32a : (32 * (12 * (M0 / 80) + 6)) % 32 = 0 := by
    rw [Nat.mul_mod]
    simp
  rw [h32a]
  simp
  rw [Nat.add_mod]
  have h16k := mul_sixteen_mod_thirty_two (M0 / 80)
  rw [h16k]
  have h24 : 24 % 32 = 24 := by decide
  rw [h24]
  have h01 : (M0 / 80) % 2 = 0 ∨ (M0 / 80) % 2 = 1 := Nat.mod_two_eq_zero_or_one (M0 / 80)
  rcases h01 with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num

/-- Residue `19 mod 80` forces `5M+1` divisible by `16`. -/
theorem mod16_zero_of_mod80_nineteen (M0 : Nat) (h : M0 % 80 = 19) :
    (5 * M0 + 1) % 16 = 0 := by
  have hdec : M0 = 80 * (M0 / 80) + 19 := by
    have hd := Nat.div_add_mod M0 80
    rw [h] at hd
    omega
  rw [hdec]
  have hlin : 5 * (80 * (M0 / 80) + 19) + 1 = 16 * (25 * (M0 / 80) + 6) := by
    omega
  rw [hlin]
  rw [Nat.mul_mod]
  simp

/-- Residue `59 mod 80` makes `5M+1` not divisible by `32`. -/
theorem mod32_ne_zero_of_mod80_fifty_nine (M0 : Nat) (h : M0 % 80 = 59) :
    (5 * M0 + 1) % 32 ≠ 0 := by
  have hdec : M0 = 80 * (M0 / 80) + 59 := by
    have hd := Nat.div_add_mod M0 80
    rw [h] at hd
    omega
  rw [hdec]
  have hlin : 5 * (80 * (M0 / 80) + 59) + 1 =
      32 * (12 * (M0 / 80) + 9) + (16 * (M0 / 80) + 8) := by omega
  rw [hlin]
  rw [Nat.add_mod]
  have h32a : (32 * (12 * (M0 / 80) + 9)) % 32 = 0 := by
    rw [Nat.mul_mod]
    simp
  rw [h32a]
  simp
  rw [Nat.add_mod]
  have h16k := mul_sixteen_mod_thirty_two (M0 / 80)
  rw [h16k]
  have h8 : 8 % 32 = 8 := by decide
  rw [h8]
  have h01 : (M0 / 80) % 2 = 0 ∨ (M0 / 80) % 2 = 1 := Nat.mod_two_eq_zero_or_one (M0 / 80)
  rcases h01 with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num

/-- 52.6, head weight `3`: the exact mod 80 residue of the first C3
endpoint, given the last rise step. -/
theorem word_endpoint_mod80_head_three (w : List Nat) (x : Nat)
    (hvalid : StringFlow.Word.wordValid w x)
    (hend : StringFlow.Word.wordOrbit w x % 8 = 3)
    (hmax : (5 * StringFlow.Word.wordOrbit w x + 1) % 16 ≠ 0) :
    (StringFlow.Word.wordLast w = 1 → StringFlow.Word.wordOrbit w x % 80 = 43) ∧
    (StringFlow.Word.wordLast w = 2 → StringFlow.Word.wordOrbit w x % 80 = 59) := by
  have h80 := StringFlow.Word.word_endpoint_mod80 w x hvalid hend
  constructor
  · intro hlast
    rcases h80.1 hlast with h3 | h43
    · exfalso
      exact hmax (mod16_zero_of_mod80_three (StringFlow.Word.wordOrbit w x) h3)
    · exact h43
  · intro hlast
    rcases h80.2 hlast with h19 | h59
    · exfalso
      exact hmax (mod16_zero_of_mod80_nineteen (StringFlow.Word.wordOrbit w x) h19)
    · exact h59

/-- 52.6, head weight at least `4` (phase 2: `5`): the exact mod 80
residue of the first C3 endpoint, given the last rise step. -/
theorem word_endpoint_mod80_head_five (w : List Nat) (x : Nat)
    (hvalid : StringFlow.Word.wordValid w x)
    (hend : StringFlow.Word.wordOrbit w x % 8 = 3)
    (hdiv : (5 * StringFlow.Word.wordOrbit w x + 1) % 32 = 0) :
    (StringFlow.Word.wordLast w = 1 → StringFlow.Word.wordOrbit w x % 80 = 3) ∧
    (StringFlow.Word.wordLast w = 2 → StringFlow.Word.wordOrbit w x % 80 = 19) := by
  have h80 := StringFlow.Word.word_endpoint_mod80 w x hvalid hend
  constructor
  · intro hlast
    rcases h80.1 hlast with h3 | h43
    · exact h3
    · exfalso
      exact (mod32_ne_zero_of_mod80_forty_three (StringFlow.Word.wordOrbit w x) h43) hdiv
  · intro hlast
    rcases h80.2 hlast with h19 | h59
    · exact h19
    · exfalso
      exact (mod32_ne_zero_of_mod80_fifty_nine (StringFlow.Word.wordOrbit w x) h59) hdiv

/-- The analytic bridge of phase 2: the upper power bound
`2^T < 2 * 5^P` (i.e. `T < P log2 5 + 1`), the B0 range `P < 205`,
and the last-step rigidity bounds on `U`.  It is supplied by
`phase2Bridge_of_cycle2` from `feasible64`/`uReq`. -/
def Phase2Bridge (b Q L U : Nat) (ts : List Nat) : Prop :=
  (2 ^ ((L + U) + ts.sum) < 2 * 5 ^ (L + Q)) ∧
  (L + Q < 205) ∧
  (if b = 1 then U ≤ L - 1 else 1 ≤ U)

/-- A phase-2 QB-8 cycle supplies every analytic field of
`Phase2Bridge`: the B0 `P` range and the strict `U` bounds come from
`feasible64`, and the upper power bound is the upper half of the
ceiling identity (`tCeil_pow_two_lt`). -/
theorem phase2Bridge_of_cycle2
    (b Q L U : Nat) (ts : List Nat)
    (hb : b = 1 ∨ b = 2)
    (hfeas : StringFlow.TD1.feasible64 b Q L = true)
    (hU : StringFlow.uReq b Q L = U)
    (hQlen : ts.length = Q)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum) :
    Phase2Bridge b Q L U ts := by
  have hrange := StringFlow.TD1.feasible64_range b Q L hfeas
  have hP9 : 9 ≤ L + Q := hrange.1
  have hP205 : L + Q < 205 := hrange.2
  have hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L :=
    StringFlow.TD1.uReq_bounds_of_feasible b Q L U hfeas hU
  have hsum : ts.sum = 3 * Q + b := by
    rcases hb with rfl | rfl
    · have hsum' := sum_eq_of_two_mul_eight ts (by simpa using hTchain)
      rw [hQlen] at hsum'
      omega
    · have hsum' := sum_eq_of_four_mul_eight ts (by simpa using hTchain)
      rw [hQlen] at hsum'
      omega
  have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U :=
    StringFlow.TD1.uReq_T_of_feasible b Q L U hfeas hU
  have hTtot : (L + U) + ts.sum = StringFlow.tCeil (L + Q) := by omega
  have hpow : 2 ^ ((L + U) + ts.sum) < 2 * 5 ^ (L + Q) := by
    rw [hTtot]
    exact StringFlow.tCeil_pow_two_lt (L + Q) hP9 hP205
  constructor
  · exact hpow
  · constructor
    · exact hP205
    · rcases hb with rfl | rfl
      · simpa using hU1
      · exact hU1.1

/-- Every packaged phase-2 QB-8 cycle carries `Phase2Bridge`. -/
theorem phase2Bridge_of_qb8_cycle2
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Cycle2 b Q L U m M0 w ns ts) :
    Phase2Bridge b Q L U ts :=
  phase2Bridge_of_cycle2 b Q L U ts h.hb h.hfeas h.hU h.hQlen h.hTchain

/-- A real phase-2 QB-8 cycle: the actual first-C3 word plus the
52.7 length/weight matching data and the C3 chain.  A real
`FirstC3Orbit` supplies every field via `real_cycle_of_firstC3_orbit`;
the only upstream input left is the construction of `FirstC3Orbit`
from a frame-A QB-8 cycle. -/
structure RealQb8Cycle (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hfuel : w.length ≤ 1000
  hUcount : (w.filter (fun t => t = 2)).length = U
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hbridge : Phase2Bridge b Q L U ts
  hne : w ≠ []
  hwlen : w.length = L
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hQlen : ts.length = Q
  hmax : StringFlow.GC.c3ExactMax ns ts
  hchainFirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- A real phase-2 QB-8 cycle is impossible. -/
theorem td0_of_real_cycle (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) : False := by
  rcases h with ⟨hok, hvalid, hend, hfuel, hUcount, hb, hm7, hmle, hadm,
    hQ8, hS26, hbridge, hne, hwlen, hM0, hQlen, hmax,
    hchainFirst, hlchain, hTchain, hhead, hge⟩
  rcases hbridge with ⟨hTpow, hP205, hU1⟩
  have hc3' : StringFlow.GC.c3Exact ns ts :=
    StringFlow.GC.c3Exact_of_c3ExactMax ns ts hmax
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact hne hnil
    omega
  have hP9 : 9 ≤ L + Q := by omega
  have hTle : (L + U) + ts.sum ≤ StringFlow.tCeil (L + Q) :=
    StringFlow.tCeil_ge_of_pow_two_lt (L + Q) ((L + U) + ts.sum) hP9 hP205 hTpow
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  have hUle : U ≤ L := by
    have hle : (w.filter (fun t => t = 2)).length ≤ w.length :=
      List.length_filter_le (fun t => t = 2) w
    rwa [hUcount, hwlen] at hle
  have hU1full : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L := by
    rcases hb with rfl | rfl
    · simpa using hU1
    · exact ⟨hU1, hUle⟩
  have hrise0 := StringFlow.rising_equation_of_wordValid w m M0 hvalid hM0
  have hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + StringFlow.Word.wordA w := by
    rw [hwS, hwlen] at hrise0
    exact hrise0
  have hchain0 := StringFlow.GC.c3_chain_closed_form ns ts hc3'
  have hchain : 2 ^ ts.sum * m = 5 ^ Q * M0 + StringFlow.GC.chainA ts := by
    rw [hlchain, hchainFirst, hQlen] at hchain0
    exact hchain0
  have hne_ts : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    omega
  have hA : 0 < StringFlow.GC.chainA ts := StringFlow.GC.chainA_pos ts hne_ts
  have hgeT : StringFlow.tCeil (L + Q) ≤ (L + U) + ts.sum :=
    StringFlow.tCeil_le_total_of_cycle L Q (L + U) ts.sum m M0
      (StringFlow.Word.wordA w) (StringFlow.GC.chainA ts) hrise hchain hA hP9 hP205
  have hTsum : (L + U) + ts.sum = StringFlow.tCeil (L + Q) := by omega
  have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U :=
    tCeil_eq_of_chain_sum b Q L U ts hb hQlen hTchain hTsum
  have hwordOK : StringFlow.Word.wordOK w := StringFlow.TD1.wordOK_of_mem_two w hok
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    rcases hok t ht with rfl | rfl <;> omega
  have hfirstWord : StringFlow.Word.wordFirst w m :=
    StringFlow.Word.wordFirst_of_wordValid w m hwordOK hpos hvalid hend
  have hhitlen : StringFlow.firstC3H w.length m = (true, StringFlow.wordWeight w) :=
    StringFlow.TD1.firstC3H_of_wordFirst w m hok hfirstWord
  have hword : StringFlow.TD1.firstC3WordAux w.length m = w :=
    StringFlow.TD1.firstC3WordAux_of_wordFirst w m hok hfirstWord
  have hhit : (StringFlow.firstC3H w.length m).1 = true := by rw [hhitlen]
  have hsum : w.length + (1000 - w.length) = 1000 := by omega
  have hstable := StringFlow.TD1.firstC3WordAux_stable_of_hit w.length m
    (1000 - w.length) hhit
  rw [hsum] at hstable
  have hw1000 : w = StringFlow.TD1.firstC3WordAux 1000 m := by
    rw [hstable, hword]
  have h201full : m = 201 → L = 20 ∧ U = 6 ∧ b = 2 := by
    intro hm201
    have hb1 := StringFlow.TD1.b1_orbit
    have hhit100 : (StringFlow.firstC3H 100 201).1 = true := by
      rw [hb1.2]
    have hstable100 := StringFlow.TD1.firstC3WordAux_stable_of_hit 100 201 900 hhit100
    have hw201 : w = StringFlow.TD1.b1Word := by
      rw [hw1000, hm201, hstable100, hb1.1]
    have hL20 : L = 20 := by
      rw [← hwlen, hw201]
      exact StringFlow.TD1.b1_length
    have hU6 : U = 6 := by
      rw [← hUcount, hw201]
      exact StringFlow.TD1.b1_count_two
    have hM0val : M0 = 286189779 := by
      rw [← hM0, hw201, hm201]
      exact StringFlow.TD1.b1_wordOrbit_201
    have hb2 : b = 2 := by
      cases ts with
      | nil =>
          have hQ0 : 0 = Q := by simpa using hQlen
          omega
      | cons a as =>
          have hhead_a : if b = 1 then a = 3 else a = 5 := hhead a as rfl
          have hmax_head : (5 * M0 + 1) % 2 ^ (a + 1) ≠ 0 := by
            have hh := StringFlow.GC.head_max_of_c3ExactMax ns a as hmax
            rwa [hchainFirst] at hh
          by_cases hb1 : b = 1
          · subst b
            have ha3 : a = 3 := by simpa using hhead_a
            have hmax16 : (5 * M0 + 1) % 16 ≠ 0 := by
              rw [ha3] at hmax_head
              simpa using hmax_head
            have hmod32 : (5 * M0 + 1) % 32 = 0 := by
              rw [hM0val]
            have hmod16 : (5 * M0 + 1) % 16 = 0 := by
              have hmod := (Nat.mod_mod_of_dvd (5 * M0 + 1) (by decide : 16 ∣ 32)).symm
              rw [hmod, hmod32]
            omega
          · rcases hb with rfl | rfl
            · contradiction
            · rfl
    exact ⟨hL20, hU6, hb2⟩
  exact td0_of_firstWord_orbit b Q L U m M0 w ns ts hok hvalid hend hfuel
    hUcount hb hm7 hmle hadm hQ8 hS26 hT hU1full h201full hne hwlen hM0 hQlen
    hc3' hchainFirst hlchain hTchain hhead hge

/-- The `m = 201` rigidity of a real phase-2 cycle: its shape is
`L = 20`, `U = 6`, and `b = 2`. -/
theorem h201full_of_real_cycle
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) :
    m = 201 → L = 20 ∧ U = 6 ∧ b = 2 := by
  rcases h with ⟨hok, hvalid, hend, hfuel, hUcount, hb, hm7, hmle, hadm,
    hQ8, hS26, hbridge, hne, hwlen, hM0, hQlen, hmax,
    hchainFirst, hlchain, hTchain, hhead, hge⟩
  have hwordOK : StringFlow.Word.wordOK w := StringFlow.TD1.wordOK_of_mem_two w hok
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    rcases hok t ht with rfl | rfl <;> omega
  have hfirstWord : StringFlow.Word.wordFirst w m :=
    StringFlow.Word.wordFirst_of_wordValid w m hwordOK hpos hvalid hend
  have hhitlen : StringFlow.firstC3H w.length m = (true, StringFlow.wordWeight w) :=
    StringFlow.TD1.firstC3H_of_wordFirst w m hok hfirstWord
  have hword : StringFlow.TD1.firstC3WordAux w.length m = w :=
    StringFlow.TD1.firstC3WordAux_of_wordFirst w m hok hfirstWord
  have hhit : (StringFlow.firstC3H w.length m).1 = true := by rw [hhitlen]
  have hsum : w.length + (1000 - w.length) = 1000 := by omega
  have hstable := StringFlow.TD1.firstC3WordAux_stable_of_hit w.length m
    (1000 - w.length) hhit
  rw [hsum] at hstable
  have hw1000 : w = StringFlow.TD1.firstC3WordAux 1000 m := by
    rw [hstable, hword]
  intro hm201
  have hb1 := StringFlow.TD1.b1_orbit
  have hhit100 : (StringFlow.firstC3H 100 201).1 = true := by
    rw [hb1.2]
  have hstable100 := StringFlow.TD1.firstC3WordAux_stable_of_hit 100 201 900 hhit100
  have hw201 : w = StringFlow.TD1.b1Word := by
    rw [hw1000, hm201, hstable100, hb1.1]
  have hL20 : L = 20 := by
    rw [← hwlen, hw201]
    exact StringFlow.TD1.b1_length
  have hU6 : U = 6 := by
    rw [← hUcount, hw201]
    exact StringFlow.TD1.b1_count_two
  have hM0val : M0 = 286189779 := by
    rw [← hM0, hw201, hm201]
    exact StringFlow.TD1.b1_wordOrbit_201
  have hb2 : b = 2 := by
    cases ts with
    | nil =>
        have hQ0 : 0 = Q := by simpa using hQlen
        omega
    | cons a as =>
        have hhead_a : if b = 1 then a = 3 else a = 5 := hhead a as rfl
        have hmax_head : (5 * M0 + 1) % 2 ^ (a + 1) ≠ 0 := by
          have hh := StringFlow.GC.head_max_of_c3ExactMax ns a as hmax
          rwa [hchainFirst] at hh
        by_cases hb1 : b = 1
        · subst b
          have ha3 : a = 3 := by simpa using hhead_a
          have hmax16 : (5 * M0 + 1) % 16 ≠ 0 := by
            rw [ha3] at hmax_head
            simpa using hmax_head
          have hmod32 : (5 * M0 + 1) % 32 = 0 := by
            rw [hM0val]
          have hmod16 : (5 * M0 + 1) % 16 = 0 := by
            have hmod := (Nat.mod_mod_of_dvd (5 * M0 + 1) (by decide : 16 ∣ 32)).symm
            rw [hmod, hmod32]
          omega
        · rcases hb with rfl | rfl
          · contradiction
          · rfl
  exact ⟨hL20, hU6, hb2⟩

/-- For `m < 617`, the family last step is rigid: `wordLast w = b`.
The basin bound forces `m = 201`, whose first-C3 word ends at `t=2`
and belongs to the B family. -/
theorem hlast_of_real_cycle_lt_617
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) (hm617 : m < 617) :
    StringFlow.Word.wordLast w = b := by
  have hS : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U h.hok h.hvalid h.hend h.hfuel
      h.hUcount h.hwlen
  have hS26 : 26 ≤ StringFlow.firstC3S 1000 m := by
    rw [hS]
    exact h.hS26
  have hm201 := StringFlow.TD1.basin_617_sharp m h.hm7 hm617 h.hadm hS26
  have h201 := h201full_of_real_cycle b Q L U m M0 w ns ts h hm201
  have hb2 : b = 2 := h201.2.2
  have hwordOK : StringFlow.Word.wordOK w := StringFlow.TD1.wordOK_of_mem_two w h.hok
  have hpos : ∀ t ∈ w, 1 ≤ t := by
    intro t ht
    rcases h.hok t ht with rfl | rfl <;> omega
  have hfirstWord : StringFlow.Word.wordFirst w m :=
    StringFlow.Word.wordFirst_of_wordValid w m hwordOK hpos h.hvalid h.hend
  have hhitlen : StringFlow.firstC3H w.length m = (true, StringFlow.wordWeight w) :=
    StringFlow.TD1.firstC3H_of_wordFirst w m h.hok hfirstWord
  have hword : StringFlow.TD1.firstC3WordAux w.length m = w :=
    StringFlow.TD1.firstC3WordAux_of_wordFirst w m h.hok hfirstWord
  have hhit : (StringFlow.firstC3H w.length m).1 = true := by rw [hhitlen]
  have hsum : w.length + (1000 - w.length) = 1000 := by
    have hle := h.hfuel
    omega
  have hstable := StringFlow.TD1.firstC3WordAux_stable_of_hit w.length m
    (1000 - w.length) hhit
  rw [hsum] at hstable
  have hw1000 : w = StringFlow.TD1.firstC3WordAux 1000 m := by
    rw [hstable, hword]
  have hb1 := StringFlow.TD1.b1_orbit
  have hhit100 : (StringFlow.firstC3H 100 201).1 = true := by
    rw [hb1.2]
  have hstable100 := StringFlow.TD1.firstC3WordAux_stable_of_hit 100 201 900 hhit100
  have hw201 : w = StringFlow.TD1.b1Word := by
    rw [hw1000, hm201, hstable100, hb1.1]
  rw [hb2, hw201]
  exact StringFlow.TD1.b1_last

/-- A real phase-2 cycle forces the exact ceiling identity
`tCeil(L+Q) = L + 3Q + b + U`. -/
theorem tCeil_eq_of_real_cycle
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) :
    StringFlow.tCeil (L + Q) = L + 3 * Q + b + U := by
  rcases h with ⟨hok, hvalid, hend, hfuel, hUcount, hb, hm7, hmle, hadm,
    hQ8, hS26, hbridge, hne, hwlen, hM0, hQlen, hmax,
    hchainFirst, hlchain, hTchain, hhead, hge⟩
  rcases hbridge with ⟨hTpow, hP205, hU1⟩
  have hc3' : StringFlow.GC.c3Exact ns ts :=
    StringFlow.GC.c3Exact_of_c3ExactMax ns ts hmax
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact hne hnil
    omega
  have hP9 : 9 ≤ L + Q := by omega
  have hTle : (L + U) + ts.sum ≤ StringFlow.tCeil (L + Q) :=
    StringFlow.tCeil_ge_of_pow_two_lt (L + Q) ((L + U) + ts.sum) hP9 hP205 hTpow
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  have hUle : U ≤ L := by
    have hle : (w.filter (fun t => t = 2)).length ≤ w.length :=
      List.length_filter_le (fun t => t = 2) w
    rwa [hUcount, hwlen] at hle
  have hU1full : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L := by
    rcases hb with rfl | rfl
    · simpa using hU1
    · exact ⟨hU1, hUle⟩
  have hrise0 := StringFlow.rising_equation_of_wordValid w m M0 hvalid hM0
  have hrise : 2 ^ (L + U) * M0 = 5 ^ L * m + StringFlow.Word.wordA w := by
    rw [hwS, hwlen] at hrise0
    exact hrise0
  have hchain0 := StringFlow.GC.c3_chain_closed_form ns ts hc3'
  have hchain : 2 ^ ts.sum * m = 5 ^ Q * M0 + StringFlow.GC.chainA ts := by
    rw [hlchain, hchainFirst, hQlen] at hchain0
    exact hchain0
  have hne_ts : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    omega
  have hA : 0 < StringFlow.GC.chainA ts := StringFlow.GC.chainA_pos ts hne_ts
  have hgeT : StringFlow.tCeil (L + Q) ≤ (L + U) + ts.sum :=
    StringFlow.tCeil_le_total_of_cycle L Q (L + U) ts.sum m M0
      (StringFlow.Word.wordA w) (StringFlow.GC.chainA ts) hrise hchain hA hP9 hP205
  have hTsum : (L + U) + ts.sum = StringFlow.tCeil (L + Q) := by omega
  exact tCeil_eq_of_chain_sum b Q L U ts hb hQlen hTchain hTsum

/-- A real phase-2 cycle supplies the packaged `Qb8Cycle2` datum. -/
theorem qb8_cycle2_of_real_cycle
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) :
    Qb8Cycle2 b Q L U m M0 w ns ts := by
  have hT := tCeil_eq_of_real_cycle b Q L U m M0 w ns ts h
  have h201full := h201full_of_real_cycle b Q L U m M0 w ns ts h
  rcases h with ⟨hok, hvalid, hend, hfuel, hUcount, hb, hm7, hmle, hadm,
    hQ8, hS26, hbridge, hne, hwlen, hM0, hQlen, hmax,
    hchainFirst, hlchain, hTchain, hhead, hge⟩
  rcases hbridge with ⟨hTpow, hP205, hU1⟩
  have hc3' : StringFlow.GC.c3Exact ns ts :=
    StringFlow.GC.c3Exact_of_c3ExactMax ns ts hmax
  have hU1full : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L := by
    have hUle : U ≤ L := by
      have hle : (w.filter (fun t => t = 2)).length ≤ w.length :=
        List.length_filter_le (fun t => t = 2) w
      rwa [hUcount, hwlen] at hle
    rcases hb with rfl | rfl
    · simpa using hU1
    · exact ⟨hU1, hUle⟩
  have hS : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U hok hvalid hend hfuel hUcount hwlen
  have hS64 : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m hm7 hmle hadm
    rwa [hS] at hb
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact hne hnil
    omega
  have hfeas : StringFlow.TD1.feasible64 b Q L = true :=
    StringFlow.TD1.feasible64_of_cycle_params b Q L U hb hQ8 hL1 hT hU1full hS64
  have hU : StringFlow.uReq b Q L = U :=
    StringFlow.TD1.uReq_eq_of_tCeil b Q L U hT
  have hB1 : m < 617 → m = 201 ∧ L + Q < 59 := by
    intro hm617
    have hS26' : 26 ≤ StringFlow.firstC3S 1000 m := by
      rw [hS]
      exact hS26
    have hm201 := StringFlow.TD1.basin_617_sharp m hm7 hm617 hadm hS26'
    have h201 := h201full hm201
    constructor
    · exact hm201
    · have hL20 : L = 20 := h201.1
      have hU6 : U = 6 := h201.2.1
      have hb2 : b = 2 := h201.2.2
      have hU' : StringFlow.uReq 2 Q 20 = 6 := by
        rw [hb2, hL20, hU6] at hU
        exact hU
      have hQ28 : Q = 28 :=
        StringFlow.TD1.b1B_uReq_solutions_full Q hQ8 hU'
      omega
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  exact {
    hb := hb
    hm7 := hm7
    hfeas := hfeas
    hU := hU
    hB1 := hB1
    hwlen := hwlen
    hwS := hwS
    hok := hok
    hvalid := hvalid
    hM0 := hM0
    hQlen := hQlen
    hc3 := hc3'
    hfirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge
    hS26 := hS26 }

/-- The real-cycle wrapper can also be closed through the packaged
`Qb8Cycle2` phase-2 datum. -/
theorem td0_of_real_cycle_via_cycle2
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) : False :=
  qb8_phase2_closed b Q L U m M0 w ns ts
    (qb8_cycle2_of_real_cycle b Q L U m M0 w ns ts h)

/-- In a real first-C3 orbit, the chain's last node is the odd start
`m`. -/
theorem chainLast_odd_of_firstC3_orbit
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) :
    StringFlow.GC.chainLast ns % 2 = 1 := by
  rw [h.hlchain]
  exact h.hadm.2.1

/-- A real first-C3 orbit datum supplies every field of
`RealQb8Cycle`. -/
theorem real_cycle_of_firstC3_orbit
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) :
    RealQb8Cycle b Q L U m M0 w ns ts := by
  have hhit : (StringFlow.firstC3H 1000 m).1 = true := by
    rw [h.hfirst]
  have hoddm : m % 2 = 1 := h.hadm.2.1
  have hvalid : StringFlow.Word.wordValid w m := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_valid_of_hit 1000 m hoddm hhit
  have hend : StringFlow.Word.wordOrbit w m % 8 = 3 := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_endpoint_mod8_of_hit 1000 m hoddm hhit
  have hok : ∀ t ∈ w, t = 1 ∨ t = 2 := by
    rw [h.hw]
    exact StringFlow.TD1.firstC3WordAux_ok_of_hit 1000 m hhit
  have hS : StringFlow.firstC3S 1000 m = L + U := by
    unfold StringFlow.firstC3S
    rw [h.hfirst]
  have hS64 : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m h.hm7 h.hmle h.hadm
    rwa [hS] at hb
  have hfuel : w.length ≤ 1000 := by
    rw [h.hwlen]
    have hL : L ≤ 1000 := by omega
    exact hL
  have hweight : StringFlow.wordWeight w = L + U := by
    rw [h.hw]
    have hw' := StringFlow.TD1.firstC3WordAux_weight_of_hit 1000 m hhit
    unfold StringFlow.firstC3S at hw'
    rw [h.hfirst] at hw'
    exact hw'
  have hUcount : (w.filter (fun t => t = 2)).length = U := by
    have hfs : (w.filter (fun t => t = 2)).length = (L + U) - L := by
      simpa [hweight, h.hwlen] using
        (StringFlow.filter_count_eq_wordWeight_sub_length w hok)
    rw [hfs]
    rw [Nat.add_comm, Nat.add_sub_cancel]
  have hL1 : 1 ≤ L := StringFlow.TD1.feasible64_L_ge_1 b Q L h.hfeas
  have hne : w ≠ [] := by
    intro hnil
    have hlen0 : w.length = 0 := by rw [hnil]; simp
    have hL0 : L = 0 := by
      rw [h.hwlen] at hlen0
      exact hlen0
    omega
  have hmax : StringFlow.GC.c3ExactMax ns ts :=
    StringFlow.GC.c3ExactMax_of_c3Exact_of_ge_three_last ns ts h.hc3 h.hge
      (chainLast_odd_of_firstC3_orbit b Q L U m M0 w ns ts h)
  have hbridge : Phase2Bridge b Q L U ts :=
    phase2Bridge_of_cycle2 b Q L U ts h.hb h.hfeas h.hU h.hQlen h.hTchain
  exact {
    hok := hok
    hvalid := hvalid
    hend := hend
    hfuel := hfuel
    hUcount := hUcount
    hb := h.hb
    hm7 := h.hm7
    hmle := h.hmle
    hadm := h.hadm
    hQ8 := h.hQ8
    hS26 := h.hS26
    hbridge := hbridge
    hne := hne
    hwlen := h.hwlen
    hM0 := h.hM0
    hQlen := h.hQlen
    hmax := hmax
    hchainFirst := h.hchainFirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge }

/-- Phase-2 closure through the real-cycle wrapper: a real first-C3
orbit is contradictory. -/
theorem td0_of_firstC3_orbit_real
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) : False :=
  td0_of_real_cycle b Q L U m M0 w ns ts
    (real_cycle_of_firstC3_orbit b Q L U m M0 w ns ts h)

/-- Phase-2 closure from a real first-C3 word, routed through
`RealQb8Cycle`. -/
theorem td0_of_firstWord_orbit_real
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hb : b = 1 ∨ b = 2)
    (hm7 : 7 ≤ m) (hmle : m ≤ 10 ^ 6)
    (hadm : StringFlow.admissible m)
    (hQ8 : 8 ≤ Q) (hS26 : 26 ≤ L + U)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L)
    (h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2)
    (hne : w ≠ [])
    (hwlen : w.length = L)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hchainFirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) : False :=
  td0_of_firstC3_orbit_real b Q L U m M0 w ns ts
    (firstC3_orbit_of_firstWord b Q L U m M0 w ns ts hok hvalid hend hfuel
      hUcount hb hm7 hmle hadm hQ8 hS26 hT hU1 h201 hne hwlen hM0 hQlen hc3
      hchainFirst hlchain hTchain hhead hge)

/-- Frame-A + QB-8 cycle wrapper: stage one supplies a `Td0Data`,
and phase two supplies a `Qb8Cycle2`. -/
structure Qb8Cycle (b Q L TT m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hodd : m % 2 = 1
  hfive : m % 5 ≠ 0
  hsplit : Td0Data b Q L TT m M0 ns ts w ∨
    ∃ U, Qb8Cycle2 b Q L U m M0 w ns ts

/-- The phase-2 branch of the frame-A + QB-8 wrapper: a real
`FirstC3Orbit` supplies `Qb8Cycle` through `Qb8Cycle2`. -/
theorem qb8_cycle_of_firstC3_orbit_phase2
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts) :
    Qb8Cycle b Q L (L + U) m M0 w ns ts := by
  refine {
    hm7 := h.hm7
    hmle := h.hmle
    hodd := h.hadm.2.1
    hfive := h.hadm.2.2
    hsplit := ?_ }
  right
  refine ⟨U, qb8_cycle2_of_real_cycle b Q L U m M0 w ns ts
    (real_cycle_of_firstC3_orbit b Q L U m M0 w ns ts h)⟩

/-- The stage-one branch of the frame-A + QB-8 wrapper: a real
`FirstC3Orbit` with `S <= 25` and the stage-one table/branch inputs
supplies `Qb8Cycle` through `Td0Data`. -/
theorem qb8_cycle_of_firstC3_orbit_stage1
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts)
    (hS25 : L + U ≤ 25)
    (hlast : StringFlow.Word.wordLast w = b)
    (hmlt : m < StringFlow.tableM0 b Q L) :
    Qb8Cycle b Q L (StringFlow.tCeil (L + Q)) m M0 w ns ts := by
  refine {
    hm7 := h.hm7
    hmle := h.hmle
    hodd := h.hadm.2.1
    hfive := h.hadm.2.2
    hsplit := ?_ }
  left
  exact td0_data_of_firstC3_orbit_stage1 b Q L U m M0 w ns ts h
    hS25 hlast hmlt

/-- Stage-one phase-2 closure from a real first-C3 orbit: the two
remaining analytic inputs are the family last step and the threshold
bound. -/
theorem td0_of_firstC3_orbit_stage1
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : FirstC3Orbit b Q L U m M0 w ns ts)
    (hS25 : L + U ≤ 25)
    (hlast : StringFlow.Word.wordLast w = b)
    (hmlt : m < StringFlow.tableM0 b Q L) : False :=
  td0_closed_of_data b Q L (StringFlow.tCeil (L + Q)) m M0 ns ts w
    (td0_data_of_firstC3_orbit_stage1 b Q L U m M0 w ns ts h
      hS25 hlast hmlt)

/-- Packaged stage-one upstream inputs: the real first-C3 orbit plus
the family last step and the threshold bound. -/
structure StageOneInputs (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat) : Prop where
  orbit : FirstC3Orbit b Q L U m M0 w ns ts
  hS25 : L + U ≤ 25
  hlast : StringFlow.Word.wordLast w = b
  hmlt : m < StringFlow.tableM0 b Q L

/-- Stage-one closure from the packaged upstream inputs. -/
theorem td0_of_stageOneInputs
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : StageOneInputs b Q L U m M0 w ns ts) : False :=
  td0_of_firstC3_orbit_stage1 b Q L U m M0 w ns ts
    h.orbit h.hS25 h.hlast h.hmlt

/-- In the `m < 617` basin branch, the stage-one last-step input is
automatic: only the threshold bound remains upstream. -/
theorem td0_of_stageOneInputs_lt_617
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : StageOneInputs b Q L U m M0 w ns ts) (hm617 : m < 617) : False := by
  let hr : RealQb8Cycle b Q L U m M0 w ns ts :=
    real_cycle_of_firstC3_orbit b Q L U m M0 w ns ts h.orbit
  have hlast : StringFlow.Word.wordLast w = b :=
    hlast_of_real_cycle_lt_617 b Q L U m M0 w ns ts hr hm617
  exact td0_of_firstC3_orbit_stage1 b Q L U m M0 w ns ts h.orbit h.hS25 hlast h.hmlt

/-- The family last step `wordLast = b` directly gives the A/B family
`U` bounds: A family has `U <= L - 1`, B family has `1 <= U`. -/
theorem U_bounds_of_hlast (w : List Nat) (L U b : Nat)
    (hb : b = 1 ∨ b = 2)
    (hlast : StringFlow.Word.wordLast w = b)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hwlen : w.length = L) :
    if b = 1 then U ≤ L - 1 else 1 ≤ U := by
  rcases hb with rfl | rfl
  · have hfc := StringFlow.dropLast_filter_count_last_one w hlast
    have hle : (w.dropLast.filter (fun t => t = 2)).length ≤ w.dropLast.length :=
      List.length_filter_le (fun t => t = 2) w.dropLast
    have hlen : w.dropLast.length = L - 1 := by
      rw [StringFlow.dropLast_length, hwlen]
    have hU : U = (w.dropLast.filter (fun t => t = 2)).length := by
      rw [← hUcount, hfc]
    rw [hU]
    simp
    rw [hlen] at hle
    exact hle
  · have hfc := StringFlow.filter_count_of_last_two w hlast
    have hU : U = (w.dropLast.filter (fun t => t = 2)).length + 1 := by
      rw [← hUcount, hfc]
    rw [hU]
    simp

/-- In the `m < 617` basin branch, the full `U` rigidity follows
from the real cycle without any extra stage-one last-step input. -/
theorem hU1_of_real_cycle_lt_617
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : RealQb8Cycle b Q L U m M0 w ns ts) (hm617 : m < 617) :
    if b = 1 then U ≤ L - 1 else 1 ≤ U :=
  U_bounds_of_hlast w L U b h.hb
    (hlast_of_real_cycle_lt_617 b Q L U m M0 w ns ts h hm617)
    h.hUcount h.hwlen

/-- Frame-A + QB-8 branch synthesis: any QB-8 cycle is impossible. -/
theorem td0_of_qb8_cycle (b Q L TT m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8Cycle b Q L TT m M0 w ns ts) : False := by
  rcases h.hsplit with hstage | ⟨U, hphase⟩
  · exact td0_closed_of_data b Q L TT m M0 ns ts w hstage
  · exact qb8_phase2_closed b Q L U m M0 w ns ts hphase

end StringFlow.TD0

namespace StringFlow.TD0

/-- Inputs of a real frame-A QB-8 cycle before the first-C3
derivation: the actual rising word, the C3 chain, the family
parameters, the exact ceiling identity `hT`, and the family last
step `hlast`.  The remaining analytic work is to certify `hT` and
`hlast` from the abstract QB-8 definition; `hSfirst`, `hwS`,
`hfeas`, `hU`, and `h201` are all derived here. -/
structure Qb8OrbitInput (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U
  hlast : StringFlow.Word.wordLast w = b
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- The exact ceiling identity already forces the certified `P` range
`L + Q < 205`, because `tCeil` is `0` outside the table. -/
theorem P_lt_205_of_tCeil_eq (b Q L U : Nat)
    (hb1 : 1 ≤ b)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U) :
    L + Q < 205 :=
  StringFlow.TD1.tCeil_pos_lt_205 (L + Q) (by
    rw [hT]
    omega)

/-- A real frame-A QB-8 orbit supplies every field of `Qb8Orbit`;
the first-C3 weight and the word weight are derived from the actual
word instead of being inputs. -/
theorem qb8_orbit_of_firstWord
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hb : b = 1 ∨ b = 2)
    (hm7 : 7 ≤ m) (hmle : m ≤ 10 ^ 6)
    (hadm : StringFlow.admissible m)
    (hQ8 : 8 ≤ Q) (hS26 : 26 ≤ L + U)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hlast : StringFlow.Word.wordLast w = b)
    (hne : w ≠ []) (hwlen : w.length = L)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hchainFirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have hSfirst : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U hok hvalid hend hfuel hUcount hwlen
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  have hS64 : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m hm7 hmle hadm
    rwa [hSfirst] at hb
  have hUle : U ≤ L := by
    have hle : (w.filter (fun t => t = 2)).length ≤ w.length :=
      List.length_filter_le (fun t => t = 2) w
    rwa [hUcount, hwlen] at hle
  have hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L := by
    rcases hb with rfl | rfl
    · have hU1' : U ≤ L - 1 := by
        simpa using U_bounds_of_hlast w L U 1 (Or.inl rfl) hlast hUcount hwlen
      simp [hU1']
    · have hU1' : 1 ≤ U := by
        simpa using U_bounds_of_hlast w L U 2 (Or.inr rfl) hlast hUcount hwlen
      simp [hU1', hUle]
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle0
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact hne hnil
    omega
  have hfeas : StringFlow.TD1.feasible64 b Q L = true :=
    StringFlow.TD1.feasible64_of_cycle_params b Q L U hb hQ8 hL1 hT hU1 hS64
  have hU : StringFlow.uReq b Q L = U :=
    StringFlow.TD1.uReq_eq_of_tCeil b Q L U hT
  have hlastOdd : StringFlow.GC.chainLast ns % 2 = 1 := by
    rw [hlchain]
    exact hadm.2.1
  let hreal : RealQb8Cycle b Q L U m M0 w ns ts := {
    hok := hok
    hvalid := hvalid
    hend := hend
    hfuel := hfuel
    hUcount := hUcount
    hb := hb
    hm7 := hm7
    hmle := hmle
    hadm := hadm
    hQ8 := hQ8
    hS26 := hS26
    hbridge := phase2Bridge_of_cycle2 b Q L U ts hb hfeas hU hQlen hTchain
    hne := hne
    hwlen := hwlen
    hM0 := hM0
    hQlen := hQlen
    hmax := StringFlow.GC.c3ExactMax_of_c3Exact_of_ge_three_last ns ts hc3 hge hlastOdd
    hchainFirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }
  have h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2 :=
    h201full_of_real_cycle b Q L U m M0 w ns ts hreal
  exact {
    hb := hb
    hm7 := hm7
    hmle := hmle
    hadm := hadm
    hQ8 := hQ8
    hS26 := hS26
    hfeas := hfeas
    hU := hU
    hSfirst := hSfirst
    h201 := h201
    hwlen := hwlen
    hwS := hwS
    hok := hok
    hvalid := hvalid
    hM0 := hM0
    hQlen := hQlen
    hc3 := hc3
    hfirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }

/-- A real frame-A QB-8 orbit with the family `U` bound supplied
directly (52.12), instead of deriving it from `wordLast`. -/
theorem qb8_orbit_of_firstWord_u1
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (hok : ∀ t ∈ w, t = 1 ∨ t = 2)
    (hvalid : StringFlow.Word.wordValid w m)
    (hend : StringFlow.Word.wordOrbit w m % 8 = 3)
    (hfuel : w.length ≤ 1000)
    (hUcount : (w.filter (fun t => t = 2)).length = U)
    (hb : b = 1 ∨ b = 2)
    (hm7 : 7 ≤ m) (hmle : m ≤ 10 ^ 6)
    (hadm : StringFlow.admissible m)
    (hQ8 : 8 ≤ Q) (hS26 : 26 ≤ L + U)
    (hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U)
    (hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L)
    (hne : w ≠ []) (hwlen : w.length = L)
    (hM0 : StringFlow.Word.wordOrbit w m = M0)
    (hQlen : ts.length = Q)
    (hc3 : StringFlow.GC.c3Exact ns ts)
    (hchainFirst : StringFlow.GC.chainFirst ns = M0)
    (hlchain : StringFlow.GC.chainLast ns = m)
    (hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
               else 4 * 8 ^ ts.length = 2 ^ ts.sum)
    (hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5)
    (hge : ∀ t ∈ ts, 3 ≤ t) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have hSfirst : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U hok hvalid hend hfuel hUcount hwlen
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U hok hUcount hwlen
  have hS64 : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m hm7 hmle hadm
    rwa [hSfirst] at hb
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle0
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact hne hnil
    omega
  have hfeas : StringFlow.TD1.feasible64 b Q L = true :=
    StringFlow.TD1.feasible64_of_cycle_params b Q L U hb hQ8 hL1 hT hU1 hS64
  have hU : StringFlow.uReq b Q L = U :=
    StringFlow.TD1.uReq_eq_of_tCeil b Q L U hT
  have hlastOdd : StringFlow.GC.chainLast ns % 2 = 1 := by
    rw [hlchain]
    exact hadm.2.1
  let hreal : RealQb8Cycle b Q L U m M0 w ns ts := {
    hok := hok
    hvalid := hvalid
    hend := hend
    hfuel := hfuel
    hUcount := hUcount
    hb := hb
    hm7 := hm7
    hmle := hmle
    hadm := hadm
    hQ8 := hQ8
    hS26 := hS26
    hbridge := phase2Bridge_of_cycle2 b Q L U ts hb hfeas hU hQlen hTchain
    hne := hne
    hwlen := hwlen
    hM0 := hM0
    hQlen := hQlen
    hmax := StringFlow.GC.c3ExactMax_of_c3Exact_of_ge_three_last ns ts hc3 hge hlastOdd
    hchainFirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }
  have h201 : m = 201 → L = 20 ∧ U = 6 ∧ b = 2 :=
    h201full_of_real_cycle b Q L U m M0 w ns ts hreal
  exact {
    hb := hb
    hm7 := hm7
    hmle := hmle
    hadm := hadm
    hQ8 := hQ8
    hS26 := hS26
    hfeas := hfeas
    hU := hU
    hSfirst := hSfirst
    h201 := h201
    hwlen := hwlen
    hwS := hwS
    hok := hok
    hvalid := hvalid
    hM0 := hM0
    hQlen := hQlen
    hc3 := hc3
    hfirst := hchainFirst
    hlchain := hlchain
    hTchain := hTchain
    hhead := hhead
    hge := hge }

/-- Phase-2 closure from the complete frame-A QB-8 orbit inputs. -/
theorem td0_of_qb8OrbitInput
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitInput b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_firstWord b Q L U m M0 w ns ts h.hok h.hvalid h.hend h.hfuel
      h.hUcount h.hb h.hm7 h.hmle h.hadm h.hQ8 h.hS26 h.hT h.hlast
      h.hne h.hwlen h.hM0 h.hQlen h.hc3 h.hfirst h.hlchain h.hTchain h.hhead h.hge)

/-- A real frame-A QB-8 cycle with the GC-7 numerator inputs: the
exact ceiling identity `hT` is derived instead of being an input. -/
structure Qb8OrbitGC7Input (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hlast : StringFlow.Word.wordLast w = b
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hP205 : L + Q < 205
  hD : 0 < 2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q)
  hcyc : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts =
      m * (2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q))

/-- From the exact cycle equation and the GC-7 window, the exact
ceiling identity is derived and the full `Qb8Orbit` datum is
constructed. -/
theorem qb8_orbit_of_gc7Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitGC7Input b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have htsne : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    have hQ : 8 ≤ ts.length := by rw [h.hQlen]; exact h.hQ8
    omega
  have hpm : StringFlow.GC.pmiTotal w ts =
      5 * m * (2 ^ (w.sum + ts.sum) - 5 ^ (w.length + ts.length)) := by
    apply pmiTotal_eq_five_mul_D w ts m htsne
    simpa [h.hQlen, h.hwlen, wordWeight_eq_sum w] using h.hcyc
  have hrise : ∀ t ∈ w, t ≤ 2 := by
    intro t ht
    rcases h.hok t ht with rfl | rfl <;> norm_num
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle0
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact h.hne hnil
    have hwlen : w.length = L := h.hwlen
    omega
  have hP9 : 9 ≤ L + Q := by
    have hQge : 8 ≤ Q := h.hQ8
    omega
  have hD' : 0 < 2 ^ (w.sum + ts.sum) - 5 ^ (w.length + ts.length) := by
    simpa [h.hwlen, h.hQlen, wordWeight_eq_sum w] using h.hD
  have hT0 : StringFlow.tCeil (w.length + ts.length) = w.sum + ts.sum :=
    tCeil_eq_of_gc7_and_cycle w ts m hpm hrise h.hge h.hm7
      (by simpa [h.hwlen, h.hQlen] using hP9)
      (by simpa [h.hwlen, h.hQlen] using h.hP205)
      hD'
  have hwS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U h.hok h.hUcount h.hwlen
  have hsum : ts.sum = 3 * Q + b := by
    rcases h.hb with rfl | rfl
    · have hs := sum_eq_of_two_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
    · have hs := sum_eq_of_four_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
  have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U := by
    have hT0' : StringFlow.tCeil (L + Q) = w.sum + ts.sum := by
      simpa [h.hwlen, h.hQlen] using hT0
    rw [hT0']
    have hws : w.sum = StringFlow.wordWeight w := (wordWeight_eq_sum w).symm
    rw [hws, hwS, hsum]
    omega
  exact qb8_orbit_of_firstWord b Q L U m M0 w ns ts h.hok h.hvalid h.hend h.hfuel
    h.hUcount h.hb h.hm7 h.hmle h.hadm h.hQ8 h.hS26 hT h.hlast
    h.hne h.hwlen h.hM0 h.hQlen h.hc3 h.hfirst h.hlchain h.hTchain h.hhead h.hge

/-- Phase-2 closure from the complete GC-7 cycle inputs. -/
theorem td0_of_qb8OrbitGC7Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitGC7Input b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_gc7Input b Q L U m M0 w ns ts h)

/-- From the additive cycle equation, the total numerator equals
`m * (2^(S+T) - 5^(L+Q))`. -/
theorem cycle_equation_A_eq (L Q S T m A : Nat)
    (h : 2 ^ (S + T) * m = 5 ^ (L + Q) * m + A)
    (hA : 0 < A) :
    A = m * (2 ^ (S + T) - 5 ^ (L + Q)) := by
  have hlt : 5 ^ (L + Q) < 2 ^ (S + T) :=
    pow_lt_of_cycle_equation L Q S T m A h hA
  have hAeq : A = 2 ^ (S + T) * m - 5 ^ (L + Q) * m := by
    rw [h]
    omega
  rw [hAeq]
  rw [Nat.mul_comm (2 ^ (S + T)) m, Nat.mul_comm (5 ^ (L + Q)) m]
  rw [← Nat.mul_sub]

/-- A real frame-A QB-8 cycle with only the structural inputs: the
exact cycle equation `hcyc` and the positive denominator `hD` are
derived from the word and chain equations. -/
structure Qb8OrbitCycleInput (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hlast : StringFlow.Word.wordLast w = b
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hP205 : L + Q < 205

/-- From the structural inputs, derive the GC-7 numerator input and
construct the full `Qb8Orbit`. -/
theorem qb8_orbit_of_cycleInput
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitCycleInput b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have htsne : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    have hQ : 8 ≤ ts.length := by rw [h.hQlen]; exact h.hQ8
    omega
  have hrise : 2 ^ StringFlow.wordWeight w * M0 =
      5 ^ L * m + StringFlow.Word.wordA w := by
    simpa [h.hwlen] using (rising_equation_of_wordValid w m M0 h.hvalid h.hM0)
  have hchain : 2 ^ ts.sum * m =
      5 ^ Q * M0 + StringFlow.GC.chainA ts := by
    simpa [h.hlchain, h.hfirst, h.hQlen] using
      (StringFlow.GC.c3_chain_closed_form ns ts h.hc3)
  have hcycAdd : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    simpa [h.hQlen] using
      (cycle_equation_of_rising_and_chain L Q (StringFlow.wordWeight w) ts.sum
        m M0 (StringFlow.GC.chainA ts) (StringFlow.Word.wordA w) hrise hchain)
  have hApos : 0 < 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    have hcpos : 0 < StringFlow.GC.chainA ts :=
      StringFlow.GC.chainA_pos ts htsne
    have h2 : 0 < 2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts :=
      Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
    omega
  have hcycAdd' : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        (5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts) := by
    rw [← Nat.add_assoc]
    exact hcycAdd
  have hcyc : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts =
      m * (2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q)) :=
    cycle_equation_A_eq L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
  have hD : 0 < 2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q) := by
    have hlt := pow_lt_of_cycle_equation L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
    omega
  exact qb8_orbit_of_gc7Input b Q L U m M0 w ns ts {
    hb := h.hb
    hm7 := h.hm7
    hmle := h.hmle
    hadm := h.hadm
    hQ8 := h.hQ8
    hS26 := h.hS26
    hlast := h.hlast
    hwlen := h.hwlen
    hUcount := h.hUcount
    hok := h.hok
    hvalid := h.hvalid
    hend := h.hend
    hM0 := h.hM0
    hfuel := h.hfuel
    hne := h.hne
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hfirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge
    hP205 := h.hP205
    hD := hD
    hcyc := hcyc }

/-- Phase-2 closure from the structural QB-8 cycle inputs. -/
theorem td0_of_qb8OrbitCycleInput
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitCycleInput b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_cycleInput b Q L U m M0 w ns ts h)

/-- The structural QB-8 cycle input without the B0 range: `hP205` is
derived from the chain upper bounds and the exact cycle equation. -/
structure Qb8OrbitStructuralInput (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hlast : StringFlow.Word.wordLast w = b
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- From the structural inputs, the B0 range `P < 205` is derived
from the chain upper bounds, and the full `Qb8Orbit` is constructed. -/
theorem qb8_orbit_of_structuralInput
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitStructuralInput b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have htsne : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    have hQ : 8 ≤ ts.length := by rw [h.hQlen]; exact h.hQ8
    omega
  have hrise : 2 ^ StringFlow.wordWeight w * M0 =
      5 ^ L * m + StringFlow.Word.wordA w := by
    simpa [h.hwlen] using (rising_equation_of_wordValid w m M0 h.hvalid h.hM0)
  have hchain : 2 ^ ts.sum * m =
      5 ^ Q * M0 + StringFlow.GC.chainA ts := by
    simpa [h.hlchain, h.hfirst, h.hQlen] using
      (StringFlow.GC.c3_chain_closed_form ns ts h.hc3)
  have hcycAdd : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    simpa [h.hQlen] using
      (cycle_equation_of_rising_and_chain L Q (StringFlow.wordWeight w) ts.sum
        m M0 (StringFlow.GC.chainA ts) (StringFlow.Word.wordA w) hrise hchain)
  have hApos : 0 < 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    have hcpos : 0 < StringFlow.GC.chainA ts :=
      StringFlow.GC.chainA_pos ts htsne
    have h2 : 0 < 2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts :=
      Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
    omega
  have hcycAdd' : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        (5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts) := by
    rw [← Nat.add_assoc]
    exact hcycAdd
  have hcyc : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts =
      m * (2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q)) :=
    cycle_equation_A_eq L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
  have hD : 0 < 2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q) := by
    have hlt := pow_lt_of_cycle_equation L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
    omega
  have hS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U h.hok h.hUcount h.hwlen
  have hSfirst : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U h.hok h.hvalid h.hend h.hfuel h.hUcount h.hwlen
  have hSle : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m h.hm7 h.hmle h.hadm
    rwa [hSfirst] at hb
  have hTsum : ts.sum = 3 * Q + b := by
    rcases h.hb with rfl | rfl
    · have hs := sum_eq_of_two_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
    · have hs := sum_eq_of_four_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
  have hQ2 : 2 ≤ Q := le_trans (by norm_num : 2 ≤ 8) h.hQ8
  have hAlt : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts <
      5 ^ (L + Q) + 2 ^ (StringFlow.wordWeight w + ts.sum) := by
    exact A_lt_five_pow_add_two_pow b Q L (L + U) (StringFlow.wordWeight w)
      (StringFlow.wordWeight w + ts.sum) (L + Q) w ts
      h.hok h.hwlen h.hb h.hQlen hQ2 h.hhead h.hge hTsum rfl rfl
      (by rw [hTsum]; omega) rfl
  have hpow : 6 * 2 ^ (StringFlow.wordWeight w + ts.sum) <
      8 * 5 ^ (L + Q) := by
    have hDle : 5 ^ (L + Q) < 2 ^ (StringFlow.wordWeight w + ts.sum) := by omega
    exact pow_six_lt_eight_mul (L + Q) (StringFlow.wordWeight w + ts.sum) m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hDle h.hm7 hAlt
  have hP205 : L + Q < 205 := by
    have hb1 : 1 ≤ b := by
      rcases h.hb with rfl | rfl <;> norm_num
    have hQleP : Q ≤ L + Q := by omega
    have hSdef : L + U = (L + Q) - Q + U := by omega
    have hTdef : StringFlow.wordWeight w + ts.sum =
        L + U + 3 * Q + b := by
      rw [hS, hTsum]
      omega
    exact P_lt_205_of_pow_six (L + Q) Q b U (L + U)
      (StringFlow.wordWeight w + ts.sum) hb1 (by omega : 0 ≤ U)
      hSdef hQleP hSle hTdef hpow
  exact qb8_orbit_of_gc7Input b Q L U m M0 w ns ts {
    hb := h.hb
    hm7 := h.hm7
    hmle := h.hmle
    hadm := h.hadm
    hQ8 := h.hQ8
    hS26 := h.hS26
    hlast := h.hlast
    hwlen := h.hwlen
    hUcount := h.hUcount
    hok := h.hok
    hvalid := h.hvalid
    hend := h.hend
    hM0 := h.hM0
    hfuel := h.hfuel
    hne := h.hne
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hfirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge
    hP205 := hP205
    hD := hD
    hcyc := hcyc }

/-- Phase-2 closure from the structural QB-8 cycle inputs, with the
B0 range derived internally. -/
theorem td0_of_qb8OrbitStructuralInput
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitStructuralInput b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_structuralInput b Q L U m M0 w ns ts h)

/-- The structural QB-8 cycle input with the family `U` bound:
`hT`, `hP205`, `hcyc`, and `hD` are all derived, so the only
analytic input is the 52.12 `U` bound `hU1`. -/
structure Qb8OrbitStructuralU1Input (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t

/-- From the structural inputs and the family `U` bound, the exact
ceiling identity and B0 range are derived, and the full `Qb8Orbit`
is constructed. -/
theorem qb8_orbit_of_structuralU1Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitStructuralU1Input b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have htsne : ts ≠ [] := by
    intro hts
    have hlen0 : ts.length = 0 := by rw [hts]; simp
    have hQ : 8 ≤ ts.length := by rw [h.hQlen]; exact h.hQ8
    omega
  have hrise : 2 ^ StringFlow.wordWeight w * M0 =
      5 ^ L * m + StringFlow.Word.wordA w := by
    simpa [h.hwlen] using (rising_equation_of_wordValid w m M0 h.hvalid h.hM0)
  have hchain : 2 ^ ts.sum * m =
      5 ^ Q * M0 + StringFlow.GC.chainA ts := by
    simpa [h.hlchain, h.hfirst, h.hQlen] using
      (StringFlow.GC.c3_chain_closed_form ns ts h.hc3)
  have hcycAdd : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    simpa [h.hQlen] using
      (cycle_equation_of_rising_and_chain L Q (StringFlow.wordWeight w) ts.sum
        m M0 (StringFlow.GC.chainA ts) (StringFlow.Word.wordA w) hrise hchain)
  have hApos : 0 < 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts := by
    have hcpos : 0 < StringFlow.GC.chainA ts :=
      StringFlow.GC.chainA_pos ts htsne
    have h2 : 0 < 2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts :=
      Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) hcpos
    omega
  have hcycAdd' : 2 ^ (StringFlow.wordWeight w + ts.sum) * m =
      5 ^ (L + Q) * m +
        (5 ^ Q * StringFlow.Word.wordA w +
          2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts) := by
    rw [← Nat.add_assoc]
    exact hcycAdd
  have hcyc : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts =
      m * (2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q)) :=
    cycle_equation_A_eq L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
  have hD : 0 < 2 ^ (StringFlow.wordWeight w + ts.sum) - 5 ^ (L + Q) := by
    have hlt := pow_lt_of_cycle_equation L Q (StringFlow.wordWeight w) ts.sum m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hApos
    omega
  have hS : StringFlow.wordWeight w = L + U :=
    StringFlow.wordWeight_of_count w L U h.hok h.hUcount h.hwlen
  have hSfirst : StringFlow.firstC3S 1000 m = L + U :=
    firstC3S_1000_of_firstWord w m L U h.hok h.hvalid h.hend h.hfuel h.hUcount h.hwlen
  have hSle : L + U ≤ 64 := by
    have hb := StringFlow.TD1.basin_1e6_weight_1000 m h.hm7 h.hmle h.hadm
    rwa [hSfirst] at hb
  have hTsum : ts.sum = 3 * Q + b := by
    rcases h.hb with rfl | rfl
    · have hs := sum_eq_of_two_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
    · have hs := sum_eq_of_four_mul_eight ts (by simpa using h.hTchain)
      rw [h.hQlen] at hs
      omega
  have hQ2 : 2 ≤ Q := le_trans (by norm_num : 2 ≤ 8) h.hQ8
  have hAlt : 5 ^ Q * StringFlow.Word.wordA w +
      2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts <
      5 ^ (L + Q) + 2 ^ (StringFlow.wordWeight w + ts.sum) := by
    exact A_lt_five_pow_add_two_pow b Q L (L + U) (StringFlow.wordWeight w)
      (StringFlow.wordWeight w + ts.sum) (L + Q) w ts
      h.hok h.hwlen h.hb h.hQlen hQ2 h.hhead h.hge hTsum rfl rfl
      (by rw [hTsum]; omega) rfl
  have hpow : 6 * 2 ^ (StringFlow.wordWeight w + ts.sum) <
      8 * 5 ^ (L + Q) := by
    have hDle : 5 ^ (L + Q) < 2 ^ (StringFlow.wordWeight w + ts.sum) := by omega
    exact pow_six_lt_eight_mul (L + Q) (StringFlow.wordWeight w + ts.sum) m
      (5 ^ Q * StringFlow.Word.wordA w +
        2 ^ StringFlow.wordWeight w * StringFlow.GC.chainA ts)
      hcycAdd' hDle h.hm7 hAlt
  have hP205 : L + Q < 205 := by
    have hb1 : 1 ≤ b := by
      rcases h.hb with rfl | rfl <;> norm_num
    have hQleP : Q ≤ L + Q := by omega
    have hSdef : L + U = (L + Q) - Q + U := by omega
    have hTdef : StringFlow.wordWeight w + ts.sum =
        L + U + 3 * Q + b := by
      rw [hS, hTsum]
      omega
    exact P_lt_205_of_pow_six (L + Q) Q b U (L + U)
      (StringFlow.wordWeight w + ts.sum) hb1 (by omega : 0 ≤ U)
      hSdef hQleP hSle hTdef hpow
  have hpm : StringFlow.GC.pmiTotal w ts =
      5 * m * (2 ^ (w.sum + ts.sum) - 5 ^ (w.length + ts.length)) := by
    apply pmiTotal_eq_five_mul_D w ts m htsne
    simpa [h.hQlen, h.hwlen, wordWeight_eq_sum w] using hcyc
  have hrise12 : ∀ t ∈ w, t ≤ 2 := by
    intro t ht
    rcases h.hok t ht with rfl | rfl <;> norm_num
  have hL1 : 1 ≤ L := by
    have hlenpos : 0 < w.length := by
      by_contra hle0
      have hzero : w.length = 0 := by omega
      have hnil : w = [] := List.eq_nil_iff_length_eq_zero.mpr hzero
      exact h.hne hnil
    have hwlen : w.length = L := h.hwlen
    omega
  have hP9 : 9 ≤ L + Q := by
    have hQge : 8 ≤ Q := h.hQ8
    omega
  have hD' : 0 < 2 ^ (w.sum + ts.sum) - 5 ^ (w.length + ts.length) := by
    simpa [h.hwlen, h.hQlen, wordWeight_eq_sum w] using hD
  have hT0 : StringFlow.tCeil (w.length + ts.length) = w.sum + ts.sum :=
    tCeil_eq_of_gc7_and_cycle w ts m hpm hrise12 h.hge h.hm7
      (by simpa [h.hwlen, h.hQlen] using hP9)
      (by simpa [h.hwlen, h.hQlen] using hP205)
      hD'
  have hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U := by
    have hT0' : StringFlow.tCeil (L + Q) = w.sum + ts.sum := by
      simpa [h.hwlen, h.hQlen] using hT0
    rw [hT0']
    have hws : w.sum = StringFlow.wordWeight w := (wordWeight_eq_sum w).symm
    rw [hws, hS, hTsum]
    omega
  exact qb8_orbit_of_firstWord_u1 b Q L U m M0 w ns ts h.hok h.hvalid h.hend h.hfuel
    h.hUcount h.hb h.hm7 h.hmle h.hadm h.hQ8 h.hS26 hT h.hU1
    h.hne h.hwlen h.hM0 h.hQlen h.hc3 h.hfirst h.hlchain h.hTchain h.hhead h.hge

/-- Phase-2 closure from the structural inputs with the family
`U` bound. -/
theorem td0_of_qb8OrbitStructuralU1Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitStructuralU1Input b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_structuralU1Input b Q L U m M0 w ns ts h)

/-- The B0-level structural input: `Qb8OrbitCycleInput` plus the
exact `uReq` ceiling identity `hT`.  The B0 range `hP205` is derived
from `hT`, so the remaining analytic inputs are only `hT` and the
family last step `hlast`. -/
structure Qb8OrbitB0Input (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hlast : StringFlow.Word.wordLast w = b
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U

/-- From the `uReq` identity, the B0 range is derived and the full
`Qb8Orbit` datum is constructed. -/
theorem qb8_orbit_of_b0Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitB0Input b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts := by
  have hb1 : 1 ≤ b := by
    rcases h.hb with rfl | rfl <;> norm_num
  have hP205 : L + Q < 205 :=
    P_lt_205_of_tCeil_eq b Q L U hb1 h.hT
  exact qb8_orbit_of_cycleInput b Q L U m M0 w ns ts {
    hb := h.hb
    hm7 := h.hm7
    hmle := h.hmle
    hadm := h.hadm
    hQ8 := h.hQ8
    hS26 := h.hS26
    hlast := h.hlast
    hwlen := h.hwlen
    hUcount := h.hUcount
    hok := h.hok
    hvalid := h.hvalid
    hend := h.hend
    hM0 := h.hM0
    hfuel := h.hfuel
    hne := h.hne
    hQlen := h.hQlen
    hc3 := h.hc3
    hfirst := h.hfirst
    hlchain := h.hlchain
    hTchain := h.hTchain
    hhead := h.hhead
    hge := h.hge
    hP205 := hP205 }

/-- Phase-2 closure from the B0-level structural inputs. -/
theorem td0_of_qb8OrbitB0Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitB0Input b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_b0Input b Q L U m M0 w ns ts h)

/-- The abstract frame-A + QB-8 cycle datum: the same fields as
`Qb8OrbitB0Input`, presented as the packaged QB-8 definition. -/
abbrev Qb8CycleAbstract (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop :=
  Qb8OrbitB0Input b Q L U m M0 w ns ts

/-- Top-level phase-2 closure from the abstract frame-A + QB-8
cycle: every such cycle is impossible. -/
theorem td0_of_qb8CycleAbstract
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8CycleAbstract b Q L U m M0 w ns ts) : False :=
  td0_of_qb8OrbitB0Input b Q L U m M0 w ns ts h

/-- The abstract QB-8 cycle with the family `U` bound as a direct
input (52.12), so the remaining analytic inputs are the `uReq`
identity `hT` and the `U` bound `hU1`. -/
structure Qb8OrbitU1Input (b Q L U m M0 : Nat) (w : List Nat)
    (ns ts : List Nat) : Prop where
  hb : b = 1 ∨ b = 2
  hm7 : 7 ≤ m
  hmle : m ≤ 10 ^ 6
  hadm : StringFlow.admissible m
  hQ8 : 8 ≤ Q
  hS26 : 26 ≤ L + U
  hU1 : if b = 1 then U ≤ L - 1 else 1 ≤ U ∧ U ≤ L
  hwlen : w.length = L
  hUcount : (w.filter (fun t => t = 2)).length = U
  hok : ∀ t ∈ w, t = 1 ∨ t = 2
  hvalid : StringFlow.Word.wordValid w m
  hend : StringFlow.Word.wordOrbit w m % 8 = 3
  hM0 : StringFlow.Word.wordOrbit w m = M0
  hfuel : w.length ≤ 1000
  hne : w ≠ []
  hQlen : ts.length = Q
  hc3 : StringFlow.GC.c3Exact ns ts
  hfirst : StringFlow.GC.chainFirst ns = M0
  hlchain : StringFlow.GC.chainLast ns = m
  hTchain : if b = 1 then 2 ^ ts.sum = 2 * 8 ^ ts.length
            else 4 * 8 ^ ts.length = 2 ^ ts.sum
  hhead : ∀ a as, ts = a :: as → if b = 1 then a = 3 else a = 5
  hge : ∀ t ∈ ts, 3 ≤ t
  hT : StringFlow.tCeil (L + Q) = L + 3 * Q + b + U

/-- From the `uReq` identity and the family `U` bound, the full
`Qb8Orbit` datum is constructed. -/
theorem qb8_orbit_of_u1Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitU1Input b Q L U m M0 w ns ts) :
    Qb8Orbit b Q L U m M0 w ns ts :=
  qb8_orbit_of_firstWord_u1 b Q L U m M0 w ns ts h.hok h.hvalid h.hend h.hfuel
    h.hUcount h.hb h.hm7 h.hmle h.hadm h.hQ8 h.hS26 h.hT h.hU1
    h.hne h.hwlen h.hM0 h.hQlen h.hc3 h.hfirst h.hlchain h.hTchain h.hhead h.hge

/-- Phase-2 closure from the `uReq` + `U`-bound inputs. -/
theorem td0_of_qb8OrbitU1Input
    (b Q L U m M0 : Nat) (w : List Nat) (ns ts : List Nat)
    (h : Qb8OrbitU1Input b Q L U m M0 w ns ts) : False :=
  td0_of_qb8_orbit b Q L U m M0 w ns ts
    (qb8_orbit_of_u1Input b Q L U m M0 w ns ts h)

end StringFlow.TD0
