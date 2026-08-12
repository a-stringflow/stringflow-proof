import Td1S3

/-!
# TD-1 interval exclusion in cleared integer form

This module formalizes the 52.15 equivalences

    A_req > A_max  iff  2^b * X > Y
    A_req < A0     iff  2^b < Z

for the A family (`b = 1`, `t_last = 1`, `t_1 = 3`) and the B family
(`b = 2`, `t_last = 2`, `t_1 = 5`).  All quantities are integer and
the `S3` closed form comes from `Td1S3.lean`.
-/

namespace StringFlow.TD1

/-- `A_req` for the A family: `2*8^Q*m - 5^Q*M0`. -/
def areqA (Q m M0 : Nat) : Nat := 2 * 8 ^ Q * m - 5 ^ Q * M0

/-- `A_req` for the B family: `4*8^Q*m - 5^Q*M0`. -/
def areqB (Q m M0 : Nat) : Nat := 4 * 8 ^ Q * m - 5 ^ Q * M0

/-- `A_max,3` for the A family: `A0 + S3`. -/
def amaxA (Q : Nat) : Nat := a0 Q + s3 Q

/-- `A_max,5` for the B family:
`5^(Q-1) + 32*5^(Q-2) + 4*S3`. -/
def amaxB (Q : Nat) : Nat :=
  5 ^ (Q - 1) + 32 * 5 ^ (Q - 2) + 4 * s3 Q

/-- `X = 8^Q*m - S3`. -/
def xVal (Q m : Nat) : Nat := 8 ^ Q * m - s3 Q

/-- `Y = 5^Q*M0 + A0 - S3` for the A family. -/
def yVal (Q M0 : Nat) : Nat := (5 ^ Q * M0 + a0 Q) - s3 Q

/-- `Y_B = 5^Q*M0 + 5^(Q-1) + 32*5^(Q-2)` for the B family. -/
def yBVal (Q M0 : Nat) : Nat :=
  5 ^ Q * M0 + 5 ^ (Q - 1) + 32 * 5 ^ (Q - 2)

/-- A-family upper exclusion in cleared form:
`A_req > A_max,3` iff `2*8^Q*m > 5^Q*M0 + A0 + S3`. -/
theorem td1A_areq_gt_amax_iff (Q m M0 : Nat)
    (hM0 : 5 ^ Q * M0 ≤ 2 * 8 ^ Q * m) :
    areqA Q m M0 > amaxA Q ↔
      2 * 8 ^ Q * m > 5 ^ Q * M0 + a0 Q + s3 Q := by
  unfold areqA amaxA
  omega

/-- A-family lower exclusion:
`A_req < A0` iff `2 < Z`. -/
theorem td1A_areq_lt_a0_iff (Q m M0 : Nat)
    (hM0 : 5 ^ Q * M0 ≤ 2 * 8 ^ Q * m) :
    areqA Q m M0 < a0 Q ↔ 2 * 8 ^ Q * m < 5 ^ Q * M0 + a0 Q := by
  unfold areqA
  omega

/-- B-family upper exclusion in cleared form:
`A_req > A_max,5` iff
`4*8^Q*m > 5^Q*M0 + 5^(Q-1) + 32*5^(Q-2) + 4*S3`. -/
theorem td1B_areq_gt_amax_iff (Q m M0 : Nat)
    (hM0 : 5 ^ Q * M0 ≤ 4 * 8 ^ Q * m) :
    areqB Q m M0 > amaxB Q ↔
      4 * 8 ^ Q * m >
        5 ^ Q * M0 + 5 ^ (Q - 1) + 32 * 5 ^ (Q - 2) + 4 * s3 Q := by
  unfold areqB amaxB
  omega

/-- B-family lower exclusion:
`A_req < A0` iff `4 < Z`. -/
theorem td1B_areq_lt_a0_iff (Q m M0 : Nat)
    (hM0 : 5 ^ Q * M0 ≤ 4 * 8 ^ Q * m) :
    areqB Q m M0 < a0 Q ↔ 4 * 8 ^ Q * m < 5 ^ Q * M0 + a0 Q := by
  unfold areqB
  omega

end StringFlow.TD1
