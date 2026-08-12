import DeltaRecords

/-!
# Stage 1 (S <= 25) parameter certificate

This certificate checks every feasible (b, Q, L) with S <= 25
at the threshold m0 = max(7, 2^(S-6)-1).  The upper and lower
branch inequalities are evaluated in exact rational arithmetic.
The single triple (b=2, Q=8, L=7) that fails both branches is
ruled out by the global cycle-equation bound A_total < 7*D.
-/

namespace StringFlow

def uReq (b Q L : Nat) : Nat :=
  tCeil (L + Q) - (L + 3*Q + b)

def feasible (b Q L : Nat) : Bool :=
  let T := tCeil (L + Q)
  let U := uReq b Q L
  decide (1 <= b && b <= 2 && 8 <= Q && Q <= 50 && 1 <= L && L <= 25 &&
          L + 3*Q + b <= T &&
          (if b = 1 then U <= L - 1 else 1 <= U && U <= L) &&
          L + U <= 25)

def branchAt (b Q L : Nat) : Bool :=
  if ! feasible b Q L then true else
    let P := L + Q
    let T := tCeil P
    let U := uReq b Q L
    let S := L + U
    let m0 := if S <= 6 then 7 else max 7 ((2^(S-6)) - 1)
    let a : Rat := (8 / 5 : Rat) ^ Q
    let x : Rat := (2 * (5^P : Nat) : Rat) / (2^T : Rat)
    let B : Rat := (if b = 1 then a else 2 * a) * x
    let rho : Rat := (4 / 5 : Rat) ^ U
    let hmax : Rat :=
      1 - (2 / 3 : Rat) * rho - (1 : Rat) / (3 * (if b = 1 then a else 2 * a))
    let hmin : Rat :=
      if b = 1 then
        let K := L - U - 1
        (1 / 3 : Rat) + ((2 / 5 : Rat) ^ K) * ((2 / 3 : Rat) - ((4 / 5 : Rat) ^ (U + 1)))
      else
        let K := L - U
        (1 / 3 : Rat) + ((2 / 5 : Rat) ^ K) * ((2 / 3 : Rat) - ((4 / 5 : Rat) ^ U))
    let Ubr : Rat := if b = 1 then
        2 * a - (2 * a - (89 / 25 : Rat)) / (3 * (m0 : Rat))
      else
        4 * a - (4 * a - (29 / 5 : Rat)) / (3 * (m0 : Rat))
    let Lbr : Rat := if b = 1 then
        2 * a - (a - 1) / (3 * (m0 : Rat))
      else
        4 * a - (a - 1) / (3 * (m0 : Rat))
    let Rmax : Rat := B * (1 + hmax / (m0 : Rat))
    let Rmin : Rat := B * (1 + hmin / (m0 : Rat))
    decide (Rmax < Ubr || Rmin > Lbr)

def auOfAux : Nat → Nat → List Nat → Nat
  | A, _, [] => A
  | A, W, t :: ts => auOfAux (5 * A + 2^W) (W + t) ts

def auOf (word : List Nat) : Nat := auOfAux 0 0 word

def sixAuOK : Bool :=
  auOf [2,1,1,1,1,1,2] = 36373 &&
  auOf [1,2,1,1,1,1,2] = 30123 &&
  auOf [1,1,2,1,1,1,2] = 27623 &&
  auOf [1,1,1,2,1,1,2] = 26623 &&
  auOf [1,1,1,1,2,1,2] = 26223 &&
  auOf [1,1,1,1,1,2,2] = 26063

theorem sixAuOK_check : sixAuOK = true := by
  native_decide

def infeasibleOK : Bool :=
  let T := tCeil 15
  let D := 2^T - 5^15
  decide (5^8 * auOf [2,1,1,1,1,1,2] + 2^9 * 21614413 < 7 * D)

def okAt (b Q L : Nat) : Bool :=
  branchAt b Q L ||
    ((decide (b = 2) && decide (Q = 8) && decide (L = 7)) && infeasibleOK)

def stageOneOK : Bool :=
  allInRange 8 51 (fun Q =>
    allInRange 1 26 (fun L =>
      allInRange 1 3 (fun b => okAt b Q L)))

theorem stageOne_check : stageOneOK = true := by
  native_decide

theorem stageOne_okAt (b Q L : Nat)
    (hb1 : 1 <= b) (hb2 : b <= 2) (hQ8 : 8 <= Q) (hQ50 : Q <= 50)
    (hL1 : 1 <= L) (hL25 : L <= 25) : okAt b Q L = true := by
  have hb3 : b < 3 := by omega
  have hQ51 : Q < 51 := by omega
  have hL26 : L < 26 := by omega
  have hQrange := allInRange_spec 8 51
    (fun Q => allInRange 1 26 (fun L => allInRange 1 3 (fun b => okAt b Q L)))
    stageOne_check Q hQ8 hQ51
  have hLrange := allInRange_spec 1 26
    (fun L => allInRange 1 3 (fun b => okAt b Q L)) hQrange L hL1 hL26
  exact allInRange_spec 1 3 (fun b => okAt b Q L) hLrange b hb1 hb3

#print axioms StringFlow.stageOne_check

end StringFlow
