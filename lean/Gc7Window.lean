import Td1Phase2
import Gc13

/-!
# GC-7 13.1 window re-read in exact rational form

The section-13.1 real window

    m <= (5 + (5/3) * 2^delta) / (5 * (2^delta - 1))

is rewritten with the exact identity `2^delta = 2^T / 5^P`, where
`T = tCeil P`.  The cleared GC-7 bound

    3 * m * (2^T - 5^P) <= 3 * 5^P + 2^T

then has the same rational right-hand side.  This module certifies
that the two rational forms agree on the six small-`P` table used by
GC-13.
-/

namespace StringFlow.GC

/-- The cleared GC-7 `m` window: `(3*5^P + 2^T)/(3*(2^T - 5^P))`. -/
def gc7WindowCleared (P : Nat) : Rat :=
  let T := StringFlow.GC.gc13T P
  let N : Nat := 3 * 5 ^ P + 2 ^ T
  let D : Nat := 3 * (2 ^ T - 5 ^ P)
  ((N : Rat) / (D : Rat))

/-- The section-13.1 window with `2^delta = 2^T / 5^P`. -/
def gc7WindowDelta (P : Nat) : Rat :=
  let T := StringFlow.GC.gc13T P
  let q : Rat := (((2 ^ T : Nat) : Rat) / ((5 ^ P : Nat) : Rat))
  (5 + (5 / 3 : Rat) * q) / (5 * (q - 1))

/-- The two rational forms agree for the six small-`P` values. -/
def gc7WindowRatOK : Bool :=
  [31, 59, 205, 351, 497, 643].all (fun P =>
    decide (gc7WindowCleared P = gc7WindowDelta P))

theorem gc7_window_rat_check : gc7WindowRatOK = true := by
  native_decide

theorem gc7_window_rat_31 : gc7WindowCleared 31 = gc7WindowDelta 31 := by
  native_decide

theorem gc7_window_rat_59 : gc7WindowCleared 59 = gc7WindowDelta 59 := by
  native_decide

theorem gc7_window_rat_205 : gc7WindowCleared 205 = gc7WindowDelta 205 := by
  native_decide

theorem gc7_window_rat_351 : gc7WindowCleared 351 = gc7WindowDelta 351 := by
  native_decide

theorem gc7_window_rat_497 : gc7WindowCleared 497 = gc7WindowDelta 497 := by
  native_decide

theorem gc7_window_rat_643 : gc7WindowCleared 643 = gc7WindowDelta 643 := by
  native_decide

end StringFlow.GC
