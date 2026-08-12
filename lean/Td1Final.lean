import StageOneScan
import Td1Phase2
import Td1Window

/-!
# TD-1 certificate assembly

This module collects the finite certificate gates of TD-1 into one
theorem.  The individual components remain authoritative:

- `stageOneOK`: 52.21.1 `m0` threshold certificate;
- `stageOneScanOK`: 52.21.1 word-level certificate;
- `b0OK`: phase-2 `S <= 64` implies `P <= 188`;
- `phase2UpperBoundOK`: G5' Rat records plus the two base
  `mt >= 8/3` checks.
-/

namespace StringFlow.TD1

/-- The assembled TD-1 certificate gates. -/
theorem td1_cert_components :
    StringFlow.stageOneOK = true ∧
      StringFlow.stageOneScanOK = true ∧
      b0OK = true ∧
      phase2UpperBoundOK = true := by
  constructor
  · exact StringFlow.stageOne_check
  · constructor
    · exact StringFlow.stageOneScan_check
    · constructor
      · exact b0_check
      · exact phase2_upper_bound_check

/-- The two basin-bound certificates used by phase 2, assembled. -/
theorem td1_basin_bounds :
    (∀ m : Nat, 7 ≤ m → m < 617 → admissible m →
      ∃ c : Cert, coverCert cert617 m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 26) ∧
    (∀ m : Nat, 7 ≤ m → m ≤ 1000000 → admissible m →
      ∃ c : Cert, coverCert cert1e6 m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 64) := by
  constructor
  · exact StringFlow.basin_617_cert
  · exact StringFlow.basin_1e6_cert

/-- The full certificate layer of TD-1: all four certificate gates
plus both basin-bound certificates. -/
theorem td1_cert_all :
    (StringFlow.stageOneOK = true ∧ StringFlow.stageOneScanOK = true ∧
      b0OK = true ∧ phase2UpperBoundOK = true) ∧
    (∀ m : Nat, 7 ≤ m → m < 617 → admissible m →
      ∃ c : Cert, coverCert cert617 m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 26) ∧
    (∀ m : Nat, 7 ≤ m → m ≤ 1000000 → admissible m →
      ∃ c : Cert, coverCert cert1e6 m = some c ∧
        ∃ S : Nat, firstC3H c.w.length m = (true, S) ∧ S ≤ 64) := by
  rcases td1_cert_components with ⟨h1, h2, h3, h4⟩
  rcases td1_basin_bounds with ⟨hb1, hb2⟩
  exact ⟨⟨h1, h2, h3, h4⟩, hb1, hb2⟩

/-- The two `Z`-to-`R` window bridges, assembled. -/
theorem td1_window_bridges :
    (∀ Q m M0 : Nat,
      (5 ^ Q * M0 + a0 Q < 2 * 8 ^ Q * m) ↔
        (3 * 5 ^ Q * M0 + 8 ^ Q < 6 * 8 ^ Q * m + 5 ^ Q)) ∧
    (∀ Q m M0 : Nat,
      (5 ^ Q * M0 + a0 Q < 4 * 8 ^ Q * m) ↔
        (3 * 5 ^ Q * M0 + 8 ^ Q < 12 * 8 ^ Q * m + 5 ^ Q)) := by
  constructor
  · intro Q m M0
    exact td1A_Z_lt_two_iff_R_lt_LA Q m M0
  · intro Q m M0
    exact td1B_Z_lt_four_iff_R_lt_LB Q m M0

end StringFlow.TD1
