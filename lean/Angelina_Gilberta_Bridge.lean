import UnifiedCoreBridge
import UnifiedCoreAudit
import S6AuditStage1

/-!
# Angelina--Gilberta bridge

This file isolates the transition from real-orbit reachability to the
`OrbitFrom7` input required by the pure unified core.  The short-depth
instance is proved directly from the finite prefix bridge; the general
instance is left as an explicit definitional target.
-/

namespace S6Audit

/-- A real previous terminal with its five-adic odd part.  Keeping these
fields packaged together prevents the block quotient `q` from being
substituted for the terminal odd part `s`. -/
structure AngelinaGilbertaRealTerminal where
  r : Nat
  s : Nat
  k : Nat
  hprod : s * 5 ^ k = r + 1
  hs_odd : IsOdd s
  hs_not_five : ¬ 5 ∣ s
  hreach : GeneralOrbitFrom7 r

/-- The reset context needed by the full-orbit to legal-orbit bridge. -/
structure AngelinaGilbertaFullOrbitContext
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) (r : Nat) where
  hPrem : _root_.UnifiedCoreAudit.All36_20PremisesNoHge
    j Wp Wj q Aj A_s s W_s r_s L H_s weight
  hrj : r = (Aj + 5 ^ j * q) / 2 ^ Wj
  hReach : FullOrbitFrom7 r
  hReset : ∃ s0 k t δ r_prev : Nat,
    ResetHeadEq s0 j k t δ r ∧
    s0 * 5 ^ k = r_prev + 1 ∧
    PreviousTerminalAtDepth s0 j k r_prev
  hH : 2 ≤ H_s

/-- The general bridge target.  It is intentionally a `def`, not a
theorem: proving it from the full-orbit context without a depth bound is
the remaining assembly step. -/
def angelinaGilbertaBridge : Prop :=
  ∀ (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) (r : Nat),
    AngelinaGilbertaFullOrbitContext
      j Wp Wj q Aj A_s s W_s r_s L H_s weight r →
    OrbitFrom7 r

/-- The short-depth instance of the bridge is closed by the existing
finite full-orbit prefix bridge. -/
theorem angelinaGilbertaBridge_of_short
    (j Wp Wj q Aj A_s s W_s r_s L H_s : Nat)
    (weight : Nat → Nat) (r : Nat)
    (hctx : AngelinaGilbertaFullOrbitContext
      j Wp Wj q Aj A_s s W_s r_s L H_s weight r)
    (hshort : ∃ n : Nat, fullOrbitIter n = r ∧ n ≤ 15) :
    OrbitFrom7 r :=
  fullOrbitFrom7_le15_imp_OrbitFrom7 r hctx.hReach hshort

end S6Audit
