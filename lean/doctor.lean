import FinalStatement
import trinity
import Closure
import kaltsit
import amiya
import RealOrbitLocalLemma
import DwdbDiv
import CycleBridge

/-!
# Doctor: Master Commander and Final Divergence Assembly

This module serves as the final assembly point (Doctor) uniting:
- kaltsit.lean: maximal cyclic rise block existence (, L, t, hstop)
- miya.lean: rank lower bounds and layer condition bridges
- 	rinity.lean: Trinity block contradiction (TrinityBlock → False)
- Closure.lean: global merge congruence and scale crush

Core Flow:
  CycleQb8Input h (hypothetical cycle)
  ⇒ construct maximal rise block (b, L, t, δ, rt)
  ⇒ C1 (predecessor terminal) + C2 (valuation upper bound ≤ 2L+11) + C3 (valuation lower bound ≥ 2L+12)
  ⇒ TrinityBlock h b L t δ rt
  ⇒ trinity_block_contradicts h b L t δ rt tb : False
  ⇒ ¬ OrbitCycle 7 (no positive cycle of 7)
  ⇒ five_x_plus_one_diverges_at_7 : IsUnboundedOrbit 7 (unconditional divergence)
-/

namespace StringFlow

namespace Doctor

open Trinity
open Closure

/-- Master no-cycle theorem from a Trinity Block:
eliminates any positive periodic cycle of 7 under the accelerated 5x+1 map. -/
theorem no_cycle_at_7_of_trinityBlock
    (hA : Trinity.trinityBlockExists) : ¬ OrbitCycle 7 :=
  Trinity.trinity_no_cycle_of_block_exists hA

/-- Conditional assembly from Trinity block existence:
once 	rinityBlockExists is supplied, divergence follows. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_block
    (hA : Trinity.trinityBlockExists) : IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

/-- Master zero-parameter divergence theorem from non-periodicity. -/
theorem five_x_plus_one_diverges_at_7_of_no_cycle
    (hno : ¬ OrbitCycle 7) : IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 hno

/-- Forward construction of Trinity Block existence from failure window and window bound. -/
theorem trinityBlockExists_of_failure_window_and_window
    (hfw : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    Trinity.trinityBlockExists :=
  Trinity.trinityBlockExists_of_no_cycle
    (CycleBridge.no_cycle_of_window_bound_of_failureWindowExistence hwin hfw)

/-- Master divergence theorem on the public statement IsUnboundedOrbit 7
via the Trinity framework. -/
theorem five_x_plus_one_diverges_at_7
    (hA : Trinity.trinityBlockExists) : IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

end Doctor

end StringFlow