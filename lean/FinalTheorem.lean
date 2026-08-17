import FinalStatement
import trinity
import Closure
import RealOrbitLocalLemma
import DwdbDiv
import kaltsit

namespace StringFlow

open Closure

/-- Real assembly bridge: once the corrected decisive window upper
bound and `failureWindowExistence` are closed, the Trinity failure-window
route immediately gives the public divergence statement. -/
theorem five_x_plus_one_diverges_at_7_of_window_and_failure_window
    (hF : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    IsUnboundedOrbit 7 :=
  Trinity.five_x_plus_one_diverges_at_7_of_failure_window_and_window_bound
    hF hwin

/-- Trinity-block route: once `trinityBlockExists` is supplied, the
public statement is immediate.  This is the exact assembly requested
for the final theorem; the remaining work is supplying `hA`. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_block
    (hA : Trinity.trinityBlockExists) :
    IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

/-- Internal assembly target for the public statement. -/
theorem five_x_plus_one_diverges_at_7
    (hF : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    IsUnboundedOrbit 7 :=
  five_x_plus_one_diverges_at_7_of_window_and_failure_window hF hwin

end StringFlow
