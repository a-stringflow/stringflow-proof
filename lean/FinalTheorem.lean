import FinalStatement
import trinity

/-!
# Internal final assembly target

The public statement is `IsUnboundedOrbit 7`, defined in
`FinalStatement.lean`. This file only contains the internal assembly
theorem for that statement; it is not part of the public interface.
-/

namespace StringFlow

/-- Real assembly bridge: once the corrected decisive window upper
bound and `failureWindowExistence` are closed, the Trinity failure-window
route immediately gives the public divergence statement. -/
theorem five_x_plus_one_diverges_at_7_of_window_and_failure_window
    (hF : CycleBridge.failureWindowExistence)
    (hwin : BlockAutomaton.decisiveWindowValuationBoundCorrected) :
    IsUnboundedOrbit 7 :=
  Trinity.five_x_plus_one_diverges_at_7_of_failure_window_and_window_bound
    hF hwin

/-- Internal assembly target for the public statement. -/
theorem five_x_plus_one_diverges_at_7 : IsUnboundedOrbit 7 := by
  -- Internal assembly is not complete.
  sorry

end StringFlow
