import FinalStatement

/-!
# Internal final assembly target

The public statement is `IsUnboundedOrbit 7`, defined in
`FinalStatement.lean`. This file only contains the internal assembly
theorem for that statement; it is not part of the public interface.
-/

namespace StringFlow

/-- Internal assembly target for the public statement. -/
theorem five_x_plus_one_diverges_at_7 : IsUnboundedOrbit 7 := by
  -- Internal assembly is not complete.
  sorry

end StringFlow
