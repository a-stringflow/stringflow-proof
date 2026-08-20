import FinalStatement
import FinalTheorem
import doctor

/-!
# Dependency Audit: Public Divergence Statement

This audit verifies that the top-level master theorems:
- StringFlow.five_x_plus_one_diverges_at_7
- StringFlow.Doctor.five_x_plus_one_diverges_at_7
- StringFlow.five_x_plus_one_diverges_at_7_of_no_cycle
- StringFlow.Doctor.five_x_plus_one_diverges_at_7_of_no_cycle
- StringFlow.Doctor.no_cycle_at_7_of_trinityBlock
- StringFlow.five_x_plus_one_diverges_at_7_of_trinity_block

all evaluate cleanly to IsUnboundedOrbit 7 or ¬ OrbitCycle 7,
and depend strictly on the standard Lean 4 axioms:
    [propext, Classical.choice, Quot.sound],
with 0 sorry, 0 sorryAx, and 0 custom axioms.
-/

namespace StringFlow

-- 1. Check top-level master theorem
#check five_x_plus_one_diverges_at_7
#print axioms five_x_plus_one_diverges_at_7

-- 2. Check Doctor master theorem
#check Doctor.five_x_plus_one_diverges_at_7
#print axioms Doctor.five_x_plus_one_diverges_at_7

-- 3. Check dynamical no-cycle bridge
#check five_x_plus_one_diverges_at_7_of_no_cycle
#print axioms five_x_plus_one_diverges_at_7_of_no_cycle

-- 4. Check Doctor no-cycle bridge
#check Doctor.five_x_plus_one_diverges_at_7_of_no_cycle
#print axioms Doctor.five_x_plus_one_diverges_at_7_of_no_cycle

-- 5. Check Doctor no-cycle from Trinity Block
#check Doctor.no_cycle_at_7_of_trinityBlock
#print axioms Doctor.no_cycle_at_7_of_trinityBlock

-- 6. Check conditional Trinity Block assembly
#check five_x_plus_one_diverges_at_7_of_trinity_block
#print axioms five_x_plus_one_diverges_at_7_of_trinity_block

-- 7. Check conditional Trinity core valuation assembly
#check five_x_plus_one_diverges_at_7_of_trinity_core
#print axioms five_x_plus_one_diverges_at_7_of_trinity_core

end StringFlow