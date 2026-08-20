import FinalStatement
import trinity
import Closure
import RealOrbitLocalLemma
import DwdbDiv
import kaltsit
import doctor

namespace StringFlow

open Closure

/-- Direct dynamical divergence bridge: if the accelerated 5x+1 orbit of 7
never enters a periodic cycle (¬ OrbitCycle 7), then by the Dirichlet
Pigeonhole Principle on bounded subsets of ℕ, the orbit is unbounded. -/
theorem five_x_plus_one_diverges_at_7_of_no_cycle
    (h : ¬ OrbitCycle 7) :
    IsUnboundedOrbit 7 :=
  unbounded_of_no_cycle 7 h

/-- Trinity-block route: once 	rinityBlockExists is supplied on a real
selected rise block, the three 2-adic valuation constraints contradict,
eliminating all cycles and yielding the public divergence statement. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_block
    (hA : Trinity.trinityBlockExists) :
    IsUnboundedOrbit 7 :=
  Trinity.trinity_unbounded_of_block_exists hA

/-- Trinity core valuation route: once the joint valuation core
TrinityCoreValuation is supplied, the public divergence statement follows. -/
theorem five_x_plus_one_diverges_at_7_of_trinity_core
    (hcore : Trinity.TrinityCoreValuation)
    (hasm : Trinity.trinityBlockExistsOfCoreValuation) :
    IsUnboundedOrbit 7 :=
  Trinity.five_x_plus_one_diverges_at_7_of_trinity_core hcore hasm

/-- Master divergence theorem: connects Trinity block existence directly to
the public divergence statement IsUnboundedOrbit 7. -/
theorem five_x_plus_one_diverges_at_7
    (hA : Trinity.trinityBlockExists) :
    IsUnboundedOrbit 7 :=
  Doctor.five_x_plus_one_diverges_at_7 hA

end StringFlow