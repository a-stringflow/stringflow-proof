import S6Audit
import SurvExAudit

/-!
# Axiom audit for the S6 / local-lemma final theorems

Run:
  cd lean
  lake env lean AxiomAudit.lean

The output lists every axiom the two final theorems depend on. For the
formalization to be reviewable, the list must contain only trusted Lean
axioms (for example `propext`, `Quot.sound`, `Classical.choice`) and must
not contain `sorryAx` or a custom `axiom`.
-/

namespace S6Audit

-- Statement check: pure t=2 M=1 base exclusion.
#check pure_t2_m1_no_odd_hit

-- Axioms used by `pure_t2_m1_no_odd_hit`.
#print axioms pure_t2_m1_no_odd_hit

-- Statement check: local lemma.
#check local_lemma_final

-- Axioms used by `local_lemma_final`.
#print axioms local_lemma_final

end S6Audit

namespace StringFlow

-- Statement check: final bridge through the SURV-EX/TD0 no-cycle interface.
#check five_x_plus_one_diverges_at_7_of_surv_ex_td0

-- Axioms used by the final bridge.
#print axioms five_x_plus_one_diverges_at_7_of_surv_ex_td0

end StringFlow

namespace StringFlow.SurvEx

-- Statement check: L-B'c branch is formally closed.
#check lb_prime_c

-- Axioms used by `lb_prime_c`.
#print axioms lb_prime_c

end StringFlow.SurvEx
