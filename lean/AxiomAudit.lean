import S6Audit
import SurvExAudit
import UnifiedCoreBridge

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

-- Statement check: full-orbit block word is a continuous suffix.
#check blockWord_eq_orbitSegment_of_fullOrbit

-- Axioms used by the word-segment continuity lemma.
#print axioms blockWord_eq_orbitSegment_of_fullOrbit

-- Statement check: every block state from a full-orbit head is full-orbit.
#check blockState_fullOrbit_of_premises_fullOrbit

-- Axioms used by the block-state full-orbit transfer.
#print axioms blockState_fullOrbit_of_premises_fullOrbit

-- Statement check: exact `m2>0` tail residue on `u`.
#check tail_failure_m2_even_u_mod8
#check tail_failure_m2_odd_u_mod8

-- Axioms used by the `m2>0` residue lemmas.
#print axioms tail_failure_m2_even_u_mod8
#print axioms tail_failure_m2_odd_u_mod8

-- Statement check: full `m2>0` tail audit.
#check tail_failure_m2_pos_audit

-- Axioms used by the `m2>0` tail audit.
#print axioms tail_failure_m2_pos_audit

-- Statement check: exact full-orbit predecessor identification.
#check candidateRj_eq_fullOrbitIter_of_weight

-- Axioms used by the exact-predecessor bridge lemma.
#print axioms candidateRj_eq_fullOrbitIter_of_weight

-- Statement check: packaged candidate parameterization from reset data.
#check candidate_parameterization_of_reset_full_orbit

-- Axioms used by the packaged candidate bridge.
#print axioms candidate_parameterization_of_reset_full_orbit

-- Statement check: `d=1` exclusion assembled from the reset bridge.
#check d1_exclusion_of_reset_candidate

-- Axioms used by the `d=1` reset-candidate exclusion.
#print axioms d1_exclusion_of_reset_candidate

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
