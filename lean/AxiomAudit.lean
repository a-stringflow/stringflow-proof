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

-- Statement check: segment-length-`d` candidate bridge.
#check candidate_parameterization_of_reset_full_orbit_d

-- Axioms used by the segment-length-`d` candidate bridge.
#print axioms candidate_parameterization_of_reset_full_orbit_d

-- Statement check: `d=2` exclusion assembled from the reset bridge.
#check d2_exclusion_of_reset_candidate

-- Axioms used by the `d=2` reset-candidate exclusion.
#print axioms d2_exclusion_of_reset_candidate

-- Statement check: depth-16/17 step weights and `m2>0` start constraint.
#check orbitStepWeight_16_eq_one
#check orbitStepWeight_17_ge_three
#check no_t2_step_at_depth_16_17
#check m2_pos_first_step_weight_two

-- Axioms used by the new finite-prefix `m2>0` constraints.
#print axioms orbitStepWeight_16_eq_one
#print axioms no_t2_step_at_depth_16_17
#print axioms m2_pos_first_step_weight_two

-- Statement check: `m2>0` run start pushed to depth at least 18.
#check m2_pos_tail_start_ge_18

-- Axioms used by the depth-`≥18` run-start constraint.
#print axioms m2_pos_tail_start_ge_18

-- Statement check: modulo-5 rigidity of all block states.
#check mod5_cancel_two
#check mod5_cancel_four
#check legal_step_next_mod5
#check blockState_next_mod5_of_premises
#check blockState_mod5_of_premises

-- Axioms used by the modulo-5 block rigidity lemmas.
#print axioms legal_step_next_mod5
#print axioms blockState_mod5_of_premises

-- Statement check: full `m2>0` audit with modulo-5 rigidity.
#check tail_failure_m2_pos_audit_mod5

-- Axioms used by the combined `m2>0` audit.
#print axioms tail_failure_m2_pos_audit_mod5

-- Statement checks: generalized reset bridge and `hr` lemmas.
#check candidateX_of_reset_and_terminal_general
#check terminal_chain_identity
#check terminal_chain_identity_of_full_orbit_d
#check previous_terminal_hr_of_word_and_segment
#check d2_exclusion_of_corrected_residue

-- Axioms used by the generalized reset bridge and `hr` lemmas.
#print axioms candidateX_of_reset_and_terminal_general
#print axioms terminal_chain_identity
#print axioms terminal_chain_identity_of_full_orbit_d
#print axioms previous_terminal_hr_of_word_and_segment
#print axioms d2_exclusion_of_corrected_residue

-- Axioms used by the `k≥1` exclusion chain.
#print axioms reset_k_is_five_valuation
#print axioms kge1_excluded_by_segment_step

-- Statement checks: `m2>0` word-weight relations and the size bound.
#check weight_diff_ge_steps
#check m2_pos_tail_weight_sum
#check m2_pos_H_s_upper
#check m2_pos_run_start_depth
#check m2_pos_u_size_bound
#check fullOrbitIter_lt_five_pow
#check m2_pos_size_bound_sharp
#check m2_pos_W_s_Wp_lower
#check m2_pos_word_size_wiring
#check m2_pos_H_s_exact
#check m2_pos_failure_size_inequality
#check m2_pos_failure_word_inequality
#check orbitSegmentWord_getD
#check m2_pos_block_head_depth_ge_18
#check m2_pos_block_head_depth_ge_19

-- Axioms used by the `m2>0` word-weight relations.
#print axioms weight_diff_ge_steps
#print axioms m2_pos_tail_weight_sum
#print axioms m2_pos_H_s_upper
#print axioms m2_pos_run_start_depth
#print axioms m2_pos_u_size_bound
#print axioms fullOrbitIter_lt_five_pow
#print axioms m2_pos_size_bound_sharp
#print axioms m2_pos_W_s_Wp_lower
#print axioms m2_pos_word_size_wiring
#print axioms m2_pos_H_s_exact
#print axioms m2_pos_failure_size_inequality
#print axioms m2_pos_failure_word_inequality
#print axioms orbitSegmentWord_getD
#print axioms m2_pos_block_head_depth_ge_18
#print axioms m2_pos_block_head_depth_ge_19

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
