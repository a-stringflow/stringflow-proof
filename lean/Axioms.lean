import CollatzRank
import TwoPowPlusOne
import BalanceReduction
import FBeta
import PhOne
import PhTwo
import Qb
import Gc
import Gc15
import Gc13
import Td1
import Td1Window
import Td1Phase2
import Td1Final
import Gc7Window
import Td1S3
import Td1Interval
import Td0Final

/-!
# Axiom check

These `#print axioms` commands are part of the build verification:
every theorem used by the string-flow algebra formalization must be
provable without custom axioms (`no axioms`).
-/

#print axioms StringFlow.binaryWeight_add_mul_two_pow
#print axioms StringFlow.binaryWeight_complement
#print axioms StringFlow.binaryWeight_le_of_lt_pow_two
#print axioms StringFlow.binaryLength_two_pow
#print axioms StringFlow.binaryLength_two_pow_sub_one
#print axioms StringFlow.binaryZeros_four_mul
#print axioms StringFlow.binaryZeros_two_mul
#print axioms StringFlow.binaryLength_add_mul_two_pow
#print axioms StringFlow.binaryWeight_mul_all_ones
#print axioms StringFlow.binaryLength_mul_all_ones
#print axioms StringFlow.digitDelta_add
#print axioms StringFlow.balance_mersenne
#print axioms StringFlow.balance_two_pow_add_one
#print axioms StringFlow.collatzStep_collatzProfileN
#print axioms StringFlow.profileRank_collatzProfileN_eq_V
#print axioms StringFlow.collatz_no_descent_profile_rank
#print axioms StringFlow.no_regular_rank_of_balance
#print axioms StringFlow.five_x_one_no_descent_profile_rank
#print axioms StringFlow.mersenne_no_regular_rank
#print axioms StringFlow.two_pow_add_one_no_regular_rank
#print axioms StringFlow.n_eq_two_pow_mul_oddPart
#print axioms StringFlow.oddPart_odd_of_pos
#print axioms StringFlow.oddPart_le_half_of_even
#print axioms StringFlow.iterate_halve_pow_mul
#print axioms StringFlow.iterate_fStep_eq_halve_while_even
#print axioms StringFlow.iterate_fStep_odd_reaches_uStep
#print axioms StringFlow.uStep_lt_of_lt
#print axioms StringFlow.uStep_le_b_of_le
#print axioms StringFlow.iterate_uStep_lt_of_gt
#print axioms StringFlow.not_cyclePoint_uStep_of_gt
#print axioms StringFlow.iterate_halve_le
#print axioms StringFlow.fStep_le_two_b_of_odd_le
#print axioms StringFlow.fStep_le_two_b_of_even_le
#print axioms StringFlow.iterate_fStep_le_two_b_run
#print axioms StringFlow.iterate_add
#print axioms StringFlow.iterate_fStep_uRunLenSum
#print axioms StringFlow.iterate_fStep_le_two_b_of_odd_le
#print axioms StringFlow.iterate_fStep_odd_is_run_boundary
#print axioms StringFlow.uStep_cyclePoint_iff_fStep_cyclePoint
#print axioms StringFlow.exists_uStep_cyclePoint_of_fStep_cyclePoint
#print axioms StringFlow.fStep_cyclePoint_le_two_b
#print axioms StringFlow.eventually_cyclePoint
#print axioms StringFlow.bitCount_add
#print axioms StringFlow.bitCount_single_initial
#print axioms StringFlow.bitCount_first_run
#print axioms StringFlow.fStep_period_of_uStep_period
#print axioms StringFlow.fStep_parityWord_count_of_uStep_steps
#print axioms StringFlow.fStep_parityWord_count_of_uStep_period
#print axioms StringFlow.PH.prefixWeight_segment
#print axioms StringFlow.PH.ph1_word_decomposition
#print axioms StringFlow.PH.localLambda_eq_of_wordWeights_agree
#print axioms StringFlow.PH.localLambda_firstRun_eq
#print axioms StringFlow.PH.ph2_lower_bound
#print axioms StringFlow.PH.ph2_lower_bound_of_firstRunPrefix
#print axioms StringFlow.QB.qb7_core
#print axioms StringFlow.QB.qb7_no_internal_data
#print axioms StringFlow.QB.c3_step_lt
#print axioms StringFlow.QB.rise_step_gt
#print axioms StringFlow.QB.c3_chain_strictlyDecreasing
#print axioms StringFlow.QB.startsFrom_consecutive_of_allOne
#print axioms StringFlow.QB.qb8_structure
#print axioms StringFlow.GC.c3_chain_closed_form
#print axioms StringFlow.GC.c3_chain_residual
#print axioms StringFlow.GC.c3_chain_residual_inverse
#print axioms StringFlow.GC.c3_residual_unique_small
#print axioms StringFlow.GC.two_pow_mod3
#print axioms StringFlow.GC.c3_mod3_of_even
#print axioms StringFlow.GC.c3_mod3_of_odd
#print axioms StringFlow.GC.gc42_mod16_of_weight_three
#print axioms StringFlow.GC.gc42_mod16_of_weight_ge_four
#print axioms StringFlow.GC.gc41_three_mul_congruence
#print axioms StringFlow.GC.gc41_three_mul_residue
#print axioms StringFlow.GC.gc41_q8_candidate
#print axioms StringFlow.GC.gc41_q9_no_odd
#print axioms StringFlow.GC.gc41_q_ge10_no
#print axioms StringFlow.GC.gc41_b_zero_no_solution
#print axioms StringFlow.GC.gc43_linear_bound
#print axioms StringFlow.GC.four_pow_le_five_pow
#print axioms StringFlow.GC.geomRise_invariant
#print axioms StringFlow.GC.geomRise_bound
#print axioms StringFlow.GC.risePart_le_geomRise
#print axioms StringFlow.GC.risePart_bound
#print axioms StringFlow.GC.geomTail_invariant
#print axioms StringFlow.GC.geomTail_bound
#print axioms StringFlow.GC.c3PartFrom_le
#print axioms StringFlow.GC.c3PartFrom_cleared_bound
#print axioms StringFlow.GC.gc7_pmi_cleared_bound
#print axioms StringFlow.GC.gc7_m_cleared_bound
#print axioms StringFlow.GC.gc15_rise_all_one_bound
#print axioms StringFlow.GC.gc15_rise_cons_one
#print axioms StringFlow.GC.gc15_rise_cons_two
#print axioms StringFlow.GC.gc15_risePart_bound
#print axioms StringFlow.GC.gc13_allOK_check
#print axioms StringFlow.GC.gc13_t1_bound
#print axioms StringFlow.GC.gc13_t2_bound
#print axioms StringFlow.GC.pow_two_lt_imp_le
#print axioms StringFlow.GC.gc13_u0_31
#print axioms StringFlow.GC.gc13_u0_59
#print axioms StringFlow.GC.gc13_u0_205
#print axioms StringFlow.GC.gc13_u0_351
#print axioms StringFlow.GC.gc13_u0_497
#print axioms StringFlow.GC.gc13_u0_643
#print axioms StringFlow.GC.gc13_long_rise_contradicts
#print axioms StringFlow.GC.gc7_window_for_gc13
#print axioms StringFlow.TD1.b1_orbit_check
#print axioms StringFlow.TD1.b1B_uReq_check
#print axioms StringFlow.TD1.b1B_large_uReq_check
#print axioms StringFlow.TD1.b1B_uReq_solutions_full
#print axioms StringFlow.TD1.b1_201
#print axioms StringFlow.TD1.basin_617_sharp
#print axioms StringFlow.TD1.phase2_m_ge_201
#print axioms StringFlow.TD1.phase2_m_ge_201_of_weight
#print axioms StringFlow.TD1.certBasin25A_check
#print axioms StringFlow.TD1.certBasin25B_check
#print axioms StringFlow.TD1.b1B_delta_value
#print axioms StringFlow.TD1.b1A_alt_delta_values
#print axioms StringFlow.TD1.a0_three_mul
#print axioms StringFlow.TD1.td1A_Z_lt_two_iff
#print axioms StringFlow.TD1.td1B_Z_lt_four_iff
#print axioms StringFlow.TD1.td1B_Z_gt_four_iff
#print axioms StringFlow.TD1.td1A_Z_lt_two_iff_R_lt_LA
#print axioms StringFlow.TD1.td1B_Z_lt_four_iff_R_lt_LB
#print axioms StringFlow.TD1.td1A_R_lt_LA_iff
#print axioms StringFlow.TD1.td1A_R_lt_UA_iff
#print axioms StringFlow.TD1.td1B_R_lt_LB_iff
#print axioms StringFlow.TD1.td1B_R_lt_UB_iff
#print axioms StringFlow.TD1.phase2_delta_check
#print axioms StringFlow.TD1.phase2_upper_201_31
#print axioms StringFlow.tCeil_pow_lt
#print axioms StringFlow.TD1.phase2_upper_617_59
#print axioms StringFlow.TD1.b0_check
#print axioms StringFlow.TD1.b0_spec
#print axioms StringFlow.TD1.phase2_record_rat_check
#print axioms StringFlow.TD1.phase2_tRat_ge_t31
#print axioms StringFlow.TD1.phase2_tRat_ge_t59
#print axioms StringFlow.TD1.phase2_upper_bound_check
#print axioms StringFlow.TD1.td1_cert_components
#print axioms StringFlow.TD1.td1_basin_bounds
#print axioms StringFlow.TD1.td1_cert_all
#print axioms StringFlow.TD1.td1_window_bridges
#print axioms StringFlow.GC.gc7_window_rat_check
#print axioms StringFlow.GC.gc7_window_rat_31
#print axioms StringFlow.GC.gc7_window_rat_59
#print axioms StringFlow.GC.gc7_window_rat_205
#print axioms StringFlow.GC.gc7_window_rat_351
#print axioms StringFlow.GC.gc7_window_rat_497
#print axioms StringFlow.GC.gc7_window_rat_643
#print axioms StringFlow.TD1.three_mul_s3
#print axioms StringFlow.TD1.a0_sub_s3
#print axioms StringFlow.TD1.td1A_areq_gt_amax_iff
#print axioms StringFlow.TD1.td1A_areq_lt_a0_iff
#print axioms StringFlow.TD1.td1B_areq_gt_amax_iff
#print axioms StringFlow.TD1.td1B_areq_lt_a0_iff

#check StringFlow.no_regular_rank_of_balance
#check StringFlow.balance_two_pow_add_one
#check StringFlow.balance_mersenne
#check StringFlow.five_x_one_no_descent_profile_rank
#check StringFlow.mersenne_no_regular_rank
#check StringFlow.two_pow_add_one_no_regular_rank
#check StringFlow.iterate_fStep_odd_reaches_uStep
#check StringFlow.uStep_lt_of_lt
#check StringFlow.not_cyclePoint_uStep_of_gt
#check StringFlow.uStep_cyclePoint_iff_fStep_cyclePoint
#check StringFlow.fStep_cyclePoint_le_two_b
#check StringFlow.eventually_cyclePoint
#check StringFlow.fStep_period_of_uStep_period
#check StringFlow.fStep_parityWord_count_of_uStep_period
#check StringFlow.PH.ph1_word_decomposition
#check StringFlow.PH.localLambda_eq_of_wordWeights_agree
#check StringFlow.PH.ph2_lower_bound
#check StringFlow.PH.ph2_lower_bound_of_firstRunPrefix
#check StringFlow.QB.qb7_core
#check StringFlow.QB.qb7_no_internal_data
#check StringFlow.QB.c3_step_lt
#check StringFlow.QB.rise_step_gt
#check StringFlow.QB.c3_chain_strictlyDecreasing
#check StringFlow.QB.startsFrom_consecutive_of_allOne
#check StringFlow.QB.qb8_structure
#check StringFlow.GC.c3_chain_closed_form
#check StringFlow.GC.c3_chain_residual
#check StringFlow.GC.c3_chain_residual_inverse
#check StringFlow.GC.c3_residual_unique_small
#check StringFlow.GC.c3_mod3_of_even
#check StringFlow.GC.c3_mod3_of_odd
#check StringFlow.GC.gc42_mod16_of_weight_three
#check StringFlow.GC.gc42_mod16_of_weight_ge_four
#check StringFlow.GC.gc41_three_mul_residue
#check StringFlow.GC.gc41_b_zero_no_solution
#check StringFlow.GC.gc43_linear_bound
#check StringFlow.GC.geomRise_invariant
#check StringFlow.GC.geomRise_bound
#check StringFlow.GC.risePart_bound
#check StringFlow.GC.geomTail_bound
#check StringFlow.GC.c3PartFrom_le
#check StringFlow.GC.c3PartFrom_cleared_bound
#check StringFlow.GC.gc7_pmi_cleared_bound
#check StringFlow.GC.gc7_m_cleared_bound
#check StringFlow.GC.gc15_rise_all_one_bound
#check StringFlow.GC.gc15_rise_cons_one
#check StringFlow.GC.gc15_rise_cons_two
#check StringFlow.GC.gc15_risePart_bound
#check StringFlow.GC.gc13_allOK_check
#check StringFlow.GC.gc13_t1_bound
#check StringFlow.GC.gc13_t2_bound
#check StringFlow.GC.pow_two_lt_imp_le
#check StringFlow.GC.gc13_u0_31
#check StringFlow.GC.gc13_u0_59
#check StringFlow.GC.gc13_u0_205
#check StringFlow.GC.gc13_u0_351
#check StringFlow.GC.gc13_u0_497
#check StringFlow.GC.gc13_u0_643
#check StringFlow.GC.gc13_long_rise_contradicts
#check StringFlow.GC.gc7_window_for_gc13
#check StringFlow.TD1.b1_201
#check StringFlow.TD1.basin_617_sharp
#check StringFlow.TD1.phase2_m_ge_201
#check StringFlow.TD1.phase2_m_ge_201_of_weight
#check StringFlow.TD1.b1B_uReq_solutions_full
#check StringFlow.TD1.b1A_alt_delta_values
#check StringFlow.TD1.td1A_Z_lt_two_iff
#check StringFlow.TD1.td1B_Z_gt_four_iff
#check StringFlow.TD1.td1A_Z_lt_two_iff_R_lt_LA
#check StringFlow.TD1.td1B_Z_lt_four_iff_R_lt_LB
#check StringFlow.TD1.td1A_R_lt_UA_iff
#check StringFlow.TD1.td1B_R_lt_UB_iff
#check StringFlow.TD1.phase2_delta_check
#check StringFlow.TD1.phase2_upper_201_31
#check StringFlow.tCeil_pow_lt
#check StringFlow.TD1.phase2_upper_617_59
#check StringFlow.TD1.b0_spec
#check StringFlow.TD1.phase2_tRat_ge_t31
#check StringFlow.TD1.phase2_tRat_ge_t59
#check StringFlow.TD1.phase2_upper_bound_check
#check StringFlow.TD1.td1_cert_components
#check StringFlow.TD1.td1_basin_bounds
#check StringFlow.TD1.td1_cert_all
#check StringFlow.TD1.td1_window_bridges
#check StringFlow.GC.gc7_window_rat_check
#check StringFlow.GC.gc7_window_rat_31
#check StringFlow.GC.gc7_window_rat_59
#check StringFlow.GC.gc7_window_rat_205
#check StringFlow.GC.gc7_window_rat_351
#check StringFlow.GC.gc7_window_rat_497
#check StringFlow.GC.gc7_window_rat_643
#check StringFlow.TD1.three_mul_s3
#check StringFlow.TD1.a0_sub_s3
#check StringFlow.TD1.td1A_areq_gt_amax_iff
#check StringFlow.TD1.td1A_areq_lt_a0_iff
#check StringFlow.TD1.td1B_areq_gt_amax_iff
#check StringFlow.TD1.td1B_areq_lt_a0_iff
#print axioms StringFlow.TD0.td0_of_qb8_orbit
#check StringFlow.TD0.td0_of_qb8_orbit
#print axioms StringFlow.TD0.td0_of_qb8OrbitInput
#check StringFlow.TD0.td0_of_qb8OrbitInput
#print axioms StringFlow.TD0.td0_of_qb8OrbitGC7Input
#check StringFlow.TD0.td0_of_qb8OrbitGC7Input
#print axioms StringFlow.TD0.td0_of_qb8OrbitCycleInput
#check StringFlow.TD0.td0_of_qb8OrbitCycleInput
#print axioms StringFlow.TD0.td0_of_qb8OrbitB0Input
#check StringFlow.TD0.td0_of_qb8OrbitB0Input
#print axioms StringFlow.TD0.td0_of_qb8CycleAbstract
#check StringFlow.TD0.td0_of_qb8CycleAbstract
#print axioms StringFlow.TD0.td0_of_qb8OrbitU1Input
#check StringFlow.TD0.td0_of_qb8OrbitU1Input
#print axioms StringFlow.TD0.td0_of_qb8OrbitStructuralInput
#check StringFlow.TD0.td0_of_qb8OrbitStructuralInput
#print axioms StringFlow.TD0.td0_of_qb8OrbitStructuralU1Input
#check StringFlow.TD0.td0_of_qb8OrbitStructuralU1Input
#check StringFlow.TD0.qb8_orbit_of_structuralU1Input
#check StringFlow.TD0.qb8_orbit_of_structuralInput
#check StringFlow.TD0.qb8_orbit_of_u1Input
#check StringFlow.TD0.qb8_orbit_of_firstWord_u1
#check StringFlow.TD0.qb8_orbit_of_b0Input
#check StringFlow.TD0.qb8_orbit_of_cycleInput
#check StringFlow.TD0.qb8_orbit_of_gc7Input
#check StringFlow.TD0.qb8_orbit_of_firstWord
#check StringFlow.TD0.P_lt_205_of_tCeil_eq
#check StringFlow.TD0.pmiTotal_eq_five_mul_D
#check StringFlow.TD0.pow_two_lt_two_mul_of_gc7
#check StringFlow.TD0.tCeil_eq_of_gc7_and_cycle
#check StringFlow.TD0.log2_five_lt_nineteen_eighths
#print axioms StringFlow.TD0.P_lt_205_of_b0
#check StringFlow.TD0.P_lt_205_of_b0
#check StringFlow.TD0.log2_four_thirds_lt_half
#check StringFlow.TD0.pow_six_lt_eight_mul
#check StringFlow.TD0.log_lt_of_pow_six
#print axioms StringFlow.TD0.P_lt_205_of_pow_six
#check StringFlow.TD0.P_lt_205_of_pow_six
#check StringFlow.TD0.wordOK_of_mem_one_two
#check StringFlow.TD0.A_lt_five_pow_add_two_pow
