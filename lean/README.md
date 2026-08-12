# String-Flow Algebra: Lean 4 formalization

Lean 4.33.0-rc2 is pinned in `lean-toolchain`.

Mathlib is required through `lakefile.lean`
(`leanprover-community/mathlib4` at `v4.33.0-rc2`).  The real-number
layer is used by `Td0Real.lean`.

## Modules

- `BinaryDigits.lean`: `binaryWeight` (`s_2`), `binaryLength` (`L`),
  `twoValuation` (`v_2`), `oddPart`, `binaryZeros`; proofs of the
  shift, all-ones block, complement, digit-sum bound, and disjoint
  block concatenation lemmas.
- `DigitBalance.lean`: `digitDelta` (`s_2(aq)-s_2(q)`), additivity over
  disjoint blocks (Observation 2.30), `BalanceWitness`, and the
  Mersenne special case of Lemma 2.28.
- `TwoPowPlusOne.lean`: the second special case of Lemma 2.28,
  `a = 2^m + 1`, `b = 1`, with the explicit witness
  `d = 2^(2m)-a`, `e = 2^(2m-1)-1`.
- `CollatzRank.lean`: `profileRank` (`A^z B^o`), the exact profile
  family `n_j = 3*2^(j+2)+1`, `V_j = 9*2^j+1`, and the 3x+1 case of
  Theorem 2.25 (no one-dimensional 2-regular descending rank).
- `BalanceReduction.lean`: Theorem 2.29, conditional on the balance
  lemma: whenever odd `d, e` witness `a*d+b = 2^(L(a))*e` with
  `s2(d)=s2(e)`, no `A^z B^o` rank descends along `T_{a,b}`; it also
  contains the 5x+1 trivial-cycle exclusion (rest of Theorem 2.25) and
  the concrete corollaries `mersenne_no_regular_rank`,
  `two_pow_add_one_no_regular_rank`.
- `Valuation.lean`: `v_2`/`oddPart` structural facts: decomposition
  `n = 2^(v2 n) * oddPart(n)`, oddness of the odd part, and the bound
  `oddPart(m) <= m/2` for even `m`.
- `Pmi.lean`: PMI and PMI-B.  It formalizes the algebraic content of
  the prefix margin identity (after clearing the `5^P` denominator):
  `sum_j 5^(P-j)*2^(W_j) = 5*n0*(2^T - 5^P)` from the cycle equation,
  the PMI-B counting bound for bad prefixes `5^j <= 2^(W_j)`, and the
  corollary that a budget below `2*5^P` forces every proper prefix to
  satisfy `2^(W_j) < 5^j`.  Only `propext` and `Quot.sound` are used.
- `PhOne.lean`: PH-1 from `ph_qb_gc_chain.md` section 3.  It defines
  the in-word prefix weight `wordPrefixWeight`, the word cut
  `wordWeights`, the cleared-denominator local factor `localLambda`,
  and the word contribution `wordContribution`.  It proves the PH-1
  `M`-recurrence form `prefixWeight_segment` (`W_{c+k} = W_c + W_w(k)`)
  and the decomposition theorem `ph1_word_decomposition`
  (`C = 2^(W_c) * Lambda` as an integer identity after clearing the
  `5`-denominators), plus the word-independence theorem
  `localLambda_eq_of_wordWeights_agree`.  Only `propext` and
  `Quot.sound` are used.
- `PhTwo.lean`: PH-2 from `ph_qb_gc_chain.md` section 4.  It defines
  the first-run word `firstRunWord t r` (a C3 step of weight `t`
  followed by `r` ones), the cleared-denominator bound numerator
  `phiNumerator`, and proves the exact geometric-run identity
  `localLambda_firstRun_eq` together with the tail-monotone lower
  bound `ph2_lower_bound` and its length form
  `ph2_lower_bound_of_firstRunPrefix`.  Only `propext` and
  `Quot.sound` are used.
- `Qb.lean`: the current QB-7/QB-8 spike-structure route.  It
  formalizes the QB-7 contradiction core `qb7_core` as a `Rat`
  inequality (`(5/4 - q)m > 1/5` against the exact cycle identity;
  `qb7_no_internal_data` packages the conclusion), the QB-8 C3-step
  decrease `c3_step_lt`, the rising-step increase
  `rise_step_gt`, the strict decrease of a C3 chain
  `c3_chain_strictlyDecreasing`, the consecutive-start corollary
  `startsFrom_consecutive_of_allOne`, and their assembly
  `qb8_structure`.  The `Rat`-layer theorem uses
  `Classical.choice`; the structural lemmas use only `propext` and
  `Quot.sound`.
- `ScratchLift.lean`: the Hensel-lift inverse `invFive` modulo powers
  of 5, used by the GC-4 residual statement.
- `Gc.lean`: GC core lemmas from `ph_qb_gc_chain.md`.  It defines the
  exact C3 chain `c3Exact`, the chain numerator `chainA`, and proves
  the GC-1/GC-4 closed form `c3_chain_closed_form`
  (`2^T * N_{Q+1} = 5^Q * N_1 + A_chain`), the residual congruence
  `c3_chain_residual`, the inverse-form residual
  `c3_chain_residual_inverse`, and the uniqueness corollary
  `c3_residual_unique_small` for `Q >= 9`.  It also proves the GC-3
  mod-3 closure theorems `c3_mod3_of_even`/`c3_mod3_of_odd` and the
  GC-42 mod-16 classifications
  `gc42_mod16_of_weight_three`/`gc42_mod16_of_weight_ge_four`.
  It also formalizes GC-41: the `b = 0` branch is excluded in frame A
  (`gc41_b_zero_no_solution`), including the `3m ≡ 1 (mod 5^Q)`
  residual, the `Q = 8` odd candidate `260417`, the parity exclusion
  for `Q = 9`, and the modulus bound for `Q >= 10`.
  It also proves GC-43 in cleared-denominator form
  (`gc43_linear_bound`): from the C3 chain equation and the rising
  bound `2^S N_1 <= 5^L m + A_max`, one obtains
  `(2^(T+S)-5^(L+Q))m <= 5^Q A_max + 2^S A_chain`.
  For GC-7 it currently contains the rising-segment bound
  `risePart_bound` (`risePart rise c3 <= 4 * 5^P`), based on
  `geomRise_invariant` and `geomRise_bound`
  (`geomRise L c <= 4 * 5^(L+c)`), plus the C3-segment geometric tail
  `geomTail_invariant`/`geomTail_bound`
  (`24 * geomTail (Q+1) <= 5 * 8^(Q+1)`).
  The cleared-denominator GC-7 upper bound is now closed:
  `c3PartFrom_le`, `c3PartFrom_cleared_bound`, and
  `gc7_pmi_cleared_bound`
  (`3 * pmiTotal <= 3 * 5^(P+1) + 5 * 2^T`) all compile.
  Its integer `m` narrow-window form is also closed:
  `gc7_m_cleared_bound` derives
  `3*m*(2^T-5^P) <= 3*5^P + 2^T` from the PMI numerator identity.
  The real-valued re-read of this integer form as the section-13.1
  `m` window with `delta = log_2(2^T/5^P)` is now compiled in
  `Td0Real.lean`.  The GC-13 cleared core and the `U=0` branch table
  are compiled in `Gc13.lean` (`gc13_allOK_check`, `gc13_t1_bound`,
  `gc13_t2_bound`, `gc13_u0_31/59/205/351/497/643`, and
  `gc13_long_rise_contradicts`).  The GC-7-to-GC-13 bridge is closed
  as `gc7_window_for_gc13`.
  GC-15 is closed in cleared-denominator form:
  `gc15_rise_all_one_bound` (`U=0`) and `gc15_risePart_bound`
  (`3*5^U*risePart <= 15*5^(P+U)-10*5^P*4^U`).
  The closed form, residual, mod-3, and mod-16 theorems use only
  `propext` and `Quot.sound`; `c3_chain_residual_inverse` also uses
  `Classical.choice` through the Hensel inverse in `ScratchLift.lean`.
- `AutomatonInterface.lean`: interface for the local-lemma weighted
  automaton.  It defines `G_i mod 2^m` transitions, the exact failure
  congruence, the fixed-`K` abstraction, and a verified concrete blocker
  showing that `K=32` identifies two reachable states with different
  representatives.  The local lemma itself remains an open statement.
- `FBeta.lean`: Problem 1 foundations for `F_b`: the reduced map
  `U_b(o) = oddpart(o+b)`, strict decrease above `b`
  (`uStep_lt_of_lt`), the exact one-run reduction
  `iterate_fStep_odd_reaches_uStep`, invariance of the odd set below
  `b` (`uStep_le_b_of_le`), strict decrease of all positive iterates
  above `b` (`iterate_uStep_lt_of_gt`), and absence of `U_b` cycles
  above `b` (`not_cyclePoint_uStep_of_gt`).  It then formalizes the
  cycle structure (Theorems 1.1 and 1.2): the run decomposition
  `uRunLen`/`uRunLenSum`, the exact equivalence
  `uStep_cyclePoint_iff_fStep_cyclePoint` between `U_b` cycles and
  `F_b` cycles on odd points `o <= b`, the bound
  `fStep_cyclePoint_le_two_b` (every positive cycle lies in
  `[1, 2b]`), and `eventually_cyclePoint` (every positive orbit enters
  a cycle).  The finite pigeonhole lemma `exists_repeat_lt` is proved
  constructively.  It also formalizes the cycle parity word: over the
  `F_b` orbit of one `U_b` period, the word of parities contains exactly
  `p` ones (`fStep_parityWord_count_of_uStep_period`), and one `U_b`
  period `p` is an `F_b` period of length `uRunLenSum b o p`
  (`fStep_period_of_uStep_period`).
- `Axioms.lean`: `#print axioms` checks; output is only Lean's built-in
  `propext` and `Quot.sound` (no `Classical.choice`, no custom axioms,
  no `sorry`).
- `Domination.lean`: the word-domination foundation for first-C3 hit
  times (`ph_qb_gc_chain.md` 52.21.2quater).  It defines the exact
  prefix predicate `domWord`, the pointwise weight predicate
  `domWordLE`, the word weight `wordWeight`, the first-C3 evaluator
  `firstC3H`, and the interval certificate `domCert`.  Theorems
  `domWordLE_firstC3H` (D1) and `domCert_spec` (D2) prove that a
  dominated start reaches C3 within the word length with
  `S ≤ wordWeight w`.
- `BasinCert.lean`: certificate blocks `Cert`, the contiguous range
  checker `certsOK`, the cover lookup `coverCert`, and the soundness
  theorem `certsOK_spec` lifting `domCert_spec` to a whole interval.
- `DeltaRecords.lean`: the G5' delta-record grouping used by
  `ph_qb_gc_chain.md` 52.21.2bis.  It tabulates
  `T(P) = ceil(P log2 5)` for `9 ≤ P < 205` and certifies
  `delta(P) ≥ delta(31)` for `P < 59` and `delta(P) ≥ delta(59)`
  for `59 ≤ P < 205` by exact power comparisons (`native_decide`).
- `StageOne.lean`: the 52.21.1 `m0` threshold certificate.  It checks
  the upper/lower branch conditions at `m0` in exact rational
  arithmetic for every feasible `(b, Q, L)` with `S ≤ 25`, and rules
  out the single dual-failure triple `(b,Q,L) = (2,8,7)` by the
  global cycle-equation bound `A_total < 7D` (`native_decide`).
  The uncovered-side `k`-interval exclusion is closed in
  `StageOneScan.lean`.
- `StageOneScan.lean`: the stage-one word-level certificate.  It
  enumerates all 471,727 rising words with `native_decide`, verifies
  that every uncovered-side residue `7 ≤ r < m0` is excluded by the
  `A_chain` range bound, and verifies the unique lower-only triple's
  upper side at its first representative above `m0`.  It also exposes
  per-triple/per-word extraction
  (`tripleScan_of_stageOneScanOK`,
  `wordBad_of_stageOneScanOK`).
- `Certificates.lean`: the generated basin certificates and their
  Lean verification.  `cert617` (16 blocks, including dummy gap
  blocks) closes `m < 617 ⇒ S ≤ 26` as `basin_617_cert`, and
  `cert1e6` (96 blocks) closes `m ≤ 10^6 ⇒ S ≤ 64` as
  `basin_1e6_cert`.  Besides the usual `propext`,
  `Classical.choice`, and `Quot.sound`, the only added axioms are the
  `native_decide` certificate checks
  `cert617_check._native.native_decide.ax_1_1` and
  `cert1e6_check._native.native_decide.ax_1_1`.
- `AllOddCert.lean`: the same domination-certificate soundness
  theorem, but quantified over every odd start (`m % 2 = 1`) instead
  of the admissible starts (`7 <= m`, odd, `5 ∤ m`).  B-L needs this
  because a W leaf may be divisible by 5.
- `CertificatesAllOdd.lean`: generated all-odd certificates.
  `basin_1e6_allodd_cert` closes every odd `m <= 10^6` with
  `S <= 64`; `basin_399861_cap63_allodd_cert` closes every odd
  `m < 399861` with `S <= 63`.  Together they prove BL-1 in
  `b_l_reduction.md`: no W element `r <= 10^6` has `S >= 64` and
  `F < 1`.
- `Td1.lean`: the TD-1 finite bridge from `ph_qb_gc_chain.md`
  52.21.2bis.  It certifies the first-C3 word of 201
  (`b1_orbit_check`), the B-family `U_req = 6` solution
  `(Q,b) = (28,2)` (`b1B_uReq_solutions_full`), and the sharp basin
  split `basin_617_sharp`: below 617, first-C3 weight 26 is attained
  only at 201.  It also records the A-family `U_req = 6` alternatives
  `Q = 29, 30`; the source's B1 statement omits `Q = 30`, and the
  A-family alternative is incompatible with the 201 orbit, whose final
  rising step has weight 2.
- `Td1Window.lean`: the cleared-integer form of 52.15--52.16.  `a0 Q`
  is the all-three chain numerator with
  `3 * a0 Q = 8^Q - 5^Q`; the A/B `R < U` and `R < L` inequalities
  and the `Z < 2`, `Z < 4`, `Z > 4` comparisons are proved as exact
  equivalences between integer power inequalities
  (`td1A_R_lt_LA_iff`, `td1A_R_lt_UA_iff`, `td1B_R_lt_LB_iff`,
  `td1B_R_lt_UB_iff`).  The bridge theorems
  `td1A_Z_lt_two_iff_R_lt_LA` and `td1B_Z_lt_four_iff_R_lt_LB`
  connect the `Z` windows to the corresponding `R < L` windows.
- `Td1Phase2.lean`: the phase-2 exact rational checks from
  52.21.2bis.  `tRat P = 2 * (1 - 5^P / 2^T)` with `T = tCeil P`
  realizes `t = 2 * (1 - 2^(-delta))` without `Real`/`log`;
  `phase2_delta_check` certifies `201 * t(31) >= 8/3` and
  `617 * t(59) >= 8/3`.  `b0_check`/`b0_spec` certify B0: every
  phase-2 feasible triple with `S <= 64` has `P <= 188`.
  `phase2_record_rat_check`/`phase2_tRat_ge_t31`/
  `phase2_tRat_ge_t59` certify the exact Rat form of the G5'
  records, and `phase2_upper_bound_check` combines the record checks
  with the two base `mt >= 8/3` checks.  The derived Rat bounds
  `phase2_mt_ge_of_m_ge_617` and `phase2_mt_ge_of_m_ge_201` turn the
  G5' records into `m * t(P) >= 8/3` for `m >= 617`, and for
  `m >= 201` with `P < 59`.  `phase2_mt_ge_of_b2` packages the B2 Rat
  conclusion, taking the B1 bridge (`m < 617` forces `m = 201` and
  `P < 59`) as an explicit input.  `phase2_b1_P_lt_59`/
  `phase2_b1_bridge`/`phase2_mt_ge_of_b2_of_201` expose the B1 bridge
  (`L=20, b=2, U_req=6` force `Q=28`, `P=48`) and its B1+B2 package.
- `Td0Phase2.lean`: exact A/B `Rmax < U` iff `mt > G_up`
  equivalences (`aUpper_iff`/`bUpper_iff`), the exact `G_up` bounds,
  and `upperAt_of_mt_ge`, which turns `m*t(P) >= 8/3` into
  `upperAt b Q L m = true`.
  `Td1.lean` also proves `phase2_m_ge_201`: first-C3 weight at least
  26 forces `m >= 201`.
- `Td1Final.lean`: assembles the TD-1 certificate gates into one
  theorem `td1_cert_components`: `stageOneOK`,
  `stageOneScanOK`, `b0OK`, and `phase2UpperBoundOK` are all true;
  `td1_basin_bounds` assembles the two basin-bound certificates, and
  `td1_cert_all` combines the certificate gates with both basin
  bounds.
- `Gc7Window.lean`: the exact rational re-read of GC-7 13.1 for the
  six small-`P` values.  `gc7_window_rat_check` certifies that
  `(3*5^P+2^T)/(3*(2^T-5^P))` equals
  `(5+(5/3)*2^delta)/(5*(2^delta-1))` with
  `2^delta = 2^T/5^P`; the per-`P` theorems
  `gc7_window_rat_31/59/205/351/497/643` are also compiled.
- `Td1S3.lean`: the `S3` closed form
  `S3 = (8^Q - 64*5^(Q-2))/3` and the endpoint identity
  `A0 - S3 = 13*5^(Q-2)` (`three_mul_s3`, `a0_sub_s3`).
- `Td1Interval.lean`: the cleared 52.15 interval-exclusion
  equivalences for A/B families (`td1A_areq_gt_amax_iff`,
  `td1A_areq_lt_a0_iff`, `td1B_areq_gt_amax_iff`,
  `td1B_areq_lt_a0_iff`).
- `Td1Interp.lean`: the 52.10 chain interpolation bounds
  `A0 <= A_chain <= A_max` for the A/B families
  (`chainA_ge_a0`, `chainA_le_amaxA`, `chainA_le_amaxB`), plus the
  tight B-family identity `chainA_eq_amaxB`.
- `Td0CertBridge.lean`: bridge from the stage-one certificate to the
  final window.  It proves `auOf = chainA`, `wordA = chainA`, the
  A/B chain-value min/max equal `a0`/`amaxA`/`amaxB`, the cleared
  word certificates `wordBadA_cleared`/`wordBadB_cleared`, and the
  rising/global cycle equations
  (`rising_equation_chainA`,
  `cycle_equation_of_rising_and_chain`).  The Areq equivalence layer
  is also here: `r_eq_of_congruence`, `wordBad_imp_areq`,
  `global_D_equation`, and `areq_cert_eq_chainA` convert the
  certificate residue and quotient into the real `m` and `A_chain`.
- `ScratchOrbit.lean`: the orbit-to-`pos` combinatorial layer.  It
  characterizes `combinations` membership (`mem_combinations_iff`),
  proves that the descending `twosPositions` list of a word is a
  combination (`twosPositions_mem_combinations`), and closes the
  last-entry cases used by the A/B families:
  `twosPositions_mem_combinations_of_last_one` and
  `twosPositions_mem_combinations_of_last_two`, with the
  `dropLast`/filter-count identities that let the B-family certificate
  strip the final `t = 2` before enumerating positions.
- `Td0Real.lean`: the Mathlib/Real bridge for GC-7 13.1.  It proves
  `2^delta = q` for `q = 2^T/5^P`, the general real window
  `m <= (5 + (5/3)*2^delta)/(5*(2^delta-1))`, and the identity
  `delta = T - P*log_2 5` (`deltaCeil_eq`).
- `Td0Final.lean`: the final window contradiction for TD-0/TD-1.
  It proves `A_req = A_chain` from the C3 closed form when
  `M0 = N1` (`td1A_chain_closed_form_of_eq`,
  `td1B_chain_closed_form_of_eq`) and assembles the final
  contradictions `td1A_closed`/`td1B_closed` from the interpolation
  bounds `A0 < A_chain < A_max` and the interval exclusion; the
  assembled forms `td1A_closed_of_chain`/`td1B_closed_of_chain`
  derive the interpolation bounds from `Td1Interp`, and
  `td1B_closed_eq_amaxB` closes the tight B family from
  `Areq != amaxB`.  The interval numerator uses
  `M0 = chainFirst ns`.  The Areq bridge is closed:
  `wordBadA_areq_excl`/`wordBadB_areq_excl` connect a word certificate
  to the A/B interval exclusion, `td1A_cert_areq_excl`/
  `td1B_cert_areq_excl` specialize to the stage-one tables, and
  `td1A_cert_closed`/`td1B_cert_closed` combine the C3 closed form,
  interpolation bounds, and certificate exclusion into `False`.
  The A/B synthesis `td0_cert_closed` and the packaged interface
  `Td0Data`/`td0_closed_of_data` turn all inputs into a single
  contradiction, so a frame-A + QB-8 wrapper only needs to produce
  one `Td0Data` datum.  The two stage-one lower-branch triples are
  handled inside the datum: `td0_A_special_false` closes `(1,20,11)`
  by its residue `m = 17749` versus `m0 = 31`, and
  `td0_B_special_false` closes `(2,8,7)` by the global cycle equation
  and the `sixAuOK` maximum.  The phase-2 branch closes through the
  Rat-to-`Areq` bridges `upperBranchA_areq_gt`/`upperBranchB_areq_ne`
  and the packaged interface `Td0Data2`/`td0_phase2_closed`.  The
  frame-A + QB-8 interface is assembled by `Qb8Cycle`/
  `td0_of_qb8_cycle`, with phase-2 datum construction
  `Qb8Cycle2`/`qb8_cycle2_to_td0Data2`.
- `TD1_STATUS.md`: current TD-1 formalization status, compiled modules,
  and remaining gaps.

## Legacy (archived)

- `BasinBounds.lean`: retired orbit-iteration module for the
  accelerated 5x+1 step (`stepC3`), the first-C3 iterator
  (`iterateC3` returning `L, U, M`), the prefix weight `S = L + U`,
  and the old kernel-`decide` theorems `basin_617`, `basin_201`,
  `m_min_ge_201`, `S_ge_26_imp_m_ge_201`, `m201_orbit`, and
  `basin_617_sharp`.  It is not imported by any current module, is
  intentionally absent from the build, and is no longer cited by the
  proof.  Both basin bounds are now closed by the certificate chain
  `BasinCert.lean` + `Certificates.lean`; that chain is the current
  authority.  Do not rebuild or verify this archived module.

## Build

```powershell
$dir = "C:\Users\Ex_Je\Documents\数学研究\lean"
$lean = "C:\Users\Ex_Je\lean4\lean-4.31.0-windows\bin\lean.exe"
$pkgPaths = (Get-ChildItem "$dir\.lake\packages" -Directory |
  ForEach-Object { Join-Path $_.FullName ".lake\build\lib\lean" } |
  Where-Object { Test-Path $_ }) -join ";"
$env:LEAN_PATH = "$dir;$pkgPaths;C:\Users\Ex_Je\lean4\lean-4.31.0-windows\lib\lean"
& $lean -R $dir -o "$dir\BinaryDigits.olean" "$dir\BinaryDigits.lean"
& $lean -R $dir -o "$dir\DigitBalance.olean" "$dir\DigitBalance.lean"
& $lean -R $dir -o "$dir\TwoPowPlusOne.olean" "$dir\TwoPowPlusOne.lean"
& $lean -R $dir -o "$dir\CollatzRank.olean" "$dir\CollatzRank.lean"
& $lean -R $dir -o "$dir\BalanceReduction.olean" "$dir\BalanceReduction.lean"
& $lean -R $dir -o "$dir\Valuation.olean" "$dir\Valuation.lean"
& $lean -R $dir -o "$dir\Pmi.olean" "$dir\Pmi.lean"
& $lean -R $dir -o "$dir\PhOne.olean" "$dir\PhOne.lean"
& $lean -R $dir -o "$dir\PhTwo.olean" "$dir\PhTwo.lean"
& $lean -R $dir -o "$dir\Qb.olean" "$dir\Qb.lean"
& $lean -R $dir -o "$dir\ScratchLift.olean" "$dir\ScratchLift.lean"
& $lean -R $dir -o "$dir\Gc.olean" "$dir\Gc.lean"
& $lean -R $dir -o "$dir\FBeta.olean" "$dir\FBeta.lean"
& $lean -R $dir -o "$dir\Domination.olean" "$dir\Domination.lean"
& $lean -R $dir -o "$dir\BasinCert.olean" "$dir\BasinCert.lean"
& $lean -R $dir -o "$dir\AllOddCert.olean" "$dir\AllOddCert.lean"
& $lean -R $dir -o "$dir\DeltaRecords.olean" "$dir\DeltaRecords.lean"
& $lean -R $dir -o "$dir\StageOne.olean" "$dir\StageOne.lean"
& $lean -R $dir -o "$dir\StageOneScan.olean" "$dir\StageOneScan.lean"
& $lean -R $dir -o "$dir\Certificates.olean" "$dir\Certificates.lean"
& $lean -R $dir -o "$dir\CertificatesAllOdd.olean" "$dir\CertificatesAllOdd.lean"
& $lean -R $dir -o "$dir\Td1.olean" "$dir\Td1.lean"
& $lean -R $dir -o "$dir\Td1Window.olean" "$dir\Td1Window.lean"
& $lean -R $dir -o "$dir\Td1Phase2.olean" "$dir\Td1Phase2.lean"
& $lean -R $dir -o "$dir\Td1Final.olean" "$dir\Td1Final.lean"
& $lean -R $dir -o "$dir\Gc7Window.olean" "$dir\Gc7Window.lean"
& $lean -R $dir -o "$dir\Td1S3.olean" "$dir\Td1S3.lean"
& $lean -R $dir -o "$dir\Td1Interval.olean" "$dir\Td1Interval.lean"
& $lean -R $dir -o "$dir\Td1Interp.olean" "$dir\Td1Interp.lean"
& $lean -R $dir -o "$dir\Td0Real.olean" "$dir\Td0Real.lean"
& $lean -R $dir -o "$dir\Td0CertBridge.olean" "$dir\Td0CertBridge.lean"
& $lean -R $dir -o "$dir\Td0Final.olean" "$dir\Td0Final.lean"
& $lean -R $dir -o "$dir\Axioms.olean" "$dir\Axioms.lean"
# `BasinBounds.lean` is archived and intentionally not rebuilt.
```
