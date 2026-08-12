# TD-1 formalization status

Status date: 2026-08-10.  The goal is the Lean 4 formalization of the
current TD-0/TD-1 proof in `ph_qb_gc_chain.md`.

## Compiled modules

- `Gc.lean`: GC-1/3/4/41/42/43, GC-7 cleared PMI and `m` window,
  GC-13 branch table, GC-15 general `U` bound.
- `Td1.lean`: first-C3 word of 201, B-family `U_req` rigidity
  (`b1_201`, `b1B_uReq_solutions_full`), sharp basin split below 617
  (`basin_617_sharp`), and phase-2 `m >= 201`
  (`phase2_m_ge_201`, `phase2_m_ge_201_of_weight`).
- `Td1Window.lean`: cleared-integer A/B ratio-window equivalences from
  52.15--52.16 (`td1A_R_lt_LA_iff`, `td1A_R_lt_UA_iff`,
  `td1B_R_lt_LB_iff`, `td1B_R_lt_UB_iff`, the `Z` comparisons, and
  the bridge theorems `td1A_Z_lt_two_iff_R_lt_LA`,
  `td1B_Z_lt_four_iff_R_lt_LB`).
- `Td1Phase2.lean`: exact Rat `mt >= 8/3` checks
  (`phase2_delta_check`), the Rat form of G5' records
  (`phase2_record_rat_check`, `phase2_tRat_ge_t31`,
  `phase2_tRat_ge_t59`), B0 (`b0_spec`), and the combined
  `phase2_upper_bound_check`.  It also derives the Rat bounds
  `phase2_mt_ge_of_m_ge_617` and `phase2_mt_ge_of_m_ge_201`, and the
  B2 Rat form `phase2_mt_ge_of_b2` (with the B1 bridge as an input),
  plus the B1 bridge theorems `phase2_b1_P_lt_59`,
  `phase2_b1_bridge`, and `phase2_mt_ge_of_b2_of_201`.
- `Td0Phase2.lean`: the exact A/B `Rmax < U` iff `mt > G_up`
  equivalences (`aUpper_iff`/`bUpper_iff`), the exact `G_up` bounds,
  and the bridge `upperAt_of_mt_ge` from `m*t(P) >= 8/3` to
  `upperAt = true`.  It now also has the corrected analytic upper
  branch `upperBranch` (with the exact `1/(3B)` term instead of
  `1/(3*2^(b-1)a)`), the corrected G-up equivalences
  `aUpperCorrect_iff`/`bUpperCorrect_iff`, the bridge
  `upperBranch_of_mt_ge`, the prefix ratio identity
  `phase2B_eq`, and the propositional extraction
  `upperBranchA_prop`/`upperBranchB_prop`.
- `RisingBound.lean`: 44.2 formalized.  It defines the maximal rising
  prefix numerator `amaxWord L U`, proves the recursive maximum
  (`amaxWord_succ_one_le`), the cleared identity
  `three_mul_amaxWord_add`, the real-word bound
  `wordA_le_amaxWord`, and the exact h-max form
  `amaxWord_div_eq_hmax`:
  `A_max/5^L = 1 - (2/3)(4/5)^U - 1/(3B)` with
  `B = 5^L / 2^(L+U)`.
- `Td1Final.lean`: assembled certificate gates
  (`td1_cert_components`), assembled basin bounds
  (`td1_basin_bounds`), and the combined certificate layer
  (`td1_cert_all`).
- `Gc7Window.lean`: exact rational re-read of GC-7 13.1 for the six
  small-`P` values (`gc7_window_rat_check`).
- `Td1S3.lean`: `S3` closed form and the endpoint identity
  `A0 - S3 = 13*5^(Q-2)` (`three_mul_s3`, `a0_sub_s3`).
- `Td1Interval.lean`: cleared 52.15 interval-exclusion equivalences
  for A/B families (`td1A_areq_gt_amax_iff`,
  `td1A_areq_lt_a0_iff`, `td1B_areq_gt_amax_iff`,
  `td1B_areq_lt_a0_iff`).
- `Td1Interp.lean`: 52.10 chain interpolation bounds.  It proves the
  lower bound `a0 <= A_chain` for every C3 chain, the A-family upper
  bound `A_chain <= amaxA`, and the B-family upper bound
  `A_chain <= amaxB` (`chainA_ge_a0`, `chainA_le_amaxA`,
  `chainA_le_amaxB`), plus the tight B-family identity
  `chainA_eq_amaxB`.
- `Td0CertBridge.lean`: certificate bridge to the final window.  It
  proves `auOf = chainA`, `wordA = chainA`, the A/B chain-value
  min/max equal `a0`/`amaxA`/`amaxB`, the cleared word certificates
  `wordBadA_cleared`/`wordBadB_cleared`, and the rising/global cycle
  equations (`rising_equation_chainA`,
  `cycle_equation_of_rising_and_chain`).  The `Areq` equivalence
  layer is now closed: `r_eq_of_congruence` proves the certificate
  residue is the real `m`, `wordBad_imp_areq` lifts the boolean word
  certificate to the propositional interval exclusion,
  `global_D_equation`/`areq_cert_eq_chainA` identify the certificate
  quotient with `A_chain`.
- `ScratchOrbit.lean`: the orbit-to-`pos` membership layer.  It
  proves the `combinations` characterization
  (`mem_combinations_iff`), the descending-position membership
  `twosPositions_mem_combinations`, the drop-last/filter-count
  identities for `wordLast = 1/2`
  (`dropLast_filter_count_last_one`,
  `filter_count_of_last_two`,
  `dropLast_filter_count_last_two`), and the A/B last-entry
  specializations
  `twosPositions_mem_combinations_of_last_one` /
  `twosPositions_mem_combinations_of_last_two`.
- `Td0Real.lean`: Mathlib/Real bridge for GC-7 13.1.  It defines the
  exact ratio `q = 2^T/5^P` in `Real`, the real delta
  `delta = log_2 q`, proves `2^delta = q`, and closes the general
  `P,T` window
  `m <= (5 + (5/3)*2^delta)/(5*(2^delta-1))`
  from `gc7_m_cleared_bound` (`gc7_real_window_ratio`,
  `gc7_real_window_delta`, `deltaCeil_eq`).
- `Td0Final.lean`: final window contradiction.  It specializes the
  C3 closed form to `M0 = N1` and proves `A_req = A_chain` for both
  families (`td1A_chain_closed_form_of_eq`,
  `td1B_chain_closed_form_of_eq`), then assembles
  `td1A_closed`/`td1B_closed` from the interpolation bounds and the
  interval exclusion.  The assembled forms
  `td1A_closed_of_chain`/`td1B_closed_of_chain` now derive the
  interpolation bounds from the C3 chain data (`Td1Interp`), leaving
  only the interval-exclusion certificate as an input.  The interval
  numerator uses `M0 = chainFirst ns`, and the B-family tight closure
  `td1B_closed_eq_amaxB` only needs `Areq != amaxB`.  The Areq bridge
  is wired into the tabulated certificates:
  `wordBadA_areq_excl`/`wordBadB_areq_excl` connect a word-level
  certificate to `A_req > A_max` (A) or `A_req != A_max,5` (B), and
  `td1A_cert_areq_excl`/`td1B_cert_areq_excl` specialize those to the
  stage-one tables.  The final closures `td1A_cert_closed` and
  `td1B_cert_closed` combine the C3 closed form, the interpolation
  bounds, and the certificate exclusion into `False`.  The A/B branch
  synthesis `td0_cert_closed` and the packaged interface
  `Td0Data`/`td0_closed_of_data` are also compiled.
  `td0_closed_of_data` internally closes the two non-upper-branch
  triples `(1,20,11)` and `(2,8,7)`
  (`td0_A_special_false`, `td0_B_special_false`), and
  `tableUpper_of_feasible_not_special` derives `tableUpper = true`
  for every other feasible triple.
- `StageOne.lean`, `StageOneScan.lean`: 52.21.1 certificates, plus
  per-triple/per-word extraction
  (`tripleScan_of_stageOneScanOK`,
  `wordBad_of_stageOneScanOK`).
- `DeltaRecords.lean`: G5' power-comparison records.
- `Domination.lean`, `BasinCert.lean`, `Certificates.lean`,
  `CertificatesAllOdd.lean`: first-C3 basin certificates.

## Remaining gaps

1. TD-0 final assembly (mostly done): `Td0Final.lean` now compiles
   `td1A_cert_closed_of_word`, `td1B_cert_closed_of_word`, and the
   A/B branch synthesis `td0_cert_closed`: given a real rising word
   `w` and the C3 chain `ns/ts`, every feasible **stage-one**
   (`S <= 25`) branch is contradictory, including the two
   stage-one lower-branch triples handled by
   `td0_A_special_false`/`td0_B_special_false`.  All stage-one
   inputs are packaged in `Td0Data`, with `td0_closed_of_data`
   closing one datum without requiring `tableUpper = true`.
   The phase-2 (`S >= 26`) branch is now wired into `Td0Final`:
   the B0/B1/B2/B3 and G5' Rat/basin certificates are compiled, the
   corrected `upperBranch`/`phase2B_eq` plus the 44.2 word bound
   are compiled, the Rat-to-`Areq` interval-exclusion bridge
   (`upperBranchA_areq_gt` / `upperBranchB_areq_ne`) is closed, and
   the packaged `Td0Data2` / `td0_phase2_closed` phase-2 closure is
   compiled.
2. Frame-A + QB-8 cycle construction: the wrapper interface
   `Qb8Cycle`/`td0_of_qb8_cycle` and the phase-2 datum constructor
   `Qb8Cycle2`/`qb8_cycle2_to_td0Data2` are compiled.  The remaining
   analytic task is to prove that every frame-A QB-8 cycle supplies
   the fields of one of these structures.  The phase-2 wrapper derives
   `5^(L+Q) < 2^tCeil(L+Q)` from `tCeil_pow_lt`, and the `P` range,
   `tCeil` identity, `U <= L` and `Q >= 8` from `feasible64` plus
   `uReq = U`.  The remaining `hB1` condition is exposed in
   wrapper-ready form by `phase2_b1_condition_of_201`.  The complete
   real-orbit input `Qb8OrbitInput`/`qb8_orbit_of_firstWord`/
   `td0_of_qb8OrbitInput` is compiled: `hSfirst`, `hwS`, `hfeas`,
   `hU`, and `h201` are all derived.  The GC-7 chain then derives the
   exact ceiling identity from the cycle equation: the inputs
   `Qb8OrbitGC7Input`/`qb8_orbit_of_gc7Input` and
   `Qb8OrbitCycleInput`/`qb8_orbit_of_cycleInput` and
   `Qb8OrbitB0Input`/`qb8_orbit_of_b0Input`, the `U`-bound variant
   `Qb8OrbitU1Input`/`qb8_orbit_of_u1Input`, and the structural
   variant `Qb8OrbitStructuralInput`/`qb8_orbit_of_structuralInput`
   and the structural `U`-bound variant
   `Qb8OrbitStructuralU1Input`/`qb8_orbit_of_structuralU1Input`
   are compiled, with the top-level abstract entry
   `Qb8CycleAbstract`/`td0_of_qb8CycleAbstract`.  In the structural
   variants `hcyc`, `hD`, `hT`, and the B0 range `hP205` are all
   derived from the real word and chain, so the remaining analytic
   inputs are the family last step `hlast` (52.12, word layer) or the
   family `U` bound `hU1` (52.12, analytic layer).  The B0 range has
   both an independent formal proof path via `P_lt_205_of_b0`
   (`log2_five_lt_nineteen_eighths` gives `log2 5 < 19/8`) and a
   structural path via `P_lt_205_of_pow_six`.
3. Main theorem: `7` divergence depends on D0/SURV-EX/TD0 and the
   upstream analytic chain (local lemma, L, C, `G_i >= 1`, `c_k`,
   `m_d >= 2^(d+2)`, D0); those are not yet Lean-formalized.

## Build

```powershell
$dir = "C:\Users\Ex_Je\Documents\数学研究\lean"
$lean = "C:\Users\Ex_Je\lean4\lean-4.31.0-windows\bin\lean.exe"
$pkgPaths = (Get-ChildItem "$dir\.lake\packages" -Directory |
  ForEach-Object { Join-Path $_.FullName ".lake\build\lib\lean" } |
  Where-Object { Test-Path $_ }) -join ";"
$env:LEAN_PATH = "$dir;$pkgPaths;C:\Users\Ex_Je\lean4\lean-4.31.0-windows\lib\lean"
& $lean -R $dir -o "$dir\Td0Real.olean" "$dir\Td0Real.lean"
& $lean -R $dir -o "$dir\Td1Interp.olean" "$dir\Td1Interp.lean"
& $lean -R $dir -o "$dir\Td0CertBridge.olean" "$dir\Td0CertBridge.lean"
& $lean -R $dir -o "$dir\Td0Final.olean" "$dir\Td0Final.lean"
& $lean -R $dir -o "$dir\Axioms.olean" "$dir\Axioms.lean"
```
