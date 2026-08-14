import Lake
open System Lake DSL

package StringFlow

@[default_target]
lean_lib StringFlow where
  roots := #[`AllOddCert, `AutomatonInterface, `Axioms, `BalanceRecurrence,
    `BalanceReduction, `BasinCert, `BinaryDigits, `Certificates,
    `CertificatesAllOdd, `CollatzRank, `DeltaRecords, `DigitBalance, `Domination,
    `FBeta, `Gc, `Gc13, `Gc15, `Gc7Window, `LteMacro, `MacroWindow,
    `ModTwoCycle, `BlockAutomaton, `PhOne, `PhTwo, `Pmi, `Qb, `QWindow, `ScratchLift,
    `ScratchOrbit, `ScratchTest2, `RisingBound, `StageOne, `StageOneScan, `SurvivorExplicit,
    `SurvExAudit, `S6Audit, `S6AuditStage1, `FinalStatement, `FinalTheorem, `CycleBridge, `DwdbDiv, `Td0CertBridge, `Td0Final, `Td0Phase2, `Td0Real, `Td1, `Td1Final,
    `Td1Interp, `Td1Interval, `Td1Phase2, `Td1S3, `Td1Window, `TwoPowPlusOne,
    `Valuation, `WordWindow, `C4C8Tail, `FinitePrefix,
    `UnifiedCoreBridge, `UnifiedCoreAudit, `PureCore, `PmiLocalLemma,
    `RealOrbitLocalLemma, `Angelina_Gilberta_Bridge, `kaltsit,
    `RealOrbitCharge]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0-rc2"
