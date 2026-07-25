(**
  The carrier-indexed orbit of paired global dynamic-truth formula codes.

  [RawCodedDynamicTruthPairedGlobalSuccessorGraph] supplies both ends of the
  represented recursion: a rank-zero pair of global Sigma-truth/Pi-falsity
  predicates and an adequacy-preserving paired successor.  This file merely
  instantiates the generic carrier-indexed paired orbit with those two fixed
  graphs.

  The public output-first environment is

      globalSigmaCode :: globalPiCode :: level :: tail.

  Unlike the historical local-row orbit, both public coordinates here code
  the complete ten-witness traversal wrapped around the local row checks.
  They are ternary global predicates, not the thirteen-slot local rows.  The
  represented induction used for totality ranges over every carrier element,
  including nonstandard levels in nonstandard PA models.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph.

Module PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.

(** The graph contains no additional coding layer: it is the generic paired
    orbit specialized to the checked global base and successor graphs. *)
Definition dynamicTruthPairedGlobalFormulaCodeOrbitGraph : formula :=
  carrierIndexedPairedCodeOrbitGraph
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph.

Definition RawDynamicTruthPairedGlobalFormulaCodeOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (level globalSigmaCode globalPiCode : M) : Prop :=
  RawCarrierIndexedPairedCodeOrbitAt M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthPairedGlobalFormulaCodeOrbitAt
  M tail level globalSigmaCode globalPiCode : clear implicits.

(** The adequate semantic view records the invariant used by represented
    induction.  Keeping it separate from the law-free orbit relation avoids
    silently strengthening the graph's exact semantics. *)
Definition RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (level globalSigmaCode globalPiCode : M) : Prop :=
  RawCarrierIndexedPairedAdequateCodeOrbitAt M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt
  M tail level globalSigmaCode globalPiCode : clear implicits.

(** Exact, law-free output-first semantics. *)
Theorem raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff : forall
    (M : RawPAModel) tail level globalSigmaCode globalPiCode,
  raw_formula_sat M
    (scons M globalSigmaCode
      (scons M globalPiCode (scons M level tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail level globalSigmaCode globalPiCode.
Proof.
  intros M tail level globalSigmaCode globalPiCode.
  unfold dynamicTruthPairedGlobalFormulaCodeOrbitGraph,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt.
  exact (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level globalSigmaCode globalPiCode).
Qed.

(** The adequate view is exactly the law-free orbit relation together with
    atomic adequacy of both global formula codes. *)
Theorem raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff : forall
    (M : RawPAModel) tail level globalSigmaCode globalPiCode,
  RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
    tail level globalSigmaCode globalPiCode <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode /\
    RawCodedFormulaAtomicallyAdequate M globalSigmaCode /\
    RawCodedFormulaAtomicallyAdequate M globalPiCode.
Proof.
  intros M tail level globalSigmaCode globalPiCode.
  unfold RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt,
    RawCarrierIndexedPairedAdequateCodeOrbitAt.
  reflexivity.
Qed.

(** At zero the orbit selects exactly the globally wrapped rank-zero pair. *)
Theorem raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail globalSigmaCode globalPiCode,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_zero M) globalSigmaCode globalPiCode <->
  raw_formula_sat M
    (scons M globalSigmaCode (scons M globalPiCode tail))
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalSigmaCode globalPiCode.
  unfold RawDynamicTruthPairedGlobalFormulaCodeOrbitAt.
  exact (raw_carrierIndexedPairedCodeOrbitAt_zero_iff M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail globalSigmaCode globalPiCode).
Qed.

(** The successor view exposes the preceding global pair and the exact
    global paired-successor relation.  No metatheoretic decoding or choice of
    a successor code occurs in this statement. *)
Theorem raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalSigmaCode nextGlobalPiCode,
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M level) nextGlobalSigmaCode nextGlobalPiCode <->
  exists previousGlobalSigmaCode previousGlobalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail level previousGlobalSigmaCode previousGlobalPiCode /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalSigmaCode nextGlobalPiCode.
  unfold RawDynamicTruthPairedGlobalFormulaCodeOrbitAt at 1.
  rewrite (raw_carrierIndexedPairedCodeOrbitAt_succ_iff M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level nextGlobalSigmaCode nextGlobalPiCode).
  split.
  - intros (previousGlobalSigmaCode & previousGlobalPiCode &
      hprevious & hsuccessor).
    exists previousGlobalSigmaCode, previousGlobalPiCode. split.
    + exact hprevious.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail level
          previousGlobalSigmaCode previousGlobalPiCode
          nextGlobalSigmaCode nextGlobalPiCode)).
      exact hsuccessor.
  - intros (previousGlobalSigmaCode & previousGlobalPiCode &
      hprevious & hsuccessor).
    exists previousGlobalSigmaCode, previousGlobalPiCode. split.
    + exact hprevious.
    + apply (proj2
        (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail level
          previousGlobalSigmaCode previousGlobalPiCode
          nextGlobalSigmaCode nextGlobalPiCode)).
      exact hsuccessor.
Qed.

(** Formula-level zero view in the public output-first convention. *)
Theorem raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_zero_iff :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      tail globalSigmaCode globalPiCode,
  raw_formula_sat M
    (scons M globalSigmaCode (scons M globalPiCode
      (scons M (raw_zero M) tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph <->
  raw_formula_sat M
    (scons M globalSigmaCode (scons M globalPiCode tail))
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail globalSigmaCode globalPiCode.
  rewrite raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  exact (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_zero_iff M hPA
    tail globalSigmaCode globalPiCode).
Qed.

(** Formula-level successor view. *)
Theorem raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_succ_iff :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextGlobalSigmaCode nextGlobalPiCode,
  raw_formula_sat M
    (scons M nextGlobalSigmaCode (scons M nextGlobalPiCode
      (scons M (raw_succ M level) tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph <->
  exists previousGlobalSigmaCode previousGlobalPiCode : M,
    raw_formula_sat M
      (scons M previousGlobalSigmaCode (scons M previousGlobalPiCode
        (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      previousGlobalSigmaCode previousGlobalPiCode level
      nextGlobalSigmaCode nextGlobalPiCode.
Proof.
  intros M hPA tail level nextGlobalSigmaCode nextGlobalPiCode.
  rewrite raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  rewrite (raw_dynamicTruthPairedGlobalFormulaCodeOrbitAt_succ_iff M hPA
    tail level nextGlobalSigmaCode nextGlobalPiCode).
  setoid_rewrite
    raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** Unconditional adequate totality of the specialized global orbit.  The
    generic represented induction consumes the already checked adequate base
    and successor interfaces, so [level] may be any carrier element. *)
Theorem dynamicTruthPairedGlobalFormulaCodeOrbitGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitGraphTotal M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph.
Proof.
  intros M hPA.
  exact (raw_carrierIndexedPairedAdequateCodeOrbitGraph_total M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalBaseGraph_raw_adequate_total M hPA)
    (dynamicTruthPairedGlobalSuccessorGraph_raw_adequate_total M hPA)).
Qed.

(** Expanded carrier-facing form used by later global-polarity projections. *)
Corollary
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    RawCodedFormulaAtomicallyAdequate M globalSigmaCode /\
    RawCodedFormulaAtomicallyAdequate M globalPiCode.
Proof.
  intros M hPA tail level.
  exact (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_adequate_total
    M hPA tail level).
Qed.

End PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
