(**
  Root-closed paired global dynamic-truth formula-code orbits.

  The global base codes are concrete three-variable quotations, so their
  root closure is unconditional in every PA model.  The successor side is
  stated through the honest closure-preserving interface: later dynamic-row
  construction may discharge it without this orbit layer pretending that
  arbitrary malformed predecessor codes have successors.

  Once that interface is supplied, represented induction selects both the
  global Sigma code and the global Pi code at every carrier level and keeps
  the ordinary orbit graph together with root-closure certificates for both.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateTernaryApplication
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedRootClosedCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthGlobalBaseRootClosure.

Module PABoundedRawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedRootClosedCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.

Definition RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (level globalSigmaCode globalPiCode : M) : Prop :=
  RawCarrierIndexedPairedRootClosedCodeOrbitAt M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt
  M tail level globalSigmaCode globalPiCode : clear implicits.

Definition dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExistsFormula
    : formula :=
  carrierIndexedPairedRootClosedCodeOrbitExistsFormula
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph.

Theorem
    raw_sat_dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExistsFormula_iff
    : forall (M : RawPAModel) tail level,
  raw_formula_sat M (scons M level tail)
    dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExistsFormula <->
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.
Proof.
  intros M tail level.
  unfold dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExistsFormula,
    RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt.
  exact
    (raw_sat_carrierIndexedPairedRootClosedCodeOrbitExistsFormula_iff M
      dynamicTruthPairedGlobalBaseGraph
      dynamicTruthPairedGlobalSuccessorGraph tail level).
Qed.

(** The concrete rank-zero pair discharges the root-closed base interface. *)
Theorem dynamicTruthPairedGlobalOrbitBaseGraph_raw_root_closed_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedRootClosedCodeOrbitBaseTotal M
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail.
  destruct (dynamicTruthPairedGlobalBaseGraph_raw_adequate_total
    M hPA tail) as
    (globalSigmaCode & globalPiCode & hgraph &
     hglobalSigmaAdequate & hglobalPiAdequate).
  exists globalSigmaCode, globalPiCode. split; [exact hgraph |].
  exact (dynamicTruthPairedGlobalBaseAt_root_closed M hPA
    globalSigmaCode globalPiCode
    (proj1 (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
      globalSigmaCode globalPiCode) hgraph)).
Qed.

(** Named dynamic specialization of the generic guarded successor contract. *)
Definition RawDynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal
    (M : RawPAModel) : Prop :=
  RawCarrierIndexedPairedRootClosedCodeOrbitSuccessorTotal M
    dynamicTruthPairedGlobalSuccessorGraph.

Arguments RawDynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal
  M : clear implicits.

(** Refined semantic witnesses at every carrier level. *)
Theorem dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.
Proof.
  intros M hPA hsuccessor tail level.
  unfold RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt.
  exact (raw_carrierIndexedPairedRootClosedCodeOrbitExists_all M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalOrbitBaseGraph_raw_root_closed_total M hPA)
    hsuccessor tail level).
Qed.

(** Expanded downstream form.  In particular the selected global Pi code
    carries the established *root-level* certificate (unit shift at cutoff
    three and arbitrary represented substitution at depth three).  This
    statement deliberately does not claim arbitrary-depth ternary-application
    interchange; that stronger result needs fixed-point traces at every
    cutoff [depth + 3]. *)
Corollary
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_root_closed_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    RawCodedTernaryPredicateRootClosed M globalSigmaCode /\
    RawCodedTernaryPredicateRootClosed M globalPiCode.
Proof.
  intros M hPA hsuccessor tail level.
  exact (raw_carrierIndexedPairedRootClosedCodeOrbitGraph_total M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalOrbitBaseGraph_raw_root_closed_total M hPA)
    hsuccessor tail level).
Qed.

End PABoundedRawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitGraph.
