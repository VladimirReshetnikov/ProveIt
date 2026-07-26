(**
  Deeply closed paired global dynamic-truth formula-code orbits.

  The concrete rank-zero outputs are quotations of formulas scoped below
  three, so their deep closure is unconditional in every PA model.  The
  successor wrapper is completely transparent; its only remaining premise is
  arbitrary-cutoff operational closure of the two actual local-row witnesses
  from their literal depth eighteen.

  Under that explicit premise, PA-definable induction selects global Sigma
  and Pi formula codes at every element of the model, including nonstandard
  levels, while retaining the ordinary orbit graph and a represented deep
  closure certificate for both coordinates.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTernaryPredicateDeepClosure
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedDeepClosedCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure.

Module
  PABoundedRawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedDeepClosedCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.

Definition RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (level globalSigmaCode globalPiCode : M) : Prop :=
  RawCarrierIndexedPairedDeepClosedCodeOrbitAt M
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    tail level globalSigmaCode globalPiCode.

Arguments RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt
  M tail level globalSigmaCode globalPiCode : clear implicits.

(** The invariant used by induction is a literal PA formula. *)
Definition dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExistsFormula
    : formula :=
  carrierIndexedPairedDeepClosedCodeOrbitExistsFormula
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph.

Theorem
    raw_sat_dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExistsFormula_iff
    : forall (M : RawPAModel) tail level,
  raw_formula_sat M (scons M level tail)
    dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExistsFormula <->
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.
Proof.
  intros M tail level.
  unfold dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExistsFormula,
    RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt.
  exact
    (raw_sat_carrierIndexedPairedDeepClosedCodeOrbitExistsFormula_iff M
      dynamicTruthPairedGlobalBaseGraph
      dynamicTruthPairedGlobalSuccessorGraph tail level).
Qed.

(** ------------------------------------------------------------------
    Unconditional concrete base. *)

Theorem rawDynamicTruthGlobalSigmaBaseCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateDeepClosed M
    (rawDynamicTruthGlobalSigmaBaseCode M).
Proof.
  intros M hPA.
  rewrite (rawDynamicTruthGlobalSigmaBaseCode_quoted M hPA).
  exact (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
    dynamicTruthGlobalSigmaBaseFormula
    dynamicTruthGlobalSigmaBaseFormula_scoped).
Qed.

Theorem rawDynamicTruthGlobalPiBaseCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateDeepClosed M
    (rawDynamicTruthGlobalPiBaseCode M).
Proof.
  intros M hPA.
  rewrite (rawDynamicTruthGlobalPiBaseCode_quoted M hPA).
  exact (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
    dynamicTruthGlobalPiBaseFormula
    dynamicTruthGlobalPiBaseFormula_scoped).
Qed.

Theorem dynamicTruthPairedGlobalBaseAt_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall globalSigma globalPi,
  RawDynamicTruthPairedGlobalBaseAt M globalSigma globalPi ->
  RawCodedTernaryPredicateDeepClosed M globalSigma /\
  RawCodedTernaryPredicateDeepClosed M globalPi.
Proof.
  intros M hPA globalSigma globalPi hbase.
  unfold RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt in hbase.
  destruct hbase as [-> ->].
  split.
  - exact (rawDynamicTruthGlobalSigmaBaseCode_deep_closed M hPA).
  - exact (rawDynamicTruthGlobalPiBaseCode_deep_closed M hPA).
Qed.

Theorem dynamicTruthPairedGlobalOrbitBaseGraph_raw_deep_closed_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedDeepClosedCodeOrbitBaseTotal M
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail.
  exists (rawDynamicTruthGlobalSigmaBaseCode M),
    (rawDynamicTruthGlobalPiBaseCode M).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
        (rawDynamicTruthGlobalSigmaBaseCode M)
        (rawDynamicTruthGlobalPiBaseCode M))).
    unfold RawDynamicTruthPairedGlobalBaseAt,
      RawDynamicTruthPairedGlobalWrapperAt.
    split; reflexivity.
  - split.
    + exact (rawDynamicTruthGlobalSigmaBaseCode_deep_closed M hPA).
    + exact (rawDynamicTruthGlobalPiBaseCode_deep_closed M hPA).
Qed.

(** ------------------------------------------------------------------
    Guarded concrete successor. *)

Definition RawDynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal
    (M : RawPAModel) : Prop :=
  RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal M
    dynamicTruthPairedGlobalSuccessorGraph.

Arguments RawDynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal
  M : clear implicits.

Theorem
    dynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal_of_local_closure :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal M.
Proof.
  intros M hPA hlocalClosure.
  unfold RawDynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal,
    RawCarrierIndexedPairedDeepClosedCodeOrbitSuccessorTotal,
    RawDynamicTruthPairedGlobalDeepClosedSuccessorTotal.
  exact (dynamicTruthPairedGlobalSuccessorGraph_raw_deep_closed_total
    M hPA hlocalClosure).
Qed.

(** Preserve deep closure along an already selected concrete edge. *)
Corollary dynamicTruthPairedGlobalSuccessorGraph_preserves_deep_closure :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  forall (tail : nat -> M) lowerLevel previousSigma previousPi
      nextSigma nextPi,
    RawCodedTernaryPredicateDeepClosed M previousSigma ->
    RawCodedTernaryPredicateDeepClosed M previousPi ->
    raw_formula_sat M
      (scons M nextSigma (scons M nextPi
        (scons M previousSigma (scons M previousPi
          (scons M lowerLevel tail)))))
      dynamicTruthPairedGlobalSuccessorGraph ->
    RawCodedTernaryPredicateDeepClosed M nextSigma /\
    RawCodedTernaryPredicateDeepClosed M nextPi.
Proof.
  intros M hPA hlocalClosure tail lowerLevel previousSigma previousPi
    nextSigma nextPi hpreviousSigma hpreviousPi hgraph.
  apply (dynamicTruthPairedGlobalSuccessorAt_deep_closed
    M hPA hlocalClosure previousSigma previousPi lowerLevel
    nextSigma nextPi hpreviousSigma hpreviousPi).
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
      lowerLevel previousSigma previousPi nextSigma nextPi) hgraph).
Qed.

(** PA-definable induction over the represented invariant. *)
Theorem dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExists_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.
Proof.
  intros M hPA hlocalClosure tail level.
  unfold RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt.
  exact (raw_carrierIndexedPairedDeepClosedCodeOrbitExists_all M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalOrbitBaseGraph_raw_deep_closed_total M hPA)
    (dynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal_of_local_closure
      M hPA hlocalClosure)
    tail level).
Qed.

(** Expanded downstream form: the ordinary paired global orbit remains
    visible alongside both represented deep-closure certificates. *)
Theorem
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_deep_closed_total :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    RawCodedTernaryPredicateDeepClosed M globalSigmaCode /\
    RawCodedTernaryPredicateDeepClosed M globalPiCode.
Proof.
  intros M hPA hlocalClosure.
  exact (raw_carrierIndexedPairedDeepClosedCodeOrbitGraph_total M hPA
    dynamicTruthPairedGlobalBaseGraph
    dynamicTruthPairedGlobalSuccessorGraph
    (dynamicTruthPairedGlobalOrbitBaseGraph_raw_deep_closed_total M hPA)
    (dynamicTruthPairedGlobalOrbitDeepClosedSuccessorTotal_of_local_closure
      M hPA hlocalClosure)).
Qed.

End
  PABoundedRawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph.
