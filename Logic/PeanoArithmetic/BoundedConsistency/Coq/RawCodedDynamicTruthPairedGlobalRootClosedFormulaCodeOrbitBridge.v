(**
  Concrete root-closed global dynamic-truth orbits.

  The global-successor closure module proves that its concrete successor
  graph preserves the established ternary root certificate, provided the two
  actual local successor rows are operationally closed at cutoff 18.  The
  generic root-closed orbit module expects precisely the same guarded
  callback.  This file records that definitional bridge and immediately feeds
  it to PA-definable paired-orbit induction.

  There are deliberately two distinct cutoffs in this argument.  Local rows
  occur beneath ten existential and five universal wrapper binders, so their
  shift and substitution traces are required at [3 + 10 + 5 = 18].  The
  resulting global formula codes receive only the public root certificate at
  cutoff 3.  Neither certificate says that formula operations commute at all
  carrier-valued cutoffs or depths; no arbitrary-depth ternary-application
  interchange is claimed here.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitGraph.

Module
  PABoundedRawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitGraph.

(** The concrete successor theorem has exactly the guarded callback shape
    consumed by the root-closed orbit.  In particular, this theorem does not
    add a closure premise for malformed or merely atomically adequate codes. *)
Theorem
    dynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal_of_local_closure :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  RawDynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal M.
Proof.
  intros M hPA hlocalClosure.
  exact (dynamicTruthPairedGlobalSuccessorGraph_raw_root_closed_total
    M hPA hlocalClosure).
Qed.

(** Graph-facing preservation for an already selected successor edge.  This
    is the useful non-total variant of the preceding bridge: downstream code
    can retain its concrete graph witness while transporting both predecessor
    root certificates to the two selected outputs. *)
Corollary dynamicTruthPairedGlobalSuccessorGraph_preserves_root_closure :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  forall (tail : nat -> M) lowerLevel previousSigma previousPi
      nextSigma nextPi,
    RawCodedTernaryPredicateRootClosed M previousSigma ->
    RawCodedTernaryPredicateRootClosed M previousPi ->
    raw_formula_sat M
      (scons M nextSigma (scons M nextPi
        (scons M previousSigma (scons M previousPi
          (scons M lowerLevel tail)))))
      dynamicTruthPairedGlobalSuccessorGraph ->
    RawCodedTernaryPredicateRootClosed M nextSigma /\
    RawCodedTernaryPredicateRootClosed M nextPi.
Proof.
  intros M hPA hlocalClosure tail lowerLevel previousSigma previousPi
    nextSigma nextPi hpreviousSigma hpreviousPi hgraph.
  apply (dynamicTruthPairedGlobalSuccessorAt_root_closed
    M hPA hlocalClosure previousSigma previousPi lowerLevel
    nextSigma nextPi hpreviousSigma hpreviousPi).
  exact (proj1
    (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
      lowerLevel previousSigma previousPi nextSigma nextPi) hgraph).
Qed.

(** The represented root-closed orbit exists at every element of an arbitrary
    PA model.  Its level quantifier therefore includes nonstandard levels. *)
Theorem
    dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExists_all_of_local_closure
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitAt M
      tail level globalSigmaCode globalPiCode.
Proof.
  intros M hPA hlocalClosure.
  apply (dynamicTruthPairedGlobalRootClosedFormulaCodeOrbitExists_all M hPA).
  exact
    (dynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal_of_local_closure
      M hPA hlocalClosure).
Qed.

(** Strongest expanded graph form currently justified by the cutoff-18 local
    closure premise: the ordinary paired global orbit graph is retained, and
    both selected coordinates carry cutoff-3 root certificates. *)
Theorem
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_root_closed_total_of_local_closure
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalClosure M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    RawCodedTernaryPredicateRootClosed M globalSigmaCode /\
    RawCodedTernaryPredicateRootClosed M globalPiCode.
Proof.
  intros M hPA hlocalClosure.
  apply
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_root_closed_total
      M hPA).
  exact
    (dynamicTruthPairedGlobalOrbitRootClosedSuccessorTotal_of_local_closure
      M hPA hlocalClosure).
Qed.

End
  PABoundedRawCodedDynamicTruthPairedGlobalRootClosedFormulaCodeOrbitBridge.
