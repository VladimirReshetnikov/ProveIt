(**
  The carrier-indexed syntactic orbit of paired *local-row* formula codes.

  The rank-zero local Sigma/Pi codes and the mutually recursive local
  successor row have already been represented separately.  This file merely
  specializes the generic two-coordinate carrier orbit to those checked
  components.
  Its public, output-first environment convention is

      sigmaCode :: piCode :: level :: tail.

  In particular, [level] is an element of an arbitrary PA model.  Totality
  below is therefore obtained by represented PA induction and covers
  nonstandard levels; it is not a meta-level recursion over [nat].

  Important representation boundary: a positive iterate is the code of an
  eight-witness row predicate whose free variables still name the four beta
  tables and the current state.  It is *not* the code of the globally closed
  ten-witness truth certificate.  The historical public names in this module
  are retained for compatibility, but certificate-field graphs must first
  pass these local row codes through the separate global-wrapper
  construction; they must not consume this orbit directly.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthTotality
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthPairedBaseFormulaCodeGraph
  RawCodedDynamicTruthPairedBaseAdequacy
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy.

Module PABoundedRawCodedDynamicTruthPairedFormulaCodeOrbitGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.
Import PABoundedRawCodedDynamicTruthPairedBaseAdequacy.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

(** No new coding machinery is hidden here: this is the literal generic
    orbit instantiated by the two fixed local dynamic-truth row graphs. *)
Definition dynamicTruthPairedFormulaCodeOrbitGraph : formula :=
  carrierIndexedPairedCodeOrbitGraph
    dynamicTruthPairedBaseFormulaCodeGraph
    dynamicTruthPairedSuccessorRowGraph.

Definition RawDynamicTruthPairedFormulaCodeOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (level sigmaCode piCode : M) : Prop :=
  RawCarrierIndexedPairedCodeOrbitAt M
    dynamicTruthPairedBaseFormulaCodeGraph
    dynamicTruthPairedSuccessorRowGraph
    tail level sigmaCode piCode.

Arguments RawDynamicTruthPairedFormulaCodeOrbitAt
  M tail level sigmaCode piCode : clear implicits.

(** Exact, law-free output-first semantics. *)
Theorem raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff : forall
    (M : RawPAModel) tail level sigmaCode piCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode (scons M level tail)))
    dynamicTruthPairedFormulaCodeOrbitGraph <->
  RawDynamicTruthPairedFormulaCodeOrbitAt M
    tail level sigmaCode piCode.
Proof.
  intros M tail level sigmaCode piCode.
  unfold dynamicTruthPairedFormulaCodeOrbitGraph,
    RawDynamicTruthPairedFormulaCodeOrbitAt.
  exact (raw_sat_carrierIndexedPairedCodeOrbitGraph_iff M
    dynamicTruthPairedBaseFormulaCodeGraph
    dynamicTruthPairedSuccessorRowGraph
    tail level sigmaCode piCode).
Qed.

(** At zero, the orbit is exactly the paired local rank-zero row. *)
Theorem raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail sigmaCode piCode,
  RawDynamicTruthPairedFormulaCodeOrbitAt M
    tail (raw_zero M) sigmaCode piCode <->
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode tail))
    dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail sigmaCode piCode.
  unfold RawDynamicTruthPairedFormulaCodeOrbitAt.
  exact (raw_carrierIndexedPairedCodeOrbitAt_zero_iff M hPA
    dynamicTruthPairedBaseFormulaCodeGraph
    dynamicTruthPairedSuccessorRowGraph
    tail sigmaCode piCode).
Qed.

(** The successor view exposes the preceding pair and the genuine paired
    *local* row relation.  No choice of a successor code is made here. *)
Theorem raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextSigmaCode nextPiCode,
  RawDynamicTruthPairedFormulaCodeOrbitAt M
    tail (raw_succ M level) nextSigmaCode nextPiCode <->
  exists previousSigmaCode previousPiCode : M,
    RawDynamicTruthPairedFormulaCodeOrbitAt M
      tail level previousSigmaCode previousPiCode /\
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigmaCode previousPiCode level
      nextSigmaCode nextPiCode.
Proof.
  intros M hPA tail level nextSigmaCode nextPiCode.
  unfold RawDynamicTruthPairedFormulaCodeOrbitAt at 1.
  rewrite (raw_carrierIndexedPairedCodeOrbitAt_succ_iff M hPA
    dynamicTruthPairedBaseFormulaCodeGraph
    dynamicTruthPairedSuccessorRowGraph
    tail level nextSigmaCode nextPiCode).
  split.
  - intros (previousSigmaCode & previousPiCode & hprevious & hrow).
    exists previousSigmaCode, previousPiCode. split.
    + exact hprevious.
    + apply (proj1
        (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail level
          previousSigmaCode previousPiCode nextSigmaCode nextPiCode)).
      exact hrow.
  - intros (previousSigmaCode & previousPiCode & hprevious & hrow).
    exists previousSigmaCode, previousPiCode. split.
    + exact hprevious.
    + apply (proj2
        (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail level
          previousSigmaCode previousPiCode nextSigmaCode nextPiCode)).
      exact hrow.
Qed.

(** Formula-level zero view in the public output-first convention. *)
Theorem raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail sigmaCode piCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode
      (scons M (raw_zero M) tail)))
    dynamicTruthPairedFormulaCodeOrbitGraph <->
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode tail))
    dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail sigmaCode piCode.
  rewrite raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff.
  exact (raw_dynamicTruthPairedFormulaCodeOrbitAt_zero_iff M hPA
    tail sigmaCode piCode).
Qed.

(** Formula-level successor view.  The two cross-polarized component
    transformations remain visible through
    [RawDynamicTruthPairedSuccessorRowAt]. *)
Theorem raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_succ_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level nextSigmaCode nextPiCode,
  raw_formula_sat M
    (scons M nextSigmaCode (scons M nextPiCode
      (scons M (raw_succ M level) tail)))
    dynamicTruthPairedFormulaCodeOrbitGraph <->
  exists previousSigmaCode previousPiCode : M,
    raw_formula_sat M
      (scons M previousSigmaCode (scons M previousPiCode
        (scons M level tail)))
      dynamicTruthPairedFormulaCodeOrbitGraph /\
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigmaCode previousPiCode level
      nextSigmaCode nextPiCode.
Proof.
  intros M hPA tail level nextSigmaCode nextPiCode.
  rewrite raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff.
  rewrite (raw_dynamicTruthPairedFormulaCodeOrbitAt_succ_iff M hPA
    tail level nextSigmaCode nextPiCode).
  setoid_rewrite raw_sat_dynamicTruthPairedFormulaCodeOrbitGraph_iff.
  reflexivity.
Qed.

(** Strengthened totality at every carrier level.  The only open operation
    premise is precisely the adequacy-preserving successor interface.  The
    adequate base witnesses are supplied unconditionally by the fixed
    quoted Sigma/Pi base row. *)
Theorem dynamicTruthPairedFormulaCodeOrbitGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedSuccessorRowGraph ->
  forall (tail : nat -> M) level,
  exists sigmaCode piCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode (scons M level tail)))
      dynamicTruthPairedFormulaCodeOrbitGraph /\
    RawCodedFormulaAtomicallyAdequate M sigmaCode /\
    RawCodedFormulaAtomicallyAdequate M piCode.
Proof.
  intros M hPA hsuccessor tail level.
  pose proof
    (raw_carrierIndexedPairedAdequateCodeOrbitGraph_total M hPA
      dynamicTruthPairedBaseFormulaCodeGraph
      dynamicTruthPairedSuccessorRowGraph
      (dynamicTruthPairedBaseFormulaCodeGraph_adequate_total M hPA)
      hsuccessor) as horbitTotal.
  exact (horbitTotal tail level).
Qed.

(** All operation premises of the preceding theorem have now been discharged
    by the adequacy-preserving paired successor.  The conclusion is an
    unconditional carrier-facing orbit of atomically adequate local-row
    syntax codes.  It deliberately makes no claim that those codes are the
    globally closed truth predicates required by downstream certificate
    fields. *)
Corollary dynamicTruthPairedFormulaCodeOrbitGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) level,
  exists sigmaCode piCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode (scons M level tail)))
      dynamicTruthPairedFormulaCodeOrbitGraph /\
    RawCodedFormulaAtomicallyAdequate M sigmaCode /\
    RawCodedFormulaAtomicallyAdequate M piCode.
Proof.
  intros M hPA tail level.
  exact (dynamicTruthPairedFormulaCodeOrbitGraph_adequate_total M hPA
    (dynamicTruthPairedSuccessorRowGraph_raw_adequate_total M hPA)
    tail level).
Qed.

End PABoundedRawCodedDynamicTruthPairedFormulaCodeOrbitGraph.
