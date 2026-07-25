(**
  Closing the context-insertion proof induction from formula-trace composition.

  The constructor analysis, represented strong induction, and binder
  commuting square are proved in separate modules.  This file connects those
  layers and records the single remaining algebraic input: formula-shift
  traces must compose across binary and quantified syntax constructors.

  In particular, no broad weakening or transplant premise appears here.
  Once [RawCodedFormulaShiftCompositional] is supplied, PA's own induction
  rebuilds every covered proof tree at every carrier-valued insertion depth.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality RawCodedFormulaShiftTotality
  RawCodedContextLists RawCodedContextInsert
  RawCodedContextInsertShiftCommutation
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertRootStep.

Module PABoundedRawCodedPALocalProofContextInsertComplete.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextInsert.
Import PABoundedRawCodedContextInsertShiftCommutation.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertRootStep.

(** Formula-shift composition discharges exactly the adequacy-guarded unit
    shift callback used by All-I and Ex-E. *)
Lemma raw_adequateUnitFormulaShiftExists_of_compositional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  RawAdequateUnitFormulaShiftExists M.
Proof.
  intros M hPA hcompositional formula hadequate.
  exact (raw_codedFormulaUnitShift_exists_of_atomically_adequate
    M hPA hcompositional formula hadequate).
Qed.

(** The represented depth induction in the commuting-square module closes
    the second binder callback without any further hypothesis. *)
Lemma raw_contextInsertUnitShiftSquare_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextInsertUnitShiftSquare M.
Proof.
  intros M hPA head shiftedHead depth source target shiftedSource
    hinsertion hheadShift hsourceShift.
  exact (raw_contextInsertAt_shift_commutes M hPA
    head shiftedHead depth source target shiftedSource
    hinsertion hsourceShift hheadShift).
Qed.

(** All seventeen proof-rule cases, with binder callbacks instantiated. *)
Theorem raw_codedPALocalProof_contextInsertRootStep_of_compositional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  RawCodedPALocalProofContextInsertRootStep M.
Proof.
  intros M hPA hcompositional.
  exact
    (raw_codedPALocalProof_contextInsertRootStep_of_binder_callbacks
      M hPA
      (raw_adequateUnitFormulaShiftExists_of_compositional
        M hPA hcompositional)
      (raw_contextInsertUnitShiftSquare_all M hPA)).
Qed.

(** Public arbitrary-depth transplant.  The root and insertion depth may be
    nonstandard elements of [M]; both inductions used below are represented
    arithmetic inductions, not Rocq recursions. *)
Theorem raw_codedPALocalProofContextInsertAt_all_of_compositional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall root,
    RawCodedPALocalProofContextInsertAt M root.
Proof.
  intros M hPA hcompositional root.
  exact (raw_codedPALocalProofContextInsertAt_all M hPA
    (raw_codedPALocalProof_contextInsertRootStep_of_compositional
      M hPA hcompositional)
    root).
Qed.

(** Depth zero is the guarded single-cons theorem needed by clients that do
    not manipulate the general insertion relation directly. *)
Corollary raw_codedPALocalProof_adequateConsTransplant_of_compositional :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall context head conclusion root,
    RawCodedFormulaAtomicallyAdequate M head ->
    RawContextListRealizable M context ->
    RawCodedPALocalProofOf M context conclusion root ->
    exists transplanted : M,
      RawCodedPALocalProofOf M
        (rawListNode M head context) conclusion transplanted.
Proof.
  intros M hPA hcompositional context head conclusion root
    hhead hcontext hproof.
  exact
    (raw_codedPALocalProof_adequateConsTransplant_of_contextInsertRootStep
      M hPA
      (raw_codedPALocalProof_contextInsertRootStep_of_compositional
        M hPA hcompositional)
      context head conclusion root hhead hcontext hproof).
Qed.

End PABoundedRawCodedPALocalProofContextInsertComplete.
