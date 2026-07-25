(**
  Unconditional formula unit shifts and local-proof context insertion.

  [RawCodedFormulaShiftTotality] and
  [RawCodedPALocalProofContextInsertComplete] expose their sole remaining
  algebraic premise explicitly.  Three-table trace concatenation proves that
  premise in every raw PA model.  This file is the intentionally small bridge
  that instantiates the conditional APIs; it contains no new induction.
*)

From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftTotality
  RawCodedFormulaOperationTraceConcatenation
  RawCodedContextLists
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertRootStep
  RawCodedPALocalProofContextInsertComplete.

Module PABoundedRawCodedPALocalProofContextInsertUnconditional.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertRootStep.
Import PABoundedRawCodedPALocalProofContextInsertComplete.

(** Adequate formula codes admit the unit shift used below a binder. *)
Theorem raw_adequateUnitFormulaShiftExists : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawAdequateUnitFormulaShiftExists M.
Proof.
  intros M hPA.
  exact (raw_adequateUnitFormulaShiftExists_of_compositional M hPA
    (raw_codedFormulaShift_compositional M hPA)).
Qed.

(** Concrete form of the preceding callback, useful independently of proof
    transplantation. *)
Corollary raw_codedFormulaUnitShift_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  exists target,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) source target.
Proof.
  intros M hPA source hadequate.
  exact (raw_adequateUnitFormulaShiftExists M hPA source hadequate).
Qed.

(** Every proof root can be transplanted through context insertion at an
    arbitrary, possibly nonstandard, carrier-valued depth. *)
Theorem raw_codedPALocalProofContextInsertAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedPALocalProofContextInsertAt M root.
Proof.
  intros M hPA root.
  exact (raw_codedPALocalProofContextInsertAt_all_of_compositional M hPA
    (raw_codedFormulaShift_compositional M hPA) root).
Qed.

(** Guarded depth-zero specialization: prepend one atomically adequate head
    to a realizable source context and transplant the proof. *)
Corollary raw_codedPALocalProof_adequateConsTransplant : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall context head conclusion root,
    RawCodedFormulaAtomicallyAdequate M head ->
    RawContextListRealizable M context ->
    RawCodedPALocalProofOf M context conclusion root ->
    exists transplanted : M,
      RawCodedPALocalProofOf M
        (rawListNode M head context) conclusion transplanted.
Proof.
  intros M hPA context head conclusion root hhead hcontext hproof.
  exact (raw_codedPALocalProof_adequateConsTransplant_of_compositional
    M hPA (raw_codedFormulaShift_compositional M hPA)
    context head conclusion root hhead hcontext hproof).
Qed.

End PABoundedRawCodedPALocalProofContextInsertUnconditional.
