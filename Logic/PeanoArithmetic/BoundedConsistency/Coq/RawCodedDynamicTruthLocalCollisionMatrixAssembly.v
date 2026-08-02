(**
  Assembly of the native seven-by-six local collision matrix.

  The Sigma row is ordered

    QF, implication-false-left, implication-true-right, conjunction,
    disjunction, existential, universal,

  and the Pi row is ordered

    QF, implication, conjunction, disjunction, universal, existential.

  This file performs only the finite assembly that is justified by the
  preceding cell compilers.  In particular, the input record below exposes
  every proof that must already live in the literal common context.  It does
  not project a branch from an actual successor row, prove local decision,
  or manufacture any of the remaining carrier-indexed proof compilers.

  The forty-two cells have the following exact partition:

    1 aligned QF cell;
    7 mixed-QF replay cells and 4 mixed-QF quantifier cells;
    2 implication and 2 Boolean predecessor-conditional cells;
    16 fixed-constructor cells;
    8 binder off-diagonal cells; and
    2 same-constructor quantifier cells.

  Once every pair implication is assembled, the generic finite-disjunction
  matrix theorem turns proofs of the right-associated Or7 and Or6 rows into
  a local proof of bottom.  Its independent context-traversal resources are
  retained as an explicit premise of that final theorem.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionMatrix
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthImpGuardedCollisionHelperBatch.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedCollisionHelperBatch.

(** ------------------------------------------------------------------
    Literal row order and exact carrier codes. *)

Inductive DynamicTruthLocalSigmaBranch : Type :=
| DTLocalSigmaQF
| DTLocalSigmaImpFalseLeft
| DTLocalSigmaImpTrueRight
| DTLocalSigmaAnd
| DTLocalSigmaOr
| DTLocalSigmaEx
| DTLocalSigmaAll.

Inductive DynamicTruthLocalPiBranch : Type :=
| DTLocalPiQF
| DTLocalPiImp
| DTLocalPiAnd
| DTLocalPiOr
| DTLocalPiAll
| DTLocalPiEx.

Definition dynamicTruthLocalSigmaBranchOrder :
    list DynamicTruthLocalSigmaBranch :=
  [ DTLocalSigmaQF;
    DTLocalSigmaImpFalseLeft;
    DTLocalSigmaImpTrueRight;
    DTLocalSigmaAnd;
    DTLocalSigmaOr;
    DTLocalSigmaEx;
    DTLocalSigmaAll ].

Definition dynamicTruthLocalPiBranchOrder :
    list DynamicTruthLocalPiBranch :=
  [ DTLocalPiQF;
    DTLocalPiImp;
    DTLocalPiAnd;
    DTLocalPiOr;
    DTLocalPiAll;
    DTLocalPiEx ].

Definition rawDynamicTruthLocalSigmaBranchCode
    (M : RawPAModel) (lowerPiApplication : M)
    (branch : DynamicTruthLocalSigmaBranch) : M :=
  match branch with
  | DTLocalSigmaQF => rawDynamicTruthSigmaQFEx8BranchCode M
  | DTLocalSigmaImpFalseLeft =>
      rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M
  | DTLocalSigmaImpTrueRight =>
      rawDynamicTruthSigmaImpTrueRightEx8BranchCode M
  | DTLocalSigmaAnd => rawDynamicTruthSigmaAndEx8BranchCode M
  | DTLocalSigmaOr => rawDynamicTruthSigmaOrEx8BranchCode M
  | DTLocalSigmaEx => rawDynamicTruthSigmaEx8BranchCode M
  | DTLocalSigmaAll =>
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPiApplication
  end.

Definition rawDynamicTruthLocalPiBranchCode
    (M : RawPAModel) (lowerSigmaApplication : M)
    (branch : DynamicTruthLocalPiBranch) : M :=
  match branch with
  | DTLocalPiQF => rawDynamicTruthPiQFEx8BranchCode M
  | DTLocalPiImp => rawDynamicTruthPiImpEx8BranchCode M
  | DTLocalPiAnd => rawDynamicTruthPiAndEx8BranchCode M
  | DTLocalPiOr => rawDynamicTruthPiOrEx8BranchCode M
  | DTLocalPiAll => rawDynamicTruthPiAllEx8BranchCode M
  | DTLocalPiEx =>
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigmaApplication
  end.

Definition rawDynamicTruthLocalSigmaBranches
    (M : RawPAModel) (lowerPiApplication : M) : list M :=
  map (rawDynamicTruthLocalSigmaBranchCode M lowerPiApplication)
    dynamicTruthLocalSigmaBranchOrder.

Definition rawDynamicTruthLocalPiBranches
    (M : RawPAModel) (lowerSigmaApplication : M) : list M :=
  map (rawDynamicTruthLocalPiBranchCode M lowerSigmaApplication)
    dynamicTruthLocalPiBranchOrder.

Lemma rawDynamicTruthLocalSigmaBranches_length : forall M lowerPi,
  length (rawDynamicTruthLocalSigmaBranches M lowerPi) = 7.
Proof. reflexivity. Qed.

Lemma rawDynamicTruthLocalPiBranches_length : forall M lowerSigma,
  length (rawDynamicTruthLocalPiBranches M lowerSigma) = 6.
Proof. reflexivity. Qed.

(** A compact, executable record of the surveyed cell classification. *)
Inductive DynamicTruthLocalCollisionKind : Type :=
| DTLocalCollisionQF
| DTLocalCollisionMixedReplay
| DTLocalCollisionMixedQuantifier
| DTLocalCollisionImpConditional
| DTLocalCollisionBooleanConditional
| DTLocalCollisionFixedConstructor
| DTLocalCollisionBinderOffDiagonal
| DTLocalCollisionQuantifierConditional.

Definition dynamicTruthLocalCollisionKind
    (sigmaBranch : DynamicTruthLocalSigmaBranch)
    (piBranch : DynamicTruthLocalPiBranch)
    : DynamicTruthLocalCollisionKind :=
  match sigmaBranch, piBranch with
  | DTLocalSigmaQF, DTLocalPiQF => DTLocalCollisionQF
  | DTLocalSigmaQF, DTLocalPiImp
  | DTLocalSigmaQF, DTLocalPiAnd
  | DTLocalSigmaQF, DTLocalPiOr
  | DTLocalSigmaImpFalseLeft, DTLocalPiQF
  | DTLocalSigmaImpTrueRight, DTLocalPiQF
  | DTLocalSigmaAnd, DTLocalPiQF
  | DTLocalSigmaOr, DTLocalPiQF => DTLocalCollisionMixedReplay
  | DTLocalSigmaQF, DTLocalPiAll
  | DTLocalSigmaQF, DTLocalPiEx
  | DTLocalSigmaEx, DTLocalPiQF
  | DTLocalSigmaAll, DTLocalPiQF => DTLocalCollisionMixedQuantifier
  | DTLocalSigmaImpFalseLeft, DTLocalPiImp
  | DTLocalSigmaImpTrueRight, DTLocalPiImp =>
      DTLocalCollisionImpConditional
  | DTLocalSigmaAnd, DTLocalPiAnd
  | DTLocalSigmaOr, DTLocalPiOr =>
      DTLocalCollisionBooleanConditional
  | DTLocalSigmaImpFalseLeft, DTLocalPiAnd
  | DTLocalSigmaImpFalseLeft, DTLocalPiOr
  | DTLocalSigmaImpFalseLeft, DTLocalPiAll
  | DTLocalSigmaImpTrueRight, DTLocalPiAnd
  | DTLocalSigmaImpTrueRight, DTLocalPiOr
  | DTLocalSigmaImpTrueRight, DTLocalPiAll
  | DTLocalSigmaAnd, DTLocalPiImp
  | DTLocalSigmaAnd, DTLocalPiOr
  | DTLocalSigmaAnd, DTLocalPiAll
  | DTLocalSigmaOr, DTLocalPiImp
  | DTLocalSigmaOr, DTLocalPiAnd
  | DTLocalSigmaOr, DTLocalPiAll
  | DTLocalSigmaEx, DTLocalPiImp
  | DTLocalSigmaEx, DTLocalPiAnd
  | DTLocalSigmaEx, DTLocalPiOr
  | DTLocalSigmaEx, DTLocalPiAll =>
      DTLocalCollisionFixedConstructor
  | DTLocalSigmaImpFalseLeft, DTLocalPiEx
  | DTLocalSigmaImpTrueRight, DTLocalPiEx
  | DTLocalSigmaAnd, DTLocalPiEx
  | DTLocalSigmaOr, DTLocalPiEx
  | DTLocalSigmaAll, DTLocalPiImp
  | DTLocalSigmaAll, DTLocalPiAnd
  | DTLocalSigmaAll, DTLocalPiOr
  | DTLocalSigmaAll, DTLocalPiEx =>
      DTLocalCollisionBinderOffDiagonal
  | DTLocalSigmaEx, DTLocalPiEx
  | DTLocalSigmaAll, DTLocalPiAll =>
      DTLocalCollisionQuantifierConditional
  end.

Definition dynamicTruthLocalCollisionKinds :
    list DynamicTruthLocalCollisionKind :=
  flat_map
    (fun sigmaBranch =>
      map (dynamicTruthLocalCollisionKind sigmaBranch)
        dynamicTruthLocalPiBranchOrder)
    dynamicTruthLocalSigmaBranchOrder.

Lemma dynamicTruthLocalCollisionKinds_length :
  length dynamicTruthLocalCollisionKinds = 42.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Exact same-context input boundary. *)

Definition rawDynamicTruthLocalSigmaConstructorBranchCode
    (M : RawPAModel) (lowerPiApplication : M)
    (branch : DynamicTruthSigmaConstructorBranch) : M :=
  match branch with
  | DTSigmaImpFalseLeft =>
      rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M
  | DTSigmaImpTrueRight =>
      rawDynamicTruthSigmaImpTrueRightEx8BranchCode M
  | DTSigmaAnd => rawDynamicTruthSigmaAndEx8BranchCode M
  | DTSigmaOr => rawDynamicTruthSigmaOrEx8BranchCode M
  | DTSigmaEx => rawDynamicTruthSigmaEx8BranchCode M
  | DTSigmaAll =>
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPiApplication
  end.

Definition rawDynamicTruthLocalPiConstructorBranchCode
    (M : RawPAModel) (lowerSigmaApplication : M)
    (branch : DynamicTruthPiConstructorBranch) : M :=
  match branch with
  | DTPiImp => rawDynamicTruthPiImpEx8BranchCode M
  | DTPiAnd => rawDynamicTruthPiAndEx8BranchCode M
  | DTPiOr => rawDynamicTruthPiOrEx8BranchCode M
  | DTPiAll => rawDynamicTruthPiAllEx8BranchCode M
  | DTPiEx =>
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigmaApplication
  end.

(** A transparent alias for one proof root in the literal common context.
    Keeping this large judgement out of indexed and record declarations
    avoids forcing the elaborator to normalize its existential package at
    every field occurrence. *)
Definition RawDynamicTruthLocalRootAt
    (M : RawPAModel) (context target : M) : Prop :=
  exists root : M, RawCodedPALocalProofOf M context target root.

Arguments RawDynamicTruthLocalRootAt M context target : clear implicits.

Definition RawDynamicTruthLocalFixedPairFamily
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  forall sigmaBranch piBranch,
    DynamicTruthFixedConstructorCell sigmaBranch piBranch ->
    RawDynamicTruthLocalRootAt M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaConstructorBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiConstructorBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))).

Arguments RawDynamicTruthLocalFixedPairFamily
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

Record RawDynamicTruthLocalCollisionMatrixInputs
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop := {
  rawDynamicTruthLocalCollision_context_realizable :
    RawContextListRealizable M context;
  rawDynamicTruthLocalCollision_lowerPi_adequate :
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication;
  rawDynamicTruthLocalCollision_lowerSigma_adequate :
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication;
  rawDynamicTruthLocalCollision_context_self_shift :
    RawContextShift M context context;

  rawDynamicTruthLocalCollision_qf_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthQFEx8BranchExclusivityCode M);
  rawDynamicTruthLocalCollision_predecessor_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M);
  rawDynamicTruthLocalCollision_impFalse_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpFalseLeftConditionalCellCode M);
  rawDynamicTruthLocalCollision_impTrue_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthImpTrueRightConditionalCellCode M);
  rawDynamicTruthLocalCollision_and_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthAndConditionalCellCode M);
  rawDynamicTruthLocalCollision_or_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthOrConditionalCellCode M);

  rawDynamicTruthLocalCollision_fixed_pairs :
    RawDynamicTruthLocalFixedPairFamily M context
      lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthLocalCollision_binder_inputs :
    forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderOffDiagonalProofInputsAt M context cell
        lowerPiApplication lowerSigmaApplication;

  rawDynamicTruthLocalCollision_sigmaEx_direct_trace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerSigmaApplication);
  rawDynamicTruthLocalCollision_sigmaAll_direct_trace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerPiApplication);
  rawDynamicTruthLocalCollision_sigmaEx_cross_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthLocalCollision_sigmaAll_cross_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);

  rawDynamicTruthLocalCollision_mixed_replay_root :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M);
  rawDynamicTruthLocalCollision_mixed_cell_roots :
    forall cell : DynamicTruthMixedQFCell,
      RawDynamicTruthLocalRootAt M context
        (rawDynamicTruthMixedQFCellCode M cell
          lowerPiApplication lowerSigmaApplication)
}.

Arguments RawDynamicTruthLocalCollisionMatrixInputs
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** ------------------------------------------------------------------
    Small composition lemmas used by the finite case split. *)

Theorem raw_dynamicTruthLocal_pair_of_conditional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context premise sigmaBranch piBranch cellRoot premiseRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M premise
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellRoot ->
  RawCodedPALocalProofOf M context premise premiseRoot ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
      pairRoot.
Proof.
  intros M hPA context premise sigmaBranch piBranch
    cellRoot premiseRoot hcell hpremise.
  exists (rawProofImpERoot M context premise
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    cellRoot premiseRoot).
  exact (raw_codedPALocalProofOf_impE M hPA context premise
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    cellRoot premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_mixedQF_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  (exists replayRoot : M,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M) replayRoot) ->
  (forall cell : DynamicTruthMixedQFCell,
    exists cellRoot : M,
      RawCodedPALocalProofOf M context
        (rawDynamicTruthMixedQFCellCode M cell
          lowerPiApplication lowerSigmaApplication) cellRoot) ->
  forall cell : DynamicTruthMixedQFCell,
    exists pairRoot : M,
      RawCodedPALocalProofOf M context
        (rawDynamicTruthMixedQFCollisionCode M cell
          lowerPiApplication lowerSigmaApplication) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma
    (replayRoot & hreplay) hcells cell.
  destruct (hcells cell) as [cellRoot hcell].
  destruct cell;
    cbn [rawDynamicTruthMixedQFCellCode] in hcell |- *.
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaQFPiImp lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaQFPiImp lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaQFPiAnd lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaQFPiAnd lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaQFPiOr lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaQFPiOr lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - now exists cellRoot.
  - now exists cellRoot.
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaImpFalseLeftPiQF lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaImpFalseLeftPiQF lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaImpTrueRightPiQF lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaImpTrueRightPiQF lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaAndPiQF lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaAndPiQF lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
      (rawDynamicTruthMixedQFSigmaBranchCode M
        DTMQFSigmaOrPiQF lowerPi)
      (rawDynamicTruthMixedQFPiBranchCode M
        DTMQFSigmaOrPiQF lowerSigma)
      cellRoot replayRoot hcell hreplay).
  - now exists cellRoot.
  - now exists cellRoot.
Qed.

(** The binder helper uses constructor-oriented branch codes internally.
    These equations identify them with the literal row codes above. *)
Lemma rawDynamicTruthBinderOffDiagonalSigmaBranchCode_eq_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall cell lowerPiApplication,
  rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell
    lowerPiApplication =
  rawDynamicTruthLocalSigmaConstructorBranchCode M lowerPiApplication
    (dynamicTruthBinderOffDiagonalSigmaBranch cell).
Proof.
  intros M hPA cell lowerPi.
  destruct cell.
  - change (rawFormulaEx8Code M
      (rawDynamicTruthSigmaUniversalCode M lowerPi) =
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi).
    symmetry. apply rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native.
    exact hPA.
  - change (rawFormulaEx8Code M
      (rawDynamicTruthSigmaUniversalCode M lowerPi) =
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi).
    symmetry. apply rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native.
    exact hPA.
  - change (rawFormulaEx8Code M
      (rawDynamicTruthSigmaUniversalCode M lowerPi) =
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi).
    symmetry. apply rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native.
    exact hPA.
  - change (rawFormulaEx8Code M
      (rawDynamicTruthSigmaUniversalCode M lowerPi) =
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi).
    symmetry. apply rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native.
    exact hPA.
  - change (rawDynamicTruthSigmaConstructorEx8BranchCode M
      DTSigmaImpFalseLeft pBot =
      rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
      by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaConstructorEx8BranchCode M
      DTSigmaImpTrueRight pBot =
      rawDynamicTruthSigmaImpTrueRightEx8BranchCode M).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
      by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaConstructorEx8BranchCode M
      DTSigmaAnd pBot = rawDynamicTruthSigmaAndEx8BranchCode M).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthSigmaConstructorEx8BranchCode M
      DTSigmaOr pBot = rawDynamicTruthSigmaOrEx8BranchCode M).
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
Qed.

Lemma rawDynamicTruthBinderOffDiagonalPiBranchCode_eq_local : forall
    (M : RawPAModel), RawPASatisfies M -> forall cell lowerSigmaApplication,
  rawDynamicTruthBinderOffDiagonalPiBranchCode M cell
    lowerSigmaApplication =
  rawDynamicTruthLocalPiConstructorBranchCode M lowerSigmaApplication
    (dynamicTruthBinderOffDiagonalPiBranch cell).
Proof.
  intros M hPA cell lowerSigma.
  destruct cell.
  - change (rawDynamicTruthPiConstructorEx8BranchCode M DTPiImp pBot =
      rawDynamicTruthPiImpEx8BranchCode M).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiConstructorEx8BranchCode M DTPiAnd pBot =
      rawDynamicTruthPiAndEx8BranchCode M).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiAndEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiConstructorEx8BranchCode M DTPiOr pBot =
      rawDynamicTruthPiOrEx8BranchCode M).
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite rawDynamicTruthPiOrEx8BranchCode_eq_quoted by exact hPA.
    reflexivity.
  - change (rawDynamicTruthPiFormulaEx8Code M
      (rawDynamicTruthPiExistentialCode M lowerSigma) =
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma).
    symmetry. apply rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
    exact hPA.
  - change (rawDynamicTruthPiFormulaEx8Code M
      (rawDynamicTruthPiExistentialCode M lowerSigma) =
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma).
    symmetry. apply rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
    exact hPA.
  - change (rawDynamicTruthPiFormulaEx8Code M
      (rawDynamicTruthPiExistentialCode M lowerSigma) =
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma).
    symmetry. apply rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
    exact hPA.
  - change (rawDynamicTruthPiFormulaEx8Code M
      (rawDynamicTruthPiExistentialCode M lowerSigma) =
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma).
    symmetry. apply rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
    exact hPA.
  - change (rawDynamicTruthPiFormulaEx8Code M
      (rawDynamicTruthPiExistentialCode M lowerSigma) =
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma).
    symmetry. apply rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
    exact hPA.
Qed.

Theorem raw_dynamicTruthLocal_binder_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication cell,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt M context cell
    lowerPiApplication lowerSigmaApplication ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaConstructorBranchCode M
          lowerPiApplication
          (dynamicTruthBinderOffDiagonalSigmaBranch cell))
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiConstructorBranchCode M
            lowerSigmaApplication
            (dynamicTruthBinderOffDiagonalPiBranch cell))
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma cell
    hcontext hlowerPi hlowerSigma hinputs.
  destruct (raw_dynamicTruthBinderOffDiagonal_matrix_pair M hPA
    context cell lowerPi lowerSigma hcontext hlowerPi hlowerSigma hinputs)
    as [pairRoot hpair].
  exists pairRoot.
  rewrite rawDynamicTruthBinderOffDiagonalSigmaBranchCode_eq_local in hpair
    by exact hPA.
  rewrite rawDynamicTruthBinderOffDiagonalPiBranchCode_eq_local in hpair
    by exact hPA.
  exact hpair.
Qed.

(** ------------------------------------------------------------------
    Specialized pairs supplied by the common input record. *)

Theorem raw_dynamicTruthLocal_qf_pair : forall
    (M : RawPAModel) context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M (rawDynamicTruthSigmaQFEx8BranchCode M)
        (rawFormulaImpCode M (rawDynamicTruthPiQFEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_qf_root
    M context lowerPi lowerSigma hinputs) as [root hroot].
  exists root.
  exact hroot.
Qed.

Theorem raw_dynamicTruthLocal_impFalse_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
        (rawFormulaImpCode M (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_impFalse_root
    M context lowerPi lowerSigma hinputs) as [cellRoot hcell].
  destruct (rawDynamicTruthLocalCollision_predecessor_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  unfold rawDynamicTruthImpFalseLeftConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_impTrue_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
        (rawFormulaImpCode M (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_impTrue_root
    M context lowerPi lowerSigma hinputs) as [cellRoot hcell].
  destruct (rawDynamicTruthLocalCollision_predecessor_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  unfold rawDynamicTruthImpTrueRightConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_and_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M (rawDynamicTruthSigmaAndEx8BranchCode M)
        (rawFormulaImpCode M (rawDynamicTruthPiAndEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_and_root
    M context lowerPi lowerSigma hinputs) as [cellRoot hcell].
  destruct (rawDynamicTruthLocalCollision_predecessor_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  unfold rawDynamicTruthAndConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaAndEx8BranchCode M)
    (rawDynamicTruthPiAndEx8BranchCode M)
    cellRoot premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_or_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M (rawDynamicTruthSigmaOrEx8BranchCode M)
        (rawFormulaImpCode M (rawDynamicTruthPiOrEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_or_root
    M context lowerPi lowerSigma hinputs) as [cellRoot hcell].
  destruct (rawDynamicTruthLocalCollision_predecessor_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  unfold rawDynamicTruthOrConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaOrEx8BranchCode M)
    (rawDynamicTruthPiOrEx8BranchCode M)
    cellRoot premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_sigmaExPiEx_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M (rawDynamicTruthSigmaEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_sigmaEx_direct_trace
    M context lowerPi lowerSigma hinputs) as [trace].
  destruct (rawDynamicTruthLocalCollision_sigmaEx_cross_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaExPiExConditionalCell_direct
      M hPA context lowerSigma trace
      (rawDynamicTruthLocalCollision_context_realizable
        M context lowerPi lowerSigma hinputs)
      (rawDynamicTruthLocalCollision_context_self_shift
        M context lowerPi lowerSigma hinputs)) as hcell.
  unfold rawDynamicTruthSigmaExPiExConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M lowerSigma)
    (rawDynamicTruthSigmaEx8BranchCode M)
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma)
    (rawDynamicTruthSigmaExPiExConditionalCellLocalRoot
      M hPA context lowerSigma trace)
    premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_sigmaAllPiAll_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall context lowerPi lowerSigma,
  RawDynamicTruthLocalCollisionMatrixInputs M context lowerPi lowerSigma ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi)
        (rawFormulaImpCode M (rawDynamicTruthPiAllEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma hinputs.
  destruct (rawDynamicTruthLocalCollision_sigmaAll_direct_trace
    M context lowerPi lowerSigma hinputs) as [trace].
  destruct (rawDynamicTruthLocalCollision_sigmaAll_cross_root
    M context lowerPi lowerSigma hinputs) as [premiseRoot hpremise].
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct
      M hPA context lowerPi trace
      (rawDynamicTruthLocalCollision_context_realizable
        M context lowerPi lowerSigma hinputs)
      (rawDynamicTruthLocalCollision_context_self_shift
        M context lowerPi lowerSigma hinputs)) as hcell.
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M lowerPi)
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi)
    (rawDynamicTruthPiAllEx8BranchCode M)
    (rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot
      M hPA context lowerPi trace)
    premiseRoot hcell hpremise).
Qed.

(** ------------------------------------------------------------------
    The complete forty-two-cell pair family. *)

Theorem raw_dynamicTruthLocalCollisionMatrix_pair_of_imp_pairs : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaBranch piBranch,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  (exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot) ->
  (exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiImpEx8BranchCode M)
          (rawFormulaBotCode M))) pairRoot) ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaBranch piBranch
    hinputs himpFalsePair himpTruePair.
  destruct sigmaBranch.
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_qf_pair
        M context lowerPi lowerSigma hinputs).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaQFPiImp).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaQFPiAnd).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaQFPiOr).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaQFPiAll).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaQFPiEx).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaImpFalseLeftPiQF).
    + exact himpFalsePair.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpFalseLeft DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpFalseLeft DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpFalseLeft DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaImpFalseLeftPiEx
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs
          DTBODSigmaImpFalseLeftPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaImpTrueRightPiQF).
    + exact himpTruePair.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpTrueRight DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpTrueRight DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs
        DTSigmaImpTrueRight DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaImpTrueRightPiEx
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs
          DTBODSigmaImpTrueRightPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaAndPiQF).
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaAnd DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_and_pair M hPA
        context lowerPi lowerSigma hinputs).
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaAnd DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaAnd DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAndPiEx
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaAndPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaOrPiQF).
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaOr DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaOr DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_or_pair M hPA
        context lowerPi lowerSigma hinputs).
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaOr DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaOrPiEx
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaOrPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaExPiQF).
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaEx DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaEx DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaEx DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalCollision_fixed_pairs
        M context lowerPi lowerSigma hinputs DTSigmaEx DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_sigmaExPiEx_pair M hPA
        context lowerPi lowerSigma hinputs).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalCollision_mixed_replay_root
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_mixed_cell_roots
          M context lowerPi lowerSigma hinputs)
        DTMQFSigmaAllPiQF).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiImp
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaAllPiImp)).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiAnd
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaAllPiAnd)).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiOr
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaAllPiOr)).
    + exact (raw_dynamicTruthLocal_sigmaAllPiAll_pair M hPA
        context lowerPi lowerSigma hinputs).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiEx
        (rawDynamicTruthLocalCollision_context_realizable
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerPi_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_lowerSigma_adequate
          M context lowerPi lowerSigma hinputs)
        (rawDynamicTruthLocalCollision_binder_inputs
          M context lowerPi lowerSigma hinputs DTBODSigmaAllPiEx)).
Qed.

(** Compatibility wrapper using the historical implication resources stored
    in the common matrix-input record. *)
Theorem raw_dynamicTruthLocalCollisionMatrix_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaBranch piBranch,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaBranch piBranch hinputs.
  exact (raw_dynamicTruthLocalCollisionMatrix_pair_of_imp_pairs
    M hPA context lowerPi lowerSigma sigmaBranch piBranch hinputs
    (raw_dynamicTruthLocal_impFalse_pair M hPA
      context lowerPi lowerSigma hinputs)
    (raw_dynamicTruthLocal_impTrue_pair M hPA
      context lowerPi lowerSigma hinputs)).
Qed.

(** Corrected implication wrapper.  Every non-implication matrix cell still
    comes from the established common input package; only the two diagonal
    implication pairs are replaced by applications of the guarded cells. *)
Theorem raw_dynamicTruthLocalCollisionMatrix_pair_guarded_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaBranch piBranch,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaBranch piBranch
    hinputs [predecessorRoot hpredecessor]
    [falseCellRoot hfalseCell] [trueCellRoot htrueCell].
  exact (raw_dynamicTruthLocalCollisionMatrix_pair_of_imp_pairs
    M hPA context lowerPi lowerSigma sigmaBranch piBranch hinputs
    (raw_dynamicTruthImpFalseLeftGuarded_pair M hPA context
      falseCellRoot predecessorRoot hfalseCell hpredecessor)
    (raw_dynamicTruthImpTrueRightGuarded_pair M hPA context
      trueCellRoot predecessorRoot htrueCell hpredecessor)).
Qed.

Theorem raw_dynamicTruthLocalCollisionMatrix_pair_family : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M).
Proof.
  intros M hPA context lowerPi lowerSigma hinputs
    left hleft right hright.
  unfold rawDynamicTruthLocalSigmaBranches in hleft.
  apply in_map_iff in hleft.
  destruct hleft as [sigmaBranch [hleft _]].
  subst left.
  unfold rawDynamicTruthLocalPiBranches in hright.
  apply in_map_iff in hright.
  destruct hright as [piBranch [hright _]].
  subst right.
  exact (raw_dynamicTruthLocalCollisionMatrix_pair M hPA context
    lowerPi lowerSigma sigmaBranch piBranch hinputs).
Qed.

Theorem raw_dynamicTruthLocalCollisionMatrix_pair_family_guarded_imp : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M).
Proof.
  intros M hPA context lowerPi lowerSigma hinputs
    hpredecessor hfalseCell htrueCell left hleft right hright.
  unfold rawDynamicTruthLocalSigmaBranches in hleft.
  apply in_map_iff in hleft.
  destruct hleft as [sigmaBranch [hleft _]].
  subst left.
  unfold rawDynamicTruthLocalPiBranches in hright.
  apply in_map_iff in hright.
  destruct hright as [piBranch [hright _]].
  subst right.
  exact (raw_dynamicTruthLocalCollisionMatrix_pair_guarded_imp
    M hPA context lowerPi lowerSigma sigmaBranch piBranch hinputs
    hpredecessor hfalseCell htrueCell).
Qed.

(** ------------------------------------------------------------------
    Elimination of the explicit Or7/Or6 rows. *)

Definition rawDynamicTruthLocalSigmaOr7Code
    (M : RawPAModel) (lowerPiApplication : M) : M :=
  rawFormulaOrCode M
    (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawFormulaOrCode M
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawFormulaOrCode M
        (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
        (rawFormulaOrCode M
          (rawDynamicTruthSigmaAndEx8BranchCode M)
          (rawFormulaOrCode M
            (rawDynamicTruthSigmaOrEx8BranchCode M)
            (rawFormulaOrCode M
              (rawDynamicTruthSigmaEx8BranchCode M)
              (rawDynamicTruthSigmaUniversalEx8BranchCode M
                lowerPiApplication)))))).

Definition rawDynamicTruthLocalPiOr6Code
    (M : RawPAModel) (lowerSigmaApplication : M) : M :=
  rawFormulaOrCode M
    (rawDynamicTruthPiQFEx8BranchCode M)
    (rawFormulaOrCode M
      (rawDynamicTruthPiImpEx8BranchCode M)
      (rawFormulaOrCode M
        (rawDynamicTruthPiAndEx8BranchCode M)
        (rawFormulaOrCode M
          (rawDynamicTruthPiOrEx8BranchCode M)
          (rawFormulaOrCode M
            (rawDynamicTruthPiAllEx8BranchCode M)
            (rawDynamicTruthPiExistentialEx8BranchCode M
              lowerSigmaApplication))))).

Theorem
    raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_of_pair_family :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaRowRoot piRowRoot,
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    (rawFormulaBotCode M) ->
  RawFiniteDisjunctionMatrixResources M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalSigmaOr7Code M lowerPiApplication)
    sigmaRowRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalPiOr6Code M lowerSigmaApplication)
    piRowRoot ->
  exists bottomRoot : M,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) bottomRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaRowRoot piRowRoot
    hpairs hresources hsigmaRow hpiRow.
  unfold rawDynamicTruthLocalSigmaBranches,
    dynamicTruthLocalSigmaBranchOrder,
    rawDynamicTruthLocalPiBranches,
    dynamicTruthLocalPiBranchOrder in hresources.
  cbn [map] in hresources.
  apply (raw_codedPALocalProofOf_rightDisjunctionSevenBySixMatrix
    M hPA context (rawFormulaBotCode M)
    (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
    (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
    (rawDynamicTruthSigmaAndEx8BranchCode M)
    (rawDynamicTruthSigmaOrEx8BranchCode M)
    (rawDynamicTruthSigmaEx8BranchCode M)
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi)
    (rawDynamicTruthPiQFEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    (rawDynamicTruthPiAndEx8BranchCode M)
    (rawDynamicTruthPiOrEx8BranchCode M)
    (rawDynamicTruthPiAllEx8BranchCode M)
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma)
    sigmaRowRoot piRowRoot hresources).
  - exact hsigmaRow.
  - exact hpiRow.
  - unfold rawDynamicTruthLocalSigmaBranches,
      dynamicTruthLocalSigmaBranchOrder,
      rawDynamicTruthLocalPiBranches,
      dynamicTruthLocalPiBranchOrder in hpairs.
    cbn [map] in hpairs.
    exact hpairs.
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaRowRoot piRowRoot,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawFiniteDisjunctionMatrixResources M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalSigmaOr7Code M lowerPiApplication)
    sigmaRowRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalPiOr6Code M lowerSigmaApplication)
    piRowRoot ->
  exists bottomRoot : M,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) bottomRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaRowRoot piRowRoot
    hinputs hresources hsigmaRow hpiRow.
  exact
    (raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_of_pair_family
      M hPA context lowerPi lowerSigma sigmaRowRoot piRowRoot
      (raw_dynamicTruthLocalCollisionMatrix_pair_family M hPA context
        lowerPi lowerSigma hinputs)
      hresources hsigmaRow hpiRow).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_guarded_imp :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication
      sigmaRowRoot piRowRoot,
  RawDynamicTruthLocalCollisionMatrixInputs M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M) ->
  RawDynamicTruthLocalRootAt M context
    (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M) ->
  RawFiniteDisjunctionMatrixResources M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication)
    (rawDynamicTruthLocalPiBranches M lowerSigmaApplication)
    context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalSigmaOr7Code M lowerPiApplication)
    sigmaRowRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalPiOr6Code M lowerSigmaApplication)
    piRowRoot ->
  exists bottomRoot : M,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) bottomRoot.
Proof.
  intros M hPA context lowerPi lowerSigma sigmaRowRoot piRowRoot
    hinputs hpredecessor hfalseCell htrueCell
    hresources hsigmaRow hpiRow.
  exact
    (raw_codedPALocalProofOf_dynamicTruthLocalCollisionMatrix_bottom_of_pair_family
      M hPA context lowerPi lowerSigma sigmaRowRoot piRowRoot
      (raw_dynamicTruthLocalCollisionMatrix_pair_family_guarded_imp
        M hPA context lowerPi lowerSigma hinputs
        hpredecessor hfalseCell htrueCell)
      hresources hsigmaRow hpiRow).
Qed.

End PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
