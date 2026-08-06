(**
  Constructor-local guards for the two Boolean diagonal collisions.

  The historical conjunction and disjunction cells assume that *every*
  synchronized predecessor row is exclusive.  The recursive truth table
  only justifies that assertion for direct children of the parent currently
  being evaluated.  This module states the honest guarded premise once,
  parametrically in the Boolean constructor, and reuses it for both the
  conjunction and disjunction diagonal cells.

  The constructor tag below is metatheoretic: each value selects one fixed
  formula of PA.  No nonstandard carrier element is inspected in Coq.  This
  keeps the represented statement small while factoring all proof plumbing
  shared by [and] and [or].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthImpGuardedBranchExclusivity.

Module PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.

(** The two constructors have identical direct-child proof structure. *)
Inductive DynamicTruthBooleanConstructor : Type :=
| DTBooleanAnd
| DTBooleanOr.

Definition rawDynamicTruthBooleanConstructorCode
    (M : RawPAModel) (constructor : DynamicTruthBooleanConstructor)
    (left right : M) : M :=
  match constructor with
  | DTBooleanAnd => rawFormulaAndCode M left right
  | DTBooleanOr => rawFormulaOrCode M left right
  end.

Definition dynamicTruthBooleanConstructorCodeTermAt
    (constructor : DynamicTruthBooleanConstructor)
    (parent left right : term) : formula :=
  match constructor with
  | DTBooleanAnd => formulaAndCodeTermAt parent left right
  | DTBooleanOr => formulaOrCodeTermAt parent left right
  end.

Lemma raw_sat_dynamicTruthBooleanConstructorCodeTermAt_iff : forall
    constructor (M : RawPAModel) e parent left right,
  raw_formula_sat M e
    (dynamicTruthBooleanConstructorCodeTermAt constructor
      parent left right) <->
  raw_term_eval M e parent =
    rawDynamicTruthBooleanConstructorCode M constructor
      (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros constructor M e parent left right.
  destruct constructor; cbn
    [dynamicTruthBooleanConstructorCodeTermAt
      rawDynamicTruthBooleanConstructorCode].
  - apply raw_sat_formulaAndCodeTermAt_iff.
  - apply raw_sat_formulaOrCodeTermAt_iff.
Qed.

(** Binder layout is deliberately identical to the guarded implication
    predecessor.  Beneath the outer state indices and common child, the
    parent is [#5].  Opening [left] and [right] moves it to [#7], while the
    common child becomes [#2]. *)
Definition dynamicTruthBooleanGuardedConstructorBodyFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pImp
    (dynamicTruthBooleanConstructorCodeTermAt constructor
      (tVar 7) (tVar 1) (tVar 0))
    (pImp
      (pOr
        (pEq (tVar 2) (tVar 1))
        (pEq (tVar 2) (tVar 0)))
      pBot).

Definition dynamicTruthBooleanGuardedPredecessorStateExclusivityBodyFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pImp
    (dynamicTruthStateMemberTermAt
      (tVar 15) (tVar 14) (tVar 13) (tVar 12)
      (tVar 11) (tVar 10) (tVar 9) (tVar 8)
      (tVar 7) (tVar 2) tZero (tVar 0)
      (tVar 4) (tVar 3))
    (pImp
      (dynamicTruthStateMemberTermAt
        (tVar 15) (tVar 14) (tVar 13) (tVar 12)
        (tVar 11) (tVar 10) (tVar 9) (tVar 8)
        (tVar 7) (tVar 1) (Term.numeral 1) (tVar 0)
        (tVar 4) (tVar 3))
      (pAll (pAll
        (dynamicTruthBooleanGuardedConstructorBodyFormula constructor)))).

Definition dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pAll (pAll (pAll
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityBodyFormula
      constructor))).

Definition RawDynamicTruthBooleanGuardedPredecessorStateExclusiveAt
    (constructor : DynamicTruthBooleanConstructor)
    (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current parent assignmentCode assignmentStep : M) : Prop :=
  forall sigmaIndex piIndex child : M,
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current sigmaIndex (raw_zero M) child
      assignmentCode assignmentStep ->
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current piIndex (rawNumeralValue M 1) child
      assignmentCode assignmentStep ->
    forall left right : M,
      parent = rawDynamicTruthBooleanConstructorCode M constructor
        left right ->
      (child = left \/ child = right) -> False.

Arguments RawDynamicTruthBooleanGuardedPredecessorStateExclusiveAt
  constructor M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current parent assignmentCode assignmentStep : clear implicits.

Lemma
    raw_sat_dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula_iff :
    forall constructor (M : RawPAModel) e,
  raw_formula_sat M e
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor) <->
  RawDynamicTruthBooleanGuardedPredecessorStateExclusiveAt constructor M
    (e 12) (e 11) (e 10) (e 9)
    (e 8) (e 7) (e 6) (e 5)
    (e 4) (e 2) (e 1) (e 0).
Proof.
  intros constructor M e.
  unfold dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula,
    dynamicTruthBooleanGuardedPredecessorStateExclusivityBodyFormula,
    dynamicTruthBooleanGuardedConstructorBodyFormula,
    RawDynamicTruthBooleanGuardedPredecessorStateExclusiveAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  setoid_rewrite
    raw_sat_dynamicTruthBooleanConstructorCodeTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Select the already established literal row branches by constructor. *)
Definition dynamicTruthBooleanSigmaEx8BranchFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  match constructor with
  | DTBooleanAnd => dynamicTruthSigmaAndEx8BranchFormula
  | DTBooleanOr => dynamicTruthSigmaOrEx8BranchFormula
  end.

Definition dynamicTruthBooleanPiEx8BranchFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  match constructor with
  | DTBooleanAnd => dynamicTruthPiAndEx8BranchFormula
  | DTBooleanOr => dynamicTruthPiOrEx8BranchFormula
  end.

Definition RawDynamicTruthBooleanSigmaEx8BranchAt constructor
    (M : RawPAModel) (e : nat -> M) : Prop :=
  match constructor with
  | DTBooleanAnd => RawDynamicTruthSigmaAndEx8BranchAt M e
  | DTBooleanOr => RawDynamicTruthSigmaOrEx8BranchAt M e
  end.

Definition RawDynamicTruthBooleanPiEx8BranchAt constructor
    (M : RawPAModel) (e : nat -> M) : Prop :=
  match constructor with
  | DTBooleanAnd => RawDynamicTruthPiAndEx8BranchAt M e
  | DTBooleanOr => RawDynamicTruthPiOrEx8BranchAt M e
  end.

Lemma raw_sat_dynamicTruthBooleanSigmaEx8BranchFormula_iff : forall
    constructor (M : RawPAModel) e,
  raw_formula_sat M e
    (dynamicTruthBooleanSigmaEx8BranchFormula constructor) <->
  RawDynamicTruthBooleanSigmaEx8BranchAt constructor M e.
Proof.
  intros constructor M e. destruct constructor; cbn
    [dynamicTruthBooleanSigmaEx8BranchFormula
      RawDynamicTruthBooleanSigmaEx8BranchAt].
  - apply raw_sat_dynamicTruthSigmaAndEx8BranchFormula_iff.
  - apply raw_sat_dynamicTruthSigmaOrEx8BranchFormula_iff.
Qed.

Lemma raw_sat_dynamicTruthBooleanPiEx8BranchFormula_iff : forall
    constructor (M : RawPAModel) e,
  raw_formula_sat M e
    (dynamicTruthBooleanPiEx8BranchFormula constructor) <->
  RawDynamicTruthBooleanPiEx8BranchAt constructor M e.
Proof.
  intros constructor M e. destruct constructor; cbn
    [dynamicTruthBooleanPiEx8BranchFormula
      RawDynamicTruthBooleanPiEx8BranchAt].
  - apply raw_sat_dynamicTruthPiAndEx8BranchFormula_iff.
  - apply raw_sat_dynamicTruthPiOrEx8BranchFormula_iff.
Qed.

Definition dynamicTruthBooleanGuardedConditionalCellFormula
    (constructor : DynamicTruthBooleanConstructor) : formula :=
  pImp
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor)
    (pImp (dynamicTruthBooleanSigmaEx8BranchFormula constructor)
      (pImp (dynamicTruthBooleanPiEx8BranchFormula constructor) pBot)).

Lemma raw_sat_dynamicTruthBooleanGuardedConditionalCellFormula_iff : forall
    constructor (M : RawPAModel) e,
  raw_formula_sat M e
    (dynamicTruthBooleanGuardedConditionalCellFormula constructor) <->
  (RawDynamicTruthBooleanGuardedPredecessorStateExclusiveAt constructor M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) (e 2) (e 1) (e 0) ->
   RawDynamicTruthBooleanSigmaEx8BranchAt constructor M e ->
   RawDynamicTruthBooleanPiEx8BranchAt constructor M e -> False).
Proof.
  intros constructor M e.
  unfold dynamicTruthBooleanGuardedConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite
    raw_sat_dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthBooleanSigmaEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthBooleanPiEx8BranchFormula_iff.
  reflexivity.
Qed.

(** One proof, by cases on the metatheoretic tag, covers both Boolean
    diagonals.  Constructor injectivity identifies the child on which the
    positive and negative predecessor states collide. *)
Theorem dynamicTruthBooleanGuardedConditionalCellFormula_raw_valid : forall
    constructor (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthBooleanGuardedConditionalCellFormula constructor).
Proof.
  intros constructor M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthBooleanGuardedConditionalCellFormula_iff
      constructor M e)).
  destruct constructor.
  - intros hexclusive hsigma hpi.
    cbn [RawDynamicTruthBooleanSigmaEx8BranchAt
      RawDynamicTruthBooleanPiEx8BranchAt] in hsigma, hpi.
    destruct hsigma as
      (sigmaLeftIndex & sigmaLeft & sigmaRightIndex & sigmaRight &
       sigmaWitness & sigmaNewCode & sigmaNewStep & sigmaSpare &
       hsigmaCode & hsigmaLeft & hsigmaRight).
    destruct hpi as
      (piLeftIndex & piLeft & piRightIndex & piRight &
       piWitness & piNewCode & piNewStep & piSpare &
       hpiCode & hpiCase).
    assert (hconstructor :
        rawFormulaAndCode M sigmaLeft sigmaRight =
        rawFormulaAndCode M piLeft piRight).
    { rewrite <- hsigmaCode, <- hpiCode. reflexivity. }
    destruct (rawFormulaAndCode_injective_cross M hPA
      sigmaLeft sigmaRight piLeft piRight hconstructor)
      as [hleft hright].
    destruct hpiCase as [hpiLeft | hpiRight].
    + subst piLeft.
      exact (hexclusive sigmaLeftIndex piLeftIndex sigmaLeft
        hsigmaLeft hpiLeft sigmaLeft sigmaRight hsigmaCode
        (or_introl eq_refl)).
    + subst piRight.
      exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
        hsigmaRight hpiRight sigmaLeft sigmaRight hsigmaCode
        (or_intror eq_refl)).
  - intros hexclusive hsigma hpi.
    cbn [RawDynamicTruthBooleanSigmaEx8BranchAt
      RawDynamicTruthBooleanPiEx8BranchAt] in hsigma, hpi.
    destruct hsigma as
      (sigmaLeftIndex & sigmaLeft & sigmaRightIndex & sigmaRight &
       sigmaWitness & sigmaNewCode & sigmaNewStep & sigmaSpare &
       hsigmaCode & hsigmaCase).
    destruct hpi as
      (piLeftIndex & piLeft & piRightIndex & piRight &
       piWitness & piNewCode & piNewStep & piSpare &
       hpiCode & hpiLeft & hpiRight).
    assert (hconstructor :
        rawFormulaOrCode M sigmaLeft sigmaRight =
        rawFormulaOrCode M piLeft piRight).
    { rewrite <- hsigmaCode, <- hpiCode. reflexivity. }
    destruct (rawFormulaOrCode_injective_cross M hPA
      sigmaLeft sigmaRight piLeft piRight hconstructor)
      as [hleft hright].
    destruct hsigmaCase as [hsigmaLeft | hsigmaRight].
    + subst piLeft.
      exact (hexclusive sigmaLeftIndex piLeftIndex sigmaLeft
        hsigmaLeft hpiLeft sigmaLeft sigmaRight hsigmaCode
        (or_introl eq_refl)).
    + subst piRight.
      exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
        hsigmaRight hpiRight sigmaLeft sigmaRight hsigmaCode
        (or_intror eq_refl)).
Qed.

Theorem PA_proves_dynamicTruthBooleanGuardedConditionalCellFormula : forall
    constructor,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthBooleanGuardedConditionalCellFormula constructor).
Proof.
  intro constructor.
  apply PA_proves_open_formula_of_raw_valid.
  exact (dynamicTruthBooleanGuardedConditionalCellFormula_raw_valid
    constructor).
Qed.

(** Transparent carrier codes for the generic predecessor, its selected
    row branches, and the guarded conditional cell. *)
Definition rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
    (M : RawPAModel) (constructor : DynamicTruthBooleanConstructor) : M :=
  rawFixedFormulaNumeralCode M
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor).

Definition rawDynamicTruthBooleanSigmaEx8BranchCode
    (M : RawPAModel) (constructor : DynamicTruthBooleanConstructor) : M :=
  match constructor with
  | DTBooleanAnd => rawDynamicTruthSigmaAndEx8BranchCode M
  | DTBooleanOr => rawDynamicTruthSigmaOrEx8BranchCode M
  end.

Definition rawDynamicTruthBooleanPiEx8BranchCode
    (M : RawPAModel) (constructor : DynamicTruthBooleanConstructor) : M :=
  match constructor with
  | DTBooleanAnd => rawDynamicTruthPiAndEx8BranchCode M
  | DTBooleanOr => rawDynamicTruthPiOrEx8BranchCode M
  end.

Definition rawDynamicTruthBooleanGuardedConditionalCellCode
    (M : RawPAModel) (constructor : DynamicTruthBooleanConstructor) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
      M constructor)
    (rawFormulaImpCode M
      (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
        (rawFormulaBotCode M))).

Lemma
    rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode_eq_quoted :
    forall constructor (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
      M constructor =
  rawQuotedFormulaCode M
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor).
Proof.
  intros constructor M hPA.
  unfold rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthBooleanSigmaEx8BranchCode_eq_quoted : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthBooleanSigmaEx8BranchCode M constructor =
  rawQuotedFormulaCode M
    (dynamicTruthBooleanSigmaEx8BranchFormula constructor).
Proof.
  intros constructor M hPA. destruct constructor; cbn
    [rawDynamicTruthBooleanSigmaEx8BranchCode
      dynamicTruthBooleanSigmaEx8BranchFormula].
  - apply rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted. exact hPA.
  - apply rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthBooleanPiEx8BranchCode_eq_quoted : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthBooleanPiEx8BranchCode M constructor =
  rawQuotedFormulaCode M
    (dynamicTruthBooleanPiEx8BranchFormula constructor).
Proof.
  intros constructor M hPA. destruct constructor; cbn
    [rawDynamicTruthBooleanPiEx8BranchCode
      dynamicTruthBooleanPiEx8BranchFormula].
  - apply rawDynamicTruthPiAndEx8BranchCode_eq_quoted. exact hPA.
  - apply rawDynamicTruthPiOrEx8BranchCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthBooleanGuardedConditionalCellCode_eq_quoted : forall
    constructor (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthBooleanGuardedConditionalCellCode M constructor =
  rawQuotedFormulaCode M
    (dynamicTruthBooleanGuardedConditionalCellFormula constructor).
Proof.
  intros constructor M hPA.
  unfold rawDynamicTruthBooleanGuardedConditionalCellCode,
    dynamicTruthBooleanGuardedConditionalCellFormula.
  rewrite
    rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthBooleanSigmaEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthBooleanPiEx8BranchCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthBooleanGuardedConditionalCell :
    forall constructor (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthBooleanGuardedConditionalCellCode M constructor)
      certificate.
Proof.
  intros constructor M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthBooleanGuardedConditionalCellFormula constructor)
    (PA_proves_dynamicTruthBooleanGuardedConditionalCellFormula
      constructor)) as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthBooleanGuardedConditionalCellCode_eq_quoted
    by exact hPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** Applying a guarded cell to its matching predecessor root leaves exactly
    the two branch implications required by the local collision matrix. *)
Theorem raw_dynamicTruthBooleanGuarded_pair : forall
    constructor (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthBooleanGuardedConditionalCellCode M constructor)
    cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
      M constructor) predecessorRoot ->
  exists pairRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros constructor M hPA context cellRoot predecessorRoot
    hcell hpredecessor.
  unfold rawDynamicTruthBooleanGuardedConditionalCellCode in hcell.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
      M constructor)
    (rawFormulaImpCode M
      (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
        (rawFormulaBotCode M)))
    cellRoot predecessorRoot hcell hpredecessor) as hpair.
  eexists. exact hpair.
Qed.

End PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
