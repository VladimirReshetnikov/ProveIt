(**
  Conditional conjunction and disjunction cells in the native row matrix.

  A Sigma conjunction stores two earlier positive states, whereas a Pi
  conjunction stores one earlier negative state.  A Sigma disjunction stores
  one earlier positive state, whereas a Pi disjunction stores two earlier
  negative states.  Formula-constructor injectivity aligns the corresponding
  children, so both same-constructor cells reduce to the explicit
  predecessor-state exclusivity law introduced by the implication-cell
  module.

  As there, this file proves the conditional cells and their exact represented
  proof interfaces; it does not manufacture the predecessor invariant or
  claim the complete seven-by-six matrix.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedDynamicTruthImpBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.

(** ------------------------------------------------------------------
    Literal eight-witness branch formulae and exact semantic views. *)

Definition dynamicTruthSigmaAndEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowAndFormula.

Definition dynamicTruthPiAndEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthPiRowAndFormula.

Definition dynamicTruthSigmaOrEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowOrFormula.

Definition dynamicTruthPiOrEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthPiRowOrFormula.

Definition RawDynamicTruthSigmaAndEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaAndCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (raw_zero M) leftCode (e 1) (e 0) /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (raw_zero M) rightCode (e 1) (e 0).

Definition RawDynamicTruthPiAndEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaAndCode M leftCode rightCode /\
    (RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (rawNumeralValue M 1) leftCode (e 1) (e 0) \/
     RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (rawNumeralValue M 1) rightCode (e 1) (e 0)).

Definition RawDynamicTruthSigmaOrEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaOrCode M leftCode rightCode /\
    (RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (raw_zero M) leftCode (e 1) (e 0) \/
     RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (raw_zero M) rightCode (e 1) (e 0)).

Definition RawDynamicTruthPiOrEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaOrCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (rawNumeralValue M 1) leftCode (e 1) (e 0) /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (rawNumeralValue M 1) rightCode (e 1) (e 0).

Arguments RawDynamicTruthSigmaAndEx8BranchAt M e : clear implicits.
Arguments RawDynamicTruthPiAndEx8BranchAt M e : clear implicits.
Arguments RawDynamicTruthSigmaOrEx8BranchAt M e : clear implicits.
Arguments RawDynamicTruthPiOrEx8BranchAt M e : clear implicits.

Lemma raw_sat_dynamicTruthSigmaAndEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthSigmaAndEx8BranchFormula <->
  RawDynamicTruthSigmaAndEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthSigmaAndEx8BranchFormula,
    dynamicTruthSigmaRowAndFormula,
    RawDynamicTruthSigmaAndEx8BranchAt, fixedLevelEx8, fixedLevelAnd3.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaAndCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPiAndEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthPiAndEx8BranchFormula <->
  RawDynamicTruthPiAndEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthPiAndEx8BranchFormula,
    dynamicTruthPiRowAndFormula,
    RawDynamicTruthPiAndEx8BranchAt, fixedLevelEx8.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaAndCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_dynamicTruthSigmaOrEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthSigmaOrEx8BranchFormula <->
  RawDynamicTruthSigmaOrEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthSigmaOrEx8BranchFormula,
    dynamicTruthSigmaRowOrFormula,
    RawDynamicTruthSigmaOrEx8BranchAt, fixedLevelEx8.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaOrCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPiOrEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthPiOrEx8BranchFormula <->
  RawDynamicTruthPiOrEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthPiOrEx8BranchFormula,
    dynamicTruthPiRowOrFormula,
    RawDynamicTruthPiOrEx8BranchAt, fixedLevelEx8, fixedLevelAnd3.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaOrCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Conditional cells and their PA proofs. *)

Definition dynamicTruthAndConditionalCellFormula : formula :=
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaAndEx8BranchFormula
      (pImp dynamicTruthPiAndEx8BranchFormula pBot)).

Definition dynamicTruthOrConditionalCellFormula : formula :=
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaOrEx8BranchFormula
      (pImp dynamicTruthPiOrEx8BranchFormula pBot)).

Theorem dynamicTruthAndConditionalCellFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthAndConditionalCellFormula.
Proof.
  intros M hPA e.
  unfold dynamicTruthAndConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaAndEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiAndEx8BranchFormula_iff.
  intros hexclusive hsigma hpi.
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
  - subst piLeft.
    exact (hexclusive sigmaLeftIndex piLeftIndex sigmaLeft
      hsigmaLeft hpiLeft).
  - subst piRight.
    exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
      hsigmaRight hpiRight).
Qed.

Theorem dynamicTruthOrConditionalCellFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthOrConditionalCellFormula.
Proof.
  intros M hPA e.
  unfold dynamicTruthOrConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaOrEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiOrEx8BranchFormula_iff.
  intros hexclusive hsigma hpi.
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
  - subst piLeft.
    exact (hexclusive sigmaLeftIndex piLeftIndex sigmaLeft
      hsigmaLeft hpiLeft).
  - subst piRight.
    exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
      hsigmaRight hpiRight).
Qed.

Theorem PA_proves_dynamicTruthAndConditionalCellFormula :
  Formula.BProv Formula.Ax_s [] dynamicTruthAndConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthAndConditionalCellFormula_raw_valid.
Qed.

Theorem PA_proves_dynamicTruthOrConditionalCellFormula :
  Formula.BProv Formula.Ax_s [] dynamicTruthOrConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthOrConditionalCellFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    Exact carrier codes and represented proof certificates. *)

Definition rawDynamicTruthSigmaAndEx8BranchCode (M : RawPAModel) : M :=
  rawFormulaEx8Code M
    (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowAndFormula).

Definition rawDynamicTruthPiAndEx8BranchCode (M : RawPAModel) : M :=
  rawFormulaEx8Code M
    (rawDynamicTruthPiFixedFormulaNumeralCode M dynamicTruthPiRowAndFormula).

Definition rawDynamicTruthSigmaOrEx8BranchCode (M : RawPAModel) : M :=
  rawFormulaEx8Code M
    (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowOrFormula).

Definition rawDynamicTruthPiOrEx8BranchCode (M : RawPAModel) : M :=
  rawFormulaEx8Code M
    (rawDynamicTruthPiFixedFormulaNumeralCode M dynamicTruthPiRowOrFormula).

Definition rawDynamicTruthAndConditionalCellCode (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M (rawDynamicTruthSigmaAndEx8BranchCode M)
      (rawFormulaImpCode M (rawDynamicTruthPiAndEx8BranchCode M)
        (rawFormulaBotCode M))).

Definition rawDynamicTruthOrConditionalCellCode (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M (rawDynamicTruthSigmaOrEx8BranchCode M)
      (rawFormulaImpCode M (rawDynamicTruthPiOrEx8BranchCode M)
        (rawFormulaBotCode M))).

Lemma rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaAndEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthSigmaAndEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaAndEx8BranchCode,
    dynamicTruthSigmaAndEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA). reflexivity.
Qed.

Lemma rawDynamicTruthPiAndEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiAndEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthPiAndEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthPiAndEx8BranchCode,
    dynamicTruthPiAndEx8BranchFormula, fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaOrEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthSigmaOrEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaOrEx8BranchCode,
    dynamicTruthSigmaOrEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA). reflexivity.
Qed.

Lemma rawDynamicTruthPiOrEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiOrEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthPiOrEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthPiOrEx8BranchCode,
    dynamicTruthPiOrEx8BranchFormula, fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthAndConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthAndConditionalCellCode M =
  rawQuotedFormulaCode M dynamicTruthAndConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthAndConditionalCellCode,
    dynamicTruthAndConditionalCellFormula.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted by exact hPA.
  rewrite rawDynamicTruthPiAndEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthOrConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthOrConditionalCellCode M =
  rawQuotedFormulaCode M dynamicTruthOrConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthOrConditionalCellCode,
    dynamicTruthOrConditionalCellFormula.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted by exact hPA.
  rewrite rawDynamicTruthPiOrEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthAndConditionalCellCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthAndConditionalCellCode M =
  rawNumeralValue M (formulaCode dynamicTruthAndConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthAndConditionalCellCode_eq_quoted by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthOrConditionalCellCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthOrConditionalCellCode M =
  rawNumeralValue M (formulaCode dynamicTruthOrConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthOrConditionalCellCode_eq_quoted by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthAndConditionalCell : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate,
    RawCodedPAProofOf M (rawDynamicTruthAndConditionalCellCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthAndConditionalCellFormula
    PA_proves_dynamicTruthAndConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthAndConditionalCellCode_eq_numeral by exact hPA.
  exact hcertificate.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthOrConditionalCell : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate,
    RawCodedPAProofOf M (rawDynamicTruthOrConditionalCellCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthOrConditionalCellFormula
    PA_proves_dynamicTruthOrConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthOrConditionalCellCode_eq_numeral by exact hPA.
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Common-context collision endpoints. *)

Theorem raw_codedPALocalProofOf_dynamicTruthAndConditionalCellCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthAndConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M) predecessorRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaAndEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiAndEx8BranchCode M) piRoot ->
  exists collisionRoot,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi.
  exists (rawDynamicTruthImpConditionalCellCollisionRoot M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaAndEx8BranchCode M)
    (rawDynamicTruthPiAndEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot).
  unfold rawDynamicTruthAndConditionalCellCode in hcell.
  exact (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
    M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaAndEx8BranchCode M)
    (rawDynamicTruthPiAndEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi).
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthOrConditionalCellCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthOrConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M) predecessorRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaOrEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiOrEx8BranchCode M) piRoot ->
  exists collisionRoot,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi.
  exists (rawDynamicTruthImpConditionalCellCollisionRoot M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaOrEx8BranchCode M)
    (rawDynamicTruthPiOrEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot).
  unfold rawDynamicTruthOrConditionalCellCode in hcell.
  exact (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
    M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaOrEx8BranchCode M)
    (rawDynamicTruthPiOrEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi).
Qed.

End PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
