(**
  Two conditional implication cells in the dynamic-truth constructor matrix.

  The native Sigma row has two ways to certify a true implication: a false
  left child or a true right child.  The native Pi row certifies a false
  implication by a true left child and a false right child.  Consequently,
  either Sigma implication branch collides with the Pi implication branch
  once the synchronized predecessor-state table is known to be exclusive.

  This file keeps that predecessor obligation completely explicit.  The
  literal row branches expose [RawDynamicTruthStateMember] atoms; they do
  not, by themselves, expose applications of the preceding global Sigma and
  Pi formula codes.  Thus the conditional cells below consume a local proof
  of state-table exclusivity.  No state-member-to-application compiler, and
  no complete constructor matrix or local field, is claimed here.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedPAProvability
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedPAProofImpICertificates
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthPairedSuccessorAdequacy.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthImpBranchExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

(** ------------------------------------------------------------------
    The honest predecessor-state exclusivity premise.

    Outside the native eight row witnesses, the synchronized table columns
    occupy variables [#12] through [#5], the current row is [#4], and the
    common assignment is [#1,#0].  Three universal binders introduce a
    Sigma-state index, a Pi-state index, and their common child code. *)

Definition dynamicTruthImpPredecessorStateExclusivityFormula : formula :=
  pAll (pAll (pAll
    (pImp
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
        pBot)))).

Definition RawDynamicTruthImpPredecessorStateExclusiveAt
    (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current assignmentCode assignmentStep : M) : Prop :=
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
      assignmentCode assignmentStep -> False.

Arguments RawDynamicTruthImpPredecessorStateExclusiveAt
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
    dynamicTruthImpPredecessorStateExclusivityFormula <->
  RawDynamicTruthImpPredecessorStateExclusiveAt M
    (e 12) (e 11) (e 10) (e 9)
    (e 8) (e 7) (e 6) (e 5)
    (e 4) (e 1) (e 0).
Proof.
  intros M e.
  unfold dynamicTruthImpPredecessorStateExclusivityFormula,
    RawDynamicTruthImpPredecessorStateExclusiveAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The three literal native [Ex8] implication branches. *)

Definition dynamicTruthSigmaImpFalseLeftEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowImpFalseLeftFormula.

Definition dynamicTruthSigmaImpTrueRightEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowImpTrueRightFormula.

Definition dynamicTruthPiImpEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthPiRowImpFormula.

Definition RawDynamicTruthSigmaImpFalseLeftEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaImpCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (rawNumeralValue M 1) leftCode
      (e 1) (e 0) /\
    spare = spare.

Definition RawDynamicTruthSigmaImpTrueRightEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaImpCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (raw_zero M) rightCode
      (e 1) (e 0) /\
    spare = spare.

Definition RawDynamicTruthPiImpEx8BranchAt
    (M : RawPAModel) (e : nat -> M) : Prop :=
  exists leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M,
    e 2 = rawFormulaImpCode M leftCode rightCode /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) leftIndex (raw_zero M) leftCode
      (e 1) (e 0) /\
    RawDynamicTruthStateMember M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) rightIndex (rawNumeralValue M 1) rightCode
      (e 1) (e 0) /\
    spare = spare.

Arguments RawDynamicTruthSigmaImpFalseLeftEx8BranchAt M e
  : clear implicits.
Arguments RawDynamicTruthSigmaImpTrueRightEx8BranchAt M e
  : clear implicits.
Arguments RawDynamicTruthPiImpEx8BranchAt M e : clear implicits.

Lemma raw_sat_dynamicTruthSigmaImpFalseLeftEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthSigmaImpFalseLeftEx8BranchFormula <->
  RawDynamicTruthSigmaImpFalseLeftEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthSigmaImpFalseLeftEx8BranchFormula,
    dynamicTruthSigmaRowImpFalseLeftFormula,
    RawDynamicTruthSigmaImpFalseLeftEx8BranchAt,
    fixedLevelEx8, fixedLevelAnd3.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthSigmaImpTrueRightEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthSigmaImpTrueRightEx8BranchFormula <->
  RawDynamicTruthSigmaImpTrueRightEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthSigmaImpTrueRightEx8BranchFormula,
    dynamicTruthSigmaRowImpTrueRightFormula,
    RawDynamicTruthSigmaImpTrueRightEx8BranchAt,
    fixedLevelEx8, fixedLevelAnd3.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPiImpEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthPiImpEx8BranchFormula <->
  RawDynamicTruthPiImpEx8BranchAt M e.
Proof.
  intros M e.
  unfold dynamicTruthPiImpEx8BranchFormula,
    dynamicTruthPiRowImpFormula,
    RawDynamicTruthPiImpEx8BranchAt,
    fixedLevelEx8, fixedLevelAnd4.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The two conditional matrix cells and their exact semantics. *)

Definition dynamicTruthImpFalseLeftConditionalCellFormula : formula :=
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaImpFalseLeftEx8BranchFormula
      (pImp dynamicTruthPiImpEx8BranchFormula pBot)).

Definition dynamicTruthImpTrueRightConditionalCellFormula : formula :=
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaImpTrueRightEx8BranchFormula
      (pImp dynamicTruthPiImpEx8BranchFormula pBot)).

Lemma raw_sat_dynamicTruthImpFalseLeftConditionalCellFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthImpFalseLeftConditionalCellFormula <->
  (RawDynamicTruthImpPredecessorStateExclusiveAt M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) (e 1) (e 0) ->
   RawDynamicTruthSigmaImpFalseLeftEx8BranchAt M e ->
   RawDynamicTruthPiImpEx8BranchAt M e -> False).
Proof.
  intros M e.
  unfold dynamicTruthImpFalseLeftConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaImpFalseLeftEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthImpTrueRightConditionalCellFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthImpTrueRightConditionalCellFormula <->
  (RawDynamicTruthImpPredecessorStateExclusiveAt M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) (e 1) (e 0) ->
   RawDynamicTruthSigmaImpTrueRightEx8BranchAt M e ->
   RawDynamicTruthPiImpEx8BranchAt M e -> False).
Proof.
  intros M e.
  unfold dynamicTruthImpTrueRightConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaImpTrueRightEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.
  reflexivity.
Qed.

Theorem dynamicTruthImpFalseLeftConditionalCellFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthImpFalseLeftConditionalCellFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthImpFalseLeftConditionalCellFormula_iff M e)).
  intros hexclusive hsigma hpi.
  destruct hsigma as
    (sigmaLeftIndex & sigmaLeft & sigmaRightIndex & sigmaRight &
     sigmaWitness & sigmaNewAssignmentCode & sigmaNewAssignmentStep &
     sigmaSpare & hsigmaCode & hsigmaLeft & _).
  destruct hpi as
    (piLeftIndex & piLeft & piRightIndex & piRight &
     piWitness & piNewAssignmentCode & piNewAssignmentStep &
     piSpare & hpiCode & hpiLeft & hpiRight & _).
  assert (hconstructor :
      rawFormulaImpCode M sigmaLeft sigmaRight =
      rawFormulaImpCode M piLeft piRight).
  {
    rewrite <- hsigmaCode, <- hpiCode. reflexivity.
  }
  destruct (rawFormulaImpCode_injective_cross M hPA
    sigmaLeft sigmaRight piLeft piRight hconstructor)
    as [hleft _].
  subst piLeft.
  exact (hexclusive piLeftIndex sigmaLeftIndex sigmaLeft
    hpiLeft hsigmaLeft).
Qed.

Theorem dynamicTruthImpTrueRightConditionalCellFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthImpTrueRightConditionalCellFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthImpTrueRightConditionalCellFormula_iff M e)).
  intros hexclusive hsigma hpi.
  destruct hsigma as
    (sigmaLeftIndex & sigmaLeft & sigmaRightIndex & sigmaRight &
     sigmaWitness & sigmaNewAssignmentCode & sigmaNewAssignmentStep &
     sigmaSpare & hsigmaCode & hsigmaRight & _).
  destruct hpi as
    (piLeftIndex & piLeft & piRightIndex & piRight &
     piWitness & piNewAssignmentCode & piNewAssignmentStep &
     piSpare & hpiCode & hpiLeft & hpiRight & _).
  assert (hconstructor :
      rawFormulaImpCode M sigmaLeft sigmaRight =
      rawFormulaImpCode M piLeft piRight).
  {
    rewrite <- hsigmaCode, <- hpiCode. reflexivity.
  }
  destruct (rawFormulaImpCode_injective_cross M hPA
    sigmaLeft sigmaRight piLeft piRight hconstructor)
    as [_ hright].
  subst piRight.
  exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
    hsigmaRight hpiRight).
Qed.

(** A small open-validity wrapper.  Completeness is applied only after
    sealing the formula; elimination of that fixed standard seal then gives
    an ordinary PA proof of the original conditional cell. *)
Lemma PA_proves_open_formula_of_raw_valid : forall target : formula,
  (forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e target) ->
  Formula.BProv Formula.Ax_s [] target.
Proof.
  intros target hvalid.
  assert (hclosed : Formula.BProv Formula.Ax_s [] (Formula.sealPA target)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner. exact (hvalid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] target (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Theorem PA_proves_dynamicTruthImpFalseLeftConditionalCellFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthImpFalseLeftConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthImpFalseLeftConditionalCellFormula_raw_valid.
Qed.

Theorem PA_proves_dynamicTruthImpTrueRightConditionalCellFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthImpTrueRightConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthImpTrueRightConditionalCellFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier codes for the premise, branches, and cells. *)

Definition rawDynamicTruthImpPredecessorStateExclusivityCode
    (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M
    dynamicTruthImpPredecessorStateExclusivityFormula.

Definition rawDynamicTruthSigmaImpFalseLeftRowCode
    (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M
    dynamicTruthSigmaRowImpFalseLeftFormula.

Definition rawDynamicTruthSigmaImpTrueRightRowCode
    (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M
    dynamicTruthSigmaRowImpTrueRightFormula.

Definition rawDynamicTruthPiImpRowCode (M : RawPAModel) : M :=
  rawDynamicTruthPiFixedFormulaNumeralCode M
    dynamicTruthPiRowImpFormula.

Definition rawDynamicTruthSigmaImpFalseLeftEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M (rawDynamicTruthSigmaImpFalseLeftRowCode M).

Definition rawDynamicTruthSigmaImpTrueRightEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M (rawDynamicTruthSigmaImpTrueRightRowCode M).

Definition rawDynamicTruthPiImpEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M (rawDynamicTruthPiImpRowCode M).

Definition rawDynamicTruthImpFalseLeftConditionalCellCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).

Definition rawDynamicTruthImpTrueRightConditionalCellCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).

Lemma rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpPredecessorStateExclusivityCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpPredecessorStateExclusivityFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpPredecessorStateExclusivityCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M =
  rawQuotedFormulaCode M
    dynamicTruthSigmaImpFalseLeftEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaImpFalseLeftEx8BranchCode,
    rawDynamicTruthSigmaImpFalseLeftRowCode,
    dynamicTruthSigmaImpFalseLeftEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaImpTrueRightEx8BranchCode M =
  rawQuotedFormulaCode M
    dynamicTruthSigmaImpTrueRightEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaImpTrueRightEx8BranchCode,
    rawDynamicTruthSigmaImpTrueRightRowCode,
    dynamicTruthSigmaImpTrueRightEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthPiImpEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiImpEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthPiImpEx8BranchFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthPiImpEx8BranchCode,
    rawDynamicTruthPiImpRowCode,
    dynamicTruthPiImpEx8BranchFormula, fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthImpFalseLeftConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpFalseLeftConditionalCellCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpFalseLeftConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpFalseLeftConditionalCellCode,
    dynamicTruthImpFalseLeftConditionalCellFormula.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthImpTrueRightConditionalCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpTrueRightConditionalCellCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpTrueRightConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpTrueRightConditionalCellCode,
    dynamicTruthImpTrueRightConditionalCellFormula.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

(** Standard-numeral equations are used both by the represented-proof
    bridge and by the atomic-adequacy checks for guarded context insertion. *)
Lemma rawDynamicTruthImpPredecessorStateExclusivityCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpPredecessorStateExclusivityCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthImpPredecessorStateExclusivityFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthSigmaImpFalseLeftEx8BranchFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaImpTrueRightEx8BranchCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthSigmaImpTrueRightEx8BranchFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthPiImpEx8BranchCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiImpEx8BranchCode M =
  rawNumeralValue M (formulaCode dynamicTruthPiImpEx8BranchFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthImpFalseLeftConditionalCellCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpFalseLeftConditionalCellCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthImpFalseLeftConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpFalseLeftConditionalCellCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthImpTrueRightConditionalCellCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpTrueRightConditionalCellCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthImpTrueRightConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpTrueRightConditionalCellCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

(** ------------------------------------------------------------------
    Ordinary represented proofs of the two conditional cells. *)

Theorem raw_codedPAProofOf_dynamicTruthImpFalseLeftConditionalCell : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthImpFalseLeftConditionalCellCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthImpFalseLeftConditionalCellFormula
    PA_proves_dynamicTruthImpFalseLeftConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthImpFalseLeftConditionalCellCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthImpTrueRightConditionalCell : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthImpTrueRightConditionalCellCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthImpTrueRightConditionalCellFormula
    PA_proves_dynamicTruthImpTrueRightConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthImpTrueRightConditionalCellCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Exact common-context local collision compiler.

    This compiler is deliberately parameterized by a checked local root of
    the predecessor-state exclusivity premise.  It performs exactly three
    implication eliminations and does not manufacture that premise. *)

Definition rawDynamicTruthImpConditionalCellCollisionRoot
    (M : RawPAModel)
    (context predecessor sigmaBranch piBranch
      cellRoot predecessorRoot sigmaRoot piRoot : M) : M :=
  rawProofImpERoot M context piBranch (rawFormulaBotCode M)
    (rawProofImpERoot M context sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
      (rawProofImpERoot M context predecessor
        (rawFormulaImpCode M sigmaBranch
          (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
        cellRoot predecessorRoot)
      sigmaRoot)
    piRoot.

Arguments rawDynamicTruthImpConditionalCellCollisionRoot
  M context predecessor sigmaBranch piBranch
    cellRoot predecessorRoot sigmaRoot piRoot : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context predecessor sigmaBranch piBranch
      cellRoot predecessorRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M predecessor
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellRoot ->
  RawCodedPALocalProofOf M context predecessor predecessorRoot ->
  RawCodedPALocalProofOf M context sigmaBranch sigmaRoot ->
  RawCodedPALocalProofOf M context piBranch piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthImpConditionalCellCollisionRoot M context
      predecessor sigmaBranch piBranch
      cellRoot predecessorRoot sigmaRoot piRoot).
Proof.
  intros M hPA context predecessor sigmaBranch piBranch
    cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi.
  unfold rawDynamicTruthImpConditionalCellCollisionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    piBranch (rawFormulaBotCode M)); [|exact hpi].
  apply (raw_codedPALocalProofOf_impE M hPA context
    sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M)));
    [|exact hsigma].
  exact (raw_codedPALocalProofOf_impE M hPA context
    predecessor
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    cellRoot predecessorRoot hcell hpredecessor).
Qed.

Definition rawDynamicTruthImpFalseLeftConditionalCellCollisionRoot
    (M : RawPAModel)
    (context cellRoot predecessorRoot sigmaRoot piRoot : M) : M :=
  rawDynamicTruthImpConditionalCellCollisionRoot M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot.

Definition rawDynamicTruthImpTrueRightConditionalCellCollisionRoot
    (M : RawPAModel)
    (context cellRoot predecessorRoot sigmaRoot piRoot : M) : M :=
  rawDynamicTruthImpConditionalCellCollisionRoot M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot predecessorRoot sigmaRoot piRoot.

Arguments rawDynamicTruthImpFalseLeftConditionalCellCollisionRoot
  M context cellRoot predecessorRoot sigmaRoot piRoot : clear implicits.
Arguments rawDynamicTruthImpTrueRightConditionalCellCollisionRoot
  M context cellRoot predecessorRoot sigmaRoot piRoot : clear implicits.

Corollary
    raw_codedPALocalProofOf_dynamicTruthImpFalseLeftConditionalCellCollision
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpFalseLeftConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M) predecessorRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiImpEx8BranchCode M) piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthImpFalseLeftConditionalCellCollisionRoot M context
      cellRoot predecessorRoot sigmaRoot piRoot).
Proof.
  intros M hPA context cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi.
  unfold rawDynamicTruthImpFalseLeftConditionalCellCollisionRoot,
    rawDynamicTruthImpFalseLeftConditionalCellCode.
  exact
    (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
      M hPA context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawDynamicTruthPiImpEx8BranchCode M)
      cellRoot predecessorRoot sigmaRoot piRoot
      hcell hpredecessor hsigma hpi).
Qed.

Corollary
    raw_codedPALocalProofOf_dynamicTruthImpTrueRightConditionalCellCollision
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      context cellRoot predecessorRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpTrueRightConditionalCellCode M) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M) predecessorRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiImpEx8BranchCode M) piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthImpTrueRightConditionalCellCollisionRoot M context
      cellRoot predecessorRoot sigmaRoot piRoot).
Proof.
  intros M hPA context cellRoot predecessorRoot sigmaRoot piRoot
    hcell hpredecessor hsigma hpi.
  unfold rawDynamicTruthImpTrueRightConditionalCellCollisionRoot,
    rawDynamicTruthImpTrueRightConditionalCellCode.
  exact
    (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
      M hPA context
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
      (rawDynamicTruthPiImpEx8BranchCode M)
      cellRoot predecessorRoot sigmaRoot piRoot
      hcell hpredecessor hsigma hpi).
Qed.

(** Insert all three assumptions into one realizable context.  This helper
    records every guarded context extension explicitly; in particular, it
    never invokes an unrestricted weakening principle. *)
Theorem raw_dynamicTruthImpConditionalCellCollision_under_assumptions :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context predecessor sigmaBranch piBranch cellRoot,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M predecessor ->
  RawCodedFormulaAtomicallyAdequate M sigmaBranch ->
  RawCodedFormulaAtomicallyAdequate M piBranch ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M predecessor
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M piBranch
        (rawListNode M sigmaBranch
          (rawListNode M predecessor context)))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context predecessor sigmaBranch piBranch cellRoot
    hcontext hpredecessorAdequate hsigmaAdequate hpiAdequate hcell.
  set (predecessorContext := rawListNode M predecessor context).
  assert (hpredecessorContext :
      RawContextListRealizable M predecessorContext).
  {
    unfold predecessorContext.
    exact (raw_contextList_cons_realizable M hPA
      context predecessor hcontext).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context predecessor
    (rawFormulaImpCode M predecessor
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellRoot hpredecessorAdequate hcontext hcell)
    as [cellPredecessor hcellPredecessor].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    context predecessor hcontext) as hpredecessorHead.
  set (sigmaContext := rawListNode M sigmaBranch predecessorContext).
  assert (hsigmaContext : RawContextListRealizable M sigmaContext).
  {
    unfold sigmaContext.
    exact (raw_contextList_cons_realizable M hPA
      predecessorContext sigmaBranch hpredecessorContext).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    predecessorContext sigmaBranch
    (rawFormulaImpCode M predecessor
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellPredecessor hsigmaAdequate hpredecessorContext hcellPredecessor)
    as [cellSigma hcellSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    predecessorContext sigmaBranch predecessor
    (rawProofAssumptionRoot M predecessorContext predecessor)
    hsigmaAdequate hpredecessorContext hpredecessorHead)
    as [predecessorSigma hpredecessorSigma].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    predecessorContext sigmaBranch hpredecessorContext) as hsigmaHead.
  set (piContext := rawListNode M piBranch sigmaContext).
  assert (hpiContext : RawContextListRealizable M piContext).
  {
    unfold piContext.
    exact (raw_contextList_cons_realizable M hPA
      sigmaContext piBranch hsigmaContext).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch
    (rawFormulaImpCode M predecessor
      (rawFormulaImpCode M sigmaBranch
        (rawFormulaImpCode M piBranch (rawFormulaBotCode M))))
    cellSigma hpiAdequate hsigmaContext hcellSigma)
    as [cellPi hcellPi].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch predecessor predecessorSigma
    hpiAdequate hsigmaContext hpredecessorSigma)
    as [predecessorPi hpredecessorPi].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch sigmaBranch
    (rawProofAssumptionRoot M sigmaContext sigmaBranch)
    hpiAdequate hsigmaContext hsigmaHead)
    as [sigmaPi hsigmaPi].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    sigmaContext piBranch hsigmaContext) as hpiHead.
  exists (rawDynamicTruthImpConditionalCellCollisionRoot M piContext
    predecessor sigmaBranch piBranch cellPi predecessorPi sigmaPi
    (rawProofAssumptionRoot M piContext piBranch)).
  exact
    (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
      M hPA piContext predecessor sigmaBranch piBranch
      cellPi predecessorPi sigmaPi
      (rawProofAssumptionRoot M piContext piBranch)
      hcellPi hpredecessorPi hsigmaPi hpiHead).
Qed.

(** Fixed specializations.  Their contexts visibly retain the predecessor
    exclusivity assumption, which remains the obligation of the caller. *)
Corollary
    raw_dynamicTruthImpFalseLeftConditionalCellCollision_under_assumptions
    : forall (M : RawPAModel), RawPASatisfies M -> forall context cellRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpFalseLeftConditionalCellCode M) cellRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawListNode M
          (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
          (rawListNode M
            (rawDynamicTruthImpPredecessorStateExclusivityCode M)
            context)))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context cellRoot hcontext hcell.
  unfold rawDynamicTruthImpFalseLeftConditionalCellCode in hcell.
  apply (raw_dynamicTruthImpConditionalCellCollision_under_assumptions
    M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot hcontext).
  - rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthImpPredecessorStateExclusivityFormula).
  - rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaImpFalseLeftEx8BranchFormula).
  - rewrite rawDynamicTruthPiImpEx8BranchCode_eq_numeral by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiImpEx8BranchFormula).
  - exact hcell.
Qed.

Corollary
    raw_dynamicTruthImpTrueRightConditionalCellCollision_under_assumptions
    : forall (M : RawPAModel), RawPASatisfies M -> forall context cellRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthImpTrueRightConditionalCellCode M) cellRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawListNode M
          (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
          (rawListNode M
            (rawDynamicTruthImpPredecessorStateExclusivityCode M)
            context)))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context cellRoot hcontext hcell.
  unfold rawDynamicTruthImpTrueRightConditionalCellCode in hcell.
  apply (raw_dynamicTruthImpConditionalCellCollision_under_assumptions
    M hPA context
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
    (rawDynamicTruthPiImpEx8BranchCode M)
    cellRoot hcontext).
  - rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthImpPredecessorStateExclusivityFormula).
  - rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaImpTrueRightEx8BranchFormula).
  - rewrite rawDynamicTruthPiImpEx8BranchCode_eq_numeral by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiImpEx8BranchFormula).
  - exact hcell.
Qed.

(** The ordinary represented cell proofs can be opened into witnessed PA
    bases.  Even there, contradiction appears only after the predecessor
    exclusivity formula and both selected branches are adjoined. *)
Theorem raw_dynamicTruthImpFalseLeftConditionalCell_local_base : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext cellRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpFalseLeftConditionalCellCode M) cellRoot.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_dynamicTruthImpFalseLeftConditionalCell
    M hPA) as [certificate hcertificate].
  destruct hcertificate as
    (witnessList & cellRoot & baseContext &
      _ & hwitness & hcoverage & hendpoint).
  exists witnessList, baseContext, cellRoot.
  split; [exact hwitness |]. split; assumption.
Qed.

Theorem raw_dynamicTruthImpTrueRightConditionalCell_local_base : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext cellRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpTrueRightConditionalCellCode M) cellRoot.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_dynamicTruthImpTrueRightConditionalCell
    M hPA) as [certificate hcertificate].
  destruct hcertificate as
    (witnessList & cellRoot & baseContext &
      _ & hwitness & hcoverage & hendpoint).
  exists witnessList, baseContext, cellRoot.
  split; [exact hwitness |]. split; assumption.
Qed.

Theorem
    raw_dynamicTruthImpFalseLeftConditionalCellCollision_in_witnessed_base
    : forall (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext collisionRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawListNode M
          (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
          (rawListNode M
            (rawDynamicTruthImpPredecessorStateExclusivityCode M)
            baseContext)))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA.
  destruct (raw_dynamicTruthImpFalseLeftConditionalCell_local_base M hPA)
    as (witnessList & baseContext & cellRoot & hwitness & hcell).
  assert (hcontext : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  destruct
    (raw_dynamicTruthImpFalseLeftConditionalCellCollision_under_assumptions
      M hPA baseContext cellRoot hcontext hcell)
    as [collisionRoot hcollision].
  exists witnessList, baseContext, collisionRoot.
  split; assumption.
Qed.

Theorem
    raw_dynamicTruthImpTrueRightConditionalCellCollision_in_witnessed_base
    : forall (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext collisionRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawListNode M
          (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
          (rawListNode M
            (rawDynamicTruthImpPredecessorStateExclusivityCode M)
            baseContext)))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA.
  destruct (raw_dynamicTruthImpTrueRightConditionalCell_local_base M hPA)
    as (witnessList & baseContext & cellRoot & hwitness & hcell).
  assert (hcontext : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  destruct
    (raw_dynamicTruthImpTrueRightConditionalCellCollision_under_assumptions
      M hPA baseContext cellRoot hcontext hcell)
    as [collisionRoot hcollision].
  exists witnessList, baseContext, collisionRoot.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthImpBranchExclusivity.
