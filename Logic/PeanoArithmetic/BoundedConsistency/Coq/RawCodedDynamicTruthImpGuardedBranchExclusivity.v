(**
  Implication collisions guarded by direct-child predecessor exclusivity.

  The original implication cells consume unconditional exclusivity of every
  synchronized predecessor-table row.  That premise is stronger than the
  row data justify: atomic adequacy and rank domains propagate only to the
  displayed children of the current constructor.

  The guarded premise below keeps the existing three binders for the two
  state indices and their common child.  Only after both state assumptions
  does it quantify the implication's left and right codes and require that
  the common child is one of them.  This binder order is deliberate.  Global
  row projection can continue to produce both evidence roots in the old
  joint-state context; constructor-specific admissibility is derived later,
  beneath the two additional witnesses and their shape/direct-child guards.

  Both native implication collisions are already strong enough to discharge
  those guards.  Constructor injectivity synchronizes the Sigma and Pi row
  witnesses, exactly as in the historical unconditional cells.
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
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedPAProvability.

Module PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.

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
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedPAProvability.

(** Outside the three predecessor binders the synchronized table layout is
    unchanged.  Beneath them the common child is [#0] and the current parent
    is [#5].  Two later binders introduce left and right, moving the parent
    to [#7] and the common child to [#2]. *)
Definition dynamicTruthImpGuardedConstructorBodyFormula : formula :=
  pImp
    (formulaImpCodeTermAt (tVar 7) (tVar 1) (tVar 0))
    (pImp
      (pOr
        (pEq (tVar 2) (tVar 1))
        (pEq (tVar 2) (tVar 0)))
      pBot).

Definition dynamicTruthImpGuardedPredecessorStateExclusivityBodyFormula
    : formula :=
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
      (pAll (pAll dynamicTruthImpGuardedConstructorBodyFormula))).

Definition dynamicTruthImpGuardedPredecessorStateExclusivityFormula
    : formula :=
  pAll (pAll (pAll
    dynamicTruthImpGuardedPredecessorStateExclusivityBodyFormula)).

Definition RawDynamicTruthImpGuardedPredecessorStateExclusiveAt
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
      parent = rawFormulaImpCode M left right ->
      (child = left \/ child = right) -> False.

Arguments RawDynamicTruthImpGuardedPredecessorStateExclusiveAt
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current parent assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_dynamicTruthImpGuardedPredecessorStateExclusivityFormula_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula <->
  RawDynamicTruthImpGuardedPredecessorStateExclusiveAt M
    (e 12) (e 11) (e 10) (e 9)
    (e 8) (e 7) (e 6) (e 5)
    (e 4) (e 2) (e 1) (e 0).
Proof.
  intros M e.
  unfold dynamicTruthImpGuardedPredecessorStateExclusivityFormula,
    dynamicTruthImpGuardedPredecessorStateExclusivityBodyFormula,
    dynamicTruthImpGuardedConstructorBodyFormula,
    RawDynamicTruthImpGuardedPredecessorStateExclusiveAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Guarded replacements for the two implication matrix cells. *)
Definition dynamicTruthImpFalseLeftGuardedConditionalCellFormula : formula :=
  pImp dynamicTruthImpGuardedPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaImpFalseLeftEx8BranchFormula
      (pImp dynamicTruthPiImpEx8BranchFormula pBot)).

Definition dynamicTruthImpTrueRightGuardedConditionalCellFormula : formula :=
  pImp dynamicTruthImpGuardedPredecessorStateExclusivityFormula
    (pImp dynamicTruthSigmaImpTrueRightEx8BranchFormula
      (pImp dynamicTruthPiImpEx8BranchFormula pBot)).

Lemma raw_sat_dynamicTruthImpFalseLeftGuardedConditionalCellFormula_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula <->
  (RawDynamicTruthImpGuardedPredecessorStateExclusiveAt M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) (e 2) (e 1) (e 0) ->
   RawDynamicTruthSigmaImpFalseLeftEx8BranchAt M e ->
   RawDynamicTruthPiImpEx8BranchAt M e -> False).
Proof.
  intros M e.
  unfold dynamicTruthImpFalseLeftGuardedConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite
    raw_sat_dynamicTruthImpGuardedPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaImpFalseLeftEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthImpTrueRightGuardedConditionalCellFormula_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
    dynamicTruthImpTrueRightGuardedConditionalCellFormula <->
  (RawDynamicTruthImpGuardedPredecessorStateExclusiveAt M
      (e 12) (e 11) (e 10) (e 9)
      (e 8) (e 7) (e 6) (e 5)
      (e 4) (e 2) (e 1) (e 0) ->
   RawDynamicTruthSigmaImpTrueRightEx8BranchAt M e ->
   RawDynamicTruthPiImpEx8BranchAt M e -> False).
Proof.
  intros M e.
  unfold dynamicTruthImpTrueRightGuardedConditionalCellFormula.
  cbn [raw_formula_sat].
  rewrite
    raw_sat_dynamicTruthImpGuardedPredecessorStateExclusivityFormula_iff.
  rewrite raw_sat_dynamicTruthSigmaImpTrueRightEx8BranchFormula_iff.
  rewrite raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.
  reflexivity.
Qed.

Theorem dynamicTruthImpFalseLeftGuardedConditionalCellFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthImpFalseLeftGuardedConditionalCellFormula_iff
      M e)).
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
  { rewrite <- hsigmaCode, <- hpiCode. reflexivity. }
  destruct (rawFormulaImpCode_injective_cross M hPA
    sigmaLeft sigmaRight piLeft piRight hconstructor) as [hleft _].
  subst piLeft.
  exact (hexclusive piLeftIndex sigmaLeftIndex sigmaLeft
    hpiLeft hsigmaLeft sigmaLeft sigmaRight hsigmaCode
    (or_introl eq_refl)).
Qed.

Theorem dynamicTruthImpTrueRightGuardedConditionalCellFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthImpTrueRightGuardedConditionalCellFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthImpTrueRightGuardedConditionalCellFormula_iff
      M e)).
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
  { rewrite <- hsigmaCode, <- hpiCode. reflexivity. }
  destruct (rawFormulaImpCode_injective_cross M hPA
    sigmaLeft sigmaRight piLeft piRight hconstructor) as [_ hright].
  subst piRight.
  exact (hexclusive sigmaRightIndex piRightIndex sigmaRight
    hsigmaRight hpiRight sigmaLeft sigmaRight hsigmaCode
    (or_intror eq_refl)).
Qed.

Theorem PA_proves_dynamicTruthImpFalseLeftGuardedConditionalCellFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthImpFalseLeftGuardedConditionalCellFormula_raw_valid.
Qed.

Theorem PA_proves_dynamicTruthImpTrueRightGuardedConditionalCellFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthImpTrueRightGuardedConditionalCellFormula.
Proof.
  apply PA_proves_open_formula_of_raw_valid.
  exact dynamicTruthImpTrueRightGuardedConditionalCellFormula_raw_valid.
Qed.

(** Transparent carrier codes and represented PA certificates, ready for
    substitution into the native fixed-helper bundle. *)
Definition rawDynamicTruthImpGuardedPredecessorStateExclusivityCode
    (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula.

Definition rawDynamicTruthImpFalseLeftGuardedConditionalCellCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).

Definition rawDynamicTruthImpTrueRightGuardedConditionalCellCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).

Lemma rawDynamicTruthImpGuardedPredecessorStateExclusivityCode_eq_quoted :
    forall (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpGuardedPredecessorStateExclusivityCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthImpFalseLeftGuardedConditionalCellCode_eq_quoted :
    forall (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpFalseLeftGuardedConditionalCellCode,
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula.
  rewrite rawDynamicTruthImpGuardedPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthImpTrueRightGuardedConditionalCellCode_eq_quoted :
    forall (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpTrueRightGuardedConditionalCellCode M =
  rawQuotedFormulaCode M
    dynamicTruthImpTrueRightGuardedConditionalCellFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthImpTrueRightGuardedConditionalCellCode,
    dynamicTruthImpTrueRightGuardedConditionalCellFormula.
  rewrite rawDynamicTruthImpGuardedPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiImpEx8BranchCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthImpFalseLeftGuardedConditionalCellCode_eq_numeral :
    forall (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthImpFalseLeftGuardedConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpFalseLeftGuardedConditionalCellCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthImpTrueRightGuardedConditionalCellCode_eq_numeral :
    forall (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpTrueRightGuardedConditionalCellCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthImpTrueRightGuardedConditionalCellFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpTrueRightGuardedConditionalCellCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Theorem
    raw_codedPAProofOf_dynamicTruthImpFalseLeftGuardedConditionalCell :
    forall (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthImpFalseLeftGuardedConditionalCellCode M)
      certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthImpFalseLeftGuardedConditionalCellFormula
    PA_proves_dynamicTruthImpFalseLeftGuardedConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthImpFalseLeftGuardedConditionalCellCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

Theorem
    raw_codedPAProofOf_dynamicTruthImpTrueRightGuardedConditionalCell :
    forall (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthImpTrueRightGuardedConditionalCellCode M)
      certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthImpTrueRightGuardedConditionalCellFormula
    PA_proves_dynamicTruthImpTrueRightGuardedConditionalCellFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthImpTrueRightGuardedConditionalCellCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

End PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
