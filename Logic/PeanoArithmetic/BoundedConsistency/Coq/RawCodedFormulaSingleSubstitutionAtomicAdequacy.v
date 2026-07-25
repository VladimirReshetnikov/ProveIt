(**
  Atomic adequacy after represented single substitution.

  A formula-operation trace already supplies an honest target formula
  postorder, including for nonstandard trace bounds.  Thus preservation of
  [RawCodedFormulaAtomicallyAdequate] reduces exactly to the equality leaves.
  At such a leaf, the substitution atom first shifts the replacement to the
  current binder depth and then opens the source term with that shifted code.

  [RawCodedTermOpeningAfterShiftSyntaxStable] records the one genuinely
  term-level preservation theorem still needed below.  It does not assume
  that any carrier value is a standard quotation, nor does it ask for an
  unrelated functionality law.  Everything above that seam—including
  constructor separation, recovery of the atomic operation rows, target
  formula syntax, and iteration through three substitutions—is proved here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedAssignment RawCodedProofDescent
  RawCodedTermEvaluationRealization RawCodedTermEvaluationStepFunctionality
  RawCodedFormulaOperations
  RawCodedFormulaOperationQuotedRankSound
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaSingleSubstitutionTotality.

Import ListNotations.

Module PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationQuotedRankSound.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaSingleSubstitutionTotality.

(** This is the exact unresolved term-syntax seam.  The premise includes the
    two represented traces actually stored by a substitution atom.  The
    replacement begins with any honest syntax certificate; the conclusion
    may use any target assignment defined through an enclosing code which
    strictly contains the opening output. *)
Definition RawCodedTermOpeningAfterShiftSyntaxStable
    (M : RawPAModel) : Prop :=
  forall replacement depth input liftedReplacement output : M,
    RawCodedTermShift M (raw_zero M) depth
      replacement liftedReplacement ->
    RawCodedTermOpening M depth liftedReplacement input output ->
    forall replacementAssignmentCode replacementAssignmentStep : M,
      RawTermSyntaxRealizable M replacement
        replacementAssignmentCode replacementAssignmentStep ->
    forall targetAssignmentCode targetAssignmentStep enclosing : M,
      rawLt M output enclosing ->
      RawCodedAssignmentDefinedThrough M
        targetAssignmentCode targetAssignmentStep enclosing ->
      RawTermSyntaxRealizable M output
        targetAssignmentCode targetAssignmentStep.

Arguments RawCodedTermOpeningAfterShiftSyntaxStable M : clear implicits.

(** The seam is equivalently usable directly at a formula-substitution atom.
    This wrapper keeps the formula proof independent of the atom's existential
    packaging while retaining the two concrete term traces above. *)
Lemma raw_codedFormulaSubstitutionAtom_target_syntax_of_opening_stable :
  forall (M : RawPAModel),
  RawCodedTermOpeningAfterShiftSyntaxStable M ->
  forall replacement depth input output,
  RawCodedFormulaSubstitutionAtom M replacement depth input output ->
  forall replacementAssignmentCode replacementAssignmentStep,
  RawTermSyntaxRealizable M replacement
    replacementAssignmentCode replacementAssignmentStep ->
  forall targetAssignmentCode targetAssignmentStep enclosing,
  rawLt M output enclosing ->
  RawCodedAssignmentDefinedThrough M
    targetAssignmentCode targetAssignmentStep enclosing ->
  RawTermSyntaxRealizable M output
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hstable replacement depth input output
    (liftedReplacement & hshift & hopening)
    replacementAssignmentCode replacementAssignmentStep hreplacement
    targetAssignmentCode targetAssignmentStep enclosing houtput hassignment.
  exact (hstable replacement depth input liftedReplacement output
    hshift hopening replacementAssignmentCode replacementAssignmentStep
    hreplacement targetAssignmentCode targetAssignmentStep enclosing
    houtput hassignment).
Qed.

(** Equality fields lie strictly below their enclosing list code. *)
Lemma raw_formulaSubstitution_eq_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M left (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_formulaSubstitution_eq_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M right (rawFormulaEqCode M left right).
Proof.
  intros M hPA left right.
  unfold rawFormulaEqCode, rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |]. cbn. tauto.
Qed.

Lemma raw_formulaSubstitution_nonzero_binary_neq_eq : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right eqLeft eqRight,
  tag <> 0 ->
  rawCodeList3 M (rawNumeralValue M tag) left right <>
  rawFormulaEqCode M eqLeft eqRight.
Proof.
  intros M hPA tag left right eqLeft eqRight htag heq.
  unfold rawFormulaEqCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [htags _].
  apply (rawNumeralValue_injective M hPA tag 0) in htags.
  exact (htag htags).
Qed.

(** Constructor separation is independent of the atomic relation.  If a
    target row is an equality, no bottom, connective, or quantifier branch
    can have produced it. *)
Lemma raw_formulaOperation_eq_row_of_target : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (atom : M -> M -> M -> M -> Prop)
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth left right,
  RawCodedFormulaOperationTraversalRow M atom
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  output = rawFormulaEqCode M left right ->
  RawCodedFormulaEqOperationRow M atom parameter depth input output.
Proof.
  intros M hPA atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth left right hrow houtputEq.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [exact heq | ..].
  - destruct hbot as [_ houtput]. exfalso.
    unfold rawFormulaBotCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct himp as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaSubstitution_nonzero_binary_neq_eq
      M hPA 2 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaImpCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hand as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaSubstitution_nonzero_binary_neq_eq
      M hPA 3 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaAndCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hor as
      (_ & _ & outputLeft & _ & _ & _ & outputRight & _ &
       _ & _ & _ & _ & _ & _ & _ & houtput).
    exfalso. apply (raw_formulaSubstitution_nonzero_binary_neq_eq
      M hPA 4 outputLeft outputRight left right); [discriminate |].
    unfold rawFormulaOrCode in houtput.
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hall as
      (_ & _ & outputChild & _ & _ & _ & _ & _ & houtput).
    exfalso. unfold rawFormulaAllCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) outputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
  - destruct hex as
      (_ & _ & outputChild & _ & _ & _ & _ & _ & houtput).
    exfalso. unfold rawFormulaExCode, rawFormulaEqCode in houtput, houtputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) outputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym houtput) houtputEq).
Qed.

(** The target is atomically adequate.  Notice that source adequacy is not
    needed here: the represented operation trace itself validates every
    target constructor, and the explicit term stability law validates the
    only atomic payloads. *)
Theorem raw_codedFormulaSingleSubstitution_target_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningAfterShiftSyntaxStable M ->
  forall replacement replacementAssignmentCode replacementAssignmentStep,
  RawTermSyntaxRealizable M replacement
    replacementAssignmentCode replacementAssignmentStep ->
  forall input output,
  RawCodedFormulaSingleSubstitution M replacement input output ->
  RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA hstable replacement replacementAssignmentCode
    replacementAssignmentStep hreplacement input output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof (raw_formulaOperationTrace_target_syntax M
    (RawCodedFormulaSubstitutionAtom M) replacement (raw_zero M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output htrace) as htargetSyntax.
  exists targetCode, targetStep, bound, rootIndex.
  split; [exact htargetSyntax |].
  intros index code left right assignmentCode assignmentStep
    hindex htargetLookup hcodeEq hassignment.
  destruct htrace as
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  destruct (hsourceDefined index hindex) as [source hsourceLookup].
  destruct (hdepthDefined index hindex) as [depth hdepthLookup].
  pose proof (hrows index source code depth hindex
    (conj hsourceLookup (conj htargetLookup hdepthLookup))) as hrow.
  pose proof (raw_formulaOperation_eq_row_of_target M hPA
    (RawCodedFormulaSubstitutionAtom M)
    replacement sourceCode sourceStep targetCode targetStep
    depthCode depthStep index source code depth left right hrow hcodeEq)
    as heqRow.
  destruct heqRow as
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsourceEq & htargetEq & hleftSubstitution & hrightSubstitution).
  assert (htargetFields : targetLeft = left /\ targetRight = right).
  {
    unfold rawFormulaEqCode in htargetEq, hcodeEq.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ (eq_trans (eq_sym htargetEq) hcodeEq))
      as [_ [hleft hright]]. exact (conj hleft hright).
  }
  destruct htargetFields as [-> ->]. split.
  - apply (raw_codedFormulaSubstitutionAtom_target_syntax_of_opening_stable
      M hstable replacement depth sourceLeft left hleftSubstitution
      replacementAssignmentCode replacementAssignmentStep hreplacement
      assignmentCode assignmentStep code).
    + rewrite hcodeEq.
      exact (raw_formulaSubstitution_eq_left_lt M hPA left right).
    + exact hassignment.
  - apply (raw_codedFormulaSubstitutionAtom_target_syntax_of_opening_stable
      M hstable replacement depth sourceRight right hrightSubstitution
      replacementAssignmentCode replacementAssignmentStep hreplacement
      assignmentCode assignmentStep code).
    + rewrite hcodeEq.
      exact (raw_formulaSubstitution_eq_right_lt M hPA left right).
    + exact hassignment.
Qed.

(** Totality and stability combine into the exact reusable chaining step. *)
Theorem raw_codedFormulaSingleSubstitution_exists_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M ->
  RawCodedTermOpeningAfterShiftSyntaxStable M ->
  forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  exists target,
    RawCodedFormulaSingleSubstitution M replacement source target /\
    RawCodedFormulaAtomicallyAdequate M target.
Proof.
  intros M hPA hopeningTotal hstable source hsource replacement
    assignmentCode assignmentStep hreplacement.
  destruct (raw_codedFormulaSingleSubstitution_exists_of_atomically_adequate
    M hPA hopeningTotal source hsource replacement
    assignmentCode assignmentStep hreplacement) as [target hsubstitution].
  exists target. split; [exact hsubstitution |].
  exact (raw_codedFormulaSingleSubstitution_target_atomically_adequate
    M hPA hstable replacement assignmentCode assignmentStep hreplacement
    source target hsubstitution).
Qed.

(** Three applications are the immediate use case for the dynamic truth
    orbit.  Every intermediate code remains in the same honest nonstandard
    domain, so the next totality invocation is justified without decoding. *)
Theorem raw_codedFormulaSingleSubstitution_three_exists :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M ->
  RawCodedTermOpeningAfterShiftSyntaxStable M ->
  forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement1 assignmentCode1 assignmentStep1,
  RawTermSyntaxRealizable M replacement1 assignmentCode1 assignmentStep1 ->
  forall replacement2 assignmentCode2 assignmentStep2,
  RawTermSyntaxRealizable M replacement2 assignmentCode2 assignmentStep2 ->
  forall replacement3 assignmentCode3 assignmentStep3,
  RawTermSyntaxRealizable M replacement3 assignmentCode3 assignmentStep3 ->
  exists target1 target2 target3,
    RawCodedFormulaSingleSubstitution M replacement1 source target1 /\
    RawCodedFormulaAtomicallyAdequate M target1 /\
    RawCodedFormulaSingleSubstitution M replacement2 target1 target2 /\
    RawCodedFormulaAtomicallyAdequate M target2 /\
    RawCodedFormulaSingleSubstitution M replacement3 target2 target3 /\
    RawCodedFormulaAtomicallyAdequate M target3.
Proof.
  intros M hPA hopeningTotal hstable source hsource
    replacement1 assignmentCode1 assignmentStep1 hreplacement1
    replacement2 assignmentCode2 assignmentStep2 hreplacement2
    replacement3 assignmentCode3 assignmentStep3 hreplacement3.
  destruct (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA hopeningTotal hstable source hsource
    replacement1 assignmentCode1 assignmentStep1 hreplacement1)
    as (target1 & hsubstitution1 & htarget1).
  destruct (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA hopeningTotal hstable target1 htarget1
    replacement2 assignmentCode2 assignmentStep2 hreplacement2)
    as (target2 & hsubstitution2 & htarget2).
  destruct (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA hopeningTotal hstable target2 htarget2
    replacement3 assignmentCode3 assignmentStep3 hreplacement3)
    as (target3 & hsubstitution3 & htarget3).
  exists target1, target2, target3.
  repeat split; assumption.
Qed.

End PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
