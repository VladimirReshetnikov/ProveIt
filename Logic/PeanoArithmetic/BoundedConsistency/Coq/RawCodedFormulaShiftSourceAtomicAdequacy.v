(**
  Atomic syntax adequacy for the source of a represented formula shift.

  Target adequacy belongs to the basic shift module.  Source adequacy also
  needs the independently proved source-column syntax realization for term
  shifts, so it lives in this small downstream module rather than creating a
  dependency cycle.  Higher formula-bound clients and template compilers can
  now share the result without importing one another.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation
  RawCodedTermEvaluationStepFunctionality
  RawCodedFormulaOperations
  RawCodedFormulaRankTotality
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedFormulaSubstitutionAtomSourceSyntax.

Module PABoundedRawCodedFormulaShiftSourceAtomicAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.

(** Forget target and depth data in one operation row.  Child source
    lookups are the first projections of the synchronized triple lookups. *)
Lemma raw_codedFormulaOperationTraversalRow_source_syntax_core : forall
    (M : RawPAModel) atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth,
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  RawCodedFormulaSyntaxTraversalRow M
    sourceCode sourceStep index input.
Proof.
  intros M atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as
      (inputLeft & outputLeft & inputRight & outputRight &
        hinput & _ & _ & _).
    left. exists inputLeft, inputRight. exact hinput.
  - right. left. exact (proj1 hbot).
  - right. right. left.
    destruct himp as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & outputLeft & leftDepth &
       rightIndex & inputRight & outputRight & rightDepth &
       hleftIndex & hleftLookup & _ & hrightIndex & hrightLookup & _ &
       hinput & _).
    exists leftIndex, inputLeft, rightIndex, inputRight.
    repeat split; try assumption.
    + exact (proj1 hleftLookup).
    + exact (proj1 hrightLookup).
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    repeat split; try assumption.
    exact (proj1 hchildLookup).
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & outputChild & childDepth &
       hchildIndex & hchildLookup & _ & hinput & _).
    exists childIndex, inputChild.
    repeat split; try assumption.
    exact (proj1 hchildLookup).
Qed.

(** If an operation source is an equality, constructor separation rules out
    every non-equality source row.  This is the source-column counterpart of
    [raw_formulaShift_eq_row_of_target]. *)
Lemma raw_formulaShift_eq_row_of_source_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth left right,
  RawCodedFormulaOperationTraversalRow M (RawCodedFormulaShiftAtom M)
    parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth ->
  input = rawFormulaEqCode M left right ->
  RawCodedFormulaEqOperationRow M (RawCodedFormulaShiftAtom M)
    parameter depth input output.
Proof.
  intros M hPA parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth left right hrow hinputEq.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [exact heq | ..].
  - destruct hbot as [hinput _]. exfalso.
    unfold rawFormulaBotCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct himp as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 2 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaImpCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hand as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 3 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaAndCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hor as
      (_ & inputLeft & _ & _ & _ & inputRight & _ & _ &
       _ & _ & _ & _ & _ & _ & hinput & _).
    exfalso. apply (raw_formulaShift_nonzero_binary_neq_eq
      M hPA 4 inputLeft inputRight left right); [discriminate |].
    unfold rawFormulaOrCode in hinput.
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hall as
      (_ & inputChild & _ & _ & _ & _ & _ & hinput & _).
    exfalso. unfold rawFormulaAllCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) inputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
  - destruct hex as
      (_ & inputChild & _ & _ & _ & _ & _ & hinput & _).
    exfalso. unfold rawFormulaExCode, rawFormulaEqCode in hinput, hinputEq.
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) inputChild
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hinput) hinputEq).
Qed.

(** A formula shift certifies the source formula's atomic term payloads as
    represented syntax, including for nonstandard traces. *)
Theorem raw_codedFormulaShift_source_atomically_adequate_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount input output,
  RawCodedFormulaShift M cutoff amount input output ->
  RawCodedFormulaAtomicallyAdequate M input.
Proof.
  intros M hPA cutoff amount input output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as htraceForSyntax.
  assert (hsourceSyntax : RawCodedFormulaSyntaxTraversal M
      sourceCode sourceStep bound rootIndex input).
  {
    destruct htraceForSyntax as
      (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
       hrootLookup & hrows).
    repeat split; try assumption.
    - exact (proj1 hrootLookup).
    - intros index code hindex hsourceLookup.
      destruct (htargetDefined index hindex) as [target htargetLookup].
      destruct (hdepthDefined index hindex) as [depth hdepthLookup].
      apply (raw_codedFormulaOperationTraversalRow_source_syntax_core M
        (RawCodedFormulaShiftAtom M) amount
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        index code target depth).
      apply hrows; [exact hindex |].
      repeat split; assumption.
  }
  exists sourceCode, sourceStep, bound, rootIndex.
  split; [exact hsourceSyntax |].
  intros index code left right assignmentCode assignmentStep
    hindex hsourceLookup hcodeEq hassignment.
  destruct htrace as
    (hsourceDefined & htargetDefined & hdepthDefined & hrootBelow &
     hrootLookup & hrows).
  destruct (htargetDefined index hindex) as [target htargetLookup].
  destruct (hdepthDefined index hindex) as [depth hdepthLookup].
  pose proof (hrows index code target depth hindex
    (conj hsourceLookup (conj htargetLookup hdepthLookup))) as hrow.
  pose proof (raw_formulaShift_eq_row_of_source_core M hPA
    amount sourceCode sourceStep targetCode targetStep depthCode depthStep
    index code target depth left right hrow hcodeEq) as heqRow.
  destruct heqRow as
    (sourceLeft & targetLeft & sourceRight & targetRight &
     hsourceEq & htargetEq & hleftShift & hrightShift).
  assert (hsourceFields : sourceLeft = left /\ sourceRight = right).
  {
    unfold rawFormulaEqCode in hsourceEq, hcodeEq.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ (eq_trans (eq_sym hsourceEq) hcodeEq))
      as [_ [hleft hright]]. exact (conj hleft hright).
  }
  destruct hsourceFields as [-> ->]. split.
  - apply (raw_codedTermShift_source_syntax_realizable M hPA
      depth amount left targetLeft assignmentCode assignmentStep code).
    + exact hleftShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_left_lt M hPA left right).
    + exact hassignment.
  - apply (raw_codedTermShift_source_syntax_realizable M hPA
      depth amount right targetRight assignmentCode assignmentStep code).
    + exact hrightShift.
    + rewrite hcodeEq. exact (raw_formulaShift_eq_right_lt M hPA left right).
    + exact hassignment.
Qed.

End PABoundedRawCodedFormulaShiftSourceAtomicAdequacy.
