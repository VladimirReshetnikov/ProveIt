(**
  Totality of represented single substitution on nonstandard formula codes.

  The public operation is a synchronized beta-coded traversal, so its input
  need not be the quotation of a metatheoretic formula.  The honest domain is
  [RawCodedFormulaAtomicallyAdequate]: it supplies a represented formula
  postorder and genuine term-syntax certificates at every equality leaf.
  The replacement is separately guarded by [RawTermSyntaxRealizable].

  Formula-level composition is closed here without an extra premise.  The
  only lower-level seam is [RawCodedTermOpeningTotal]: after the replacement
  has itself been shifted to the current binder depth, opening must be total
  on a certified (possibly nonstandard) term code.  This is exactly the term
  analogue of [raw_codedTermShift_exists_of_syntax_realizable]; no standard
  quotation, decoding function, or hidden functionality hypothesis occurs in
  the interface.  The final theorem below makes this one premise explicit.
*)

From Stdlib Require Import Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawModelCompleteness
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedAssignmentTotality
  RawCodedProofDescent
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaShiftTotality
  RawCodedFormulaOperationTraceConcatenation.

Module PABoundedRawCodedFormulaSingleSubstitutionTotality.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.

(** The precise lower-level totality law.  Opening may insert an arbitrary
    carrier value, so only the source term needs a syntax certificate.  The
    replacement-syntax guard enters one level above, when that replacement is
    shifted capture-avoidably before opening. *)
Definition RawCodedTermOpeningTotal (M : RawPAModel) : Prop :=
  forall input assignmentCode assignmentStep : M,
    RawTermSyntaxRealizable M input assignmentCode assignmentStep ->
    forall cutoff liftedReplacement : M,
      exists output : M,
        RawCodedTermOpening M cutoff liftedReplacement input output.

Arguments RawCodedTermOpeningTotal M : clear implicits.

(** Totality of the atomic action at one equality payload.  The represented
    shift computes the capture-avoiding lift of the replacement; the explicit
    opening law then transforms the source term. *)
Lemma raw_codedFormulaSubstitutionAtom_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M ->
  forall replacement replacementAssignmentCode replacementAssignmentStep,
  RawTermSyntaxRealizable M replacement
    replacementAssignmentCode replacementAssignmentStep ->
  forall depth input inputAssignmentCode inputAssignmentStep,
  RawTermSyntaxRealizable M input inputAssignmentCode inputAssignmentStep ->
  exists output,
    RawCodedFormulaSubstitutionAtom M
      replacement depth input output.
Proof.
  intros M hPA hopening replacement replacementAssignmentCode
    replacementAssignmentStep hreplacement depth input
    inputAssignmentCode inputAssignmentStep hinput.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement replacementAssignmentCode replacementAssignmentStep
    hreplacement (raw_zero M) depth) as [liftedReplacement hshift].
  destruct (hopening input inputAssignmentCode inputAssignmentStep hinput
    depth liftedReplacement) as [output hopen].
  exists output, liftedReplacement. split; assumption.
Qed.

(** ------------------------------------------------------------------
    Constructor composition for the formula traversal.

    These proofs are atom-parametric in the generic concatenation engine;
    only the final specialization fixes the substitution atom. *)

Lemma raw_codedFormulaSubstitution_binary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      kind replacement depth sourceLeft targetLeft sourceRight targetRight,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth sourceLeft targetLeft ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth sourceRight targetRight ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight).
Proof.
  intros M hPA kind replacement depth sourceLeft targetLeft
    sourceRight targetRight hleft hright.
  unfold RawCodedFormulaOperation in hleft, hright |- *.
  destruct hleft as
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftDepthCode & leftDepthStep & leftBound & leftRootIndex & hleft).
  destruct hright as
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightDepthCode & rightDepthStep & rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 (proj2 hleft)))). }
  destruct (raw_formulaOperationTraces_concatenate M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    replacement depth
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftDepthCode leftDepthStep leftBound leftRootIndex
    sourceLeft targetLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex
    sourceRight targetRight hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        depthCode & depthStep & hcombined & hleftRetained).
  destruct hcombined as
    [hsourceDefined [htargetDefined [hdepthDefined
      [hrightBelow [hrightRoot hrows]]]]].
  set (combinedBound := raw_add M leftBound rightBound).
  assert (hleftCombinedBelow : rawLt M leftRootIndex combinedBound).
  {
    unfold combinedBound.
    exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound
      (raw_add M leftBound rightBound) hleftBelow
      (raw_proof_left_le_sum M leftBound rightBound)).
  }
  assert (hbinary : RawCodedFormulaBinaryOperationRow M
      (rawFormulaShiftBinaryCode M kind)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      combinedBound
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) depth).
  {
    exists leftRootIndex, sourceLeft, targetLeft, depth,
      (raw_add M leftBound rightRootIndex),
      sourceRight, targetRight, depth.
    split; [exact hleftCombinedBelow |].
    split; [exact hleftRetained |].
    split; [reflexivity |].
    split; [exact hrightBelow |].
    split; [exact hrightRoot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      (RawCodedFormulaSubstitutionAtom M) replacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      combinedBound
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) depth).
  {
    destruct kind; cbn [rawFormulaShiftBinaryCode] in hbinary |- *.
    - right. right. left. exact hbinary.
    - right. right. right. left. exact hbinary.
    - right. right. right. right. left. exact hbinary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    combinedBound
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight)
    depth hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M combinedBound), combinedBound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split; [exact (raw_assignment_lt_self_succ M hPA combinedBound) |].
  split; assumption.
Qed.

Lemma raw_codedFormulaSubstitution_unary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      kind replacement depth sourceChild targetChild,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_succ M depth) sourceChild targetChild ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild).
Proof.
  intros M hPA kind replacement depth sourceChild targetChild hchild.
  unfold RawCodedFormulaOperation in hchild |- *.
  destruct hchild as
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex &
     hsourceDefined & htargetDefined & hdepthDefined &
     hrootBelow & hroot & hrows).
  assert (hunary : RawCodedFormulaUnaryOperationRow M
      (rawFormulaShiftUnaryCode M kind)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild) depth).
  {
    exists rootIndex, sourceChild, targetChild, (raw_succ M depth).
    split; [exact hrootBelow |]. split; [exact hroot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      (RawCodedFormulaSubstitutionAtom M) replacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild) depth).
  {
    destruct kind; cbn [rawFormulaShiftUnaryCode] in hunary |- *.
    - right. right. right. right. right. left. exact hunary.
    - right. right. right. right. right. right. exact hunary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild)
    depth hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split; [exact (raw_assignment_lt_self_succ M hPA bound) |].
  split; assumption.
Qed.

(** ------------------------------------------------------------------
    PA-definable strong induction over arbitrary formula codes. *)

Definition RawCodedFormulaSingleSubstitutionTotalBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    RawCodedFormulaAtomicallyAdequate M input ->
    forall replacement assignmentCode assignmentStep : M,
      RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
      forall depth : M,
        exists output : M,
          RawCodedFormulaOperation M
            (RawCodedFormulaSubstitutionAtom M)
            replacement depth input output.

Arguments RawCodedFormulaSingleSubstitutionTotalBelow M current
  : clear implicits.

(** Binder layout after the input is introduced:
    replacement, assignment code, assignment step, then depth and output.
    At the operation body these are variables 4,3,2,1,0; the input is 5. *)
Definition codedFormulaSingleSubstitutionTotalBelowTermAt
    (current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))
        (pAll (pAll (pAll
          (pImp
            (termSyntaxRealizableTermAt (tVar 2) (tVar 1) (tVar 0))
            (pAll (pEx
              (codedFormulaOperationTermAt
                codedFormulaSubstitutionAtomTermAt
                (tVar 4) (tVar 1) (tVar 5) (tVar 0)))))))))).

Lemma raw_singleSubstitutionTotality_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) = raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_sat_codedFormulaSingleSubstitutionTotalBelowTermAt_iff : forall
    (M : RawPAModel) e current,
  raw_formula_sat M e
    (codedFormulaSingleSubstitutionTotalBelowTermAt current) <->
  RawCodedFormulaSingleSubstitutionTotalBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedFormulaSingleSubstitutionTotalBelowTermAt,
    RawCodedFormulaSingleSubstitutionTotalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_termSyntaxRealizableTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff M _
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  setoid_rewrite raw_singleSubstitutionTotality_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaSingleSubstitutionTotalBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSingleSubstitutionTotalBelow M (raw_zero M).
Proof.
  intros M hPA input hinput _ replacement assignmentCode assignmentStep
    _ depth.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

Lemma raw_codedFormulaSingleSubstitutionTotalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M -> forall current,
  RawCodedFormulaSingleSubstitutionTotalBelow M current ->
  RawCodedFormulaSingleSubstitutionTotalBelow M (raw_succ M current).
Proof.
  intros M hPA hopening current hprefix input hinput hadequate
    replacement assignmentCode assignmentStep hreplacement depth.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hadequate replacement
      assignmentCode assignmentStep hreplacement depth).
  - destruct hadequate as
      (formulaCode & formulaStep & bound & rootIndex & hsyntax & hatomic).
    pose proof hsyntax as hsyntaxFull.
    destruct hsyntax as
      [hdefined [hrootBelow [hrootLookup hsyntaxRows]]].
    pose proof (hsyntaxRows rootIndex current hrootBelow hrootLookup)
      as hrootRow.
    destruct (raw_codedFormulaSyntaxTraversalRow_shape M
      formulaCode formulaStep rootIndex current hrootRow)
      as (shape & hcode & hshape).
    destruct shape as
      [sourceLeft sourceRight
      |
      | sourceLeft sourceRight
      | sourceLeft sourceRight
      | sourceLeft sourceRight
      | sourceChild
      | sourceChild].
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct (hatomic rootIndex
        (rawFormulaEqCode M sourceLeft sourceRight)
        sourceLeft sourceRight (raw_zero M) (raw_zero M)
        hrootBelow hrootLookup eq_refl
        (raw_codedZeroAssignment_defined_all M hPA
          (rawFormulaEqCode M sourceLeft sourceRight)))
        as [hleftSyntax hrightSyntax].
      destruct (raw_codedFormulaSubstitutionAtom_exists M hPA hopening
        replacement assignmentCode assignmentStep hreplacement
        depth sourceLeft (raw_zero M) (raw_zero M) hleftSyntax)
        as [targetLeft hleft].
      destruct (raw_codedFormulaSubstitutionAtom_exists M hPA hopening
        replacement assignmentCode assignmentStep hreplacement
        depth sourceRight (raw_zero M) (raw_zero M) hrightSyntax)
        as [targetRight hright].
      exists (rawFormulaEqCode M targetLeft targetRight).
      exact (raw_codedFormulaSubstitution_of_valid_tree M hPA replacement
        (RFSTEq M depth sourceLeft targetLeft sourceRight targetRight)
        (conj hleft hright)).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      exists (rawFormulaBotCode M).
      exact (raw_codedFormulaSubstitution_of_valid_tree M hPA replacement
        (RFSTBot M depth) I).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaImpCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaImpCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 2) sourceLeft sourceRight)
        hleftAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetLeft hleft].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 2) sourceLeft sourceRight)
        hrightAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetRight hright].
      exists (rawFormulaImpCode M targetLeft targetRight).
      exact (raw_codedFormulaSubstitution_binary_composition M hPA
        RFSBImp replacement depth sourceLeft targetLeft
        sourceRight targetRight hleft hright).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAndCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAndCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 3) sourceLeft sourceRight)
        hleftAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetLeft hleft].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 3) sourceLeft sourceRight)
        hrightAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetRight hright].
      exists (rawFormulaAndCode M targetLeft targetRight).
      exact (raw_codedFormulaSubstitution_binary_composition M hPA
        RFSBAnd replacement depth sourceLeft targetLeft
        sourceRight targetRight hleft hright).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaOrCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaOrCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 4) sourceLeft sourceRight)
        hleftAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetLeft hleft].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 4) sourceLeft sourceRight)
        hrightAdequate replacement assignmentCode assignmentStep
        hreplacement depth) as [targetRight hright].
      exists (rawFormulaOrCode M targetLeft targetRight).
      exact (raw_codedFormulaSubstitution_binary_composition M hPA
        RFSBOr replacement depth sourceLeft targetLeft
        sourceRight targetRight hleft hright).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as [childIndex [hchildIndex hchildLookup]].
      assert (hchildBound : rawLt M childIndex bound).
      { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
          hchildIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAllCode M sourceChild)
        hsyntaxFull hatomic childIndex sourceChild
        hchildBound hchildLookup) as hchildAdequate.
      destruct (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) sourceChild)
        hchildAdequate replacement assignmentCode assignmentStep
        hreplacement (raw_succ M depth)) as [targetChild hchild].
      exists (rawFormulaAllCode M targetChild).
      exact (raw_codedFormulaSubstitution_unary_composition M hPA
        RFSUAll replacement depth sourceChild targetChild hchild).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as [childIndex [hchildIndex hchildLookup]].
      assert (hchildBound : rawLt M childIndex bound).
      { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
          hchildIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaExCode M sourceChild)
        hsyntaxFull hatomic childIndex sourceChild
        hchildBound hchildLookup) as hchildAdequate.
      destruct (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) sourceChild)
        hchildAdequate replacement assignmentCode assignmentStep
        hreplacement (raw_succ M depth)) as [targetChild hchild].
      exists (rawFormulaExCode M targetChild).
      exact (raw_codedFormulaSubstitution_unary_composition M hPA
        RFSUEx replacement depth sourceChild targetChild hchild).
Qed.

Theorem raw_codedFormulaSingleSubstitutionTotalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M ->
  forall current,
    RawCodedFormulaSingleSubstitutionTotalBelow M current.
Proof.
  intros M hPA hopening.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaSingleSubstitutionTotalBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTotalBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedFormulaSingleSubstitutionTotalBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaSingleSubstitutionTotalBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTotalBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaSingleSubstitutionTotalBelow_succ
        M hPA hopening current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaSingleSubstitutionTotalBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Arbitrary-depth operation totality is useful below binders and is the
    stronger internal statement from which root single substitution follows. *)
Theorem raw_codedFormulaSubstitutionAt_exists_of_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M -> forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  forall depth,
    exists target,
      RawCodedFormulaOperation M
        (RawCodedFormulaSubstitutionAtom M)
        replacement depth source target.
Proof.
  intros M hPA hopening source hadequate replacement
    assignmentCode assignmentStep hreplacement depth.
  pose proof (raw_codedFormulaSingleSubstitutionTotalBelow_all M hPA
    hopening (raw_succ M source)) as hall.
  exact (hall source (raw_assignment_lt_self_succ M hPA source)
    hadequate replacement assignmentCode assignmentStep
    hreplacement depth).
Qed.

(** Exact public endpoint.  Both codes may be nonstandard carrier elements;
    no conclusion identifies the output with an external quotation. *)
Corollary raw_codedFormulaSingleSubstitution_exists_of_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningTotal M -> forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement assignmentCode assignmentStep,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  exists target,
    RawCodedFormulaSingleSubstitution M replacement source target.
Proof.
  intros M hPA hopening source hadequate replacement
    assignmentCode assignmentStep hreplacement.
  exact (raw_codedFormulaSubstitutionAt_exists_of_atomically_adequate
    M hPA hopening source hadequate replacement
    assignmentCode assignmentStep hreplacement (raw_zero M)).
Qed.

End PABoundedRawCodedFormulaSingleSubstitutionTotality.
