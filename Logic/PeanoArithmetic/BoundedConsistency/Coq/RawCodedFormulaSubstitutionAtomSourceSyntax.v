(**
  Honest source syntax for represented term shifts and substitution atoms.

  [RawCodedTermShiftSyntaxRealization] constructs a characteristic support
  table for an arbitrary assignment column, then applies it to the target
  column of a shift trace.  The same construction applies to the source
  column.  This module supplies the symmetric structural argument and uses
  it to discharge the source-syntax interface required by guarded ternary
  opening.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedProofDescent RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedAssignmentTotality RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationRealization RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality RawCodedTermShiftSyntaxRealization
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosureOpeningInterchange.

Module PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.

(** The support-prefix construction is column-generic.  Applying it to the
    source assignment and reading the source halves of the shift rows gives
    a syntax certificate even for nonstandard trace bounds and term codes. *)
Theorem raw_codedTermShiftTrace_source_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  rawLt M input enclosing ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep enclosing ->
  RawTermSyntaxRealizable M input assignmentCode assignmentStep.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing
    (hsourceDefined & htargetDefined & hrootBelow & hrootLookup &
     hrows & hcutoff)
    hinputEnclosing hassignment.
  destruct (raw_termShiftTargetSupportPrefix_exists M hPA
    sourceCode sourceStep bound (raw_succ M input)) as
    (supportCode & supportStep & hsupport).
  destruct hsupport as [hsupportDefined hsupportExact].
  exists supportCode, supportStep.
  unfold RawTermSyntaxCertificateWithSupport.
  split.
  - split; [exact hsupportDefined |].
    intros code hcodeBound hsupported.
    pose proof (proj1 (hsupportExact code hcodeBound) hsupported)
      as hoccurrence.
    destruct hoccurrence as [index [hindexBound hsourceLookup]].
    destruct (htargetDefined index hindexBound)
      as [target htargetLookup].
    pose proof (hrows index code target hindexBound
      (conj hsourceLookup htargetLookup)) as hrow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in hrow.
    destruct hrow as
      [hvariable | [hzero | [hsucc | [hadd | hmul]]]].
    + destruct hvariable as
        (inputIndex & outputIndex & hinput & houtput & hshifted).
      exists inputIndex, (raw_zero M). left. exact hinput.
    + exists (raw_zero M), (raw_zero M). right; left.
      exact (proj1 hzero).
    + destruct hsucc as
        (childIndex & inputChild & outputChild &
         hchildIndex & hchildLookup & hinput & houtput).
      assert (hchildCode : rawLt M inputChild code).
      {
        rewrite hinput. exact (raw_termShiftSyntax_succ_child_lt
          M hPA inputChild).
      }
      assert (hchildBound : rawLt M inputChild (raw_succ M input)).
      {
        exact (raw_assignment_lt_trans M hPA
          inputChild code (raw_succ M input) hchildCode hcodeBound).
      }
      exists inputChild, (raw_zero M). right; right; left.
      split; [exact hinput |]. split.
      * apply (proj2 (hsupportExact inputChild hchildBound)).
        exists childIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             childIndex index bound hchildIndex hindexBound).
        -- exact (proj1 hchildLookup).
      * exact hchildCode.
    + destruct hadd as
        (leftIndex & inputLeft & outputLeft &
         rightIndex & inputRight & outputRight &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup &
         hinput & houtput).
      assert (hleftCode : rawLt M inputLeft code).
      {
        rewrite hinput. unfold rawTermAddCode.
        exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
      }
      assert (hrightCode : rawLt M inputRight code).
      {
        rewrite hinput. unfold rawTermAddCode.
        exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
      }
      assert (hleftBound : rawLt M inputLeft (raw_succ M input)).
      {
        exact (raw_assignment_lt_trans M hPA
          inputLeft code (raw_succ M input) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M inputRight (raw_succ M input)).
      {
        exact (raw_assignment_lt_trans M hPA
          inputRight code (raw_succ M input) hrightCode hcodeBound).
      }
      exists inputLeft, inputRight. right; right; right; left.
      split; [exact hinput |]. repeat split.
      * apply (proj2 (hsupportExact inputLeft hleftBound)).
        exists leftIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             leftIndex index bound hleftIndex hindexBound).
        -- exact (proj1 hleftLookup).
      * apply (proj2 (hsupportExact inputRight hrightBound)).
        exists rightIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             rightIndex index bound hrightIndex hindexBound).
        -- exact (proj1 hrightLookup).
      * exact hleftCode.
      * exact hrightCode.
    + destruct hmul as
        (leftIndex & inputLeft & outputLeft &
         rightIndex & inputRight & outputRight &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup &
         hinput & houtput).
      assert (hleftCode : rawLt M inputLeft code).
      {
        rewrite hinput. unfold rawTermMulCode.
        exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
      }
      assert (hrightCode : rawLt M inputRight code).
      {
        rewrite hinput. unfold rawTermMulCode.
        exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
      }
      assert (hleftBound : rawLt M inputLeft (raw_succ M input)).
      {
        exact (raw_assignment_lt_trans M hPA
          inputLeft code (raw_succ M input) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M inputRight (raw_succ M input)).
      {
        exact (raw_assignment_lt_trans M hPA
          inputRight code (raw_succ M input) hrightCode hcodeBound).
      }
      exists inputLeft, inputRight. right; right; right; right.
      split; [exact hinput |]. repeat split.
      * apply (proj2 (hsupportExact inputLeft hleftBound)).
        exists leftIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             leftIndex index bound hleftIndex hindexBound).
        -- exact (proj1 hleftLookup).
      * apply (proj2 (hsupportExact inputRight hrightBound)).
        exists rightIndex. split.
        -- exact (raw_assignment_lt_trans M hPA
             rightIndex index bound hrightIndex hindexBound).
        -- exact (proj1 hrightLookup).
      * exact hleftCode.
      * exact hrightCode.
  - split.
    + intros code hcodeBound hsupported index hvariable.
      apply hassignment.
      assert (hindexCode : rawLt M index code).
      {
        rewrite hvariable.
        exact (raw_termShiftSyntax_var_index_lt M hPA index).
      }
      destruct (raw_lt_succ_cases M hPA code input hcodeBound)
        as [hcodeInput | ->].
      * exact (raw_assignment_lt_trans M hPA index input enclosing
          (raw_assignment_lt_trans M hPA index code input
            hindexCode hcodeInput)
          hinputEnclosing).
      * exact (raw_assignment_lt_trans M hPA
          index input enclosing hindexCode hinputEnclosing).
    + apply (proj2 (hsupportExact input
        (raw_assignment_lt_self_succ M hPA input))).
      exists rootIndex. split; [exact hrootBelow |].
      exact (proj1 hrootLookup).
Qed.

Corollary raw_codedTermShift_source_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff amount input output assignmentCode assignmentStep enclosing,
  RawCodedTermShift M cutoff amount input output ->
  rawLt M input enclosing ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep enclosing ->
  RawTermSyntaxRealizable M input assignmentCode assignmentStep.
Proof.
  intros M hPA cutoff amount input output assignmentCode assignmentStep
    enclosing
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace) hinput hassignment.
  exact (raw_codedTermShiftTrace_source_syntax_realizable M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output assignmentCode assignmentStep enclosing
    htrace hinput hassignment).
Qed.

Corollary raw_codedTermShift_source_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output,
  RawCodedTermShift M cutoff amount input output ->
  RawCodedTermSyntax M input.
Proof.
  intros M hPA cutoff amount input output hshift.
  exists (raw_zero M), (raw_zero M).
  apply (raw_codedTermShift_source_syntax_realizable M hPA
    cutoff amount input output
    (raw_zero M) (raw_zero M) (raw_succ M input)).
  - exact hshift.
  - exact (raw_assignment_lt_self_succ M hPA input).
  - exact (raw_codedZeroAssignment_defined_all M hPA
      (raw_succ M input)).
Qed.

(** The first shift stored in a substitution atom has the displayed
    replacement as its source. *)
Theorem raw_codedFormulaSubstitutionAtom_source_syntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSubstitutionAtomSourceSyntax M.
Proof.
  intros M hPA replacement depth input output
    (liftedReplacement & hshift & hopening).
  exact (raw_codedTermShift_source_syntax M hPA
    (raw_zero M) depth replacement liftedReplacement hshift).
Qed.

End PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
