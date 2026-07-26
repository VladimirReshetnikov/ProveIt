(**
  Constructor compositionality for arbitrary represented formula operations.

  The trace-concatenation library already contains all of the model-internal
  work needed to join two independently realized, possibly nonstandard
  operation traversals.  Its public constructor theorem was specialized to
  formula shift.  Proof-template opening uses the same traversal machinery
  with the substitution atom, so this module exposes the underlying generic
  theorem once and for all.

  The atom is required to have an object-language representation only because
  trace concatenation copies the second table by PA-definable induction.  Both
  existing atoms—term shift and capture-avoiding term substitution—satisfy
  this interface.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedProofDescent
  RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTraceConcatenation.

Module PABoundedRawCodedFormulaOperationCompositionality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.

(** Concatenate the two child traces, retain their roots, and append one
    binary-constructor row.  No property specific to shifting is used. *)
Theorem raw_codedFormulaOperation_binary_composition : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall
      (codedAtom : term -> term -> term -> term -> formula)
      (rawAtom : M -> M -> M -> M -> Prop),
  (forall e parameter depth input output,
    raw_formula_sat M e (codedAtom parameter depth input output) <->
    rawAtom (raw_term_eval M e parameter)
      (raw_term_eval M e depth)
      (raw_term_eval M e input) (raw_term_eval M e output)) ->
  forall parameter kind rootDepth
    sourceLeft targetLeft sourceRight targetRight,
  RawCodedFormulaOperation M rawAtom parameter rootDepth
    sourceLeft targetLeft ->
  RawCodedFormulaOperation M rawAtom parameter rootDepth
    sourceRight targetRight ->
  RawCodedFormulaOperation M rawAtom parameter rootDepth
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight).
Proof.
  intros M hPA codedAtom rawAtom hatom parameter kind rootDepth
    sourceLeft targetLeft sourceRight targetRight hleft hright.
  unfold RawCodedFormulaOperation in hleft, hright |- *.
  destruct hleft as
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftDepthCode & leftDepthStep & leftBound & leftRootIndex &
     hleftSourceDefined & hleftTargetDefined & hleftDepthDefined &
     hleftBelow & hleftRoot & hleftRows).
  destruct hright as
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightDepthCode & rightDepthStep & rightBound & rightRootIndex &
     hrightSourceDefined & hrightTargetDefined & hrightDepthDefined &
     hrightBelow & hrightRoot & hrightRows).
  set (hleftTrace := conj hleftSourceDefined
    (conj hleftTargetDefined
      (conj hleftDepthDefined
        (conj hleftBelow (conj hleftRoot hleftRows))))).
  set (hrightTrace := conj hrightSourceDefined
    (conj hrightTargetDefined
      (conj hrightDepthDefined
        (conj hrightBelow (conj hrightRoot hrightRows))))).
  destruct (raw_formulaOperationTraces_concatenate M hPA
    codedAtom rawAtom hatom parameter rootDepth
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftDepthCode leftDepthStep leftBound leftRootIndex
    sourceLeft targetLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex
    sourceRight targetRight hleftTrace hrightTrace)
    as (sourceCode & sourceStep & targetCode & targetStep &
        depthCode & depthStep & hcombined & hleftRetained).
  destruct hcombined as
    [hsourceDefined
      [htargetDefined
        [hdepthDefined
          [hrightCombinedBelow [hrightCombinedRoot hrows]]]]].
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
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) rootDepth).
  {
    exists leftRootIndex, sourceLeft, targetLeft, rootDepth,
      (raw_add M leftBound rightRootIndex),
      sourceRight, targetRight, rootDepth.
    split; [exact hleftCombinedBelow |].
    split; [exact hleftRetained |].
    split; [reflexivity |].
    split; [exact hrightCombinedBelow |].
    split; [exact hrightCombinedRoot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      rawAtom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      combinedBound
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) rootDepth).
  {
    destruct kind; cbn [rawFormulaShiftBinaryCode] in hbinary |- *.
    - right. right. left. exact hbinary.
    - right. right. right. left. exact hbinary.
    - right. right. right. right. left. exact hbinary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    rawAtom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    combinedBound
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight)
    rootDepth hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M combinedBound), combinedBound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split.
  - exact (raw_assignment_lt_self_succ M hPA combinedBound).
  - split; [exact hnewRoot | exact hnewRows].
Qed.

(** Append one quantified-constructor row above a child trace whose root
    depth has already been incremented. *)
Theorem raw_codedFormulaOperation_unary_composition : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (rawAtom : M -> M -> M -> M -> Prop)
      parameter kind rootDepth sourceChild targetChild,
  RawCodedFormulaOperation M rawAtom parameter (raw_succ M rootDepth)
    sourceChild targetChild ->
  RawCodedFormulaOperation M rawAtom parameter rootDepth
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild).
Proof.
  intros M hPA rawAtom parameter kind rootDepth
    sourceChild targetChild hchild.
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
      (rawFormulaShiftUnaryCode M kind targetChild) rootDepth).
  {
    exists rootIndex, sourceChild, targetChild, (raw_succ M rootDepth).
    split; [exact hrootBelow |]. split; [exact hroot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      rawAtom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild) rootDepth).
  {
    destruct kind; cbn [rawFormulaShiftUnaryCode] in hunary |- *.
    - right. right. right. right. right. left. exact hunary.
    - right. right. right. right. right. right. exact hunary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    rawAtom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild)
    rootDepth hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split.
  - exact (raw_assignment_lt_self_succ M hPA bound).
  - split; [exact hnewRoot | exact hnewRows].
Qed.

(** Public specialization for the capture-avoiding substitution atom. *)
Corollary raw_codedFormulaSubstitution_binary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement kind rootDepth
      sourceLeft targetLeft sourceRight targetRight,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement rootDepth sourceLeft targetLeft ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement rootDepth sourceRight targetRight ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement rootDepth
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight).
Proof.
  intros M hPA replacement kind rootDepth
    sourceLeft targetLeft sourceRight targetRight.
  eapply (raw_codedFormulaOperation_binary_composition M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)).
  exact (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M).
Qed.

Corollary raw_codedFormulaSubstitution_unary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement kind rootDepth sourceChild targetChild,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_succ M rootDepth) sourceChild targetChild ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement rootDepth
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild).
Proof.
  intros M hPA replacement kind rootDepth sourceChild targetChild hchild.
  eapply (raw_codedFormulaOperation_unary_composition M hPA
    (RawCodedFormulaSubstitutionAtom M)); exact hchild.
Qed.

End PABoundedRawCodedFormulaOperationCompositionality.
