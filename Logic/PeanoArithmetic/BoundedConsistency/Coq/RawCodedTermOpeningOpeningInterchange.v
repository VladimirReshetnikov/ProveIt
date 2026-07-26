(**
  Interchange of two represented capture-avoiding term openings.

  The outer opening acts one level deeper before the inner opening.  One
  explicit cancellation premise records what happens when the source is the
  variable at that outer cutoff; this is the only nonrecursive exceptional
  case.  A later concrete atom module derives that premise from the two
  stored lifts of its fixed replacement.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAdditionLaws
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedFormulaOperations
  RawCodedProofDescent RawCodedTermOpeningTotality
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTermOpeningShiftInterchange RawCodedTermOpeningProtection.

Module PABoundedRawCodedTermOpeningOpeningInterchange.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermOpeningShiftInterchange.
Import PABoundedRawCodedTermOpeningProtection.

Lemma raw_openingOpening_succ_lt_succ_elim : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M (raw_succ M left) (raw_succ M right) ->
  rawLt M left right.
Proof.
  intros M hPA left right [gap hgap].
  exists gap.
  rewrite raw_succ_add_pair in hgap by exact hPA.
  exact (raw_succ_injective_syntax M hPA _ _ hgap).
Qed.

Lemma raw_openingOpening_le_lt_trans : forall
    (M : RawPAModel), RawPASatisfies M -> forall left middle right,
  rawLe M left middle -> rawLt M middle right -> rawLt M left right.
Proof.
  intros M hPA left middle right [leftGap hleft] [rightGap hright].
  exists (raw_add M leftGap rightGap).
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_add_assoc by exact hPA.
  rewrite hleft.
  rewrite <- raw_add_succ by exact hPA.
  exact hright.
Qed.

(** The variable square.  All compound cases recurse uniformly; only a
    variable exactly at [S depth] uses [hcancellation]. *)
Lemma raw_codedTermOpening_opening_variable_interchange : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement inputIndex
      transformedInput output transformedOutput,
  rawLe M openingDepth depth ->
  RawCodedTermOpening M depth outerAtDepth
    replacement transformedReplacement ->
  RawCodedTermOpening M openingDepth transformedReplacement
    outerAtSucc outerAtDepth ->
  RawCodedTermOpening M (raw_succ M depth) outerAtSucc
    (rawTermVarCode M inputIndex) transformedInput ->
  RawCodedTermOpening M openingDepth replacement
    (rawTermVarCode M inputIndex) output ->
  RawCodedTermOpening M openingDepth transformedReplacement
    transformedInput transformedOutput ->
  RawCodedTermOpening M depth outerAtDepth output transformedOutput.
Proof.
  intros M hPA depth openingDepth outerAtDepth outerAtSucc
    replacement transformedReplacement inputIndex
    transformedInput output transformedOutput hdepth
    hreplacement hcancellation htop hleft hright.
  destruct (raw_codedTermOpening_variable_inversion M hPA
    openingDepth replacement inputIndex output hleft) as
    [[hinputBelow houtput] |
      [[hinputAt houtput] |
        (inputPredecessor & hinputSucc & hinputAbove & houtput)]].
  - assert (hinputDepth : rawLt M inputIndex depth).
    {
      exact (raw_lt_le_trans_pair M hPA
        inputIndex openingDepth depth hinputBelow hdepth).
    }
    assert (hinputSuccDepth : rawLt M inputIndex (raw_succ M depth)).
    {
      exact (raw_assignment_lt_trans M hPA inputIndex depth
        (raw_succ M depth) hinputDepth
        (raw_assignment_lt_self_succ M hPA depth)).
    }
    destruct (raw_codedTermOpening_variable_inversion M hPA
      (raw_succ M depth) outerAtSucc inputIndex transformedInput htop)
      as [htopLow | [htopEqual | htopHigh]].
    + destruct htopLow as [_ htransformedInput].
      subst transformedInput. subst output.
      destruct (raw_codedTermOpening_variable_inversion M hPA
        openingDepth transformedReplacement inputIndex transformedOutput
        hright) as
        [[_ htransformedOutput] |
          [[hrightAt _] | (rightPred & _ & hrightAbove & _)]].
      * subst transformedOutput.
        apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
        left. split; [exact hinputDepth | reflexivity].
      * subst inputIndex. exfalso.
        exact (raw_not_lt_self M hPA openingDepth hinputBelow).
      * exfalso. apply (raw_not_lt_self M hPA inputIndex).
        exact (raw_assignment_lt_trans M hPA inputIndex openingDepth
          inputIndex hinputBelow hrightAbove).
    + destruct htopEqual as [htopAt _].
      rewrite htopAt in hinputSuccDepth.
      exfalso. exact (raw_not_lt_self M hPA
        (raw_succ M depth) hinputSuccDepth).
    + destruct htopHigh as (topPred & _ & htopAbove & _).
      exfalso. apply (raw_not_lt_self M hPA inputIndex).
      exact (raw_assignment_lt_trans M hPA inputIndex
        (raw_succ M depth) inputIndex hinputSuccDepth htopAbove).
  - subst inputIndex. subst output.
    assert (hopeningSuccDepth :
        rawLt M openingDepth (raw_succ M depth)).
    { exact (raw_lt_succ_of_le M hPA openingDepth depth hdepth). }
    destruct (raw_codedTermOpening_variable_inversion M hPA
      (raw_succ M depth) outerAtSucc openingDepth transformedInput htop)
      as [htopLow | [htopEqual | htopHigh]].
    + destruct htopLow as [_ htransformedInput].
      subst transformedInput.
      destruct (raw_codedTermOpening_variable_inversion M hPA
        openingDepth transformedReplacement openingDepth transformedOutput
        hright) as
        [[hrightBelow _] |
          [[_ htransformedOutput] | (rightPred & _ & hrightAbove & _)]].
      * exfalso. exact (raw_not_lt_self M hPA
          openingDepth hrightBelow).
      * subst transformedOutput. exact hreplacement.
      * exfalso. exact (raw_not_lt_self M hPA
          openingDepth hrightAbove).
    + destruct htopEqual as [htopAt _].
      rewrite htopAt in hopeningSuccDepth.
      exfalso. exact (raw_not_lt_self M hPA
        (raw_succ M depth) hopeningSuccDepth).
    + destruct htopHigh as (topPred & _ & htopAbove & _).
      exfalso. apply (raw_not_lt_self M hPA openingDepth).
      exact (raw_assignment_lt_trans M hPA openingDepth
        (raw_succ M depth) openingDepth hopeningSuccDepth htopAbove).
  - subst inputIndex. subst output.
    destruct (raw_codedTermOpening_variable_inversion M hPA
      (raw_succ M depth) outerAtSucc
      (raw_succ M inputPredecessor) transformedInput htop) as
      [htopBelow | [htopAt | htopAbove]].
    + destruct htopBelow as [hinputSuccBelow htransformedInput].
      subst transformedInput.
      assert (hpredecessorDepth : rawLt M inputPredecessor depth).
      { exact (raw_openingOpening_succ_lt_succ_elim M hPA
          inputPredecessor depth hinputSuccBelow). }
      destruct (raw_codedTermOpening_variable_inversion M hPA
        openingDepth transformedReplacement
        (raw_succ M inputPredecessor) transformedOutput hright) as
        [[hrightBelow _] |
          [[hrightAt _] |
            (rightPred & hrightSucc & _ & htransformedOutput)]].
      * exfalso. apply (raw_not_lt_self M hPA
          (raw_succ M inputPredecessor)).
        exact (raw_assignment_lt_trans M hPA
          (raw_succ M inputPredecessor) openingDepth
          (raw_succ M inputPredecessor) hrightBelow hinputAbove).
      * rewrite hrightAt in hinputAbove.
        exfalso. exact (raw_not_lt_self M hPA
          openingDepth hinputAbove).
      * assert (hrightPred : rightPred = inputPredecessor).
        {
          symmetry. exact (raw_succ_injective_syntax M hPA _ _ hrightSucc).
        }
        subst rightPred. subst transformedOutput.
        apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
        left. split; [exact hpredecessorDepth | reflexivity].
    + destruct htopAt as [hinputAt htransformedInput].
      assert (hpredDepth : inputPredecessor = depth).
      {
        exact (raw_succ_injective_syntax M hPA _ _ hinputAt).
      }
      subst inputPredecessor. subst transformedInput.
      pose proof (raw_codedTermOpening_functional M hPA
        openingDepth transformedReplacement outerAtSucc
        outerAtDepth transformedOutput hcancellation hright)
        as htransformedOutput.
      subst transformedOutput.
      apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
      right; left. split; reflexivity.
    + destruct htopAbove as
        (topPredecessor & hinputTopSucc & hinputTopAbove &
         htransformedInput).
      assert (htopPredecessor : topPredecessor = inputPredecessor).
      {
        symmetry.
        exact (raw_succ_injective_syntax M hPA _ _ hinputTopSucc).
      }
      subst topPredecessor. subst transformedInput.
      assert (hdepthPredecessor : rawLt M depth inputPredecessor).
      {
        exact (raw_openingOpening_succ_lt_succ_elim M hPA
          depth inputPredecessor hinputTopAbove).
      }
      assert (hopeningPredecessor : rawLt M openingDepth inputPredecessor).
      {
        exact (raw_openingOpening_le_lt_trans M hPA openingDepth depth
          inputPredecessor hdepth hdepthPredecessor).
      }
      destruct (raw_codedTermOpening_variable_inversion M hPA
        openingDepth transformedReplacement inputPredecessor
        transformedOutput hright) as
        [[hrightBelow _] |
          [[hrightAt _] |
            (rightPred & hrightSucc & _ & htransformedOutput)]].
      * exfalso. apply (raw_not_lt_self M hPA inputPredecessor).
        exact (raw_assignment_lt_trans M hPA
          inputPredecessor openingDepth inputPredecessor
          hrightBelow hopeningPredecessor).
      * subst inputPredecessor. exfalso.
        exact (raw_not_lt_self M hPA openingDepth hopeningPredecessor).
      * subst transformedOutput.
        apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
        right; right. exists rightPred.
        split; [exact hrightSucc |].
        split; [exact hdepthPredecessor | reflexivity].
Qed.

End PABoundedRawCodedTermOpeningOpeningInterchange.
