(**
  Concrete opening/opening algebra for the substitution atom.

  A substitution atom first protects its replacement by the current binder
  depth and then opens a coded term.  Consequently, composing two such atoms
  is not plain relational composition: the outer replacement itself must be
  opened, and the two independently constructed protected lifts must be
  related.  [raw_codedTermOpening_lift_cancellation] supplies exactly that
  missing relation.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedProofDescent RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization RawCodedFormulaShiftTotality
  RawCodedFormulaOperationTreeRealization
  RawCodedFormulaOperationCompositionality
  RawCodedTemplateTernaryApplication
  RawCodedFormulaSubstitutionAtomSourceSyntax
  RawCodedTermShiftAmountComposition RawCodedTermOpeningProtection
  RawCodedTermOpeningLiftCancellation
  RawCodedTermOpeningOpeningInterchangeInduction.

Module PABoundedRawCodedFormulaSubstitutionAtomInterchange.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
Import PABoundedRawCodedTermShiftAmountComposition.
Import PABoundedRawCodedTermOpeningProtection.
Import PABoundedRawCodedTermOpeningLiftCancellation.
Import PABoundedRawCodedTermOpeningOpeningInterchangeInduction.

(** Equality-leaf square for two nested substitution atoms.  All four
    existential protected replacements are retained explicitly until shift
    functionality and lift cancellation relate them. *)
Theorem raw_codedFormulaSubstitutionAtom_substitutionAtom_interchange :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      outerReplacement depth openingDepth
      replacement transformedReplacement
      input transformedInput output transformedOutput,
  RawCodedFormulaSubstitutionAtom M outerReplacement depth
    replacement transformedReplacement ->
  RawCodedFormulaSubstitutionAtom M outerReplacement
    (raw_succ M (raw_add M depth openingDepth))
    input transformedInput ->
  RawCodedFormulaSubstitutionAtom M replacement openingDepth
    input output ->
  RawCodedFormulaSubstitutionAtom M transformedReplacement openingDepth
    transformedInput transformedOutput ->
  RawCodedFormulaSubstitutionAtom M outerReplacement
    (raw_add M depth openingDepth) output transformedOutput.
Proof.
  intros M hPA outerReplacement depth openingDepth
    replacement transformedReplacement
    input transformedInput output transformedOutput
    (outerAtDepth & houterAtDepthShift & houterReplacementOpen)
    (outerAtSucc & houterAtSuccShift & htopOpen)
    (replacementAtOpening & hreplacementAtOpeningShift & hleftOpen)
    (transformedReplacementAtOpening &
      htransformedReplacementAtOpeningShift & hrightOpen).

  pose proof (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) depth outerReplacement outerAtDepth
    houterAtDepthShift) as houterAtDepthSyntax.
  destruct (raw_codedTermShift_exists_of_syntax M hPA outerAtDepth
    houterAtDepthSyntax (raw_zero M) openingDepth)
    as [outerAtCombined houterAtCombinedFromDepth].
  pose proof (raw_codedTermShift_amount_composition M hPA
    (raw_zero M) depth openingDepth
    outerReplacement outerAtDepth outerAtCombined
    houterAtDepthShift houterAtCombinedFromDepth)
    as houterAtCombinedShift.

  assert (hprotectedOuterOpening :
      RawCodedTermOpening M (raw_add M depth openingDepth)
        outerAtCombined replacementAtOpening
        transformedReplacementAtOpening).
  {
    exact (raw_codedTermOpening_protection M hPA
      depth openingDepth outerAtDepth outerAtCombined
      replacement replacementAtOpening
      transformedReplacement transformedReplacementAtOpening
      houterAtCombinedFromDepth hreplacementAtOpeningShift
      houterReplacementOpen htransformedReplacementAtOpeningShift).
  }

  assert (hopeningBelowCombined :
      rawLe M openingDepth (raw_add M depth openingDepth)).
  { exact (raw_proof_right_le_sum M hPA depth openingDepth). }

  assert (hliftCancellation :
      RawCodedTermOpening M openingDepth
        transformedReplacementAtOpening outerAtSucc outerAtCombined).
  {
    exact (raw_codedTermOpening_lift_cancellation M hPA
      outerReplacement (raw_add M depth openingDepth) openingDepth
      outerAtCombined outerAtSucc
      transformedReplacement transformedReplacementAtOpening
      hopeningBelowCombined houterAtCombinedShift houterAtSuccShift
      htransformedReplacementAtOpeningShift).
  }

  exists outerAtCombined. split; [exact houterAtCombinedShift |].
  exact (raw_codedTermOpening_opening_interchange_with_cancellation
    M hPA (raw_add M depth openingDepth) openingDepth
    outerAtCombined outerAtSucc
    replacementAtOpening transformedReplacementAtOpening
    input transformedInput output transformedOutput
    hopeningBelowCombined hprotectedOuterOpening hliftCancellation
    htopOpen hleftOpen hrightOpen).
Qed.

(** Small constructor wrappers used by the formula-level represented
    induction.  They keep the invariant proof independent of the finite beta
    realization details. *)
Lemma raw_codedFormulaSubstitution_eq_of_term_atoms : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth inputLeft outputLeft inputRight outputRight,
  RawCodedFormulaSubstitutionAtom M replacement depth
    inputLeft outputLeft ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    inputRight outputRight ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth
    (rawFormulaEqCode M inputLeft inputRight)
    (rawFormulaEqCode M outputLeft outputRight).
Proof.
  intros M hPA replacement depth inputLeft outputLeft
    inputRight outputRight hleft hright.
  pose proof (raw_codedFormulaSubstitution_of_valid_tree M hPA replacement
    (RFSTEq M depth inputLeft outputLeft inputRight outputRight)) as htree.
  cbn [RawFormulaSubstitutionTreeValid RawFormulaOperationTreeValid
    rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget] in htree.
  exact (htree (conj hleft hright)).
Qed.

Lemma raw_codedFormulaSubstitution_bot : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement depth,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA replacement depth.
  pose proof (raw_codedFormulaSubstitution_of_valid_tree M hPA replacement
    (RFSTBot M depth)) as htree.
  cbn [RawFormulaSubstitutionTreeValid RawFormulaOperationTreeValid
    rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget] in htree.
  exact (htree I).
Qed.

Lemma raw_codedFormulaSubstitution_binary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement kind depth
      inputLeft outputLeft inputRight outputRight,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth inputLeft outputLeft ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth inputRight outputRight ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth
    (rawFormulaShiftBinaryCode M kind inputLeft inputRight)
    (rawFormulaShiftBinaryCode M kind outputLeft outputRight).
Proof.
  intros M hPA replacement kind depth inputLeft outputLeft
    inputRight outputRight hleft hright.
  exact (raw_codedFormulaOperation_binary_composition M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    replacement kind depth inputLeft outputLeft inputRight outputRight
    hleft hright).
Qed.

Lemma raw_codedFormulaSubstitution_unary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement kind depth inputChild outputChild,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_succ M depth) inputChild outputChild ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth
    (rawFormulaShiftUnaryCode M kind inputChild)
    (rawFormulaShiftUnaryCode M kind outputChild).
Proof.
  intros M hPA replacement kind depth inputChild outputChild hchild.
  exact (raw_codedFormulaOperation_unary_composition M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement kind depth
    inputChild outputChild hchild).
Qed.

End PABoundedRawCodedFormulaSubstitutionAtomInterchange.
