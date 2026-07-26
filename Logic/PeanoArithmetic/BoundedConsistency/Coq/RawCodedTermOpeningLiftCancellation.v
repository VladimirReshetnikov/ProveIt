(**
  Cancellation between adjacent protected lifts.

  If [base] is shifted by [depth] and by [S depth], then opening the latter
  at any smaller cutoff [openingDepth] recovers the former.  The replacement
  used by that opening has itself been protected by [openingDepth].

  The apparently tempting proof by meta-level induction on [openingDepth]
  would be invalid for a nonstandard element of a raw PA model.  Instead we
  split [depth = openingDepth + gap], build the two intermediate shifts
  representedly, cancel one unit shift at cutoff zero, and transport that
  cancellation by the represented protection theorem.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedAdditionLaws RawCodedProofDescent
  RawCodedFormulaOperations
  RawCodedFormulaShiftTotality RawCodedTermShiftSyntaxRealization
  RawCodedTemplateTernaryApplication
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedFormulaSubstitutionAtomSourceSyntax
  RawCodedTermShiftProtection RawCodedTermShiftAmountComposition
  RawCodedTermOpeningProtection
  RawCodedTermOpeningUnitShiftCancellation.

Module PABoundedRawCodedTermOpeningLiftCancellation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermShiftAmountComposition.
Import PABoundedRawCodedTermOpeningProtection.
Import PABoundedRawCodedTermOpeningUnitShiftCancellation.

(** Represented shift totality, packaged for the existential syntax
    interface used by the application layer. *)
Lemma raw_codedTermShift_exists_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedTermSyntax M input -> forall cutoff amount,
  exists output, RawCodedTermShift M cutoff amount input output.
Proof.
  intros M hPA input
    (assignmentCode & assignmentStep & hsyntax) cutoff amount.
  exact (raw_codedTermShift_exists_of_syntax_realizable M hPA
    input assignmentCode assignmentStep hsyntax cutoff amount).
Qed.

(** Arithmetic normalization for the upper adjacent lift. *)
Lemma raw_codedTermOpeningLiftCancellation_succ_gap : forall
    (M : RawPAModel), RawPASatisfies M -> forall gap openingDepth depth,
  raw_add M openingDepth gap = depth ->
  raw_add M (raw_succ M gap) openingDepth = raw_succ M depth.
Proof.
  intros M hPA gap openingDepth depth hdepth.
  rewrite raw_succ_add_pair by exact hPA.
  rewrite (raw_add_comm M hPA gap openingDepth).
  now rewrite hdepth.
Qed.

(** The cancellation relation needed by opening/opening interchange.  Every
    constructed shift is represented by a genuine trace; functionality is
    used only to identify its endpoint with the endpoint supplied by the
    caller. *)
Theorem raw_codedTermOpening_lift_cancellation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      base depth openingDepth liftedAtDepth liftedAtSucc
      replacement liftedReplacement,
  rawLe M openingDepth depth ->
  RawCodedTermShift M (raw_zero M) depth base liftedAtDepth ->
  RawCodedTermShift M (raw_zero M) (raw_succ M depth)
    base liftedAtSucc ->
  RawCodedTermShift M (raw_zero M) openingDepth
    replacement liftedReplacement ->
  RawCodedTermOpening M openingDepth liftedReplacement
    liftedAtSucc liftedAtDepth.
Proof.
  intros M hPA base depth openingDepth liftedAtDepth liftedAtSucc
    replacement liftedReplacement hopeningDepth hdepthShift hsuccShift
    hreplacementShift.
  destruct hopeningDepth as [gap hdepth].

  pose proof (raw_codedTermShift_source_syntax M hPA
    (raw_zero M) depth base liftedAtDepth hdepthShift) as hbaseSyntax.
  destruct (raw_codedTermShift_exists_of_syntax M hPA base hbaseSyntax
    (raw_zero M) gap) as [gapLift hgapShift].

  pose proof (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) gap base gapLift hgapShift) as hgapLiftSyntax.
  destruct (raw_codedTermShift_exists_of_syntax M hPA gapLift
    hgapLiftSyntax (raw_zero M) (rawNumeralValue M 1))
    as [gapSuccLift hunitShift].

  pose proof (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) (rawNumeralValue M 1) gapLift gapSuccLift hunitShift)
    as hgapSuccLiftSyntax.
  destruct (raw_codedTermShift_exists_of_syntax M hPA gapLift
    hgapLiftSyntax (raw_zero M) openingDepth)
    as [depthCandidate hgapAtOpening].
  destruct (raw_codedTermShift_exists_of_syntax M hPA gapSuccLift
    hgapSuccLiftSyntax (raw_zero M) openingDepth)
    as [succCandidate hgapSuccAtOpening].

  assert (hdepthCandidate :
      RawCodedTermShift M (raw_zero M) depth base depthCandidate).
  {
    pose proof (raw_codedTermShift_amount_composition M hPA
      (raw_zero M) gap openingDepth base gapLift depthCandidate
      hgapShift hgapAtOpening) as hcomposed.
    rewrite (raw_add_comm M hPA gap openingDepth) in hcomposed.
    now rewrite hdepth in hcomposed.
  }
  assert (hsuccCandidate :
      RawCodedTermShift M (raw_zero M) (raw_succ M depth)
        base succCandidate).
  {
    pose proof (raw_codedTermShift_amount_composition M hPA
      (raw_zero M) gap (rawNumeralValue M 1)
      base gapLift gapSuccLift hgapShift hunitShift) as hgapThenUnit.
    rewrite raw_termShiftProtection_add_one in hgapThenUnit by exact hPA.
    pose proof (raw_codedTermShift_amount_composition M hPA
      (raw_zero M) (raw_succ M gap) openingDepth
      base gapSuccLift succCandidate hgapThenUnit hgapSuccAtOpening)
      as hcomposed.
    rewrite (raw_codedTermOpeningLiftCancellation_succ_gap
      M hPA gap openingDepth depth hdepth) in hcomposed.
    exact hcomposed.
  }

  assert (hdepthEndpoint : depthCandidate = liftedAtDepth).
  {
    exact (raw_codedTermShift_functional M hPA
      (raw_zero M) depth base depthCandidate liftedAtDepth
      hdepthCandidate hdepthShift).
  }
  assert (hsuccEndpoint : succCandidate = liftedAtSucc).
  {
    exact (raw_codedTermShift_functional M hPA
      (raw_zero M) (raw_succ M depth) base succCandidate liftedAtSucc
      hsuccCandidate hsuccShift).
  }

  pose proof (raw_codedTermOpening_zero_after_unit_shift M hPA
    replacement gapLift gapSuccLift hunitShift) as hcancelZero.
  pose proof (raw_codedTermOpening_protection M hPA
    (raw_zero M) openingDepth replacement liftedReplacement
    gapSuccLift succCandidate gapLift depthCandidate
    hreplacementShift hgapSuccAtOpening hcancelZero hgapAtOpening)
    as hprotected.
  rewrite raw_add_zero_left in hprotected by exact hPA.
  now rewrite hdepthEndpoint, hsuccEndpoint in hprotected.
Qed.

End PABoundedRawCodedTermOpeningLiftCancellation.
