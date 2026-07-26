(** Protective-shift stability of the concrete substitution atom. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedFormulaShiftTotality
  RawCodedTermOpeningTotality RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTermShiftProtection RawCodedTermShiftAmountComposition
  RawCodedTermOpeningProtection.

Module PABoundedRawCodedFormulaSubstitutionAtomProtective.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermShiftAmountComposition.
Import PABoundedRawCodedTermOpeningProtection.

(** The general carrier-valued protection law.  The intermediate lifted
    replacement is honest because it is the target of the shift stored in
    the original atom; no syntax premise on the displayed replacement is
    needed. *)
Theorem raw_codedFormulaSubstitutionAtom_protection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth protection input transformedInput
      liftedInput liftedTransformedInput,
  RawCodedFormulaSubstitutionAtom M
    replacement depth input transformedInput ->
  RawCodedTermShift M (raw_zero M) protection input liftedInput ->
  RawCodedTermShift M (raw_zero M) protection
    transformedInput liftedTransformedInput ->
  RawCodedFormulaSubstitutionAtom M replacement
    (raw_add M depth protection) liftedInput liftedTransformedInput.
Proof.
  intros M hPA replacement depth protection input transformedInput
    liftedInput liftedTransformedInput
    (depthReplacement & hdepthReplacement & hopening)
    hinputShift houtputShift.
  destruct (raw_codedTermShift_target_syntax M hPA
    (raw_zero M) depth replacement depthReplacement hdepthReplacement)
    as (assignmentCode & assignmentStep & hdepthReplacementSyntax).
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    depthReplacement assignmentCode assignmentStep
    hdepthReplacementSyntax (raw_zero M) protection)
    as (protectedReplacement & hprotectedReplacement).
  exists protectedReplacement. split.
  - exact (raw_codedTermShift_amount_composition M hPA
      (raw_zero M) depth protection replacement depthReplacement
      protectedReplacement hdepthReplacement hprotectedReplacement).
  - exact (raw_codedTermOpening_protection M hPA
      depth protection depthReplacement protectedReplacement
      input liftedInput transformedInput liftedTransformedInput
      hprotectedReplacement hinputShift hopening houtputShift).
Qed.

(** Exact unguarded record consumed by generic ternary assembly. *)
Theorem raw_codedFormulaSubstitutionAtom_protectiveShiftStable : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement,
  RawCodedFormulaOperationProtectiveShiftStable M
    (RawCodedFormulaSubstitutionAtom M) replacement.
Proof.
  intros M hPA replacement. constructor.
  - intros depth input transformedInput liftedInput
      liftedTransformedInput hatom hinput houtput.
    pose proof (raw_codedFormulaSubstitutionAtom_protection M hPA
      replacement depth (rawNumeralValue M 1)
      input transformedInput liftedInput liftedTransformedInput
      hatom hinput houtput) as hprotected.
    rewrite raw_termShiftProtection_add_one in hprotected by exact hPA.
    exact hprotected.
  - intros depth input transformedInput liftedInput
      liftedTransformedInput hatom hinput houtput.
    pose proof (raw_codedFormulaSubstitutionAtom_protection M hPA
      replacement depth (rawNumeralValue M 2)
      input transformedInput liftedInput liftedTransformedInput
      hatom hinput houtput) as hprotected.
    rewrite raw_termShiftProtection_add_two in hprotected by exact hPA.
    exact hprotected.
Qed.

End PABoundedRawCodedFormulaSubstitutionAtomProtective.
