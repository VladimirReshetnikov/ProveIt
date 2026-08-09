(**
  Template-level validity of the fixed opened And-I coverage source body.

  This boundary performs the two substantial semantic transports: the PA
  embedding is identified with the abstracted compiler law, and abstraction
  is opened at the arbitrary level value.  Keeping this proof opaque lets the
  final raw-formula validity theorem reduce only its outer universal binder.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceEmbedding.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceTemplateValidity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceEmbedding.

(** The predicate environment is irrelevant because the abstracted source is
    a genuine PA formula; spelling it explicitly keeps this theorem aligned
    with [rawTemplateFormulaSat_embedPA]. *)
Theorem
    rawTemplateFormulaSat_coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBody :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (variables : nat -> M) level,
  rawTemplateFormulaSat M (scons M level variables)
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    (embedPAFormula
      coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula).
Proof.
  intros M hPA variables level.
  rewrite coqRestrictedPADirectAndIntroductionOpenedCoverageSource_embed.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate)).
  apply raw_coqRestrictedPADirectAndIntroductionOpenedCoverageLaw_valid.
  exact hPA.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceTemplateValidity.
