(** Direct structural quotation and substitution for the fixed source. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceEmbedding.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceSubstitution.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceEmbedding.

Lemma rawDirect_andIntroductionOpenedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula.
Proof.
  intros M inputs. unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_andIntroductionOpenedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_andIntroductionOpenedCoverageSourceBody_agreement
    in hopen.
  rewrite coqRestrictedPADirectAndIntroductionOpenedCoverageSource_open
    in hopen.
  exact hopen.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceSubstitution.
