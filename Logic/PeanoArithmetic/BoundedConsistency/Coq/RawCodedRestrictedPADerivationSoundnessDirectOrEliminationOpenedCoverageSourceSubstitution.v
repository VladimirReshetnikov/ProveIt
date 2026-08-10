(** Direct structural quotation and substitution for the fixed Or-E source. *)

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
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceEmbedding.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceSubstitution.

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
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceEmbedding.

Lemma rawDirect_orEliminationOpenedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula.
Proof.
  intros M inputs. unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_orEliminationOpenedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_orEliminationOpenedCoverageSourceBody_agreement in hopen.
  rewrite coqRestrictedPADirectOrEliminationOpenedCoverageSource_open in hopen.
  exact hopen.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceSubstitution.
