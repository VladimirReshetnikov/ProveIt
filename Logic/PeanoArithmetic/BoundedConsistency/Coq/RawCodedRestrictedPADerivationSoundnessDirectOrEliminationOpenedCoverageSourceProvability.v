(** Raw-model validity and PA provability of the fixed opened Or-E source. *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateEmbeddedUniversalValidity
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceEmbedding.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceProvability.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateEmbeddedUniversalValidity.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceEmbedding.

Theorem raw_orElimination_openedCoverageSource_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula.
  apply (raw_formula_sat_all_of_embedded_template_validity M
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyFormula
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  intros inner level.
  rewrite coqRestrictedPADirectOrEliminationOpenedCoverageSource_embed.
  unfold coqRestrictedPADirectOrEliminationOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M inner
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate)).
  apply raw_orElimination_openedCoverageLaw_valid. exact hPA.
Qed.

Theorem PA_proves_coqRestrictedPADirectOrEliminationOpenedCoverageSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (raw_orElimination_openedCoverageSource_valid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectOrEliminationOpenedCoverageSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSourceProvability.
