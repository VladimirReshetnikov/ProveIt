(** Raw-model validity and PA provability of the fixed opened Eq-E source. *)

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
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceTemplateValidity
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceEmbedding.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceProvability.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateEmbeddedUniversalValidity.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceTemplateValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceEmbedding.

Theorem raw_equalityElimination_openedCoverageSource_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula.
  apply (raw_formula_sat_all_of_embedded_template_validity M
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyFormula
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  intros inner level.
  rewrite coqRestrictedPADirectEqualityEliminationOpenedCoverageSource_embed.
  unfold
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M inner
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate)).
  apply raw_equalityElimination_openedCoverageLaw_valid. exact hPA.
Qed.

Theorem PA_proves_coqRestrictedPADirectEqualityEliminationOpenedCoverageSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (raw_equalityElimination_openedCoverageSource_valid
        M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectEqualityEliminationOpenedCoverageSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageSourceProvability.
