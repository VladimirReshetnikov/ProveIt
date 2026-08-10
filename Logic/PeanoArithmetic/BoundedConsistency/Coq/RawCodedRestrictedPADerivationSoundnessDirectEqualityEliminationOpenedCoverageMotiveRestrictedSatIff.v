(** Semantic equation for the Eq-E motive child's restricted proof. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedShape.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedSatIff.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedShape.

Lemma raw_eqE_motive_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectEqEMotiveChildRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 1) /\
  RawProofAtomicallyAdequate M (variables 1) /\
  RawProofHasFormulaCoverage M (variables 1) /\
  RawProofRuleCoverage M (variables 1).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectEqE_motive_child_restricted_shape.
  cbn [rawTemplateFormulaSat].
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].
  rewrite raw_carrierRestrictedProofContextSat_iff.
  repeat rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofAtomicallyAdequateTermAt_iff,
    raw_sat_proofHasFormulaCoverageTermAt_iff,
    raw_sat_proofRuleCoverageTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedSatIff.
