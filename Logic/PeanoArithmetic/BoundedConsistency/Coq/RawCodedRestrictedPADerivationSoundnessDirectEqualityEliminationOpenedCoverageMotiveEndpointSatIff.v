(** Semantic equation for the Eq-E motive child's displayed endpoint. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedProofRules
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointShape.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointSatIff.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointShape.

Lemma raw_eqE_motive_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectEqEMotiveChildEndpointTemplate <->
  RawProofRuleValid M (variables 1) (variables 7) (variables 0).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectEqE_motive_child_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA, raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointSatIff.
