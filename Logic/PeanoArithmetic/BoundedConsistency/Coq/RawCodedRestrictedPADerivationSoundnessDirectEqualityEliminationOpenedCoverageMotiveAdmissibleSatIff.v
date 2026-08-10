(**
  Semantic equation for the Eq-E motive child's source-instance
  admissibility package.  The existential coverage witness is intentionally
  normalized in this isolated module because it is the largest component.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedProofAtomicAdequacy
  RawCodedFixedLevelTruthTotality
  RawCodedProofFormulaCoverage
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleShape.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleSatIff.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveShapeDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleShape.

Lemma raw_eqE_motive_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectEqEMotiveChildAdmissibleTemplate <->
  RawCodedFormulaAtomicallyAdequate M (variables 0) /\
  RawCodedAssignmentDefinedThrough M
    (variables 9) (variables 8) (variables 0) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 0) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 1) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 9) (variables 8) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectEqE_motive_child_admissible_shape.
  cbn [rawTemplateFormulaSat].
  repeat rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetFormulaQuantifierBoundedContext_seal_free].
  rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofFormulaCoverageTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  cbn [raw_term_eval scons]. tauto.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleSatIff.
