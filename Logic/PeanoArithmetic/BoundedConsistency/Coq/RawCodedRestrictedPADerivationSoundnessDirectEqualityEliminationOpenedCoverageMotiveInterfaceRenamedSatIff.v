(**
  Semantic view of the renamed complete Eq-E motive-child interface.

  Renaming by [S] accounts for the common formula-coverage witness opened by
  the synchronized source.  The resulting child proof is [#2], its witness
  context is [#8], and its source-instance conclusion is [#1].
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedProofAtomicAdequacy
  RawCodedFixedLevelTruthTotality
  RawCodedProofFormulaCoverage
  RawCodedProofRules
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedCarrierRestrictedProofReroot
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesBelowOneSatIff
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveInterfaceShape
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedSatIff
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointSatIff
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleSatIff.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveInterfaceRenamedSatIff.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationOpenedCoverageSourceTemplateValidityChildShapesBelowOneSatIff.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveInterfaceShape.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveRestrictedSatIff.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveEndpointSatIff.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveAdmissibleSatIff.

(** A named proposition keeps ParentData and the final law assembly from
    repeating this long, but exact, shifted conjunction. *)
Definition RawCoqRestrictedPAEqualityEliminationMotiveChildInterface
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop :=
  rawLt M (variables 2) (variables 13) /\
  RawCarrierRestrictedProofAt M (fun index => variables (S index))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2) /\
  RawProofRuleValid M (variables 2) (variables 8) (variables 1) /\
  RawCodedFormulaAtomicallyAdequate M (variables 1) /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) (variables 1) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 1) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 2) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.

Arguments RawCoqRestrictedPAEqualityEliminationMotiveChildInterface
  M variables parameters : clear implicits.

Lemma raw_eqE_motive_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate)
  <->
  RawCoqRestrictedPAEqualityEliminationMotiveChildInterface
    M variables parameters.
Proof.
  intros M variables parameters predicates.
  rewrite rawTemplateFormulaSat_rename.
  rewrite coqRestrictedPADirectEqE_motive_child_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite raw_exE_child_below_one_sat_iff,
    raw_eqE_motive_child_restricted_sat_iff,
    raw_eqE_motive_child_endpoint_sat_iff,
    raw_eqE_motive_child_admissible_sat_iff.
  unfold RawCoqRestrictedPAEqualityEliminationMotiveChildInterface.
  cbn. tauto.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveInterfaceRenamedSatIff.
