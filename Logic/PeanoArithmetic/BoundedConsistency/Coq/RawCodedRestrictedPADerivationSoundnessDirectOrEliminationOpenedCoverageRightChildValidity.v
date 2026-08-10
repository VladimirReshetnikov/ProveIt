(** One independently checked recursive descent for Or-E's right branch. *)

From Stdlib Require Import List.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildValidity.

Import ListNotations.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData.

Theorem raw_orElimination_right_child_interface_of_parent_data : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables parameters,
  RawCoqRestrictedPAOrEliminationOpenedParentData M variables parameters ->
  RawCoqRestrictedPAOrEliminationChildInterface
    CoqOrEliminationRightBranchChild M variables parameters.
Proof.
  intros M hPA variables parameters hparent.
  destruct hparent as
    [hrestricted hatomic hformulaCoverage hruleCoverage hassignmentCoverage
      hcode hconstructor hentry hdisjunctionEndpoint
      hleftEndpoint hrightEndpoint].
  destruct (raw_recursive_constructor_child_interface_at_endpoint_context
    M hPA (rawOrEliminationOpenedShiftedVariables variables)
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8) (variables 7)
    (variables 6) (variables 5) (raw_zero M)
    (variables 3) (variables 2) (variables 1)
    [rawNumeralValue M 10; variables 8; variables 7; variables 6;
      variables 5; variables 3; variables 2; variables 1]
    [variables 3; variables 2; variables 1]
    (variables 1) (rawListNode M (variables 6) (variables 8))
    (variables 5) (variables 10) (variables 9)
    hrestricted hatomic hformulaCoverage hruleCoverage
    hconstructor hentry hcode (ltac:(right; right; left; reflexivity))
    hrightEndpoint hassignmentCoverage)
    as [hbelow [hchildRestricted [hchildAtomic [hchildFormulaCoverage
      [hchildRuleCoverage [hchildRuleValid [hconclusionAtomic
        [hconclusionDefined hconclusionBounded]]]]]]]].
  repeat split; try assumption.
  - exists (variables 0). exact hchildFormulaCoverage.
  - exists (variables 0). split; assumption.
Qed.

Corollary raw_orElimination_right_child_sat_of_parent_data : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  RawCoqRestrictedPAOrEliminationOpenedParentData M variables parameters ->
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
        CoqOrEliminationRightBranchChild)).
Proof.
  intros M hPA variables parameters predicates hparent.
  apply (proj2 (raw_orElimination_right_child_interface_renamed_sat_iff
    M variables parameters predicates)).
  exact (raw_orElimination_right_child_interface_of_parent_data
    M hPA variables parameters hparent).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildValidity.
