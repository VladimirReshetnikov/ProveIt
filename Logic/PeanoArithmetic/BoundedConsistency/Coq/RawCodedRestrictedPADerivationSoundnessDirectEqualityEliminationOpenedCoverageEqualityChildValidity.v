(** One independently checked recursive descent for Eq-E's equality child. *)

From Stdlib Require Import List.

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildValidity.

Import ListNotations.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData.

(** Descend through the tag-16 constructor at its first recursive endpoint.
    Keeping this descent in its own module prevents the motive-child semantic
    view from being unfolded while the kernel checks this proof. *)
Theorem raw_equalityElimination_equality_child_interface_of_parent_data :
    forall (M : RawPAModel), RawPASatisfies M -> forall variables parameters,
  RawCoqRestrictedPAEqualityEliminationOpenedParentData
    M variables parameters ->
  RawCoqRestrictedPAEqualityEliminationEqualityChildInterface
    M variables parameters.
Proof.
  intros M hPA variables parameters hparent.
  destruct hparent as
    [hrestricted hatomic hformulaCoverage hruleCoverage hassignmentCoverage
      hcode hconstructor hentry hequalityEndpoint hmotiveEndpoint].
  destruct (raw_recursive_constructor_child_interface_at_endpoint_context
    M hPA (rawEqualityEliminationOpenedShiftedVariables variables)
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8) (variables 7)
    (variables 6) (variables 5) (raw_zero M)
    (variables 3) (variables 2) (raw_zero M)
    [rawNumeralValue M 16; variables 8; variables 7; variables 6;
      variables 5; variables 3; variables 2]
    [variables 3; variables 2]
    (variables 3) (variables 8) (variables 4)
    (variables 10) (variables 9)
    hrestricted hatomic hformulaCoverage hruleCoverage
    hconstructor hentry hcode (ltac:(left; reflexivity))
    hequalityEndpoint hassignmentCoverage)
    as [hbelow [hchildRestricted [hchildAtomic [hchildFormulaCoverage
      [hchildRuleCoverage [hchildRuleValid [hconclusionAtomic
        [hconclusionDefined hconclusionBounded]]]]]]]].
  repeat split; try assumption.
  - exists (variables 0). exact hchildFormulaCoverage.
  - exists (variables 0). split; assumption.
Qed.

Corollary raw_equalityElimination_equality_child_sat_of_parent_data :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  RawCoqRestrictedPAEqualityEliminationOpenedParentData
    M variables parameters ->
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate).
Proof.
  intros M hPA variables parameters predicates hparent.
  apply (proj2
    (raw_eqE_equality_child_interface_renamed_sat_iff
      M variables parameters predicates)).
  exact
    (raw_equalityElimination_equality_child_interface_of_parent_data
      M hPA variables parameters hparent).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildValidity.
