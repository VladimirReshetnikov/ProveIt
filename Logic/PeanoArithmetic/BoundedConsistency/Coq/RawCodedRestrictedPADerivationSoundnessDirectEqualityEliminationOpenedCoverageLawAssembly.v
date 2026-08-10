(** Assemble the two opaque child descents into the opened Eq-E law. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildValidity
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveChildValidity.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageLawAssembly.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageValiditySupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageParentData.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageMotiveChildValidity.

Theorem raw_equalityElimination_openedCoverageLaw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPADirectEqualityEliminationOpenedCoverageLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  pose proof
    (raw_equalityElimination_openedParentData_of_semantic_premises
      M hPA variables parameters predicates hrestricted hatomic
      hruleCoverage hcommonCoverage hcase) as hparent.
  pose proof
    (raw_equalityElimination_equality_child_sat_of_parent_data
      M hPA variables parameters predicates hparent) as hequality.
  pose proof
    (raw_equalityElimination_motive_child_sat_of_parent_data
      M hPA variables parameters predicates hparent) as hmotive.
  (** Reduce only the outer conjunction.  An aggregate rename rewrite makes
      the kernel normalize both large child views simultaneously; retaining
      the two certified renamed leaves keeps this assembly propositional. *)
  change
    (rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate) /\
      rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          coqRestrictedPADirectEqualityEliminationMotiveChildInterfaceTemplate)).
  exact (conj hequality hmotive).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageLawAssembly.
