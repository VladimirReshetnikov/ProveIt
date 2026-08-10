(** Assemble the three opaque child descents into the opened Or-E law. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildValidity.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawAssembly.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageParentData.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLeftChildValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageRightChildValidity.

Theorem raw_orElimination_openedCoverageLaw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPADirectOrEliminationOpenedCoverageLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  pose proof
    (raw_orElimination_openedParentData_of_semantic_premises
      M hPA variables parameters predicates hrestricted hatomic
      hruleCoverage hcommonCoverage hcase) as hparent.
  pose proof
    (raw_orElimination_disjunction_child_sat_of_parent_data
      M hPA variables parameters predicates hparent) as hdisjunction.
  pose proof
    (raw_orElimination_left_child_sat_of_parent_data
      M hPA variables parameters predicates hparent) as hleft.
  pose proof
    (raw_orElimination_right_child_sat_of_parent_data
      M hPA variables parameters predicates hparent) as hright.
  (** Reduce only the two outer conjunction constructors.  Rewriting the
      aggregate renaming theorem here asks the kernel to normalize all three
      large child interfaces at once; keeping the renamed leaves opaque makes
      this final assembly a small propositional certificate. *)
  change
    (rawTemplateFormulaSat M variables parameters predicates
        (templateFormulaRename S
          (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
            CoqOrEliminationDisjunctionChild)) /\
      (rawTemplateFormulaSat M variables parameters predicates
          (templateFormulaRename S
            (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
              CoqOrEliminationLeftBranchChild)) /\
        rawTemplateFormulaSat M variables parameters predicates
          (templateFormulaRename S
            (coqRestrictedPADirectOrEliminationChildInterfaceTemplate
              CoqOrEliminationRightBranchChild)))).
  exact (conj hdisjunction (conj hleft hright)).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageLawAssembly.
