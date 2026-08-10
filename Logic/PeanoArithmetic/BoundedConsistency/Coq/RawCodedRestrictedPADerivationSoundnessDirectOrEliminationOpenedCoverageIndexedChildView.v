(** Indexed wrapper around the three concrete Or-E semantic views. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedChildView.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageValiditySupport.

Lemma raw_orElimination_child_interface_renamed_sat_iff : forall
    child (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      (coqRestrictedPADirectOrEliminationChildInterfaceTemplate child)) <->
  RawCoqRestrictedPAOrEliminationChildInterface
    child M variables parameters.
Proof.
  intros child M variables parameters predicates.
  destruct child.
  - apply raw_orElimination_disjunction_child_interface_renamed_sat_iff.
  - apply raw_orElimination_left_child_interface_renamed_sat_iff.
  - apply raw_orElimination_right_child_interface_renamed_sat_iff.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageIndexedChildView.
