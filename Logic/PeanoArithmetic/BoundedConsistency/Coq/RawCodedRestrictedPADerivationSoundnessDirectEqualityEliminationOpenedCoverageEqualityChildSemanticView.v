(**
  Semantic view of the Eq-E equality child.

  Its proof, context, and conclusion occupy exactly the same template
  positions as the already-checked Or-E disjunction child.  The reflexive
  bridge below makes that definitional reuse explicit and avoids a second
  expensive family of shape certificates.
*)

From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSharedShapesDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildSemanticView
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildSemanticView.

Import PAHierarchyReduction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageSharedShapesDefinitions.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationOpenedCoverageDisjunctionChildSemanticView.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageDefinitions.

Lemma coqRestrictedPADirectEqE_equality_child_matches_or_disjunction :
  coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate =
  coqRestrictedPADirectOrEliminationChildInterfaceTemplate
    CoqOrEliminationDisjunctionChild.
Proof. reflexivity. Qed.

Definition RawCoqRestrictedPAEqualityEliminationEqualityChildInterface
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop :=
  RawCoqRestrictedPAOrEliminationChildInterface
    CoqOrEliminationDisjunctionChild M variables parameters.

Arguments RawCoqRestrictedPAEqualityEliminationEqualityChildInterface
  M variables parameters : clear implicits.

Lemma raw_eqE_equality_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectEqualityEliminationEqualityChildInterfaceTemplate)
  <->
  RawCoqRestrictedPAEqualityEliminationEqualityChildInterface
    M variables parameters.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectEqE_equality_child_matches_or_disjunction.
  unfold RawCoqRestrictedPAEqualityEliminationEqualityChildInterface.
  apply raw_orElimination_disjunction_child_interface_renamed_sat_iff.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationOpenedCoverageEqualityChildSemanticView.
