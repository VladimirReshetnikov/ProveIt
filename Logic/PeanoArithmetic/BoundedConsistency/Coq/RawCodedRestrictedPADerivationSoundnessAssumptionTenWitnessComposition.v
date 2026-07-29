(**
  The two five-witness eliminations for the direct Assumption law.

  Public membership opens first, placing its traversal witnesses at the older
  five indices.  The expanded native context truth is inherited through those
  binders and then opens its own five witnesses.  At the resulting ten-witness
  context the final-witness compiler applies the closed PA transfer source and
  performs the last pointwise lookup.

  The only extra ambient assumption is that explicitly universal PA theorem.
  It is closed, hence all ten context shifts leave it definitionally fixed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateNestedExistentialElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance
  RawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes
  RawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership
  RawCodedRestrictedPADerivationSoundnessAssumptionFinalWitnessComposition.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionFinalWitnessComposition.

Definition coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAssumptionExpandedContextTruthTemplate
    (tfImp coqRestrictedPADirectAssumptionMembershipTemplate
      coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate).

Definition coqRestrictedPADirectAssumptionTransferSourceContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionTransferSourceTemplate :: tail.

Definition coqRestrictedPADirectAssumptionAfterContextIntroduction
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionExpandedContextTruthTemplate ::
    coqRestrictedPADirectAssumptionTransferSourceContext tail.

Definition coqRestrictedPADirectAssumptionTenWitnessReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionMembershipTemplate ::
    coqRestrictedPADirectAssumptionAfterContextIntroduction tail.

Definition coqRestrictedPADirectAssumptionMembershipDeepContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateNestedExContext 5
    coqRestrictedPADirectAssumptionMembershipBodyTemplate
    (coqRestrictedPADirectAssumptionAfterContextIntroduction tail).

Definition coqRestrictedPADirectAssumptionFinalWitnessContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateNestedExContext 4
    coqRestrictedPADirectAssumptionShiftedContextBodyTemplate
    (templateContextShift
      (coqRestrictedPADirectAssumptionMembershipDeepContext tail)).

Arguments coqRestrictedPADirectAssumptionTransferSourceContext
  tail : clear implicits.
Arguments coqRestrictedPADirectAssumptionAfterContextIntroduction
  tail : clear implicits.
Arguments coqRestrictedPADirectAssumptionTenWitnessReadyContext
  tail : clear implicits.
Arguments coqRestrictedPADirectAssumptionMembershipDeepContext
  tail : clear implicits.
Arguments coqRestrictedPADirectAssumptionFinalWitnessContext
  tail : clear implicits.

Definition coqRestrictedPADirectAssumptionFinalTransferSourceRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPADirectAssumptionFinalWitnessContext tail)
    coqRestrictedPADirectAssumptionTransferSourceTemplate.

Definition coqRestrictedPADirectAssumptionFinalWitnessRootAt
    (tail : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectAssumptionFinalWitnessRoot
    (coqRestrictedPADirectAssumptionFinalWitnessContext tail)
    (coqRestrictedPADirectAssumptionFinalTransferSourceRoot tail).

Definition coqRestrictedPADirectAssumptionShiftedContextTruthRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPADirectAssumptionMembershipDeepContext tail)
    coqRestrictedPADirectAssumptionShiftedContextTruthTemplate.

Definition coqRestrictedPADirectAssumptionContextWitnessesRoot
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateNestedExEliminationFromRoot 5
    coqRestrictedPADirectAssumptionShiftedContextBodyTemplate
    (rawCoqTemplateRenameN 5
      coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate)
    (coqRestrictedPADirectAssumptionMembershipDeepContext tail)
    (coqRestrictedPADirectAssumptionShiftedContextTruthRoot tail)
    (coqRestrictedPADirectAssumptionFinalWitnessRootAt tail).

Definition coqRestrictedPADirectAssumptionMembershipWitnessesRoot
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateNestedExEliminationRoot 5
    coqRestrictedPADirectAssumptionMembershipBodyTemplate
    coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate
    (coqRestrictedPADirectAssumptionAfterContextIntroduction tail)
    (coqRestrictedPADirectAssumptionContextWitnessesRoot tail).

Definition coqRestrictedPADirectAssumptionAfterMembershipRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectAssumptionAfterContextIntroduction tail)
    coqRestrictedPADirectAssumptionMembershipTemplate
    coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate
    (coqRestrictedPADirectAssumptionMembershipWitnessesRoot tail).

Definition coqRestrictedPADirectAssumptionTenWitnessRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectAssumptionTransferSourceContext tail)
    coqRestrictedPADirectAssumptionExpandedContextTruthTemplate
    (tfImp coqRestrictedPADirectAssumptionMembershipTemplate
      coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate)
    (coqRestrictedPADirectAssumptionAfterMembershipRoot tail).

Lemma coqRestrictedPADirectAssumptionNativeTruth_rename_five_twice :
  rawCoqTemplateRenameN 5
    (rawCoqTemplateRenameN 5
      coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate) =
  coqRestrictedPADirectAssumptionFinalNativeTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumption_shifted_context_truth_in : forall tail,
  In coqRestrictedPADirectAssumptionShiftedContextTruthTemplate
    (coqRestrictedPADirectAssumptionMembershipDeepContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectAssumptionMembershipDeepContext,
    coqRestrictedPADirectAssumptionShiftedContextTruthTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold coqRestrictedPADirectAssumptionAfterContextIntroduction.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumption_final_context_body_in : forall tail,
  In coqRestrictedPADirectAssumptionFinalContextBodyTemplate
    (coqRestrictedPADirectAssumptionFinalWitnessContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectAssumptionFinalWitnessContext.
  unfold coqRestrictedPADirectAssumptionFinalContextBodyTemplate.
  cbn [rawCoqTemplateNestedExContext].
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumption_final_membership_body_in : forall tail,
  In coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate
    (coqRestrictedPADirectAssumptionFinalWitnessContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectAssumptionFinalWitnessContext.
  unfold coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate.
  change (In
    (rawCoqTemplateRenameN 4
      (templateFormulaRename S
        coqRestrictedPADirectAssumptionMembershipBodyTemplate))
    (rawCoqTemplateNestedExContext 4
      coqRestrictedPADirectAssumptionShiftedContextBodyTemplate
      (templateContextShift
        (coqRestrictedPADirectAssumptionMembershipDeepContext tail)))).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  unfold coqRestrictedPADirectAssumptionMembershipDeepContext.
  cbn [rawCoqTemplateNestedExContext].
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAssumption_final_transfer_source_in : forall tail,
  In coqRestrictedPADirectAssumptionTransferSourceTemplate
    (coqRestrictedPADirectAssumptionFinalWitnessContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectAssumptionFinalWitnessContext.
  assert (hmembership : In
      coqRestrictedPADirectAssumptionTransferSourceTemplate
      (coqRestrictedPADirectAssumptionMembershipDeepContext tail)).
  {
    unfold coqRestrictedPADirectAssumptionMembershipDeepContext.
    replace coqRestrictedPADirectAssumptionTransferSourceTemplate with
      (rawCoqTemplateRenameN 5
        coqRestrictedPADirectAssumptionTransferSourceTemplate)
      by (vm_compute; reflexivity).
    apply raw_coqTemplateNestedExContext_inherited.
    unfold coqRestrictedPADirectAssumptionAfterContextIntroduction,
      coqRestrictedPADirectAssumptionTransferSourceContext.
    right. left. reflexivity.
  }
  replace coqRestrictedPADirectAssumptionTransferSourceTemplate with
    (rawCoqTemplateRenameN 4
      (templateFormulaRename S
        coqRestrictedPADirectAssumptionTransferSourceTemplate))
    by (vm_compute; reflexivity).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hmembership.
Qed.

Theorem coqRestrictedPADirectAssumptionTenWitnessRoot_derives : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectAssumptionTransferSourceContext tail)
    coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate
    (coqRestrictedPADirectAssumptionTenWitnessRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectAssumptionTenWitnessRoot,
    coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  unfold coqRestrictedPADirectAssumptionAfterMembershipRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  unfold coqRestrictedPADirectAssumptionMembershipWitnessesRoot.
  apply rawCoqTemplateNestedExEliminationRoot_derives.
  unfold coqRestrictedPADirectAssumptionContextWitnessesRoot.
  apply rawCoqTemplateNestedExEliminationFromRoot_derives.
  - rewrite <- coqRestrictedPADirectAssumptionShiftedContextTruth_shape.
    apply templateRawDerives_assumption.
    apply coqRestrictedPADirectAssumption_shifted_context_truth_in.
  - rewrite coqRestrictedPADirectAssumptionNativeTruth_rename_five_twice.
    apply coqRestrictedPADirectAssumptionFinalWitnessRoot_derives.
    + apply coqRestrictedPADirectAssumption_final_context_body_in.
    + apply coqRestrictedPADirectAssumption_final_membership_body_in.
    + apply templateRawDerives_assumption.
      apply coqRestrictedPADirectAssumption_final_transfer_source_in.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.
