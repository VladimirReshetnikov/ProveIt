(**
  Compose traversal transfer with the final pointwise Assumption lookup.

  This is the deepest ten-witness stage, but the theorem deliberately accepts
  an arbitrary context containing the two concrete traversal bodies.  The
  universally quantified PA transfer theorem may likewise be supplied by any
  proof root in that context.  Three applications of modus ponens turn its
  instantiated result into membership relative to the context-truth tables;
  the generic pointwise-membership compiler then returns native formula truth.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateRepeatedUniversalElimination
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance
  RawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes
  RawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionFinalWitnessComposition.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership.

Definition coqRestrictedPADirectAssumptionFinalContextBodyRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAssumptionFinalContextBodyTemplate.

Definition coqRestrictedPADirectAssumptionFinalLeftTraversalRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAssumptionLeftTraversalTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseTemplate
    (coqRestrictedPADirectAssumptionFinalContextBodyRoot context).

Definition coqRestrictedPADirectAssumptionFinalPointwiseRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAssumptionLeftTraversalTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseTemplate
    (coqRestrictedPADirectAssumptionFinalContextBodyRoot context).

Definition coqRestrictedPADirectAssumptionShiftedFinalContextBodyTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectAssumptionFinalContextBodyTemplate.

Lemma coqRestrictedPADirectAssumptionShiftedFinalContextBody_shape :
  coqRestrictedPADirectAssumptionShiftedFinalContextBodyTemplate =
  tfAnd
    (templateFormulaRename S
      coqRestrictedPADirectAssumptionLeftTraversalTemplate)
    coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPADirectAssumptionShiftedFinalContextBodyRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss
    (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionShiftedFinalContextBodyTemplate.

Definition coqRestrictedPADirectAssumptionShiftedFinalPointwiseRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2
    (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    (templateFormulaRename S
      coqRestrictedPADirectAssumptionLeftTraversalTemplate)
    coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate
    (coqRestrictedPADirectAssumptionShiftedFinalContextBodyRoot context).

Definition coqRestrictedPADirectAssumptionFinalMembershipBodyRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate.

Definition coqRestrictedPADirectAssumptionFinalRightTraversalRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 context
    coqRestrictedPADirectAssumptionRightTraversalTemplate
    coqRestrictedPADirectAssumptionFinalRightMembershipTemplate
    (coqRestrictedPADirectAssumptionFinalMembershipBodyRoot context).

Definition coqRestrictedPADirectAssumptionFinalRightMembershipRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 context
    coqRestrictedPADirectAssumptionRightTraversalTemplate
    coqRestrictedPADirectAssumptionFinalRightMembershipTemplate
    (coqRestrictedPADirectAssumptionFinalMembershipBodyRoot context).

Definition coqRestrictedPADirectAssumptionTransferInstanceRoot
    (context : TemplateContext) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  rawCoqTemplateAllEListRoot context
    coqRestrictedPADirectAssumptionTransferReplacements
    coqRestrictedPADirectAssumptionTransferSourceTemplate sourceRoot.

Definition coqRestrictedPADirectAssumptionTransferAfterLeftRoot
    (context : TemplateContext) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpImpE context
    coqRestrictedPADirectAssumptionLeftTraversalTemplate
    (tfImp coqRestrictedPADirectAssumptionRightTraversalTemplate
      (tfImp
        coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate
        coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate))
    (coqRestrictedPADirectAssumptionTransferInstanceRoot context sourceRoot)
    (coqRestrictedPADirectAssumptionFinalLeftTraversalRoot context).

Definition coqRestrictedPADirectAssumptionTransferAfterRightRoot
    (context : TemplateContext) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpImpE context
    coqRestrictedPADirectAssumptionRightTraversalTemplate
    (tfImp
      coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate
      coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate)
    (coqRestrictedPADirectAssumptionTransferAfterLeftRoot context sourceRoot)
    (coqRestrictedPADirectAssumptionFinalRightTraversalRoot context).

Definition coqRestrictedPADirectAssumptionTransferredMembershipRoot
    (context : TemplateContext) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpImpE context
    coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate
    coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate
    (coqRestrictedPADirectAssumptionTransferAfterRightRoot context sourceRoot)
    (coqRestrictedPADirectAssumptionFinalRightMembershipRoot context).

Definition coqRestrictedPADirectAssumptionFinalWitnessRoot
    (context : TemplateContext) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots context
    (coqRestrictedPADirectAssumptionTransferredMembershipRoot
      context sourceRoot)
    (coqRestrictedPADirectAssumptionShiftedFinalPointwiseRoot context).

Lemma coqRestrictedPADirectAssumption_shifted_context_body_in : forall
    context,
  In coqRestrictedPADirectAssumptionFinalContextBodyTemplate context ->
  In coqRestrictedPADirectAssumptionShiftedFinalContextBodyTemplate
    (coqRestrictedPADirectAssumptionMembershipIndexContext context).
Proof.
  intros context hin. right.
  unfold coqRestrictedPADirectAssumptionMembershipIndexContext,
    templateContextShift,
    coqRestrictedPADirectAssumptionShiftedFinalContextBodyTemplate.
  apply in_map. exact hin.
Qed.

Theorem coqRestrictedPADirectAssumptionFinalWitnessRoot_derives : forall
    context sourceRoot,
  In coqRestrictedPADirectAssumptionFinalContextBodyTemplate context ->
  In coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionTransferSourceTemplate sourceRoot ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    (coqRestrictedPADirectAssumptionFinalWitnessRoot context sourceRoot).
Proof.
  intros context sourceRoot hcontextBody hmembershipBody hsource.
  apply
    coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots_derives.
  - unfold coqRestrictedPADirectAssumptionTransferredMembershipRoot.
    rewrite <-
      coqRestrictedPADirectAssumptionFinalRightMembership_shape.
    apply templateRawDerives_impE.
    + unfold coqRestrictedPADirectAssumptionTransferAfterRightRoot.
      apply templateRawDerives_impE.
      * unfold coqRestrictedPADirectAssumptionTransferAfterLeftRoot.
        apply templateRawDerives_impE.
        -- unfold coqRestrictedPADirectAssumptionTransferInstanceRoot.
           rewrite <-
             coqRestrictedPADirectAssumptionTransferInstance_shape.
           apply rawCoqTemplateAllEListRoot_derives.
           ++ exact
                coqRestrictedPADirectAssumptionTransferReplacements_ready.
           ++ exact hsource.
        -- unfold coqRestrictedPADirectAssumptionFinalLeftTraversalRoot.
           rewrite coqRestrictedPADirectAssumptionFinalContextBody_shape
             in hcontextBody.
           apply coqRestrictedPADirect_templateRawDerives_andE1.
           apply templateRawDerives_assumption. exact hcontextBody.
      * unfold coqRestrictedPADirectAssumptionFinalRightTraversalRoot.
        rewrite coqRestrictedPADirectAssumptionFinalMembershipBody_shape
          in hmembershipBody.
        apply coqRestrictedPADirect_templateRawDerives_andE1.
        apply templateRawDerives_assumption. exact hmembershipBody.
    + unfold coqRestrictedPADirectAssumptionFinalRightMembershipRoot.
      rewrite coqRestrictedPADirectAssumptionFinalMembershipBody_shape
        in hmembershipBody.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      apply templateRawDerives_assumption. exact hmembershipBody.
  - unfold coqRestrictedPADirectAssumptionShiftedFinalPointwiseRoot.
    apply coqRestrictedPADirect_templateRawDerives_andE2.
    rewrite <-
      coqRestrictedPADirectAssumptionShiftedFinalContextBody_shape.
    apply templateRawDerives_assumption.
    exact
      (coqRestrictedPADirectAssumption_shifted_context_body_in
        context hcontextBody).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionFinalWitnessComposition.
