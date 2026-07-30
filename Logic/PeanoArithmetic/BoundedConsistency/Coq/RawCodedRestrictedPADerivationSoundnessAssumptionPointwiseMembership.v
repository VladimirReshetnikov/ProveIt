(**
  Final pointwise use in the direct Assumption branch.

  After both five-witness traversal packages have been opened and traversal
  transfer has changed public membership to the context-truth tables, one
  existential index remains.  This file builds the completely generic proof
  tree that opens that index, specializes the pointwise universal clause at
  the same index and formula, and applies its two implications.

  The surrounding context is arbitrary.  Only membership of the pointwise
  clause and transferred membership formula is required, so the constructor
  can be reused independently of the particular ten-witness context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedTemplateNestedExistentialElimination
  RawCodedTemplateRepeatedUniversalElimination
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.

Definition coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 10
    coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate.

Definition coqRestrictedPADirectAssumptionMembershipIndexContext
    (context : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate ::
    templateContextShift context.

Arguments coqRestrictedPADirectAssumptionMembershipIndexContext
  context : clear implicits.

(** Modus ponens at declarative template endpoints. *)
Lemma templateRawDerives_impE : forall
    context antecedent consequent implicationRoot antecedentRoot,
  TemplateRawDerives context (tfImp antecedent consequent) implicationRoot ->
  TemplateRawDerives context antecedent antecedentRoot ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent implicationRoot antecedentRoot).
Proof.
  intros context antecedent consequent implicationRoot antecedentRoot
    [himpValid [himpContext himpConclusion]]
    [hargValid [hargContext hargConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Definition coqRestrictedPADirectAssumptionFinalMembershipRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss context coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate.

Definition coqRestrictedPADirectAssumptionMembershipIndexBodyRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate.

Definition coqRestrictedPADirectAssumptionLiveIndexRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
    coqRestrictedPADirectAssumptionFinalHeadLookupTemplate
    (coqRestrictedPADirectAssumptionMembershipIndexBodyRoot context).

Definition coqRestrictedPADirectAssumptionHeadLookupRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
    coqRestrictedPADirectAssumptionFinalHeadLookupTemplate
    (coqRestrictedPADirectAssumptionMembershipIndexBodyRoot context).

Definition coqRestrictedPADirectAssumptionShiftedPointwiseRoot
    (context : TemplateContext) : TemplateRawProof :=
  trpAss (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate.

Definition coqRestrictedPADirectAssumptionPointwiseAfterIndexRoot
    (context : TemplateContext) (pointwiseRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpAllE (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalPointwiseIndexBodyTemplate
    (ttVar 0) pointwiseRoot.

Definition coqRestrictedPADirectAssumptionPointwiseAfterLiveRoot
    (context : TemplateContext) (pointwiseRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate
    (coqRestrictedPADirectAssumptionPointwiseAfterIndexRoot
      context pointwiseRoot)
    (coqRestrictedPADirectAssumptionLiveIndexRoot context).

Definition coqRestrictedPADirectAssumptionPointwiseAfterFormulaRoot
    (context : TemplateContext) (pointwiseRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpAllE (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalPointwiseFormulaBodyTemplate
    (ttVar 17)
    (coqRestrictedPADirectAssumptionPointwiseAfterLiveRoot
      context pointwiseRoot).

Definition coqRestrictedPADirectAssumptionPointwiseTruthRoot
    (context : TemplateContext) (pointwiseRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionFinalHeadLookupTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseTruthTemplate
    (coqRestrictedPADirectAssumptionPointwiseAfterFormulaRoot
      context pointwiseRoot)
    (coqRestrictedPADirectAssumptionHeadLookupRoot context).

Definition coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots
    (context : TemplateContext) (membershipRoot pointwiseRoot : TemplateRawProof)
    : TemplateRawProof :=
  trpExE context
    coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    membershipRoot
    (coqRestrictedPADirectAssumptionPointwiseTruthRoot
      context pointwiseRoot).

Arguments coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots
  context membershipRoot pointwiseRoot : clear implicits.

Definition coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot
    (context : TemplateContext) (membershipRoot : TemplateRawProof)
    : TemplateRawProof :=
  coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots context
    membershipRoot
    (coqRestrictedPADirectAssumptionShiftedPointwiseRoot context).

Arguments coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot
  context membershipRoot : clear implicits.

Definition coqRestrictedPADirectAssumptionPointwiseMembershipRoot
    (context : TemplateContext) : TemplateRawProof :=
  coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot context
    (coqRestrictedPADirectAssumptionFinalMembershipRoot context).

Lemma coqRestrictedPADirectAssumptionFinalNativeTruth_shift :
  templateFormulaRename S
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate =
  coqRestrictedPADirectAssumptionFinalPointwiseTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumption_shifted_pointwise_in : forall context,
  In coqRestrictedPADirectAssumptionFinalPointwiseTemplate context ->
  In coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate
    (coqRestrictedPADirectAssumptionMembershipIndexContext context).
Proof.
  intros context hin. right.
  unfold coqRestrictedPADirectAssumptionMembershipIndexContext,
    templateContextShift,
    coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate.
  apply in_map. exact hin.
Qed.

Theorem
    coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots_derives :
  forall context membershipRoot pointwiseRoot,
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate
    membershipRoot ->
  TemplateRawDerives
    (coqRestrictedPADirectAssumptionMembershipIndexContext context)
    coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate
    pointwiseRoot ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    (coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots
      context membershipRoot pointwiseRoot).
Proof.
  intros context membershipRoot pointwiseRoot hmembership hpointwise.
  unfold coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots.
  rewrite coqRestrictedPADirectAssumptionFinalLeftMembership_shape
    in hmembership.
  apply templateRawDerives_exE.
  - exact hmembership.
  - rewrite coqRestrictedPADirectAssumptionFinalNativeTruth_shift.
    unfold coqRestrictedPADirectAssumptionPointwiseTruthRoot.
    apply templateRawDerives_impE.
    + unfold coqRestrictedPADirectAssumptionPointwiseAfterFormulaRoot.
      rewrite <-
        coqRestrictedPADirectAssumptionFinalPointwiseAfterFormula_shape.
      apply templateRawDerives_allE.
      rewrite <-
        coqRestrictedPADirectAssumptionFinalPointwiseAfterLive_shape.
      unfold coqRestrictedPADirectAssumptionPointwiseAfterLiveRoot.
      apply templateRawDerives_impE.
      * unfold coqRestrictedPADirectAssumptionPointwiseAfterIndexRoot.
        rewrite <-
          coqRestrictedPADirectAssumptionFinalPointwiseAfterIndex_shape.
        apply templateRawDerives_allE.
        rewrite <-
          coqRestrictedPADirectAssumptionShiftedFinalPointwise_shape.
        exact hpointwise.
      * unfold coqRestrictedPADirectAssumptionLiveIndexRoot.
        apply coqRestrictedPADirect_templateRawDerives_andE1.
        apply templateRawDerives_assumption. left. reflexivity.
    + unfold coqRestrictedPADirectAssumptionHeadLookupRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      apply templateRawDerives_assumption. left. reflexivity.
Qed.

Corollary
    coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot_derives :
  forall context membershipRoot,
  In coqRestrictedPADirectAssumptionFinalPointwiseTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate
    membershipRoot ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    (coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot
      context membershipRoot).
Proof.
  intros context membershipRoot hpointwise hmembership.
  apply
    coqRestrictedPADirectAssumptionPointwiseMembershipFromRoots_derives.
  - exact hmembership.
  - apply templateRawDerives_assumption.
    exact
      (coqRestrictedPADirectAssumption_shifted_pointwise_in
        context hpointwise).
Qed.

Corollary coqRestrictedPADirectAssumptionPointwiseMembershipRoot_derives :
  forall context,
  In coqRestrictedPADirectAssumptionFinalPointwiseTemplate context ->
  In coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate context ->
  TemplateRawDerives context
    coqRestrictedPADirectAssumptionFinalNativeTruthTemplate
    (coqRestrictedPADirectAssumptionPointwiseMembershipRoot context).
Proof.
  intros context hpointwise hmembership.
  apply
    coqRestrictedPADirectAssumptionPointwiseMembershipFromRoot_derives;
    [exact hpointwise |].
  apply templateRawDerives_assumption. exact hmembership.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionPointwiseMembership.
