(**
  Pointwise core of synchronized native PA axiom-context truth.

  The three existential table packages have already been opened by the
  companion witness-shape module.  This file adds the one arithmetic helper
  which is genuinely absent from those packages--universal definedness of a
  beta assignment--and constructs the remaining pointwise proof entirely in
  transparent template syntax.

  Two uses of the helper are intentionally visible.  The first obtains the
  witness-table entry at the current live index; the second supplies the
  zero-assignment definedness premise of the selected axiom-soundness field.
  Context membership is transported separately to the boundedness and
  atomic-adequacy tables using the already explicit twelve-argument PA
  transfer theorem.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedContextMembershipTransferPA
  RawCodedTemplateSyntax
  RawCodedTemplateRepeatedUniversalElimination
  RawCodedTemplateNestedExistentialElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise.

Import PA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedContextMembershipTransferPA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.

(** ------------------------------------------------------------------
    The strengthened deep context and the two pointwise binders. *)

Definition coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate
    : TemplateFormula :=
  embedPAFormula codedAssignmentUniversalDefinednessFormula.

(** All original assumptions have crossed nineteen existential binders.  The
    closed helper crosses the same binders and is retained at the tail. *)
Definition coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    : TemplateContext :=
  coqRestrictedPANativeAxiomRowsDeepContext ++
    [rawCoqTemplateRenameN 19
      coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate].

Definition coqRestrictedPANativeAxiomRowsPointwiseIndexBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseIndexBodyTemplate with
  | tfImp live _ => live
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAfterLiveTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseIndexBodyTemplate with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseFormulaBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseAfterLiveTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseFormulaBodyTemplate with
  | tfImp lookup _ => lookup
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseFormulaBodyTemplate with
  | tfImp _ leaf => leaf
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwise_shape :
  coqRestrictedPANativeAxiomRowsPointwiseTemplate =
  tfAll
    (tfImp coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate
      (tfAll
        (tfImp coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate
          coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate))).
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAfterIndexContext
    : TemplateContext :=
  templateContextShift
    coqRestrictedPANativeAxiomRowsPointwiseDeepContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseAfterLiveContext
    : TemplateContext :=
  coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate ::
    coqRestrictedPANativeAxiomRowsPointwiseAfterIndexContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseBeforeLookupContext
    : TemplateContext :=
  templateContextShift
    coqRestrictedPANativeAxiomRowsPointwiseAfterLiveContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    : TemplateContext :=
  coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate ::
    coqRestrictedPANativeAxiomRowsPointwiseBeforeLookupContext.

(** Small endpoint lemmas used repeatedly below. *)
Lemma coqRestrictedPANativeAxiomRows_templateRawDerives_andI : forall
    context left right leftRoot rightRoot,
  TemplateRawDerives context left leftRoot ->
  TemplateRawDerives context right rightRoot ->
  TemplateRawDerives context (tfAnd left right)
    (trpAndI context left right leftRoot rightRoot).
Proof.
  intros context left right leftRoot rightRoot
    [hlValid [hlContext hlConclusion]]
    [hrValid [hrContext hrConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqRestrictedPANativeAxiomRows_templateRawDerives_impE : forall
    context antecedent consequent implicationRoot antecedentRoot,
  TemplateRawDerives context (tfImp antecedent consequent) implicationRoot ->
  TemplateRawDerives context antecedent antecedentRoot ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent implicationRoot antecedentRoot).
Proof.
  intros context antecedent consequent implicationRoot antecedentRoot
    [hiValid [hiContext hiConclusion]]
    [haValid [haContext haConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqRestrictedPANativeAxiomRows_templateRawDerives_allI : forall
    context body child,
  TemplateRawDerives (templateContextShift context) body child ->
  TemplateRawDerives context (tfAll body)
    (trpAllI context body child).
Proof.
  intros context body child [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqRestrictedPANativeAxiomRows_templateRawDerives_exI : forall
    context body witness child,
  TemplateRawDerives context (templateFormulaOpen witness body) child ->
  TemplateRawDerives context (tfEx body)
    (trpExI context body witness child).
Proof.
  intros context body witness child [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

(** ------------------------------------------------------------------
    Assumption projections at the innermost pointwise leaf. *)

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsFinalWitnessBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsFinalBoundedBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsFinalAdequateBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseFieldTemplate :=
  rawCoqTemplateRenameN 21
    coqRestrictedPANativeAxiomRowsFieldTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate :=
  rawCoqTemplateRenameN 21
    coqRestrictedPANativeAxiomRowsTransferSourceTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate :=
  rawCoqTemplateRenameN 21
    coqRestrictedPANativeAxiomRowsDefinedUniversalTemplate.

Lemma coqRestrictedPANativeAxiomRows_pointwise_witness_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_bounded_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_adequate_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_field_in :
  In coqRestrictedPANativeAxiomRowsPointwiseFieldTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_transfer_in :
  In coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_defined_universal_in :
  In coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseHeadLookupRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseLiveRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate).

Lemma coqRestrictedPANativeAxiomRows_pointwise_shifted_live_in :
  In (templateFormulaRename S
        coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext.
Proof. vm_compute. tauto. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseFieldRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseFieldTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseTransferRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate.

(** The three package bodies keep their conjunction spines after the two
    pointwise binders. *)
Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsWitnessTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsAxiomTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsWitnessedRowsTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsBoundedTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsBoundedRowsTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsAdequateTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsTemplate :=
  rawCoqTemplateRenameN 2
    coqRestrictedPANativeAxiomRowsAdequateRowsTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseWitnessBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRestRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRestRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRestRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot.

Lemma coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_witness_body_in.
Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_bounded_body_in.
Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_adequate_body_in.
Qed.

Theorem coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot,
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRestRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  apply coqRestrictedPADirect_templateRawDerives_andE2.
  rewrite <- coqRestrictedPANativeAxiomRowsPointwiseWitnessBody_shape.
  exact coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyRoot_derives.
Qed.

Theorem coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPANativeAxiomRowsPointwiseAdequateBody_shape.
  exact coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyRoot_derives.
Qed.

Theorem coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot.
  apply coqRestrictedPADirect_templateRawDerives_andE1.
  rewrite <- coqRestrictedPANativeAxiomRowsPointwiseBoundedBody_shape.
  exact coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyRoot_derives.
Qed.

(** ------------------------------------------------------------------
    Package the current axiom-table lookup as traversal-relative
    membership, then transport it to the other two table packages. *)

Lemma coqRestrictedPANativeAxiomRowsPointwiseHeadLookupRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupRoot.
Proof.
  apply templateRawDerives_assumption. left. reflexivity.
Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseLiveRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseLiveRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_shifted_live_in.
Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberWithTablesTermAt
      (tVar 0) (tVar 20) (tVar 13) (tVar 12)).

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAxiomMembership_shape :
  coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate =
  tfEx coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAxiomMembership_open :
  templateFormulaOpen (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipBodyTemplate =
  tfAnd
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate.
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipPairRoot :=
  trpAndI coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLiveRoot
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot :=
  trpExI coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipBodyTemplate
    (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipPairRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot.
Proof.
  rewrite coqRestrictedPANativeAxiomRowsPointwiseAxiomMembership_shape.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_exI.
  rewrite coqRestrictedPANativeAxiomRowsPointwiseAxiomMembership_open.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipPairRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_andI.
  - exact coqRestrictedPANativeAxiomRowsPointwiseLiveRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseHeadLookupRoot_derives.
Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberWithTablesTermAt
      (tVar 0) (tVar 6) (tVar 3) (tVar 2)).

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberWithTablesTermAt
      (tVar 0) (tVar 11) (tVar 8) (tVar 7)).

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferReplacements
    : list TemplateTerm :=
  [ttVar 21; ttVar 0;
   ttVar 6; ttVar 5; ttVar 4; ttVar 3; ttVar 2;
   ttVar 20; ttVar 15; ttVar 14; ttVar 13; ttVar 12].

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferReplacements
    : list TemplateTerm :=
  [ttVar 21; ttVar 0;
   ttVar 11; ttVar 10; ttVar 9; ttVar 8; ttVar 7;
   ttVar 20; ttVar 15; ttVar 14; ttVar 13; ttVar 12].

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferInstance :=
  rawCoqTemplateAllEListResult
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferInstance :=
  rawCoqTemplateAllEListResult
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateTransfer_ready :
  RawCoqTemplateAllEListReady
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate.
Proof. vm_compute. exact I. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedTransfer_ready :
  RawCoqTemplateAllEListReady
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate.
Proof. vm_compute. exact I. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateTransfer_shape :
  coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferInstance =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
    (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
        coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate)).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedTransfer_shape :
  coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferInstance =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
    (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
        coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate)).
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferRoot :=
  rawCoqTemplateAllEListRoot
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate
    coqRestrictedPANativeAxiomRowsPointwiseTransferRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferRoot :=
  rawCoqTemplateAllEListRoot
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferReplacements
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate
    coqRestrictedPANativeAxiomRowsPointwiseTransferRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate
    (trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
      coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
        coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate)
      (trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
        coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate
        (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
          (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
            coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate))
        coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferRoot
        coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot)
      coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot)
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate
    (trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
      coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
      (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
        coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate)
      (trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
        coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate
        (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate
          (tfImp coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipTemplate
            coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate))
        coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferRoot
        coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot)
      coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot)
    coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot.

Lemma coqRestrictedPANativeAxiomRowsPointwiseTransferRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseTransferTemplate
    coqRestrictedPANativeAxiomRowsPointwiseTransferRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_transfer_in.
Qed.

Theorem coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
  - apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
    + apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
      * rewrite <- coqRestrictedPANativeAxiomRowsPointwiseAdequateTransfer_shape.
        unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateTransferRoot.
        apply rawCoqTemplateAllEListRoot_derives.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseAdequateTransfer_ready.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseTransferRoot_derives.
      * exact coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalRoot_derives.
    + exact coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot_derives.
Qed.

Theorem coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
  - apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
    + apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
      * rewrite <- coqRestrictedPANativeAxiomRowsPointwiseBoundedTransfer_shape.
        unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedTransferRoot.
        apply rawCoqTemplateAllEListRoot_derives.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseBoundedTransfer_ready.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseTransferRoot_derives.
      * exact coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalRoot_derives.
    + exact coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseAxiomMembershipRoot_derives.
Qed.

(** ------------------------------------------------------------------
    Consume transported atomic-adequacy membership. *)

Definition coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate :=
  coqRestrictedPANativeAxiomRowsAtomicTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext :=
  coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody ::
    templateContextShift coqRestrictedPANativeAxiomRowsPointwiseLeafContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive :=
  match coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody with
  | tfAnd live _ => live
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup :=
  match coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody with
  | tfAnd _ lookup => lookup
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateMembership_shape :
  coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipTemplate =
  tfEx
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive
      coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup).
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseAdequateBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateTraversal :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseAdequateTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRows :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateTraversal
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRows.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_shifted_adequate_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody
    coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext.
Proof. vm_compute. tauto. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsIndexBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRows with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterIndex :=
  templateFormulaOpen (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsIndexBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterLive :=
  match coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterIndex with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsFormulaBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterLive with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterFormula :=
  templateFormulaOpen (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsFormulaBody.

Lemma coqRestrictedPANativeAxiomRowsPointwiseAdequateRows_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRows =
  tfAll coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsIndexBody /\
  coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterIndex =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsFormulaBody) /\
  coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterFormula =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate).
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLiveRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookupRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateTraversal
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRows
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtIndexRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsIndexBody
    (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRowsRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterLiveRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLive
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsFormulaBody)
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtIndexRoot
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtFormulaRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsFormulaBody
    (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAtomicBodyRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseAdequateIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookup
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtFormulaRoot
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookupRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot :=
  trpExE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipBody
    coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot
    coqRestrictedPANativeAxiomRowsPointwiseAtomicBodyRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot.
  rewrite coqRestrictedPANativeAxiomRowsPointwiseAdequateMembership_shape
    in coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot_derives.
  apply templateRawDerives_exE.
  - exact coqRestrictedPANativeAxiomRowsPointwiseAdequateMembershipRoot_derives.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseAtomicBodyRoot.
    destruct coqRestrictedPANativeAxiomRowsPointwiseAdequateRows_shape
      as [hrowsShape [hindexShape hformulaShape]].
    rewrite hformulaShape.
    apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtFormulaRoot.
      apply templateRawDerives_allE.
      rewrite hindexShape.
      unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAfterLiveRoot.
      apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateRowsAtIndexRoot.
        apply templateRawDerives_allE.
        rewrite <- hrowsShape.
        unfold coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateRowsRoot.
        apply coqRestrictedPADirect_templateRawDerives_andE2.
        rewrite <-
          coqRestrictedPANativeAxiomRowsPointwiseShiftedAdequateBody_shape.
        apply templateRawDerives_assumption.
        exact
          coqRestrictedPANativeAxiomRows_pointwise_shifted_adequate_body_in.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLiveRoot.
        apply coqRestrictedPADirect_templateRawDerives_andE1.
        apply templateRawDerives_assumption. left. reflexivity.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseAdequateMemberLookupRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** The boundedness package has the same traversal/membership shape. *)
Definition coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate :=
  coqRestrictedPANativeAxiomRowsDomainTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext :=
  coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody ::
    templateContextShift coqRestrictedPANativeAxiomRowsPointwiseLeafContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive :=
  match coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody with
  | tfAnd live _ => live
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup :=
  match coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody with
  | tfAnd _ lookup => lookup
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedMembership_shape :
  coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipTemplate =
  tfEx
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive
      coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup).
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseBoundedBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedTraversal :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseBoundedTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRows :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedTraversal
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRows.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_shifted_bounded_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody
    coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext.
Proof. vm_compute. tauto. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsIndexBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRows with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterIndex :=
  templateFormulaOpen (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsIndexBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterLive :=
  match coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterIndex with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsFormulaBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterLive with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterFormula :=
  templateFormulaOpen (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsFormulaBody.

Lemma coqRestrictedPANativeAxiomRowsPointwiseBoundedRows_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRows =
  tfAll coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsIndexBody /\
  coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterIndex =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsFormulaBody) /\
  coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterFormula =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate).
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLiveRoot :=
  trpAndE1 coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookupRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedTraversal
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRows
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtIndexRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsIndexBody
    (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRowsRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterLiveRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLive
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsFormulaBody)
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtIndexRoot
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtFormulaRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsFormulaBody
    (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseDomainBodyRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseBoundedIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookup
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtFormulaRoot
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookupRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseDomainRoot :=
  trpExE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipBody
    coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate
    coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot
    coqRestrictedPANativeAxiomRowsPointwiseDomainBodyRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseDomainRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDomainRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseDomainRoot.
  rewrite coqRestrictedPANativeAxiomRowsPointwiseBoundedMembership_shape
    in coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot_derives.
  apply templateRawDerives_exE.
  - exact coqRestrictedPANativeAxiomRowsPointwiseBoundedMembershipRoot_derives.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseDomainBodyRoot.
    destruct coqRestrictedPANativeAxiomRowsPointwiseBoundedRows_shape
      as [hrowsShape [hindexShape hformulaShape]].
    rewrite hformulaShape.
    apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtFormulaRoot.
      apply templateRawDerives_allE.
      rewrite hindexShape.
      unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAfterLiveRoot.
      apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedRowsAtIndexRoot.
        apply templateRawDerives_allE.
        rewrite <- hrowsShape.
        unfold coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedRowsRoot.
        apply coqRestrictedPADirect_templateRawDerives_andE2.
        rewrite <-
          coqRestrictedPANativeAxiomRowsPointwiseShiftedBoundedBody_shape.
        apply templateRawDerives_assumption.
        exact
          coqRestrictedPANativeAxiomRows_pointwise_shifted_bounded_body_in.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLiveRoot.
        apply coqRestrictedPADirect_templateRawDerives_andE1.
        apply templateRawDerives_assumption. left. reflexivity.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseBoundedMemberLookupRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Obtain the synchronized witness-table entry and prove PA-axiom
    recognition for the selected context formula. *)

Definition coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate :=
  coqRestrictedPANativeAxiomRowsRecognitionTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPANativeAxiomRows_pointwise_defined_universal_in.
Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedReplacements
    : list TemplateTerm :=
  [ttVar 17; ttVar 16; ttVar 20].

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedTemplate :=
  rawCoqTemplateAllEListResult
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseWitnessDefined_ready :
  RawCoqTemplateAllEListReady
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate.
Proof. vm_compute. exact I. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedIndexBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndex :=
  templateFormulaOpen (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedIndexBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExists :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndex with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExists with
  | tfEx body => body
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwiseWitnessDefined_shape :
  coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedTemplate =
  tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedIndexBody /\
  coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndex =
  tfImp
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    (tfEx coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody).
Proof. vm_compute. split; reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedRoot :=
  rawCoqTemplateAllEListRoot
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndexRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedIndexBody
    (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)
    (tfEx coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndexRoot
    coqRestrictedPANativeAxiomRowsPointwiseLiveRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    (tfEx coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot.
Proof.
  destruct coqRestrictedPANativeAxiomRowsPointwiseWitnessDefined_shape
    as [hdefinedShape hindexShape].
  unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot.
  rewrite <- hindexShape.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedAtIndexRoot.
    apply templateRawDerives_allE.
    rewrite <- hdefinedShape.
    unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessDefinedRoot.
    apply rawCoqTemplateAllEListRoot_derives.
    + exact coqRestrictedPANativeAxiomRowsPointwiseWitnessDefined_ready.
    + exact
        coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseLiveRoot_derives.
Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext :=
  coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody ::
    templateContextShift coqRestrictedPANativeAxiomRowsPointwiseLeafContext.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseWitnessBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessTraversal :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseWitnessTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedAxiomTraversal :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseAxiomTraversalTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows :=
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseWitnessedRowsTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody =
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessTraversal
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseShiftedAxiomTraversal
      coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRows_pointwise_shifted_witness_body_in :
  In coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody
    coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext.
Proof. vm_compute. tauto. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsIndexBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterIndex :=
  templateFormulaOpen (ttVar 2)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsIndexBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLive :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterIndex with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsWitnessBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLive with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterWitness :=
  templateFormulaOpen (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsWitnessBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLookup :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterWitness with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAxiomBody :=
  match coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLookup with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterAxiom :=
  templateFormulaOpen (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAxiomBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedRecognitionBody :=
  match templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Lemma coqRestrictedPANativeAxiomRowsPointwiseWitnessRows_shape :
  coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows =
  tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsIndexBody /\
  coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterIndex =
  tfImp
    (templateFormulaRename S
      (templateFormulaRename S
        coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate))
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsWitnessBody) /\
  coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterWitness =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAxiomBody) /\
  coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterAxiom =
  tfImp
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate)
    (templateFormulaOpen (ttVar 0)
      coqRestrictedPANativeAxiomRowsPointwiseShiftedRecognitionBody) /\
  templateFormulaRename S
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate =
  tfEx coqRestrictedPANativeAxiomRowsPointwiseShiftedRecognitionBody.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedLiveRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    (templateFormulaRename S
      (templateFormulaRename S
        coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate)).

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedHeadLookupRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate).

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBodyRoot :=
  trpAss coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRestRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessTraversal
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseShiftedAxiomTraversal
      coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows)
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRowsRoot :=
  trpAndE2 coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedAxiomTraversal
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessedRows
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRestRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtIndexRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsIndexBody
    (ttVar 2)
    coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRowsRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLiveRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    (templateFormulaRename S
      (templateFormulaRename S
        coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate))
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsWitnessBody)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtIndexRoot
    coqRestrictedPANativeAxiomRowsPointwiseShiftedLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtWitnessRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsWitnessBody
    (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLiveRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLookupRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody
    (tfAll coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAxiomBody)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtWitnessRoot
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBodyRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtAxiomRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAxiomBody
    (ttVar 1)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLookupRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseWitnessRelationRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    (templateFormulaRename S
      coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate)
    (templateFormulaOpen (ttVar 0)
      coqRestrictedPANativeAxiomRowsPointwiseShiftedRecognitionBody)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtAxiomRoot
    coqRestrictedPANativeAxiomRowsPointwiseShiftedHeadLookupRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseRecognitionBodyRoot :=
  trpExI coqRestrictedPANativeAxiomRowsPointwiseWitnessValueContext
    coqRestrictedPANativeAxiomRowsPointwiseShiftedRecognitionBody
    (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseWitnessRelationRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot :=
  trpExE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBody
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate
    coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionBodyRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot.
  apply templateRawDerives_exE.
  - exact
      coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupExistsRoot_derives.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseRecognitionBodyRoot.
    destruct coqRestrictedPANativeAxiomRowsPointwiseWitnessRows_shape
      as [hrows [hindex [hwitness [haxiom hrecognition]]]].
    rewrite hrecognition.
    apply coqRestrictedPANativeAxiomRows_templateRawDerives_exI.
    unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRelationRoot.
    rewrite haxiom.
    apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtAxiomRoot.
      apply templateRawDerives_allE.
      rewrite hwitness.
      unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLookupRoot.
      apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtWitnessRoot.
        apply templateRawDerives_allE.
        rewrite hindex.
        unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAfterLiveRoot.
        apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
        -- unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessRowsAtIndexRoot.
           apply templateRawDerives_allE.
           rewrite <- hrows.
           unfold
             coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRowsRoot,
             coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessRestRoot.
           apply coqRestrictedPADirect_templateRawDerives_andE2.
           apply coqRestrictedPADirect_templateRawDerives_andE2.
           rewrite <-
             coqRestrictedPANativeAxiomRowsPointwiseShiftedWitnessBody_shape.
           apply templateRawDerives_assumption.
           exact
             coqRestrictedPANativeAxiomRows_pointwise_shifted_witness_body_in.
        -- unfold coqRestrictedPANativeAxiomRowsPointwiseShiftedLiveRoot.
           apply templateRawDerives_assumption.
           vm_compute. tauto.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseWitnessLookupBodyRoot.
        apply templateRawDerives_assumption. left. reflexivity.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseShiftedHeadLookupRoot.
      apply templateRawDerives_assumption.
      vm_compute. tauto.
Qed.

(** ------------------------------------------------------------------
    The second universal-definedness instance and final axiom field. *)

Definition coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate :=
  coqRestrictedPANativeAxiomRowsDefinedTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedReplacements
    : list TemplateTerm :=
  [ttZero; ttZero; ttVar 0].

Definition coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedInstance :=
  rawCoqTemplateAllEListResult
    coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate.

Lemma coqRestrictedPANativeAxiomRowsPointwiseZeroDefined_ready :
  RawCoqTemplateAllEListReady
    coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate.
Proof. vm_compute. exact I. Qed.

Lemma coqRestrictedPANativeAxiomRowsPointwiseZeroDefined_shape :
  coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedInstance =
  coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate.
Proof. vm_compute. reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot :=
  rawCoqTemplateAllEListRoot
    coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseZeroDefinedReplacements
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot.
Proof.
  rewrite <- coqRestrictedPANativeAxiomRowsPointwiseZeroDefined_shape.
  unfold coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot.
  apply rawCoqTemplateAllEListRoot_derives.
  - exact coqRestrictedPANativeAxiomRowsPointwiseZeroDefined_ready.
  - exact coqRestrictedPANativeAxiomRowsPointwiseDefinedUniversalRoot_derives.
Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseFieldBodyTemplate :=
  match coqRestrictedPANativeAxiomRowsPointwiseFieldTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPANativeAxiomRowsPointwiseFieldAtFormulaTemplate :=
  templateFormulaOpen (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseFieldBodyTemplate.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdmissibleTemplate :=
  tfAnd coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate
      (tfAnd coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate
        coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate)).

Lemma coqRestrictedPANativeAxiomRowsPointwiseField_shape :
  coqRestrictedPANativeAxiomRowsPointwiseFieldTemplate =
  tfAll coqRestrictedPANativeAxiomRowsPointwiseFieldBodyTemplate /\
  coqRestrictedPANativeAxiomRowsPointwiseFieldAtFormulaTemplate =
  tfImp coqRestrictedPANativeAxiomRowsPointwiseAdmissibleTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate.
Proof. vm_compute. split; reflexivity. Qed.

Definition coqRestrictedPANativeAxiomRowsPointwiseDefinedDomainRoot :=
  trpAndI coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate
    coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot
    coqRestrictedPANativeAxiomRowsPointwiseDomainRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAtomicRestRoot :=
  trpAndI coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate
      coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate)
    coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot
    coqRestrictedPANativeAxiomRowsPointwiseDefinedDomainRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseAdmissibleRoot :=
  trpAndI coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionTemplate
    (tfAnd coqRestrictedPANativeAxiomRowsPointwiseAtomicTemplate
      (tfAnd coqRestrictedPANativeAxiomRowsPointwiseDefinedTemplate
        coqRestrictedPANativeAxiomRowsPointwiseDomainTemplate))
    coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot
    coqRestrictedPANativeAxiomRowsPointwiseAtomicRestRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseFieldAtFormulaRoot :=
  trpAllE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseFieldBodyTemplate
    (ttVar 0)
    coqRestrictedPANativeAxiomRowsPointwiseFieldRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseLeafRoot :=
  trpImpE coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseAdmissibleTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate
    coqRestrictedPANativeAxiomRowsPointwiseFieldAtFormulaRoot
    coqRestrictedPANativeAxiomRowsPointwiseAdmissibleRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseLeafRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseLeafContext
    coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafRoot.
Proof.
  unfold coqRestrictedPANativeAxiomRowsPointwiseLeafRoot.
  destruct coqRestrictedPANativeAxiomRowsPointwiseField_shape
    as [hfield hinstance].
  rewrite <- hinstance.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_impE.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseFieldAtFormulaRoot.
    apply templateRawDerives_allE.
    rewrite <- hfield.
    unfold coqRestrictedPANativeAxiomRowsPointwiseFieldRoot.
    apply templateRawDerives_assumption.
    exact coqRestrictedPANativeAxiomRows_pointwise_field_in.
  - unfold coqRestrictedPANativeAxiomRowsPointwiseAdmissibleRoot,
      coqRestrictedPANativeAxiomRowsPointwiseAdmissibleTemplate.
    apply coqRestrictedPANativeAxiomRows_templateRawDerives_andI.
    + exact coqRestrictedPANativeAxiomRowsPointwiseRecognitionRoot_derives.
    + unfold coqRestrictedPANativeAxiomRowsPointwiseAtomicRestRoot.
      apply coqRestrictedPANativeAxiomRows_templateRawDerives_andI.
      * exact coqRestrictedPANativeAxiomRowsPointwiseAtomicRoot_derives.
      * unfold coqRestrictedPANativeAxiomRowsPointwiseDefinedDomainRoot.
        apply coqRestrictedPANativeAxiomRows_templateRawDerives_andI.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseDefinedRoot_derives.
        -- exact coqRestrictedPANativeAxiomRowsPointwiseDomainRoot_derives.
Qed.

(** ------------------------------------------------------------------
    Close the lookup implication and the two universal binders. *)

Definition coqRestrictedPANativeAxiomRowsPointwiseLookupImpRoot :=
  trpImpI coqRestrictedPANativeAxiomRowsPointwiseBeforeLookupContext
    coqRestrictedPANativeAxiomRowsPointwiseHeadLookupTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLeafRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseFormulaAllRoot :=
  trpAllI coqRestrictedPANativeAxiomRowsPointwiseAfterLiveContext
    coqRestrictedPANativeAxiomRowsPointwiseFormulaBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLookupImpRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseLiveImpRoot :=
  trpImpI coqRestrictedPANativeAxiomRowsPointwiseAfterIndexContext
    coqRestrictedPANativeAxiomRowsPointwiseLiveTemplate
    coqRestrictedPANativeAxiomRowsPointwiseAfterLiveTemplate
    coqRestrictedPANativeAxiomRowsPointwiseFormulaAllRoot.

Definition coqRestrictedPANativeAxiomRowsPointwiseRoot :=
  trpAllI coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsPointwiseIndexBodyTemplate
    coqRestrictedPANativeAxiomRowsPointwiseLiveImpRoot.

Theorem coqRestrictedPANativeAxiomRowsPointwiseRoot_derives :
  TemplateRawDerives coqRestrictedPANativeAxiomRowsPointwiseDeepContext
    coqRestrictedPANativeAxiomRowsPointwiseTemplate
    coqRestrictedPANativeAxiomRowsPointwiseRoot.
Proof.
  rewrite coqRestrictedPANativeAxiomRowsPointwise_shape.
  unfold coqRestrictedPANativeAxiomRowsPointwiseRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_allI.
  unfold coqRestrictedPANativeAxiomRowsPointwiseLiveImpRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  unfold coqRestrictedPANativeAxiomRowsPointwiseFormulaAllRoot.
  apply coqRestrictedPANativeAxiomRows_templateRawDerives_allI.
  unfold coqRestrictedPANativeAxiomRowsPointwiseLookupImpRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  exact coqRestrictedPANativeAxiomRowsPointwiseLeafRoot_derives.
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsPointwise.
