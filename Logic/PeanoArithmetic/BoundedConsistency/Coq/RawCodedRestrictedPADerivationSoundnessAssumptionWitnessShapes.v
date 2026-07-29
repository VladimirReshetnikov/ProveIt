(**
  Exact witness-package shapes for the direct Assumption proof.

  Native context truth has already been rerooted at a transparent template.
  Public membership is an ordinary embedded PA formula.  This file normalizes
  both formulas only far enough to expose their five existential witnesses and
  the two conjunction projections consumed by traversal transfer.

  Membership witnesses open first.  Context truth is consequently renamed by
  five binders before its witnesses open, while the already opened membership
  body is renamed by the five later context binders.  The final equalities tie
  both packages to the independently audited twelve-parameter transfer
  instance.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion
  RawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance
  RawCodedRestrictedPATemplateTernaryApplicationCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.

Definition coqRestrictedPADirectAssumptionExpandedContextTruthTemplate
    : TemplateFormula :=
  coqRestrictedPATemplateTernaryApplication
    coqRestrictedPADynamicContextPredicateTemplate
    (ttVar 8) (ttVar 9)
    coqRestrictedPADirectAssumptionWitnessContextTerm.

(** Total pattern projections; the audited shape lemmas show the fallback is
    unreachable for these concrete formulas. *)
Definition coqRestrictedPADirectAssumptionExpandedContextBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionExpandedContextTruthTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionMembershipBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionMembershipTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Lemma coqRestrictedPADirectAssumptionExpandedContextTruth_shape :
  coqRestrictedPADirectAssumptionExpandedContextTruthTemplate =
  rawCoqTemplateExN 5
    coqRestrictedPADirectAssumptionExpandedContextBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionMembership_shape :
  coqRestrictedPADirectAssumptionMembershipTemplate =
  rawCoqTemplateExN 5
    coqRestrictedPADirectAssumptionMembershipBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Context truth after the first five membership witnesses. *)
Definition coqRestrictedPADirectAssumptionShiftedContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 5
    coqRestrictedPADirectAssumptionExpandedContextTruthTemplate.

Definition coqRestrictedPADirectAssumptionShiftedContextBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionShiftedContextTruthTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Lemma coqRestrictedPADirectAssumptionShiftedContextTruth_shape :
  coqRestrictedPADirectAssumptionShiftedContextTruthTemplate =
  rawCoqTemplateExN 5
    coqRestrictedPADirectAssumptionShiftedContextBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Both bodies at the final ten-witness depth. *)
Definition coqRestrictedPADirectAssumptionFinalContextBodyTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionShiftedContextBodyTemplate.

Definition coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 5
    coqRestrictedPADirectAssumptionMembershipBodyTemplate.

Definition coqRestrictedPADirectAssumptionFinalPointwiseTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalContextBodyTemplate with
  | tfAnd _ pointwise => pointwise
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalRightMembershipTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate with
  | tfAnd _ membership => membership
  | _ => tfBot
  end.

Lemma coqRestrictedPADirectAssumptionFinalContextBody_shape :
  coqRestrictedPADirectAssumptionFinalContextBodyTemplate =
  tfAnd coqRestrictedPADirectAssumptionLeftTraversalTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionFinalMembershipBody_shape :
  coqRestrictedPADirectAssumptionFinalMembershipBodyTemplate =
  tfAnd coqRestrictedPADirectAssumptionRightTraversalTemplate
    coqRestrictedPADirectAssumptionFinalRightMembershipTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionFinalRightMembership_shape :
  coqRestrictedPADirectAssumptionFinalRightMembershipTemplate =
  coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate.
Proof. vm_compute. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.
