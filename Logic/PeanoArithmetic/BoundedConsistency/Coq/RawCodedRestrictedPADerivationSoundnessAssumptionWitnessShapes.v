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
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
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
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
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

(** The transfer instance returns membership expressed with the context-truth
    tables.  One final existential index witnesses that membership. *)
Definition coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate.

Definition coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate with
  | tfAnd liveIndex _ => liveIndex
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalHeadLookupTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalMembershipIndexBodyTemplate with
  | tfAnd _ headLookup => headLookup
  | _ => tfBot
  end.

Lemma coqRestrictedPADirectAssumptionFinalLeftMembership_shape :
  coqRestrictedPADirectAssumptionFinalLeftMembershipTemplate =
  tfEx
    (tfAnd coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
      coqRestrictedPADirectAssumptionFinalHeadLookupTemplate).
Proof. vm_compute. reflexivity. Qed.

(** After opening that index, the two universal pointwise binders specialize
    to the same bound and lookup formulas.  Native context truth fixes the two
    hierarchy arguments of its conclusion leaf to zero; a later carrier-code
    equation removes that harmless difference from the public conclusion
    truth leaf. *)
Definition coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [ttZero; ttZero;
     coqRestrictedPADirectAssumptionWitnessFormulaTerm;
     ttVar 9; ttVar 8].

Definition coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectAssumptionFinalPointwiseTemplate.

Definition coqRestrictedPADirectAssumptionFinalPointwiseIndexBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalPointwiseAfterIndexTemplate
    : TemplateFormula :=
  templateFormulaOpen (ttVar 0)
    coqRestrictedPADirectAssumptionFinalPointwiseIndexBodyTemplate.

Definition coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalPointwiseAfterIndexTemplate with
  | tfImp _ consequent => consequent
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalPointwiseFormulaBodyTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalPointwiseAfterFormulaTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate with
  | tfAll _ => templateFormulaOpen (ttVar 17)
      coqRestrictedPADirectAssumptionFinalPointwiseFormulaBodyTemplate
  | _ => tfBot
  end.

Definition coqRestrictedPADirectAssumptionFinalPointwiseTruthTemplate
    : TemplateFormula :=
  match coqRestrictedPADirectAssumptionFinalPointwiseAfterFormulaTemplate with
  | tfImp _ truth => truth
  | _ => tfBot
  end.

Lemma coqRestrictedPADirectAssumptionFinalPointwiseAfterIndex_shape :
  coqRestrictedPADirectAssumptionFinalPointwiseAfterIndexTemplate =
  tfImp coqRestrictedPADirectAssumptionFinalLiveIndexTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionShiftedFinalPointwise_shape :
  coqRestrictedPADirectAssumptionShiftedFinalPointwiseTemplate =
  tfAll coqRestrictedPADirectAssumptionFinalPointwiseIndexBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionFinalPointwiseAfterLive_shape :
  coqRestrictedPADirectAssumptionFinalPointwiseAfterLiveTemplate =
  tfAll coqRestrictedPADirectAssumptionFinalPointwiseFormulaBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionFinalPointwiseAfterFormula_shape :
  coqRestrictedPADirectAssumptionFinalPointwiseAfterFormulaTemplate =
  tfImp coqRestrictedPADirectAssumptionFinalHeadLookupTemplate
    coqRestrictedPADirectAssumptionFinalPointwiseTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectAssumptionFinalPointwiseTruth_shape :
  coqRestrictedPADirectAssumptionFinalPointwiseTruthTemplate =
  rawCoqTemplateRenameN 11
    coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.
