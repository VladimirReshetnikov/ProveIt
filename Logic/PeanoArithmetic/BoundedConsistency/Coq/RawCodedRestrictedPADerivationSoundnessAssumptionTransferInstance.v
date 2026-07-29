(**
  The twelve-parameter traversal-transfer instance used by Assumption.

  Context truth opens five traversal witnesses first.  Public membership then
  opens an independent five-witness traversal.  At that ten-binder depth the
  original displayed context and formula have become [#17] and [#16], the
  context-truth tuple occupies [#9..#5], and the membership tuple occupies
  [#4..#0].

  This module instantiates the explicit universal source at exactly those
  terms and proves the resulting formula has the intended three-premise
  implication shape.  The calculation is entirely standard template syntax;
  it is kept separate so the later proof tree need not normalize twelve
  openings while validating every propositional node.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedContextMembershipTransferPA
  RawCodedTemplateSyntax
  RawCodedTemplateRepeatedUniversalElimination.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.

Import PA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextMembershipTransferPA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.

Definition coqRestrictedPADirectAssumptionTransferSourceTemplate
    : TemplateFormula :=
  embedPAFormula contextListMemberTransferUniversalFormula.

Definition coqRestrictedPADirectAssumptionTransferReplacements
    : list TemplateTerm :=
  [ttVar 17; ttVar 16;
   ttVar 9; ttVar 8; ttVar 7; ttVar 6; ttVar 5;
   ttVar 4; ttVar 3; ttVar 2; ttVar 1; ttVar 0].

Definition coqRestrictedPADirectAssumptionTransferInstanceTemplate
    : TemplateFormula :=
  rawCoqTemplateAllEListResult
    coqRestrictedPADirectAssumptionTransferReplacements
    coqRestrictedPADirectAssumptionTransferSourceTemplate.

Definition coqRestrictedPADirectAssumptionLeftTraversalTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListTraversalTermAt
      (tVar 17) (tVar 9) (tVar 8) (tVar 7) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectAssumptionRightTraversalTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListTraversalTermAt
      (tVar 17) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)).

Definition coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberWithTablesTermAt
      (tVar 16) (tVar 4) (tVar 1) (tVar 0)).

Definition coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate
    : TemplateFormula :=
  embedPAFormula
    (contextListMemberWithTablesTermAt
      (tVar 16) (tVar 9) (tVar 6) (tVar 5)).

(** The source really exposes all twelve requested binders. *)
Lemma coqRestrictedPADirectAssumptionTransferReplacements_ready :
  RawCoqTemplateAllEListReady
    coqRestrictedPADirectAssumptionTransferReplacements
    coqRestrictedPADirectAssumptionTransferSourceTemplate.
Proof.
  vm_compute. exact I.
Qed.

(** Exact implication endpoint after all twelve openings. *)
Lemma coqRestrictedPADirectAssumptionTransferInstance_shape :
  coqRestrictedPADirectAssumptionTransferInstanceTemplate =
  tfImp coqRestrictedPADirectAssumptionLeftTraversalTemplate
    (tfImp coqRestrictedPADirectAssumptionRightTraversalTemplate
      (tfImp
        coqRestrictedPADirectAssumptionRightMembershipWithTablesTemplate
        coqRestrictedPADirectAssumptionLeftMembershipWithTablesTemplate)).
Proof.
  vm_compute. reflexivity.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.
