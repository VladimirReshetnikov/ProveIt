(**
  A generic affine spine for direct-rule ready contexts.

  Every direct rule below the eight endpoint witnesses uses the same context
  shape: three rule-specific formulas, the endpoint witness body, and the
  strong-step endpoint tail.  Only the three formulas vary from rule to rule.
  This module isolates the common tail calculation so individual semantic
  compilers do not repeatedly normalize the very large endpoint template.

  Five shifts are introduced before the endpoint dispatcher (one outer
  eigenvariable entry and four endpoint binders), and the dispatcher adds
  eight more.  Consequently an arbitrary inherited tail is shifted thirteen
  times.  A tail of embedded standard PA axioms is fixed by every shift, which
  gives the append equation used by growing-witness compilers.
*)

From Stdlib Require Import List Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.

Import PA.
Import PABoundedCodedProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

(** The strong-step shell and the general binder library independently define
    the same outside-in context-shift iterator.  Making their equality opaque
    lets the affine proofs below rewrite between the two APIs without
    unfolding any concrete rule formula. *)
Lemma raw_coqTemplateContextShiftN_eq_templateContextShiftMany : forall
    count context,
  rawCoqTemplateContextShiftN count context =
  templateContextShiftMany count context.
Proof.
  induction count as [|remaining ih]; intro context.
  - reflexivity.
  - cbn [rawCoqTemplateContextShiftN templateContextShiftMany].
    apply ih.
Qed.

(** Entering the strong-step endpoint shifts an inherited tail five times:
    once before the carrier prefix and four times for the endpoint binders. *)
Lemma raw_coqRestrictedPADirectStrongStepEndpointTail_affine : forall tail,
  rawCoqRestrictedPADirectStrongStepEndpointTail tail =
  rawCoqRestrictedPADirectStrongStepEndpointTail [] ++
    templateContextShiftMany 5 tail.
Proof.
  intro tail.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail,
    rawCoqRestrictedPADirectStrongStepFourBinderContext.
  rewrite !raw_coqTemplateContextShiftN_eq_templateContextShiftMany.
  reflexivity.
Qed.

(** Composition is stated in the orientation produced by substituting one
    affine context equation inside another. *)
Lemma raw_templateContextShiftMany_compose : forall first second context,
  templateContextShiftMany first
      (templateContextShiftMany second context) =
  templateContextShiftMany (first + second) context.
Proof.
  intros first second.
  induction second as [|smaller ih]; intro context.
  - replace (first + 0) with first by lia.
    reflexivity.
  - cbn [templateContextShiftMany].
    rewrite ih.
    replace (first + S smaller) with (S (first + smaller)) by lia.
    reflexivity.
Qed.

(** The full deep endpoint contributes eight further shifts.  The explicit
    [f_equal] at the end folds the fixed prefix through the existing affine
    theorem without asking conversion to normalize the endpoint body. *)
Lemma raw_coqRestrictedPADirectStrongEndpointDeepTail_affine : forall tail,
  rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail) =
  rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail []) ++
    templateContextShiftMany 13 tail.
Proof.
  intro tail.
  rewrite
    (raw_coqRestrictedPADirectEndpointDeepTail_affine
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail)).
  rewrite raw_coqRestrictedPADirectStrongStepEndpointTail_affine.
  rewrite raw_coqTemplateContextShiftMany_app.
  rewrite raw_templateContextShiftMany_compose.
  exact
    (f_equal
      (fun prefix => prefix ++ templateContextShiftMany 13 tail)
      (eq_sym
        (raw_coqRestrictedPADirectEndpointDeepTail_affine
          (rawCoqRestrictedPADirectStrongStepEndpointTail [])))).
Qed.

(** Abstract the only common context shape needed by post-And-I rule cases.
    The names [outer], [admissible], and [branch] document the usual clients,
    but no relationship between these formulas is assumed. *)
Definition coqRestrictedPADirectStandardReadyContext
    (outer admissible branch : TemplateFormula)
    (tail : TemplateContext) : TemplateContext :=
  outer :: admissible :: branch ::
    rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
    rawCoqRestrictedPADirectEndpointDeepTail
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Arguments coqRestrictedPADirectStandardReadyContext
  outer admissible branch tail : clear implicits.

Lemma coqRestrictedPADirectStandardReadyContext_affine : forall
    outer admissible branch tail,
  coqRestrictedPADirectStandardReadyContext
      outer admissible branch tail =
  coqRestrictedPADirectStandardReadyContext
      outer admissible branch [] ++
    templateContextShiftMany 13 tail.
Proof.
  intros outer admissible branch tail.
  unfold coqRestrictedPADirectStandardReadyContext.
  rewrite raw_coqRestrictedPADirectStrongEndpointDeepTail_affine.
  reflexivity.
Qed.

(** Embedded PA axioms are sentences, hence the thirteen inherited shifts
    disappear.  This is the exact equation used to reinterpret a source root
    produced on [ready [] ++ witnesses] as a root in [ready witnesses]. *)
Lemma coqRestrictedPADirectStandardReadyContext_app_witnesses : forall
    outer admissible branch witnesses,
  coqRestrictedPADirectStandardReadyContext outer admissible branch
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStandardReadyContext outer admissible branch [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros outer admissible branch witnesses.
  rewrite coqRestrictedPADirectStandardReadyContext_affine.
  rewrite templateContextShiftMany_embedPAAxiomWitnesses_fixed.
  reflexivity.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
