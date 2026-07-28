(**
  The exact outer local-proof shell for the direct derivation-soundness
  strong step.

  [RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier]
  stops immediately outside the represented endpoint relation.  This file
  discharges the surrounding logical syntax, without adding a semantic
  soundness hypothesis.  Its only residual is therefore one constructor-
  local implication root for each of the seventeen proof rules, in the
  literal context obtained after the four endpoint binders and the eight
  existential endpoint fields have been entered.

  The order of the predicate body matters.  It is kept visibly as

    restricted proof -> endpoint -> admissible -> context truth
      -> conclusion truth.

  In particular the finite dispatcher is asked only for the remaining
  [admissible -> context truth -> conclusion truth] suffix.  Endpoint and
  restricted-proof implication introduction happen after all eight endpoint
  witnesses have been eliminated; the four endpoint universals, [K(d)], and
  the outer [d] universal are then introduced in that order.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

Import ListNotations.
Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.

(** Repeated eigenvariable entry.  The successor equation deliberately
    shifts the context first and then recurses.  Thus a proof under
    [rawCoqTemplateContextShiftN n context] is in exactly the child context
    expected by [n] successive All-I nodes; no context transport is hidden
    behind a propositional equality. *)
Fixpoint rawCoqTemplateContextShiftN
    (count : nat) (context : TemplateContext) : TemplateContext :=
  match count with
  | 0 => context
  | S remaining =>
      rawCoqTemplateContextShiftN remaining
        (templateContextShift context)
  end.

Fixpoint rawCoqTemplateAllN
    (count : nat) (body : TemplateFormula) : TemplateFormula :=
  match count with
  | 0 => body
  | S remaining => tfAll (rawCoqTemplateAllN remaining body)
  end.

Arguments rawCoqTemplateContextShiftN count context : clear implicits.
Arguments rawCoqTemplateAllN count body : clear implicits.

(** The local All-I compiler exposes the exact shifted context at every
    stage.  The direct translation supplies the represented unit shift for
    every template formula, so [raw_templateContext_shift] is an actual
    [RawContextShift], not a metatheoretic renaming shortcut. *)
Theorem raw_codedPALocalProofOf_templateAllNIntroduction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    count context body innerRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (rawCoqTemplateContextShiftN count context))
    (rawTemplateFormula translation body)
    innerRoot ->
  exists outerRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (rawCoqTemplateAllN count body))
      outerRoot.
Proof.
  intros M hPA translation count.
  induction count as [|remaining ih];
    intros context body innerRoot hinner.
  - cbn [rawCoqTemplateContextShiftN rawCoqTemplateAllN] in hinner |- *.
    exists innerRoot. exact hinner.
  - cbn [rawCoqTemplateContextShiftN] in hinner.
    destruct (ih (templateContextShift context) body innerRoot hinner)
      as [child hchild].
    destruct hchild as [hcoverage hendpoint].
    exists (rawProofAllIRoot M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (rawCoqTemplateAllN remaining body))
      child).
    cbn [rawCoqTemplateAllN].
    rewrite rawTemplateFormula_all.
    split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (rawTemplateContextCode translation context)
        (rawTemplateContextCode translation
          (templateContextShift context))
        (rawTemplateFormula translation
          (rawCoqTemplateAllN remaining body))
        child
        (raw_templateContext_shift M hPA translation context)
        hcoverage hendpoint).
    + exact (raw_proofAllI_endpoint M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation
          (rawCoqTemplateAllN remaining body))
        child).
Qed.

(** The suffix intentionally handed to the endpoint dispatcher. *)
Definition rawCoqRestrictedPADirectStrongStepRemainingTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADerivationSoundnessAdmissibleTemplate
    (tfImp coqRestrictedPADerivationSoundnessContextTruthTemplate
      coqRestrictedPADerivationSoundnessConclusionTruthTemplate).

(** The body after the four endpoint universals have been entered.  The
    outer All-I first shifts [tail], then Imp-I adds [K(d)]; four further
    All-I steps produce this exact context. *)
Definition rawCoqRestrictedPADirectStrongStepFourBinderContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateContextShiftN 4
    (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
      templateContextShift tail).

(** The endpoint implication is compiled with restricted proof still at the
    head of its tail, exactly matching the advertised implication order. *)
Definition rawCoqRestrictedPADirectStrongStepEndpointTail
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
    rawCoqRestrictedPADirectStrongStepFourBinderContext tail.

Arguments rawCoqRestrictedPADirectStrongStepFourBinderContext
  tail : clear implicits.
Arguments rawCoqRestrictedPADirectStrongStepEndpointTail
  tail : clear implicits.

(** The sharp residual.  Unfolding the imported deep-endpoint family shows
    exactly seventeen roots.  Every root lives below the endpoint witness
    conjunction in [rawCoqRestrictedPADirectEndpointDeepTail], and proves a
    constructor case implies only the eight-times-renamed remaining suffix.
    There is no result root, conclusion proof, or strong-step proof among
    these inputs. *)
Definition RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectDeepEndpointRuleCaseImplicationRoots
    M hPA inputs
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail)
    rawCoqRestrictedPADirectStrongStepRemainingTemplate.

Arguments RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
  M hPA inputs tail : clear implicits.

(** Fully unfolded public view of the residual boundary.  This statement is
    intentionally verbose: it records the deepest witness context, all ten
    literal endpoint terms, the eight-fold renaming of the suffix, and the
    fact that selection ranges over the finite seventeen-constructor type. *)
Lemma raw_coqRestrictedPADirectStrongStepRuleCaseImplicationRoots_view :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail <->
  forall selected : RawCoqRestrictedPAProofRuleCase,
    exists root : M,
      RawCodedPALocalProofOf M
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
            rawCoqRestrictedPADirectEndpointDeepTail
              (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            (rawCoqRestrictedPAProofRuleCaseTemplate selected
              (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
              (tVar 6) (tVar 5) (tVar 4) (tVar 3)
              (tVar 2) (tVar 1) (tVar 0)))
          (rawDirectTemplateFormula inputs
            (rawCoqTemplateRenameN 8
              rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
        root.
Proof. reflexivity. Qed.

(** Conversion lemmas pin the compact iterators to the advertised source
    templates and make the implication order independently auditable. *)
Lemma raw_coqRestrictedPADirectStrongStep_predicate_shape :
  rawCoqTemplateAllN 4
    (tfImp coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      (tfImp coqRestrictedPADerivationSoundnessEndpointTemplate
        rawCoqRestrictedPADirectStrongStepRemainingTemplate)) =
  coqRestrictedPADerivationSoundnessPredicateTemplate.
Proof. reflexivity. Qed.

Lemma raw_coqRestrictedPADirectStrongStep_template_shape :
  rawCoqTemplateAllN 1
    (tfImp
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
      coqRestrictedPADerivationSoundnessPredicateTemplate) =
  coqRestrictedPADerivationSoundnessCarrierStrongStepTemplate.
Proof. reflexivity. Qed.

(** A named certificate for all exact eigenvariable contexts used below.
    It is useful to consumers that transport the resulting local proof into
    a larger carrier context: each entry is a literal represented context
    shift, while binder readiness itself remains a separate transport
    obligation rather than being silently inferred from realizability. *)
Definition RawCoqRestrictedPADirectStrongStepBinderShifts
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawContextShift M
    (rawTemplateContextCode translation tail)
    (rawTemplateContextCode translation (templateContextShift tail)) /\
  forall stage : nat,
    stage < 4 ->
    RawContextShift M
      (rawTemplateContextCode translation
        (rawCoqTemplateContextShiftN stage
          (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
            templateContextShift tail)))
      (rawTemplateContextCode translation
        (templateContextShift
          (rawCoqTemplateContextShiftN stage
            (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
              templateContextShift tail)))).

Arguments RawCoqRestrictedPADirectStrongStepBinderShifts
  M hPA inputs tail : clear implicits.

Lemma raw_coqRestrictedPADirectStrongStepBinderShifts : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  RawCoqRestrictedPADirectStrongStepBinderShifts M hPA inputs tail.
Proof.
  intros M hPA inputs tail.
  unfold RawCoqRestrictedPADirectStrongStepBinderShifts.
  split.
  - apply raw_templateContext_shift. exact hPA.
  - intros stage _.
    apply raw_templateContext_shift. exact hPA.
Qed.

(** Assemble the exact predicate body around the endpoint dispatcher. *)
Theorem
    raw_codedPALocalProofOf_coqRestrictedPADirectStrongStepPredicateBody :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail ->
  exists bodyRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawCoqRestrictedPADirectStrongStepFourBinderContext tail))
      (rawDirectTemplateFormula inputs
        (tfImp
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate
          (tfImp
            coqRestrictedPADerivationSoundnessEndpointTemplate
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      bodyRoot.
Proof.
  intros M hPA inputs tail hcaseRoots.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectEndpointFromRuleCases
      M hPA inputs
      (rawCoqRestrictedPADirectStrongStepEndpointTail tail)
      rawCoqRestrictedPADirectStrongStepRemainingTemplate
      hcaseRoots) as [dispatchRoot hdispatch].
  set (fourBinderContext :=
    rawCoqRestrictedPADirectStrongStepFourBinderContext tail).
  assert (hendpointImp : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
          fourBinderContext))
      (rawDirectTemplateFormula inputs
        (tfImp coqRestrictedPADerivationSoundnessEndpointTemplate
          rawCoqRestrictedPADirectStrongStepRemainingTemplate))
      (rawProofImpIRoot M
        (rawTemplateContextCode translation
          (coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
            fourBinderContext))
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessEndpointTemplate)
        (rawDirectTemplateFormula inputs
          rawCoqRestrictedPADirectStrongStepRemainingTemplate)
        dispatchRoot)).
  {
    rewrite rawDirectTemplateFormula_imp_code.
    apply (raw_codedPALocalProofOf_impI M hPA
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
          fourBinderContext))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessEndpointTemplate)
      (rawDirectTemplateFormula inputs
        rawCoqRestrictedPADirectStrongStepRemainingTemplate)
      dispatchRoot).
    unfold rawCoqRestrictedPADirectStrongStepEndpointTail in hdispatch.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessEndpointTemplate ::
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
          fourBinderContext))
      (rawDirectTemplateFormula inputs
        rawCoqRestrictedPADirectStrongStepRemainingTemplate)
      dispatchRoot).
    exact hdispatch.
  }
  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation fourBinderContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    (rawDirectTemplateFormula inputs
      (tfImp coqRestrictedPADerivationSoundnessEndpointTemplate
        rawCoqRestrictedPADirectStrongStepRemainingTemplate))
    (rawProofImpIRoot M
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessRestrictedProofTemplate ::
          fourBinderContext))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessEndpointTemplate)
      (rawDirectTemplateFormula inputs
        rawCoqRestrictedPADirectStrongStepRemainingTemplate)
      dispatchRoot)).
  repeat rewrite rawDirectTemplateFormula_imp_code.
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation fourBinderContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    (rawDirectTemplateFormula inputs
      (tfImp coqRestrictedPADerivationSoundnessEndpointTemplate
        rawCoqRestrictedPADirectStrongStepRemainingTemplate))).
  exact hendpointImp.
Qed.

(** Close the body through all five universals and both surrounding
    implications.  This is the desired direct strong-step local proof; its
    sole hypothesis is the seventeen-case family above. *)
Theorem raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    tail,
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail ->
  exists strongStepRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) tail)
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      strongStepRoot.
Proof.
  intros M hPA inputs tail hcaseRoots.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStepPredicateBody
      M hPA inputs tail hcaseRoots) as [bodyRoot hbody].
  set (body :=
    tfImp coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      (tfImp coqRestrictedPADerivationSoundnessEndpointTemplate
        rawCoqRestrictedPADirectStrongStepRemainingTemplate)).
  destruct
    (raw_codedPALocalProofOf_templateAllNIntroduction
      M hPA translation 4
      (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
        templateContextShift tail)
      body bodyRoot) as [predicateRoot hpredicate].
  {
    unfold rawCoqRestrictedPADirectStrongStepFourBinderContext in hbody.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqTemplateContextShiftN 4
          (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
            templateContextShift tail)))
      (rawTemplateFormula translation body) bodyRoot).
    exact hbody.
  }
  assert (hpredicate' : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
          templateContextShift tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessPredicateTemplate)
      predicateRoot).
  {
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate ::
          templateContextShift tail))
      (rawTemplateFormula translation
        (rawCoqTemplateAllN 4 body)) predicateRoot).
    exact hpredicate.
  }
  assert (himp : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation (templateContextShift tail))
      (rawDirectTemplateFormula inputs
        (tfImp
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
          coqRestrictedPADerivationSoundnessPredicateTemplate))
      (rawProofImpIRoot M
        (rawTemplateContextCode translation (templateContextShift tail))
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessPredicateTemplate)
        predicateRoot)).
  {
    rewrite rawDirectTemplateFormula_imp_code.
    exact (raw_codedPALocalProofOf_impI M hPA
      (rawTemplateContextCode translation (templateContextShift tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessPredicateTemplate)
      predicateRoot hpredicate').
  }
  destruct
    (raw_codedPALocalProofOf_templateAllNIntroduction
      M hPA translation 1 tail
      (tfImp
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate
        coqRestrictedPADerivationSoundnessPredicateTemplate)
      (rawProofImpIRoot M
        (rawTemplateContextCode translation (templateContextShift tail))
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessPredicateTemplate)
        predicateRoot)
      himp) as [strongStepRoot hstrongStep].
  exists strongStepRoot.
  rewrite
    raw_coqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode_view.
  exact hstrongStep.
Qed.

(** Explicit carrier-context endpoint.  The exact shell itself uses no
    weakening, so it needs only the represented shifts recorded above.  A
    consumer that moves the closed shell into a different carrier context
    must supply the stronger all-future-binders condition
    [RawContextBinderReady].  Keeping that premise public prevents ordinary
    membership inclusion from being mistaken for eigenvariable-safe
    transport. *)
Corollary
    raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep_in_binderReady_context
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      tail targetContext,
  let sourceContext := rawTemplateContextCode
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail in
  RawContextListRealizable M targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawContextBinderReady M sourceContext targetContext ->
  RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots
    M hPA inputs tail ->
  exists strongStepRoot : M,
    RawCodedPALocalProofOf M targetContext
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      strongStepRoot.
Proof.
  intros M hPA inputs tail targetContext.
  cbn zeta.
  intros htargetRealizable hincluded hbinderReady hcaseRoots.
  destruct (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep
    M hPA inputs tail hcaseRoots) as [sourceRoot hsource].
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail)
    targetContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs)
    sourceRoot).
  - apply raw_templateContext_realizable. exact hPA.
  - exact htargetRealizable.
  - exact hincluded.
  - exact hbinderReady.
  - exact hsource.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
