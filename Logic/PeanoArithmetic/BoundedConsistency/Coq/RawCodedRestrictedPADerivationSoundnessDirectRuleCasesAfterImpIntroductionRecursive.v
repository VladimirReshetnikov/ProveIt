(**
  Direct rule-case integration after the Imp-I recursive-child law.

  The post-Or-I-left-truth dispatcher begins with the two Imp-I seams.  The
  first is the recursive-child law; unlike the already compiled Assumption
  and Or-I-left fields, no native theorem currently produces that law from
  the direct truth selectors alone.  In particular, the generic renamed
  child-truth compiler still needs an honest structural child interface and
  the Imp-I-specific extension of context truth by the antecedent.

  This module therefore records the smallest non-circular integration
  boundary: one independently selected represented recursive-child root on
  a finite standard PA-axiom tail.  Generic witnessed-tail transport carries
  that root through any earlier and later batches.  The continuation then
  exposes nineteen fields, while the adjacent dynamic implication Tarski
  law remains explicit rather than being smuggled in through this premise.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.

(** Exact nineteen-field remainder after deleting only the Imp-I recursive
    seam.  The dynamic Imp-I truth law remains the first visible field. *)
Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionRecursive
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterImpRecursive_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpRecursive_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpRecursive_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpRecursive_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpRecursive_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpRecursive_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionRecursive
  M hPA inputs tail : clear implicits.

Theorem raw_afterOrIntroductionLeftTruth_of_afterImpIntroductionRecursive :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionRecursive
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeftTruth
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hrecursive hremaining.
  destruct hremaining.
  constructor; assumption.
Qed.

(** Provenance boundary for this increment.  It contains an actual local
    proof root, not semantic validity of the recursive law and not the whole
    dispatcher record, and its tail is certified by standard PA witnesses. *)
Definition RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
  M hPA inputs : clear implicits.

(** The fixed ready prefix is affine in a standard PA-axiom tail.  Sentence
    closure makes all shifts introduced by the endpoint binders disappear. *)
Lemma coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof
    (coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses
      witnesses) as horReady.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext
    in horReady.
  cbn [List.app] in horReady.
  pose proof (f_equal (skipn 3) horReady) as hdeep.
  cbn [skipn] in hdeep.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
    in hdeep.
  unfold
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepImpIntroductionCaseContext,
    coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext.
  cbn [List.app].
  now rewrite hdeep.
Qed.

(** Place an independently selected Imp-I recursive root between any earlier
    witness prefix and any later suffix. *)
Theorem raw_impIntroductionRecursiveChildLawRoot_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext [])
      prefix witnesses suffix
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionRecursiveChildLawTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectImpIntroductionReadyContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionRecursive
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
  M hPA inputs : clear implicits.

(** Merge the independently selected recursive-law batch with the nineteen
    batches chosen by the continuation. *)
Theorem
    raw_remainingAfterOrIntroductionLeftTruthCompiler_of_selectedImpIntroductionRecursive
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (recursiveWitnesses & _ & hrecursive) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ recursiveWitnesses))
    as [suffix hremainingTail].
  exists (recursiveWitnesses ++ suffix).
  apply raw_afterOrIntroductionLeftTruth_of_afterImpIntroductionRecursive.
  - exact
      (raw_impIntroductionRecursiveChildLawRoot_surround_witnessed_tail
        M hPA inputs baseWitnesses recursiveWitnesses suffix hrecursive).
  - replace ((baseWitnesses ++ recursiveWitnesses) ++ suffix)
      with (baseWitnesses ++ (recursiveWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native package endpoint with the Imp-I recursive field absent from the
    continuation.  A future native producer can discharge exactly the
    selected-tail conjunct without changing this growing-tail interface. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpIntroductionRecursive
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    let inputs :=
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth in
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
      M hPA inputs /\
    (RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
      M hPA inputs /\
     RawCoqRestrictedPADirectRemainingAfterImpIntroductionRecursiveStandardTailCompiler
       M hPA inputs)) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hcontinuation.
  apply
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterOrIntroductionLeftTruth
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth [hselected hremaining]].
  split; [exact horTruth |].
  exact
    (raw_remainingAfterOrIntroductionLeftTruthCompiler_of_selectedImpIntroductionRecursive
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hselected hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
