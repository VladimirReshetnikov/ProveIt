(**
  Direct rule-case integration after excluded middle.

  The public excluded-middle residual first consumes the represented bottom,
  implication, and disjunction constructor rows.  Its remaining semantic
  content is exactly

      admissibility of the displayed disjunction -> truth of it.

  A carrier-parametric native compiler for that positive excluded-middle
  truth row is not yet available.  This module selects an actual local-proof
  root for precisely that non-target core and promotes it through the three
  constructor-row antecedents using a checked finite template derivation.
  The public target is never an input.

  The selected core is synchronized with a certified finite standard-PA
  witness tail.  Standard surrounding-tail transport then supports the
  growing continuation whose excluded-middle field has been deleted.
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
  RawCodedPALocalProofExistential
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
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** ------------------------------------------------------------------
    Exact positive-truth core and finite constructor-row promotion. *)

Definition coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate.

Definition RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectExcludedMiddleCaseContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleTruthCoreTemplate)
      root.

Arguments RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot
  M translation tail : clear implicits.

Definition coqRestrictedPADirectExcludedMiddleAfterImpTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
    coqRestrictedPADirectExcludedMiddleTruthCoreTemplate.

Definition coqRestrictedPADirectExcludedMiddleAfterBottomTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExcludedMiddleImpTemplate
    coqRestrictedPADirectExcludedMiddleAfterImpTemplate.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionContext0 tail :=
  coqRestrictedPADirectExcludedMiddleTruthCoreTemplate ::
    coqRestrictedPADirectExcludedMiddleCaseContext tail.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionContext1 tail :=
  coqRestrictedPADirectExcludedMiddleBottomTemplate ::
    coqRestrictedPADirectExcludedMiddleCorePromotionContext0 tail.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionContext2 tail :=
  coqRestrictedPADirectExcludedMiddleImpTemplate ::
    coqRestrictedPADirectExcludedMiddleCorePromotionContext1 tail.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionContext3 tail :=
  coqRestrictedPADirectExcludedMiddleOrTemplate ::
    coqRestrictedPADirectExcludedMiddleCorePromotionContext2 tail.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionAssumptionRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectExcludedMiddleCorePromotionContext3 tail)
    coqRestrictedPADirectExcludedMiddleTruthCoreTemplate.

Definition coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleCorePromotionContext2 tail)
    coqRestrictedPADirectExcludedMiddleOrTemplate
    coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAssumptionRoot tail).

Definition coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleCorePromotionContext1 tail)
    coqRestrictedPADirectExcludedMiddleImpTemplate
    coqRestrictedPADirectExcludedMiddleAfterImpTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot tail).

Definition coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleCorePromotionContext0 tail)
    coqRestrictedPADirectExcludedMiddleBottomTemplate
    coqRestrictedPADirectExcludedMiddleAfterBottomTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot tail).

Definition coqRestrictedPADirectExcludedMiddleCorePromotionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
    coqRestrictedPADirectExcludedMiddleTruthLawTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot tail).

Lemma coqRestrictedPADirectExcludedMiddleCorePromotionAssumptionRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCorePromotionContext3 tail)
    coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAssumptionRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectExcludedMiddleCorePromotionContext3,
    coqRestrictedPADirectExcludedMiddleCorePromotionContext2,
    coqRestrictedPADirectExcludedMiddleCorePromotionContext1,
    coqRestrictedPADirectExcludedMiddleCorePromotionContext0.
  do 3 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCorePromotionContext2 tail)
    coqRestrictedPADirectExcludedMiddleAfterImpTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot,
    coqRestrictedPADirectExcludedMiddleAfterImpTemplate.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleCorePromotionAssumptionRoot_valid
      tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCorePromotionContext1 tail)
    coqRestrictedPADirectExcludedMiddleAfterBottomTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot,
    coqRestrictedPADirectExcludedMiddleAfterBottomTemplate.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterOrRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCorePromotionContext0 tail)
    coqRestrictedPADirectExcludedMiddleTruthLawTemplate
    (coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot,
    coqRestrictedPADirectExcludedMiddleTruthLawTemplate.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleCorePromotionAfterImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleCorePromotionRoot_valid :
    forall tail,
  TemplateRawDerives (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    (tfImp coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
      coqRestrictedPADirectExcludedMiddleTruthLawTemplate)
    (coqRestrictedPADirectExcludedMiddleCorePromotionRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleCorePromotionRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleCorePromotionTargetRoot_valid tail).
Qed.

Theorem raw_excludedMiddleTruthLawRoot_of_coreLawRoot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail.
Proof.
  intros M hPA inputs tail (coreRoot & hcore).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectExcludedMiddleCorePromotionRoot tail)
      (proj1
        (coqRestrictedPADirectExcludedMiddleCorePromotionRoot_valid tail)))
    as hpromotion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation
      (coqRestrictedPADirectExcludedMiddleCaseContext tail)
      coqRestrictedPADirectExcludedMiddleTruthCoreTemplate
      coqRestrictedPADirectExcludedMiddleTruthLawTemplate
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExcludedMiddleCorePromotionRoot tail))
      coreRoot hpromotion hcore) as htarget.
  eexists. exact htarget.
Qed.

(** ------------------------------------------------------------------
    Exact fifteen-field continuation after deleting excluded middle. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterExcludedMiddle
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterExcludedMiddle_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterExcludedMiddle_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterExcludedMiddle
  M hPA inputs tail : clear implicits.

Theorem raw_afterBottomElimination_of_afterExcludedMiddle : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterExcludedMiddle
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hexcluded hremaining.
  destruct hremaining. constructor; assumption.
Qed.

(** ------------------------------------------------------------------
    Certified selection, affine transport, and growing-tail merge. *)

Definition RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectExcludedMiddleCaseContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectExcludedMiddleCaseContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof (coqRestrictedPADirectBottomCaseContext_app_witnesses witnesses)
    as hbottom.
  unfold coqRestrictedPADirectBottomCaseContext in hbottom.
  cbn [List.app] in hbottom.
  pose proof (f_equal (skipn 1) hbottom) as hdeep.
  cbn [skipn] in hdeep.
  unfold coqRestrictedPADirectBottomDeepContext in hdeep.
  unfold coqRestrictedPADirectExcludedMiddleCaseContext,
    coqRestrictedPADirectExcludedMiddleDeepContext.
  cbn [List.app]. now rewrite hdeep.
Qed.

Theorem raw_excludedMiddleTruthCoreLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      prefix witnesses suffix,
  RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectExcludedMiddleTruthCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix (root & hroot).
  rewrite coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectExcludedMiddleCaseContext [])
      prefix witnesses suffix
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectExcludedMiddleTruthCoreTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterExcludedMiddleStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterExcludedMiddle
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterExcludedMiddleStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_remainingAfterBottomEliminationCompiler_of_selectedExcludedCore :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterExcludedMiddleStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (coreWitnesses & _ & hcore) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ coreWitnesses))
    as [suffix hremainingTail].
  exists (coreWitnesses ++ suffix).
  apply raw_afterBottomElimination_of_afterExcludedMiddle.
  - apply raw_excludedMiddleTruthLawRoot_of_coreLawRoot.
    exact (raw_excludedMiddleTruthCoreLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses coreWitnesses suffix hcore).
  - replace ((baseWitnesses ++ coreWitnesses) ++ suffix)
      with (baseWitnesses ++ (coreWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native endpoint with excluded middle absent from the final continuation
    and its positive-truth core retained as the exact producer boundary. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterExcludedMiddle
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
     (RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
        M hPA inputs /\
      (RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs /\
       (RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail
          M hPA inputs /\
        (RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
           M hPA inputs /\
         RawCoqRestrictedPADirectRemainingAfterExcludedMiddleStandardTailCompiler
           M hPA inputs)))))) ->
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
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterBottomElimination
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth
      [hrecursive
        [hsplit
          [himpECore [hbottomCore [hexcludedCore hremaining]]]]]].
  split; [exact horTruth |].
  split; [exact hrecursive |].
  split; [exact hsplit |].
  split; [exact himpECore |].
  split; [exact hbottomCore |].
  exact
    (raw_remainingAfterBottomEliminationCompiler_of_selectedExcludedCore
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hexcludedCore hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
