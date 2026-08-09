(**
  Direct rule-case integration after bottom elimination.

  The public Bottom-E residual first receives the strong prefix, restricted
  proof, literal constructor code, bottom formula code, and child endpoint.
  Its irreducible semantic payload is then exactly

      witness-context truth -> bottom.

  Producing that payload requires the represented recursive child call and
  represented refutation of a true bottom certificate; those dynamic
  compilers are not yet available at this carrier-parametric boundary.  This
  module therefore selects an actual local-proof root for precisely that
  non-target core.  A checked finite implication-introduction tree promotes
  it to the full public residual without assuming the target itself.

  The core root is synchronized with a certified finite standard-PA witness
  tail.  Affine tail transport and the growing-tail merge then remove the
  Bottom-E field from the successor continuation.
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
  RawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase
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
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** ------------------------------------------------------------------
    Exact contradiction core and finite promotion to the public law. *)

Definition RawCoqRestrictedPADirectBottomContradictionCoreLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectBottomCaseContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      root.

Arguments RawCoqRestrictedPADirectBottomContradictionCoreLawRoot
  M translation tail : clear implicits.

Definition coqRestrictedPADirectBottomCorePromotionContext0 tail :=
  coqRestrictedPADirectBottomAfterEndpointTemplate ::
    coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomCorePromotionContext1 tail :=
  coqRestrictedPADirectBottomStrongPrefixTemplate ::
    coqRestrictedPADirectBottomCorePromotionContext0 tail.

Definition coqRestrictedPADirectBottomCorePromotionContext2 tail :=
  coqRestrictedPADirectBottomRestrictedProofTemplate ::
    coqRestrictedPADirectBottomCorePromotionContext1 tail.

Definition coqRestrictedPADirectBottomCorePromotionContext3 tail :=
  coqRestrictedPADirectBottomCodeEqualityTemplate ::
    coqRestrictedPADirectBottomCorePromotionContext2 tail.

Definition coqRestrictedPADirectBottomCorePromotionContext4 tail :=
  coqRestrictedPADirectBottomFormulaCodeTemplate ::
    coqRestrictedPADirectBottomCorePromotionContext3 tail.

Definition coqRestrictedPADirectBottomCorePromotionContext5 tail :=
  coqRestrictedPADirectBottomChildEndpointTemplate ::
    coqRestrictedPADirectBottomCorePromotionContext4 tail.

Definition coqRestrictedPADirectBottomCorePromotionAssumptionRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectBottomCorePromotionContext5 tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate.

Definition coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCorePromotionContext4 tail)
    coqRestrictedPADirectBottomChildEndpointTemplate
    coqRestrictedPADirectBottomAfterEndpointTemplate
    (coqRestrictedPADirectBottomCorePromotionAssumptionRoot tail).

Definition coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCorePromotionContext3 tail)
    coqRestrictedPADirectBottomFormulaCodeTemplate
    coqRestrictedPADirectBottomAfterFormulaTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot tail).

Definition coqRestrictedPADirectBottomCorePromotionAfterCodeRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCorePromotionContext2 tail)
    coqRestrictedPADirectBottomCodeEqualityTemplate
    coqRestrictedPADirectBottomAfterCodeTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot tail).

Definition coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCorePromotionContext1 tail)
    coqRestrictedPADirectBottomRestrictedProofTemplate
    coqRestrictedPADirectBottomAfterRestrictedTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterCodeRoot tail).

Definition coqRestrictedPADirectBottomCorePromotionTargetRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCorePromotionContext0 tail)
    coqRestrictedPADirectBottomStrongPrefixTemplate
    coqRestrictedPADirectBottomAfterStrongPrefixTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot tail).

Definition coqRestrictedPADirectBottomCorePromotionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectBottomCaseContext tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate
    coqRestrictedPADirectBottomRecursiveContradictionLawTemplate
    (coqRestrictedPADirectBottomCorePromotionTargetRoot tail).

Lemma coqRestrictedPADirectBottomCorePromotionAssumptionRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext5 tail)
    coqRestrictedPADirectBottomAfterEndpointTemplate
    (coqRestrictedPADirectBottomCorePromotionAssumptionRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectBottomCorePromotionContext5,
    coqRestrictedPADirectBottomCorePromotionContext4,
    coqRestrictedPADirectBottomCorePromotionContext3,
    coqRestrictedPADirectBottomCorePromotionContext2,
    coqRestrictedPADirectBottomCorePromotionContext1,
    coqRestrictedPADirectBottomCorePromotionContext0.
  do 5 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext4 tail)
    coqRestrictedPADirectBottomAfterFormulaTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot,
    coqRestrictedPADirectBottomAfterFormulaTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCorePromotionAssumptionRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext3 tail)
    coqRestrictedPADirectBottomAfterCodeTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot,
    coqRestrictedPADirectBottomAfterCodeTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectBottomCorePromotionAfterEndpointRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionAfterCodeRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext2 tail)
    coqRestrictedPADirectBottomAfterRestrictedTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterCodeRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCorePromotionAfterCodeRoot,
    coqRestrictedPADirectBottomAfterRestrictedTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCorePromotionAfterFormulaRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext1 tail)
    coqRestrictedPADirectBottomAfterStrongPrefixTemplate
    (coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot,
    coqRestrictedPADirectBottomAfterStrongPrefixTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCorePromotionAfterCodeRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionTargetRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectBottomCorePromotionContext0 tail)
    coqRestrictedPADirectBottomRecursiveContradictionLawTemplate
    (coqRestrictedPADirectBottomCorePromotionTargetRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectBottomCorePromotionTargetRoot,
    coqRestrictedPADirectBottomRecursiveContradictionLawTemplate.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectBottomCorePromotionAfterRestrictedRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectBottomCorePromotionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectBottomCaseContext tail)
    (tfImp coqRestrictedPADirectBottomAfterEndpointTemplate
      coqRestrictedPADirectBottomRecursiveContradictionLawTemplate)
    (coqRestrictedPADirectBottomCorePromotionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectBottomCorePromotionRoot.
  apply coqRestrictedPADirectBottom_templateRawDerives_impI.
  exact (coqRestrictedPADirectBottomCorePromotionTargetRoot_valid tail).
Qed.

Theorem raw_bottomRecursiveContradictionLawRoot_of_coreLawRoot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectBottomContradictionCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail.
Proof.
  intros M hPA inputs tail (coreRoot & hcore).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectBottomCorePromotionRoot tail)
      (proj1 (coqRestrictedPADirectBottomCorePromotionRoot_valid tail)))
    as hpromotion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation (coqRestrictedPADirectBottomCaseContext tail)
      coqRestrictedPADirectBottomAfterEndpointTemplate
      coqRestrictedPADirectBottomRecursiveContradictionLawTemplate
      (rawTemplateProofCode translation
        (coqRestrictedPADirectBottomCorePromotionRoot tail))
      coreRoot hpromotion hcore) as htarget.
  eexists. exact htarget.
Qed.

(** ------------------------------------------------------------------
    Exact sixteen-field continuation after deleting Bottom-E. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterBottom_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterBottom_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterBottom_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterBottom_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
  M hPA inputs tail : clear implicits.

Theorem raw_afterImpElimination_of_afterBottomElimination : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpElimination
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hbottom hremaining.
  destruct hremaining. constructor; assumption.
Qed.

(** ------------------------------------------------------------------
    Certified core selection and growing-tail merge. *)

Definition RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectBottomContradictionCoreLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectBottomCaseContext_app_witnesses : forall witnesses,
  coqRestrictedPADirectBottomCaseContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectBottomCaseContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof (coqRestrictedPADirectImpECaseContext_app_witnesses witnesses)
    as himpE.
  unfold coqRestrictedPADirectImpECaseContext in himpE.
  cbn [List.app] in himpE.
  pose proof (f_equal (skipn 1) himpE) as hdeep.
  cbn [skipn] in hdeep.
  unfold coqRestrictedPADirectImpEDeepContext in hdeep.
  unfold coqRestrictedPADirectBottomCaseContext,
    coqRestrictedPADirectBottomDeepContext.
  cbn [List.app]. now rewrite hdeep.
Qed.

Theorem raw_bottomContradictionCoreLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      prefix witnesses suffix,
  RawCoqRestrictedPADirectBottomContradictionCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectBottomContradictionCoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix (root & hroot).
  rewrite coqRestrictedPADirectBottomCaseContext_app_witnesses in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectBottomCaseContext [])
      prefix witnesses suffix
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomAfterEndpointTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectBottomCaseContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterBottomElimination
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_remainingAfterImpEliminationCompiler_of_selectedBottomCore :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpEliminationStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (coreWitnesses & _ & hcore) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ coreWitnesses))
    as [suffix hremainingTail].
  exists (coreWitnesses ++ suffix).
  apply raw_afterImpElimination_of_afterBottomElimination.
  - apply raw_bottomRecursiveContradictionLawRoot_of_coreLawRoot.
    exact (raw_bottomContradictionCoreLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses coreWitnesses suffix hcore).
  - replace ((baseWitnesses ++ coreWitnesses) ++ suffix)
      with (baseWitnesses ++ (coreWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native endpoint with the Bottom-E target removed from the final
    continuation and its represented contradiction core exposed instead. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterBottomElimination
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
        RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
          M hPA inputs))))) ->
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
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpElimination
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth [hrecursive [hsplit [himpECore [hbottomCore hremaining]]]]].
  split; [exact horTruth |].
  split; [exact hrecursive |].
  split; [exact hsplit |].
  split; [exact himpECore |].
  exact
    (raw_remainingAfterImpEliminationCompiler_of_selectedBottomCore
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hbottomCore hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
