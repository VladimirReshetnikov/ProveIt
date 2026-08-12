(**
  A named residual package for the exact V2 rule-case assembler.

  The V2 continuation has a deliberately concrete interface: thirteen
  append-row compilers and six already-established frontier tails.  Keeping
  those twenty-one coordinates as a record makes the remaining construction
  compositional.  In particular, later row producers can fill this record
  without having to repeat the long endpoint signature, while the adapter
  below remains a transparent application of the exact V2 theorem.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation
  CodedProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
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
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation.
Import PABoundedCodedProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.

Record
  RawCoqRestrictedPADirectRemainingRuleCasesV2RowResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  raw_v2_row_and_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []);
  raw_v2_row_excluded_middle :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectExcludedMiddleCaseContext []);
  raw_v2_row_or_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []);
  raw_v2_row_existential_elimination_binder :
    RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []);
  raw_v2_row_existential_elimination_result :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []);
  raw_v2_row_and_elimination_left :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []);
  raw_v2_row_and_elimination_right :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []);
  raw_v2_row_or_introduction_right :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []);
  raw_v2_row_equality_reflexivity :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []);
  raw_v2_row_universal_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []);
  raw_v2_row_universal_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []);
  raw_v2_row_existential_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []);
  raw_v2_row_equality_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []);
  raw_v2_frontier_assumption :
    RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs;
  raw_v2_frontier_or_introduction_left :
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs;
  raw_v2_frontier_imp_introduction_recursive :
    RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs;
  raw_v2_frontier_imp_introduction_fixed_row_split :
    RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
      M hPA inputs;
  raw_v2_frontier_imp_elimination :
    RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs;
  raw_v2_frontier_bottom :
    RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
      M hPA inputs
}.

(**
  Unpack the named package and invoke the exact endpoint.  No proof
  irrelevance, rewriting, or additional semantic assumption is hidden here:
  the structural alignment remains an explicit premise, exactly as it is in
  the underlying compiler theorem.
*)
Theorem
    raw_remainingRuleCasesV2Compiler_of_aligned_row_resource_package :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2RowResources
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural hresources.
  destruct hresources.
  eapply
    (raw_remainingRuleCasesV2Compiler_of_aligned_thirteen_rows_and_frontier
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs).
  all: assumption.
Qed.
