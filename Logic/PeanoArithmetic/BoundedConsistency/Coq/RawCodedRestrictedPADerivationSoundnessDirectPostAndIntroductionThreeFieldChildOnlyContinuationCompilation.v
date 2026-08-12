(**
  Thread the exact three-field child-only boundary through the established
  post-And-I continuation and into the V2 rule-case compiler.

  This module deliberately leaves the Eq-E recursive-child compiler as one
  explicit premise.  It can therefore be checked independently of the Eq-E
  source implementation.  Once that source compiler is available, a tiny
  adapter discharges the premise by definitional conversion; no additional
  synchronization argument is required here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
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
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderCompilation
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlySameContextUnaryIntegration
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedContinuationIntegration.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationSemanticRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlySameContextUnaryIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedContinuationIntegration.

(** The Eq-E source compiler and the three-field wrapper unfold to the same
    child-pair predicate.  State the conversion once so all downstream exact
    endpoints can remain independent of that definitional detail. *)
Theorem
    raw_threeFieldEqualityEliminationChildren_standardTailCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs.
  exact
    (raw_equalityEliminationChildInterfaceRoots_standardTailCompiler
      M hPA inputs).
Qed.

(** Eleven literal rows cover the three exact Or-E/Ex-E roots, the And-E
    truth pair, and the six dynamic coordinates of the existing post-And-I
    endpoint.  Arithmetic recursive descent remains exactly the Eq-E child
    pair named in the last premise. *)
Theorem
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_eleven_rows_and_equalityChildren :
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
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural horEliminationResources hexBinderResources
    hexResultResources handLeftResources handRightResources
    horIntroductionResources hequalityReflexivityResources
    huniversalIntroductionResources huniversalEliminationResources
    hexistentialIntroductionResources hequalityEliminationResources
    hequalityChildren.
  apply
    (raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_six_rows_and_sevenFieldChildOnlyRemainder
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs).
  - exact hstructural.
  - exact horIntroductionResources.
  - exact hequalityReflexivityResources.
  - exact huniversalIntroductionResources.
  - exact huniversalEliminationResources.
  - exact hexistentialIntroductionResources.
  - exact hequalityEliminationResources.
  - apply
      raw_remainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler_of_fiveFieldRemainder.
    apply
      (raw_remainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler_of_aligned_andElimination_rows_and_threeFieldRemainder
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs).
    + exact hstructural.
    + exact handLeftResources.
    + exact handRightResources.
    + apply
        (raw_remainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler_of_aligned_orElimination_existentialElimination_rows_and_equalityChildren
          M hPA tail predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
          inputs).
      * exact hstructural.
      * exact horEliminationResources.
      * exact hexBinderResources.
      * exact hexResultResources.
      * exact hequalityChildren.
Qed.

(** Exact post-And-I endpoint: the Eq-E source theorem above removes the last
    arithmetic child premise from the generic eleven-row continuation. *)
Corollary
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_eleven_rows :
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
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural horEliminationResources hexBinderResources
    hexResultResources handLeftResources handRightResources
    horIntroductionResources hequalityReflexivityResources
    huniversalIntroductionResources huniversalEliminationResources
    hexistentialIntroductionResources hequalityEliminationResources.
  exact
    (raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_eleven_rows_and_equalityChildren
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
      hstructural horEliminationResources hexBinderResources
      hexResultResources handLeftResources handRightResources
      horIntroductionResources hequalityReflexivityResources
      huniversalIntroductionResources huniversalEliminationResources
      hexistentialIntroductionResources hequalityEliminationResources
      (raw_threeFieldEqualityEliminationChildren_standardTailCompiler
        M hPA inputs)).
Qed.

(** Add the And-I and excluded-middle rows and feed the compiled post-And-I
    continuation directly to the current strongest V2 assembler.  The six
    older frontier premises are unchanged and therefore remain explicit. *)
Corollary
    raw_remainingRuleCasesV2Compiler_of_aligned_thirteen_rows_equalityChildren_and_frontier :
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
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectExcludedMiddleCaseContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural handIntroductionResources hexcludedMiddleResources
    horEliminationResources hexBinderResources hexResultResources
    handLeftResources handRightResources horIntroductionResources
    hequalityReflexivityResources huniversalIntroductionResources
    huniversalEliminationResources hexistentialIntroductionResources
    hequalityEliminationResources hequalityChildren hassumption horTruth
    himpRecursive hsplit himpE hbottom.
  apply
    (raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_bottom_and_alignedAndIntroduction_excludedMiddle
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs).
  - exact hstructural.
  - exact handIntroductionResources.
  - exact hexcludedMiddleResources.
  - exact
      (raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_eleven_rows_and_equalityChildren
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
        hstructural horEliminationResources hexBinderResources
        hexResultResources handLeftResources handRightResources
        horIntroductionResources hequalityReflexivityResources
        huniversalIntroductionResources huniversalEliminationResources
        hexistentialIntroductionResources hequalityEliminationResources
        hequalityChildren).
  - exact hassumption.
  - exact horTruth.
  - exact himpRecursive.
  - exact hsplit.
  - exact himpE.
  - exact hbottom.
Qed.

(** Exact V2 endpoint: all three recursive Or-E/Ex-E/Eq-E packages have now
    been compiled, so only the pre-existing literal rows and frontier
    coordinates remain in the statement. *)
Corollary
    raw_remainingRuleCasesV2Compiler_of_aligned_thirteen_rows_and_frontier :
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
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectExcludedMiddleCaseContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural handIntroductionResources hexcludedMiddleResources
    horEliminationResources hexBinderResources hexResultResources
    handLeftResources handRightResources horIntroductionResources
    hequalityReflexivityResources huniversalIntroductionResources
    huniversalEliminationResources hexistentialIntroductionResources
    hequalityEliminationResources hassumption horTruth himpRecursive
    hsplit himpE hbottom.
  exact
    (raw_remainingRuleCasesV2Compiler_of_aligned_thirteen_rows_equalityChildren_and_frontier
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
      hstructural handIntroductionResources hexcludedMiddleResources
      horEliminationResources hexBinderResources hexResultResources
      handLeftResources handRightResources horIntroductionResources
      hequalityReflexivityResources huniversalIntroductionResources
      huniversalEliminationResources hexistentialIntroductionResources
      hequalityEliminationResources
      (raw_threeFieldEqualityEliminationChildren_standardTailCompiler
        M hPA inputs)
      hassumption horTruth himpRecursive hsplit himpE hbottom).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation.
