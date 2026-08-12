(**
  Specialize the native-closure V2 continuation at the Or-I-left
  projection.  The literal row family is kept as a small record so this
  adapter does not repeat the long thirteen-row telescope at every call
  site.  The dynamic Or law is intentionally still explicit: the closure
  package identifies the selected leaf, but it does not manufacture the
  semantic Tarski law.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation
  RawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureProjection
  RawCodedTemplateNumeralParameters
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyContinuationCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureProjection.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureContinuation.

(** The thirteen literal append rows used by the exact V2 assembler. *)
Record RawCoqRestrictedPADirectV2LiteralRows
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  raw_v2_literal_and_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []);
  raw_v2_literal_excluded_middle :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectExcludedMiddleCaseContext []);
  raw_v2_literal_or_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectOrEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrEliminationReadyContext []);
  raw_v2_literal_existential_elimination_binder :
    RawCoqRestrictedPADirectModeOneAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationBinderContextTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []);
  raw_v2_literal_existential_elimination_result :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectExistentialEliminationResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialEliminationReadyContext []);
  raw_v2_literal_and_elimination_left :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []);
  raw_v2_literal_and_elimination_right :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []);
  raw_v2_literal_or_introduction_right :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []);
  raw_v2_literal_equality_reflexivity :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []);
  raw_v2_literal_universal_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []);
  raw_v2_literal_universal_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []);
  raw_v2_literal_existential_introduction :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []);
  raw_v2_literal_equality_elimination :
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext [])
}.

Arguments RawCoqRestrictedPADirectV2LiteralRows M hPA inputs : clear implicits.

(**
  The native closure supplies Assumption internally, and the projection
  theorem supplies Or-I-left from the explicit empty-tail dynamic law.  The
  underlying four-frontier endpoint then leaves only the three Imp fields.
*)
Theorem
    raw_remainingRuleCasesV2Compiler_of_literalRows_and_threeImpFrontiers_of_nativeClosureAtFor_of_dynamicLawAtEmpty :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    (tail : nat -> M) predecessorLevel' baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel' baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
    M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence contextTruth conclusionTruth inputs ->
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel' baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  RawCoqRestrictedPADirectV2LiteralRows M hPA inputs ->
  RawCoqRestrictedPADirectDynamicTruthLawRootAtEmpty M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    tail predecessorLevel' baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hclosure hstructural hrows hdynamic himpRecursive hsplit himpE.
  destruct hrows as
    (handIntroductionResources & hexcludedMiddleResources
     & horEliminationResources & hexBinderResources & hexResultResources
     & handLeftResources & handRightResources & horIntroductionResources
     & hequalityReflexivityResources & huniversalIntroductionResources
     & huniversalEliminationResources & hexistentialIntroductionResources
     & hequalityEliminationResources).
  pose proof
    (raw_selectedOrIntroductionLeftTruthTail_of_nativeDirectTruthInputsWithClosureAtFor_of_dynamicLawAtEmpty
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence contextTruth conclusionTruth inputs hclosure hdynamic)
    as horTruth.
  eapply
    (raw_remainingRuleCasesV2Compiler_of_aligned_thirteen_rows_and_four_frontiers_of_nativeClosureAtFor
      M hPA parameters contextTruth conclusionTruth currentGlobalSigma
      currentGlobalPi predecessorLevel nextSigmaEvidence tail predecessorLevel'
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs).
  - exact hclosure.
  - exact hstructural.
  - exact handIntroductionResources.
  - exact hexcludedMiddleResources.
  - exact horEliminationResources.
  - exact hexBinderResources.
  - exact hexResultResources.
  - exact handLeftResources.
  - exact handRightResources.
  - exact horIntroductionResources.
  - exact hequalityReflexivityResources.
  - exact huniversalIntroductionResources.
  - exact huniversalEliminationResources.
  - exact hexistentialIntroductionResources.
  - exact hequalityEliminationResources.
  - exact horTruth.
  - exact himpRecursive.
  - exact hsplit.
  - exact himpE.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureContinuation.
