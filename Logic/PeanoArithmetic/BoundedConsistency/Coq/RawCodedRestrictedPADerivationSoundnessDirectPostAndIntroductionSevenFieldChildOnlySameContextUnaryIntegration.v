(**
  Discharge the three same-context unary child hypotheses at the aligned
  post-And-I boundary.

  The opened-coverage compiler supplies And-E-left, And-E-right, and
  Or-I-right unconditionally on standard witness tails.  This thin layer
  feeds those roots to the existing six-row endpoint and deliberately leaves
  its exact seven-field child-only residual unchanged.
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
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageCompilation.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlySameContextUnaryIntegration.

Import ListNotations.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageCompilation.

(** This is the preceding aligned endpoint with precisely its three explicit
    same-context unary child-interface premises removed. *)
Theorem
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_six_rows_and_sevenFieldChildOnlyRemainder
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural horTruthResources hequalityReflexivityResources
    huniversalIntroductionResources huniversalEliminationResources
    hexistentialIntroductionResources hequalityEliminationResources
    hremaining.
  apply
    (raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_six_rows_interfaces_and_sevenFieldChildOnlyRemainder
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs).
  - exact hstructural.
  - exact horTruthResources.
  - exact hequalityReflexivityResources.
  - exact huniversalIntroductionResources.
  - exact huniversalEliminationResources.
  - exact hexistentialIntroductionResources.
  - exact hequalityEliminationResources.
  - apply raw_andEliminationLeftChildInterface_standardTailCompiler.
  - apply raw_andEliminationRightChildInterface_standardTailCompiler.
  - apply raw_orIntroductionRightChildInterface_standardTailCompiler.
  - exact hremaining.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlySameContextUnaryIntegration.
