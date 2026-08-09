(**
  Downstream integration for the aligned And-I compiler.

  The aligned producer constructs the two genuine recursive-child roots and
  truth of their outer conjunction on one certified standard-PA witness tail.
  This file threads that selected three-root package through the existing
  post-And-I and excluded-middle affine continuations.  It deliberately sits
  downstream from both producers: no rule-case module needs to import native
  dynamic-truth machinery, and every context extension remains encapsulated
  by the already-audited growing-tail combinators.

  The first theorem removes And-I from the sixteen-field continuation after
  Bottom-E.  The two corollaries expose the resulting improvement at the V2
  dispatcher boundary, for either an explicitly selected Imp-I truth core or
  the stronger fixed-row split that produces that core.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedContinuationIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareCompletion.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

(** Compile the aligned And-I roots first, place the fourteen remaining rule
    cases after their chosen witness batch, and finally select the positive
    excluded-middle core.  Each merger transports represented proof roots;
    no equality between independently enlarged context codes is assumed. *)
Theorem
    raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction :
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
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural handAppend hexcluded hafterAnd.
  exact
    (raw_remainingAfterBottomEliminationCompiler_of_selectedExcludedCore
      M hPA inputs hexcluded
      (raw_remainingAfterExcludedMiddleCompiler_of_selectedAndICores
        M hPA inputs
        (raw_selectedAndIntroductionCoreTail_of_aligned_append_concrete_row
          M hPA tail predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned
          inputLevelNumeral inputs hstructural handAppend)
        hafterAnd)).
Qed.

(** Replace the selected excluded-middle core as well.  Its append compiler
    runs at the excluded-middle case prefix, independently of the And-I
    prefix; the downstream affine merger synchronizes the two finite witness
    batches before exposing the post-Bottom continuation. *)
Corollary
    raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction_and_excludedMiddle :
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
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterBottomEliminationStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural handAppend hexcludedAppend hafterAnd.
  exact
    (raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural handAppend
      (raw_selectedExcludedMiddleTruthCoreTail_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hexcludedAppend)
      hafterAnd).
Qed.

(** Expose the same reduction at the V2 dispatcher boundary.  All prefix
    cases and exact Bottom-E compilation are unchanged; only the former
    selected-And-I premise has been replaced by aligned append resources. *)
Corollary
    raw_remainingRuleCasesV2Compiler_of_selected_prefix_bottom_and_alignedAndIntroduction :
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
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpIntroductionTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectBottomAdmissibilityAwareCaseStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural handAppend hexcluded hafterAnd
    hassumption horTruth himpRecursive himpTruth himpE hbottom.
  exact
    (raw_remainingRuleCasesV2Compiler_of_selected_prefix_and_bottom
      M hPA inputs hassumption horTruth himpRecursive himpTruth
      himpE hbottom
      (raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned
        inputLevelNumeral inputs hstructural handAppend
        hexcluded hafterAnd)).
Qed.

(** The fixed-row split is the native Imp-I producer used by the present
    direct pipeline.  Keeping this corollary separate avoids immediately
    projecting its selected truth core and preserves the strongest premise
    available to later callback integration. *)
Corollary
    raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_bottom_and_alignedAndIntroduction :
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
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
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
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural handAppend hexcluded hafterAnd
    hassumption horTruth himpRecursive hsplit himpE hbottom.
  exact
    (raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_and_bottom
      M hPA inputs hassumption horTruth himpRecursive hsplit
      himpE hbottom
      (raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned
        inputLevelNumeral inputs hstructural handAppend
        hexcluded hafterAnd)).
Qed.

(** Current strongest V2 endpoint: neither excluded middle nor And-I is
    supplied as a selected semantic target.  Both are compiled from literal
    append/concrete-row resources under the one aligned structural input. *)
Corollary
    raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_bottom_and_alignedAndIntroduction_excludedMiddle :
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
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
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
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural handAppend hexcludedAppend hafterAnd
    hassumption horTruth himpRecursive hsplit himpE hbottom.
  exact
    (raw_remainingRuleCasesV2Compiler_of_fixedRowSplit_and_bottom
      M hPA inputs hassumption horTruth himpRecursive hsplit
      himpE hbottom
      (raw_remainingAfterBottomEliminationCompiler_of_alignedAndIntroduction_and_excludedMiddle
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural handAppend hexcludedAppend hafterAnd)).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedContinuationIntegration.
