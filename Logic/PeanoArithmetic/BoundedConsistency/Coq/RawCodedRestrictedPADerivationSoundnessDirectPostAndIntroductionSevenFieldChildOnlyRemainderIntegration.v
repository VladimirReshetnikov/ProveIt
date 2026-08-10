(**
  Remove the K-only truth coordinates from the seven-field post-And-I
  remainder.

  The existential-introduction and equality-elimination entries of the
  previous seven-field boundary each bundle genuine recursive-child
  interfaces with a dynamic-truth implication.  The latter implications are
  now supplied by the aligned parent-truth compiler.  This module therefore
  exposes the exact refined boundary: existential introduction retains its
  one child-interface law, while equality elimination retains its pair of
  child-interface laws.

  The two aligned truth compilers may choose a witness suffix independently
  of the refined continuation.  We synchronize them through the exported
  append-stability theorem for their K-only pair.  Consequently no proof
  compares the model codes of independently selected contexts.
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
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldRemainderIntegration.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.

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

(** ------------------------------------------------------------------
    Rule-level wrappers for the genuine child coordinates. *)

Definition
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRootAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).

Definition
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRootsAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
  M hPA inputs tail : clear implicits.

(** These two reconstruction lemmas isolate the only definitional knowledge
    about the original rule bundles.  Later record assembly can consequently
    treat both rules just like ordinary abstract coordinates. *)
Lemma raw_existentialIntroductionSemanticRoots_of_childInterface_and_dynamicTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRoot
      M hPA inputs tail ->
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
      M hPA inputs tail ->
  RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail.
Proof.
  intros M hPA inputs tail hchild htruth.
  unfold
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots,
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRoot,
    RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot.
  split; assumption.
Qed.

Lemma raw_equalityEliminationSemanticRoots_of_childInterfaces_and_dynamicTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
      M hPA inputs tail ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
      M hPA inputs tail ->
  RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail.
Proof.
  intros M hPA inputs tail hchildren htruth.
  unfold
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots,
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots,
    RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot.
  split; assumption.
Qed.

(** ------------------------------------------------------------------
    The refined seven-field boundary and its witness-indexed forms. *)

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldChildOnlyRemainder
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_existentialIntroductionChild :
    RawCoqRestrictedPADirectExistentialIntroductionChildInterfaceLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISevenChildOnly_equalityEliminationChildren :
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldChildOnlyRemainder
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldChildOnlyRemainder
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
  M hPA inputs : clear implicits.

(** Pointwise reconstruction of the previous seven-field boundary.  Notice
    that the K-only record supplies exactly the two truth halves and nothing
    about either recursive child operation. *)
Theorem
    raw_sevenFieldRemainder_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRoots
      M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldChildOnlyRemainder
      M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
      M hPA inputs tail.
Proof.
  intros M hPA inputs tail [hexistentialTruth hequalityTruth] hremaining.
  destruct hremaining as
    [hleftTruth hrightTruth horElimination huniversalEliminationRecursive
      hexistentialChild hexistentialElimination hequalityChildren].
  constructor.
  - exact hleftTruth.
  - exact hrightTruth.
  - exact horElimination.
  - exact huniversalEliminationRecursive.
  - exact
      (raw_existentialIntroductionSemanticRoots_of_childInterface_and_dynamicTruth
        M hPA inputs tail hexistentialChild hexistentialTruth).
  - exact hexistentialElimination.
  - exact
      (raw_equalityEliminationSemanticRoots_of_childInterfaces_and_dynamicTruth
        M hPA inputs tail hequalityChildren hequalityTruth).
Qed.

Corollary
    raw_sevenFieldRemainderAtWitnesses_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldAtWitnesses
      M hPA inputs witnesses.
Proof.
  intros M hPA inputs witnesses hkOnly hremaining.
  exact
    (raw_sevenFieldRemainder_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses))
      hkOnly hremaining).
Qed.

(** Synchronize the K-only pair with an independently growing refined
    continuation.  The application combinator invokes the continuation only
    after the pair's suffix has been selected, then transports the whole pair
    through the continuation suffix via its exported append-stability law. *)
Theorem
    raw_remainingAfterAndIntroductionSevenFieldStandardTailCompiler_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs hkOnly hremaining.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldAtWitnesses
      M hPA inputs)).
  apply (raw_coqStandardWitnessTailCompiler_apply
    (RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
      M hPA inputs)
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldAtWitnesses
      M hPA inputs)).
  - exact
      (raw_existentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses_append_stable
        M hPA inputs).
  - exact hkOnly.
  - intros baseWitnesses.
    destruct (hremaining baseWitnesses) as [suffix hremainingAt].
    exists suffix.
    intro hkOnlyAt.
    exact
      (raw_sevenFieldRemainderAtWitnesses_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder
        M hPA inputs (baseWitnesses ++ suffix)
        hkOnlyAt hremainingAt).
Qed.

(** The local aligned endpoint needs only the two literal append-row
    resources introduced in this refinement. *)
Corollary
    raw_remainingAfterAndIntroductionSevenFieldStandardTailCompiler_of_aligned_existentialIntroduction_equalityElimination_rows_and_childOnlyRemainder
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
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldChildOnlyStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural hexistentialResources hequalityResources hremaining.
  apply
    raw_remainingAfterAndIntroductionSevenFieldStandardTailCompiler_of_existentialIntroductionEqualityEliminationKOnly_and_childOnlyRemainder.
  - exact
      (raw_existentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler_of_aligned_append_concrete_rows
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hexistentialResources hequalityResources).
  - exact hremaining.
Qed.

(** Full post-And-I endpoint.  It extends the preceding four-row assembler
    with exactly the two new row resources while sharing the same structural
    alignment and arithmetic child interfaces. *)
Corollary
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_six_rows_interfaces_and_sevenFieldChildOnlyRemainder
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
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
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
    hleft hright horRecursive hremaining.
  apply
    (raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_four_rows_interfaces_and_sevenFieldRemainder
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs).
  - exact hstructural.
  - exact horTruthResources.
  - exact hequalityReflexivityResources.
  - exact huniversalIntroductionResources.
  - exact huniversalEliminationResources.
  - exact hleft.
  - exact hright.
  - exact horRecursive.
  - exact
      (raw_remainingAfterAndIntroductionSevenFieldStandardTailCompiler_of_aligned_existentialIntroduction_equalityElimination_rows_and_childOnlyRemainder
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hexistentialIntroductionResources
        hequalityEliminationResources hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
