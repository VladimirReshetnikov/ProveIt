(**
  Remove the two conjunction-elimination truth coordinates from the refined
  post-And-I continuation.

  The aligned And-E producer now exports both projection-truth roots on one
  synchronized standard PA witness tail.  The genuinely remaining boundary
  therefore has exactly three semantic groups:

    - Or-E's recursive pair;
    - Ex-E's recursive pair; and
    - Eq-E's two recursive-child interfaces.

  The synchronized And-E pair is append-stable, so an independently growing
  three-field continuation may safely choose a later witness suffix.  This
  module never compares carrier codes of contexts selected by separate
  compilers.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
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
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionFiveFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction.

(** This record is deliberately child-only.  In particular, neither And-E
    projection truth nor any other parent-truth implication is retained. *)
Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionThreeFieldChildOnlyRemainder
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndIThreeChildOnly_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIThreeChildOnly_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIThreeChildOnly_equalityEliminationChildren :
    RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionThreeFieldChildOnlyRemainder
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionThreeFieldChildOnlyRemainder
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
  M hPA inputs : clear implicits.

(** Pointwise reconstruction makes the field correspondence explicit: the
    synchronized pair fills exactly the first two coordinates of the prior
    five-field record, and the residual record supplies the last three. *)
Theorem
    raw_fiveFieldChildOnlyRemainder_of_andEliminationTruthRoots_and_threeFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationDynamicTruthRoots
      M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionThreeFieldChildOnlyRemainder
      M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionFiveFieldChildOnlyRemainder
      M hPA inputs tail.
Proof.
  intros M hPA inputs tail [hleftTruth hrightTruth] hremaining.
  destruct hremaining as
    [horElimination hexistentialElimination hequalityChildren].
  constructor.
  - exact hleftTruth.
  - exact hrightTruth.
  - exact horElimination.
  - exact hexistentialElimination.
  - exact hequalityChildren.
Qed.

Corollary
    raw_fiveFieldChildOnlyRemainderAtWitnesses_of_andEliminationTruthRoots_and_threeFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCoqRestrictedPADirectAndEliminationDynamicTruthRootsAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
      M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
      M hPA inputs witnesses.
Proof.
  intros M hPA inputs witnesses handElimination hremaining.
  exact
    (raw_fiveFieldChildOnlyRemainder_of_andEliminationTruthRoots_and_threeFieldRemainder
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses))
      handElimination hremaining).
Qed.

(** Select the And-E pair first, run the residual compiler after that suffix,
    and use pair append-stability to carry both truth roots to the final
    common context. *)
Theorem
    raw_remainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler_of_andEliminationTruthRoots_and_threeFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationDynamicTruthRootsStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA inputs handElimination hremaining.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
      M hPA inputs)).
  apply (raw_coqStandardWitnessTailCompiler_apply
    (RawCoqRestrictedPADirectAndEliminationDynamicTruthRootsAtWitnesses
      M hPA inputs)
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyAtWitnesses
      M hPA inputs)).
  - exact
      (raw_andEliminationDynamicTruthRootsAtWitnesses_append_stable
        M hPA inputs).
  - exact handElimination.
  - intros baseWitnesses.
    destruct (hremaining baseWitnesses) as [suffix hremainingAt].
    exists suffix.
    intro handEliminationAt.
    exact
      (raw_fiveFieldChildOnlyRemainderAtWitnesses_of_andEliminationTruthRoots_and_threeFieldRemainder
        M hPA inputs (baseWitnesses ++ suffix)
        handEliminationAt hremainingAt).
Qed.

(** The aligned endpoint introduces only the two And-E literal-row resources
    eliminated at this refinement. *)
Corollary
    raw_remainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler_of_aligned_andElimination_rows_and_threeFieldRemainder :
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
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
      M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler
      M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural hleftResources hrightResources hremaining.
  apply
    raw_remainingAfterAndIntroductionFiveFieldChildOnlyStandardTailCompiler_of_andEliminationTruthRoots_and_threeFieldRemainder.
  - exact
      (raw_andEliminationDynamicTruthRootsStandardTailCompiler_of_aligned_append_concrete_rows
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hleftResources hrightResources).
  - exact hremaining.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration.
