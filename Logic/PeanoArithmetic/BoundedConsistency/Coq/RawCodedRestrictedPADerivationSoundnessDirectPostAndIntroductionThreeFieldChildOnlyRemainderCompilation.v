(**
  Compile the final three child-only coordinates below And introduction.

  Or elimination and existential elimination already provide exact semantic
  root compilers.  Equality elimination contributes only its two recursive
  child interfaces here: its dynamic-truth half is synchronized later with
  the existential-introduction truth half.  The three independently selected
  witness suffixes therefore have to be put on one common standard-PA tail.

  We select the Or-E suffix first, then the Ex-E suffix, and finally the Eq-E
  suffix.  Only evidence selected before the last suffix needs transport.
  Consequently this module is independent of the still more specific Eq-E
  source compiler: any compiler of the exact child-pair predicate can fill the
  final premise.
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
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationSemanticRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderCompilation.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationSemanticRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationSemanticRootsCompilation.

(** This private-to-the-three-field-boundary wrapper is intentionally named
    differently from the Eq-E compiler's public witness-indexed predicate.
    Both unfold to the same exact pair of child interfaces, so the finished
    Eq-E compiler can be supplied by conversion without an adapter theorem. *)
Definition
    RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
  M hPA inputs : clear implicits.

(** The pointwise constructor records the exact coordinate correspondence.
    Keeping it separate from tail synchronization prevents definitional
    unfolding of the large semantic-root records in the compiler proof. *)
Theorem
    raw_threeFieldChildOnlyRemainder_of_orElimination_existentialElimination_equalityChildren :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail ->
  RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectEqualityEliminationChildInterfaceRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionThreeFieldChildOnlyRemainder
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hor hex heq.
  constructor; assumption.
Qed.

Corollary
    raw_threeFieldChildOnlyRemainderAtWitnesses_of_orElimination_existentialElimination_equalityChildren :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
    M hPA inputs witnesses ->
  RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
    M hPA inputs witnesses ->
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenAtWitnesses
    M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
    M hPA inputs witnesses.
Proof.
  intros M hPA inputs witnesses hor hex heq.
  exact
    (raw_threeFieldChildOnlyRemainder_of_orElimination_existentialElimination_equalityChildren
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses))
      hor hex heq).
Qed.

(** Synchronize three independently growing compilers.  Eq-E is selected
    last, hence its child pair need not be transported in this proof. *)
Theorem
    raw_remainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler_of_orElimination_existentialElimination_equalityChildren :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrEliminationSemanticRootsStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectExistentialEliminationSemanticRootsStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs horCompiler hexCompiler heqCompiler.
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
        M hPA inputs)
      (RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
        M hPA inputs)
      (raw_orEliminationSemanticRootsAtWitnesses_append_stable
        M hPA inputs)
      horCompiler hexCompiler) as horExCompiler.
  pose proof
    (raw_coqStandardWitnessTailCompiler_and
      (fun witnesses =>
        RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
            M hPA inputs witnesses /\
        RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
            M hPA inputs witnesses)
      (RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenAtWitnesses
        M hPA inputs)
      (raw_coqStandardWitnessTailAppendStable_and
        (RawCoqRestrictedPADirectOrEliminationSemanticRootsAtWitnesses
          M hPA inputs)
        (RawCoqRestrictedPADirectExistentialEliminationSemanticRootsAtWitnesses
          M hPA inputs)
        (raw_orEliminationSemanticRootsAtWitnesses_append_stable
          M hPA inputs)
        (raw_existentialEliminationSemanticRootsAtWitnesses_append_stable
          M hPA inputs))
      horExCompiler heqCompiler) as hallCompiler.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyAtWitnesses
      M hPA inputs)).
  intros baseWitnesses.
  destruct (hallCompiler baseWitnesses)
    as [suffix [[horAt hexAt] heqAt]].
  exists suffix.
  exact
    (raw_threeFieldChildOnlyRemainderAtWitnesses_of_orElimination_existentialElimination_equalityChildren
      M hPA inputs (baseWitnesses ++ suffix)
      horAt hexAt heqAt).
Qed.

(** Resolve the Or-E and Ex-E compilers from their exact aligned literal-row
    endpoints.  Equality children remain as the sole arithmetic premise; the
    dedicated Eq-E source compiler will discharge precisely this premise. *)
Corollary
    raw_remainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler_of_aligned_orElimination_existentialElimination_rows_and_equalityChildren :
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
  RawCoqRestrictedPADirectThreeFieldEqualityEliminationChildrenStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural horResources hexBinderResources hexResultResources
    hequalityChildren.
  apply
    raw_remainingAfterAndIntroductionThreeFieldChildOnlyStandardTailCompiler_of_orElimination_existentialElimination_equalityChildren.
  - exact
      (raw_orEliminationSemanticRoots_standardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural horResources).
  - exact
      (raw_existentialEliminationSemanticRoots_standardTailCompiler_of_aligned_append_concrete_rows
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hexBinderResources hexResultResources).
  - exact hequalityChildren.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionThreeFieldChildOnlyRemainderCompilation.
