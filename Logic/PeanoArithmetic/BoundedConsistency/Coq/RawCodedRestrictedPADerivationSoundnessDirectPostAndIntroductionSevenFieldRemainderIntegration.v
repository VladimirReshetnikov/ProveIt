(**
  Assemble the post-And-I continuation from seven compiled coordinates.

  The historical post-And-I record has fourteen rule-level fields.  Earlier
  compilers now discharge exactly seven of them:

    - the recursive laws for And-E-left, And-E-right, and Or-I-right;
    - Or-I-right's dynamic-truth law;
    - the All-I eigenvariable law and All-E dynamic-truth law; and
    - equality reflexivity's atomic-truth law.

  This module exposes the complementary seven-field record.  Its fields are
  only the two And-E truth laws, all Or-E roots, the All-E recursive law, all
  Ex-I roots, all Ex-E roots, and all Eq-E roots.  No already compiled target
  is hidden in that residual boundary.

  Every component compiler may choose a different finite suffix of standard
  PA-axiom witnesses.  We combine them solely through the generic affine
  append-stability and continuation combinators.  In particular, the proof
  never compares, much less identifies, the model codes of two independently
  selected contexts.
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
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionAlignedTruthIntegration
  RawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldRemainderIntegration.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionAlignedTruthIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

(** ------------------------------------------------------------------
    The exact complementary seven-field continuation. *)

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndISeven_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndISeven_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
  M hPA inputs : clear implicits.

(** ------------------------------------------------------------------
    The seven complementary coordinates already supplied by compilers. *)

Definition RawCoqRestrictedPADirectUniversalKOnlyAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectUniversalKOnlySemanticRoots M hPA inputs
    (embedPAContext (map witnessedAxiom witnesses)).

(** The nesting mirrors the three existing compiler bundles: three unary
    recursive roots, two aligned truth roots, and two universal K-only roots.
    It therefore records exactly seven historical coordinates. *)
Definition RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  (RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses
      M hPA inputs witnesses /\
   (RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
        M hPA inputs witnesses /\
    RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
        M hPA inputs witnesses)) /\
  RawCoqRestrictedPADirectUniversalKOnlyAtWitnesses
    M hPA inputs witnesses.

Definition
    RawCoqRestrictedPADirectPostAndIResolvedSevenStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
      M hPA inputs).

Arguments RawCoqRestrictedPADirectUniversalKOnlyAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectPostAndIResolvedSevenStandardTailCompiler
  M hPA inputs : clear implicits.

(** The already synchronized unary triple remains valid after every later
    witness suffix.  This is merely the conjunction closure of the three
    rule-specific affine transport theorems. *)
Lemma raw_sameContextUnaryRecursiveRootsAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - exact
      (raw_andEliminationLeft_recursiveChildRoot_append_stable
        M hPA inputs).
  - apply raw_coqStandardWitnessTailAppendStable_and.
    + exact
        (raw_andEliminationRight_recursiveChildRoot_append_stable
          M hPA inputs).
    + exact
        (raw_orIntroductionRight_recursiveChildRoot_append_stable
          M hPA inputs).
Qed.

(** Both fields of the universal pair are represented local proofs under
    affine ready contexts.  The introduction transport was already exported
    with its stronger surrounding-prefix statement; elimination uses the
    shared ready-formula transport directly. *)
Lemma raw_universalKOnlyAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectUniversalKOnlyAtWitnesses M hPA inputs).
Proof.
  intros M hPA inputs witnesses suffix huniversal.
  destruct huniversal as [hintroduction helimination].
  constructor.
  - pose proof
      (raw_universalIntroductionEigenSemanticRoots_surround_witnessed_tail
        M hPA inputs [] witnesses suffix hintroduction) as htransported.
    cbn [List.app] in htransported.
    exact htransported.
  - unfold
      RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      in helimination |- *.
    pose proof
      (raw_directReadyFormulaRoot_surround_witnessed_tail
        M hPA inputs
        coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
        coqRestrictedPADirectUniversalEliminationReadyContext_app_witnesses
        [] witnesses suffix
        coqRestrictedPADirectUniversalEliminationDynamicTruthLawTemplate
        helimination) as htransported.
    cbn [List.app] in htransported.
    exact htransported.
Qed.

Lemma raw_postAndIResolvedSevenAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses.
  apply raw_coqStandardWitnessTailAppendStable_and.
  - apply raw_coqStandardWitnessTailAppendStable_and.
    + exact
        (raw_sameContextUnaryRecursiveRootsAtWitnesses_append_stable
          M hPA inputs).
    + apply raw_coqStandardWitnessTailAppendStable_and.
      * exact
          (raw_orIntroductionRightTruthAtWitnesses_append_stable
            M hPA inputs).
      * exact
          (raw_equalityReflexivityTruthAtWitnesses_append_stable
            M hPA inputs).
  - exact
      (raw_universalKOnlyAtWitnesses_append_stable M hPA inputs).
Qed.

(** Synchronize the seven compiled coordinates.  The intermediate pairings
    use the generic affine conjunction combinator, so each later compiler is
    run only after the suffixes selected before it. *)
Theorem raw_postAndIResolvedSevenStandardTailCompiler_of_compilers : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectPostAndIResolvedSevenStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hleft hright horRecursive horTruth hequalityTruth
    huniversal.
  pose proof
    (raw_sameContextUnaryRecursiveStandardTailCompiler_of_interfaces
      M hPA inputs hleft hright horRecursive) as hunary.
  pose proof
    (raw_postAndIntroductionTruthPairStandardTailCompiler
      M hPA inputs horTruth hequalityTruth) as htruthPair.
  pose proof
    (raw_coqStandardWitnessTailCompiler_and _ _
      (raw_sameContextUnaryRecursiveRootsAtWitnesses_append_stable
        M hPA inputs)
      hunary htruthPair) as hunaryAndTruth.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectUniversalKOnlyAtWitnesses
      M hPA inputs)) in huniversal.
  unfold
    RawCoqRestrictedPADirectPostAndIResolvedSevenStandardTailCompiler,
    RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses.
  exact
    (raw_coqStandardWitnessTailCompiler_and _ _
      (raw_coqStandardWitnessTailAppendStable_and _ _
        (raw_sameContextUnaryRecursiveRootsAtWitnesses_append_stable
          M hPA inputs)
        (raw_coqStandardWitnessTailAppendStable_and _ _
          (raw_orIntroductionRightTruthAtWitnesses_append_stable
            M hPA inputs)
          (raw_equalityReflexivityTruthAtWitnesses_append_stable
            M hPA inputs)))
      hunaryAndTruth huniversal).
Qed.

(** Pointwise reconstruction documents the exact partition of the historical
    record.  Destruction of the two bundles leaves fourteen assumptions in
    precisely the historical field order. *)
Theorem raw_afterAndIntroduction_of_resolvedSeven_and_sevenFieldRemainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix),
  RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
    M hPA inputs witnesses ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionSevenFieldRemainder
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs witnesses
    [[[hleftRecursive [hrightRecursive horRecursive]]
       [horTruth hequalityTruth]] huniversal] hremaining.
  destruct huniversal as [huniversalIntroduction huniversalEliminationTruth].
  destruct hremaining as
    [hleftTruth hrightTruth horElimination huniversalEliminationRecursive
      hexistentialIntroduction hexistentialElimination hequalityElimination].
  constructor; assumption.
Qed.

(** Compose the synchronized seven roots with the exact seven-field
    continuation.  The generic application combinator transports all seven
    earlier roots through the suffix selected by the residual compiler. *)
Theorem
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_compilers_and_sevenFieldRemainder
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hleft hright horRecursive horTruth hequalityTruth
    huniversal hremaining.
  pose proof
    (raw_postAndIResolvedSevenStandardTailCompiler_of_compilers
      M hPA inputs hleft hright horRecursive horTruth hequalityTruth
      huniversal) as hresolved.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
      M hPA inputs)).
  apply (raw_coqStandardWitnessTailCompiler_apply
    (RawCoqRestrictedPADirectPostAndIResolvedSevenAtWitnesses
      M hPA inputs)
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
      M hPA inputs)).
  - exact
      (raw_postAndIResolvedSevenAtWitnesses_append_stable M hPA inputs).
  - exact hresolved.
  - intros baseWitnesses.
    destruct (hremaining baseWitnesses) as [suffix hremainingAt].
    exists suffix.
    intro hresolvedAt.
    exact
      (raw_afterAndIntroduction_of_resolvedSeven_and_sevenFieldRemainder
        M hPA inputs (baseWitnesses ++ suffix)
        hresolvedAt hremainingAt).
Qed.

(** End-to-end aligned form.  One structural alignment is shared by the four
    aligned rule producers, while each literal resource remains attached to
    its own rule context. *)
Corollary
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_four_rows_interfaces_and_sevenFieldRemainder
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
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionSevenFieldStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
    hstructural horTruthResources hequalityTruthResources
    huniversalIntroductionResources huniversalEliminationResources
    hleft hright horRecursive hremaining.
  apply
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_compilers_and_sevenFieldRemainder.
  - exact hleft.
  - exact hright.
  - exact horRecursive.
  - exact
      (raw_orIntroductionRightDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural horTruthResources).
  - exact
      (raw_equalityReflexivityAtomicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hequalityTruthResources).
  - exact
      (raw_universalKOnlySemanticRootsStandardTailCompiler_of_aligned_append_concrete_rows
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural huniversalIntroductionResources
        huniversalEliminationResources).
  - exact hremaining.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionSevenFieldRemainderIntegration.
