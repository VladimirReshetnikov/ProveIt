(**
  Compile the remaining K-only existential-introduction and
  equality-elimination truth laws from aligned parent truth.

  The genuine recursive-child operations for these rules remain separate
  semantic obligations.  Their dynamic-truth fields, however, conclude the
  common outer conclusion and inspect their displayed constructor fields
  only as antecedents.  We therefore compile the aligned mode-zero parent
  source in each rule's exact ready context and add those antecedents with
  represented K-combinator proofs.  The generic parent-consequence and
  iterated-antecedent machinery lives in the universal-rules production
  module and is deliberately reused here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedPALocalProofIteratedUnusedAntecedents
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

(** ------------------------------------------------------------------
    Exact affine ready contexts. *)

Lemma coqRestrictedPADirectExistentialIntroductionReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialIntroductionCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialIntroductionCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectExistentialIntroductionOuterContextTruthTemplate
      coqRestrictedPADirectExistentialIntroductionDeepAdmissibleTemplate
      coqRestrictedPADirectExistentialIntroductionCaseTemplate witnesses).
Qed.

Lemma coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepEqualityEliminationReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
      coqRestrictedPADirectEqualityEliminationCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
      coqRestrictedPADirectEqualityEliminationCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectEqualityEliminationOuterContextTruthTemplate
      coqRestrictedPADirectEqualityEliminationDeepAdmissibleTemplate
      coqRestrictedPADirectEqualityEliminationCaseTemplate witnesses).
Qed.

(** Both rule-specific consequents are definitionally the shared outer
    conclusion truth selected by aligned structural inputs. *)
Lemma raw_existentialIntroduction_mode_zero_parent_source_aligned : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  change (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  exact
    (raw_andIntroduction_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
Qed.

Lemma raw_equalityElimination_mode_zero_parent_source_aligned : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  change (rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectAssumptionOuterConclusionTruthTemplate).
  exact
    (raw_andIntroduction_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
Qed.

(** ------------------------------------------------------------------
    Exact standalone consequence and dynamic-law compilers. *)

Definition
    RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRootAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext tail).

Definition RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRootAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext tail).

Arguments RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectExistentialIntroductionResultTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
    coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate.

Definition
    RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
      M hPA inputs).

Definition
    RawCoqRestrictedPADirectEqualityEliminationResultTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
    coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate.

Definition
    RawCoqRestrictedPADirectEqualityEliminationDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionResultTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectEqualityEliminationResultTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_existentialIntroductionDynamicTruthStandardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialIntroductionResultTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      [coqRestrictedPADirectExistentialIntroductionFormulaCodeTemplate;
       coqRestrictedPADirectExistentialIntroductionSubstitutionTemplate;
       coqRestrictedPADirectExistentialIntroductionChildTruthTemplate]
      coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate
      htruth) as hlaws.
  intros baseWitnesses.
  destruct (hlaws baseWitnesses) as (suffix & root & hroot).
  exists suffix, root.
  cbn [coqTemplateImpChain] in hroot.
  exact hroot.
Qed.

Theorem
    raw_equalityEliminationDynamicTruthStandardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectEqualityEliminationResultTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      [coqRestrictedPADirectEqualityEliminationTargetSubstitutionTemplate;
       coqRestrictedPADirectEqualityEliminationEqualityFormulaCodeTemplate;
       coqRestrictedPADirectEqualityEliminationSourceSubstitutionTemplate;
       coqRestrictedPADirectEqualityEliminationEqualityChildTruthTemplate;
       coqRestrictedPADirectEqualityEliminationMotiveChildTruthTemplate]
      coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate
      htruth) as hlaws.
  intros baseWitnesses.
  destruct (hlaws baseWitnesses) as (suffix & root & hroot).
  exists suffix, root.
  cbn [coqTemplateImpChain] in hroot.
  exact hroot.
Qed.

Theorem
    raw_existentialIntroductionResultTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectExistentialIntroductionResultTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_parent_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      coqRestrictedPADirectExistentialIntroductionOuterConclusionTruthTemplate
      coqRestrictedPADirectExistentialIntroductionReadyContext_app_witnesses
      (raw_existentialIntroduction_mode_zero_parent_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

Corollary
    raw_existentialIntroductionDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_existentialIntroductionDynamicTruthStandardTailCompiler_of_result_truth.
  exact
    (raw_existentialIntroductionResultTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

Theorem
    raw_equalityEliminationResultTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectEqualityEliminationResultTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_parent_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      coqRestrictedPADirectEqualityEliminationOuterConclusionTruthTemplate
      coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
      (raw_equalityElimination_mode_zero_parent_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

Corollary
    raw_equalityEliminationDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_equalityEliminationDynamicTruthStandardTailCompiler_of_result_truth.
  exact
    (raw_equalityEliminationResultTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

(** ------------------------------------------------------------------
    Synchronize both independently growing dynamic-truth compilers. *)

Record
    RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectKOnly_existentialIntroductionTruth :
    RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectKOnly_equalityEliminationTruth :
    RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRoots
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRoots
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.

Definition
    RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Lemma
    raw_existentialIntroductionDynamicTruthLawRoot_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
    M hPA inputs
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
    M hPA inputs
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix hroot.
  exact
    (raw_directReadyFormulaRoot_surround_witnessed_tail
      M hPA inputs
      coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext
      coqRestrictedPADirectExistentialIntroductionReadyContext_app_witnesses
      prefix witnesses suffix
      coqRestrictedPADirectExistentialIntroductionDynamicTruthLawTemplate
      hroot).
Qed.

(** Equality elimination has the same affine ready-context shape.  Exporting
    both transports keeps later residual-record integrations independent of
    either rule's internal context definition. *)
Lemma
    raw_equalityEliminationDynamicTruthLawRoot_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
    M hPA inputs
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
    M hPA inputs
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix hroot.
  exact
    (raw_directReadyFormulaRoot_surround_witnessed_tail
      M hPA inputs
      coqRestrictedPADirectStrongStepEqualityEliminationReadyContext
      coqRestrictedPADirectEqualityEliminationReadyContext_app_witnesses
      prefix witnesses suffix
      coqRestrictedPADirectEqualityEliminationDynamicTruthLawTemplate
      hroot).
Qed.

(** Once synchronized, the K-only pair survives every later standard-witness
    suffix.  This is the reusable interface expected by continuation
    composition; downstream modules need not repeat either affine proof. *)
Lemma
    raw_existentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses_append_stable
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs witnesses suffix hroots.
  destruct hroots as [hexistential hequality].
  constructor.
  - pose proof
      (raw_existentialIntroductionDynamicTruthLawRoot_surround_witnessed_tail
        M hPA inputs [] witnesses suffix hexistential) as htransported.
    cbn [List.app] in htransported.
    exact htransported.
  - pose proof
      (raw_equalityEliminationDynamicTruthLawRoot_surround_witnessed_tail
        M hPA inputs [] witnesses suffix hequality) as htransported.
    cbn [List.app] in htransported.
    exact htransported.
Qed.

Theorem
    raw_existentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler_of_standalone :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityEliminationDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hexistential hequality.
  pose proof
    (raw_standardWitnessTailCompiler_pair
      (RawCoqRestrictedPADirectExistentialIntroductionDynamicTruthLawRoot
        M hPA inputs)
      (RawCoqRestrictedPADirectEqualityEliminationDynamicTruthLawRoot
        M hPA inputs)
      (raw_existentialIntroductionDynamicTruthLawRoot_surround_witnessed_tail
        M hPA inputs)
      hexistential hequality) as hpair.
  intros baseWitnesses.
  destruct (hpair baseWitnesses) as
    (suffix & hexistentialRoot & hequalityRoot).
  exists suffix.
  constructor; assumption.
Qed.

Corollary
    raw_existentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler_of_aligned_append_concrete_rows :
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
      (coqRestrictedPADirectStrongStepExistentialIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepEqualityEliminationReadyContext []) ->
  RawCoqRestrictedPADirectExistentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hexistentialResources hequalityResources.
  apply
    raw_existentialIntroductionEqualityEliminationKOnlyRootsStandardTailCompiler_of_standalone.
  - exact
      (raw_existentialIntroductionDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hexistentialResources).
  - exact
      (raw_equalityEliminationDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hequalityResources).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionEqualityEliminationAlignedTruthProduction.
