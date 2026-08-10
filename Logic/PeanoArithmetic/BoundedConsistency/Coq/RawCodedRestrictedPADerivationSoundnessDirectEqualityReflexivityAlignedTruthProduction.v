(**
  Compile equality-reflexivity's atomic truth law from aligned parent truth.

  The reflexivity branch has no recursive derivation child.  Its sole
  semantic input is the implication

      formula-code -> truth(parent conclusion).

  Native dynamic truth already supplies the consequent at the common parent
  coordinates.  This module first transports that aligned global source into
  the exact reflexivity semantic context, then inserts the unused formula-code
  antecedent with a represented K proof.  The two stages are exposed
  separately so later rule-case assembly may reuse an independently obtained
  parent-truth compiler without depending on append traversal internals.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedPALocalProofIteratedUnusedAntecedents
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

(** The reflexivity semantic context is another instance of the common
    three-formula ready-context spine.  The case module's deep-context shape
    lemma exposes that spine without normalizing the eight endpoint binders. *)
Lemma coqRestrictedPADirectEqualityReflexivitySemanticContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectEqualityReflexivitySemanticContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectEqualityReflexivitySemanticContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectEqualityReflexivitySemanticContext,
    coqRestrictedPADirectEqualityReflexivityAdmissibleContext,
    coqRestrictedPADirectEqualityReflexivityCaseContext.
  rewrite !coqRestrictedPADirectEqualityReflexivity_deep_context_shape.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
      coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
      coqRestrictedPADirectEqualityReflexivityCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
      coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
      coqRestrictedPADirectEqualityReflexivityCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectEqualityReflexivityContextTruthTemplate
      coqRestrictedPADirectEqualityReflexivityAdmissibleTemplate
      coqRestrictedPADirectEqualityReflexivityCaseTemplate witnesses).
Qed.

(** Equality reflexivity concludes the same displayed parent formula as all
    other direct rules.  Therefore the mode-zero aligned source previously
    identified for And-I is definitionally the reflexivity conclusion-truth
    atom as well. *)
Lemma raw_equalityReflexivity_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate.
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
      coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate).
  exact
    (raw_andIntroduction_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural).
Qed.

(** A composable compiler for the consequent alone. *)
Definition
    RawCoqRestrictedPADirectEqualityReflexivityConclusionTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectEqualityReflexivitySemanticContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectEqualityReflexivityConclusionTruthStandardTailCompiler
  M hPA inputs : clear implicits.

(** The exact standard-tail interface consumed by the post-And-I record. *)
Definition
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
  M hPA inputs : clear implicits.

(** Insert the unused formula-code antecedent in an arbitrary translation and
    reflexivity tail.  Keeping this lemma independent of structural alignment
    makes the logical K step reusable by any future parent-truth producer. *)
Theorem raw_equalityReflexivityAtomicTruthLawRoot_of_conclusion_truth : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) tail root,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectEqualityReflexivitySemanticContext tail))
    (rawTemplateFormula translation
      coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate)
    root ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot
    M translation tail.
Proof.
  intros M hPA translation tail root htruth.
  destruct
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA translation
      (coqRestrictedPADirectEqualityReflexivitySemanticContext tail)
      [coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate]
      coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate
      root htruth) as [lawRoot hlaw].
  exists lawRoot.
  cbn [coqTemplateImpChain] in hlaw.
  rewrite rawTemplateFormula_imp in hlaw.
  exact hlaw.
Qed.

(** Lift any composable parent-truth compiler to the exact reflexivity law.
    The selected suffix is preserved verbatim, which is essential when this
    compiler is sequenced with the other twenty-two rule-case fields. *)
Theorem
    raw_equalityReflexivityAtomicTruthStandardTailCompiler_of_conclusion_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectEqualityReflexivityConclusionTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs htruth baseWitnesses.
  destruct (htruth baseWitnesses) as (suffix & root & hroot).
  exists suffix.
  exact
    (raw_equalityReflexivityAtomicTruthLawRoot_of_conclusion_truth
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix)))
      root hroot).
Qed.

(** Compile aligned parent truth in the literal reflexivity semantic context.
    The append producer may extend each incoming witness prefix; both the
    global source and its identification with conclusion truth remain on that
    same extension. *)
Theorem
    raw_equalityReflexivityConclusionTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectEqualityReflexivityConclusionTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  pose proof
    (raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectEqualityReflexivitySemanticContext [])
      coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable
      hresources) as hglobal.
  pose proof
    (raw_equalityReflexivity_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural) as hidentification.
  intro baseWitnesses.
  destruct (hglobal baseWitnesses) as
    (suffix & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.
  exists suffix, sourceRoot.
  rewrite
    coqRestrictedPADirectEqualityReflexivitySemanticContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix))))
        (coqRestrictedPADirectEqualityReflexivitySemanticContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate)
      sourceRoot).
  change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix))))
        (coqRestrictedPADirectEqualityReflexivitySemanticContext []))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          coqRestrictedPADirectAssumptionOuterConclusionTerm
          (ttVar 9) (ttVar 8))) sourceRoot) in hsourceRoot.
  rewrite hidentification in hsourceRoot.
  exact hsourceRoot.
Qed.

(** End-to-end reflexivity compiler: literal append/concrete-row resources
    suffice for the exact atomic implication field. *)
Corollary
    raw_equalityReflexivityAtomicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectEqualityReflexivitySemanticContext []) ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_equalityReflexivityAtomicTruthStandardTailCompiler_of_conclusion_truth.
  exact
    (raw_equalityReflexivityConclusionTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction.
