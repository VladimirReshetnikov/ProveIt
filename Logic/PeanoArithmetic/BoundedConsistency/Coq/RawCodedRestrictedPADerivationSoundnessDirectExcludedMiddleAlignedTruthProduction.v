(**
  Compile the selected excluded-middle truth core from aligned append rows.

  Excluded middle has no recursive proof child.  Once native dynamic truth
  supplies truth of the displayed conclusion at the parent coordinates, the
  remaining core is only

      admissible(conclusion) -> truth(conclusion).

  A represented K-combinator inserts that unused admissibility antecedent.
  Consequently the older decision-split reduction is not needed at this
  boundary: the only proof-producing premise below is the literal mode-zero
  append trace and concrete row implication consumed by the generic global
  source compiler.
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
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleAlignedTruthProduction.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

(** The parent formula and live assignment coordinates are shared by every
    direct rule after the eight endpoint witnesses have been opened.  Thus
    the aligned mode-zero source used for And-I is definitionally the same
    conclusion-truth atom required by excluded middle. *)
Lemma raw_excludedMiddle_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate.
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

(** Select one finite witness batch, compile conclusion truth in the literal
    excluded-middle case context, and use a represented K proof to add the
    unused admissibility premise.  The selected-tail witness certificate is
    constructed independently from the proof roots, so there is no hidden
    equality between a native context code and the standard witness tail. *)
Theorem
    raw_selectedExcludedMiddleTruthCoreTail_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectExcludedMiddleCaseContext []) ->
  RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
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
      (coqRestrictedPADirectExcludedMiddleCaseContext [])
      coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable
      hresources) as hglobal.
  pose proof
    (raw_excludedMiddle_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural) as hidentification.
  destruct (hglobal []) as (witnesses & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.
  cbn [List.app] in hsourceRoot.

  assert (hconclusion : RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectExcludedMiddleCaseContext
          (embedPAContext (map witnessedAxiom witnesses))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
      sourceRoot).
  {
    rewrite coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses.
    rewrite rawTemplateContextCode_app_on_tail.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext (map witnessedAxiom witnesses)))
        (coqRestrictedPADirectExcludedMiddleCaseContext []))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          coqRestrictedPADirectAssumptionOuterConclusionTerm
          (ttVar 9) (ttVar 8))) sourceRoot) in hsourceRoot.
    rewrite hidentification in hsourceRoot.
    exact hsourceRoot.
  }

  destruct
    (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectExcludedMiddleCaseContext
        (embedPAContext (map witnessedAxiom witnesses)))
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate
      coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
      sourceRoot hconclusion) as [coreRoot hcore].
  exists witnesses. split.
  - exact (raw_directEmbeddedPAAxiomWitnessContext
      M hPA inputs witnesses).
  - exists coreRoot.
    unfold coqRestrictedPADirectExcludedMiddleTruthCoreTemplate.
    exact hcore.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleAlignedTruthProduction.
