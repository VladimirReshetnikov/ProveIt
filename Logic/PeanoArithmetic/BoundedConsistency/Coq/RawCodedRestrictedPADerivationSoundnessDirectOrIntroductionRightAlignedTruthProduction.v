(**
  Compile the Or-I-right dynamic truth law from aligned append evidence.

  The right-disjunction rule asks for the represented law

      formulaCode -> formulaTruth -> resultTruth.

  Its result is the displayed outer conclusion, so native structural
  alignment supplies [resultTruth] directly at the shared parent coordinates.
  Neither preceding antecedent is needed for that derivation.  We nevertheless
  introduce both antecedents with genuine represented K-combinator proofs;
  this is essential because meta-level weakening is unavailable for an opaque
  model-coded context.

  The resource premise remains literal: it contains only a mode-zero append
  trace and its concrete successor-row proof on each requested finite standard
  witness extension.  The generic append traversal, alignment rewrite, and
  iterated K compiler manufacture the public dynamic-truth root.
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
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedPALocalProofIteratedUnusedAntecedents.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction.

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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.

(** The complete Or-I-right ready context is a fixed finite prefix over its
    endpoint tail.  Deriving this from the already checked excluded-middle
    affine law avoids unfolding the large strong-step endpoint shell. *)
Lemma coqRestrictedPADirectOrIntroductionRightReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrIntroductionRightCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrIntroductionRightCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrIntroductionRightCaseTemplate witnesses).
Qed.

(** The append traversal is rerooted at the same displayed parent tuple used
    by Or-I-right.  The earlier And-I identification theorem is deliberately
    reused: both rule cases name this common outer-conclusion truth template,
    and no rule-specific semantic fact is needed here. *)
Lemma raw_orIntroductionRight_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectOrIntroductionRightResultTruthTemplate.
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

(** Growing-tail interface for the single Or-I-right dynamic-truth field.
    Keeping this interface independent of the fourteen-field continuation
    lets later integrations synchronize it with any other finite compiler by
    ordinary standard-witness-prefix concatenation. *)
Definition
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.

(** Compile parent truth from the literal append resources, then add the two
    unused antecedents in their source order.  The consequence proof and both
    K steps remain in exactly the same Or-I-right ready context. *)
Theorem
    raw_orIntroductionRightDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []) ->
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
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
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext [])
      coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable
      hresources) as hglobal.
  pose proof
    (raw_orIntroductionRight_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural) as hidentification.
  unfold
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler.
  intro baseWitnesses.
  destruct (hglobal baseWitnesses) as
    (suffix & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.

  assert (hresultTruth : RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionRightResultTruthTemplate)
      sourceRoot).
  {
    rewrite
      coqRestrictedPADirectOrIntroductionRightReadyContext_app_witnesses.
    rewrite rawTemplateContextCode_app_on_tail.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix))))
        (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext []))
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
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix))))
      [coqRestrictedPADirectOrIntroductionRightFormulaCodeTemplate;
       coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate]
      coqRestrictedPADirectOrIntroductionRightResultTruthTemplate
      sourceRoot hresultTruth) as [lawRoot hlaw].
  exists suffix, lawRoot.
  unfold coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate.
  cbn [coqTemplateImpChain] in hlaw.
  exact hlaw.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction.
