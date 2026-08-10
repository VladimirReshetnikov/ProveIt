(**
  Fill two post-And-I truth holes from aligned append resources.

  After the And-I case has been removed, the remaining rule-case record still
  contains fourteen fields.  Two of those fields are parent-truth laws rather
  than genuine recursive-child obligations:

    - Or-I-right's dynamic-truth implication; and
    - equality reflexivity's atomic-truth implication.

  Their aligned producers are independent standard-witness-tail compilers and
  may therefore select different finite suffixes.  This module synchronizes
  those suffixes without identifying their context codes.  Append-stability
  transports the first proof across the suffix chosen by the second compiler;
  the resulting pair is then transported once more across the suffix chosen
  by a residual continuation with precisely these two holes.

  The context transport is entirely generic.  Each rule contributes only its
  affine equation saying that its ready context consists of a fixed prefix
  followed by the embedded standard-PA witnesses.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionAlignedTruthIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityAlignedTruthProduction.

(** Exact predicates at a concrete standard-witness batch.  Naming these
    predicates keeps the synchronization combinators independent of the
    details of the two rule contexts. *)
Definition RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext (map witnessedAxiom witnesses)).

Definition RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
  M hPA inputs witnesses : clear implicits.

(** The residual compiler is allowed to use exactly the synchronized pair of
    missing roots.  It may select a further suffix before assembling all
    fourteen post-And-I fields.  Stating the two holes as one conjunction is
    what lets the generic continuation combinator transport them together. *)
Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionTwoTruthHolesStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      (RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
          M hPA inputs witnesses /\
       RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
          M hPA inputs witnesses) ->
      RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
        M hPA inputs witnesses).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionTwoTruthHolesStandardTailCompiler
  M hPA inputs : clear implicits.

(** Or-I-right's exact represented root is stable under every later standard
    witness suffix.  The rule-specific work is only its affine context law;
    the represented proof transport itself is shared. *)
Theorem raw_orIntroductionRightTruthAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses,
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
      coqRestrictedPADirectOrIntroductionRightReadyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionRightDynamicTruthLawTemplate)).
Qed.

(** The same generic transport applies to the explicitly constructed
    implication code used by equality reflexivity; the generic theorem does
    not require its conclusion to be syntactically a translated template. *)
Theorem raw_equalityReflexivityTruthAtWitnesses_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses,
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectEqualityReflexivitySemanticContext
      coqRestrictedPADirectEqualityReflexivitySemanticContext_app_witnesses
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityReflexivityFormulaCodeTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPADirectEqualityReflexivityConclusionTruthTemplate))).
Qed.

(** Synchronize the independently selected Or-I-right and reflexivity tails.
    The conjunction combinator runs the reflexivity compiler after the suffix
    selected by Or-I-right, then transports the Or-I-right root across that
    second suffix. *)
Theorem raw_postAndIntroductionTruthPairStandardTailCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
          M hPA inputs witnesses /\
      RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
          M hPA inputs witnesses).
Proof.
  intros M hPA inputs horIntroductionRight hequalityReflexivity.
  apply (raw_coqStandardWitnessTailCompiler_and
    (RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
      M hPA inputs)
    (RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
      M hPA inputs)).
  - exact (raw_orIntroductionRightTruthAtWitnesses_append_stable
      M hPA inputs).
  - exact horIntroductionRight.
  - exact hequalityReflexivity.
Qed.

(** Fill the two holes and then run the residual continuation.  The pair must
    be append-stable because the continuation may choose a third suffix; this
    is the subtle synchronization step that prevents accidental comparison of
    independently generated model-coded contexts. *)
Theorem
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_two_truth_compilers_and_continuation
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionTwoTruthHolesStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs horIntroductionRight hequalityReflexivity
    hcontinuation.
  change (RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
      M hPA inputs)).
  apply (raw_coqStandardWitnessTailCompiler_apply
    (fun witnesses =>
      RawCoqRestrictedPADirectOrIntroductionRightTruthAtWitnesses
          M hPA inputs witnesses /\
      RawCoqRestrictedPADirectEqualityReflexivityTruthAtWitnesses
          M hPA inputs witnesses)
    (RawCoqRestrictedPADirectRemainingAfterAndIntroductionAtWitnesses
      M hPA inputs)).
  - apply raw_coqStandardWitnessTailAppendStable_and.
    + exact (raw_orIntroductionRightTruthAtWitnesses_append_stable
        M hPA inputs).
    + exact (raw_equalityReflexivityTruthAtWitnesses_append_stable
        M hPA inputs).
  - exact (raw_postAndIntroductionTruthPairStandardTailCompiler
      M hPA inputs horIntroductionRight hequalityReflexivity).
  - exact hcontinuation.
Qed.

(** End-to-end removal of both selected truth fields.  One structural
    alignment witnesses both identifications with parent truth, while the two
    literal append/concrete-row resources target their different ready
    contexts.  The residual continuation contains only the other post-And-I
    obligations. *)
Corollary
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_aligned_orIntroductionRight_equalityReflexivity_and_continuation
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
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionTwoTruthHolesStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural horResources hequalityResources hcontinuation.
  apply
    raw_remainingAfterAndIntroductionStandardTailCompiler_of_two_truth_compilers_and_continuation.
  - exact
      (raw_orIntroductionRightDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural horResources).
  - exact
      (raw_equalityReflexivityAtomicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hequalityResources).
  - exact hcontinuation.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectPostAndIntroductionAlignedTruthIntegration.
