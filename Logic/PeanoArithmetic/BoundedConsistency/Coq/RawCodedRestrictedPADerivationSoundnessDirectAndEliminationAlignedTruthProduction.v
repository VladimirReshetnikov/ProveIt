(**
  Compile both conjunction-elimination dynamic-truth laws from aligned
  append evidence.

  Unlike the K-only rules whose consequents are the outer conclusion, And-E
  returns one of the two displayed conjunct codes.  Native alignment already
  identifies the shared mode-zero source at *arbitrary* rule-local root
  terms.  We exploit that stronger reroot theorem at [#6] for And-E-left and
  [#5] for And-E-right, then introduce the formula-code and conjunction-truth
  antecedents with represented K proofs.

  The implementation first generalizes the existing parent-only append
  compiler to arbitrary root terms, subject to its honest syntactic row
  stability premise.  A small rule index then shares all remaining proof
  code between the two projections.  The two literal append resources remain
  independent and may select different standard PA witness suffixes.
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
  RawCodedTemplateDirectStructuralTranslation
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedPALocalProofIteratedUnusedAntecedents
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

(** ------------------------------------------------------------------
    A root-term-general append compiler. *)

(** This is the arbitrary-reroot generalization of the earlier parent-source
    compiler.  Row stability cannot be inferred for arbitrary opaque terms,
    so it remains an explicit syntactic premise. *)
Theorem
    raw_directFormulaStandardTailCompilerAt_of_rerooted_append_concrete_row :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    readyContext rootFormula rootAssignmentCode rootAssignmentStep
    consequence,
  RawCoqRestrictedPADirectReadyContextStandardWitnessAffine readyContext ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) ->
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep) =
    rawDirectTemplateFormula inputs consequence ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      rootFormula rootAssignmentCode rootAssignmentStep (readyContext []) ->
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs readyContext consequence.
Proof.
  intros M hPA inputs readyContext rootFormula rootAssignmentCode
    rootAssignmentStep consequence haffine hrows hidentification hresources.
  pose proof
    (raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      rootFormula rootAssignmentCode rootAssignmentStep (readyContext [])
      hrows hresources) as hglobal.
  intros baseWitnesses.
  destruct (hglobal baseWitnesses) as
    (suffix & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.
  exists suffix, sourceRoot.
  rewrite haffine.
  rewrite rawTemplateContextCode_app_on_tail.
  rewrite <- hidentification.
  exact hsourceRoot.
Qed.

(** ------------------------------------------------------------------
    One shared description of the two And-E projections. *)

Inductive CoqRestrictedPADirectAndEliminationProjection : Type :=
  | CoqAndEliminationLeftProjection
  | CoqAndEliminationRightProjection.

Definition coqRestrictedPADirectAndEliminationReadyContextFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateContext -> TemplateContext :=
  match projection with
  | CoqAndEliminationLeftProjection =>
      coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext
  | CoqAndEliminationRightProjection =>
      coqRestrictedPADirectStrongStepAndEliminationRightReadyContext
  end.

Definition coqRestrictedPADirectAndEliminationResultFormulaTermFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateTerm :=
  match projection with
  | CoqAndEliminationLeftProjection =>
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
  | CoqAndEliminationRightProjection =>
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
  end.

Definition coqRestrictedPADirectAndEliminationFormulaCodeTemplateFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateFormula :=
  match projection with
  | CoqAndEliminationLeftProjection =>
      coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
  | CoqAndEliminationRightProjection =>
      coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
  end.

Definition coqRestrictedPADirectAndEliminationFormulaTruthTemplateFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateFormula :=
  match projection with
  | CoqAndEliminationLeftProjection =>
      coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate
  | CoqAndEliminationRightProjection =>
      coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate
  end.

Definition coqRestrictedPADirectAndEliminationResultTruthTemplateFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateFormula :=
  match projection with
  | CoqAndEliminationLeftProjection =>
      coqRestrictedPADirectAndEliminationLeftResultTruthTemplate
  | CoqAndEliminationRightProjection =>
      coqRestrictedPADirectAndEliminationRightResultTruthTemplate
  end.

Definition coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    : TemplateFormula :=
  coqTemplateImpChain
    [coqRestrictedPADirectAndEliminationFormulaCodeTemplateFor projection;
     coqRestrictedPADirectAndEliminationFormulaTruthTemplateFor projection]
    (coqRestrictedPADirectAndEliminationResultTruthTemplateFor projection).

Lemma coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor_left :
  coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor
      CoqAndEliminationLeftProjection =
    coqRestrictedPADirectAndEliminationLeftDynamicTruthLawTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor_right :
  coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor
      CoqAndEliminationRightProjection =
    coqRestrictedPADirectAndEliminationRightDynamicTruthLawTemplate.
Proof. reflexivity. Qed.

Definition
    RawCoqRestrictedPADirectAndEliminationResultTruthStandardTailCompilerFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    (coqRestrictedPADirectAndEliminationReadyContextFor projection)
    (coqRestrictedPADirectAndEliminationResultTruthTemplateFor projection).

Definition
    RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
    (projection : CoqRestrictedPADirectAndEliminationProjection)
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    (coqRestrictedPADirectAndEliminationReadyContextFor projection)
    (coqRestrictedPADirectAndEliminationDynamicTruthLawTemplateFor projection).

Arguments
  RawCoqRestrictedPADirectAndEliminationResultTruthStandardTailCompilerFor
  projection M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
  projection M hPA inputs : clear implicits.

(** Both concrete reroots leave the shared rows unchanged.  Quantification
    over the two-element rule index prevents the finite computation from
    being duplicated while retaining the necessary non-arbitrary premise. *)
Lemma coqRestrictedPADirectAndElimination_mode_zero_result_rows_stable :
  forall projection,
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (coqRestrictedPADirectAndEliminationResultFormulaTermFor projection)
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Lemma coqRestrictedPADirectAndEliminationReadyContextFor_app_witnesses :
  forall projection witnesses,
  coqRestrictedPADirectAndEliminationReadyContextFor projection
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectAndEliminationReadyContextFor projection [] ++
      embedPAContext (map witnessedAxiom witnesses).
Proof.
  intros projection witnesses. destruct projection.
  - exact
      (coqRestrictedPADirectSameContextUnary_andEliminationLeft_readyContext_app_witnesses
        witnesses).
  - exact
      (coqRestrictedPADirectSameContextUnary_andEliminationRight_readyContext_app_witnesses
        witnesses).
Qed.

(** Alignment is used only here: its arbitrary-root congruence specializes
    directly to the selected conjunct and the live assignment pair. *)
Lemma raw_andElimination_mode_zero_result_source_aligned : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (projection : CoqRestrictedPADirectAndEliminationProjection)
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
        (coqRestrictedPADirectAndEliminationResultFormulaTermFor projection)
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs
      (coqRestrictedPADirectAndEliminationResultTruthTemplateFor projection).
Proof.
  intros M hPA projection tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  rewrite (proj1
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    (coqRestrictedPADirectAndEliminationResultFormulaTermFor projection)
    (ttVar 9) (ttVar 8)).
  destruct projection; reflexivity.
Qed.

(** The dynamic law differs from result truth only by two unused
    antecedents.  This proof is completely independent of alignment and of
    the selected projection. *)
Theorem
    raw_andEliminationDynamicTruthStandardTailCompilerFor_of_result_truth :
  forall projection (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationResultTruthStandardTailCompilerFor
      projection M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
      projection M hPA inputs.
Proof.
  intros projection M hPA inputs htruth.
  exact
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      (coqRestrictedPADirectAndEliminationReadyContextFor projection)
      [coqRestrictedPADirectAndEliminationFormulaCodeTemplateFor projection;
       coqRestrictedPADirectAndEliminationFormulaTruthTemplateFor projection]
      (coqRestrictedPADirectAndEliminationResultTruthTemplateFor projection)
      htruth).
Qed.

(** The shared rule-indexed endpoint.  Clients select only a projection and
    provide the literal append trace for that conjunct's root term. *)
Theorem
    raw_andEliminationDynamicTruthStandardTailCompilerFor_of_aligned_append_concrete_row :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (projection : CoqRestrictedPADirectAndEliminationProjection)
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
      (coqRestrictedPADirectAndEliminationResultFormulaTermFor projection)
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectAndEliminationReadyContextFor projection []) ->
  RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
      projection M hPA inputs.
Proof.
  intros M hPA projection tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_andEliminationDynamicTruthStandardTailCompilerFor_of_result_truth.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_rerooted_append_concrete_row
      M hPA inputs
      (coqRestrictedPADirectAndEliminationReadyContextFor projection)
      (coqRestrictedPADirectAndEliminationResultFormulaTermFor projection)
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectAndEliminationResultTruthTemplateFor projection)
      (coqRestrictedPADirectAndEliminationReadyContextFor_app_witnesses
        projection)
      (coqRestrictedPADirectAndElimination_mode_zero_result_rows_stable
        projection)
      (raw_andElimination_mode_zero_result_source_aligned
        M hPA projection tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

(** ------------------------------------------------------------------
    Exact public left/right compilers and their paired interface. *)

Definition
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs).

Definition
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectAndEliminationRightDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.

Corollary
    raw_andEliminationLeftDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
  RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  change
    (RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
      CoqAndEliminationLeftProjection M hPA inputs).
  exact
    (raw_andEliminationDynamicTruthStandardTailCompilerFor_of_aligned_append_concrete_row
      M hPA CoqAndEliminationLeftProjection tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi
      aligned inputLevelNumeral inputs hstructural hresources).
Qed.

Corollary
    raw_andEliminationRightDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      coqRestrictedPADirectAndEliminationRightResultFormulaTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext []) ->
  RawCoqRestrictedPADirectAndEliminationRightDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  change
    (RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilerFor
      CoqAndEliminationRightProjection M hPA inputs).
  exact
    (raw_andEliminationDynamicTruthStandardTailCompilerFor_of_aligned_append_concrete_row
      M hPA CoqAndEliminationRightProjection tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi
      aligned inputLevelNumeral inputs hstructural hresources).
Qed.

Record RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawCoqRestrictedPADirect_andEliminationLeftDynamicTruthCompiler :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthStandardTailCompiler
      M hPA inputs;
  rawCoqRestrictedPADirect_andEliminationRightDynamicTruthCompiler :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthStandardTailCompiler
      M hPA inputs
}.

Arguments
  RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilers
  M hPA inputs : clear implicits.

Corollary
    raw_andEliminationDynamicTruthStandardTailCompilers_of_aligned_append_concrete_rows :
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
  RawCoqRestrictedPADirectAndEliminationDynamicTruthStandardTailCompilers
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hleftResources hrightResources.
  constructor.
  - exact
      (raw_andEliminationLeftDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hleftResources).
  - exact
      (raw_andEliminationRightDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hrightResources).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationAlignedTruthProduction.
