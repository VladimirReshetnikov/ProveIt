(**
  Produce the remaining And-I parent-truth root from aligned append evidence.

  The post-And-I continuation has only one semantic residual after its two
  recursive children have been compiled: truth of the outer conjunction at
  the live assignment coordinates [(#9,#8)].  This module exposes the honest
  proof-producing boundary for that residual.  Its premise supplies exactly
  two roots on a finite standard-PA extension:

  - literal existence of a mode-zero four-state append trace; and
  - the concrete successor-row implication below the append witnesses.

  The generic append eliminator converts those roots into the growing global
  Sigma source.  Native structural alignment then reroots that source at the
  parent formula and the two live assignment variables.  No formula-truth
  root, global-source root, or target equality is assumed by the resource
  compiler itself.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceIntegration.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceIntegration.

(** Literal proof-producing resources for one mode-zero root application.
    The three root terms and the finite outer prefix are parameters, so this
    boundary is reusable by other direct rules.  Every root is already on the
    same standard witness extension.  In particular, the second field is not
    a desired global-source or truth root: it is the concrete row implication
    consumed by the represented append traversal. *)
Definition
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (boundName : TemplateParameterName)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot rowRoot : M,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let allWitnesses := baseWitnesses ++ suffix in
  let sourceContext := rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom allWitnesses)) in
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (embedPATerm (Term.numeral 0))
    rootFormula rootAssignmentCode rootAssignmentStep outerPrefix in
  let antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter boundName) in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral 0))
        rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (templateContextShiftMany 5 witnessContext))
    (rawTemplateFormula translation
      (tfImp antecedent
        (tfImp rowLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))) rowRoot.

Arguments
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
  M hPA inputs boundName rootFormula rootAssignmentCode rootAssignmentStep
  outerPrefix : clear implicits.

(** Derived growing global source, kept separate from the literal resource
    boundary above.  This interface is useful when a client already knows
    its own identification of the global Sigma source with a target atom. *)
Definition
    RawCoqRestrictedPADirectModeZeroGlobalSourceStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm)
    (outerPrefix : TemplateContext) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
  exists sourceRoot : M,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  let sourceContext := rawTemplateContextCode translation
    (embedPAContext
      (map witnessedAxiom (baseWitnesses ++ suffix))) in
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep)) sourceRoot.

Arguments
  RawCoqRestrictedPADirectModeZeroGlobalSourceStandardTailCompilerAt
  M hPA inputs rootFormula rootAssignmentCode rootAssignmentStep outerPrefix
  : clear implicits.

(** The sole syntactic side condition needed by the generic append endpoint
    is stated explicitly.  It cannot be dropped for arbitrary opaque root
    terms, since root substitution need not leave the opened rows invariant. *)
Theorem
    raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    boundName rootFormula rootAssignmentCode rootAssignmentStep outerPrefix,
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter boundName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter boundName) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs boundName rootFormula rootAssignmentCode
      rootAssignmentStep outerPrefix ->
  RawCoqRestrictedPADirectModeZeroGlobalSourceStandardTailCompilerAt
    M hPA inputs rootFormula rootAssignmentCode rootAssignmentStep
      outerPrefix.
Proof.
  intros M hPA inputs boundName rootFormula rootAssignmentCode
    rootAssignmentStep outerPrefix hrowStable hresources
    baseWitnesses.
  unfold
    RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    in hresources.
  destruct (hresources baseWitnesses) as
    (suffix & modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep &
      appendRoot & rowRoot & happend & hrow).
  cbn zeta in happend, hrow.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (allWitnesses := baseWitnesses ++ suffix).
  set (sourceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      allWitnesses (raw_zero M)).
  set (sourceContext := rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom allWitnesses))).
  assert (hsource : RawCodedPAAxiomWitnessContext M
      sourceWitnessList sourceContext).
  {
    unfold sourceWitnessList, sourceContext, allWitnesses, translation.
    exact (raw_directEmbeddedPAAxiomWitnessContext
      M hPA inputs (baseWitnesses ++ suffix)).
  }
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_shared_global_at_root_terms_of_append_and_concrete_row_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      sourceWitnessList sourceContext 0 boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootFormula rootAssignmentCode rootAssignmentStep
      outerPrefix appendRoot rowRoot
      (or_introl eq_refl) hrowStable hsource happend hrow)
    as [sourceRoot hsourceRoot].
  exists suffix, sourceRoot.
  cbn zeta.
  unfold sourceContext, allWitnesses, translation in hsourceRoot.
  exact hsourceRoot.
Qed.

(** At the And-I parent coordinates the shared rows are closed under the
    concrete three-term rerooting.  The existing finite computation was first
    needed by Imp-I, but its statement is rule-independent; this alias gives
    the fact its semantic role at the And-I boundary. *)
Lemma coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable :
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof.
  exact
    coqRestrictedPADirectImpIntroduction_shared_rows_at_root_terms_eq.
Qed.

(** Structural alignment identifies the generated mode-zero source with
    conclusion truth at the same parent tuple.  The final rewrite is only the
    definitional five-argument truth shape; it does not invoke a semantic
    truth principle. *)
Theorem raw_andIntroduction_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate.
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
  rewrite (proj1
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    (ttVar 9) (ttVar 8)).
  rewrite coqRestrictedPADirectAssumption_outer_conclusion_truth_shape.
  reflexivity.
Qed.

(** Genuine discharge of the one-root post-And-I residual.  The append-row
    producer may enlarge every caller-provided standard prefix; its global
    source is compiled on that same enlarged tail and rewritten to parent
    truth only after native alignment has supplied the represented-code
    equality. *)
Theorem
    raw_restrictedPADirectAndIntroductionTruthCoreStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectAndIntroductionTruthCoreStandardTailCompiler
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
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext [])
      coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable
      hresources) as hglobal.
  pose proof
    (raw_andIntroduction_mode_zero_parent_source_aligned
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural) as hidentification.
  unfold
    RawCoqRestrictedPADirectAndIntroductionTruthCoreStandardTailCompiler.
  intro baseWitnesses.
  destruct (hglobal baseWitnesses) as
    (suffix & sourceRoot & hsourceRoot).
  cbn zeta in hsourceRoot.
  exists suffix, sourceRoot.
  rewrite
    coqRestrictedPADirectAndIntroductionReadyContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix))))
        (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      sourceRoot).
  change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawTemplateContextCode
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix))))
        (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          coqRestrictedPADirectAssumptionOuterConclusionTerm
          (ttVar 9) (ttVar 8))) sourceRoot) in hsourceRoot.
  rewrite hidentification in hsourceRoot.
  exact hsourceRoot.
Qed.

(** Close the complete selected And-I package, not merely its final truth
    residual.  The recursive child pair is unconditional; the only resources
    retained here are the concrete append-row roots needed for parent truth.
    This is the form consumed by the post-And-I continuation compiler. *)
Corollary
    raw_selectedAndIntroductionCoreTail_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_selectedAndIntroductionCoreTail_of_children_and_truth
      M hPA inputs
      (raw_selectedAndIntroductionChildCoreTail M hPA inputs)
      (raw_restrictedPADirectAndIntroductionTruthCoreStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hresources)).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
