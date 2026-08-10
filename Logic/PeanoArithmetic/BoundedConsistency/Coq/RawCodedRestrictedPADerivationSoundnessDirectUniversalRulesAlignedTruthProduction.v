(**
  Compile the K-only universal-rule residuals from aligned parent truth.

  Universal introduction and universal elimination each retain one semantic
  field after their constructor projections have been compiled.  Although
  the displayed antecedents mention a shifted context, a recursive child, or
  an opened universal formula, both residuals conclude truth of the common
  outer conclusion.  Native structural alignment already supplies exactly
  that consequent.  The antecedents are therefore introduced by genuine
  represented K-combinator proofs in the unchanged rule context.

  The first half of this module abstracts the repeated mechanism.  It turns a
  literal append/concrete-row resource in any affine ready context into a
  compiler for an identified consequence, lifts such a compiler through an
  arbitrary metatheoretic list of unused antecedents, and synchronizes two
  growing standard-witness compilers.  The second half specializes those
  abstractions to the exact universal-introduction and
  universal-elimination contexts and law templates.
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
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction
  RawCodedPALocalProofIteratedUnusedAntecedents.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.

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
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.
Import PABoundedRawCodedPALocalProofIteratedUnusedAntecedents.

(** ------------------------------------------------------------------
    Generic growing-tail and affine-ready-context infrastructure. *)

(** A proof-producing property which may enlarge every incoming finite list
    of standard PA-axiom witnesses.  Keeping the payload abstract makes the
    synchronization lemma below useful for rule roots as well as append
    resources. *)
Definition RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (payload : TemplateContext -> Prop) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    payload
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments RawCoqRestrictedPADirectStandardWitnessTailCompiler
  payload : clear implicits.

(** The only context fact required by the generic source compiler. *)
Definition RawCoqRestrictedPADirectReadyContextStandardWitnessAffine
    (readyContext : TemplateContext -> TemplateContext) : Prop :=
  forall witnesses : StandardPAAxiomWitnessPrefix,
    readyContext (embedPAContext (map witnessedAxiom witnesses)) =
    readyContext [] ++ embedPAContext (map witnessedAxiom witnesses).

Arguments RawCoqRestrictedPADirectReadyContextStandardWitnessAffine
  readyContext : clear implicits.

(** A concrete local-proof payload at a parameterized ready context. *)
Definition RawCoqRestrictedPADirectFormulaLocalProofAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (readyContext : TemplateContext -> TemplateContext)
    (formula : TemplateFormula) (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (readyContext tail))
      (rawDirectTemplateFormula inputs formula)
      root.

Arguments RawCoqRestrictedPADirectFormulaLocalProofAt
  M hPA inputs readyContext formula tail : clear implicits.

Definition RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (readyContext : TemplateContext -> TemplateContext)
    (formula : TemplateFormula) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectFormulaLocalProofAt
      M hPA inputs readyContext formula).

Arguments RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
  M hPA inputs readyContext formula : clear implicits.

(** Arbitrary represented roots survive standard-witness growth whenever the
    surrounding ready context has the affine equation above.  This is the
    rule-independent transport needed to synchronize independently growing
    semantic fields. *)
Theorem raw_directReadyFormulaRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    readyContext,
  RawCoqRestrictedPADirectReadyContextStandardWitnessAffine readyContext ->
  forall prefix witnesses suffix formula,
  RawCoqRestrictedPADirectFormulaLocalProofAt
    M hPA inputs readyContext formula
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectFormulaLocalProofAt
    M hPA inputs readyContext formula
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs readyContext haffine
    prefix witnesses suffix formula (root & hroot).
  rewrite haffine in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (readyContext []) prefix witnesses suffix
      (rawDirectTemplateFormula inputs formula)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite haffine.
  exact htransported.
Qed.

(** Dependency-ordered pairing of growing compilers.  The second compiler is
    invoked after the first one's witness extension; the first payload is
    then transported through the second extension. *)
Theorem raw_standardWitnessTailCompiler_pair : forall
    (firstPayload secondPayload : TemplateContext -> Prop),
  (forall prefix witnesses suffix,
    firstPayload (embedPAContext (map witnessedAxiom witnesses)) ->
    firstPayload
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix))))) ->
  RawCoqRestrictedPADirectStandardWitnessTailCompiler firstPayload ->
  RawCoqRestrictedPADirectStandardWitnessTailCompiler secondPayload ->
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (fun tail => firstPayload tail /\ secondPayload tail).
Proof.
  intros firstPayload secondPayload hfirstSurround
    hfirst hsecond baseWitnesses.
  destruct (hfirst baseWitnesses) as [firstSuffix hfirstPayload].
  destruct (hsecond (baseWitnesses ++ firstSuffix))
    as [secondSuffix hsecondPayload].
  pose proof
    (hfirstSurround [] (baseWitnesses ++ firstSuffix) secondSuffix
      hfirstPayload) as hfirstFinal.
  cbn [List.app] in hfirstFinal.
  exists (firstSuffix ++ secondSuffix).
  replace ((baseWitnesses ++ firstSuffix) ++ secondSuffix)
    with (baseWitnesses ++ (firstSuffix ++ secondSuffix))
    in hfirstFinal, hsecondPayload by apply app_assoc.
  exact (conj hfirstFinal hsecondPayload).
Qed.

(** Turn the literal append trace and concrete successor-row implication into
    any consequence identified with the shared mode-zero parent source.  No
    rule-specific syntax occurs in this theorem. *)
Theorem
    raw_directFormulaStandardTailCompilerAt_of_parent_append_concrete_row :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    readyContext consequence,
  RawCoqRestrictedPADirectReadyContextStandardWitnessAffine readyContext ->
  rawDirectTemplateFormula inputs
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8)) =
    rawDirectTemplateFormula inputs consequence ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8) (readyContext []) ->
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs readyContext consequence.
Proof.
  intros M hPA inputs readyContext consequence
    haffine hidentification hresources.
  pose proof
    (raw_modeZeroGlobalSourceStandardTailCompilerAt_of_append_concrete_row
      M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8) (readyContext [])
      coqRestrictedPADirectAndIntroduction_mode_zero_parent_rows_stable
      hresources) as hglobal.
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

(** Lift a consequence compiler through any finite list of represented,
    unused antecedents without changing its selected witness suffix. *)
Theorem raw_directImpChainStandardTailCompilerAt_of_consequence : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    readyContext antecedents consequence,
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs readyContext consequence ->
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs readyContext
      (coqTemplateImpChain antecedents consequence).
Proof.
  intros M hPA inputs readyContext antecedents consequence
    hconsequence baseWitnesses.
  destruct (hconsequence baseWitnesses) as
    (suffix & consequenceRoot & hconsequenceRoot).
  destruct
    (raw_codedPALocalProofOf_iterated_unused_antecedents
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (readyContext
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix))))
      antecedents consequence consequenceRoot hconsequenceRoot)
    as [lawRoot hlaw].
  exists suffix, lawRoot.
  exact hlaw.
Qed.

(** ------------------------------------------------------------------
    Exact universal-rule context affinities and source identifications. *)

Lemma coqRestrictedPADirectUniversalIntroductionReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalIntroductionCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalIntroductionCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalIntroductionCaseTemplate witnesses).
Qed.

Lemma coqRestrictedPADirectUniversalEliminationReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepUniversalEliminationReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalEliminationCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
    coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalEliminationCaseTemplate [] ++
    embedPAContext (map witnessedAxiom witnesses)).
  exact
    (coqRestrictedPADirectStandardReadyContext_app_witnesses
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectUniversalEliminationCaseTemplate witnesses).
Qed.

Lemma raw_universalIntroduction_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectUniversalIntroductionResultTruthTemplate.
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

Lemma raw_universalElimination_mode_zero_parent_source_aligned : forall
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
      coqRestrictedPADirectUniversalEliminationResultTruthTemplate.
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
    Standalone exact compilers. *)

Definition
    RawCoqRestrictedPADirectUniversalIntroductionResultTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
    coqRestrictedPADirectUniversalIntroductionResultTruthTemplate.

Definition
    RawCoqRestrictedPADirectUniversalIntroductionEigenStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs).

Definition
    RawCoqRestrictedPADirectUniversalEliminationResultTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectFormulaStandardTailCompilerAt
    M hPA inputs
    coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
    coqRestrictedPADirectUniversalEliminationResultTruthTemplate.

Definition
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectUniversalIntroductionResultTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectUniversalIntroductionEigenStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectUniversalEliminationResultTruthStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_universalIntroductionEigenStandardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectUniversalIntroductionResultTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalIntroductionEigenStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
      [coqRestrictedPADirectUniversalIntroductionContextShiftTemplate;
       coqRestrictedPADirectUniversalIntroductionChildEndpointTemplate;
       coqRestrictedPADirectAssumptionWitnessContextTruthTemplate;
       coqRestrictedPADirectUniversalIntroductionFormulaCodeTemplate]
      coqRestrictedPADirectUniversalIntroductionResultTruthTemplate
      htruth) as hlaws.
  intros baseWitnesses.
  destruct (hlaws baseWitnesses) as (suffix & root & hroot).
  exists suffix, root.
  cbn [coqTemplateImpChain] in hroot.
  exact hroot.
Qed.

Theorem
    raw_universalEliminationDynamicTruthStandardTailCompiler_of_result_truth :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectUniversalEliminationResultTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs htruth.
  pose proof
    (raw_directImpChainStandardTailCompilerAt_of_consequence
      M hPA inputs
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
      [coqRestrictedPADirectUniversalEliminationSubstitutionTemplate;
       coqRestrictedPADirectUniversalEliminationFormulaCodeTemplate;
       coqRestrictedPADirectUniversalEliminationFormulaTruthTemplate]
      coqRestrictedPADirectUniversalEliminationResultTruthTemplate
      htruth) as hlaws.
  intros baseWitnesses.
  destruct (hlaws baseWitnesses) as (suffix & root & hroot).
  exists suffix, root.
  cbn [coqTemplateImpChain] in hroot.
  exact hroot.
Qed.

Theorem
    raw_universalIntroductionResultTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectUniversalIntroductionResultTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_parent_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
      coqRestrictedPADirectUniversalIntroductionResultTruthTemplate
      coqRestrictedPADirectUniversalIntroductionReadyContext_app_witnesses
      (raw_universalIntroduction_mode_zero_parent_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

Corollary
    raw_universalIntroductionEigenStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectUniversalIntroductionEigenStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply raw_universalIntroductionEigenStandardTailCompiler_of_result_truth.
  exact
    (raw_universalIntroductionResultTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

Theorem
    raw_universalEliminationResultTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectUniversalEliminationResultTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  exact
    (raw_directFormulaStandardTailCompilerAt_of_parent_append_concrete_row
      M hPA inputs
      coqRestrictedPADirectStrongStepUniversalEliminationReadyContext
      coqRestrictedPADirectUniversalEliminationResultTruthTemplate
      coqRestrictedPADirectUniversalEliminationReadyContext_app_witnesses
      (raw_universalElimination_mode_zero_parent_source_aligned
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural)
      hresources).
Qed.

Corollary
    raw_universalEliminationDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row :
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
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hresources.
  apply
    raw_universalEliminationDynamicTruthStandardTailCompiler_of_result_truth.
  exact
    (raw_universalEliminationResultTruthStandardTailCompiler_of_aligned_append_concrete_row
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural hresources).
Qed.

(** ------------------------------------------------------------------
    Synchronized pair of both K-only universal residuals. *)

Record RawCoqRestrictedPADirectUniversalKOnlySemanticRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectUniversalKOnly_introductionEigen :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectUniversalKOnly_eliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectUniversalKOnlySemanticRoots
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqRestrictedPADirectStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectUniversalKOnlySemanticRoots
      M hPA inputs).

Arguments
  RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
  M hPA inputs : clear implicits.

Lemma raw_universalIntroductionEigenSemanticRoots_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
    M hPA inputs
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
    M hPA inputs
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix hroot.
  exact
    (raw_directReadyFormulaRoot_surround_witnessed_tail
      M hPA inputs
      coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext
      coqRestrictedPADirectUniversalIntroductionReadyContext_app_witnesses
      prefix witnesses suffix
      coqRestrictedPADirectUniversalIntroductionEigenSemanticLawTemplate
      hroot).
Qed.

Theorem
    raw_universalKOnlySemanticRootsStandardTailCompiler_of_standalone :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectUniversalIntroductionEigenStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalEliminationDynamicTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hintroduction helimination.
  pose proof
    (raw_standardWitnessTailCompiler_pair
      (RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
        M hPA inputs)
      (RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
        M hPA inputs)
      (raw_universalIntroductionEigenSemanticRoots_surround_witnessed_tail
        M hPA inputs)
      hintroduction helimination) as hpair.
  intros baseWitnesses.
  destruct (hpair baseWitnesses) as
    (suffix & hintroductionRoot & heliminationRoot).
  exists suffix.
  constructor; assumption.
Qed.

Corollary
    raw_universalKOnlySemanticRootsStandardTailCompiler_of_aligned_append_concrete_rows :
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
      (coqRestrictedPADirectStrongStepUniversalIntroductionReadyContext []) ->
  RawCoqRestrictedPADirectModeZeroAppendConcreteRowStandardTailCompilerAt
    M hPA inputs coqDynamicTruthAppendRowBoundParameterName
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (coqRestrictedPADirectStrongStepUniversalEliminationReadyContext []) ->
  RawCoqRestrictedPADirectUniversalKOnlySemanticRootsStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural hintroductionResources heliminationResources.
  apply
    raw_universalKOnlySemanticRootsStandardTailCompiler_of_standalone.
  - exact
      (raw_universalIntroductionEigenStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural hintroductionResources).
  - exact
      (raw_universalEliminationDynamicTruthStandardTailCompiler_of_aligned_append_concrete_row
        M hPA tail predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
        inputs hstructural heliminationResources).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalRulesAlignedTruthProduction.
