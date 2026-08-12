(**
  Compile the exact V2 carried-consistency resources into the public native
  final trace-proof callback.

  The V2 rule dispatcher and the carried consistency bridge were previously
  connected only by a pointwise theorem with a long list of arguments.  The
  public staged successor, however, consumes a compiler quantified over every
  graph trace and every witnessed prerequisite context.  This module records
  the honest proof-producing seam between those two interfaces.

  In particular, the resource compiler below must choose both direct-input
  records, prove the two code equalities which relate them, construct the V2
  rule resources, retain the strong-prefix closure remainder, and provide the
  carried consistency bridge.  Nothing in this adapter turns model truth into
  a represented PA proof.  Its only job is to thread those explicit resources
  into the already checked V2 final theorem.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  RawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2ResourceHandoff
  CompactPAUniformProvability.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2ResourceHandoff.
Import PABoundedCompactPAUniformProvability.

(** All arithmetic data required to close one selected final graph trace.
    The stage coordinates are parameters of the record; every other field is
    a proof-producing choice made by the residual compiler at that trace. *)
Record RawDynamicTruthNativeFinalV2CarriedTraceResourcesAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (stageTail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode : M) : Prop := {
  rawDynamicTruthNativeFinalV2_basicInputs :
    RawCodedTemplateDirectStructuralInputs M;
  rawDynamicTruthNativeFinalV2_extendedInputs :
    RawCodedTemplateDirectStructuralInputs M;
  rawDynamicTruthNativeFinalV2_parameters :
    RawCodedTemplateNumeralParameters M;
  rawDynamicTruthNativeFinalV2_contextTruth :
    RawCoqRestrictedPATruthDirectSelector M
      rawDynamicTruthNativeFinalV2_parameters;
  rawDynamicTruthNativeFinalV2_conclusionTruth :
    RawCoqRestrictedPATruthDirectSelector M
      rawDynamicTruthNativeFinalV2_parameters;
  rawDynamicTruthNativeFinalV2_currentGlobalSigma : M;
  rawDynamicTruthNativeFinalV2_currentGlobalPi : M;
  rawDynamicTruthNativeFinalV2_predecessorLevel : M;
  rawDynamicTruthNativeFinalV2_nextSigmaEvidence : M;
  rawDynamicTruthNativeFinalV2_resourceTail : nat -> M;
  rawDynamicTruthNativeFinalV2_alignedPredecessorLevel : M;
  rawDynamicTruthNativeFinalV2_alignedBaseContext : M;
  rawDynamicTruthNativeFinalV2_alignedCurrentLocal : M;
  rawDynamicTruthNativeFinalV2_nextInputGlobalSigma : M;
  rawDynamicTruthNativeFinalV2_nextInputGlobalPi : M;
  rawDynamicTruthNativeFinalV2_aligned :
    RawDynamicTruthNativeLocalAlignedPredecessorAt M
      rawDynamicTruthNativeFinalV2_resourceTail
      rawDynamicTruthNativeFinalV2_alignedPredecessorLevel
      rawDynamicTruthNativeFinalV2_alignedBaseContext
      rawDynamicTruthNativeFinalV2_alignedCurrentLocal
      rawDynamicTruthNativeFinalV2_nextInputGlobalSigma
      rawDynamicTruthNativeFinalV2_nextInputGlobalPi;
  rawDynamicTruthNativeFinalV2_inputLevelNumeral : M;
  rawDynamicTruthNativeFinalV2_sourceBaseContext : M;
  rawDynamicTruthNativeFinalV2_replacement : M;
  rawDynamicTruthNativeFinalV2_axiom : M;
  rawDynamicTruthNativeFinalV2_closureCount : M;
  rawDynamicTruthNativeFinalV2_bodyCodeEquality :
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
        rawDynamicTruthNativeFinalV2_extendedInputs =
      rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
        rawDynamicTruthNativeFinalV2_basicInputs;
  rawDynamicTruthNativeFinalV2_universalCodeEquality :
    rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        rawDynamicTruthNativeFinalV2_extendedInputs =
      rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        rawDynamicTruthNativeFinalV2_basicInputs;
  rawDynamicTruthNativeFinalV2_ruleResources :
    RawDynamicTruthNativeFinalV2ResourceBundle M hPA
      rawDynamicTruthNativeFinalV2_parameters
      rawDynamicTruthNativeFinalV2_contextTruth
      rawDynamicTruthNativeFinalV2_conclusionTruth
      rawDynamicTruthNativeFinalV2_currentGlobalSigma
      rawDynamicTruthNativeFinalV2_currentGlobalPi
      rawDynamicTruthNativeFinalV2_predecessorLevel
      rawDynamicTruthNativeFinalV2_nextSigmaEvidence
      rawDynamicTruthNativeFinalV2_resourceTail
      rawDynamicTruthNativeFinalV2_alignedPredecessorLevel
      rawDynamicTruthNativeFinalV2_alignedBaseContext
      rawDynamicTruthNativeFinalV2_alignedCurrentLocal
      rawDynamicTruthNativeFinalV2_nextInputGlobalSigma
      rawDynamicTruthNativeFinalV2_nextInputGlobalPi
      rawDynamicTruthNativeFinalV2_aligned
      rawDynamicTruthNativeFinalV2_inputLevelNumeral
      rawDynamicTruthNativeFinalV2_extendedInputs;
  rawDynamicTruthNativeFinalV2_closureRemainder :
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M rawDynamicTruthNativeFinalV2_basicInputs
      rawDynamicTruthNativeFinalV2_replacement
      rawDynamicTruthNativeFinalV2_axiom
      rawDynamicTruthNativeFinalV2_closureCount;
  rawDynamicTruthNativeFinalV2_carriedConsistency :
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        rawDynamicTruthNativeFinalV2_basicInputs)
      stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      rawDynamicTruthNativeFinalV2_sourceBaseContext
}.

Arguments RawDynamicTruthNativeFinalV2CarriedTraceResourcesAt
  M hPA stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode : clear implicits.

(** Honest trace-indexed residual.  It receives exactly the graph and proof
    resources visible at the public final callback invocation. *)
Definition RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (stageTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode witnessList
      baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawDynamicTruthNativeFinalV2CarriedTraceResourcesAt M hPA
      stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode.

Arguments RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler
  M hPA : clear implicits.

(** The pointwise V2 handoff closes the public final callback at every trace.
    Notice that the witnessed prerequisite package is passed to the resource
    compiler, but no contraction back to its original base is requested. *)
Theorem
    raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_v2_carried_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler M hPA ->
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.
Proof.
  intros M hPA hresources stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode witnessList
    baseContext htrace hprerequisites.
  destruct
    (hresources stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode witnessList
      baseContext htrace hprerequisites)
    as [basicInputs extendedInputs parameters contextTruth conclusionTruth
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      resourceTail alignedPredecessorLevel alignedBaseContext
      alignedCurrentLocal nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral sourceBaseContext replacement axiom closureCount
      hbodyCode huniversalCode hruleResources hremainder hcarried].
  exact
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_v2_resource_bundle_and_carried_consistency
      M hPA basicInputs extendedInputs parameters contextTruth conclusionTruth
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
      resourceTail alignedPredecessorLevel alignedBaseContext
      alignedCurrentLocal nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      replacement axiom closureCount hbodyCode huniversalCode
      hruleResources htrace hremainder hcarried).
Qed.

(** Dependency-ordered boundary with only its final coordinate changed.  The
    first six fields are definitionally identical to the established trace
    boundary, making this adapter safe for all existing callback consumers. *)
Definition RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler M hPA.

Arguments RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilers
  M hPA translation : clear implicits.

Theorem
    raw_dynamicTruthNativeDependencyOrderedTraceProofKernelCompilers_of_v2_carried_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
    M translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split; [exact hcrossLevel |].
  split; [exact hshift |].
  split; [exact hsubstitution |].
  split; [exact haxiom |].
  exact
    (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_v2_carried_resources
      M hPA hfinal).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilers
        M hPA translation.

(** Exact object-language target from the explicit V2/carried resource
    boundary.  This is still conditional: the theorem intentionally makes
    the remaining arbitrary-model compiler family visible in its premise. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_v2_carried_resources
    :
  RawDynamicTruthNativeDependencyOrderedV2CarriedKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hresources.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_trace_proof_kernel_compilers.
  intros M hPA.
  destruct (hresources M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedTraceProofKernelCompilers_of_v2_carried_resources
      M hPA translation hmodel).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation.
