(**
  Assumption-retaining positive-rank permuted-append compilation.

  The historical positive strong-step resource returned proofs of the
  restricted-derivation and rule-validity premises over the bare PA tail.
  Those formulae are precisely assumptions of the direct strong-step shell.
  This file removes both proof roots from the resource coordinate: only the
  two synchronized permuted-append packages remain.  Arithmetic endpoint
  roots are then compiled from assumption leaves while the caller prefix is
  retained literally.

  The resulting logical roots are not silently coerced to the newer guarded
  collision interface.  That conversion needs constructor-generic guarded
  evidence, which the two concrete predecessor-row packages do not contain.
  We therefore name the exact continuation needed by the guarded dependency
  bundle and keep its prefix lifetime visible in the endpoint adapter.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomTruth
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAGrowingTemplateRebase
  RawCodedPAGrowingTemplateConjunction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthSharedSuccessorPermutedAppendGlobalRoots
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit
  RawCodedDynamicTruthNativeZeroGuardedCollisionCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativePositiveAssumptionRetainingPermutedAppendCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAGrowingTemplateRebase.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthSharedSuccessorPermutedAppendGlobalRoots.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.

(** The genuinely append-specific positive resource.  Compared with
    [RawDynamicTruthNativeAlignedStrongStepPermutedAppendProofResourcesCompilerWithPA],
    this interface deletes both proof-root outputs.  The remaining packages
    contain only the append witness data and traversal kernels. *)
Definition
    RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList inputLevelNumeral
      (inputs : RawCodedTemplateDirectStructuralInputs M),
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
      inputLevelNumeral ->
    RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        0 appendWitnesses /\
      RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        1 appendWitnesses.

Arguments
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
  M hPA : clear implicits.

(** Compatibility is pure forgetting: no proof is transformed and no
    represented context is contracted. *)
Theorem
    raw_dynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA_of_proof_resources :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendProofResourcesCompilerWithPA
    M hPA ->
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA.
Proof.
  intros M hPA hresources tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    inputLevelNumeral inputs hsource hnumeral hstructural.
  destruct
    (hresources tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      inputLevelNumeral inputs hsource hnumeral hstructural) as
    (_restrictedRoot & _ruleRoot & appendWitnesses &
      _hrestricted & _hrule & hsigma & hpi).
  exists appendWitnesses. split; assumption.
Qed.

(** Positive logical-root callback at the honest direct-shell boundary.
    The selected direct inputs are returned because they determine how the
    live caller prefix is encoded. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList callerPrefix,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      callerPrefix ->
    In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M
        (rawTemplateContextCodeOnTail
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          targetContext callerPrefix)
        (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned).

Arguments
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs
  M hPA : clear implicits.

(** Compile positive logical roots without ever producing either direct-shell
    premise over a bare PA context.  The endpoint evidence is built below
    [predecessor-state ++ callerPrefix], rebased onto the arithmetic endpoint,
    and synchronized there before admissibility is compiled. *)
Theorem
    raw_dynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs_of_permuted_append_input_resources :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs
    M hPA.
Proof.
  intros M hPA hresources tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    callerPrefix hsourceWitnessed hrestrictedIn hruleIn.
  pose proof
    (rawDynamicTruthNativeLocalAligned_currentTrace M tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi aligned)
    as htrace.
  destruct htrace as
    (_ & inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hinputLevel & hsuccessor & hnumeral &
      hsigmaDomain & hpiDomain & hsigmaApplication & hpiApplication).
  subst inputLevel.
  destruct
    (raw_dynamicTruthNativeAlignedStrongStepStructuralInputs_exists
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral hnumeral) as [inputs hstructural].
  pose proof hstructural as hstructuralForResources.
  destruct hstructural as
    (localSigmaRow & localPiRow & hwrapper & hlevel &
      hsigmaRow & hpiRow & hsigmaConclusion & hpiConclusion &
      hpermutedSigmaEvidence & hpermutedPiEvidence).
  destruct
    (hresources tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      inputLevelNumeral inputs hsourceWitnessed hnumeral
      hstructuralForResources) as
    (appendWitnesses & hsigmaInputs & hpiInputs).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (stateCallerPrefix :=
    coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix).
  assert (hrestrictedState :
      In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
        stateCallerPrefix).
  {
    unfold stateCallerPrefix. apply in_or_app. right.
    exact hrestrictedIn.
  }
  assert (hruleState :
      In coqStrongStepProofEndpointAtomicAdequacyRulePremise
        stateCallerPrefix).
  {
    unfold stateCallerPrefix. apply in_or_app. right.
    exact hruleIn.
  }
  destruct
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_from_template_assumptions_under_prefix
      M hPA inputs sourceWitnessList baseContext stateCallerPrefix
      inputLevelNumeral
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hsourceWitnessed hrestrictedState hruleState hlevel
      hsigmaDomain hpiDomain) as
    (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).

  pose proof
    (raw_directStructuralTemplatePrefix_atomically_adequate
      M hPA inputs stateCallerPrefix) as hstateCallerAdequate.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_input_package
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      0 appendWitnesses hsigmaInputs) as hsigmaGrowingEmpty.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_input_package
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      1 appendWitnesses hpiInputs) as hpiGrowingEmpty.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_suffix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      [] stateCallerPrefix
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      hstateCallerAdequate hsigmaGrowingEmpty) as hsigmaGrowing.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_suffix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      [] stateCallerPrefix
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      hstateCallerAdequate hpiGrowingEmpty) as hpiGrowing.
  cbn [List.app] in hsigmaGrowing, hpiGrowing.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      stateCallerPrefix
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      hsigmaGrowing hpiGrowing) as happendPair.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofPairAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      stateCallerPrefix
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      endpointWitnessList endpointContext hendpointWitnessed happendPair)
    as hreBasedPair.
  destruct hreBasedPair as
    (evidenceWitnessList & evidenceContext & sigmaRoot & piRoot &
      hevidenceWitnessed & hendpointEvidenceIncluded & hsigma & hpi).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation endpointWitnessList endpointContext
      evidenceWitnessList evidenceContext stateCallerPrefix
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hendpointWitnessed hevidenceWitnessed hendpointEvidenceIncluded
      hatomic) as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation endpointWitnessList endpointContext
      evidenceWitnessList evidenceContext stateCallerPrefix
      (rawFormulaOrCode M
        (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)) domainRoot
      hendpointWitnessed hevidenceWitnessed hendpointEvidenceIncluded
      hdomain) as [transportedDomainRoot htransportedDomain].
  unfold stateCallerPrefix in
    htransportedAtomic, htransportedDomain, hsigma, hpi.
  rewrite
    (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      evidenceContext callerPrefix)
    in htransportedAtomic, htransportedDomain, hsigma, hpi.
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_under_prefix_atomic_and_domain
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      evidenceWitnessList evidenceContext callerPrefix
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      (rawDirectTemplateFormula inputs
        (coqFourStateTableAppendPermutedTemplateGlobalSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      transportedAtomicRoot transportedDomainRoot sigmaRoot piRoot
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs callerPrefix)
      hevidenceWitnessed htransportedAtomic htransportedDomain hsigma hpi)
    as (targetWitnessList & targetContext & htargetWitnessed &
      hevidenceTargetIncluded & hlogicalRoots).
  exists inputs, targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceTargetIncluded member
      (hendpointEvidenceIncluded member
        (hbaseEndpointIncluded member hmember))).
  - unfold coqFourStateTableAppendPermutedTemplateGlobalSource
      in hlogicalRoots.
    rewrite hpermutedSigmaEvidence, hpermutedPiEvidence in hlogicalRoots.
    exact hlogicalRoots.
Qed.

(** Resource bundle with the positive proof-root coordinate deleted.  The
    zero and six predecessor-independent fields are definitionally the same
    as in the previous sharp logical assumption-retaining package. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  let translation := rawBottomDirectStructuralTemplateTranslation M hPA in
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M translation coqDynamicTruthPredecessorStateTemplateContext /\
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA /\
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
    M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers
  M hPA : clear implicits.

Theorem
    raw_dynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers_of_proof_resources :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroGrowingFixedProductionOrRefutationProofResourceStrongStepKernelCompilers
    M hPA ->
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers
    M hPA.
Proof.
  intros M hPA
    (hzero & hpositive & hremainder & hcrossLevel & hshift &
      hsubstitution & haxiom & hfinal).
  exact (conj hzero
    (conj
      (raw_dynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA_of_proof_resources
        M hPA hpositive)
      (conj hremainder
        (conj hcrossLevel
          (conj hshift
            (conj hsubstitution
              (conj haxiom hfinal))))))).
Qed.

(** Dependency-bundle endpoint for the reduced positive coordinate. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedAssumptionRetainingPositiveLogicalRootsUnderCallerPrefix_of_permuted_append_input_resources :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs
    M hPA.
Proof.
  intros M hPA
    (_hzero & hpositive & _hremainder & _hcrossLevel & _hshift &
      _hsubstitution & _haxiom & _hfinal).
  exact
    (raw_dynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs_of_permuted_append_input_resources
      M hPA hpositive).
Qed.

(** Exact residual between positive concrete logical roots and the guarded
    collision coordinate.  It is deliberately a continuation, rather than
    an assertion that concrete predecessor evidence supplies all three
    constructor-generic guarded branches.  The same caller prefix and direct
    translation occur in premise and conclusion. *)
Definition
    RawDynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList callerPrefix
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      logicalWitnessList logicalContext,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      callerPrefix ->
    In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
    RawCodedPAAxiomWitnessContext M logicalWitnessList logicalContext ->
    RawContextListIncluded M baseContext logicalContext ->
    RawDynamicTruthPredecessorStateLogicalRootsAt M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        logicalContext callerPrefix)
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned) ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M logicalContext targetContext /\
      RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext callerPrefix.

Arguments
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix
  M hPA : clear implicits.

Theorem
    raw_dynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase_of_positive_permuted_append_inputs_and_logical_continuation :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA ->
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA.
Proof.
  intros M hPA hpositive hcontinuation tail predecessorLevel baseContext
    currentLocal nextInputGlobalSigma nextInputGlobalPi aligned
    sourceWitnessList callerPrefix hsource hrestrictedIn hruleIn.
  destruct
    (raw_dynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerUnderCallerPrefixOnWitnessedBaseWithDirectInputs_of_permuted_append_input_resources
      M hPA hpositive tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      callerPrefix hsource hrestrictedIn hruleIn) as
    (inputs & logicalWitnessList & logicalContext & hlogicalWitnessed &
      hbaseLogicalIncluded & hlogicalRoots).
  destruct
    (hcontinuation tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      callerPrefix inputs logicalWitnessList logicalContext hsource
      hrestrictedIn hruleIn hlogicalWitnessed hbaseLogicalIncluded
      hlogicalRoots) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hlogicalTargetIncluded & hcollision).
  exists inputs, targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hlogicalTargetIncluded member
      (hbaseLogicalIncluded member hmember)).
  - exact hcollision.
Qed.

(** Guarded dependency resource boundary after factoring its positive field
    through the reduced append input coordinate.  The continuation is the
    sole residual added by this factorization; every other sharp guarded
    field is passed through unchanged. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA /\
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA /\
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix
    M hPA /\
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA) /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers
  M hPA : clear implicits.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_positive_permuted_append_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA
    (hzero & hpositive & hcontinuation & hremainder & hcrossLevel &
      hshift & hsubstitution & haxiom & hfinal).
  split; [exact hzero |].
  split.
  - exact
      (raw_dynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase_of_positive_permuted_append_inputs_and_logical_continuation
        M hPA hpositive hcontinuation).
  - split; [exact hremainder |].
    split; [exact hcrossLevel |].
    split; [exact hshift |].
    split; [exact hsubstitution |].
    split; [exact haxiom | exact hfinal].
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers
      M hPA.

Theorem
    raw_dynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilersInAllModels_of_proof_resources :
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroGrowingFixedProductionOrRefutationProofResourceStrongStepKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilersInAllModels.
Proof.
  intros hlegacy M hPA.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCanonicalAssumptionRetainingLogicalZeroPositivePermutedAppendInputResourceStrongStepKernelCompilers_of_proof_resources
      M hPA (hlegacy M hPA)).
Qed.

Definition
    RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers
      M hPA.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels_of_positive_permuted_append_inputs :
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels.
Proof.
  intros hresources M hPA.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_positive_permuted_append_inputs
      M hPA (hresources M hPA)).
Qed.

(** There is intentionally no compact corollary here.  The current compact
    callback assembler consumes a prefix-free guarded split bundle, whereas
    this endpoint preserves the direct-shell caller prefix.  Producing that
    corollary now would require precisely the invalid prefix contraction this
    module is designed to avoid. *)

End
  PABoundedRawCodedDynamicTruthNativePositiveAssumptionRetainingPermutedAppendCompilation.
