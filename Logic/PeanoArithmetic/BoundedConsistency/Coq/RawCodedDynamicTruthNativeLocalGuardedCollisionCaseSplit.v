(**
  Assemble guarded collision roots by the native zero/successor split.

  Rank zero and positive rank use genuinely different proof resources.  The
  former is normalized to the canonical bottom trace; the latter carries an
  aligned predecessor record.  This module keeps those producers separate and
  performs only the structural case analysis already proved for a native local
  callback.  Both branches may grow their witnessed PA tails.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedSyntaxConstructors
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAGrowingTemplateRebase
  RawCodedLtSuccCasesProofCompilation
  RawCodedTemplateProofCompiler
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthPredecessorStateProjectionCompilation
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary
  RawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAGrowingTemplateRebase.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthPredecessorStateProjectionCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.

(** Rank-zero producer at the literal guarded callback interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
  M hPA translation : clear implicits.

(** Positive-rank producer after the native trace has selected and aligned its
    predecessor.  Passing the existing witness list is weaker than asking the
    producer to rediscover a witness for [baseContext]. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).

Arguments
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Invocation-local proof resources for the rank-zero collision.  Both
    direct-shell premises may grow independently from the normalized
    callback's witnessed PA tail.  The constructor-specific fixed producers
    may also depend on the normalized invocation and canonical trace; this is
    weaker than demanding a single model-global producer for every callback.

    The selected direct inputs are returned together with their evidence
    identification, so all three constructor branches use one translation
    without imposing that translation on the normalization phase. *)
Definition
    RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        witnessList baseContext []
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate) /\
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        witnessList baseContext []
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise) /\
      RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
        M hPA inputs.

Arguments
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
  M hPA : clear implicits.

(** Honest retained-assumption rank-zero resources.  Restricted-proof and
    rule-validity formulas are free-variable shell premises, not PA theorems;
    they therefore do not belong in the proof-producing resource bundle when
    the collision is still compiled below the caller prefix.  Only evidence
    identification and the constructor-indexed fixed append residues remain. *)
Definition
    RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
      RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
      RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
        M hPA inputs.

Arguments
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
  M hPA : clear implicits.

(** The older post-discharge bundle projects to the weaker retained-prefix
    bundle by forgetting its two proof roots.  The converse is intentionally
    absent: those roots need not be PA-provable outside the direct shell. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources_of_proof_resources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA.
Proof.
  intros M hPA hresources tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hnormalized htrace.
  destruct
    (hresources tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hnormalized htrace) as
    (inputs & hidentification & _hrestricted & _hrule & hfixed).
  exists inputs. split; assumption.
Qed.

(** Compile the exact guarded collision while the two direct-shell premises
    remain in scope.  This endpoint strictly relaxes the post-discharge
    compiler: no proof of either premise is requested, and every resulting
    root records the unchanged caller prefix in its represented context. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGuardedCollisionRootsUnderCallerPrefixOnNormalizedResources_of_fixed_resources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA ->
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence callerPrefix,
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    (rawBottomDirectStructuralTemplateTranslation M hPA)
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists targetWitnessList targetContext,
    RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA hresources tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence callerPrefix
    hnormalized htrace hrestrictedIn hruleIn.
  destruct
    (hresources tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hnormalized htrace) as
    (inputs & hidentification & hfixed).
  destruct
    (raw_dynamicTruthZeroCanonicalIdentified_guardedCollisionAppendRowKernelPayloadPairsForCaller_of_fixed
      M hPA inputs hidentification hfixed callerPrefix) as
    (himpPayload & handPayload & horPayload).
  destruct
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs
      M hPA inputs
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots callerPrefix
      hidentification hnormalized hrestrictedIn hruleIn
      himpPayload handPayload horPayload) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hcollision).
  exists inputs, targetWitnessList, targetContext.
  split; [exact hidentification |].
  split; [exact htargetWitnessed |].
  split; assumption.
Qed.

(** Literal callback boundary for the retained-prefix construction.  Unlike
    the historical rank-zero callback above, this interface also returns the
    selected direct inputs: the caller must know which translation represents
    [callerPrefix] before it can consume the collision roots.  Keeping the
    evidence identification beside those inputs prevents a later adapter from
    silently identifying two independently selected translations. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence callerPrefix,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      callerPrefix ->
    In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
    exists targetWitnessList targetContext,
      RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext callerPrefix.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext
  M hPA : clear implicits.

(** Normalize the actual guarded callback without discharging its caller.
    This is the retained-prefix counterpart of the empty-prefix adapter below:
    the state roots are reconstructed from the witnessed PA tail, the literal
    zero trace is canonicalized once, and the weaker fixed-resource compiler
    is invoked at the same [callerPrefix]. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext_of_normalized_fixed_resources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext
    M hPA.
Proof.
  intros M hPA hresources tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence callerPrefix hcurrent htrace hlevel
    hrestrictedIn hruleIn.
  pose proof hcurrent as hcurrentForWitness.
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hcurrentForWitness.
  destruct hcurrentForWitness as
    [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
  pose proof
    (raw_dynamicTruthPredecessorStateProjectionRootsAt_of_realizable
      M hPA baseContext
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hbaseWitnessed)) as hstateRoots.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_zero_normalized
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent hlevel hstateRoots)
    as hnormalized.
  subst level.
  pose proof
    (raw_dynamicTruthNativeLocalZeroFullTraceAt_canonical
      M hPA tail inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence) htrace)) as hcanonicalTrace.
  exact
    (raw_dynamicTruthNativeLocalZeroGuardedCollisionRootsUnderCallerPrefixOnNormalizedResources_of_fixed_resources
      M hPA hresources tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence callerPrefix
      hnormalized hcanonicalTrace hrestrictedIn hruleIn).
Qed.

(** Positive-rank counterpart of the retained-prefix zero compiler.  The
    aligned predecessor fixes all native values but may select its own direct
    structural inputs.  Consequently the inputs are returned with the roots
    instead of being quantified outside the producer.  No zero-specific
    evidence identification is requested in this branch. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
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
      RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext callerPrefix.

Arguments
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
  M hPA : clear implicits.

(** Any historical aligned producer can be consumed at the retained-prefix
    boundary by ordinary weakening.  This compatibility direction is valid
    because the producer has already selected a witnessed target PA context;
    adding translated caller assumptions only enlarges that context.  It is
    extracted here so the three root transports are not repeated by every
    dependency-package adapter. *)
Theorem
    raw_dynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase_of_plain :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA.
Proof.
  intros M hPA haligned tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    callerPrefix hsourceWitnessed _hrestrictedIn _hruleIn.
  destruct
    (haligned tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      hsourceWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hboolean & himp).
  destruct hboolean as [(andRoot & hand) (orRoot & hor)].
  destruct himp as [impRoot himp].
  set (inputs := rawBottomTemplateDirectStructuralInputs M hPA).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (htargetRealizable : RawContextListRealizable M targetContext).
  {
    exact
      (raw_codedPAAxiomWitnessContext_context_realizable
        M targetWitnessList targetContext htargetWitnessed).
  }
  assert (hprefixAdequate : RawCodedTemplatePrefixAtomicallyAdequate M
      translation ([] ++ callerPrefix)).
  {
    exact
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs ([] ++ callerPrefix)).
  }
  destruct
    (raw_codedPALocalProof_templateSuffix M hPA translation
      targetContext [] callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaAndEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiAndEx8BranchCode M)
          (rawFormulaBotCode M)))
      andRoot htargetRealizable hprefixAdequate hand) as
    [prefixedAndRoot hprefixedAnd].
  destruct
    (raw_codedPALocalProof_templateSuffix M hPA translation
      targetContext [] callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaOrEx8BranchCode M)
        (rawFormulaImpCode M
          (rawDynamicTruthPiOrEx8BranchCode M)
          (rawFormulaBotCode M)))
      orRoot htargetRealizable hprefixAdequate hor) as
    [prefixedOrRoot hprefixedOr].
  destruct
    (raw_codedPALocalProof_templateSuffix M hPA translation
      targetContext [] callerPrefix
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      impRoot htargetRealizable hprefixAdequate himp) as
    [prefixedImpRoot hprefixedImp].
  exists inputs, targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  constructor.
  - constructor.
    + exists prefixedAndRoot. exact hprefixedAnd.
    + exists prefixedOrRoot. exact hprefixedOr.
  - exists prefixedImpRoot. exact hprefixedImp.
Qed.

(** Prefix-preserving rank dispatcher.  This is the collision boundary that
    can be placed below implication introduction: both branches retain the
    same syntactic caller, although their direct structural witnesses may be
    selected from branch-specific normalized data. *)
Definition
    RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
    forall callerPrefix,
      In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
        callerPrefix ->
      In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
      exists inputs : RawCodedTemplateDirectStructuralInputs M,
      exists targetWitnessList targetContext,
        RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
        RawContextListIncluded M baseContext targetContext /\
        RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
          (rawDirectStructuralTemplateTranslation M hPA inputs)
          targetContext callerPrefix.

Arguments
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix
  M hPA : clear implicits.

(** Extract the common retained-prefix rank split once.  Row parameters are
    needed only to expose the native zero/successor dichotomy; neither branch
    has to rebuild or transport them after the aligned predecessor has been
    selected. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix_of_zero_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix
    M hPA.
Proof.
  intros M hPA hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows callerPrefix
    hrestrictedIn hruleIn.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent) as hlegacyCurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots)
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hlegacyCurrent htrace) as
    [(_currentLocalRoot & hlevel & _hfield & _hcurrentRoot) |
      (predecessorLevel & _hlevel & aligned & _halignedRows)].
  - destruct
      (hzero tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal witnessList baseContext helperRoots
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
        piEvidence callerPrefix hcurrent htrace hlevel
        hrestrictedIn hruleIn) as
      (inputs & targetWitnessList & targetContext & _hidentification &
        htargetWitnessed & hincluded & hcollision).
    exists inputs, targetWitnessList, targetContext.
    split; [exact htargetWitnessed |].
    split; [exact hincluded | exact hcollision].
  - pose proof hcurrent as hfields.
    unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
      RawDynamicTruthNativeLocalCurrentHelperBatchContextAt in hfields.
    destruct hfields as
      [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
    exact
      (haligned tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned witnessList callerPrefix
        hbaseWitnessed hrestrictedIn hruleIn).
Qed.

(** Public retained-prefix dispatcher with the entire rank-zero normalization
    route inlined.  The residuals now match the two genuine semantic cases:
    normalized fixed collision producers at zero and an aligned collision
    producer at positive rank. *)
Corollary
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix_of_zero_normalized_fixed_resources_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix
    M hPA.
Proof.
  intros M hPA hzeroResources haligned.
  exact
    (raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilderUnderCallerPrefix_of_zero_and_witnessed_aligned
      M hPA
      (raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnCurrentGuardedHelperContext_of_normalized_fixed_resources
        M hPA hzeroResources)
      haligned).
Qed.

(** Normalize the literal guarded callback, canonicalize its zero trace, and
    invoke the relaxed collision endpoint.  State-projection roots are
    reconstructed from realizability of the witnessed PA context, so the
    producer interface does not repeat that derived resource. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext_of_normalized_proof_resources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    M hPA (rawBottomDirectStructuralTemplateTranslation M hPA).
Proof.
  intros M hPA hresources tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace hlevel.
  pose proof hcurrent as hcurrentForWitness.
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hcurrentForWitness.
  destruct hcurrentForWitness as
    [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
  pose proof
    (raw_dynamicTruthPredecessorStateProjectionRootsAt_of_realizable
      M hPA baseContext
      (raw_codedPAAxiomWitnessContext_context_realizable
        M witnessList baseContext hbaseWitnessed)) as hstateRoots.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_zero_normalized
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent hlevel hstateRoots)
    as hnormalized.
  subst level.
  pose proof
    (raw_dynamicTruthNativeLocalZeroFullTraceAt_canonical
      M hPA tail inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      (proj1 (raw_dynamicTruthNativeLocalProofTraceAt_zero_iff M tail
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain
        sigmaEvidence piEvidence) htrace)) as hcanonicalTrace.
  destruct
    (hresources tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence
      hnormalized hcanonicalTrace) as
    (inputs & hidentification & hrestricted & hrule & hfixed).
  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_independently_growing_restricted_rule_roots_and_guarded_collision_fixed_productions_or_refutations
      M hPA inputs
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots hidentification hnormalized
      hrestricted hrule hfixed).
Qed.

(** Structural assembly into the public collision builder.  No collision
    formula is proved here; the theorem only routes the exact zero or aligned
    successor resources to the corresponding producer. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext
    M hPA translation ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M translation.
Proof.
  intros M hPA translation hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded
      M translation tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hcurrent) as hlegacyCurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots)
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hlegacyCurrent htrace) as
    [(_currentLocalRoot & hlevel & _hfield & _hcurrentRoot) |
      (predecessorLevel & _hlevel & aligned & _halignedRows)].
  - exact
      (hzero tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal witnessList baseContext helperRoots
        inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
        piEvidence hcurrent htrace hlevel).
  - pose proof hcurrent as hfields.
    unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
      RawDynamicTruthNativeLocalCurrentHelperBatchContextAt in hfields.
    destruct hfields as
      [_ (_ & _ & _ & _ & _ & _ & hbaseWitnessed & _)].
    exact
      (haligned tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned witnessList hbaseWitnessed).
Qed.

(** Public collision builder with the entire rank-zero normalization adapter
    inlined.  Only the honest normalized proof resources and the independent
    aligned positive producer remain as premises. *)
Corollary
    raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_normalized_proof_resources_and_witnessed_aligned :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeLocalZeroGuardedCollisionProofResourcesCompilerOnNormalizedResources
    M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA).
Proof.
  intros M hPA hzeroResources haligned.
  exact
    (raw_dynamicTruthNativeLocalCurrentGrowingGuardedCollisionRootsBuilder_of_zero_and_witnessed_aligned
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (raw_dynamicTruthNativeLocalZeroGrowingGuardedCollisionRootsCompilerOnCurrentGuardedHelperContext_of_normalized_proof_resources
        M hPA hzeroResources)
      haligned).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
