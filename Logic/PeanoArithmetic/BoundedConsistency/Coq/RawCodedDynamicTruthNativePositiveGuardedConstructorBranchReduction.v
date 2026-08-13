(**
  Isolate the constructor-coordinate residue in the positive guarded callback.

  The positive append compiler already produces the three predecessor-state
  logical roots under a live caller prefix.  Those roots do not, by
  themselves, inhabit the three deeper constructor-specific prefixes used by
  guarded implication, conjunction, and disjunction.  This module therefore
  exposes exactly those three branch packages as the remaining continuation.

  Everything after the branch packages is proved here: each constructor is
  closed on its own witnessed PA extension, the two Boolean diagonals are
  synchronized, and that pair is finally synchronized with implication.  At
  every stage the literal caller prefix is retained; no prefix contraction or
  bare canonical-application principle is assumed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedContextLists
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedLtSuccCasesProofCompilation
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation
  RawCodedDynamicTruthNativeZeroGuardedCollisionCompilation
  RawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativePositiveAssumptionRetainingPermutedAppendCompilation.

Module
  PABoundedRawCodedDynamicTruthNativePositiveGuardedConstructorBranchReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativePositiveAssumptionRetainingPermutedAppendCompilation.

(** The three constructor-local packages may grow their standard-PA witness
    tails independently.  Their common source and their caller prefix are
    nevertheless literal, not merely extensionally related. *)
Record
    RawDynamicTruthGuardedConstructorBranchRootsOnWitnessedExtensionsUnderCallerPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (sourceContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthGuardedConstructorBranches_imp :
    exists witnessList context,
      RawCodedPAAxiomWitnessContext M witnessList context /\
      RawContextListIncluded M sourceContext context /\
      RawDynamicTruthImpGuardedBranchRootsAt M translation
        context callerPrefix;
  rawDynamicTruthGuardedConstructorBranches_and :
    exists witnessList context,
      RawCodedPAAxiomWitnessContext M witnessList context /\
      RawContextListIncluded M sourceContext context /\
      RawDynamicTruthBooleanGuardedBranchRootsAt DTBooleanAnd M translation
        context callerPrefix;
  rawDynamicTruthGuardedConstructorBranches_or :
    exists witnessList context,
      RawCodedPAAxiomWitnessContext M witnessList context /\
      RawContextListIncluded M sourceContext context /\
      RawDynamicTruthBooleanGuardedBranchRootsAt DTBooleanOr M translation
        context callerPrefix
}.

Arguments
  RawDynamicTruthGuardedConstructorBranchRootsOnWitnessedExtensionsUnderCallerPrefixAt
  M translation sourceContext callerPrefix : clear implicits.

(** Close and synchronize the three packages.  This theorem is the
    proof-producing part removed from the old opaque logical-to-collision
    continuation. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_of_constructor_branch_roots_on_witnessed_extensions :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext callerPrefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthGuardedConstructorBranchRootsOnWitnessedExtensionsUnderCallerPrefixAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    sourceContext callerPrefix ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext callerPrefix
    hsource hbranches.
  destruct hbranches as
    [(impWitnessList & impContext & himpWitnessed & hsourceImpIncluded &
        himpBranches)
     (andWitnessList & andContext & handWitnessed & hsourceAndIncluded &
        handBranches)
     (orWitnessList & orContext & horWitnessed & hsourceOrIncluded &
        horBranches)].
  destruct
    (raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      impWitnessList impContext callerPrefix
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      himpWitnessed himpBranches) as
    (impTargetWitnessList & impTargetContext & impRoot &
      himpTargetWitnessed & himpTargetIncluded & himp).
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_under_caller_prefix
      DTBooleanAnd M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      andWitnessList andContext callerPrefix
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs callerPrefix)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs
        (coqDynamicTruthBooleanGuardedDeepPrefix
          DTBooleanAnd callerPrefix))
      handWitnessed handBranches) as
    (andTargetWitnessList & andTargetContext & andRoot &
      handTargetWitnessed & handTargetIncluded & hand).
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_under_caller_prefix
      DTBooleanOr M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      orWitnessList orContext callerPrefix
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs callerPrefix)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs
        (coqDynamicTruthBooleanGuardedDeepPrefix
          DTBooleanOr callerPrefix))
      horWitnessed horBranches) as
    (orTargetWitnessList & orTargetContext & orRoot &
      horTargetWitnessed & horTargetIncluded & hor).
  assert (handGrowing :
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sourceWitnessList sourceContext callerPrefix
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
          (rawFormulaImpCode M
            (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
            (rawFormulaBotCode M)))).
  {
    exists andTargetWitnessList, andTargetContext, andRoot.
    split; [exact handTargetWitnessed |].
    split.
    - intros member hmember.
      exact (handTargetIncluded member
        (hsourceAndIncluded member hmember)).
    - exact hand.
  }
  assert (horGrowing :
      RawCodedPAGrowingTemplateLocalProofAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sourceWitnessList sourceContext callerPrefix
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
          (rawFormulaImpCode M
            (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
            (rawFormulaBotCode M)))).
  {
    exists orTargetWitnessList, orTargetContext, orRoot.
    split; [exact horTargetWitnessed |].
    split.
    - intros member hmember.
      exact (horTargetIncluded member
        (hsourceOrIncluded member hmember)).
    - exact hor.
  }
  destruct
    (raw_dynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt_of_independently_growing_roots
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext callerPrefix handGrowing horGrowing) as
    (booleanWitnessList & booleanContext & hbooleanWitnessed &
      hsourceBooleanIncluded & hboolean).
  assert (hsourceImpTargetIncluded :
      RawContextListIncluded M sourceContext impTargetContext).
  {
    intros member hmember.
    exact (himpTargetIncluded member
      (hsourceImpIncluded member hmember)).
  }
  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_merge_boolean_and_imp
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext callerPrefix booleanWitnessList booleanContext
      impTargetWitnessList impTargetContext impRoot
      hbooleanWitnessed hsourceBooleanIncluded hboolean
      himpTargetWitnessed hsourceImpTargetIncluded himp).
Qed.

(** Call-site-exact remainder.  It intentionally accepts the already
    compiled logical roots even though only a future branch producer needs
    to inspect them: this makes the reduction plug into the positive append
    endpoint without changing the lifetime of any assumption. *)
Definition
    RawDynamicTruthNativeAlignedLogicalRootsToGuardedConstructorBranchRootsContinuationUnderCallerPrefix
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
    RawDynamicTruthGuardedConstructorBranchRootsOnWitnessedExtensionsUnderCallerPrefixAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      logicalContext callerPrefix.

Arguments
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedConstructorBranchRootsContinuationUnderCallerPrefix
  M hPA : clear implicits.

(** The new continuation is sufficient for the old collision continuation;
    the proof above discharges every remaining constructor closure and merge. *)
Theorem
    raw_dynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix_of_constructor_branch_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedConstructorBranchRootsContinuationUnderCallerPrefix
    M hPA ->
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix
    M hPA.
Proof.
  intros M hPA hcontinuation tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    callerPrefix inputs logicalWitnessList logicalContext hsource
    hrestrictedIn hruleIn hlogicalWitnessed hbaseLogicalIncluded
    hlogicalRoots.
  pose proof
    (hcontinuation tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
      callerPrefix inputs logicalWitnessList logicalContext hsource
      hrestrictedIn hruleIn hlogicalWitnessed hbaseLogicalIncluded
      hlogicalRoots) as hbranches.
  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_of_constructor_branch_roots_on_witnessed_extensions
      M hPA inputs logicalWitnessList logicalContext callerPrefix
      hlogicalWitnessed hbranches).
Qed.

(** Sharp dependency boundary obtained by replacing only the old opaque
    continuation field. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputConstructorBranchSplitGrowingKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA /\
  RawDynamicTruthNativeAlignedStrongStepPermutedAppendInputResourcesCompilerWithPA
    M hPA /\
  RawDynamicTruthNativeAlignedLogicalRootsToGuardedConstructorBranchRootsContinuationUnderCallerPrefix
    M hPA /\
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA) /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputConstructorBranchSplitGrowingKernelCompilers
  M hPA : clear implicits.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers_of_constructor_branch_split :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputConstructorBranchSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA
    (hzero & hpositive & hbranches & hremainder & hcrossLevel & hshift &
      hsubstitution & haxiom & hfinal).
  split; [exact hzero |].
  split; [exact hpositive |].
  split.
  - exact
      (raw_dynamicTruthNativeAlignedLogicalRootsToGuardedCollisionContinuationUnderCallerPrefix_of_constructor_branch_roots
        M hPA hbranches).
  - split; [exact hremainder |].
    split; [exact hcrossLevel |].
    split; [exact hshift |].
    split; [exact hsubstitution |].
    split; [exact haxiom | exact hfinal].
Qed.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_constructor_branch_split :
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputConstructorBranchSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA hresources.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_positive_permuted_append_inputs
      M hPA
      (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingPositivePermutedAppendInputResourceSplitGrowingKernelCompilers_of_constructor_branch_split
        M hPA hresources)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativePositiveGuardedConstructorBranchReduction.
