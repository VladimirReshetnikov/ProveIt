(**
  Isolate predecessor-state arithmetic inside the growing native callback.

  The reduced local staged package contains four current-kernel roots.  Only
  one of them is the predecessor-state implication produced by global-row
  traversal.  This module factors that root out, permits its compiler to grow
  the witnessed PA context, and leaves the other three collision roots in a
  dependency-ordered remainder builder.

  At a positive current level, consecutive native traces provide an aligned
  predecessor record.  A compiler need only return the three logical roots
  (admissibility, Sigma evidence, and Pi evidence) on a witnessed extension;
  the already proved native-trace closure turns those roots into the universal
  predecessor implication.  The zero case remains a separate exact callback.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthNativeLocalDecisionRootCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalDecisionRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.

(** The three current-kernel roots unrelated to predecessor global rows. *)
Record RawDynamicTruthNativeLocalReducedCurrentKernelTailInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Type := {
  rawDynamicTruthNativeLocalReducedKernelTail_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalReducedKernelTail_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalReducedKernelTail_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalReducedCurrentKernelTailInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Reduced staged resources with the predecessor implication removed. *)
Definition RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication : M) : Prop :=
  RawDynamicTruthNativeLocalDomainCaseDecisionRootsAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence /\
  RawDynamicTruthLocalRootAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    (rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain lowerPiApplication) /\
  RawDynamicTruthLocalRootAt M
    (rawDynamicTruthNativeLocalExclusivePiContextOn M baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence)
    (rawDynamicTruthPiSuccessorRowCode M
      piRowDomain lowerSigmaApplication) /\
  exists currentKernelTail :
      RawDynamicTruthNativeLocalReducedCurrentKernelTailInputsAt
        M baseContext lowerPiApplication lowerSigmaApplication,
    True.

Arguments RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
  : clear implicits.

(** Reinsert the separately compiled predecessor root into the historical
    reduced staged package. *)
Theorem raw_dynamicTruthNativeLocalReducedStagedRootsAt_of_predecessor_and_tail
    : forall (M : RawPAModel) baseContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalRootAt M baseContext
    (rawDynamicTruthImpPredecessorStateExclusivityCode M) ->
  RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalReducedStagedRootsAt M
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication.
Proof.
  intros M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hpredecessor (hcases & hsigmaRow & hpiRow & kernelTail & _).
  split; [exact hcases |].
  split; [exact hsigmaRow |].
  split; [exact hpiRow |].
  exists
    {| rawDynamicTruthNativeLocalReducedKernel_predecessorRoot :=
         hpredecessor;
       rawDynamicTruthNativeLocalReducedKernel_sigmaExCrossRoot :=
         rawDynamicTruthNativeLocalReducedKernelTail_sigmaExCrossRoot
           M baseContext lowerPiApplication lowerSigmaApplication kernelTail;
       rawDynamicTruthNativeLocalReducedKernel_sigmaAllCrossRoot :=
         rawDynamicTruthNativeLocalReducedKernelTail_sigmaAllCrossRoot
           M baseContext lowerPiApplication lowerSigmaApplication kernelTail;
       rawDynamicTruthNativeLocalReducedKernel_mixedReplayRoot :=
         rawDynamicTruthNativeLocalReducedKernelTail_mixedReplayRoot
           M baseContext lowerPiApplication lowerSigmaApplication kernelTail
    |}.
  exact I.
Qed.

(** Exact context-growing producer for the one predecessor implication. *)
Definition RawDynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpPredecessorStateExclusivityCode M).

Arguments RawDynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder
  M translation : clear implicits.

(** Zero-current callback.  Its arguments are exactly the left alternative
    of the proved current-package case split. *)
Definition RawDynamicTruthNativeLocalZeroPredecessorRootCompiler
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence currentLocalRoot,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalProofTraceAt M tail level
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain
      sigmaEvidence piEvidence ->
    level = raw_zero M ->
    currentLocal = rawQuotedFormulaCode M
      dynamicTruthLocalDecisionExclusiveBaseFormula ->
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpPredecessorStateExclusivityCode M).

Arguments RawDynamicTruthNativeLocalZeroPredecessorRootCompiler
  M translation : clear implicits.

(** Positive-current arithmetic boundary.  The aligned native record fixes
    all predecessor row parameters; the compiler returns only the three
    logical roots on one witnessed extension. *)
Definition RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi),
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
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

Arguments RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompiler M
  : clear implicits.

(** Callback form used by the actual current-package assembly.  Unlike the
    context-only interface above, it receives the concrete witness list which
    the helper package already carries.  This is strictly weaker: a global
    row compiler need not rediscover a witness for its source context. *)
Definition
    RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase
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
      RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
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
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase
  M : clear implicits.

(** Assemble the predecessor producer by the exact zero/successor split.
    In the successor branch the logical-roots compiler is closed against the
    carried exclusivity projection by the native-trace theorem. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder_of_zero_and_aligned_logical_roots
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroPredecessorRootCompiler M translation ->
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompiler M ->
  RawDynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder
    M translation.
Proof.
  intros M hPA translation hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hcurrent htrace) as
    [(currentLocalRoot & hlevel & hfield & hcurrentRoot) |
      (predecessorLevel & hlevel & aligned & _)].
  - exact (hzero tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence currentLocalRoot hcurrent htrace hlevel hfield
      hcurrentRoot).
  - destruct (haligned tail predecessorLevel baseContext currentLocal
      inputGlobalSigma inputGlobalPi aligned) as
      (targetWitnessList & targetContext & htargetWitnessed &
        hincluded & hlogicalRoots).
    pose proof hcurrent as hfields.
    destruct hfields as
      [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
        currentSubstitutionRoot & currentAxiomSoundnessRoot &
        currentFinalRoot & hbaseWitnessed & _) ].
    exists targetWitnessList, targetContext.
    split; [exact htargetWitnessed |].
    split; [exact hincluded |].
    exact
      (raw_dynamicTruthNativeLocalAligned_predecessorRoot_on_witnessed_extension_logical_roots
        M hPA tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned
        targetWitnessList targetContext
        (raw_codedPAAxiomWitnessContext_context_realizable M
          witnessList baseContext hbaseWitnessed)
        htargetWitnessed hincluded hlogicalRoots).
Qed.

(** Preferred assembly: pass the witness list already stored by the current
    helper context to the aligned global-row compiler. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder_of_zero_and_witnessed_aligned_logical_roots
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroPredecessorRootCompiler M translation ->
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase
    M ->
  RawDynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder
    M translation.
Proof.
  intros M hPA translation hzero haligned tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exact_cases_aligned_with_next
      M hPA translation tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hcurrent htrace) as
    [(currentLocalRoot & hlevel & hfield & hcurrentRoot) |
      (predecessorLevel & hlevel & aligned & _)].
  - exact (hzero tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence currentLocalRoot hcurrent htrace hlevel hfield
      hcurrentRoot).
  - pose proof hcurrent as hfields.
    destruct hfields as
      [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
        currentSubstitutionRoot & currentAxiomSoundnessRoot &
        currentFinalRoot & hbaseWitnessed & _) ].
    destruct (haligned tail predecessorLevel baseContext currentLocal
      inputGlobalSigma inputGlobalPi aligned witnessList hbaseWitnessed) as
      (targetWitnessList & targetContext & htargetWitnessed &
        hincluded & hlogicalRoots).
    exists targetWitnessList, targetContext.
    split; [exact htargetWitnessed |].
    split; [exact hincluded |].
    exact
      (raw_dynamicTruthNativeLocalAligned_predecessorRoot_on_witnessed_extension_logical_roots
        M hPA tail predecessorLevel baseContext currentLocal
        inputGlobalSigma inputGlobalPi aligned
        targetWitnessList targetContext
        (raw_codedPAAxiomWitnessContext_context_realizable M
          witnessList baseContext hbaseWitnessed)
        htargetWitnessed hincluded hlogicalRoots).
Qed.

(** The remaining reduced staged resources are requested only after the
    predecessor producer has fixed its target context and root. *)
Definition RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext (helperRoots : list M)
      inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
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
    forall targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
      RawContextListIncluded M baseContext targetContext ->
      RawDynamicTruthLocalRootAt M targetContext
        (rawDynamicTruthImpPredecessorStateExclusivityCode M) ->
      RawDynamicTruthNativeLocalReducedStagedRootsWithoutPredecessorAt M
        targetContext sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication.

Arguments
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
  M translation : clear implicits.

(** Dependency-ordered composition of the separately growing predecessor
    root and the fixed-target remainder. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder_of_predecessor_and_remainder
    : forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder
    M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
    M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
    M translation.
Proof.
  intros M translation hpredecessor hremainder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows.
  destruct (hpredecessor tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hpredecessorRoot).
  pose proof (hremainder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows
    targetWitnessList targetContext htargetWitnessed hincluded
    hpredecessorRoot) as htail.
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact
    (raw_dynamicTruthNativeLocalReducedStagedRootsAt_of_predecessor_and_tail
      M targetContext sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hpredecessorRoot htail).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
