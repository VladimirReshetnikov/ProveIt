(**
  Permit the native local callback to grow its witnessed PA context.

  The global-row traversal used by the predecessor-state argument introduces
  finitely many standard PA-axiom witnesses.  The earlier local callback
  boundary required every staged root to remain over the helper context with
  which the callback started.  That requirement was stronger than the
  mathematics and prevented the growing predecessor compiler from being
  threaded into the native successor.

  This file changes only that structural boundary.  A growing root builder
  may return a witnessed PA context containing the original helper context.
  Binder-safe witnessed-context weakening transports the fixed helper batch
  into that returned context.  The established reduced staged-root assembly
  then constructs the local field there and packages it as an ordinary PA
  proof.  No proof-producing arithmetic root is added here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.

(** Transport an ordered fixed-helper family through one inclusion between
    witnessed PA contexts.  Roots may change, but helper order, multiplicity,
    and translated target codes remain literal. *)
Lemma raw_fixedPAHelperBatchLocalProofs_witnessed_inclusion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M) helpers roots
      sourceWitnessList sourceContext targetWitnessList targetContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawFixedPAHelperBatchLocalProofs M translation sourceContext
    helpers roots ->
  exists targetRoots,
    RawFixedPAHelperBatchLocalProofs M translation targetContext
      helpers targetRoots.
Proof.
  intros M hPA translation helpers.
  induction helpers as [| helper helperTail ih]; intros roots
    sourceWitnessList sourceContext targetWitnessList targetContext
    hsource htarget hincluded hroots.
  - destruct roots as [| root rootTail].
    + exists []. exact I.
    + contradiction.
  - destruct roots as [| root rootTail].
    + contradiction.
    + cbn [RawFixedPAHelperBatchLocalProofs] in hroots.
      destruct hroots as [hroot hrootTail].
      destruct
        (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
          M hPA sourceWitnessList sourceContext
          targetWitnessList targetContext
          (rawFixedPAHelperTranslatedTargetCode M translation helper)
          root hsource htarget hincluded hroot)
        as [targetRoot htargetRoot].
      destruct (ih rootTail sourceWitnessList sourceContext
        targetWitnessList targetContext hsource htarget hincluded hrootTail)
        as [targetRootTail htargetRootTail].
      exists (targetRoot :: targetRootTail).
      cbn [RawFixedPAHelperBatchLocalProofs].
      split; assumption.
Qed.

(** Growing counterpart of
    [RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder].  Its returned
    context must be a witnessed extension of the actual current-package
    helper context; hence it cannot switch to an unrelated proof base. *)
Definition RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
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
      exists targetWitnessList targetContext,
        RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
        RawContextListIncluded M baseContext targetContext /\
        RawDynamicTruthNativeLocalReducedStagedRootsAt M targetContext
          sigmaDomain piDomain sigmaEvidence piEvidence
          sigmaRowDomain piRowDomain
          lowerPiApplication lowerSigmaApplication.

Arguments RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
  M translation : clear implicits.

(** Every fixed-context reduced builder is a growing builder by choosing its
    input witnessed context unchanged.  This establishes that the new
    boundary is a genuine relaxation, not an alternative assumption. *)
Theorem
    raw_dynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder_of_fixed
    : forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
    M translation.
Proof.
  intros M translation hfixed tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
    piEvidence hcurrent htrace sigmaRowDomain piRowDomain
    lowerPiApplication lowerSigmaApplication hrows.
  pose proof hcurrent as hfields.
  destruct hfields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hwitnessed & _) ].
  exists witnessList, baseContext.
  split; [exact hwitnessed |].
  split.
  - exact (raw_contextListIncluded_refl M baseContext).
  - exact (hfixed tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal witnessList baseContext helperRoots
      inputGlobalSigma inputGlobalPi sigmaDomain piDomain sigmaEvidence
      piEvidence hcurrent htrace sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication hrows).
Qed.

(** Compile one selected native local target from a growing staged builder.
    The selected trace and exact row parameters are unchanged.  Only after
    the builder chooses its target context do we weaken the fixed helpers and
    run the existing reduced local-field assembly. *)
Theorem
    raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_growing_reduced_current_builder
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
    M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompilerAt M tail level.
Proof.
  intros M hPA translation hagreement hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  destruct
    (raw_dynamicTruthNativeLocalCurrentHelperContextAt_exists
      M hPA translation hagreement tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent)
    as (witnessList & baseContext & helperRoots & hcurrentHelpers).
  intros inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform.
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_of_transform
    M tail level inputGlobalSigma inputGlobalPi fieldCode
    hadequateOrbit htransform) as
    (sigmaDomain & piDomain & sigmaEvidence & piEvidence &
      hfieldCode & htrace).
  destruct (raw_dynamicTruthNativeLocalProofTraceAt_exposes_exact_rows
    M tail level inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPiApplication &
      lowerSigmaApplication & hlinked).
  destruct (hbuilder tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots
    inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    hcurrentHelpers htrace
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
    hlinked) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hbaseIncluded & hstaged).
  pose proof hcurrentHelpers as hcontextFields.
  destruct hcontextFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  destruct
    (raw_fixedPAHelperBatchLocalProofs_witnessed_inclusion
      M hPA translation rawDynamicTruthReadyAndAllMixedQFPAHelpers
      helperRoots witnessList baseContext targetWitnessList targetContext
      hbaseWitnessed htargetWitnessed hbaseIncluded hhelpers)
    as [targetHelperRoots htargetHelpers].
  pose proof
    (raw_dynamicTruthNativeLocalFieldRootOn_of_reduced_staged_roots_and_40_helpers
      M hPA translation targetWitnessList targetContext targetHelperRoots
      tail level inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      hagreement htargetWitnessed htargetHelpers htrace hlinked hstaged)
    as hfieldRoot.
  rewrite hfieldCode.
  exact
    (raw_codedPAProofOf_dynamicTruthNativeLocalFieldRootOn
      M targetWitnessList targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence
      htargetWitnessed hfieldRoot).
Qed.

(** Public local callback endpoint with honest witnessed context growth. *)
Theorem
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_growing_reduced_current_builder
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
    M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_growing_reduced_current_builder
      M hPA translation hagreement hbuilder tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent) as hcompiler.
  destruct
    (raw_dynamicTruthNativeLocalPositiveProof_exists_of_compilerAt
      M hPA tail level hcompiler) as
    (nextLocal & localCertificate & hgraph & hcertificate).
  exists nextLocal, localCertificate.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.
