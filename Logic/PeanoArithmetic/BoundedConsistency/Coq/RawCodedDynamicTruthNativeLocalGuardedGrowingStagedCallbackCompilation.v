(**
  Growing native callback through the predecessor-free guarded matrix.

  The guarded reduced field theorem is indexed by a witnessed context that
  already carries the corrected forty-two-helper batch.  The native staged
  callback may have to enlarge that context while it constructs the guarded
  predecessor and the remaining collision pairs.  This module supplies the
  exact structural adapter: transport the fixed helpers to the returned
  witnessed extension, run the guarded reduced field compiler there, and
  package the resulting local root as an ordinary PA proof.

  No new arithmetic premise is introduced here.  The sole proof-producing
  boundary is the growing guarded reduced staged-root builder, whose result
  is the predecessor-free package defined in the preceding module.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation
  RawCodedDynamicTruthNativeLocalHelperBatchGeneralization
  RawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

(** Context-growing producer for the corrected reduced package.  Its source
    is the literal guarded helper context generated from the current six
    fields; its target must witness and include that source context. *)
Definition
    RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
    (M : RawPAModel)
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
    forall sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication,
      RawDynamicTruthNativeLocalExactRowParametersAt M level
        inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain
        lowerPiApplication lowerSigmaApplication ->
      exists targetWitnessList targetContext,
        RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
        RawContextListIncluded M baseContext targetContext /\
        RawDynamicTruthNativeLocalGuardedReducedStagedRootsAt M
          targetContext sigmaDomain piDomain sigmaEvidence piEvidence
          sigmaRowDomain piRowDomain
          lowerPiApplication lowerSigmaApplication.

Arguments
  RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
  M translation : clear implicits.

(** Reduce one current package and one selected transform to an ordinary PA
    proof.  The forty-two helpers are weakened only after the builder has
    chosen its target, so their order and the guarded suffix stay literal. *)
Theorem
    raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_growing_guarded_reduced_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
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
    (raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_exists
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
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    in hcontextFields.
  destruct hcontextFields as
    [_ (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & hbaseWitnessed & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers)].
  destruct
    (raw_fixedPAHelperBatchLocalProofs_witnessed_inclusion
      M hPA translation rawDynamicTruthReadyAndGuardedMixedQFPAHelpers
      helperRoots witnessList baseContext targetWitnessList targetContext
      hbaseWitnessed htargetWitnessed hbaseIncluded hhelpers)
    as [targetHelperRoots htargetHelpers].
  pose proof
    (raw_dynamicTruthNativeLocalFieldRootOn_of_guarded_reduced_staged_roots_and_42_helpers
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

(** Public guarded callback endpoint with witnessed context growth. *)
Theorem
    raw_dynamicTruthNativeStagedNextLocalCompiler_of_growing_guarded_reduced_current_builder :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
    M translation ->
  RawDynamicTruthNativeStagedNextLocalCompiler M.
Proof.
  intros M hPA translation hagreement hbuilder
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_dynamicTruthNativeLocalDecisionExclusiveProofCompilerAt_of_growing_guarded_reduced_current_builder
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
  PABoundedRawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation.
