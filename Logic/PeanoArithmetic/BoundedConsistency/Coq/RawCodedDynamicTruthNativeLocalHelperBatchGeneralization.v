(**
  General finite-helper contexts for the native local staged callback.

  The historical callback context was tied to one forty-helper list even
  though its construction uses the fully generic fixed-helper master.  This
  file factors the six synchronized current-field roots over an arbitrary
  finite helper batch.  The guarded implication integration then specializes
  the generic package to forty-two helpers and projects the exact legacy
  prefix for unchanged consumers.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.

(** The six current fields and the helper family share one witnessed PA
    context.  No property of [helpers] is required beyond finiteness of its
    metatheoretic list. *)
Definition RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (helpers : list RawFixedPAHelper)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext : M) (helperRoots : list M) : Prop :=
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal /\
  exists currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      currentLocal currentLocalRoot /\
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot /\
    RawCodedPALocalProofOf M baseContext
      currentShift currentShiftRoot /\
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot /\
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot /\
    RawCodedPALocalProofOf M baseContext
      currentFinal currentFinalRoot /\
    RawFixedPAHelperBatchLocalProofs M translation baseContext
      helpers helperRoots.

Arguments RawDynamicTruthNativeLocalCurrentHelperBatchContextAt
  M translation helpers tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
  : clear implicits.

(** The generic fixed-helper master supplies this package for every finite
    helper family.  Thus adding a PA helper never changes the current graph
    hypothesis or requires a new callback residual. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperBatchContextAt_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall helpers (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  exists witnessList baseContext : M, exists helperRoots : list M,
    RawDynamicTruthNativeLocalCurrentHelperBatchContextAt M translation
      helpers tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots.
Proof.
  intros M hPA translation hagreement helpers tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  pose proof
    (raw_sixFieldMasterCommonContextProofsWithFixedPAHelperBatch
      M hPA translation hagreement
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal helpers (proj2 hcurrent))
    as hpackage.
  unfold RawSixFieldMasterCommonContextProofsWithFixedPAHelperBatchOf
    in hpackage.
  destruct hpackage as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & helperRoots & hwitness & hcurrentLocal &
      hcurrentCrossLevel & hcurrentShift & hcurrentSubstitution &
      hcurrentAxiomSoundness & hcurrentFinal & hhelpers).
  exists witnessList, baseContext, helperRoots.
  split; [exact hcurrent |].
  exists currentLocalRoot, currentCrossLevelRoot, currentShiftRoot,
    currentSubstitutionRoot, currentAxiomSoundnessRoot, currentFinalRoot.
  split; [exact hwitness |].
  split; [exact hcurrentLocal |].
  split; [exact hcurrentCrossLevel |].
  split; [exact hcurrentShift |].
  split; [exact hcurrentSubstitution |].
  split; [exact hcurrentAxiomSoundness |].
  split; [exact hcurrentFinal | exact hhelpers].
Qed.

(** Project a helper prefix while retaining all six field roots verbatim.
    The projected root list is computational, so this theorem does not rely
    on choice or eliminate a propositional list witness. *)
Theorem raw_dynamicTruthNativeLocalCurrentHelperBatchContextAt_prefix :
    forall (M : RawPAModel) translation prefix suffix
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentHelperBatchContextAt M translation
    (prefix ++ suffix) tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalCurrentHelperBatchContextAt M translation
    prefix tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext (firstn (length prefix) helperRoots).
Proof.
  intros M translation prefix suffix tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    [hcurrent (localRoot & crossRoot & shiftRoot & substitutionRoot &
      axiomRoot & finalRoot & hwitness & hlocal & hcross & hshift &
      hsubstitution & haxiom & hfinal & hhelpers)].
  split; [exact hcurrent |].
  exists localRoot, crossRoot, shiftRoot, substitutionRoot, axiomRoot,
    finalRoot.
  split; [exact hwitness |].
  split; [exact hlocal |].
  split; [exact hcross |].
  split; [exact hshift |].
  split; [exact hsubstitution |].
  split; [exact haxiom |].
  split; [exact hfinal |].
  exact (raw_fixedPAHelperBatchLocalProofs_app_prefix_firstn M
    translation baseContext prefix suffix helperRoots hhelpers).
Qed.

Definition RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext : M) (helperRoots : list M) : Prop :=
  RawDynamicTruthNativeLocalCurrentHelperBatchContextAt M translation
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots.

Arguments RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt
  M translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
  : clear implicits.

Corollary raw_dynamicTruthNativeLocalCurrentGuardedHelperContextAt_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  exists witnessList baseContext : M, exists helperRoots : list M,
    RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots.
Proof.
  intros M hPA translation hagreement tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent.
  exact (raw_dynamicTruthNativeLocalCurrentHelperBatchContextAt_exists
    M hPA translation hagreement
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent).
Qed.

(** Compatibility projection to the established forty-helper callback
    context.  It is definitionally the prefix of the guarded package. *)
Corollary
    raw_dynamicTruthNativeLocalCurrentHelperContextAt_of_guarded :
    forall (M : RawPAModel) translation
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots,
  RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext helperRoots ->
  RawDynamicTruthNativeLocalCurrentHelperContextAt M translation
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    witnessList baseContext
      (firstn (length rawDynamicTruthReadyAndAllMixedQFPAHelpers)
        helperRoots).
Proof.
  intros M translation tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal witnessList baseContext helperRoots
    hguarded.
  unfold RawDynamicTruthNativeLocalCurrentGuardedHelperContextAt in hguarded.
  unfold rawDynamicTruthReadyAndGuardedMixedQFPAHelpers in hguarded.
  pose proof
    (raw_dynamicTruthNativeLocalCurrentHelperBatchContextAt_prefix
      M translation rawDynamicTruthReadyAndAllMixedQFPAHelpers
      rawDynamicTruthGuardedImpCollisionFixedPAHelpers
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal
      witnessList baseContext helperRoots hguarded) as hprefix.
  exact hprefix.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalHelperBatchGeneralization.
