(**
  Carry the final universal-soundness bridge through one more PA-context
  extension.

  An ordinary soundness certificate is first merged with the staged roots.
  Some of the arithmetic and list theorems used by the consistency shell may
  then require a further finite prefix of the standard PA axioms.  The older
  growing bridge stopped after the first merge and therefore required the
  consistency implication in that exact intermediate context.

  This module exposes the honest interface.  A pointwise consistency
  producer may return a later witnessed context containing the intermediate
  base.  Represented witnessed-context weakening transports the ordinary
  soundness root to that later base; the existing binder-safe bridge
  transport then places it below the four restricted-proof heads.  No
  equality between the two contexts and no truth-to-proof callback is used.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

(** A consistency implication carried from [sourceBaseContext] to a later
    witnessed base.  The full staged prerequisite package is retained at the
    target so the final structural closer can consume the returned context. *)
Definition RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt
    (M : RawPAModel) (soundnessCode : M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode sourceBaseContext : M) : Prop :=
  exists finalWitnessList finalBaseContext bridgeRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      finalWitnessList finalBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawContextListIncluded M sourceBaseContext finalBaseContext /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode finalBaseContext)
      (rawFormulaImpCode M soundnessCode nextFinal)
      bridgeRoot.

Arguments RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt
  M soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext : clear implicits.

(** The generic two-stage accumulator.  The first stage merges the ordinary
    PA certificate into the staged base.  The supplied carried compiler may
    extend that merged base once more; witnessed-context weakening then moves
    the local soundness root to the exact final base before the four bridge
    heads are introduced. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_ordinary_carried
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      soundnessCode (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawCodedPAProofOf M soundnessCode soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  (forall mergedWitnessList mergedBaseContext,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt
      M soundnessCode tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode mergedBaseContext) ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt
    M soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    soundnessCertificate htrace hprerequisites hsoundnessCertificate
    hfieldsAdequate hcarried.
  destruct
    (raw_dynamicTruthNativeFinalStagedPrerequisites_add_proof
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness soundnessCode soundnessCertificate
      hprerequisites hsoundnessCertificate)
    as (mergedWitnessList & mergedBaseContext & soundnessBaseRoot &
      hmergedPrerequisites & hsoundnessBase).
  destruct (hcarried mergedWitnessList mergedBaseContext
    hmergedPrerequisites) as
    (finalWitnessList & finalBaseContext & bridgeRoot &
      hfinalPrerequisites & hmergedIncluded & hbridge).

  pose proof hmergedPrerequisites as hmergedPrerequisitesCopy.
  destruct hmergedPrerequisitesCopy as
    (currentLocalRoot0 & currentCrossLevelRoot0 & currentShiftRoot0 &
      currentSubstitutionRoot0 & currentAxiomSoundnessRoot0 &
      currentFinalRoot0 & nextLocalRoot0 & nextCrossLevelRoot0 &
      nextShiftRoot0 & nextSubstitutionRoot0 & nextAxiomSoundnessRoot0 &
      [hmergedPrefix _]).
  destruct hmergedPrefix as [hmergedWitnessed _ _ _ _ _ _ _ _ _ _].
  pose proof hfinalPrerequisites as hfinalPrerequisitesCopy.
  destruct hfinalPrerequisitesCopy as
    (currentLocalRoot1 & currentCrossLevelRoot1 & currentShiftRoot1 &
      currentSubstitutionRoot1 & currentAxiomSoundnessRoot1 &
      currentFinalRoot1 & nextLocalRoot1 & nextCrossLevelRoot1 &
      nextShiftRoot1 & nextSubstitutionRoot1 & nextAxiomSoundnessRoot1 &
      [hfinalPrefix _]).
  destruct hfinalPrefix as [hfinalWitnessed _ _ _ _ _ _ _ _ _ _].

  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA mergedWitnessList mergedBaseContext
      finalWitnessList finalBaseContext soundnessCode soundnessBaseRoot
      hmergedWitnessed hfinalWitnessed hmergedIncluded hsoundnessBase)
    as [finalSoundnessBaseRoot hfinalSoundnessBase].
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  destruct (raw_codedPALocalProof_to_restrictedPABridgeContext
    M hPA (raw_succ M level) successorNumeralCode
    finalWitnessList finalBaseContext soundnessCode
    finalSoundnessBaseRoot hnumeral hfinalWitnessed
    hfieldsAdequate hfinalSoundnessBase)
    as [soundnessRoot hsoundness].
  exists finalWitnessList, finalBaseContext, soundnessRoot, bridgeRoot.
  exact (conj hfinalPrerequisites (conj hsoundness hbridge)).
Qed.

(** Direct-code specialization used by the native final construction. *)
Corollary
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary_carried
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  (forall mergedWitnessList mergedBaseContext,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode mergedBaseContext) ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    soundnessCertificate htrace hprerequisites hsoundnessCertificate
    hfieldsAdequate hcarried.
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_ordinary_carried
      M hPA
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate htrace hprerequisites hsoundnessCertificate
      hfieldsAdequate hcarried).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
