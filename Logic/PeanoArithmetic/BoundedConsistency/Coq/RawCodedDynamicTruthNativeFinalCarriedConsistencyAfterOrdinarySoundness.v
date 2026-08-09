(**
  Apply ordinary universal soundness after consistency has been carried.

  The older carried bridge adds the ordinary soundness certificate first and
  asks a consistency producer to grow from the resulting base.  The unified
  synchronized construction naturally works in the opposite order: it first
  compiles arithmetic, coherence, and bottom refutation, returning a carried
  implication on a later witnessed base; the direct rule-case compiler then
  returns an ordinary PA certificate.

  This file proves that the order is immaterial.  We open the ordinary
  certificate, merge its witnessed PA context with the carried base, move all
  eleven staged prerequisite roots to that literal common context, and
  transport both the soundness root and the carried implication below the
  same restricted-proof bridge heads.  The result is the exact grown bridge
  consumed by the final staged proof compiler.  No equality between the two
  finite PA contexts is asserted.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPAConsistencyBridgeContextTransport
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency.

Module
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.
Import PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency.

(** Reverse the two growth stages.  The carried implication is first moved
    from its existing base to the honest merge with the ordinary
    certificate's hidden PA-axiom context. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_carried_then_ordinary :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    soundnessCode (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCodedPAProofOf M soundnessCode soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt M
    soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate
    htrace hsoundnessCertificate hfieldsAdequate hcarried.
  destruct hcarried as
    (carriedWitnessList & carriedBaseContext & carriedBridgeRoot &
      hcarriedPrerequisites & _ & hcarriedBridge).
  pose proof hcarriedPrerequisites as hcarriedPrerequisitesCopy.
  destruct hcarriedPrerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      nextShiftRoot & nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hcarriedPrefix _]).
  destruct hcarriedPrefix as
    [hcarriedWitnessed _ _ _ _ _ _ _ _ _ _].

  destruct
    (raw_codedPAProofOf_witnessedLocal_fields
      M soundnessCode soundnessCertificate hsoundnessCertificate)
    as (soundnessWitnessList & soundnessBaseContext & soundnessBaseRoot &
      hsoundnessWitnessed & hsoundnessBase).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      soundnessWitnessList soundnessBaseContext
      carriedWitnessList carriedBaseContext
      hsoundnessWitnessed hcarriedWitnessed)
    as (mergedWitnessList & mergedBaseContext & hmergedWitnessed &
      _ & hsoundnessIncluded & _ & hcarriedIncluded & _).

  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA soundnessWitnessList soundnessBaseContext
      mergedWitnessList mergedBaseContext soundnessCode soundnessBaseRoot
      hsoundnessWitnessed hmergedWitnessed hsoundnessIncluded
      hsoundnessBase)
    as [mergedSoundnessBaseRoot hmergedSoundnessBase].
  pose proof
    (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed_context_transport
      M hPA carriedWitnessList carriedBaseContext
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hcarriedPrerequisites
      hmergedWitnessed hcarriedIncluded)
    as hmergedPrerequisites.

  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  destruct
    (raw_codedPALocalProof_to_restrictedPABridgeContext
      M hPA (raw_succ M level) successorNumeralCode
      mergedWitnessList mergedBaseContext soundnessCode
      mergedSoundnessBaseRoot hnumeral hmergedWitnessed
      hfieldsAdequate hmergedSoundnessBase)
    as [soundnessRoot hsoundness].

  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_all_atomically_adequate_of_witnessed
      M hPA level successorNumeralCode mergedWitnessList mergedBaseContext
      hnumeral hmergedWitnessed)
    as hmergedBridgeAdequate.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      carriedWitnessList carriedBaseContext hcarriedWitnessed)
    as hcarriedRealizable.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      mergedWitnessList mergedBaseContext hmergedWitnessed)
    as hmergedRealizable.
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeContext_transport
      M hPA successorNumeralCode carriedBaseContext mergedBaseContext
      (rawFormulaImpCode M soundnessCode nextFinal) carriedBridgeRoot
      hcarriedRealizable hmergedRealizable hcarriedIncluded
      hmergedBridgeAdequate hcarriedBridge)
    as [consistencyBridgeRoot hconsistencyBridge].

  exists mergedWitnessList, mergedBaseContext,
    soundnessRoot, consistencyBridgeRoot.
  split; [exact hmergedPrerequisites |].
  split; assumption.
Qed.

(** Direct-code specialization for the derivation-soundness sentence. *)
Corollary
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_carried_then_ordinary :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt M
    inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate
    htrace hsoundness hfields hcarried.
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_carried_then_ordinary
      M hPA
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      soundnessCertificate htrace hsoundness hfields hcarried).
Qed.

(** Once the represented rule cases yield an ordinary direct-soundness
    certificate, the already-carried implication reaches the literal final
    staged proof certificate with no further consistency producer. *)
Corollary
    raw_dynamicTruthNativeFinalStagedNextFinalProof_of_direct_carried_then_ordinary :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    soundnessCertificate ->
  RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      tail level nextFinal finalCertificate.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode sourceBaseContext soundnessCertificate
    htrace hsoundness hcarried.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  pose proof
    (raw_restrictedPAProofFieldsCode_atomically_adequate
      M hPA level successorNumeralCode hnumeral) as hfields.
  apply
    (raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode htrace).
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_carried_then_ordinary
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
      soundnessCertificate htrace hsoundness hfields hcarried).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterOrdinarySoundness.
