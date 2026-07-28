(**
  Grow the final staged context by an ordinary universal-soundness proof.

  An ordinary PA proof hides its own witnessed PA-axiom context.  The final
  dynamic-truth stage also carries eleven roots in a witnessed context, but
  there is no reason for those two contexts to be literally equal.  This
  file joins them honestly: it merges the two witnessed contexts, transports
  every old staged root, and only then reconstructs the context-dependent
  consistency bridge over the merged base.

  The result is deliberately pointwise and existential in the grown base.
  It does not claim to implement the older rigid compiler whose result must
  live over the caller's original [baseContext].  This distinction matters
  when the ordinary proof uses an induction instance or any other PA axiom
  absent from that original context.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateStructuralTranslation
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAOrdinaryProofWitnessedContextAccumulation
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAOrdinaryProofWitnessedContextAccumulation.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.

(** ------------------------------------------------------------------
    Binder-safe transport from a witnessed base to the exact final bridge. *)

(** The selected-axiom transport proved earlier is independent of the
    transported conclusion.  This factored form exposes that generality and
    is used below for the newly accumulated universal-soundness root.

    Atomic adequacy of the three shifted heads follows from their represented
    context shifts.  The one genuinely new syntactic obligation is therefore
    adequacy of the projected-fields head. *)
Theorem raw_codedPALocalProof_to_restrictedPABridgeContext : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      numeralValue numeralCode witnessList baseContext conclusion root,
  RawNumeralTermCodeAt M numeralValue numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M numeralCode) ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode baseContext)
      conclusion transportedRoot.
Proof.
  intros M hPA numeralValue numeralCode witnessList baseContext
    conclusion root hnumeral hwitness hfieldsAdequate hlocal.
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext numeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext numeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      numeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA numeralValue numeralCode baseContext hnumeral hbaseShift).
  }
  destruct hcontexts as [_ [_ hproofShift]].
  assert (hshiftedProofRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterProofContextCode M numeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  assert (hshiftedProofAdequate :
      RawContextAllAtomicallyAdequate M shiftedProofContext).
  {
    exact (raw_contextShift_target_all_atomically_adequate M hPA
      (rawRestrictedPAAfterProofContextCode M numeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  set (bridgeContext := rawCoqRestrictedPAConsistencyBridgeContextCode
    M numeralCode baseContext).
  assert (hbridgeRealizable : RawContextListRealizable M bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode.
    exact (raw_contextList_cons_realizable M hPA shiftedProofContext
      (rawRestrictedPAProofFieldsCode M numeralCode)
      hshiftedProofRealizable).
  }
  assert (hbridgeAdequate :
      RawContextAllAtomicallyAdequate M bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode.
    exact (raw_contextAllAtomicallyAdequate_cons M hPA shiftedProofContext
      (rawRestrictedPAProofFieldsCode M numeralCode)
      hshiftedProofAdequate hfieldsAdequate).
  }
  assert (hbaseIncluded : RawContextListIncluded M baseContext bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode, shiftedProofContext,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextListIncluded_cons_target M hPA).
    exact (raw_contextListIncluded_refl M baseContext).
  }
  assert (hbridgeReady :
      RawContextBinderReady M baseContext bridgeContext).
  {
    exact (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA baseContext bridgeContext hbaseIncluded hbridgeAdequate).
  }
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA baseContext bridgeContext conclusion root
      hbaseRealizable hbridgeRealizable hbaseIncluded hbridgeReady hlocal)
    as [transportedRoot htransported].
  exists transportedRoot.
  unfold bridgeContext in htransported.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Add one ordinary certificate to all eleven final staged roots. *)

(** Open [newCertificate], merge its hidden witnessed context with the
    staged base, and transport every existing root through the uniform
    context-transport relation returned by the completed merge theorem. *)
Theorem raw_dynamicTruthNativeFinalStagedPrerequisites_add_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      newConclusion newCertificate,
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness ->
  RawCodedPAProofOf M newConclusion newCertificate ->
  exists mergedWitnessList mergedBaseContext newRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawCodedPALocalProofOf M mergedBaseContext newConclusion newRoot.
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    newConclusion newCertificate hprerequisites hnewCertificate.
  destruct hprerequisites as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomSoundness]).
  destruct hprefix as
    [hwitnessed hcurrentLocal hcurrentCrossLevel hcurrentShift
      hcurrentSubstitution hcurrentAxiomSoundness hcurrentFinal
      hnextLocal hnextCrossLevel hnextShift hnextSubstitution].
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA newConclusion newCertificate witnessList baseContext
    hnewCertificate hwitnessed) as
    (mergedWitnessList & mergedBaseContext & newRoot &
      hmergedWitnessed & htransport & hnewLocal).
  destruct (htransport currentLocal currentLocalRoot hcurrentLocal) as
    [mergedCurrentLocalRoot hmergedCurrentLocal].
  destruct (htransport currentCrossLevel currentCrossLevelRoot
    hcurrentCrossLevel) as
    [mergedCurrentCrossLevelRoot hmergedCurrentCrossLevel].
  destruct (htransport currentShift currentShiftRoot hcurrentShift) as
    [mergedCurrentShiftRoot hmergedCurrentShift].
  destruct (htransport currentSubstitution currentSubstitutionRoot
    hcurrentSubstitution) as
    [mergedCurrentSubstitutionRoot hmergedCurrentSubstitution].
  destruct (htransport currentAxiomSoundness currentAxiomSoundnessRoot
    hcurrentAxiomSoundness) as
    [mergedCurrentAxiomSoundnessRoot hmergedCurrentAxiomSoundness].
  destruct (htransport currentFinal currentFinalRoot hcurrentFinal) as
    [mergedCurrentFinalRoot hmergedCurrentFinal].
  destruct (htransport nextLocal nextLocalRoot hnextLocal) as
    [mergedNextLocalRoot hmergedNextLocal].
  destruct (htransport nextCrossLevel nextCrossLevelRoot hnextCrossLevel) as
    [mergedNextCrossLevelRoot hmergedNextCrossLevel].
  destruct (htransport nextShift nextShiftRoot hnextShift) as
    [mergedNextShiftRoot hmergedNextShift].
  destruct (htransport nextSubstitution nextSubstitutionRoot
    hnextSubstitution) as
    [mergedNextSubstitutionRoot hmergedNextSubstitution].
  destruct (htransport nextAxiomSoundness nextAxiomSoundnessRoot
    hnextAxiomSoundness) as
    [mergedNextAxiomSoundnessRoot hmergedNextAxiomSoundness].
  exists mergedWitnessList, mergedBaseContext, newRoot.
  split.
  - exists mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
      mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
      mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
      mergedNextLocalRoot, mergedNextCrossLevelRoot, mergedNextShiftRoot,
      mergedNextSubstitutionRoot, mergedNextAxiomSoundnessRoot.
    constructor.
    + constructor; assumption.
    + exact hmergedNextAxiomSoundness.
  - exact hnewLocal.
Qed.

(** ------------------------------------------------------------------
    The honest grown-base final bridge package. *)

(** Both final roots use the same existentially returned base.  The exact
    universal-soundness code is fixed by [inputs], preventing an unrelated
    ordinary proof from being paired with the consistency bridge. *)
Definition RawDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAt
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode : M) : Prop :=
  exists mergedWitnessList mergedBaseContext
      soundnessRoot consistencyBridgeRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode mergedBaseContext)
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      soundnessRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode mergedBaseContext)
      (rawFormulaImpCode M
        (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
        nextFinal)
      consistencyBridgeRoot.

Arguments RawDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAt
  M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode : clear implicits.

(** Merge the exact ordinary soundness proof into the staged base, transport
    that root through the three canonical shifts and fields head, and invoke
    the existing pointwise consistency compiler again at the new base.

    The graph trace is deliberately reused unchanged: it does not mention a
    proof context.  By contrast, every bridge-context object is regenerated
    after the merge. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessBridge_of_ordinary :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
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
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness ->
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  rawStructuralTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler
    M inputs ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAt
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
    hfieldsAdequate hlevel hconsistencyCompiler.
  destruct
    (raw_dynamicTruthNativeFinalStagedPrerequisites_add_proof
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      soundnessCertificate hprerequisites hsoundnessCertificate)
    as (mergedWitnessList & mergedBaseContext & soundnessBaseRoot &
      hmergedPrerequisites & hsoundnessBase).
  pose proof hmergedPrerequisites as hmergedPrerequisitesCopy.
  destruct hmergedPrerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hmergedPrefix _]).
  destruct hmergedPrefix as [hmergedWitnessed _ _ _ _ _ _ _ _ _ _].
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  destruct (raw_codedPALocalProof_to_restrictedPABridgeContext
    M hPA (raw_succ M level) successorNumeralCode
    mergedWitnessList mergedBaseContext
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    soundnessBaseRoot hnumeral hmergedWitnessed hfieldsAdequate
    hsoundnessBase) as
    [soundnessRoot hsoundness].
  destruct (hconsistencyCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode mergedWitnessList mergedBaseContext
    htrace hmergedPrerequisites hlevel) as
    [consistencyBridgeRoot hconsistencyBridge].
  exists mergedWitnessList, mergedBaseContext,
    soundnessRoot, consistencyBridgeRoot.
  split; [exact hmergedPrerequisites |].
  split; [exact hsoundness | exact hconsistencyBridge].
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
