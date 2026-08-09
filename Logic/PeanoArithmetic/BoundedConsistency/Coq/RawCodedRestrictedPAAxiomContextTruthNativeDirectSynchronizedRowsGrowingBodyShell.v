(**
  Carry a growing synchronized PA-axiom row through the native body shell.

  The row compiler may extend its witnessed PA base by a finite standard
  prefix.  Universal introduction, however, shifts the complete consistency
  bridge built over that enlarged base.  The two tails are therefore not
  definitionally equal.  This module proves the needed inclusion honestly:
  the enlarged witnessed base self-shifts, its literal inclusion in its
  bridge is preserved by both parallel represented shifts, and binder-safe
  weakening transports the four-head row to the twice-shifted bridge tail.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedContextInsertShiftCommutation
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextInclusionWeakening
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAAxiomContextSelfShift
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification
  RawCodedRestrictedPAConsistencyBridgeContextTransport.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedContextInsertShiftCommutation.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextInclusionWeakening.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectTraversalLeaf.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification.
Import PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.

(** A consistency bridge is atomically adequate over any witnessed PA base.
    Only the represented numeral trace matters; none of the staged proof
    roots are needed for this syntax fact. *)
Lemma
    raw_coqRestrictedPAConsistencyBridgeContext_all_atomically_adequate_of_witnessed
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      level successorNumeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawContextAllAtomicallyAdequate M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext).
Proof.
  intros M hPA level successorNumeralCode witnessList baseContext
    hnumeral hwitnessed.
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitnessed).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
  }
  destruct hcontexts as [_ [_ hproofShift]].
  pose proof (raw_contextShift_target_all_atomically_adequate M hPA
    (rawRestrictedPAAfterProofContextCode M successorNumeralCode
      shiftedWitnessContext)
    shiftedProofContext hproofShift) as hshiftedProofAdequate.
  pose proof
    (raw_restrictedPAProofFieldsCode_atomically_adequate
      M hPA level successorNumeralCode hnumeral) as hfieldsAdequate.
  unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
    rawRestrictedPAFieldsContextCode.
  exact (raw_contextAllAtomicallyAdequate_cons M hPA
    shiftedProofContext
    (rawRestrictedPAProofFieldsCode M successorNumeralCode)
    hshiftedProofAdequate hfieldsAdequate).
Qed.

(** The enlarged base occurs literally as the tail of its bridge. *)
Lemma raw_coqRestrictedPAConsistencyBridgeContext_base_included : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      successorNumeralCode baseContext,
  RawContextListIncluded M baseContext
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext).
Proof.
  intros M hPA successorNumeralCode baseContext.
  unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
    rawRestrictedPAFieldsContextCode,
    rawRestrictedPACanonicalShiftedProofContextCode,
    rawRestrictedPAShiftedProofContextCode.
  repeat apply (raw_contextListIncluded_cons_target M hPA).
  exact (raw_contextListIncluded_refl M baseContext).
Qed.

(** Pointwise carried adapter.  The output prefix is explicit: it records
    that the selected implication root now lives over the consistency bridge
    whose base is the row compiler's enlarged witnessed context. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruth_growing_bridge_root_of_synchronized_link
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawCoqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler M -> forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    level currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    successorNumeralCode baseWitnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    M hPA parameters inputs tail level currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
          M parameters inputs nextGlobalSigma sigmaApplicationSelector
          contextApplicationSelector))
      root.
Proof.
  intros M hPA hrows parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    successorNumeralCode baseWitnessList baseContext
    hnumeral hsynchronized hbaseWitnessed.

  pose proof hsynchronized as hsynchronizedCopy.
  destruct hsynchronizedCopy as [hlink hlower hprovenance].
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_target_identification
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector hsynchronized)
    as htarget.
  assert (hcanonicalIdentification :
      RawCoqRestrictedPANativeAxiomRowsGrowingIdentificationOn
        M inputs parameters nextGlobalSigma
        (rawDirectTemplateFormula inputs
          coqRestrictedPANativeAxiomRowsFieldTemplate)
        sigmaApplicationSelector contextApplicationSelector).
  {
    constructor.
    - reflexivity.
    - exact htarget.
  }

  (** Grow the witnessed PA base before constructing the bridge shifts. *)
  destruct
    (hrows parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector
      (rawDirectTemplateFormula inputs
        coqRestrictedPANativeAxiomRowsFieldTemplate)
      baseWitnessList baseContext hcanonicalIdentification hbaseWitnessed)
    as (prefix & rowRoot & hfinalWitnessed & hbaseIncluded & hrow).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode
      M prefix baseWitnessList).
  set (finalBase :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  change (RawCodedPAAxiomWitnessContext M finalWitnessList finalBase)
    in hfinalWitnessed.
  change (RawContextListIncluded M baseContext finalBase)
    in hbaseIncluded.
  change (RawCodedPALocalProofOf M
    (rawCoqRestrictedPANativeAxiomContextTruthRowContext M inputs
      (rawDirectTemplateFormula inputs
        coqRestrictedPANativeAxiomRowsFieldTemplate) finalBase)
    (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
      M parameters nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector) rowRoot) in hrow.

  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_all_atomically_adequate_of_witnessed
      M hPA level successorNumeralCode finalWitnessList finalBase
      hnumeral hfinalWitnessed) as hbridgeAdequate.
  pose proof
    (raw_coqRestrictedPANativeAxiomContextTruthLink_axiom_adequate
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector hlink)
    as haxiomAdequate.
  set (bridgeContext :=
    rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode finalBase).
  change (RawContextAllAtomicallyAdequate M bridgeContext)
    in hbridgeAdequate.
  pose proof (raw_contextAllAtomicallyAdequate_cons M hPA
    bridgeContext nextAxiomSoundness hbridgeAdequate haxiomAdequate)
    as hsourceAdequate.

  (** Construct the actual two All-I shifts and expose both shifted heads
      and both bridge tails. *)
  destruct (raw_contextShift_exists_of_all_atomically_adequate M hPA
    (rawListNode M nextAxiomSoundness bridgeContext) hsourceAdequate)
    as [context1 hshift01].
  pose proof (raw_contextShift_target_all_atomically_adequate M hPA
    (rawListNode M nextAxiomSoundness bridgeContext) context1 hshift01)
    as hcontext1Adequate.
  destruct (raw_contextShift_exists_of_all_atomically_adequate M hPA
    context1 hcontext1Adequate) as [context2 hshift12].
  destruct (raw_contextShift_cons_invert M hPA
    nextAxiomSoundness bridgeContext context1 hshift01) as
    (shiftedAxiomSoundness1 & shiftedBridgeTail1 & hcontext1 &
      haxiomShift1 & hbridgeShift1).
  subst context1.
  destruct (raw_contextShift_cons_invert M hPA
    shiftedAxiomSoundness1 shiftedBridgeTail1 context2 hshift12) as
    (shiftedAxiomSoundness2 & shiftedBridgeTail2 & hcontext2 &
      haxiomShift2 & hbridgeShift2).
  subst context2.

  pose proof
    (raw_coqRestrictedPANativeAxiomRowsGrowingIdentificationOn_of_synchronized_link
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      shiftedAxiomSoundness1 shiftedAxiomSoundness2
      hsynchronized haxiomShift1 haxiomShift2) as hshiftedIdentification.
  destruct hshiftedIdentification as [hshiftedField hshiftedTarget].
  rewrite hshiftedField in hrow.

  (** The witnessed enlarged base is fixed by shift.  Its inclusion in the
      bridge therefore survives both parallel bridge-tail shifts. *)
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      finalWitnessList finalBase hfinalWitnessed) as hfinalRealizable.
  pose proof (raw_codedPAAxiomWitnessContext_selfShift M hPA
    finalWitnessList finalBase hfinalWitnessed) as hfinalSelfShift.
  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_base_included
      M hPA successorNumeralCode finalBase) as hfinalIncludedBridge.
  change (RawContextListIncluded M finalBase bridgeContext)
    in hfinalIncludedBridge.
  pose proof (raw_contextListIncluded_of_parallel_shifts M hPA
    finalBase bridgeContext finalBase shiftedBridgeTail1
    hfinalIncludedBridge hfinalSelfShift hbridgeShift1)
    as hfinalIncludedShift1.
  pose proof (raw_contextListIncluded_of_parallel_shifts M hPA
    finalBase shiftedBridgeTail1 finalBase shiftedBridgeTail2
    hfinalIncludedShift1 hfinalSelfShift hbridgeShift2)
    as hfinalIncludedShift2.
  pose proof (raw_contextShift_target_realizable M
    shiftedBridgeTail1 shiftedBridgeTail2 hbridgeShift2)
    as hshiftedBridgeTail2Realizable.
  pose proof (raw_contextShift_target_all_atomically_adequate M hPA
    shiftedBridgeTail1 shiftedBridgeTail2 hbridgeShift2)
    as hshiftedBridgeTail2Adequate.
  pose proof (raw_contextBinderReady_of_target_all_atomically_adequate
    M hPA finalBase shiftedBridgeTail2 hfinalIncludedShift2
    hshiftedBridgeTail2Adequate) as htailBinderReady.

  destruct
    (raw_codedPALocalProof_coqRestrictedPANativeAxiomContextTruthRowContext_transport
      M hPA inputs shiftedAxiomSoundness2 finalBase shiftedBridgeTail2
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      rowRoot hfinalRealizable hshiftedBridgeTail2Realizable
      hfinalIncludedShift2 htailBinderReady hrow)
    as [transportedRowRoot htransportedRow].

  (** The transported row is definitionally the traversal leaf below the
      two shifted binders and the three explicit body assumptions. *)
  destruct
    (raw_coqRestrictedPANativeAxiomContextTruthBodyRoot_of_traversal_leaf
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      bridgeContext
      (rawListNode M shiftedAxiomSoundness1 shiftedBridgeTail1)
      (rawListNode M shiftedAxiomSoundness2 shiftedBridgeTail2)
      hlink hshift01 hshift12
      (ex_intro _ transportedRowRoot htransportedRow))
    as [bodyRoot hbody].
  exists prefix,
    (rawProofImpIRoot M bridgeContext nextAxiomSoundness
      (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
        M parameters inputs nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      bodyRoot).
  split; [exact hfinalWitnessed |].
  split; [exact hbaseIncluded |].
  unfold bridgeContext.
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode finalBase)
    nextAxiomSoundness
    (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector)
    bodyRoot hbody).
Qed.

(** No row-compiler premise remains.  The native selector equation also
    rewrites the selected target to the canonical direct coherence code used
    by the final carried-consistency assembly. *)
Corollary
    raw_coqRestrictedPANativeAxiomContextTruth_growing_bridge_root_compiled
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    level currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    successorNumeralCode baseWitnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    M hPA parameters inputs tail level currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      root.
Proof.
  intros M hPA parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    successorNumeralCode baseWitnessList baseContext
    hnumeral hsynchronized hbaseWitnessed.
  destruct
    (raw_coqRestrictedPANativeAxiomContextTruth_growing_bridge_root_of_synchronized_link
      M hPA
      (raw_coqRestrictedPANativeAxiomContextTruthGrowingRowsCompiler_compiled
        M hPA)
      parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      successorNumeralCode baseWitnessList baseContext
      hnumeral hsynchronized hbaseWitnessed) as
    (prefix & root & hfinalWitnessed & hbaseIncluded & hroot).
  pose proof hsynchronized as hsynchronizedCopy.
  destruct hsynchronizedCopy as [hlink _ _].
  pose proof hlink as hlinkCopy.
  destruct hlinkCopy as
    [_ (currentLevel & currentLevelNumeral & hlevel & hsuccessor &
      hlevelNumeral & hsigmaDomain & hpiDomain & happlication &
      hselector & hfield & hsigmaDeep & hcontextDeep & hcontextLeaf)].
  exists prefix, root.
  split; [exact hfinalWitnessed |].
  split; [exact hbaseIncluded |].
  rewrite
    (raw_coqRestrictedPAAxiomContextsTruthDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector hcontextLeaf).
  exact hroot.
Qed.

(** Strongest fixed-stage consequence currently supported by the growing
    APIs.  A final staged trace and its ordinary prerequisites select the
    exact native direct inputs and produce a closed implication root over an
    explicitly enlarged consistency bridge.  The lower direct numeral code
    is returned too, so downstream direct-coherence consumers retain the
    same level witness rather than reconstructing it from another package. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_growing_selected_axiom_context_root_exists
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode baseWitnessList baseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    baseWitnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  exists parameters : RawCodedTemplateNumeralParameters M,
  exists currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    rawNumeralTemplateParameterBound parameters
        coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level) /\
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode /\
    RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector /\
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      root.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode baseWitnessList baseContext
    htrace hprerequisites.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomSoundnessRoot]).
  destruct hprefix as
    [hbaseWitnessed hcurrentLocalRoot hcurrentCrossLevelRoot
      hcurrentShiftRoot hcurrentSubstitutionRoot hcurrentAxiomSoundnessRoot
      hcurrentFinalRoot hnextLocalRoot hnextCrossLevelRoot hnextShiftRoot
      hnextSubstitutionRoot].
  destruct
    (raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_rows_synchronized_link_exists
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace) as
    (parameters & currentGlobalSigma & currentGlobalPi & sigmaDomain &
      piDomain & nextSigmaEvidence & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & contextApplicationSelector & inputs &
      hupper & hsynchronized).
  destruct
    (raw_coqRestrictedPANativeAxiomContextTruth_growing_bridge_root_compiled
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      successorNumeralCode baseWitnessList baseContext
      hnumeral hsynchronized hbaseWitnessed) as
    (prefix & root & hfinalWitnessed & hbaseIncluded & hroot).
  pose proof hsynchronized as hsynchronizedCopy.
  destruct hsynchronizedCopy as
    [hlink hlower
      (contextTruth & conclusionTruth & hinputs & hconclusionLeaf)].
  assert (hlowerCode :
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode).
  {
    rewrite hinputs.
    exact (raw_coqRestrictedPANativeAxiomRows_lower_term_code
      M hPA parameters contextTruth conclusionTruth
      (raw_succ M level) successorNumeralCode hlower hnumeral).
  }
  pose proof
    (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed_context_transport
      M hPA baseWitnessList baseContext
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hprerequisites hfinalWitnessed hbaseIncluded)
    as hfinalPrerequisites.
  exists parameters, currentGlobalSigma, currentGlobalPi,
    sigmaDomain, piDomain, nextSigmaEvidence,
    nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs,
    prefix, root.
  split; [exact hupper |].
  split; [exact hlowerCode |].
  split; [exact hsynchronized |].
  split; [exact hfinalPrerequisites |].
  split; [exact hfinalWitnessed |].
  split; [exact hbaseIncluded |].
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell.
