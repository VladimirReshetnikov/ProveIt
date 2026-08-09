(**
  Keep unified native truth and growing axiom-row coherence synchronized.

  The older unified truth package and the growing synchronized-row package
  were both constructed from the same native direct-input closure witness,
  but their public constructors existentially hid that common provenance.
  Choosing the two packages independently would leave no honest way to
  identify their dependent selectors or structural inputs.

  This module destructs the common closure witness once.  It then builds the
  conclusion/bottom link, closure remainder, exact axiom-row synchronization,
  and growing bridge coherence root from those very same witnesses.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink
  RawCodedRestrictedPANativeFinalUnifiedTruthLink.

Module
  PABoundedRawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.
Import PABoundedRawCodedRestrictedPANativeFinalUnifiedTruthLink.

(** Both public native views, indexed by one literal choice of parameters,
    inputs, successors, and dependent selectors. *)
Definition RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    closureCount axiom : Prop :=
  RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
      M parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom /\
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector.

Arguments RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
  M hPA parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom : clear implicits.

(** Destruct the native closure package once and build both projections.
    Paired-successor functionality aligns only the graph successor; no
    equality between separately selected direct-input records is used. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_truth_link_exists
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  exists parameters : RawCodedTemplateNumeralParameters M,
  exists currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists closureCount axiom : M,
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
      raw_succ M level /\
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level) /\
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode /\
    RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode hstaged.
  pose proof hstaged as hstagedCopy.
  destruct hstagedCopy as
    [hcurrent hnextLocal hnextCrossLevel hnextShift hnextSubstitution
      hnextAxiomSoundness hnextFinal hsource].
  destruct hsource as
    [hsourceFormula hsuccessorNumeral hnextTarget hsourceGraph].
  pose proof
    (raw_dynamicTruthNativeFivePositiveGraphs_orbit_coherent M hPA
      tail level nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hnextLocal hnextCrossLevel hnextShift
      hnextSubstitution hnextAxiomSoundness) as hcoherent.
  destruct hcoherent as
    (currentGlobalSigma & currentGlobalPi & horbit & hlocalTransform &
      hcrossTransform & hshiftTransform & hsubstitutionTransform &
      haxiomTransform).
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
      M tail level currentGlobalSigma currentGlobalPi nextAxiomSoundness
      horbit haxiomTransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  destruct
    (raw_coqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt_of_trace
      M hPA tail level currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (parameters & hlower & hupper & hnative).
  destruct htrace as
    [horbitAgain (currentLevel & traceNextGlobalSigma & traceNextGlobalPi &
      currentLevelNumeral & hlevel & htraceSuccessor & hnumeral &
      hsigmaDomain & hpiDomain & htraceApplication)].
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hnative.
  destruct hnative as
    (nativeNextGlobalSigma & nativeNextGlobalPi & sigmaApplicationSelector &
      contextApplicationSelector & contextTruth & conclusionTruth & inputs &
      closureCount & axiom & hnativeSuccessor & hsigmaDeep & hcontextDeep &
      hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
      hconclusionLeaf & hselectorNative & hconclusionNative &
      happlication & hremainder).
  assert (hlowerCode :
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm =
      rawNumeralTemplateParameterCode parameters
        coqRestrictedPASoundnessLowerLevelParameterName).
  {
    rewrite hinputs. reflexivity.
  }
  pose proof (rawNumeralTemplateParameter_valid parameters
    coqRestrictedPASoundnessLowerLevelParameterName) as hparameterNumeral.
  rewrite hlower in hparameterNumeral.
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M level)
    (rawNumeralTemplateParameterCode parameters
      coqRestrictedPASoundnessLowerLevelParameterName)
    successorNumeralCode hparameterNumeral hsuccessorNumeral)
    as hlowerFunctional.
  pose proof (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    currentGlobalSigma currentGlobalPi currentLevel
    traceNextGlobalSigma traceNextGlobalPi
    nativeNextGlobalSigma nativeNextGlobalPi htraceSuccessor)
    as hfunctional.
  rewrite hlevel in hfunctional.
  specialize (hfunctional hnativeSuccessor).
  destruct hfunctional as [hsigma hpi].
  subst nativeNextGlobalSigma. subst nativeNextGlobalPi.
  assert (haxiomLink :
      RawCoqRestrictedPANativeAxiomContextTruthLinkAt
        M parameters inputs tail level
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence nextAxiomSoundness
        traceNextGlobalSigma traceNextGlobalPi sigmaApplicationSelector
        contextApplicationSelector).
  {
    split; [exact horbitAgain |].
    exists currentLevel, currentLevelNumeral.
    split; [exact hlevel |].
    split; [exact htraceSuccessor |].
    split; [exact hnumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact htraceApplication |].
    split; [exact hselectorNative |].
    split; [exact hfield |].
    split; [exact hsigmaDeep |].
    split; [exact hcontextDeep |].
    exact hcontextLeaf.
  }
  assert (hsynchronized :
      RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
        M hPA parameters inputs tail level
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence nextAxiomSoundness
        traceNextGlobalSigma traceNextGlobalPi sigmaApplicationSelector
        contextApplicationSelector).
  {
    constructor.
    - exact haxiomLink.
    - exact hlower.
    - exists contextTruth, conclusionTruth.
      split; assumption.
  }
  assert (hunified :
      RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
        M parameters inputs tail level
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence nextAxiomSoundness
        traceNextGlobalSigma traceNextGlobalPi sigmaApplicationSelector
        contextApplicationSelector closureCount axiom).
  {
    split; [exact haxiomLink |].
    split.
    - split; [exact hnativeSuccessor |].
      split; [exact hsigmaDeep | exact hconclusionLeaf].
    - exact hremainder.
  }
  exists parameters, currentGlobalSigma, currentGlobalPi,
    sigmaDomain, piDomain, nextSigmaEvidence,
    traceNextGlobalSigma, traceNextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    inputs, closureCount, axiom.
  split; [exact hlower |].
  split; [exact hupper |].
  split.
  - rewrite hlowerCode. exact hlowerFunctional.
  - split; assumption.
Qed.

(** The complete carried object returned to final consistency assembly. *)
Record RawCoqRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherenceAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    (nextFinal successorNumeralCode : M)
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    closureCount axiom baseWitnessList baseContext
    (prefix : StandardPAAxiomWitnessPrefix) root : Prop := {
  rawCoqRestrictedPANativeFinalUnifiedGrowing_lower_level :
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName = raw_succ M level;
  rawCoqRestrictedPANativeFinalUnifiedGrowing_upper_level :
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level);
  rawCoqRestrictedPANativeFinalUnifiedGrowing_direct_level :
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode;
  rawCoqRestrictedPANativeFinalUnifiedGrowing_native_link :
    RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom;
  rawCoqRestrictedPANativeFinalUnifiedGrowing_final_prerequisites :
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness;
  rawCoqRestrictedPANativeFinalUnifiedGrowing_final_witnessed :
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode
        M prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext);
  rawCoqRestrictedPANativeFinalUnifiedGrowing_base_included :
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext);
  rawCoqRestrictedPANativeFinalUnifiedGrowing_coherence_root :
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      root
}.

(** Final unconditional seam: one staged trace and one prerequisite package
    produce a single package containing both native truth projections and
    their growing, transported coherence root. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_growing_coherence_exists
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
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists closureCount axiom : M,
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCoqRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherenceAt
      M hPA parameters inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom baseWitnessList baseContext prefix root.
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
    (raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_truth_link_exists
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace) as
    (parameters & currentGlobalSigma & currentGlobalPi & sigmaDomain &
      piDomain & nextSigmaEvidence & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & contextApplicationSelector & inputs &
      closureCount & axiom & hlower & hupper & hlevelCode & hnative).
  destruct hnative as [hunified hsynchronized].
  destruct
    (raw_coqRestrictedPANativeAxiomContextTruth_growing_bridge_root_compiled
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      successorNumeralCode baseWitnessList baseContext
      hnumeral hsynchronized hbaseWitnessed) as
    (prefix & root & hfinalWitnessed & hbaseIncluded & hcoherenceRoot).
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
  exists parameters, inputs,
    currentGlobalSigma, currentGlobalPi, sigmaDomain, piDomain,
    nextSigmaEvidence, nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    closureCount, axiom, prefix, root.
  constructor.
  - exact hlower.
  - exact hupper.
  - exact hlevelCode.
  - split; assumption.
  - exact hfinalPrerequisites.
  - exact hfinalWitnessed.
  - exact hbaseIncluded.
  - exact hcoherenceRoot.
Qed.

End
  PABoundedRawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence.
