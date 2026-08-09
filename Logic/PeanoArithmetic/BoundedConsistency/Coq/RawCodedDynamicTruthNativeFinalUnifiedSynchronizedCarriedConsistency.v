(**
  Unconditional carried consistency from one synchronized native package.

  The unified native package fixes one literal choice of numeral parameters,
  direct soundness inputs, paired-global successor, and dependent truth
  selectors.  Its growing-coherence endpoint may enlarge an arbitrary
  witnessed PA base.  This file completes the two later growth stages:

  - the open-shell arithmetic roots are compiled on a second witnessed base;
  - the honest selected-Sigma refutation is compiled on a third witnessed
    base and weakened into that base's restricted consistency bridge.

  One subtle representation point deserves emphasis.  The selected-Sigma
  proof is compiled with an *extended* structural translation.  Predicate
  slots two and three of that translation are the actual current global Pi
  and Sigma predicates.  The ordinary soundness translation intentionally
  sends those otherwise unused slots to bottom and therefore cannot identify
  the shared successor-row templates with the native paired successor.  The
  extended-row identification theorem supplies the exact two row equations;
  the transparent global wrapper and ternary-application functionality then
  identify the compiled antecedent with the unified selector output.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell
  RawCodedRestrictedPAConsistencyBridgeContextTransport
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations
  RawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence
  RawCodedRestrictedPAOpenShellArithmeticFinalPrerequisitesIntegration
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge
  RawCodedDynamicTruthNativeFinalCarriedConsistencyBottomGrowth.

Module
  PABoundedRawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingBodyShell.
Import PABoundedRawCodedRestrictedPAConsistencyBridgeContextTransport.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations.
Import
  PABoundedRawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence.
Import
  PABoundedRawCodedRestrictedPAOpenShellArithmeticFinalPrerequisitesIntegration.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessCarriedBridge.
Import PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyBottomGrowth.

(** Compile the honest selected-Sigma theorem on a growing PA tail and turn
    its antecedent into the exact application selected by the unified native
    package.  The returned proof already lives in the restricted consistency
    bridge over the compiler's enlarged base. *)
Theorem
    raw_dynamicTruthNativeFinalDirectBottomGrowth_of_unified_synchronized_compiled :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    closureCount axiom successorNumeralCode baseWitnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
  rawNumeralTemplateParameterBound parameters
    coqRestrictedPASoundnessUpperLevelParameterName =
    raw_succ M (raw_succ M level) ->
  RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
    M hPA parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthNativeFinalDirectBottomGrowthAt M inputs
    successorNumeralCode baseContext.
Proof.
  intros M hPA parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom successorNumeralCode baseWitnessList baseContext
    hnumeral hupperBound hcombined hbaseWitnessed.
  destruct hcombined as [hunified hsynchronized].
  destruct hsynchronized as [haxiomLink hlowerBound hprovenance].
  pose proof haxiomLink as haxiomLinkCopy.
  destruct haxiomLinkCopy as
    [hcurrentOrbit
      (currentLevel & currentLevelNumeral & hcurrentLevel & hsuccessor &
       hcurrentNumeral & hsigmaDomain & hpiDomain & hnativeApplication &
       hselectorNative & hnextAxiom & hnextSigmaDeep & hcontextDeep &
       hcontextLeaf)].
  subst currentLevel.

  (** Recover selectors for the two *current* global predicates.  Their deep
      closure follows from the adequate orbit retained by the synchronized
      axiom link, even at a nonstandard predecessor level. *)
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail (raw_succ M level)
      currentGlobalSigma currentGlobalPi hcurrentOrbit)
    as [hcurrentSigmaDeep hcurrentPiDeep].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA currentGlobalPi hcurrentPiDeep)
    as [lowerPiSelector lowerPiCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA currentGlobalSigma hcurrentSigmaDeep)
    as [lowerSigmaSelector lowerSigmaCommuting].

  (** Expose the literal local rows and the transparent wrapper hidden in
      the paired-global successor. *)
  destruct hsuccessor as
    (localSigmaRow & localPiRow & [hsigmaRow hpiRow] & hglobalWrapper).
  destruct hsigmaRow as
    (sigmaUpperNumeral & sigmaRowDomain & sigmaLowerApplication &
      hsigmaUpperNumeral & hsigmaRowDomain & hsigmaLower & hsigmaRowCode).
  destruct hpiRow as
    (piUpperNumeral & piRowDomain & piLowerApplication &
      hpiUpperNumeral & hpiRowDomain & hpiLower & hpiRowCode).
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M (raw_succ M level))
    sigmaUpperNumeral piUpperNumeral
    hsigmaUpperNumeral hpiUpperNumeral) as hrowNumerals.
  subst piUpperNumeral.

  pose proof (rawNumeralTemplateParameter_valid parameters
    coqDynamicTruthUpperLevelParameterName) as hparameterUpperNumeral.
  change (RawNumeralTermCodeAt M
      (rawNumeralTemplateParameterBound parameters
        coqRestrictedPASoundnessUpperLevelParameterName)
      (rawNumeralTemplateParameterCode parameters
        coqDynamicTruthUpperLevelParameterName))
    in hparameterUpperNumeral.
  rewrite hupperBound in hparameterUpperNumeral.
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M (raw_succ M level))
    (rawNumeralTemplateParameterCode parameters
      coqDynamicTruthUpperLevelParameterName)
    sigmaUpperNumeral hparameterUpperNumeral hsigmaUpperNumeral)
    as hupperCode.

  (** Use the context/conclusion selectors from the very same basic [inputs]
      package, and extend only its two unused opaque slots. *)
  destruct hprovenance as
    (contextTruth & conclusionTruth & hinputs & hconclusionLeaf).
  set (extendedInputs := rawCoqRestrictedPAExtendedRowsInputs
    M hPA parameters contextTruth conclusionTruth
    currentGlobalPi currentGlobalSigma
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting).
  set (extendedTranslation :=
    rawDirectStructuralTemplateTranslation M hPA extendedInputs).
  assert (hextendedAgreement :
      RawCodedTemplatePAAgreement M extendedTranslation).
  {
    unfold extendedTranslation.
    apply rawDirectStructuralTemplatePAAgreement.
  }

  pose proof
    (raw_coqRestrictedPAExtendedRows_identify_native
      M hPA parameters contextTruth conclusionTruth
      (raw_succ M level) (raw_succ M (raw_succ M level))
      currentGlobalPi currentGlobalSigma
      lowerPiSelector lowerSigmaSelector
      lowerPiCommuting lowerSigmaCommuting
      hlowerBound
      hupperBound sigmaUpperNumeral sigmaRowDomain piRowDomain
      sigmaLowerApplication piLowerApplication
      hupperCode hsigmaRowDomain hpiRowDomain hsigmaLower hpiLower)
    as [hsigmaTemplate hpiTemplate].
  change (rawDirectTemplateFormula extendedInputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawDynamicTruthSigmaSuccessorRowCode M
      sigmaRowDomain sigmaLowerApplication) in hsigmaTemplate.
  change (rawDirectTemplateFormula extendedInputs
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawDynamicTruthPiSuccessorRowCode M
      piRowDomain piLowerApplication) in hpiTemplate.
  rewrite <- hsigmaRowCode in hsigmaTemplate.
  rewrite <- hpiRowCode in hpiTemplate.

  (** Normalize the global source to the successor's public Sigma code. *)
  assert (hglobalSource :
      rawTemplateFormula extendedTranslation
        (coqRestrictedPASelectedSigmaBottomGlobalSource
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate) =
      nextGlobalSigma).
  {
    unfold coqRestrictedPASelectedSigmaBottomGlobalSource.
    rewrite (rawTemplateFormula_dynamicTruthGlobalExistentialSource
      M hPA extendedTranslation hextendedAgreement 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate).
    change (rawDynamicTruthGlobalFormulaCode M tZero
      (rawDirectTemplateFormula extendedInputs
        coqDynamicTruthSharedSigmaSuccessorRowTemplate)
      (rawDirectTemplateFormula extendedInputs
        coqDynamicTruthSharedPiSuccessorRowTemplate) = nextGlobalSigma).
    rewrite hsigmaTemplate, hpiTemplate.
    symmetry. exact (proj1 hglobalWrapper).
  }

  (** The protected shifts are inherited from the extended numeral-term
      interpreter.  They produce the five-step represented application of
      the exact source at quoted bottom, zero, and zero. *)
  pose proof
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_shift_by
      M hPA parameters contextTruth conclusionTruth
      (rawCoqRestrictedPAExtendedRowsTail
        M hPA parameters currentGlobalPi currentGlobalSigma
        lowerPiSelector lowerSigmaSelector
        lowerPiCommuting lowerSigmaCommuting)
      0 2 coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)
    as hfirstShift.
  pose proof
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_shift_by
      M hPA parameters contextTruth conclusionTruth
      (rawCoqRestrictedPAExtendedRowsTail
        M hPA parameters currentGlobalPi currentGlobalSigma
        lowerPiSelector lowerSigmaSelector
        lowerPiCommuting lowerSigmaCommuting)
      0 1 coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)
    as hsecondShift.
  change (RawCodedTermShift M (raw_zero M) (rawNumeralValue M 2)
      (rawTemplateTerm extendedTranslation
        coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)
      (rawTemplateTerm extendedTranslation
        (coqRestrictedPATemplateTernaryFirstLifted
          coqRestrictedPASelectedSigmaBottomGlobalFirstArgument)))
    in hfirstShift.
  change (RawCodedTermShift M (raw_zero M) (rawNumeralValue M 1)
      (rawTemplateTerm extendedTranslation
        coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)
      (rawTemplateTerm extendedTranslation
        (coqRestrictedPATemplateTernarySecondLifted
          coqRestrictedPASelectedSigmaBottomGlobalZeroArgument)))
    in hsecondShift.
  pose proof
    (raw_codedTemplateTernaryApplication_selectedSigmaBottom_global
      M extendedTranslation
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      hfirstShift hsecondShift) as happlication.
  rewrite hglobalSource in happlication.
  unfold coqRestrictedPASelectedSigmaBottomGlobalFirstArgument,
    coqRestrictedPASelectedSigmaBottomGlobalZeroArgument in happlication.
  change (RawCodedTernaryApplication M nextGlobalSigma
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      (rawTemplateFormula extendedTranslation
        coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource))
    in happlication.
  pose proof (rawTernaryApplicationOutput_unique M hPA
    nextGlobalSigma sigmaApplicationSelector
    (rawQuotedTermCode M rawFormulaBotCodeTerm)
    (rawQuotedTermCode M tZero)
    (rawQuotedTermCode M tZero)
    (rawTemplateFormula extendedTranslation
      coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
    (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax
      M hPA rawFormulaBotCodeTerm)
    (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero)
    (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero)
    happlication) as happliedCode.

  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_compiled_growing
      M hPA extendedTranslation hextendedAgreement
      baseWitnessList baseContext hbaseWitnessed)
    as (prefix & compiledRoot & hfinalWitnessed & hbaseIncluded & hcompiled).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      prefix baseWitnessList).
  set (finalBaseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  change (RawCodedPAAxiomWitnessContext M
      finalWitnessList finalBaseContext) in hfinalWitnessed.
  change (RawContextListIncluded M baseContext finalBaseContext)
    in hbaseIncluded.
  change (RawCodedPALocalProofOf M finalBaseContext
      (rawFormulaImpCode M
        (rawTemplateFormula extendedTranslation
          coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
        (rawFormulaBotCode M)) compiledRoot) in hcompiled.
  rewrite <- happliedCode in hcompiled.

  pose proof hunified as hunifiedCopy.
  destruct hunifiedCopy as [_ [hbottomLink _]].
  pose proof (proj2 (proj2 hbottomLink)) as hnativeConclusionLeaf.
  change (RawCodedPALocalProofOf M finalBaseContext
      (rawCoqRestrictedPASelectedSigmaBottomRefutationCode
        M nextGlobalSigma sigmaApplicationSelector) compiledRoot)
    in hcompiled.
  rewrite <-
    (raw_coqRestrictedPABottomTruthRefutationDirectCode_native_view
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      hnativeConclusionLeaf) in hcompiled.

  (** The compiled root begins in [finalBaseContext].  The base occurs
      literally below the restricted bridge heads; target adequacy supplies
      the binder invariant required by represented context weakening. *)
  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_all_atomically_adequate_of_witnessed
      M hPA level successorNumeralCode
      finalWitnessList finalBaseContext hnumeral hfinalWitnessed)
    as hbridgeAdequate.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      finalWitnessList finalBaseContext hfinalWitnessed)
    as hfinalRealizable.
  set (bridgeContext :=
    rawCoqRestrictedPAConsistencyBridgeContextCode M
      successorNumeralCode finalBaseContext).
  assert (hbridgeRealizable : RawContextListRealizable M bridgeContext).
  {
    unfold bridgeContext.
    exact (raw_coqRestrictedPAConsistencyBridgeContext_realizable
      M hPA finalWitnessList finalBaseContext successorNumeralCode
      hfinalWitnessed).
  }
  pose proof
    (raw_coqRestrictedPAConsistencyBridgeContext_base_included
      M hPA successorNumeralCode finalBaseContext) as hfinalInBridge.
  change (RawContextListIncluded M finalBaseContext bridgeContext)
    in hfinalInBridge.
  change (RawContextAllAtomicallyAdequate M bridgeContext)
    in hbridgeAdequate.
  pose proof
    (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA finalBaseContext bridgeContext
      hfinalInBridge hbridgeAdequate) as hbridgeReady.
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA finalBaseContext bridgeContext
      (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
      compiledRoot hfinalRealizable hbridgeRealizable
      hfinalInBridge hbridgeReady hcompiled)
    as [bottomRoot hbottom].
  exists finalWitnessList, finalBaseContext, bottomRoot.
  split; [exact hfinalWitnessed |].
  split; [exact hbaseIncluded |].
  unfold bridgeContext in hbottom.
  exact hbottom.
Qed.

(** The final public package retains the literal synchronized native link,
    the closure remainder needed by the direct-rule-cases compiler, and the
    carried consistency bridge built from those same [inputs]. *)
Record RawDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistencyAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    closureCount axiom sourceBaseContext : Prop := {
  rawDynamicTruthNativeFinalUnifiedCarried_lower_level :
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName = raw_succ M level;
  rawDynamicTruthNativeFinalUnifiedCarried_upper_level :
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level);
  rawDynamicTruthNativeFinalUnifiedCarried_direct_level :
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode;
  rawDynamicTruthNativeFinalUnifiedCarried_native_link :
    RawCoqRestrictedPANativeFinalUnifiedSynchronizedTruthLinkAt
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom;
  rawDynamicTruthNativeFinalUnifiedCarried_closure_remainder :
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount;
  rawDynamicTruthNativeFinalUnifiedCarried_consistency :
    RawDynamicTruthNativeFinalCarriedConsistencyCodeBridgeAt M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode sourceBaseContext
}.

(** Starting from exactly one final staged trace and one prerequisite package
    on an arbitrary witnessed source base, perform coherence, arithmetic, and
    bottom growth in order and return the shared carried package. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_carried_consistency_exists :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
    RawDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistencyAt
      M hPA parameters inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom baseContext.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode baseWitnessList baseContext
    htrace hprerequisites.
  destruct
    (raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_growing_coherence_exists
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode baseWitnessList baseContext
      htrace hprerequisites)
    as (parameters & inputs & currentGlobalSigma & currentGlobalPi &
      sigmaDomain & piDomain & nextSigmaEvidence & nextGlobalSigma &
      nextGlobalPi & sigmaApplicationSelector & contextApplicationSelector &
      closureCount & axiom & coherencePrefix & coherenceRoot & hgrowing).
  destruct hgrowing as
    [hlower hupper hlevel hcombined hcoherencePrerequisites
      hcoherenceWitnessed hbaseToCoherence hcoherence].
  set (coherenceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      coherencePrefix baseWitnessList).
  set (coherenceBaseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      coherencePrefix baseContext).
  change (RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      coherenceWitnessList coherenceBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness) in hcoherencePrerequisites.
  change (RawCodedPAAxiomWitnessContext M
      coherenceWitnessList coherenceBaseContext) in hcoherenceWitnessed.
  change (RawContextListIncluded M baseContext coherenceBaseContext)
    in hbaseToCoherence.
  change (RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode coherenceBaseContext)
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      coherenceRoot) in hcoherence.

  destruct
    (raw_dynamicTruthNativeFinalStagedPrerequisites_openShell_arithmetic_of_trace
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode
      coherenceWitnessList coherenceBaseContext
      htrace hlevel hcoherencePrerequisites)
    as (arithmeticWitnessList & arithmeticBaseContext &
      admissibleRoot & contextBoundedRoot & contextAdequateRoot &
      harithmeticPrerequisites & hcoherenceToArithmetic & harithmetic).
  pose proof
    (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed
      M arithmeticWitnessList arithmeticBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness harithmeticPrerequisites)
    as harithmeticWitnessed.
  pose proof
    (raw_dynamicTruthNativeFinal_bridge_context_all_atomically_adequate
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      arithmeticWitnessList arithmeticBaseContext
      htrace harithmeticPrerequisites)
    as harithmeticBridgeAdequate.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      coherenceWitnessList coherenceBaseContext hcoherenceWitnessed)
    as hcoherenceRealizable.
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      arithmeticWitnessList arithmeticBaseContext harithmeticWitnessed)
    as harithmeticRealizable.
  destruct
    (raw_codedPALocalProof_coqRestrictedPAConsistencyBridgeContext_transport
      M hPA successorNumeralCode
      coherenceBaseContext arithmeticBaseContext
      (rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
      coherenceRoot hcoherenceRealizable harithmeticRealizable
      hcoherenceToArithmetic harithmeticBridgeAdequate hcoherence)
    as [arithmeticCoherenceRoot harithmeticCoherence].

  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  pose proof
    (raw_dynamicTruthNativeFinalDirectBottomGrowth_of_unified_synchronized_compiled
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom successorNumeralCode
      arithmeticWitnessList arithmeticBaseContext
      hnumeral hupper hcombined harithmeticWitnessed)
    as hbottomGrowth.
  pose proof
    (raw_contextListIncluded_trans M baseContext coherenceBaseContext
      arithmeticBaseContext hbaseToCoherence hcoherenceToArithmetic)
    as hbaseToArithmetic.
  pose proof (proj1 hcombined) as hunified.
  pose proof
    (raw_dynamicTruthNativeFinalCarriedConsistencyCodeBridge_of_bottom_growth
      M hPA parameters inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      closureCount axiom baseContext
      arithmeticWitnessList arithmeticBaseContext
      arithmeticCoherenceRoot admissibleRoot contextBoundedRoot
      contextAdequateRoot htrace harithmeticPrerequisites
      hbaseToArithmetic hlevel hunified harithmeticCoherence
      harithmetic hbottomGrowth) as hcarried.
  pose proof hunified as hunifiedCopy.
  destruct hunifiedCopy as [_ [_ hremainder]].
  exists parameters, inputs,
    currentGlobalSigma, currentGlobalPi, sigmaDomain, piDomain,
    nextSigmaEvidence, nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    closureCount, axiom.
  constructor; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency.
