(**
  Select one native direct input package for both final truth obligations.

  Axiom-context truth and bottom refutation were previously linked to the
  final staged graph by two independent compiler interfaces.  That is too
  strong for the level-indexed final construction: the native package
  already chooses one direct structural input record and exposes both its
  context-truth and conclusion-truth leaves at once.

  This module retains that dependency.  From the literal five-field staged
  trace it exactifies the common paired-global orbit, extracts the axiom
  successor trace, and chooses one native closure package.  Functional
  uniqueness identifies its successor with the graph successor.  The result
  simultaneously contains:

  - the selected axiom/context-truth link;
  - the selected conclusion/bottom-truth link; and
  - the strong-prefix closure remainder for those very same direct inputs.

  Thus later pointwise final compilers need not assume two global
  graph-to-package synchronization functions, and cannot accidentally mix
  selectors or structural inputs chosen by different native packages.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

Module PABoundedRawCodedRestrictedPANativeFinalUnifiedTruthLink.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

(** One exact native package view.  Both links share [parameters], [inputs],
    the successor predicates, and the dependent Sigma selector; the closure
    remainder is indexed by the same [inputs]. *)
Definition RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
    (M : RawPAModel)
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
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
      M parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector /\
  RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
      M parameters inputs currentGlobalSigma currentGlobalPi
      predecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector /\
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount.

Arguments RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
  M parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    closureCount axiom : clear implicits.

(** The final staged graph chooses a single coherent native package.  Notice
    that the two level equations and closure witnesses are returned with the
    links rather than reconstructed later from unrelated existential
    choices. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_unified_native_truth_link_exists
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
    RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt
      M parameters inputs tail level
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
  destruct (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    currentGlobalSigma currentGlobalPi currentLevel
    traceNextGlobalSigma traceNextGlobalPi
    nativeNextGlobalSigma nativeNextGlobalPi htraceSuccessor) as hfunctional.
  rewrite hlevel in hfunctional.
  specialize (hfunctional hnativeSuccessor).
  destruct hfunctional as [hsigma hpi].
  subst nativeNextGlobalSigma. subst nativeNextGlobalPi.
  exists parameters, currentGlobalSigma, currentGlobalPi,
    sigmaDomain, piDomain, nextSigmaEvidence,
    traceNextGlobalSigma, traceNextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    inputs, closureCount, axiom.
  split; [exact hlower |].
  split; [exact hupper |].
  unfold RawCoqRestrictedPANativeFinalUnifiedTruthLinkAt.
  split.
  - split; [exact horbitAgain |].
    exists currentLevel, currentLevelNumeral.
    repeat split; try assumption.
  - split.
    + split; [exact hnativeSuccessor |].
      split; [exact hsigmaDeep | exact hconclusionLeaf].
    + exact hremainder.
Qed.

End PABoundedRawCodedRestrictedPANativeFinalUnifiedTruthLink.
