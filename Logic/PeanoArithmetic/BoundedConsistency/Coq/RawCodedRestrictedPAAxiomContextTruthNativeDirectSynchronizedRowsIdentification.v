(**
  Identify the transparent growing PA-axiom row with the native graph row.

  The small [RawCoqRestrictedPANativeAxiomContextTruthLinkAt] record keeps
  the graph-selected predicates and the direct context leaf synchronized,
  but deliberately forgets two pieces of construction provenance:

  - the direct inputs were built from the very same context/conclusion
    selectors; and
  - the lower numeral parameter denotes the current graph level.

  Both facts are present in the coherent native direct-input package.  This
  module retains exactly that additional data, identifies the transparent
  axiom field and selected context target, and finally transports the field
  identity through the two represented binder shifts.  The latter transport
  is sound because the complete axiom-field template is syntactically
  closed; represented shift functionality therefore identifies both shift
  outputs with its unchanged direct code.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruthTotality
  RawCodedAssignment
  RawCodedProofAtomicAdequacy
  RawCodedPAAxiomWitness
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTripleUniversalOpening
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes
  RawCodedTemplateTernaryApplication
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedTargetTemplateContext
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink
  RawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsWitnessShapes.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsGrowingCarrier.

(** The native link plus the two pieces of direct-input provenance which it
    intentionally omits.  Only the lower level is retained: the row field
    does not mention the upper hierarchy parameter. *)
Record RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : Prop := {
  rawCoqRestrictedPANativeAxiomRowsSynchronized_native_link :
    RawCoqRestrictedPANativeAxiomContextTruthLinkAt
      M parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector;
  rawCoqRestrictedPANativeAxiomRowsSynchronized_lower_level :
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
    raw_succ M predecessorLevel;
  rawCoqRestrictedPANativeAxiomRowsSynchronized_direct_provenance :
    exists contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters,
      inputs =
        rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth /\
      forall first second third fourth fifth,
        rawDirectTemplateFormula inputs
          (tfOpaque coqRestrictedPAConclusionTruthPredicateName
            [first; second; third; fourth; fifth]) =
        rawTernaryApplicationOutput sigmaApplicationSelector
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters third)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters fourth)
          (rawCoqRestrictedPADerivationSoundnessTemplateTermView
            M parameters fifth)
}.

Arguments RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
  M hPA parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector : clear implicits.

(** Build the synchronized link without passing through the deliberately
    smaller coherence-link interface.  In particular, this proof retains the
    canonical [inputs] equation and the conclusion-leaf equation carried by
    the native direct-input package.  Functionality of the paired successor
    is the only alignment step: it identifies the package's successor with
    the successor already selected by the proof trace. *)
Theorem
    raw_coqRestrictedPANativeAxiomRowsSynchronizedLink_exists_of_trace_and_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (tail : nat -> M) predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  nextAxiomSoundness =
    rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence ->
  rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
    raw_succ M predecessorLevel ->
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence ->
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector.
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness htrace hfield hlower hnative.
  destruct htrace as
    [horbit (currentLevel & traceNextGlobalSigma & traceNextGlobalPi &
      currentLevelNumeral & hlevel & htraceSuccessor & hnumeral &
      hsigmaDomain & hpiDomain & htraceApplication)].
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hnative.
  destruct hnative as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  pose proof (raw_dynamicTruthPairedGlobalSuccessorAt_functional M hPA
    currentGlobalSigma currentGlobalPi currentLevel
    traceNextGlobalSigma traceNextGlobalPi nextGlobalSigma nextGlobalPi
    htraceSuccessor) as hfunctional.
  rewrite hlevel in hfunctional.
  specialize (hfunctional hsuccessor).
  destruct hfunctional as [hsigma hpi].
  subst nextGlobalSigma. subst nextGlobalPi.
  assert (hlink :
      RawCoqRestrictedPANativeAxiomContextTruthLinkAt
        M parameters inputs tail predecessorLevel
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        nextSigmaEvidence nextAxiomSoundness
        traceNextGlobalSigma traceNextGlobalPi sigmaApplicationSelector
        contextApplicationSelector).
  {
    split; [exact horbit |].
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
  exists traceNextGlobalSigma, traceNextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs.
  constructor.
  - exact hlink.
  - exact hlower.
  - exists contextTruth, conclusionTruth.
    split; assumption.
Qed.

(** The coherent wrapper exposes both numeral-stage equations.  The lower
    equation becomes part of the synchronized link; the upper equation is
    returned alongside it for the later bounded-soundness body. *)
Theorem
    raw_coqRestrictedPANativeAxiomRowsSynchronizedLink_exists_of_coherent_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  nextAxiomSoundness =
    rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence ->
  RawCoqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt
    M hPA currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence ->
  exists parameters : RawCodedTemplateNumeralParameters M,
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    rawNumeralTemplateParameterBound parameters
        coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M predecessorLevel) /\
    RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector.
Proof.
  intros M hPA tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness htrace hfield hcoherent.
  unfold RawCoqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt
    in hcoherent.
  destruct hcoherent as (parameters & hlower & hupper & hnative).
  destruct
    (raw_coqRestrictedPANativeAxiomRowsSynchronizedLink_exists_of_trace_and_inputs
      M hPA parameters tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness htrace hfield hlower hnative)
    as (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
      contextApplicationSelector & inputs & hsynchronized).
  exists parameters, nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs.
  split; assumption.
Qed.

(** A final staged trace determines all synchronized-row witnesses while
    retaining the canonical direct-input provenance.  This is the exact
    staged analogue of the smaller native coherence-link constructor. *)
Theorem
    raw_dynamicTruthNativeFinalStagedGraphTrace_axiom_rows_synchronized_link_exists
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
    rawNumeralTemplateParameterBound parameters
        coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M level) /\
    RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
      M hPA parameters inputs tail level
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      contextApplicationSelector.
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
      hnextSubstitution hnextAxiomSoundness) as horbitCoherent.
  destruct horbitCoherent as
    (currentGlobalSigma & currentGlobalPi & horbit & hlocalTransform &
      hcrossTransform & hshiftTransform & hsubstitutionTransform &
      haxiomTransform).
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
      M tail level currentGlobalSigma currentGlobalPi nextAxiomSoundness
      horbit haxiomTransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  pose proof
    (raw_coqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt_of_trace
      M hPA tail level currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as hcoherentInputs.
  destruct
    (raw_coqRestrictedPANativeAxiomRowsSynchronizedLink_exists_of_coherent_inputs
      M hPA tail level currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
      htrace hfield hcoherentInputs) as
    (parameters & nextGlobalSigma & nextGlobalPi &
      sigmaApplicationSelector & contextApplicationSelector & inputs &
      hupper & hsynchronized).
  exists parameters, currentGlobalSigma, currentGlobalPi,
    sigmaDomain, piDomain, nextSigmaEvidence,
    nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector, inputs.
  split; assumption.
Qed.

(** The native one-variable domain templates become the two transparent
    restricted-target domain contexts after opening their level slot. *)
Lemma coqRestrictedPANativeAxiomRowsSigmaDomainTemplate_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthNativeAxiomSigmaDomainTemplate) =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetSigmaDomainContext (tVar 0)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPANativeAxiomRowsPiDomainTemplate_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthNativeAxiomPiDomainTemplate) =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetPiDomainContext (tVar 0)).
Proof. reflexivity. Qed.

(** Functionality of represented numeral coding identifies the parameter's
    canonical numeral code with the independently selected graph numeral. *)
Lemma raw_coqRestrictedPANativeAxiomRows_lower_term_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    currentLevel currentLevelNumeral,
  rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName = currentLevel ->
  RawNumeralTermCodeAt M currentLevel currentLevelNumeral ->
  rawDirectTemplateTerm
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      coqRestrictedPASoundnessLowerLevelTerm = currentLevelNumeral.
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    currentLevel currentLevelNumeral hbound hnumeral.
  rewrite rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
  cbn [coqRestrictedPASoundnessLowerLevelTerm
    rawCoqRestrictedPADerivationSoundnessTemplateTermView
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols
    rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
  apply (raw_numeralTermCodeAt_functional M hPA currentLevel).
  - rewrite <- hbound.
    apply rawNumeralTemplateParameter_valid.
  - exact hnumeral.
Qed.

(** Each direct domain component is another realization of the very same
    represented single-substitution trace stored by the native graph. *)
Lemma raw_coqRestrictedPANativeAxiomRows_sigma_domain_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    currentLevelNumeral sigmaDomain,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = currentLevelNumeral ->
  RawCodedFormulaSingleSubstitution M currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
    sigmaDomain ->
  rawDirectTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetSigmaDomainContext (tVar 0))) = sigmaDomain.
Proof.
  intros M hPA inputs currentLevelNumeral sigmaDomain
    hlevelCode hsigmaDomain.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthNativeAxiomSigmaDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hdirect.
  change (RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      (embedPAFormula dynamicTruthNativeAxiomSigmaDomainTemplate))
    (rawDirectTemplateFormula inputs
      (templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
        (embedPAFormula dynamicTruthNativeAxiomSigmaDomainTemplate))))
    in hdirect.
  unfold rawDirectTemplateFormula in hdirect.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hdirect.
  rewrite rawQuotedFormulaCode_standard in hdirect by exact hPA.
  rewrite coqRestrictedPANativeAxiomRowsSigmaDomainTemplate_open in hdirect.
  rewrite hlevelCode in hdirect.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
    (rawStructuralTemplateFormulaWith M
      (rawDirectTemplateSymbols inputs)
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetSigmaDomainContext (tVar 0))))
    sigmaDomain hdirect hsigmaDomain).
Qed.

Lemma raw_coqRestrictedPANativeAxiomRows_pi_domain_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    currentLevelNumeral piDomain,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = currentLevelNumeral ->
  RawCodedFormulaSingleSubstitution M currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
    piDomain ->
  rawDirectTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetPiDomainContext (tVar 0))) = piDomain.
Proof.
  intros M hPA inputs currentLevelNumeral piDomain
    hlevelCode hpiDomain.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthNativeAxiomPiDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hdirect.
  change (RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      (embedPAFormula dynamicTruthNativeAxiomPiDomainTemplate))
    (rawDirectTemplateFormula inputs
      (templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
        (embedPAFormula dynamicTruthNativeAxiomPiDomainTemplate))))
    in hdirect.
  unfold rawDirectTemplateFormula in hdirect.
  rewrite rawStructuralTemplateFormulaWith_embedPA in hdirect.
  rewrite rawQuotedFormulaCode_standard in hdirect by exact hPA.
  rewrite coqRestrictedPANativeAxiomRowsPiDomainTemplate_open in hdirect.
  rewrite hlevelCode in hdirect.
  exact (raw_codedFormulaSingleSubstitution_functional M hPA
    currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
    (rawStructuralTemplateFormulaWith M
      (rawDirectTemplateSymbols inputs)
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetPiDomainContext (tVar 0))))
    piDomain hdirect hpiDomain).
Qed.

Lemma raw_coqRestrictedPANativeAxiomRows_domain_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    currentLevelNumeral sigmaDomain piDomain,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = currentLevelNumeral ->
  RawCodedFormulaSingleSubstitution M currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M currentLevelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
    piDomain ->
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsDomainTemplate =
    rawFormulaOrCode M sigmaDomain piDomain.
Proof.
  intros M hPA inputs currentLevelNumeral sigmaDomain piDomain
    hlevelCode hsigmaDomain hpiDomain.
  unfold coqRestrictedPANativeAxiomRowsDomainTemplate,
    restrictedTargetFormulaQuantifierBoundedContext.
  change (rawFormulaOrCode M
    (rawDirectTemplateFormula inputs
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetSigmaDomainContext (tVar 0))))
    (rawDirectTemplateFormula inputs
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetPiDomainContext (tVar 0)))) =
    rawFormulaOrCode M sigmaDomain piDomain).
  rewrite (raw_coqRestrictedPANativeAxiomRows_sigma_domain_code
    M hPA inputs currentLevelNumeral sigmaDomain
    hlevelCode hsigmaDomain).
  rewrite (raw_coqRestrictedPANativeAxiomRows_pi_domain_code
    M hPA inputs currentLevelNumeral piDomain
    hlevelCode hpiDomain).
  reflexivity.
Qed.

(** The selected conclusion leaf in the transparent field is the exact
    Sigma application stored by the native axiom graph. *)
Lemma raw_coqRestrictedPANativeAxiomRows_sigma_leaf_code : forall
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    nextGlobalSigma
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    nextSigmaEvidence,
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero) = nextSigmaEvidence ->
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsSigmaLeafTemplate = nextSigmaEvidence.
Proof.
  intros M parameters inputs nextGlobalSigma sigmaApplicationSelector
    nextSigmaEvidence hconclusion hselector.
  unfold coqRestrictedPANativeAxiomRowsSigmaLeafTemplate.
  rewrite hconclusion.
  cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermView
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols
    rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
  exact hselector.
Qed.

(** PA embedding agreement fixes the three ordinary syntax predicates in
    the transparent field to their standard represented formula codes. *)
Lemma raw_coqRestrictedPANativeAxiomRows_recognition_code : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsRecognitionTemplate =
  rawNumeralValue M
    (formulaCode (witnessedPAAxiomRecognitionTermAt (tVar 0))).
Proof.
  intros M hPA inputs.
  unfold coqRestrictedPANativeAxiomRowsRecognitionTemplate,
    rawDirectTemplateFormula.
  rewrite rawStructuralTemplateFormulaWith_embedPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma raw_coqRestrictedPANativeAxiomRows_atomic_code : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsAtomicTemplate =
  rawNumeralValue M
    (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 0))).
Proof.
  intros M hPA inputs.
  unfold coqRestrictedPANativeAxiomRowsAtomicTemplate,
    rawDirectTemplateFormula.
  rewrite rawStructuralTemplateFormulaWith_embedPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma raw_coqRestrictedPANativeAxiomRows_defined_code : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsDefinedTemplate =
  rawNumeralValue M
    (formulaCode
      (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))).
Proof.
  intros M hPA inputs.
  unfold coqRestrictedPANativeAxiomRowsDefinedTemplate,
    rawDirectTemplateFormula.
  rewrite rawStructuralTemplateFormulaWith_embedPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

(** The first requested equality before binder shifting. *)
Theorem raw_coqRestrictedPANativeAxiomRows_field_identification : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    M hPA parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector ->
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate = nextAxiomSoundness.
Proof.
  intros M hPA parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector hsynchronized.
  destruct hsynchronized as [hlink hlower hprovenance].
  destruct hprovenance as
    (contextTruth & conclusionTruth & hinputs & hconclusion).
  pose proof hlink as hlinkCopy.
  destruct hlinkCopy as
    [_ (currentLevel & currentLevelNumeral & hlevel & _ & hnumeral &
      hsigmaDomain & hpiDomain & _ & hselector & hfield & _ & _ & _)].
  assert (hlevelCode :
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm = currentLevelNumeral).
  {
    rewrite hinputs.
    apply (raw_coqRestrictedPANativeAxiomRows_lower_term_code
      M hPA parameters contextTruth conclusionTruth
      currentLevel currentLevelNumeral).
    - rewrite hlevel. exact hlower.
    - exact hnumeral.
  }
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_domain_code
      M hPA inputs currentLevelNumeral sigmaDomain piDomain
      hlevelCode hsigmaDomain hpiDomain) as hdomain.
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_sigma_leaf_code
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      nextSigmaEvidence hconclusion hselector) as hsigmaLeaf.
  rewrite hfield.
  unfold coqRestrictedPANativeAxiomRowsFieldTemplate.
  change (rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPANativeAxiomRowsRecognitionTemplate)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPANativeAxiomRowsAtomicTemplate)
          (rawFormulaAndCode M
            (rawDirectTemplateFormula inputs
              coqRestrictedPANativeAxiomRowsDefinedTemplate)
            (rawDirectTemplateFormula inputs
              coqRestrictedPANativeAxiomRowsDomainTemplate))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPANativeAxiomRowsSigmaLeafTemplate)) =
    rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence).
  rewrite (raw_coqRestrictedPANativeAxiomRows_recognition_code
    M hPA inputs).
  rewrite (raw_coqRestrictedPANativeAxiomRows_atomic_code M hPA inputs).
  rewrite (raw_coqRestrictedPANativeAxiomRows_defined_code M hPA inputs).
  rewrite hdomain, hsigmaLeaf.
  reflexivity.
Qed.

(** The second requested equality.  The canonical provenance lets us use
    the native-output theorem for the very same context selector; no
    extensional predicate equality is introduced. *)
Theorem raw_coqRestrictedPANativeAxiomRows_target_identification : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    M hPA parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector ->
  rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsTargetTemplate =
  rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
    M parameters nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector.
Proof.
  intros M hPA parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector hsynchronized.
  destruct hsynchronized as [hlink _ hprovenance].
  destruct hprovenance as
    (contextTruth & conclusionTruth & hinputs & hconclusion).
  subst inputs.
  pose proof
    (raw_coqRestrictedPADynamicContextPredicateTemplate_native_output
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector contextApplicationSelector
      hconclusion (ttVar 0) ttZero ttZero) as houtput.
  rewrite !rawCoqRestrictedPADerivationSoundnessDirectTerm_view in houtput.
  unfold coqRestrictedPANativeAxiomRowsTargetTemplate.
  symmetry. exact houtput.
Qed.

(** A small reusable scoping lemma.  It avoids normalizing a large embedded
    PA formula merely to establish that shifting above its whole scope is
    the identity. *)
Lemma templateShiftRenamingAt_below_identity : forall scope index,
  index < scope -> templateShiftRenamingAt scope index = index.
Proof.
  induction scope as [|scope ih]; intros index hindex.
  - inversion hindex.
  - destruct index as [|index].
    + reflexivity.
    + cbn [templateShiftRenamingAt]. f_equal.
      apply ih. now apply Nat.succ_lt_mono.
Qed.

Lemma templateTermRename_shift_scoped_identity : forall scope input,
  TemplateTermScoped scope input ->
  templateTermRename (templateShiftRenamingAt scope) input = input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope hscope;
    cbn [TemplateTermScoped templateTermRename] in hscope |- *;
    try reflexivity.
  - now rewrite (templateShiftRenamingAt_below_identity
      scope n hscope).
  - now rewrite (IHinput scope hscope).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope hleft), (IHinput2 scope hright).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope hleft), (IHinput2 scope hright).
Qed.

Lemma templateTermsRename_shift_scoped_identity : forall scope inputs,
  TemplateTermsScoped scope inputs ->
  templateTermsRename (templateShiftRenamingAt scope) inputs = inputs.
Proof.
  intros scope inputs. unfold templateTermsRename.
  induction inputs as [|input tail ih];
    intro hscope; cbn [TemplateTermsScoped] in hscope |- *.
  - reflexivity.
  - destruct hscope as [hinput htail].
    change (templateTermRename (templateShiftRenamingAt scope) input ::
      map (templateTermRename (templateShiftRenamingAt scope)) tail =
      input :: tail).
    f_equal.
    + exact (templateTermRename_shift_scoped_identity
        scope input hinput).
    + exact (ih htail).
Qed.

Lemma templateFormulaRename_shift_scoped_identity : forall scope input,
  TemplateFormulaScoped scope input ->
  templateFormulaRename (templateShiftRenamingAt scope) input = input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope hscope;
    cbn [TemplateFormulaScoped templateFormulaRename] in hscope |- *;
    try reflexivity.
  - destruct hscope as [hleft hright].
    now rewrite (templateTermRename_shift_scoped_identity
      scope t hleft),
      (templateTermRename_shift_scoped_identity scope t0 hright).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope hleft), (IHinput2 scope hright).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope hleft), (IHinput2 scope hright).
  - destruct hscope as [hleft hright].
    now rewrite (IHinput1 scope hleft), (IHinput2 scope hright).
  - f_equal. rewrite <- templateFormulaRename_shift_succ.
    exact (IHinput (S scope) hscope).
  - f_equal. rewrite <- templateFormulaRename_shift_succ.
    exact (IHinput (S scope) hscope).
  - f_equal.
    exact (templateTermsRename_shift_scoped_identity
      scope l hscope).
Qed.

(** Scope preservation for a general template substitution.  This compact
    lemma is useful beyond the present row: it handles binders by lifting
    both the source and target scopes together. *)
Definition TemplateTermSubstitutionScoped
    (sourceScope targetScope : nat)
    (substitution : nat -> TemplateTerm) : Prop :=
  forall index, index < sourceScope ->
    TemplateTermScoped targetScope (substitution index).

Lemma templateTermScoped_rename_succ : forall scope input,
  TemplateTermScoped scope input ->
  TemplateTermScoped (S scope) (templateTermRename S input).
Proof.
  intros scope input. revert scope.
  induction input; intros scope hscope;
    cbn [TemplateTermScoped templateTermRename] in hscope |- *;
    try reflexivity; try lia.
  - exact (IHinput scope hscope).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 scope hleft).
    + exact (IHinput2 scope hright).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 scope hleft).
    + exact (IHinput2 scope hright).
Qed.

Lemma templateTermUpSubst_scoped : forall
    sourceScope targetScope substitution,
  TemplateTermSubstitutionScoped sourceScope targetScope substitution ->
  TemplateTermSubstitutionScoped (S sourceScope) (S targetScope)
    (templateTermUpSubst substitution).
Proof.
  intros sourceScope targetScope substitution hsubstitution
    [|index] hindex.
  - cbn [templateTermUpSubst TemplateTermScoped]. lia.
  - cbn [templateTermUpSubst].
    apply templateTermScoped_rename_succ.
    apply hsubstitution. lia.
Qed.

Lemma templateTermSubst_scoped : forall
    sourceScope targetScope substitution input,
  TemplateTermSubstitutionScoped sourceScope targetScope substitution ->
  TemplateTermScoped sourceScope input ->
  TemplateTermScoped targetScope (templateTermSubst substitution input).
Proof.
  intros sourceScope targetScope substitution input.
  revert sourceScope targetScope substitution.
  induction input; intros sourceScope targetScope substitution
    hsubstitution hscope;
    cbn [TemplateTermScoped templateTermSubst] in hscope |- *;
    try reflexivity.
  - exact (hsubstitution n hscope).
  - exact (IHinput sourceScope targetScope substitution
      hsubstitution hscope).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope substitution
        hsubstitution hleft).
    + exact (IHinput2 sourceScope targetScope substitution
        hsubstitution hright).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope substitution
        hsubstitution hleft).
    + exact (IHinput2 sourceScope targetScope substitution
        hsubstitution hright).
Qed.

Lemma templateTermsSubst_scoped : forall
    sourceScope targetScope substitution inputs,
  TemplateTermSubstitutionScoped sourceScope targetScope substitution ->
  TemplateTermsScoped sourceScope inputs ->
  TemplateTermsScoped targetScope
    (templateTermsSubst substitution inputs).
Proof.
  intros sourceScope targetScope substitution inputs hsubstitution.
  induction inputs as [|input tail ih]; intro hscope;
    cbn [TemplateTermsScoped templateTermsSubst] in hscope |- *.
  - exact I.
  - destruct hscope as [hinput htail]. split.
    + exact (templateTermSubst_scoped sourceScope targetScope
        substitution input hsubstitution hinput).
    + exact (ih htail).
Qed.

Lemma templateFormulaSubst_scoped : forall
    sourceScope targetScope substitution input,
  TemplateTermSubstitutionScoped sourceScope targetScope substitution ->
  TemplateFormulaScoped sourceScope input ->
  TemplateFormulaScoped targetScope
    (templateFormulaSubst substitution input).
Proof.
  intros sourceScope targetScope substitution input.
  revert sourceScope targetScope substitution.
  induction input; intros sourceScope targetScope substitution
    hsubstitution hscope;
    cbn [TemplateFormulaScoped templateFormulaSubst] in hscope |- *;
    try exact I.
  - destruct hscope as [hleft hright]. split.
    + exact (templateTermSubst_scoped sourceScope targetScope
        substitution t hsubstitution hleft).
    + exact (templateTermSubst_scoped sourceScope targetScope
        substitution t0 hsubstitution hright).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope substitution
        hsubstitution hleft).
    + exact (IHinput2 sourceScope targetScope substitution
        hsubstitution hright).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope substitution
        hsubstitution hleft).
    + exact (IHinput2 sourceScope targetScope substitution
        hsubstitution hright).
  - destruct hscope as [hleft hright]. split.
    + exact (IHinput1 sourceScope targetScope substitution
        hsubstitution hleft).
    + exact (IHinput2 sourceScope targetScope substitution
        hsubstitution hright).
  - exact (IHinput (S sourceScope) (S targetScope)
      (templateTermUpSubst substitution)
      (templateTermUpSubst_scoped sourceScope targetScope
        substitution hsubstitution) hscope).
  - exact (IHinput (S sourceScope) (S targetScope)
      (templateTermUpSubst substitution)
      (templateTermUpSubst_scoped sourceScope targetScope
        substitution hsubstitution) hscope).
  - exact (templateTermsSubst_scoped sourceScope targetScope
      substitution l hsubstitution hscope).
Qed.

Lemma templateFormulaOpen_scoped : forall scope replacement input,
  TemplateTermScoped scope replacement ->
  TemplateFormulaScoped (S scope) input ->
  TemplateFormulaScoped scope (templateFormulaOpen replacement input).
Proof.
  intros scope replacement input hreplacement hinput.
  unfold templateFormulaOpen.
  apply (templateFormulaSubst_scoped (S scope) scope
    (templateInstTerm replacement) input).
  - intros [|index] hindex.
    + exact hreplacement.
    + cbn [templateInstTerm TemplateTermScoped]. lia.
  - exact hinput.
Qed.

Lemma coqRestrictedPANativeAxiomRowsDomainTemplate_scoped :
  TemplateFormulaScoped 1 coqRestrictedPANativeAxiomRowsDomainTemplate.
Proof.
  unfold coqRestrictedPANativeAxiomRowsDomainTemplate,
    restrictedTargetFormulaQuantifierBoundedContext.
  change
    (TemplateFormulaScoped 1
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetSigmaDomainContext (tVar 0))) /\
     TemplateFormulaScoped 1
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetPiDomainContext (tVar 0)))).
  split.
  - rewrite <- coqRestrictedPANativeAxiomRowsSigmaDomainTemplate_open.
    apply templateFormulaOpen_scoped.
    + cbn [coqRestrictedPASoundnessLowerLevelTerm TemplateTermScoped].
      exact I.
    + apply templateFormulaScoped_embedPA. raw_scope_formula.
  - rewrite <- coqRestrictedPANativeAxiomRowsPiDomainTemplate_open.
    apply templateFormulaOpen_scoped.
    + cbn [coqRestrictedPASoundnessLowerLevelTerm TemplateTermScoped].
      exact I.
    + apply templateFormulaScoped_embedPA. raw_scope_formula.
Qed.

Lemma coqRestrictedPANativeAxiomRowsFieldTemplate_scoped :
  TemplateFormulaScoped 0 coqRestrictedPANativeAxiomRowsFieldTemplate.
Proof.
  unfold coqRestrictedPANativeAxiomRowsFieldTemplate.
  cbn [TemplateFormulaScoped].
  split.
  - split.
    + unfold coqRestrictedPANativeAxiomRowsRecognitionTemplate.
      apply templateFormulaScoped_embedPA. raw_scope_formula.
    + split.
      * unfold coqRestrictedPANativeAxiomRowsAtomicTemplate.
        apply templateFormulaScoped_embedPA. raw_scope_formula.
      * split.
        -- unfold coqRestrictedPANativeAxiomRowsDefinedTemplate.
           apply templateFormulaScoped_embedPA. raw_scope_formula.
        -- exact coqRestrictedPANativeAxiomRowsDomainTemplate_scoped.
  - unfold coqRestrictedPANativeAxiomRowsSigmaLeafTemplate.
    cbn [TemplateFormulaScoped TemplateTermsScoped TemplateTermScoped].
    lia.
Qed.

(** The transparent field is closed, hence a unit shift at the outermost
    cutoff leaves its template syntax literally unchanged. *)
Lemma coqRestrictedPANativeAxiomRowsFieldTemplate_shift_closed :
  templateFormulaRename (templateShiftRenamingAt 0)
      coqRestrictedPANativeAxiomRowsFieldTemplate =
    coqRestrictedPANativeAxiomRowsFieldTemplate.
Proof.
  apply templateFormulaRename_shift_scoped_identity.
  exact coqRestrictedPANativeAxiomRowsFieldTemplate_scoped.
Qed.

Lemma raw_coqRestrictedPANativeAxiomRows_field_shift_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_shiftAt M hPA inputs 0
    coqRestrictedPANativeAxiomRowsFieldTemplate) as hshift.
  cbn [rawNumeralValue] in hshift.
  rewrite coqRestrictedPANativeAxiomRowsFieldTemplate_shift_closed in hshift.
  exact hshift.
Qed.

(** Assemble precisely the identification record consumed by the growing
    row carrier after the two actual binder-shift traces. *)
Theorem
    raw_coqRestrictedPANativeAxiomRowsGrowingIdentificationOn_of_synchronized_link
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
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
      shiftedAxiomSoundness1 shiftedAxiomSoundness2,
  RawCoqRestrictedPANativeAxiomRowsSynchronizedLinkAt
    M hPA parameters inputs tail predecessorLevel currentGlobalSigma
    currentGlobalPi sigmaDomain piDomain nextSigmaEvidence
    nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    nextAxiomSoundness shiftedAxiomSoundness1 ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    shiftedAxiomSoundness1 shiftedAxiomSoundness2 ->
  RawCoqRestrictedPANativeAxiomRowsGrowingIdentificationOn
    M inputs parameters nextGlobalSigma shiftedAxiomSoundness2
    sigmaApplicationSelector contextApplicationSelector.
Proof.
  intros M hPA parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    shiftedAxiomSoundness1 shiftedAxiomSoundness2
    hsynchronized hshift1 hshift2.
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_field_identification
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector hsynchronized)
    as hfield.
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_target_identification
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector hsynchronized)
    as htarget.
  pose proof
    (raw_coqRestrictedPANativeAxiomRows_field_shift_identity M hPA inputs)
    as hidentity.
  rewrite <- hfield in hshift1.
  pose proof (raw_codedFormulaShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate)
    shiftedAxiomSoundness1 hidentity hshift1) as hfirst.
  rewrite <- hfirst in hshift2.
  pose proof (raw_codedFormulaShift_functional M hPA
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate)
    (rawDirectTemplateFormula inputs
      coqRestrictedPANativeAxiomRowsFieldTemplate)
    shiftedAxiomSoundness2 hidentity hshift2) as hsecond.
  constructor.
  - exact hsecond.
  - exact htarget.
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification.
