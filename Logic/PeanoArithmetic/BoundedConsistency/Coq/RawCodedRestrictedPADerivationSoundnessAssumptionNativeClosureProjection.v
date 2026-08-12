From Stdlib Require Import List.

(**
  Project the selected Assumption frontier from the native closure package.

  The closure package is intentionally larger than the Assumption compiler:
  it remembers the same selectors, direct structural input, and closure
  remainder needed by later stages.  This lemma exposes the already available
  Assumption law without asking a caller to reconstruct the dependent
  selector equations a second time.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPADerivationSoundnessAssumptionNativePackageCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation
  RawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedTernaryPredicateDeepClosure
  RawCodedTemplateSyntax
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedSyntaxConstructors
  RawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedTemplateNumeralParameters.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativePackageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder.
Import PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedTemplateNumeralParameters.
Import ListNotations.

(**
  The closure package is usually consumed existentially.  For the V2
  continuation, however, the structural input record is already fixed by a
  caller.  This predicate freezes the two direct truth selectors and that
  input record while retaining exactly the closure witnesses.  The resulting
  projection below can therefore return the selected Assumption tail for the
  caller's [inputs], rather than hiding it behind another existential.
*)
Definition RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence : M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists closureCount axiom : M,
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi
      (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi /\
    RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
    RawCodedTernaryPredicateDeepClosed M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector) /\
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    (forall lower upper context assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput contextTruth
        lower upper context assignmentCode assignmentStep =
      rawTernaryApplicationOutput contextApplicationSelector
        assignmentStep assignmentCode context) /\
    (forall lower upper conclusion assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper conclusion assignmentCode assignmentStep =
      rawTernaryApplicationOutput sigmaApplicationSelector
        conclusion assignmentCode assignmentStep) /\
    (forall first second third fourth fifth,
      rawDirectTemplateFormula inputs
        (tfOpaque coqRestrictedPAContextTruthPredicateName
          [first; second; third; fourth; fifth]) =
      rawTernaryApplicationOutput contextApplicationSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)) /\
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
          M parameters fifth)) /\
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero) = nextSigmaEvidence /\
    (forall lower upper,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero) = nextSigmaEvidence) /\
    RawCodedTernaryApplication M nextGlobalSigma
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      nextSigmaEvidence /\
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount.

Arguments RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
  M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
  nextSigmaEvidence contextTruth conclusionTruth inputs : clear implicits.

Theorem
    raw_selectedAssumptionTail_of_nativeDirectTruthInputsWithClosureAtFor :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
    M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence contextTruth conclusionTruth inputs ->
  RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence contextTruth conclusionTruth inputs
    hclosure.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor in
    hclosure.
  destruct hclosure as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & closureCount & axiom & hsuccessor &
     hsigmaDeep & hcontextDeep & hinputs & hcontextOutput &
     hconclusionOutput & hcontextLeaf & hconclusionLeaf & hselectorNative &
     hconclusionNative & happlication & hclosureRemainder).
  subst inputs.
  unfold RawCoqRestrictedPADirectSelectedAssumptionTail.
  exact
    (raw_coqRestrictedPADirectStrongStepAssumptionLaw_on_selected_tail
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector contextApplicationSelector
      hconclusionLeaf hcontextLeaf).
Qed.

Theorem
    raw_selectedAssumptionTail_of_nativeDirectTruthInputsWithClosureAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence ->
  exists contextTruth conclusionTruth inputs,
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hclosure.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hclosure.
  destruct hclosure as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hclosureRemainder).
  assert (hdirect :
      PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.RawCoqRestrictedPANativeDirectTruthInputsAt
        M hPA parameters
        currentGlobalSigma currentGlobalPi predecessorLevel
        nextSigmaEvidence).
  {
    unfold
      PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.RawCoqRestrictedPANativeDirectTruthInputsAt.
    exists nextGlobalSigma, nextGlobalPi,
      sigmaApplicationSelector, contextApplicationSelector,
      contextTruth, conclusionTruth, inputs.
    split; [exact hsuccessor |].
    split; [exact hsigmaDeep |].
    split; [exact hcontextDeep |].
    split; [exact hinputs |].
    split; [exact hcontextOutput |].
    split; [exact hconclusionOutput |].
    split; [exact hcontextLeaf |].
    split; [exact hconclusionLeaf |].
    split; [exact hselectorNative |].
    split; [exact hconclusionNative | exact happlication].
    all: assumption.
  }
  exact
    (raw_selectedAssumptionTail_of_nativeDirectTruthInputsAt
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hdirect).
Qed.
