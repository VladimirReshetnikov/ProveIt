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
  RawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedTemplateNumeralParameters.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativePackageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import PABoundedRawCodedTemplateNumeralParameters.

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
