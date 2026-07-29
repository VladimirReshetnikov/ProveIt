(**
  Extract the compiled Assumption field from the native direct-truth package.

  The native package already carries the shared Sigma selector, the derived
  dynamic-context selector, both direct truth selectors, their structural
  input record, and the exact context/conclusion leaf equations.  This module
  merely projects those dependent witnesses and feeds the equations to the
  selected-tail Assumption compiler.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateNumeralParameters
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeft
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativePackageCompilation.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateNumeralParameters.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeft.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.

Theorem raw_selectedAssumptionTail_of_nativeDirectTruthInputsAt : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  exists contextTruth conclusionTruth inputs,
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    RawCoqRestrictedPADirectSelectedAssumptionTail M hPA inputs.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaSelector & contextSelector &
     contextTruth & conclusionTruth & inputs & hsuccessor & hsigmaClosed &
     hcontextClosed & hinputs & hcontextOutput & hconclusionOutput &
     hcontextLeaf & hconclusionLeaf & hevidence & hconclusionEvidence &
     happlication).
  exists contextTruth, conclusionTruth, inputs.
  split; [exact hinputs |].
  subst inputs.
  unfold RawCoqRestrictedPADirectSelectedAssumptionTail.
  exact
    (raw_coqRestrictedPADirectStrongStepAssumptionLaw_on_selected_tail
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaSelector contextSelector
      hconclusionLeaf hcontextLeaf).
Qed.

(** A continuation-friendly projection: the native package supplies an input
    record for which the post-Assumption twenty-one-field compiler can always
    be lifted back to the older post-Or-I-left interface. *)
Corollary
    raw_remainingCompiler_after_orIntroductionLeft_of_nativeDirectTruthInputsAt :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  exists contextTruth conclusionTruth inputs,
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    (RawCoqRestrictedPADirectRemainingAfterAssumptionStandardTailCompiler
      M hPA inputs ->
     RawCoqRestrictedPADirectRemainingRuleCasesStandardTailCompiler
      M hPA inputs).
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs.
  destruct
    (raw_selectedAssumptionTail_of_nativeDirectTruthInputsAt
      M hPA parameters currentGlobalSigma currentGlobalPi
      predecessorLevel nextSigmaEvidence hinputs)
    as (contextTruth & conclusionTruth & inputs & hinputShape & hassumption).
  exists contextTruth, conclusionTruth, inputs.
  split; [exact hinputShape |].
  exact
    (raw_remainingCompiler_after_orIntroductionLeft_of_afterAssumption
      M hPA inputs hassumption).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativePackageCompilation.
