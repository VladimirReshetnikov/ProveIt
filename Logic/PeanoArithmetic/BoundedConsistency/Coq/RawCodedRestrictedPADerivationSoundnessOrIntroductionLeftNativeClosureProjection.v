(**
  Project the selected Or-I-left frontier from a fixed native closure input.

  The closure witness identifies the direct conclusion leaf with the
  selected Sigma application.  A separate dynamic-law root at the empty
  witnessed tail supplies the only genuinely semantic Or-I-left premise;
  the theorem below combines these two facts without quantifying over a
  fresh structural-input record.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeClosureProjection
  RawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters.

From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport.

Import
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureProjection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.

Theorem
    raw_selectedOrIntroductionLeftTruthTail_of_nativeDirectTruthInputsWithClosureAtFor_of_dynamicLawAtEmpty :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor
    M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
    nextSigmaEvidence contextTruth conclusionTruth inputs ->
  RawCoqRestrictedPADirectDynamicTruthLawRootAtEmpty M hPA inputs ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence contextTruth conclusionTruth inputs
    hclosure hdynamic.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAtFor in
    hclosure.
  destruct hclosure as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & closureCount & axiom & hsuccessor &
     hsigmaDeep & hcontextDeep & hinputs & hcontextOutput &
     hconclusionOutput & hcontextLeaf & hconclusionLeaf & hselectorNative &
     hconclusionNative & happlication & hclosureRemainder).
  subst inputs.
  pose proof
    (raw_selectedNativeOrIntroductionLeftTruthTail_of_dynamic_reroot_at_empty
      M hPA parameters contextTruth conclusionTruth nextGlobalSigma
      sigmaApplicationSelector hconclusionLeaf hdynamic) as hnative.
  exact
    (raw_selectedPublicOrIntroductionLeftTruthTail_of_native
      M hPA parameters contextTruth conclusionTruth nextGlobalSigma
      sigmaApplicationSelector hconclusionLeaf hnative).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeClosureProjection.
