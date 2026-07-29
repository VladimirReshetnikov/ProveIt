(**
  Compile native direct truth data after the Assumption field.

  The native truth package already chooses the two direct truth selectors,
  proves their literal ternary-application equations, and supplies the exact
  strong-prefix closure remainder.  The post-Assumption dispatcher separately
  turns those equations, together with a twenty-one-field continuation, into
  an ordinary PA certificate of direct universal soundness.

  This module joins those interfaces without exposing any of the native
  existential selectors to callers.  Its trace-level corollary additionally
  retains the lower/upper stage equations, which are needed when the resulting
  soundness certificate is inserted into the final staged bridge.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** Package-level composition.  The continuation is quantified over the
    native package's dependent selector choices; after destructing the
    package, its application is therefore definitionally about the same
    direct structural input as the leaf equations and closure remainder. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterAssumption
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    RawCoqRestrictedPADirectRemainingAfterAssumptionStandardTailCompiler
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hremaining.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  subst inputs.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_afterAssumption
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector contextApplicationSelector
      hconclusionLeaf hcontextLeaf (hremaining contextTruth conclusionTruth)
      (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount hremainder)
    as [soundnessCertificate hsoundness].
  exists contextTruth, conclusionTruth, soundnessCertificate.
  exact hsoundness.
Qed.

(** Trace-level composition.  Unlike a bare existential certificate, this
    result remembers that its direct lower and upper parameters are the two
    consecutive stages selected by the same native successor trace. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeTrace_afterAssumption
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  (forall parameters contextTruth conclusionTruth,
    RawCoqRestrictedPADirectRemainingAfterAssumptionStandardTailCompiler
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  exists parameters contextTruth conclusionTruth soundnessCertificate,
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
      raw_succ M predecessorLevel /\
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M predecessorLevel) /\
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence htrace hremaining.
  destruct
    (raw_coqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt_of_trace
      M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace)
    as (parameters & hlower & hupper & hinputs).
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterAssumption
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs (hremaining parameters))
    as (contextTruth & conclusionTruth & soundnessCertificate & hsoundness).
  exists parameters, contextTruth, conclusionTruth, soundnessCertificate.
  split; [exact hlower |].
  split; [exact hupper | exact hsoundness].
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.
