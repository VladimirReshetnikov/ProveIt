(**
  Compile the public direct Assumption semantic field on a witnessed PA tail.

  The universal-source compiler supplies a local proof of the transparent
  native law below the finite strong-step prefix.  Witnessed PA axioms are
  sentences, so the Assumption ready context is affine in that selected tail
  despite its intervening existential shifts.  The native-law carrier equality
  then transports the conclusion to the exact public residual expected by the
  direct dispatcher.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition
  RawCodedRestrictedPADerivationSoundnessAssumptionUniversalSourceCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeLawTransport.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.

Import PA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionUniversalSourceCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeLawTransport.

Lemma coqRestrictedPADirectStrongStepAssumptionReadyContext_app_witnesses :
  forall witnesses,
  coqRestrictedPADirectStrongStepAssumptionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepAssumptionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectStrongStepAssumptionReadyContext,
    coqRestrictedPADirectStrongStepAssumptionAdmissibleContext,
    coqRestrictedPADirectStrongStepAssumptionCaseContext,
    coqRestrictedPADirectStrongStepAssumptionDeepEndpointContext,
    rawCoqRestrictedPADirectEndpointDeepTail,
    rawCoqRestrictedPADirectEndpointDeepContext,
    rawCoqRestrictedPADirectStrongStepEndpointTail,
    rawCoqRestrictedPADirectStrongStepFourBinderContext.
  cbn [rawCoqTemplateNestedExContext rawCoqTemplateContextShiftN
    templateContextShift templateContextRename List.map List.app].
  repeat rewrite templateContextShift_embedPAAxiomWitnesses.
  reflexivity.
Qed.

Theorem
    raw_coqRestrictedPADirectStrongStepAssumptionLaw_on_selected_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector hconclusion hcontext.
  destruct
    (raw_codedPALocalProof_assumptionNativeLaw_on_selected_tail
      M hPA inputs
      (coqRestrictedPADirectStrongStepAssumptionReadyContext []))
    as (witnesses & root & hwitnessed & hnative).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (witnessTail := embedPAContext (map witnessedAxiom witnesses)).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)).
  assert (htailCode : rawTemplateContextCode translation witnessTail =
      extendedContext).
  {
    unfold witnessTail, extendedContext.
    rewrite rawTemplateContextCode_as_on_tail.
    exact (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
  }
  assert (hreadyCode : rawTemplateContextCode translation
      (coqRestrictedPADirectStrongStepAssumptionReadyContext witnessTail) =
      rawTemplateContextCodeOnTail translation extendedContext
        (coqRestrictedPADirectStrongStepAssumptionReadyContext [])).
  {
    unfold witnessTail.
    unfold witnessTail in htailCode.
    rewrite
      coqRestrictedPADirectStrongStepAssumptionReadyContext_app_witnesses.
    rewrite rawTemplateContextCode_app_on_tail.
    now rewrite htailCode.
  }
  pose proof (raw_coqRestrictedPADirectAssumptionNativeLaw_code
    M hPA parameters contextTruth conclusionTruth
    sigmaCode sigmaSelector contextSelector hconclusion hcontext) as hlaw.
  change (rawDirectTemplateFormula inputs
      coqRestrictedPADirectAssumptionMembershipTruthLawTemplate =
    rawDirectTemplateFormula inputs
      coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate)
    in hlaw.

  exists witnesses. split.
  - unfold witnessTail.
    unfold witnessTail in htailCode.
    rewrite htailCode. exact hwitnessed.
  - unfold
      RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot,
      RawCoqRestrictedPADirectAssumptionMembershipTruthLawRootAt.
    unfold witnessTail in hreadyCode.
    exists root.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepAssumptionReadyContext
          (embedPAContext (map witnessedAxiom witnesses))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionMembershipTruthLawTemplate)
      root).
    rewrite hreadyCode, hlaw.
    exact hnative.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.
