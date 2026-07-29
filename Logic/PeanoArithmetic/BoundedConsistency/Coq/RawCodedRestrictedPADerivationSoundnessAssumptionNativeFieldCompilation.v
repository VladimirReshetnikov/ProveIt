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
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
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
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition
  RawCodedRestrictedPADerivationSoundnessAssumptionUniversalSourceCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionNativeLawTransport.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.

Import PA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
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
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
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

(** Adding a finite standard prefix in front of a witnessed direct tail keeps
    every old context member.  This elementary inclusion is separated from
    proof transport so later rule compilers can reuse the exact carrier fact. *)
Lemma raw_assumption_standardPrefix_target_included : forall
    (M : RawPAModel), RawPASatisfies M -> forall prefix context,
  RawContextListIncluded M context
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix context).
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih]; intro context.
  - exact (raw_contextListIncluded_refl M context).
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    apply (raw_contextListIncluded_cons_target M hPA).
    exact (ih context).
Qed.

(** The selected Assumption witness batch remains included when another
    independently selected batch is placed before it and an arbitrary later
    suffix is placed after it. *)
Lemma raw_assumption_directEmbeddedPAAxiomWitnessContext_surrounded_included :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawContextListIncluded M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses)))
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix))))).
Proof.
  intros M hPA inputs prefix witnesses suffix member hmember.
  pose proof
    (raw_directEmbeddedPAAxiomWitnessContext_suffix_included
      M hPA inputs witnesses suffix) as hsuffix.
  assert (htargetCode :
    rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))) =
    rawStandardPAAxiomWitnessPrefixContextCode M prefix
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom (witnesses ++ suffix))))).
  {
    rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (prefix ++ (witnesses ++ suffix)) (raw_zero M)).
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    f_equal.
    rewrite rawTemplateContextCode_as_on_tail.
    exact (eq_sym
      (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        (witnesses ++ suffix) (raw_zero M))).
  }
  rewrite htargetCode.
  exact
    (raw_assumption_standardPrefix_target_included M hPA prefix
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom (witnesses ++ suffix))))
      member (hsuffix member hmember)).
Qed.

(** Transport the exact public Assumption residual to a common witnessed tail.
    Both an earlier prefix and a later suffix are allowed, so this theorem can
    be composed with rule compilers in either selection order. *)
Theorem raw_assumptionLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectStrongStepAssumptionMembershipTruthLawRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite
    coqRestrictedPADirectStrongStepAssumptionReadyContext_app_witnesses
    in hroot.
  rewrite rawTemplateContextCode_app_on_tail in hroot.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses)))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))))
      (coqRestrictedPADirectStrongStepAssumptionReadyContext [])
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionMembershipTruthLawTemplate)
      root
      (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs witnesses)
      (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs
        (prefix ++ (witnesses ++ suffix)))
      (raw_assumption_directEmbeddedPAAxiomWitnessContext_surrounded_included
        M hPA inputs prefix witnesses suffix)
      hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite
    coqRestrictedPADirectStrongStepAssumptionReadyContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  exact htransported.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeFieldCompilation.
