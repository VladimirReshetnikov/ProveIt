(**
  Replace the Assumption transfer-source hypothesis by PA's proof.

  The ten-witness template exports an implication from the closed universal
  context-membership transfer theorem to the native Assumption law.  This file
  compiles the PA theorem above an arbitrary witnessed base, inserts an
  arbitrary finite direct-template prefix, compiles that implication over the
  same selected witnessed tail, and combines both roots by modus ponens.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedProofBinaryConstructors
  RawCodedContextLists
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedContextMembershipTransferPA
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance
  RawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionUniversalSourceCompilation.

Import PA.
Import PABoundedCodedProof.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedContextMembershipTransferPA.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTransferInstance.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.

Theorem
    raw_codedPALocalProof_assumptionNativeLaw_on_selected_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) prefix,
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        prefix)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate)
      root.
Proof.
  intros M hPA inputs prefix.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (agreement :=
    rawDirectStructuralTemplatePAAgreement M hPA inputs).
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedTemplatePALocalProofOf_contextListMemberTransferUniversal_on_tail
      M hPA translation agreement (raw_zero M) (raw_zero M) hempty)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M)).
  set (witnessTail := embedPAContext (map witnessedAxiom witnesses)).
  set (fullTemplateContext := prefix ++ witnessTail).

  assert (htailCode : rawTemplateContextCode translation witnessTail =
      extendedContext).
  {
    unfold witnessTail, extendedContext.
    rewrite rawTemplateContextCode_as_on_tail.
    exact (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation agreement witnesses (raw_zero M)).
  }
  assert (hfullCode : rawTemplateContextCode translation fullTemplateContext =
      rawTemplateContextCodeOnTail translation extendedContext prefix).
  {
    unfold fullTemplateContext.
    rewrite rawTemplateContextCode_app_on_tail.
    now rewrite htailCode.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectAssumptionTransferImplicationRoot
      fullTemplateContext)
    (proj1
      (coqRestrictedPADirectAssumptionTransferImplicationRoot_derives
        fullTemplateContext))) as himplication.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation fullTemplateContext)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectAssumptionTransferSourceTemplate
        coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionTransferImplicationRoot
        fullTemplateContext))) in himplication.
  rewrite hfullCode in himplication.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionTransferSourceTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionTransferImplicationRoot
        fullTemplateContext))) in himplication.

  destruct (raw_codedPALocalProof_directTemplatePrefix M hPA inputs
    extendedContext prefix
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionTransferSourceTemplate)
    sourceRoot
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      extendedContext hextended)
    hsource) as [prefixedSourceRoot hprefixedSource].

  exists witnesses.
  exists (rawProofImpERoot M
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionTransferSourceTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionTransferImplicationRoot
        fullTemplateContext))
    prefixedSourceRoot).
  split; [exact hextended |].
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionTransferSourceTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectAssumptionTransferImplicationRoot
        fullTemplateContext))
    prefixedSourceRoot himplication hprefixedSource).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionUniversalSourceCompilation.
