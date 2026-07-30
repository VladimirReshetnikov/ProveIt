(**
  Proof-code compilation of the complete opened Or-I-left coverage source.

  The unconditional PA theorem is instantiated at the direct carrier level,
  transported beneath the exact opened-coverage eigencontext, and exposed in
  the root interface consumed by the recursive-child compiler.  No semantic
  validity hypothesis for the opened law remains at this stage.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  CodedSyntax
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageProvability.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageProvability.

(** The ready context is affine in a tail of embedded PA axioms.  Every such
    axiom is a sentence, so all binder-induced shifts leave the tail fixed. *)
Lemma coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext,
    rawCoqRestrictedPADirectEndpointDeepTail,
    rawCoqRestrictedPADirectEndpointDeepContext,
    rawCoqRestrictedPADirectStrongStepEndpointTail,
    rawCoqRestrictedPADirectStrongStepFourBinderContext.
  cbn [rawCoqTemplateNestedExContext rawCoqTemplateContextShiftN
    templateContextShift templateContextRename List.map List.app].
  repeat rewrite templateContextShift_embedPAAxiomWitnesses.
  reflexivity.
Qed.

Lemma raw_standardPAAxiomWitnessPrefixContextCode_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall prefix baseContext,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
Proof.
  intros M hPA prefix.
  induction prefix as [|witness tail ih]; intros baseContext hbase.
  - exact hbase.
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    apply (raw_contextList_cons_realizable M hPA).
    exact (ih baseContext hbase).
Qed.

(** Prefixing the same finite standard PA list preserves membership
    inclusion between the two carrier tails. *)
Lemma raw_standardPAAxiomWitnessPrefixContextCode_samePrefix_included :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    prefix sourceTail targetTail,
  RawContextListRealizable M sourceTail ->
  RawContextListRealizable M targetTail ->
  RawContextListIncluded M sourceTail targetTail ->
  RawContextListIncluded M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix sourceTail)
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix targetTail).
Proof.
  intros M hPA prefix.
  induction prefix as [|witness tail ih];
    intros sourceTail targetTail hsourceReal htargetReal hincluded.
  - exact hincluded.
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    apply (raw_contextListIncluded_cons M hPA).
    + exact (raw_standardPAAxiomWitnessPrefixContextCode_realizable
        M hPA tail sourceTail hsourceReal).
    + exact (raw_standardPAAxiomWitnessPrefixContextCode_realizable
        M hPA tail targetTail htargetReal).
    + reflexivity.
    + exact (ih sourceTail targetTail
        hsourceReal htargetReal hincluded).
Qed.

(** Compile the universal source over any already witnessed base.  The same
    generic theorem can be reused for future universal arithmetic sources;
    only the source theorem and substitution trace are branch-specific. *)
Theorem raw_codedPALocalProof_openedCoverageLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate)
      (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext [])
      hbase
      PA_proves_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource
      (rawDirect_openedCoverageSource_substitution M hPA inputs)).
Qed.

(** Empty-base specialization in the exact template-tail root interface used
    by the existing Or-I-left recursive-child compiler. *)
Corollary raw_openedCoverageCompilerLawRoot_on_selected_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists (witnesses : StandardPAAxiomWitnessPrefix),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct (raw_codedPALocalProof_openedCoverageLaw_on_witnessed_base
    M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & hroot).
  exists witnesses. split.
  - rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hwitnessed.
  - unfold
      RawCoqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawRoot.
    exists root.
    rewrite (raw_coverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses).
    exact hroot.
Qed.

(** Feeding the compiled structural law to the earlier proof-code compiler
    eliminates the Or-I-left recursive-child residual on the selected tail. *)
Corollary raw_orIntroductionLeft_recursiveChildLawRoot_on_selected_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists (witnesses : StandardPAAxiomWitnessPrefix),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs.
  destruct (raw_openedCoverageCompilerLawRoot_on_selected_witnessed_tail
    M hPA inputs) as (witnesses & hwitnessed & hopened).
  exists witnesses. split; [exact hwitnessed |].
  apply raw_codedPALocalProof_recursiveChildLaw_of_openedCoverageCompiler.
  exact hopened.
Qed.

(** The direct translation of any finite standard PA prefix is itself an
    honest witnessed PA context. *)
Lemma raw_directEmbeddedPAAxiomWitnessContext : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs witnesses.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  pose proof (raw_codedPAAxiomWitnessContext_standardPrefix M hPA
    witnesses (raw_zero M) (raw_zero M) hempty) as hwitnessed.
  rewrite rawTemplateContextCode_as_on_tail.
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    witnesses (raw_zero M)).
  exact hwitnessed.
Qed.

(** Appending another finite standard tail preserves every member of the
    original standard prefix. *)
Lemma raw_directEmbeddedPAAxiomWitnessContext_suffix_included : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses suffix,
  RawContextListIncluded M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses)))
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs witnesses suffix.
  rewrite !rawTemplateContextCode_as_on_tail.
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    witnesses (raw_zero M)).
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    (witnesses ++ suffix) (raw_zero M)).
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  apply (raw_standardPAAxiomWitnessPrefixContextCode_samePrefix_included
    M hPA witnesses (raw_zero M)
    (rawStandardPAAxiomWitnessPrefixContextCode M suffix (raw_zero M))).
  - exact (raw_templateContext_realizable M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs) []).
  - exact (raw_standardPAAxiomWitnessPrefixContextCode_realizable
      M hPA suffix (raw_zero M)
      (raw_templateContext_realizable M hPA
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])).
  - exact (raw_contextListIncluded_zero M hPA
      (rawStandardPAAxiomWitnessPrefixContextCode M
        suffix (raw_zero M))).
Qed.

(** Once compiled, the Or-I-left recursive law survives appending any later
    standard PA tail.  This is the exact stability property needed to merge
    independently selected rule-case axiom prefixes. *)
Theorem raw_orIntroductionLeft_recursiveChildLawRoot_append_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    witnesses suffix,
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs
      (embedPAContext (map witnessedAxiom (witnesses ++ suffix))).
Proof.
  intros M hPA inputs witnesses suffix [root hroot].
  rewrite
    coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses
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
        (witnesses ++ suffix) (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom (witnesses ++ suffix))))
      (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext [])
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate)
      root
      (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs witnesses)
      (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs
        (witnesses ++ suffix))
      (raw_directEmbeddedPAAxiomWitnessContext_suffix_included
        M hPA inputs witnesses suffix)
      hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  exact htransported.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
