(**
  Prototype integration over a witnessed finite template tail.

  The original direct rule-case integration specializes every semantic root
  to the empty template tail and only afterwards weakens the resulting
  strong-step proof into a PA-axiom context.  That order prevents a semantic
  compiler from using an ordinary PA helper theorem: compiling such a helper
  honestly adds its finite witnessed PA-axiom prefix.

  This module records the smallest replacement boundary.  The caller
  supplies a finite template tail whose translated code is already an honest
  witnessed PA context, and all twenty-three semantic fields are required in
  that one literal tail.  The strong-step proof is then transported only once,
  from this witnessed base into the context obtained by adjoining the genuine
  induction axiom.  No shared integration or case module is changed here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAInductionAxiomCertificate
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleCases.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedCodedProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCases.

(** Folding a concatenated finite template context onto zero is the same as
    folding its left prefix onto the already-folded right tail. *)
Lemma raw_templateContextCode_app_on_tail : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    left right,
  rawTemplateContextCode translation (left ++ right) =
  rawTemplateContextCodeOnTail translation
    (rawTemplateContextCode translation right) left.
Proof.
  intros M translation left.
  induction left as [| formula tail ih]; intro right.
  - reflexivity.
  - cbn [List.app rawTemplateContextCode rawTemplateContextCodeOnTail].
    f_equal. apply ih.
Qed.

(** This is the literal equation needed after a [BProv] compiler selects a
    finite standard prefix.  It turns the returned carrier context back into
    the finite [TemplateContext] expected by every rule-case residual. *)
Lemma raw_templateContextCode_standardPAAxiomPrefix_app : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall prefix tail,
  rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom prefix) ++ tail) =
  rawStandardPAAxiomWitnessPrefixContextCode M prefix
    (rawTemplateContextCode translation tail).
Proof.
  intros M translation hagreement prefix tail.
  rewrite raw_templateContextCode_app_on_tail.
  exact (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement prefix
    (rawTemplateContextCode translation tail)).
Qed.

(** Honest generalization of the old [tail = []] integration theorem.  The
    source of the one weakening step and the base consumed by the growing
    compiler are definitionally the same translated template context. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_semantic_roots_on_witnessed_tail
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : TemplateContext)
      replacement axiom closureCount baseWitnessList,
  RawCodedPAAxiomWitnessContext M baseWitnessList
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail) ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs tail ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      soundnessCertificate.
Proof.
  intros M hPA inputs tail replacement axiom closureCount
    baseWitnessList hbase hremainder hsemantic.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (baseContext := rawTemplateContextCode translation tail).
  set (extendedWitnessList :=
    rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)).
  set (extendedContext :=
    rawPAInductionExtendedContext M baseContext axiom).

  assert (hextended : RawCodedPAAxiomWitnessContext M
      extendedWitnessList extendedContext).
  {
    unfold extendedWitnessList, extendedContext, baseContext.
    exact
      (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
        M hPA inputs replacement axiom closureCount
        baseWitnessList
        (rawTemplateContextCode translation tail)
        hbase hremainder).
  }
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      baseWitnessList baseContext hbase).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      extendedWitnessList extendedContext hextended).
  }

  (** The translated tail occurs literally as the tail of the extended
      context: [extendedContext = axiom :: baseContext]. *)
  assert (hbaseIncluded : RawContextListIncluded M
      baseContext extendedContext).
  {
    unfold extendedContext, rawPAInductionExtendedContext.
    apply (raw_contextListIncluded_cons_target M hPA
      baseContext baseContext axiom).
    exact (raw_contextListIncluded_refl M baseContext).
  }
  assert (hbaseReady : RawContextBinderReady M
      baseContext extendedContext).
  {
    exact (raw_contextBinderReady_witnessed_target M hPA
      baseContext extendedContext extendedWitnessList
      hbaseIncluded hextended).
  }

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep_of_rule_case_semantic_roots
      M hPA inputs tail hsemantic)
    as [baseStrongStepRoot hbaseStrongStep].
  change (RawCodedPALocalProofOf M baseContext
    (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
      M inputs) baseStrongStepRoot) in hbaseStrongStep.
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA baseContext extendedContext
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      baseStrongStepRoot hbaseRealizable hextendedRealizable
      hbaseIncluded hbaseReady hbaseStrongStep)
    as [strongStepRoot hstrongStep].

  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_growing_case_and_finalizer
      M hPA inputs replacement axiom closureCount
      baseWitnessList baseContext strongStepRoot
      hbase hremainder hstrongStep)
    as (prefix & zeroChild & stepChild & arithmeticOpenRoot & bodyChild &
      hsoundness).
  eexists. exact hsoundness.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromWitnessedRuleCases.
