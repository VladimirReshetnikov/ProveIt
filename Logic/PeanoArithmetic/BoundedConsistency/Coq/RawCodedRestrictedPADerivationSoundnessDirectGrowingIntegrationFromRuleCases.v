(**
  Connect the exact seventeen-way direct rule dispatcher to the growing
  strong-prefix compiler.

  The rule-case shell is compiled over the empty finite template tail.  The
  induction axiom selected by the closure remainder can have a genuinely
  nonstandard universal-closure depth, so it must not be reinterpreted as a
  finite [TemplateFormula].  Instead, the closure remainder proves that the
  enlarged carrier context is a witnessed PA-axiom context.  The shell's
  public binder-ready transport theorem then moves the closed strong-step
  root into that literal enlarged context before the existing growing case
  and finalizer integration is invoked.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
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
  RawCodedTemplateDirectStructuralTranslation
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixFinalizerCompilationDirect
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixGrowingIntegrationDirect
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleCases.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromRuleCases.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
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

(** Exact composition boundary.  The only semantic premise is the existing
    residual-only package, specialized to the empty template tail.  Closure
    and base witnessing are the exact inputs already consumed by the growing
    compiler; the conclusion is an ordinary PA proof of the concrete direct
    universal-soundness code. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_rule_case_semantic_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCoqRestrictedPADirectRuleCaseSemanticRoots M hPA inputs [] ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      soundnessCertificate.
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext hbase hremainder hsemantic.
  set (extendedWitnessList :=
    rawPAInductionExtendedWitnessList M baseWitnessList
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixDirectCode
        M inputs)).
  set (extendedContext :=
    rawPAInductionExtendedContext M baseContext axiom).

  (** The induction context is carrier-valued, but closure proves it is an
      honest witnessed PA context. *)
  assert (hextended : RawCodedPAAxiomWitnessContext M
      extendedWitnessList extendedContext).
  {
    unfold extendedWitnessList, extendedContext.
    exact
      (raw_coqRestrictedPADerivationSoundnessCarrierFinalizerDirect_extendedContext_witnessed
        M hPA inputs replacement axiom closureCount
        baseWitnessList baseContext hbase hremainder).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      extendedWitnessList extendedContext hextended).
  }

  (** The empty compiled tail is included in every context.  Witnessing of
      the target supplies the stronger binder-readiness invariant required
      to transport proof trees containing All-I and Ex-E. *)
  assert (hemptyIncluded : RawContextListIncluded M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])
      extendedContext).
  {
    change (RawContextListIncluded M (raw_zero M) extendedContext).
    exact (raw_contextListIncluded_zero M hPA extendedContext).
  }
  assert (hemptyReady : RawContextBinderReady M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])
      extendedContext).
  {
    exact (raw_contextBinderReady_witnessed_target M hPA
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])
      extendedContext extendedWitnessList hemptyIncluded hextended).
  }

  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectStrongStep_of_rule_case_semantic_roots
      M hPA inputs [] hsemantic)
    as [emptyStrongStepRoot hemptyStrongStep].
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])
      extendedContext
      (rawCoqRestrictedPADerivationSoundnessCarrierStrongStepDirectCode
        M inputs)
      emptyStrongStepRoot
      (raw_templateContext_realizable M hPA
        (rawDirectStructuralTemplateTranslation M hPA inputs) [])
      hextendedRealizable hemptyIncluded hemptyReady hemptyStrongStep)
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectGrowingIntegrationFromRuleCases.
