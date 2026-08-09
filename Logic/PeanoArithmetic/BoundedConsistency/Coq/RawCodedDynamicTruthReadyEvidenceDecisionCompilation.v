(**
  Compile predecessor evidence totality directly in a caller-ready context.

  The historical predecessor adapter inserted both the Sigma-state and
  Pi-state atoms as literal assumptions.  Those atoms are exclusive, so
  asking for represented proofs of both in a consistent ready context would
  make the resulting producer vacuous.  This file instead invokes the local
  decision field at its honest premises: projected closed decision code,
  atomic adequacy, rank-domain totality, and generated assignment coverage.

  Assignment coverage is the only premise that grows the PA-axiom tail.  Its
  compiler returns an explicit [StandardPAAxiomWitnessPrefix]; the other
  three roots are transported to that precise extension before admissibility
  and decision elimination are assembled.  Thus the public result retains
  the metatheoretic witness prefix required by direct rule-case integration.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthLocalFieldProjectionCompilation.

Module PABoundedRawCodedDynamicTruthReadyEvidenceDecisionCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.

(** Strongest non-vacuous ready-context boundary for the decision leaf.
    The result names the exact standard witness batch and records inclusion
    of the caller's witnessed context, so downstream roots can be surrounded
    or synchronized without forgetting where this proof was constructed. *)
Theorem
    raw_dynamicTruthReadyEvidenceDecision_on_standard_witness_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
    sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot atomicRoot domainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalDecisionCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    decisionSourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawFormulaOrCode M sigmaDomain piDomain) domainRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) decisionRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawFormulaOrCode M sigmaEvidence piEvidence) decisionRoot.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext prefix
    sigmaDomain piDomain sigmaEvidence piEvidence
    decisionSourceRoot atomicRoot domainRoot
    hprefix hbase hchain hdecisionSource hatomic hdomain.
  destruct
    (raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      hprefix hbase) as
    (witnesses & assignmentRoot & hextended & hassignment).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }

  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      prefix (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hbase hextended hincluded hatomic) as
    [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      prefix (rawFormulaOrCode M sigmaDomain piDomain) domainRoot
      hbase hextended hincluded hdomain) as
    [transportedDomainRoot htransportedDomain].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext []
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      decisionSourceRoot hbase hextended hincluded hdecisionSource) as
    [transportedDecisionSourceRoot htransportedDecisionSource].
  cbn [rawTemplateContextCodeOnTail] in htransportedDecisionSource.
  destruct
    (raw_codedPALocalProof_templatePrefix
      M hPA translation extendedContext prefix
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      transportedDecisionSourceRoot
      (raw_codedPAAxiomWitnessContext_context_realizable
        M extendedWitnessList extendedContext hextended)
      hprefix htransportedDecisionSource) as
    [prefixedDecisionSourceRoot hprefixedDecisionSource].

  assert (hassignmentCode : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext prefix)
      (rawDynamicTruthLocalAssignmentDefinedCode M) assignmentRoot).
  {
    unfold rawDynamicTruthLocalAssignmentDefinedCode.
    exact hassignment.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalAdmissible_of_components
      M hPA
      (rawTemplateContextCodeOnTail translation extendedContext prefix)
      sigmaDomain piDomain) as [admissibleRoot hadmissible].
  {
    constructor.
    - exists transportedAtomicRoot. exact htransportedAtomic.
    - exists assignmentRoot. exact hassignmentCode.
    - exists transportedDomainRoot. exact htransportedDomain.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthLocalEvidenceDecision_of_elimination_chain
      M hPA
      (rawTemplateContextCodeOnTail translation extendedContext prefix)
      sigmaDomain piDomain sigmaEvidence piEvidence
      prefixedDecisionSourceRoot admissibleRoot
      hchain hprefixedDecisionSource hadmissible) as
    [decisionRoot hdecision].
  exists witnesses, decisionRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hdecision].
Qed.

End PABoundedRawCodedDynamicTruthReadyEvidenceDecisionCompilation.
