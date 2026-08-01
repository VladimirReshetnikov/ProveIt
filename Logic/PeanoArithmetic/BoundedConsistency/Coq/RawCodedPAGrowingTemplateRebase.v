(** Unary rebasing for a proof over a growing witnessed PA tail.

    This module is kept above concrete traversal clients in the dependency
    graph.  A producer and its caller may independently choose finite batches
    of PA-axiom witnesses; completed-context merge supplies a common target,
    while prefix-preserving transport keeps temporary assumptions intact.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedLtSuccCasesProofCompilation
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateLocalProofWitnessedTailTransport.

Module PABoundedRawCodedPAGrowingTemplateRebase.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.

(** Rebase one growing proof onto an arbitrary witnessed caller tail.  No
    relation between the producer's original source and the new caller is
    required: only the witnessed target actually selected by the producer
    needs to be merged. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_rebase : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    producerSourceWitnessList producerSourceContext prefix conclusion
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    producerSourceWitnessList producerSourceContext prefix conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix conclusion.
Proof.
  intros M hPA translation
    producerSourceWitnessList producerSourceContext prefix conclusion
    baseWitnessList baseContext hbase
    (producerWitnessList & producerContext & root &
      hproducerWitnessed & _hproducerSourceIncluded & hproof).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      producerWitnessList producerContext baseWitnessList baseContext
      hproducerWitnessed hbase)
    as (targetWitnessList & targetContext & htargetWitnessed &
      _hproducerWitnessIncluded & hproducerIncluded &
      _hbaseWitnessIncluded & hbaseIncluded & _hbaseTransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation producerWitnessList producerContext
      targetWitnessList targetContext prefix conclusion root
      hproducerWitnessed htargetWitnessed hproducerIncluded hproof)
    as [transportedRoot htransported].
  exists targetWitnessList, targetContext, transportedRoot.
  split; [exact htargetWitnessed |].
  split; [exact hbaseIncluded | exact htransported].
Qed.

End PABoundedRawCodedPAGrowingTemplateRebase.
