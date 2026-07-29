(**
  Binder-safe transport beneath a shared finite template prefix.

  Independently compiled PA helper theorems select different finite witnessed
  axiom tails.  Rule-case proofs do not live directly in those tails: each is
  nested below a finite list of temporary template assumptions.  This module
  lifts witnessed-context inclusion through any such common prefix and then
  applies the completed binder-safe local-proof weakening theorem.
*)

From Stdlib Require Import List.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail.

Module PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.

(** Membership inclusion is preserved while the same metatheoretic template
    list is folded onto both carrier-coded tails. *)
Lemma raw_templateContextCodeOnTail_included : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceTail targetTail prefix,
  RawContextListRealizable M sourceTail ->
  RawContextListRealizable M targetTail ->
  RawContextListIncluded M sourceTail targetTail ->
  RawContextListIncluded M
    (rawTemplateContextCodeOnTail translation sourceTail prefix)
    (rawTemplateContextCodeOnTail translation targetTail prefix).
Proof.
  intros M hPA translation sourceTail targetTail prefix.
  induction prefix as [|head tail ih];
    intros hsourceReal htargetReal hincluded.
  - exact hincluded.
  - cbn [rawTemplateContextCodeOnTail].
    apply (raw_contextListIncluded_cons M hPA).
    + exact (raw_templateContextOnTail_realizable M hPA
        translation sourceTail tail hsourceReal).
    + exact (raw_templateContextOnTail_realizable M hPA
        translation targetTail tail htargetReal).
    + reflexivity.
    + exact (ih hsourceReal htargetReal hincluded).
Qed.

(** Binder readiness is likewise stable under a shared local prefix.  The
    head formula need not be independently adequate: inversion of any source
    shift supplies the same concrete head shift on the target side. *)
Lemma raw_templateContextCodeOnTail_binderReady : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceTail targetTail prefix,
  RawContextListRealizable M sourceTail ->
  RawContextListRealizable M targetTail ->
  RawContextBinderReady M sourceTail targetTail ->
  RawContextBinderReady M
    (rawTemplateContextCodeOnTail translation sourceTail prefix)
    (rawTemplateContextCodeOnTail translation targetTail prefix).
Proof.
  intros M hPA translation sourceTail targetTail prefix.
  induction prefix as [|head tail ih];
    intros hsourceReal htargetReal hready.
  - exact hready.
  - cbn [rawTemplateContextCodeOnTail].
    apply (raw_contextBinderReady_cons M hPA).
    + exact (raw_templateContextOnTail_realizable M hPA
        translation sourceTail tail hsourceReal).
    + exact (raw_templateContextOnTail_realizable M hPA
        translation targetTail tail htargetReal).
    + exact (ih hsourceReal htargetReal hready).
Qed.

(** General local transport once the two carrier tails already satisfy the
    concrete realizability, inclusion, and binder-readiness invariants. *)
Theorem raw_codedPALocalProof_sameTemplatePrefix_transport : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceTail targetTail prefix conclusion root,
  RawContextListRealizable M sourceTail ->
  RawContextListRealizable M targetTail ->
  RawContextListIncluded M sourceTail targetTail ->
  RawContextBinderReady M sourceTail targetTail ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceTail prefix)
    conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetTail prefix)
      conclusion transportedRoot.
Proof.
  intros M hPA translation sourceTail targetTail prefix conclusion root
    hsourceReal htargetReal hincluded hready hproof.
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawTemplateContextCodeOnTail translation sourceTail prefix)
    (rawTemplateContextCodeOnTail translation targetTail prefix)
    conclusion root).
  - exact (raw_templateContextOnTail_realizable M hPA
      translation sourceTail prefix hsourceReal).
  - exact (raw_templateContextOnTail_realizable M hPA
      translation targetTail prefix htargetReal).
  - exact (raw_templateContextCodeOnTail_included M hPA translation
      sourceTail targetTail prefix hsourceReal htargetReal hincluded).
  - exact (raw_templateContextCodeOnTail_binderReady M hPA translation
      sourceTail targetTail prefix hsourceReal htargetReal hready).
  - exact hproof.
Qed.

(** Public specialization: witnessing provides both realizability facts and
    the initial binder square, so callers need supply only literal context
    inclusion and the local proof to be transported. *)
Corollary raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceTail targetWitnessList targetTail
    prefix conclusion root,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceTail ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetTail ->
  RawContextListIncluded M sourceTail targetTail ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceTail prefix)
    conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetTail prefix)
      conclusion transportedRoot.
Proof.
  intros M hPA translation sourceWitnessList sourceTail
    targetWitnessList targetTail prefix conclusion root
    hsourceWitnessed htargetWitnessed hincluded hproof.
  apply (raw_codedPALocalProof_sameTemplatePrefix_transport
    M hPA translation sourceTail targetTail prefix conclusion root).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceTail hsourceWitnessed).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetTail htargetWitnessed).
  - exact hincluded.
  - exact (raw_contextBinderReady_witnessed_target M hPA
      sourceTail targetTail targetWitnessList
      hincluded htargetWitnessed).
  - exact hproof.
Qed.

End PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
