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
  RawCodedFixedLevelTruthTotality
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertUnconditional
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
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.

(** The weakest translation-generic condition needed to insert a finite
    template prefix above an existing local proof.  Direct structural
    translations satisfy it automatically, but arithmetic-only clients can
    discharge it without constructing the much larger direct-input record. *)
Definition RawCodedTemplatePrefixAtomicallyAdequate
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (prefix : TemplateContext) : Prop :=
  forall formula,
    In formula prefix ->
    RawCodedFormulaAtomicallyAdequate M
      (rawTemplateFormula translation formula).

Arguments RawCodedTemplatePrefixAtomicallyAdequate
  M translation prefix : clear implicits.

(** Insert an arbitrary finite adequate template prefix.  This factors the
    induction previously repeated by direct-template clients and avoids any
    assumption that the temporary formulas themselves are PA axioms. *)
Theorem raw_codedPALocalProof_templatePrefix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseContext prefix conclusion root,
  RawContextListRealizable M baseContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists prefixedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      conclusion prefixedRoot.
Proof.
  intros M hPA translation baseContext prefix.
  induction prefix as [|head tail ih];
    intros conclusion root hbase hadequate hproof.
  - cbn [rawTemplateContextCodeOnTail].
    exists root. exact hproof.
  - cbn [rawTemplateContextCodeOnTail].
    destruct (ih conclusion root hbase
      (fun formula hformula => hadequate formula (or_intror hformula))
      hproof) as [tailRoot htail].
    apply (raw_codedPALocalProof_adequateConsTransplant M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation head)
      conclusion tailRoot).
    + exact (hadequate head (or_introl eq_refl)).
    + exact (raw_templateContextOnTail_realizable M hPA
        translation baseContext tail hbase).
    + exact htail.
Qed.

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
