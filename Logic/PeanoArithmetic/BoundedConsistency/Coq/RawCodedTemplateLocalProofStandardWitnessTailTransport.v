(**
  Translation-generic local-proof transport across standard witnessed tails.

  A branch compiler commonly produces a local proof below a fixed finite
  template prefix and a selected list of standard PA axioms.  Independently
  compiled branches may contribute an earlier witness batch and later
  compilers may append another batch.  This module proves once and for all
  that the original local proof transports to the combined tail.

  No direct-soundness input record is required.  The only translation-specific
  premise is ordinary agreement with embedded PA syntax.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport.

Import ListNotations.

Module PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.

Lemma raw_templateContextCode_app_on_tail_general : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    left right,
  rawTemplateContextCode translation (left ++ right) =
  rawTemplateContextCodeOnTail translation
    (rawTemplateContextCode translation right) left.
Proof.
  intros M translation left.
  induction left as [| head tail ih]; intro right.
  - reflexivity.
  - cbn [List.app rawTemplateContextCode rawTemplateContextCodeOnTail].
    now rewrite ih.
Qed.

Lemma raw_templateContextCode_as_on_tail_general : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M) context,
  rawTemplateContextCode translation context =
  rawTemplateContextCodeOnTail translation (raw_zero M) context.
Proof.
  intros M translation context.
  induction context as [| head tail ih].
  - reflexivity.
  - cbn [rawTemplateContextCode rawTemplateContextCodeOnTail].
    now rewrite ih.
Qed.

Lemma raw_standardPAAxiomWitnessPrefixContextCode_target_included : forall
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

Lemma raw_standardPAAxiomWitnessPrefixContextCode_samePrefix_included_general :
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
  induction prefix as [| witness tail ih];
    intros sourceTail targetTail hsource htarget hincluded.
  - exact hincluded.
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    apply (raw_contextListIncluded_cons M hPA).
    + exact (raw_standardPAAxiomWitnessPrefix_context_realizable
        M hPA tail sourceTail hsource).
    + exact (raw_standardPAAxiomWitnessPrefix_context_realizable
        M hPA tail targetTail htarget).
    + reflexivity.
    + exact (ih sourceTail targetTail hsource htarget hincluded).
Qed.

Lemma raw_templateEmbeddedPAAxiomWitnessContext : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA translation hagreement witnesses.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  pose proof (raw_codedPAAxiomWitnessContext_standardPrefix M hPA
    witnesses (raw_zero M) (raw_zero M) hempty) as hwitnessed.
  rewrite raw_templateContextCode_as_on_tail_general.
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement witnesses (raw_zero M)).
  exact hwitnessed.
Qed.

Lemma raw_templateEmbeddedPAAxiomWitnessContext_surrounded_included : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    prefix witnesses suffix,
  RawContextListIncluded M
    (rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom witnesses)))
    (rawTemplateContextCode translation
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix))))).
Proof.
  intros M hPA translation hagreement prefix witnesses suffix.
  rewrite !raw_templateContextCode_as_on_tail_general.
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement witnesses (raw_zero M)).
  rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement
    (prefix ++ (witnesses ++ suffix)) (raw_zero M)).
  rewrite !rawStandardPAAxiomWitnessPrefixContextCode_app.
  intros member hmember.
  apply
    (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA prefix
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M suffix
          (raw_zero M))) member).
  apply
    (raw_standardPAAxiomWitnessPrefixContextCode_samePrefix_included_general
      M hPA witnesses
      (raw_zero M)
      (rawStandardPAAxiomWitnessPrefixContextCode M suffix (raw_zero M))).
  - exact (raw_templateContext_realizable M hPA translation []).
  - exact (raw_standardPAAxiomWitnessPrefix_context_realizable
      M hPA suffix (raw_zero M)
      (raw_templateContext_realizable M hPA translation [])).
  - exact (raw_contextListIncluded_zero M hPA
      (rawStandardPAAxiomWitnessPrefixContextCode M suffix (raw_zero M))).
  - exact hmember.
Qed.

(** The main reusable result.  The local template prefix is completely
    arbitrary and the conclusion is an arbitrary carrier formula code. *)
Theorem raw_codedPALocalProof_standardWitnessTail_surround_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    localPrefix prefix witnesses suffix conclusion root,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (localPrefix ++ embedPAContext (map witnessedAxiom witnesses)))
    conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (localPrefix ++ embedPAContext
          (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))))
      conclusion transportedRoot.
Proof.
  intros M hPA translation hagreement localPrefix prefix witnesses suffix
    conclusion root hroot.
  rewrite raw_templateContextCode_app_on_tail_general in hroot.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom witnesses)))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (prefix ++ (witnesses ++ suffix)) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext
          (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))))
      localPrefix conclusion root
      (raw_templateEmbeddedPAAxiomWitnessContext
        M hPA translation hagreement witnesses)
      (raw_templateEmbeddedPAAxiomWitnessContext
        M hPA translation hagreement
        (prefix ++ (witnesses ++ suffix)))
      (raw_templateEmbeddedPAAxiomWitnessContext_surrounded_included
        M hPA translation hagreement prefix witnesses suffix)
      hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite raw_templateContextCode_app_on_tail_general.
  exact htransported.
Qed.

End PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
