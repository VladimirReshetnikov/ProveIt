(**
  The assignment-definedness component of predecessor admissibility.

  The universal beta-assignment theorem is compiled beneath the literal Pi,
  Sigma predecessor-state prefix.  This module discharges prefix adequacy
  from standard PA quotation and rewrites the template context to the exact
  raw joint-state context used by the predecessor logical-roots package.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofAtomicAdequacyStandard
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination.

Module
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.

(** Both temporary assumptions are embedded ordinary PA formulae, so PA
    agreement turns their translated codes into standard quotation and the
    generic quotation theorem supplies atomic adequacy. *)
Lemma raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    coqDynamicTruthPredecessorStateTemplateContext.
Proof.
  intros M hPA translation hagreement formula hformula.
  unfold coqDynamicTruthPredecessorStateTemplateContext in hformula.
  destruct hformula as [<- | [<- | []]].
  - rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorPiStateMemberBodyFormula).
    exact (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula).
  - rewrite (rawTemplateFormula_embedPA hagreement
      dynamicTruthPredecessorSigmaStateMemberBodyFormula).
    exact (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorSigmaStateMemberBodyFormula).
Qed.

(** Produce the exact assignment component under the literal predecessor
    state assumptions.  The returned standard prefix is retained so the
    atomic-adequacy and domain components can later be transported into this
    same extension before the three roots are conjoined. *)
Theorem
    raw_dynamicTruthPredecessorLocalAssignmentRoot_on_witnessed_extension :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext))
      (rawDynamicTruthLocalAssignmentDefinedCode M) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hbase)
    as (witnesses & root & hextended & hproof).
  exists witnesses, root. split; [exact hextended |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext)) in hproof.
  unfold rawDynamicTruthLocalAssignmentDefinedCode.
  exact hproof.
Qed.

End
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
