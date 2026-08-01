(**
  Object-level and represented universal beta-assignment definedness.

  [RawCodedAssignmentUniversalDefinedness] proves semantically, by PA's
  internal induction, that every beta-coded assignment has an entry at every
  carrier index.  This module closes that result into one PA sentence and
  compiles any three-term instance over an arbitrary witnessed local tail.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedAssignmentUniversalDefinedness
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedPALocalProofUniversalEliminationChain.

Module PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentUniversalDefinedness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** Binder order is code, step, bound.  At the body these occur at de
    Bruijn indices two, one, and zero respectively. *)
Definition codedAssignmentUniversalDefinednessFormula : formula :=
  pAll (pAll (pAll
    (codedAssignmentDefinedThroughTermAt
      (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_codedAssignmentUniversalDefinednessFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedAssignmentUniversalDefinednessFormula <->
  forall code step bound : M,
    RawCodedAssignmentDefinedThrough M code step bound.
Proof.
  intros M e.
  unfold codedAssignmentUniversalDefinednessFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma codedAssignmentUniversalDefinednessFormula_sentence :
  Formula.Sentence codedAssignmentUniversalDefinednessFormula.
Proof.
  intros k hfree.
  unfold codedAssignmentUniversalDefinednessFormula,
    codedAssignmentDefinedThroughTermAt,
    betaEntryExistsPrefixTermAt in hfree.
  cbn in hfree. lia.
Qed.

Lemma codedAssignmentUniversalDefinednessFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedAssignmentUniversalDefinednessFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_codedAssignmentUniversalDefinednessFormula_iff M e)).
  exact (raw_codedAssignment_definedThrough_all M hPA).
Qed.

(** Completeness is used only to turn the already internal semantic PA
    induction into an ordinary finite PA derivation. *)
Theorem PA_proves_codedAssignmentUniversalDefinednessFormula :
  Formula.BProv Formula.Ax_s []
    codedAssignmentUniversalDefinednessFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedAssignmentUniversalDefinednessFormula_sentence.
  - exact codedAssignmentUniversalDefinednessFormula_raw_valid.
Qed.

Definition coqAssignmentUniversalDefinednessInstanceTemplate
    (code step bound : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedAssignmentUniversalDefinednessFormula)
    [code; step; bound].

Lemma coqAssignmentUniversalDefinednessInstanceTemplate_open : forall
    code step bound,
  templateUniversalOpenMany
    (embedPAFormula codedAssignmentUniversalDefinednessFormula)
    [code; step; bound] =
  Some (coqAssignmentUniversalDefinednessInstanceTemplate
    code step bound).
Proof.
  intros code step bound.
  unfold coqAssignmentUniversalDefinednessInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedAssignmentUniversalDefinednessFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** The predecessor-local assignment slots are code [#1], step [#0], and
    formula-code bound [#2].  This concrete opening computes definitionally
    to the exact PA fragment used by the admissibility guard. *)
Lemma coqAssignmentUniversalDefinednessInstanceTemplate_local :
  coqAssignmentUniversalDefinednessInstanceTemplate
    (ttVar 1) (ttVar 0) (ttVar 2) =
  embedPAFormula
    (codedAssignmentDefinedThroughTermAt (tVar 1) (tVar 0) (tVar 2)).
Proof.
  unfold coqAssignmentUniversalDefinednessInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedAssignmentUniversalDefinednessFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

(** Compile the closed theorem once, choose one finite standard axiom
    prefix, and perform all three represented [All-E] steps there. *)
Theorem
    raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext code step bound,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code step bound)) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    code step bound hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      codedAssignmentUniversalDefinednessFormula
      [code; step; bound]
      (coqAssignmentUniversalDefinednessInstanceTemplate code step bound)
      hbase PA_proves_codedAssignmentUniversalDefinednessFormula
      (coqAssignmentUniversalDefinednessInstanceTemplate_open
        code step bound)).
Qed.

(** Compile four arbitrary defined-through instances from the shared closed
    PA theorem on one witnessed tail.  Four-state append is the first client,
    but the statement deliberately allows four unrelated bounds so other
    synchronized beta-table constructions can reuse it.  Selecting the PA
    witness batch once is strictly weaker than asking four callers to choose
    and subsequently merge independent batches. *)
Theorem
    raw_codedPALocalProofOf_assignmentUniversalDefinedness_four_instances_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext
    code1 step1 bound1 code2 step2 bound2
    code3 step3 bound3 code4 step4 bound4,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      root1 root2 root3 root4,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code1 step1 bound1)) root1 /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code2 step2 bound2)) root2 /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code3 step3 bound3)) root3 /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code4 step4 bound4)) root4.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    code1 step1 bound1 code2 step2 bound2
    code3 step3 bound3 code4 step4 bound4 hbase.
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_list_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      codedAssignmentUniversalDefinednessFormula
      [[code1; step1; bound1]; [code2; step2; bound2];
       [code3; step3; bound3]; [code4; step4; bound4]]
      [coqAssignmentUniversalDefinednessInstanceTemplate code1 step1 bound1;
       coqAssignmentUniversalDefinednessInstanceTemplate code2 step2 bound2;
       coqAssignmentUniversalDefinednessInstanceTemplate code3 step3 bound3;
       coqAssignmentUniversalDefinednessInstanceTemplate code4 step4 bound4]
      hbase PA_proves_codedAssignmentUniversalDefinednessFormula)
    as (witnesses & roots & hextended & hroots).
  - repeat constructor;
      apply coqAssignmentUniversalDefinednessInstanceTemplate_open.
  - repeat match goal with
      | h : Forall2 _ (_ :: _) _ |- _ => inversion h; subst; clear h
    end.
    exists witnesses, y, y0, y1, y2.
    split; [exact hextended |].
    split; [eassumption |].
    split; [eassumption |].
    split; eassumption.
Qed.

(** Prefix-general form for use beneath temporary assumptions and
    eigenvariables.  Since this theorem has no caller-supplied premise root,
    only the compiled conclusion must be inserted beneath the prefix. *)
Theorem
    raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix code step bound,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (coqAssignmentUniversalDefinednessInstanceTemplate
          code step bound)) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    prefix code step bound hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      code step bound hbase)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext prefix
    (rawTemplateFormula translation
      (coqAssignmentUniversalDefinednessInstanceTemplate
        code step bound)) sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      extendedWitnessList extendedContext hextended)
    hprefix hsource) as [root hroot].
  exists witnesses, root. split; assumption.
Qed.

(** Public specialization to the literal predecessor-local assignment
    formula.  PA-agreement can immediately rewrite this embedded conclusion
    to the standard quoted numeral used by native admissibility. *)
Corollary
    raw_codedPALocalProofOf_assignmentDefinedThrough_local_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2)))) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      (ttVar 1) (ttVar 0) (ttVar 2) hbase)
    as (prefix & root & hprefixed & hproof).
  rewrite coqAssignmentUniversalDefinednessInstanceTemplate_local in hproof.
  exists prefix, root. split; assumption.
Qed.

(** Exact standard-numeral presentation consumed by
    [RawDynamicTruthLocalAdmissibilityComponentsAt]. *)
Corollary
    raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2)))) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentDefinedThrough_local_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext hbase)
    as (prefix & root & hprefixed & hproof).
  rewrite (rawTemplateFormula_embedPA hagreement
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (tVar 2))) in hproof.
  rewrite rawQuotedFormulaCode_standard in hproof by exact hPA.
  exists prefix, root. split; assumption.
Qed.

(** The same exact local numeral beneath an arbitrary adequate temporary
    prefix.  This is the form consumed by predecessor-state integration. *)
Corollary
    raw_codedPALocalProofOf_assignmentDefinedThrough_local_numeral_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2)))) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    prefix hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      (ttVar 1) (ttVar 0) (ttVar 2) hprefix hbase)
    as (witnesses & root & hextended & hproof).
  rewrite coqAssignmentUniversalDefinednessInstanceTemplate_local in hproof.
  rewrite (rawTemplateFormula_embedPA hagreement
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (tVar 2))) in hproof.
  rewrite rawQuotedFormulaCode_standard in hproof by exact hPA.
  exists witnesses, root. split; assumption.
Qed.

End PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
