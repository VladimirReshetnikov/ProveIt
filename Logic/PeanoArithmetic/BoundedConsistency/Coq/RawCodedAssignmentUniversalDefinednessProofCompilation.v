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
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
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
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
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

End PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
