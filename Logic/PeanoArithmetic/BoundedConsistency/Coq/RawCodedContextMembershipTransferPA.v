(**
  PA proof that context membership is independent of a traversal witness.

  Both [contextListMemberTermAt] and the context-wide dynamic truth formula
  existentially hide a complete traversal of the coded context.  Those two
  existential witnesses need not use the same Goedel-beta tables.  Before a
  pointwise truth hypothesis can be applied to a public membership witness,
  the latter must therefore be transported to the tables selected by the
  context-truth witness.

  [RawCodedContextFunctionality] proves that transport semantically in every
  raw PA model.  This file packages the exact, smaller implication needed by
  the Assumption rule as ordinary PA syntax and applies raw-model
  completeness only to that standard arithmetic formula.  In particular,
  no carrier-valued opaque truth code is decoded or passed to completeness.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextFunctionality
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail.

Module PABoundedRawCodedContextMembershipTransferPA.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.

(** The implication is deliberately oriented from the right traversal to
    the left traversal.  In the Assumption compiler, the left tables come
    from context truth and the right tables come from public membership. *)
Definition contextListMemberTransferTermAt
    (root member
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep
      : term) : formula :=
  pImp
    (contextListTraversalTermAt root leftBound
      leftTailCode leftTailStep leftHeadCode leftHeadStep)
    (pImp
      (contextListTraversalTermAt root rightBound
        rightTailCode rightTailStep rightHeadCode rightHeadStep)
      (pImp
        (contextListMemberWithTablesTermAt member rightBound
          rightHeadCode rightHeadStep)
        (contextListMemberWithTablesTermAt member leftBound
          leftHeadCode leftHeadStep))).

Lemma raw_sat_contextListMemberTransferTermAt_iff : forall
    (M : RawPAModel) e root member
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep,
  raw_formula_sat M e
    (contextListMemberTransferTermAt root member
      leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
      rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep) <->
  (RawContextListTraversal M
      (raw_term_eval M e root)
      (raw_term_eval M e leftBound)
      (raw_term_eval M e leftTailCode)
      (raw_term_eval M e leftTailStep)
      (raw_term_eval M e leftHeadCode)
      (raw_term_eval M e leftHeadStep) ->
   RawContextListTraversal M
      (raw_term_eval M e root)
      (raw_term_eval M e rightBound)
      (raw_term_eval M e rightTailCode)
      (raw_term_eval M e rightTailStep)
      (raw_term_eval M e rightHeadCode)
      (raw_term_eval M e rightHeadStep) ->
   RawContextListMemberWithTables M
      (raw_term_eval M e member)
      (raw_term_eval M e rightBound)
      (raw_term_eval M e rightHeadCode)
      (raw_term_eval M e rightHeadStep) ->
   RawContextListMemberWithTables M
      (raw_term_eval M e member)
      (raw_term_eval M e leftBound)
      (raw_term_eval M e leftHeadCode)
      (raw_term_eval M e leftHeadStep)).
Proof.
  intros M e root member
    leftBound leftTailCode leftTailStep leftHeadCode leftHeadStep
    rightBound rightTailCode rightTailStep rightHeadCode rightHeadStep.
  unfold contextListMemberTransferTermAt.
  cbn [raw_formula_sat].
  rewrite !raw_sat_contextListTraversalTermAt_iff.
  rewrite !raw_sat_contextListMemberWithTablesTermAt_iff.
  tauto.
Qed.

(** A fixed open PA formula.  Its free variables, from high to low, are

      root, member,
      leftBound, leftTailCode, leftTailStep, leftHeadCode, leftHeadStep,
      rightBound, rightTailCode, rightTailStep, rightHeadCode, rightHeadStep.

    Keeping the formula open makes it directly instantiable inside the
    endpoint-witness scope used by the restricted-proof soundness compiler. *)
Definition contextListMemberTransferFormula : formula :=
  contextListMemberTransferTermAt
    (tVar 11) (tVar 10)
    (tVar 9) (tVar 8) (tVar 7) (tVar 6) (tVar 5)
    (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0).

Theorem contextListMemberTransferFormula_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e contextListMemberTransferFormula.
Proof.
  intros M hPA e.
  unfold contextListMemberTransferFormula.
  apply (proj2 (raw_sat_contextListMemberTransferTermAt_iff
    M e
    (tVar 11) (tVar 10)
    (tVar 9) (tVar 8) (tVar 7) (tVar 6) (tVar 5)
    (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
  cbn [raw_term_eval].
  intros hleft hright hmember.
  exact (raw_contextListMemberWithTables_transport M hPA
    (e 11) (e 10)
    (e 4) (e 3) (e 2) (e 1) (e 0)
    (e 9) (e 8) (e 7) (e 6) (e 5)
    hright hleft hmember).
Qed.

(** Keep an explicitly twelve-quantifier source public.  Deep represented compilers
    can eliminate its twelve binders at arbitrary carrier-valued witness
    terms; they must not rely on the accidental free-variable positions of an
    open theorem after several surrounding existential eliminations. *)
Definition contextListMemberTransferUniversalFormula : formula :=
  Formula.closeN 12 contextListMemberTransferFormula.

(** Completeness first supplies a sealed theorem; eliminating that generic
    seal returns the convenient open theorem. *)
Theorem PA_proves_contextListMemberTransferFormula :
  Formula.BProv Formula.Ax_s [] contextListMemberTransferFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA contextListMemberTransferFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (contextListMemberTransferFormula_raw_valid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] contextListMemberTransferFormula
    (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** Universal introduction closes the explicitly displayed parameters. *)
Theorem PA_proves_contextListMemberTransferUniversalFormula :
  Formula.BProv Formula.Ax_s [] contextListMemberTransferUniversalFormula.
Proof.
  unfold contextListMemberTransferUniversalFormula.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - exact PA_proves_contextListMemberTransferFormula.
Qed.

(** Carrier-facing global certificate.  Its formula is a standard quotation,
    and the finite PA-axiom witness list remains explicit in the certificate. *)
Theorem raw_codedPAProofOf_contextListMemberTransferFormula : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M contextListMemberTransferFormula)
      certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    contextListMemberTransferFormula
    PA_proves_contextListMemberTransferFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** Universally quantified carrier-facing certificate retained for arbitrary represented
    instantiation. *)
Theorem raw_codedPAProofOf_contextListMemberTransferUniversalFormula : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M contextListMemberTransferUniversalFormula)
      certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    contextListMemberTransferUniversalFormula
    PA_proves_contextListMemberTransferUniversalFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** Exact usable form over an existing witnessed PA tail.  The theorem does
    not pretend that a PA theorem is a context-free logical theorem: it
    returns the finite standard PA-axiom prefix selected by [BProv], together
    with the synchronized enlarged context and its local proof root. *)
Theorem raw_codedTemplatePALocalProofOf_contextListMemberTransfer_on_tail :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext)
      (rawTemplateFormula translation
        (embedPAFormula contextListMemberTransferFormula)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  exact (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation hagreement baseWitnessList baseContext
    contextListMemberTransferFormula hbase
    PA_proves_contextListMemberTransferFormula).
Qed.

(** Exact witnessed-tail form of the explicitly universal source. *)
Theorem
    raw_codedTemplatePALocalProofOf_contextListMemberTransferUniversal_on_tail :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext)
      (rawTemplateFormula translation
        (embedPAFormula contextListMemberTransferUniversalFormula)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  exact (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation hagreement baseWitnessList baseContext
    contextListMemberTransferUniversalFormula hbase
    PA_proves_contextListMemberTransferUniversalFormula).
Qed.

End PABoundedRawCodedContextMembershipTransferPA.
