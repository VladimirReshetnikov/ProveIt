(**
  Represented projection of endpoint atomic adequacy.

  Proof-wide atomic adequacy stores its endpoint invariant behind two
  existential support-table witnesses.  Downstream restricted-proof clients
  should not have to reopen that implementation each time they need the
  conclusion formula of a particular endpoint.  This module packages the
  semantic root-endpoint theorem as one ordinary PA sentence and compiles an
  arbitrary three-term instance over an existing witnessed PA context.

  Completeness is applied only to the fixed standard arithmetic sentence
  below.  No carrier-valued formula code is decoded by the metatheory.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedFixedLevelTruthTotality
  RawCodedProofEndpoints
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain.

Module PABoundedRawCodedProofEndpointAtomicAdequacyProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** The open implication uses proof root, endpoint context, and endpoint
    conclusion at variables two, one, and zero.  Keeping this intermediate
    formula open lets completeness use [sealPA] without expanding the large
    support-table encodings in a hand-written scope proof. *)
Definition proofEndpointAtomicAdequacyFormula : formula :=
  pImp
    (proofAtomicallyAdequateTermAt (tVar 2))
    (pImp
      (proofEndpointTermAt (tVar 2) (tVar 1) (tVar 0))
      (codedFormulaAtomicallyAdequateTermAt (tVar 0))).

Lemma raw_sat_proofEndpointAtomicAdequacyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e proofEndpointAtomicAdequacyFormula <->
  (RawProofAtomicallyAdequate M (e 2) ->
   RawProofEndpoint M (e 2) (e 1) (e 0) ->
   RawCodedFormulaAtomicallyAdequate M (e 0)).
Proof.
  intros M e.
  unfold proofEndpointAtomicAdequacyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_proofEndpointTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  cbn [raw_term_eval scons]. tauto.
Qed.

Lemma proofEndpointAtomicAdequacyFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e proofEndpointAtomicAdequacyFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_proofEndpointAtomicAdequacyFormula_iff M e)).
  intros hatomic hendpoint.
  exact (proj2
    (raw_proofAtomicallyAdequate_root_endpoint M hPA (e 2) hatomic
      (e 1) (e 0) hendpoint)).
Qed.

(** Completeness first proves the standard open implication by sealing and
    reopening it.  No carrier value occurs in this step. *)
Theorem PA_proves_proofEndpointAtomicAdequacyFormula :
  Formula.BProv Formula.Ax_s []
    proofEndpointAtomicAdequacyFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA proofEndpointAtomicAdequacyFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (proofEndpointAtomicAdequacyFormula_raw_valid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] proofEndpointAtomicAdequacyFormula
    (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** Binder order is proof root, endpoint context, and endpoint conclusion.
    [closeN] introduces those three binders without requiring a gigantic
    syntactic expansion of their bodies. *)
Definition proofEndpointAtomicAdequacyUniversalFormula : formula :=
  Formula.closeN 3 proofEndpointAtomicAdequacyFormula.

Theorem PA_proves_proofEndpointAtomicAdequacyUniversalFormula :
  Formula.BProv Formula.Ax_s []
    proofEndpointAtomicAdequacyUniversalFormula.
Proof.
  unfold proofEndpointAtomicAdequacyUniversalFormula.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - exact PA_proves_proofEndpointAtomicAdequacyFormula.
Qed.

Definition coqProofEndpointAtomicAdequacyInstanceTemplate
    (root context conclusion : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula proofEndpointAtomicAdequacyUniversalFormula)
    [root; context; conclusion].

Lemma coqProofEndpointAtomicAdequacyInstanceTemplate_open : forall
    root context conclusion,
  templateUniversalOpenMany
    (embedPAFormula proofEndpointAtomicAdequacyUniversalFormula)
    [root; context; conclusion] =
  Some (coqProofEndpointAtomicAdequacyInstanceTemplate
    root context conclusion).
Proof.
  intros root context conclusion. reflexivity.
Qed.

(** Stable views of the two premises and conclusion.  Naming these views
    avoids duplicating the very large opened standard formula in client
    interfaces. *)
Definition coqProofEndpointAtomicAdequacyAtomicPremise
    (root context conclusion : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent
    (coqProofEndpointAtomicAdequacyInstanceTemplate
      root context conclusion).

Definition coqProofEndpointAtomicAdequacyEndpointPremise
    (root context conclusion : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent (templateImpConsequent
    (coqProofEndpointAtomicAdequacyInstanceTemplate
      root context conclusion)).

Definition coqProofEndpointAtomicAdequacyConclusion
    (root context conclusion : TemplateTerm) : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    (coqProofEndpointAtomicAdequacyInstanceTemplate
      root context conclusion)).

Lemma coqProofEndpointAtomicAdequacyInstanceTemplate_imp2_shape : forall
    root context conclusion,
  coqProofEndpointAtomicAdequacyInstanceTemplate root context conclusion =
  tfImp
    (coqProofEndpointAtomicAdequacyAtomicPremise
      root context conclusion)
    (tfImp
      (coqProofEndpointAtomicAdequacyEndpointPremise
        root context conclusion)
      (coqProofEndpointAtomicAdequacyConclusion
        root context conclusion)).
Proof.
  intros root context conclusion. reflexivity.
Qed.

(** Compile the PA theorem once and perform all three represented [All-E]
    steps in the single standard witness extension chosen by its finite
    derivation. *)
Theorem
    raw_codedPALocalProofOf_proofEndpointAtomicAdequacy_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext root context conclusion,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyInstanceTemplate
          root context conclusion)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    root context conclusion hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      proofEndpointAtomicAdequacyUniversalFormula
      [root; context; conclusion]
      (coqProofEndpointAtomicAdequacyInstanceTemplate
        root context conclusion)
      hbase PA_proves_proofEndpointAtomicAdequacyUniversalFormula
      (coqProofEndpointAtomicAdequacyInstanceTemplate_open
        root context conclusion)).
Qed.

(** Apply the compiled implication to caller-supplied proof-wide adequacy and
    endpoint roots.  The finite PA derivation may adjoin a standard axiom
    prefix, so both incoming roots are transported into that exact extension
    before the two checked [Imp-E] nodes are constructed. *)
Theorem
    raw_codedPALocalProofOf_proofEndpointAtomicAdequacy_of_roots_on_witnessed_extension :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext root context conclusion
      atomicRoot endpointRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (coqProofEndpointAtomicAdequacyAtomicPremise
        root context conclusion)) atomicRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (coqProofEndpointAtomicAdequacyEndpointPremise
        root context conclusion)) endpointRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix) resultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyConclusion
          root context conclusion)) resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    root context conclusion atomicRoot endpointRoot hbase hatomic hendpoint.
  destruct
    (raw_codedPALocalProofOf_proofEndpointAtomicAdequacy_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      root context conclusion hbase)
    as (prefix & implicationRoot & hextended & himplication).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      prefix baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA prefix baseContext).
  }
  assert (hatomicOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyAtomicPremise
          root context conclusion)) atomicRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hatomic. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyAtomicPremise
          root context conclusion)) atomicRoot
      hbase hextended hincluded hatomicOnEmptyPrefix)
    as [transportedAtomicRoot htransportedAtomic].
  cbn [rawTemplateContextCodeOnTail] in htransportedAtomic.
  assert (hendpointOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyEndpointPremise
          root context conclusion)) endpointRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hendpoint. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyEndpointPremise
          root context conclusion)) endpointRoot
      hbase hextended hincluded hendpointOnEmptyPrefix)
    as [transportedEndpointRoot htransportedEndpoint].
  cbn [rawTemplateContextCodeOnTail] in htransportedEndpoint.
  rewrite coqProofEndpointAtomicAdequacyInstanceTemplate_imp2_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
    (rawTemplateFormula translation
      (coqProofEndpointAtomicAdequacyAtomicPremise
        root context conclusion))
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyEndpointPremise
          root context conclusion))
      (rawTemplateFormula translation
        (coqProofEndpointAtomicAdequacyConclusion
          root context conclusion)))
    implicationRoot transportedAtomicRoot
    himplication htransportedAtomic) as hafterAtomic.
  lazymatch type of hafterAtomic with
  | RawCodedPALocalProofOf _ _ _ ?afterAtomicRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
        (rawTemplateFormula translation
          (coqProofEndpointAtomicAdequacyEndpointPremise
            root context conclusion))
        (rawTemplateFormula translation
          (coqProofEndpointAtomicAdequacyConclusion
            root context conclusion))
        afterAtomicRoot transportedEndpointRoot
        hafterAtomic htransportedEndpoint) as hresult;
      lazymatch type of hresult with
      | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists prefix, resultRoot;
          split; [exact hextended |];
          split; [exact hincluded | exact hresult]
      end
  end.
Qed.

End PABoundedRawCodedProofEndpointAtomicAdequacyProofCompilation.
