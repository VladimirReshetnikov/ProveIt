(**
  Represented inheritance of atomic adequacy by implication children.

  A dynamic-truth row exposes its constructor witnesses only after the
  row's existential prefix has been opened.  At that point the useful
  premise is not a separately supplied syntax traversal, but the equality

      parent = implication(left, right).

  This module internalizes the corresponding general PA law.  It is kept
  independent of dynamic truth: every atomically adequate implication code
  has atomically adequate left and right children.  The compiler-facing
  half permits the three displayed codes to be arbitrary capture-avoiding
  template terms and synchronizes both caller premises on the finite PA
  witness extension chosen for the closed theorem.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaBoundAtomicallyAdequateTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalEliminationChain.

Module PABoundedRawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** Binder order is parent, left child, right child.  The body therefore
    sees those values at de Bruijn indices [2], [1], and [0]. *)
Definition codedFormulaImpChildrenAtomicAdequacyBodyFormula : formula :=
  pImp
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))
    (pImp
      (formulaImpCodeTermAt (tVar 2) (tVar 1) (tVar 0))
      (pAnd
        (codedFormulaAtomicallyAdequateTermAt (tVar 1))
        (codedFormulaAtomicallyAdequateTermAt (tVar 0)))).

Definition codedFormulaImpChildrenAtomicAdequacyFormula : formula :=
  pAll (pAll (pAll codedFormulaImpChildrenAtomicAdequacyBodyFormula)).

Lemma raw_codedFormulaAtomicallyAdequate_imp_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall parent left right,
  RawCodedFormulaAtomicallyAdequate M parent ->
  parent = rawFormulaImpCode M left right ->
  RawCodedFormulaAtomicallyAdequate M left /\
  RawCodedFormulaAtomicallyAdequate M right.
Proof.
  intros M hPA parent left right hparent hshape.
  subst parent.
  destruct (raw_codedFormulaAtomicallyAdequate_shape_at M hPA
    (rawShapeImp left right) hparent) as
    (formulaCode & formulaStep & bound & rootIndex &
      htraversal & hatomic & leftIndex & rightIndex &
      hleftBelow & hleftLookup & hrightBelow & hrightLookup).
  split.
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaImpCode M left right) leftIndex left
      htraversal hatomic hleftBelow hleftLookup).
  - exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
      formulaCode formulaStep bound rootIndex
      (rawFormulaImpCode M left right) rightIndex right
      htraversal hatomic hrightBelow hrightLookup).
Qed.

Lemma raw_sat_codedFormulaImpChildrenAtomicAdequacyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedFormulaImpChildrenAtomicAdequacyFormula <->
  forall parent left right : M,
    RawCodedFormulaAtomicallyAdequate M parent ->
    parent = rawFormulaImpCode M left right ->
    RawCodedFormulaAtomicallyAdequate M left /\
    RawCodedFormulaAtomicallyAdequate M right.
Proof.
  intros M e.
  unfold codedFormulaImpChildrenAtomicAdequacyFormula,
    codedFormulaImpChildrenAtomicAdequacyBodyFormula.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma codedFormulaImpChildrenAtomicAdequacyFormula_sentence :
  Formula.Sentence codedFormulaImpChildrenAtomicAdequacyFormula.
Proof.
  intros k hfree.
  unfold codedFormulaImpChildrenAtomicAdequacyFormula,
    codedFormulaImpChildrenAtomicAdequacyBodyFormula,
    codedFormulaAtomicallyAdequateTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedFormulaImpChildrenAtomicAdequacyFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedFormulaImpChildrenAtomicAdequacyFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_codedFormulaImpChildrenAtomicAdequacyFormula_iff M e)).
  exact (raw_codedFormulaAtomicallyAdequate_imp_children M hPA).
Qed.

Theorem PA_proves_codedFormulaImpChildrenAtomicAdequacyFormula :
  Formula.BProv Formula.Ax_s []
    codedFormulaImpChildrenAtomicAdequacyFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedFormulaImpChildrenAtomicAdequacyFormula_sentence.
  - exact codedFormulaImpChildrenAtomicAdequacyFormula_raw_valid.
Qed.

(** Capture-avoiding opening is essential here: the implication-row
    witnesses live below several unrelated global and local binders. *)
Definition coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
    (parent left right : TemplateTerm) : TemplateFormula :=
  templateUniversalOpenManyOrBot
    (embedPAFormula codedFormulaImpChildrenAtomicAdequacyFormula)
    [parent; left; right].

Lemma coqFormulaImpChildrenAtomicAdequacyInstanceTemplate_open : forall
    parent left right,
  templateUniversalOpenMany
    (embedPAFormula codedFormulaImpChildrenAtomicAdequacyFormula)
    [parent; left; right] =
  Some (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
    parent left right).
Proof.
  intros parent left right.
  unfold coqFormulaImpChildrenAtomicAdequacyInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedFormulaImpChildrenAtomicAdequacyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst].
  reflexivity.
Qed.

Definition coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate
    parent left right :=
  templateImpAntecedent
    (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate parent left right).

Definition coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
    parent left right :=
  templateImpAntecedent (templateImpConsequent
    (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate parent left right)).

Definition coqFormulaImpChildrenAtomicAdequacyConclusionTemplate
    parent left right :=
  templateImpConsequent (templateImpConsequent
    (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate parent left right)).

Lemma coqFormulaImpChildrenAtomicAdequacyInstanceTemplate_imp2_shape : forall
    parent left right,
  coqFormulaImpChildrenAtomicAdequacyInstanceTemplate parent left right =
  tfImp
    (coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate
      parent left right)
    (tfImp
      (coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
        parent left right)
      (coqFormulaImpChildrenAtomicAdequacyConclusionTemplate
        parent left right)).
Proof.
  intros parent left right.
  unfold coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate,
    coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate,
    coqFormulaImpChildrenAtomicAdequacyConclusionTemplate,
    coqFormulaImpChildrenAtomicAdequacyInstanceTemplate,
    templateUniversalOpenManyOrBot,
    codedFormulaImpChildrenAtomicAdequacyFormula,
    codedFormulaImpChildrenAtomicAdequacyBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_formulaImpChildrenAtomicAdequacy_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext parent left right,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
          parent left right)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    parent left right hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      codedFormulaImpChildrenAtomicAdequacyFormula
      [parent; left; right]
      (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
        parent left right)
      hbase PA_proves_codedFormulaImpChildrenAtomicAdequacyFormula
      (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate_open
        parent left right)).
Qed.

Theorem
    raw_codedPALocalProofOf_formulaImpChildrenAtomicAdequacy_instance_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix parent left right,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) proofRoot,
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
        (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
          parent left right)) proofRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    parent left right hprefix hbase.
  destruct
    (raw_codedPALocalProofOf_formulaImpChildrenAtomicAdequacy_instance_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      parent left right hbase)
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
      (coqFormulaImpChildrenAtomicAdequacyInstanceTemplate
        parent left right)) sourceRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      extendedWitnessList extendedContext hextended)
    hprefix hsource) as [proofRoot hproof].
  exists witnesses, proofRoot. split; assumption.
Qed.

(** Transport both premise proofs to the theorem compiler's chosen
    standard-axiom extension and perform the two represented [Imp-E] steps.
    Keeping this context kernel generic avoids repeating it in the Sigma and
    Pi implication leaves. *)
Theorem
    raw_codedPALocalProofOf_formulaImpChildrenAtomicAdequacy_of_roots_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix parent left right
      parentRoot shapeRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate
        parent left right)) parentRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
        parent left right)) shapeRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) resultRoot,
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
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyConclusionTemplate
          parent left right)) resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    parent left right parentRoot shapeRoot hprefix hbase hparent hshape.
  destruct
    (raw_codedPALocalProofOf_formulaImpChildrenAtomicAdequacy_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      parent left right hprefix hbase)
    as (witnesses & implicationRoot & hextended & himplication).
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
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate
          parent left right))
      parentRoot hbase hextended hincluded hparent)
    as [transportedParentRoot htransportedParent].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
          parent left right))
      shapeRoot hbase hextended hincluded hshape)
    as [transportedShapeRoot htransportedShape].
  rewrite coqFormulaImpChildrenAtomicAdequacyInstanceTemplate_imp2_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      (coqFormulaImpChildrenAtomicAdequacyParentPremiseTemplate
        parent left right))
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
          parent left right))
      (rawTemplateFormula translation
        (coqFormulaImpChildrenAtomicAdequacyConclusionTemplate
          parent left right)))
    implicationRoot transportedParentRoot
    himplication htransportedParent) as hafterParent.
  lazymatch type of hafterParent with
  | RawCodedPALocalProofOf _ _ _ ?afterParentRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawTemplateContextCodeOnTail translation extendedContext prefix)
        (rawTemplateFormula translation
          (coqFormulaImpChildrenAtomicAdequacyShapePremiseTemplate
            parent left right))
        (rawTemplateFormula translation
          (coqFormulaImpChildrenAtomicAdequacyConclusionTemplate
            parent left right))
        afterParentRoot transportedShapeRoot
        hafterParent htransportedShape) as hresult;
      lazymatch type of hresult with
      | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists witnesses, resultRoot;
          split; [exact hextended |];
          split; [exact hincluded | exact hresult]
      end
  end.
Qed.

End PABoundedRawCodedFormulaImpChildrenAtomicAdequacyProofCompilation.
