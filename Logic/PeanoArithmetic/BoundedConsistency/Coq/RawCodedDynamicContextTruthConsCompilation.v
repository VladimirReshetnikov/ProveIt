(**
  Proof-producing cons closure for native dynamic context truth.

  The public dynamic-context predicate hides one complete context traversal
  and requires the selected Sigma predicate at every live head-table row.
  Implication introduction needs the following structural operation inside
  PA, not merely as a metatheoretic semantic fact:

      C_Sigma(Gamma,a,s) -> Sigma(A,a,s) -> C_Sigma(A :: Gamma,a,s).

  This file first isolates the arithmetic part of that operation.  From an
  old traversal it constructs four beta-table witnesses for the cons
  traversal and classifies every live row of the new head table as either
  the newly adjoined head or an old live row.  The classification is an
  ordinary PA formula and is therefore compiled by raw-model completeness;
  no carrier-valued Sigma predicate is decoded by completeness.

  The second half uses that structural source in a uniform proof template.
  The Sigma leaf remains opaque throughout, so the resulting local proof is
  valid for the possibly nonstandard deeply closed predicate selected by the
  dynamic-truth construction.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedProofBinaryConstructors
  RawCodedAssignment
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateRepeatedUniversalElimination
  RawCodedTemplateNestedExistentialElimination
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateTernaryApplication
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicContextTruthDirectSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion
  RawCodedRestrictedPATemplateTernaryApplicationCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicContextTruthConsCompilation.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.
Import PABoundedRawCodedTemplateNestedExistentialElimination.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicContextTruthDirectSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
Import PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.

(** ------------------------------------------------------------------
    Semantic closure, used both as an audit and to justify the exact row
    classifier below. *)

Theorem raw_dynamicContextAllSigma_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (Sigma : M -> M -> M -> Prop)
    root head assignmentCode assignmentStep,
  RawDynamicContextAllSigma M Sigma
    root assignmentCode assignmentStep ->
  Sigma head assignmentCode assignmentStep ->
  RawDynamicContextAllSigma M Sigma
    (rawListNode M head root) assignmentCode assignmentStep.
Proof.
  intros M hPA Sigma root head assignmentCode assignmentStep
    (bound & tailCode & tailStep & headCode & headStep &
      htraversal & hall) hhead.
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists (raw_succ M bound), newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  intros index hindex formulaCode hlookup.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - apply (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep formulaCode
      hheadPrepend)) in hlookup.
    subst formulaCode. exact hhead.
  - assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
    { exact (raw_assignment_lt_self_succ M hPA predecessor). }
    assert (hpredBound : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound hpredSelf hlt).
      - rewrite <- heq. exact hpredSelf.
    }
    apply (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep
      (proj1 (proj2 (proj2 htraversal))) hheadPrepend
      predecessor hpredBound formulaCode)) in hlookup.
    exact (hall predecessor hpredBound formulaCode hlookup).
Qed.

(** The pure-arithmetic output needed by a uniform proof with an opaque
    pointwise predicate.  Every new head-table lookup is either equal to the
    adjoined head or already occurs at a live old row. *)
Definition RawContextListConsTruthTransfer (M : RawPAModel)
    (root head bound tailCode tailStep headCode headStep : M) : Prop :=
  RawContextListTraversal M root bound
      tailCode tailStep headCode headStep ->
  exists newTailCode newTailStep newHeadCode newHeadStep : M,
    RawContextListTraversal M (rawListNode M head root) (raw_succ M bound)
      newTailCode newTailStep newHeadCode newHeadStep /\
    forall index,
      rawLt M index (raw_succ M bound) ->
      forall formulaCode,
      RawCodedAssignmentLookup M
        newHeadCode newHeadStep index formulaCode ->
      head = formulaCode \/
      exists predecessor,
        rawLt M predecessor bound /\
        RawCodedAssignmentLookup M
          headCode headStep predecessor formulaCode.

Arguments RawContextListConsTruthTransfer
  M root head bound tailCode tailStep headCode headStep : clear implicits.

Theorem raw_contextListConsTruthTransfer : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root head bound tailCode tailStep headCode headStep,
  RawContextListConsTruthTransfer M
    root head bound tailCode tailStep headCode headStep.
Proof.
  intros M hPA root head bound tailCode tailStep headCode headStep
    htraversal.
  destruct (raw_contextListConsExtension_exists M hPA
    root head bound tailCode tailStep headCode headStep htraversal)
    as (newTailCode & newTailStep & newHeadCode & newHeadStep &
      _ & hheadPrepend & hnewTraversal).
  exists newTailCode, newTailStep, newHeadCode, newHeadStep.
  split; [exact hnewTraversal |].
  intros index hindex formulaCode hlookup.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - left.
    apply (proj1 (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep formulaCode
      hheadPrepend)) in hlookup.
    symmetry. exact hlookup.
  - right.
    assert (hpredSelf : rawLt M predecessor (raw_succ M predecessor)).
    { exact (raw_assignment_lt_self_succ M hPA predecessor). }
    assert (hpredBound : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound hpredSelf hlt).
      - rewrite <- heq. exact hpredSelf.
    }
    exists predecessor. split; [exact hpredBound |].
    apply (proj1 (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      headCode headStep head bound newHeadCode newHeadStep
      (proj1 (proj2 (proj2 htraversal))) hheadPrepend
      predecessor hpredBound formulaCode)) in hlookup.
    exact hlookup.
Qed.

(** ------------------------------------------------------------------
    A standard seven-parameter PA source for the structural transfer.

    The open variables are, from high to low,

      root, head, bound, tailCode, tailStep, headCode, headStep.

    Four existential binders then choose the new table pairs.  The two
    universal binders choose [index] and [formulaCode], and the final
    existential chooses an old predecessor row in the inherited case. *)

(** The inherited-row alternative is factored out to make all three shifts
    caused by its existential binder visible. *)
Definition contextListConsTruthOldRowTermAt
    (bound headCode headStep : term) : formula :=
  pEx
    (pAnd
      (Formula.ltTermAt (tVar 0) (liftTerm 7 bound))
      (codedAssignmentLookupTermAt
        (liftTerm 7 headCode) (liftTerm 7 headStep)
        (tVar 0) (tVar 1))).

(** This formula is placed after the four new-table witnesses have opened.
    Its two universal binders choose the new row and its formula value. *)
Definition contextListConsTruthRowsTermAt
    (head bound oldHeadCode oldHeadStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0)
        (tSucc (liftTerm 5 bound)))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (tVar 3) (tVar 2) (tVar 1) (tVar 0))
          (pOr
            (pEq (liftTerm 6 head) (tVar 0))
            (contextListConsTruthOldRowTermAt
              bound oldHeadCode oldHeadStep))))).

Definition contextListConsTruthTransferTermAt
    (root head bound tailCode tailStep headCode headStep : term) : formula :=
  pImp
    (contextListTraversalTermAt root bound
      tailCode tailStep headCode headStep)
    (pEx (pEx (pEx (pEx
      (pAnd
        (contextListTraversalTermAt
          (nodeTerm (liftTerm 4 head) (liftTerm 4 root))
          (tSucc (liftTerm 4 bound))
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (contextListConsTruthRowsTermAt
          head bound headCode headStep)))))).

Definition contextListConsTruthTransferFormula : formula :=
  contextListConsTruthTransferTermAt
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Definition contextListConsTruthTransferUniversalFormula : formula :=
  Formula.closeN 7 contextListConsTruthTransferFormula.

Lemma raw_dynamicContextCons_eval_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 input) =
  raw_term_eval M e input.
Proof.
  intros M a b c d e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 4) with (S (S (S (S index)))) by lia.
  reflexivity.
Qed.

Lemma raw_dynamicContextCons_eval_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 input) =
  raw_term_eval M e input.
Proof.
  intros M a b c d f e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 5) with (S (S (S (S (S index))))) by lia.
  reflexivity.
Qed.

Lemma raw_dynamicContextCons_eval_liftTerm_six : forall
    (M : RawPAModel) a b c d f g (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c
      (scons M d (scons M f (scons M g e))))))
    (liftTerm 6 input) =
  raw_term_eval M e input.
Proof.
  intros M a b c d f g e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 6) with (S (S (S (S (S (S index)))))) by lia.
  reflexivity.
Qed.

Lemma raw_dynamicContextCons_eval_liftTerm_seven : forall
    (M : RawPAModel) a b c d f g h (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c
      (scons M d (scons M f (scons M g (scons M h e)))))))
    (liftTerm 7 input) =
  raw_term_eval M e input.
Proof.
  intros M a b c d f g h e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 7) with (S (S (S (S (S (S (S index))))))) by lia.
  reflexivity.
Qed.

Lemma raw_dynamicContextCons_eval_succ_liftTerm_four : forall
    (M : RawPAModel) a b c d (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (tSucc (liftTerm 4 input)) =
  raw_succ M (raw_term_eval M e input).
Proof.
  intros M a b c d e input. cbn [raw_term_eval].
  now rewrite raw_dynamicContextCons_eval_liftTerm_four.
Qed.

Lemma raw_dynamicContextCons_eval_succ_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) input,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (tSucc (liftTerm 5 input)) =
  raw_succ M (raw_term_eval M e input).
Proof.
  intros M a b c d f e input. cbn [raw_term_eval].
  now rewrite raw_dynamicContextCons_eval_liftTerm_five.
Qed.

Lemma raw_sat_contextListConsTruthTransferTermAt_iff : forall
    (M : RawPAModel) e root head bound
      tailCode tailStep headCode headStep,
  raw_formula_sat M e
    (contextListConsTruthTransferTermAt
      root head bound tailCode tailStep headCode headStep) <->
  RawContextListConsTruthTransfer M
    (raw_term_eval M e root)
    (raw_term_eval M e head)
    (raw_term_eval M e bound)
    (raw_term_eval M e tailCode)
    (raw_term_eval M e tailStep)
    (raw_term_eval M e headCode)
    (raw_term_eval M e headStep).
Proof.
  intros M e root head bound tailCode tailStep headCode headStep.
  unfold contextListConsTruthTransferTermAt,
    contextListConsTruthRowsTermAt,
    contextListConsTruthOldRowTermAt,
    RawContextListConsTruthTransfer.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_eval_nodeTerm.
  repeat setoid_rewrite raw_dynamicContextCons_eval_succ_liftTerm_four.
  repeat setoid_rewrite raw_dynamicContextCons_eval_succ_liftTerm_five.
  repeat setoid_rewrite raw_dynamicContextCons_eval_liftTerm_four.
  repeat setoid_rewrite raw_dynamicContextCons_eval_liftTerm_five.
  repeat setoid_rewrite raw_dynamicContextCons_eval_liftTerm_six.
  repeat setoid_rewrite raw_dynamicContextCons_eval_liftTerm_seven.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Theorem contextListConsTruthTransferFormula_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e contextListConsTruthTransferFormula.
Proof.
  intros M hPA e.
  unfold contextListConsTruthTransferFormula.
  apply (proj2 (raw_sat_contextListConsTruthTransferTermAt_iff
    M e (tVar 6) (tVar 5) (tVar 4) (tVar 3)
      (tVar 2) (tVar 1) (tVar 0))).
  cbn [raw_term_eval].
  apply raw_contextListConsTruthTransfer. exact hPA.
Qed.

Theorem PA_proves_contextListConsTruthTransferFormula :
  Formula.BProv Formula.Ax_s [] contextListConsTruthTransferFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA contextListConsTruthTransferFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (contextListConsTruthTransferFormula_raw_valid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] contextListConsTruthTransferFormula
    (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Theorem PA_proves_contextListConsTruthTransferUniversalFormula :
  Formula.BProv Formula.Ax_s []
    contextListConsTruthTransferUniversalFormula.
Proof.
  unfold contextListConsTruthTransferUniversalFormula.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - exact PA_proves_contextListConsTruthTransferFormula.
Qed.

(** ------------------------------------------------------------------
    Exact native templates at the implication-introduction witness depth.

    The endpoint witnesses put [Gamma,A,a,s] at slots [#7,#6,#9,#8].
    Context truth is exposed through its transparent five-existential
    skeleton.  The head Sigma leaf stays opaque and is therefore never
    submitted to raw-model completeness. *)

Definition coqDynamicContextConsStructuralSourceTemplate : TemplateFormula :=
  embedPAFormula contextListConsTruthTransferUniversalFormula.

Definition coqDynamicContextConsOldTruthTemplate : TemplateFormula :=
  coqRestrictedPATemplateTernaryApplication
    coqRestrictedPADynamicContextPredicateTemplate
    (ttVar 8) (ttVar 9) (ttVar 7).

Definition coqDynamicContextConsHeadSigmaTemplate : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [ttZero; ttZero; ttVar 6; ttVar 9; ttVar 8].

Definition coqDynamicContextConsNewContextTerm : TemplateTerm :=
  embedPATerm (nodeTerm (tVar 6) (tVar 7)).

Definition coqDynamicContextConsNewTruthTemplate : TemplateFormula :=
  coqRestrictedPATemplateTernaryApplication
    coqRestrictedPADynamicContextPredicateTemplate
    (ttVar 8) (ttVar 9) coqDynamicContextConsNewContextTerm.

Definition coqDynamicContextConsNativeLawTemplate : TemplateFormula :=
  tfImp coqDynamicContextConsOldTruthTemplate
    (tfImp coqDynamicContextConsHeadSigmaTemplate
      coqDynamicContextConsNewTruthTemplate).

(** Public Imp-I spelling of the same law.  The first premise is precisely
    the recursive child's witnessed-context truth, while the second premise
    is the antecedent truth already exposed by the Imp-I endpoint.  Keeping
    this definition separate from the transparent native law makes the final
    carrier equality an explicit, auditable interface boundary. *)
Definition coqRestrictedPADirectImpIntroductionNewContextTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     coqDynamicContextConsNewContextTerm;
     ttVar 9; ttVar 8].

Definition coqRestrictedPADirectImpIntroductionContextConsLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (tfImp coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate
      coqRestrictedPADirectImpIntroductionNewContextTruthTemplate).

Definition RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionContextConsLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot
  M hPA inputs tail : clear implicits.

(** Total projections are followed by kernel-computed shape lemmas.  This
    keeps later proof objects readable without trusting an informal account
    of nine nested de Bruijn shifts. *)
Definition coqDynamicContextConsOldBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsOldTruthTemplate with
  | tfEx (tfEx (tfEx (tfEx (tfEx body)))) => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldTraversalTemplate : TemplateFormula :=
  match coqDynamicContextConsOldBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldPointwiseTemplate : TemplateFormula :=
  match coqDynamicContextConsOldBodyTemplate with
  | tfAnd _ pointwise => pointwise
  | _ => tfBot
  end.

Lemma coqDynamicContextConsOldTruth_shape :
  coqDynamicContextConsOldTruthTemplate =
  rawCoqTemplateExN 5 coqDynamicContextConsOldBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldBody_shape :
  coqDynamicContextConsOldBodyTemplate =
  tfAnd coqDynamicContextConsOldTraversalTemplate
    coqDynamicContextConsOldPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

(** At the old five-witness depth the original endpoint terms have shifted
    by five, while the traversal tuple occupies slots [#4..#0]. *)
Definition coqDynamicContextConsStructuralReplacements :
    list TemplateTerm :=
  [ttVar 12; ttVar 11; ttVar 4; ttVar 3;
   ttVar 2; ttVar 1; ttVar 0].

Definition coqDynamicContextConsStructuralInstanceTemplate :
    TemplateFormula :=
  rawCoqTemplateAllEListResult
    coqDynamicContextConsStructuralReplacements
    coqDynamicContextConsStructuralSourceTemplate.

Definition coqDynamicContextConsStructuralAntecedentTemplate :
    TemplateFormula :=
  match coqDynamicContextConsStructuralInstanceTemplate with
  | tfImp antecedent _ => antecedent
  | _ => tfBot
  end.

Definition coqDynamicContextConsStructuralResultTemplate :
    TemplateFormula :=
  match coqDynamicContextConsStructuralInstanceTemplate with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqDynamicContextConsStructuralBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsStructuralResultTemplate with
  | tfEx (tfEx (tfEx (tfEx body))) => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsNewTraversalTemplate : TemplateFormula :=
  match coqDynamicContextConsStructuralBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqDynamicContextConsRowsTemplate : TemplateFormula :=
  match coqDynamicContextConsStructuralBodyTemplate with
  | tfAnd _ rows => rows
  | _ => tfBot
  end.

Lemma coqDynamicContextConsStructuralSource_ready :
  RawCoqTemplateAllEListReady
    coqDynamicContextConsStructuralReplacements
    coqDynamicContextConsStructuralSourceTemplate.
Proof. vm_compute. exact I. Qed.

Lemma coqDynamicContextConsStructuralInstance_shape :
  coqDynamicContextConsStructuralInstanceTemplate =
  tfImp coqDynamicContextConsStructuralAntecedentTemplate
    coqDynamicContextConsStructuralResultTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsStructuralResult_shape :
  coqDynamicContextConsStructuralResultTemplate =
  rawCoqTemplateExN 4 coqDynamicContextConsStructuralBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsStructuralBody_shape :
  coqDynamicContextConsStructuralBodyTemplate =
  tfAnd coqDynamicContextConsNewTraversalTemplate
    coqDynamicContextConsRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsStructuralAntecedent_agreement :
  coqDynamicContextConsStructuralAntecedentTemplate =
  coqDynamicContextConsOldTraversalTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Reintroducing the target context witnesses at the final nine-witness
    depth uses the successor old bound and the four new tables. *)
Definition coqDynamicContextConsFinalNewTruthTemplate : TemplateFormula :=
  rawCoqTemplateRenameN 4
    (rawCoqTemplateRenameN 5 coqDynamicContextConsNewTruthTemplate).

Definition coqDynamicContextConsNewTruthWitnesses : list TemplateTerm :=
  [ttSucc (ttVar 8); ttVar 3; ttVar 2; ttVar 1; ttVar 0].

Fixpoint coqDynamicContextConsOpenExistentials
    (witnesses : list TemplateTerm) (target : TemplateFormula)
    : TemplateFormula :=
  match witnesses with
  | [] => target
  | witness :: remaining =>
      match target with
      | tfEx body =>
          coqDynamicContextConsOpenExistentials remaining
            (templateFormulaOpen witness body)
      | _ => target
      end
  end.

Fixpoint coqDynamicContextConsIntroduceExistentials
    (context : TemplateContext) (witnesses : list TemplateTerm)
    (target : TemplateFormula) (sourceRoot : TemplateRawProof)
    : TemplateRawProof :=
  match witnesses with
  | [] => sourceRoot
  | witness :: remaining =>
      match target with
      | tfEx body =>
          trpExI context body witness
            (coqDynamicContextConsIntroduceExistentials
              context remaining (templateFormulaOpen witness body)
              sourceRoot)
      | _ => sourceRoot
      end
  end.

Theorem coqDynamicContextConsIntroduceExistentials_derives : forall
    context witnesses target sourceRoot,
  TemplateRawDerives context
    (coqDynamicContextConsOpenExistentials witnesses target) sourceRoot ->
  TemplateRawDerives context target
    (coqDynamicContextConsIntroduceExistentials
      context witnesses target sourceRoot).
Proof.
  intros context witnesses.
  revert context.
  induction witnesses as [|witness remaining ih];
    intros context target sourceRoot hsource.
  - exact hsource.
  - destruct target;
      cbn [coqDynamicContextConsOpenExistentials
        coqDynamicContextConsIntroduceExistentials] in *;
      try exact hsource.
    pose proof (ih context _ sourceRoot hsource) as hchild.
    destruct hchild as [hvalid [hcontext hconclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; try assumption; reflexivity.
Qed.

Definition coqDynamicContextConsFinalNewBodyTemplate : TemplateFormula :=
  coqDynamicContextConsOpenExistentials
    coqDynamicContextConsNewTruthWitnesses
    coqDynamicContextConsFinalNewTruthTemplate.

Definition coqDynamicContextConsFinalNewTraversalTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalNewBodyTemplate with
  | tfAnd traversal _ => traversal
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalNewPointwiseTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalNewBodyTemplate with
  | tfAnd _ pointwise => pointwise
  | _ => tfBot
  end.

Lemma coqDynamicContextConsFinalNewBody_shape :
  coqDynamicContextConsFinalNewBodyTemplate =
  tfAnd coqDynamicContextConsFinalNewTraversalTemplate
    coqDynamicContextConsFinalNewPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsFinalTraversal_agreement :
  coqDynamicContextConsFinalNewTraversalTemplate =
  coqDynamicContextConsNewTraversalTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Pointwise target at the final table-witness depth. *)
Definition coqDynamicContextConsFinalIndexBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalNewPointwiseTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalLiveTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalIndexBodyTemplate with
  | tfImp live _ => live
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalAfterLiveTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalIndexBodyTemplate with
  | tfImp _ afterLive => afterLive
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalFormulaBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalAfterLiveTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalLookupTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalFormulaBodyTemplate with
  | tfImp lookup _ => lookup
  | _ => tfBot
  end.

Definition coqDynamicContextConsFinalSigmaTemplate : TemplateFormula :=
  match coqDynamicContextConsFinalFormulaBodyTemplate with
  | tfImp _ sigma => sigma
  | _ => tfBot
  end.

Lemma coqDynamicContextConsFinalPointwise_shape :
  coqDynamicContextConsFinalNewPointwiseTemplate =
  tfAll coqDynamicContextConsFinalIndexBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsFinalIndexBody_shape :
  coqDynamicContextConsFinalIndexBodyTemplate =
  tfImp coqDynamicContextConsFinalLiveTemplate
    coqDynamicContextConsFinalAfterLiveTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsFinalAfterLive_shape :
  coqDynamicContextConsFinalAfterLiveTemplate =
  tfAll coqDynamicContextConsFinalFormulaBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsFinalFormulaBody_shape :
  coqDynamicContextConsFinalFormulaBodyTemplate =
  tfImp coqDynamicContextConsFinalLookupTemplate
    coqDynamicContextConsFinalSigmaTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Instantiate the structural row classifier at the two eigenvariables
    introduced while proving target pointwise truth. *)
Definition coqDynamicContextConsDeepRowsTemplate : TemplateFormula :=
  rawCoqTemplateRenameN 2 coqDynamicContextConsRowsTemplate.

Definition coqDynamicContextConsDeepRowsIndexBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsDeepRowsTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsRowsAtIndexTemplate : TemplateFormula :=
  templateFormulaOpen (ttVar 1)
    coqDynamicContextConsDeepRowsIndexBodyTemplate.

Definition coqDynamicContextConsRowsAtIndexAfterLiveTemplate
    : TemplateFormula :=
  match coqDynamicContextConsRowsAtIndexTemplate with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqDynamicContextConsRowsFormulaBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsRowsAtIndexAfterLiveTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsRowsAtFormulaTemplate : TemplateFormula :=
  templateFormulaOpen (ttVar 0)
    coqDynamicContextConsRowsFormulaBodyTemplate.

Definition coqDynamicContextConsRowAlternativeTemplate : TemplateFormula :=
  match coqDynamicContextConsRowsAtFormulaTemplate with
  | tfImp _ alternative => alternative
  | _ => tfBot
  end.

Definition coqDynamicContextConsHeadEqualityTemplate : TemplateFormula :=
  match coqDynamicContextConsRowAlternativeTemplate with
  | tfOr equality _ => equality
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldRowExistsTemplate : TemplateFormula :=
  match coqDynamicContextConsRowAlternativeTemplate with
  | tfOr _ oldRow => oldRow
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldRowBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsOldRowExistsTemplate with
  | tfEx body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldRowLiveTemplate : TemplateFormula :=
  match coqDynamicContextConsOldRowBodyTemplate with
  | tfAnd live _ => live
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldRowLookupTemplate : TemplateFormula :=
  match coqDynamicContextConsOldRowBodyTemplate with
  | tfAnd _ lookup => lookup
  | _ => tfBot
  end.

Lemma coqDynamicContextConsDeepRows_shape :
  coqDynamicContextConsDeepRowsTemplate =
  tfAll coqDynamicContextConsDeepRowsIndexBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsRowsAtIndex_shape :
  coqDynamicContextConsRowsAtIndexTemplate =
  tfImp (templateFormulaRename S coqDynamicContextConsFinalLiveTemplate)
    coqDynamicContextConsRowsAtIndexAfterLiveTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsRowsAfterLive_shape :
  coqDynamicContextConsRowsAtIndexAfterLiveTemplate =
  tfAll coqDynamicContextConsRowsFormulaBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsRowsAtFormula_shape :
  coqDynamicContextConsRowsAtFormulaTemplate =
  tfImp coqDynamicContextConsFinalLookupTemplate
    coqDynamicContextConsRowAlternativeTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsRowAlternative_shape :
  coqDynamicContextConsRowAlternativeTemplate =
  tfOr coqDynamicContextConsHeadEqualityTemplate
    coqDynamicContextConsOldRowExistsTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldRowExists_shape :
  coqDynamicContextConsOldRowExistsTemplate =
  tfEx coqDynamicContextConsOldRowBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldRowBody_shape :
  coqDynamicContextConsOldRowBodyTemplate =
  tfAnd coqDynamicContextConsOldRowLiveTemplate
    coqDynamicContextConsOldRowLookupTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Equality transport in the head alternative. *)
Definition coqDynamicContextConsHeadEqualityLeftTerm : TemplateTerm :=
  match coqDynamicContextConsHeadEqualityTemplate with
  | tfEq lhs _ => lhs
  | _ => ttZero
  end.

Definition coqDynamicContextConsHeadEqualityRightTerm : TemplateTerm :=
  match coqDynamicContextConsHeadEqualityTemplate with
  | tfEq _ rhs => rhs
  | _ => ttZero
  end.

Definition coqDynamicContextConsSigmaMotiveTemplate : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [ttZero; ttZero; ttVar 0; ttVar 21; ttVar 20].

Lemma coqDynamicContextConsHeadEquality_shape :
  coqDynamicContextConsHeadEqualityTemplate =
  tfEq coqDynamicContextConsHeadEqualityLeftTerm
    coqDynamicContextConsHeadEqualityRightTerm.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsSigmaMotive_head :
  templateFormulaOpen coqDynamicContextConsHeadEqualityLeftTerm
    coqDynamicContextConsSigmaMotiveTemplate =
  rawCoqTemplateRenameN 2
    (rawCoqTemplateRenameN 4
      (rawCoqTemplateRenameN 5
        coqDynamicContextConsHeadSigmaTemplate)).
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsSigmaMotive_formula :
  templateFormulaOpen coqDynamicContextConsHeadEqualityRightTerm
    coqDynamicContextConsSigmaMotiveTemplate =
  coqDynamicContextConsFinalSigmaTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Old pointwise truth after the four structural witnesses, two target
    eigenvariables, and the inherited-row predecessor witness. *)
Definition coqDynamicContextConsDeepOldPointwiseTemplate : TemplateFormula :=
  templateFormulaRename S
    (rawCoqTemplateRenameN 2
      (rawCoqTemplateRenameN 4
        coqDynamicContextConsOldPointwiseTemplate)).

Definition coqDynamicContextConsDeepOldIndexBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsDeepOldPointwiseTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldPointwiseAtIndexTemplate : TemplateFormula :=
  templateFormulaOpen (ttVar 0)
    coqDynamicContextConsDeepOldIndexBodyTemplate.

Definition coqDynamicContextConsOldPointwiseAfterLiveTemplate
    : TemplateFormula :=
  match coqDynamicContextConsOldPointwiseAtIndexTemplate with
  | tfImp _ result => result
  | _ => tfBot
  end.

Definition coqDynamicContextConsDeepOldFormulaBodyTemplate : TemplateFormula :=
  match coqDynamicContextConsOldPointwiseAfterLiveTemplate with
  | tfAll body => body
  | _ => tfBot
  end.

Definition coqDynamicContextConsOldPointwiseAtFormulaTemplate
    : TemplateFormula :=
  templateFormulaOpen (ttVar 1)
    coqDynamicContextConsDeepOldFormulaBodyTemplate.

Lemma coqDynamicContextConsDeepOldPointwise_shape :
  coqDynamicContextConsDeepOldPointwiseTemplate =
  tfAll coqDynamicContextConsDeepOldIndexBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldPointwiseAtIndex_shape :
  coqDynamicContextConsOldPointwiseAtIndexTemplate =
  tfImp coqDynamicContextConsOldRowLiveTemplate
    coqDynamicContextConsOldPointwiseAfterLiveTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldPointwiseAfterLive_shape :
  coqDynamicContextConsOldPointwiseAfterLiveTemplate =
  tfAll coqDynamicContextConsDeepOldFormulaBodyTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextConsOldPointwiseAtFormula_shape :
  coqDynamicContextConsOldPointwiseAtFormulaTemplate =
  tfImp coqDynamicContextConsOldRowLookupTemplate
    (templateFormulaRename S coqDynamicContextConsFinalSigmaTemplate).
Proof. vm_compute. reflexivity. Qed.

(** ------------------------------------------------------------------
    Declarative proof-tree assembly. *)

Lemma coqDynamicContextCons_templateRawDerives_impE : forall
    context antecedent consequent implicationRoot antecedentRoot,
  TemplateRawDerives context (tfImp antecedent consequent)
    implicationRoot ->
  TemplateRawDerives context antecedent antecedentRoot ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent
      implicationRoot antecedentRoot).
Proof.
  intros context antecedent consequent implicationRoot antecedentRoot
    [hiValid [hiContext hiConclusion]]
    [haValid [haContext haConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqDynamicContextCons_templateRawDerives_andI : forall
    context left right leftRoot rightRoot,
  TemplateRawDerives context left leftRoot ->
  TemplateRawDerives context right rightRoot ->
  TemplateRawDerives context (tfAnd left right)
    (trpAndI context left right leftRoot rightRoot).
Proof.
  intros context left right leftRoot rightRoot
    [hlValid [hlContext hlConclusion]]
    [hrValid [hrContext hrConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqDynamicContextCons_templateRawDerives_allI : forall
    context body child,
  TemplateRawDerives (templateContextShift context) body child ->
  TemplateRawDerives context (tfAll body)
    (trpAllI context body child).
Proof.
  intros context body child [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqDynamicContextCons_templateRawDerives_orE : forall
    context left right conclusion disjunctionRoot leftRoot rightRoot,
  TemplateRawDerives context (tfOr left right) disjunctionRoot ->
  TemplateRawDerives (left :: context) conclusion leftRoot ->
  TemplateRawDerives (right :: context) conclusion rightRoot ->
  TemplateRawDerives context conclusion
    (trpOrE context left right conclusion
      disjunctionRoot leftRoot rightRoot).
Proof.
  intros context left right conclusion disjunctionRoot leftRoot rightRoot
    [hdValid [hdContext hdConclusion]]
    [hlValid [hlContext hlConclusion]]
    [hrValid [hrContext hrConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Definition coqDynamicContextConsSourceContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsStructuralSourceTemplate :: tail.

Definition coqDynamicContextConsAfterOldIntroduction
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsOldTruthTemplate ::
    coqDynamicContextConsSourceContext tail.

Definition coqDynamicContextConsAfterHeadIntroduction
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsHeadSigmaTemplate ::
    coqDynamicContextConsAfterOldIntroduction tail.

Definition coqDynamicContextConsOldWitnessContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateNestedExContext 4
    coqDynamicContextConsOldBodyTemplate
    (templateContextShift
      (coqDynamicContextConsAfterHeadIntroduction tail)).

Definition coqDynamicContextConsStructuralWitnessContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqTemplateNestedExContext 3
    coqDynamicContextConsStructuralBodyTemplate
    (templateContextShift
      (coqDynamicContextConsOldWitnessContext tail)).

Definition coqDynamicContextConsIndexContext
    (tail : TemplateContext) : TemplateContext :=
  templateContextShift
    (coqDynamicContextConsStructuralWitnessContext tail).

Definition coqDynamicContextConsLiveContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsFinalLiveTemplate ::
    coqDynamicContextConsIndexContext tail.

Definition coqDynamicContextConsFormulaContext
    (tail : TemplateContext) : TemplateContext :=
  templateContextShift (coqDynamicContextConsLiveContext tail).

Definition coqDynamicContextConsLookupContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsFinalLookupTemplate ::
    coqDynamicContextConsFormulaContext tail.

Definition coqDynamicContextConsHeadBranchContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsHeadEqualityTemplate ::
    coqDynamicContextConsLookupContext tail.

Definition coqDynamicContextConsOldBranchContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsOldRowExistsTemplate ::
    coqDynamicContextConsLookupContext tail.

Definition coqDynamicContextConsOldRowWitnessContext
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicContextConsOldRowBodyTemplate ::
    templateContextShift (coqDynamicContextConsOldBranchContext tail).

Arguments coqDynamicContextConsSourceContext tail : clear implicits.
Arguments coqDynamicContextConsAfterOldIntroduction tail : clear implicits.
Arguments coqDynamicContextConsAfterHeadIntroduction tail : clear implicits.
Arguments coqDynamicContextConsOldWitnessContext tail : clear implicits.
Arguments coqDynamicContextConsStructuralWitnessContext tail : clear implicits.
Arguments coqDynamicContextConsIndexContext tail : clear implicits.
Arguments coqDynamicContextConsLiveContext tail : clear implicits.
Arguments coqDynamicContextConsFormulaContext tail : clear implicits.
Arguments coqDynamicContextConsLookupContext tail : clear implicits.
Arguments coqDynamicContextConsHeadBranchContext tail : clear implicits.
Arguments coqDynamicContextConsOldBranchContext tail : clear implicits.
Arguments coqDynamicContextConsOldRowWitnessContext tail : clear implicits.

Lemma coqDynamicContextCons_old_body_in : forall tail,
  In coqDynamicContextConsOldBodyTemplate
    (coqDynamicContextConsOldWitnessContext tail).
Proof.
  intro tail. unfold coqDynamicContextConsOldWitnessContext.
  cbn [rawCoqTemplateNestedExContext]. left. reflexivity.
Qed.

Lemma coqDynamicContextCons_source_in_old_witness_context : forall tail,
  In coqDynamicContextConsStructuralSourceTemplate
    (coqDynamicContextConsOldWitnessContext tail).
Proof.
  intro tail.
  replace coqDynamicContextConsStructuralSourceTemplate with
    (rawCoqTemplateRenameN 4
      (templateFormulaRename S
        coqDynamicContextConsStructuralSourceTemplate))
    by (vm_compute; reflexivity).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsAfterHeadIntroduction,
    coqDynamicContextConsAfterOldIntroduction,
    coqDynamicContextConsSourceContext.
  right. right. left. reflexivity.
Qed.

Definition coqDynamicContextConsOldBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsOldBodyTemplate.

Definition coqDynamicContextConsOldTraversalRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE1 (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsOldTraversalTemplate
    coqDynamicContextConsOldPointwiseTemplate
    (coqDynamicContextConsOldBodyRoot tail).

Definition coqDynamicContextConsStructuralSourceRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsStructuralSourceTemplate.

Definition coqDynamicContextConsStructuralInstanceRoot
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateAllEListRoot
    (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsStructuralReplacements
    coqDynamicContextConsStructuralSourceTemplate
    (coqDynamicContextConsStructuralSourceRoot tail).

Definition coqDynamicContextConsStructuralResultRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpE (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsStructuralAntecedentTemplate
    coqDynamicContextConsStructuralResultTemplate
    (coqDynamicContextConsStructuralInstanceRoot tail)
    (coqDynamicContextConsOldTraversalRoot tail).

Theorem coqDynamicContextConsStructuralResultRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsOldWitnessContext tail)
    coqDynamicContextConsStructuralResultTemplate
    (coqDynamicContextConsStructuralResultRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsStructuralResultRoot.
  apply coqDynamicContextCons_templateRawDerives_impE.
  - rewrite <- coqDynamicContextConsStructuralInstance_shape.
    unfold coqDynamicContextConsStructuralInstanceRoot.
    apply rawCoqTemplateAllEListRoot_derives.
    + exact coqDynamicContextConsStructuralSource_ready.
    + apply templateRawDerives_assumption.
      apply coqDynamicContextCons_source_in_old_witness_context.
  - rewrite coqDynamicContextConsStructuralAntecedent_agreement.
    unfold coqDynamicContextConsOldTraversalRoot.
    apply coqRestrictedPADirect_templateRawDerives_andE1.
    rewrite <- coqDynamicContextConsOldBody_shape.
    apply templateRawDerives_assumption.
    apply coqDynamicContextCons_old_body_in.
Qed.

Definition coqDynamicContextConsLookupStructuralBodyTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 2
    coqDynamicContextConsStructuralBodyTemplate.

Definition coqDynamicContextConsLookupNewTraversalTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 2
    coqDynamicContextConsNewTraversalTemplate.

Lemma coqDynamicContextConsLookupStructuralBody_shape :
  coqDynamicContextConsLookupStructuralBodyTemplate =
  tfAnd coqDynamicContextConsLookupNewTraversalTemplate
    coqDynamicContextConsDeepRowsTemplate.
Proof. vm_compute. reflexivity. Qed.

Definition coqDynamicContextConsDeepHeadSigmaTemplate : TemplateFormula :=
  rawCoqTemplateRenameN 2
    (rawCoqTemplateRenameN 4
      (rawCoqTemplateRenameN 5
        coqDynamicContextConsHeadSigmaTemplate)).

Definition coqDynamicContextConsDeepOldBodyTemplate : TemplateFormula :=
  templateFormulaRename S
    (rawCoqTemplateRenameN 2
      (rawCoqTemplateRenameN 4
        coqDynamicContextConsOldBodyTemplate)).

Definition coqDynamicContextConsDeepOldTraversalTemplate : TemplateFormula :=
  templateFormulaRename S
    (rawCoqTemplateRenameN 2
      (rawCoqTemplateRenameN 4
        coqDynamicContextConsOldTraversalTemplate)).

Lemma coqDynamicContextConsDeepOldBody_shape :
  coqDynamicContextConsDeepOldBodyTemplate =
  tfAnd coqDynamicContextConsDeepOldTraversalTemplate
    coqDynamicContextConsDeepOldPointwiseTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicContextCons_structural_body_in : forall tail,
  In coqDynamicContextConsStructuralBodyTemplate
    (coqDynamicContextConsStructuralWitnessContext tail).
Proof.
  intro tail. unfold coqDynamicContextConsStructuralWitnessContext.
  cbn [rawCoqTemplateNestedExContext]. left. reflexivity.
Qed.

Lemma coqDynamicContextCons_lookup_structural_body_in : forall tail,
  In coqDynamicContextConsLookupStructuralBodyTemplate
    (coqDynamicContextConsLookupContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsLookupStructuralBodyTemplate.
  cbn [rawCoqTemplateRenameN].
  unfold coqDynamicContextConsLookupContext.
  right.
  unfold coqDynamicContextConsFormulaContext,
    templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsLiveContext.
  right.
  unfold coqDynamicContextConsIndexContext,
    templateContextShift, templateContextRename.
  apply in_map.
  exact (coqDynamicContextCons_structural_body_in tail).
Qed.

Lemma coqDynamicContextCons_head_sigma_in_old_witness : forall tail,
  In (rawCoqTemplateRenameN 5
      coqDynamicContextConsHeadSigmaTemplate)
    (coqDynamicContextConsOldWitnessContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsOldWitnessContext.
  change (In
    (rawCoqTemplateRenameN 4
      (templateFormulaRename S
        coqDynamicContextConsHeadSigmaTemplate))
    (rawCoqTemplateNestedExContext 4
      coqDynamicContextConsOldBodyTemplate
      (templateContextShift
        (coqDynamicContextConsAfterHeadIntroduction tail)))).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsAfterHeadIntroduction.
  left. reflexivity.
Qed.

Lemma coqDynamicContextCons_head_sigma_in_structural_witness : forall tail,
  In (rawCoqTemplateRenameN 4
      (rawCoqTemplateRenameN 5
        coqDynamicContextConsHeadSigmaTemplate))
    (coqDynamicContextConsStructuralWitnessContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsStructuralWitnessContext.
  change (In
    (rawCoqTemplateRenameN 3
      (templateFormulaRename S
        (rawCoqTemplateRenameN 5
          coqDynamicContextConsHeadSigmaTemplate)))
    (rawCoqTemplateNestedExContext 3
      coqDynamicContextConsStructuralBodyTemplate
      (templateContextShift
        (coqDynamicContextConsOldWitnessContext tail)))).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  apply coqDynamicContextCons_head_sigma_in_old_witness.
Qed.

Lemma coqDynamicContextCons_head_sigma_in_head_branch : forall tail,
  In coqDynamicContextConsDeepHeadSigmaTemplate
    (coqDynamicContextConsHeadBranchContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsDeepHeadSigmaTemplate.
  cbn [rawCoqTemplateRenameN].
  unfold coqDynamicContextConsHeadBranchContext,
    coqDynamicContextConsLookupContext.
  right. right.
  unfold coqDynamicContextConsFormulaContext,
    templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsLiveContext.
  right.
  unfold coqDynamicContextConsIndexContext,
    templateContextShift, templateContextRename.
  apply in_map.
  apply coqDynamicContextCons_head_sigma_in_structural_witness.
Qed.

Lemma coqDynamicContextCons_old_body_in_structural_witness : forall tail,
  In (rawCoqTemplateRenameN 4 coqDynamicContextConsOldBodyTemplate)
    (coqDynamicContextConsStructuralWitnessContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsStructuralWitnessContext.
  change (In
    (rawCoqTemplateRenameN 3
      (templateFormulaRename S coqDynamicContextConsOldBodyTemplate))
    (rawCoqTemplateNestedExContext 3
      coqDynamicContextConsStructuralBodyTemplate
      (templateContextShift
        (coqDynamicContextConsOldWitnessContext tail)))).
  apply raw_coqTemplateNestedExContext_inherited.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  apply coqDynamicContextCons_old_body_in.
Qed.

Lemma coqDynamicContextCons_deep_old_body_in : forall tail,
  In coqDynamicContextConsDeepOldBodyTemplate
    (coqDynamicContextConsOldRowWitnessContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsDeepOldBodyTemplate.
  cbn [rawCoqTemplateRenameN].
  unfold coqDynamicContextConsOldRowWitnessContext.
  right.
  unfold templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsOldBranchContext.
  right.
  unfold coqDynamicContextConsLookupContext.
  right.
  unfold coqDynamicContextConsFormulaContext,
    templateContextShift, templateContextRename.
  apply in_map.
  unfold coqDynamicContextConsLiveContext.
  right.
  unfold coqDynamicContextConsIndexContext,
    templateContextShift, templateContextRename.
  apply in_map.
  apply coqDynamicContextCons_old_body_in_structural_witness.
Qed.

(** Row classification in the final lookup context. *)
Definition coqDynamicContextConsLookupStructuralBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsLookupStructuralBodyTemplate.

Definition coqDynamicContextConsDeepRowsRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE2 (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsLookupNewTraversalTemplate
    coqDynamicContextConsDeepRowsTemplate
    (coqDynamicContextConsLookupStructuralBodyRoot tail).

Definition coqDynamicContextConsRowsAtIndexRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllE (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsDeepRowsIndexBodyTemplate (ttVar 1)
    (coqDynamicContextConsDeepRowsRoot tail).

Definition coqDynamicContextConsShiftedLiveRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsLookupContext tail)
    (templateFormulaRename S coqDynamicContextConsFinalLiveTemplate).

Definition coqDynamicContextConsRowsAfterLiveRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpE (coqDynamicContextConsLookupContext tail)
    (templateFormulaRename S coqDynamicContextConsFinalLiveTemplate)
    coqDynamicContextConsRowsAtIndexAfterLiveTemplate
    (coqDynamicContextConsRowsAtIndexRoot tail)
    (coqDynamicContextConsShiftedLiveRoot tail).

Definition coqDynamicContextConsRowsAtFormulaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllE (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsRowsFormulaBodyTemplate (ttVar 0)
    (coqDynamicContextConsRowsAfterLiveRoot tail).

Definition coqDynamicContextConsLookupRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsFinalLookupTemplate.

Definition coqDynamicContextConsRowAlternativeRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpE (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsFinalLookupTemplate
    coqDynamicContextConsRowAlternativeTemplate
    (coqDynamicContextConsRowsAtFormulaRoot tail)
    (coqDynamicContextConsLookupRoot tail).

Lemma coqDynamicContextCons_shifted_live_in_lookup : forall tail,
  In (templateFormulaRename S
      coqDynamicContextConsFinalLiveTemplate)
    (coqDynamicContextConsLookupContext tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsLookupContext.
  right.
  unfold coqDynamicContextConsFormulaContext,
    templateContextShift, templateContextRename,
    coqDynamicContextConsLiveContext.
  apply in_map. left. reflexivity.
Qed.

Theorem coqDynamicContextConsRowAlternativeRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsRowAlternativeTemplate
    (coqDynamicContextConsRowAlternativeRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsRowAlternativeRoot.
  apply coqDynamicContextCons_templateRawDerives_impE.
  - rewrite <- coqDynamicContextConsRowsAtFormula_shape.
    unfold coqDynamicContextConsRowsAtFormulaRoot.
    apply templateRawDerives_allE.
    rewrite <- coqDynamicContextConsRowsAfterLive_shape.
    unfold coqDynamicContextConsRowsAfterLiveRoot.
    apply coqDynamicContextCons_templateRawDerives_impE.
    + rewrite <- coqDynamicContextConsRowsAtIndex_shape.
      unfold coqDynamicContextConsRowsAtIndexRoot.
      apply templateRawDerives_allE.
      rewrite <- coqDynamicContextConsDeepRows_shape.
      unfold coqDynamicContextConsDeepRowsRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      rewrite <- coqDynamicContextConsLookupStructuralBody_shape.
      apply templateRawDerives_assumption.
      apply coqDynamicContextCons_lookup_structural_body_in.
    + apply templateRawDerives_assumption.
      apply coqDynamicContextCons_shifted_live_in_lookup.
  - apply templateRawDerives_assumption. left. reflexivity.
Qed.

(** The newly adjoined head branch is one equality substitution through the
    opaque Sigma leaf.  Template equality elimination is admissible for
    opaque applications because the direct selector supplies genuine
    opening traces. *)
Definition coqDynamicContextConsHeadEqualityRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsHeadBranchContext tail)
    coqDynamicContextConsHeadEqualityTemplate.

Definition coqDynamicContextConsDeepHeadSigmaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsHeadBranchContext tail)
    coqDynamicContextConsDeepHeadSigmaTemplate.

Definition coqDynamicContextConsHeadBranchSigmaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpEqElim (coqDynamicContextConsHeadBranchContext tail)
    coqDynamicContextConsHeadEqualityLeftTerm
    coqDynamicContextConsHeadEqualityRightTerm
    coqDynamicContextConsSigmaMotiveTemplate
    (coqDynamicContextConsHeadEqualityRoot tail)
    (coqDynamicContextConsDeepHeadSigmaRoot tail).

Theorem coqDynamicContextConsHeadBranchSigmaRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsHeadBranchContext tail)
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsHeadBranchSigmaRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsHeadBranchSigmaRoot.
  rewrite <- coqDynamicContextConsSigmaMotive_formula.
  apply coqRestrictedPADirect_templateRawDerives_eqElim.
  - rewrite <- coqDynamicContextConsHeadEquality_shape.
    apply templateRawDerives_assumption. left. reflexivity.
  - rewrite coqDynamicContextConsSigmaMotive_head.
    apply templateRawDerives_assumption.
    apply coqDynamicContextCons_head_sigma_in_head_branch.
Qed.

(** The inherited-row branch opens its predecessor witness and specializes
    the old pointwise context-truth universal twice. *)
Definition coqDynamicContextConsOldRowBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsOldRowBodyTemplate.

Definition coqDynamicContextConsOldRowLiveRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE1 (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsOldRowLiveTemplate
    coqDynamicContextConsOldRowLookupTemplate
    (coqDynamicContextConsOldRowBodyRoot tail).

Definition coqDynamicContextConsOldRowLookupRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE2 (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsOldRowLiveTemplate
    coqDynamicContextConsOldRowLookupTemplate
    (coqDynamicContextConsOldRowBodyRoot tail).

Definition coqDynamicContextConsDeepOldBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsDeepOldBodyTemplate.

Definition coqDynamicContextConsDeepOldPointwiseRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE2 (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsDeepOldTraversalTemplate
    coqDynamicContextConsDeepOldPointwiseTemplate
    (coqDynamicContextConsDeepOldBodyRoot tail).

Definition coqDynamicContextConsOldPointwiseAtIndexRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllE (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsDeepOldIndexBodyTemplate (ttVar 0)
    (coqDynamicContextConsDeepOldPointwiseRoot tail).

Definition coqDynamicContextConsOldPointwiseAfterLiveRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpE (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsOldRowLiveTemplate
    coqDynamicContextConsOldPointwiseAfterLiveTemplate
    (coqDynamicContextConsOldPointwiseAtIndexRoot tail)
    (coqDynamicContextConsOldRowLiveRoot tail).

Definition coqDynamicContextConsOldPointwiseAtFormulaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllE (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsDeepOldFormulaBodyTemplate (ttVar 1)
    (coqDynamicContextConsOldPointwiseAfterLiveRoot tail).

Definition coqDynamicContextConsOldRowSigmaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpE (coqDynamicContextConsOldRowWitnessContext tail)
    coqDynamicContextConsOldRowLookupTemplate
    (templateFormulaRename S coqDynamicContextConsFinalSigmaTemplate)
    (coqDynamicContextConsOldPointwiseAtFormulaRoot tail)
    (coqDynamicContextConsOldRowLookupRoot tail).

Definition coqDynamicContextConsOldRowExistsRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsOldBranchContext tail)
    coqDynamicContextConsOldRowExistsTemplate.

Definition coqDynamicContextConsOldBranchSigmaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpExE (coqDynamicContextConsOldBranchContext tail)
    coqDynamicContextConsOldRowBodyTemplate
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsOldRowExistsRoot tail)
    (coqDynamicContextConsOldRowSigmaRoot tail).

Theorem coqDynamicContextConsOldRowSigmaRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsOldRowWitnessContext tail)
    (templateFormulaRename S coqDynamicContextConsFinalSigmaTemplate)
    (coqDynamicContextConsOldRowSigmaRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsOldRowSigmaRoot.
  apply coqDynamicContextCons_templateRawDerives_impE.
  - rewrite <- coqDynamicContextConsOldPointwiseAtFormula_shape.
    unfold coqDynamicContextConsOldPointwiseAtFormulaRoot.
    apply templateRawDerives_allE.
    rewrite <- coqDynamicContextConsOldPointwiseAfterLive_shape.
    unfold coqDynamicContextConsOldPointwiseAfterLiveRoot.
    apply coqDynamicContextCons_templateRawDerives_impE.
    + rewrite <- coqDynamicContextConsOldPointwiseAtIndex_shape.
      unfold coqDynamicContextConsOldPointwiseAtIndexRoot.
      apply templateRawDerives_allE.
      rewrite <- coqDynamicContextConsDeepOldPointwise_shape.
      unfold coqDynamicContextConsDeepOldPointwiseRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE2.
      rewrite <- coqDynamicContextConsDeepOldBody_shape.
      apply templateRawDerives_assumption.
      apply coqDynamicContextCons_deep_old_body_in.
    + unfold coqDynamicContextConsOldRowLiveRoot.
      apply coqRestrictedPADirect_templateRawDerives_andE1.
      rewrite <- coqDynamicContextConsOldRowBody_shape.
      apply templateRawDerives_assumption. left. reflexivity.
  - unfold coqDynamicContextConsOldRowLookupRoot.
    apply coqRestrictedPADirect_templateRawDerives_andE2.
    rewrite <- coqDynamicContextConsOldRowBody_shape.
    apply templateRawDerives_assumption. left. reflexivity.
Qed.

Theorem coqDynamicContextConsOldBranchSigmaRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsOldBranchContext tail)
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsOldBranchSigmaRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsOldBranchSigmaRoot.
  apply templateRawDerives_exE.
  - rewrite <- coqDynamicContextConsOldRowExists_shape.
    apply templateRawDerives_assumption. left. reflexivity.
  - apply coqDynamicContextConsOldRowSigmaRoot_derives.
Qed.

Definition coqDynamicContextConsPointwiseSigmaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpOrE (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsHeadEqualityTemplate
    coqDynamicContextConsOldRowExistsTemplate
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsRowAlternativeRoot tail)
    (coqDynamicContextConsHeadBranchSigmaRoot tail)
    (coqDynamicContextConsOldBranchSigmaRoot tail).

Theorem coqDynamicContextConsPointwiseSigmaRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsLookupContext tail)
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsPointwiseSigmaRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsPointwiseSigmaRoot.
  apply coqDynamicContextCons_templateRawDerives_orE.
  - rewrite <- coqDynamicContextConsRowAlternative_shape.
    apply coqDynamicContextConsRowAlternativeRoot_derives.
  - apply coqDynamicContextConsHeadBranchSigmaRoot_derives.
  - apply coqDynamicContextConsOldBranchSigmaRoot_derives.
Qed.

(** Close the lookup implication and the two pointwise universal binders. *)
Definition coqDynamicContextConsAfterLookupRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqDynamicContextConsFormulaContext tail)
    coqDynamicContextConsFinalLookupTemplate
    coqDynamicContextConsFinalSigmaTemplate
    (coqDynamicContextConsPointwiseSigmaRoot tail).

Definition coqDynamicContextConsAfterFormulaRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllI (coqDynamicContextConsLiveContext tail)
    coqDynamicContextConsFinalFormulaBodyTemplate
    (coqDynamicContextConsAfterLookupRoot tail).

Definition coqDynamicContextConsAfterLiveRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqDynamicContextConsIndexContext tail)
    coqDynamicContextConsFinalLiveTemplate
    coqDynamicContextConsFinalAfterLiveTemplate
    (coqDynamicContextConsAfterFormulaRoot tail).

Definition coqDynamicContextConsFinalPointwiseRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAllI (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsFinalIndexBodyTemplate
    (coqDynamicContextConsAfterLiveRoot tail).

Theorem coqDynamicContextConsFinalPointwiseRoot_derives : forall tail,
  TemplateRawDerives
    (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsFinalNewPointwiseTemplate
    (coqDynamicContextConsFinalPointwiseRoot tail).
Proof.
  intro tail.
  rewrite coqDynamicContextConsFinalPointwise_shape.
  unfold coqDynamicContextConsFinalPointwiseRoot.
  apply coqDynamicContextCons_templateRawDerives_allI.
  rewrite coqDynamicContextConsFinalIndexBody_shape.
  unfold coqDynamicContextConsAfterLiveRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  rewrite coqDynamicContextConsFinalAfterLive_shape.
  unfold coqDynamicContextConsAfterFormulaRoot.
  apply coqDynamicContextCons_templateRawDerives_allI.
  rewrite coqDynamicContextConsFinalFormulaBody_shape.
  unfold coqDynamicContextConsAfterLookupRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqDynamicContextConsPointwiseSigmaRoot_derives.
Qed.

(** Reassemble the five target witnesses, then eliminate the four
    structural witnesses and the five old-context witnesses. *)
Definition coqDynamicContextConsFinalStructuralBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsStructuralBodyTemplate.

Definition coqDynamicContextConsFinalNewTraversalRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndE1 (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsNewTraversalTemplate
    coqDynamicContextConsRowsTemplate
    (coqDynamicContextConsFinalStructuralBodyRoot tail).

Definition coqDynamicContextConsFinalNewBodyRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAndI (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsFinalNewTraversalTemplate
    coqDynamicContextConsFinalNewPointwiseTemplate
    (coqDynamicContextConsFinalNewTraversalRoot tail)
    (coqDynamicContextConsFinalPointwiseRoot tail).

Definition coqDynamicContextConsFinalNewTruthRoot
    (tail : TemplateContext) : TemplateRawProof :=
  coqDynamicContextConsIntroduceExistentials
    (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsNewTruthWitnesses
    coqDynamicContextConsFinalNewTruthTemplate
    (coqDynamicContextConsFinalNewBodyRoot tail).

Theorem coqDynamicContextConsFinalNewTruthRoot_derives : forall tail,
  TemplateRawDerives
    (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsFinalNewTruthTemplate
    (coqDynamicContextConsFinalNewTruthRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsFinalNewTruthRoot.
  apply coqDynamicContextConsIntroduceExistentials_derives.
  change (TemplateRawDerives
    (coqDynamicContextConsStructuralWitnessContext tail)
    coqDynamicContextConsFinalNewBodyTemplate
    (coqDynamicContextConsFinalNewBodyRoot tail)).
  rewrite coqDynamicContextConsFinalNewBody_shape.
  unfold coqDynamicContextConsFinalNewBodyRoot.
  apply coqDynamicContextCons_templateRawDerives_andI.
  - rewrite coqDynamicContextConsFinalTraversal_agreement.
    unfold coqDynamicContextConsFinalNewTraversalRoot.
    apply coqRestrictedPADirect_templateRawDerives_andE1.
    rewrite <- coqDynamicContextConsStructuralBody_shape.
    apply templateRawDerives_assumption.
    apply coqDynamicContextCons_structural_body_in.
  - apply coqDynamicContextConsFinalPointwiseRoot_derives.
Qed.

Definition coqDynamicContextConsAfterStructuralWitnessesRoot
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateNestedExEliminationFromRoot 4
    coqDynamicContextConsStructuralBodyTemplate
    (rawCoqTemplateRenameN 5 coqDynamicContextConsNewTruthTemplate)
    (coqDynamicContextConsOldWitnessContext tail)
    (coqDynamicContextConsStructuralResultRoot tail)
    (coqDynamicContextConsFinalNewTruthRoot tail).

Theorem coqDynamicContextConsAfterStructuralWitnessesRoot_derives :
  forall tail,
  TemplateRawDerives (coqDynamicContextConsOldWitnessContext tail)
    (rawCoqTemplateRenameN 5 coqDynamicContextConsNewTruthTemplate)
    (coqDynamicContextConsAfterStructuralWitnessesRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsAfterStructuralWitnessesRoot.
  apply rawCoqTemplateNestedExEliminationFromRoot_derives.
  - rewrite <- coqDynamicContextConsStructuralResult_shape.
    apply coqDynamicContextConsStructuralResultRoot_derives.
  - change (TemplateRawDerives
      (coqDynamicContextConsStructuralWitnessContext tail)
      coqDynamicContextConsFinalNewTruthTemplate
      (coqDynamicContextConsFinalNewTruthRoot tail)).
    apply coqDynamicContextConsFinalNewTruthRoot_derives.
Qed.

Definition coqDynamicContextConsOldTruthRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpAss (coqDynamicContextConsAfterHeadIntroduction tail)
    coqDynamicContextConsOldTruthTemplate.

Definition coqDynamicContextConsAfterOldWitnessesRoot
    (tail : TemplateContext) : TemplateRawProof :=
  rawCoqTemplateNestedExEliminationFromRoot 5
    coqDynamicContextConsOldBodyTemplate
    coqDynamicContextConsNewTruthTemplate
    (coqDynamicContextConsAfterHeadIntroduction tail)
    (coqDynamicContextConsOldTruthRoot tail)
    (coqDynamicContextConsAfterStructuralWitnessesRoot tail).

Lemma coqDynamicContextCons_old_truth_in_after_head : forall tail,
  In coqDynamicContextConsOldTruthTemplate
    (coqDynamicContextConsAfterHeadIntroduction tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsAfterHeadIntroduction,
    coqDynamicContextConsAfterOldIntroduction.
  right. left. reflexivity.
Qed.

Theorem coqDynamicContextConsAfterOldWitnessesRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsAfterHeadIntroduction tail)
    coqDynamicContextConsNewTruthTemplate
    (coqDynamicContextConsAfterOldWitnessesRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsAfterOldWitnessesRoot.
  apply rawCoqTemplateNestedExEliminationFromRoot_derives.
  - rewrite <- coqDynamicContextConsOldTruth_shape.
    apply templateRawDerives_assumption.
    apply coqDynamicContextCons_old_truth_in_after_head.
  - apply coqDynamicContextConsAfterStructuralWitnessesRoot_derives.
Qed.

Definition coqDynamicContextConsAfterHeadRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqDynamicContextConsAfterOldIntroduction tail)
    coqDynamicContextConsHeadSigmaTemplate
    coqDynamicContextConsNewTruthTemplate
    (coqDynamicContextConsAfterOldWitnessesRoot tail).

Definition coqDynamicContextConsNativeLawRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI (coqDynamicContextConsSourceContext tail)
    coqDynamicContextConsOldTruthTemplate
    (tfImp coqDynamicContextConsHeadSigmaTemplate
      coqDynamicContextConsNewTruthTemplate)
    (coqDynamicContextConsAfterHeadRoot tail).

Definition coqDynamicContextConsStructuralImplicationRoot
    (tail : TemplateContext) : TemplateRawProof :=
  trpImpI tail coqDynamicContextConsStructuralSourceTemplate
    coqDynamicContextConsNativeLawTemplate
    (coqDynamicContextConsNativeLawRoot tail).

Theorem coqDynamicContextConsNativeLawRoot_derives : forall tail,
  TemplateRawDerives (coqDynamicContextConsSourceContext tail)
    coqDynamicContextConsNativeLawTemplate
    (coqDynamicContextConsNativeLawRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsNativeLawRoot,
    coqDynamicContextConsNativeLawTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  unfold coqDynamicContextConsAfterHeadRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqDynamicContextConsAfterOldWitnessesRoot_derives.
Qed.

Theorem coqDynamicContextConsStructuralImplicationRoot_derives : forall tail,
  TemplateRawDerives tail
    (tfImp coqDynamicContextConsStructuralSourceTemplate
      coqDynamicContextConsNativeLawTemplate)
    (coqDynamicContextConsStructuralImplicationRoot tail).
Proof.
  intro tail.
  unfold coqDynamicContextConsStructuralImplicationRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqDynamicContextConsNativeLawRoot_derives.
Qed.

(** ------------------------------------------------------------------
    Carrier compilation on an honest witnessed PA tail. *)

Theorem
    raw_codedTemplatePALocalProofOf_contextListConsTruthTransferUniversal_on_tail :
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
        coqDynamicContextConsStructuralSourceTemplate) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  change (exists (prefix : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext)
      (rawTemplateFormula translation
        (embedPAFormula
          contextListConsTruthTransferUniversalFormula)) root).
  exact (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation hagreement baseWitnessList baseContext
    contextListConsTruthTransferUniversalFormula hbase
    PA_proves_contextListConsTruthTransferUniversalFormula).
Qed.

Theorem raw_codedPALocalProof_dynamicContextConsNativeLaw_on_selected_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) prefix,
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        prefix)
      (rawDirectTemplateFormula inputs
        coqDynamicContextConsNativeLawTemplate)
      root.
Proof.
  intros M hPA inputs prefix.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (agreement :=
    rawDirectStructuralTemplatePAAgreement M hPA inputs).
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedTemplatePALocalProofOf_contextListConsTruthTransferUniversal_on_tail
      M hPA translation agreement (raw_zero M) (raw_zero M) hempty)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M)).
  set (witnessTail := embedPAContext (map witnessedAxiom witnesses)).
  set (fullTemplateContext := prefix ++ witnessTail).

  assert (htailCode : rawTemplateContextCode translation witnessTail =
      extendedContext).
  {
    unfold witnessTail, extendedContext.
    rewrite rawTemplateContextCode_as_on_tail.
    exact (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation agreement witnesses (raw_zero M)).
  }
  assert (hfullCode : rawTemplateContextCode translation fullTemplateContext =
      rawTemplateContextCodeOnTail translation extendedContext prefix).
  {
    unfold fullTemplateContext.
    rewrite rawTemplateContextCode_app_on_tail.
    now rewrite htailCode.
  }

  pose proof (raw_templateProof_localProof M hPA translation
    (coqDynamicContextConsStructuralImplicationRoot fullTemplateContext)
    (proj1
      (coqDynamicContextConsStructuralImplicationRoot_derives
        fullTemplateContext))) as himplication.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation fullTemplateContext)
    (rawTemplateFormula translation
      (tfImp coqDynamicContextConsStructuralSourceTemplate
        coqDynamicContextConsNativeLawTemplate))
    (rawTemplateProofCode translation
      (coqDynamicContextConsStructuralImplicationRoot
        fullTemplateContext))) in himplication.
  rewrite hfullCode in himplication.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqDynamicContextConsStructuralSourceTemplate)
      (rawTemplateFormula translation
        coqDynamicContextConsNativeLawTemplate))
    (rawTemplateProofCode translation
      (coqDynamicContextConsStructuralImplicationRoot
        fullTemplateContext))) in himplication.

  destruct (raw_codedPALocalProof_directTemplatePrefix M hPA inputs
    extendedContext prefix
    (rawTemplateFormula translation
      coqDynamicContextConsStructuralSourceTemplate)
    sourceRoot
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      extendedContext hextended)
    hsource) as [prefixedSourceRoot hprefixedSource].

  exists witnesses.
  exists (rawProofImpERoot M
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      coqDynamicContextConsStructuralSourceTemplate)
    (rawTemplateFormula translation
      coqDynamicContextConsNativeLawTemplate)
    (rawTemplateProofCode translation
      (coqDynamicContextConsStructuralImplicationRoot
        fullTemplateContext))
    prefixedSourceRoot).
  split; [exact hextended |].
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation extendedContext prefix)
    (rawTemplateFormula translation
      coqDynamicContextConsStructuralSourceTemplate)
    (rawTemplateFormula translation
      coqDynamicContextConsNativeLawTemplate)
    (rawTemplateProofCode translation
      (coqDynamicContextConsStructuralImplicationRoot
        fullTemplateContext))
    prefixedSourceRoot himplication hprefixedSource).
Qed.

(** The two five-argument public truth leaves erase their displayed
    hierarchy arguments when they are connected to the selected ternary
    Sigma predicate.  Consequently the public Imp-I spelling and the native
    cons law have literally equal carrier formula codes. *)
Theorem raw_coqRestrictedPADirectImpIntroductionContextConsLaw_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  rawDirectTemplateFormula inputs
    coqRestrictedPADirectImpIntroductionContextConsLawTemplate =
  rawDirectTemplateFormula inputs
    coqDynamicContextConsNativeLawTemplate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector hconclusion hcontext.
  unfold
    coqRestrictedPADirectImpIntroductionContextConsLawTemplate,
    coqDynamicContextConsNativeLawTemplate.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  f_equal.
  - exact (raw_coqRestrictedPAContextTruthLeaf_expansion
      M hPA parameters contextTruth conclusionTruth
      sigmaCode sigmaSelector contextSelector hconclusion hcontext
      coqRestrictedPASoundnessLowerLevelTerm
      coqRestrictedPASoundnessUpperLevelTerm
      coqRestrictedPADirectAssumptionWitnessContextTerm
      (ttVar 9) (ttVar 8)).
  - f_equal.
    + unfold coqRestrictedPADirectImpIntroductionAntecedentTruthTemplate,
        coqDynamicContextConsHeadSigmaTemplate.
      rewrite (hconclusion
        coqRestrictedPASoundnessLowerLevelTerm
        coqRestrictedPASoundnessUpperLevelTerm
        (ttVar 6) (ttVar 9) (ttVar 8)).
      rewrite (hconclusion ttZero ttZero
        (ttVar 6) (ttVar 9) (ttVar 8)).
      reflexivity.
    + unfold
        coqRestrictedPADirectImpIntroductionNewContextTruthTemplate.
      exact (raw_coqRestrictedPAContextTruthLeaf_expansion
        M hPA parameters contextTruth conclusionTruth
        sigmaCode sigmaSelector contextSelector hconclusion hcontext
        coqRestrictedPASoundnessLowerLevelTerm
        coqRestrictedPASoundnessUpperLevelTerm
        coqDynamicContextConsNewContextTerm
        (ttVar 9) (ttVar 8)).
Qed.

(** Every binder-induced shift fixes a tail of embedded witnessed PA axioms,
    because those axioms are sentences.  We inherit the deepest endpoint
    calculation from the neighboring Or-I-left compiler and discard its
    three rule-specific prefix formulas. *)
Lemma coqDynamicContextConsImpIntroductionReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof
    (coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses
      witnesses) as horReady.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext
    in horReady.
  cbn [List.app] in horReady.
  pose proof (f_equal (skipn 3) horReady) as hdeep.
  cbn [skipn] in hdeep.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
    in hdeep.
  unfold
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepImpIntroductionCaseContext,
    coqRestrictedPADirectStrongStepImpIntroductionDeepEndpointContext.
  cbn [List.app].
  now rewrite hdeep.
Qed.

(** Compile the exact public Imp-I cons residual on the standard witnessed
    tail selected while compiling the closed arithmetic source theorem. *)
Theorem
    raw_coqRestrictedPADirectImpIntroductionContextConsLaw_on_selected_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector hconclusion hcontext.
  destruct
    (raw_codedPALocalProof_dynamicContextConsNativeLaw_on_selected_tail
      M hPA inputs
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext []))
    as (witnesses & root & hwitnessed & hnative).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (witnessTail := embedPAContext (map witnessedAxiom witnesses)).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)).
  assert (htailCode : rawTemplateContextCode translation witnessTail =
      extendedContext).
  {
    unfold witnessTail, extendedContext.
    rewrite rawTemplateContextCode_as_on_tail.
    exact (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
  }
  assert (hreadyCode : rawTemplateContextCode translation
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext
        witnessTail) =
      rawTemplateContextCodeOnTail translation extendedContext
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext [])).
  {
    unfold witnessTail.
    unfold witnessTail in htailCode.
    rewrite
      coqDynamicContextConsImpIntroductionReadyContext_app_witnesses.
    rewrite rawTemplateContextCode_app_on_tail.
    now rewrite htailCode.
  }
  pose proof
    (raw_coqRestrictedPADirectImpIntroductionContextConsLaw_code
      M hPA parameters contextTruth conclusionTruth
      sigmaCode sigmaSelector contextSelector hconclusion hcontext) as hlaw.
  change (rawDirectTemplateFormula inputs
      coqRestrictedPADirectImpIntroductionContextConsLawTemplate =
    rawDirectTemplateFormula inputs
      coqDynamicContextConsNativeLawTemplate) in hlaw.

  exists witnesses. split.
  - unfold witnessTail.
    unfold witnessTail in htailCode.
    rewrite htailCode. exact hwitnessed.
  - unfold
      RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot.
    unfold witnessTail in hreadyCode.
    exists root.
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectStrongStepImpIntroductionReadyContext
          (embedPAContext (map witnessedAxiom witnesses))))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionContextConsLawTemplate)
      root).
    rewrite hreadyCode, hlaw.
    exact hnative.
Qed.

(** Later rule compilers may select their own witness batches before or
    after this one.  The generic surround theorem transports the proof below
    both batches without inspecting any carrier code as a metatheoretic list. *)
Theorem raw_impIntroductionContextConsLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectImpIntroductionContextConsLawRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite
    coqDynamicContextConsImpIntroductionReadyContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepImpIntroductionReadyContext [])
      prefix witnesses suffix
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionContextConsLawTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite
    coqDynamicContextConsImpIntroductionReadyContext_app_witnesses.
  exact htransported.
Qed.

End PABoundedRawCodedDynamicContextTruthConsCompilation.
