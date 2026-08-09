(**
  Fixed PA refutations of the seven branches exposed by the honest
  selected-Sigma bottom boundary.

  The global source must first be applied and its ten traversal witnesses
  opened.  After the selected row's eight local witnesses are opened, every
  constructor branch has a contradiction-bearing principal fragment: the
  common parent is the closed code of falsity, while the branch asserts that
  this parent is a binary or unary constructor.  The QF branch instead
  asserts a positive rank-zero certificate for falsity.

  This module reifies only those principal fragments as ordinary PA syntax.
  In particular, the universal branch's opaque predecessor application is
  deliberately discarded by And-E1 before reification.  The resulting seven
  open PA schemata are valid in every raw PA model, hence have ordinary PA
  proofs.  A cumulative helper batch compiles all seven proofs on one growing
  witnessed PA tail.  They are then lifted under the literal Ex10+Ex8 prefix
  and converted to the full branch-to-bottom implications.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelBottomLaws
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthGlobalOpenedRowSelection
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFixedLevelBottomLaws.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.

(** The QF leaf is itself the contradiction-bearing fragment.  Every other
    branch begins with the formula-constructor atom; this remains true for
    the universal branch even though its second conjunct is opaque. *)
Definition coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
    (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  match branch with
  | DTLocalSigmaQF =>
      coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch
  | _ => templateAndLeftOrBot
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch)
  end.

Definition coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
    (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  tfImp
    (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal branch)
    tfBot.

(** Reification is deliberately partial in the library.  The fallback can
    never occur here, as the following kernel computation records. *)
Definition coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
    (branch : DynamicTruthLocalSigmaBranch) : formula :=
  match templateFormulaAsPAFormula
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch)
  with
  | Some output => output
  | None => pBot
  end.

Lemma
    coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation_reifies :
  forall branch,
  templateFormulaAsPAFormula
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch) =
  Some
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA branch).
Proof.
  intro branch. destruct branch; reflexivity.
Qed.

Lemma
    coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation_embeds :
  forall branch,
  embedPAFormula
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA branch) =
  coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch.
Proof.
  intro branch.
  exact (templateFormulaAsPAFormula_sound _ _
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation_reifies
      branch)).
Qed.

(** Each reified schema is valid with its displayed free variables.  The
    constructor cases use only list-code arity separation.  In the QF case,
    the root-row functionality theorem forces every rank-zero certificate
    for falsity to output zero, contradicting the requested output one. *)
Theorem
    coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA_raw_valid :
  forall branch (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA branch).
Proof.
  intros branch M hPA e. destruct branch.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcertificate.
    pose proof (raw_rankZeroTruthCertificate_bot_output_zero M hPA
      (rawNumeralValue M 1) _ _ hcertificate) as honeZero.
    exact (raw_zero_neq_truthOne M hPA (eq_sym honeZero)).
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 2
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))).
    exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 2
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))).
    exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 3
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))).
    exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 4
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))).
    exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_unary M hPA 6
      (raw_term_eval M e (tVar 6))).
    exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
      coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
      coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_unary M hPA 5
      (raw_term_eval M e (tVar 6))).
    exact hcode.
Qed.

(** Completeness applies to the universal closure; eliminating that closure
    recovers the displayed open schema.  This small wrapper is intentionally
    generic and is useful for any fixed open PA theorem proved by raw-model
    validity. *)
Lemma PA_proves_open_formula_of_raw_valid : forall target : formula,
  (forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e target) ->
  Formula.BProv Formula.Ax_s [] target.
Proof.
  intros target hvalid.
  assert (hclosed : Formula.BProv Formula.Ax_s [] (Formula.sealPA target)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner. exact (hvalid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] target (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Theorem
    PA_proves_coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation :
  forall branch,
  Formula.BProv Formula.Ax_s []
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA branch).
Proof.
  intro branch. apply PA_proves_open_formula_of_raw_valid.
  exact
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA_raw_valid
      branch).
Qed.

(** Package the seven fixed schemata for the existing dependent helper-batch
    interface.  The proof field remains correlated with its formula field. *)
Definition rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper
    (branch : DynamicTruthLocalSigmaBranch) : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA branch;
     rawFixedPAHelperBProv :=
       PA_proves_coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
         branch |}.

Definition rawRestrictedPASelectedSigmaBottomOpenedRefutationHelpers
    : list RawFixedPAHelper :=
  map rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper
    dynamicTruthLocalSigmaBranchOrder.

(** Generic cumulative compilation for a helper batch over an arbitrary
    witnessed tail.  Unlike the older six-field wrapper, this statement has
    no unrelated master roots.  Prefix concatenation records literally that
    all helper proofs end in one carrier-coded context. *)
Theorem raw_fixedPAHelperBatch_on_witnessed_tail : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    helpers baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) roots,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawFixedPAHelperBatchLocalProofs M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      helpers roots.
Proof.
  intros M hPA translation hagreement helpers.
  induction helpers as [|helper helperTail ih];
    intros baseWitnessList baseContext hbase.
  - exists [], []. cbn. split; [exact hbase | exact I].
  - destruct (ih baseWitnessList baseContext hbase)
      as (tailPrefix & tailRoots & htailWitnessed & htailProofs).
    set (tailWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        tailPrefix baseWitnessList).
    set (tailContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M tailPrefix baseContext).
    destruct
      (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
        M hPA translation hagreement tailWitnessList tailContext
        (rawFixedPAHelperFormula helper) htailWitnessed
        (rawFixedPAHelperBProv helper))
      as (headPrefix & headRoot & hheadWitnessed & hheadProof).
    assert (htailRealizable : RawContextListRealizable M tailContext).
    {
      exact (raw_codedPAAxiomWitnessContext_context_realizable M
        tailWitnessList tailContext htailWitnessed).
    }
    destruct
      (raw_fixedPAHelperBatchLocalProofs_standardPrefix
        M hPA translation headPrefix tailContext helperTail tailRoots
        htailRealizable htailProofs)
      as [transportedTailRoots htransportedTail].
    exists (headPrefix ++ tailPrefix),
      (headRoot :: transportedTailRoots).
    rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app,
      rawStandardPAAxiomWitnessPrefixContextCode_app.
    split; [exact hheadWitnessed |].
    cbn [RawFixedPAHelperBatchLocalProofs].
    split; [exact hheadProof | exact htransportedTail].
Qed.

Lemma raw_fixedPAHelperBatchLocalProofs_member : forall
    (M : RawPAModel) translation context helpers roots helper,
  RawFixedPAHelperBatchLocalProofs M translation context helpers roots ->
  In helper helpers ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFixedPAHelperTranslatedTargetCode M translation helper) root.
Proof.
  intros M translation context helpers.
  induction helpers as [|head tail ih]; intros roots helper hproofs hin.
  - contradiction.
  - destruct roots as [|root rootTail]; [contradiction |].
    cbn [RawFixedPAHelperBatchLocalProofs] in hproofs.
    destruct hproofs as [hhead htail].
    destruct hin as [<- | hin].
    + now exists root.
    + exact (ih rootTail helper htail hin).
Qed.

Lemma dynamicTruthLocalSigmaBranchOrder_complete_here : forall branch,
  In branch dynamicTruthLocalSigmaBranchOrder.
Proof. intro branch. destruct branch; cbn; tauto. Qed.

Lemma rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper_target :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) branch,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper branch) =
  rawTemplateFormula translation
    (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch).
Proof.
  intros M translation branch.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper.
  change (rawTemplateFormula translation
    (embedPAFormula
      (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutationPA
        branch)) =
    rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch)).
  now rewrite
    coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation_embeds.
Qed.

Definition coqRestrictedPASelectedSigmaBottomOpenedBranchRemainder
    (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch).

Lemma coqRestrictedPASelectedSigmaBottomOpenedBranch_shape_non_qf :
  forall branch,
  branch <> DTLocalSigmaQF ->
  coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch =
  tfAnd
    (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal branch)
    (coqRestrictedPASelectedSigmaBottomOpenedBranchRemainder branch).
Proof.
  intros branch hnot. destruct branch; try reflexivity.
  exfalso. apply hnot. reflexivity.
Qed.

(** Convert a proof of the principal refutation into a proof of the whole
    branch refutation without changing the parent context.  Context insertion
    is explicit: the principal refutation is transplanted below the branch
    assumption, the principal is projected, and that assumption is then
    discharged by Imp-I. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_opened_branch_refutation_of_principal :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context branch principalRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation branch))
    principalRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch))
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation context branch principalRoot
    hcontext hprincipal.
  set (branchFormula :=
    coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch).
  set (principal :=
    coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal branch).
  unfold coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
    in hprincipal.
  fold principal in hprincipal.
  rewrite rawTemplateFormula_imp, rawTemplateFormula_bot in hprincipal.
  assert (hbranchAdequate : RawCodedFormulaAtomicallyAdequate M
      (rawTemplateFormula translation branchFormula)).
  {
    apply raw_codedTemplateFormula_atomically_adequate_core.
    exact hPA.
  }
  destruct
    (raw_codedPALocalProof_adequateConsTransplant M hPA context
      (rawTemplateFormula translation branchFormula)
      (rawFormulaImpCode M
        (rawTemplateFormula translation principal)
        (rawFormulaBotCode M))
      principalRoot hbranchAdequate hcontext hprincipal)
    as [liftedPrincipalRoot hliftedPrincipal].
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawTemplateFormula translation branchFormula) hcontext)
    as hbranchAssumption.
  subst branchFormula. subst principal.
  assert (hprincipalAssumption : exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              branch)) context)
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal branch))
        root).
  {
    Ltac project_non_qf constructorName model pa trans ctx branchHyp :=
      let hshape := fresh "hshape" in
      assert (hshape :=
        coqRestrictedPASelectedSigmaBottomOpenedBranch_shape_non_qf
          constructorName ltac:(discriminate));
      rewrite hshape, rawTemplateFormula_and in branchHyp;
      try rewrite hshape, rawTemplateFormula_and;
      eexists;
      exact (raw_codedPALocalProofOf_andE1 model pa
        (rawListNode model
          (rawFormulaAndCode model
            (rawTemplateFormula trans
              (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
                constructorName))
            (rawTemplateFormula trans
              (coqRestrictedPASelectedSigmaBottomOpenedBranchRemainder
                constructorName))) ctx)
        (rawTemplateFormula trans
          (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal
            constructorName))
        (rawTemplateFormula trans
          (coqRestrictedPASelectedSigmaBottomOpenedBranchRemainder
            constructorName))
        _ branchHyp).
    destruct branch.
    - exists (rawProofAssumptionRoot M
        (rawListNode M
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
              DTLocalSigmaQF)) context)
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch
            DTLocalSigmaQF))).
      unfold coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal.
      exact hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaImpFalseLeft)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaImpTrueRight)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaAnd)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaOr)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaEx)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
    - project_non_qf constr:(DTLocalSigmaAll)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        hbranchAssumption.
  }
  destruct hprincipalAssumption as [projectedRoot hprojected].
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawListNode M
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch))
      context)
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomOpenedBranchPrincipal branch))
    (rawFormulaBotCode M)
    liftedPrincipalRoot projectedRoot hliftedPrincipal hprojected) as hbottom.
  lazymatch type of hbottom with
  | RawCodedPALocalProofOf _ _ _ ?bottomRoot =>
      exists (rawProofImpIRoot M context
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch))
        (rawFormulaBotCode M) bottomRoot);
      exact (raw_codedPALocalProofOf_impI M hPA context
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch))
        (rawFormulaBotCode M) bottomRoot hbottom)
  end.
Qed.

(** Resource construction factored from the finite case eliminator. *)
Lemma raw_finiteDisjunctionConsTransplantAdequate_of_members_here :
    forall (M : RawPAModel), RawPASatisfies M -> forall branches,
  (forall branch, In branch branches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawFiniteDisjunctionConsTransplantAdequate M branches.
Proof.
  intros M hPA branches.
  induction branches as [|head tail ih]; intro hall.
  - exact I.
  - destruct tail as [|second rest].
    + exact I.
    + cbn [RawFiniteDisjunctionConsTransplantAdequate].
      split.
      * apply hall. now left.
      * split.
        -- apply
             (raw_finiteRightDisjunctionCode_atomically_adequate_of_members
               M hPA (second :: rest)).
           intros branch hbranch. apply hall. now right.
        -- apply ih. intros branch hbranch. apply hall. now right.
Qed.

Lemma raw_finiteDisjunctionDerivedCaseResources_of_members_here :
    forall (M : RawPAModel), RawPASatisfies M -> forall branches context,
  RawContextListRealizable M context ->
  (forall branch, In branch branches ->
    RawCodedFormulaAtomicallyAdequate M branch) ->
  RawFiniteDisjunctionDerivedCaseResources M branches context.
Proof.
  intros M hPA branches context hcontext hall.
  destruct branches as [|first tail].
  - exact I.
  - destruct tail as [|second rest].
    + exact I.
    + cbn [RawFiniteDisjunctionDerivedCaseResources].
      split; [exact hcontext |].
      apply raw_finiteDisjunctionConsTransplantAdequate_of_members_here;
        assumption.
Qed.

(** Compile all seven principal refutations on one extension and turn them
    into the exact support record consumed by the global-opened boundary. *)
Theorem
    raw_restrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupport_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext sourcePrefix,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupportAt
      M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      sourcePrefix.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext sourcePrefix hbase.
  destruct
    (raw_fixedPAHelperBatch_on_witnessed_tail
      M hPA translation hagreement
      rawRestrictedPASelectedSigmaBottomOpenedRefutationHelpers
      baseWitnessList baseContext hbase)
    as (prefix & helperRoots & hextended & hhelpers).
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
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      extendedWitnessList extendedContext hextended).
  }
  set (deepPrefix :=
    coqRestrictedPASelectedSigmaBottomNativeLocalDeepContextOn sourcePrefix).
  assert (hdeepRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      extendedContext deepPrefix hextendedRealizable).
  }
  assert (hdeepAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation deepPrefix).
  {
    intros formula _hin.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation formula).
  }
  exists prefix. split; [exact hextended |].
  split; [exact hincluded |].
  constructor.
  - apply (raw_finiteDisjunctionDerivedCaseResources_of_members_here
      M hPA
      (rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
        M translation)
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix));
      [exact hdeepRealizable |].
    intros encodedBranch hencodedBranch.
    unfold rawRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranches
      in hencodedBranch.
    apply in_map_iff in hencodedBranch.
    destruct hencodedBranch as [branch [<- _]].
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation
      (coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaBranch branch)).
  - intro branch.
    assert (hhelperIn : In
        (rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper branch)
        rawRestrictedPASelectedSigmaBottomOpenedRefutationHelpers).
    {
      unfold rawRestrictedPASelectedSigmaBottomOpenedRefutationHelpers.
      apply in_map.
      exact (dynamicTruthLocalSigmaBranchOrder_complete_here branch).
    }
    destruct
      (raw_fixedPAHelperBatchLocalProofs_member
        M translation extendedContext
        rawRestrictedPASelectedSigmaBottomOpenedRefutationHelpers
        helperRoots
        (rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper branch)
        hhelpers hhelperIn)
      as [principalRoot hprincipal].
    rewrite rawRestrictedPASelectedSigmaBottomOpenedRefutationHelper_target
      in hprincipal.
    destruct
      (raw_codedPALocalProof_templatePrefix M hPA translation
        extendedContext deepPrefix
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomOpenedPrincipalRefutation
            branch))
        principalRoot hextendedRealizable hdeepAdequate hprincipal)
      as [deepPrincipalRoot hdeepPrincipal].
    exact
      (raw_codedPALocalProofOf_selectedSigmaBottom_opened_branch_refutation_of_principal
        M hPA translation
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        branch deepPrincipalRoot hdeepRealizable hdeepPrincipal).
Qed.

(** Unconditional growing endpoint for the selected-Sigma falsity row.  The
    first prefix selects the row; the second compiles the seven fixed branch
    refutations.  Their concatenation is returned as one ordinary standard
    PA witness prefix over the caller's original context. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation_compiled_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource)
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  set (source :=
    coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalSource).
  set (sourcePrefix := ([source] : TemplateContext)).
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_applied_root_row_selected
      M hPA translation hagreement baseWitnessList baseContext
      sourcePrefix
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate hbase)
    as (rowPrefix & selectedRoot & hrowWitnessed & _hrowIncluded & hselected).
  set (rowWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rowPrefix baseWitnessList).
  set (rowContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M rowPrefix baseContext).
  destruct
    (raw_restrictedPASelectedSigmaBottomGlobalOpenedSevenCaseSupport_growing
      M hPA translation hagreement rowWitnessList rowContext
      sourcePrefix hrowWitnessed)
    as (casePrefix & hcaseWitnessed & hrowCaseIncluded & hsupport).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      casePrefix rowWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M casePrefix rowContext).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      rowWitnessList rowContext finalWitnessList finalContext
      (coqRestrictedPASelectedSigmaBottomNativeAppliedGlobalDeepContextOn
        sourcePrefix)
      (rawTemplateFormula translation
        coqRestrictedPASelectedSigmaBottomNativeOpenedSigmaRow)
      selectedRoot hrowWitnessed hcaseWitnessed hrowCaseIncluded hselected)
    as [transportedSelectedRoot htransportedSelected].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottom_native_applied_refutation
      M hPA translation finalWitnessList finalContext
      transportedSelectedRoot hcaseWitnessed htransportedSelected hsupport)
    as [root hroot].
  exists (casePrefix ++ rowPrefix), root.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app,
    rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hcaseWitnessed |].
  split.
  - intros member hmember.
    apply hrowCaseIncluded.
    apply _hrowIncluded.
    exact hmember.
  - unfold source in hroot. exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations.
