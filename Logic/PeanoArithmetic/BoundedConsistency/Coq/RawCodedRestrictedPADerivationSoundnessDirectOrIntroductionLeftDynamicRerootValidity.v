(**
  Raw-model validity of the carrier-parametric Or-I-left reroot law.

  The source formula is fixed syntactically in the preceding module.  This
  file proves its arithmetic content: the parent restriction is evaluated
  below the eight constructor witnesses, whereas the child restriction is
  evaluated immediately below the outer abstraction variable.  Carrier
  restricted proofs ignore those unrelated assignment tails, so the ordinary
  recursive-child argument connects the two interpretations without assuming
  that the hierarchy value is a standard numeral.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedProofConstructors
  RawCodedProofOrIConstructors
  RawModelCompleteness
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource.

(** Iterated weakening shifts the semantic variable environment by exactly
    the displayed metatheoretic count. *)
Lemma rawTemplateFormulaSat_rawCoqTemplateRenameN : forall
    count (M : RawPAModel) variables parameters predicates formula,
  rawTemplateFormulaSat M variables parameters predicates
    (rawCoqTemplateRenameN count formula) <->
  rawTemplateFormulaSat M
    (fun index => variables (index + count))
    parameters predicates formula.
Proof.
  induction count as [|count ih];
    intros M variables parameters predicates formula.
  - cbn [rawCoqTemplateRenameN].
    apply rawTemplateFormulaSat_variables_ext.
    intros index. f_equal. lia.
  - cbn [rawCoqTemplateRenameN].
    rewrite ih, rawTemplateFormulaSat_rename.
    apply rawTemplateFormulaSat_variables_ext.
    intros index. f_equal. lia.
Qed.

(** The nested strong-step projections reduce definitionally to the compact
    restriction of the left recursive child.  Recording the equation keeps
    the semantic proof independent of those projection implementation
    details. *)
Lemma
    coqRestrictedPADirectOrIntroductionLeftChildRestrictedCore_shape :
  coqRestrictedPADirectOrIntroductionLeftChildRestrictedCoreTemplate =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 2)).
Proof. reflexivity. Qed.

Theorem
    raw_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLaw_valid :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate.
  cbn [rawTemplateFormulaSat]. intros hparent hcase.

  rewrite rawTemplateFormulaSat_rename in hparent.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate
    in hparent.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hparent.
  unfold coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate,
    coqRestrictedPASoundnessLowerLevelTerm in hparent.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter in hparent;
    [|apply restrictedTargetProofContext_seal_free].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectOrIntroductionLeft_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as [hcode _].
  unfold coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat] in hcode.

  rewrite rawTemplateFormulaSat_rename.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftChildRestrictedCore_shape.
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].

  apply (proj2 (raw_carrierRestrictedProofContextSat_iff M
    (fun index => variables (S index))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (tVar 2))).
  eapply raw_carrierRestrictedProofAt_orI_left_child_between;
    [exact hPA | |].
  - apply (proj1 (raw_carrierRestrictedProofContextSat_iff M
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (tVar 4))).
    exact hparent.
  - exact hcode.
Qed.

Theorem
    raw_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula.
Proof.
  intros M hPA variables.
  unfold
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula)).
  rewrite
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_embed.
  unfold
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate)).
  apply
    raw_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLaw_valid.
  exact hPA.
Qed.

(** Semantic completeness applies to the standard seal of the source.  The
    seal is then eliminated with identity renaming, yielding the intended
    open theorem whose displayed outer quantifier binds the arbitrary
    carrier hierarchy level. *)
Theorem
    PA_proves_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
