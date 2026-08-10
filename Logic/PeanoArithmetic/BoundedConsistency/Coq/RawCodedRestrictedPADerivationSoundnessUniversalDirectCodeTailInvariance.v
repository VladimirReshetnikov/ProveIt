(**
  Opaque-tail invariance of the direct restricted-soundness code.

  Direct template inputs contain operation witnesses as well as the symbols
  which determine their translated codes.  A formula code, however, depends
  only on those symbols.  This module records a reusable extensionality
  theorem: changing opaque predicate interpretations outside a syntactic
  prefix cannot change the translation of a formula whose opaque names all
  lie in that prefix.

  The restricted-derivation soundness template uses precisely predicate
  names zero and one.  Consequently its universal direct code is unchanged
  when the dynamic-truth rows are installed at names two and above.  This is
  the exact bridge between the basic inputs carried by the consistency
  package and the extended inputs used by the rule-case compiler.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedPAProvability
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** ------------------------------------------------------------------
    Generic syntactic support and structural extensionality. *)

(** Every opaque leaf of [formula] has a predicate name strictly below
    [bound].  Terms need no companion predicate because they contain only
    variables, named parameters, and the fixed arithmetic constructors. *)
Fixpoint RawTemplateFormulaOpaqueNamesBelow
    (bound : nat) (formula : TemplateFormula) : Prop :=
  match formula with
  | tfEq _ _ => True
  | tfBot => True
  | tfImp lhs rhs =>
      RawTemplateFormulaOpaqueNamesBelow bound lhs /\
      RawTemplateFormulaOpaqueNamesBelow bound rhs
  | tfAnd lhs rhs =>
      RawTemplateFormulaOpaqueNamesBelow bound lhs /\
      RawTemplateFormulaOpaqueNamesBelow bound rhs
  | tfOr lhs rhs =>
      RawTemplateFormulaOpaqueNamesBelow bound lhs /\
      RawTemplateFormulaOpaqueNamesBelow bound rhs
  | tfAll body => RawTemplateFormulaOpaqueNamesBelow bound body
  | tfEx body => RawTemplateFormulaOpaqueNamesBelow bound body
  | tfOpaque predicate _ => predicate < bound
  end.

Arguments RawTemplateFormulaOpaqueNamesBelow bound formula
  : clear implicits.

(** Agreement of named parameter codes propagates through every finite
    template term.  This lemma deliberately ignores opaque predicates. *)
Lemma rawStructuralTemplateTermWith_parameter_ext : forall
    (M : RawPAModel)
    (first second : RawCodedTemplateStructuralSymbols M),
  (forall name,
    rawStructuralTemplateParameterCode first name =
    rawStructuralTemplateParameterCode second name) ->
  forall term,
  rawStructuralTemplateTermWith M first term =
  rawStructuralTemplateTermWith M second term.
Proof.
  intros M first second hparameters term.
  induction term as
      [index | name | | child IHchild
      | left IHleft right IHright | left IHleft right IHright];
    cbn [rawStructuralTemplateTermWith].
  - reflexivity.
  - apply hparameters.
  - reflexivity.
  - now rewrite IHchild.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
Qed.

Lemma rawStructuralTemplateTermsWith_parameter_ext : forall
    (M : RawPAModel)
    (first second : RawCodedTemplateStructuralSymbols M),
  (forall name,
    rawStructuralTemplateParameterCode first name =
    rawStructuralTemplateParameterCode second name) ->
  forall terms,
  rawStructuralTemplateTermsWith M first terms =
  rawStructuralTemplateTermsWith M second terms.
Proof.
  intros M first second hparameters terms.
  unfold rawStructuralTemplateTermsWith.
  apply map_ext.
  intro term.
  apply rawStructuralTemplateTermWith_parameter_ext.
  exact hparameters.
Qed.

(** Structural formula translation only observes opaque interpretations at
    names which actually occur.  The opaque-agreement premise is intentionally
    stated after translating arguments: together with parameter agreement,
    this avoids imposing any extensionality law on opaque selector functions. *)
Theorem rawStructuralTemplateFormulaWith_opaque_prefix_ext : forall
    (M : RawPAModel) bound formula
    (first second : RawCodedTemplateStructuralSymbols M),
  RawTemplateFormulaOpaqueNamesBelow bound formula ->
  (forall name,
    rawStructuralTemplateParameterCode first name =
    rawStructuralTemplateParameterCode second name) ->
  (forall predicate arguments, predicate < bound ->
    rawStructuralTemplateOpaqueCode first predicate arguments =
    rawStructuralTemplateOpaqueCode second predicate arguments) ->
  rawStructuralTemplateFormulaWith M first formula =
  rawStructuralTemplateFormulaWith M second formula.
Proof.
  intros M bound formula.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments];
    intros first second hbelow hparameters hopaque;
    cbn [RawTemplateFormulaOpaqueNamesBelow
      rawStructuralTemplateFormulaWith] in hbelow |- *.
  - rewrite
      (rawStructuralTemplateTermWith_parameter_ext
        M first second hparameters left),
      (rawStructuralTemplateTermWith_parameter_ext
        M first second hparameters right).
    reflexivity.
  - reflexivity.
  - destruct hbelow as [hleft hright].
    rewrite (IHleft first second hleft hparameters hopaque),
      (IHright first second hright hparameters hopaque).
    reflexivity.
  - destruct hbelow as [hleft hright].
    rewrite (IHleft first second hleft hparameters hopaque),
      (IHright first second hright hparameters hopaque).
    reflexivity.
  - destruct hbelow as [hleft hright].
    rewrite (IHleft first second hleft hparameters hopaque),
      (IHright first second hright hparameters hopaque).
    reflexivity.
  - now rewrite (IHbody first second hbelow hparameters hopaque).
  - now rewrite (IHbody first second hbelow hparameters hopaque).
  - rewrite (rawStructuralTemplateTermsWith_parameter_ext
      M first second hparameters arguments).
    apply hopaque.
    exact hbelow.
Qed.

(** The direct-input proof fields are irrelevant to code translation.  This
    wrapper is often the most convenient reusable form of the previous
    structural-symbol theorem. *)
Corollary rawDirectTemplateFormula_opaque_prefix_ext : forall
    (M : RawPAModel) bound formula
    (first second : RawCodedTemplateDirectStructuralInputs M),
  RawTemplateFormulaOpaqueNamesBelow bound formula ->
  (forall name,
    rawStructuralTemplateParameterCode
      (rawDirectTemplateSymbols first) name =
    rawStructuralTemplateParameterCode
      (rawDirectTemplateSymbols second) name) ->
  (forall predicate arguments, predicate < bound ->
    rawStructuralTemplateOpaqueCode
      (rawDirectTemplateSymbols first) predicate arguments =
    rawStructuralTemplateOpaqueCode
      (rawDirectTemplateSymbols second) predicate arguments) ->
  rawDirectTemplateFormula first formula =
  rawDirectTemplateFormula second formula.
Proof.
  intros M bound formula first second hbelow hparameters hopaque.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_opaque_prefix_ext
    with (bound := bound); assumption.
Qed.

(** Embedded PA formulae have no opaque leaves. *)
Lemma rawTemplateFormulaOpaqueNamesBelow_embedPA : forall
    bound formula,
  RawTemplateFormulaOpaqueNamesBelow bound (embedPAFormula formula).
Proof.
  intros bound formula.
  induction formula; cbn [embedPAFormula
    RawTemplateFormulaOpaqueNamesBelow] in *; intuition.
Qed.

Lemma rawTemplateFormulaOpaqueNamesBelow_closeN : forall
    bound count formula,
  RawTemplateFormulaOpaqueNamesBelow bound formula ->
  RawTemplateFormulaOpaqueNamesBelow bound
    (restrictedTargetTemplateCloseN count formula).
Proof.
  intros bound count.
  induction count as [|count IHcount]; intros formula hformula.
  - exact hformula.
  - cbn [restrictedTargetTemplateCloseN].
    apply IHcount.
    exact hformula.
Qed.

(** Instantiating a restricted-target context introduces named terms but no
    opaque formula family. *)
Lemma rawTemplateFormulaOpaqueNamesBelow_restrictedTarget : forall
    bound replacement context,
  RawTemplateFormulaOpaqueNamesBelow bound
    (restrictedTargetTemplateFormulaContext replacement context).
Proof.
  intros bound replacement context.
  induction context;
    cbn [restrictedTargetTemplateFormulaContext
      RawTemplateFormulaOpaqueNamesBelow] in *; try intuition.
  - apply rawTemplateFormulaOpaqueNamesBelow_embedPA.
  - apply rawTemplateFormulaOpaqueNamesBelow_closeN.
    exact IHcontext.
Qed.

(** Renaming and term substitution change only arguments of opaque leaves,
    never their predicate names.  These two closure lemmas let larger
    compiler templates inherit a small opaque support proof from their
    unshifted source without reopening their term-level definitions. *)
Lemma rawTemplateFormulaOpaqueNamesBelow_rename : forall
    bound renaming formula,
  RawTemplateFormulaOpaqueNamesBelow bound formula ->
  RawTemplateFormulaOpaqueNamesBelow bound
    (templateFormulaRename renaming formula).
Proof.
  intros bound renaming formula.
  revert renaming.
  induction formula; intros renaming hbelow;
    cbn [templateFormulaRename RawTemplateFormulaOpaqueNamesBelow]
      in hbelow |- *; intuition.
Qed.

Lemma rawTemplateFormulaOpaqueNamesBelow_subst : forall
    bound substitution formula,
  RawTemplateFormulaOpaqueNamesBelow bound formula ->
  RawTemplateFormulaOpaqueNamesBelow bound
    (templateFormulaSubst substitution formula).
Proof.
  intros bound substitution formula.
  revert substitution.
  induction formula; intros substitution hbelow;
    cbn [templateFormulaSubst RawTemplateFormulaOpaqueNamesBelow]
      in hbelow |- *; intuition.
Qed.

(** ------------------------------------------------------------------
    The two-name support theorem for restricted derivation soundness. *)

Lemma
    coqRestrictedPADerivationSoundnessUniversalTemplate_opaque_names_below_two :
  RawTemplateFormulaOpaqueNamesBelow 2
    coqRestrictedPADerivationSoundnessUniversalTemplate.
Proof.
  unfold coqRestrictedPADerivationSoundnessUniversalTemplate,
    coqRestrictedPADerivationSoundnessPredicateTemplate,
    coqRestrictedPADerivationSoundnessRestrictedProofTemplate,
    coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate,
    coqRestrictedPADerivationSoundnessProofWideCertificatesTemplate,
    coqRestrictedPADerivationSoundnessEndpointTemplate,
    coqRestrictedPADerivationSoundnessAdmissibleTemplate,
    coqRestrictedPADerivationSoundnessAdmissibleCoreTemplate,
    coqRestrictedPADerivationSoundnessCommonCoverageTemplate,
    coqRestrictedPADerivationSoundnessContextTruthTemplate,
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate,
    coqRestrictedPAContextTruthPredicateName,
    coqRestrictedPAConclusionTruthPredicateName.
  cbn [RawTemplateFormulaOpaqueNamesBelow].
  repeat split;
    try apply rawTemplateFormulaOpaqueNamesBelow_embedPA;
    try apply rawTemplateFormulaOpaqueNamesBelow_restrictedTarget;
    lia.
Qed.

(** The closure-induction body used to manufacture the universal soundness
    certificate has the same two-name support.  The shifted and opened
    carrier prefixes inherit support from the generic preservation lemmas
    above. *)
Lemma
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate_opaque_names_below_two
    : RawTemplateFormulaOpaqueNamesBelow 2
        coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate.
Proof.
  assert (hpredicate : RawTemplateFormulaOpaqueNamesBelow 2
      coqRestrictedPADerivationSoundnessPredicateTemplate).
  {
    pose proof
      coqRestrictedPADerivationSoundnessUniversalTemplate_opaque_names_below_two
      as huniversal.
    unfold coqRestrictedPADerivationSoundnessUniversalTemplate
      in huniversal.
    exact huniversal.
  }
  assert (hprefix : RawTemplateFormulaOpaqueNamesBelow 2
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate).
  {
    unfold
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixTemplate,
      coqRestrictedPADerivationSoundnessCarrierPredicateTemplate.
    cbn [RawTemplateFormulaOpaqueNamesBelow].
    split.
    - apply rawTemplateFormulaOpaqueNamesBelow_embedPA.
    - exact hpredicate.
  }
  assert (hshifted : RawTemplateFormulaOpaqueNamesBelow 2
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate).
  {
    unfold
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixShiftedTemplate.
    apply rawTemplateFormulaOpaqueNamesBelow_rename.
    exact hprefix.
  }
  assert (hsuccessor : RawTemplateFormulaOpaqueNamesBelow 2
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate).
  {
    unfold
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixSuccessorTemplate,
      templateFormulaOpen.
    apply rawTemplateFormulaOpaqueNamesBelow_subst.
    exact hshifted.
  }
  assert (hzero : RawTemplateFormulaOpaqueNamesBelow 2
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate).
  {
    unfold
      coqRestrictedPADerivationSoundnessCarrierStrongPrefixZeroTemplate,
      templateFormulaOpen.
    apply rawTemplateFormulaOpaqueNamesBelow_subst.
    exact hprefix.
  }
  unfold
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate.
  cbn [RawTemplateFormulaOpaqueNamesBelow].
  intuition.
Qed.

(** Installing an arbitrary tail at names [2 + p] preserves every formula
    supported by the two reserved soundness selectors. *)
Theorem
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_below_two_eq_basic
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      formula,
  RawTemplateFormulaOpaqueNamesBelow 2 formula ->
  rawDirectTemplateFormula
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth tail) formula =
  rawDirectTemplateFormula
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth) formula.
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail formula hbelow.
  apply rawDirectTemplateFormula_opaque_prefix_ext with (bound := 2).
  - exact hbelow.
  - intro name. reflexivity.
  - intros [|[|predicate]] arguments hpredicate;
      cbn [rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
        rawCoqRestrictedPADerivationSoundnessTemplateSymbols
        rawNumeralTemplateSymbols
        rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawCoqRestrictedPADerivationSoundnessOpaqueCode]; try reflexivity.
    lia.
Qed.

(** The reusable exact code seam.  It needs no semantic property of the
    opaque tail beyond the operation witnesses required to construct it. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_extended_eq_basic
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters),
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth tail) =
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail.
  rewrite !raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_below_two_eq_basic.
  exact
    coqRestrictedPADerivationSoundnessUniversalTemplate_opaque_names_below_two.
Qed.

(** The same invariance transports the closure-induction body.  This is
    needed because the carried package chooses its closure witnesses for the
    basic two-selector inputs, whereas represented rule cases are compiled
    against the extended row inputs. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_extended_eq_basic
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters),
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
    (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth tail) =
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail.
  rewrite
    !raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_view.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_below_two_eq_basic.
  exact
    coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyTemplate_opaque_names_below_two.
Qed.

(** Closure data depends on [inputs] only through the carrier-body code.
    State that transport once at the most general code-equality boundary. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_transport
    : forall (M : RawPAModel)
      (first second : RawCodedTemplateDirectStructuralInputs M)
      replacement axiom closureCount,
  rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M first =
    rawCoqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode
      M second ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M first replacement axiom closureCount ->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M second replacement axiom closureCount.
Proof.
  intros M first second replacement axiom closureCount hcode hremainder.
  unfold
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
    in hremainder |- *.
  rewrite <- hcode.
  exact hremainder.
Qed.

Corollary
    raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_extended_iff_basic
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder M
      (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth tail)
      replacement axiom closureCount <->
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      replacement axiom closureCount.
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail
    replacement axiom closureCount.
  pose proof
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirectCode_extended_eq_basic
      M hPA parameters contextTruth conclusionTruth tail) as hcode.
  split; intro hremainder.
  - exact
      (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_transport
        M _ _ replacement axiom closureCount hcode hremainder).
  - exact
      (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_transport
        M _ _ replacement axiom closureCount (eq_sym hcode) hremainder).
Qed.

(** An already constructed proof certificate can be retargeted along the
    code equality without changing its proof tree. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_basic_of_extended
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      certificate,
  RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth tail))
      certificate ->
  RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      certificate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail certificate
    hcertificate.
  rewrite <-
    (raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_extended_eq_basic
      M hPA parameters contextTruth conclusionTruth tail).
  exact hcertificate.
Qed.

(** Concrete specialization to the two dynamic-truth successor rows. *)
Corollary
    raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_extended_rows_eq_basic
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      lowerPiCode lowerSigmaCode
      (lowerPiSelector :
        RawCodedTernaryApplicationSelector M lowerPiCode)
      (lowerSigmaSelector :
        RawCodedTernaryApplicationSelector M lowerSigmaCode)
      (lowerPiCommuting :
        RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
          M lowerPiCode lowerPiSelector)
      (lowerSigmaCommuting :
        RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
          M lowerSigmaCode lowerSigmaSelector),
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
    (rawCoqRestrictedPAExtendedRowsInputs
      M hPA parameters contextTruth conclusionTruth
      lowerPiCode lowerSigmaCode lowerPiSelector lowerSigmaSelector
      lowerPiCommuting lowerSigmaCommuting) =
  rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    lowerPiCode lowerSigmaCode lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting.
  unfold rawCoqRestrictedPAExtendedRowsInputs.
  apply
    raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_extended_eq_basic.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance.
