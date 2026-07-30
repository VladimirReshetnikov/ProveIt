(**
  Compile the full Sigma-row domain projection.

  The two previously compiled positive local components start from rows in
  which the final universal/existential alternative has already been
  selected.  They therefore do not yet provide an eliminator whose
  antecedent is the genuine successor row.  The smallest such eliminator on
  the Sigma side is

      Ex^8 (domain /\ seven-way-branches) -> Ex^8 domain.

  It preserves the actual eight table witnesses and forgets only the branch
  disjunction.  In particular, this is a projection from the *full* native
  Sigma row, not another restricted-branch statement.

  The fixed source proof is sent through the same direct structural
  translator as the restricted universal component.  Its code is then
  identified first with the honest source-template polynomial and finally
  with the native Sigma-row polynomial.  The latter step uses PA only to
  identify quotations of the fixed leaves with their numeral codes.

  This is one component of the eventual local decision/exclusivity bundle;
  it does not claim that the remaining branch-specific eliminators or the
  complete bundle have already been assembled.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateClosedProofCompilation
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthUniversalLeafProofCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateClosedProofCompilation.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.

(** ------------------------------------------------------------------
    Honest source proof from the complete seven-way row. *)

Definition coqDynamicTruthSigmaDomainProjectionFormula : TemplateFormula :=
  tfImp coqDynamicTruthSigmaSuccessorRowTemplate
    (templateRepeatedExists 8 coqDynamicTruthSigmaDomainLeafTemplate).

Definition coqDynamicTruthSigmaDomainProjectionProof : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [coqDynamicTruthSigmaDomainLeafTemplate]
    coqDynamicTruthSigmaBranchesTemplate [] 0.

Theorem coqDynamicTruthSigmaDomainProjectionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaDomainProjectionFormula
    coqDynamicTruthSigmaDomainProjectionProof.
Proof.
  unfold coqDynamicTruthSigmaDomainProjectionFormula,
    coqDynamicTruthSigmaDomainProjectionProof,
    coqDynamicTruthSigmaSuccessorRowTemplate.
  change (TemplateRawDerives []
    (tfImp
      (templateRepeatedExists 8
        (templateRightConjunction
          [coqDynamicTruthSigmaDomainLeafTemplate]
          coqDynamicTruthSigmaBranchesTemplate))
      (templateRepeatedExists 8
        (templateSelectedRightConjunction
          [coqDynamicTruthSigmaDomainLeafTemplate]
          coqDynamicTruthSigmaBranchesTemplate [] 0)))
    (templateRepeatedExistsSelectionProof 8
      [coqDynamicTruthSigmaDomainLeafTemplate]
      coqDynamicTruthSigmaBranchesTemplate [] 0)).
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

(** The native row is read beneath thirteen ambient columns.  Closing the
    projection over exactly those columns makes it a reusable master-field
    component rather than an open row lemma. *)
Definition coqDynamicTruthSigmaDomainProjectionFieldFormula
    : TemplateFormula :=
  templateRepeatedForall coqDynamicTruthSigmaRowEnvironmentArity
    coqDynamicTruthSigmaDomainProjectionFormula.

Definition coqDynamicTruthSigmaDomainProjectionFieldProof
    : TemplateRawProof :=
  templateUniversalCloseProof coqDynamicTruthSigmaRowEnvironmentArity
    coqDynamicTruthSigmaDomainProjectionFormula
    coqDynamicTruthSigmaDomainProjectionProof.

Theorem coqDynamicTruthSigmaDomainProjectionFieldProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaDomainProjectionFieldFormula
    coqDynamicTruthSigmaDomainProjectionFieldProof.
Proof.
  unfold coqDynamicTruthSigmaDomainProjectionFieldFormula,
    coqDynamicTruthSigmaDomainProjectionFieldProof.
  apply templateUniversalCloseProof_derives.
  exact coqDynamicTruthSigmaDomainProjectionProof_derives.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier-code polynomials. *)

Definition rawCoqDynamicTruthSigmaDomainProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
      domain lowerApplication)
    (rawFormulaEx8Code M domain).

Definition rawDynamicTruthSigmaDomainProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthSigmaSuccessorRowCode M domain lowerApplication)
    (rawFormulaEx8Code M domain).

Definition rawCoqDynamicTruthSigmaDomainProjectionFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M coqDynamicTruthSigmaRowEnvironmentArity
    (rawCoqDynamicTruthSigmaDomainProjectionCode M
      domain lowerApplication).

Definition rawDynamicTruthSigmaDomainProjectionFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M coqDynamicTruthSigmaRowEnvironmentArity
    (rawDynamicTruthSigmaDomainProjectionCode M
      domain lowerApplication).

(** Direct interpretation of the complete source row.  This equation is
    proved structurally; no adequacy or operation law for the opaque atom is
    inferred from a code equality. *)
Lemma rawDirect_coqDynamicTruthSigmaSuccessorRowTemplate_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaSuccessorRowTemplate =
  rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold coqDynamicTruthSigmaSuccessorRowTemplate,
    rawCoqDynamicTruthSigmaSuccessorRowTemplateCode.
  change (rawFormulaEx8Code M
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaDomainLeafTemplate)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaBranchesTemplate)) =
    rawFormulaEx8Code M
      (rawFormulaAndCode M concreteDomain
        (rawCoqDynamicTruthSigmaBranchesTemplateCode M
          concreteLowerApplication))).
  rewrite (rawCoqDynamicTruthSigmaDirect_domain_identified
    identification).
  unfold coqDynamicTruthSigmaBranchesTemplate,
    coqDynamicTruthSigmaQfLeafTemplate,
    coqDynamicTruthSigmaImpFalseLeftLeafTemplate,
    coqDynamicTruthSigmaImpTrueRightLeafTemplate,
    coqDynamicTruthSigmaAndLeafTemplate,
    coqDynamicTruthSigmaOrLeafTemplate,
    coqDynamicTruthSigmaExLeafTemplate,
    rawCoqDynamicTruthSigmaBranchesTemplateCode.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  rewrite rawDirect_coqDynamicTruthSigmaUniversalLeafTemplate.
  rewrite (rawCoqDynamicTruthSigmaDirect_lowerApplication_identified
    identification).
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthSigmaDomainProjection_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaDomainProjectionFormula =
  rawCoqDynamicTruthSigmaDomainProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold coqDynamicTruthSigmaDomainProjectionFormula,
    rawCoqDynamicTruthSigmaDomainProjectionCode.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
    templateRepeatedExists].
  rewrite (rawDirect_coqDynamicTruthSigmaSuccessorRowTemplate_identified
    M inputs concreteDomain concreteLowerApplication identification).
  rewrite (rawCoqDynamicTruthSigmaDirect_domain_identified
    identification).
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthSigmaDomainProjectionField_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaDomainProjectionFieldFormula =
  rawCoqDynamicTruthSigmaDomainProjectionFieldCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold coqDynamicTruthSigmaDomainProjectionFieldFormula,
    rawCoqDynamicTruthSigmaDomainProjectionFieldCode.
  rewrite rawDirectTemplateFormula_repeatedForall.
  rewrite (rawDirect_coqDynamicTruthSigmaDomainProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

(** Honest quotation of the six fixed alternatives and the universal prefix
    agrees with the numeral leaves used by the native row graph. *)
Lemma rawCoqDynamicTruthSigmaSuccessorRowTemplateCode_eq_native :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall domain lowerApplication,
  rawCoqDynamicTruthSigmaSuccessorRowTemplateCode M
    domain lowerApplication =
  rawDynamicTruthSigmaSuccessorRowCode M domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthSigmaSuccessorRowTemplateCode,
    rawCoqDynamicTruthSigmaBranchesTemplateCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    rawDynamicTruthSigmaSuccessorRowCode,
    rawDynamicTruthSigmaBranchesCode,
    rawDynamicTruthSigmaUniversalCode,
    rawDynamicTruthSigmaNoBinderCode,
    rawFormulaEx3Code.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

(** The unclosed projection is the form consumed by local row roots.  Keep
    this equality separate from the universally closed field equality below:
    clients that already have a witnessed, self-shifting base can compile the
    open implication there and need not introduce and later eliminate the
    thirteen environment binders. *)
Theorem rawCoqDynamicTruthSigmaDomainProjectionCode_eq_native :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall domain lowerApplication,
  rawCoqDynamicTruthSigmaDomainProjectionCode M
    domain lowerApplication =
  rawDynamicTruthSigmaDomainProjectionCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthSigmaDomainProjectionCode,
    rawDynamicTruthSigmaDomainProjectionCode.
  rewrite (rawCoqDynamicTruthSigmaSuccessorRowTemplateCode_eq_native
    M hPA domain lowerApplication).
  reflexivity.
Qed.

Theorem rawCoqDynamicTruthSigmaDomainProjectionFieldCode_eq_native :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall domain lowerApplication,
  rawCoqDynamicTruthSigmaDomainProjectionFieldCode M
    domain lowerApplication =
  rawDynamicTruthSigmaDomainProjectionFieldCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthSigmaDomainProjectionFieldCode,
    rawDynamicTruthSigmaDomainProjectionFieldCode.
  rewrite (rawCoqDynamicTruthSigmaDomainProjectionCode_eq_native
    M hPA domain lowerApplication).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact represented PA certificate. *)

Definition rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthSigmaDomainProjectionFieldProof.

Arguments rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
  M hPA inputs : clear implicits.

Theorem raw_codedPAProofOf_coqDynamicTruthSigmaDomainProjectionField :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaDomainProjectionFieldFormula)
    (rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaDomainProjectionFieldFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaDomainProjectionFieldProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthSigmaDomainProjectionFieldProof_derives.
Qed.

(** The same direct inputs already selected for the restricted universal
    branch identify this component.  Thus a future combined local-field
    compiler can emit both certificates before hiding the shared inputs. *)
Theorem
    raw_codedPAProofOf_dynamicTruthSigmaDomainProjectionField_identified :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawDynamicTruthSigmaDomainProjectionFieldCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthSigmaDomainProjectionFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <- (rawCoqDynamicTruthSigmaDomainProjectionFieldCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite <-
    (rawDirect_coqDynamicTruthSigmaDomainProjectionField_identified
      M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthSigmaDomainProjectionField.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
