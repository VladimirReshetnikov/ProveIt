(**
  Compile the full Pi-row domain projection.

  The previously compiled positive Pi component starts from a row in which
  the final existential alternative has already been selected.  It therefore
  does not yet provide an eliminator whose antecedent is the genuine
  successor row.  The smallest such eliminator on the Pi side is

      Ex^8 (domain /\ six-way-branches) -> Ex^8 domain.

  It preserves the actual eight table witnesses and forgets only the branch
  disjunction.  In particular, this is a projection from the *full* native Pi
  row.  The six-way disjunction below is the genuine Pi syntax; it is not a
  Sigma row reused by erasing polarity.

  The fixed source proof is sent through the direct structural translator.
  Its code is identified first with the honest source-template polynomial and
  then, using the existing quotation theorem, with the native Pi-row
  polynomial.  The public component is closed over the row's thirteen ambient
  columns.

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
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthPiExistentialLeafProofCompilation
  RawCodedDynamicTruthUniversalLeafProofCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.

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
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.

(** ------------------------------------------------------------------
    Honest source proof from the complete six-way row. *)

Definition coqDynamicTruthPiDomainProjectionFormula : TemplateFormula :=
  tfImp coqDynamicTruthPiSuccessorRowTemplate
    (templateRepeatedExists 8 coqDynamicTruthPiDomainLeafTemplate).

Definition coqDynamicTruthPiDomainProjectionProof : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [coqDynamicTruthPiDomainLeafTemplate]
    coqDynamicTruthPiBranchesTemplate [] 0.

Theorem coqDynamicTruthPiDomainProjectionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthPiDomainProjectionFormula
    coqDynamicTruthPiDomainProjectionProof.
Proof.
  unfold coqDynamicTruthPiDomainProjectionFormula,
    coqDynamicTruthPiDomainProjectionProof,
    coqDynamicTruthPiSuccessorRowTemplate.
  change (TemplateRawDerives []
    (tfImp
      (templateRepeatedExists 8
        (templateRightConjunction
          [coqDynamicTruthPiDomainLeafTemplate]
          coqDynamicTruthPiBranchesTemplate))
      (templateRepeatedExists 8
        (templateSelectedRightConjunction
          [coqDynamicTruthPiDomainLeafTemplate]
          coqDynamicTruthPiBranchesTemplate [] 0)))
    (templateRepeatedExistsSelectionProof 8
      [coqDynamicTruthPiDomainLeafTemplate]
      coqDynamicTruthPiBranchesTemplate [] 0)).
  apply templateRepeatedExistsSelectionProof_derives.
Qed.

(** The native row is read beneath thirteen ambient columns.  Closing the
    projection over exactly those columns makes it a reusable master-field
    component rather than an open row lemma. *)
Definition coqDynamicTruthPiDomainProjectionFieldFormula
    : TemplateFormula :=
  templateRepeatedForall coqDynamicTruthPiRowEnvironmentArity
    coqDynamicTruthPiDomainProjectionFormula.

Definition coqDynamicTruthPiDomainProjectionFieldProof
    : TemplateRawProof :=
  templateUniversalCloseProof coqDynamicTruthPiRowEnvironmentArity
    coqDynamicTruthPiDomainProjectionFormula
    coqDynamicTruthPiDomainProjectionProof.

Theorem coqDynamicTruthPiDomainProjectionFieldProof_derives :
  TemplateRawDerives []
    coqDynamicTruthPiDomainProjectionFieldFormula
    coqDynamicTruthPiDomainProjectionFieldProof.
Proof.
  unfold coqDynamicTruthPiDomainProjectionFieldFormula,
    coqDynamicTruthPiDomainProjectionFieldProof.
  apply templateUniversalCloseProof_derives.
  exact coqDynamicTruthPiDomainProjectionProof_derives.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier-code polynomials. *)

Definition rawCoqDynamicTruthPiDomainProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawCoqDynamicTruthPiSuccessorRowTemplateCode M
      domain lowerApplication)
    (rawDynamicTruthPiFormulaEx8Code M domain).

Definition rawDynamicTruthPiDomainProjectionCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthPiSuccessorRowCode M domain lowerApplication)
    (rawDynamicTruthPiFormulaEx8Code M domain).

Definition rawCoqDynamicTruthPiDomainProjectionFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M coqDynamicTruthPiRowEnvironmentArity
    (rawCoqDynamicTruthPiDomainProjectionCode M
      domain lowerApplication).

Definition rawDynamicTruthPiDomainProjectionFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M coqDynamicTruthPiRowEnvironmentArity
    (rawDynamicTruthPiDomainProjectionCode M
      domain lowerApplication).

(** Direct interpretation of the complete source row.  The imported Pi
    identification theorem traverses the genuine right-associated Or6 tree
    and rewrites only its domain and lower-Sigma opaque application. *)
Lemma rawDirect_coqDynamicTruthPiDomainProjection_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiDomainProjectionFormula =
  rawCoqDynamicTruthPiDomainProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold coqDynamicTruthPiDomainProjectionFormula,
    rawCoqDynamicTruthPiDomainProjectionCode.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
    templateRepeatedExists].
  rewrite (rawDirect_coqDynamicTruthPiSuccessorRowTemplate_identified
    M inputs concreteDomain concreteLowerApplication identification).
  rewrite (rawCoqDynamicTruthPiDirect_domain_identified identification).
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthPiDomainProjectionField_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiDomainProjectionFieldFormula =
  rawCoqDynamicTruthPiDomainProjectionFieldCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication identification.
  unfold coqDynamicTruthPiDomainProjectionFieldFormula,
    rawCoqDynamicTruthPiDomainProjectionFieldCode.
  rewrite rawDirectTemplateFormula_repeatedForall.
  rewrite (rawDirect_coqDynamicTruthPiDomainProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

(** The source-template module already proves that honest quotations of all
    five fixed non-binder alternatives and the existential-prefix fragments
    coincide with the numeral leaves in the native Pi row. *)
Theorem rawCoqDynamicTruthPiDomainProjectionCode_eq_native :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall domain lowerApplication,
  rawCoqDynamicTruthPiDomainProjectionCode M
    domain lowerApplication =
  rawDynamicTruthPiDomainProjectionCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthPiDomainProjectionCode,
    rawDynamicTruthPiDomainProjectionCode.
  rewrite (rawCoqDynamicTruthPiSuccessorRowTemplateCode_eq_native
    M hPA domain lowerApplication).
  reflexivity.
Qed.

(** Closing the open equality under the fixed row environment yields the
    graph-facing field equality without redoing any quotation arithmetic. *)
Theorem rawCoqDynamicTruthPiDomainProjectionFieldCode_eq_native :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall domain lowerApplication,
  rawCoqDynamicTruthPiDomainProjectionFieldCode M
    domain lowerApplication =
  rawDynamicTruthPiDomainProjectionFieldCode M
    domain lowerApplication.
Proof.
  intros M hPA domain lowerApplication.
  unfold rawCoqDynamicTruthPiDomainProjectionFieldCode,
    rawDynamicTruthPiDomainProjectionFieldCode.
  rewrite (rawCoqDynamicTruthPiDomainProjectionCode_eq_native
    M hPA domain lowerApplication).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact represented PA certificate. *)

Definition rawCoqDynamicTruthPiDomainProjectionFieldCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthPiDomainProjectionFieldProof.

Arguments rawCoqDynamicTruthPiDomainProjectionFieldCertificate
  M hPA inputs : clear implicits.

Theorem raw_codedPAProofOf_coqDynamicTruthPiDomainProjectionField :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiDomainProjectionFieldFormula)
    (rawCoqDynamicTruthPiDomainProjectionFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthPiDomainProjectionFieldCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiDomainProjectionFieldFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiDomainProjectionFieldProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthPiDomainProjectionFieldProof_derives.
Qed.

(** The direct inputs shared with the restricted existential compiler identify
    this projection before the source quotation is retargeted to the native
    row polynomial. *)
Theorem
    raw_codedPAProofOf_dynamicTruthPiDomainProjectionField_identified :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawDynamicTruthPiDomainProjectionFieldCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthPiDomainProjectionFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <- (rawCoqDynamicTruthPiDomainProjectionFieldCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite <-
    (rawDirect_coqDynamicTruthPiDomainProjectionField_identified
      M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthPiDomainProjectionField.
Qed.

End PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.
