(**
  Compile the honest Rocq universal-row projection to a PA certificate.

  [RawCodedDynamicTruthUniversalLeafSourceTemplate] isolates the table-based
  source theorem: after explicitly restricting a Sigma row to its universal
  branch, the domain conjunct may be forgotten while all eight row witnesses
  are preserved.  This module sends that transparent proof through the
  direct structural translation and the closed-template certificate packer.

  Two kinds of input remain deliberately separate:

  - [RawCodedTemplateDirectStructuralInputs] contains actual represented term
    traces and direct relational opaque formula shift/open traces.  Unlike a
    [RawFormulaShiftTree], those relations remain meaningful for a genuinely
    nonstandard lower-Pi formula code.
  - [RawCoqDynamicTruthSigmaDirectTemplateIdentification] identifies the selected
    domain and opaque-application outputs with the codes chosen by a concrete
    dynamic field.  These two equalities do not imply any operation-tree or
    commutation fact.

  The native row environment has thirteen columns outside its eight
  witnesses.  The public field endpoint therefore universally closes the
  restricted projection thirteen times.  No claim is made that this formula
  is a projection from the full seven-way row disjunction; the restriction
  remains visible in every exported name and target code.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPAProvability
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateClosedProofCompilation
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateClosedProofCompilation.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.

(** ------------------------------------------------------------------
    Direct-symbol code equations.

    The source-template module states analogous equations for the older
    finite-tree translator.  Reprove the few equations needed here directly
    from the common symbol interpretation; no conversion from a relational
    opaque trace to a metatheoretic tree is involved. *)

Definition rawCoqDynamicTruthLowerPiDirectAtomTemplateCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawStructuralTemplateOpaqueCode
    (rawDirectTemplateSymbols inputs)
    coqDynamicTruthLowerPiPredicateName
    [rawTermVarCode M (rawNumeralValue M 9);
     rawTermVarCode M (rawNumeralValue M 1);
     rawTermVarCode M (rawNumeralValue M 0)].

Theorem rawDirect_coqDynamicTruthLowerPiAtomTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs coqDynamicTruthLowerPiAtomTemplate =
  rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M inputs.
Proof.
  intros M inputs. reflexivity.
Qed.

Theorem rawDirect_coqDynamicTruthSigmaUniversalLeafTemplate : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaUniversalLeafTemplate =
  rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
    (rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M inputs).
Proof.
  intros M inputs.
  unfold coqDynamicTruthSigmaUniversalLeafTemplate,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate,
    coqDynamicTruthSigmaBinderPrependTemplate,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode.
  cbn [templateRepeatedExists rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  reflexivity.
Qed.

(** These are only the two target-code equalities.  All represented opaque
    shift/open relations remain fields of [inputs] and cannot be recovered
    from this record. *)
Record RawCoqDynamicTruthSigmaDirectTemplateIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (concreteDomain concreteLowerApplication : M) : Prop := {
  rawCoqDynamicTruthSigmaDirect_domain_identified :
    rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaDomainLeafTemplate = concreteDomain;
  rawCoqDynamicTruthSigmaDirect_lowerApplication_identified :
    rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M inputs =
      concreteLowerApplication
}.

Arguments rawCoqDynamicTruthSigmaDirect_domain_identified
  {M inputs concreteDomain concreteLowerApplication} _.
Arguments rawCoqDynamicTruthSigmaDirect_lowerApplication_identified
  {M inputs concreteDomain concreteLowerApplication} _.

Theorem rawDirect_coqDynamicTruthSigmaRestrictedProjection_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaRestrictedUniversalProjectionFormula =
  rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication
    identification.
  unfold rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode.
  change (rawFormulaImpCode M
    (rawFormulaEx8Code M
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          coqDynamicTruthSigmaDomainLeafTemplate)
        (rawDirectTemplateFormula inputs
          coqDynamicTruthSigmaUniversalLeafTemplate)))
    (rawFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaUniversalLeafTemplate)) =
    rawFormulaImpCode M
      (rawFormulaEx8Code M
        (rawFormulaAndCode M concreteDomain
          (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
            concreteLowerApplication)))
      (rawFormulaEx8Code M
        (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M
          concreteLowerApplication))).
  rewrite !rawDirect_coqDynamicTruthSigmaUniversalLeafTemplate.
  rewrite (rawCoqDynamicTruthSigmaDirect_domain_identified identification).
  rewrite (rawCoqDynamicTruthSigmaDirect_lowerApplication_identified
    identification).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Direct compilation of the unrestricted-free-variable proof core. *)

Definition rawCoqDynamicTruthSigmaRestrictedProjectionCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthSigmaRestrictedUniversalProjectionProof.

Arguments rawCoqDynamicTruthSigmaRestrictedProjectionCertificate
  M hPA inputs : clear implicits.

(** This theorem uses only the operational structural inputs.  It is the
    compiler's exact endpoint before any client-specific code equalities are
    applied. *)
Theorem raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedProjection : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaRestrictedUniversalProjectionFormula)
    (rawCoqDynamicTruthSigmaRestrictedProjectionCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthSigmaRestrictedProjectionCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaRestrictedUniversalProjectionFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaRestrictedUniversalProjectionProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthSigmaRestrictedUniversalProjectionProof_derives.
Qed.

(** Once the two code outputs are identified, the very same certificate is
    targeted at the explicit raw polynomial used by the restricted field. *)
Theorem raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedProjection_identified :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthSigmaRestrictedProjectionCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <- (rawDirect_coqDynamicTruthSigmaRestrictedProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedProjection.
Qed.

(** ------------------------------------------------------------------
    Thirteen-variable closure for the actual row environment. *)

Definition coqDynamicTruthSigmaRowEnvironmentArity : nat := 13.

Definition coqDynamicTruthSigmaRestrictedUniversalFieldFormula
    : TemplateFormula :=
  coqDynamicTruthSigmaClosedRestrictedProjectionFormula
    coqDynamicTruthSigmaRowEnvironmentArity.

Definition coqDynamicTruthSigmaRestrictedUniversalFieldProof
    : TemplateRawProof :=
  coqDynamicTruthSigmaClosedRestrictedProjectionProof
    coqDynamicTruthSigmaRowEnvironmentArity.

Theorem coqDynamicTruthSigmaRestrictedUniversalFieldProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaRestrictedUniversalFieldFormula
    coqDynamicTruthSigmaRestrictedUniversalFieldProof.
Proof.
  unfold coqDynamicTruthSigmaRestrictedUniversalFieldFormula,
    coqDynamicTruthSigmaRestrictedUniversalFieldProof.
  apply coqDynamicTruthSigmaClosedRestrictedProjectionProof_derives.
Qed.

Fixpoint rawTemplateRepeatedAllCode
    (M : RawPAModel) (binderCount : nat) (bodyCode : M) : M :=
  match binderCount with
  | 0 => bodyCode
  | S smaller =>
      rawFormulaAllCode M
        (rawTemplateRepeatedAllCode M smaller bodyCode)
  end.

Arguments rawTemplateRepeatedAllCode M binderCount bodyCode
  : clear implicits.

Definition rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M
    coqDynamicTruthSigmaRowEnvironmentArity
    (rawCoqDynamicTruthSigmaRestrictedUniversalProjectionCode M
      domain lowerApplication).

Lemma rawDirectTemplateFormula_repeatedForall : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    binderCount body,
  rawDirectTemplateFormula inputs
    (templateRepeatedForall binderCount body) =
  rawTemplateRepeatedAllCode M binderCount
    (rawDirectTemplateFormula inputs body).
Proof.
  intros M inputs binderCount.
  induction binderCount as [|smaller ih]; intro body;
    cbn [templateRepeatedForall rawTemplateRepeatedAllCode].
  - reflexivity.
  - change (rawFormulaAllCode M
      (rawDirectTemplateFormula inputs
        (templateRepeatedForall smaller body)) =
      rawFormulaAllCode M
        (rawTemplateRepeatedAllCode M smaller
          (rawDirectTemplateFormula inputs body))).
    now rewrite ih.
Qed.

Theorem rawDirect_coqDynamicTruthSigmaRestrictedUniversalField_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaRestrictedUniversalFieldFormula =
  rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthSigmaRestrictedUniversalFieldFormula,
    coqDynamicTruthSigmaClosedRestrictedProjectionFormula,
    rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode.
  rewrite rawDirectTemplateFormula_repeatedForall.
  rewrite (rawDirect_coqDynamicTruthSigmaRestrictedProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

Definition rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthSigmaRestrictedUniversalFieldProof.

Arguments rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
  M hPA inputs : clear implicits.

Theorem raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaRestrictedUniversalFieldFormula)
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaRestrictedUniversalFieldFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaRestrictedUniversalFieldProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthSigmaRestrictedUniversalFieldProof_derives.
Qed.

Theorem raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_identified :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <-
    (rawDirect_coqDynamicTruthSigmaRestrictedUniversalField_identified
      M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField.
Qed.

(** ------------------------------------------------------------------
    Final field-output seam.

    A graph-producing client commonly has an output [fieldCode] in addition
    to its domain and lower-application outputs.  The following record states
    exactly the three equalities needed to retarget the certificate. *)

Record RawCoqDynamicTruthSigmaRestrictedUniversalFieldIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (concreteDomain concreteLowerApplication fieldCode : M) : Prop := {
  rawCoqDynamicTruthSigmaRestrictedUniversalField_template :
    RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
      concreteDomain concreteLowerApplication;
  rawCoqDynamicTruthSigmaRestrictedUniversalField_output :
    fieldCode =
      rawCoqDynamicTruthSigmaRestrictedUniversalFieldCode M
        concreteDomain concreteLowerApplication
}.

Arguments rawCoqDynamicTruthSigmaRestrictedUniversalField_template
  {M inputs concreteDomain concreteLowerApplication fieldCode} _.
Arguments rawCoqDynamicTruthSigmaRestrictedUniversalField_output
  {M inputs concreteDomain concreteLowerApplication fieldCode} _.

Theorem raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_output :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication fieldCode,
  RawCoqDynamicTruthSigmaRestrictedUniversalFieldIdentification M inputs
    concreteDomain concreteLowerApplication fieldCode ->
  RawCodedPAProofOf M fieldCode
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication fieldCode
    identification.
  rewrite (rawCoqDynamicTruthSigmaRestrictedUniversalField_output
    identification).
  apply
    raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_identified.
  exact (rawCoqDynamicTruthSigmaRestrictedUniversalField_template
    identification).
Qed.

End PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
