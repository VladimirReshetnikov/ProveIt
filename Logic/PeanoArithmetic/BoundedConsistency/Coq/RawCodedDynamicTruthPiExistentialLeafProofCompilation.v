(**
  Compile the honest restricted Pi/existential row projection.

  The native Pi-falsity successor row is not the Sigma row with a renamed
  output.  It has six alternatives, and its final alternative is the
  existential case whose opaque leaf applies the preceding Sigma predicate.
  The source-template module proves only the logically honest projection

      Ex^8 (domain /\ existential-branch) -> Ex^8 existential-branch.

  This file sends that proof through the direct structural translator and
  the closed-template proof compiler.  The resulting certificate is first
  targeted at the translator's exact output and then, using
  [RawCoqDynamicTruthPiDirectTemplateIdentification], at the native domain
  and lower-Sigma application selected by a dynamic row graph.

  As for the Sigma/universal compiler, the row has thirteen ambient columns.
  The public field therefore universally closes the restricted projection
  thirteen times.  No theorem below projects the existential alternative
  from the full six-way disjunction.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateClosedProofCompilation
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafProofCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateClosedProofCompilation.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.

(** ------------------------------------------------------------------
    Direct compilation before closing the native row environment. *)

Definition rawCoqDynamicTruthPiRestrictedProjectionCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthPiRestrictedExistentialProjectionProof.

Arguments rawCoqDynamicTruthPiRestrictedProjectionCertificate
  M hPA inputs : clear implicits.

(** The direct translator preserves the source derivation exactly.  This
    endpoint does not yet rewrite either opaque output to a graph witness. *)
Theorem raw_codedPAProofOf_coqDynamicTruthPiRestrictedProjection : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiRestrictedExistentialProjectionFormula)
    (rawCoqDynamicTruthPiRestrictedProjectionCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthPiRestrictedProjectionCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiRestrictedExistentialProjectionFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiRestrictedExistentialProjectionProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthPiRestrictedExistentialProjectionProof_derives.
Qed.

(** Functionality of the concrete operation traces identifies the direct
    domain and opaque atom with the native graph outputs. *)
Theorem
    raw_codedPAProofOf_coqDynamicTruthPiRestrictedProjection_identified :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawCoqDynamicTruthPiRestrictedExistentialProjectionCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthPiRestrictedProjectionCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <- (rawDirect_coqDynamicTruthPiRestrictedProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthPiRestrictedProjection.
Qed.

(** ------------------------------------------------------------------
    Thirteen-variable closure for the actual native row environment. *)

Definition coqDynamicTruthPiRowEnvironmentArity : nat := 13.

Definition coqDynamicTruthPiRestrictedExistentialFieldFormula
    : TemplateFormula :=
  coqDynamicTruthPiClosedRestrictedProjectionFormula
    coqDynamicTruthPiRowEnvironmentArity.

Definition coqDynamicTruthPiRestrictedExistentialFieldProof
    : TemplateRawProof :=
  coqDynamicTruthPiClosedRestrictedProjectionProof
    coqDynamicTruthPiRowEnvironmentArity.

Theorem coqDynamicTruthPiRestrictedExistentialFieldProof_derives :
  TemplateRawDerives []
    coqDynamicTruthPiRestrictedExistentialFieldFormula
    coqDynamicTruthPiRestrictedExistentialFieldProof.
Proof.
  unfold coqDynamicTruthPiRestrictedExistentialFieldFormula,
    coqDynamicTruthPiRestrictedExistentialFieldProof.
  apply coqDynamicTruthPiClosedRestrictedProjectionProof_derives.
Qed.

(** Reuse the transparent repeated-universal raw-code fold established by
    the Sigma compiler.  The helper is polarity-neutral: it merely applies
    the formula-All constructor a fixed metatheoretic number of times. *)
Definition rawCoqDynamicTruthPiRestrictedExistentialFieldCode
    (M : RawPAModel) (domain lowerApplication : M) : M :=
  rawTemplateRepeatedAllCode M
    coqDynamicTruthPiRowEnvironmentArity
    (rawCoqDynamicTruthPiRestrictedExistentialProjectionCode M
      domain lowerApplication).

Theorem rawDirect_coqDynamicTruthPiRestrictedExistentialField_identified :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiRestrictedExistentialFieldFormula =
  rawCoqDynamicTruthPiRestrictedExistentialFieldCode M
    concreteDomain concreteLowerApplication.
Proof.
  intros M inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthPiRestrictedExistentialFieldFormula,
    coqDynamicTruthPiClosedRestrictedProjectionFormula,
    rawCoqDynamicTruthPiRestrictedExistentialFieldCode.
  rewrite rawDirectTemplateFormula_repeatedForall.
  rewrite (rawDirect_coqDynamicTruthPiRestrictedProjection_identified
    M inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

Definition rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawClosedTemplateProofCertificate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqDynamicTruthPiRestrictedExistentialFieldProof.

Arguments rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
  M hPA inputs : clear implicits.

Theorem raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAProofOf M
    (rawDirectTemplateFormula inputs
      coqDynamicTruthPiRestrictedExistentialFieldFormula)
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs.
  unfold rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate.
  change (RawCodedPAProofOf M
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiRestrictedExistentialFieldFormula)
    (rawClosedTemplateProofCertificate M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthPiRestrictedExistentialFieldProof)).
  apply (raw_codedPAProofOf_closedTemplate M hPA).
  exact coqDynamicTruthPiRestrictedExistentialFieldProof_derives.
Qed.

Theorem
    raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_identified
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  RawCodedPAProofOf M
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCode M
      concreteDomain concreteLowerApplication)
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  rewrite <-
    (rawDirect_coqDynamicTruthPiRestrictedExistentialField_identified
      M inputs concreteDomain concreteLowerApplication identification).
  apply raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField.
Qed.

(** ------------------------------------------------------------------
    Final graph-output seam.

    The output equality is deliberately separate from the operational
    direct-input record.  A client must show that its selected field code is
    the exact thirteen-fold closure compiled above. *)

Record RawCoqDynamicTruthPiRestrictedExistentialFieldIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (concreteDomain concreteLowerApplication fieldCode : M) : Prop := {
  rawCoqDynamicTruthPiRestrictedExistentialField_template :
    RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
      concreteDomain concreteLowerApplication;
  rawCoqDynamicTruthPiRestrictedExistentialField_output :
    fieldCode =
      rawCoqDynamicTruthPiRestrictedExistentialFieldCode M
        concreteDomain concreteLowerApplication
}.

Arguments rawCoqDynamicTruthPiRestrictedExistentialField_template
  {M inputs concreteDomain concreteLowerApplication fieldCode} _.
Arguments rawCoqDynamicTruthPiRestrictedExistentialField_output
  {M inputs concreteDomain concreteLowerApplication fieldCode} _.

Theorem
    raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_output :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication fieldCode,
  RawCoqDynamicTruthPiRestrictedExistentialFieldIdentification M inputs
    concreteDomain concreteLowerApplication fieldCode ->
  RawCodedPAProofOf M fieldCode
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication fieldCode
    identification.
  rewrite (rawCoqDynamicTruthPiRestrictedExistentialField_output
    identification).
  apply
    raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_identified.
  exact (rawCoqDynamicTruthPiRestrictedExistentialField_template
    identification).
Qed.

End PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.
