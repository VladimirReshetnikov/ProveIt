(**
  Compile closed template derivations into ordinary PA certificates.

  [RawCodedTemplateProofCompiler] deliberately stops at a local proof in an
  arbitrary translated context.  For a closed template derivation that
  context is the empty raw list, so it can be paired with the existing empty
  witnessed-PA-axiom traversal.  This module records that final, reusable
  packaging step and specializes it to the universal-leaf projection schema.

  No opaque formula is treated as a PA axiom: opaque applications may occur
  inside the compiled theorem, but the certificate's witnessed axiom list is
  literally empty.
*)

From Stdlib Require Import List.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedPAProvability
  RawCodedRestrictedProofStandardAdequacy RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler RawCodedTemplateProjectionSchemas.

Module PABoundedRawCodedTemplateClosedProofCompilation.

Import ListNotations.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProjectionSchemas.

(** Exact three-field certificate with empty witness list and the proof root
    emitted by the structural template compiler. *)
Definition rawClosedTemplateProofCertificate
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (derivation : TemplateRawProof) : M :=
  rawCodeList3 M (rawNumeralValue M 0) (raw_zero M)
    (rawTemplateProofCode translation derivation).

Arguments rawClosedTemplateProofCertificate
  M translation derivation : clear implicits.

(** Empty template contexts use the standard empty PA-axiom witness
    traversal.  Reprove this tiny reduction locally to avoid coupling the
    generic compiler bridge to any particular proof-leaf module. *)
Lemma raw_closedTemplate_axiomContext_empty : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAAxiomWitnessContext M (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
  cbn [rawQuotedPAAxiomWitnessList rawQuotedContextCode
    rawListCode map] in h.
  exact h.
Qed.

(** Any honestly validated closed template is therefore an ordinary
    represented PA proof.  The only PA-axiom traversal used here is the
    canonical empty traversal. *)
Theorem raw_codedPAProofOf_closedTemplate : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (translation : RawCodedTemplateTranslation M)
      conclusion derivation,
  TemplateRawDerives [] conclusion derivation ->
  RawCodedPAProofOf M
    (rawTemplateFormula translation conclusion)
    (rawClosedTemplateProofCertificate M translation derivation).
Proof.
  intros M hPA translation conclusion derivation
    (hvalid & hcontext & hconclusion).
  pose proof (raw_templateProof_localProof M hPA translation
    derivation hvalid) as hlocal.
  rewrite hcontext, hconclusion in hlocal.
  cbn [rawTemplateContextCode] in hlocal.
  destruct hlocal as [hcoverage hendpoint].
  exists (raw_zero M),
    (rawTemplateProofCode translation derivation), (raw_zero M).
  split.
  - unfold rawClosedTemplateProofCertificate. reflexivity.
  - repeat split.
    + exact (raw_closedTemplate_axiomContext_empty M hPA).
    + exact hcoverage.
    + exact hendpoint.
Qed.

(** Give a stable name to the exact source formula compiled by the
    universal-leaf proof. *)
Definition templateUniversalLeafProjectionFormula
    (boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula
      : TemplateFormula) : TemplateFormula :=
  templateRepeatedForall 2
    (tfImp
      (templateRepeatedExists 5
        (templateRightConjunction
          [boundFormula; freeFormula; codeFormula; subformulaFormula;
            universalFormula; rankFormula; negationFormula]
          leafFormula))
      (templateRepeatedExists 5
        (templateRightConjunction
          [boundFormula; freeFormula; codeFormula; negationFormula]
          leafFormula))).

Definition rawUniversalLeafProjectionProofCertificate
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula
      : TemplateFormula) : M :=
  rawClosedTemplateProofCertificate M translation
    (templateUniversalLeafProjectionProof
      boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula).

Arguments rawUniversalLeafProjectionProofCertificate
  M translation boundFormula freeFormula codeFormula subformulaFormula
    universalFormula rankFormula negationFormula leafFormula
    : clear implicits.

(** Compiler-facing exact endpoint for the dynamic universal-leaf logical
    core.  A later concrete specialization only has to identify the eight
    translated leaves with its represented dynamic syntax. *)
Theorem raw_codedPAProofOf_universalLeafProjectionTemplate : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (translation : RawCodedTemplateTranslation M)
      boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula,
  RawCodedPAProofOf M
    (rawTemplateFormula translation
      (templateUniversalLeafProjectionFormula
        boundFormula freeFormula codeFormula subformulaFormula
        universalFormula rankFormula negationFormula leafFormula))
    (rawUniversalLeafProjectionProofCertificate M translation
      boundFormula freeFormula codeFormula subformulaFormula
      universalFormula rankFormula negationFormula leafFormula).
Proof.
  intros M hPA translation boundFormula freeFormula codeFormula
    subformulaFormula universalFormula rankFormula negationFormula
    leafFormula.
  eapply (raw_codedPAProofOf_closedTemplate M hPA translation).
  exact (templateUniversalLeafProjectionProof_derives
    boundFormula freeFormula codeFormula subformulaFormula
    universalFormula rankFormula negationFormula leafFormula).
Qed.

End PABoundedRawCodedTemplateClosedProofCompilation.
