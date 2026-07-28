(**
  The exact carrier syntax for the positive single-substitution field.

  A positive master index is presented by a predecessor [p], while its
  current truth predicates live at [S p].  The eventual output-first graph
  must apply those carried Sigma/Pi predicates to the seven operation
  parameters

    replacement, source, target,
    source assignment code/step, target assignment code/step

  and then assemble the literal universally closed Tarski transport law.
  This module isolates that syntax layer.  It supplies a transparent formula
  polynomial, exact quotation, and ordinary PA proofs for every externally
  fixed standard level.  It intentionally does not turn the standard proof
  family into a proof compiler at an arbitrary, possibly nonstandard,
  carrier index; the orbit transform and that compiler belong to the later
  positive graph.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFixedLevelTruthOperationTarskiSubstitutionPositive
  RawCodedDynamicTruthNativeLocalPositiveGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

(** ------------------------------------------------------------------
    Exact native target formula.

    The variables before closure are exactly the variables used by
    [fixedLevelFormulaSubstitutionTarskiStepFormula]:

      #0 replacement, #1 source, #2 target,
      #3/#4 source assignment, #5/#6 target assignment. *)

Definition dynamicTruthNativeSubstitutionAll7 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll body)))))).

Definition dynamicTruthNativeSubstitutionSourceAdmissibleFormula
    (sigmaDomain piDomain : formula) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt (tVar 1))
    (pAnd
      (codedAssignmentDefinedThroughTermAt
        (tVar 3) (tVar 4) (tVar 1))
      (pOr sigmaDomain piDomain)).

Definition dynamicTruthNativeSubstitutionCertificateTransportFormula
    (sourceSigma targetSigma sourcePi targetPi : formula) : formula :=
  pAnd
    (operationTransportIff sourceSigma targetSigma)
    (operationTransportIff sourcePi targetPi).

Definition dynamicTruthNativeSubstitutionStepCarrierFormula
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : formula)
    : formula :=
  pImp
    (operationTransportAnd5
      (codedFormulaSingleSubstitutionTermAt
        (tVar 0) (tVar 1) (tVar 2))
      (codedFormulaSubstitutionAssignmentRelationTermAt
        (tVar 0) (tVar 1) (tVar 3) (tVar 4) (tVar 5) (tVar 6))
      (dynamicTruthNativeSubstitutionSourceAdmissibleFormula
        sigmaDomain piDomain)
      (codedFormulaTargetAdmissibilityDataTermAt
        (tVar 2) (tVar 5) (tVar 6))
      (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2)))
    (dynamicTruthNativeSubstitutionCertificateTransportFormula
      sourceSigma targetSigma sourcePi targetPi).

Definition dynamicTruthNativeSubstitutionFieldCarrierFormula
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : formula)
    : formula :=
  dynamicTruthNativeSubstitutionAll7
    (dynamicTruthNativeSubstitutionStepCarrierFormula
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).

Lemma dynamicTruthNativeSubstitutionStepCarrierFormula_fixedLevel :
    forall level,
  dynamicTruthNativeSubstitutionStepCarrierFormula
    (fixedLevelSigmaDomainTermAt level (tVar 1))
    (fixedLevelPiDomainTermAt level (tVar 1))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 1) (tVar 3) (tVar 4))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 2) (tVar 5) (tVar 6))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 1) (tVar 3) (tVar 4))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 2) (tVar 5) (tVar 6)) =
  fixedLevelFormulaSubstitutionTarskiStepFormula level.
Proof.
  intro level.
  unfold dynamicTruthNativeSubstitutionStepCarrierFormula,
    dynamicTruthNativeSubstitutionSourceAdmissibleFormula,
    dynamicTruthNativeSubstitutionCertificateTransportFormula,
    fixedLevelFormulaSubstitutionTarskiStepFormula,
    fixedLevelFormulaSubstitutionTarskiStepTermAt,
    fixedLevelFormulaSubstitutionTransportReadyTermAt,
    fixedLevelTruthCertificateTransportTermAt,
    fixedLevelTruthAdmissibleTermAt.
  reflexivity.
Qed.

(** Unlike [Formula.sealPA], this carrier construction closes exactly the
    seven displayed operation parameters.  That literal shape is important
    when a nonstandard formula code is assembled constructor by constructor. *)
Definition dynamicTruthNativeSubstitutionFixedLevelFieldFormula
    (level : nat) : formula :=
  dynamicTruthNativeSubstitutionAll7
    (fixedLevelFormulaSubstitutionTarskiStepFormula level).

Lemma dynamicTruthNativeSubstitutionFieldCarrierFormula_fixedLevel :
    forall level,
  dynamicTruthNativeSubstitutionFieldCarrierFormula
    (fixedLevelSigmaDomainTermAt level (tVar 1))
    (fixedLevelPiDomainTermAt level (tVar 1))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 1) (tVar 3) (tVar 4))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 2) (tVar 5) (tVar 6))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 1) (tVar 3) (tVar 4))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 2) (tVar 5) (tVar 6)) =
  dynamicTruthNativeSubstitutionFixedLevelFieldFormula level.
Proof.
  intro level.
  unfold dynamicTruthNativeSubstitutionFieldCarrierFormula,
    dynamicTruthNativeSubstitutionFixedLevelFieldFormula.
  rewrite dynamicTruthNativeSubstitutionStepCarrierFormula_fixedLevel.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier code polynomial. *)

Definition dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm
    (a b c d e : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm a
    (dynamicTruthLocalFormulaAndCodeTerm b
      (dynamicTruthLocalFormulaAndCodeTerm c
        (dynamicTruthLocalFormulaAndCodeTerm d e))).

Definition dynamicTruthNativeSubstitutionFormulaIffCodeTerm
    (left right : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm left right)
    (dynamicTruthLocalFormulaImpCodeTerm right left).

Definition dynamicTruthNativeSubstitutionFormulaAll7CodeTerm
    (body : term) : term :=
  dynamicTruthLocalFormulaAllCodeTerm
    (dynamicTruthLocalFormulaAllCodeTerm
      (dynamicTruthLocalFormulaAllCodeTerm
        (dynamicTruthLocalFormulaAllCodeTerm
          (dynamicTruthLocalFormulaAllCodeTerm
            (dynamicTruthLocalFormulaAllCodeTerm
              (dynamicTruthLocalFormulaAllCodeTerm body)))))).

Definition dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm
    (sigmaDomain piDomain : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (Term.numeral
      (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 1))))
    (dynamicTruthLocalFormulaAndCodeTerm
      (Term.numeral
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 3) (tVar 4) (tVar 1))))
      (dynamicTruthLocalFormulaOrCodeTerm sigmaDomain piDomain)).

Definition dynamicTruthNativeSubstitutionFieldCodeTerm
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : term)
    : term :=
  dynamicTruthNativeSubstitutionFormulaAll7CodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm
      (dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm
        (Term.numeral
          (formulaCode
            (codedFormulaSingleSubstitutionTermAt
              (tVar 0) (tVar 1) (tVar 2))))
        (Term.numeral
          (formulaCode
            (codedFormulaSubstitutionAssignmentRelationTermAt
              (tVar 0) (tVar 1) (tVar 3) (tVar 4)
              (tVar 5) (tVar 6))))
        (dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm
          sigmaDomain piDomain)
        (Term.numeral
          (formulaCode
            (codedFormulaTargetAdmissibilityDataTermAt
              (tVar 2) (tVar 5) (tVar 6))))
        (Term.numeral
          (formulaCode
            (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2)))))
      (dynamicTruthLocalFormulaAndCodeTerm
        (dynamicTruthNativeSubstitutionFormulaIffCodeTerm
          sourceSigma targetSigma)
        (dynamicTruthNativeSubstitutionFormulaIffCodeTerm
          sourcePi targetPi))).

Definition rawDynamicTruthNativeSubstitutionFormulaAnd5Code
    (M : RawPAModel) (a b c d e : M) : M :=
  rawFormulaAndCode M a
    (rawFormulaAndCode M b
      (rawFormulaAndCode M c (rawFormulaAndCode M d e))).

Definition rawDynamicTruthNativeSubstitutionFormulaIffCode
    (M : RawPAModel) (left right : M) : M :=
  rawFormulaAndCode M
    (rawFormulaImpCode M left right)
    (rawFormulaImpCode M right left).

Definition rawDynamicTruthNativeSubstitutionFormulaAll7Code
    (M : RawPAModel) (body : M) : M :=
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawFormulaAllCode M body)))))).

Definition rawDynamicTruthNativeSubstitutionSourceAdmissibleCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawFormulaAndCode M
    (rawNumeralValue M
      (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 1))))
    (rawFormulaAndCode M
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 3) (tVar 4) (tVar 1))))
      (rawFormulaOrCode M sigmaDomain piDomain)).

Definition rawDynamicTruthNativeSubstitutionFieldCode
    (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M) : M :=
  rawDynamicTruthNativeSubstitutionFormulaAll7Code M
    (rawFormulaImpCode M
      (rawDynamicTruthNativeSubstitutionFormulaAnd5Code M
        (rawNumeralValue M
          (formulaCode
            (codedFormulaSingleSubstitutionTermAt
              (tVar 0) (tVar 1) (tVar 2))))
        (rawNumeralValue M
          (formulaCode
            (codedFormulaSubstitutionAssignmentRelationTermAt
              (tVar 0) (tVar 1) (tVar 3) (tVar 4)
              (tVar 5) (tVar 6))))
        (rawDynamicTruthNativeSubstitutionSourceAdmissibleCode M
          sigmaDomain piDomain)
        (rawNumeralValue M
          (formulaCode
            (codedFormulaTargetAdmissibilityDataTermAt
              (tVar 2) (tVar 5) (tVar 6))))
        (rawNumeralValue M
          (formulaCode
            (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2)))))
      (rawFormulaAndCode M
        (rawDynamicTruthNativeSubstitutionFormulaIffCode M
          sourceSigma targetSigma)
        (rawDynamicTruthNativeSubstitutionFormulaIffCode M
          sourcePi targetPi))).

Lemma raw_eval_dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm : forall
    (M : RawPAModel) e a b c d f,
  raw_term_eval M e
    (dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm a b c d f) =
  rawDynamicTruthNativeSubstitutionFormulaAnd5Code M
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e d)
    (raw_term_eval M e f).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm,
    rawDynamicTruthNativeSubstitutionFormulaAnd5Code.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeSubstitutionFormulaIffCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e
    (dynamicTruthNativeSubstitutionFormulaIffCodeTerm left right) =
  rawDynamicTruthNativeSubstitutionFormulaIffCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionFormulaIffCodeTerm,
    rawDynamicTruthNativeSubstitutionFormulaIffCode.
  rewrite raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthLocalFormulaImpCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeSubstitutionFormulaAll7CodeTerm : forall
    (M : RawPAModel) e body,
  raw_term_eval M e
    (dynamicTruthNativeSubstitutionFormulaAll7CodeTerm body) =
  rawDynamicTruthNativeSubstitutionFormulaAll7Code M
    (raw_term_eval M e body).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionFormulaAll7CodeTerm,
    rawDynamicTruthNativeSubstitutionFormulaAll7Code.
  rewrite !raw_eval_dynamicTruthLocalFormulaAllCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm :
    forall (M : RawPAModel) e sigmaDomain piDomain,
  raw_term_eval M e
    (dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm
      sigmaDomain piDomain) =
  rawDynamicTruthNativeSubstitutionSourceAdmissibleCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm,
    rawDynamicTruthNativeSubstitutionSourceAdmissibleCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    raw_eval_dynamicTruthLocalFormulaOrCodeTerm,
    !raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeSubstitutionFieldCodeTerm : forall
    (M : RawPAModel) e
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  raw_term_eval M e
    (dynamicTruthNativeSubstitutionFieldCodeTerm
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi) =
  rawDynamicTruthNativeSubstitutionFieldCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
    (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionFieldCodeTerm,
    rawDynamicTruthNativeSubstitutionFieldCode.
  rewrite raw_eval_dynamicTruthNativeSubstitutionFormulaAll7CodeTerm,
    raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthNativeSubstitutionFormulaAnd5CodeTerm,
    raw_eval_dynamicTruthNativeSubstitutionSourceAdmissibleCodeTerm,
    raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthNativeSubstitutionFormulaIffCodeTerm,
    !raw_term_eval_numeral.
  reflexivity.
Qed.

Definition dynamicTruthNativeSubstitutionFieldCodeTermAt
    (output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      : term) : formula :=
  pEq output
    (dynamicTruthNativeSubstitutionFieldCodeTerm
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).

Lemma raw_sat_dynamicTruthNativeSubstitutionFieldCodeTermAt_iff : forall
    (M : RawPAModel) e
      output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  raw_formula_sat M e
    (dynamicTruthNativeSubstitutionFieldCodeTermAt
      output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
  <->
  raw_term_eval M e output =
    rawDynamicTruthNativeSubstitutionFieldCode M
      (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
      (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
      (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi).
Proof.
  intros.
  unfold dynamicTruthNativeSubstitutionFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthNativeSubstitutionFieldCodeTerm
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi) <->
    raw_term_eval M e output =
      rawDynamicTruthNativeSubstitutionFieldCode M
        (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
        (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
        (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi)).
  rewrite raw_eval_dynamicTruthNativeSubstitutionFieldCodeTerm.
  reflexivity.
Qed.

(** Quotation is structural.  The six standard side-condition fragments are
    explicitly rewritten to their represented numeral codes; the carried
    domain and truth applications remain the six polynomial inputs. *)
Theorem rawDynamicTruthNativeSubstitutionFieldCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  rawDynamicTruthNativeSubstitutionFieldCode M
    (rawQuotedFormulaCode M sigmaDomain)
    (rawQuotedFormulaCode M piDomain)
    (rawQuotedFormulaCode M sourceSigma)
    (rawQuotedFormulaCode M targetSigma)
    (rawQuotedFormulaCode M sourcePi)
    (rawQuotedFormulaCode M targetPi) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeSubstitutionFieldCarrierFormula
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
  unfold rawDynamicTruthNativeSubstitutionFieldCode,
    rawDynamicTruthNativeSubstitutionFormulaAll7Code,
    rawDynamicTruthNativeSubstitutionFormulaAnd5Code,
    rawDynamicTruthNativeSubstitutionFormulaIffCode,
    rawDynamicTruthNativeSubstitutionSourceAdmissibleCode,
    dynamicTruthNativeSubstitutionFieldCarrierFormula,
    dynamicTruthNativeSubstitutionAll7,
    dynamicTruthNativeSubstitutionStepCarrierFormula,
    dynamicTruthNativeSubstitutionCertificateTransportFormula,
    dynamicTruthNativeSubstitutionSourceAdmissibleFormula,
    operationTransportAnd5, operationTransportIff.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaSingleSubstitutionTermAt
      (tVar 0) (tVar 1) (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaSubstitutionAssignmentRelationTermAt
      (tVar 0) (tVar 1) (tVar 3) (tVar 4) (tVar 5) (tVar 6))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 1))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt
      (tVar 3) (tVar 4) (tVar 1))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaTargetAdmissibilityDataTermAt
      (tVar 2) (tVar 5) (tVar 6))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2))).
  reflexivity.
Qed.

(** At standard predecessor [p] the current carried truth level is [S p]. *)
Corollary
    rawDynamicTruthNativeSubstitutionFieldCode_quoted_successor_level :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthNativeSubstitutionFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 1)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 1)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 1) (tVar 3) (tVar 4)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 2) (tVar 5) (tVar 6)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 1) (tVar 3) (tVar 4)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 2) (tVar 5) (tVar 6))) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeSubstitutionFixedLevelFieldFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeSubstitutionFieldCode_quoted by exact hPA.
  rewrite dynamicTruthNativeSubstitutionFieldCarrierFormula_fixedLevel.
  reflexivity.
Qed.

Lemma dynamicTruthNativeSubstitutionFixedLevelFieldFormula_closeN :
    forall level,
  dynamicTruthNativeSubstitutionFixedLevelFieldFormula level =
  Formula.closeN 7 (fixedLevelFormulaSubstitutionTarskiStepFormula level).
Proof.
  intro level.
  unfold dynamicTruthNativeSubstitutionFixedLevelFieldFormula,
    dynamicTruthNativeSubstitutionAll7.
  reflexivity.
Qed.

Theorem PA_proves_dynamicTruthNativeSubstitutionFixedLevelFieldFormula :
    forall level,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthNativeSubstitutionFixedLevelFieldFormula level).
Proof.
  intro level.
  rewrite dynamicTruthNativeSubstitutionFixedLevelFieldFormula_closeN.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - exact (PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula level).
Qed.

Theorem raw_dynamicTruthNativeSubstitutionFixedLevelField_quoted_proof :
  forall (M : RawPAModel), RawPASatisfies M -> forall level,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M
        (dynamicTruthNativeSubstitutionFixedLevelFieldFormula level))
      certificate.
Proof.
  intros M hPA level.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthNativeSubstitutionFixedLevelFieldFormula level)
    (PA_proves_dynamicTruthNativeSubstitutionFixedLevelFieldFormula level))
    as [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

Corollary rawDynamicTruthNativeSubstitutionFieldCode_standard_proof :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeSubstitutionFieldCode M
        (rawQuotedFormulaCode M
          (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 1)))
        (rawQuotedFormulaCode M
          (fixedLevelPiDomainTermAt (S predecessor) (tVar 1)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
            (tVar 1) (tVar 3) (tVar 4)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
            (tVar 2) (tVar 5) (tVar 6)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S predecessor)
            (tVar 1) (tVar 3) (tVar 4)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S predecessor)
            (tVar 2) (tVar 5) (tVar 6))))
      certificate.
Proof.
  intros M hPA predecessor.
  rewrite
    rawDynamicTruthNativeSubstitutionFieldCode_quoted_successor_level
    by exact hPA.
  exact (raw_dynamicTruthNativeSubstitutionFixedLevelField_quoted_proof
    M hPA (S predecessor)).
Qed.

End PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
