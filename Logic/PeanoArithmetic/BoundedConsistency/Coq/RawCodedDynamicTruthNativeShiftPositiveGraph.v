(**
  The carrier-indexed positive formula-shift-invariance field.

  At predecessor [p], the positive master coordinate is the closed native
  formula-shift Tarski law for the current truth level [S p].  The graph
  selects the genuine paired global Sigma/Pi formula codes from the orbit at
  [S p], applies them to the source and target formula/assignment triples,
  instantiates the current-level source domains, retains the represented
  formula-shift and assignment-shift relations literally, and builds the
  exact eight-variable universal closure used by the fixed-level field.

  All exact graph semantics is law free.  PA is used only for syntax
  totality, orbit adequacy, and represented proofs of externally fixed
  standard instances.  No semantic-validity-to-proof inference occurs; the
  remaining arbitrary-carrier proof compiler is isolated at the end.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    Exact native target formula.

    The free-variable layout before closing is exactly the fixed operation
    law's layout:

      #0 cutoff, #1 amount, #2 source, #3 target,
      #4 source assignment code, #5 source assignment step,
      #6 target assignment code, #7 target assignment step. *)

Definition dynamicTruthNativeShiftSourceAdmissibleFormula
    (sigmaDomain piDomain : formula) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))
    (pAnd
      (codedAssignmentDefinedThroughTermAt
        (tVar 4) (tVar 5) (tVar 2))
      (pOr sigmaDomain piDomain)).

Definition dynamicTruthNativeShiftCertificateTransportFormula
    (sourceSigma targetSigma sourcePi targetPi : formula) : formula :=
  pAnd
    (operationTransportIff sourceSigma targetSigma)
    (operationTransportIff sourcePi targetPi).

Definition dynamicTruthNativeShiftStepCarrierFormula
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : formula)
    : formula :=
  pImp
    (operationTransportAnd5
      (codedFormulaShiftTermAt (tVar 0) (tVar 1) (tVar 2) (tVar 3))
      (codedFormulaShiftAssignmentRelationTermAt
        (tVar 0) (tVar 1) (tVar 2)
        (tVar 4) (tVar 5) (tVar 6) (tVar 7))
      (dynamicTruthNativeShiftSourceAdmissibleFormula
        sigmaDomain piDomain)
      (codedFormulaTargetAdmissibilityDataTermAt
        (tVar 3) (tVar 6) (tVar 7))
      (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3)))
    (dynamicTruthNativeShiftCertificateTransportFormula
      sourceSigma targetSigma sourcePi targetPi).

Definition dynamicTruthNativeShiftFieldCarrierFormula
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : formula)
    : formula :=
  operationTarskiPositiveAll8
    (dynamicTruthNativeShiftStepCarrierFormula
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).

Lemma dynamicTruthNativeShiftStepCarrierFormula_fixedLevel : forall level,
  dynamicTruthNativeShiftStepCarrierFormula
    (fixedLevelSigmaDomainTermAt level (tVar 2))
    (fixedLevelPiDomainTermAt level (tVar 2))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 2) (tVar 4) (tVar 5))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 3) (tVar 6) (tVar 7))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 2) (tVar 4) (tVar 5))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 3) (tVar 6) (tVar 7)) =
  fixedLevelFormulaShiftTarskiStepFormula level.
Proof.
  intro level.
  unfold dynamicTruthNativeShiftStepCarrierFormula,
    dynamicTruthNativeShiftSourceAdmissibleFormula,
    dynamicTruthNativeShiftCertificateTransportFormula,
    fixedLevelFormulaShiftTarskiStepFormula,
    fixedLevelFormulaShiftTarskiStepTermAt,
    fixedLevelFormulaShiftTransportReadyTermAt,
    fixedLevelTruthCertificateTransportTermAt,
    fixedLevelTruthAdmissibleTermAt.
  reflexivity.
Qed.

(** The positive carrier uses the literal eight-variable closure.  PAHF's
    generic [sealPA] closes [Formula.bound] variables; that bound is a safe
    structural over-approximation and can add redundant quantifiers.  For a
    carrier-built formula its value can itself be nonstandard, whereas the
    operation interface has exactly the eight displayed parameters. *)
Definition dynamicTruthNativeShiftFixedLevelFieldFormula
    (level : nat) : formula :=
  operationTarskiPositiveAll8
    (fixedLevelFormulaShiftTarskiStepFormula level).

Lemma dynamicTruthNativeShiftFieldCarrierFormula_fixedLevel : forall level,
  dynamicTruthNativeShiftFieldCarrierFormula
    (fixedLevelSigmaDomainTermAt level (tVar 2))
    (fixedLevelPiDomainTermAt level (tVar 2))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 2) (tVar 4) (tVar 5))
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 3) (tVar 6) (tVar 7))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 2) (tVar 4) (tVar 5))
    (fixedLevelPiFalsityCertificateTermAt level
      (tVar 3) (tVar 6) (tVar 7)) =
  dynamicTruthNativeShiftFixedLevelFieldFormula level.
Proof.
  intro level.
  unfold dynamicTruthNativeShiftFieldCarrierFormula,
    dynamicTruthNativeShiftFixedLevelFieldFormula.
  rewrite dynamicTruthNativeShiftStepCarrierFormula_fixedLevel.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Represented applications in the eight-variable shift layout.

    Sequential one-variable substitution needs already-shifted replacement
    terms.  For the source triple [#2,#4,#5] these are [#4,#5,#5]; for the
    target triple [#3,#6,#7] they are [#5,#7,#7]. *)

Definition dynamicTruthNativeShiftSourceFirstReplacement : term := tVar 4.
Definition dynamicTruthNativeShiftSourceSecondReplacement : term := tVar 5.
Definition dynamicTruthNativeShiftSourceThirdReplacement : term := tVar 5.

Definition dynamicTruthNativeShiftTargetFirstReplacement : term := tVar 5.
Definition dynamicTruthNativeShiftTargetSecondReplacement : term := tVar 7.
Definition dynamicTruthNativeShiftTargetThirdReplacement : term := tVar 7.

Definition dynamicTruthNativeShiftApplicationTermAt
    (firstReplacement secondReplacement thirdReplacement : term)
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        (Term.numeral (termCode firstReplacement))
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral (termCode secondReplacement))
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral (termCode thirdReplacement))
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthNativeShiftApplication (M : RawPAModel)
    (firstReplacement secondReplacement thirdReplacement : term)
    (input output : M) : Prop :=
  exists firstResult secondResult : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode firstReplacement))
      input firstResult /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode secondReplacement))
      firstResult secondResult /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode thirdReplacement))
      secondResult output.

Arguments RawDynamicTruthNativeShiftApplication
  M firstReplacement secondReplacement thirdReplacement input output
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff : forall
    (M : RawPAModel) e firstReplacement secondReplacement thirdReplacement
      input output,
  raw_formula_sat M e
    (dynamicTruthNativeShiftApplicationTermAt
      firstReplacement secondReplacement thirdReplacement input output) <->
  RawDynamicTruthNativeShiftApplication M
    firstReplacement secondReplacement thirdReplacement
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros.
  unfold dynamicTruthNativeShiftApplicationTermAt,
    RawDynamicTruthNativeShiftApplication.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_dynamicTruthNativeShiftApplication_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      firstReplacement secondReplacement thirdReplacement input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthNativeShiftApplication M
      firstReplacement secondReplacement thirdReplacement input output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA firstReplacement secondReplacement thirdReplacement
    input hinput.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    input hinput
    (rawNumeralValue M (termCode firstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      firstReplacement)
    (rawNumeralValue M (termCode secondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      secondReplacement)
    (rawNumeralValue M (termCode thirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      thirdReplacement)) as
    (firstResult & secondResult & output & hfirst & _hfirstAdequate &
     hsecond & _hsecondAdequate & hthird & houtputAdequate).
  exists output. split; [|exact houtputAdequate].
  exists firstResult, secondResult. repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier code polynomial. *)

Definition dynamicTruthNativeShiftFormulaAnd5CodeTerm
    (a b c d e : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm a
    (dynamicTruthLocalFormulaAndCodeTerm b
      (dynamicTruthLocalFormulaAndCodeTerm c
        (dynamicTruthLocalFormulaAndCodeTerm d e))).

Definition dynamicTruthNativeShiftFormulaIffCodeTerm
    (left right : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm left right)
    (dynamicTruthLocalFormulaImpCodeTerm right left).

Definition dynamicTruthNativeShiftFormulaAll8CodeTerm (body : term) : term :=
  dynamicTruthLocalFormulaAllCodeTerm
    (dynamicTruthLocalFormulaAllCodeTerm
      (dynamicTruthLocalFormulaAllCodeTerm
        (dynamicTruthLocalFormulaAllCodeTerm
          (dynamicTruthLocalFormulaAllCodeTerm
            (dynamicTruthLocalFormulaAllCodeTerm
              (dynamicTruthLocalFormulaAllCodeTerm
                (dynamicTruthLocalFormulaAllCodeTerm body))))))).

Definition dynamicTruthNativeShiftSourceAdmissibleCodeTerm
    (sigmaDomain piDomain : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (Term.numeral
      (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
    (dynamicTruthLocalFormulaAndCodeTerm
      (Term.numeral
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 4) (tVar 5) (tVar 2))))
      (dynamicTruthLocalFormulaOrCodeTerm sigmaDomain piDomain)).

Definition dynamicTruthNativeShiftFieldCodeTerm
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : term)
    : term :=
  dynamicTruthNativeShiftFormulaAll8CodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm
      (dynamicTruthNativeShiftFormulaAnd5CodeTerm
        (Term.numeral
          (formulaCode
            (codedFormulaShiftTermAt
              (tVar 0) (tVar 1) (tVar 2) (tVar 3))))
        (Term.numeral
          (formulaCode
            (codedFormulaShiftAssignmentRelationTermAt
              (tVar 0) (tVar 1) (tVar 2)
              (tVar 4) (tVar 5) (tVar 6) (tVar 7))))
        (dynamicTruthNativeShiftSourceAdmissibleCodeTerm
          sigmaDomain piDomain)
        (Term.numeral
          (formulaCode
            (codedFormulaTargetAdmissibilityDataTermAt
              (tVar 3) (tVar 6) (tVar 7))))
        (Term.numeral
          (formulaCode
            (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3)))))
      (dynamicTruthLocalFormulaAndCodeTerm
        (dynamicTruthNativeShiftFormulaIffCodeTerm sourceSigma targetSigma)
        (dynamicTruthNativeShiftFormulaIffCodeTerm sourcePi targetPi))).

Definition rawDynamicTruthNativeShiftFormulaAnd5Code (M : RawPAModel)
    (a b c d e : M) : M :=
  rawFormulaAndCode M a
    (rawFormulaAndCode M b
      (rawFormulaAndCode M c (rawFormulaAndCode M d e))).

Definition rawDynamicTruthNativeShiftFormulaIffCode (M : RawPAModel)
    (left right : M) : M :=
  rawFormulaAndCode M
    (rawFormulaImpCode M left right)
    (rawFormulaImpCode M right left).

Definition rawDynamicTruthNativeShiftFormulaAll8Code (M : RawPAModel)
    (body : M) : M :=
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawFormulaAllCode M (rawFormulaAllCode M body))))))).

Definition rawDynamicTruthNativeShiftSourceAdmissibleCode (M : RawPAModel)
    (sigmaDomain piDomain : M) : M :=
  rawFormulaAndCode M
    (rawNumeralValue M
      (formulaCode (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
    (rawFormulaAndCode M
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 4) (tVar 5) (tVar 2))))
      (rawFormulaOrCode M sigmaDomain piDomain)).

Definition rawDynamicTruthNativeShiftFieldCode (M : RawPAModel)
    (sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M) : M :=
  rawDynamicTruthNativeShiftFormulaAll8Code M
    (rawFormulaImpCode M
      (rawDynamicTruthNativeShiftFormulaAnd5Code M
        (rawNumeralValue M
          (formulaCode
            (codedFormulaShiftTermAt
              (tVar 0) (tVar 1) (tVar 2) (tVar 3))))
        (rawNumeralValue M
          (formulaCode
            (codedFormulaShiftAssignmentRelationTermAt
              (tVar 0) (tVar 1) (tVar 2)
              (tVar 4) (tVar 5) (tVar 6) (tVar 7))))
        (rawDynamicTruthNativeShiftSourceAdmissibleCode M
          sigmaDomain piDomain)
        (rawNumeralValue M
          (formulaCode
            (codedFormulaTargetAdmissibilityDataTermAt
              (tVar 3) (tVar 6) (tVar 7))))
        (rawNumeralValue M
          (formulaCode
            (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3)))))
      (rawFormulaAndCode M
        (rawDynamicTruthNativeShiftFormulaIffCode M sourceSigma targetSigma)
        (rawDynamicTruthNativeShiftFormulaIffCode M sourcePi targetPi))).

Lemma raw_eval_dynamicTruthNativeShiftFormulaAnd5CodeTerm : forall
    (M : RawPAModel) e a b c d f,
  raw_term_eval M e
    (dynamicTruthNativeShiftFormulaAnd5CodeTerm a b c d f) =
  rawDynamicTruthNativeShiftFormulaAnd5Code M
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e d)
    (raw_term_eval M e f).
Proof.
  intros.
  unfold dynamicTruthNativeShiftFormulaAnd5CodeTerm,
    rawDynamicTruthNativeShiftFormulaAnd5Code.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeShiftFormulaIffCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e
    (dynamicTruthNativeShiftFormulaIffCodeTerm left right) =
  rawDynamicTruthNativeShiftFormulaIffCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros.
  unfold dynamicTruthNativeShiftFormulaIffCodeTerm,
    rawDynamicTruthNativeShiftFormulaIffCode.
  rewrite raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthLocalFormulaImpCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeShiftFormulaAll8CodeTerm : forall
    (M : RawPAModel) e body,
  raw_term_eval M e (dynamicTruthNativeShiftFormulaAll8CodeTerm body) =
  rawDynamicTruthNativeShiftFormulaAll8Code M
    (raw_term_eval M e body).
Proof.
  intros.
  unfold dynamicTruthNativeShiftFormulaAll8CodeTerm,
    rawDynamicTruthNativeShiftFormulaAll8Code.
  rewrite !raw_eval_dynamicTruthLocalFormulaAllCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeShiftSourceAdmissibleCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain,
  raw_term_eval M e
    (dynamicTruthNativeShiftSourceAdmissibleCodeTerm
      sigmaDomain piDomain) =
  rawDynamicTruthNativeShiftSourceAdmissibleCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain).
Proof.
  intros.
  unfold dynamicTruthNativeShiftSourceAdmissibleCodeTerm,
    rawDynamicTruthNativeShiftSourceAdmissibleCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    raw_eval_dynamicTruthLocalFormulaOrCodeTerm,
    !raw_term_eval_numeral.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeShiftFieldCodeTerm : forall
    (M : RawPAModel) e
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  raw_term_eval M e
    (dynamicTruthNativeShiftFieldCodeTerm
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi) =
  rawDynamicTruthNativeShiftFieldCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
    (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi).
Proof.
  intros.
  unfold dynamicTruthNativeShiftFieldCodeTerm,
    rawDynamicTruthNativeShiftFieldCode.
  rewrite raw_eval_dynamicTruthNativeShiftFormulaAll8CodeTerm,
    raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthNativeShiftFormulaAnd5CodeTerm,
    raw_eval_dynamicTruthNativeShiftSourceAdmissibleCodeTerm,
    raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthNativeShiftFormulaIffCodeTerm,
    !raw_term_eval_numeral.
  reflexivity.
Qed.

Definition dynamicTruthNativeShiftFieldCodeTermAt
    (output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      : term) : formula :=
  pEq output
    (dynamicTruthNativeShiftFieldCodeTerm
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).

Lemma raw_sat_dynamicTruthNativeShiftFieldCodeTermAt_iff : forall
    (M : RawPAModel) e
      output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  raw_formula_sat M e
    (dynamicTruthNativeShiftFieldCodeTermAt
      output sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
  <->
  raw_term_eval M e output =
    rawDynamicTruthNativeShiftFieldCode M
      (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
      (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
      (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi).
Proof.
  intros.
  unfold dynamicTruthNativeShiftFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthNativeShiftFieldCodeTerm
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi) <->
    raw_term_eval M e output =
      rawDynamicTruthNativeShiftFieldCode M
        (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
        (raw_term_eval M e sourceSigma) (raw_term_eval M e targetSigma)
        (raw_term_eval M e sourcePi) (raw_term_eval M e targetPi)).
  rewrite raw_eval_dynamicTruthNativeShiftFieldCodeTerm.
  reflexivity.
Qed.

Theorem rawDynamicTruthNativeShiftFieldCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  rawDynamicTruthNativeShiftFieldCode M
    (rawQuotedFormulaCode M sigmaDomain)
    (rawQuotedFormulaCode M piDomain)
    (rawQuotedFormulaCode M sourceSigma)
    (rawQuotedFormulaCode M targetSigma)
    (rawQuotedFormulaCode M sourcePi)
    (rawQuotedFormulaCode M targetPi) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeShiftFieldCarrierFormula
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
  unfold rawDynamicTruthNativeShiftFieldCode,
    rawDynamicTruthNativeShiftFormulaAll8Code,
    rawDynamicTruthNativeShiftFormulaAnd5Code,
    rawDynamicTruthNativeShiftFormulaIffCode,
    rawDynamicTruthNativeShiftSourceAdmissibleCode,
    dynamicTruthNativeShiftFieldCarrierFormula,
    dynamicTruthNativeShiftStepCarrierFormula,
    dynamicTruthNativeShiftCertificateTransportFormula,
    dynamicTruthNativeShiftSourceAdmissibleFormula,
    operationTarskiPositiveAll8, operationTransportAnd5,
    operationTransportIff.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaShiftTermAt (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaShiftAssignmentRelationTermAt
      (tVar 0) (tVar 1) (tVar 2)
      (tVar 4) (tVar 5) (tVar 6) (tVar 7))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt
      (tVar 4) (tVar 5) (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaTargetAdmissibilityDataTermAt
      (tVar 3) (tVar 6) (tVar 7))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3))).
  reflexivity.
Qed.

(** At standard predecessor [p], the transparent polynomial targets the
    literal eight-variable closure of the fixed level-[S p] shift law. *)
Corollary rawDynamicTruthNativeShiftFieldCode_quoted_successor_level : forall
    (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthNativeShiftFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 2) (tVar 4) (tVar 5)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
        (tVar 3) (tVar 6) (tVar 7)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 2) (tVar 4) (tVar 5)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S predecessor)
        (tVar 3) (tVar 6) (tVar 7))) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeShiftFixedLevelFieldFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeShiftFieldCode_quoted by exact hPA.
  rewrite dynamicTruthNativeShiftFieldCarrierFormula_fixedLevel.
  reflexivity.
Qed.

Lemma dynamicTruthNativeShiftFixedLevelFieldFormula_closeN : forall level,
  dynamicTruthNativeShiftFixedLevelFieldFormula level =
  Formula.closeN 8 (fixedLevelFormulaShiftTarskiStepFormula level).
Proof.
  intro level.
  unfold dynamicTruthNativeShiftFixedLevelFieldFormula,
    operationTarskiPositiveAll8.
  reflexivity.
Qed.

Theorem PA_proves_dynamicTruthNativeShiftFixedLevelFieldFormula :
  forall level,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthNativeShiftFixedLevelFieldFormula level).
Proof.
  intro level.
  rewrite dynamicTruthNativeShiftFixedLevelFieldFormula_closeN.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - exact (PA_proves_fixedLevelFormulaShiftTarskiStepFormula level).
Qed.

Theorem raw_dynamicTruthNativeShiftFixedLevelField_quoted_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M
        (dynamicTruthNativeShiftFixedLevelFieldFormula level)) certificate.
Proof.
  intros M hPA level.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthNativeShiftFixedLevelFieldFormula level)
    (PA_proves_dynamicTruthNativeShiftFixedLevelFieldFormula level)) as
    [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

Corollary rawDynamicTruthNativeShiftFieldCode_standard_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeShiftFieldCode M
        (rawQuotedFormulaCode M
          (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
        (rawQuotedFormulaCode M
          (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
            (tVar 2) (tVar 4) (tVar 5)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt (S predecessor)
            (tVar 3) (tVar 6) (tVar 7)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S predecessor)
            (tVar 2) (tVar 4) (tVar 5)))
        (rawQuotedFormulaCode M
          (fixedLevelPiFalsityCertificateTermAt (S predecessor)
            (tVar 3) (tVar 6) (tVar 7)))) certificate.
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeShiftFieldCode_quoted_successor_level
    by exact hPA.
  exact (raw_dynamicTruthNativeShiftFixedLevelField_quoted_proof
    M hPA (S predecessor)).
Qed.

(** ------------------------------------------------------------------
    The genuine paired orbit at current level [S p]. *)

Definition dynamicTruthNativeShiftInputOrbitGraph : formula :=
  dynamicTruthNativeLocalInputOrbitGraph.

Definition RawDynamicTruthNativeShiftInputOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel globalSigma globalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M predecessorLevel) globalSigma globalPi.

Arguments RawDynamicTruthNativeShiftInputOrbitAt
  M tail predecessorLevel globalSigma globalPi : clear implicits.

Theorem raw_sat_dynamicTruthNativeShiftInputOrbitGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M predecessorLevel tail)))
    dynamicTruthNativeShiftInputOrbitGraph <->
  RawDynamicTruthNativeShiftInputOrbitAt M
    tail predecessorLevel globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeShiftInputOrbitGraph,
    RawDynamicTruthNativeShiftInputOrbitAt.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff
    M tail predecessorLevel globalSigma globalPi).
Qed.

Corollary raw_sat_dynamicTruthNativeShiftInputOrbitGraph_standard_iff : forall
    (M : RawPAModel) tail predecessor globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M (rawNumeralValue M predecessor) tail)))
    dynamicTruthNativeShiftInputOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor)) globalSigma globalPi.
Proof.
  intros.
  unfold dynamicTruthNativeShiftInputOrbitGraph.
  exact (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_standard_iff
    M tail predecessor globalSigma globalPi).
Qed.

(** ------------------------------------------------------------------
    Transform the current orbit pair into the shift field.

    Beneath the eight witnesses the environment is

      targetPi :: sourcePi :: targetSigma :: sourceSigma ::
      piDomain :: sigmaDomain :: currentLevelNumeral :: currentLevel ::
      fieldCode :: currentGlobalSigma :: currentGlobalPi ::
      predecessorLevel :: tail. *)

Definition dynamicTruthNativeShiftAnd8
    (a b c d e f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd e (pAnd f (pAnd g h)))))).

Definition dynamicTruthNativeShiftFieldTransformGraph : formula :=
  fixedLevelEx8
    (pAnd
      (pEq (tVar 7) (tSucc (tVar 11)))
      (dynamicTruthNativeShiftAnd8
        (numeralTermCodeAtTermAt (tVar 7) (tVar 6))
        (codedFormulaSingleSubstitutionTermAt
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (tVar 5))
        (codedFormulaSingleSubstitutionTermAt
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (tVar 4))
        (dynamicTruthNativeShiftApplicationTermAt
          dynamicTruthNativeShiftSourceFirstReplacement
          dynamicTruthNativeShiftSourceSecondReplacement
          dynamicTruthNativeShiftSourceThirdReplacement
          (tVar 9) (tVar 3))
        (dynamicTruthNativeShiftApplicationTermAt
          dynamicTruthNativeShiftTargetFirstReplacement
          dynamicTruthNativeShiftTargetSecondReplacement
          dynamicTruthNativeShiftTargetThirdReplacement
          (tVar 9) (tVar 2))
        (dynamicTruthNativeShiftApplicationTermAt
          dynamicTruthNativeShiftSourceFirstReplacement
          dynamicTruthNativeShiftSourceSecondReplacement
          dynamicTruthNativeShiftSourceThirdReplacement
          (tVar 10) (tVar 1))
        (dynamicTruthNativeShiftApplicationTermAt
          dynamicTruthNativeShiftTargetFirstReplacement
          dynamicTruthNativeShiftTargetSecondReplacement
          dynamicTruthNativeShiftTargetThirdReplacement
          (tVar 10) (tVar 0))
        (dynamicTruthNativeShiftFieldCodeTermAt
          (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0)))).

Definition RawDynamicTruthNativeShiftFieldTransformAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi predecessorLevel fieldCode : M)
    : Prop :=
  exists currentLevel currentLevelNumeral sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      currentGlobalSigma sourceSigma /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      currentGlobalSigma targetSigma /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      currentGlobalPi sourcePi /\
    RawDynamicTruthNativeShiftApplication M
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      currentGlobalPi targetPi /\
    fieldCode = rawDynamicTruthNativeShiftFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.

Arguments RawDynamicTruthNativeShiftFieldTransformAt
  M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
  : clear implicits.

Local Opaque dynamicTruthNativeShiftApplicationTermAt.

Theorem raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff : forall
    (M : RawPAModel) tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M currentGlobalSigma
      (scons M currentGlobalPi (scons M predecessorLevel tail))))
    dynamicTruthNativeShiftFieldTransformGraph <->
  RawDynamicTruthNativeShiftFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
Proof.
  intros M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
  unfold dynamicTruthNativeShiftFieldTransformGraph,
    RawDynamicTruthNativeShiftFieldTransformAt,
    fixedLevelEx8, dynamicTruthNativeShiftAnd8.
  cbn [raw_formula_sat].
  split.
  - intros (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi & hfield).
    change (currentLevel = raw_succ M predecessorLevel) in hlevel.
    apply (proj1 (raw_sat_numeralTermCodeAtTermAt_iff M _
      (tVar 7) (tVar 6))) in hnumeral.
    cbn [raw_term_eval scons] in hnumeral.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 6)
      (Term.numeral
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (tVar 5))) in hsigmaDomain.
    rewrite raw_term_eval_numeral in hsigmaDomain.
    cbn [raw_term_eval scons] in hsigmaDomain.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 6)
      (Term.numeral
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (tVar 4))) in hpiDomain.
    rewrite raw_term_eval_numeral in hpiDomain.
    cbn [raw_term_eval scons] in hpiDomain.
    apply (proj1 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      (tVar 9) (tVar 3))) in hsourceSigma.
    cbn [raw_term_eval scons] in hsourceSigma.
    apply (proj1 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      (tVar 9) (tVar 2))) in htargetSigma.
    cbn [raw_term_eval scons] in htargetSigma.
    apply (proj1 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
      dynamicTruthNativeShiftSourceFirstReplacement
      dynamicTruthNativeShiftSourceSecondReplacement
      dynamicTruthNativeShiftSourceThirdReplacement
      (tVar 10) (tVar 1))) in hsourcePi.
    cbn [raw_term_eval scons] in hsourcePi.
    apply (proj1 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
      dynamicTruthNativeShiftTargetFirstReplacement
      dynamicTruthNativeShiftTargetSecondReplacement
      dynamicTruthNativeShiftTargetThirdReplacement
      (tVar 10) (tVar 0))) in htargetPi.
    cbn [raw_term_eval scons] in htargetPi.
    apply (proj1 (raw_sat_dynamicTruthNativeShiftFieldCodeTermAt_iff M _
      (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
      (tVar 1) (tVar 0))) in hfield.
    cbn [raw_term_eval scons] in hfield.
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    split; [exact hlevel |].
    split; [exact hnumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hsourceSigma |].
    split; [exact htargetSigma |].
    split; [exact hsourcePi |].
    split; [exact htargetPi | exact hfield].
  - intros (currentLevel & currentLevelNumeral & sigmaDomain & piDomain &
      sourceSigma & targetSigma & sourcePi & targetPi & hlevel & hnumeral &
      hsigmaDomain & hpiDomain & hsourceSigma & htargetSigma &
      hsourcePi & htargetPi & hfield).
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    repeat split.
    + change (currentLevel = raw_succ M predecessorLevel). exact hlevel.
    + apply (proj2 (raw_sat_numeralTermCodeAtTermAt_iff M _
        (tVar 7) (tVar 6))).
      cbn [raw_term_eval scons]. exact hnumeral.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (tVar 5))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hsigmaDomain.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 6)
          (Term.numeral
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (tVar 4))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hpiDomain.
    + apply (proj2 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
        dynamicTruthNativeShiftSourceFirstReplacement
        dynamicTruthNativeShiftSourceSecondReplacement
        dynamicTruthNativeShiftSourceThirdReplacement
        (tVar 9) (tVar 3))).
      cbn [raw_term_eval scons]. exact hsourceSigma.
    + apply (proj2 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
        dynamicTruthNativeShiftTargetFirstReplacement
        dynamicTruthNativeShiftTargetSecondReplacement
        dynamicTruthNativeShiftTargetThirdReplacement
        (tVar 9) (tVar 2))).
      cbn [raw_term_eval scons]. exact htargetSigma.
    + apply (proj2 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
        dynamicTruthNativeShiftSourceFirstReplacement
        dynamicTruthNativeShiftSourceSecondReplacement
        dynamicTruthNativeShiftSourceThirdReplacement
        (tVar 10) (tVar 1))).
      cbn [raw_term_eval scons]. exact hsourcePi.
    + apply (proj2 (raw_sat_dynamicTruthNativeShiftApplicationTermAt_iff M _
        dynamicTruthNativeShiftTargetFirstReplacement
        dynamicTruthNativeShiftTargetSecondReplacement
        dynamicTruthNativeShiftTargetThirdReplacement
        (tVar 10) (tVar 0))).
      cbn [raw_term_eval scons]. exact htargetPi.
    + apply (proj2 (raw_sat_dynamicTruthNativeShiftFieldCodeTermAt_iff M _
        (tVar 8) (tVar 5) (tVar 4) (tVar 3) (tVar 2)
        (tVar 1) (tVar 0))).
      cbn [raw_term_eval scons]. exact hfield.
Qed.

(** Constructor closure makes the selected field itself atomically adequate. *)
Lemma rawDynamicTruthNativeShiftFieldCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M sourceSigma ->
  RawCodedFormulaAtomicallyAdequate M targetSigma ->
  RawCodedFormulaAtomicallyAdequate M sourcePi ->
  RawCodedFormulaAtomicallyAdequate M targetPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeShiftFieldCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
Proof.
  intros M hPA sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hsigmaDomain hpiDomain hsourceSigma htargetSigma hsourcePi htargetPi.
  unfold rawDynamicTruthNativeShiftFieldCode,
    rawDynamicTruthNativeShiftFormulaAll8Code,
    rawDynamicTruthNativeShiftFormulaAnd5Code,
    rawDynamicTruthNativeShiftFormulaIffCode,
    rawDynamicTruthNativeShiftSourceAdmissibleCode.
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedFormulaShiftTermAt (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
          (codedFormulaShiftAssignmentRelationTermAt
            (tVar 0) (tVar 1) (tVar 2)
            (tVar 4) (tVar 5) (tVar 6) (tVar 7))).
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
           ++ apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
              ** exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                   (codedAssignmentDefinedThroughTermAt
                     (tVar 4) (tVar 5) (tVar 2))).
              ** apply raw_formulaOrCode_atomically_adequate;
                   [exact hPA | exact hsigmaDomain | exact hpiDomain].
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaTargetAdmissibilityDataTermAt
                  (tVar 3) (tVar 6) (tVar 7))).
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |];
        apply raw_formulaImpCode_atomically_adequate;
        try exact hPA; assumption.
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |];
        apply raw_formulaImpCode_atomically_adequate;
        try exact hPA; assumption.
Qed.

(** ------------------------------------------------------------------
    Adequacy-preserving relational totality of the transform.

    The selected domain and application codes are produced by represented
    syntax relations.  Their adequacy invariants are retained long enough to
    prove that the transparent field polynomial is itself a formula code. *)

Definition RawDynamicTruthNativeShiftFieldTransformTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) currentGlobalSigma currentGlobalPi
      predecessorLevel,
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi ->
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M currentGlobalSigma
          (scons M currentGlobalPi (scons M predecessorLevel tail))))
        dynamicTruthNativeShiftFieldTransformGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeShiftFieldTransformTotalOnAdequate M
  : clear implicits.

Theorem
    dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftFieldTransformTotalOnAdequate M.
Proof.
  intros M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
    hcurrentSigma hcurrentPi.
  set (currentLevel := raw_succ M predecessorLevel).
  destruct (raw_numeralTermCodeExists_all M hPA currentLevel) as
    [currentLevelNumeral hcurrentLevelNumeral].
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalSigmaInputDomainTemplate hcurrentLevelNumeral) as
    (sigmaDomain & hsigmaDomain & hsigmaDomainAdequate).
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthLocalPiInputDomainTemplate hcurrentLevelNumeral) as
    (piDomain & hpiDomain & hpiDomainAdequate).
  destruct (raw_dynamicTruthNativeShiftApplication_exists_adequate
    M hPA dynamicTruthNativeShiftSourceFirstReplacement
    dynamicTruthNativeShiftSourceSecondReplacement
    dynamicTruthNativeShiftSourceThirdReplacement
    currentGlobalSigma hcurrentSigma) as
    (sourceSigma & hsourceSigma & hsourceSigmaAdequate).
  destruct (raw_dynamicTruthNativeShiftApplication_exists_adequate
    M hPA dynamicTruthNativeShiftTargetFirstReplacement
    dynamicTruthNativeShiftTargetSecondReplacement
    dynamicTruthNativeShiftTargetThirdReplacement
    currentGlobalSigma hcurrentSigma) as
    (targetSigma & htargetSigma & htargetSigmaAdequate).
  destruct (raw_dynamicTruthNativeShiftApplication_exists_adequate
    M hPA dynamicTruthNativeShiftSourceFirstReplacement
    dynamicTruthNativeShiftSourceSecondReplacement
    dynamicTruthNativeShiftSourceThirdReplacement
    currentGlobalPi hcurrentPi) as
    (sourcePi & hsourcePi & hsourcePiAdequate).
  destruct (raw_dynamicTruthNativeShiftApplication_exists_adequate
    M hPA dynamicTruthNativeShiftTargetFirstReplacement
    dynamicTruthNativeShiftTargetSecondReplacement
    dynamicTruthNativeShiftTargetThirdReplacement
    currentGlobalPi hcurrentPi) as
    (targetPi & htargetPi & htargetPiAdequate).
  exists (rawDynamicTruthNativeShiftFieldCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
        currentGlobalSigma currentGlobalPi predecessorLevel _)).
    exists currentLevel, currentLevelNumeral, sigmaDomain, piDomain,
      sourceSigma, targetSigma, sourcePi, targetPi.
    split; [unfold currentLevel; reflexivity |].
    split; [exact hcurrentLevelNumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hsourceSigma |].
    split; [exact htargetSigma |].
    split; [exact hsourcePi |].
    split; [exact htargetPi | reflexivity].
  - exact (rawDynamicTruthNativeShiftFieldCode_atomically_adequate M hPA
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hsigmaDomainAdequate hpiDomainAdequate
      hsourceSigmaAdequate htargetSigmaAdequate
      hsourcePiAdequate htargetPiAdequate).
Qed.

(** ------------------------------------------------------------------
    Output-first composition with the genuine current-level orbit. *)

Definition dynamicTruthNativeShiftPositiveGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthNativeShiftInputOrbitGraph
    dynamicTruthNativeShiftFieldTransformGraph.

Definition RawDynamicTruthNativeShiftPositiveAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists currentGlobalSigma currentGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeShiftFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.

Arguments RawDynamicTruthNativeShiftPositiveAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthNativeShiftPositiveGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthNativeShiftPositiveGraph <->
  RawDynamicTruthNativeShiftPositiveAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthNativeShiftPositiveGraph,
    RawDynamicTruthNativeShiftPositiveAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthNativeShiftInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj2
        (raw_sat_dynamicTruthNativeShiftInputOrbitGraph_iff M tail
          predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
          currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
      exact htransform.
Qed.

(** Totality keeps the formula-code invariant in its public conclusion. *)
Definition RawDynamicTruthNativeShiftPositiveAdequateTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeShiftPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeShiftPositiveAdequateTotal M
  : clear implicits.

Theorem dynamicTruthNativeShiftPositiveGraph_raw_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftPositiveAdequateTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  destruct
    (dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransform & hfieldAdequate).
  exists fieldCode. split; [|exact hfieldAdequate].
  apply (proj2 (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact horbit.
  - apply (proj1
      (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
        currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)).
    exact htransform.
Qed.

Definition RawDynamicTruthNativeShiftPositiveTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeShiftPositiveGraph.

Arguments RawDynamicTruthNativeShiftPositiveTotal M : clear implicits.

Corollary dynamicTruthNativeShiftPositiveGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftPositiveTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct (dynamicTruthNativeShiftPositiveGraph_raw_adequate_total
    M hPA tail predecessorLevel) as (fieldCode & hfield & _).
  now exists fieldCode.
Qed.

(** ------------------------------------------------------------------
    Exact remaining object-proof compiler seam.

    The fixed-level theorem above supplies genuine represented PA proofs for
    every externally fixed standard level.  At an arbitrary carrier index,
    relational syntax totality alone cannot manufacture a represented proof.
    The following premise therefore asks only for the missing uniform
    compiler on the exact adequate orbit witness and exact transform trace;
    it assumes neither semantic validity nor model-theoretic soundness. *)

Definition RawDynamicTruthNativeShiftProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeShiftFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeShiftProofCompiler M : clear implicits.

Definition RawDynamicTruthNativeShiftPositiveProofTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeShiftPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeShiftPositiveProofTotal M : clear implicits.

Theorem dynamicTruthNativeShiftPositiveGraph_raw_proof_total_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftProofCompiler M ->
  RawDynamicTruthNativeShiftPositiveProofTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler tail predecessorLevel currentGlobalSigma
    currentGlobalPi fieldCode hadequateOrbit htransform) as
    [certificate hcertificate].
  exists fieldCode, certificate.
  split.
  - apply (proj2 (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
