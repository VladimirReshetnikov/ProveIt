(**
  The carrier-indexed positive local decision/exclusivity field.

  The standard level-[n] local field is the conjunction of two statements:

    * every input admissible at level [n] has either a Sigma-truth or a
      Pi-falsity certificate at level [S n]; and
    * no admissible input has both certificates.

  At a nonstandard carrier index one cannot ask Rocq to unfold the external
  fixed-level recursion.  This module instead performs the same construction
  entirely on represented syntax.  At predecessor [p] it

    1. selects the actual paired global Sigma/Pi orbit codes at [S p];
    2. applies the genuine paired global successor graph at lower level
       [S p], exposing the native Sigma [Or7] and Pi [Or6] rows whose
       evidence predicates live at [S (S p)];
    3. applies those ternary evidence predicates to the three
       universally bound input variables;
    4. instantiates the two input-domain templates with the numeral term for
       [S p]; and
    5. builds the exact right-associated conjunction used by the external
       fixed-level formula.

  The graph is output first and is indexed by the predecessor:

      fieldCode :: predecessorLevel :: tail.

  All graph semantics below are law free.  PA is used only for relational
  totality of the represented syntax operations.  In particular this file
  does *not* infer a represented PA proof from semantic validity.  The final
  record names the exact proof compiler still required by the master-field
  successor construction.
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
  RawCodedFixedLevelTruthScheduleInvariant
  RawCodedFixedLevelTruthLaws
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedTermOpeningTotalityDischarge
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

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
Import PABoundedRawCodedFixedLevelTruthScheduleInvariant.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedTermOpeningTotalityDischarge.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    The exact formula family mirrored by the carrier polynomial. *)

Definition dynamicTruthLocalAdmissibleFormula
    (sigmaDomain piDomain : formula) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))
    (pAnd
      (codedAssignmentDefinedThroughTermAt
        (tVar 1) (tVar 0) (tVar 2))
      (pOr sigmaDomain piDomain)).

Definition dynamicTruthLocalDecisionExclusiveCarrierFormula
    (sigmaDomain piDomain sigmaEvidence piEvidence : formula) : formula :=
  let admissible :=
    dynamicTruthLocalAdmissibleFormula sigmaDomain piDomain in
  pAnd
    (pAll (pAll (pAll
      (pImp admissible (pOr sigmaEvidence piEvidence)))))
    (pAll (pAll (pAll
      (pImp admissible
        (pImp sigmaEvidence (pImp piEvidence pBot)))))).

(** With the native externally indexed components, the displayed carrier
    family is definitionally the existing fixed-level bundle.  This pins the
    target shape independently of all later code-graph machinery. *)
Lemma dynamicTruthLocalDecisionExclusiveCarrierFormula_fixedLevel : forall
    inputLevel,
  dynamicTruthLocalDecisionExclusiveCarrierFormula
    (fixedLevelSigmaDomainTermAt inputLevel (tVar 2))
    (fixedLevelPiDomainTermAt inputLevel (tVar 2))
    (fixedLevelSigmaTruthCertificateTermAt (S inputLevel)
      (tVar 2) (tVar 1) (tVar 0))
    (fixedLevelPiFalsityCertificateTermAt (S inputLevel)
      (tVar 2) (tVar 1) (tVar 0)) =
  fixedLevelLocalDecisionExclusiveBundleFormula inputLevel.
Proof.
  intro inputLevel.
  unfold dynamicTruthLocalDecisionExclusiveCarrierFormula,
    dynamicTruthLocalAdmissibleFormula,
    fixedLevelLocalDecisionExclusiveBundleFormula,
    fixedLevelInputTruthCertificateTotalityFormula,
    fixedLevelSuccessorTruthDecisionTermAt,
    fixedLevelAdmissibleTruthCertificateExclusiveFormula,
    fixedLevelTruthAdmissibleTermAt.
  reflexivity.
Qed.

(** The domain templates reserve free variable zero for the represented
    numeral term.  Their formula-code argument starts at [#3], and therefore
    becomes [#2] after the placeholder is substituted away. *)
Definition dynamicTruthLocalSigmaInputDomainTemplate : formula :=
  dynamicTruthSigmaRecordDomainTermAt (tVar 0) (tVar 3).

Definition dynamicTruthLocalPiInputDomainTemplate : formula :=
  dynamicTruthPiRecordDomainTermAt (tVar 0) (tVar 3).

(** ------------------------------------------------------------------
    Ternary application in the three-universal local-field layout.

    Sequential substitution by [#4], [#2], and [#0] implements the final
    renaming [#0 |-> #2, #1 |-> #1, #2 |-> #0].  The first two indices
    compensate for the free-variable slot removed by each later
    substitution. *)

Definition dynamicTruthLocalApplicationFirstReplacement : term := tVar 4.
Definition dynamicTruthLocalApplicationSecondReplacement : term := tVar 2.
Definition dynamicTruthLocalApplicationThirdReplacement : term := tVar 0.

Definition dynamicTruthLocalApplicationFirstReplacementCode : term :=
  Term.numeral (termCode dynamicTruthLocalApplicationFirstReplacement).
Definition dynamicTruthLocalApplicationSecondReplacementCode : term :=
  Term.numeral (termCode dynamicTruthLocalApplicationSecondReplacement).
Definition dynamicTruthLocalApplicationThirdReplacementCode : term :=
  Term.numeral (termCode dynamicTruthLocalApplicationThirdReplacement).

Definition dynamicTruthLocalTernaryApplicationTermAt
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        dynamicTruthLocalApplicationFirstReplacementCode
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthLocalApplicationSecondReplacementCode
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthLocalApplicationThirdReplacementCode
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthLocalTernaryApplication (M : RawPAModel)
    (input output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthLocalApplicationFirstReplacement))
      input first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthLocalApplicationSecondReplacement))
      first second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthLocalApplicationThirdReplacement))
      second output.

Arguments RawDynamicTruthLocalTernaryApplication M input output
  : clear implicits.

Theorem raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (dynamicTruthLocalTernaryApplicationTermAt input output) <->
  RawDynamicTruthLocalTernaryApplication M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold dynamicTruthLocalTernaryApplicationTermAt,
    RawDynamicTruthLocalTernaryApplication,
    dynamicTruthLocalApplicationFirstReplacementCode,
    dynamicTruthLocalApplicationSecondReplacementCode,
    dynamicTruthLocalApplicationThirdReplacementCode.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** PA proves enough syntax-operation totality to apply every atomically
    adequate ternary predicate in this fixed variable layout. *)
Lemma raw_dynamicTruthLocalTernaryApplication_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthLocalTernaryApplication M input output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input hinput.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    input hinput
    (rawNumeralValue M
      (termCode dynamicTruthLocalApplicationFirstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthLocalApplicationFirstReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthLocalApplicationSecondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthLocalApplicationSecondReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthLocalApplicationThirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthLocalApplicationThirdReplacement)) as
    (first & second & output & hfirst & _hfirstAdequate &
     hsecond & _hsecondAdequate & hthird & houtputAdequate).
  exists output. split; [|exact houtputAdequate].
  exists first, second. repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Transparent code polynomial for the local bundle. *)

Definition dynamicTruthLocalFormulaImpCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 2) left right.

Definition dynamicTruthLocalFormulaAndCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 3) left right.

Definition dynamicTruthLocalFormulaOrCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 4) left right.

Definition dynamicTruthLocalFormulaAllCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 5) child.

Definition dynamicTruthLocalFormulaAll3CodeTerm (child : term) : term :=
  dynamicTruthLocalFormulaAllCodeTerm
    (dynamicTruthLocalFormulaAllCodeTerm
      (dynamicTruthLocalFormulaAllCodeTerm child)).

Definition dynamicTruthLocalAdmissibleCodeTerm
    (sigmaDomain piDomain : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (Term.numeral
      (formulaCode
        (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
    (dynamicTruthLocalFormulaAndCodeTerm
      (Term.numeral
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2))))
      (dynamicTruthLocalFormulaOrCodeTerm sigmaDomain piDomain)).

Definition dynamicTruthLocalDecisionCodeTerm
    (sigmaDomain piDomain sigmaEvidence piEvidence : term) : term :=
  dynamicTruthLocalFormulaImpCodeTerm
    (dynamicTruthLocalAdmissibleCodeTerm sigmaDomain piDomain)
    (dynamicTruthLocalFormulaOrCodeTerm sigmaEvidence piEvidence).

Definition dynamicTruthLocalExclusiveCodeTerm
    (sigmaDomain piDomain sigmaEvidence piEvidence : term) : term :=
  dynamicTruthLocalFormulaImpCodeTerm
    (dynamicTruthLocalAdmissibleCodeTerm sigmaDomain piDomain)
    (dynamicTruthLocalFormulaImpCodeTerm sigmaEvidence
      (dynamicTruthLocalFormulaImpCodeTerm piEvidence
        rawFormulaBotCodeTerm)).

Definition dynamicTruthLocalDecisionExclusiveFieldCodeTerm
    (sigmaDomain piDomain sigmaEvidence piEvidence : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (dynamicTruthLocalFormulaAll3CodeTerm
      (dynamicTruthLocalDecisionCodeTerm
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (dynamicTruthLocalFormulaAll3CodeTerm
      (dynamicTruthLocalExclusiveCodeTerm
        sigmaDomain piDomain sigmaEvidence piEvidence)).

Definition rawDynamicTruthLocalFormulaAll3Code (M : RawPAModel)
    (child : M) : M :=
  rawFormulaAllCode M
    (rawFormulaAllCode M (rawFormulaAllCode M child)).

Definition rawDynamicTruthLocalAdmissibleCode (M : RawPAModel)
    (sigmaDomain piDomain : M) : M :=
  rawFormulaAndCode M
    (rawNumeralValue M
      (formulaCode
        (codedFormulaAtomicallyAdequateTermAt (tVar 2))))
    (rawFormulaAndCode M
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt
            (tVar 1) (tVar 0) (tVar 2))))
      (rawFormulaOrCode M sigmaDomain piDomain)).

Definition rawDynamicTruthLocalDecisionCode (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaOrCode M sigmaEvidence piEvidence).

Definition rawDynamicTruthLocalExclusiveCode (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain)
    (rawFormulaImpCode M sigmaEvidence
      (rawFormulaImpCode M piEvidence (rawFormulaBotCode M))).

Definition rawDynamicTruthLocalDecisionExclusiveFieldCode
    (M : RawPAModel)
    (sigmaDomain piDomain sigmaEvidence piEvidence : M) : M :=
  rawFormulaAndCode M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalDecisionCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)).

Lemma raw_eval_dynamicTruthLocalFormulaImpCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthLocalFormulaImpCodeTerm left right) =
  rawFormulaImpCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthLocalFormulaImpCodeTerm, rawFormulaImpCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalFormulaAndCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthLocalFormulaAndCodeTerm left right) =
  rawFormulaAndCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthLocalFormulaAndCodeTerm, rawFormulaAndCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalFormulaOrCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthLocalFormulaOrCodeTerm left right) =
  rawFormulaOrCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthLocalFormulaOrCodeTerm, rawFormulaOrCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalFormulaAllCodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthLocalFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthLocalFormulaAllCodeTerm, rawFormulaAllCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalFormulaAll3CodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthLocalFormulaAll3CodeTerm child) =
  rawDynamicTruthLocalFormulaAll3Code M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthLocalFormulaAll3CodeTerm,
    rawDynamicTruthLocalFormulaAll3Code.
  rewrite !raw_eval_dynamicTruthLocalFormulaAllCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalAdmissibleCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain,
  raw_term_eval M e
    (dynamicTruthLocalAdmissibleCodeTerm sigmaDomain piDomain) =
  rawDynamicTruthLocalAdmissibleCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain).
Proof.
  intros. unfold dynamicTruthLocalAdmissibleCodeTerm,
    rawDynamicTruthLocalAdmissibleCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    raw_eval_dynamicTruthLocalFormulaOrCodeTerm,
    !raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalDecisionCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain sigmaEvidence piEvidence,
  raw_term_eval M e
    (dynamicTruthLocalDecisionCodeTerm
      sigmaDomain piDomain sigmaEvidence piEvidence) =
  rawDynamicTruthLocalDecisionCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e sigmaEvidence) (raw_term_eval M e piEvidence).
Proof.
  intros. unfold dynamicTruthLocalDecisionCodeTerm,
    rawDynamicTruthLocalDecisionCode.
  rewrite raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthLocalAdmissibleCodeTerm,
    raw_eval_dynamicTruthLocalFormulaOrCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalExclusiveCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain sigmaEvidence piEvidence,
  raw_term_eval M e
    (dynamicTruthLocalExclusiveCodeTerm
      sigmaDomain piDomain sigmaEvidence piEvidence) =
  rawDynamicTruthLocalExclusiveCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e sigmaEvidence) (raw_term_eval M e piEvidence).
Proof.
  intros. unfold dynamicTruthLocalExclusiveCodeTerm,
    rawDynamicTruthLocalExclusiveCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthLocalAdmissibleCodeTerm,
    raw_eval_rawFormulaBotCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthLocalDecisionExclusiveFieldCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain sigmaEvidence piEvidence,
  raw_term_eval M e
    (dynamicTruthLocalDecisionExclusiveFieldCodeTerm
      sigmaDomain piDomain sigmaEvidence piEvidence) =
  rawDynamicTruthLocalDecisionExclusiveFieldCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e sigmaEvidence) (raw_term_eval M e piEvidence).
Proof.
  intros. unfold dynamicTruthLocalDecisionExclusiveFieldCodeTerm,
    rawDynamicTruthLocalDecisionExclusiveFieldCode.
  rewrite raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    !raw_eval_dynamicTruthLocalFormulaAll3CodeTerm,
    raw_eval_dynamicTruthLocalDecisionCodeTerm,
    raw_eval_dynamicTruthLocalExclusiveCodeTerm. reflexivity.
Qed.

Definition dynamicTruthLocalDecisionExclusiveFieldCodeTermAt
    (output sigmaDomain piDomain sigmaEvidence piEvidence : term) : formula :=
  pEq output
    (dynamicTruthLocalDecisionExclusiveFieldCodeTerm
      sigmaDomain piDomain sigmaEvidence piEvidence).

Lemma raw_sat_dynamicTruthLocalDecisionExclusiveFieldCodeTermAt_iff :
    forall (M : RawPAModel) e
      output sigmaDomain piDomain sigmaEvidence piEvidence,
  raw_formula_sat M e
    (dynamicTruthLocalDecisionExclusiveFieldCodeTermAt
      output sigmaDomain piDomain sigmaEvidence piEvidence) <->
  raw_term_eval M e output =
    rawDynamicTruthLocalDecisionExclusiveFieldCode M
      (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
      (raw_term_eval M e sigmaEvidence) (raw_term_eval M e piEvidence).
Proof.
  intros.
  unfold dynamicTruthLocalDecisionExclusiveFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthLocalDecisionExclusiveFieldCodeTerm
          sigmaDomain piDomain sigmaEvidence piEvidence) <->
    raw_term_eval M e output =
      rawDynamicTruthLocalDecisionExclusiveFieldCode M
        (raw_term_eval M e sigmaDomain)
        (raw_term_eval M e piDomain)
        (raw_term_eval M e sigmaEvidence)
        (raw_term_eval M e piEvidence)).
  rewrite raw_eval_dynamicTruthLocalDecisionExclusiveFieldCodeTerm.
  reflexivity.
Qed.

(** Structural quotation audit for the carrier polynomial. *)
Theorem rawDynamicTruthLocalDecisionExclusiveFieldCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain sigmaEvidence piEvidence,
  rawDynamicTruthLocalDecisionExclusiveFieldCode M
    (rawQuotedFormulaCode M sigmaDomain)
    (rawQuotedFormulaCode M piDomain)
    (rawQuotedFormulaCode M sigmaEvidence)
    (rawQuotedFormulaCode M piEvidence) =
  rawQuotedFormulaCode M
    (dynamicTruthLocalDecisionExclusiveCarrierFormula
      sigmaDomain piDomain sigmaEvidence piEvidence).
Proof.
  intros M hPA sigmaDomain piDomain sigmaEvidence piEvidence.
  unfold rawDynamicTruthLocalDecisionExclusiveFieldCode,
    rawDynamicTruthLocalFormulaAll3Code,
    rawDynamicTruthLocalDecisionCode,
    rawDynamicTruthLocalExclusiveCode,
    rawDynamicTruthLocalAdmissibleCode,
    dynamicTruthLocalDecisionExclusiveCarrierFormula,
    dynamicTruthLocalAdmissibleFormula.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (tVar 0) (tVar 2))).
  reflexivity.
Qed.

(** Standard-point alignment for the positive splice.  A predecessor [p]
    must produce the master-local formula at input level [S p], and that
    formula mentions evidence predicates at [S (S p)].  Keeping both
    successors visible here prevents the former off-by-one construction
    (which rebuilt the input-[p] formula) from satisfying this interface. *)
Corollary
    rawDynamicTruthLocalDecisionExclusiveFieldCode_quoted_successor_level :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthLocalDecisionExclusiveFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 2)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiFalsityCertificateTermAt (S (S predecessor))
        (tVar 2) (tVar 1) (tVar 0))) =
  rawQuotedFormulaCode M
    (fixedLevelLocalDecisionExclusiveBundleFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthLocalDecisionExclusiveFieldCode_quoted
    by exact hPA.
  rewrite dynamicTruthLocalDecisionExclusiveCarrierFormula_fixedLevel.
  reflexivity.
Qed.

(** Keep the verified formula-code polynomial folded in graph proofs. *)
Opaque dynamicTruthLocalDecisionExclusiveFieldCodeTerm.

(** ------------------------------------------------------------------
    The genuine orbit slice at the positive input level [S p].

    Beneath the hidden [inputLevel] witness the environment is

      inputLevel :: globalSigma :: globalPi :: predecessorLevel :: tail.

    The wrapper is intentionally separate and opaque in the outer graph so
    that reducing the one-witness shell never expands the full orbit. *)

Definition dynamicTruthNativeLocalInputOrbitRenaming (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | S (S (S tailIndex)) => S (S (S (S tailIndex)))
  end.

Definition dynamicTruthNativeLocalInputOrbitBodyGraph : formula :=
  Formula.rename dynamicTruthNativeLocalInputOrbitRenaming
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph.

Lemma raw_sat_dynamicTruthNativeLocalInputOrbitBodyGraph_iff : forall
    (M : RawPAModel) tail inputLevel globalSigma globalPi predecessorLevel,
  raw_formula_sat M
    (scons M inputLevel (scons M globalSigma (scons M globalPi
      (scons M predecessorLevel tail))))
    dynamicTruthNativeLocalInputOrbitBodyGraph <->
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M inputLevel tail)))
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Proof.
  intros M tail inputLevel globalSigma globalPi predecessorLevel.
  unfold dynamicTruthNativeLocalInputOrbitBodyGraph.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|tailIndex]]]; reflexivity.
Qed.

Local Opaque dynamicTruthNativeLocalInputOrbitBodyGraph.

Definition dynamicTruthNativeLocalInputOrbitGraph : formula :=
  pEx
    (pAnd
      (pEq (tVar 0) (tSucc (tVar 3)))
      dynamicTruthNativeLocalInputOrbitBodyGraph).

Definition RawDynamicTruthNativeLocalInputOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel globalSigma globalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M predecessorLevel) globalSigma globalPi.

Arguments RawDynamicTruthNativeLocalInputOrbitAt
  M tail predecessorLevel globalSigma globalPi : clear implicits.

Theorem raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M predecessorLevel tail)))
    dynamicTruthNativeLocalInputOrbitGraph <->
  RawDynamicTruthNativeLocalInputOrbitAt M
    tail predecessorLevel globalSigma globalPi.
Proof.
  intros M tail predecessorLevel globalSigma globalPi.
  unfold dynamicTruthNativeLocalInputOrbitGraph,
    RawDynamicTruthNativeLocalInputOrbitAt.
  cbn [raw_formula_sat raw_term_eval scons].
  setoid_rewrite raw_sat_dynamicTruthNativeLocalInputOrbitBodyGraph_iff.
  setoid_rewrite
    raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff.
  split.
  - intros [inputLevel [hlevel horbit]].
    subst inputLevel. exact horbit.
  - intro horbit.
    exists (raw_succ M predecessorLevel).
    split; [reflexivity | exact horbit].
Qed.

(** The standard predecessor [p] is sent to the genuine orbit at [S p]. *)
Corollary raw_sat_dynamicTruthNativeLocalInputOrbitGraph_standard_iff : forall
    (M : RawPAModel) tail predecessor globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M (rawNumeralValue M predecessor) tail)))
    dynamicTruthNativeLocalInputOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor)) globalSigma globalPi.
Proof.
  intros M tail predecessor globalSigma globalPi.
  rewrite raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff.
  change (RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor)) globalSigma globalPi <->
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (rawNumeralValue M (S predecessor)) globalSigma globalPi).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Transform an adequate input-level pair into the exact local target.

    Eight witnesses leave the body environment

      piEvidence :: sigmaEvidence :: piDomain :: sigmaDomain ::
      inputLevelNumeral :: evidenceGlobalPi :: evidenceGlobalSigma ::
      inputLevel :: fieldCode :: inputGlobalSigma :: inputGlobalPi ::
      predecessorLevel :: tail.

    The checked equality [inputLevel = S predecessorLevel] is duplicated at
    the transform boundary on purpose: the source and transform can be
    audited independently, yet must align on the same positive input level. *)

Definition dynamicTruthNativeLocalSuccessorRenaming (index : nat) : nat :=
  match index with
  | 0 => 6
  | 1 => 5
  | 2 => 9
  | 3 => 10
  | 4 => 7
  | S (S (S (S (S tailIndex)))) => 12 + tailIndex
  end.

Definition dynamicTruthNativeLocalTransformEnvironment (M : RawPAModel)
    (piEvidence sigmaEvidence piDomain sigmaDomain inputLevelNumeral
      evidenceGlobalPi evidenceGlobalSigma inputLevel fieldCode
      inputGlobalSigma inputGlobalPi predecessorLevel : M)
    (tail : nat -> M) : nat -> M :=
  scons M piEvidence (scons M sigmaEvidence
    (scons M piDomain (scons M sigmaDomain
      (scons M inputLevelNumeral
        (scons M evidenceGlobalPi (scons M evidenceGlobalSigma
          (scons M inputLevel (scons M fieldCode
            (scons M inputGlobalSigma (scons M inputGlobalPi
              (scons M predecessorLevel tail))))))))))).

Definition dynamicTruthNativeLocalSuccessorBodyGraph : formula :=
  Formula.rename dynamicTruthNativeLocalSuccessorRenaming
    dynamicTruthPairedGlobalSuccessorGraph.

Lemma raw_sat_dynamicTruthNativeLocalSuccessorBodyGraph_iff : forall
    (M : RawPAModel) tail
      piEvidence sigmaEvidence piDomain sigmaDomain inputLevelNumeral
      evidenceGlobalPi evidenceGlobalSigma inputLevel fieldCode
      inputGlobalSigma inputGlobalPi predecessorLevel,
  raw_formula_sat M
    (dynamicTruthNativeLocalTransformEnvironment M
      piEvidence sigmaEvidence piDomain sigmaDomain inputLevelNumeral
      evidenceGlobalPi evidenceGlobalSigma inputLevel fieldCode
      inputGlobalSigma inputGlobalPi predecessorLevel tail)
    dynamicTruthNativeLocalSuccessorBodyGraph <->
  raw_formula_sat M
    (scons M evidenceGlobalSigma (scons M evidenceGlobalPi
      (scons M inputGlobalSigma (scons M inputGlobalPi
        (scons M inputLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph.
Proof.
  intros.
  unfold dynamicTruthNativeLocalSuccessorBodyGraph.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|[|[|tailIndex]]]]];
    cbn [dynamicTruthNativeLocalTransformEnvironment
      dynamicTruthNativeLocalSuccessorRenaming scons]; reflexivity.
Qed.

Local Opaque dynamicTruthNativeLocalSuccessorBodyGraph.
Local Opaque dynamicTruthPairedGlobalSuccessorGraph.
Local Opaque dynamicTruthLocalTernaryApplicationTermAt.

Definition dynamicTruthNativeLocalFieldTransformGraph : formula :=
  fixedLevelEx8
    (pAnd
      (pEq (tVar 7) (tSucc (tVar 11)))
      (pAnd
        dynamicTruthNativeLocalSuccessorBodyGraph
        (fixedLevelAnd6
          (numeralTermCodeAtTermAt (tVar 7) (tVar 4))
          (codedFormulaSingleSubstitutionTermAt
            (tVar 4)
            (Term.numeral
              (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
            (tVar 3))
          (codedFormulaSingleSubstitutionTermAt
            (tVar 4)
            (Term.numeral
              (formulaCode dynamicTruthLocalPiInputDomainTemplate))
            (tVar 2))
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 6) (tVar 1))
          (dynamicTruthLocalTernaryApplicationTermAt
            (tVar 5) (tVar 0))
          (dynamicTruthLocalDecisionExclusiveFieldCodeTermAt
            (tVar 8) (tVar 3) (tVar 2) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthNativeLocalFieldTransformAt
    (M : RawPAModel)
    (inputGlobalSigma inputGlobalPi predecessorLevel fieldCode : M) : Prop :=
  exists inputLevel evidenceGlobalSigma evidenceGlobalPi inputLevelNumeral
      sigmaDomain piDomain sigmaEvidence piEvidence : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      inputGlobalSigma inputGlobalPi inputLevel
      evidenceGlobalSigma evidenceGlobalPi /\
    RawNumeralTermCodeAt M inputLevel inputLevelNumeral /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      piDomain /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalSigma sigmaEvidence /\
    RawDynamicTruthLocalTernaryApplication M
      evidenceGlobalPi piEvidence /\
    fieldCode = rawDynamicTruthLocalDecisionExclusiveFieldCode M
      sigmaDomain piDomain sigmaEvidence piEvidence.

Arguments RawDynamicTruthNativeLocalFieldTransformAt
  M inputGlobalSigma inputGlobalPi predecessorLevel fieldCode
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff : forall
    (M : RawPAModel) tail
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M inputGlobalSigma
      (scons M inputGlobalPi (scons M predecessorLevel tail))))
    dynamicTruthNativeLocalFieldTransformGraph <->
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel fieldCode.
Proof.
  intros M tail inputGlobalSigma inputGlobalPi predecessorLevel fieldCode.
  unfold dynamicTruthNativeLocalFieldTransformGraph,
    RawDynamicTruthNativeLocalFieldTransformAt, fixedLevelEx8,
    fixedLevelAnd6.
  cbn [raw_formula_sat].
  (** Rewriting the successor-body equivalence under all eight existential
      binders makes Rocq's setoid-rewrite machinery traverse the (large)
      native successor graph and can overflow its reduction stack.  We keep
      that graph opaque and transport each conjunct explicitly instead. *)
  split.
  - intros (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & sigmaDomain & piDomain & sigmaEvidence &
      piEvidence & hlevel & hsuccessor & hnumeral & hsigmaDomain &
      hpiDomain & hsigmaEvidence & hpiEvidence & hfield).
    change (inputLevel = raw_succ M predecessorLevel) in hlevel.
    apply (proj1
      (raw_sat_dynamicTruthNativeLocalSuccessorBodyGraph_iff M tail
        piEvidence sigmaEvidence piDomain sigmaDomain inputLevelNumeral
        evidenceGlobalPi evidenceGlobalSigma inputLevel fieldCode
        inputGlobalSigma inputGlobalPi predecessorLevel)) in hsuccessor.
    apply (proj1
      (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
        inputLevel inputGlobalSigma inputGlobalPi evidenceGlobalSigma
        evidenceGlobalPi)) in hsuccessor.
    apply (proj1 (raw_sat_numeralTermCodeAtTermAt_iff M _
      (tVar 7) (tVar 4))) in hnumeral.
    cbn [raw_term_eval scons] in hnumeral.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 4)
      (Term.numeral
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (tVar 3))) in hsigmaDomain.
    rewrite raw_term_eval_numeral in hsigmaDomain.
    cbn [raw_term_eval scons] in hsigmaDomain.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 4)
      (Term.numeral
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (tVar 2))) in hpiDomain.
    rewrite raw_term_eval_numeral in hpiDomain.
    cbn [raw_term_eval scons] in hpiDomain.
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 6) (tVar 1))) in hsigmaEvidence.
    cbn [raw_term_eval scons] in hsigmaEvidence.
    apply (proj1 (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff
      M _ (tVar 5) (tVar 0))) in hpiEvidence.
    cbn [raw_term_eval scons] in hpiEvidence.
    apply (proj1
      (raw_sat_dynamicTruthLocalDecisionExclusiveFieldCodeTermAt_iff M _
        (tVar 8) (tVar 3) (tVar 2) (tVar 1) (tVar 0))) in hfield.
    cbn [raw_term_eval scons] in hfield.
    exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
      inputLevelNumeral, sigmaDomain, piDomain, sigmaEvidence, piEvidence.
    repeat split; assumption.
  - intros (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & sigmaDomain & piDomain & sigmaEvidence &
      piEvidence & hlevel & hsuccessor & hnumeral & hsigmaDomain &
      hpiDomain & hsigmaEvidence & hpiEvidence & hfield).
    exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
      inputLevelNumeral, sigmaDomain, piDomain, sigmaEvidence, piEvidence.
    repeat split.
    + change (inputLevel = raw_succ M predecessorLevel).
      exact hlevel.
    + apply (proj2
        (raw_sat_dynamicTruthNativeLocalSuccessorBodyGraph_iff M tail
          piEvidence sigmaEvidence piDomain sigmaDomain inputLevelNumeral
          evidenceGlobalPi evidenceGlobalSigma inputLevel fieldCode
          inputGlobalSigma inputGlobalPi predecessorLevel)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
          inputLevel inputGlobalSigma inputGlobalPi evidenceGlobalSigma
          evidenceGlobalPi)).
      exact hsuccessor.
    + apply (proj2 (raw_sat_numeralTermCodeAtTermAt_iff M _
        (tVar 7) (tVar 4))).
      cbn [raw_term_eval scons].
      exact hnumeral.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 4)
          (Term.numeral
            (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
          (tVar 3))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons].
      exact hsigmaDomain.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 4)
          (Term.numeral
            (formulaCode dynamicTruthLocalPiInputDomainTemplate))
          (tVar 2))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons].
      exact hpiDomain.
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 6) (tVar 1))).
      cbn [raw_term_eval scons].
      exact hsigmaEvidence.
    + apply (proj2
        (raw_sat_dynamicTruthLocalTernaryApplicationTermAt_iff M _
          (tVar 5) (tVar 0))).
      cbn [raw_term_eval scons].
      exact hpiEvidence.
    + apply (proj2
        (raw_sat_dynamicTruthLocalDecisionExclusiveFieldCodeTermAt_iff M _
          (tVar 8) (tVar 3) (tVar 2) (tVar 1) (tVar 0))).
      cbn [raw_term_eval scons].
      exact hfield.
Qed.

(** The transform really contains the native Sigma-[Or7]/Pi-[Or6] row pair,
    not merely two opaque evidence codes. *)
Theorem raw_dynamicTruthNativeLocalFieldTransformAt_exposes_rows : forall
    (M : RawPAModel) inputGlobalSigma inputGlobalPi predecessorLevel fieldCode,
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel fieldCode ->
  exists inputLevel evidenceGlobalSigma evidenceGlobalPi
      localSigmaRow localPiRow : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedSuccessorRowAt M
      inputGlobalSigma inputGlobalPi inputLevel localSigmaRow localPiRow /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow evidenceGlobalSigma evidenceGlobalPi.
Proof.
  intros M inputGlobalSigma inputGlobalPi predecessorLevel fieldCode
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
     inputLevelNumeral & sigmaDomain & piDomain & sigmaEvidence &
     piEvidence & hlevel & hsuccessor & _).
  destruct hsuccessor as [localSigmaRow [localPiRow [hrows hwrapper]]].
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    localSigmaRow, localPiRow.
  split; [exact hlevel |].
  split; [exact hrows | exact hwrapper].
Qed.

(** Unfolding the paired row relation exposes the two transparent carrier
    polynomials themselves.  Their branch constructors are exactly the
    seven-way Sigma disjunction and six-way Pi disjunction from the native
    successor-row modules. *)
Corollary raw_dynamicTruthNativeLocalFieldTransformAt_row_code_polynomials :
  forall (M : RawPAModel) inputGlobalSigma inputGlobalPi
      predecessorLevel fieldCode,
  RawDynamicTruthNativeLocalFieldTransformAt M
    inputGlobalSigma inputGlobalPi predecessorLevel fieldCode ->
  exists inputLevel localSigmaRow localPiRow
      sigmaNumeral sigmaDomain sigmaLowerApplication
      piNumeral piDomain piLowerApplication : M,
    inputLevel = raw_succ M predecessorLevel /\
    RawNumeralTermCodeAt M (raw_succ M inputLevel) sigmaNumeral /\
    RawCodedFormulaSingleSubstitution M sigmaNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      sigmaDomain /\
    RawDynamicTruthCoqLowerApplication M
      inputGlobalPi sigmaLowerApplication /\
    localSigmaRow = rawDynamicTruthSigmaSuccessorRowCode M
      sigmaDomain sigmaLowerApplication /\
    RawNumeralTermCodeAt M (raw_succ M inputLevel) piNumeral /\
    RawCodedFormulaSingleSubstitution M piNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) piDomain /\
    RawDynamicTruthPiCoqLowerApplication M
      inputGlobalSigma piLowerApplication /\
    localPiRow = rawDynamicTruthPiSuccessorRowCode M
      piDomain piLowerApplication.
Proof.
  intros M inputGlobalSigma inputGlobalPi predecessorLevel fieldCode h.
  destruct (raw_dynamicTruthNativeLocalFieldTransformAt_exposes_rows
    M inputGlobalSigma inputGlobalPi predecessorLevel fieldCode h) as
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
     localSigmaRow & localPiRow & hlevel & [hsigma hpi] & _).
  destruct hsigma as
    (sigmaNumeral & sigmaDomain & sigmaLowerApplication &
     hsigmaNumeral & hsigmaDomain & hsigmaLower & hsigmaRow).
  destruct hpi as
    (piNumeral & piDomain & piLowerApplication &
     hpiNumeral & hpiDomain & hpiLower & hpiRow).
  exists inputLevel, localSigmaRow, localPiRow,
    sigmaNumeral, sigmaDomain, sigmaLowerApplication,
    piNumeral, piDomain, piLowerApplication.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Relational totality of the transform. *)

Lemma raw_dynamicTruthLocalInputDomain_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall level numeralCode template,
  RawNumeralTermCodeAt M level numeralCode ->
  exists domain,
    RawCodedFormulaSingleSubstitution M numeralCode
      (rawNumeralValue M (formulaCode template)) domain /\
    RawCodedFormulaAtomicallyAdequate M domain.
Proof.
  intros M hPA level numeralCode template hnumeral.
  exact (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA (raw_codedTermOpening_total M hPA)
    (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M (formulaCode template))
    (raw_fixedFormulaNumeral_atomically_adequate M hPA template)
    numeralCode (raw_zero M) (raw_zero M)
    (raw_numeralTermCode_syntax_realizable_zero M hPA
      level numeralCode hnumeral)).
Qed.

Definition RawDynamicTruthNativeLocalFieldTransformTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) inputGlobalSigma inputGlobalPi predecessorLevel,
    RawCodedFormulaAtomicallyAdequate M inputGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M inputGlobalPi ->
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M inputGlobalSigma
          (scons M inputGlobalPi (scons M predecessorLevel tail))))
        dynamicTruthNativeLocalFieldTransformGraph.

Arguments RawDynamicTruthNativeLocalFieldTransformTotalOnAdequate M
  : clear implicits.

Theorem dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalFieldTransformTotalOnAdequate M.
Proof.
  intros M hPA tail inputGlobalSigma inputGlobalPi predecessorLevel
    hinputSigma hinputPi.
  set (inputLevel := raw_succ M predecessorLevel).
  destruct (dynamicTruthPairedGlobalSuccessorGraph_raw_adequate_total
    M hPA tail inputLevel inputGlobalSigma inputGlobalPi
    hinputSigma hinputPi) as
    (evidenceGlobalSigma & evidenceGlobalPi & hsuccessor &
     hevidenceSigma & hevidencePi).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail inputLevel
      inputGlobalSigma inputGlobalPi evidenceGlobalSigma evidenceGlobalPi)
    hsuccessor) as hsuccessorAt.
  destruct (raw_numeralTermCodeExists_all M hPA inputLevel) as
    [inputLevelNumeral hinputLevelNumeral].
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA inputLevel inputLevelNumeral
    dynamicTruthLocalSigmaInputDomainTemplate hinputLevelNumeral) as
    (sigmaDomain & hsigmaDomain & _hsigmaDomainAdequate).
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA inputLevel inputLevelNumeral
    dynamicTruthLocalPiInputDomainTemplate hinputLevelNumeral) as
    (piDomain & hpiDomain & _hpiDomainAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA evidenceGlobalSigma hevidenceSigma) as
    (sigmaEvidence & hsigmaEvidence & _hsigmaEvidenceAdequate).
  destruct (raw_dynamicTruthLocalTernaryApplication_exists_adequate
    M hPA evidenceGlobalPi hevidencePi) as
    (piEvidence & hpiEvidence & _hpiEvidenceAdequate).
  exists (rawDynamicTruthLocalDecisionExclusiveFieldCode M
    sigmaDomain piDomain sigmaEvidence piEvidence).
  apply (proj2
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
      inputGlobalSigma inputGlobalPi predecessorLevel _)).
  exists inputLevel, evidenceGlobalSigma, evidenceGlobalPi,
    inputLevelNumeral, sigmaDomain, piDomain, sigmaEvidence, piEvidence.
  split; [unfold inputLevel; reflexivity |].
  split; [exact hsuccessorAt |].
  split; [exact hinputLevelNumeral |].
  split; [exact hsigmaDomain |].
  split; [exact hpiDomain |].
  split; [exact hsigmaEvidence |].
  split; [exact hpiEvidence | reflexivity].
Qed.

(** ------------------------------------------------------------------
    Composition with the genuine paired orbit at [S p]. *)

Definition dynamicTruthNativeLocalPositiveGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthNativeLocalInputOrbitGraph
    dynamicTruthNativeLocalFieldTransformGraph.

Definition RawDynamicTruthNativeLocalPositiveAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists inputGlobalSigma inputGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (raw_succ M predecessorLevel)
      inputGlobalSigma inputGlobalPi /\
    RawDynamicTruthNativeLocalFieldTransformAt M
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode.

Arguments RawDynamicTruthNativeLocalPositiveAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthNativeLocalPositiveGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthNativeLocalPositiveGraph <->
  RawDynamicTruthNativeLocalPositiveAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthNativeLocalPositiveGraph,
    RawDynamicTruthNativeLocalPositiveAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (inputGlobalSigma & inputGlobalPi & horbit & htransform).
    exists inputGlobalSigma, inputGlobalPi. split.
    + apply (proj1 (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff
        M tail predecessorLevel inputGlobalSigma inputGlobalPi)).
      exact horbit.
    + apply (proj1 (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff
        M tail inputGlobalSigma inputGlobalPi predecessorLevel fieldCode)).
      exact htransform.
  - intros (inputGlobalSigma & inputGlobalPi & horbit & htransform).
    exists inputGlobalSigma, inputGlobalPi. split.
    + apply (proj2 (raw_sat_dynamicTruthNativeLocalInputOrbitGraph_iff
        M tail predecessorLevel inputGlobalSigma inputGlobalPi)).
      exact horbit.
    + apply (proj2 (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff
        M tail inputGlobalSigma inputGlobalPi predecessorLevel fieldCode)).
      exact htransform.
Qed.

Definition RawDynamicTruthNativeLocalPositiveTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeLocalPositiveGraph.

Arguments RawDynamicTruthNativeLocalPositiveTotal M : clear implicits.

Theorem dynamicTruthNativeLocalPositiveGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalPositiveTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (inputGlobalSigma & inputGlobalPi & horbit &
     hinputSigma & hinputPi).
  destruct (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
    M hPA tail inputGlobalSigma inputGlobalPi predecessorLevel
    hinputSigma hinputPi) as [fieldCode htransform].
  exists fieldCode.
  apply (proj2 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists inputGlobalSigma, inputGlobalPi. split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi)).
    exact horbit.
  - apply (proj1 (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff
      M tail inputGlobalSigma inputGlobalPi predecessorLevel fieldCode)).
    exact htransform.
Qed.

(** ------------------------------------------------------------------
    The exact remaining proof-producing boundary.

    Relational totality selects a transparent target but cannot turn truth
    in all PA models into a represented proof at a possibly nonstandard
    carrier index.  The interface below asks for a compiler on the exact
    adequate orbit witness and exact transform trace selected above. *)

Definition RawDynamicTruthNativeLocalDecisionExclusiveProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      inputGlobalSigma inputGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      inputGlobalSigma inputGlobalPi ->
    RawDynamicTruthNativeLocalFieldTransformAt M
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeLocalDecisionExclusiveProofCompiler M
  : clear implicits.

Definition RawDynamicTruthNativeLocalPositiveProofTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeLocalPositiveGraph /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeLocalPositiveProofTotal M : clear implicits.

Theorem dynamicTruthNativeLocalPositiveGraph_raw_proof_total_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalDecisionExclusiveProofCompiler M ->
  RawDynamicTruthNativeLocalPositiveProofTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (inputGlobalSigma & inputGlobalPi & horbit &
     hinputSigma & hinputPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M
          tail (raw_succ M predecessorLevel)
          inputGlobalSigma inputGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct (dynamicTruthNativeLocalFieldTransformGraph_raw_total_on_adequate
    M hPA tail inputGlobalSigma inputGlobalPi predecessorLevel
    hinputSigma hinputPi) as [fieldCode htransformSat].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeLocalFieldTransformGraph_iff M tail
      inputGlobalSigma inputGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler tail predecessorLevel inputGlobalSigma inputGlobalPi
    fieldCode hadequateOrbit htransform) as [certificate hcertificate].
  exists fieldCode, certificate. split; [|exact hcertificate].
  apply (proj2 (raw_sat_dynamicTruthNativeLocalPositiveGraph_iff
    M tail predecessorLevel fieldCode)).
  exists inputGlobalSigma, inputGlobalPi. split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
        tail (raw_succ M predecessorLevel)
        inputGlobalSigma inputGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

End PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
