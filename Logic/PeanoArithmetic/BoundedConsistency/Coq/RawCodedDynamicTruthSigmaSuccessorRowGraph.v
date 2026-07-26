(**
  A concrete carrier-indexed code graph for the Sigma successor row.

  The native Rocq partial-truth construction is polarity aware.  A Sigma
  successor row consumes the *Pi-falsity* predicate from the preceding
  level; dually, a Pi row consumes the preceding Sigma-truth predicate.  This
  module implements the first of those two honest structural transformers.
  It does not identify the two predicates and it does not insert a fallback
  code for malformed inputs.

  The public graph is read under

      next :: previousPi :: lowerLevel :: tail.

  It builds the code of the eight-witness Sigma row used by Coq's four-table
  certificate.  Its upper rank bound is the represented numeral for
  [lowerLevel + 1], while its universal clause applies [previousPi] to the
  child formula and the freshly prepended assignment.  Thus every quantity
  that can be nonstandard remains a carrier element.

  The row environment, before its eight witnesses, is

      assignmentStep :: assignmentCode :: formulaCode :: mode :: rowIndex ::
      assignmentStepStep :: assignmentStepCode ::
      assignmentCodeStep :: assignmentCodeCode ::
      formulaStep :: formulaCodeTable :: modeStep :: modeCode :: tail.

  The [mode] slot is deliberately retained even though this component checks
  the Sigma branch.  It makes the generated row fit literally beneath the
  five universal row binders of [fixedLevelSuccessorTruthTraversalRowsTermAt].
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaOperations RawCodedFormulaOperationsStandardRealization
  RawCodedNumeralTermCode
  RawCodedRankZeroTruthTraversal RawCodedFixedLevelTruth
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedCarrierIndexedCodeOrbitGraph.

Module PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedCarrierIndexedCodeOrbitGraph.

(** ------------------------------------------------------------------
    Application of the lower Pi predicate in the native Coq row layout.

    Beneath the row's eight witnesses and the binder-extension witnesses,
    the lower ternary predicate must read variables [#9], [#1], and [#0].
    Three ordinary one-variable substitutions realize that renaming.  The
    first two replacement indices compensate for the two later binder
    removals, exactly as in [dynamicTruthTernaryApplicationGraph]. *)

Definition dynamicTruthCoqLowerFirstReplacement : term := tVar 11.
Definition dynamicTruthCoqLowerSecondReplacement : term := tVar 2.
Definition dynamicTruthCoqLowerThirdReplacement : term := tVar 0.

Definition dynamicTruthCoqLowerFirstReplacementCode : term :=
  Term.numeral (termCode dynamicTruthCoqLowerFirstReplacement).

Definition dynamicTruthCoqLowerSecondReplacementCode : term :=
  Term.numeral (termCode dynamicTruthCoqLowerSecondReplacement).

Definition dynamicTruthCoqLowerThirdReplacementCode : term :=
  Term.numeral (termCode dynamicTruthCoqLowerThirdReplacement).

(** Term-parametric form, useful inside a larger represented graph.  The two
    hidden variables are the intermediate formula codes. *)
Definition dynamicTruthCoqLowerApplicationTermAt
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        dynamicTruthCoqLowerFirstReplacementCode
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthCoqLowerSecondReplacementCode
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthCoqLowerThirdReplacementCode
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthCoqLowerApplication (M : RawPAModel)
    (input output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthCoqLowerFirstReplacement))
      input first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthCoqLowerSecondReplacement))
      first second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthCoqLowerThirdReplacement))
      second output.

Arguments RawDynamicTruthCoqLowerApplication M input output
  : clear implicits.

Theorem raw_sat_dynamicTruthCoqLowerApplicationTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (dynamicTruthCoqLowerApplicationTermAt input output) <->
  RawDynamicTruthCoqLowerApplication M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold dynamicTruthCoqLowerApplicationTermAt,
    RawDynamicTruthCoqLowerApplication,
    dynamicTruthCoqLowerFirstReplacementCode,
    dynamicTruthCoqLowerSecondReplacementCode,
    dynamicTruthCoqLowerThirdReplacementCode.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons].
  split; intro h; exact h.
Qed.

Definition standardDynamicTruthCoqLowerApplication (input : formula) :
    formula :=
  Formula.subst
    (Formula.instTerm dynamicTruthCoqLowerThirdReplacement)
    (Formula.subst
      (Formula.instTerm dynamicTruthCoqLowerSecondReplacement)
      (Formula.subst
        (Formula.instTerm dynamicTruthCoqLowerFirstReplacement)
        input)).

Definition dynamicTruthCoqLowerApplicationRenaming (index : nat) : nat :=
  match index with
  | 0 => 9
  | 1 => 1
  | 2 => 0
  | S (S (S tailIndex)) => tailIndex
  end.

Definition DynamicTruthCoqLowerScoped (input : formula) : Prop :=
  forall index, Formula.Free index input -> index < 3.

Arguments DynamicTruthCoqLowerScoped input : clear implicits.

(** This literal syntactic equality is the de Bruijn audit for the three
    sequential substitutions. *)
Theorem standardDynamicTruthCoqLowerApplication_eq_rename : forall input,
  DynamicTruthCoqLowerScoped input ->
  standardDynamicTruthCoqLowerApplication input =
    Formula.rename dynamicTruthCoqLowerApplicationRenaming input.
Proof.
  intros input hscope.
  unfold standardDynamicTruthCoqLowerApplication.
  rewrite !Formula.subst_comp.
  rewrite <- Formula.subst_var_rename.
  apply Formula.subst_ext_free.
  intros index hfree.
  specialize (hscope index hfree).
  destruct index as [|[|[|tailIndex]]];
    cbn [Formula.instTerm dynamicTruthCoqLowerFirstReplacement
      dynamicTruthCoqLowerSecondReplacement
      dynamicTruthCoqLowerThirdReplacement
      dynamicTruthCoqLowerApplicationRenaming Term.subst];
    try reflexivity; lia.
Qed.

(** Standard formula inputs realize the three checked operation trees.  This
    theorem is only an adequacy audit; the public graph itself accepts
    carrier-valued inputs and never recurses over this [formula]. *)
Theorem raw_dynamicTruthCoqLowerApplication_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawDynamicTruthCoqLowerApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (standardDynamicTruthCoqLowerApplication input)).
Proof.
  intros M hPA input.
  unfold standardDynamicTruthCoqLowerApplication.
  set (first := Formula.subst
    (Formula.instTerm dynamicTruthCoqLowerFirstReplacement) input).
  set (second := Formula.subst
    (Formula.instTerm dynamicTruthCoqLowerSecondReplacement) first).
  exists (rawQuotedFormulaCode M first),
    (rawQuotedFormulaCode M second).
  split.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthCoqLowerFirstReplacement).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      dynamicTruthCoqLowerFirstReplacement input).
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthCoqLowerSecondReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthCoqLowerSecondReplacement first).
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthCoqLowerThirdReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthCoqLowerThirdReplacement second).
Qed.

Corollary raw_dynamicTruthCoqLowerApplication_standard_rename : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  DynamicTruthCoqLowerScoped input ->
  RawDynamicTruthCoqLowerApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (Formula.rename dynamicTruthCoqLowerApplicationRenaming input)).
Proof.
  intros M hPA input hscope.
  rewrite <- (standardDynamicTruthCoqLowerApplication_eq_rename
    input hscope).
  exact (raw_dynamicTruthCoqLowerApplication_standard M hPA input).
Qed.

(** ------------------------------------------------------------------
    The fixed local alternatives in the eight-witness row environment. *)

Definition dynamicTruthSigmaRowQfFormula : formula :=
  rankZeroTruthCertificateTermAt
    (tVar 10) (Term.numeral 1) (tVar 9) (tVar 8).

Definition dynamicTruthSigmaRowImpFalseLeftFormula : formula :=
  fixedLevelAnd3
    (formulaImpCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) (Term.numeral 1) (tVar 6)
      (tVar 9) (tVar 8))
    (pEq (tVar 0) (tVar 0)).

Definition dynamicTruthSigmaRowImpTrueRightFormula : formula :=
  fixedLevelAnd3
    (formulaImpCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 5) tZero (tVar 4)
      (tVar 9) (tVar 8))
    (pEq (tVar 0) (tVar 0)).

Definition dynamicTruthSigmaRowAndFormula : formula :=
  fixedLevelAnd3
    (formulaAndCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) tZero (tVar 6)
      (tVar 9) (tVar 8))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 5) tZero (tVar 4)
      (tVar 9) (tVar 8)).

Definition dynamicTruthSigmaRowOrFormula : formula :=
  pAnd
    (formulaOrCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (pOr
      (dynamicTruthStateMemberTermAt
        (tVar 20) (tVar 19) (tVar 18) (tVar 17)
        (tVar 16) (tVar 15) (tVar 14) (tVar 13)
        (tVar 12) (tVar 7) tZero (tVar 6)
        (tVar 9) (tVar 8))
      (dynamicTruthStateMemberTermAt
        (tVar 20) (tVar 19) (tVar 18) (tVar 17)
        (tVar 16) (tVar 15) (tVar 14) (tVar 13)
        (tVar 12) (tVar 5) tZero (tVar 4)
        (tVar 9) (tVar 8))).

Definition dynamicTruthSigmaRowExFormula : formula :=
  fixedLevelAnd3
    (formulaExCodeTermAt (tVar 10) (tVar 6))
    (codedAssignmentPrependTermAt
      (tVar 9) (tVar 8) (tVar 3) (tVar 10) (tVar 2) (tVar 1))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) tZero (tVar 6)
      (tVar 2) (tVar 1)).

Definition dynamicTruthSigmaRowUniversalPrefixFormula : formula :=
  dynamicTruthUniversalPrefixTermAt (tVar 10) (tVar 6).

(** The fixed first conjunct underneath the three binder-extension
    witnesses.  The dynamic lower application is conjoined to this code. *)
Definition dynamicTruthSigmaRowBinderPrependFormula : formula :=
  codedAssignmentPrependTermAt
    (liftTerm 3 (tVar 9)) (liftTerm 3 (tVar 8))
    (tVar 2) (liftTerm 3 (tVar 10)) (tVar 1) (tVar 0).

(** The domain template reserves variable zero for a closed numeral term.
    Its formula-code variable is [#11], so single substitution removes the
    placeholder and leaves that code at [#10], exactly where the eight-row
    witness layout expects it. *)
Definition dynamicTruthSigmaRowDomainTemplate : formula :=
  dynamicTruthSigmaRecordDomainTermAt (tVar 0) (tVar 11).

(** Naming this large fixed code prevents conversion from repeatedly
    normalizing the complete formula tree when comparing graph atoms. *)
Definition dynamicTruthSigmaRowDomainTemplateCode : nat :=
  formulaCode dynamicTruthSigmaRowDomainTemplate.

Definition dynamicTruthSigmaRowInstantiatedDomain
    (upperNumeral : term) : formula :=
  Formula.subst (Formula.instTerm upperNumeral)
    dynamicTruthSigmaRowDomainTemplate.

(** Formula-level reference construction.  This is used only to specify the
    exact syntax computed by the raw graph; recursion over hierarchy levels
    never occurs here. *)
Definition dynamicTruthSigmaSuccessorRowFormula
    (upperNumeral : term) (lowerPi : formula) : formula :=
  fixedLevelEx8
    (pAnd
      (dynamicTruthSigmaRowInstantiatedDomain upperNumeral)
      (fixedLevelOr7
        dynamicTruthSigmaRowQfFormula
        dynamicTruthSigmaRowImpFalseLeftFormula
        dynamicTruthSigmaRowImpTrueRightFormula
        dynamicTruthSigmaRowAndFormula
        dynamicTruthSigmaRowOrFormula
        dynamicTruthSigmaRowExFormula
        (pAnd dynamicTruthSigmaRowUniversalPrefixFormula
          (fixedLevelNoBinderCounterexampleTermAt
            (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
            (tVar 9) (tVar 8) (tVar 10))))).

(** ------------------------------------------------------------------
    Transparent formula-code terms. *)

Definition formulaImpCodeTerm (left right : term) : term :=
  codeList3Term (Term.numeral 2) left right.

Definition formulaAndCodeTerm (left right : term) : term :=
  codeList3Term (Term.numeral 3) left right.

Definition formulaOrCodeTerm (left right : term) : term :=
  codeList3Term (Term.numeral 4) left right.

Definition formulaExCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 6) child.

Definition formulaEx3CodeTerm (child : term) : term :=
  formulaExCodeTerm (formulaExCodeTerm (formulaExCodeTerm child)).

Definition formulaEx8CodeTerm (child : term) : term :=
  formulaExCodeTerm (formulaExCodeTerm (formulaExCodeTerm
    (formulaExCodeTerm (formulaExCodeTerm (formulaExCodeTerm
      (formulaExCodeTerm (formulaExCodeTerm child))))))).

Definition fixedFormulaNumeralCodeTerm (phi : formula) : term :=
  Term.numeral (formulaCode phi).

Definition dynamicTruthSigmaNoBinderCodeTerm
    (lowerApplication : term) : term :=
  formulaImpCodeTerm
    (formulaEx3CodeTerm
      (formulaAndCodeTerm
        (fixedFormulaNumeralCodeTerm
          dynamicTruthSigmaRowBinderPrependFormula)
        lowerApplication))
    rawFormulaBotCodeTerm.

Definition dynamicTruthSigmaUniversalCodeTerm
    (lowerApplication : term) : term :=
  formulaAndCodeTerm
    (fixedFormulaNumeralCodeTerm
      dynamicTruthSigmaRowUniversalPrefixFormula)
    (dynamicTruthSigmaNoBinderCodeTerm lowerApplication).

Definition dynamicTruthSigmaBranchesCodeTerm
    (lowerApplication : term) : term :=
  formulaOrCodeTerm
    (fixedFormulaNumeralCodeTerm dynamicTruthSigmaRowQfFormula)
    (formulaOrCodeTerm
      (fixedFormulaNumeralCodeTerm
        dynamicTruthSigmaRowImpFalseLeftFormula)
      (formulaOrCodeTerm
        (fixedFormulaNumeralCodeTerm
          dynamicTruthSigmaRowImpTrueRightFormula)
        (formulaOrCodeTerm
          (fixedFormulaNumeralCodeTerm dynamicTruthSigmaRowAndFormula)
          (formulaOrCodeTerm
            (fixedFormulaNumeralCodeTerm dynamicTruthSigmaRowOrFormula)
            (formulaOrCodeTerm
              (fixedFormulaNumeralCodeTerm dynamicTruthSigmaRowExFormula)
              (dynamicTruthSigmaUniversalCodeTerm lowerApplication)))))).

Definition dynamicTruthSigmaSuccessorRowCodeTerm
    (domain lowerApplication : term) : term :=
  formulaEx8CodeTerm
    (formulaAndCodeTerm domain
      (dynamicTruthSigmaBranchesCodeTerm lowerApplication)).

(** Carrier counterpart of the preceding fixed polynomial term. *)
Definition rawFixedFormulaNumeralCode (M : RawPAModel)
    (phi : formula) : M :=
  rawNumeralValue M (formulaCode phi).

Definition rawFormulaEx3Code (M : RawPAModel) (child : M) : M :=
  rawFormulaExCode M (rawFormulaExCode M (rawFormulaExCode M child)).

Definition rawFormulaEx8Code (M : RawPAModel) (child : M) : M :=
  rawFormulaExCode M (rawFormulaExCode M (rawFormulaExCode M
    (rawFormulaExCode M (rawFormulaExCode M (rawFormulaExCode M
      (rawFormulaExCode M (rawFormulaExCode M child))))))).

Definition rawDynamicTruthSigmaNoBinderCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawFormulaEx3Code M
      (rawFormulaAndCode M
        (rawFixedFormulaNumeralCode M
          dynamicTruthSigmaRowBinderPrependFormula)
        lowerApplication))
    (rawFormulaBotCode M).

Definition rawDynamicTruthSigmaUniversalCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaAndCode M
    (rawFixedFormulaNumeralCode M
      dynamicTruthSigmaRowUniversalPrefixFormula)
    (rawDynamicTruthSigmaNoBinderCode M lowerApplication).

Definition rawDynamicTruthSigmaBranchesCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaOrCode M
    (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowQfFormula)
    (rawFormulaOrCode M
      (rawFixedFormulaNumeralCode M
        dynamicTruthSigmaRowImpFalseLeftFormula)
      (rawFormulaOrCode M
        (rawFixedFormulaNumeralCode M
          dynamicTruthSigmaRowImpTrueRightFormula)
        (rawFormulaOrCode M
          (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowAndFormula)
          (rawFormulaOrCode M
            (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowOrFormula)
            (rawFormulaOrCode M
              (rawFixedFormulaNumeralCode M dynamicTruthSigmaRowExFormula)
              (rawDynamicTruthSigmaUniversalCode M lowerApplication)))))).

Definition rawDynamicTruthSigmaSuccessorRowCode (M : RawPAModel)
    (domain lowerApplication : M) : M :=
  rawFormulaEx8Code M
    (rawFormulaAndCode M domain
      (rawDynamicTruthSigmaBranchesCode M lowerApplication)).

Lemma raw_eval_formulaImpCodeTerm : forall (M : RawPAModel) e left right,
  raw_term_eval M e (formulaImpCodeTerm left right) =
  rawFormulaImpCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaImpCodeTerm, rawFormulaImpCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_formulaAndCodeTerm : forall (M : RawPAModel) e left right,
  raw_term_eval M e (formulaAndCodeTerm left right) =
  rawFormulaAndCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaAndCodeTerm, rawFormulaAndCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_formulaOrCodeTerm : forall (M : RawPAModel) e left right,
  raw_term_eval M e (formulaOrCodeTerm left right) =
  rawFormulaOrCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaOrCodeTerm, rawFormulaOrCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_formulaExCodeTerm : forall (M : RawPAModel) e child,
  raw_term_eval M e (formulaExCodeTerm child) =
  rawFormulaExCode M (raw_term_eval M e child).
Proof.
  intros. unfold formulaExCodeTerm, rawFormulaExCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_formulaEx3CodeTerm : forall (M : RawPAModel) e child,
  raw_term_eval M e (formulaEx3CodeTerm child) =
  rawFormulaEx3Code M (raw_term_eval M e child).
Proof.
  intros. unfold formulaEx3CodeTerm, rawFormulaEx3Code.
  rewrite !raw_eval_formulaExCodeTerm. reflexivity.
Qed.

Lemma raw_eval_formulaEx8CodeTerm : forall (M : RawPAModel) e child,
  raw_term_eval M e (formulaEx8CodeTerm child) =
  rawFormulaEx8Code M (raw_term_eval M e child).
Proof.
  intros. unfold formulaEx8CodeTerm, rawFormulaEx8Code.
  rewrite !raw_eval_formulaExCodeTerm. reflexivity.
Qed.

Lemma raw_eval_fixedFormulaNumeralCodeTerm : forall
    (M : RawPAModel) e phi,
  raw_term_eval M e (fixedFormulaNumeralCodeTerm phi) =
  rawFixedFormulaNumeralCode M phi.
Proof.
  intros. unfold fixedFormulaNumeralCodeTerm,
    rawFixedFormulaNumeralCode.
  apply raw_term_eval_numeral.
Qed.

Lemma raw_eval_dynamicTruthSigmaNoBinderCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaNoBinderCodeTerm lowerApplication) =
  rawDynamicTruthSigmaNoBinderCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthSigmaNoBinderCodeTerm,
    rawDynamicTruthSigmaNoBinderCode.
  rewrite raw_eval_formulaImpCodeTerm,
    raw_eval_formulaEx3CodeTerm,
    raw_eval_formulaAndCodeTerm,
    raw_eval_fixedFormulaNumeralCodeTerm,
    raw_eval_rawFormulaBotCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaUniversalCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaUniversalCodeTerm lowerApplication) =
  rawDynamicTruthSigmaUniversalCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthSigmaUniversalCodeTerm,
    rawDynamicTruthSigmaUniversalCode.
  rewrite raw_eval_formulaAndCodeTerm,
    raw_eval_fixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthSigmaNoBinderCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaBranchesCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaBranchesCodeTerm lowerApplication) =
  rawDynamicTruthSigmaBranchesCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthSigmaBranchesCodeTerm,
    rawDynamicTruthSigmaBranchesCode.
  rewrite !raw_eval_formulaOrCodeTerm,
    !raw_eval_fixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthSigmaUniversalCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthSigmaSuccessorRowCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthSigmaSuccessorRowCodeTerm domain lowerApplication) =
  rawDynamicTruthSigmaSuccessorRowCode M
    (raw_term_eval M e domain) (raw_term_eval M e lowerApplication).
Proof.
  intros M e domain lowerApplication.
  unfold dynamicTruthSigmaSuccessorRowCodeTerm,
    rawDynamicTruthSigmaSuccessorRowCode.
  rewrite raw_eval_formulaEx8CodeTerm,
    raw_eval_formulaAndCodeTerm,
    raw_eval_dynamicTruthSigmaBranchesCodeTerm.
  reflexivity.
Qed.

Definition dynamicTruthSigmaSuccessorRowCodeTermAt
    (output domain lowerApplication : term) : formula :=
  pEq output
    (dynamicTruthSigmaSuccessorRowCodeTerm domain lowerApplication).

Lemma raw_sat_dynamicTruthSigmaSuccessorRowCodeTermAt_iff : forall
    (M : RawPAModel) e output domain lowerApplication,
  raw_formula_sat M e
      (dynamicTruthSigmaSuccessorRowCodeTermAt
        output domain lowerApplication) <->
  raw_term_eval M e output =
    rawDynamicTruthSigmaSuccessorRowCode M
      (raw_term_eval M e domain)
      (raw_term_eval M e lowerApplication).
Proof.
  intros M e output domain lowerApplication.
  unfold dynamicTruthSigmaSuccessorRowCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthSigmaSuccessorRowCodeTerm domain lowerApplication) <->
    raw_term_eval M e output =
      rawDynamicTruthSigmaSuccessorRowCode M
        (raw_term_eval M e domain)
        (raw_term_eval M e lowerApplication)).
  rewrite raw_eval_dynamicTruthSigmaSuccessorRowCodeTerm.
  reflexivity.
Qed.

(** In a PA model the fixed numeral leaves used by the polynomial assembler
    are the genuine structural quotations of the displayed formulas. *)
Lemma rawFixedFormulaNumeralCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  rawFixedFormulaNumeralCode M phi = rawQuotedFormulaCode M phi.
Proof.
  intros M hPA phi.
  unfold rawFixedFormulaNumeralCode.
  symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthSigmaNoBinderCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerPi,
  rawDynamicTruthSigmaNoBinderCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)) =
    rawQuotedFormulaCode M
      (fixedLevelNoBinderCounterexampleTermAt
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
        (tVar 9) (tVar 8) (tVar 10)).
Proof.
  intros M hPA lowerPi.
  unfold rawDynamicTruthSigmaNoBinderCode,
    rawFormulaEx3Code, fixedLevelNoBinderCounterexampleTermAt,
    fixedLevelEx3, dynamicTruthSigmaRowBinderPrependFormula.
  cbn [rawQuotedFormulaCode].
  rewrite rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaUniversalCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerPi,
  rawDynamicTruthSigmaUniversalCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)) =
    rawQuotedFormulaCode M
      (pAnd dynamicTruthSigmaRowUniversalPrefixFormula
        (fixedLevelNoBinderCounterexampleTermAt
          (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
          (tVar 9) (tVar 8) (tVar 10))).
Proof.
  intros M hPA lowerPi.
  unfold rawDynamicTruthSigmaUniversalCode.
  cbn [rawQuotedFormulaCode].
  rewrite rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  rewrite rawDynamicTruthSigmaNoBinderCode_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaBranchesCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerPi,
  rawDynamicTruthSigmaBranchesCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)) =
    rawQuotedFormulaCode M
      (fixedLevelOr7
        dynamicTruthSigmaRowQfFormula
        dynamicTruthSigmaRowImpFalseLeftFormula
        dynamicTruthSigmaRowImpTrueRightFormula
        dynamicTruthSigmaRowAndFormula
        dynamicTruthSigmaRowOrFormula
        dynamicTruthSigmaRowExFormula
        (pAnd dynamicTruthSigmaRowUniversalPrefixFormula
          (fixedLevelNoBinderCounterexampleTermAt
            (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
            (tVar 9) (tVar 8) (tVar 10)))).
Proof.
  intros M hPA lowerPi.
  unfold rawDynamicTruthSigmaBranchesCode, fixedLevelOr7.
  cbn [rawQuotedFormulaCode].
  repeat rewrite rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  rewrite rawDynamicTruthSigmaUniversalCode_quoted by exact hPA.
  reflexivity.
Qed.

(** Hence the raw polynomial is not merely some well-formed formula code: on
    standard syntax inputs it is the literal quotation of the native Coq
    eight-witness Sigma successor row. *)
Theorem rawDynamicTruthSigmaSuccessorRowCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall upperNumeral lowerPi,
  rawDynamicTruthSigmaSuccessorRowCode M
      (rawQuotedFormulaCode M
        (dynamicTruthSigmaRowInstantiatedDomain upperNumeral))
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)) =
    rawQuotedFormulaCode M
      (dynamicTruthSigmaSuccessorRowFormula upperNumeral lowerPi).
Proof.
  intros M hPA upperNumeral lowerPi.
  unfold rawDynamicTruthSigmaSuccessorRowCode,
    rawFormulaEx8Code, dynamicTruthSigmaSuccessorRowFormula,
    fixedLevelEx8.
  cbn [rawQuotedFormulaCode].
  rewrite rawDynamicTruthSigmaBranchesCode_quoted by exact hPA.
  reflexivity.
Qed.

Theorem raw_dynamicTruthSigmaRowInstantiatedDomain_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall upperNumeral,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M upperNumeral)
    (rawNumeralValue M
      dynamicTruthSigmaRowDomainTemplateCode)
    (rawQuotedFormulaCode M
      (dynamicTruthSigmaRowInstantiatedDomain upperNumeral)).
Proof.
  intros M hPA upperNumeral.
  unfold dynamicTruthSigmaRowInstantiatedDomain.
  unfold dynamicTruthSigmaRowDomainTemplateCode.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    dynamicTruthSigmaRowDomainTemplate).
  exact (raw_codedFormulaSingleSubstitution_standard M hPA
    upperNumeral dynamicTruthSigmaRowDomainTemplate).
Qed.

(** Keep the already verified fixed polynomial opaque while reducing the
    semantics of the surrounding graph.  Otherwise [cbn] expands eight
    quantifiers and six nested disjunction codes at once and can overflow
    Rocq's reduction stack before the dedicated evaluation lemma is used. *)
Opaque dynamicTruthSigmaSuccessorRowCodeTerm.
Opaque dynamicTruthSigmaRowDomainTemplateCode.

(** ------------------------------------------------------------------
    The represented successor graph and its exact raw semantics. *)

(** Three witnesses are [upperNumeralCode], [domainCode], and
    [lowerApplicationCode], from outermost to innermost.  At the body the
    environment is

      lowerApplication :: domain :: upperNumeral ::
      next :: previousPi :: lowerLevel :: tail.
*)
Definition dynamicTruthSigmaSuccessorRowGraph : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 5)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral dynamicTruthSigmaRowDomainTemplateCode)
        (tVar 1))
      (dynamicTruthCoqLowerApplicationTermAt (tVar 4) (tVar 0))
      (pEq (tVar 3)
        (dynamicTruthSigmaSuccessorRowCodeTerm
          (tVar 1) (tVar 0)))))).

Definition RawDynamicTruthSigmaSuccessorRowAt (M : RawPAModel)
    (previousPi lowerLevel next : M) : Prop :=
  exists upperNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M (raw_succ M lowerLevel) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M
        dynamicTruthSigmaRowDomainTemplateCode) domain /\
    RawDynamicTruthCoqLowerApplication M previousPi lowerApplication /\
    next = rawDynamicTruthSigmaSuccessorRowCode M
      domain lowerApplication.

Arguments RawDynamicTruthSigmaSuccessorRowAt
  M previousPi lowerLevel next : clear implicits.

Local Opaque dynamicTruthCoqLowerApplicationTermAt.

Theorem raw_sat_dynamicTruthSigmaSuccessorRowGraph_iff : forall
    (M : RawPAModel) tail previousPi lowerLevel next,
  raw_formula_sat M
    (scons M next (scons M previousPi (scons M lowerLevel tail)))
    dynamicTruthSigmaSuccessorRowGraph <->
  RawDynamicTruthSigmaSuccessorRowAt M previousPi lowerLevel next.
Proof.
  intros M tail previousPi lowerLevel next.
  unfold dynamicTruthSigmaSuccessorRowGraph,
    RawDynamicTruthSigmaSuccessorRowAt, fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthCoqLowerApplicationTermAt_iff.
  split.
  - intros (upperNumeral & domain & lowerApplication &
      hupper & hdomain & hlower & hnext).
    exists upperNumeral, domain, lowerApplication.
    assert (hupper' : RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) upperNumeral).
    {
      change (RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) upperNumeral) in hupper.
      exact hupper.
    }
    assert (hdomain' : RawCodedFormulaSingleSubstitution M
        upperNumeral
        (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
        domain).
    {
      change (RawCodedFormulaSingleSubstitution M upperNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M upperNumeral
                (scons M next
                  (scons M previousPi (scons M lowerLevel tail))))))
          (Term.numeral dynamicTruthSigmaRowDomainTemplateCode))
        domain) in hdomain.
      rewrite raw_term_eval_numeral in hdomain.
      exact hdomain.
    }
    assert (hlower' : RawDynamicTruthCoqLowerApplication M
        previousPi lowerApplication).
    {
      change (RawDynamicTruthCoqLowerApplication M
        previousPi lowerApplication) in hlower.
      exact hlower.
    }
    assert (hnext' : next = rawDynamicTruthSigmaSuccessorRowCode M
        domain lowerApplication).
    {
      change (next = raw_term_eval M
        (scons M lowerApplication
          (scons M domain
            (scons M upperNumeral
              (scons M next
                (scons M previousPi (scons M lowerLevel tail))))))
        (dynamicTruthSigmaSuccessorRowCodeTerm (tVar 1) (tVar 0)))
        in hnext.
      rewrite raw_eval_dynamicTruthSigmaSuccessorRowCodeTerm in hnext.
      cbn [raw_term_eval scons] in hnext.
      exact hnext.
    }
    repeat split; assumption.
  - intros (upperNumeral & domain & lowerApplication &
      hupper & hdomain & hlower & hnext).
    exists upperNumeral, domain, lowerApplication.
    repeat split.
    + change (RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) upperNumeral).
      exact hupper.
    + change (RawCodedFormulaSingleSubstitution M upperNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M upperNumeral
                (scons M next
                  (scons M previousPi (scons M lowerLevel tail))))))
          (Term.numeral dynamicTruthSigmaRowDomainTemplateCode))
        domain).
      rewrite raw_term_eval_numeral. exact hdomain.
    + change (RawDynamicTruthCoqLowerApplication M
        previousPi lowerApplication).
      exact hlower.
    + change (next = raw_term_eval M
        (scons M lowerApplication
          (scons M domain
            (scons M upperNumeral
              (scons M next
                (scons M previousPi (scons M lowerLevel tail))))))
        (dynamicTruthSigmaSuccessorRowCodeTerm (tVar 1) (tVar 0))).
      rewrite raw_eval_dynamicTruthSigmaSuccessorRowCodeTerm.
      cbn [raw_term_eval scons]. exact hnext.
Qed.

(** Standard-syntax adequacy of the whole structural graph.  The rank input
    remains a carrier element; the sole hypothesis [hupper] says that the
    represented numeral trace selected the displayed closed numeral term.
    For standard ranks this is supplied by the numeral-code realization
    theorem, while the carrier-facing theorem above does not assume it. *)
Theorem raw_dynamicTruthSigmaSuccessorRow_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lowerLevel upperNumeral lowerPi,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel)
    (rawQuotedTermCode M upperNumeral) ->
  DynamicTruthCoqLowerScoped lowerPi ->
  RawDynamicTruthSigmaSuccessorRowAt M
    (rawQuotedFormulaCode M lowerPi) lowerLevel
    (rawQuotedFormulaCode M
      (dynamicTruthSigmaSuccessorRowFormula upperNumeral lowerPi)).
Proof.
  intros M hPA lowerLevel upperNumeral lowerPi hupper hscope.
  exists (rawQuotedTermCode M upperNumeral),
    (rawQuotedFormulaCode M
      (dynamicTruthSigmaRowInstantiatedDomain upperNumeral)),
    (rawQuotedFormulaCode M
      (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)).
  split; [exact hupper |]. split.
  - exact (raw_dynamicTruthSigmaRowInstantiatedDomain_standard
      M hPA upperNumeral).
  - split.
    + exact (raw_dynamicTruthCoqLowerApplication_standard_rename
        M hPA lowerPi hscope).
    + symmetry.
      exact (rawDynamicTruthSigmaSuccessorRowCode_quoted
        M hPA upperNumeral lowerPi).
Qed.

(** The two totality inputs below state exactly the remaining operation
    obligations.  They are intentionally adequacy-sensitive rather than
    hidden behind a standard-only recursion or an arbitrary fallback code. *)
Definition RawDynamicTruthSigmaDomainStepTotal (M : RawPAModel) : Prop :=
  forall lowerLevel upperNumeral,
    RawNumeralTermCodeAt M (raw_succ M lowerLevel) upperNumeral ->
    exists domain,
      RawCodedFormulaSingleSubstitution M upperNumeral
        (rawNumeralValue M
          dynamicTruthSigmaRowDomainTemplateCode) domain.

Definition RawDynamicTruthCoqLowerApplicationTotal (M : RawPAModel) : Prop :=
  forall previousPi, exists lowerApplication,
    RawDynamicTruthCoqLowerApplication M previousPi lowerApplication.

Arguments RawDynamicTruthSigmaDomainStepTotal M : clear implicits.
Arguments RawDynamicTruthCoqLowerApplicationTotal M : clear implicits.

(** Exact successor totality from the two operation interfaces.  Numeral
    totality itself is already unconditional in PA and reaches nonstandard
    [lowerLevel]. *)
Theorem dynamicTruthSigmaSuccessorRowGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaDomainStepTotal M ->
  RawDynamicTruthCoqLowerApplicationTotal M ->
  RawCarrierIndexedCodeOrbitSuccessorTotal M
    dynamicTruthSigmaSuccessorRowGraph.
Proof.
  intros M hPA hdomain hlower tail lowerLevel previousPi.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M lowerLevel)) as [upperNumeral hupperNumeral].
  destruct (hdomain lowerLevel upperNumeral hupperNumeral)
    as [domain hdomainWitness].
  destruct (hlower previousPi) as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthSigmaSuccessorRowCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthSigmaSuccessorRowGraph_iff M tail
      previousPi lowerLevel _)).
  exists upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** Why this graph is not yet fed directly to [carrierIndexedCodeOrbitGraph]:
    the native fixed-level family is mutually recursive.  This graph maps a
    Pi-falsity code to a Sigma-row code, not a Sigma formula code to the next
    Sigma formula code.  A faithful family orbit must carry both polarities
    (or one explicitly combined mode-indexed predicate) and must preserve the
    atomic-adequacy invariant needed by three represented substitutions.
    The one-code orbit's unrestricted successor-totality interface records
    neither fact.  Accordingly this module stops at the checked Sigma
    component; it does not state a weakened paired interface with a vacuous
    dual conjunct. *)

End PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
