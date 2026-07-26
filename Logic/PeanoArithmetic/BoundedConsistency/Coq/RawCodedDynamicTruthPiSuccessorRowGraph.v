(**
  A concrete carrier-indexed code graph for the Pi-falsity successor row.

  The native Rocq partial-truth construction is polarity aware.  This is
  the genuine dual of the Sigma row: a Pi-falsity successor consumes the
  *Sigma-truth* predicate from the preceding level.  The dependency is
  retained explicitly throughout this module; it is never replaced by a
  dummy polarity, a tautological relation, or a fallback output.

  The public output-first graph is read under

      nextPi :: previousSigma :: lowerLevel :: tail.

  It constructs the code of the eight-witness Pi row used by Rocq's
  four-table truth certificate.  The row includes all six native cases:
  rank-zero falsity, implication, conjunction, disjunction, universal, and
  existential.  The final existential case applies [previousSigma] beneath
  a checked assignment prepend and asserts that no such lower-level truth
  witness exists.

  Every index and syntax code in the public relation is a carrier element.
  Exact graph semantics therefore applies equally at standard and
  nonstandard levels.  Totality is stated honestly in terms of the two
  remaining formula-operation interfaces rather than being hidden behind a
  standard-only quotation or an arbitrary default code.
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

Module PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.

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
    Application of the preceding Sigma predicate.

    Beneath the row's eight witnesses and the three binder-extension
    witnesses, the lower ternary predicate must read [#9], [#1], and [#0].
    Rocq's syntax-operation layer exposes one-variable substitution, so the
    application is represented by three checked substitutions.  The first
    two replacement indices compensate for the two later binder removals. *)

Definition dynamicTruthPiCoqLowerFirstReplacement : term := tVar 11.
Definition dynamicTruthPiCoqLowerSecondReplacement : term := tVar 2.
Definition dynamicTruthPiCoqLowerThirdReplacement : term := tVar 0.

Definition dynamicTruthPiCoqLowerFirstReplacementCode : term :=
  Term.numeral (termCode dynamicTruthPiCoqLowerFirstReplacement).

Definition dynamicTruthPiCoqLowerSecondReplacementCode : term :=
  Term.numeral (termCode dynamicTruthPiCoqLowerSecondReplacement).

Definition dynamicTruthPiCoqLowerThirdReplacementCode : term :=
  Term.numeral (termCode dynamicTruthPiCoqLowerThirdReplacement).

Definition dynamicTruthPiCoqLowerApplicationTermAt
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        dynamicTruthPiCoqLowerFirstReplacementCode
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthPiCoqLowerSecondReplacementCode
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthPiCoqLowerThirdReplacementCode
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthPiCoqLowerApplication (M : RawPAModel)
    (previousSigma output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthPiCoqLowerFirstReplacement))
      previousSigma first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthPiCoqLowerSecondReplacement))
      first second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthPiCoqLowerThirdReplacement))
      second output.

Arguments RawDynamicTruthPiCoqLowerApplication M previousSigma output
  : clear implicits.

Theorem raw_sat_dynamicTruthPiCoqLowerApplicationTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (dynamicTruthPiCoqLowerApplicationTermAt input output) <->
  RawDynamicTruthPiCoqLowerApplication M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold dynamicTruthPiCoqLowerApplicationTermAt,
    RawDynamicTruthPiCoqLowerApplication,
    dynamicTruthPiCoqLowerFirstReplacementCode,
    dynamicTruthPiCoqLowerSecondReplacementCode,
    dynamicTruthPiCoqLowerThirdReplacementCode.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition standardDynamicTruthPiCoqLowerApplication (input : formula) :
    formula :=
  Formula.subst
    (Formula.instTerm dynamicTruthPiCoqLowerThirdReplacement)
    (Formula.subst
      (Formula.instTerm dynamicTruthPiCoqLowerSecondReplacement)
      (Formula.subst
        (Formula.instTerm dynamicTruthPiCoqLowerFirstReplacement)
        input)).

Definition dynamicTruthPiCoqLowerApplicationRenaming (index : nat) : nat :=
  match index with
  | 0 => 9
  | 1 => 1
  | 2 => 0
  | S (S (S tailIndex)) => tailIndex
  end.

Definition DynamicTruthPiCoqLowerScoped (input : formula) : Prop :=
  forall index, Formula.Free index input -> index < 3.

Arguments DynamicTruthPiCoqLowerScoped input : clear implicits.

(** A literal syntactic audit of the sequential de Bruijn substitutions. *)
Theorem standardDynamicTruthPiCoqLowerApplication_eq_rename : forall input,
  DynamicTruthPiCoqLowerScoped input ->
  standardDynamicTruthPiCoqLowerApplication input =
    Formula.rename dynamicTruthPiCoqLowerApplicationRenaming input.
Proof.
  intros input hscope.
  unfold standardDynamicTruthPiCoqLowerApplication.
  rewrite !Formula.subst_comp.
  rewrite <- Formula.subst_var_rename.
  apply Formula.subst_ext_free.
  intros index hfree.
  specialize (hscope index hfree).
  destruct index as [|[|[|tailIndex]]];
    cbn [Formula.instTerm dynamicTruthPiCoqLowerFirstReplacement
      dynamicTruthPiCoqLowerSecondReplacement
      dynamicTruthPiCoqLowerThirdReplacement
      dynamicTruthPiCoqLowerApplicationRenaming Term.subst];
    try reflexivity; lia.
Qed.

Theorem raw_dynamicTruthPiCoqLowerApplication_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawDynamicTruthPiCoqLowerApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (standardDynamicTruthPiCoqLowerApplication input)).
Proof.
  intros M hPA input.
  unfold standardDynamicTruthPiCoqLowerApplication.
  set (first := Formula.subst
    (Formula.instTerm dynamicTruthPiCoqLowerFirstReplacement) input).
  set (second := Formula.subst
    (Formula.instTerm dynamicTruthPiCoqLowerSecondReplacement) first).
  exists (rawQuotedFormulaCode M first),
    (rawQuotedFormulaCode M second).
  split.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthPiCoqLowerFirstReplacement).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      dynamicTruthPiCoqLowerFirstReplacement input).
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthPiCoqLowerSecondReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthPiCoqLowerSecondReplacement first).
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthPiCoqLowerThirdReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthPiCoqLowerThirdReplacement second).
Qed.

Corollary raw_dynamicTruthPiCoqLowerApplication_standard_rename : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  DynamicTruthPiCoqLowerScoped input ->
  RawDynamicTruthPiCoqLowerApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming input)).
Proof.
  intros M hPA input hscope.
  rewrite <- (standardDynamicTruthPiCoqLowerApplication_eq_rename
    input hscope).
  exact (raw_dynamicTruthPiCoqLowerApplication_standard M hPA input).
Qed.

(** ------------------------------------------------------------------
    The six fixed alternatives in the native eight-witness row layout. *)

Definition dynamicTruthPiRowQfFormula : formula :=
  rankZeroTruthCertificateTermAt
    (tVar 10) tZero (tVar 9) (tVar 8).

Definition dynamicTruthPiRowImpFormula : formula :=
  fixedLevelAnd4
    (formulaImpCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) tZero (tVar 6)
      (tVar 9) (tVar 8))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 5) (Term.numeral 1) (tVar 4)
      (tVar 9) (tVar 8))
    (pEq (tVar 0) (tVar 0)).

Definition dynamicTruthPiRowAndFormula : formula :=
  pAnd
    (formulaAndCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (pOr
      (dynamicTruthStateMemberTermAt
        (tVar 20) (tVar 19) (tVar 18) (tVar 17)
        (tVar 16) (tVar 15) (tVar 14) (tVar 13)
        (tVar 12) (tVar 7) (Term.numeral 1) (tVar 6)
        (tVar 9) (tVar 8))
      (dynamicTruthStateMemberTermAt
        (tVar 20) (tVar 19) (tVar 18) (tVar 17)
        (tVar 16) (tVar 15) (tVar 14) (tVar 13)
        (tVar 12) (tVar 5) (Term.numeral 1) (tVar 4)
        (tVar 9) (tVar 8))).

Definition dynamicTruthPiRowOrFormula : formula :=
  fixedLevelAnd3
    (formulaOrCodeTermAt (tVar 10) (tVar 6) (tVar 4))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) (Term.numeral 1) (tVar 6)
      (tVar 9) (tVar 8))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 5) (Term.numeral 1) (tVar 4)
      (tVar 9) (tVar 8)).

Definition dynamicTruthPiRowAllFormula : formula :=
  fixedLevelAnd3
    (formulaAllCodeTermAt (tVar 10) (tVar 6))
    (codedAssignmentPrependTermAt
      (tVar 9) (tVar 8) (tVar 3) (tVar 10) (tVar 2) (tVar 1))
    (dynamicTruthStateMemberTermAt
      (tVar 20) (tVar 19) (tVar 18) (tVar 17)
      (tVar 16) (tVar 15) (tVar 14) (tVar 13)
      (tVar 12) (tVar 7) (Term.numeral 1) (tVar 6)
      (tVar 2) (tVar 1)).

Definition dynamicTruthPiRowExistentialPrefixFormula : formula :=
  formulaExCodeTermAt (tVar 10) (tVar 6).

Definition dynamicTruthPiRowBinderPrependFormula : formula :=
  codedAssignmentPrependTermAt
    (liftTerm 3 (tVar 9)) (liftTerm 3 (tVar 8))
    (tVar 2) (liftTerm 3 (tVar 10)) (tVar 1) (tVar 0).

(** Variable zero is the closed numeral-term placeholder.  The formula code
    starts at [#11] and becomes [#10] after that placeholder is removed. *)
Definition dynamicTruthPiRowDomainTemplate : formula :=
  dynamicTruthPiRecordDomainTermAt (tVar 0) (tVar 11).

Definition dynamicTruthPiRowInstantiatedDomain
    (successorNumeral : term) : formula :=
  Formula.subst (Formula.instTerm successorNumeral)
    dynamicTruthPiRowDomainTemplate.

Definition dynamicTruthPiSuccessorRowFormula
    (successorNumeral : term) (lowerSigma : formula) : formula :=
  fixedLevelEx8
    (pAnd
      (dynamicTruthPiRowInstantiatedDomain successorNumeral)
      (fixedLevelOr6
        dynamicTruthPiRowQfFormula
        dynamicTruthPiRowImpFormula
        dynamicTruthPiRowAndFormula
        dynamicTruthPiRowOrFormula
        dynamicTruthPiRowAllFormula
        (pAnd dynamicTruthPiRowExistentialPrefixFormula
          (fixedLevelNoBinderCounterexampleTermAt
            (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
              lowerSigma)
            (tVar 9) (tVar 8) (tVar 10))))).

(** ------------------------------------------------------------------
    Transparent formula-code polynomial for the displayed row. *)

Definition dynamicTruthPiFormulaImpCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 2) left right.

Definition dynamicTruthPiFormulaAndCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 3) left right.

Definition dynamicTruthPiFormulaOrCodeTerm
    (left right : term) : term :=
  codeList3Term (Term.numeral 4) left right.

Definition dynamicTruthPiFormulaAllCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 5) child.

Definition dynamicTruthPiFormulaExCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 6) child.

Definition dynamicTruthPiFormulaEx3CodeTerm (child : term) : term :=
  dynamicTruthPiFormulaExCodeTerm
    (dynamicTruthPiFormulaExCodeTerm
      (dynamicTruthPiFormulaExCodeTerm child)).

Definition dynamicTruthPiFormulaEx8CodeTerm (child : term) : term :=
  dynamicTruthPiFormulaExCodeTerm
    (dynamicTruthPiFormulaExCodeTerm
      (dynamicTruthPiFormulaExCodeTerm
        (dynamicTruthPiFormulaExCodeTerm
          (dynamicTruthPiFormulaExCodeTerm
            (dynamicTruthPiFormulaExCodeTerm
              (dynamicTruthPiFormulaExCodeTerm
                (dynamicTruthPiFormulaExCodeTerm child))))))).

Definition dynamicTruthPiFixedFormulaNumeralCodeTerm
    (phi : formula) : term :=
  Term.numeral (formulaCode phi).

Definition dynamicTruthPiNoBinderCodeTerm
    (lowerApplication : term) : term :=
  dynamicTruthPiFormulaImpCodeTerm
    (dynamicTruthPiFormulaEx3CodeTerm
      (dynamicTruthPiFormulaAndCodeTerm
        (dynamicTruthPiFixedFormulaNumeralCodeTerm
          dynamicTruthPiRowBinderPrependFormula)
        lowerApplication))
    rawFormulaBotCodeTerm.

Definition dynamicTruthPiExistentialCodeTerm
    (lowerApplication : term) : term :=
  dynamicTruthPiFormulaAndCodeTerm
    (dynamicTruthPiFixedFormulaNumeralCodeTerm
      dynamicTruthPiRowExistentialPrefixFormula)
    (dynamicTruthPiNoBinderCodeTerm lowerApplication).

Definition dynamicTruthPiBranchesCodeTerm
    (lowerApplication : term) : term :=
  dynamicTruthPiFormulaOrCodeTerm
    (dynamicTruthPiFixedFormulaNumeralCodeTerm dynamicTruthPiRowQfFormula)
    (dynamicTruthPiFormulaOrCodeTerm
      (dynamicTruthPiFixedFormulaNumeralCodeTerm dynamicTruthPiRowImpFormula)
      (dynamicTruthPiFormulaOrCodeTerm
        (dynamicTruthPiFixedFormulaNumeralCodeTerm
          dynamicTruthPiRowAndFormula)
        (dynamicTruthPiFormulaOrCodeTerm
          (dynamicTruthPiFixedFormulaNumeralCodeTerm
            dynamicTruthPiRowOrFormula)
          (dynamicTruthPiFormulaOrCodeTerm
            (dynamicTruthPiFixedFormulaNumeralCodeTerm
              dynamicTruthPiRowAllFormula)
            (dynamicTruthPiExistentialCodeTerm lowerApplication))))).

Definition dynamicTruthPiSuccessorRowCodeTerm
    (domain lowerApplication : term) : term :=
  dynamicTruthPiFormulaEx8CodeTerm
    (dynamicTruthPiFormulaAndCodeTerm domain
      (dynamicTruthPiBranchesCodeTerm lowerApplication)).

(** Carrier counterparts of the fixed polynomial syntax. *)
Definition rawDynamicTruthPiFixedFormulaNumeralCode (M : RawPAModel)
    (phi : formula) : M :=
  rawNumeralValue M (formulaCode phi).

Definition rawDynamicTruthPiFormulaEx3Code
    (M : RawPAModel) (child : M) : M :=
  rawFormulaExCode M
    (rawFormulaExCode M (rawFormulaExCode M child)).

Definition rawDynamicTruthPiFormulaEx8Code
    (M : RawPAModel) (child : M) : M :=
  rawFormulaExCode M
    (rawFormulaExCode M
      (rawFormulaExCode M
        (rawFormulaExCode M
          (rawFormulaExCode M
            (rawFormulaExCode M
              (rawFormulaExCode M (rawFormulaExCode M child))))))).

Definition rawDynamicTruthPiNoBinderCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx3Code M
      (rawFormulaAndCode M
        (rawDynamicTruthPiFixedFormulaNumeralCode M
          dynamicTruthPiRowBinderPrependFormula)
        lowerApplication))
    (rawFormulaBotCode M).

Definition rawDynamicTruthPiExistentialCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaAndCode M
    (rawDynamicTruthPiFixedFormulaNumeralCode M
      dynamicTruthPiRowExistentialPrefixFormula)
    (rawDynamicTruthPiNoBinderCode M lowerApplication).

Definition rawDynamicTruthPiBranchesCode (M : RawPAModel)
    (lowerApplication : M) : M :=
  rawFormulaOrCode M
    (rawDynamicTruthPiFixedFormulaNumeralCode M dynamicTruthPiRowQfFormula)
    (rawFormulaOrCode M
      (rawDynamicTruthPiFixedFormulaNumeralCode M dynamicTruthPiRowImpFormula)
      (rawFormulaOrCode M
        (rawDynamicTruthPiFixedFormulaNumeralCode M
          dynamicTruthPiRowAndFormula)
        (rawFormulaOrCode M
          (rawDynamicTruthPiFixedFormulaNumeralCode M
            dynamicTruthPiRowOrFormula)
          (rawFormulaOrCode M
            (rawDynamicTruthPiFixedFormulaNumeralCode M
              dynamicTruthPiRowAllFormula)
            (rawDynamicTruthPiExistentialCode M lowerApplication))))).

Definition rawDynamicTruthPiSuccessorRowCode (M : RawPAModel)
    (domain lowerApplication : M) : M :=
  rawDynamicTruthPiFormulaEx8Code M
    (rawFormulaAndCode M domain
      (rawDynamicTruthPiBranchesCode M lowerApplication)).

(** Direct evaluation lemmas show that the represented graph computes this
    polynomial on arbitrary carrier-valued inputs. *)
Lemma raw_eval_dynamicTruthPiFormulaImpCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthPiFormulaImpCodeTerm left right) =
  rawFormulaImpCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthPiFormulaImpCodeTerm, rawFormulaImpCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaAndCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthPiFormulaAndCodeTerm left right) =
  rawFormulaAndCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthPiFormulaAndCodeTerm, rawFormulaAndCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaOrCodeTerm : forall
    (M : RawPAModel) e left right,
  raw_term_eval M e (dynamicTruthPiFormulaOrCodeTerm left right) =
  rawFormulaOrCode M
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold dynamicTruthPiFormulaOrCodeTerm, rawFormulaOrCode.
  rewrite raw_eval_codeList3Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaAllCodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthPiFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthPiFormulaAllCodeTerm, rawFormulaAllCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaExCodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthPiFormulaExCodeTerm child) =
  rawFormulaExCode M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthPiFormulaExCodeTerm, rawFormulaExCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaEx3CodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthPiFormulaEx3CodeTerm child) =
  rawDynamicTruthPiFormulaEx3Code M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthPiFormulaEx3CodeTerm,
    rawDynamicTruthPiFormulaEx3Code.
  rewrite !raw_eval_dynamicTruthPiFormulaExCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFormulaEx8CodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthPiFormulaEx8CodeTerm child) =
  rawDynamicTruthPiFormulaEx8Code M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthPiFormulaEx8CodeTerm,
    rawDynamicTruthPiFormulaEx8Code.
  rewrite !raw_eval_dynamicTruthPiFormulaExCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiFixedFormulaNumeralCodeTerm : forall
    (M : RawPAModel) e phi,
  raw_term_eval M e (dynamicTruthPiFixedFormulaNumeralCodeTerm phi) =
  rawDynamicTruthPiFixedFormulaNumeralCode M phi.
Proof.
  intros. unfold dynamicTruthPiFixedFormulaNumeralCodeTerm,
    rawDynamicTruthPiFixedFormulaNumeralCode.
  apply raw_term_eval_numeral.
Qed.

Lemma raw_eval_dynamicTruthPiNoBinderCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiNoBinderCodeTerm lowerApplication) =
  rawDynamicTruthPiNoBinderCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthPiNoBinderCodeTerm,
    rawDynamicTruthPiNoBinderCode.
  rewrite raw_eval_dynamicTruthPiFormulaImpCodeTerm,
    raw_eval_dynamicTruthPiFormulaEx3CodeTerm,
    raw_eval_dynamicTruthPiFormulaAndCodeTerm,
    raw_eval_dynamicTruthPiFixedFormulaNumeralCodeTerm,
    raw_eval_rawFormulaBotCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiExistentialCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiExistentialCodeTerm lowerApplication) =
  rawDynamicTruthPiExistentialCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthPiExistentialCodeTerm,
    rawDynamicTruthPiExistentialCode.
  rewrite raw_eval_dynamicTruthPiFormulaAndCodeTerm,
    raw_eval_dynamicTruthPiFixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthPiNoBinderCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiBranchesCodeTerm : forall
    (M : RawPAModel) e lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiBranchesCodeTerm lowerApplication) =
  rawDynamicTruthPiBranchesCode M
    (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthPiBranchesCodeTerm,
    rawDynamicTruthPiBranchesCode.
  rewrite !raw_eval_dynamicTruthPiFormulaOrCodeTerm,
    !raw_eval_dynamicTruthPiFixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthPiExistentialCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthPiSuccessorRowCodeTerm : forall
    (M : RawPAModel) e domain lowerApplication,
  raw_term_eval M e
    (dynamicTruthPiSuccessorRowCodeTerm domain lowerApplication) =
  rawDynamicTruthPiSuccessorRowCode M
    (raw_term_eval M e domain) (raw_term_eval M e lowerApplication).
Proof.
  intros. unfold dynamicTruthPiSuccessorRowCodeTerm,
    rawDynamicTruthPiSuccessorRowCode.
  rewrite raw_eval_dynamicTruthPiFormulaEx8CodeTerm,
    raw_eval_dynamicTruthPiFormulaAndCodeTerm,
    raw_eval_dynamicTruthPiBranchesCodeTerm.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Literal quotation audit on standard syntax inputs. *)

Lemma rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  rawDynamicTruthPiFixedFormulaNumeralCode M phi =
  rawQuotedFormulaCode M phi.
Proof.
  intros M hPA phi.
  unfold rawDynamicTruthPiFixedFormulaNumeralCode.
  symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthPiNoBinderCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerSigma,
  rawDynamicTruthPiNoBinderCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
          lowerSigma)) =
  rawQuotedFormulaCode M
    (fixedLevelNoBinderCounterexampleTermAt
      (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming lowerSigma)
      (tVar 9) (tVar 8) (tVar 10)).
Proof.
  intros M hPA lowerSigma.
  unfold rawDynamicTruthPiNoBinderCode,
    rawDynamicTruthPiFormulaEx3Code,
    fixedLevelNoBinderCounterexampleTermAt,
    fixedLevelEx3, dynamicTruthPiRowBinderPrependFormula.
  cbn [rawQuotedFormulaCode].
  rewrite rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthPiExistentialCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerSigma,
  rawDynamicTruthPiExistentialCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
          lowerSigma)) =
  rawQuotedFormulaCode M
    (pAnd dynamicTruthPiRowExistentialPrefixFormula
      (fixedLevelNoBinderCounterexampleTermAt
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming lowerSigma)
        (tVar 9) (tVar 8) (tVar 10))).
Proof.
  intros M hPA lowerSigma.
  unfold rawDynamicTruthPiExistentialCode.
  cbn [rawQuotedFormulaCode].
  rewrite rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiNoBinderCode_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthPiBranchesCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerSigma,
  rawDynamicTruthPiBranchesCode M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
          lowerSigma)) =
  rawQuotedFormulaCode M
    (fixedLevelOr6
      dynamicTruthPiRowQfFormula
      dynamicTruthPiRowImpFormula
      dynamicTruthPiRowAndFormula
      dynamicTruthPiRowOrFormula
      dynamicTruthPiRowAllFormula
      (pAnd dynamicTruthPiRowExistentialPrefixFormula
        (fixedLevelNoBinderCounterexampleTermAt
          (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
            lowerSigma)
          (tVar 9) (tVar 8) (tVar 10)))).
Proof.
  intros M hPA lowerSigma.
  unfold rawDynamicTruthPiBranchesCode, fixedLevelOr6.
  cbn [rawQuotedFormulaCode].
  repeat rewrite rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiExistentialCode_quoted by exact hPA.
  reflexivity.
Qed.

(** The carrier polynomial is exactly the native Pi row quotation whenever
    its two operation inputs are quotations of the displayed syntax. *)
Theorem rawDynamicTruthPiSuccessorRowCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      successorNumeral lowerSigma,
  rawDynamicTruthPiSuccessorRowCode M
      (rawQuotedFormulaCode M
        (dynamicTruthPiRowInstantiatedDomain successorNumeral))
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
          lowerSigma)) =
  rawQuotedFormulaCode M
    (dynamicTruthPiSuccessorRowFormula successorNumeral lowerSigma).
Proof.
  intros M hPA successorNumeral lowerSigma.
  unfold rawDynamicTruthPiSuccessorRowCode,
    rawDynamicTruthPiFormulaEx8Code,
    dynamicTruthPiSuccessorRowFormula, fixedLevelEx8.
  cbn [rawQuotedFormulaCode].
  rewrite rawDynamicTruthPiBranchesCode_quoted by exact hPA.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Represented successor graph and exact arbitrary-model semantics.

    Three witnesses are [successorNumeralCode], [domainCode], and
    [lowerApplicationCode], from outermost to innermost.  At the body the
    environment is

      lowerApplication :: domain :: successorNumeral ::
        nextPi :: previousSigma :: lowerLevel :: tail.
*)
Definition dynamicTruthPiSuccessorRowGraph : formula :=
  pEx (pEx (pEx
    (fixedLevelAnd4
      (numeralTermCodeAtTermAt (tSucc (tVar 5)) (tVar 2))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 2)
        (Term.numeral (formulaCode dynamicTruthPiRowDomainTemplate))
        (tVar 1))
      (dynamicTruthPiCoqLowerApplicationTermAt (tVar 4) (tVar 0))
      (pEq (tVar 3)
        (dynamicTruthPiSuccessorRowCodeTerm
          (tVar 1) (tVar 0)))))).

Definition RawDynamicTruthPiSuccessorRowAt (M : RawPAModel)
    (previousSigma lowerLevel nextPi : M) : Prop :=
  exists successorNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M
      (raw_succ M lowerLevel) successorNumeral /\
    RawCodedFormulaSingleSubstitution M successorNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) domain /\
    RawDynamicTruthPiCoqLowerApplication M
      previousSigma lowerApplication /\
    nextPi = rawDynamicTruthPiSuccessorRowCode M
      domain lowerApplication.

Arguments RawDynamicTruthPiSuccessorRowAt
  M previousSigma lowerLevel nextPi : clear implicits.

(** Keep the two large, already-audited subformulae atomic while reducing the
    outer existential/conjunction shell.  Their exact evaluation lemmas are
    used immediately below.  Without this local opacity [cbn] needlessly
    expands the entire eight-witness syntax polynomial. *)
Local Opaque dynamicTruthPiCoqLowerApplicationTermAt.
Local Opaque dynamicTruthPiSuccessorRowCodeTerm.

(** This equivalence is law-free.  In particular, [previousSigma] appears
    as the input of three checked substitution traces in the exact relation;
    the dual dependency is not merely a comment on the intended syntax. *)
Theorem raw_sat_dynamicTruthPiSuccessorRowGraph_iff : forall
    (M : RawPAModel) tail previousSigma lowerLevel nextPi,
  raw_formula_sat M
    (scons M nextPi
      (scons M previousSigma (scons M lowerLevel tail)))
    dynamicTruthPiSuccessorRowGraph <->
  RawDynamicTruthPiSuccessorRowAt M
    previousSigma lowerLevel nextPi.
Proof.
  intros M tail previousSigma lowerLevel nextPi.
  unfold dynamicTruthPiSuccessorRowGraph,
    RawDynamicTruthPiSuccessorRowAt, fixedLevelAnd4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_dynamicTruthPiCoqLowerApplicationTermAt_iff.
  split.
  - intros (successorNumeral & domain & lowerApplication &
      hsuccessorNumeral & hdomain & hlower & hnext).
    exists successorNumeral, domain, lowerApplication.
    assert (hsuccessorNumeral' : RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) successorNumeral).
    {
      change (RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) successorNumeral)
        in hsuccessorNumeral.
      exact hsuccessorNumeral.
    }
    assert (hdomain' : RawCodedFormulaSingleSubstitution M
        successorNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthPiRowDomainTemplate)) domain).
    {
      change (RawCodedFormulaSingleSubstitution M successorNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M successorNumeral
                (scons M nextPi
                  (scons M previousSigma (scons M lowerLevel tail))))))
          (Term.numeral
            (formulaCode dynamicTruthPiRowDomainTemplate)))
        domain) in hdomain.
      rewrite raw_term_eval_numeral in hdomain.
      exact hdomain.
    }
    assert (hlower' : RawDynamicTruthPiCoqLowerApplication M
        previousSigma lowerApplication).
    {
      change (RawDynamicTruthPiCoqLowerApplication M
        previousSigma lowerApplication) in hlower.
      exact hlower.
    }
    assert (hnext' : nextPi = rawDynamicTruthPiSuccessorRowCode M
        domain lowerApplication).
    {
      change (nextPi = raw_term_eval M
        (scons M lowerApplication
          (scons M domain
            (scons M successorNumeral
              (scons M nextPi
                (scons M previousSigma (scons M lowerLevel tail))))))
        (dynamicTruthPiSuccessorRowCodeTerm (tVar 1) (tVar 0)))
        in hnext.
      rewrite raw_eval_dynamicTruthPiSuccessorRowCodeTerm in hnext.
      cbn [raw_term_eval scons] in hnext.
      exact hnext.
    }
    repeat split; assumption.
  - intros (successorNumeral & domain & lowerApplication &
      hsuccessorNumeral & hdomain & hlower & hnext).
    exists successorNumeral, domain, lowerApplication.
    repeat split.
    + change (RawNumeralTermCodeAt M
        (raw_succ M lowerLevel) successorNumeral).
      exact hsuccessorNumeral.
    + change (RawCodedFormulaSingleSubstitution M successorNumeral
        (raw_term_eval M
          (scons M lowerApplication
            (scons M domain
              (scons M successorNumeral
                (scons M nextPi
                  (scons M previousSigma (scons M lowerLevel tail))))))
          (Term.numeral
            (formulaCode dynamicTruthPiRowDomainTemplate)))
        domain).
      rewrite raw_term_eval_numeral. exact hdomain.
    + change (RawDynamicTruthPiCoqLowerApplication M
        previousSigma lowerApplication).
      exact hlower.
    + change (nextPi = raw_term_eval M
        (scons M lowerApplication
          (scons M domain
            (scons M successorNumeral
              (scons M nextPi
                (scons M previousSigma (scons M lowerLevel tail))))))
        (dynamicTruthPiSuccessorRowCodeTerm (tVar 1) (tVar 0))).
      rewrite raw_eval_dynamicTruthPiSuccessorRowCodeTerm.
      cbn [raw_term_eval scons]. exact hnext.
Qed.

(** The remaining operation obligations are exposed as conditional
    interfaces.  Neither premise can be replaced by a default output
    without losing the formula's intended dependency. *)
Definition RawDynamicTruthPiDomainStepTotal (M : RawPAModel) : Prop :=
  forall lowerLevel successorNumeral,
    RawNumeralTermCodeAt M
      (raw_succ M lowerLevel) successorNumeral ->
    exists domain,
      RawCodedFormulaSingleSubstitution M successorNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthPiRowDomainTemplate)) domain.

Definition RawDynamicTruthPiCoqLowerApplicationTotal
    (M : RawPAModel) : Prop :=
  forall previousSigma, exists lowerApplication,
    RawDynamicTruthPiCoqLowerApplication M
      previousSigma lowerApplication.

Arguments RawDynamicTruthPiDomainStepTotal M : clear implicits.
Arguments RawDynamicTruthPiCoqLowerApplicationTotal M : clear implicits.

(** Numeral-code totality is already unconditional in PA and applies to
    nonstandard [lowerLevel].  The two explicit interfaces supply the
    domain substitution and the lower-Sigma application. *)
Theorem dynamicTruthPiSuccessorRowGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiDomainStepTotal M ->
  RawDynamicTruthPiCoqLowerApplicationTotal M ->
  RawCarrierIndexedCodeOrbitSuccessorTotal M
    dynamicTruthPiSuccessorRowGraph.
Proof.
  intros M hPA hdomain hlower tail lowerLevel previousSigma.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M lowerLevel))
    as [successorNumeral hsuccessorNumeral].
  destruct (hdomain lowerLevel successorNumeral hsuccessorNumeral)
    as [domain hdomainWitness].
  destruct (hlower previousSigma)
    as [lowerApplication hlowerApplication].
  exists (rawDynamicTruthPiSuccessorRowCode M
    domain lowerApplication).
  apply (proj2
    (raw_sat_dynamicTruthPiSuccessorRowGraph_iff M tail
      previousSigma lowerLevel _)).
  exists successorNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** The mutually recursive family will combine this transformer with the
    Sigma transformer in a paired carrier-indexed orbit.  This theorem's
    type deliberately remains one directional:

      previous Sigma-truth code  --->  next Pi-falsity code.
*)

End PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
