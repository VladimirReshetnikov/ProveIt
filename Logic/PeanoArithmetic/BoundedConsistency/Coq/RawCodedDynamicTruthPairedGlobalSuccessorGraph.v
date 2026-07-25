(**
  Globalize the paired dynamic-truth successor rows.

  The previously constructed paired successor returns codes of the *local*
  eight-witness Sigma/Pi row checkers.  Such a row checker is not itself a
  truth predicate: positive rows only consult four beta tables, without
  asserting that those tables are defined or that all referenced rows are
  closed.  This file puts both local rows under one genuine four-table
  traversal and selects root mode zero for Sigma truth and root mode one for
  Pi falsity.

  The public successor convention is

      nextSigmaGlobal :: nextPiGlobal ::
      previousSigmaGlobal :: previousPiGlobal :: lowerLevel :: tail.

  All formula-code construction is a transparent polynomial in the two
  local row codes.  In particular, no carrier element is decoded as a Rocq
  [formula], which is essential at nonstandard levels.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators RawCodedBasicFormulaScopes
  RawCodedCarrierIndexedPairedCodeOrbitGraph
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthPairedBaseFormulaCodeGraph
  RawCodedDynamicTruthPairedBaseAdequacy
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy.

Module PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.
Import PABoundedRawCodedDynamicTruthPairedBaseAdequacy.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

(** ------------------------------------------------------------------
    Literal local-row placement.

    We deliberately reorder the ten existential table witnesses.  At the
    traversal body their environment is

      assignmentStepStep #0, assignmentStepCode #1,
      assignmentCodeStep #2, assignmentCodeCode #3,
      formulaStep #4, formulaCode #5, modeStep #6, modeCode #7,
      rootIndex #8, bound #9,
      root #10, assignmentCode #11, assignmentStep #12.

    Beneath the five row binders this becomes exactly the 13-slot layout of
    both existing local successor rows.  The otherwise unused local slot #3
    is occupied by [mode].  Therefore the local formula code is inserted
    literally: it is neither shifted nor substituted. *)

Definition dynamicTruthGlobalWitnessEnvironment (M : RawPAModel)
    (assignmentStepStep assignmentStepCode
      assignmentCodeStep assignmentCodeCode
      formulaStep formulaCode modeStep modeCode rootIndex bound
      root assignmentCode assignmentStep : M)
    (tail : nat -> M) : nat -> M :=
  scons M assignmentStepStep (scons M assignmentStepCode
    (scons M assignmentCodeStep (scons M assignmentCodeCode
      (scons M formulaStep (scons M formulaCode
        (scons M modeStep (scons M modeCode
          (scons M rootIndex (scons M bound
            (scons M root (scons M assignmentCode
              (scons M assignmentStep tail)))))))))))).

Definition dynamicTruthGlobalRowEnvironment (M : RawPAModel)
    (index mode code assignmentCode assignmentStep
      assignmentStepStep assignmentStepCode
      assignmentCodeStep assignmentCodeCode
      formulaStep formulaCode modeStep modeCode rootIndex bound
      root rootAssignmentCode rootAssignmentStep : M)
    (tail : nat -> M) : nat -> M :=
  scons M assignmentStep (scons M assignmentCode
    (scons M code (scons M mode (scons M index
      (dynamicTruthGlobalWitnessEnvironment M
        assignmentStepStep assignmentStepCode
        assignmentCodeStep assignmentCodeCode
        formulaStep formulaCode modeStep modeCode rootIndex bound
        root rootAssignmentCode rootAssignmentStep tail))))).

(** The first thirteen values are the complete public interface of a local
    row formula.  Keeping this theorem explicit makes the no-shift argument
    independently auditable. *)
Theorem dynamicTruthGlobalRowEnvironment_first_thirteen : forall
    (M : RawPAModel)
    index mode code assignmentCode assignmentStep
    assignmentStepStep assignmentStepCode
    assignmentCodeStep assignmentCodeCode
    formulaStep formulaCode modeStep modeCode rootIndex bound
    root rootAssignmentCode rootAssignmentStep tail,
  let e := dynamicTruthGlobalRowEnvironment M
    index mode code assignmentCode assignmentStep
    assignmentStepStep assignmentStepCode
    assignmentCodeStep assignmentCodeCode
    formulaStep formulaCode modeStep modeCode rootIndex bound
    root rootAssignmentCode rootAssignmentStep tail in
  e 0 = assignmentStep /\ e 1 = assignmentCode /\
  e 2 = code /\ e 3 = mode /\ e 4 = index /\
  e 5 = assignmentStepStep /\ e 6 = assignmentStepCode /\
  e 7 = assignmentCodeStep /\ e 8 = assignmentCodeCode /\
  e 9 = formulaStep /\ e 10 = formulaCode /\
  e 11 = modeStep /\ e 12 = modeCode.
Proof.
  intros. cbn [dynamicTruthGlobalRowEnvironment
    dynamicTruthGlobalWitnessEnvironment scons].
  repeat split; reflexivity.
Qed.

Definition DynamicTruthGlobalLocalRowScoped (localRow : formula) : Prop :=
  StandardFormulaScoped 13 localRow.

Arguments DynamicTruthGlobalLocalRowScoped localRow : clear implicits.

(** ------------------------------------------------------------------
    Formula-level reference wrapper.

    The closed-row alternative is literally the same polarity split as
    [fixedLevelClosedSuccessorRowTermAt]:

      (mode = 0 /\ localSigma) \/ (mode = 1 /\ localPi).

    This rules out arbitrary mode values; two implications would be too
    weak because both could hold vacuously. *)

Definition dynamicTruthGlobalSigmaModeFormula : formula :=
  pEq (tVar 3) tZero.

Definition dynamicTruthGlobalPiModeFormula : formula :=
  pEq (tVar 3) (Term.numeral 1).

Definition dynamicTruthGlobalRowBoundFormula : formula :=
  Formula.ltTermAt (tVar 4) (tVar 14).

Definition dynamicTruthGlobalRowLookupFormula : formula :=
  fixedLevelStateLookupTermAt
    (tVar 12) (tVar 11) (tVar 10) (tVar 9)
    (tVar 8) (tVar 7) (tVar 6) (tVar 5)
    (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0).

Definition dynamicTruthGlobalRowsFormula
    (localSigma localPi : formula) : formula :=
  fixedTruthTraversalAll5
    (pImp dynamicTruthGlobalRowBoundFormula
      (pImp dynamicTruthGlobalRowLookupFormula
        (pOr
          (pAnd dynamicTruthGlobalSigmaModeFormula localSigma)
          (pAnd dynamicTruthGlobalPiModeFormula localPi)))).

Definition dynamicTruthGlobalModeDefinedFormula : formula :=
  codedAssignmentDefinedThroughTermAt (tVar 7) (tVar 6) (tVar 9).

Definition dynamicTruthGlobalFormulaDefinedFormula : formula :=
  codedAssignmentDefinedThroughTermAt (tVar 5) (tVar 4) (tVar 9).

Definition dynamicTruthGlobalAssignmentCodeDefinedFormula : formula :=
  codedAssignmentDefinedThroughTermAt (tVar 3) (tVar 2) (tVar 9).

Definition dynamicTruthGlobalAssignmentStepDefinedFormula : formula :=
  codedAssignmentDefinedThroughTermAt (tVar 1) (tVar 0) (tVar 9).

Definition dynamicTruthGlobalRootBoundFormula : formula :=
  Formula.ltTermAt (tVar 8) (tVar 9).

Definition dynamicTruthGlobalRootLookupFormula (rootMode : term) : formula :=
  fixedLevelStateLookupTermAt
    (tVar 7) (tVar 6) (tVar 5) (tVar 4)
    (tVar 3) (tVar 2) (tVar 1) (tVar 0)
    (tVar 8) rootMode (tVar 10) (tVar 11) (tVar 12).

Definition dynamicTruthGlobalTraversalBodyFormula (rootMode : term)
    (localSigma localPi : formula) : formula :=
  fixedTruthTraversalAnd7
    dynamicTruthGlobalModeDefinedFormula
    dynamicTruthGlobalFormulaDefinedFormula
    dynamicTruthGlobalAssignmentCodeDefinedFormula
    dynamicTruthGlobalAssignmentStepDefinedFormula
    dynamicTruthGlobalRootBoundFormula
    (dynamicTruthGlobalRootLookupFormula rootMode)
    (dynamicTruthGlobalRowsFormula localSigma localPi).

Definition dynamicTruthGlobalFormula (rootMode : term)
    (localSigma localPi : formula) : formula :=
  fixedTruthTraversalEx10
    (dynamicTruthGlobalTraversalBodyFormula
      rootMode localSigma localPi).

(** The scope theorem is the syntactic counterpart of the preceding slot
    audit.  A 13-variable local row becomes part of a ternary global truth
    predicate after the five row binders and ten traversal witnesses. *)
Theorem dynamicTruthGlobalRowsFormula_scoped : forall localSigma localPi,
  DynamicTruthGlobalLocalRowScoped localSigma ->
  DynamicTruthGlobalLocalRowScoped localPi ->
  StandardFormulaScoped 13
    (dynamicTruthGlobalRowsFormula localSigma localPi).
Proof.
  intros localSigma localPi hSigma hPi.
  unfold dynamicTruthGlobalRowsFormula, fixedTruthTraversalAll5.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - unfold dynamicTruthGlobalRowBoundFormula.
    apply standardFormulaScoped_ltTermAt;
      apply standardTermScoped_var; lia.
  - apply standardFormulaScoped_imp.
    + unfold dynamicTruthGlobalRowLookupFormula,
        fixedLevelStateLookupTermAt, fixedLevelAnd4.
      repeat apply standardFormulaScoped_and;
        apply standardFormulaScoped_codedAssignmentLookupTermAt;
        apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_or.
      * apply standardFormulaScoped_and.
        -- unfold dynamicTruthGlobalSigmaModeFormula.
           apply standardFormulaScoped_eq.
           ++ apply standardTermScoped_var. lia.
           ++ apply standardTermScoped_zero.
        -- exact (standardFormulaScoped_weaken 13 18 localSigma
             hSigma (ltac:(lia))).
      * apply standardFormulaScoped_and.
        -- unfold dynamicTruthGlobalPiModeFormula.
           apply standardFormulaScoped_eq.
           ++ apply standardTermScoped_var. lia.
           ++ apply standardTermScoped_numeral.
        -- exact (standardFormulaScoped_weaken 13 18 localPi
             hPi (ltac:(lia))).
Qed.

Theorem dynamicTruthGlobalFormula_scoped : forall rootMode localSigma localPi,
  StandardTermScoped 13 rootMode ->
  DynamicTruthGlobalLocalRowScoped localSigma ->
  DynamicTruthGlobalLocalRowScoped localPi ->
  StandardFormulaScoped 3
    (dynamicTruthGlobalFormula rootMode localSigma localPi).
Proof.
  intros rootMode localSigma localPi hrootMode hSigma hPi.
  unfold dynamicTruthGlobalFormula, fixedTruthTraversalEx10, fixedLevelEx8.
  repeat apply standardFormulaScoped_ex.
  unfold dynamicTruthGlobalTraversalBodyFormula, fixedTruthTraversalAnd7.
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalModeDefinedFormula.
    apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalFormulaDefinedFormula.
    apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalAssignmentCodeDefinedFormula.
    apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalAssignmentStepDefinedFormula.
    apply standardFormulaScoped_codedAssignmentDefinedThroughTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalRootBoundFormula.
    apply standardFormulaScoped_ltTermAt;
      apply standardTermScoped_var; lia. }
  apply standardFormulaScoped_and.
  { unfold dynamicTruthGlobalRootLookupFormula,
      fixedLevelStateLookupTermAt, fixedLevelAnd4.
    apply standardFormulaScoped_and.
    { apply standardFormulaScoped_codedAssignmentLookupTermAt.
      * apply standardTermScoped_var. lia.
      * apply standardTermScoped_var. lia.
      * apply standardTermScoped_var. lia.
      * exact hrootMode. }
    apply standardFormulaScoped_and.
    { apply standardFormulaScoped_codedAssignmentLookupTermAt;
        apply standardTermScoped_var; lia. }
    apply standardFormulaScoped_and.
    { apply standardFormulaScoped_codedAssignmentLookupTermAt;
        apply standardTermScoped_var; lia. }
    apply standardFormulaScoped_codedAssignmentLookupTermAt;
      apply standardTermScoped_var; lia. }
  exact (dynamicTruthGlobalRowsFormula_scoped
    localSigma localPi hSigma hPi).
Qed.

(** ------------------------------------------------------------------
    Transparent formula-code polynomial. *)

Definition dynamicTruthFormulaAllCodeTerm (child : term) : term :=
  codeList2Term (Term.numeral 5) child.

Definition dynamicTruthFormulaAll5CodeTerm (child : term) : term :=
  dynamicTruthFormulaAllCodeTerm (dynamicTruthFormulaAllCodeTerm
    (dynamicTruthFormulaAllCodeTerm (dynamicTruthFormulaAllCodeTerm
      (dynamicTruthFormulaAllCodeTerm child)))).

Definition dynamicTruthFormulaEx10CodeTerm (child : term) : term :=
  formulaEx8CodeTerm
    (formulaExCodeTerm (formulaExCodeTerm child)).

Definition dynamicTruthFormulaAnd7CodeTerm
    (a b c d f g h : term) : term :=
  formulaAndCodeTerm a (formulaAndCodeTerm b
    (formulaAndCodeTerm c (formulaAndCodeTerm d
      (formulaAndCodeTerm f (formulaAndCodeTerm g h))))).

Definition dynamicTruthGlobalRowChoiceCodeTerm
    (localSigma localPi : term) : term :=
  formulaOrCodeTerm
    (formulaAndCodeTerm
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalSigmaModeFormula)
      localSigma)
    (formulaAndCodeTerm
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalPiModeFormula)
      localPi).

Definition dynamicTruthGlobalRowsCodeTerm
    (localSigma localPi : term) : term :=
  dynamicTruthFormulaAll5CodeTerm
    (formulaImpCodeTerm
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalRowBoundFormula)
      (formulaImpCodeTerm
        (fixedFormulaNumeralCodeTerm dynamicTruthGlobalRowLookupFormula)
        (dynamicTruthGlobalRowChoiceCodeTerm localSigma localPi))).

Definition dynamicTruthGlobalFormulaCodeTerm (rootMode : term)
    (localSigma localPi : term) : term :=
  dynamicTruthFormulaEx10CodeTerm
    (dynamicTruthFormulaAnd7CodeTerm
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalModeDefinedFormula)
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalFormulaDefinedFormula)
      (fixedFormulaNumeralCodeTerm
        dynamicTruthGlobalAssignmentCodeDefinedFormula)
      (fixedFormulaNumeralCodeTerm
        dynamicTruthGlobalAssignmentStepDefinedFormula)
      (fixedFormulaNumeralCodeTerm dynamicTruthGlobalRootBoundFormula)
      (fixedFormulaNumeralCodeTerm
        (dynamicTruthGlobalRootLookupFormula rootMode))
      (dynamicTruthGlobalRowsCodeTerm localSigma localPi)).

Definition rawDynamicTruthFormulaAll5Code (M : RawPAModel)
    (child : M) : M :=
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawFormulaAllCode M child)))).

Definition rawDynamicTruthFormulaEx10Code (M : RawPAModel)
    (child : M) : M :=
  rawFormulaEx8Code M
    (rawFormulaExCode M (rawFormulaExCode M child)).

Definition rawDynamicTruthFormulaAnd7Code (M : RawPAModel)
    (a b c d f g h : M) : M :=
  rawFormulaAndCode M a (rawFormulaAndCode M b
    (rawFormulaAndCode M c (rawFormulaAndCode M d
      (rawFormulaAndCode M f (rawFormulaAndCode M g h))))).

Definition rawDynamicTruthGlobalRowChoiceCode (M : RawPAModel)
    (localSigma localPi : M) : M :=
  rawFormulaOrCode M
    (rawFormulaAndCode M
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalSigmaModeFormula)
      localSigma)
    (rawFormulaAndCode M
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalPiModeFormula)
      localPi).

Definition rawDynamicTruthGlobalRowsCode (M : RawPAModel)
    (localSigma localPi : M) : M :=
  rawDynamicTruthFormulaAll5Code M
    (rawFormulaImpCode M
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalRowBoundFormula)
      (rawFormulaImpCode M
        (rawFixedFormulaNumeralCode M dynamicTruthGlobalRowLookupFormula)
        (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi))).

Definition rawDynamicTruthGlobalFormulaCode (M : RawPAModel)
    (rootMode : term) (localSigma localPi : M) : M :=
  rawDynamicTruthFormulaEx10Code M
    (rawDynamicTruthFormulaAnd7Code M
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalModeDefinedFormula)
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalFormulaDefinedFormula)
      (rawFixedFormulaNumeralCode M
        dynamicTruthGlobalAssignmentCodeDefinedFormula)
      (rawFixedFormulaNumeralCode M
        dynamicTruthGlobalAssignmentStepDefinedFormula)
      (rawFixedFormulaNumeralCode M dynamicTruthGlobalRootBoundFormula)
      (rawFixedFormulaNumeralCode M
        (dynamicTruthGlobalRootLookupFormula rootMode))
      (rawDynamicTruthGlobalRowsCode M localSigma localPi)).

Lemma raw_eval_dynamicTruthFormulaAllCodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthFormulaAllCodeTerm child) =
  rawFormulaAllCode M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthFormulaAllCodeTerm, rawFormulaAllCode.
  rewrite raw_eval_codeList2Term, raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthFormulaAll5CodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthFormulaAll5CodeTerm child) =
  rawDynamicTruthFormulaAll5Code M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthFormulaAll5CodeTerm,
    rawDynamicTruthFormulaAll5Code.
  rewrite !raw_eval_dynamicTruthFormulaAllCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthFormulaEx10CodeTerm : forall
    (M : RawPAModel) e child,
  raw_term_eval M e (dynamicTruthFormulaEx10CodeTerm child) =
  rawDynamicTruthFormulaEx10Code M (raw_term_eval M e child).
Proof.
  intros. unfold dynamicTruthFormulaEx10CodeTerm,
    rawDynamicTruthFormulaEx10Code.
  rewrite raw_eval_formulaEx8CodeTerm,
    !raw_eval_formulaExCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthFormulaAnd7CodeTerm : forall
    (M : RawPAModel) e a b c d f g h,
  raw_term_eval M e (dynamicTruthFormulaAnd7CodeTerm a b c d f g h) =
  rawDynamicTruthFormulaAnd7Code M
    (raw_term_eval M e a) (raw_term_eval M e b)
    (raw_term_eval M e c) (raw_term_eval M e d)
    (raw_term_eval M e f) (raw_term_eval M e g)
    (raw_term_eval M e h).
Proof.
  intros. unfold dynamicTruthFormulaAnd7CodeTerm,
    rawDynamicTruthFormulaAnd7Code.
  rewrite !raw_eval_formulaAndCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthGlobalRowChoiceCodeTerm : forall
    (M : RawPAModel) e localSigma localPi,
  raw_term_eval M e
    (dynamicTruthGlobalRowChoiceCodeTerm localSigma localPi) =
  rawDynamicTruthGlobalRowChoiceCode M
    (raw_term_eval M e localSigma) (raw_term_eval M e localPi).
Proof.
  intros. unfold dynamicTruthGlobalRowChoiceCodeTerm,
    rawDynamicTruthGlobalRowChoiceCode.
  rewrite raw_eval_formulaOrCodeTerm, !raw_eval_formulaAndCodeTerm,
    !raw_eval_fixedFormulaNumeralCodeTerm. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthGlobalRowsCodeTerm : forall
    (M : RawPAModel) e localSigma localPi,
  raw_term_eval M e
    (dynamicTruthGlobalRowsCodeTerm localSigma localPi) =
  rawDynamicTruthGlobalRowsCode M
    (raw_term_eval M e localSigma) (raw_term_eval M e localPi).
Proof.
  intros. unfold dynamicTruthGlobalRowsCodeTerm,
    rawDynamicTruthGlobalRowsCode.
  rewrite raw_eval_dynamicTruthFormulaAll5CodeTerm,
    !raw_eval_formulaImpCodeTerm,
    !raw_eval_fixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthGlobalRowChoiceCodeTerm.
  reflexivity.
Qed.

Lemma raw_eval_dynamicTruthGlobalFormulaCodeTerm : forall
    (M : RawPAModel) e rootMode localSigma localPi,
  raw_term_eval M e
    (dynamicTruthGlobalFormulaCodeTerm rootMode localSigma localPi) =
  rawDynamicTruthGlobalFormulaCode M rootMode
    (raw_term_eval M e localSigma) (raw_term_eval M e localPi).
Proof.
  intros. unfold dynamicTruthGlobalFormulaCodeTerm,
    rawDynamicTruthGlobalFormulaCode.
  rewrite raw_eval_dynamicTruthFormulaEx10CodeTerm,
    raw_eval_dynamicTruthFormulaAnd7CodeTerm,
    !raw_eval_fixedFormulaNumeralCodeTerm,
    raw_eval_dynamicTruthGlobalRowsCodeTerm.
  reflexivity.
Qed.

(** On standard syntax inputs the raw polynomial is the structural quotation
    of the displayed reordered-witness formula.  This theorem does not claim
    syntactic equality with the native traversal, whose ten bound variables
    occur in a different order. *)
Theorem rawDynamicTruthGlobalFormulaCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootMode localSigma localPi,
  rawDynamicTruthGlobalFormulaCode M rootMode
    (rawQuotedFormulaCode M localSigma)
    (rawQuotedFormulaCode M localPi) =
  rawQuotedFormulaCode M
    (dynamicTruthGlobalFormula rootMode localSigma localPi).
Proof.
  intros M hPA rootMode localSigma localPi.
  unfold rawDynamicTruthGlobalFormulaCode,
    rawDynamicTruthFormulaEx10Code,
    rawDynamicTruthFormulaAnd7Code,
    rawDynamicTruthGlobalRowsCode,
    rawDynamicTruthFormulaAll5Code,
    rawDynamicTruthGlobalRowChoiceCode.
  repeat rewrite rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

(** Keep the large fixed constructor polynomial folded during graph proofs. *)
Opaque dynamicTruthGlobalFormulaCodeTerm.

(** ------------------------------------------------------------------
    The standalone paired wrapper graph.

    Its public environment is

      globalSigma :: globalPi :: localSigma :: localPi :: tail.
*)

Definition dynamicTruthPairedGlobalWrapperGraph : formula :=
  pAnd
    (pEq (tVar 0)
      (dynamicTruthGlobalFormulaCodeTerm tZero (tVar 2) (tVar 3)))
    (pEq (tVar 1)
      (dynamicTruthGlobalFormulaCodeTerm
        (Term.numeral 1) (tVar 2) (tVar 3))).

Definition RawDynamicTruthPairedGlobalWrapperAt (M : RawPAModel)
    (localSigma localPi globalSigma globalPi : M) : Prop :=
  globalSigma = rawDynamicTruthGlobalFormulaCode M
    tZero localSigma localPi /\
  globalPi = rawDynamicTruthGlobalFormulaCode M
    (Term.numeral 1) localSigma localPi.

Arguments RawDynamicTruthPairedGlobalWrapperAt
  M localSigma localPi globalSigma globalPi : clear implicits.

Theorem raw_sat_dynamicTruthPairedGlobalWrapperGraph_iff : forall
    (M : RawPAModel) tail localSigma localPi globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi
      (scons M localSigma (scons M localPi tail))))
    dynamicTruthPairedGlobalWrapperGraph <->
  RawDynamicTruthPairedGlobalWrapperAt M
    localSigma localPi globalSigma globalPi.
Proof.
  intros M tail localSigma localPi globalSigma globalPi.
  unfold dynamicTruthPairedGlobalWrapperGraph,
    RawDynamicTruthPairedGlobalWrapperAt.
  cbn [raw_formula_sat raw_term_eval scons].
  rewrite !raw_eval_dynamicTruthGlobalFormulaCodeTerm.
  reflexivity.
Qed.

(** Constructor closure preserves internal atomic adequacy.  The fixed
    leaves are literal formula numerals, while the only variable leaves are
    the two already adequate local row codes. *)
Lemma rawDynamicTruthFormulaAll5Code_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthFormulaAll5Code M child).
Proof.
  intros M hPA child hchild.
  unfold rawDynamicTruthFormulaAll5Code.
  repeat apply raw_formulaAllCode_atomically_adequate; assumption.
Qed.

Lemma rawDynamicTruthFormulaEx10Code_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthFormulaEx10Code M child).
Proof.
  intros M hPA child hchild.
  unfold rawDynamicTruthFormulaEx10Code, rawFormulaEx8Code.
  repeat apply raw_formulaExCode_atomically_adequate; assumption.
Qed.

Lemma rawDynamicTruthGlobalRowChoiceCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawCodedFormulaAtomicallyAdequate M localSigma ->
  RawCodedFormulaAtomicallyAdequate M localPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthGlobalRowChoiceCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi hSigma hPi.
  unfold rawDynamicTruthGlobalRowChoiceCode.
  apply raw_formulaOrCode_atomically_adequate; [exact hPA | |].
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthGlobalSigmaModeFormula).
    + exact hSigma.
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthGlobalPiModeFormula).
    + exact hPi.
Qed.

Lemma rawDynamicTruthGlobalRowsCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall localSigma localPi,
  RawCodedFormulaAtomicallyAdequate M localSigma ->
  RawCodedFormulaAtomicallyAdequate M localPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthGlobalRowsCode M localSigma localPi).
Proof.
  intros M hPA localSigma localPi hSigma hPi.
  unfold rawDynamicTruthGlobalRowsCode.
  apply rawDynamicTruthFormulaAll5Code_atomically_adequate; [exact hPA |].
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthGlobalRowBoundFormula).
  - apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthGlobalRowLookupFormula).
    + exact (rawDynamicTruthGlobalRowChoiceCode_atomically_adequate
        M hPA localSigma localPi hSigma hPi).
Qed.

Theorem rawDynamicTruthGlobalFormulaCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootMode localSigma localPi,
  RawCodedFormulaAtomicallyAdequate M localSigma ->
  RawCodedFormulaAtomicallyAdequate M localPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthGlobalFormulaCode M
      rootMode localSigma localPi).
Proof.
  intros M hPA rootMode localSigma localPi hSigma hPi.
  unfold rawDynamicTruthGlobalFormulaCode,
    rawDynamicTruthFormulaAnd7Code.
  apply rawDynamicTruthFormulaEx10Code_atomically_adequate; [exact hPA |].
  repeat apply raw_formulaAndCode_atomically_adequate; try exact hPA;
    try apply raw_fixedFormulaNumeral_atomically_adequate; try exact hPA.
  exact (rawDynamicTruthGlobalRowsCode_atomically_adequate
    M hPA localSigma localPi hSigma hPi).
Qed.

Theorem dynamicTruthPairedGlobalWrapperGraph_adequacy : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      localSigma localPi globalSigma globalPi,
  RawDynamicTruthPairedGlobalWrapperAt M
    localSigma localPi globalSigma globalPi ->
  RawCodedFormulaAtomicallyAdequate M localSigma ->
  RawCodedFormulaAtomicallyAdequate M localPi ->
  RawCodedFormulaAtomicallyAdequate M globalSigma /\
  RawCodedFormulaAtomicallyAdequate M globalPi.
Proof.
  intros M hPA localSigma localPi globalSigma globalPi
    [-> ->] hSigma hPi.
  split; apply rawDynamicTruthGlobalFormulaCode_atomically_adequate;
    assumption.
Qed.

(** ------------------------------------------------------------------
    Combined global successor.

    Beneath the two hidden local-row witnesses the environment is

      localPi #0, localSigma #1,
      nextSigmaGlobal #2, nextPiGlobal #3,
      previousSigmaGlobal #4, previousPiGlobal #5,
      lowerLevel #6, tail #7 ...

    The two renamings below feed this environment to the already checked
    local-row graph and to the standalone wrapper graph. *)

Definition dynamicTruthGlobalSuccessorRowRenaming (index : nat) : nat :=
  match index with
  | 0 => 1
  | 1 => 0
  | 2 => 4
  | 3 => 5
  | 4 => 6
  | S (S (S (S (S tailIndex)))) => 7 + tailIndex
  end.

Definition dynamicTruthGlobalSuccessorWrapperRenaming (index : nat) : nat :=
  match index with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 0
  | S (S (S (S tailIndex))) => 7 + tailIndex
  end.

Lemma raw_sat_dynamicTruthGlobalSuccessorRowRenamed_iff : forall
    (M : RawPAModel) tail lowerLevel previousSigma previousPi
      nextSigma nextPi localSigma localPi,
  raw_formula_sat M
    (scons M localPi (scons M localSigma
      (scons M nextSigma (scons M nextPi
        (scons M previousSigma (scons M previousPi
          (scons M lowerLevel tail)))))))
    (Formula.rename dynamicTruthGlobalSuccessorRowRenaming
      dynamicTruthPairedSuccessorRowGraph) <->
  raw_formula_sat M
    (scons M localSigma (scons M localPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    dynamicTruthPairedSuccessorRowGraph.
Proof.
  intros M tail lowerLevel previousSigma previousPi
    nextSigma nextPi localSigma localPi.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|[|[|tailIndex]]]]];
    cbn [dynamicTruthGlobalSuccessorRowRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (7 + tailIndex) with
      (S (S (S (S (S (S (S tailIndex))))))) by lia.
    reflexivity.
Qed.

Lemma raw_sat_dynamicTruthGlobalSuccessorWrapperRenamed_iff : forall
    (M : RawPAModel) tail lowerLevel previousSigma previousPi
      nextSigma nextPi localSigma localPi,
  raw_formula_sat M
    (scons M localPi (scons M localSigma
      (scons M nextSigma (scons M nextPi
        (scons M previousSigma (scons M previousPi
          (scons M lowerLevel tail)))))))
    (Formula.rename dynamicTruthGlobalSuccessorWrapperRenaming
      dynamicTruthPairedGlobalWrapperGraph) <->
  raw_formula_sat M
    (scons M nextSigma (scons M nextPi
      (scons M localSigma (scons M localPi tail))))
    dynamicTruthPairedGlobalWrapperGraph.
Proof.
  intros M tail lowerLevel previousSigma previousPi
    nextSigma nextPi localSigma localPi.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|[|tailIndex]]]];
    cbn [dynamicTruthGlobalSuccessorWrapperRenaming].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - replace (7 + tailIndex) with
      (S (S (S (S (S (S (S tailIndex))))))) by lia.
    reflexivity.
Qed.

Definition dynamicTruthPairedGlobalSuccessorGraph : formula :=
  pEx (pEx
    (pAnd
      (Formula.rename dynamicTruthGlobalSuccessorRowRenaming
        dynamicTruthPairedSuccessorRowGraph)
      (Formula.rename dynamicTruthGlobalSuccessorWrapperRenaming
        dynamicTruthPairedGlobalWrapperGraph))).

Definition RawDynamicTruthPairedGlobalSuccessorAt (M : RawPAModel)
    (previousSigma previousPi lowerLevel nextSigma nextPi : M) : Prop :=
  exists localSigma localPi : M,
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigma previousPi lowerLevel localSigma localPi /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigma localPi nextSigma nextPi.

Arguments RawDynamicTruthPairedGlobalSuccessorAt
  M previousSigma previousPi lowerLevel nextSigma nextPi : clear implicits.

(** Exact law-free semantics.  The existentially exposed values are the
    local row codes; the two public outputs are genuine global predicates. *)
Theorem raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff : forall
    (M : RawPAModel) tail lowerLevel previousSigma previousPi
      nextSigma nextPi,
  raw_formula_sat M
    (scons M nextSigma (scons M nextPi
      (scons M previousSigma (scons M previousPi
        (scons M lowerLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph <->
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel nextSigma nextPi.
Proof.
  intros M tail lowerLevel previousSigma previousPi nextSigma nextPi.
  unfold dynamicTruthPairedGlobalSuccessorGraph,
    RawDynamicTruthPairedGlobalSuccessorAt.
  cbn [raw_formula_sat].
  split.
  - intros [localSigma [localPi [hrow hwrapper]]].
    exists localSigma, localPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail
          lowerLevel previousSigma previousPi localSigma localPi)).
      apply (proj1
        (raw_sat_dynamicTruthGlobalSuccessorRowRenamed_iff M tail
          lowerLevel previousSigma previousPi nextSigma nextPi
          localSigma localPi)).
      exact hrow.
    + apply (proj1
        (raw_sat_dynamicTruthPairedGlobalWrapperGraph_iff M tail
          localSigma localPi nextSigma nextPi)).
      apply (proj1
        (raw_sat_dynamicTruthGlobalSuccessorWrapperRenamed_iff M tail
          lowerLevel previousSigma previousPi nextSigma nextPi
          localSigma localPi)).
      exact hwrapper.
  - intros [localSigma [localPi [hrow hwrapper]]].
    exists localSigma, localPi. split.
    + apply (proj2
        (raw_sat_dynamicTruthGlobalSuccessorRowRenamed_iff M tail
          lowerLevel previousSigma previousPi nextSigma nextPi
          localSigma localPi)).
      apply (proj2
        (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail
          lowerLevel previousSigma previousPi localSigma localPi)).
      exact hrow.
    + apply (proj2
        (raw_sat_dynamicTruthGlobalSuccessorWrapperRenamed_iff M tail
          lowerLevel previousSigma previousPi nextSigma nextPi
          localSigma localPi)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalWrapperGraph_iff M tail
          localSigma localPi nextSigma nextPi)).
      exact hwrapper.
Qed.

(** This is the adequate paired-successor interface required by the generic
    carrier-indexed orbit.  Adequacy first flows through the local row
    compiler and then through the constructor-only global shell. *)
Theorem dynamicTruthPairedGlobalSuccessorGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedGlobalSuccessorGraph.
Proof.
  intros M hPA tail lowerLevel previousSigma previousPi
    hpreviousSigma hpreviousPi.
  destruct (dynamicTruthPairedSuccessorRowGraph_raw_adequate_total
    M hPA tail lowerLevel previousSigma previousPi
    hpreviousSigma hpreviousPi) as
    (localSigma & localPi & hlocal & hlocalSigma & hlocalPi).
  set (nextSigma := rawDynamicTruthGlobalFormulaCode M
    tZero localSigma localPi).
  set (nextPi := rawDynamicTruthGlobalFormulaCode M
    (Term.numeral 1) localSigma localPi).
  exists nextSigma, nextPi.
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
        lowerLevel previousSigma previousPi nextSigma nextPi)).
    exists localSigma, localPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail
          lowerLevel previousSigma previousPi localSigma localPi)).
      exact hlocal.
    + unfold RawDynamicTruthPairedGlobalWrapperAt,
        nextSigma, nextPi. split; reflexivity.
  - split; unfold nextSigma, nextPi;
      apply rawDynamicTruthGlobalFormulaCode_atomically_adequate;
      assumption.
Qed.

(** ------------------------------------------------------------------
    Row-aligned rank-zero base and its global wrapper.

    The older local base graph uses the conventional ternary environment
    [code :: assignmentCode :: assignmentStep].  The five row binders use
    the reverse endpoint order [assignmentStep :: assignmentCode :: code].
    These two fixed formulas are therefore the row-aligned rank-zero leaves
    inserted into the global shell. *)

Definition dynamicTruthGlobalSigmaZeroRowFormula : formula :=
  fixedLevelSigmaZeroTermAt (tVar 2) (tVar 1) (tVar 0).

Definition dynamicTruthGlobalPiZeroRowFormula : formula :=
  fixedLevelPiZeroTermAt (tVar 2) (tVar 1) (tVar 0).

Definition rawDynamicTruthGlobalSigmaZeroRowCode (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M dynamicTruthGlobalSigmaZeroRowFormula.

Definition rawDynamicTruthGlobalPiZeroRowCode (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M dynamicTruthGlobalPiZeroRowFormula.

Definition rawDynamicTruthGlobalSigmaBaseCode (M : RawPAModel) : M :=
  rawDynamicTruthGlobalFormulaCode M tZero
    (rawDynamicTruthGlobalSigmaZeroRowCode M)
    (rawDynamicTruthGlobalPiZeroRowCode M).

Definition rawDynamicTruthGlobalPiBaseCode (M : RawPAModel) : M :=
  rawDynamicTruthGlobalFormulaCode M (Term.numeral 1)
    (rawDynamicTruthGlobalSigmaZeroRowCode M)
    (rawDynamicTruthGlobalPiZeroRowCode M).

Definition dynamicTruthPairedGlobalBaseGraph : formula :=
  pAnd
    (pEq (tVar 0)
      (dynamicTruthGlobalFormulaCodeTerm tZero
        (fixedFormulaNumeralCodeTerm
          dynamicTruthGlobalSigmaZeroRowFormula)
        (fixedFormulaNumeralCodeTerm
          dynamicTruthGlobalPiZeroRowFormula)))
    (pEq (tVar 1)
      (dynamicTruthGlobalFormulaCodeTerm (Term.numeral 1)
        (fixedFormulaNumeralCodeTerm
          dynamicTruthGlobalSigmaZeroRowFormula)
        (fixedFormulaNumeralCodeTerm
          dynamicTruthGlobalPiZeroRowFormula))).

Definition RawDynamicTruthPairedGlobalBaseAt (M : RawPAModel)
    (globalSigma globalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalWrapperAt M
    (rawDynamicTruthGlobalSigmaZeroRowCode M)
    (rawDynamicTruthGlobalPiZeroRowCode M)
    globalSigma globalPi.

Arguments RawDynamicTruthPairedGlobalBaseAt M globalSigma globalPi
  : clear implicits.

Theorem raw_sat_dynamicTruthPairedGlobalBaseGraph_iff : forall
    (M : RawPAModel) tail globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi tail))
    dynamicTruthPairedGlobalBaseGraph <->
  RawDynamicTruthPairedGlobalBaseAt M globalSigma globalPi.
Proof.
  intros M tail globalSigma globalPi.
  unfold dynamicTruthPairedGlobalBaseGraph,
    RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt,
    rawDynamicTruthGlobalSigmaZeroRowCode,
    rawDynamicTruthGlobalPiZeroRowCode.
  cbn [raw_formula_sat raw_term_eval scons].
  rewrite !raw_eval_dynamicTruthGlobalFormulaCodeTerm,
    !raw_eval_fixedFormulaNumeralCodeTerm.
  reflexivity.
Qed.

Theorem dynamicTruthPairedGlobalBaseGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal M
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail.
  set (localSigma := rawDynamicTruthGlobalSigmaZeroRowCode M).
  set (localPi := rawDynamicTruthGlobalPiZeroRowCode M).
  set (globalSigma := rawDynamicTruthGlobalFormulaCode M
    tZero localSigma localPi).
  set (globalPi := rawDynamicTruthGlobalFormulaCode M
    (Term.numeral 1) localSigma localPi).
  exists globalSigma, globalPi. split.
  - apply (proj2
      (raw_sat_dynamicTruthPairedGlobalBaseGraph_iff M tail
        globalSigma globalPi)).
    unfold RawDynamicTruthPairedGlobalBaseAt,
      RawDynamicTruthPairedGlobalWrapperAt,
      globalSigma, globalPi, localSigma, localPi.
    split; reflexivity.
  - assert (hlocalSigma : RawCodedFormulaAtomicallyAdequate M localSigma).
    { unfold localSigma, rawDynamicTruthGlobalSigmaZeroRowCode.
      exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthGlobalSigmaZeroRowFormula). }
    assert (hlocalPi : RawCodedFormulaAtomicallyAdequate M localPi).
    { unfold localPi, rawDynamicTruthGlobalPiZeroRowCode.
      exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthGlobalPiZeroRowFormula). }
    split; unfold globalSigma, globalPi;
      apply rawDynamicTruthGlobalFormulaCode_atomically_adequate;
      assumption.
Qed.

(** ------------------------------------------------------------------
    Semantic pinning against the native level-zero certificates.

    The formulas are intentionally not syntactically equal: the native
    traversal puts [modeCode] in body slot #9 and [rootIndex] in slot #0,
    whereas the literal-row wrapper uses slots #7 and #8 respectively.
    Since all ten witnesses are existential, the following permutation
    proves exact semantic equivalence. *)

Lemma dynamicTruthGlobalRowsFormula_zero_eq :
  dynamicTruthGlobalRowsFormula
    dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula =
  fixedLevelZeroTruthTraversalRowsTermAt
    (tVar 7) (tVar 6) (tVar 5) (tVar 4)
    (tVar 3) (tVar 2) (tVar 1) (tVar 0) (tVar 9).
Proof.
  reflexivity.
Qed.

Lemma dynamicTruthGlobalTraversalBodyFormula_zero_eq : forall rootMode,
  dynamicTruthGlobalTraversalBodyFormula rootMode
    dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula =
  fixedLevelZeroTruthTraversalTermAt
    (tVar 7) (tVar 6) (tVar 5) (tVar 4)
    (tVar 3) (tVar 2) (tVar 1) (tVar 0)
    (tVar 9) (tVar 8) rootMode
    (tVar 10) (tVar 11) (tVar 12).
Proof.
  intro rootMode.
  unfold dynamicTruthGlobalTraversalBodyFormula,
    dynamicTruthGlobalModeDefinedFormula,
    dynamicTruthGlobalFormulaDefinedFormula,
    dynamicTruthGlobalAssignmentCodeDefinedFormula,
    dynamicTruthGlobalAssignmentStepDefinedFormula,
    dynamicTruthGlobalRootBoundFormula,
    dynamicTruthGlobalRootLookupFormula,
    fixedLevelZeroTruthTraversalTermAt.
  rewrite dynamicTruthGlobalRowsFormula_zero_eq.
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthGlobalZeroFormula_iff : forall
    (M : RawPAModel) e rootMode,
  raw_formula_sat M e
    (dynamicTruthGlobalFormula (Term.numeral rootMode)
      dynamicTruthGlobalSigmaZeroRowFormula
      dynamicTruthGlobalPiZeroRowFormula) <->
  exists modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex : M,
    RawFixedLevelZeroTruthTraversal M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex (rawNumeralValue M rootMode)
      (e 0) (e 1) (e 2).
Proof.
  intros M e rootMode.
  unfold dynamicTruthGlobalFormula.
  rewrite dynamicTruthGlobalTraversalBodyFormula_zero_eq.
  cbn [fixedTruthTraversalEx10 fixedLevelEx8 raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelZeroTruthTraversalTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros (bound & rootIndex & modeCode & modeStep & formulaCode &
      formulaStep & assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & htraversal).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    rewrite raw_term_eval_numeral in htraversal.
    exact htraversal.
  - intros (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & bound & rootIndex &
      htraversal).
    exists bound, rootIndex, modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep.
    rewrite raw_term_eval_numeral.
    exact htraversal.
Qed.

Definition dynamicTruthGlobalSigmaBaseFormula : formula :=
  dynamicTruthGlobalFormula tZero
    dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula.

Definition dynamicTruthGlobalPiBaseFormula : formula :=
  dynamicTruthGlobalFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula.

Theorem rawDynamicTruthGlobalSigmaBaseCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthGlobalSigmaBaseCode M =
  rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthGlobalSigmaBaseCode,
    rawDynamicTruthGlobalSigmaZeroRowCode,
    rawDynamicTruthGlobalPiZeroRowCode,
    dynamicTruthGlobalSigmaBaseFormula.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  exact (rawDynamicTruthGlobalFormulaCode_quoted M hPA
    tZero dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula).
Qed.

Theorem rawDynamicTruthGlobalPiBaseCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthGlobalPiBaseCode M =
  rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthGlobalPiBaseCode,
    rawDynamicTruthGlobalSigmaZeroRowCode,
    rawDynamicTruthGlobalPiZeroRowCode,
    dynamicTruthGlobalPiBaseFormula.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  exact (rawDynamicTruthGlobalFormulaCode_quoted M hPA
    (Term.numeral 1) dynamicTruthGlobalSigmaZeroRowFormula
    dynamicTruthGlobalPiZeroRowFormula).
Qed.

(** Thus the public base graph returns structural quotations of the
    reordered-witness global formulas in every PA model. *)
Theorem dynamicTruthPairedGlobalBaseGraph_quoted_representation : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail globalSigma globalPi,
  raw_formula_sat M
    (scons M globalSigma (scons M globalPi tail))
    dynamicTruthPairedGlobalBaseGraph <->
  globalSigma = rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula /\
  globalPi = rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula.
Proof.
  intros M hPA tail globalSigma globalPi.
  rewrite raw_sat_dynamicTruthPairedGlobalBaseGraph_iff.
  unfold RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt,
    rawDynamicTruthGlobalSigmaBaseCode,
    rawDynamicTruthGlobalPiBaseCode.
  change ((globalSigma = rawDynamicTruthGlobalSigmaBaseCode M /\
    globalPi = rawDynamicTruthGlobalPiBaseCode M) <->
    (globalSigma =
      rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula /\
     globalPi =
      rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)).
  rewrite rawDynamicTruthGlobalSigmaBaseCode_quoted by exact hPA.
  rewrite rawDynamicTruthGlobalPiBaseCode_quoted by exact hPA.
  reflexivity.
Qed.

Corollary dynamicTruthPairedGlobalBaseGraph_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M
    (scons M (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      (scons M (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
        tail))
    dynamicTruthPairedGlobalBaseGraph.
Proof.
  intros M hPA tail.
  apply (proj2
    (dynamicTruthPairedGlobalBaseGraph_quoted_representation M hPA tail
      _ _)).
  split; reflexivity.
Qed.

Theorem raw_sat_dynamicTruthGlobalSigmaBaseFormula_native_iff : forall
    (M : RawPAModel) tail root assignmentCode assignmentStep,
  raw_formula_sat M
    (scons M root (scons M assignmentCode
      (scons M assignmentStep tail)))
    dynamicTruthGlobalSigmaBaseFormula <->
  raw_formula_sat M
    (scons M root (scons M assignmentCode
      (scons M assignmentStep tail)))
    (fixedLevelSigmaTruthCertificateTermAt 0
      (tVar 0) (tVar 1) (tVar 2)).
Proof.
  intros M tail root assignmentCode assignmentStep.
  unfold dynamicTruthGlobalSigmaBaseFormula.
  change (raw_formula_sat M
    (scons M root (scons M assignmentCode
      (scons M assignmentStep tail)))
    (dynamicTruthGlobalFormula (Term.numeral 0)
      dynamicTruthGlobalSigmaZeroRowFormula
      dynamicTruthGlobalPiZeroRowFormula) <->
    raw_formula_sat M
      (scons M root (scons M assignmentCode
        (scons M assignmentStep tail)))
      (fixedLevelSigmaTruthCertificateTermAt 0
        (tVar 0) (tVar 1) (tVar 2))).
  rewrite raw_sat_dynamicTruthGlobalZeroFormula_iff.
  rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  cbn [RawFixedLevelSigmaTruthCertificate raw_term_eval scons].
  reflexivity.
Qed.

Theorem raw_sat_dynamicTruthGlobalPiBaseFormula_native_iff : forall
    (M : RawPAModel) tail root assignmentCode assignmentStep,
  raw_formula_sat M
    (scons M root (scons M assignmentCode
      (scons M assignmentStep tail)))
    dynamicTruthGlobalPiBaseFormula <->
  raw_formula_sat M
    (scons M root (scons M assignmentCode
      (scons M assignmentStep tail)))
    (fixedLevelPiFalsityCertificateTermAt 0
      (tVar 0) (tVar 1) (tVar 2)).
Proof.
  intros M tail root assignmentCode assignmentStep.
  unfold dynamicTruthGlobalPiBaseFormula.
  rewrite raw_sat_dynamicTruthGlobalZeroFormula_iff.
  rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [RawFixedLevelPiFalsityCertificate raw_term_eval scons].
  reflexivity.
Qed.

End PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
