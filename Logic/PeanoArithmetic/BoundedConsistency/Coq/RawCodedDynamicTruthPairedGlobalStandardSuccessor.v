(**
  Exact standard-syntax realization of paired dynamic-truth successors.

  The Sigma row module already exposes its standard realization, while the
  Pi row historically stopped at quotation of its constructor polynomial.
  This module supplies the missing dual theorem and packages both polarities
  behind the paired global successor relation.  Keeping these derived facts
  outside the foundational graph files also gives downstream clients a
  narrow dependency: existing graph users need not be rebuilt merely because
  a new standard-syntax view is added.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph.

Module PABoundedRawCodedDynamicTruthPairedGlobalStandardSuccessor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.

(** Standard substitution realizes the domain component of a Pi successor
    row.  This is the exact dual of
    [raw_dynamicTruthSigmaRowInstantiatedDomain_standard]. *)
Theorem raw_dynamicTruthPiRowInstantiatedDomain_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall successorNumeral,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M successorNumeral)
    (rawNumeralValue M
      (formulaCode dynamicTruthPiRowDomainTemplate))
    (rawQuotedFormulaCode M
      (dynamicTruthPiRowInstantiatedDomain successorNumeral)).
Proof.
  intros M hPA successorNumeral.
  unfold dynamicTruthPiRowInstantiatedDomain.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    dynamicTruthPiRowDomainTemplate).
  exact (raw_codedFormulaSingleSubstitution_standard M hPA
    successorNumeral dynamicTruthPiRowDomainTemplate).
Qed.

(** The complete Pi row is therefore a literal quotation whenever its lower
    predicate is standard three-variable syntax. *)
Theorem raw_dynamicTruthPiSuccessorRow_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lowerLevel successorNumeral lowerSigma,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel)
    (rawQuotedTermCode M successorNumeral) ->
  DynamicTruthPiCoqLowerScoped lowerSigma ->
  RawDynamicTruthPiSuccessorRowAt M
    (rawQuotedFormulaCode M lowerSigma) lowerLevel
    (rawQuotedFormulaCode M
      (dynamicTruthPiSuccessorRowFormula successorNumeral lowerSigma)).
Proof.
  intros M hPA lowerLevel successorNumeral lowerSigma
    hsuccessorNumeral hscope.
  exists (rawQuotedTermCode M successorNumeral),
    (rawQuotedFormulaCode M
      (dynamicTruthPiRowInstantiatedDomain successorNumeral)),
    (rawQuotedFormulaCode M
      (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
        lowerSigma)).
  split; [exact hsuccessorNumeral |].
  split.
  - exact (raw_dynamicTruthPiRowInstantiatedDomain_standard
      M hPA successorNumeral).
  - split.
    + exact (raw_dynamicTruthPiCoqLowerApplication_standard_rename
        M hPA lowerSigma hscope).
    + symmetry.
      exact (rawDynamicTruthPiSuccessorRowCode_quoted
        M hPA successorNumeral lowerSigma).
Qed.

(** Standard-syntax realization of one complete paired global successor.
    Both local rows use the same represented successor numeral; the outer
    wrapper is then identified by the generic global quotation theorem. *)
Theorem raw_dynamicTruthPairedGlobalSuccessor_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lowerLevel successorNumeral previousSigma previousPi,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel)
    (rawQuotedTermCode M successorNumeral) ->
  DynamicTruthCoqLowerScoped previousPi ->
  DynamicTruthPiCoqLowerScoped previousSigma ->
  RawDynamicTruthPairedGlobalSuccessorAt M
    (rawQuotedFormulaCode M previousSigma)
    (rawQuotedFormulaCode M previousPi) lowerLevel
    (rawQuotedFormulaCode M
      (dynamicTruthGlobalFormula tZero
        (dynamicTruthSigmaSuccessorRowFormula
          successorNumeral previousPi)
        (dynamicTruthPiSuccessorRowFormula
          successorNumeral previousSigma)))
    (rawQuotedFormulaCode M
      (dynamicTruthGlobalFormula (Term.numeral 1)
        (dynamicTruthSigmaSuccessorRowFormula
          successorNumeral previousPi)
        (dynamicTruthPiSuccessorRowFormula
          successorNumeral previousSigma))).
Proof.
  intros M hPA lowerLevel successorNumeral previousSigma previousPi
    hsuccessorNumeral hpiScope hsigmaScope.
  exists
    (rawQuotedFormulaCode M
      (dynamicTruthSigmaSuccessorRowFormula
        successorNumeral previousPi)),
    (rawQuotedFormulaCode M
      (dynamicTruthPiSuccessorRowFormula
        successorNumeral previousSigma)).
  split.
  - split.
    + exact (raw_dynamicTruthSigmaSuccessorRow_standard
        M hPA lowerLevel successorNumeral previousPi
        hsuccessorNumeral hpiScope).
    + exact (raw_dynamicTruthPiSuccessorRow_standard
        M hPA lowerLevel successorNumeral previousSigma
        hsuccessorNumeral hsigmaScope).
  - unfold RawDynamicTruthPairedGlobalWrapperAt.
    split; symmetry; apply rawDynamicTruthGlobalFormulaCode_quoted;
      exact hPA.
Qed.

End PABoundedRawCodedDynamicTruthPairedGlobalStandardSuccessor.
