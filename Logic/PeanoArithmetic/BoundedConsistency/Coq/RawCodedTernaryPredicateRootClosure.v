(**
  Root closure for represented ternary predicates.

  The existing scoped diagonal-substitution theorem specializes its
  replacement to a model-internal numeral term.  Ternary-application
  interchange needs the stronger, semantically natural statement: a formula
  with no free variable at or above the current depth is unchanged by
  substitution of *any* honestly represented term.

  The replacement is never inserted into such a formula.  Nevertheless the
  raw substitution atom first shifts it to the current depth, so the proof
  uses represented term-shift totality to choose that auxiliary code and then
  reuses the existing identity-opening tree for each standard equality leaf.
  Formula constructors are rebuilt bottom-up, retaining the exact input code
  as their output.  This yields the advertised three-variable root-closure
  certificate for every standard ternary-scoped quotation.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTermEvaluationRealization
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedFormulaDiagonalOperation
  RawCodedFormulaDiagonalOperationComposition
  RawCodedFormulaShiftTotality
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateTernaryApplication.

Module PABoundedRawCodedTernaryPredicateRootClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaDiagonalOperation.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateTernaryApplication.

(** An arbitrary represented replacement can be shifted to [depth].  Once
    selected, the standard input term is fixed because all of its variables
    lie strictly below that depth. *)
Lemma raw_codedFormulaSubstitutionAtom_standard_identity_below_of_syntax :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    replacement assignmentCode assignmentStep scope depth input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  StandardTermScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA replacement assignmentCode assignmentStep
    scope depth input hreplacement hscope hdepth.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement assignmentCode assignmentStep hreplacement
    (raw_zero M) depth) as [liftedReplacement hliftedReplacement].
  exists liftedReplacement. split.
  - exact hliftedReplacement.
  - exact (raw_codedTermOpening_standard_identity_below M hPA
      scope depth liftedReplacement input hscope hdepth).
Qed.

(** Structural diagonal substitution for a standard formula and an arbitrary
    represented replacement.  This is deliberately depth-indexed: entering a
    binder increments both the metatheoretic scope and the carrier cutoff. *)
Theorem raw_codedFormulaDiagonalSubstitution_standard_scoped_of_syntax :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    replacement assignmentCode assignmentStep scope depth input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  StandardFormulaScoped scope input ->
  rawLe M (rawNumeralValue M scope) depth ->
  RawCodedFormulaDiagonalSubstitution M replacement depth
    (rawQuotedFormulaCode M input).
Proof.
  intros M hPA replacement assignmentCode assignmentStep
    scope depth input hreplacement.
  revert scope depth.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros scope depth hscope hdepth;
    cbn [rawQuotedFormulaCode].
  - apply (raw_codedFormulaDiagonalSubstitution_eq M hPA
      replacement depth (rawQuotedTermCode M lhs)
      (rawQuotedTermCode M rhs)).
    + apply
        (raw_codedFormulaSubstitutionAtom_standard_identity_below_of_syntax
          M hPA replacement assignmentCode assignmentStep
          scope depth lhs hreplacement).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply
        (raw_codedFormulaSubstitutionAtom_standard_identity_below_of_syntax
          M hPA replacement assignmentCode assignmentStep
          scope depth rhs hreplacement).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - exact (raw_codedFormulaDiagonalSubstitution_bot M hPA
      replacement depth).
  - apply (raw_codedFormulaDiagonalSubstitution_imp M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_and M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_or M hPA
      replacement depth (rawQuotedFormulaCode M lhs)
      (rawQuotedFormulaCode M rhs)).
    + apply (IHlhs scope depth).
      * intros index hfree. apply hscope. now left.
      * exact hdepth.
    + apply (IHrhs scope depth).
      * intros index hfree. apply hscope. now right.
      * exact hdepth.
  - apply (raw_codedFormulaDiagonalSubstitution_all M hPA
      replacement depth (rawQuotedFormulaCode M child)).
    apply (IHchild (S scope) (raw_succ M depth)).
    + exact (StandardFormulaScoped_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M depth)).
      exact (raw_rank_succ_le M hPA _ _ hdepth).
  - apply (raw_codedFormulaDiagonalSubstitution_ex M hPA
      replacement depth (rawQuotedFormulaCode M child)).
    apply (IHchild (S scope) (raw_succ M depth)).
    + exact (StandardFormulaScoped_ex_binder scope child hscope).
    + change (rawLe M (raw_succ M (rawNumeralValue M scope))
        (raw_succ M depth)).
      exact (raw_rank_succ_le M hPA _ _ hdepth).
Qed.

(** A quoted formula whose free variables are among [#0,#1,#2] satisfies the
    complete represented root-closure interface.  In particular the final
    substitution clause quantifies over arbitrary, possibly nonstandard,
    represented replacement terms. *)
Theorem raw_quotedFormula_ternaryPredicateRootClosed : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  StandardFormulaScoped 3 input ->
  RawCodedTernaryPredicateRootClosed M (rawQuotedFormulaCode M input).
Proof.
  intros M hPA input hscope.
  split.
  - exact (raw_quotedFormula_atomically_adequate M hPA input).
  - split.
    + exact (raw_codedFormulaShift_standard_scoped_identity
        M hPA 3 1 input hscope).
    + intros replacement assignmentCode assignmentStep hreplacement.
      apply (raw_codedFormulaOperation_of_diagonal M hPA
        (RawCodedFormulaSubstitutionAtom M) replacement
        (rawNumeralValue M 3) (rawQuotedFormulaCode M input)).
      apply
        (raw_codedFormulaDiagonalSubstitution_standard_scoped_of_syntax
          M hPA replacement assignmentCode assignmentStep 3
          (rawNumeralValue M 3) input hreplacement hscope).
      apply raw_rank_le_refl. exact hPA.
Qed.

End PABoundedRawCodedTernaryPredicateRootClosure.
