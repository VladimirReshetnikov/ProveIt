(**
  An arithmetical formula for represented ternary-predicate root closure.

  [RawCodedTernaryPredicateRootClosed] is a carrier-level interface: it says
  that a formula code is atomically adequate, is fixed by the protective
  shift above its three free arguments, and is fixed by substitution of
  every honestly represented term above those arguments.  This file gives
  that interface an actual PA formula.

  The three universal binders in the last conjunct have the environment

      replacement :: assignmentCode :: assignmentStep :: tail

  when read from [tVar 2] down to [tVar 0].  In particular, the predicate
  term must be lifted by three before it is passed to the represented
  formula-operation graph.  Keeping that lift visible is important: an
  unlifted predicate would accidentally refer to [assignmentStep].
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateTernaryApplication.

Module PABoundedRawCodedTernaryPredicateRootClosureFormula.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateTernaryApplication.

(** Formula with one displayed term parameter [predicate]. *)
Definition codedTernaryPredicateRootClosedTermAt
    (predicate : term) : formula :=
  operationAnd3
    (codedFormulaAtomicallyAdequateTermAt predicate)
    (codedFormulaShiftTermAt
      (Term.numeral 3) (Term.numeral 1) predicate predicate)
    (pAll (pAll (pAll
      (pImp
        (termSyntaxRealizableTermAt (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaOperationTermAt
          codedFormulaSubstitutionAtomTermAt
          (tVar 2) (Term.numeral 3)
          (liftTerm 3 predicate) (liftTerm 3 predicate)))))).

(** Closed-over-environment presentation used by invariant formulas. *)
Definition codedTernaryPredicateRootClosedFormula : formula :=
  codedTernaryPredicateRootClosedTermAt (tVar 0).

(** The only renaming calculation needed by the semantic proof. *)
Lemma raw_rootClosure_eval_liftTerm_three : forall
    (M : RawPAModel) replacement assignmentCode assignmentStep
    (e : nat -> M) t,
  raw_term_eval M
    (scons M assignmentStep
      (scons M assignmentCode (scons M replacement e)))
    (liftTerm 3 t) =
  raw_term_eval M e t.
Proof.
  intros M replacement assignmentCode assignmentStep e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia.
  reflexivity.
Qed.

(** Exact raw semantics.  No PA laws are required merely to interpret the
    formula; the relation is built from the exact semantics of its three
    represented subgraphs. *)
Theorem raw_sat_codedTernaryPredicateRootClosedTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) predicate,
  raw_formula_sat M e
    (codedTernaryPredicateRootClosedTermAt predicate) <->
  RawCodedTernaryPredicateRootClosed M
    (raw_term_eval M e predicate).
Proof.
  intros M e predicate.
  unfold codedTernaryPredicateRootClosedTermAt,
    RawCodedTernaryPredicateRootClosed, operationAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  rewrite raw_sat_codedFormulaShiftTermAt_iff.
  setoid_rewrite raw_sat_termSyntaxRealizableTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff
    M _ codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  repeat setoid_rewrite raw_rootClosure_eval_liftTerm_three.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Corollary raw_sat_codedTernaryPredicateRootClosedFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedTernaryPredicateRootClosedFormula <->
  RawCodedTernaryPredicateRootClosed M (e 0).
Proof.
  intros M e. unfold codedTernaryPredicateRootClosedFormula.
  rewrite raw_sat_codedTernaryPredicateRootClosedTermAt_iff.
  reflexivity.
Qed.

End PABoundedRawCodedTernaryPredicateRootClosureFormula.
