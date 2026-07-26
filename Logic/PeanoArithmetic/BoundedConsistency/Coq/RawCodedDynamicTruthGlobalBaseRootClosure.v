(**
  Three-variable root closure of the paired global truth-code base.

  The global rank-zero codes are literal quotations of the row-aligned
  Sigma/Pi traversal predicates.  Their local rows use thirteen variables;
  the wrapper binds ten traversal witnesses and exposes exactly the three
  intended predicate arguments.  The syntactic scope calculation therefore
  feeds the generic quoted-formula closure theorem, including substitution
  by arbitrary represented replacement terms.
*)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeDecision
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateRootClosure.

Module PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateRootClosure.

(** The two row-aligned rank-zero leaves fit the thirteen-slot local-row
    environment.  These are finite metatheoretic calculations, so the small
    executable scope checker is the clearest audit. *)
Lemma dynamicTruthGlobalSigmaZeroRowFormula_scoped :
  DynamicTruthGlobalLocalRowScoped dynamicTruthGlobalSigmaZeroRowFormula.
Proof.
  unfold DynamicTruthGlobalLocalRowScoped.
  apply (proj1 (standardFormulaScopedb_spec 13 _)).
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthGlobalPiZeroRowFormula_scoped :
  DynamicTruthGlobalLocalRowScoped dynamicTruthGlobalPiZeroRowFormula.
Proof.
  unfold DynamicTruthGlobalLocalRowScoped.
  apply (proj1 (standardFormulaScopedb_spec 13 _)).
  vm_compute. reflexivity.
Qed.

Lemma dynamicTruthGlobalSigmaBaseFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthGlobalSigmaBaseFormula.
Proof.
  unfold dynamicTruthGlobalSigmaBaseFormula.
  apply dynamicTruthGlobalFormula_scoped.
  - apply (proj1 (standardTermScopedb_spec 13 tZero)).
    reflexivity.
  - exact dynamicTruthGlobalSigmaZeroRowFormula_scoped.
  - exact dynamicTruthGlobalPiZeroRowFormula_scoped.
Qed.

Lemma dynamicTruthGlobalPiBaseFormula_scoped :
  StandardFormulaScoped 3 dynamicTruthGlobalPiBaseFormula.
Proof.
  unfold dynamicTruthGlobalPiBaseFormula.
  apply dynamicTruthGlobalFormula_scoped.
  - apply (proj1 (standardTermScopedb_spec 13 (Term.numeral 1))).
    reflexivity.
  - exact dynamicTruthGlobalSigmaZeroRowFormula_scoped.
  - exact dynamicTruthGlobalPiZeroRowFormula_scoped.
Qed.

(** Exact root-closure certificates for the two concrete base outputs. *)
Theorem rawDynamicTruthGlobalSigmaBaseCode_root_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateRootClosed M
    (rawDynamicTruthGlobalSigmaBaseCode M).
Proof.
  intros M hPA.
  rewrite (rawDynamicTruthGlobalSigmaBaseCode_quoted M hPA).
  exact (raw_quotedFormula_ternaryPredicateRootClosed M hPA
    dynamicTruthGlobalSigmaBaseFormula
    dynamicTruthGlobalSigmaBaseFormula_scoped).
Qed.

Theorem rawDynamicTruthGlobalPiBaseCode_root_closed : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateRootClosed M
    (rawDynamicTruthGlobalPiBaseCode M).
Proof.
  intros M hPA.
  rewrite (rawDynamicTruthGlobalPiBaseCode_quoted M hPA).
  exact (raw_quotedFormula_ternaryPredicateRootClosed M hPA
    dynamicTruthGlobalPiBaseFormula
    dynamicTruthGlobalPiBaseFormula_scoped).
Qed.

(** The relational base view forces precisely those two codes, so closure is
    available without relying on a particular existential witness chosen by
    the orbit totality proof. *)
Theorem dynamicTruthPairedGlobalBaseAt_root_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall globalSigma globalPi,
  RawDynamicTruthPairedGlobalBaseAt M globalSigma globalPi ->
  RawCodedTernaryPredicateRootClosed M globalSigma /\
  RawCodedTernaryPredicateRootClosed M globalPi.
Proof.
  intros M hPA globalSigma globalPi hbase.
  unfold RawDynamicTruthPairedGlobalBaseAt,
    RawDynamicTruthPairedGlobalWrapperAt in hbase.
  destruct hbase as [-> ->].
  split.
  - exact (rawDynamicTruthGlobalSigmaBaseCode_root_closed M hPA).
  - exact (rawDynamicTruthGlobalPiBaseCode_root_closed M hPA).
Qed.

End PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
