(**
  The two-code *local* base row for carrier-indexed dynamic truth.

  Coq's fixed-level truth certificates are mutually polarized: Sigma truth
  and Pi falsity are separate ternary predicates, and each positive-level
  constructor refers to the opposite predicate at the preceding level.  The
  local-row iteration must therefore start with both rank-zero formula codes.
  These predicates still take the surrounding four-table state through free
  variables; a globally closed dynamic truth orbit must wrap them in the
  ten existential table witnesses before using them as certificate fields.

  The public base-graph convention is

      sigmaCode :: piCode :: tail.

  Both coordinates are literal internal numerals before any arithmetic laws
  are used.  In a model of PA those numerals agree with the structural raw
  quotations of the two displayed ternary formulas.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFixedLevelTruth
  RawCodedDynamicTruthTernaryApplicationGraph
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedCarrierIndexedPairedCodeOrbitGraph.

Module PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthTernaryApplicationGraph.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedCarrierIndexedPairedCodeOrbitGraph.

(** The positive coordinate is the base formula already fixed by the
    preceding syntax-fragment module.  The negative coordinate differs only
    in its rank domain and in the truth value requested from the rank-zero
    certificate. *)
Definition dynamicTruthPiBaseTernaryFormula : formula :=
  fixedLevelPiZeroTermAt (tVar 0) (tVar 1) (tVar 2).

Definition RawDynamicTruthPiBase (M : RawPAModel)
    (code assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelPiZero M code assignmentCode assignmentStep.

Arguments RawDynamicTruthPiBase M code assignmentCode assignmentStep
  : clear implicits.

Theorem raw_sat_dynamicTruthPiBaseTernaryFormula_iff : forall
    (M : RawPAModel) tail code assignmentCode assignmentStep,
  raw_formula_sat M
    (scons M code (scons M assignmentCode (scons M assignmentStep tail)))
    dynamicTruthPiBaseTernaryFormula <->
  RawDynamicTruthPiBase M code assignmentCode assignmentStep.
Proof.
  intros M tail code assignmentCode assignmentStep.
  unfold dynamicTruthPiBaseTernaryFormula, RawDynamicTruthPiBase.
  rewrite raw_sat_fixedLevelPiZeroTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition DynamicTruthPiBaseTernaryScoped : Prop :=
  forall index,
    Formula.Free index dynamicTruthPiBaseTernaryFormula -> index < 3.

Theorem dynamicTruthPiBaseTernaryFormula_scoped :
  DynamicTruthPiBaseTernaryScoped.
Proof.
  intros index hfree.
  vm_compute in hfree.
  lia.
Qed.

Corollary dynamicTruthPiBaseTernaryFormula_application_scoped :
  DynamicTruthTernaryScoped dynamicTruthPiBaseTernaryFormula.
Proof.
  exact dynamicTruthPiBaseTernaryFormula_scoped.
Qed.

(** This standard application lemma is useful when checking the base case of
    a successor row.  It does not serve as the nonstandard totality argument;
    that argument uses the represented substitution construction. *)
Corollary dynamicTruthPiBaseTernaryApplicationGraph_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthTernaryApplicationRenaming
          dynamicTruthPiBaseTernaryFormula))
      (scons M
        (rawQuotedFormulaCode M dynamicTruthPiBaseTernaryFormula) tail))
    dynamicTruthTernaryApplicationGraph.
Proof.
  intros M hPA tail.
  apply dynamicTruthTernaryApplicationGraph_standard_rename;
    [exact hPA |].
  exact dynamicTruthPiBaseTernaryFormula_application_scoped.
Qed.

(** A direct two-output graph is preferable to combining two output-first
    graphs with a fake level argument: the paired orbit's base callback has
    exactly the environment [sigmaCode :: piCode :: tail]. *)
Definition dynamicTruthPairedBaseFormulaCodeGraph : formula :=
  pAnd
    (pEq (tVar 0)
      (Term.numeral (formulaCode dynamicTruthBaseTernaryFormula)))
    (pEq (tVar 1)
      (Term.numeral (formulaCode dynamicTruthPiBaseTernaryFormula))).

Definition RawDynamicTruthPairedBaseFormulaCodeAt (M : RawPAModel)
    (sigmaCode piCode : M) : Prop :=
  sigmaCode = rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula /\
  piCode = rawQuotedFormulaCode M dynamicTruthPiBaseTernaryFormula.

Arguments RawDynamicTruthPairedBaseFormulaCodeAt M sigmaCode piCode
  : clear implicits.

(** Law-free semantics records the two literal numeral values. *)
Theorem dynamicTruthPairedBaseFormulaCodeGraph_numeral_representation :
    forall (M : RawPAModel) tail sigmaCode piCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode tail))
    dynamicTruthPairedBaseFormulaCodeGraph <->
  sigmaCode =
      rawNumeralValue M (formulaCode dynamicTruthBaseTernaryFormula) /\
  piCode =
      rawNumeralValue M (formulaCode dynamicTruthPiBaseTernaryFormula).
Proof.
  intros M tail sigmaCode piCode.
  unfold dynamicTruthPairedBaseFormulaCodeGraph.
  cbn [raw_formula_sat raw_term_eval scons].
  rewrite !raw_term_eval_numeral. reflexivity.
Qed.

(** In PA models the literal numeral and structural quotation views agree. *)
Theorem dynamicTruthPairedBaseFormulaCodeGraph_representation : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail sigmaCode piCode,
  raw_formula_sat M
    (scons M sigmaCode (scons M piCode tail))
    dynamicTruthPairedBaseFormulaCodeGraph <->
  RawDynamicTruthPairedBaseFormulaCodeAt M sigmaCode piCode.
Proof.
  intros M hPA tail sigmaCode piCode.
  rewrite dynamicTruthPairedBaseFormulaCodeGraph_numeral_representation.
  unfold RawDynamicTruthPairedBaseFormulaCodeAt.
  rewrite (rawQuotedFormulaCode_standard M hPA
    dynamicTruthBaseTernaryFormula).
  rewrite (rawQuotedFormulaCode_standard M hPA
    dynamicTruthPiBaseTernaryFormula).
  reflexivity.
Qed.

(** Both literal numerals are canonical witnesses in every raw arithmetic
    structure, so base totality itself requires no PA laws. *)
Theorem dynamicTruthPairedBaseFormulaCodeGraph_raw_total : forall
    (M : RawPAModel) tail,
  exists sigmaCode piCode : M,
    raw_formula_sat M
      (scons M sigmaCode (scons M piCode tail))
      dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M tail.
  exists (rawNumeralValue M (formulaCode dynamicTruthBaseTernaryFormula)).
  exists (rawNumeralValue M (formulaCode dynamicTruthPiBaseTernaryFormula)).
  apply (proj2
    (dynamicTruthPairedBaseFormulaCodeGraph_numeral_representation
      M tail _ _)).
  split; reflexivity.
Qed.

Corollary dynamicTruthPairedBaseFormulaCodeGraph_paired_orbit_base_total :
    forall (M : RawPAModel),
  RawCarrierIndexedPairedCodeOrbitBaseTotal M
    dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M tail.
  exact (dynamicTruthPairedBaseFormulaCodeGraph_raw_total M tail).
Qed.

(** The exact structural quotations give the canonical PA-model base row. *)
Corollary dynamicTruthPairedBaseFormulaCodeGraph_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  raw_formula_sat M
    (scons M (rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula)
      (scons M (rawQuotedFormulaCode M dynamicTruthPiBaseTernaryFormula)
        tail))
    dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail.
  apply (proj2
    (dynamicTruthPairedBaseFormulaCodeGraph_representation M hPA tail _ _)).
  split; reflexivity.
Qed.

End PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.
