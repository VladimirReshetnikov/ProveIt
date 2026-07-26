(**
  The represented ternary-formula application needed by dynamic truth.

  Lean's dynamic truth successor inserts a carried ternary truth formula
  beneath five fresh existential binders.  At that point its three arguments
  are de Bruijn variables [#4], [#3], and [#0].  Rocq's raw syntax library
  currently exposes one-variable substitution rather than simultaneous
  substitution.  This module records the exact three-step implementation:

      substitute #6; substitute #4; substitute #0.

  The apparently surprising first two indices compensate for the removal of
  one free-variable slot at each later substitution.  On formulae scoped
  below three variables, the composite is exactly the renaming

      #0 |-> #4,  #1 |-> #3,  #2 |-> #0.

  The graph is output-first.  It is read under

      output :: input :: tail

  and hence can also be used unchanged under

      appliedLower :: previous :: index :: tail

  inside a dynamic-truth successor graph.  Its two existential witnesses are
  the intermediate formula codes.  Exact graph semantics are law-free;
  identifying fixed numeral codes with structural quotations and realizing
  the operation on standard syntax use PA.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization.

Module PABoundedRawCodedDynamicTruthTernaryApplicationGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.

(** The three ordinary variable terms used by the sequential application. *)
Definition dynamicTruthApplicationFirstReplacement : term := tVar 6.
Definition dynamicTruthApplicationSecondReplacement : term := tVar 4.
Definition dynamicTruthApplicationThirdReplacement : term := tVar 0.

(** Their fixed code numerals as object-language terms. *)
Definition dynamicTruthApplicationFirstReplacementCode : term :=
  Term.numeral (termCode dynamicTruthApplicationFirstReplacement).

Definition dynamicTruthApplicationSecondReplacementCode : term :=
  Term.numeral (termCode dynamicTruthApplicationSecondReplacement).

Definition dynamicTruthApplicationThirdReplacementCode : term :=
  Term.numeral (termCode dynamicTruthApplicationThirdReplacement).

(**
  Two existential binders put the environment in the order

      second :: first :: output :: input :: tail.

  Thus variables [1] and [0] name the intermediate results, while [2] and
  [3] continue to name the requested output and original carried input.
*)
Definition dynamicTruthTernaryApplicationGraph : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        dynamicTruthApplicationFirstReplacementCode
        (tVar 3) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthApplicationSecondReplacementCode
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          dynamicTruthApplicationThirdReplacementCode
          (tVar 0) (tVar 2))))).

(** Transparent carrier semantics of the three checked substitutions. *)
Definition RawDynamicTruthTernaryApplication (M : RawPAModel)
    (input output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationFirstReplacement))
      input first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationSecondReplacement))
      first second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthApplicationThirdReplacement))
      second output.

Arguments RawDynamicTruthTernaryApplication M input output
  : clear implicits.

(** Exact semantics in every raw arithmetic structure. *)
Theorem raw_sat_dynamicTruthTernaryApplicationGraph_iff : forall
    (M : RawPAModel) tail input output,
  raw_formula_sat M (scons M output (scons M input tail))
    dynamicTruthTernaryApplicationGraph <->
  RawDynamicTruthTernaryApplication M input output.
Proof.
  intros M tail input output.
  unfold dynamicTruthTernaryApplicationGraph,
    RawDynamicTruthTernaryApplication,
    dynamicTruthApplicationFirstReplacementCode,
    dynamicTruthApplicationSecondReplacementCode,
    dynamicTruthApplicationThirdReplacementCode.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Ordinary syntax counterpart of the represented computation. *)
Definition standardDynamicTruthTernaryApplication (input : formula) :
    formula :=
  Formula.subst
    (Formula.instTerm dynamicTruthApplicationThirdReplacement)
    (Formula.subst
      (Formula.instTerm dynamicTruthApplicationSecondReplacement)
      (Formula.subst
        (Formula.instTerm dynamicTruthApplicationFirstReplacement)
        input)).

(** The simultaneous renaming implemented on ternary-scoped syntax. *)
Definition dynamicTruthTernaryApplicationRenaming (index : nat) : nat :=
  match index with
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | S (S (S tailIndex)) => tailIndex
  end.

Definition DynamicTruthTernaryScoped (input : formula) : Prop :=
  forall index, Formula.Free index input -> index < 3.

Arguments DynamicTruthTernaryScoped input : clear implicits.

(**
  This is the de Bruijn calculation which motivates replacement indices
  [6], [4], and [0].  The values of the displayed renaming above index two
  are irrelevant because the input is ternary-scoped.
*)
Theorem standardDynamicTruthTernaryApplication_eq_rename : forall input,
  DynamicTruthTernaryScoped input ->
  standardDynamicTruthTernaryApplication input =
    Formula.rename dynamicTruthTernaryApplicationRenaming input.
Proof.
  intros input hscope.
  unfold standardDynamicTruthTernaryApplication.
  rewrite !Formula.subst_comp.
  rewrite <- Formula.subst_var_rename.
  apply Formula.subst_ext_free.
  intros index hfree.
  specialize (hscope index hfree).
  destruct index as [|[|[|tailIndex]]];
    cbn [Formula.instTerm dynamicTruthApplicationFirstReplacement
      dynamicTruthApplicationSecondReplacement
      dynamicTruthApplicationThirdReplacement
      dynamicTruthTernaryApplicationRenaming Term.subst];
    try reflexivity; lia.
Qed.

(** A standard external formula supplies all three finite operation trees. *)
Theorem raw_dynamicTruthTernaryApplication_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawDynamicTruthTernaryApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (standardDynamicTruthTernaryApplication input)).
Proof.
  intros M hPA input.
  unfold standardDynamicTruthTernaryApplication.
  set (first := Formula.subst
    (Formula.instTerm dynamicTruthApplicationFirstReplacement) input).
  set (second := Formula.subst
    (Formula.instTerm dynamicTruthApplicationSecondReplacement) first).
  exists (rawQuotedFormulaCode M first),
    (rawQuotedFormulaCode M second).
  split.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthApplicationFirstReplacement).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      dynamicTruthApplicationFirstReplacement input).
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthApplicationSecondReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthApplicationSecondReplacement first).
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthApplicationThirdReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthApplicationThirdReplacement second).
Qed.

(** Standard graph witness, stated directly in output-first form. *)
Corollary dynamicTruthTernaryApplicationGraph_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail input,
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        (standardDynamicTruthTernaryApplication input))
      (scons M (rawQuotedFormulaCode M input) tail))
    dynamicTruthTernaryApplicationGraph.
Proof.
  intros M hPA tail input.
  apply (proj2
    (raw_sat_dynamicTruthTernaryApplicationGraph_iff M tail
      (rawQuotedFormulaCode M input)
      (rawQuotedFormulaCode M
        (standardDynamicTruthTernaryApplication input)))).
  exact (raw_dynamicTruthTernaryApplication_standard M hPA input).
Qed.

(** On ternary-scoped standard syntax the graph selects the expected
    [#4,#3,#0] application literally, not merely an equivalent formula. *)
Corollary dynamicTruthTernaryApplicationGraph_standard_rename : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail input,
  DynamicTruthTernaryScoped input ->
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        (Formula.rename dynamicTruthTernaryApplicationRenaming input))
      (scons M (rawQuotedFormulaCode M input) tail))
    dynamicTruthTernaryApplicationGraph.
Proof.
  intros M hPA tail input hscope.
  rewrite <- (standardDynamicTruthTernaryApplication_eq_rename
    input hscope).
  exact (dynamicTruthTernaryApplicationGraph_standard
    M hPA tail input).
Qed.

End PABoundedRawCodedDynamicTruthTernaryApplicationGraph.
