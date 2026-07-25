(**
  Output-first graphs for bottom and formula-code negation.

  The generic formula-constructor combinators cover the constructors with
  recursive formula children.  Dynamic truth fields also need the derived
  negation operation: in particular, the universal-record branch and the
  two implications making up a truth equivalence negate a model-coded lower
  truth application.  At a nonstandard stage that child is merely a carrier
  element, so quoting an external Rocq formula is not an adequate graph.

  A child graph is read under

      child :: level :: tail.

  The public negation graph is read under

      output :: level :: tail.

  Its existential binder changes the environment to

      child :: output :: level :: tail.

  The explicit renaming below forwards the child, level, and untouched tail.
  The final conjunct uses the already represented formula-code negation
  relation, whose output is [Imp child Bot].  Consequently all semantic and
  totality results are law-free: this is a polynomial syntax constructor,
  not a recursive decoding operation.
*)

From Stdlib Require Import Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedTruthCertificateMasterAssembler.

Module PABoundedRawCodedOutputFirstFormulaNegationGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTruthCertificateMasterAssembler.

(** The constant bottom-code graph is output-first and ignores both the
    supplied level and the ambient tail. *)
Definition outputFirstFormulaBottomGraph : formula :=
  formulaBotCodeTermAt (tVar 0).

Theorem raw_sat_outputFirstFormulaBottomGraph_iff : forall
    (M : RawPAModel) tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    outputFirstFormulaBottomGraph <->
  output = rawFormulaBotCode M.
Proof.
  intros M tail level output.
  unfold outputFirstFormulaBottomGraph.
  rewrite raw_sat_formulaBotCodeTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem outputFirstFormulaBottomGraph_raw_total : forall
    (M : RawPAModel),
  RawOutputFirstFieldGraphTotal M outputFirstFormulaBottomGraph.
Proof.
  intros M tail level.
  exists (rawFormulaBotCode M).
  apply (proj2
    (raw_sat_outputFirstFormulaBottomGraph_iff M tail level _)).
  reflexivity.
Qed.

(** Under the negation graph's witness binder, an input child graph must
    read variable zero as [child], variable one as [level], and then resume
    the original tail. *)
Definition outputFirstNegationChildRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 2
  | S (S tailIndex) => 3 + tailIndex
  end.

Lemma raw_sat_outputFirstNegationChildRenamedGraph_iff : forall
    (M : RawPAModel) childGraph child output level tail,
  raw_formula_sat M
    (scons M child (scons M output (scons M level tail)))
    (Formula.rename outputFirstNegationChildRenaming childGraph) <->
  raw_formula_sat M (scons M child (scons M level tail)) childGraph.
Proof.
  intros M childGraph child output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]].
  - reflexivity.
  - reflexivity.
  - unfold outputFirstNegationChildRenaming.
    replace (3 + tailIndex) with (S (S (S tailIndex))) by lia.
    reflexivity.
Qed.

(** The output-first graph of [child |-> Imp child Bot]. *)
Definition outputFirstFormulaNegationGraph
    (childGraph : formula) : formula :=
  pEx
    (pAnd
      (Formula.rename outputFirstNegationChildRenaming childGraph)
      (codedFormulaNegationTermAt (tVar 0) (tVar 1))).

Definition RawOutputFirstFormulaNegationGraphAt (M : RawPAModel)
    (childGraph : formula) (tail : nat -> M)
    (level output : M) : Prop :=
  exists child : M,
    raw_formula_sat M (scons M child (scons M level tail)) childGraph /\
    RawCodedFormulaNegation M child output.

Arguments RawOutputFirstFormulaNegationGraphAt
  M childGraph tail level output : clear implicits.

(** Exact arbitrary-structure semantics.  In particular this theorem does
    not assume that [child] is a well-formed standard formula code. *)
Theorem raw_sat_outputFirstFormulaNegationGraph_iff : forall
    (M : RawPAModel) childGraph tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (outputFirstFormulaNegationGraph childGraph) <->
  RawOutputFirstFormulaNegationGraphAt M
    childGraph tail level output.
Proof.
  intros M childGraph tail level output.
  unfold outputFirstFormulaNegationGraph,
    RawOutputFirstFormulaNegationGraphAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_outputFirstNegationChildRenamedGraph_iff.
  setoid_rewrite raw_sat_codedFormulaNegationTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Constructor totality lifts pointwise through any total child graph.
    No PA axioms are needed because [Imp child Bot] is a transparent
    polynomial constructor code for every carrier element [child]. *)
Theorem outputFirstFormulaNegationGraph_raw_total : forall
    (M : RawPAModel) childGraph,
  RawOutputFirstFieldGraphTotal M childGraph ->
  RawOutputFirstFieldGraphTotal M
    (outputFirstFormulaNegationGraph childGraph).
Proof.
  intros M childGraph hchild tail level.
  destruct (hchild tail level) as [child hchildGraph].
  exists (rawFormulaImpCode M child (rawFormulaBotCode M)).
  apply (proj2
    (raw_sat_outputFirstFormulaNegationGraph_iff M
      childGraph tail level _)).
  exists child. split; [exact hchildGraph |].
  unfold RawCodedFormulaNegation. reflexivity.
Qed.

End PABoundedRawCodedOutputFirstFormulaNegationGraph.
