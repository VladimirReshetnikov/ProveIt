(**
  Constructor combinators for output-first formula-code graphs.

  A component graph is read under

      output :: level :: tail.

  The binary combinator existentially chooses two child codes, evaluates both
  child graphs at the same level and tail, and constrains the public output to
  the corresponding Imp/And/Or code.  The unary combinator does the analogous
  job for All/Ex.  All renamings are explicit, so the construction works for
  arbitrary nonstandard field codes without decoding syntax in Rocq.
*)

From Stdlib Require Import Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedTruthCertificateMasterAssembler.

Module PABoundedRawCodedOutputFirstFormulaGraphCombinators.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTruthCertificateMasterAssembler.

Inductive RawOutputFirstFormulaBinaryKind : Type :=
| ROFBImp
| ROFBAnd
| ROFBOr.

Inductive RawOutputFirstFormulaUnaryKind : Type :=
| ROFUAll
| ROFUEx.

Definition rawOutputFirstFormulaBinaryCode (M : RawPAModel)
    (kind : RawOutputFirstFormulaBinaryKind) (left right : M) : M :=
  match kind with
  | ROFBImp => rawFormulaImpCode M left right
  | ROFBAnd => rawFormulaAndCode M left right
  | ROFBOr => rawFormulaOrCode M left right
  end.

Definition outputFirstFormulaBinaryCodeTermAt
    (kind : RawOutputFirstFormulaBinaryKind)
    (output left right : term) : formula :=
  match kind with
  | ROFBImp => formulaImpCodeTermAt output left right
  | ROFBAnd => formulaAndCodeTermAt output left right
  | ROFBOr => formulaOrCodeTermAt output left right
  end.

Lemma raw_sat_outputFirstFormulaBinaryCodeTermAt_iff : forall
    (M : RawPAModel) kind e output left right,
  raw_formula_sat M e
    (outputFirstFormulaBinaryCodeTermAt kind output left right) <->
  raw_term_eval M e output =
    rawOutputFirstFormulaBinaryCode M kind
      (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros M kind e output left right.
  destruct kind; cbn
    [outputFirstFormulaBinaryCodeTermAt
      rawOutputFirstFormulaBinaryCode].
  - apply raw_sat_formulaImpCodeTermAt_iff.
  - apply raw_sat_formulaAndCodeTermAt_iff.
  - apply raw_sat_formulaOrCodeTermAt_iff.
Qed.

Definition rawOutputFirstFormulaUnaryCode (M : RawPAModel)
    (kind : RawOutputFirstFormulaUnaryKind) (child : M) : M :=
  match kind with
  | ROFUAll => rawFormulaAllCode M child
  | ROFUEx => rawFormulaExCode M child
  end.

Definition outputFirstFormulaUnaryCodeTermAt
    (kind : RawOutputFirstFormulaUnaryKind)
    (output child : term) : formula :=
  match kind with
  | ROFUAll => formulaAllCodeTermAt output child
  | ROFUEx => formulaExCodeTermAt output child
  end.

Lemma raw_sat_outputFirstFormulaUnaryCodeTermAt_iff : forall
    (M : RawPAModel) kind e output child,
  raw_formula_sat M e
    (outputFirstFormulaUnaryCodeTermAt kind output child) <->
  raw_term_eval M e output =
    rawOutputFirstFormulaUnaryCode M kind (raw_term_eval M e child).
Proof.
  intros M kind e output child.
  destruct kind; cbn
    [outputFirstFormulaUnaryCodeTermAt rawOutputFirstFormulaUnaryCode].
  - apply raw_sat_formulaAllCodeTermAt_iff.
  - apply raw_sat_formulaExCodeTermAt_iff.
Qed.

(** After two existential binders the environment is

      right :: left :: output :: level :: tail.

    [outputSlot] is one for the left graph and zero for the right graph. *)
Definition outputFirstBinaryChildRenaming
    (outputSlot index : nat) : nat :=
  match index with
  | 0 => outputSlot
  | 1 => 3
  | S (S tailIndex) => 4 + tailIndex
  end.

Definition outputFirstBinaryEnvironment (M : RawPAModel)
    (right left output level : M) (tail : nat -> M) : nat -> M :=
  scons M right (scons M left (scons M output (scons M level tail))).

Lemma raw_sat_outputFirstBinaryChildRenamedGraph_iff : forall
    (M : RawPAModel) graph right left output level tail outputSlot,
  raw_formula_sat M
    (outputFirstBinaryEnvironment M right left output level tail)
    (Formula.rename (outputFirstBinaryChildRenaming outputSlot) graph) <->
  raw_formula_sat M
    (scons M
      ((outputFirstBinaryEnvironment M right left output level tail)
        outputSlot)
      (scons M level tail)) graph.
Proof.
  intros M graph right left output level tail outputSlot.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]].
  - reflexivity.
  - unfold outputFirstBinaryEnvironment,
      outputFirstBinaryChildRenaming.
    cbn [scons]. reflexivity.
  - unfold outputFirstBinaryEnvironment,
      outputFirstBinaryChildRenaming.
    cbn [scons]. reflexivity.
Qed.

Corollary raw_sat_outputFirstBinary_left_iff : forall
    (M : RawPAModel) graph right left output level tail,
  raw_formula_sat M
    (outputFirstBinaryEnvironment M right left output level tail)
    (Formula.rename (outputFirstBinaryChildRenaming 1) graph) <->
  raw_formula_sat M (scons M left (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_outputFirstBinaryChildRenamedGraph_iff.
  cbn [outputFirstBinaryEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_outputFirstBinary_right_iff : forall
    (M : RawPAModel) graph right left output level tail,
  raw_formula_sat M
    (outputFirstBinaryEnvironment M right left output level tail)
    (Formula.rename (outputFirstBinaryChildRenaming 0) graph) <->
  raw_formula_sat M (scons M right (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_outputFirstBinaryChildRenamedGraph_iff.
  cbn [outputFirstBinaryEnvironment scons]. reflexivity.
Qed.

(** Output-first graph for a pointwise binary formula constructor. *)
Definition outputFirstFormulaBinaryGraph
    (kind : RawOutputFirstFormulaBinaryKind)
    (leftGraph rightGraph : formula) : formula :=
  pEx (pEx
    (pAnd
      (Formula.rename (outputFirstBinaryChildRenaming 1) leftGraph)
      (pAnd
        (Formula.rename (outputFirstBinaryChildRenaming 0) rightGraph)
        (outputFirstFormulaBinaryCodeTermAt kind
          (tVar 2) (tVar 1) (tVar 0))))).

Definition RawOutputFirstFormulaBinaryGraphAt (M : RawPAModel)
    (kind : RawOutputFirstFormulaBinaryKind)
    (leftGraph rightGraph : formula) (tail : nat -> M)
    (level output : M) : Prop :=
  exists left right : M,
    raw_formula_sat M (scons M left (scons M level tail)) leftGraph /\
    raw_formula_sat M (scons M right (scons M level tail)) rightGraph /\
    output = rawOutputFirstFormulaBinaryCode M kind left right.

Arguments RawOutputFirstFormulaBinaryGraphAt
  M kind leftGraph rightGraph tail level output : clear implicits.

Theorem raw_sat_outputFirstFormulaBinaryGraph_iff : forall
    (M : RawPAModel) kind leftGraph rightGraph tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (outputFirstFormulaBinaryGraph kind leftGraph rightGraph) <->
  RawOutputFirstFormulaBinaryGraphAt M kind
    leftGraph rightGraph tail level output.
Proof.
  intros M kind leftGraph rightGraph tail level output.
  unfold outputFirstFormulaBinaryGraph,
    RawOutputFirstFormulaBinaryGraphAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_outputFirstBinary_left_iff.
  setoid_rewrite raw_sat_outputFirstBinary_right_iff.
  setoid_rewrite raw_sat_outputFirstFormulaBinaryCodeTermAt_iff.
  cbn [outputFirstBinaryEnvironment raw_term_eval scons].
  reflexivity.
Qed.

Theorem outputFirstFormulaBinaryGraph_raw_total : forall
    (M : RawPAModel) kind leftGraph rightGraph,
  RawOutputFirstFieldGraphTotal M leftGraph ->
  RawOutputFirstFieldGraphTotal M rightGraph ->
  RawOutputFirstFieldGraphTotal M
    (outputFirstFormulaBinaryGraph kind leftGraph rightGraph).
Proof.
  intros M kind leftGraph rightGraph hleft hright tail level.
  destruct (hleft tail level) as [left hleftGraph].
  destruct (hright tail level) as [right hrightGraph].
  exists (rawOutputFirstFormulaBinaryCode M kind left right).
  apply (proj2 (raw_sat_outputFirstFormulaBinaryGraph_iff M kind
    leftGraph rightGraph tail level _)).
  exists left, right. repeat split; assumption.
Qed.

(** Under one existential binder the environment is

      child :: output :: level :: tail.
*)
Definition outputFirstUnaryChildRenaming (index : nat) : nat :=
  match index with
  | 0 => 0
  | 1 => 2
  | S (S tailIndex) => 3 + tailIndex
  end.

Definition outputFirstUnaryEnvironment (M : RawPAModel)
    (child output level : M) (tail : nat -> M) : nat -> M :=
  scons M child (scons M output (scons M level tail)).

Lemma raw_sat_outputFirstUnaryChildRenamedGraph_iff : forall
    (M : RawPAModel) graph child output level tail,
  raw_formula_sat M
    (outputFirstUnaryEnvironment M child output level tail)
    (Formula.rename outputFirstUnaryChildRenaming graph) <->
  raw_formula_sat M (scons M child (scons M level tail)) graph.
Proof.
  intros M graph child output level tail.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]].
  - reflexivity.
  - unfold outputFirstUnaryEnvironment, outputFirstUnaryChildRenaming.
    cbn [scons]. reflexivity.
  - unfold outputFirstUnaryEnvironment, outputFirstUnaryChildRenaming.
    cbn [scons]. reflexivity.
Qed.

Definition outputFirstFormulaUnaryGraph
    (kind : RawOutputFirstFormulaUnaryKind)
    (childGraph : formula) : formula :=
  pEx
    (pAnd
      (Formula.rename outputFirstUnaryChildRenaming childGraph)
      (outputFirstFormulaUnaryCodeTermAt kind (tVar 1) (tVar 0))).

Definition RawOutputFirstFormulaUnaryGraphAt (M : RawPAModel)
    (kind : RawOutputFirstFormulaUnaryKind) (childGraph : formula)
    (tail : nat -> M) (level output : M) : Prop :=
  exists child : M,
    raw_formula_sat M (scons M child (scons M level tail)) childGraph /\
    output = rawOutputFirstFormulaUnaryCode M kind child.

Arguments RawOutputFirstFormulaUnaryGraphAt
  M kind childGraph tail level output : clear implicits.

Theorem raw_sat_outputFirstFormulaUnaryGraph_iff : forall
    (M : RawPAModel) kind childGraph tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (outputFirstFormulaUnaryGraph kind childGraph) <->
  RawOutputFirstFormulaUnaryGraphAt M kind
    childGraph tail level output.
Proof.
  intros M kind childGraph tail level output.
  unfold outputFirstFormulaUnaryGraph,
    RawOutputFirstFormulaUnaryGraphAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_outputFirstUnaryChildRenamedGraph_iff.
  setoid_rewrite raw_sat_outputFirstFormulaUnaryCodeTermAt_iff.
  cbn [outputFirstUnaryEnvironment raw_term_eval scons].
  reflexivity.
Qed.

Theorem outputFirstFormulaUnaryGraph_raw_total : forall
    (M : RawPAModel) kind childGraph,
  RawOutputFirstFieldGraphTotal M childGraph ->
  RawOutputFirstFieldGraphTotal M
    (outputFirstFormulaUnaryGraph kind childGraph).
Proof.
  intros M kind childGraph hchild tail level.
  destruct (hchild tail level) as [child hchildGraph].
  exists (rawOutputFirstFormulaUnaryCode M kind child).
  apply (proj2 (raw_sat_outputFirstFormulaUnaryGraph_iff M kind
    childGraph tail level _)).
  exists child. split; [exact hchildGraph | reflexivity].
Qed.

End PABoundedRawCodedOutputFirstFormulaGraphCombinators.
